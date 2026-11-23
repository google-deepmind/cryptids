#!/usr/bin/env python3
# Copyright (c) 2026 Google LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Dependency-aware sharding and artifact helper for BusyBeaver CI and Docs CI.

Commands:
  plan        Partition BusyBeaver's module graph into:
                - `foundation`: `BusyBeaverChallenge` plus every local module
                  imported by at least one non-root module in `BusyBeaver`
                  (e.g. `Cryptids.Machines`, `Defs`, `Basic`, `Calculi.*`,
                  `A6.*`, `Pomme.*`, and shared donor `M_*` modules).
                - `shards[0..N-1]`: all remaining pure leaf modules
                  (in-degree 0 outside `BusyBeaver.lean`), deterministically
                  assigned via `crc32(module) % N` so adding/removing proofs in
                  PRs preserves per-shard cache locality.
  pack        Pack `.lake/build/{lib/lean,ir}` artifacts for `foundation` or a
              given `--shard` into a zstd tarball.
  docs-args   Emit the minimal `lake build` target list required by
              `literate.toml` so `docs.yml` never compiles excluded `M_*` blobs.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import pathlib
import re
import shlex
import subprocess
import tempfile
import tomllib
import zlib

IMPORT_LINE_RE = re.compile(
    r"^(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+(.+)$"
)


def strip_lean_comments(src: str) -> str:
  """Strip `--` line comments and nested `/- ... -/` block comments."""
  out: list[str] = []
  i = 0
  n = len(src)
  depth = 0
  in_str = False
  while i < n:
    ch = src[i]
    nxt = src[i + 1] if i + 1 < n else ""
    if depth > 0:
      if ch == "/" and nxt == "-":
        depth += 1
        i += 2
      elif ch == "-" and nxt == "/":
        depth -= 1
        i += 2
      else:
        if ch == "\n":
          out.append("\n")
        i += 1
    elif in_str:
      out.append(ch)
      if ch == "\\" and i + 1 < n:
        out.append(nxt)
        i += 2
      else:
        if ch == '"':
          in_str = False
        i += 1
    else:
      if ch == "/" and nxt == "-":
        depth = 1
        out.append(" ")
        i += 2
      elif ch == "-" and nxt == "-":
        while i < n and src[i] != "\n":
          i += 1
      else:
        if ch == '"':
          in_str = True
        out.append(ch)
        i += 1
  return "".join(out)


def mod_to_source(root: pathlib.Path, mod: str) -> pathlib.Path:
  parts = [p.strip("«»") for p in mod.split(".")]
  return root.joinpath(*parts).with_suffix(".lean")


def parse_local_imports(root: pathlib.Path, path: pathlib.Path) -> list[str]:
  # In Lean 4, module headers consist solely of optional `module`, optional
  # `prelude`, and `import` statements before the first command/declaration.
  clean = strip_lean_comments(path.read_text(encoding="utf-8"))
  found: list[str] = []
  for raw_line in clean.splitlines():
    line = raw_line.strip()
    if not line or line in ("prelude", "module"):
      continue
    match = IMPORT_LINE_RE.match(line)
    if not match:
      break
    for tok in match.group(1).split():
      if mod_to_source(root, tok).is_file():
        found.append(tok)
  return found


def compute_partition(
    root: pathlib.Path, num_shards: int
) -> tuple[list[str], list[list[str]]]:
  bb_root = root / "BusyBeaver.lean"
  if not bb_root.is_file():
    raise SystemExit(f"Missing {bb_root}")

  seed_imports = parse_local_imports(root, bb_root)
  reachable: dict[str, list[str]] = {}
  stack = list(seed_imports)
  while stack:
    mod = stack.pop()
    if mod in reachable or mod == "BusyBeaver":
      continue
    src = mod_to_source(root, mod)
    if not src.is_file():
      continue
    imps = parse_local_imports(root, src)
    reachable[mod] = imps
    stack.extend(imps)

  # Include BusyBeaverChallenge and its local imports (if any) in foundation.
  challenge_mods = {"BusyBeaverChallenge"}
  c_stack = ["BusyBeaverChallenge"]
  while c_stack:
    mod = c_stack.pop()
    src = mod_to_source(root, mod)
    if not src.is_file():
      continue
    for imp in parse_local_imports(root, src):
      if imp not in challenge_mods:
        challenge_mods.add(imp)
        c_stack.append(imp)

  imported_by_nonroot: set[str] = set()
  for imps in reachable.values():
    imported_by_nonroot.update(imps)

  foundation = sorted((imported_by_nonroot | challenge_mods) - {"BusyBeaver"})
  foundation_set = set(foundation)
  leaves = sorted(m for m in reachable if m not in foundation_set)

  # Invariant check: no leaf may import a module outside foundation.
  for leaf in leaves:
    bad = [imp for imp in reachable[leaf] if imp not in foundation_set]
    if bad:
      raise SystemExit(f"Partition invariant violated: {leaf} imports {bad}")

  shards: list[list[str]] = [[] for _ in range(num_shards)]
  for mod in leaves:
    idx = zlib.crc32(mod.encode("utf-8")) % num_shards
    shards[idx].append(mod)

  return foundation, shards


def hash_files(root: pathlib.Path, rel_paths: list[str]) -> str:
  h = hashlib.sha256()
  for rel in sorted(rel_paths):
    p = root / rel
    h.update(rel.encode("utf-8"))
    h.update(b"\0")
    h.update(hashlib.sha256(p.read_bytes()).digest())
    h.update(b"\0")
  return h.hexdigest()[:24]


def emit_output(key: str, value: str) -> None:
  gh_out = os.environ.get("GITHUB_OUTPUT")
  if gh_out:
    with open(gh_out, "a", encoding="utf-8") as f:
      f.write(f"{key}={value}\n")
  print(f"{key}={value}")


def module_artifact_paths(root: pathlib.Path, mod: str) -> list[str]:
  rel_no_ext = pathlib.Path(*mod.split("."))
  parent_part = rel_no_ext.parent
  stem = rel_no_ext.name
  results: list[str] = []
  for sub in ("lib/lean", "ir"):
    base_dir = root / ".lake" / "build" / sub / parent_part
    if not base_dir.is_dir():
      continue
    for entry in sorted(base_dir.iterdir()):
      if entry.is_file() and (
          entry.name == stem or entry.name.startswith(stem + ".")
      ):
        results.append(entry.relative_to(root).as_posix())
  return results


def cmd_plan(args: argparse.Namespace) -> None:
  root = pathlib.Path(args.root).resolve()
  foundation, shards = compute_partition(root, args.num_shards)

  base_cfg = ["lean-toolchain", "lake-manifest.json", "lakefile.toml"]
  f_rels = base_cfg + [
      mod_to_source(root, m).relative_to(root).as_posix() for m in foundation
  ]
  f_hash = hash_files(root, f_rels)
  emit_output("foundation_count", str(len(foundation)))
  emit_output("foundation_hash", f_hash)

  if args.targets_out:
    targets = foundation if args.shard is None else shards[args.shard]
    out_path = pathlib.Path(args.targets_out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(targets) + ("\n" if targets else ""), encoding="utf-8")

  if args.shard is not None:
    shard_mods = shards[args.shard]
    s_rels = [
        mod_to_source(root, m).relative_to(root).as_posix() for m in shard_mods
    ]
    s_hash = hash_files(root, s_rels) if s_rels else "empty"
    emit_output("shard_count", str(len(shard_mods)))
    emit_output("shard_hash", s_hash)


def cmd_pack(args: argparse.Namespace) -> None:
  root = pathlib.Path(args.root).resolve()
  foundation, shards = compute_partition(root, args.num_shards)
  if args.group == "foundation":
    mods = foundation
  else:
    shard_idx = int(args.group)
    mods = shards[shard_idx]

  collected: list[str] = []
  missing: list[str] = []
  for mod in mods:
    olean = (
        root
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / (mod.replace(".", "/") + ".olean")
    )
    trace = (
        root
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / (mod.replace(".", "/") + ".trace")
    )
    ir_c = (
        root / ".lake" / "build" / "ir" / (mod.replace(".", "/") + ".c")
    )
    if not (olean.is_file() and trace.is_file() and ir_c.is_file()):
      missing.append(mod)
      continue
    collected.extend(module_artifact_paths(root, mod))

  if missing and not args.allow_partial:
    raise SystemExit(
        f"Missing compiled artifacts for {len(missing)} module(s), e.g. "
        f"{missing[:5]}"
    )

  out_file = pathlib.Path(args.out).resolve()
  unique_files = sorted(set(collected))
  if not unique_files:
    out_file.unlink(missing_ok=True)
    if args.allow_partial:
      print("No completed module artifacts found; skipping partial archive.")
      return
    raise SystemExit("No compiled module artifacts found to pack.")

  out_file.parent.mkdir(parents=True, exist_ok=True)
  with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as tf:
    for rel in unique_files:
      tf.write(rel + "\n")
    list_path = tf.name
  try:
    subprocess.run(
        ["tar", "--zstd", "-cf", str(out_file), "-C", str(root), "-T", list_path],
        check=True,
    )
  finally:
    pathlib.Path(list_path).unlink(missing_ok=True)
  size_mb = out_file.stat().st_size / (1024 * 1024)
  print(
      f"Packed {len(unique_files)} files ({len(mods) - len(missing)}/{len(mods)}"
      f" modules) into {out_file} ({size_mb:.2f} MiB)"
  )


def cmd_docs_args(args: argparse.Namespace) -> None:
  root = pathlib.Path(args.root).resolve()
  cfg = tomllib.loads((root / "literate.toml").read_text(encoding="utf-8"))
  excludes = [e.strip() for e in cfg.get("exclude", [])]

  def is_excluded(mod: str) -> bool:
    return any(mod == ex or mod.startswith(ex + ".") for ex in excludes)

  targets: list[str] = []
  seen: set[str] = set()
  for entry in cfg.get("targets", []):
    mod = entry.get("module")
    lib = entry.get("library")
    if mod:
      src = mod_to_source(root, mod)
      mod_dir = root / mod.replace(".", "/")
      candidates: list[str] = []
      if src.is_file():
        candidates.append(mod)
      if mod_dir.is_dir():
        for f in sorted(mod_dir.rglob("*.lean")):
          candidates.append(".".join(f.relative_to(root).with_suffix("").parts))
      if not candidates:
        raise SystemExit(f"literate.toml target module {mod!r} matches no .lean files")
      for c in candidates:
        if not is_excluded(c) and c not in seen:
          seen.add(c)
          targets.append(c)
    elif lib:
      if not is_excluded(lib) and lib not in seen:
        seen.add(lib)
        targets.append(lib)
  emit_output("build_args", " ".join(shlex.quote(t) for t in targets))


def main() -> None:
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument("--root", default=".", help="Repository root directory")
  sub = parser.add_subparsers(dest="cmd", required=True)

  p_plan = sub.add_parser("plan")
  p_plan.add_argument("--num-shards", type=int, default=8)
  p_plan.add_argument("--shard", type=int, default=None)
  p_plan.add_argument("--targets-out", default=None)
  p_plan.set_defaults(func=cmd_plan)

  p_pack = sub.add_parser("pack")
  p_pack.add_argument("--num-shards", type=int, default=8)
  p_pack.add_argument(
      "--group", required=True, help="'foundation' or shard index 0..N-1"
  )
  p_pack.add_argument("--out", required=True)
  p_pack.add_argument("--allow-partial", action="store_true")
  p_pack.set_defaults(func=cmd_pack)

  p_docs = sub.add_parser("docs-args")
  p_docs.set_defaults(func=cmd_docs_args)

  parsed = parser.parse_args()
  parsed.func(parsed)


if __name__ == "__main__":
  main()
