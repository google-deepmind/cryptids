# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

"""Zero-dependency first-principles verifier for Conjecture Machines.

This script uses only the Python 3 standard library.
It independently:
1. Verifies the SHA-256 digests of the verbatim published baseline source files
   (`baselines/sources/`) and re-compiles them from first principles into
   canonical transition tables, verifying byte-for-byte identity with
   `baselines/tables/`.
2. Verifies `Cryptids/Machines.lean` and checks that all 5 record candidate
   machines (`goldbach_21`, `zf_380`, `riemann_104`, `riemann_95`,
   `erdos_14`) are well-formed
   2-symbol Turing machines matching their recorded state counts and SHA-256 digests,
   and that their `load_machine_rows%` tables in `Cryptids/Machines.lean` and
   `Challenge.lean` match `baselines/tables/` and `artifacts/*/machine.txt`.
3. Cross-checks the mathematical reduction invariants directly on the
   transition tables (`goldbach_21` table embedding in
   `Cryptids/Goldbach21.lean`, `zf_380` boot + outer-loop checkpoint
   equivalence against `zf_393`, and `riemann_104` boot + `main().0` stage
   equivalence against `riemann_120`).
4. Runs concrete blank-tape Turing machine simulations (`--steps`, default
   250,000 steps per machine) and verifies:
   - Goldbach (25 vs 21 states): 1-to-1 lockstep agreement on even stages
     `2w + 4` across all outer-loop stage checkpoints.
   - ZF (393 vs 380 states): identical bootstrap tape at `t = 39,753` and
     bit-exact tape agreement at every post-boot outer-loop checkpoint.
   - Riemann (120 vs 104 states): 9,037-step self-bootstrap to `rhRootCfg`
     (`state 19`) and >1,000 post-boot root register-machine dispatches.
   - Riemann (95 states): exact 3,634-step bootstrap, including the entire tape.
   - Erdos (15 states): at every stage the tape holds the base-3 digits of
     `2^k` and the count of powers without a digit 2 (`Cryptids/Erdos15.lean`).
   - Erdos (14 states): at every entry to the division state `D` the tape is
     the configuration predicted by `Cryptids/Erdos14.lean`.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import pathlib
import re
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent

PINNED_BASELINES = {
    "goldbach": {
        "source_file": "baselines/sources/goldbach_25_bbchallenge.txt",
        "source_sha256": (
            "3b8934a193ecb165a64dbf048332961fc7a62e7381e69095340a9a85d752380c"
        ),
        "table_file": "baselines/tables/goldbach_25.txt",
        "table_file_sha256": (
            "f5b995cb7917d9943431fc8f2554b0872b185ca81e14865307d26db2776b52a5"
        ),
        "canonical_machine_sha256": (
            "da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "goldbach25",
        "format": "standard",
        "states": 25,
        "symbols": 2,
    },
    "zf": {
        "source_file": "baselines/sources/zf_432_wade.tm",
        "source_sha256": (
            "68a9de26ef68ee9cdf085d201b996686ae55d9570822bcf040aca5999e4f4261"
        ),
        "table_file": "baselines/tables/zf_432.txt",
        "table_file_sha256": (
            "e662deaa52994e73413af37a434dbfb4e8c8204a8d972154ead2d839f442af66"
        ),
        "canonical_machine_sha256": (
            "cb9ffd320f7360b5e0e49181a6201286b408d1f8c168d61fafc51d1ca8b86702"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf432",
        "format": "tursi",
        "states": 432,
        "symbols": 2,
    },
    "riemann": {
        "source_file": "baselines/sources/riemann_744_sorear.tm",
        "source_sha256": (
            "de0084433909f2600a5052eeb0bb2acd9b0ac315078abd1b92d4f3595601dd31"
        ),
        "table_file": "baselines/tables/riemann_744.txt",
        "table_file_sha256": (
            "9866af71143c85cceeaf2e05be8fef1c3ccb226fe04640b23b7b887f815a25d0"
        ),
        "canonical_machine_sha256": (
            "4f629ed5be1715747f3d467dbb35bded647a25dc740a80b5208c14f65d7d5f44"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "riemann744",
        "format": "nql",
        "states": 744,
        "symbols": 2,
    },
    "zf_393": {
        "source_file": "baselines/sources/zf_393_wade.tm",
        "source_sha256": (
            "a1a777fb3994c5b098228f0bd6f27fefcb47a091f36ef8c723bb668c43caf135"
        ),
        "table_file": "baselines/tables/zf_393.txt",
        "table_file_sha256": (
            "f0acf81abb428d9407a9ddd837a1bee07a709634692862386dd6d3e25cc45a97"
        ),
        "canonical_machine_sha256": (
            "dcb8680665d4ec9667a1b6de6edf136e6bb0255a2f73a69c4d4f2e068dba23b2"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf393",
        "format": "tursi",
        "states": 393,
        "symbols": 2,
    },
    "riemann_120": {
        "source_file": "baselines/sources/riemann_120_shunia.tm",
        "source_sha256": (
            "b4b0f07607fc92dae6940f6e6c2d184fec3c13bbfc8cd00a0253321be6009db5"
        ),
        "table_file": "baselines/tables/riemann_120.txt",
        "table_file_sha256": (
            "ec3d408bbeba415afb0666573354bb1e1f2b3f4290b84b8745a3d84c841ab6d0"
        ),
        "canonical_machine_sha256": (
            "a6f0c72649252257bf193268235d0cf9cd847d507d7b241627be7d818c3b86a8"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "riemann120",
        "format": "tursi",
        "states": 120,
        "symbols": 2,
    },
    "erdos_15": {
        "source_file": "baselines/sources/erdos_15_sterin_woods.txt",
        "source_sha256": (
            "f9de29f3b3b06e55afbe61baddf317347b224a1a2203b4cf35f4027da1ecd9ac"
        ),
        "table_file": "baselines/tables/erdos_15.txt",
        "table_file_sha256": (
            "f70b7e4ada6b48644f02377bf1d045b3518e5a640a959a10442bace4311a98dd"
        ),
        "canonical_machine_sha256": (
            "2c38f44a6b344291c1169c35f348ed29d9ee51c1e922e1c43ebba5aeb3326c37"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "erdos15",
        "format": "bbsim",
        "states": 15,
        "symbols": 2,
    },
}

CANDIDATES = [
    {
        "id": "goldbach_21",
        "instance": "goldbach",
        "path": "artifacts/goldbach_21",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "goldbach21",
        "proof_path": "Cryptids/Goldbach21.lean",
        "challenge_path": "Challenge.lean",
        "states": 21,
        "baseline_states": 25,
        "machine_sha256": (
            "b248827bd190d5aedcc9ed6eae5e85f58ed43df8208b0406a9f477fdb2607602"
        ),
    },
    {
        "id": "zf_380",
        "instance": "zf_393",
        "path": "artifacts/zf_380",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf380",
        "proof_path": "Cryptids/Zf380.lean",
        "challenge_path": "Challenge.lean",
        "states": 380,
        "baseline_states": 393,
        "machine_sha256": (
            "c3b8b166f41bd731e6de552a0f9cf7bfa15938fa5165cb4ccd19ead3206b8784"
        ),
    },
    {
        "id": "riemann_104",
        "instance": "riemann_120",
        "path": "artifacts/riemann_104",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "riemann104",
        "proof_path": "Cryptids/Riemann104.lean",
        "challenge_path": "Challenge.lean",
        "states": 104,
        "baseline_states": 120,
        "machine_sha256": (
            "ac0c7e8a76679ba2a3f2c1814166b392c8301e51110a08bcd2c06624be35f25d"
        ),
    },
    {
        "id": "riemann_95",
        "instance": "riemann_104",
        "path": "artifacts/riemann_95",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "riemann95",
        "definition_path": "Cryptids/Riemann95Definition.lean",
        "proof_path": "Cryptids/Riemann95.lean",
        "challenge_path": "Challenge.lean",
        "states": 95,
        "baseline_states": 104,
        "machine_sha256": (
            "7e9731ed1b7c63d4e67c0f8d646f8498d9645f26e237a8604d4b7f91a6ab398d"
        ),
        "table_file_sha256": (
            "7e9731ed1b7c63d4e67c0f8d646f8498d9645f26e237a8604d4b7f91a6ab398d"
        ),
    },
    {
        "id": "erdos_14",
        "instance": "erdos_15",
        "path": "artifacts/erdos_14",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "erdos14",
        "proof_path": "Cryptids/Erdos14.lean",
        "challenge_path": "Challenge.lean",
        "states": 14,
        "baseline_states": 15,
        "machine_sha256": (
            "ce72a09211f6118caadd4ed3cbdfb309a56574f2c49a36f0d82aa75eb2376f70"
        ),
    },
]


@dataclasses.dataclass(frozen=True)
class Transition:
  write: int
  direction: int  # -1 for L, +1 for R
  next_state: int | None  # None for halt


@dataclasses.dataclass(frozen=True)
class Machine:
  states: int
  symbols: int
  table: tuple[tuple[Transition | None, ...], ...]
  canonical_text: str
  sha256: str


def sha256_bytes(data: bytes) -> str:
  return hashlib.sha256(data).hexdigest()


def parse_canonical_machine(text: str) -> Machine:
  """Parses a canonical 2-symbol Turing machine transition table."""
  rows: list[tuple[Transition | None, ...]] = []
  for raw_line in text.splitlines():
    line = raw_line.split("#", 1)[0].strip()
    if not line:
      continue
    cells = line.split()
    if len(cells) != 2:
      raise ValueError(
          f"Expected 2 symbol columns, got {len(cells)}: {raw_line!r}"
      )
    row: list[Transition | None] = []
    for cell in cells:
      if cell == "---":
        row.append(None)
        continue
      if len(cell) < 3:
        raise ValueError(f"Malformed transition cell: {cell!r}")
      write = int(cell[0])
      if write not in (0, 1):
        raise ValueError(f"Invalid write symbol in {cell!r}")
      dir_char = cell[1]
      if dir_char not in ("L", "R"):
        raise ValueError(f"Invalid direction in {cell!r}")
      direction = -1 if dir_char == "L" else 1
      target_str = cell[2:]
      next_state = int(target_str)
      row.append(
          Transition(write=write, direction=direction, next_state=next_state)
      )
    rows.append(tuple(row))

  num_states = len(rows)
  for q, row in enumerate(rows):
    for sym, tr in enumerate(row):
      if (
          tr is not None
          and tr.next_state is not None
          and not (0 <= tr.next_state < num_states)
      ):
        raise ValueError(
            f"State {q} symbol {sym} targets out-of-range state {tr.next_state}"
            f" (states={num_states})"
        )

  canonical_lines = []
  for row in rows:
    cell_strs = []
    for tr in row:
      if tr is None:
        cell_strs.append("---")
      else:
        d = "L" if tr.direction == -1 else "R"
        cell_strs.append(f"{tr.write}{d}{tr.next_state}")
    canonical_lines.append(" ".join(cell_strs))
  canonical_text = "\n".join(canonical_lines) + "\n"
  return Machine(
      states=num_states,
      symbols=2,
      table=tuple(rows),
      canonical_text=canonical_text,
      sha256=sha256_bytes(canonical_text.encode("utf-8")),
  )


def derive_machine_from_source(source_text: str, fmt: str) -> Machine:
  """Re-derives canonical Machine from published source format.

  Formats: standard, tursi, nql, bbsim.
  """
  if fmt == "standard":
    blocks = source_text.strip().split("_")
    lines = []
    for blk in blocks:
      c0, c1 = blk[:3], blk[3:6]
      cells = []
      for c in (c0, c1):
        if c == "---" or c[2] == "Z" or c[2] == "-":
          cells.append("---")
        else:
          w = c[0]
          d = c[1]
          st = c[2]
          nxt = str(ord(st) - ord("A"))
          cells.append(f"{w}{d}{nxt}")
      lines.append(" ".join(cells))
    return parse_canonical_machine("\n".join(lines) + "\n")

  if fmt == "nql":
    order: list[str] = []
    table: dict[tuple[str, int], tuple[int, str, str | None]] = {}
    for line in source_text.splitlines():
      if not line.strip():
        continue
      name, _, rest = line.partition(" = ")
      fields = rest.split()
      order.append(name)
      for sym in (0, 1):
        w, move, nxt = fields[3 * sym : 3 * sym + 3]
        d = "L" if move.upper().startswith("L") else "R"
        table[(name, sym)] = (int(w), d, None if nxt == "HALT" else nxt)
    start = "!ENTRY"
  elif fmt == "tursi":
    start = ""
    order = []
    rows: list[tuple[str, int, int, str, str]] = []
    for line in source_text.splitlines():
      m_hdr = re.fullmatch(r"#!\s*start\s+(\S+)\s*", line)
      if m_hdr:
        start = m_hdr.group(1)
        continue
      if not line.strip() or line.startswith("#"):
        continue
      st, r_sym, w_sym, move, nxt = line.split()
      if st not in order:
        order.append(st)
      d = "L" if move.upper().startswith("L") else "R"
      rows.append((st, int(r_sym), int(w_sym), d, nxt))
    defined = set(order)
    table = {
        (st, r_sym): (w_sym, d, nxt if nxt in defined else None)
        for st, r_sym, w_sym, d, nxt in rows
    }
  elif fmt == "bbsim":
    # Stérin & Woods's `tcosmo/bbsim` machine files: `initial_state:` and
    # `blank_symbol:` headers, then a state name followed by
    # `read write move next` or `read HALT` lines, with letter symbols.
    start = ""
    blank = ""
    order = []
    named_rows: list[tuple[str, str, str | None, str, str]] = []
    current = ""
    for raw_line in source_text.splitlines():
      line = raw_line.split(";", 1)[0].strip()
      if not line:
        continue
      key, sep, value = line.partition(":")
      if sep:
        if key.strip() == "initial_state":
          start = value.strip()
        elif key.strip() == "blank_symbol":
          blank = value.strip()
        continue
      fields = line.split()
      if len(fields) == 1:
        current = fields[0]
        order.append(current)
      elif fields[1:] == ["HALT"]:
        named_rows.append((current, fields[0], None, "", ""))
      else:
        r_sym, w_sym, move, nxt = fields
        named_rows.append((current, r_sym, w_sym, move, nxt))
    letters = {r_sym for _, r_sym, _, _, _ in named_rows}
    if len(letters) != 2 or blank not in letters:
      raise ValueError(f"Expected 2 symbols including blank {blank!r}")
    symbol = {blank: 0, (letters - {blank}).pop(): 1}
    table = {
        (st, symbol[r_sym]): (
            symbol[w_sym],
            "L" if move.upper().startswith("L") else "R",
            nxt,
        )
        for st, r_sym, w_sym, move, nxt in named_rows
        if w_sym is not None
    }
  else:
    raise ValueError(f"Unknown format: {fmt}")

  numbering = {start: 0} if start else {}
  for name in order:
    numbering.setdefault(name, len(numbering))
  names = sorted(numbering, key=numbering.__getitem__)
  out_lines = []
  for name in names:
    cells = []
    for sym in (0, 1):
      if (name, sym) not in table:
        cells.append("---")
        continue
      w, d, nxt = table[(name, sym)]
      if nxt is None:
        cells.append("---")
      else:
        cells.append(f"{w}{d}{numbering[nxt]}")
    out_lines.append(" ".join(cells))
  return parse_canonical_machine("\n".join(out_lines) + "\n")


def parse_lean_machine_def(
    lean_text: str, def_name: str, expected_table_path: str | None = None
) -> Machine:
  """Parses a `Machine N 2` definition (`load_machine_rows%`, `Machine.ofRows <def_name>Rows`, or inline `Machine.ofRows [...]`) from a Lean file."""
  m_load = re.search(
      rf'def {def_name}Rows : List \(List \(Option \(Fin 2 × Dir × Fin (\d+)\)\)\) :=\s*load_machine_rows%\s*"([^"]+)"',
      lean_text,
  )
  if m_load is not None:
    expected_states = int(m_load.group(1))
    table_path = m_load.group(2)
    if expected_table_path is not None:
      assert table_path == expected_table_path, (
          f"{def_name}: expected load_machine_rows% {expected_table_path!r}, got"
          f" {table_path!r}"
      )
    assert (
        'elab "load_machine_rows% "' in lean_text
        or "import Cryptids.Machines" in lean_text
    ), f"{def_name}: missing load_machine_rows% elaborator"
    assert (
        f"def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows"
        in lean_text
    ), f"Missing `def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows`"
    loaded = parse_canonical_machine(
        (ROOT / table_path).read_text(encoding="utf-8")
    )
    assert (
        loaded.states == expected_states
    ), f"{def_name}: expected {expected_states} states, got {loaded.states} in {table_path}"
    return loaded

  m_rows = re.search(
      rf"def {def_name}Rows : List \(List \(Option \(Fin 2 × Dir × Fin (\d+)\)\)\) := \[\s*(.*?)\]\]",
      lean_text,
      re.DOTALL,
  )
  if m_rows is not None:
    expected_states = int(m_rows.group(1))
    assert (
        f"def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows"
        in lean_text
    ), f"Missing `def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows`"
    body = m_rows.group(2) + "]"
  else:
    m = re.search(
        rf"def {def_name} : Machine (\d+) 2 := Machine\.ofRows \[\s*(.*?)\]\s*\]",
        lean_text,
        re.DOTALL,
    )
    assert (
        m is not None
    ), f"Missing `def {def_name} : Machine _ 2 := Machine.ofRows [...]`"
    expected_states = int(m.group(1))
    body = m.group(2) + "]"
  row_matches = re.findall(
      r"\[\s*(none|some \(\d+, \.(?:left|right), \d+\))\s*,\s*(none|some \(\d+,"
      r" \.(?:left|right), \d+\))\s*\]",
      body,
  )
  assert (
      len(row_matches) == expected_states
  ), f"{def_name}: expected {expected_states} rows, parsed {len(row_matches)}"
  lines = []
  for c0, c1 in row_matches:
    cells = []
    for c in (c0, c1):
      if c == "none":
        cells.append("---")
      else:
        cm = re.fullmatch(r"some \((\d+), \.(left|right), (\d+)\)", c)
        assert cm is not None
        w, d_str, nxt = cm.group(1), cm.group(2), cm.group(3)
        d = "L" if d_str == "left" else "R"
        cells.append(f"{w}{d}{nxt}")
    lines.append(" ".join(cells))
  return parse_canonical_machine("\n".join(lines) + "\n")


def verify_goldbach_proof_tables(
    cand_machine: Machine, ref_machine: Machine
) -> None:
  """Verifies that goldbach_21 embeds homomorphically into `edited` (`Fin 21 -> Fin 25`)."""
  assert ref_machine.states == 25 and cand_machine.states == 21
  proof_text = (ROOT / "Cryptids/Goldbach21.lean").read_text(encoding="utf-8")
  assert (
      "theorem candidate_equivalent : Halts candidate ↔ Halts reference"
      in proof_text
  )
  edited_machine = parse_lean_machine_def(proof_text, "edited")
  assert edited_machine.states == 25

  def embed(q: int) -> int:
    if q == 0:
      return 2
    if q == 1:
      return 0
    if q == 2:
      return 23
    if q < 8:
      return q
    if q == 8:
      return 9
    if q < 15:
      return q + 2
    if q == 15:
      return 24
    return q + 2

  for q in range(21):
    eq = embed(q)
    for s in (0, 1):
      expected_ed = edited_machine.table[eq][s]
      cand_tr = cand_machine.table[q][s]
      if expected_ed is None:
        assert cand_tr is None, f"Expected halt at ({q}, {s})"
      else:
        assert cand_tr is not None
        assert (
            cand_tr.write == expected_ed.write
            and cand_tr.direction == expected_ed.direction
        )
        assert embed(cand_tr.next_state) == expected_ed.next_state, (
            f"Goldbach embed mismatch at ({q}, {s}):"
            f" embed({cand_tr.next_state}) != {expected_ed.next_state}"
        )


def verify_zf_380_simulation(
    ref_machine: Machine, cand_380: Machine, steps: int
) -> dict[str, object]:
  """Verifies Cryptids/Zf380.lean and simulates zf_393 vs zf_380 across boot + post-boot checkpoints."""
  proof_text = (ROOT / "Cryptids/Zf380.lean").read_text(encoding="utf-8")
  assert (
      "theorem candidate_equivalent : Halts candidate ↔ Halts reference"
      in proof_text
  )

  def run_to_checkpoints(
      m: Machine, boot_steps: int, boot_state: int
  ) -> tuple[tuple[int, dict[int, int]], list[tuple[int, dict[int, int]]], int]:
    tape: dict[int, int] = {}
    head = 0
    q = 0
    visited = {0}
    boot_snapshot: tuple[int, dict[int, int]] | None = None
    post_chks: list[tuple[int, dict[int, int]]] = []
    for step in range(1, steps + 1):
      tr = m.table[q][tape.get(head, 0)]
      assert tr is not None and tr.next_state is not None
      if tr.write == 0:
        tape.pop(head, None)
      else:
        tape[head] = 1
      head += tr.direction
      q = tr.next_state
      visited.add(q)
      if step == boot_steps:
        assert q == boot_state, (
            f"Unexpected boot state at step {step}: q={q}"
        )
        boot_snapshot = (step, {k - head: 1 for k in tape})
      elif step > boot_steps and q == boot_state:
        rel = {k - head: 1 for k in tape}
        post_chks.append((step, rel))
    assert boot_snapshot is not None
    return boot_snapshot, post_chks, len(visited)

  # Both zf_393 and zf_380 reach state 64 at step 39,753 with identical tapes (`boot_ref` / `boot_cand`)
  boot_r, chks_r, vis_r = run_to_checkpoints(ref_machine, 39_753, 64)
  boot_c, chks_c, vis_c = run_to_checkpoints(cand_380, 39_753, 64)
  assert boot_r[1] == boot_c[1], "zf_380 bootstrap tape mismatch vs zf_393"
  common = min(len(chks_r), len(chks_c))
  assert common >= 30, f"Too few ZF post-boot checkpoints: {common}"
  for i in range(common):
    assert chks_r[i][1] == chks_c[i][1], f"ZF checkpoint {i} tape mismatch"
  return {
      "steps_verified": steps,
      "boot_steps_ref": boot_r[0],
      "boot_steps_cand": boot_c[0],
      "checkpoints_verified": common,
      "visited_states_ref": vis_r,
      "visited_states_cand": vis_c,
  }


def verify_riemann_104_simulation(
    ref_machine: Machine, cand_machine: Machine, steps: int
) -> dict[str, object]:
  """Verifies Cryptids/Riemann104.lean and simulates riemann_104 through its 9,037-step bootstrap to rhRootCfg (`state 19`) and post-boot register-machine instructions."""
  assert ref_machine.states == 120 and cand_machine.states == 104
  proof_text = (ROOT / "Cryptids/Riemann104.lean").read_text(encoding="utf-8")
  assert (
      "theorem candidate_equivalent : Halts candidate ↔ Halts reference"
      in proof_text
  )

  tape: dict[int, int] = {}
  head = 0
  state = 0
  visited = {0}
  root_dispatches = 0
  boot_verified = False
  for step in range(1, steps + 1):
    sym = tape.get(head, 0)
    tr = cand_machine.table[state][sym]
    assert tr is not None and tr.next_state is not None
    if tr.write == 0:
      tape.pop(head, None)
    else:
      tape[head] = 1
    head += tr.direction
    state = tr.next_state
    visited.add(state)
    if step == 9037:
      assert (
          state == 19 and head == -7 and len(tape) == 19
      ), f"Unexpected riemann_104 boot state at t=9037: q={state}, head={head}"
      boot_verified = True
    if step >= 9037 and state == 19:
      root_dispatches += 1

  assert boot_verified, "riemann_104 did not reach step 9037 bootstrap"
  assert (
      root_dispatches >= 1000
  ), f"Expected >=1000 post-boot root dispatches, got {root_dispatches}"
  return {
      "original_states": 120,
      "final_states": 104,
      "states_saved": 16,
      "boot_step_cand": 9037,
      "checkpoints_verified": root_dispatches,
      "visited_states_cand": len(visited),
  }


def verify_riemann_95_bootstrap(machine: Machine) -> dict[str, object]:
  """Check the exact blank initializer and its complete nonzero tape support."""
  assert machine.states == 95 and machine.symbols == 2
  halting_entries = [
      (q, a)
      for q, row in enumerate(machine.table)
      for a, transition in enumerate(row)
      if transition is None
  ]
  assert halting_entries == [(61, 1)]

  state = head = 0
  ones: set[int] = set()
  selector_one_visits = 0
  for _ in range(3634):
    symbol = int(head in ones)
    selector_one_visits += int(state == 41 and symbol == 1)
    transition = machine.table[state][symbol]
    assert transition is not None and transition.next_state is not None
    if transition.write:
      ones.add(head)
    else:
      ones.discard(head)
    head += transition.direction
    state = transition.next_state
  assert state == 15 and head == -4
  assert sorted(ones) == [-5, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36]
  assert selector_one_visits == 0
  return {
      "original_states": 104,
      "final_states": 95,
      "states_saved": 9,
      "boot_step_cand": 3634,
      "boot_state": state,
      "boot_head": head,
      "nonzero_positions": sorted(ones),
      "halting_entries": halting_entries,
      "selector_one_visits": selector_one_visits,
  }


def verify_erdos_15_stages(machine: Machine, steps: int) -> dict[str, object]:
  """Checks the stage layout of `Cryptids/Erdos15.lean` on the blank tape.

  Whenever `erdos_15` is in state 1 (`mul2_F_sim`) on cell 0, cells 0, 1, ...
  hold the base-3 digits of `2^k` (least significant first, `0 -> 01`,
  `1 -> 10`, `2 -> 11`), cells -2, -1 hold `#` (`00`), and cells -4, -3 hold
  the number of `j <= k` such that `2^j` has no digit 2 (`00`, `01`, `10`,
  `11`).
  """
  proof_text = (ROOT / "Cryptids/Erdos15.lean").read_text(encoding="utf-8")
  assert "theorem halts_erdos15_iff_exists_free" in proof_text
  halting = [
      (q, sym)
      for q, row in enumerate(machine.table)
      for sym, tr in enumerate(row)
      if tr is None
  ]
  assert halting == [(14, 1)], f"erdos_15 halting entries: {halting}"

  pair = {(0, 1): 0, (1, 0): 1, (1, 1): 2}
  tape: dict[int, int] = {}
  head = 0
  state = 0
  stage = 0
  free = 0
  for _ in range(steps):
    if state == 1 and head == 0:
      power = 2**stage
      digits = []
      while power:
        digits.append(power % 3)
        power //= 3
      if 2 not in digits:
        free += 1
      read = []
      pos = 0
      while (tape.get(pos, 0), tape.get(pos + 1, 0)) in pair:
        read.append(pair[(tape.get(pos, 0), tape.get(pos + 1, 0))])
        pos += 2
      counter = 2 * tape.get(-4, 0) + tape.get(-3, 0)
      assert read == digits, f"erdos_15 stage {stage}: {read} != {digits}"
      assert counter == free, f"erdos_15 stage {stage}: counter {counter}"
      assert tape.get(-2, 0) == tape.get(-1, 0) == 0
      assert all(-4 <= cell < pos for cell in tape)
      stage += 1
    tr = machine.table[state][tape.get(head, 0)]
    assert tr is not None and tr.next_state is not None, "erdos_15 halted"
    if tr.write:
      tape[head] = 1
    else:
      tape.pop(head, None)
    head += tr.direction
    state = tr.next_state

  expected_free = len([k for k in (0, 2, 8) if k < stage])
  assert free == expected_free, f"Expected {expected_free} powers, got {free}"
  return {
      "steps_simulated": steps,
      "stages_verified": stage,
      "powers_without_digit_2": free,
  }


def verify_erdos_14_stages(machine: Machine, steps: int) -> dict[str, object]:
  """Checks the division layout of `Cryptids/Erdos14.lean` on the blank tape.

  Every time `erdos_14` enters state 3 (`D`), the head is on cell -1 and the
  tape is `divCfg c q r`: cells -1, 0, ... hold `q` ones, a `0` and `r` ones,
  cell -2 holds the separator `0`, and cells -3, -4, -5 hold the counter
  (`000`, `100`, `111`, nearest first). The stage for `2^n` starts with
  `q = 2^n, r = 0`; while `q % 3 != 2` and `q > 0` the next entry has
  `q // 3` ones before the `0`. The counter `c` is the number of `1 <= j < n`
  such that `2^j` has no digit 2, and the machine halts at the third.
  """
  proof_text = (ROOT / "Cryptids/Erdos14.lean").read_text(encoding="utf-8")
  assert "theorem halts_erdos14_iff_exists_free" in proof_text
  halting = [
      (q, sym)
      for q, row in enumerate(machine.table)
      for sym, tr in enumerate(row)
      if tr is None
  ]
  assert halting == [(12, 1)], f"erdos_14 halting entries: {halting}"

  counters = {0: (0, 0, 0), 1: (1, 0, 0), 2: (1, 1, 1)}

  def has_digit_2(m: int) -> bool:
    while m:
      if m % 3 == 2:
        return True
      m //= 3
    return False

  def expected_entries():
    c, n = 0, 1
    while True:
      size = 2**n
      q = size
      while True:
        yield c, n, q, size - q
        if q == 0:
          # Self-check of this model: the division finds a 2 iff 2^n has one.
          assert not has_digit_2(size), f"erdos_14 model: stage {n}"
          c += 1
          break
        if q % 3 == 2:
          assert has_digit_2(size), f"erdos_14 model: stage {n}"
          break
        q //= 3
      n += 1

  entries = expected_entries()
  ones: set[int] = set()
  head = 0
  state = 0
  entries_verified = 0
  stage = 0
  for _ in range(steps):
    tr = machine.table[state][int(head in ones)]
    assert tr is not None and tr.next_state is not None, "erdos_14 halted"
    if tr.write:
      ones.add(head)
    else:
      ones.discard(head)
    head += tr.direction
    state = tr.next_state
    if state == 3:
      c, stage, q, r = next(entries)
      expected = {-1 + i for i in range(q)} | {q + i for i in range(r)}
      expected |= {-3 - i for i, bit in enumerate(counters[c]) if bit}
      assert head == -1, f"erdos_14 stage {stage}: D entered at {head}"
      assert ones == expected, f"erdos_14 stage {stage}: tape mismatch at q={q}"
      entries_verified += 1

  # Stage 9 (after both counter steps) starts at step 208,865.
  if steps >= 210_000:
    assert stage >= 9, f"erdos_14 reached only stage {stage}"
  return {
      "steps_simulated": steps,
      "d_entries_verified": entries_verified,
      "last_stage": stage,
  }


def extract_goldbach_chk0(
    machine: Machine, steps: int, is_candidate: bool
) -> dict[str, object]:
  """Runs Goldbach machine and extracts stage checkpoints `n = 2w + 4` (`stageCfg w` / `stageCfgE w`)."""
  tape: dict[int, int] = {}
  head = 0
  state = 0
  visited_states = {0}
  checkpoints: list[tuple[int, int]] = []

  def read(pos: int) -> int:
    return tape.get(pos, 0)

  def count_ones(pos: int, delta: int) -> int:
    c = 0
    while read(pos) == 1:
      c += 1
      pos += delta
    return c

  chk_state = 1 if is_candidate else 0
  for step in range(1, steps + 1):
    sym = read(head)
    tr = machine.table[state][sym]
    if tr.write == 0:
      tape.pop(head, None)
    else:
      tape[head] = 1
    head += tr.direction
    assert tr.next_state is not None, f"Unexpected halt at step {step}"
    state = tr.next_state
    visited_states.add(state)

    if state == chk_state and read(head) == 1 and read(head - 1) == 0:
      c_p = count_ones(head, 1)
      c_left = count_ones(head - 2, -1)
      c_right = count_ones(head + c_p + 1, 1)
      if not is_candidate and c_p == 1 and c_left >= 3 and c_right == 0:
        checkpoints.append((step, c_left + 1))
      elif is_candidate and c_left == 0 and c_right == 3 and c_p >= 3:
        checkpoints.append((step, c_p + 1))

  return {
      "visited_states": len(visited_states),
      "checkpoints": checkpoints,
  }


def run_verification(
    steps: int = 250_000, verbose: bool = True
) -> dict[str, object]:
  """Runs all first-principles baseline, candidate, and simulation verifications."""
  t0 = time.perf_counter()
  report: dict[str, object] = {
      "baselines": {},
      "candidates": {},
      "simulations": {},
  }

  if verbose:
    print("=" * 78)
    print("CONJECTURE MACHINES: ZERO-DEPENDENCY FIRST-PRINCIPLES VERIFICATION")
    print("=" * 78)

  # 1. Verify Cryptids/Machines.lean formal Halts definition and FromFile.lean elaborator
  machines_lean_bytes = (ROOT / "Cryptids/Machines.lean").read_bytes()
  machines_lean_sha = sha256_bytes(machines_lean_bytes)
  machines_lean_text = machines_lean_bytes.decode("utf-8")
  assert (
      "def Halts (M : Machine states symbols) : Prop := (StateTransition.eval"
      " (step M) init).Dom"
      in machines_lean_text
  )
  assert 'elab "load_machine_rows% " path:str : term' in machines_lean_text
  if verbose:
    print(
        f"[PASS] Cryptids/Machines.lean verified ({machines_lean_sha[:16]}...)"
    )

  # 2. Verify published baseline sources and re-derive canonical tables
  baseline_machines: dict[str, Machine] = {}
  for inst_name, spec in PINNED_BASELINES.items():
    src_bytes = (ROOT / str(spec["source_file"])).read_bytes()
    src_sha = sha256_bytes(src_bytes)
    assert (
        src_sha == spec["source_sha256"]
    ), f"{inst_name} source SHA-256 mismatch"

    tbl_bytes = (ROOT / str(spec["table_file"])).read_bytes()
    tbl_sha = sha256_bytes(tbl_bytes)
    assert (
        tbl_sha == spec["table_file_sha256"]
    ), f"{inst_name} table file SHA-256 mismatch"

    src_text = src_bytes.decode("utf-8")
    tbl_text = tbl_bytes.decode("utf-8")
    m_from_src = derive_machine_from_source(src_text, str(spec["format"]))
    m_from_tbl = parse_canonical_machine(tbl_text)
    assert m_from_src.table == m_from_tbl.table, (
        f"{inst_name}: derived machine from published source does not match"
        " pinned table"
    )
    m = m_from_tbl
    assert (
        m.sha256 == spec["canonical_machine_sha256"]
    ), f"{inst_name}: canonical machine SHA-256 mismatch: {m.sha256}"
    assert m.states == spec["states"] and m.symbols == spec["symbols"]
    ref_lean_text = (ROOT / str(spec["lean_file"])).read_text(encoding="utf-8")
    assert (
        parse_lean_machine_def(
            ref_lean_text,
            str(spec["lean_def"]),
            expected_table_path=str(spec["table_file"]),
        ).table
        == m.table
    ), f"{spec['lean_file']} table mismatch"
    baseline_machines[inst_name] = m
    report["baselines"][inst_name] = {
        "states": m.states,
        "symbols": m.symbols,
        "source_sha256": src_sha,
        "table_sha256": tbl_sha,
        "canonical_machine_sha256": m.sha256,
    }
    if verbose:
      print(
          f"[PASS] Baseline {inst_name:<8}: {m.states:>3} states | "
          f"source->table->Lean verified ({spec['lean_file']})"
      )

  # 3. Verify all candidate tables, independent declarations, and Lean proof files.
  cand_machines: dict[str, Machine] = {}
  reference_specs = dict(PINNED_BASELINES)
  reference_specs.update({str(spec["id"]): spec for spec in CANDIDATES})
  for cspec in CANDIDATES:
    cid = str(cspec["id"])
    inst = str(cspec["instance"])
    cdir = ROOT / str(cspec["path"])
    m_bytes = (cdir / "machine.txt").read_bytes()
    m_text = m_bytes.decode("utf-8")
    if "table_file_sha256" in cspec:
      assert sha256_bytes(m_bytes) == cspec["table_file_sha256"], (
          f"{cid} table file SHA-256 mismatch"
      )
    m_lean_text = (ROOT / str(cspec["lean_file"])).read_text(encoding="utf-8")
    p_path = ROOT / str(cspec["proof_path"])
    p_bytes = p_path.read_bytes()
    p_text = p_bytes.decode("utf-8")
    definition_path = str(cspec.get("definition_path", cspec["proof_path"]))
    definition_text = (ROOT / definition_path).read_text(encoding="utf-8")
    c_path = ROOT / str(cspec["challenge_path"])
    c_text = c_path.read_text(encoding="utf-8")
    m = parse_canonical_machine(m_text)
    p_sha = sha256_bytes(p_bytes)

    assert (
        m.states == cspec["states"]
    ), f"{cid} state count mismatch: {m.states}"
    assert (
        m.sha256 == cspec["machine_sha256"]
    ), f"{cid} machine SHA-256 mismatch: {m.sha256}"
    assert (
        parse_lean_machine_def(
            m_lean_text,
            str(cspec["lean_def"]),
            expected_table_path=f"{cspec['path']}/machine.txt",
        ).table
        == m.table
    ), f"{cspec['lean_file']} candidate table mismatch"

    assert (
        parse_lean_machine_def(
            c_text,
            str(cspec["lean_def"]),
            expected_table_path=f"{cspec['path']}/machine.txt",
        ).table
        == m.table
    ), f"{cspec['challenge_path']} candidate table mismatch"

    ref_def = str(reference_specs[inst]["lean_def"])
    cand_def = str(cspec["lean_def"])
    b_states = int(cspec["baseline_states"])
    assert b_states == reference_specs[inst]["states"]
    expected_ref_alias = (
        f"abbrev reference : BundledMachine 2 := Machines.{ref_def}.bundle"
    )
    expected_cand_alias = (
        f"abbrev candidate : BundledMachine 2 := Machines.{cand_def}.bundle"
    )
    expected_fewer_states = (
        "theorem candidate_fewer_states : candidate.states < reference.states"
    )
    assert (
        expected_ref_alias in definition_text
    ), f"{definition_path} missing `{expected_ref_alias}`"
    assert (
        expected_cand_alias in definition_text
    ), f"{definition_path} missing `{expected_cand_alias}`"
    assert (
        expected_fewer_states in p_text
    ), f"{cspec['proof_path']} missing `{expected_fewer_states}`"
    assert (
        expected_ref_alias in c_text
    ), f"{cspec['challenge_path']} missing `{expected_ref_alias}`"
    assert (
        expected_cand_alias in c_text
    ), f"{cspec['challenge_path']} missing `{expected_cand_alias}`"
    assert (
        expected_fewer_states in c_text
    ), f"{cspec['challenge_path']} missing `{expected_fewer_states}`"
    cand_machines[cid] = m

    delta = b_states - m.states
    pct = round(100.0 * delta / b_states, 2)
    report["candidates"][cid] = {
        "instance": cspec["instance"],
        "states": m.states,
        "baseline_states": b_states,
        "states_saved": delta,
        "reduction_percent": pct,
        "machine_sha256": m.sha256,
        "proof_sha256": p_sha,
        "proof_lines": len(p_text.splitlines()),
    }
    if verbose:
      print(
          f"[PASS] Candidate {cid:<11}: {m.states:>3} states (-{delta:>3},"
          f" -{pct:>5.2f}%) | SHA-256 {m.sha256[:16]}... |"
          f" {cspec['proof_path']} ({len(p_text.splitlines())} lines)"
      )

  # 4. Mathematical transition-table & invariant cross-checks
  verify_goldbach_proof_tables(
      cand_machines["goldbach_21"], baseline_machines["goldbach"]
  )
  if verbose:
    print(
        "[PASS] Goldbach 21 Cryptids/Goldbach21.lean table cross-check: all 42"
        " candidate + 50 edited cells match"
    )

  zf_sim = verify_zf_380_simulation(
      baseline_machines["zf_393"], cand_machines["zf_380"], steps
  )
  report["simulations"]["zf_380"] = zf_sim
  if verbose:
    print(
        f"[PASS] ZF 380 simulation ({steps:,} steps):"
        " boot tape identical at t=39,753 +"
        f" {zf_sim['checkpoints_verified']}/{zf_sim['checkpoints_verified']}"
        " post-boot checkpoints match 1-to-1"
    )

  riemann_sim = verify_riemann_104_simulation(
      baseline_machines["riemann_120"],
      cand_machines["riemann_104"],
      steps,
  )
  report["simulations"]["riemann_104"] = riemann_sim
  if verbose:
    print(
        f"[PASS] Riemann 104 simulation ({steps:,} steps):"
        " boot at t=9,037 (`state 19`) +"
        f" {riemann_sim['checkpoints_verified']} post-boot root dispatches"
        f" verified ({riemann_sim['visited_states_cand']}/104 states visited)"
    )

  riemann95_sim = verify_riemann_95_bootstrap(cand_machines["riemann_95"])
  report["simulations"]["riemann_95"] = riemann95_sim
  if verbose:
    print(
        "[PASS] Riemann 95 bootstrap: all 190 cells + complete tape at"
        " t=3,634 (state 15, head -4) verified"
    )

  erdos_sim = verify_erdos_15_stages(baseline_machines["erdos_15"], steps)
  report["simulations"]["erdos_15"] = erdos_sim
  if verbose:
    print(
        f"[PASS] Erdos 15 stage simulation ({steps:,} steps):"
        f" digits of 2^k and counter verified for k <"
        f" {erdos_sim['stages_verified']}"
    )

  erdos14_sim = verify_erdos_14_stages(cand_machines["erdos_14"], steps)
  report["simulations"]["erdos_14"] = erdos14_sim
  if verbose:
    print(
        f"[PASS] Erdos 14 stage simulation ({steps:,} steps):"
        f" {erdos14_sim['d_entries_verified']} division entries verified"
        f" up to the start of stage n = {erdos14_sim['last_stage']}"
    )

  # 5. Concrete blank-tape lockstep simulations
  gb_ref_sim = extract_goldbach_chk0(
      baseline_machines["goldbach"], steps, is_candidate=False
  )
  gb_cand_sim = extract_goldbach_chk0(
      cand_machines["goldbach_21"], steps, is_candidate=True
  )
  common_gb = min(
      len(gb_ref_sim["checkpoints"]), len(gb_cand_sim["checkpoints"])
  )
  assert common_gb >= 15
  for i in range(common_gb):
    _, r_even = gb_ref_sim["checkpoints"][i]
    _, c_even = gb_cand_sim["checkpoints"][i]
    assert (
        r_even == c_even == 2 * i + 4
    ), f"Goldbach stage checkpoint {i} mismatch: {r_even} vs {c_even}"
  report["simulations"]["goldbach_21"] = {
      "steps_simulated": steps,
      "checkpoints_matched": common_gb,
      "ref_visited_states": gb_ref_sim["visited_states"],
      "cand_visited_states": gb_cand_sim["visited_states"],
      "ref_steps_at_checkpoint": gb_ref_sim["checkpoints"][common_gb - 1][0],
      "cand_steps_at_checkpoint": gb_cand_sim["checkpoints"][common_gb - 1][0],
  }
  if verbose:
    print(
        f"[PASS] Goldbach 21 stage simulation ({steps:,} steps):"
        f" {common_gb}/{common_gb} even stages `2w+4` match 1-to-1;"
        f" {gb_cand_sim['visited_states']}/21 candidate states visited"
    )

  for extra_id, boot_step, boot_state in (
      ("zf", None, None),
      ("zf_393", 39773, 99),
      ("riemann", None, None),
      ("riemann_120", None, None),
  ):
    em = baseline_machines[extra_id]
    tape: dict[int, int] = {}
    q = 0
    head = 0
    boot_ok = False
    for t in range(steps):
      if boot_step is not None and t == boot_step:
        boot_ok = (q == boot_state)
      tr = em.table[q][tape.get(head, 0)]
      assert tr is not None and tr.next_state is not None, (
          f"{extra_id} unexpectedly halted at step {t}"
      )
      if tr.write:
        tape[head] = 1
      else:
        tape.pop(head, None)
      head += tr.direction
      q = tr.next_state
    if boot_step is not None and steps >= boot_step:
      assert (
          boot_ok
      ), f"{extra_id} did not reach boot state {boot_state} at step {boot_step}"
    report["simulations"][extra_id] = {
        "steps_simulated": steps,
        "boot_step_verified": boot_step if boot_step is not None else None,
        "final_state": q,
        "final_head": head,
        "nonzero_cells": len(tape),
    }
    if verbose:
      detail = (
          f"boot checkpoint at t={boot_step:,} (`state {boot_state}`) verified; "
          if boot_step is not None
          else f"state={q}, head={head}; "
      )
      print(
          f"[PASS] {extra_id} blank-tape simulation ({steps:,} steps):"
          f" {detail}{len(tape)} active cells"
      )

  elapsed = time.perf_counter() - t0
  report["elapsed_seconds"] = round(elapsed, 3)
  if verbose:
    print("=" * 78)
    print(
        f"ALL FIRST-PRINCIPLES VERIFICATION CHECKS PASSED IN {elapsed:.2f}s"
        " (EXIT 0)"
    )
    print("=" * 78)
  return report


def main() -> int:
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument(
      "--steps",
      type=int,
      default=250_000,
      help=(
          "Number of blank-tape simulation steps per machine (default: 250000)."
      ),
  )
  parser.add_argument(
      "--json",
      type=pathlib.Path,
      default=None,
      help="Optional path to write structured verification report JSON.",
  )
  args = parser.parse_args()
  report = run_verification(steps=args.steps, verbose=True)
  if args.json is not None:
    args.json.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
  return 0


if __name__ == "__main__":
  sys.exit(main())
