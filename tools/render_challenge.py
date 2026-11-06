#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Synchronizes BusyBeaverChallenge.lean with BusyBeaver/Defs/*.lean.

Concatenates the declaration bodies of all Defs/*.lean submodules in umbrella
order into the `namespace BusyBeaver` section of BusyBeaverChallenge.lean.
"""

import argparse
import difflib
import pathlib
import sys


START_MARKER = "@[expose] public section\n\nnamespace BusyBeaver\nopen Relation Turing\n"
END_MARKER = "\nnamespace SixState\n"


def get_submodules(repo_root: pathlib.Path) -> list[str]:
    defs_path = repo_root / "BusyBeaver" / "Defs.lean"
    if not defs_path.exists():
        raise FileNotFoundError(f"Missing umbrella file: {defs_path}")

    submodules = []
    prefix = "public import BusyBeaver.Defs."
    for line in defs_path.read_text().splitlines():
        line = line.strip()
        if line.startswith(prefix):
            mod_name = line[len(prefix):].strip()
            submodules.append(mod_name)

    if not submodules:
        raise ValueError(f"No submodules found in {defs_path}")
    return submodules


def extract_decl_body(file_path: pathlib.Path, is_first: bool) -> str:
    content = file_path.read_text()
    ns_idx = content.find("namespace BusyBeaver")
    if ns_idx == -1:
        raise ValueError(f"Marker 'namespace BusyBeaver' not found in {file_path}")

    after_ns = content[ns_idx + len("namespace BusyBeaver"):]
    end_idx = after_ns.rfind("end BusyBeaver")
    if end_idx == -1:
        raise ValueError(f"Marker 'end BusyBeaver' not found in {file_path}")

    body = after_ns[:end_idx]
    lines = body.splitlines()

    start = 0
    while start < len(lines):
        line = lines[start].strip()
        if not line:
            start += 1
            continue
        if is_first and line == "open Relation Turing":
            start += 1
            continue
        if not is_first and line in (
            "open Relation Turing",
            "variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]",
        ):
            start += 1
            continue
        break

    return "\n".join(lines[start:]).strip()


def render_challenge(repo_root: pathlib.Path) -> str:
    submodules = get_submodules(repo_root)
    defs_dir = repo_root / "BusyBeaver" / "Defs"

    bodies = []
    for i, mod_name in enumerate(submodules):
        file_path = defs_dir / f"{mod_name}.lean"
        if not file_path.exists():
            raise FileNotFoundError(f"Missing submodule file: {file_path}")
        body = extract_decl_body(file_path, is_first=(i == 0))
        bodies.append(body)

    rendered_defs = "\n\n".join(bodies)

    challenge_path = repo_root / "BusyBeaverChallenge.lean"
    current_content = challenge_path.read_text()

    start_idx = current_content.find(START_MARKER)
    if start_idx == -1:
        raise ValueError(f"Start marker not found in {challenge_path}")

    end_idx = current_content.find(END_MARKER, start_idx + len(START_MARKER))
    if end_idx == -1:
        raise ValueError(f"End marker not found in {challenge_path}")

    prefix = current_content[:start_idx + len(START_MARKER)]
    suffix = current_content[end_idx:]

    return f"{prefix}\n{rendered_defs}\n{suffix}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parent.parent,
        help="Path to repository root.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Check whether BusyBeaverChallenge.lean is up to date without writing.",
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    challenge_path = repo_root / "BusyBeaverChallenge.lean"

    try:
        new_content = render_challenge(repo_root)
    except Exception as e:
        print(f"Error rendering challenge: {e}", file=sys.stderr)
        return 1

    current_content = challenge_path.read_text()

    if args.check:
        if current_content == new_content:
            print("BusyBeaverChallenge.lean is synchronized with BusyBeaver/Defs/*.lean.")
            return 0
        else:
            diff = difflib.unified_diff(
                current_content.splitlines(keepends=True),
                new_content.splitlines(keepends=True),
                fromfile="BusyBeaverChallenge.lean (current)",
                tofile="BusyBeaverChallenge.lean (expected)",
                n=3,
            )
            print("ERROR: BusyBeaverChallenge.lean is out of sync with BusyBeaver/Defs/*.lean.", file=sys.stderr)
            print("Run 'python3 tools/render_challenge.py' to synchronize.", file=sys.stderr)
            sys.stderr.writelines(diff)
            return 1

    if current_content != new_content:
        challenge_path.write_text(new_content)
        print("Updated BusyBeaverChallenge.lean successfully.")
    else:
        print("BusyBeaverChallenge.lean is already up to date.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
