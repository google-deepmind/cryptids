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

"""Verifies and updates CORE_MANIFEST.json against repository files.

Ensures the shared BusyBeaver core files match the pinned SHA256 checksums.
"""

import argparse
import hashlib
import json
import pathlib
import sys

CORE_FILES = [
    "BusyBeaver/Defs.lean",
    "BusyBeaver/Defs/Core.lean",
    "BusyBeaver/Defs/Patterns.lean",
    "BusyBeaver/Defs/Stack.lean",
    "BusyBeaver/Defs/Odometer.lean",
    "BusyBeaver/Defs/Transducer.lean",
    "BusyBeaver/Defs/WordRun.lean",
    "BusyBeaver/Defs/Segmented.lean",
    "BusyBeaver/Basic.lean",
    "BusyBeaver/WordRLE.lean",
    "BusyBeaver/AffRLE.lean",
    "BusyBeaver/Cert.lean",
]


def compute_sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generate_manifest(repo_root: pathlib.Path, core_version: int = 1) -> dict:
    files_map = {}
    for rel_path in CORE_FILES:
        full_path = repo_root / rel_path
        if not full_path.exists():
            raise FileNotFoundError(f"Core file not found: {full_path}")
        files_map[rel_path] = compute_sha256(full_path)
    return {
        "core_version": core_version,
        "files": files_map,
    }


def verify_manifest(repo_root: pathlib.Path, manifest_path: pathlib.Path) -> bool:
    if not manifest_path.exists():
        print(f"ERROR: Manifest file not found: {manifest_path}", file=sys.stderr)
        return False

    try:
        manifest = json.loads(manifest_path.read_text())
    except Exception as e:
        print(f"ERROR: Failed to parse manifest JSON: {e}", file=sys.stderr)
        return False

    manifest_files = manifest.get("files", {})
    all_ok = True

    for rel_path in CORE_FILES:
        full_path = repo_root / rel_path
        if not full_path.exists():
            print(f"ERROR: Core file missing: {rel_path}", file=sys.stderr)
            all_ok = False
            continue

        if rel_path not in manifest_files:
            print(f"ERROR: File {rel_path} not found in manifest", file=sys.stderr)
            all_ok = False
            continue

        expected_hash = manifest_files[rel_path]
        actual_hash = compute_sha256(full_path)
        if actual_hash != expected_hash:
            print(f"ERROR: SHA256 mismatch for {rel_path}:", file=sys.stderr)
            print(f"  expected: {expected_hash}", file=sys.stderr)
            print(f"  actual:   {actual_hash}", file=sys.stderr)
            all_ok = False

    for rel_path in manifest_files:
        if rel_path not in CORE_FILES:
            print(f"WARNING: Unexpected file in manifest: {rel_path}", file=sys.stderr)

    return all_ok


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parent.parent,
        help="Path to repository root.",
    )
    parser.add_argument(
        "--manifest",
        type=str,
        default="CORE_MANIFEST.json",
        help="Manifest file name relative to repo root.",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="Update manifest with current SHA256 hashes.",
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    manifest_path = repo_root / args.manifest

    if args.update:
        manifest = generate_manifest(repo_root)
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
        print(f"Updated {manifest_path} with {len(manifest['files'])} core files.")
        return 0

    if not verify_manifest(repo_root, manifest_path):
        print("Core manifest verification FAILED.", file=sys.stderr)
        return 1

    print(f"Core manifest verification PASSED: {len(CORE_FILES)} core files verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
