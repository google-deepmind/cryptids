"""Check every literal cell and the exact blank initializer; Lean proves equivalence."""

from pathlib import Path
import hashlib
import json
import re


ROOT = Path(__file__).resolve().parents[2]
EXPECTED_SHA256 = "7e9731ed1b7c63d4e67c0f8d646f8498d9645f26e237a8604d4b7f91a6ab398d"


def main():
    table_path = ROOT / "artifacts/riemann_95/machine.txt"
    assert hashlib.sha256(table_path.read_bytes()).hexdigest() == EXPECTED_SHA256
    table = []
    for line in table_path.read_text().splitlines():
        row = []
        for cell in line.split():
            if cell == "---":
                row.append(None)
                continue
            match = re.fullmatch(r"([01])([LR])(\d+)", cell)
            assert match, cell
            row.append((int(match[1]), -1 if match[2] == "L" else 1, int(match[3])))
        assert len(row) == 2
        table.append(row)
    assert len(table) == 95
    assert all(t is None or 0 <= t[2] < 95 for row in table for t in row)

    source = (ROOT / "Cryptids/Riemann95Definition.lean").read_text()
    literal = source.split("def rows : List (List (Option (Fin 2 × Dir × Fin 95))) := [", 1)[1]
    literal = literal.split("\n]", 1)[0]
    lean_rows = []
    for line in literal.splitlines():
        if not line.strip():
            continue
        cells = re.findall(r"none|some \(([01]), \.(left|right), (\d+)\)", line)
        assert len(cells) == 2
        lean_rows.append([
            None if not write else (int(write), -1 if direction == "left" else 1, int(state))
            for write, direction, state in cells
        ])
    assert lean_rows == table, "Lean literal differs from machine.txt"
    none = [(q, a) for q, row in enumerate(table) for a, t in enumerate(row) if t is None]
    assert none == [(61, 1)]

    state = head = 0
    ones = set()
    selector_one_visits = 0
    for _ in range(3634):
        symbol = int(head in ones)
        selector_one_visits += int(state == 41 and symbol == 1)
        transition = table[state][symbol]
        assert transition is not None
        write, direction, state = transition
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    assert state == 15 and head == -4
    assert sorted(ones) == [-5, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36]
    assert selector_one_visits == 0
    print(json.dumps({"states": 95, "cells": 190, "some": 189, "none": none,
                      "bootstrap_steps": 3634, "selector_one_visits": selector_one_visits, "lean_table_binding": "PASS",
                      "full_bootstrap_tape": "PASS"}))


if __name__ == "__main__":
    main()
