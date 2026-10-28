# 14-state Erdős powers-of-two machine

This binary Turing machine has **14 states**, 27 defined transitions, and one halting transition
(`12/ONE`, state `M` reading `1`). It starts in state 0 on the blank tape. Lean proves that it
halts if and only if some `2 ^ n` with `n > 8` has no digit `2` in base `3`, so it halts if and
only if the 15-state machine `erdos_15` does.

The machine is due to Tristan Stérin, who [announced it](https://discord.com/channels/960643023006490684/1561295445312151622/1562203343114473472)
on the bbchallenge Discord in October 2026; it is listed on the
[Cryptids](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&oldid=9722) page of the bbchallenge wiki
(revision 9722) as

```
1LB1RA_1LC1LB_0RD0RA_1LM0RE_1LF1RE_0LJ1LG_1RK0LH_1RI1LH_0LJ0RE_0RD1LJ_0LL1RK_1RN0LC_0LN---_0RK0LM
```

[`machine.txt`](machine.txt) is this table with the states `A`–`N` numbered `0`–`13`.

Unlike `erdos_15`, which keeps the base-3 digits of `2 ^ n`, this machine keeps `2 ^ n` in unary
and reads its base-3 digits by repeated division by `3`. A single `0` in the block of ones marks
where the quotient ends; a digit `2` ends the stage, and a stage that reaches quotient `0`
advances a counter, which halts at the third such stage (after `2 ^ 2` and `2 ^ 8`). The block is
then doubled in place. The layout is described in the docstring of
[`Erdos14.lean`](../../Cryptids/Erdos14.lean).

## Review entry points

- [`Machines.lean`](../../Cryptids/Machines.lean): transition table loaded from `machine.txt`.
- [`Erdos14.lean`](../../Cryptids/Erdos14.lean): `halts_erdos14_iff_exists_free`,
  `candidate_equivalent`, and `candidate_fewer_states` relative to `Erdos15`.
- [`Semantics/Erdos14.lean`](../../Cryptids/Semantics/Erdos14.lean):
  `halts_candidate_iff_not_erdosPowersOfTwo`.

`halts_erdos14_iff_exists_free` and `candidate_equivalent` use only `propext` and `Quot.sound`.

## Verification

From the repository root:

```sh
lake build
lake comparator --config comparator/erdos_14.json
python3 verify.py
```

The comparator checks the three public theorems against independent challenge definitions loaded
from [`machine.txt`](machine.txt). `candidate_fewer_states` and `candidate_equivalent` are also
checked without `Classical.choice` in `comparator/constructive.json`, and all three in
`comparator/all.json`.

The root Python verifier checks the table's SHA-256, compares the cells loaded by the
implementation and challenge, and simulates the machine on the blank tape, checking the full tape
at every entry to the division state `D` against the configurations used in the proof. This
finite check supplements the unbounded Lean proof.
