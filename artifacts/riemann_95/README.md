# 95-state Riemann Hypothesis machine

This binary Turing machine has **95 states**, 189 defined transitions, and one
halting transition (`61/ONE`). It starts in state 0 on the blank tape. Lean proves
that it halts if and only if Mathlib's `RiemannHypothesis` is false.

The construction retains the stage counter in the `x` register after `FOLD`,
removing the subsequent `MoveXM` operation. A permutation of the physical operand
banks permits a blank initializer. The reduction is proved directly against the
existing 104-state machine.

The exact 3,634-step initializer reaches state 15 at head position -4, with
padding 22, five zero active registers, and four zero extra registers. The proof
covers this full tape, the safe first stage, and all subsequent stages. It uses
the existing mathematical Riemann criterion without an extra assumption.

## Review entry points

- [`Machines.lean`](../../Cryptids/Machines.lean): transition table loaded from `machine.txt`.
- [`Riemann95Definition.lean`](../../Cryptids/Riemann95Definition.lean): machine aliases
  and initial configuration.
- [`Riemann95.lean`](../../Cryptids/Riemann95.lean):
  `halts_candidate_iff_counterexample`, `candidate_equivalent`, and
  `candidate_fewer_states` relative to `Riemann104`.
- [`Semantics/Riemann95.lean`](../../Cryptids/Semantics/Riemann95.lean):
  `halts_candidate_iff_not_riemannHypothesis`.
- [`ReductionSupport/Riemann95/README.md`](../../Cryptids/ReductionSupport/Riemann95/README.md):
  proof layers and the connection between the new and reference programs.

## Verification

From the repository root:

```sh
lake build
lake comparator --config comparator/riemann_95.json
python3 verify.py
```

The comparator checks the three public theorems against independent challenge
definitions loaded from [`machine.txt`](machine.txt), allowing only `propext`,
`Classical.choice`, and `Quot.sound`. The same targets are included in
`comparator/all.json` and the normal CI workflow.

The root Python verifier checks the table's SHA-256, compares all 190 cells
loaded by the implementation and challenge, and replays the complete blank
initializer, including its final tape. This finite check supplements the unbounded Lean proof.
