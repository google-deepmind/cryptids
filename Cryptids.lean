/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Propositions
public import Cryptids.Goldbach21
public import Cryptids.Riemann104
public import Cryptids.Riemann95
public import Cryptids.Riemann120
public import Cryptids.Zf380
public import Cryptids.Zf393
public import Cryptids.Semantics.Goldbach
public import Cryptids.Semantics.Riemann
public import Cryptids.Semantics.Riemann120
public import Cryptids.Semantics.Riemann95
public import Cryptids.Semantics.Zf
public import Cryptids.Semantics.Zf393
public import Cryptids.Erdos15
public import Cryptids.Semantics.Erdos15
public import Cryptids.Erdos14
public import Cryptids.Semantics.Erdos14

/-!
# Certified State Reductions & Formalized Conjecture-Checking Turing Machines

This library formalizes record smaller 2-symbol Turing machines for **Goldbach's Conjecture**
(`25 → 21` states), **ZF Set Theory Consistency** (`393 → 380` states), the **Riemann
Hypothesis** (`120 → 104 → 95` states), and **Erdős's conjecture on powers of two** (`15 → 14`
states), as well as complete Lean 4 formalizations of all publicly
known baseline machines (`goldbach_25`, `zf_432`, `zf_393`, `riemann_744`, `riemann_120`,
`erdos_15`),
linking every machine's blank-tape halting problem to Mathlib's statements:

- `Cryptids.Propositions` — Shared definitions of `GoldbachConjecture`,
  `MatiyasevichRiemannCounterexample`, `ZFInconsistent`, `WadeZFInconsistent`, and
  `ErdosPowersOfTwoConjecture`.
- `Cryptids.Machines` — Turing machine execution model, bundled machines (`BundledMachine`), and
  machine table definitions (`ConjectureMachines.Machines.*`).
- `Cryptids.Goldbach21`, `Cryptids.Zf380`, `Cryptids.Riemann104` — Proofs of
  `candidate.states < reference.states` and `Halts candidate ↔ Halts reference`.
- `Cryptids.Zf393`, `Cryptids.Semantics.Zf393` — Wade's 393-state ZF machine (`zf393`), our
  380-state reduction (`zf380`), and end-to-end proofs of
  `ConjectureMachines.Zf393.halts_zf393_iff_zfInconsistent`,
  `ConjectureMachines.Zf393.not_halts_zf393`,
  `ConjectureMachines.Zf380.Semantics.halts_candidate_iff_zfInconsistent`, and
  `ConjectureMachines.Zf380.Semantics.not_halts_candidate`.
- `Cryptids.Riemann120`, `Cryptids.Semantics.Riemann120` — Shunia's 120-state Riemann Hypothesis
  machine (`riemann120`), our 104-state reduction (`riemann104`), and end-to-end proofs of
  `ConjectureMachines.Riemann120.halts_riemann120_iff_not_riemannHypothesis` and
  `ConjectureMachines.Riemann104.Semantics.halts_candidate_iff_not_riemannHypothesis`.
- `Cryptids.Riemann95`, `Cryptids.Semantics.Riemann95` — A 95-state machine with an exact
  3,634-step blank initializer, unconditional equivalence to the 104-state machine, and
  `Halts candidate ↔ ¬ RiemannHypothesis`.
- `Cryptids.Erdos15`, `Cryptids.Semantics.Erdos15` — Stérin and Woods's 15-state machine for
  Erdős's conjecture on powers of two (`erdos15`), with a constructive proof of
  `Halts erdos15 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` and end-to-end proofs of
  `ConjectureMachines.Erdos15.halts_erdos15_iff_exists_counterexample` and
  `ConjectureMachines.Erdos15.halts_erdos15_iff_not_erdosPowersOfTwo`.
- `Cryptids.Erdos14`, `Cryptids.Semantics.Erdos14` — Stérin's 14-state machine for the same
  conjecture (`erdos14`), with constructive proofs of `Halts erdos14 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` and
  `Halts candidate ↔ Halts reference` relative to `erdos15`, and
  `ConjectureMachines.Erdos14.Semantics.halts_candidate_iff_not_erdosPowersOfTwo`.
- `Cryptids.Semantics.Goldbach`, `Cryptids.Semantics.Zf`, `Cryptids.Semantics.Riemann` —
  End-to-end proofs linking halting from the blank tape to the corresponding mathematical
  conjectures across all baseline machines (`goldbach25`, `zf432`, `riemann744`).
-/

