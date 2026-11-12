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
public import Cryptids.Semantics.PA
public import Cryptids.Semantics.Riemann
public import Cryptids.Semantics.Riemann120
public import Cryptids.Semantics.Riemann95
public import Cryptids.Semantics.Zf
public import Cryptids.Semantics.Zf393
public import Cryptids.ErdosTernary15
public import Cryptids.Semantics.ErdosTernary15
public import Cryptids.ErdosTernary14
public import Cryptids.Semantics.ErdosTernary14
public import Cryptids.Brocard27
public import Cryptids.Semantics.Brocard27

/-!
# Certified State Reductions & Formalized Conjecture-Checking Turing Machines

This library formalizes record smaller 2-symbol Turing machines for **Goldbach's Conjecture**
(`25 → 21` states), **ZF Set Theory Consistency** (`393 → 380` states), the **Riemann
Hypothesis** (`120 → 104 → 95` states), and **Erdős's ternary conjecture** (`15 → 14`
states), a 27-state machine for **Brocard's problem** (`brocard_27`), as well as complete
Lean 4 formalizations of all publicly
known baseline machines (`goldbach_25`, `zf_432`, `zf_393`, `riemann_744`, `riemann_120`,
`erdos_ternary_15`),
linking every machine's blank-tape halting problem to Mathlib's statements:

- `Cryptids.Propositions` — Shared definitions of `GoldbachConjecture`,
  `MatiyasevichRiemannCounterexample`, `ZFInconsistent`, `WadeZFInconsistent`,
  `ErdosTernaryConjecture`, and deeply embedded first-order Peano Arithmetic (`PATerm`,
  `PAFormula`, `PAProvable`, `paHalts`, `paZFInconsistent`).
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
- `Cryptids.Semantics.PA` — First-order Peano Arithmetic metatheory and internalized `ZF`
  reductions: arbitrary `[PAModel M]` soundness (`paProvable_sound`, `paProvable_sound_nat`),
  constructive consistency (`not_paProvable_false`), constructive $\Sigma_1^0$ standard-model
  adequacy (`paHalts_holds_iff_halts`, `paZFInconsistent_holds_iff_zfInconsistent`), Gödel–Henkin
  completeness (`paProvable_iff_holdsIn_all_models`), and object-level `PAProvable` proofs that
  `zf_380` and `zf_393` halt iff `ZF` is inconsistent (`paProvable_halts_zf380_iff_zf393`,
  `paProvable_halts_zf393_iff_zfInconsistent`, `paProvable_halts_zf380_iff_zfInconsistent`).
- `Cryptids.ErdosTernary15`, `Cryptids.Semantics.ErdosTernary15` — Stérin and Woods's 15-state
  machine for Erdős's ternary conjecture (`erdosTernary15`), with a constructive proof of
  `Halts erdosTernary15 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` and end-to-end proofs of
  `ConjectureMachines.ErdosTernary15.halts_erdosTernary15_iff_exists_counterexample` and
  `ConjectureMachines.ErdosTernary15.halts_erdosTernary15_iff_not_erdosTernary`.
- `Cryptids.ErdosTernary14`, `Cryptids.Semantics.ErdosTernary14` — Stérin's 14-state machine for
  the same conjecture (`erdosTernary14`), with constructive proofs of
  `Halts erdosTernary14 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` and `Halts candidate ↔ Halts reference` relative to
  `erdosTernary15`, and
  `ConjectureMachines.ErdosTernary14.Semantics.halts_candidate_iff_not_erdosTernary`.
- `Cryptids.Brocard27`, `Cryptids.Semantics.Brocard27` — A 27-state machine for Brocard's problem
  (`brocard27`), with constructive proofs of `Halts brocard27 ↔ ∃ n, 8 ≤ n ∧ IsTri (V n)`
  (`V n = n! / 8`) and `ConjectureMachines.Brocard27.halts_brocard27_iff_exists_square`
  (`Halts brocard27 ↔ ∃ n, 7 < n ∧ IsSquare (n! + 1)`), and
  `ConjectureMachines.Brocard27.halts_brocard27_iff_not_brocard`.
- `Cryptids.Semantics.Goldbach`, `Cryptids.Semantics.Zf`, `Cryptids.Semantics.Riemann` —
  End-to-end proofs linking halting from the blank tape to the corresponding mathematical
  conjectures across all baseline machines (`goldbach25`, `zf432`, `riemann744`).
-/

