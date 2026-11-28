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
public import Cryptids.WeakCollatz75
public import Cryptids.Semantics.WeakCollatz75
public import Cryptids.WeakCollatz41
public import Cryptids.Semantics.WeakCollatz41
public import Cryptids.WeakCollatz27
public import Cryptids.Semantics.WeakCollatz27
public import Cryptids.WeakCollatz17
public import Cryptids.Semantics.WeakCollatz17
public import Cryptids.WeakCollatz16
public import Cryptids.Semantics.WeakCollatz16
public import Cryptids.WeakCollatz15
public import Cryptids.Semantics.WeakCollatz15
public import Cryptids.Legendre21
public import Cryptids.Semantics.Legendre21

/-!
# Certified State Reductions & Formalized Conjecture-Checking Turing Machines

This library formalizes record smaller 2-symbol Turing machines for **Goldbach's Conjecture**
(`25 → 21` states), **ZF Set Theory Consistency** (`393 → 380` states), the **Riemann
Hypothesis** (`120 → 104 → 95` states), **Erdős's ternary conjecture** (`15 → 14` states),
and **Tao's Weak Collatz Conjecture** (`124 → 75 → 41 → 27 → 17 → 16 → 15` states), a 27-state
machine for **Brocard's problem** (`brocard_27`), a 21-state machine for **Legendre's conjecture**
(`legendre_21`), as well as complete Lean 4 formalizations of all publicly known baseline machines
(`goldbach_25`, `zf_432`, `zf_393`, `riemann_744`, `riemann_120`, `erdos_ternary_15`),
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
- `Cryptids.WeakCollatz75`, `Cryptids.Semantics.WeakCollatz75` — A 75-state reference machine for
  Tao's Weak Collatz Conjecture (`weakCollatz75`), with constructive proofs of halting equivalence
  to nontrivial `terras` cycles (`halts_weakCollatz75_iff_exists_cycle`) and the Böhm–Sontacchi
  (1978) Diophantine cycle equation (`halts_weakCollatz75_iff_bohmSontacchi`), plus
  `halts_weakCollatz75_iff_not_weakCollatz`.
- `Cryptids.WeakCollatz41`, `Cryptids.Semantics.WeakCollatz41` — A 41-state compression
  (`weakCollatz41`, `75 → 41` states) eliminating unbounded blank gaps via single-zero markers,
  in-place `terras` hole-shifting, local `2p` comparison/restoration, and 1-pass triple-building,
  with constructive `Halts candidate ↔ Halts reference` (`candidate_equivalent`), cycle and
  Böhm–Sontacchi equivalences, and `halts_candidate_iff_not_weakCollatz`.
- `Cryptids.WeakCollatz27`, `Cryptids.Semantics.WeakCollatz27` — A 27-state compression
  (`weakCollatz27`, `41 → 27` states; `75 → 41 → 27` overall) eliminating the per-stage step
  counter via zero-counter cycle-maximum dovetailing (`y = 1` and `z > x` stage aborts), shared
  `restCfg` stage-advance splitting, and a zero-state blank-tape warm-up (`53/53` active cells
  visited), with constructive `Halts candidate ↔ Halts reference` (`candidate_equivalent`), cycle
  and Böhm–Sontacchi equivalences, and `halts_candidate_iff_not_weakCollatz`.
- `Cryptids.WeakCollatz17`, `Cryptids.Semantics.WeakCollatz17` — A 17-state compression
  (`weakCollatz17`, `27 → 17` states; `75 → 41 → 27 → 17` overall) maintaining the single-separator
  popcount conservation law `d + y = x` (`0^∞ 1^d [0] 1^y 0^∞`) to eliminate comparison,
  restoration, and stage-doubling loops (`33/33` active cells visited), with constructive
  `Halts candidate ↔ Halts reference` (`candidate_equivalent`), cycle and Böhm–Sontacchi
  equivalences, and `halts_candidate_iff_not_weakCollatz`.
- `Cryptids.WeakCollatz16`, `Cryptids.Semantics.WeakCollatz16` — A 16-state compression
  (`weakCollatz16`, `17 → 16` states; `75 → 41 → 27 → 17 → 16` overall) exploiting constructive
  evenness of nontrivial cycle maxima (`even_of_stageHalts`, `x = 2, 4, 6, ...`) to advance stages
  by `+2` without a trim state (`31/31` active cells visited), with constructive
  `Halts candidate ↔ Halts reference` (`candidate_equivalent`), cycle and Böhm–Sontacchi
  equivalences, and `halts_candidate_iff_not_weakCollatz`.
- `Cryptids.WeakCollatz15`, `Cryptids.Semantics.WeakCollatz15` — A 15-state compression
  (`weakCollatz15`, `16 → 15` states; `75 → 41 → 27 → 17 → 16 → 15` overall) replacing inward
  parity-squeezing with a Parity-Back + Left-to-Right Pair-Eater architecture under the shifted
  conservation law `d + n = x - 1` (`n = y - 1`, zero-state `y = 2` abort, 1-step odd decrement,
  6-step boot, `29/29` active cells visited by step `93`), with constructive
  `Halts candidate ↔ Halts reference` (`candidate_equivalent`), cycle and Böhm–Sontacchi
  equivalences, and `halts_candidate_iff_not_weakCollatz`.
- `Cryptids.Legendre21`, `Cryptids.Semantics.Legendre21` — A 21-state machine for Legendre's
  conjecture (`legendre21`), built on the primality test of `goldbach_21`, with constructive
  proofs of `Halts legendre21 ↔ ∃ n, 1 ≤ n ∧ EmptyInterval n` and
  `ConjectureMachines.Legendre21.halts_legendre21_iff_exists_gap`
  (`Halts legendre21 ↔ ∃ n, 1 ≤ n ∧ ∀ p, p.Prime → ¬ (n ^ 2 < p ∧ p < (n + 1) ^ 2)`), and
  `ConjectureMachines.Legendre21.halts_legendre21_iff_not_legendre`.
- `Cryptids.Semantics.Goldbach`, `Cryptids.Semantics.Zf`, `Cryptids.Semantics.Riemann` —
  End-to-end proofs linking halting from the blank tape to the corresponding mathematical
  conjectures across all baseline machines (`goldbach25`, `zf432`, `riemann744`).
-/

