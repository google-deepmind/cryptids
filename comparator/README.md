# Verification with `leanprover/comparator`

This directory contains configuration files for verifying the proofs in [`Cryptids/`](../Cryptids/)
and [`BusyBeaver/`](../BusyBeaver/) against the self-contained challenge specifications in
[`Challenge.lean`](../Challenge.lean) and [`BusyBeaverChallenge.lean`](../BusyBeaverChallenge.lean)
using [`leanprover/comparator`](https://github.com/leanprover/comparator).

## Overview

- [`Challenge.lean`](../Challenge.lean) imports **only** Mathlib and Lean core (`Lean.Elab.Term`),
  defines all conjecture-checking baseline and candidate machines (`reference` and `candidate`),
  states the target mathematical propositions (`GoldbachConjecture`,
  `MatiyasevichRiemannCounterexample`, `ZFProvable`, `WadeZFProvable`, `PAProvable`, `paHalts`,
  `paZFInconsistent`, etc.), and states all 29 target state-reduction, equivalence, `PA`
  metatheory & internalized `ZF` provability, and semantics theorems with `sorry`.
- [`BusyBeaverChallenge.lean`](../BusyBeaverChallenge.lean) imports **only** Mathlib and Lean core
  (`Lean.Elab.Term`), defines the shared `BusyBeaver` Post-Turing execution model, accelerated
  `TapePatternSet`, `StackPatternSet`, stack/odometer/transducer reductions, and Collatz-like
  acceleration semantics (`IsClosedPatternSet`, `HasCollatzReduction`, `IsClosedStackPatternSet`,
  `HasStackedCollatzReduction`, `HasStackReduction`, `HasOdometerReduction`,
  `HasTransducerReduction`, `IsValidAcceleration`, `CollatzHalts`, `IsHalt`, `IsNotHalt`), and
  `load_rle_machine%` once, and states all 425 `BB(6)` and `BB(3, 3)` holdout theorems
  (`is_closed_pattern_set` / `is_closed_stack_pattern_set`, `has_collatz_reduction` /
  `has_stacked_collatz_reduction`, `has_stack_reduction`, `has_odometer_reduction`,
  `has_transducer_reduction`, `is_valid_acceleration`, `isHalt_iff_acceleration`,
  `is_valid_highLevel_acceleration`, `isHalt_iff_highLevel_acceleration`,
  `acceleration_iff_highLevel_acceleration`, and A6 `is_not_halt` across
  the 89 machines) with `sorry`.

Comparator exports both the challenge module (`Challenge` or `BusyBeaverChallenge`) and the
solution module (`Cryptids` or `BusyBeaver`) via `leanexport`, verifying in a Bubblewrap sandbox
that:
1. Every target theorem and all of its transitive definition dependencies match identically between
   the challenge module and the solution module.
2. Only the permitted axioms for that configuration are used:
   - **`["propext", "Quot.sound"]` (strictly constructive — no `Classical.choice`):** enforced on
     [`constructive.json`](./constructive.json), [`goldbach_21.json`](./goldbach_21.json),
     [`zf_380.json`](./zf_380.json), and [`riemann_104.json`](./riemann_104.json), covering all
     three ZF machine-to-proof-search equivalences (`halts_zf393_iff_zfInconsistent`,
     `Zf380.Semantics.halts_candidate_iff_zfInconsistent`,
     `halts_zf432_iff_wadeZFInconsistent`), first-order `PA` consistency and $\Sigma_1^0$
     adequacy (`not_paProvable_false`, `paHalts_holds_iff_halts`,
     `paZFInconsistent_holds_iff_zfInconsistent`), the direct simulation reductions (`Goldbach21`,
     `Zf380`, `Riemann104`), and all four `candidate_fewer_states` theorems (13 theorems total).
     Disallowing `Classical.choice` blocks classical `Con(ZF)` shortcuts (`not_zfInconsistent` in
     `ZFSet.{0}` or `Classical.em` + `digama0/ConZF`) for `Halts M ↔ ZFInconsistent`, while deeply
     embedded `PAProvable` provides a weak first-order metatheory strictly below `ZF` (see
     [`Cryptids/Semantics/README.md`](../Cryptids/Semantics/README.md#foundational-note-conzf-in-lean-and-constructive-equivalence)).
   - **`["propext", "Quot.sound", "Classical.choice"]`:** allowed in [`all.json`](./all.json),
     [`busy_beaver.json`](./busy_beaver.json), and the classical model-theoretic / arithmetic-stage /
     analytic configs (`pa_semantics.json`, `zf_393.json`, `zf_semantics.json`,
     `goldbach_semantics.json`, `riemann_95.json`, `riemann_120.json`, `riemann_semantics.json`).
3. The exported proof terms are accepted by the Lean default kernel.

## Configurations

| Config File | Challenge Module | Solution Module | Permitted Axioms | Verified Theorems |
| :--- | :--- | :--- | :--- | :--- |
| [`constructive.json`](./constructive.json) | `Challenge` | `Cryptids` | `propext`, `Quot.sound` | All 13 constructive theorems: all 3 ZF proof-search equivalences (`zf_393`, `zf_380`, `zf_432`), first-order `PA` consistency & $\Sigma_1^0$ adequacy (`not_paProvable_false`, `paHalts_holds_iff_halts`, `paZFInconsistent_holds_iff_zfInconsistent`), direct state reductions (`Goldbach21`, `Zf380`, `Riemann104`), and `Riemann95.candidate_fewer_states` |
| [`all.json`](./all.json) | `Challenge` | `Cryptids` | `propext`, `Quot.sound`, `Classical.choice` | All 29 conjecture-checking state-reduction, equivalence, `PA` metatheory & internalized `ZF` provability, and semantics theorems |
| [`pa_semantics.json`](./pa_semantics.json) | `Challenge` | `Cryptids.Semantics.PA` | `propext`, `Quot.sound`, `Classical.choice` | `not_paProvable_false`, `paHalts_holds_iff_halts`, `paZFInconsistent_holds_iff_zfInconsistent`, `paProvable_sound_nat`, `paProvable_halts_zf380_iff_zf393`, `paProvable_halts_zf393_iff_zfInconsistent`, `paProvable_halts_zf380_iff_zfInconsistent` |
| [`busy_beaver.json`](./busy_beaver.json) | `BusyBeaverChallenge` | `BusyBeaver` | `propext`, `Quot.sound`, `Classical.choice` | All 425 `BB(6)` and `BB(3, 3)` holdout theorems: Level A and Level B reductions (`is_closed_pattern_set`, `has_collatz_reduction`, `is_closed_stack_pattern_set`, `has_stacked_collatz_reduction`, `has_stack_reduction`, `has_odometer_reduction`, `has_transducer_reduction`, `is_valid_acceleration`, `isHalt_iff_acceleration`, `is_valid_highLevel_acceleration`, `isHalt_iff_highLevel_acceleration`, `acceleration_iff_highLevel_acceleration`) and A6 `is_not_halt` |
| [`a6.json`](./a6.json) | `BusyBeaverChallenge` | `BusyBeaver.BB6.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH` | `propext`, `Quot.sound`, `Classical.choice` | A6 `is_not_halt` |
| [`goldbach_21.json`](./goldbach_21.json) | `Challenge` | `Cryptids.Goldbach21` | `propext`, `Quot.sound` | `candidate_fewer_states`, `candidate_equivalent` |
| [`goldbach_semantics.json`](./goldbach_semantics.json) | `Challenge` | `Cryptids.Semantics.Goldbach` | `propext`, `Quot.sound`, `Classical.choice` | `halts_reference_iff_not_goldbach`, `halts_candidate_iff_not_goldbach` |
| [`zf_380.json`](./zf_380.json) | `Challenge` | `Cryptids.Zf380` | `propext`, `Quot.sound` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_393.json`](./zf_393.json) | `Challenge` | `Cryptids.Semantics.Zf393` | `propext`, `Quot.sound`, `Classical.choice` | `halts_zf393_iff_zfInconsistent`, `not_halts_zf393`, `halts_candidate_iff_zfInconsistent`, `not_halts_candidate` |
| [`zf_semantics.json`](./zf_semantics.json) | `Challenge` | `Cryptids.Semantics.Zf` | `propext`, `Quot.sound`, `Classical.choice` | `zfProvable_sound_zfSet`, `not_zfInconsistent`, `halts_zf432_iff_wadeZFInconsistent` |
| [`riemann_104.json`](./riemann_104.json) | `Challenge` | `Cryptids.Riemann104` | `propext`, `Quot.sound` | `candidate_fewer_states`, `candidate_equivalent` |
| [`riemann_95.json`](./riemann_95.json) | `Challenge` | `Cryptids.Semantics.Riemann95` | `propext`, `Quot.sound`, `Classical.choice` | `candidate_fewer_states`, `candidate_equivalent`, `halts_candidate_iff_not_riemannHypothesis` |
| [`riemann_120.json`](./riemann_120.json) | `Challenge` | `Cryptids.Semantics.Riemann120` | `propext`, `Quot.sound`, `Classical.choice` | `halts_riemann120_iff_not_riemannHypothesis`, `halts_candidate_iff_not_riemannHypothesis` |
| [`riemann_semantics.json`](./riemann_semantics.json) | `Challenge` | `Cryptids.Semantics.Riemann` | `propext`, `Quot.sound`, `Classical.choice` | `halts_riemann744_iff_exists_counterexample`, `halts_riemann744_iff_not_riemannHypothesis` |

The focused [`a6.json`](a6.json) configuration checks the A6 `IsNotHalt`
theorem against `BusyBeaverChallenge`, using only its machine module as the
solution import. It uses the same three-axiom policy as the full Busy Beaver
configuration.

## Usage

From the repository root (with `bwrap` installed):

```bash
lake exe cache get
lake comparator --config comparator/constructive.json
lake comparator --config comparator/all.json
lake comparator --config comparator/busy_beaver.json
```
