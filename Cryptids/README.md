# Certified State Reductions and Semantics of Conjecture-Checking Turing Machines (`Cryptids/`)

This library contains formally verified 2-symbol Turing machines and Lean 4 semantics proofs for **Goldbach's Conjecture**, **ZF Set Theory Consistency**, and the **Riemann Hypothesis**, developed by Maxence Faldor and Moritz Firsching using Gemini Argon.

## Formalized Machines

| Conjecture | Machine | States | Source / Provenance | Proved Halting Condition (`Halts M ↔ ...`) | Lean 4 Proofs |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Goldbach's Conjecture | `goldbach_21` | `21` | Reduced from `goldbach_25` (`25` states, Yao / Leng 2024) | `¬ GoldbachConjecture` | [`Goldbach21.lean`](./Goldbach21.lean), [`Semantics/Goldbach.lean`](./Semantics/Goldbach.lean) |
| ZF Consistency | `zf_380` | `380` | Reduced from `zf_393` (`393` states, Wade Aug 2026) | `ZFInconsistent` (`¬ Halts candidate` proved) | [`Zf380.lean`](./Zf380.lean), [`Semantics/Zf393.lean`](./Semantics/Zf393.lean) |
| ZF Consistency | `zf_393` | `393` | Andrew Wade ([`turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer) `9c5c2e82`, Aug 2026) | `ZFInconsistent` (`¬ Halts zf393` proved) | [`Zf393.lean`](./Zf393.lean), [`Semantics/Zf393.lean`](./Semantics/Zf393.lean) |
| ZF Consistency | `zf_432` | `432` | Andrew Wade ([`turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer) `33b30300`, Aug 2025) | `WadeZFInconsistent` | [`Semantics/Zf.lean`](./Semantics/Zf.lean) |
| Riemann Hypothesis | `riemann_95` | `95` | Retained stage counter and proved operand-bank permutation | `¬ RiemannHypothesis` | [`Riemann95.lean`](./Riemann95.lean), [`Semantics/Riemann95.lean`](./Semantics/Riemann95.lean) |
| Riemann Hypothesis | `riemann_104` | `104` | Reduced from `riemann_120` (`120` states, Shunia Sept 2026) | `¬ RiemannHypothesis` | [`Riemann104.lean`](./Riemann104.lean), [`Semantics/Riemann120.lean`](./Semantics/Riemann120.lean) |
| Riemann Hypothesis | `riemann_120` | `120` | Joseph M. Shunia ([`arXiv:2609.30306`](https://arxiv.org/abs/2609.30306), Sept 2026) | `¬ RiemannHypothesis` | [`Riemann120.lean`](./Riemann120.lean), [`Semantics/Riemann120.lean`](./Semantics/Riemann120.lean) |
| Riemann Hypothesis | `riemann_744` | `744` | Matiyasevich, O'Rear & Aaronson (`riemann_744_sorear.tm`, 2016) | `¬ RiemannHypothesis` | [`Semantics/Riemann.lean`](./Semantics/Riemann.lean) |

See [`RELATED_WORK.md`](../RELATED_WORK.md) for the historical progression across each domain.

## What Is Formally Proved

All proofs in [`Cryptids/`](./) are checked by the Lean 4 kernel (`v4.35.0-rc4`) without `sorry`:

1. **State reductions:** Each reduced machine (`goldbach_21`, `zf_380`, `riemann_104`, `riemann_95`) has fewer states than its reference machine (`goldbach_25`, `zf_393`, `riemann_120`, `riemann_104`) and halts from the blank tape if and only if the reference machine halts ([`Goldbach21.lean`](./Goldbach21.lean), [`Zf380.lean`](./Zf380.lean), [`Riemann104.lean`](./Riemann104.lean), [`Riemann95.lean`](./Riemann95.lean)). The direct simulation reductions (`goldbach_21`, `zf_380`, `riemann_104`) and all four `candidate_fewer_states` theorems are completely constructive (`["propext", "Quot.sound"]`, zero `Classical.choice`), audited via [`comparator/constructive.json`](../comparator/constructive.json), [`comparator/goldbach_21.json`](../comparator/goldbach_21.json), [`comparator/zf_380.json`](../comparator/zf_380.json), and [`comparator/riemann_104.json`](../comparator/riemann_104.json), while [`riemann_95`](./Riemann95.lean) routes through the arithmetic stage predicate `ShuniaCounterexample` (`Nat.Prime`, audited via [`comparator/riemann_95.json`](../comparator/riemann_95.json)).
2. **End-to-end mathematical semantics ([`Cryptids/Semantics/`](./Semantics/README.md)):**
   - **ZF Consistency (`zf_380`, `zf_393`, and `zf_432`):** Both `zf_380` and Wade's 393-state machine `zf_393` (incorporating upstream fix `10fcf152b3`) halt if and only if O'Rear's `zf2.nql` Hilbert system proves $v_0 \in v_0$ (`Halts candidate ↔ ZFInconsistent`, `Halts zf393 ↔ ZFInconsistent`), while `zf_432` halts if and only if the 20-clause deductive system enumerated by `zf_432_wade.tm` derives $v_0 \in v_0$ (`WadeZFInconsistent`). **All three proof-search equivalences are proved constructively in Lean using only `["propext", "Quot.sound"]` (no `Classical.choice`, no Excluded Middle, and no Markov's Principle)** and audited via [`comparator/constructive.json`](../comparator/constructive.json), blocking classical `Con(ZF)` shortcuts via [`Zf/Soundness.lean`](./Semantics/Zf/Soundness.lean) or `Classical.em` (object-level `PA` internalization for `zf_393` and `zf_380` is proved separately below via `PAProvable`, while `zf_432` internalization and establishing full two-way `ZF`-independence remain separate; see [`Semantics/README.md`](./Semantics/README.md#foundational-note-conzf-in-lean-and-constructive-equivalence)). Separately, [`Zf/Soundness.lean`](./Semantics/Zf/Soundness.lean) uses classical `ZFSet.{0}` (`Classical.choice`) to establish `not_zfInconsistent` and deduce unconditional non-halting (`not_halts_zf393`, `not_halts_candidate`) inside Lean's stronger meta-theory.
   - **First-Order Peano Arithmetic (`PAProvable`, [`Semantics/PA.lean`](./Semantics/PA.lean)):** Deeply embeds first-order Peano Arithmetic (`PATerm`, `PAFormula`, `PAProvable`) and $\Sigma_1^0$ encodings `paHalts M` and `paZFInconsistent` in [`Propositions.lean`](./Propositions.lean) and [`Challenge.lean`](../Challenge.lean), proving constructive consistency (`not_paProvable_false`) and constructive standard-model adequacy (`paHalts_holds_iff_halts`, `paZFInconsistent_holds_iff_zfInconsistent`; all three audited without `Classical.choice` in [`comparator/constructive.json`](../comparator/constructive.json)), along with classical standard-model soundness (`paProvable_sound_nat`) and full object-level `PA` proofs that `zf_380` and `zf_393` halt iff `ZF` is inconsistent (`paProvable_halts_zf380_iff_zf393`, `paProvable_halts_zf393_iff_zfInconsistent`, `paProvable_halts_zf380_iff_zfInconsistent`, audited in [`comparator/pa_semantics.json`](../comparator/pa_semantics.json) and [`comparator/all.json`](../comparator/all.json); these three `PAProvable` theorems use `Classical.choice` because they reason in arbitrary `PAModel`s and reflect back to `PAProvable` via internal Gödel–Henkin completeness `paProvable_iff_holdsIn_all_models`).
   - **Goldbach (`goldbach_21` and `goldbach_25`):** Both `goldbach_21` and `goldbach_25` constructively satisfy `Halts M ↔ ∃ w, ¬ HasGoldbachPair (2 * w + 4)` without `Classical.choice` ([`Goldbach21.lean`](./Goldbach21.lean)), and with `Classical.choice` (for Markov's Principle on `¬ ∀ n, ...`) satisfy `Halts candidate ↔ ¬ GoldbachConjecture` ([`Semantics/Goldbach.lean`](./Semantics/Goldbach.lean)).
   - **Riemann Hypothesis (`riemann_95`, `riemann_104`, `riemann_120`, and `riemann_744`):** All four machines (`riemann_95`, `riemann_104`, Shunia's 120-state machine `riemann_120`, and the 744-state machine `riemann_744`) halt if and only if Mathlib's `RiemannHypothesis` is false (`Halts candidate ↔ ¬ RiemannHypothesis`, `Halts riemann120 ↔ ¬ RiemannHypothesis`, and `Halts riemann744 ↔ ¬ RiemannHypothesis`).

Details on the proof architecture and the foundational distinction between constructive proof-search equivalence and meta-theoretic non-halting are in [`Cryptids/Semantics/README.md`](./Semantics/README.md).

The [95-state Riemann construction](../artifacts/riemann_95/README.md) retains the
stage counter in `x` after `FOLD` and permutes physical operand banks. Its proof
covers the entire blank initializer, the safe first stage, and all later stages,
then composes directly with the existing 104-state semantics. See the
[proof guide](./ReductionSupport/Riemann95/README.md) for the layer boundaries.

## Runtime Step Behavior

For the reduced machines in [`artifacts/`](../artifacts/), the state-space transformations affect execution step counts as follows:

- **`goldbach_21` (`339,411` vs. `170,966` steps through `n = 40`, `1.99x`):** Eliminating 4 states (`1, 8, 10, 17`) reverses the partition enumeration to test larger summands first and routes divisor acceptance through the main counter-tape scanner.
- **`zf_380` (`+0.093%` step overhead at `1,000,000` steps; `0` step overhead during `39,753`-step bootstrap):** Eliminating 13 states (`65, 68, 266, 278, 322, 335, 341, 353, 359, 361, 379, 387, 389`) via a 5-cell sliding-window invariant (`validState`) and non-destructive leftward head bounces (`1, 3, 5, 7, 9` steps) preserves 100% bit-exact tape equality after every macro-step.
- **`riemann_104` (`9,037` vs. `89,775,610` bootstrap steps, `9,934.23x` faster initialization; `498,382` vs. `111,294,346` total steps over the first `1,000` register instructions, `223.31x` speedup):** Eliminating 16 states (`120 -> 104`) splits merged scanner state `32` via a 5-cell window invariant (`120 -> 121`), replaces the two-phase `89.8M`-step bootstrap (`-9` states) with a self-bootstrapping header and dynamic on-demand zero padding (`padTotal -> padTotal + 1`), and consolidates return scanners and binary call-stack frames (`mapStack`, `-8` states).
- **`riemann_95` (`3,634` vs. `9,037` bootstrap steps, `2.49x` faster initialization):** Retaining the stage counter after `FOLD` removes the subsequent counter transfer. A permutation of the physical register banks permits the shorter blank initializer. The proof covers its complete tape and all subsequent stages.

## Building and Verifying

Build the `Cryptids` and `Challenge` targets:

```bash
lake exe cache get
lake build
```

Independently audit the proofs against [`Challenge.lean`](../Challenge.lean) with
[`leanprover/comparator`](../comparator/README.md):

```bash
lake comparator --config comparator/constructive.json
lake comparator --config comparator/all.json
```

Run the standalone zero-dependency Python verifier (re-compiles upstream baseline sources, checks SHA-256 digests and transition tables, and simulates `250,000` steps per domain):

```bash
python3 verify.py
```
