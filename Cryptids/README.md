# Certified State Reductions and Semantics of Conjecture-Checking Turing Machines (`Cryptids/`)

This library contains formally verified 2-symbol Turing machines and Lean 4 semantics proofs for **Goldbach's Conjecture**, **ZF Set Theory Consistency**, and the **Riemann Hypothesis**, developed by Maxence Faldor and Moritz Firsching using Gemini Argon. The `erdos_15` and `erdos_14` formalizations (Erdős's conjecture on powers of two) are by Daniel Veljanoski, with Claude (Anthropic) as assistant.

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
| Erdős's conjecture on powers of two | `erdos_14` | `14` | Tristan Stérin ([bbchallenge Discord](https://discord.com/channels/960643023006490684/1561295445312151622/1562203343114473472), Oct 2026; [Cryptids wiki](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&oldid=9722)) | `¬ ErdosPowersOfTwoConjecture` | [`Erdos14.lean`](./Erdos14.lean), [`Semantics/Erdos14.lean`](./Semantics/Erdos14.lean) |
| Erdős's conjecture on powers of two | `erdos_15` | `15` | Tristan Stérin & Damien Woods ([`arXiv:2107.12475`](https://arxiv.org/abs/2107.12475), 2021) | `¬ ErdosPowersOfTwoConjecture` | [`Erdos15.lean`](./Erdos15.lean), [`Semantics/Erdos15.lean`](./Semantics/Erdos15.lean) |

See [`RELATED_WORK.md`](../RELATED_WORK.md) for the historical progression across each domain.

## What Is Formally Proved

All proofs in [`Cryptids/`](./) are checked by the Lean 4 kernel (`v4.35.0-rc4`) without `sorry`:

1. **State reductions:** Each reduced machine (`goldbach_21`, `zf_380`, `riemann_104`, `riemann_95`, `erdos_14`) has fewer states than its reference machine (`goldbach_25`, `zf_393`, `riemann_120`, `riemann_104`, `erdos_15`) and halts from the blank tape if and only if the reference machine halts ([`Goldbach21.lean`](./Goldbach21.lean), [`Zf380.lean`](./Zf380.lean), [`Riemann104.lean`](./Riemann104.lean), [`Riemann95.lean`](./Riemann95.lean), [`Erdos14.lean`](./Erdos14.lean)). The direct simulation reductions (`goldbach_21`, `zf_380`, `riemann_104`), the `erdos_14` reduction, and all five `candidate_fewer_states` theorems are completely constructive (`["propext", "Quot.sound"]`, zero `Classical.choice`), audited via [`comparator/constructive.json`](../comparator/constructive.json), [`comparator/goldbach_21.json`](../comparator/goldbach_21.json), [`comparator/zf_380.json`](../comparator/zf_380.json), and [`comparator/riemann_104.json`](../comparator/riemann_104.json), while [`riemann_95`](./Riemann95.lean) routes through the arithmetic stage predicate `ShuniaCounterexample` (`Nat.Prime`, audited via [`comparator/riemann_95.json`](../comparator/riemann_95.json)).
2. **End-to-end mathematical semantics ([`Cryptids/Semantics/`](./Semantics/README.md)):**
   - **ZF Consistency (`zf_380`, `zf_393`, and `zf_432`):** Both `zf_380` and Wade's 393-state machine `zf_393` (incorporating upstream fix `10fcf152b3`) halt if and only if O'Rear's `zf2.nql` Hilbert system proves $v_0 \in v_0$ (`Halts candidate ↔ ZFInconsistent`, `Halts zf393 ↔ ZFInconsistent`), while `zf_432` halts if and only if the 20-clause deductive system enumerated by `zf_432_wade.tm` derives $v_0 \in v_0$ (`WadeZFInconsistent`). **All three proof-search equivalences are proved constructively in Lean using only `["propext", "Quot.sound"]` (no `Classical.choice`, no Excluded Middle, and no Markov's Principle)** and audited via [`comparator/constructive.json`](../comparator/constructive.json), blocking classical `Con(ZF)` shortcuts via [`Zf/Soundness.lean`](./Semantics/Zf/Soundness.lean) or `Classical.em` (while internalizing the reduction inside `PA`/`ZF` and establishing full `ZF`-independence remain separate from this Lean meta-level correspondence; see [`Semantics/README.md`](./Semantics/README.md#foundational-note-conzf-in-lean-and-constructive-equivalence)). Separately, [`Zf/Soundness.lean`](./Semantics/Zf/Soundness.lean) uses classical `ZFSet.{0}` (`Classical.choice`) to establish `not_zfInconsistent` and deduce unconditional non-halting (`not_halts_zf393`, `not_halts_candidate`) inside Lean's stronger meta-theory.
   - **Goldbach (`goldbach_21` and `goldbach_25`):** Both `goldbach_21` and `goldbach_25` constructively satisfy `Halts M ↔ ∃ w, ¬ HasGoldbachPair (2 * w + 4)` without `Classical.choice` ([`Goldbach21.lean`](./Goldbach21.lean)), and with `Classical.choice` (for Markov's Principle on `¬ ∀ n, ...`) satisfy `Halts candidate ↔ ¬ GoldbachConjecture` ([`Semantics/Goldbach.lean`](./Semantics/Goldbach.lean)).
   - **Erdős's conjecture on powers of two (`erdos_15` and `erdos_14`):** Stérin and Woods's 15-state machine constructively satisfies `Halts erdos15 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n`, where `pw n` is the base-3 digit list of `2 ^ n` computed by repeated doubling ([`Erdos15.lean`](./Erdos15.lean)), and with `Classical.choice` (Mathlib's `Nat.digits`, and Markov's Principle on `¬ ∀ n, ...`) satisfies `Halts erdos15 ↔ ¬ ErdosPowersOfTwoConjecture` ([`Semantics/Erdos15.lean`](./Semantics/Erdos15.lean)). Stérin's 14-state machine `erdos_14` constructively satisfies `Halts erdos14 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` and hence `Halts candidate ↔ Halts reference` against `erdos_15` ([`Erdos14.lean`](./Erdos14.lean)), and `Halts candidate ↔ ¬ ErdosPowersOfTwoConjecture` ([`Semantics/Erdos14.lean`](./Semantics/Erdos14.lean)).
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
- **`erdos_14` (`208,865` vs. `212` steps to reach the stage for `2 ^ 9`; `13,104,473` vs. `322` for `2 ^ 12`):** The saved state costs speed: keeping `2 ^ n` in unary and dividing it by `3` in place makes each stage about `4x` longer than the previous one, while `erdos_15` keeps the base-3 digits and needs only a few dozen steps per stage at this size.

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
