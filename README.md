# Cryptids: Formally Verified Conjecture-Checking & Busy Beaver Turing Machines

This repository contains two Lean 4 (`v4.35.0-rc4`) formalization libraries for small Turing machines whose halting behavior encodes deep mathematical problems or complex dynamical invariants:

1. **[Conjecture-Checking Turing Machines (`Cryptids/`)](Cryptids/README.md)** — Certified state reductions (`goldbach_21`, `zf_380`, `riemann_95`) and end-to-end Lean 4 mathematical semantics proofs (`Halts M ↔ ...`) for **Goldbach's Conjecture**, **ZF Set Theory Consistency**, the **Riemann Hypothesis**, and **Erdős's conjecture on powers of two**.
2. **[Busy Beaver Holdouts (`BusyBeaver/`)](BusyBeaver/README.md)** — Kernel-verified behavioral proofs (`IsHalt`, `IsNotHalt`, `HasCollatzReduction`, `HasStackedCollatzReduction`, `IsValidAcceleration`) for **Busy Beaver 6 (`BB(6)`)** and **Busy Beaver (3, 3) (`BB(3, 3)`)** holdouts—covering both community-documented machines and novel Collatz-like accelerations discovered via the autonomous agentic pipeline of [*At the Limits of Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver Frontier*](https://arxiv.org/abs/2610.22603) (some are potential Cryptids, subject to community acceptance)—connected to `ConjectureMachines.Machine` via [`BusyBeaver/Bridge.lean`](BusyBeaver/Bridge.lean).

## Overview

| Library | Scope | Key Results | Documentation |
| :--- | :--- | :--- | :--- |
| [`Cryptids/`](Cryptids/) | `(Q, 2)` Turing machines for Goldbach, ZF consistency, the Riemann Hypothesis, and Erdős's conjecture on powers of two | Certified state reductions (`25 → 21`, `393 → 380`, `120 → 104 → 95`) and end-to-end halting equivalences (`Halts M ↔ ¬ GoldbachConjecture`, `ZFInconsistent`, `¬ RiemannHypothesis`, `¬ ErdosPowersOfTwoConjecture`) | [`Cryptids/README.md`](Cryptids/README.md), [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md) |
| [`BusyBeaver/`](BusyBeaver/) | `BB(6)` `(6, 2)` and `BB(3, 3)` `(3, 3)` holdout Turing machines (some are potential Cryptids, subject to community acceptance) | Shared execution semantics (`BusyBeaver/Defs.lean`), foundational lemmas (`BusyBeaver/Basic.lean`), RLE loader and `ConjectureMachines` bridge (`BusyBeaver/Bridge.lean`), and certified behavioral proofs in [`BusyBeaver/BB6/`](BusyBeaver/BB6/README.md) (53 machines) and [`BusyBeaver/BB33/`](BusyBeaver/BB33/README.md) (6 machines) | [`BusyBeaver/README.md`](BusyBeaver/README.md), [`BusyBeaver/BB6/README.md`](BusyBeaver/BB6/README.md), [`BusyBeaver/BB33/README.md`](BusyBeaver/BB33/README.md) |

All Lean 4 proofs are checked by the kernel without `sorry` and depend only on standard Lean axioms:
- **Constructive (`["propext", "Quot.sound"]`, no `Classical.choice`):** All ZF machine-to-proof-search equivalences (`halts_zf393_iff_zfInconsistent`, `Zf380.Semantics.halts_candidate_iff_zfInconsistent`, `halts_zf432_iff_wadeZFInconsistent`), the direct simulation state reductions ([`Goldbach21.lean`](Cryptids/Goldbach21.lean), [`Zf380.lean`](Cryptids/Zf380.lean), [`Riemann104.lean`](Cryptids/Riemann104.lean)), and all four `candidate_fewer_states` theorems, audited in CI via [`comparator/constructive.json`](comparator/constructive.json). Because classical Lean (`ZFSet.{0}` in [`Soundness.lean`](Cryptids/Semantics/Zf/Soundness.lean)) proves `¬ ZFInconsistent`—so any non-halting machine would vacuously satisfy `Halts M ↔ ZFInconsistent` under `Classical.choice`—excluding `Classical.choice` blocks classical `Con(ZF)` shortcuts and ensures the Lean proof-search correspondence is constructive (while internalizing the reduction inside `PA`/`ZF` and establishing both directions of `ZF`-independence are separate metamathematical steps; see [Foundational Note on `Con(ZF)` and Constructive Equivalence](Cryptids/Semantics/README.md#foundational-note-conzf-in-lean-and-constructive-equivalence)).
- **Classical (`["propext", "Classical.choice", "Quot.sound"]`):** Set-theoretic soundness and non-halting in `ZFSet.{0}` (`zfProvable_sound_zfSet`, `not_zfInconsistent`, `not_halts_zf393`, `not_halts_candidate`), negated-$\Pi_1^0$ Goldbach equivalence (`¬ GoldbachConjecture`, which uses Markov's Principle), the arithmetic-stage `riemann_95` reduction (`Nat.Prime`), complex-analytic `RiemannHypothesis` equivalences, the `erdos_15` equivalences (`Nat.digits`, and Markov's Principle for `¬ ErdosPowersOfTwoConjecture`), and the `BB(6)` and `BB(3, 3)` holdout reductions, audited via [`comparator/all.json`](comparator/all.json) and [`comparator/busy_beaver.json`](comparator/busy_beaver.json).

The [95-state Riemann machine](artifacts/riemann_95/README.md) has a kernel-checked
blank-tape halting equivalence to the 104-state machine and to `¬ RiemannHypothesis`.
Its transition table, complete 3,634-step initializer, and proof guide are included.

## Building and Verifying

Fetch the precompiled Mathlib cache:

```bash
lake exe cache get
```

Build the conjecture-checking library (`Cryptids` and `Challenge`, default targets) and audit with [`leanprover/comparator`](comparator/README.md):

```bash
lake build
lake comparator --config comparator/constructive.json
lake comparator --config comparator/all.json
python3 verify.py
```

Build the Busy Beaver library (`BusyBeaver` and `BusyBeaverChallenge`) and audit with [`leanprover/comparator`](comparator/README.md):

```bash
lake build BusyBeaver BusyBeaverChallenge
lake comparator --config comparator/busy_beaver.json
```

## Repository Structure

- [`Cryptids/`](Cryptids/README.md) — Conjecture-checking Turing machines ([`Machines.lean`](Cryptids/Machines.lean), [`Propositions.lean`](Cryptids/Propositions.lean)), state-reduction proofs ([`Goldbach21.lean`](Cryptids/Goldbach21.lean), [`Zf380.lean`](Cryptids/Zf380.lean), [`Riemann95.lean`](Cryptids/Riemann95.lean)), and end-to-end mathematical semantics ([`Cryptids/Semantics/`](Cryptids/Semantics/README.md)).
- [`BusyBeaver/`](BusyBeaver/README.md) — Busy Beaver holdout specifications ([`Defs.lean`](BusyBeaver/Defs.lean)), foundational lemmas ([`Basic.lean`](BusyBeaver/Basic.lean)), RLE loader and bridge to `ConjectureMachines` ([`Bridge.lean`](BusyBeaver/Bridge.lean)), and machine behavioral proofs.
- [`Challenge.lean`](Challenge.lean), [`BusyBeaverChallenge.lean`](BusyBeaverChallenge.lean) & [`comparator/`](comparator/) — Self-contained target theorem specifications and configuration files for [`leanprover/comparator`](comparator/README.md).
- [`artifacts/`](artifacts/) — Canonical `machine.txt` transition tables and reduction write-ups for [`goldbach_21`](artifacts/goldbach_21/README.md), [`zf_380`](artifacts/zf_380/README.md), [`riemann_104`](artifacts/riemann_104/README.md), and [`riemann_95`](artifacts/riemann_95/README.md).
- [`baselines/`](baselines/) — Verbatim upstream source files, canonical 5-tuple tables, and [`PROVENANCE.md`](baselines/PROVENANCE.md).
- [`RELATED_WORK.md`](RELATED_WORK.md) — Literature lineage and `(Q, 2)` Turing machine conventions.
- [`verify.py`](verify.py) — Standalone Python 3 verification script for the conjecture-checking machines.

## Contributing

Pull requests and issues are welcome, especially for smaller Turing machines for these problems, machines for other conjectures, Busy Beaver holdout proofs, or streamlined Lean proofs. Please also open an issue if you notice anything amiss, such as a missing reference or provenance detail. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for general guidelines.

## Acknowledgements

We thank Eric Wieser for careful review, as well as the Busy Beaver Challenge community, `int-y1` (whose `BusyLean` project pioneered Lean 4 Busy Beaver formalizations and directed-head configuration representations), Yijun Leng, Stefan O'Rear, Yuri Matiyasevich, Scott Aaronson, Adam Yedidia, Andrew Wade, Joseph Shunia, Tristan Stérin, and Damien Woods for the baseline Turing machines and compilers, and the Mathlib community.

## License and disclaimer

Copyright 2026 Google LLC

All software is licensed under the Apache License, Version 2.0 (Apache 2.0);
you may not use this file except in compliance with the Apache 2.0 license.
You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY licenses are
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.
