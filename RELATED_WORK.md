# Related Work & Literature Lineage (`RELATED_WORK.md`)

To evaluate the independence of mathematical statements from formal axiomatic systems via the Busy Beaver function $\text{BB}(Q, 2)$, Yedidia and Aaronson (2016) initiated the systematic construction of small, standard 2-symbol deterministic Turing machines whose halting is equivalent to the falsity of major conjectures or the inconsistency of foundational axiom systems.

---

## Cost-Model Convention: Standard `(Q, 2)` Turing Machines

All baselines and candidate reductions in this repository adhere to the standard **Radó / bbchallenge `(Q, 2)` cost model**:
1. **Tape:** Two-way infinite binary tape ($\Gamma = \{0, 1\}$), initialized entirely to the blank symbol $0$.
2. **Initial State:** Deterministic start state $q_0 = 0$.
3. **Transition Function:** Partial function $\delta : \text{Fin}(Q) \times \text{Fin}(2) \to \text{Option}(\text{Fin}(2) \times \{\text{L}, \text{R}\} \times \text{Fin}(Q))$, where `none` (`---`) denotes an immediate halting transition.
4. **Formal Equivalence Requirement:** The candidate machine must satisfy `Halts candidate <-> Halts reference` from the blank tape, proved in Lean 4 using only standard axioms (`Goldbach21`, `Zf380`, and `Riemann104` prove this constructively using only `["propext", "Quot.sound"]` with no `Classical.choice`, while `Riemann95` routes through the arithmetic stage predicate `Nat.Prime` and uses `Classical.choice`). Likewise, for `ZF` consistency (`zf_380`, `zf_393`, `zf_432`), all machine-to-proof-search equivalences (`Halts M <-> ZFInconsistent`) are proved constructively in Lean without `Classical.choice`, blocking classical `Con(ZF)` shortcuts via `Cryptids/Semantics/Zf/Soundness.lean` or `Classical.em` + [`digama0/ConZF`](https://github.com/digama0/ConZF) (see [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md#foundational-note-conzf-in-lean-and-constructive-equivalence) for the distinction between this constructive Lean correspondence, internalizing the reduction inside `PA`/`ZF`, and full `ZF`-independence).

---

## Historical Progression by Domain

Community records for conjecture-checking and ZFC-independent Turing machines are tracked on the Busy Beaver Challenge wiki ([Larger Cryptids](https://wiki.bbchallenge.org/wiki/Cryptids#Larger_Cryptids) and [Logical Independence](https://wiki.bbchallenge.org/wiki/Logical_independence)).

- **Goldbach (`goldbach_21`):** Reduces `goldbach_25` (`25 -> 21` states).
- **ZF Consistency (`zf_380`, `zf_393`, `zf_432`) and Riemann Hypothesis (`riemann_104`, `riemann_120`, `riemann_744`):** Compiler and algorithmic reworks by Andrew Wade (`zf_393`, `393` states for ZF, Aug 2026) and Joseph M. Shunia (`riemann_120`, `120` states for RH, Sept 2026) improved over `zf_432` (`432` states, 2025) and `riemann_744` (`744` states, 2016); `zf_380` (`393 -> 380` states) and `riemann_104` (`120 -> 104` states) further reduce both record baselines. This repository provides Lean 4 end-to-end semantics proofs across all of `goldbach_21`, `goldbach_25`, `zf_380`, `zf_393`, `zf_432`, `riemann_104`, `riemann_120`, and `riemann_744`.
- **Erdős's conjecture on powers of two (`erdos_15`):** Tristan Stérin and Damien Woods's 15-state machine (2021), with Lean 4 semantics proofs in this repository.

### 1. Goldbach's Conjecture (`goldbach`)

Searches even integers $2n \ge 4$ for a counterexample to Goldbach's conjecture (an even integer that cannot be written as the sum of two primes) and halts if and only if a counterexample exists.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2015 | CodeGolf (`user23013` / Aaronson announcement) | `27` | Hand-crafted unary trial-division counterexample search | Informal |
| 2016 | JaredCorduan (`gid3138251`) | `27` | Verified 27-state unary Goldbach machine | Informal |
| 2024 | Andrew Yao & Yijun Leng (`lengyijun/goldbach_tm`, `bbchallenge` wiki) | `25` | Merged initialization and primality test return paths (`goldbach_25`) | Lean 4 proof (`lengyijun/goldbach_tm`) |
| 2026 | Faldor & Firsching, using Gemini Argon (`goldbach_21`) | `21` | `L`-first partition enumeration (`stageCfgE`) + elimination of states `1, 8, 10, 17` | Lean 4 proofs ([`Cryptids/Goldbach21.lean`](Cryptids/Goldbach21.lean), [`Cryptids/Semantics/Goldbach.lean`](Cryptids/Semantics/Goldbach.lean)) |

### 2. Zermelo-Fraenkel Set Theory Consistency (`zf`)

Enumerates deductions in a finite axiomatization of ZF (or metamath `set.mm` / Tarski minimal ZF encoding) and halts if and only if an inconsistency is derived.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2016 | Yedidia & Aaronson (Laconic compiler) | `7,910` | Laconic-compiled register machine for ZF consistency | Compiler pipeline |
| 2016 | Stefan O'Rear (`sorear/metamath-turing-machines`) | `748` | NQL-compiled Metamath `set.mm` verifier | Compiler pipeline |
| 2023 | Riebel | `745` | State-merging pass on O'Rear's 748-state machine | Informal |
| 2024 | Ridenour | `643` | Optimized NQL compilation + dead-branch pruning | Informal |
| 2025 | Andrew Wade ([`ajwade/turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer), commit `33b30300`, `zf_432_wade.tm`) | `432` | Tarski minimal first-order ZF encoding (`zf_432`, `bbchallenge` benchmark) | Lean 4 proofs in this repo ([`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean)) |
| 2026 | Andrew Wade ([`ajwade/turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer), commit `9c5c2e82`, Aug 2026) | `393` | Reworked register microcode (`00` moving marker), run-length dispatch, and axiom-order search (`69` framework + `324` decision DAG) | Lean 4 proofs in this repo ([`Cryptids/Zf393.lean`](Cryptids/Zf393.lean), [`Cryptids/Semantics/Zf393.lean`](Cryptids/Semantics/Zf393.lean)) |
| 2026 | Faldor & Firsching, using Gemini Argon (`zf_380`) | `380` | State reduction of `zf_393` (`393 -> 380`): 5-cell window invariant (`validState`), state merges, and non-destructive leftward bounce excursions (`1..9` steps) | Lean 4 proofs ([`Cryptids/Zf380.lean`](Cryptids/Zf380.lean), [`Cryptids/Semantics/Zf393.lean`](Cryptids/Semantics/Zf393.lean)) |

### 3. Riemann Hypothesis (`riemann`)

Enumerates positive integers $n$ and tests an elementary arithmetic inequality equivalent to the Riemann Hypothesis across all $n \ge 1$.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2016 | Matiyasevich, O'Rear & Aaronson (`riemann_744_sorear.tm`) | `744` | NQL-compiled Matiyasevich–Schoenfeld harmonic-LCM checker (`riemann_744`) | Lean 4 proofs in this repo ([`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean)) |
| 2026 | Joseph M. Shunia ([`arXiv:2609.30306`](https://arxiv.org/abs/2609.30306), Sept 2026) | `120` | 5-register self-sieving recurrence + base-$n$ offset digit count via specialized `TMBuilder` backend | Lean 4 proofs in this repo ([`Cryptids/Riemann120.lean`](Cryptids/Riemann120.lean), [`Cryptids/Semantics/Riemann120.lean`](Cryptids/Semantics/Riemann120.lean)) |
| 2026 | Faldor & Firsching, using Gemini Argon (`riemann_104`) | `104` | State reduction of `riemann_120` (`120 -> 104`): 5-cell window de-merging (`+1`), dynamic-padding self-bootstrap (`-9`), and return-scanner & call-stack consolidation (`-8`) | Lean 4 proofs ([`Cryptids/Riemann104.lean`](Cryptids/Riemann104.lean), [`Cryptids/Semantics/Riemann120.lean`](Cryptids/Semantics/Riemann120.lean)) |
| 2026 | Vladislav Isenbaev, using GPT-6.1 Sol and Aleph Prover (`riemann_95`) | `95` | Retains the stage counter after `FOLD`, permutes the operand banks, and initializes in 3,634 steps | Lean 4 proofs ([`Cryptids/Riemann95.lean`](Cryptids/Riemann95.lean), [`Cryptids/Semantics/Riemann95.lean`](Cryptids/Semantics/Riemann95.lean)); [construction and proof guide](artifacts/riemann_95/README.md) |

### 4. Erdős's Conjecture on Powers of Two (`erdos`)

Doubles a base-3 number on the tape and halts at the fourth power `2 ^ n` without a digit `2` in base `3`; the conjecture (Erdős, 1979) is that `2 ^ 0`, `2 ^ 2`, and `2 ^ 8` are the only such powers.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2021 | Tristan Stérin & Damien Woods ([`arXiv:2107.12475`](https://arxiv.org/abs/2107.12475), [`tcosmo/bbsim`](https://github.com/tcosmo/bbsim) `machines/powers_of_two_15_2.txt`) | `15` | 5-state, 4-symbol machine (reverse-ternary doubling, scan for a `2`, counter of exceptions) compiled to 2 symbols (`0 → ba`, `1 → ab`, `2 → aa`, `# → bb`) | Pen-and-paper proof in the paper; Lean 4 proofs in this repo by Daniel Veljanoski, with Claude (Anthropic) as assistant ([`Cryptids/Erdos15.lean`](Cryptids/Erdos15.lean), [`Cryptids/Semantics/Erdos15.lean`](Cryptids/Semantics/Erdos15.lean)) |
