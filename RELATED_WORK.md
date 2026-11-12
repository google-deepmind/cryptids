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
- **Erdős's ternary conjecture (`erdos_ternary_15`, `erdos_ternary_14`):** Tristan Stérin and Damien Woods's 15-state machine (2021) and Tristan Stérin's 14-state machine (Oct 2026), with Lean 4 semantics proofs in this repository.
- **Brocard's problem (`brocard_28`):** a new 28-state machine (Nov 2026) with Lean 4 semantics proofs, after Charlie Reams's 61-state machine (Nov 2026) and a 43-state table without a machine-checked proof (May 2026).
- **Oppermann's conjecture (`oppermann_22`):** a new 22-state machine (Nov 2026) with Lean 4 semantics proofs, built on the primality test of `goldbach_21`, after Joseph Jabbour and Ralph Razzouk's 28-state machine (Sep 2026) and Charlie Reams's 45-state machine (Nov 2026).

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

### 4. Erdős's Ternary Conjecture (`erdos_ternary`)

`erdos_ternary_15` doubles a base-3 number on the tape and halts at the fourth power `2 ^ n` without a digit `2` in base `3` (counting `2 ^ 0`); `erdos_ternary_14` keeps `2 ^ n` in unary, reads its base-3 digits by repeated division by `3`, and halts at the third such power (counting from `2 ^ 1`). The conjecture (Erdős, 1979) is that `2 ^ 0`, `2 ^ 2`, and `2 ^ 8` are the only such powers.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2021 | Tristan Stérin & Damien Woods ([`arXiv:2107.12475`](https://arxiv.org/abs/2107.12475), [`tcosmo/bbsim`](https://github.com/tcosmo/bbsim) `machines/powers_of_two_15_2.txt`) | `15` | 5-state, 4-symbol machine (reverse-ternary doubling, scan for a `2`, counter of exceptions) compiled to 2 symbols (`0 → ba`, `1 → ab`, `2 → aa`, `# → bb`) | Pen-and-paper proof in the paper; Lean 4 proofs in this repo by Daniel Veljjanoski, with Claude (Anthropic) as assistant ([`Cryptids/ErdosTernary15.lean`](Cryptids/ErdosTernary15.lean), [`Cryptids/Semantics/ErdosTernary15.lean`](Cryptids/Semantics/ErdosTernary15.lean)) |
| 2026 | Tristan Stérin ([bbchallenge Discord](https://discord.com/channels/960643023006490684/1561295445312151622/1562203343114473472), Oct 2026; [Cryptids wiki](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&oldid=9722)) | `14` | Keeps `2 ^ n` in unary and reads its base-3 digits by repeated division by `3`, with one `0` marking the quotient; doubles the block in place and counts exceptions | Lean 4 proofs in this repo by Daniel Veljjanoski, with Claude (Anthropic) as assistant ([`Cryptids/ErdosTernary14.lean`](Cryptids/ErdosTernary14.lean), [`Cryptids/Semantics/ErdosTernary14.lean`](Cryptids/Semantics/ErdosTernary14.lean)) |

### 5. Brocard's Problem (`brocard`)

Enumerates `n = 8, 9, …` and halts if and only if `n! + 1` is a perfect square for some such `n`, i.e. if Brocard's problem (Brocard 1876, 1885; Ramanujan 1913) has a solution beyond `n = 4, 5, 7`. Erdős conjectured that there is none; none exists for `n ≤ 10^12` (Matson 2017). `brocard_28` keeps `n! / 8` in unary, since `n! + 1 = m^2` forces `m = 2k + 1` and `n! / 8 = k (k + 1) / 2`, and tests it for triangularity by subtracting `1, 2, 3, …`. William Gasarch's SIGACT News Open Problems Column ([vol. 57, no. 3, Sept 2026](https://doi.org/10.1145/3848065.3848068), Open Problem 6.2) asks to improve the 43-state count and reports Jonathan Brown's conjecture that about 30 states may suffice; `brocard_28` improves the count to 28.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2026 | Gurpreet Tandi, Josue Gonzalez-Hendrix & Jonathan Brown ([`arXiv:2605.20215`](https://arxiv.org/abs/2605.20215), May 2026) | `≤ 43` (claimed) | Unary factorial, square test by subtracting odd numbers; the state count is an upper bound obtained by merging states, with the table in the appendix | None |
| 2026 | Charlie Reams ([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids) `brocard/`, Nov 2026) | `61` | 98-state hand design (unary factorial by copying, odd-number square test, 7-round warm-up) merged to 61 states by exact SAT | Lean 4 proof in `tinycryptids` (`TM.Brocard.M61.halts_iff`, core Lean) |
| 2026 | Daniel Veljjanoski, with Claude (Anthropic) as assistant (`brocard_28`) | `28` | Triangularity test of `n! / 8` with a free `+1` per wrap (the blank beyond the chunk block acts as its hole), in-place multiply with the counter grown by one cell at each round start, a residue gate (`n! / 8 ≡ 0 (mod 4)` exactly for `n ≥ 8`) as the warm-up gate, and a one-state start through the loop's never-read cells | Lean 4 proofs ([`Cryptids/Brocard28.lean`](Cryptids/Brocard28.lean), [`Cryptids/Semantics/Brocard28.lean`](Cryptids/Semantics/Brocard28.lean)) |

### 6. Oppermann's Conjecture (`oppermann`)

Tests `0, 1, 2, …` for primality along the blocks between consecutive quarter-squares `⌊j²/4⌋` (a block is a half-interval of the conjecture together with its first number, which is not prime) and halts if and only if Oppermann's conjecture is false: some `n ≥ 2` has no prime strictly between `n^2 - n` and `n^2`, or none strictly between `n^2` and `n^2 + n`.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2026 | Joseph Jabbour and Ralph Razzouk ([`ralphrazzouk/busybeaver`](https://github.com/ralphrazzouk/busybeaver/tree/master/problems/oppermann) `problems/oppermann/`, Sep 2026) | `29` → `28` | Hand design: the 18-state primality test of the 25-state Goldbach machine, a count of the numbers left in the interval that halts at zero, a jump to the next interval at the first prime, and a copy loop that rebuilds the count (one cell per two cells of a growing block); 28 states by identifying two states that are never read on the same symbol and a new start | Lean 4 proofs with Mathlib in `busybeaver` (`BBRank.Oppermann29.halts_iff_not_oppermann`, `BBRank.Oppermann28.halts_iff_not_oppermann`) |
| 2026 | Charlie Reams ([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids/tree/main/oppermann) `oppermann/`, Nov 2026) | `45` | 74-state hand design reduced to 45 states by exact SAT state merging: trial division by a mod walk, an interval register whose hole moves two cells per number and that grows by one cell per interval, a flag set by a prime | Lean 4 proof in `tinycryptids` (`TM.Oppermann.M45.halts_iff`) |
| 2026 | Daniel Veljjanoski, with Claude (Anthropic) as assistant (`oppermann_22`) | `22` | The trial-division test of `goldbach_21` (16 of its states, 7 cells changed) and six more states: a walker area of `j - 1` ones whose hole moves two cells per number, a flag set by the first prime of the block, a halt when the hole reaches the left end with the flag clear (one number later for blocks of even index); no rebuild between blocks, and the start runs through the loop's own states | Lean 4 proofs ([`Cryptids/Oppermann22.lean`](Cryptids/Oppermann22.lean), [`Cryptids/Semantics/Oppermann22.lean`](Cryptids/Semantics/Oppermann22.lean)) |
