# Formal Semantics of Conjecture Turing Machines (`Cryptids/Semantics/`)

This directory contains formal Lean 4 proofs connecting the Turing machines in `Cryptids/` to the
mathematical conjectures they encode, along with full provenance and attribution for the underlying
constructions.

---

## 1. Goldbach's Conjecture ([`Goldbach.lean`](./Goldbach.lean))

### Main Theorems

In [`Cryptids/Semantics/Goldbach.lean`](./Goldbach.lean), we define Goldbach's
conjecture in standard mathematical terms on top of Mathlib's `Nat.Prime`:

```lean
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q
```

and prove that both the 25-state baseline machine `reference` (`goldbach_25`) and the 21-state
compressed machine `candidate` (`goldbach_21`) halt on the blank tape if and only if Goldbach's
conjecture is false:

```lean
theorem halts_reference_iff_not_goldbach :
    Halts reference ↔ ¬ GoldbachConjecture

theorem halts_candidate_iff_not_goldbach :
    Halts candidate ↔ ¬ GoldbachConjecture
```

### Provenance and Attribution

1. **Original 27-state (26-state reachable) Goldbach Turing machine (2016)**
   - **Author**: Anonymous (`gist.github.com/anonymous/a64213f391339236c2fe31f8749a0df6`),
     popularized by Scott Aaronson and the Busy Beaver Challenge community
     ([bbchallenge Cryptids wiki](https://wiki.bbchallenge.org/wiki/Cryptids)).
2. **25-state optimization and first Lean 4 verification (`goldbach_25`, 2024)**
   - **Author**: Yijun Leng ([`github.com/lengyijun/goldbach_tm`](https://github.com/lengyijun/goldbach_tm), Apache-2.0 License).
   - Yijun Leng compressed the 26-state machine to 25 states (`goldbach_25`, which is the
     `reference` machine in [`Cryptids/Goldbach21.lean`](../Goldbach21.lean)) and gave the first
     Lean 4 formalization proving that the 25-state machine halts iff Goldbach's conjecture is
     false.
3. **21-state reduction and halting-equivalence proof (`goldbach_21`, 2026)**
   - **Authors**: Maxence Faldor and Moritz Firsching, using Gemini Argon ([`Cryptids/Goldbach21.lean`](../Goldbach21.lean)).
   - Compressed the machine to 21 states (`candidate`, eliminating states `1, 8, 10, 17` via
     `L`-first partition enumeration `stageCfgE`) and proved
     `Halts candidate ↔ Halts reference`.
4. **This formalization ([`Cryptids/Semantics/Goldbach.lean`](./Goldbach.lean))**
   - **Authors**: Maxence Faldor and Moritz Firsching, using Gemini Argon.
   - Written from scratch directly on top of the symbolic execution lemmas in
     [`Cryptids/Goldbach21.lean`](../Goldbach21.lean) (no code copied from external repositories),
     proving `Halts reference ↔ ¬ GoldbachConjecture` and combining it with `candidate_equivalent`
     to obtain `Halts candidate ↔ ¬ GoldbachConjecture`.

### Proof Architecture

The proof decomposes the execution of `reference` into five layers:

1. **Canonical Configurations (`cfg0`, `cfg6`, `cfg11`, `cfgExit`)**:
   Represents the machine's unary tape state at the four checkpoints of each primality test and
   partition search.
2. **Inner Division Loop (`cfg11_drain`)**:
   Shows that State `11` drains the remaining unary block `r` while maintaining the counter sum
   `A + B = k + 1` and the divisibility invariant `(k + 2) ∣ B + m + 2`, deciding whether the
   trial divisor `d = k + 2` divides `p = k + 4 + r'`.
3. **Trial Division Loop (`cfg6_eval`)**:
   By induction on `r`, proves that State `6` reaches `cfgExit` with boolean flag
   `decide (NoFactorFrom k (k + 3 + r))`.
4. **Primality Test (`cfg0_eval`)**:
   Combines `p = 1`, `p = 2`, and `p ≥ 3` with Mathlib's `Nat.prime_def_lt'` to prove that
   `cfg0 is_right q p` reaches `cfgExit is_right (decide (Nat.Prime p)) q p`.
5. **Goldbach Partition Search & Multi-Stage Equivalence (`stage_advance`, `stage_halt`)**:
   Shows that stage `w` (`stageCfg w = cfg0 true (2 * w + 2) 1`, testing partitions of `2 * w + 4`)
   advances to `stageCfg (w + 1)` if `2 * w + 4` is a sum of two primes, and halts at State `19`
   otherwise.

---

## 2. Riemann Hypothesis ([`Riemann.lean`](./Riemann.lean) & [`Riemann/`](./Riemann/))

### Main Theorems

In [`Cryptids/Semantics/Riemann.lean`](./Riemann.lean) and its submodules under
[`Cryptids/Semantics/Riemann/`](./Riemann/), together with [`Cryptids/Semantics/Riemann120.lean`](./Riemann120.lean),
we connect the 744-state baseline machine (`riemann_744`), Shunia's 120-state machine
(`riemann_120`), and its 104-state reduction (`riemann_104`) to Mathlib's `RiemannHypothesis`
(`Mathlib.NumberTheory.LSeries.RiemannZeta`):

```lean
theorem halts_riemann744_iff_exists_counterexample :
    ConjectureMachines.Halts Machines.riemann744 ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x

theorem exists_counterexample_iff_not_riemannHypothesis :
    (∃ x : ℕ, MatiyasevichRiemannCounterexample x) ↔ ¬ RiemannHypothesis

theorem halts_riemann744_iff_not_riemannHypothesis :
    ConjectureMachines.Halts Machines.riemann744 ↔ ¬ RiemannHypothesis

theorem halts_riemann120_iff_not_riemannHypothesis :
    Halts riemann120 ↔ ¬ RiemannHypothesis

theorem halts_candidate_iff_not_riemannHypothesis :
    Halts ConjectureMachines.Riemann104.candidate ↔ ¬ RiemannHypothesis
```

The [95-state reduction](../Riemann95.lean) has the same unconditional criterion:

```lean
-- ConjectureMachines.Riemann95.Semantics
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts ConjectureMachines.Riemann95.candidate ↔ ¬ RiemannHypothesis
```

The [proof guide](../ReductionSupport/Riemann95/README.md) explains the changed
stage representation, physical operand permutation, exact blank initializer, and
connection to the existing 104-state theorem.

Here `MatiyasevichRiemannCounterexample (x : ℕ) : Prop` is the elementary integer inequality tested
at stage $x > 253$ by the compiled NQL program `riemann.nql`:

```lean
def harmNum : ℕ → ℕ
  | 0 => 0
  | n + 1 => harmNum n * (n + 1) + n.factorial

def MatiyasevichRiemannCounterexample (x : ℕ) : Prop :=
  253 < x ∧
  let lcm := (Finset.Icc 1 x).lcm id
  let a := (harmNum lcm - lcm.factorial * x) ^ 2
  let b := lcm.factorial ^ 2
  let c := harmNum x ^ 4 * x
  let d := x.factorial ^ 4
  b * c < a * d
```

Over $\mathbb{Q}$ and $\mathbb{R}$, since $\operatorname{harmNum}(n) / n! = H_n = \sum_{k=1}^n 1/k$
(`Mathlib`'s `harmonic n`), the cross-multiplied integer inequality $b \cdot c < a \cdot d$ is
equivalent to (`matiyasevichRiemannCounterexample_iff_harmonic`,
`matiyasevichRiemannCounterexample_iff_sqrt_lt`):

$$x > 253 \;\wedge\; \sqrt{x}\, H_x^2 < H_{\operatorname{lcm}(1, \dots, x)} - x.$$

### Provenance and Attribution

1. **744-state Riemann Hypothesis Turing machine (`riemann_744`, 2016)**
   - **Authors**: Yuri Matiyasevich, Scott Aaronson, and Stefan O'Rear
     ([`sorear/metamath-turing-machines`](https://github.com/sorear/metamath-turing-machines/tree/master/machines/2016-riemann-matiyasevich-aaronson-744),
     `riemann.nql`, `riemann.subs`, and `compiler/framework.py`).
   - Built on Lowell Schoenfeld's explicit bound for Chebyshev's $\psi(x)$ under the Riemann
     Hypothesis ([*Math. Comp.* **30** (1976), 337–360](https://doi.org/10.1090/S0025-5718-1976-0457374-X)),
     Erhard Schmidt's oscillation theorem ([*Math. Ann.* **57** (1903), 195–204](https://doi.org/10.1007/BF01444344)),
     and Jeffrey Lagarias's harmonic-number criterion ([*Amer. Math. Monthly* **109** (2002), 534–543](https://doi.org/10.1080/00029890.2002.11919883)).
2. **This formalization ([`Cryptids/Semantics/Riemann.lean`](./Riemann.lean) & [`Cryptids/Semantics/Riemann/`](./Riemann/))**
   - **Authors**: Maxence Faldor and Moritz Firsching, using Gemini Argon.
   - See also [`Cryptids/Semantics/Riemann120.lean`](./Riemann120.lean) and [`Cryptids/Riemann104.lean`](../Riemann104.lean) for Joseph M. Shunia's 120-state machine (`riemann_120`, 2026) and its 104-state reduction (`riemann_104`).

---

### Proof Architecture

The formalization separates the discrete verification of the 744-state Turing machine and its
16-register NQL program (**Part I**) from the number-theoretic and real-analytic equivalence with
`RiemannHypothesis` (**Part II**).

```
Halts Machines.riemann744 (riemann_744)
  │
  │  Layer 1 + Layer 2: halts_reference_iff_regHalts (0 sorry)
  │  (Cryptids/Semantics/Riemann/Gadgets.lean & Dispatcher.lean)
  ▼
RegHalts (16-register NQL machine, 1,540 active instructions)
  │
  │  Layer 3: regHalts_iff_exists_counterexample
  │  (Cryptids/Semantics/Riemann/RegisterMachine.lean)
  ▼
∃ x : ℕ, MatiyasevichRiemannCounterexample x
  │
  │  Part II: exists_counterexample_iff_not_riemannHypothesis
  │  (Cryptids/Semantics/Riemann/Analytic.lean)
  ▼
¬ RiemannHypothesis (Mathlib.NumberTheory.LSeries.RiemannZeta)
```

#### Part I: Turing Machine ↔ Elementary Counterexample (`halts_reference_iff_exists_counterexample`)

In `compiler/framework.py`, the 744-state machine `reference` (`riemann_744`) simulates a
16-register counter machine with an 11-bit program counter (`0 ≤ pc < 2048`, with active program
`0 ≤ pc ≤ 1539`).

##### Layer 1: Canonical Tape Layout & Primitive Gadgets ([`Riemann/Gadgets.lean`](./Riemann/Gadgets.lean), `0 sorry`s)

1. **Canonical Tape Layout (`entryCfg`, `postPcCfg`)**:
   At State `0` (`!ENTRY`), the tape to the right of the head consists of:
   - An **11-bit binary Program Counter** `pcBits 11 pc` in big-endian order ($b_{10}, b_9, \dots, b_0$).
   - A **two-zero fence** `[0, 0]`.
   - A **bank of unary registers** `regs : List ℕ`, where each register value $r \in \mathbb{N}$ is
     encoded as $r + 1$ ones followed by a single zero delimiter (`encodeReg r = 1^{r+1} ++ [0]`).
   We prove `entryCfg_zero_nil : entryCfg 0 [] = init`, showing that the blank tape `init` is the
   exact canonical entry configuration for `pc = 0` and zero initialized registers (`regs = []`).
2. **Return Scan Gadgets (`return1_scan_regs`, `return2_scan_regs`)**:
   After modifying register $k$, the head returns leftward across registers $k, k-1, \dots, 0$ and
   the `[0, 0]` fence:
   - States `565`/`566` (`return.0`/`return.1`) scan left to State `9` (`dispatch.0.carry`),
     preparing to add $+1$ to `pc`.
   - States `567`/`568` (`return2.0`/`return2.1`) scan left to State `524` (`nextstate_2`), which
     steps over bit $b_0$ to State `11` (`dispatch.1.carry`), preparing to add $+2$ to `pc`.
3. **11-Bit Ripple-Carry PC Adder (`dispatch_from_9_entryCfg`, `dispatch_from_524_entryCfg`)**:
   States `9..29, 12, 13` sweep left across the 11 bits of `pc`, propagating the binary carry bit
   and landing at `entryCfg (pc + 1) regs` (from State `9`) or `entryCfg (pc + 2) regs` (from
   State `524`).
4. **Primitive Register Gadgets (`reg_init_eval`, `reg_incr_eval`, `reg_decr_eval`)**:
   Starting from `postPcCfg q pc regs` (with the head on the first `0` of the `[0, 0]` fence after
   scanning the 11-bit PC):
   - **`reg_init_eval` (`q = 32`)**: Scans right to the first double-zero at the end of `regs`,
     writes `1` to append a new register initialized to `0`, and returns to
     `entryCfg (pc + 1) (regs ++ [0])`.
   - **`reg_incr_eval` (`q = regIncrState k`, $0 \le k < 16$)**: Counts $k$ register-delimiter `0`s
     while shifting the suffix `regs[k..]` right by 1 cell via a 2-state shift gadget
     (`States 569..570`) to insert an extra `1` into register $k$, returning to
     `entryCfg (pc + 1) (regs.set k (regs[k] + 1))`.
   - **`reg_decr_eval` (`q = regDecrState k`, $0 \le k < 16$)**: Counts $k$ register-delimiter `0`s
     to reach register $k$. If `regs[k] = 0` (a single `1` followed by `0`), it leaves the tape
     unchanged and returns via `State 566` to `entryCfg (pc + 1) regs`. If `regs[k] > 0`, it shifts
     the suffix `regs[k..]` left by 1 cell via `States 33..35` (`uninit`) to delete one `1` and
     returns via `State 568` to `entryCfg (pc + 2) (regs.set k (regs[k] - 1))`.

##### Layer 2: BDD Instruction Dispatcher & Halting Simulation ([`Riemann/Dispatcher.lean`](./Riemann/Dispatcher.lean), `0 sorry`s)

1. **Bounded-Window Symbolic Evaluator (`WinState`, `winStep_sound`, `winRunToEntry_sound`)**:
   In `entryCfgR pc R`, the 13 tape cells `0 :: pcBits 11 pc ++ [0, 0]` precede the register tape
   `R : ListBlank (Fin 2)`. Any execution that stays within the first 12 cells (before the second
   `0` of the `[0, 0]` fence) is completely independent of `R`. We formalize a finite-window state
   `WinState` with a 1-step runner `winStep` and prove its soundness for arbitrary `R : ListBlank (Fin 2)`.
2. **Complete 2,048-Entry Instruction Decoder (`program : ℕ → Instr`, `allPcs_valid`)**:
   Decodes the 339-state binary decision tree (`State 0 → 523 → ...`), jump chains (`States 36..183`),
   and `noop` chains (`States 524..532`) into an explicit instruction table `program : ℕ → Instr`
   (`.initReg`, `.incr k`, `.decr k`, `.jump target`, `.halt`), and verifies all 2,048 11-bit PC
   paths via a single kernel `decide` proof (`allPcs_valid`).
3. **Reachable Invariant & Halting Equivalence (`RegInv`, `halts_reference_iff_regHalts`)**:
   Establishes the reachable invariant `RegInv c` (`c.pc < 16 ∧ c.regs.length = c.pc` during register
   allocation, and `16 ≤ c.pc < 1540 ∧ c.regs.length = 16` thereafter) and proves both forward and
   backward halting simulations between `reference` and the abstract 16-register machine (`RegHalts`).

##### Layer 3: Verification of the 16-Register NQL Machine ([`Riemann/RegisterMachine.lean`](./Riemann/RegisterMachine.lean))

Verifies the 1,540-instruction register program compiled from `riemann.nql` (`riemann.subs`):

- **Register Allocation & Bootstrap (`PC 0..38`)**: Allocates 16 registers (`r0..r15`) and initializes
   $x = r_2 = 253$ (`254` at the start of the first main loop iteration).
- **Parametric Arithmetic Subroutines (`0 sorry`s)**:
  - `exec_transfer1`, `exec_transfer2`, `exec_transfer3`: Destructive additive transfers
    $d_i \mathrel{+}= s,\; s \gets 0$.
  - `exec_copy_add`: Non-destructive register addition $d \mathrel{+}= s$ using a temporary register.
  - `exec_mul_loop`: Nested multiplication loop $d_1 \mathrel{+}= s_1 \cdot s_2$.
  - `exec_decr_pair_le`, `exec_decr_pair_gt`: Paired decrement loop comparing two registers.
  - `exec_div_loop`, `exec_sub_loop`: Euclidean division/remainder and saturating subtraction loops.
- **Main Counterexample Search Loop (`PC 38..1539`)**:
  For each $x = 254, 255, \dots$:
  1. Computes $L_x = \operatorname{lcm}(1, \dots, x)$ iteratively via $\operatorname{lcm}(L_{x-1}, x)$
     using trial division (`PC 44..256`).
  2. Unrolls 254 decrements to enforce $x > 253$ (`PC 268..780`).
  3. Computes $\operatorname{harmNum}(L_x)$ and $L_x!$ (`PC 780..946`), then forms
     $a = (\operatorname{harmNum}(L_x) - L_x!\, x)^2$ and $b = (L_x!)^2$ (`PC 946..1104`).
  4. Computes $\operatorname{harmNum}(x)$ and $x!$ (`PC 1104..1274`), then forms
     $c = \operatorname{harmNum}(x)^4 \cdot x$ and $d = (x!)^4$ (`PC 1274..1474`).
  5. Evaluates $b \cdot c < a \cdot d$ (`PC 1474..1539`), halting at `PC = 1539` if the inequality
     holds (`MatiyasevichRiemannCounterexample x`) and looping back to `PC = 38` for $x + 1$
     otherwise.

#### Part II: Elementary Counterexample ↔ Riemann Hypothesis ([`Riemann/Analytic.lean`](./Riemann/Analytic.lean))

1. **Chebyshev's $\psi(x)$ and $\operatorname{lcm}(1, \dots, x)$ (`0 sorry`s)**:
   Using Mathlib's `Chebyshev.psi` and `Nat.log_lcmUpto_eq_sum_mangoldt`, we prove:
   ```lean
   theorem psi_eq_log_lcmUpTo (x : ℕ) :
       Chebyshev.psi (x : ℝ) = Real.log (lcmUpTo x : ℝ)

   theorem exp_psi_eq_lcmUpTo (x : ℕ) :
       Real.exp (Chebyshev.psi (x : ℝ)) = (lcmUpTo x : ℝ)
   ```
2. **Harmonic–Logarithmic & Euler–Mascheroni Reduction (`0 sorry`s)**:
   Using `Mathlib.NumberTheory.Harmonic.Bounds` and `Mathlib.NumberTheory.EulerMascheroni`, we prove:
   - `psi_add_eulerMascheroniConstant_lt_harmonic_lcmUpTo`:
     $\psi(x) + \gamma < H_{\operatorname{lcm}(1, \dots, x)}$ for all $x \ge 1$.
   - `harmonic_lcmUpTo_lt_psi_add_two_thirds`:
     $H_{\operatorname{lcm}(1, \dots, x)} < \psi(x) + \tfrac{2}{3}$ for all $x \ge 254$.
   - `not_matiyasevichRiemannCounterexample_of_schoenfeldPsiBound`:
     Proves with `0 sorry`s that Schoenfeld's bound
     $|\psi(x) - x| \le \sqrt{x}\,(\log x)^2 / (8\pi)$ implies
     `¬ MatiyasevichRiemannCounterexample x` because
     $$H_{L_x} - x < \psi(x) - x + \tfrac{2}{3} < \sqrt{x}\,(\log x)^2 < \sqrt{x}\, H_x^2.$$
   - `matiyasevichRiemannCounterexample_of_sqrt_mul_one_add_log_sq_le_psi_sub`:
     Proves with `0 sorry`s that $\psi(x) - x \ge \sqrt{x}\,(1 + \log x)^2$ for $x > 253$ implies
     `MatiyasevichRiemannCounterexample x` because
     $$\sqrt{x}\, H_x^2 \le \sqrt{x}\,(1 + \log x)^2 \le \psi(x) - x < H_{L_x} - x.$$
3. Analytic number theory — Schmidt's oscillation theorem & Schoenfeld's explicit bound (`0 sorry`s):
   Both classical analytic number theory theorems connecting `RiemannHypothesis` (zeros of $\zeta(s)$)
   to Chebyshev's $\psi(x)$ are fully formalized with **zero `sorry`s**:
   - `not_riemannHypothesis_imp_exists_psi_sub_ge_sqrt_mul_one_add_log_sq`
     ([`Riemann/Schmidt.lean`](./Riemann/Schmidt.lean), `0 sorry`s):
     Formalizes Schmidt's (1903) oscillation theorem via Landau's (1905) real-analytic Mellin
     positivity method (`Mathlib.Analysis.Complex.TaylorSeries`, Tonelli's theorem `lintegral_tsum`,
     and the identity theorem on half-planes `{s : ℂ | σ < s.re}`), showing that if
     `¬ RiemannHypothesis`, there exists $x > 253$ with
     $\psi(x) - x \ge \sqrt{x}\,(1 + \log x)^2$.
   - `riemannHypothesis_imp_schoenfeldPsiBound`
     ([`Riemann/DigammaBinet.lean`](./Riemann/DigammaBinet.lean),
      [`Riemann/HorizontalBounds.lean`](./Riemann/HorizontalBounds.lean),
      [`Riemann/WeightedStieltjes.lean`](./Riemann/WeightedStieltjes.lean),
      [`Riemann/VonMangoldtCount.lean`](./Riemann/VonMangoldtCount.lean), and
      [`Riemann/ExplicitLarge.lean`](./Riemann/ExplicitLarge.lean), `0 sorry`s):
     Proves that under `RiemannHypothesis`, $|\psi(x) - x| \le \sqrt{x}\,(\log x)^2 / (8\pi)$ for all
     $x > 253$ by combining:
     - Unconditional Chebyshev/numeric bounds for $253 < x \le 6000$ (`Analytic.lean`),
     - Binet / Euler–Maclaurin formula for $\psi_0(z) = \Gamma'(z)/\Gamma(z)$ and vertical line
       estimates along $\operatorname{Re}(s) = -1/4$ (`DigammaBinet.lean`),
     - Local zero counting, symmetric zero-free heights, and Borel–Carathéodory + functional
       equation horizontal segment bounds (`HorizontalBounds.lean`),
     - Smoothed Perron integral for $\psi_1(x) = \int_0^x \psi(t)\,dt$, rectangle residue theorem
       on $[-1/4, 2] \times [-U, U]$, and multiplicity-weighted Stieltjes integration by parts
       (`WeightedStieltjes.lean`),
     - Fourth-order Euler–Maclaurin `quarticKernel` identity, zero-free region $|\operatorname{Im}(\rho)| > 6$,
       and Jensen multiplicity bound $N_w(t) \le \frac{16}{5} t \log t + \frac{11}{5} t$ for $t \ge 6$
       (`VonMangoldtCount.lean`), and
     - Large-$x$ explicit assembly for $x \ge 5000$ (`ExplicitLarge.lean`).

---

## 3. ZF Set Theory Consistency ([`Zf.lean`](./Zf.lean) & [`Zf/`](./Zf/), `0 sorry`s)

### Main Theorems

In [`Cryptids/Semantics/Zf.lean`](./Zf.lean) and its six submodules under
[`Cryptids/Semantics/Zf/`](./Zf/) (~7,000 lines total, **zero `sorry`s**), we formalize both:
1. O'Rear's Tarski $S_2$ + Metamath ZF Hilbert system `ZFProvable` (`ZFInconsistent := ZFProvable (zfMem 0 0)`) and its full soundness in Mathlib's cumulative hierarchy `ZFSet.{0}` ([`Zf/Soundness.lean`](./Zf/Soundness.lean)), and
2. The exact 20-clause deductive system `WadeZFProvable` (`WadeZFInconsistent := WadeZFProvable (zfMem 0 0)`) enumerated by Andrew Wade's `zf_432_wade.tm` (`Machines.zf432`), proving with **zero `sorry`s** that the 432-state baseline (`zf_432`) halts on the blank tape if and only if `WadeZFInconsistent` holds, while Wade's August 2026 393-state machine (`zf_393`) and its 380-state reduction (`zf_380`) in [`Cryptids/Semantics/Zf393.lean`](./Zf393.lean) halt if and only if `ZFInconsistent` holds (and hence never halt in `ZFSet.{0}`):

```lean
theorem halts_zf432_iff_wadeZFInconsistent :
    ConjectureMachines.Halts Machines.zf432 ↔ WadeZFInconsistent

theorem halts_zf393_iff_zfInconsistent :
    ConjectureMachines.Halts zf393 ↔ ZFInconsistent

theorem halts_candidate_iff_zfInconsistent :
    Halts ConjectureMachines.Zf380.candidate ↔ ZFInconsistent

theorem zfProvable_sound_zfSet (φ : ZFFormula) (h : ZFProvable φ.code)
    (v : ℕ → ZFSet.{0}) : φ.Holds v

theorem not_zfInconsistent : ¬ ZFInconsistent
```

### Foundational Note: `Con(ZF)` in Lean and Constructive Equivalence

Care is required when interpreting a Lean theorem of type `Halts M ↔ ZFInconsistent`:

1. **Why classical Lean vacuously satisfies `Halts M ↔ ZFInconsistent` for any non-halting machine:**
   Lean's type theory is proof-theoretically stronger than first-order $\mathrm{ZF}$. Using `Classical.choice` and Mathlib's cumulative hierarchy `ZFSet.{0} : Type 1`, [`Zf/Soundness.lean`](./Zf/Soundness.lean) proves `not_zfInconsistent : ¬ ZFInconsistent` inside Lean itself (and deduces `not_halts_zf393` and `not_halts_candidate`). Moreover, as noted by Elliot Glazer and formalized in Lean 4 by Mario Carneiro ([`digama0/ConZF`](https://github.com/digama0/ConZF), *"CIC + EM $\vdash$ Con(ZF): the consistency of ZF in type theory with excluded middle and no choice"*), Lean's Calculus of Inductive Constructions (`CIC`) plus Excluded Middle alone (or `¬¬ ∀ p : Prop, p ∨ ¬p`, via large elimination of `Acc`) proves $\operatorname{Con}(\mathrm{ZF})$ without `Classical.choice`, `propext`, or `Quot.sound`. Consequently, if `Classical.choice` (which yields Excluded Middle together with `propext` and `Quot.sound` by Diaconescu's theorem) or `not_zfInconsistent` is allowed, **any** provably non-halting machine—such as the 1-state machine `0R0 0R0` that moves right forever—vacuously satisfies the bare material biconditional `Halts M ↔ ZFInconsistent` (`False ↔ False`).
2. **Constructive proof-search equivalence (`["propext", "Quot.sound"]` only, enforced by `comparator`):**
   To rule out classical shortcuts through `Classical.choice`, `Classical.em`, or `not_zfInconsistent`, `ConjectureMachines.ListBlank` quotients half-tapes directly via Lean's primitive `Quot (@Turing.BlankRel Γ _)` (`Challenge.lean`, `Cryptids/Machines.lean`), and **the direct state-reduction halting equivalences (`Goldbach21.candidate_equivalent`, `Zf380.candidate_equivalent`, `Riemann104.candidate_equivalent`), the `Erdos14.candidate_equivalent` reduction, all five `candidate_fewer_states` theorems (including `Riemann95.candidate_fewer_states`; `Riemann95.candidate_equivalent` uses `Classical.choice`), and all three ZF machine-to-proof-search equivalences (`Zf393.halts_zf393_iff_zfInconsistent`, `Zf380.Semantics.halts_candidate_iff_zfInconsistent`, `Semantics.Zf.halts_zf432_iff_wadeZFInconsistent`)** are proved **constructively in Lean** using only `["propext", "Quot.sound"]`—with **zero `Classical.choice`, zero Excluded Middle, and zero Markov's Principle**:
   - **Forward completeness (`ZFInconsistent → Halts M`):** Given a finite derivation tree `d : ZFProvable (zfMem 0 0)`, structural induction extracts an explicit step count `s` and halting configuration `c` with `nSteps M s init = some c ∧ step M c = none` (no `by_contra` / unbounded search).
   - **Backward soundness (`Halts M → ZFInconsistent`):** Given `h : Halts M`, constructive induction along `StateTransition.evalInduction'` extracts the finite execution trace from `init` and decodes a valid `ZFProvable (zfMem 0 0)` derivation.
   - **Comparator gate:** [`comparator/constructive.json`](../../comparator/constructive.json), [`comparator/zf_380.json`](../../comparator/zf_380.json), [`comparator/goldbach_21.json`](../../comparator/goldbach_21.json), and [`comparator/riemann_104.json`](../../comparator/riemann_104.json) enforce `"permitted_axioms": ["propext", "Quot.sound"]` in CI, automatically rejecting any proof that invokes `Classical.choice` (including `not_zfInconsistent` in [`Zf/Soundness.lean`](./Zf/Soundness.lean) or `Classical.em` + [`digama0/ConZF`](https://github.com/digama0/ConZF)).
3. **Metamathematical scope — Lean's type theory, `PA`/`ZF` internalization, and `ZF`-independence:**
   Care must also be taken not to conflate a constructive Lean theorem `Halts M ↔ ZFInconsistent` with a formal proof of $\mathrm{ZF}$-independence:
   - **Strength of constructive Lean (`CIC` vs. `PA`/`ZF`):** Even without `Classical.choice` or Excluded Middle, Lean's Calculus of Inductive Constructions provides constructions absent from first-order $\mathrm{PA}$ and $\mathrm{ZF}$—an impredicative `Prop`, inductive families (`ZFProvable`, `Acc`, `PSet`), and a predicative universe hierarchy `Type u` (already strong enough to validate Zermelo set theory, and whether axiom-free `CIC` itself proves $\operatorname{Con}(\mathrm{ZF})$ remains an open question; see [`digama0/ConZF`](https://github.com/digama0/ConZF)). An axiom check in Lean therefore blocks classical `Con(ZF)` shortcuts, rather than restricting reasoning to $\mathrm{PA}$ or $\mathrm{ZF}$.
   - **Internalizing the reduction inside `PA`/`ZF` is separate:** Although our concrete proofs of `ZFInconsistent → Halts M` and `Halts M → ZFInconsistent` proceed by explicit finitary structural and step-indexed induction rather than ambient set-theoretic models, they establish a **meta-level correspondence in Lean**. Internalizing that compiler and trace decoder as an object-level formal theorem inside $\mathrm{PA}$ or $\mathrm{ZF}$ (i.e., proving $\mathrm{ZF} \vdash \ulcorner \operatorname{Halts}(M) \leftrightarrow \neg\operatorname{Con}(\mathrm{ZF}) \urcorner$) is a separate step not formalized in this repository.
   - **Assumptions required for both directions of `ZF`-independence:** Even once $\mathrm{ZF} \vdash \ulcorner \operatorname{Halts}(M) \leftrightarrow \neg\operatorname{Con}(\mathrm{ZF}) \urcorner$ is established, $\operatorname{Con}(\mathrm{ZF})$ alone yields only **one** direction of independence: $\mathrm{ZF} \nvdash \neg\ulcorner\operatorname{Halts}(M)\urcorner$ (by Gödel's Second Incompleteness Theorem). Ruling out the **other** direction, $\mathrm{ZF} \vdash \ulcorner\operatorname{Halts}(M)\urcorner$ (since $\mathrm{ZF} + \neg\operatorname{Con}(\mathrm{ZF})$ can still be consistent when $\mathrm{ZF}$ is consistent), requires $\operatorname{Con}(\mathrm{ZF} + \operatorname{Con}(\mathrm{ZF}))$—for example $\Sigma_1$-soundness ($1$-consistency) of $\mathrm{ZF}$, as assumed in Yedidia & Aaronson (2016).

### Formal Discovery of the `B6a` Register-Restoration Bug in `zf_432_wade.tm`

During the formal verification of `main().0..134` in [`Zf/Subroutines.lean`](./Zf/Subroutines.lean),
we discovered that the baseline Turing machine `baselines/sources/zf_432_wade.tm` was compiled from
Andrew Wade's `zf2.py` prior to his August 31, 2025 bugfix commit `10fcf152b3`
(*"Bugfix for B6a where correct variables were not being restored"*):

- In `zf_432_wade.tm`, `main().n_140.1` (State `299`) transitions on `0` to State `403`
  (`while_decnz(scratch1, 3.param1.inc).0`) instead of State `407`
  (`while_decnz(scratch1, 3.param3.inc).0`).
- Consequently, during the first distinctness check (`param1 ≠ param3`) of Clause 9 (`B6a`),
  `param3` is drained into `param1` (`param1 := p1 + p3, param3 := 0`), so the second check
  compares `param2` against `param3 = 0` (`p2 ≠ 0` instead of `p2 ≠ p3`), and subsequent clauses
  (`ac = 10..17`) see `param1 = p1 + p3` and `param3 = 0`.
- `WadeZFProvable` ([`Zf/RegisterMachine.lean`](./Zf/RegisterMachine.lean)) captures the exact
  20-clause deductive system enumerated by `zf_432_wade.tm`, while `ZFProvable`
  ([`Zf/Soundness.lean`](./Zf/Soundness.lean)) captures O'Rear's `zf2.nql` / Wade's post-`10fcf152b3`
  Hilbert system and proves its soundness in Mathlib's `ZFSet.{0}` (`not_zfInconsistent`).

### Provenance and Attribution

1. **Tarski's minimal substitution-free first-order system $S_2$ (1965) & `zf2.nql` (2016–2017)**
   - **Authors**: Alfred Tarski (*Z. Math. Logik Grundlag. Math.* **11** (1965), 207–230);
     Stefan O'Rear and CatIsFluffy ([`sorear/metamath-turing-machines`](https://github.com/sorear/metamath-turing-machines),
     `zf2.nql`).
2. **432-state ZF Turing machine (`zf_432_wade.tm`, 2025)**
   - **Author**: Andrew Wade ([`ajwade/turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer),
     `zf2.py` and `TMBuilder.py`).
3. **This formalization ([`Cryptids/Semantics/Zf.lean`](./Zf.lean) & [`Cryptids/Semantics/Zf/`](./Zf/))**
   - **Authors**: Maxence Faldor and Moritz Firsching, using Gemini Argon.
   - See also [`Cryptids/Semantics/Zf393.lean`](./Zf393.lean) and [`Cryptids/Zf380.lean`](../Zf380.lean) for Wade's 393-state machine (`zf_393`, 2026) and its 380-state reduction (`zf_380`).

### Proof Architecture

```
Halts Machines.zf432 (zf_432_wade.tm)
  │
  │  Layer 1 + Layer 1b + Layer 2: halts_reference_iff_zfRegHalts_unconditional (0 sorry)
  │  (Cryptids/Semantics/Zf/Gadgets.lean, Boot.lean, Dispatcher.lean)
  ▼
ZfRegHalts (11-register call-stack machine, 336-state decision tree)
  │
  │  Layer 3b: zfRegHalts_iff_mainLoopHalts (0 sorry)
  │  (Cryptids/Semantics/Zf/Subroutines.lean)
  ▼
MainLoopHalts (zf_432_wade.tm outer proof-enumeration loop)
  │
  │  Layer 3: mainLoopHalts_iff_wadeZFInconsistent (0 sorry)
  │  (Cryptids/Semantics/Zf/RegisterMachine.lean)
  ▼
WadeZFInconsistent (WadeZFProvable (zfMem 0 0))

ZFProvable (zfMem 0 0) (ZFInconsistent, O'Rear's zf2.nql / post-10fcf152b3 Hilbert system)
  │
  │  Part II: zfProvable_sound_zfSet & not_zfInconsistent (0 sorry)
  │  (Cryptids/Semantics/Zf/Soundness.lean)
  ▼
False (via Mathlib.SetTheory.ZFC.Basic, ZFSet.mem_irrefl)
```

1. **Part II — Gödel Numbering, Hilbert System, & Soundness in `ZFSet.{0}` ([`Zf/Soundness.lean`](./Zf/Soundness.lean), `0 sorry`s)**:
   Proves the Cantor pairing bijection `cantorUnpair (cantorPair x y) = (x, y)`, defines a total
   well-founded Tarski satisfaction predicate `zfHolds : ℕ → (ℕ → ZFSet.{u}) → Prop` on all natural
   numbers `n : ℕ`, and proves soundness of all 19 constructors of `ZFProvable` (`moot`, `mp`,
   `gen`, `b1..b8c`, `ext`, `rep`, `pow`, `uni`, `inf`) in `ZFSet.{0}`.
2. **Layer 1 & 1b — Tape Layout, Bootstrapping, & Register Gadgets ([`Zf/Gadgets.lean`](./Zf/Gadgets.lean) & [`Zf/Boot.lean`](./Zf/Boot.lean), `0 sorry`s)**:
   Proves that starting from `init = ⟨0, default⟩`, `reference` executes all 8 exponential rounds
   of `0a.boot1.A..E` (2,133,492 steps) and 1,909 cycles of `0b.boot2` to reach the canonical root
   configuration `zfRootCfg 3821 [] (List.replicate 1909 0)` at `main().0` (State `126`), and
   verifies the two-pass unary register increment (`stage3_inc_pass2`) and conditional decrement
   (`stage3_decnz_pass2_zero`, `stage3_decnz_pass2_pos`) gadgets.
3. **Layer 2 — Call-Stack Decision-Tree Dispatcher ([`Zf/Dispatcher.lean`](./Zf/Dispatcher.lean), `0 sorry`s)**:
   Verifies the 336-state unary call-stack decision tree (`States 96..431`), proves universal
   tree-walk soundness (`walkTape_sound`) and stack-bound invariance (`validStack`), and establishes
   the lockstep halting bisimulation `halts_reference_iff_zfRegHalts : Halts reference ↔ ZfRegHalts`.
4. **Layer 3 & 3b — 11-Register Machine, Subroutines, & Wff-Stack Verification ([`Zf/RegisterMachine.lean`](./Zf/RegisterMachine.lean) & [`Zf/Subroutines.lean`](./Zf/Subroutines.lean), `0 sorry`s)**:
   Verifies all 336 decision-tree subroutine states (`while_decnz`, `pair`, `unpair`, `cparam`,
   `if_eq`, `select`, and the 61 composite RPN formula subroutines) and all 135 steps of the outer
   `main()` spine (`main().0..134`), proving `zfRegHalts_iff_mainLoopHalts : ZfRegHalts ↔ MainLoopHalts`
   and `mainLoopHalts_iff_wadeZFInconsistent : MainLoopHalts ↔ WadeZFInconsistent`.

---

## 4. Shunia's 120-State Riemann Hypothesis Machine ([`Riemann120.lean`](./Riemann120.lean) & [`Riemann120/`](./Riemann120/))

In [`Cryptids/Riemann120.lean`](../Riemann120.lean) and [`Cryptids/Semantics/Riemann120.lean`](./Riemann120.lean)
(with submodules [`Backend.lean`](./Riemann120/Backend.lean), [`Program.lean`](./Riemann120/Program.lean),
[`Analytic.lean`](./Riemann120/Analytic.lean), [`VonMangoldt.lean`](./Riemann120/VonMangoldt.lean),
and [`Bridge.lean`](./Riemann120/Bridge.lean)), we formalize Joseph M. Shunia's 120-state binary
Turing machine (`riemann_120`, [`arXiv:2609.30306`](https://arxiv.org/abs/2609.30306), September 2026):

```lean
theorem halts_riemann120_iff_not_riemannHypothesis :
    Halts riemann120 ↔ ¬ RiemannHypothesis
```

1. **Layer 1 (`Riemann120.lean` & `Riemann120/Backend.lean`)**: Proves the 5-cell window invariant
   quotienting `riemann121` (`121` states) onto `riemann120` (`120` states), the 89,775,610-step blank-tape
   bootstrap to `main.0`, the moving `00` register-selection invariant across all 5 registers
   `[m, j, x, f, v]`, and the lockstep simulation `Halts riemann120 ↔ RhRegHalts`.
2. **Layer 2 (`Riemann120/Program.lean`)**: Verifies all subroutines of `riemann121` (`move`, `fold`,
   `transform`, `twice`, `divide`, `product_step`, `seed_deficit`, `digits`, `halve`, `width`,
   `compare`), the self-sieving identity $A_n = n! \prod_{p \le n} p$, and
   `RhRegHalts ↔ ∃ n ≥ 2, ShuniaCounterexample n`.
3. **Layer 3 (`Riemann120/Analytic.lean`, `Riemann120/VonMangoldt.lean`, & `Riemann120/Bridge.lean`)**:
   Proves the Stirling/Chebyshev identity connecting `shuniaProd n` to $\vartheta(n)$, the
   one-sided Landau Mellin continuation theorem (`¬ RH → ∃ n ≥ 2, ShuniaCounterexample n`), the
   elementary Chebyshev verification for $2 \le n \le 21{,}845$, and the sharp circle-average
   Jensen bound (`a_rvM = 3/4`) closing all $n \ge 21{,}846$ under `RiemannHypothesis`.

---

## 5. Wade's 393-State ZF Consistency Machine ([`Zf393.lean`](./Zf393.lean) & [`Zf393/`](./Zf393/))

In [`Cryptids/Zf393.lean`](../Zf393.lean) and [`Cryptids/Semantics/Zf393.lean`](./Zf393.lean)
(with submodules [`Backend.lean`](./Zf393/Backend.lean) and [`Program.lean`](./Zf393/Program.lean)),
we formalize Andrew Wade's 393-state binary Turing machine (`zf_393`,
[`ajwade/turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer) commit
`9c5c2e82`, August 2026):

```lean
theorem halts_zf393_iff_zfInconsistent :
    Halts zf393 ↔ ZFInconsistent

theorem not_halts_zf393 :
    ¬ Halts zf393
```

1. **Layer 1 (`Zf393.lean` & `Zf393/Backend.lean`)**: Verifies the 39,773-step blank-tape bootstrap,
   the moving `00` selector (`1.sel`), self-cleaning unary register gadgets (`1.inc`, `1.decnz`,
   `3.<reg>.inc/decnz`), root overflow into `default`, and `Halts zf393 ↔ Layer1.Zf393RegHalts`.
2. **Layer 2 & 3 (`Zf393/Program.lean` & `Zf393.lean`)**: Verifies all 324 control-DAG states
   (`69..392`), the 125-step outer `main()` spine (`99..223`), and soundness & completeness against
   O'Rear's `ZFProvable` (`Layer2.Zf393RegHalts ↔ ZFInconsistent`), yielding unconditional
   non-halting (`not_halts_zf393`) via `Cryptids.Semantics.Zf.not_zfInconsistent`.

---

## 6. Stérin and Woods's 15-State Erdős Machine ([`Erdos15.lean`](./Erdos15.lean))

In [`Cryptids/Erdos15.lean`](../Erdos15.lean) and [`Cryptids/Semantics/Erdos15.lean`](./Erdos15.lean),
we formalize Tristan Stérin and Damien Woods's 15-state binary Turing machine (`erdos_15`,
[`arXiv:2107.12475`](https://arxiv.org/abs/2107.12475), 2021) for Erdős's conjecture that `2 ^ n`
has a digit `2` in base `3` for every `n > 8`:

```lean
theorem halts_erdos15_iff_exists_counterexample :
    Halts erdos15 ↔ ∃ n : ℕ, 8 < n ∧ 2 ∉ Nat.digits 3 (2 ^ n)

theorem halts_erdos15_iff_not_erdosPowersOfTwo :
    Halts erdos15 ↔ ¬ ErdosPowersOfTwoConjecture
```

1. **Machine (`Erdos15.lean`)**: Proves the tape layout of every stage (counter cell pair, `#`,
   base-3 digits of `2 ^ n` as cell pairs), one lemma per routine (doubling pass, scan for a `2`,
   rewind, counter increment, halt), and `Halts erdos15 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` with `propext`
   and `Quot.sound` only, where `pw n` is the digit list of `2 ^ n` computed by repeated doubling.
2. **Digits (`Semantics/Erdos15.lean`)**: Proves `pw n = Nat.digits 3 (2 ^ n)` and derives both
   theorems above (`Classical.choice` enters through `Nat.digits`, and the negated form also uses
   Markov's Principle via `not_forall`, as for `¬ GoldbachConjecture`).

---

## 7. Stérin's 14-State Erdős Machine ([`Erdos14.lean`](./Erdos14.lean))

In [`Cryptids/Erdos14.lean`](../Erdos14.lean) and [`Cryptids/Semantics/Erdos14.lean`](./Erdos14.lean),
we formalize Tristan Stérin's 14-state binary Turing machine for the same conjecture (`erdos_14`,
[announced](https://discord.com/channels/960643023006490684/1561295445312151622/1562203343114473472) on the bbchallenge Discord in October 2026 and listed on the
[Cryptids](https://wiki.bbchallenge.org/w/index.php?title=Cryptids&oldid=9722) page of the bbchallenge wiki):

```lean
theorem candidate_fewer_states : candidate.states < reference.states

theorem candidate_equivalent : Halts candidate ↔ Halts reference

theorem halts_candidate_iff_not_erdosPowersOfTwo :
    Halts candidate ↔ ¬ ErdosPowersOfTwoConjecture
```

with `candidate = erdos14` and `reference = erdos15`.

1. **Machine (`Erdos14.lean`)**: The machine keeps `2 ^ n` in unary and reads its base-3 digits
   by repeated division by `3`, with a single `0` in the block marking where the quotient ends.
   One lemma per routine (division round and its three outcomes, return to the start, counter
   increment, halt, doubling) gives `Halts erdos14 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` with `propext` and
   `Quot.sound` only, using `Has2 (2 ^ n) ↔ 2 ∈ pw n` to connect the divisions with `pw`.
   `candidate_equivalent` follows from the same statement for `erdos15`, so it is also
   constructive.
2. **Semantics (`Semantics/Erdos14.lean`)**: Composes `candidate_equivalent` with
   `halts_erdos15_iff_not_erdosPowersOfTwo` (`Classical.choice` through `Nat.digits`, and
   Markov's Principle via `not_forall`, as in Section 6).
