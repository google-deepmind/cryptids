/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.SetTheory.ZFC.Basic
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Target Mathematical Propositions (`Cryptids.Propositions`)

This module collects the mathematical propositions and formal deductive systems targeted by the
conjecture-checking Turing machines in this repository, separated from the Turing machine tape
constructions and halting proofs:

1. **Goldbach's Conjecture** (`GoldbachConjecture`):
   Every even integer greater than `2` is the sum of two primes (`goldbach_25`, `goldbach_21`).
2. **Riemann Hypothesis** (`RiemannHypothesis` and `MatiyasevichRiemannCounterexample`):
   Mathlib's `RiemannHypothesis` (`riemann_744`, `riemann_120`, `riemann_104`), together with the
   elementary harmonic/LCM counterexample inequality `MatiyasevichRiemannCounterexample` directly
   tested by `riemann_744`.
3. **Zermelo–Fraenkel Set Theory Consistency** (`ZFInconsistent` vs. `WadeZFInconsistent`):
   Formula encoding via Cantor pairing (`cantorPair`, `ZFFormula`) and the two Hilbert systems
   analyzed in `Cryptids.Semantics.Zf`:
   - `ZFProvable` / `ZFInconsistent`: Stefan O'Rear's `zf2.nql` (and Andrew Wade's post-`10fcf152b3`
     `zf2.py`) Hilbert system, proved sound in Mathlib's `ZFSet.{0}` (`not_zfInconsistent`).
   - `WadeZFProvable` / `WadeZFInconsistent`: the 20-clause Hilbert system actually enumerated by
     Andrew Wade's published 432-state Turing machine `zf_432_wade.tm` (`zf2.py` prior to commit
     `10fcf152b3`), which differs from `ZFProvable` in clauses `B6a`, `B8a`, and `B8c` due to a
     register-restoration bug in `B6a` (`main().n_140.1` restoring `scratch1` into `param1` instead
     of `param3`).
4. **Erdős's Conjecture on Powers of Two** (`ErdosPowersOfTwoConjecture`):
   For every `n > 8`, the base-3 expansion of `2 ^ n` contains the digit `2` (`erdos_15`).
-/

@[expose] public section

namespace ConjectureMachines

/-! ## 1. Goldbach's Conjecture -/

/-- **Goldbach's Conjecture**: every even integer greater than 2 is the sum of two primes. -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-! ## 2. Riemann Hypothesis -/

/-- Unreduced harmonic numerator computed by the loop
`num = num * i + denom; denom = denom * i` in `riemann.nql`:
`harmNum n / n! = ∑_{i=1}^n 1 / i = harmonic n`. -/
def harmNum : ℕ → ℕ
  | 0 => 0
  | n + 1 => harmNum n * (n + 1) + n.factorial

/-- The elementary integer inequality tested at stage `x` by `riemann.nql`
(Matiyasevich, Aaronson, and O'Rear 2016): for $x > 253$ and
$L_x = \operatorname{lcm}(1, \dots, x)$,
$$b \cdot c < a \cdot d \iff H_{L_x} > x \;\wedge\; (H_{L_x} - x)^2 > x \cdot H_x^4.$$
In `Cryptids.Semantics.Riemann`, `(∃ x : ℕ, MatiyasevichRiemannCounterexample x)` is proved
equivalent to `¬ RiemannHypothesis`. -/
def MatiyasevichRiemannCounterexample (x : ℕ) : Prop :=
  253 < x ∧
  let lcm := (Finset.Icc 1 x).lcm id
  let a := (harmNum lcm - lcm.factorial * x) ^ 2
  let b := lcm.factorial ^ 2
  let c := harmNum x ^ 4 * x
  let d := x.factorial ^ 4
  b * c < a * d

/-! ## 3. Zermelo–Fraenkel Set Theory Consistency (`ZFInconsistent` vs. `WadeZFInconsistent`) -/

/-- The Cantor pairing function $\operatorname{cantorPair}(x, y) = x + \frac{(x+y)(x+y+1)}{2}$
computed by `builtin_pair` in `zf2.nql`. -/
def cantorPair (x y : ℕ) : ℕ :=
  x + (x + y) * (x + y + 1) / 2

/-- Gödel number of the atomic equality formula $v_x = v_y$ (`weq` in `zf2.nql`). -/
def zfEq (x y : ℕ) : ℕ :=
  cantorPair (cantorPair x y) 0

/-- Gödel number of the atomic membership formula $v_x \in v_y$ (`wel` in `zf2.nql`). -/
def zfMem (x y : ℕ) : ℕ :=
  cantorPair (cantorPair x y) 1

/-- Gödel number of the implication formula $\varphi \to \psi$ (`wim` in `zf2.nql`). -/
def zfImp (φ ψ : ℕ) : ℕ :=
  cantorPair (cantorPair φ ψ) 2

/-- Gödel number of the negation formula $\neg \varphi$ (`wn` in `zf2.nql`). -/
def zfNot (φ : ℕ) : ℕ :=
  cantorPair φ 3

/-- Gödel number of the universal formula $\forall v_x\, \varphi$ (`wal` in `zf2.nql`). -/
def zfAll (x φ : ℕ) : ℕ :=
  cantorPair (cantorPair x φ) 4

/-- Gödel number of the existential abbreviation
$\exists v_x\, \varphi \equiv \neg \forall v_x \neg \varphi$ (`wex` in `zf2.nql`). -/
def zfEx (x φ : ℕ) : ℕ :=
  zfNot (zfAll x (zfNot φ))

/-- Gödel number of the conjunction abbreviation
$\varphi \land \psi \equiv \neg (\varphi \to \neg \psi)$ (`wa` in `zf2.nql`). -/
def zfAnd (φ ψ : ℕ) : ℕ :=
  zfNot (zfImp φ (zfNot ψ))

/-- Well-formed formulas of first-order set theory with variables indexed by `ℕ`. -/
inductive ZFFormula : Type where
  | eq (x y : ℕ) : ZFFormula
  | mem (x y : ℕ) : ZFFormula
  | imp (φ ψ : ZFFormula) : ZFFormula
  | not (φ : ZFFormula) : ZFFormula
  | all (x : ℕ) (φ : ZFFormula) : ZFFormula
  deriving DecidableEq, Repr

namespace ZFFormula

/-- Existential quantification abbreviation
$\exists v_x\, \varphi \equiv \neg \forall v_x \neg \varphi$. -/
def ex (x : ℕ) (φ : ZFFormula) : ZFFormula :=
  .not (.all x (.not φ))

/-- Conjunction abbreviation $\varphi \land \psi \equiv \neg (\varphi \to \neg \psi)$. -/
def and (φ ψ : ZFFormula) : ZFFormula :=
  .not (.imp φ (.not ψ))

/-- The Gödel number of a `ZFFormula`, matching `zf2.nql`. -/
def code : ZFFormula → ℕ
  | .eq x y => zfEq x y
  | .mem x y => zfMem x y
  | .imp φ ψ => zfImp φ.code ψ.code
  | .not φ => zfNot φ.code
  | .all x φ => zfAll x φ.code

/-- Tarski satisfaction of a `ZFFormula` in Mathlib's cumulative hierarchy `ZFSet.{u}`
under a variable assignment `v : ℕ → ZFSet.{u}`. -/
def Holds (v : ℕ → ZFSet.{u}) : ZFFormula → Prop
  | .eq x y => v x = v y
  | .mem x y => v x ∈ v y
  | .imp φ ψ => φ.Holds v → ψ.Holds v
  | .not φ => ¬ φ.Holds v
  | .all x φ => ∀ s : ZFSet.{u}, φ.Holds (Function.update v x s)

end ZFFormula

/-- Axiom scheme `B1`: $(\varphi \to \psi) \to ((\psi \to \chi) \to (\varphi \to \chi))$. -/
def axB1 (φ ψ χ : ℕ) : ℕ :=
  zfImp (zfImp φ ψ) (zfImp (zfImp ψ χ) (zfImp φ χ))

/-- Axiom scheme `B2`: $(\neg \varphi \to \varphi) \to \varphi$. -/
def axB2 (φ : ℕ) : ℕ :=
  zfImp (zfImp (zfNot φ) φ) φ

/-- Axiom scheme `B3`: $\varphi \to (\neg \varphi \to \psi)$. -/
def axB3 (φ ψ : ℕ) : ℕ :=
  zfImp φ (zfImp (zfNot φ) ψ)

/-- Axiom scheme `B4`:
$\forall v_x (\varphi \to \psi) \to (\forall v_x \varphi \to \forall v_x \psi)$. -/
def axB4 (x φ ψ : ℕ) : ℕ :=
  zfImp (zfAll x (zfImp φ ψ)) (zfImp (zfAll x φ) (zfAll x ψ))

/-- Axiom scheme `B6a`:
$(v_x = v_y \to \forall v_z\, v_x = v_y) \land (v_x \in v_y \to \forall v_z\, v_x \in v_y)$. -/
def axB6a (x y z : ℕ) : ℕ :=
  zfAnd (zfImp (zfEq x y) (zfAll z (zfEq x y))) (zfImp (zfMem x y) (zfAll z (zfMem x y)))

/-- Axiom scheme `B6b`:
$\forall v_x \forall v_y \varphi \to \forall v_y \forall v_x \varphi$. -/
def axB6b (x y φ : ℕ) : ℕ :=
  zfImp (zfAll x (zfAll y φ)) (zfAll y (zfAll x φ))

/-- Axiom scheme `B6c`: $\exists v_x \forall v_x \varphi \to \varphi$. -/
def axB6c (x φ : ℕ) : ℕ :=
  zfImp (zfEx x (zfAll x φ)) φ

/-- Axiom scheme `B7`: $\exists v_x\, v_x = v_y$. -/
def axB7 (x y : ℕ) : ℕ :=
  zfEx x (zfEq x y)

/-- Axiom scheme `B8a`: $v_x = v_y \to (v_x = v_z \to v_y = v_z)$. -/
def axB8a (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfEq x z) (zfEq y z))

/-- Axiom scheme `B8b`: $v_x = v_y \to (v_x \in v_z \to v_y \in v_z)$. -/
def axB8b (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfMem x z) (zfMem y z))

/-- Axiom scheme `B8c`: $v_x = v_y \to (v_z \in v_x \to v_z \in v_y)$. -/
def axB8c (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfMem z x) (zfMem z y))

/-- Axiom of Extensionality (`EXT`):
$\forall v_2 ((v_2 \in v_0 \to v_2 \in v_1) \land (v_2 \in v_1 \to v_2 \in v_0)) \to v_0 = v_1$. -/
def axExt : ℕ :=
  zfImp
    (zfAll 2 (zfAnd (zfImp (zfMem 2 0) (zfMem 2 1)) (zfImp (zfMem 2 1) (zfMem 2 0))))
    (zfEq 0 1)

/-- Helper formula $\exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi)$ used in `axRep`. -/
def axRepRhs (φ : ℕ) : ℕ :=
  zfEx 3 (zfAnd (zfMem 3 0) (zfAll 1 φ))

/-- Axiom scheme of Replacement (`REP`):
$\forall v_3 \exists v_1 \forall v_2 (\forall v_1 \varphi \to v_2 = v_1) \to
  \exists v_1 \forall v_2 ((v_2 \in v_1 \to \exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi))
    \land (\exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi) \to v_2 \in v_1))$. -/
def axRep (φ : ℕ) : ℕ :=
  zfImp
    (zfAll 3 (zfEx 1 (zfAll 2 (zfImp (zfAll 1 φ) (zfEq 2 1)))))
    (zfEx 1 (zfAll 2
      (zfAnd (zfImp (zfMem 2 1) (axRepRhs φ)) (zfImp (axRepRhs φ) (zfMem 2 1)))))

/-- Axiom of Power Set (`POW`):
$\exists v_1 \forall v_2 (\forall v_3 (v_3 \in v_2 \to v_3 \in v_0) \to v_2 \in v_1)$. -/
def axPow : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfAll 3 (zfImp (zfMem 3 2) (zfMem 3 0))) (zfMem 2 1)))

/-- Axiom of Union (`UNI`):
$\exists v_1 \forall v_2 (\exists v_3 (v_2 \in v_3 \land v_3 \in v_0) \to v_2 \in v_1)$. -/
def axUni : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfEx 3 (zfAnd (zfMem 2 3) (zfMem 3 0))) (zfMem 2 1)))

/-- Helper singleton-characterization formula
$\forall v_1 ((v_1 \in v_2 \to v_1 = v_0) \land (v_1 = v_0 \to v_1 \in v_2))$ used in `axInf`. -/
def axInfSingleton : ℕ :=
  zfAll 1 (zfAnd (zfImp (zfMem 1 2) (zfEq 1 0)) (zfImp (zfEq 1 0) (zfMem 1 2)))

/-- Axiom of Infinity (`INF`):
$\exists v_1 (v_0 \in v_1 \land \forall v_0 (v_0 \in v_1 \to
  \exists v_2 (v_2 \in v_1 \land \forall v_1 (v_1 \in v_2 \leftrightarrow v_1 = v_0))))$. -/
def axInf : ℕ :=
  zfEx 1
    (zfAnd (zfMem 0 1)
      (zfAll 0 (zfImp (zfMem 0 1) (zfEx 2 (zfAnd (zfMem 2 1) axInfSingleton)))))

/-! ### 3a. O'Rear's `zf2.nql` Hilbert System (`ZFProvable`, `ZFInconsistent`) -/

/-- The inductive provability predicate `ZFProvable φ` of Stefan O'Rear's `zf2.nql` (and Andrew
Wade's post-`10fcf152b3` `zf2.py`) Hilbert system for Zermelo–Fraenkel set theory, combining
Tarski's substitution-free first-order system $S_2$ (`B1..B8c`, `mp`, `gen`) with the ZF axioms
(`ext`, `rep`, `pow`, `uni`, `inf`). Proved sound in Mathlib's `ZFSet.{0}` in
`Cryptids.Semantics.Zf.Soundness`. -/
inductive ZFProvable : ℕ → Prop where
  | moot : ZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : ZFProvable φ → ZFProvable (zfImp φ ψ) → ZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : ZFProvable φ → ZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : ZFProvable (axB1 φ ψ χ)
  | b2 (φ : ℕ) : ZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : ZFProvable (axB3 φ ψ)
  | b4 (x φ ψ : ℕ) : ZFProvable (axB4 x φ ψ)
  | b6a (x y z : ℕ) (hxz : x ≠ z) (hzy : z ≠ y) : ZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : ZFProvable (axB6b x y φ)
  | b6c (x φ : ℕ) : ZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : ZFProvable (axB7 x y)
  | b8a (x y z : ℕ) : ZFProvable (axB8a x y z)
  | b8b (x y z : ℕ) : ZFProvable (axB8b x y z)
  | b8c (x y z : ℕ) : ZFProvable (axB8c x y z)
  | ext : ZFProvable axExt
  | rep (φ : ℕ) : ZFProvable (axRep φ)
  | pow : ZFProvable axPow
  | uni : ZFProvable axUni
  | inf : ZFProvable axInf

/-- Inconsistency of O'Rear's `ZFProvable` Hilbert system: the contradiction formula
$v_0 \in v_0$ (`zfMem 0 0 = 1`) is provable. -/
def ZFInconsistent : Prop :=
  ZFProvable (zfMem 0 0)

/-! ### 3b. Wade's `zf_432_wade.tm` Hilbert System (`WadeZFProvable`, `WadeZFInconsistent`) -/

/-- Provability predicate of the 20-clause Hilbert system implemented by Andrew Wade's published
432-state Turing machine `zf_432_wade.tm` (`zf2.py` prior to his August 31, 2025 bugfix commit
`10fcf152b3`).

Compared to `ZFProvable`, in `zf_432_wade.tm` the first distinctness check of clause `B6a`
(`param1 ≠ param3`) restores `scratch1` into `param1` instead of `param3` (`main().n_140.1`),
draining `param3` to `0`. Consequently:
- `b6a_wade` tests `x ≠ z ∧ y ≠ 0` instead of `x ≠ z ∧ z ≠ y`, and
- `b8a_zero` and `b8c_zero` instantiate `z = 0` (`param3 = 0`). -/
inductive WadeZFProvable : ℕ → Prop where
  | moot : WadeZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : WadeZFProvable φ → WadeZFProvable (zfImp φ ψ) → WadeZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : WadeZFProvable φ → WadeZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : WadeZFProvable (axB1 φ ψ χ)
  | b2 (φ : ℕ) : WadeZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : WadeZFProvable (axB3 φ ψ)
  | b4 (x φ ψ : ℕ) : WadeZFProvable (axB4 x φ ψ)
  | b6a_wade (x y z : ℕ) (hxz : x ≠ z) (hy : y ≠ 0) : WadeZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : WadeZFProvable (axB6b x y φ)
  | b6c (x φ : ℕ) : WadeZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : WadeZFProvable (axB7 x y)
  | b8a_zero (x y : ℕ) : WadeZFProvable (axB8a x y 0)
  | b8b (x y z : ℕ) : WadeZFProvable (axB8b x y z)
  | b8c_zero (x y : ℕ) : WadeZFProvable (axB8c x y 0)
  | ext : WadeZFProvable axExt
  | rep (φ : ℕ) : WadeZFProvable (axRep φ)
  | pow : WadeZFProvable axPow
  | uni : WadeZFProvable axUni
  | inf : WadeZFProvable axInf

/-- Inconsistency of the `WadeZFProvable` Hilbert system enumerated by `zf_432_wade.tm` (`zf_432`):
the contradiction formula $v_0 \in v_0$ (`zfMem 0 0 = 1`) is provable. -/
def WadeZFInconsistent : Prop :=
  WadeZFProvable (zfMem 0 0)

/-! ## 4. Erdős's Conjecture on Powers of Two -/

/-- **Erdős's conjecture on powers of two** (Erdős 1979): for every `n > 8`, the base-3
expansion of `2 ^ n` contains the digit `2`. -/
def ErdosPowersOfTwoConjecture : Prop :=
  ∀ n : ℕ, 8 < n → 2 ∈ Nat.digits 3 (2 ^ n)

end ConjectureMachines
