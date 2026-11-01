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
public import Cryptids.Machines

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
  let lcm := (@Finset.Icc ℕ Nat.instPreorder Nat.instLocallyFiniteOrder 1 x).lcm id
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

/-!
## 4. First-Order Peano Arithmetic (`PATerm`, `PAFormula`, `PAProvable`)

To formalize metamathematical provability in first-order Peano Arithmetic ($\mathrm{PA}$) inside
Lean without relying on Lean's ambient type-theoretic strength, we deeply embed the syntax,
standard `ℕ` Tarski semantics, Hilbert proof system (`PAProvable`), and $\Sigma_1^0$
arithmetizations of binary Turing machine halting (`paHalts`) and `ZF` inconsistency
(`paZFInconsistent`).
-/

/-- First-order terms in the language of Peano Arithmetic
$\mathcal{L}_{\mathrm{PA}} = \{0, S, +, \times\}$. -/
inductive PATerm : Type where
  | var (x : ℕ) : PATerm
  | zero : PATerm
  | succ (t : PATerm) : PATerm
  | add (t₁ t₂ : PATerm) : PATerm
  | mul (t₁ t₂ : PATerm) : PATerm
  deriving DecidableEq, Repr

/-- Standard numeral $\overline{n}$ in $\mathcal{L}_{\mathrm{PA}}$. -/
def PATerm.ofNat : ℕ → PATerm
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

/-- Whether variable `x` occurs in a `PATerm`. -/
def PATerm.hasVar (x : ℕ) : PATerm → Bool
  | .var y => y == x
  | .zero => false
  | .succ t => t.hasVar x
  | .add t₁ t₂ | .mul t₁ t₂ => t₁.hasVar x || t₂.hasVar x

/-- Smallest variable index strictly greater than every variable occurring in a `PATerm`. -/
def PATerm.freshVar : PATerm → ℕ
  | .var x => x + 1
  | .zero => 0
  | .succ t => t.freshVar
  | .add t₁ t₂ | .mul t₁ t₂ => max t₁.freshVar t₂.freshVar

/-- Substitute term `s` for variable `x` in a `PATerm`. -/
def PATerm.subst : PATerm → ℕ → PATerm → PATerm
  | .var y, x, s => if y == x then s else .var y
  | .zero, _, _ => .zero
  | .succ t, x, s => .succ (t.subst x s)
  | .add t₁ t₂, x, s => .add (t₁.subst x s) (t₂.subst x s)
  | .mul t₁ t₂, x, s => .mul (t₁.subst x s) (t₂.subst x s)

/-- Evaluate a `PATerm` in the standard model `ℕ` under assignment `v`. -/
def PATerm.eval (v : ℕ → ℕ) : PATerm → ℕ
  | .var x => v x
  | .zero => 0
  | .succ t => t.eval v + 1
  | .add t₁ t₂ => t₁.eval v + t₂.eval v
  | .mul t₁ t₂ => t₁.eval v * t₂.eval v

/-- First-order formulas of Peano Arithmetic with variables indexed by `ℕ`. -/
inductive PAFormula : Type where
  | bot : PAFormula
  | eq (t₁ t₂ : PATerm) : PAFormula
  | and (φ ψ : PAFormula) : PAFormula
  | or (φ ψ : PAFormula) : PAFormula
  | imp (φ ψ : PAFormula) : PAFormula
  | all (x : ℕ) (φ : PAFormula) : PAFormula
  | ex (x : ℕ) (φ : PAFormula) : PAFormula
  deriving DecidableEq, Repr

/-- Negation $\neg \varphi := \varphi \to \bot$. -/
abbrev PAFormula.not (φ : PAFormula) : PAFormula := .imp φ .bot

/-- Bi-implication $\varphi \leftrightarrow \psi := (\varphi \to \psi) \land (\psi \to \varphi)$. -/
abbrev PAFormula.iff (φ ψ : PAFormula) : PAFormula := .and (.imp φ ψ) (.imp ψ φ)

/-- Inequality $s \neq t := \neg (s = t)$. -/
abbrev paNe (s t : PATerm) : PAFormula := .not (.eq s t)

/-- Non-strict inequality $a \le b := \exists k,\, a + k = b$ with a fresh witness variable `k`. -/
def paLe (a b : PATerm) : PAFormula :=
  let k := max a.freshVar b.freshVar
  .ex k (.eq (.add a (.var k)) b)

/-- Strict inequality $a < b := S(a) \le b$. -/
def paLt (a b : PATerm) : PAFormula :=
  paLe (.succ a) b

/-- Finite disjunction of a list of `PAFormula`s. -/
def paDisjList : List PAFormula → PAFormula
  | [] => .bot
  | [φ] => φ
  | φ :: rest => .or φ (paDisjList rest)

/-- Whether variable `x` occurs free in a `PAFormula`. -/
def PAFormula.hasFree (x : ℕ) : PAFormula → Bool
  | .bot => false
  | .eq t₁ t₂ => t₁.hasVar x || t₂.hasVar x
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.hasFree x || ψ.hasFree x
  | .all y φ | .ex y φ => !(y == x) && φ.hasFree x

/-- Whether term `s` is free for `x` in `φ` (no free occurrence of `x` lies under a binder
for any variable occurring in `s`). -/
def PAFormula.freeFor (x : ℕ) (s : PATerm) : PAFormula → Bool
  | .bot | .eq _ _ => true
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.freeFor x s && ψ.freeFor x s
  | .all y φ | .ex y φ => (y == x) || ((!φ.hasFree x || !s.hasVar y) && φ.freeFor x s)

/-- Substitute term `s` for free occurrences of variable `x` in `φ`. -/
def PAFormula.subst (x : ℕ) (s : PATerm) : PAFormula → PAFormula
  | .bot => .bot
  | .eq t₁ t₂ => .eq (t₁.subst x s) (t₂.subst x s)
  | .and φ ψ => .and (φ.subst x s) (ψ.subst x s)
  | .or φ ψ => .or (φ.subst x s) (ψ.subst x s)
  | .imp φ ψ => .imp (φ.subst x s) (ψ.subst x s)
  | .all y φ => if y == x then .all y φ else .all y (φ.subst x s)
  | .ex y φ => if y == x then .ex y φ else .ex y (φ.subst x s)

/-- Standard Tarski satisfaction of a `PAFormula` in `ℕ` under variable assignment `v`. -/
def PAFormula.Holds (v : ℕ → ℕ) : PAFormula → Prop
  | .bot => False
  | .eq t₁ t₂ => t₁.eval v = t₂.eval v
  | .and φ ψ => φ.Holds v ∧ ψ.Holds v
  | .or φ ψ => φ.Holds v ∨ ψ.Holds v
  | .imp φ ψ => φ.Holds v → ψ.Holds v
  | .all x φ => ∀ a : ℕ, φ.Holds (Function.update v x a)
  | .ex x φ => ∃ a : ℕ, φ.Holds (Function.update v x a)

/-- Standard Hilbert proof system for first-order Peano Arithmetic ($\mathrm{PA}$), combining
classical first-order logic with equality, the six defining equations of $0, S, +, \times$, and the
full first-order induction schema. -/
inductive PAProvable : PAFormula → Prop where
  | mp {φ ψ : PAFormula} : PAProvable φ → PAProvable (.imp φ ψ) → PAProvable ψ
  | gen (x : ℕ) {φ : PAFormula} : PAProvable φ → PAProvable (.all x φ)
  | imp_k (φ ψ : PAFormula) : PAProvable (.imp φ (.imp ψ φ))
  | imp_s (φ ψ χ : PAFormula) :
      PAProvable (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | dne (φ : PAFormula) : PAProvable (.imp (.not (.not φ)) φ)
  | and_intro (φ ψ : PAFormula) : PAProvable (.imp φ (.imp ψ (.and φ ψ)))
  | and_left (φ ψ : PAFormula) : PAProvable (.imp (.and φ ψ) φ)
  | and_right (φ ψ : PAFormula) : PAProvable (.imp (.and φ ψ) ψ)
  | or_left (φ ψ : PAFormula) : PAProvable (.imp φ (.or φ ψ))
  | or_right (φ ψ : PAFormula) : PAProvable (.imp ψ (.or φ ψ))
  | or_elim (φ ψ χ : PAFormula) :
      PAProvable (.imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (.or φ ψ) χ)))
  | all_imp (x : ℕ) (φ ψ : PAFormula) :
      PAProvable (.imp (.all x (.imp φ ψ)) (.imp (.all x φ) (.all x ψ)))
  | all_vacuous (x : ℕ) (φ : PAFormula) (h : φ.hasFree x = false) :
      PAProvable (.imp φ (.all x φ))
  | all_elim (x : ℕ) (t : PATerm) (φ : PAFormula) (h : φ.freeFor x t = true) :
      PAProvable (.imp (.all x φ) (φ.subst x t))
  | ex_intro (x : ℕ) (t : PATerm) (φ : PAFormula) (h : φ.freeFor x t = true) :
      PAProvable (.imp (φ.subst x t) (.ex x φ))
  | ex_elim (x : ℕ) (φ ψ : PAFormula) (h : ψ.hasFree x = false) :
      PAProvable (.imp (.all x (.imp φ ψ)) (.imp (.ex x φ) ψ))
  | eq_refl (t : PATerm) : PAProvable (.eq t t)
  | eq_subst (x : ℕ) (s t : PATerm) (φ : PAFormula)
      (hs : φ.freeFor x s = true) (ht : φ.freeFor x t = true) :
      PAProvable (.imp (.eq s t) (.imp (φ.subst x s) (φ.subst x t)))
  | pa_zero_ne_succ : PAProvable (.not (.eq (.succ (.var 0)) .zero))
  | pa_succ_inj :
      PAProvable (.imp (.eq (.succ (.var 0)) (.succ (.var 1))) (.eq (.var 0) (.var 1)))
  | pa_add_zero : PAProvable (.eq (.add (.var 0) .zero) (.var 0))
  | pa_add_succ :
      PAProvable (.eq (.add (.var 0) (.succ (.var 1))) (.succ (.add (.var 0) (.var 1))))
  | pa_mul_zero : PAProvable (.eq (.mul (.var 0) .zero) .zero)
  | pa_mul_succ :
      PAProvable (.eq (.mul (.var 0) (.succ (.var 1))) (.add (.mul (.var 0) (.var 1)) (.var 0)))
  | pa_ind (x : ℕ) (φ : PAFormula) :
      PAProvable (.imp (φ.subst x .zero)
        (.imp (.all x (.imp φ (φ.subst x (.succ (.var x))))) (.all x φ)))

/-! ### 4a. Arithmetization of Pairing, Gödel's $\beta$-Function, `Halts`, and `ZFInconsistent` -/

/-- Polynomial characterization $2 z = 2 x + (x + y)(x + y + 1)$ of `z = cantorPair x y`. -/
def paCantorPairEq (x y z : PATerm) : PAFormula :=
  let s := PATerm.add x y
  .eq (.mul (.ofNat 2) z) (.add (.mul (.ofNat 2) x) (.mul s (.succ s)))

/-- Gödel's $\beta$-function graph $\beta(c, d, i) = r$, defined by
$\exists q,\; c = q \cdot (1 + (i + 1) d) + r \land r < 1 + (i + 1) d$. -/
def paBetaEq (c d i r : PATerm) : PAFormula :=
  let m := PATerm.succ (.mul (.succ i) d)
  let q := max (max c.freshVar m.freshVar) r.freshVar
  .ex q (.and (.eq c (.add (.mul (.var q) m) r)) (paLt r m))

/-- Symbolic Cantor-pairing expression over variable indices and small natural constants,
used to arithmetize nested Cantor codes without expanding large numerals. -/
inductive PAZFTerm : Type where
  | var (x : ℕ) : PAZFTerm
  | const (n : ℕ) : PAZFTerm
  | pair (a b : PAZFTerm) : PAZFTerm
  deriving DecidableEq, Repr

/-- Number of fresh existential variables allocated when translating a `PAZFTerm`. -/
def PAZFTerm.numVars : PAZFTerm → ℕ
  | .var _ | .const _ => 0
  | .pair a b => 2 + a.numVars + b.numVars

/-- Translate `out = e` into a `PAFormula`, allocating fresh intermediate variables starting at
`base`. -/
def PAZFTerm.eqFormula : PAZFTerm → PATerm → ℕ → PAFormula
  | .var x, out, _ => .eq out (.var x)
  | .const n, out, _ => .eq out (.ofNat n)
  | .pair a b, out, base =>
    .ex base (.ex (base + 1)
      (.and (paCantorPairEq (.var base) (.var (base + 1)) out)
        (.and (a.eqFormula (.var base) (base + 2))
          (b.eqFormula (.var (base + 1)) (base + 2 + a.numVars)))))

/-- Symbolic Cantor code `(q, (h, (L, R)))` of a binary Turing machine configuration. -/
def pzPackCfg (q h : ℕ) (L R : PAZFTerm) : PAZFTerm :=
  .pair (.const q) (.pair (.const h) (.pair L R))

/-- Single-step relation of a 2-symbol Turing machine `M` between configuration codes `.var 4`
and `.var 5`. -/
def paStep {states : ℕ} (M : Machine states 2) : PAFormula :=
  paDisjList <| (List.finRange states).flatMap fun q =>
    (List.finRange 2).flatMap fun h =>
      match M.transition q h with
      | none => []
      | some (w, .right, q') =>
        [0, 1].map fun h' =>
          .ex 6 (.ex 7 (.ex 8 (.ex 9
            (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
              (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
                (.and (.eq (.var 8) (.add (.mul (.ofNat 2) (.var 6)) (.ofNat w.val)))
                  (.eq (.var 7) (.add (.mul (.ofNat 2) (.var 9)) (.ofNat h')))))))))
      | some (w, .left, q') =>
        [0, 1].map fun h' =>
          .ex 6 (.ex 7 (.ex 8 (.ex 9
            (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
              (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
                (.and (.eq (.var 6) (.add (.mul (.ofNat 2) (.var 8)) (.ofNat h')))
                  (.eq (.var 9) (.add (.mul (.ofNat 2) (.var 7)) (.ofNat w.val)))))))))

/-- Undefined-transition (halted) predicate for a 2-symbol Turing machine `M` at configuration
code `.var 4`. -/
def paHalted {states : ℕ} (M : Machine states 2) : PAFormula :=
  paDisjList <| (List.finRange states).flatMap fun q =>
    (List.finRange 2).flatMap fun h =>
      match M.transition q h with
      | some _ => []
      | none => [.ex 6 (.ex 7 ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10))]

/-- Closed $\Sigma_1^0$ $\mathcal{L}_{\mathrm{PA}}$-sentence asserting that the 2-symbol Turing
machine `M` halts when started in state `0` on the all-blank tape (encoded by `0`). -/
def paHalts {states : ℕ} (M : Machine states 2) : PAFormula :=
  .ex 0 (.ex 1 (.ex 2
    (.and (paBetaEq (.var 1) (.var 2) .zero .zero)
      (.and
        (.all 3 (.imp (paLt (.var 3) (.var 0))
          (.ex 4 (.ex 5
            (.and (paBetaEq (.var 1) (.var 2) (.var 3) (.var 4))
              (.and (paBetaEq (.var 1) (.var 2) (.succ (.var 3)) (.var 5))
                (paStep M)))))))
        (.ex 4
          (.and (paBetaEq (.var 1) (.var 2) (.var 0) (.var 4))
            (paHalted M)))))))

/-- Symbolic `PAZFTerm` constructors mirroring `zfEq..axInf`. -/
def pzEq (x y : PAZFTerm) : PAZFTerm := .pair (.pair x y) (.const 0)
/-- Symbolic `PAZFTerm` for `zfMem`. -/
def pzMem (x y : PAZFTerm) : PAZFTerm := .pair (.pair x y) (.const 1)
/-- Symbolic `PAZFTerm` for `zfImp`. -/
def pzImp (φ ψ : PAZFTerm) : PAZFTerm := .pair (.pair φ ψ) (.const 2)
/-- Symbolic `PAZFTerm` for `zfNot`. -/
def pzNot (φ : PAZFTerm) : PAZFTerm := .pair φ (.const 3)
/-- Symbolic `PAZFTerm` for `zfAll`. -/
def pzAll (x φ : PAZFTerm) : PAZFTerm := .pair (.pair x φ) (.const 4)
/-- Symbolic `PAZFTerm` for `zfEx`. -/
def pzEx (x φ : PAZFTerm) : PAZFTerm := pzNot (pzAll x (pzNot φ))
/-- Symbolic `PAZFTerm` for `zfAnd`. -/
def pzAnd (φ ψ : PAZFTerm) : PAZFTerm := pzNot (pzImp φ (pzNot ψ))
/-- Symbolic `PAZFTerm` for `axB1`. -/
def pzB1 (φ ψ χ : PAZFTerm) : PAZFTerm := pzImp (pzImp φ ψ) (pzImp (pzImp ψ χ) (pzImp φ χ))
/-- Symbolic `PAZFTerm` for `axB2`. -/
def pzB2 (φ : PAZFTerm) : PAZFTerm := pzImp (pzImp (pzNot φ) φ) φ
/-- Symbolic `PAZFTerm` for `axB3`. -/
def pzB3 (φ ψ : PAZFTerm) : PAZFTerm := pzImp φ (pzImp (pzNot φ) ψ)
/-- Symbolic `PAZFTerm` for `axB4`. -/
def pzB4 (x φ ψ : PAZFTerm) : PAZFTerm :=
  pzImp (pzAll x (pzImp φ ψ)) (pzImp (pzAll x φ) (pzAll x ψ))
/-- Symbolic `PAZFTerm` for `axB6a`. -/
def pzB6a (x y z : PAZFTerm) : PAZFTerm :=
  pzAnd (pzImp (pzEq x y) (pzAll z (pzEq x y))) (pzImp (pzMem x y) (pzAll z (pzMem x y)))
/-- Symbolic `PAZFTerm` for `axB6b`. -/
def pzB6b (x y φ : PAZFTerm) : PAZFTerm := pzImp (pzAll x (pzAll y φ)) (pzAll y (pzAll x φ))
/-- Symbolic `PAZFTerm` for `axB6c`. -/
def pzB6c (x φ : PAZFTerm) : PAZFTerm := pzImp (pzEx x (pzAll x φ)) φ
/-- Symbolic `PAZFTerm` for `axB7`. -/
def pzB7 (x y : PAZFTerm) : PAZFTerm := pzEx x (pzEq x y)
/-- Symbolic `PAZFTerm` for `axB8a`. -/
def pzB8a (x y z : PAZFTerm) : PAZFTerm := pzImp (pzEq x y) (pzImp (pzEq x z) (pzEq y z))
/-- Symbolic `PAZFTerm` for `axB8b`. -/
def pzB8b (x y z : PAZFTerm) : PAZFTerm := pzImp (pzEq x y) (pzImp (pzMem x z) (pzMem y z))
/-- Symbolic `PAZFTerm` for `axB8c`. -/
def pzB8c (x y z : PAZFTerm) : PAZFTerm := pzImp (pzEq x y) (pzImp (pzMem z x) (pzMem z y))
/-- Symbolic `PAZFTerm` for `axExt`. -/
def pzExt : PAZFTerm :=
  pzImp
    (pzAll (.const 2)
      (pzAnd (pzImp (pzMem (.const 2) (.const 0)) (pzMem (.const 2) (.const 1)))
        (pzImp (pzMem (.const 2) (.const 1)) (pzMem (.const 2) (.const 0)))))
    (pzEq (.const 0) (.const 1))
/-- Symbolic `PAZFTerm` for `axRepRhs`. -/
def pzRepRhs (φ : PAZFTerm) : PAZFTerm :=
  pzEx (.const 3) (pzAnd (pzMem (.const 3) (.const 0)) (pzAll (.const 1) φ))
/-- Symbolic `PAZFTerm` for `axRep`. -/
def pzRep (φ : PAZFTerm) : PAZFTerm :=
  pzImp
    (pzAll (.const 3)
      (pzEx (.const 1)
        (pzAll (.const 2) (pzImp (pzAll (.const 1) φ) (pzEq (.const 2) (.const 1))))))
    (pzEx (.const 1)
      (pzAll (.const 2)
        (pzAnd (pzImp (pzMem (.const 2) (.const 1)) (pzRepRhs φ))
          (pzImp (pzRepRhs φ) (pzMem (.const 2) (.const 1))))))
/-- Symbolic `PAZFTerm` for `axPow`. -/
def pzPow : PAZFTerm :=
  pzEx (.const 1)
    (pzAll (.const 2)
      (pzImp (pzAll (.const 3) (pzImp (pzMem (.const 3) (.const 2)) (pzMem (.const 3) (.const 0))))
        (pzMem (.const 2) (.const 1))))
/-- Symbolic `PAZFTerm` for `axUni`. -/
def pzUni : PAZFTerm :=
  pzEx (.const 1)
    (pzAll (.const 2)
      (pzImp (pzEx (.const 3) (pzAnd (pzMem (.const 2) (.const 3)) (pzMem (.const 3) (.const 0))))
        (pzMem (.const 2) (.const 1))))
/-- Symbolic `PAZFTerm` for `axInfSingleton`. -/
def pzInfSingleton : PAZFTerm :=
  pzAll (.const 1)
    (pzAnd (pzImp (pzMem (.const 1) (.const 2)) (pzEq (.const 1) (.const 0)))
      (pzImp (pzEq (.const 1) (.const 0)) (pzMem (.const 1) (.const 2))))
/-- Symbolic `PAZFTerm` for `axInf`. -/
def pzInf : PAZFTerm :=
  pzEx (.const 1)
    (pzAnd (pzMem (.const 0) (.const 1))
      (pzAll (.const 0)
        (pzImp (pzMem (.const 0) (.const 1))
          (pzEx (.const 2) (pzAnd (pzMem (.const 2) (.const 1)) pzInfSingleton)))))

/-- Validity of step `i = .var 3` (with formula code `w = .var 4`) in a $\beta$-coded `ZFProvable`
derivation `(c = .var 1, d = .var 2)`. -/
def paIsZFStep : PAFormula :=
  paDisjList
    [ (pzEq (.const 0) (.const 0)).eqFormula (.var 4) 10
    , .ex 5 (.ex 6 (.ex 8 (.ex 9
        (.and (paLt (.var 8) (.var 3))
          (.and (paLt (.var 9) (.var 3))
            (.and (paBetaEq (.var 1) (.var 2) (.var 8) (.var 5))
              (.and (paBetaEq (.var 1) (.var 2) (.var 9) (.var 6))
                ((pzImp (.var 5) (.var 4)).eqFormula (.var 6) 10))))))))
    , .ex 5 (.ex 6 (.ex 8
        (.and (paLt (.var 8) (.var 3))
          (.and (paBetaEq (.var 1) (.var 2) (.var 8) (.var 6))
            ((pzAll (.var 5) (.var 6)).eqFormula (.var 4) 10)))))
    , .ex 5 (.ex 6 (.ex 7 ((pzB1 (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 ((pzB2 (.var 5)).eqFormula (.var 4) 10)
    , .ex 5 (.ex 6 ((pzB3 (.var 5) (.var 6)).eqFormula (.var 4) 10))
    , .ex 5 (.ex 6 (.ex 7 ((pzB4 (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 (.ex 7
        (.and (paNe (.var 5) (.var 7))
          (.and (paNe (.var 7) (.var 6))
            ((pzB6a (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))))
    , .ex 5 (.ex 6 (.ex 7 ((pzB6b (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 ((pzB6c (.var 5) (.var 6)).eqFormula (.var 4) 10))
    , .ex 5 (.ex 6 ((pzB7 (.var 5) (.var 6)).eqFormula (.var 4) 10))
    , .ex 5 (.ex 6 (.ex 7 ((pzB8a (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 (.ex 7 ((pzB8b (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 (.ex 7 ((pzB8c (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , pzExt.eqFormula (.var 4) 10
    , .ex 5 ((pzRep (.var 5)).eqFormula (.var 4) 10)
    , pzPow.eqFormula (.var 4) 10
    , pzUni.eqFormula (.var 4) 10
    , pzInf.eqFormula (.var 4) 10 ]

/-- Closed $\Sigma_1^0$ $\mathcal{L}_{\mathrm{PA}}$-sentence asserting `ZFInconsistent`
($\mathrm{ZF} \vdash v_0 \in v_0$). -/
def paZFInconsistent : PAFormula :=
  .ex 0 (.ex 1 (.ex 2
    (.and
      (.all 3 (.imp (paLe (.var 3) (.var 0))
        (.ex 4 (.and (paBetaEq (.var 1) (.var 2) (.var 3) (.var 4)) paIsZFStep))))
      (.ex 4
        (.and (paBetaEq (.var 1) (.var 2) (.var 0) (.var 4))
          ((pzMem (.const 0) (.const 0)).eqFormula (.var 4) 10))))))

/-! ## 5. Erdős's Conjecture on Powers of Two -/

/-- **Erdős's conjecture on powers of two** (Erdős 1979): for every `n > 8`, the base-3
expansion of `2 ^ n` contains the digit `2`. -/
def ErdosPowersOfTwoConjecture : Prop :=
  ∀ n : ℕ, 8 < n → 2 ∈ Nat.digits 3 (2 ^ n)

end ConjectureMachines
