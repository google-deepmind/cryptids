/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Propositions

/-!
# Syntax, Substitution, Model Semantics, and Consistency of `PAProvable`

This module develops the foundational metatheory of the deeply embedded Peano Arithmetic system
`PAProvable` (`Cryptids.Propositions`):

1. **General $\mathcal{L}_{\mathrm{PA}}$-structures and models (`PAStructure`, `PAModel`)**:
   Evaluates `PATerm` and `PAFormula` in an arbitrary $\mathcal{L}_{\mathrm{PA}}$-structure `M`
   (`evalIn`, `HoldsIn`), proves variable-agreement and capture-avoiding substitution lemmas
   (`evalIn_subst`, `holdsIn_subst`), and establishes classical soundness of `PAProvable` across
   all models `M` of $\mathrm{PA}$ (`paProvable_sound`, `paProvable_sound_nat`).
2. **Constructive consistency (`NHolds`, `not_paProvable_false`)**:
   Interprets `PAFormula` in `ℕ` via the Gödel–Gentzen negative translation `NHolds`, proving
   `¬ PAProvable .bot` constructively without `Classical.choice`.
-/

@[expose] public section

namespace ConjectureMachines.Semantics.PA

/-! ## Section 1: $\mathcal{L}_{\mathrm{PA}}$-Structures and Models -/

/-- Interpretation of the signature $\mathcal{L}_{\mathrm{PA}} = \{0, S, +, \times\}$ on a carrier
type `M`. -/
class PAStructure (M : Type*) where
  /-- Interpretation of `0`. -/
  zero : M
  /-- Interpretation of successor $S$. -/
  succ : M → M
  /-- Interpretation of addition $+$. -/
  add : M → M → M
  /-- Interpretation of multiplication $\times$. -/
  mul : M → M → M

/-- Standard $\mathcal{L}_{\mathrm{PA}}$-structure on `ℕ`. -/
instance instPAStructureNat : PAStructure ℕ where
  zero := 0
  succ n := n + 1
  add := (· + ·)
  mul := (· * ·)

/-- Evaluate a `PATerm` in an $\mathcal{L}_{\mathrm{PA}}$-structure `M` under assignment `v`. -/
def PATerm.evalIn {M : Type*} [PAStructure M] (v : ℕ → M) : PATerm → M
  | .var x => v x
  | .zero => PAStructure.zero
  | .succ t => PAStructure.succ (PATerm.evalIn v t)
  | .add t₁ t₂ => PAStructure.add (PATerm.evalIn v t₁) (PATerm.evalIn v t₂)
  | .mul t₁ t₂ => PAStructure.mul (PATerm.evalIn v t₁) (PATerm.evalIn v t₂)

/-- Tarski satisfaction of a `PAFormula` in an $\mathcal{L}_{\mathrm{PA}}$-structure `M` under
assignment `v`. -/
def PAFormula.HoldsIn {M : Type*} [PAStructure M] (v : ℕ → M) : PAFormula → Prop
  | .bot => False
  | .eq t₁ t₂ => PATerm.evalIn v t₁ = PATerm.evalIn v t₂
  | .and φ ψ => PAFormula.HoldsIn v φ ∧ PAFormula.HoldsIn v ψ
  | .or φ ψ => PAFormula.HoldsIn v φ ∨ PAFormula.HoldsIn v ψ
  | .imp φ ψ => PAFormula.HoldsIn v φ → PAFormula.HoldsIn v ψ
  | .all x φ => ∀ a : M, PAFormula.HoldsIn (Function.update v x a) φ
  | .ex x φ => ∃ a : M, PAFormula.HoldsIn (Function.update v x a) φ

/-- A first-order model of Peano Arithmetic (`PA`): an $\mathcal{L}_{\mathrm{PA}}$-structure
satisfying the six Robinson `Q` axioms together with the first-order induction schema for every
`PAFormula`. -/
class PAModel (M : Type*) [PAStructure M] : Prop where
  zero_ne_succ : ∀ a : M, PAStructure.succ a ≠ PAStructure.zero
  succ_inj : ∀ {a b : M}, PAStructure.succ a = PAStructure.succ b → a = b
  add_zero : ∀ a : M, PAStructure.add a PAStructure.zero = a
  add_succ : ∀ a b : M, PAStructure.add a (PAStructure.succ b) =
    PAStructure.succ (PAStructure.add a b)
  mul_zero : ∀ a : M, PAStructure.mul a PAStructure.zero = PAStructure.zero
  mul_succ : ∀ a b : M, PAStructure.mul a (PAStructure.succ b) =
    PAStructure.add (PAStructure.mul a b) a
  ind : ∀ (x : ℕ) (φ : PAFormula) (v : ℕ → M),
    PAFormula.HoldsIn (Function.update v x PAStructure.zero) φ →
    (∀ a : M, PAFormula.HoldsIn (Function.update v x a) φ →
      PAFormula.HoldsIn (Function.update v x (PAStructure.succ a)) φ) →
    ∀ a : M, PAFormula.HoldsIn (Function.update v x a) φ

/-- The standard natural numbers `ℕ` form a `PAModel`. -/
instance instPAModelNat : PAModel ℕ where
  zero_ne_succ n := Nat.succ_ne_zero n
  succ_inj h := Nat.succ.inj h
  add_zero := Nat.add_zero
  add_succ := Nat.add_succ
  mul_zero := Nat.mul_zero
  mul_succ := Nat.mul_succ
  ind x φ v h0 hs a := by
    induction a with
    | zero => exact h0
    | succ a ih => exact hs a ih

theorem evalIn_nat_eq (v : ℕ → ℕ) (t : PATerm) : PATerm.evalIn v t = t.eval v := by
  induction t with
  | var _ | zero => rfl
  | succ _ ih => exact congrArg (· + 1) ih
  | add _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact congrArg₂ (· * ·) ih₁ ih₂

theorem holdsIn_nat_iff (v : ℕ → ℕ) (φ : PAFormula) : PAFormula.HoldsIn v φ ↔ φ.Holds v := by
  induction φ generalizing v with
  | bot => exact Iff.rfl
  | eq t₁ t₂ => simp only [PAFormula.HoldsIn, PAFormula.Holds, evalIn_nat_eq]
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ v) (ih₂ v)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ v) (ih₂ v)
  | imp _ _ ih₁ ih₂ => exact imp_congr (ih₁ v) (ih₂ v)
  | all x _ ih => exact forall_congr' fun a ↦ ih (Function.update v x a)
  | ex x _ ih => exact exists_congr fun a ↦ ih (Function.update v x a)

/-! ## Section 2: Freshness, Variable Agreement, and Substitution Lemmas -/

theorem hasVar_false_of_freshVar_le {t : PATerm} {x : ℕ} (h : t.freshVar ≤ x) :
    t.hasVar x = false := by
  induction t with
  | var y =>
    simp only [PATerm.freshVar] at h
    simp only [PATerm.hasVar, beq_eq_false_iff_ne]
    omega
  | zero => rfl
  | succ t ih => exact ih h
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    simp only [PATerm.freshVar, Nat.max_le] at h
    simp only [PATerm.hasVar, Bool.or_eq_false_iff]
    exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem evalIn_congr {M : Type*} [PAStructure M] {v₁ v₂ : ℕ → M} {t : PATerm}
    (h : ∀ x, t.hasVar x = true → v₁ x = v₂ x) :
    PATerm.evalIn v₁ t = PATerm.evalIn v₂ t := by
  induction t with
  | var x => exact h x (by simp [PATerm.hasVar])
  | zero => rfl
  | succ t ih => exact congrArg PAStructure.succ (ih h)
  | add t₁ t₂ ih₁ ih₂ =>
    refine congrArg₂ PAStructure.add (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PATerm.hasVar, hx]
  | mul t₁ t₂ ih₁ ih₂ =>
    refine congrArg₂ PAStructure.mul (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PATerm.hasVar, hx]

theorem evalIn_update_of_hasVar_false {M : Type*} [PAStructure M] (v : ℕ → M)
    {x : ℕ} (a : M) {t : PATerm} (hx : t.hasVar x = false) :
    PATerm.evalIn (Function.update v x a) t = PATerm.evalIn v t := by
  refine evalIn_congr fun y hy ↦ ?_
  have hne : y ≠ x := fun h ↦ by subst h; rw [hx] at hy; cases hy
  exact Function.update_of_ne hne a v

theorem holdsIn_congr {M : Type*} [PAStructure M] {v₁ v₂ : ℕ → M} {φ : PAFormula}
    (h : ∀ x, φ.hasFree x = true → v₁ x = v₂ x) :
    PAFormula.HoldsIn v₁ φ ↔ PAFormula.HoldsIn v₂ φ := by
  induction φ generalizing v₁ v₂ with
  | bot => exact Iff.rfl
  | eq t₁ t₂ =>
    have e₁ : PATerm.evalIn v₁ t₁ = PATerm.evalIn v₂ t₁ :=
      evalIn_congr fun x hx ↦ h x (by simp [PAFormula.hasFree, hx])
    have e₂ : PATerm.evalIn v₁ t₂ = PATerm.evalIn v₂ t₂ :=
      evalIn_congr fun x hx ↦ h x (by simp [PAFormula.hasFree, hx])
    simp only [PAFormula.HoldsIn, e₁, e₂]
  | and φ ψ ih₁ ih₂ =>
    refine and_congr (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | or φ ψ ih₁ ih₂ =>
    refine or_congr (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | imp φ ψ ih₁ ih₂ =>
    refine imp_congr (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | all y φ ih =>
    refine forall_congr' fun a ↦ ih fun x hx ↦ ?_
    by_cases hxy : x = y
    · subst hxy; simp
    · simp only [Function.update_of_ne hxy]
      exact h x (by simp [PAFormula.hasFree, Ne.symm hxy, hx])
  | ex y φ ih =>
    refine exists_congr fun a ↦ ih fun x hx ↦ ?_
    by_cases hxy : x = y
    · subst hxy; simp
    · simp only [Function.update_of_ne hxy]
      exact h x (by simp [PAFormula.hasFree, Ne.symm hxy, hx])

theorem holdsIn_update_of_hasFree_false {M : Type*} [PAStructure M] (v : ℕ → M)
    {x : ℕ} (a : M) {φ : PAFormula} (hx : φ.hasFree x = false) :
    PAFormula.HoldsIn (Function.update v x a) φ ↔ PAFormula.HoldsIn v φ := by
  refine holdsIn_congr fun y hy ↦ ?_
  have hne : y ≠ x := fun h ↦ by subst h; rw [hx] at hy; cases hy
  exact Function.update_of_ne hne a v

theorem evalIn_subst {M : Type*} [PAStructure M] (v : ℕ → M) (x : ℕ) (s t : PATerm) :
    PATerm.evalIn v (t.subst x s) = PATerm.evalIn (Function.update v x (PATerm.evalIn v s)) t := by
  induction t with
  | var y =>
    simp only [PATerm.subst]
    by_cases hxy : y = x
    · subst hxy; simp [PATerm.evalIn]
    · simp [hxy, PATerm.evalIn]
  | zero => rfl
  | succ t ih => exact congrArg PAStructure.succ ih
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ PAStructure.add ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ PAStructure.mul ih₁ ih₂

theorem subst_eq_self_of_hasFree_false {φ : PAFormula} {x : ℕ} (s : PATerm)
    (hx : φ.hasFree x = false) : φ.subst x s = φ := by
  have term_eq : ∀ {t : PATerm}, t.hasVar x = false → t.subst x s = t := by
    intro t ht
    induction t with
    | var y =>
      simp only [PATerm.hasVar, beq_eq_false_iff_ne] at ht
      simp [PATerm.subst, ht]
    | zero => rfl
    | succ t ih => exact congrArg PATerm.succ (ih ht)
    | add t₁ t₂ ih₁ ih₂ =>
      simp only [PATerm.hasVar, Bool.or_eq_false_iff] at ht
      exact congrArg₂ PATerm.add (ih₁ ht.1) (ih₂ ht.2)
    | mul t₁ t₂ ih₁ ih₂ =>
      simp only [PATerm.hasVar, Bool.or_eq_false_iff] at ht
      exact congrArg₂ PATerm.mul (ih₁ ht.1) (ih₂ ht.2)
  induction φ with
  | bot => rfl
  | eq t₁ t₂ =>
    simp only [PAFormula.hasFree, Bool.or_eq_false_iff] at hx
    exact congrArg₂ PAFormula.eq (term_eq hx.1) (term_eq hx.2)
  | and φ ψ ih₁ ih₂ =>
    simp only [PAFormula.hasFree, Bool.or_eq_false_iff] at hx
    exact congrArg₂ PAFormula.and (ih₁ hx.1) (ih₂ hx.2)
  | or φ ψ ih₁ ih₂ =>
    simp only [PAFormula.hasFree, Bool.or_eq_false_iff] at hx
    exact congrArg₂ PAFormula.or (ih₁ hx.1) (ih₂ hx.2)
  | imp φ ψ ih₁ ih₂ =>
    simp only [PAFormula.hasFree, Bool.or_eq_false_iff] at hx
    exact congrArg₂ PAFormula.imp (ih₁ hx.1) (ih₂ hx.2)
  | all y φ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · simp [hxy]
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [PAFormula.hasFree, hb, Bool.not_false, Bool.true_and] at hx
      simp [hb, ih hx]
  | ex y φ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · simp [hxy]
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [PAFormula.hasFree, hb, Bool.not_false, Bool.true_and] at hx
      simp [hb, ih hx]

theorem holdsIn_subst {M : Type*} [PAStructure M] (v : ℕ → M) {x : ℕ} {s : PATerm} {φ : PAFormula}
    (hf : φ.freeFor x s = true) :
    PAFormula.HoldsIn v (φ.subst x s) ↔
      PAFormula.HoldsIn (Function.update v x (PATerm.evalIn v s)) φ := by
  induction φ generalizing v with
  | bot => exact Iff.rfl
  | eq t₁ t₂ => simp only [PAFormula.subst, PAFormula.HoldsIn, evalIn_subst]
  | and φ ψ ih₁ ih₂ =>
    simp only [PAFormula.freeFor, Bool.and_eq_true] at hf
    exact and_congr (ih₁ v hf.1) (ih₂ v hf.2)
  | or φ ψ ih₁ ih₂ =>
    simp only [PAFormula.freeFor, Bool.and_eq_true] at hf
    exact or_congr (ih₁ v hf.1) (ih₂ v hf.2)
  | imp φ ψ ih₁ ih₂ =>
    simp only [PAFormula.freeFor, Bool.and_eq_true] at hf
    exact imp_congr (ih₁ v hf.1) (ih₂ v hf.2)
  | all y φ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · subst hxy
      simp only [beq_self_eq_true, ↓reduceIte, PAFormula.HoldsIn]
      refine forall_congr' fun a ↦ ?_
      rw [Function.update_idem]
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [hb, Bool.false_eq_true, ↓reduceIte, PAFormula.HoldsIn]
      simp only [PAFormula.freeFor, hb, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true'] at hf
      rcases hf with ⟨hno | hsy, hf'⟩
      · refine forall_congr' fun a ↦ ?_
        rw [subst_eq_self_of_hasFree_false s hno, Function.update_comm (Ne.symm hxy),
          holdsIn_update_of_hasFree_false _ _ hno]
      · refine forall_congr' fun a ↦ ?_
        rw [ih (Function.update v y a) hf', evalIn_update_of_hasVar_false v a hsy,
          Function.update_comm hxy]
  | ex y φ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · subst hxy
      simp only [beq_self_eq_true, ↓reduceIte, PAFormula.HoldsIn]
      refine exists_congr fun a ↦ ?_
      rw [Function.update_idem]
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [hb, Bool.false_eq_true, ↓reduceIte, PAFormula.HoldsIn]
      simp only [PAFormula.freeFor, hb, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true'] at hf
      rcases hf with ⟨hno | hsy, hf'⟩
      · refine exists_congr fun a ↦ ?_
        rw [subst_eq_self_of_hasFree_false s hno, Function.update_comm (Ne.symm hxy),
          holdsIn_update_of_hasFree_false _ _ hno]
      · refine exists_congr fun a ↦ ?_
        rw [ih (Function.update v y a) hf', evalIn_update_of_hasVar_false v a hsy,
          Function.update_comm hxy]

theorem freeFor_of_no_vars {x : ℕ} {s : PATerm} (hs : ∀ y, s.hasVar y = false) (φ : PAFormula) :
    φ.freeFor x s = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp [PAFormula.freeFor, ih₁, ih₂]
  | all y _ ih | ex y _ ih =>
    simp [PAFormula.freeFor, hs y, ih]

theorem freeFor_zero (x : ℕ) (φ : PAFormula) : φ.freeFor x .zero = true :=
  freeFor_of_no_vars (fun _ ↦ rfl) φ

theorem freeFor_ofNat (x n : ℕ) (φ : PAFormula) : φ.freeFor x (.ofNat n) = true := by
  refine freeFor_of_no_vars (fun y ↦ ?_) φ
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

theorem freeFor_succ_self (x : ℕ) (φ : PAFormula) :
    φ.freeFor x (.succ (.var x)) = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp [PAFormula.freeFor, ih₁, ih₂]
  | all y φ ih | ex y φ ih =>
    simp only [PAFormula.freeFor, PATerm.hasVar]
    by_cases hxy : y = x
    · simp [hxy]
    · simp [hxy, Ne.symm hxy, ih]

/-! ## Section 3: Classical Soundness of `PAProvable` Across All `PAModel`s -/

/-- Soundness of `PAProvable` in every first-order `PAModel`. -/
theorem paProvable_sound {M : Type*} [PAStructure M] [PAModel M] {φ : PAFormula}
    (h : PAProvable φ) (v : ℕ → M) : PAFormula.HoldsIn v φ := by
  induction h generalizing v with
  | mp _ _ ihφ ihimp => exact ihimp v (ihφ v)
  | gen x _ ih => intro a; exact ih (Function.update v x a)
  | imp_k _ _ => intro h₁ _; exact h₁
  | imp_s _ _ _ => intro h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)
  | dne _ => exact Classical.not_not.mp
  | and_intro _ _ => exact And.intro
  | and_left _ _ => exact And.left
  | and_right _ _ => exact And.right
  | or_left _ _ => exact Or.inl
  | or_right _ _ => exact Or.inr
  | or_elim _ _ _ =>
    intro h₁ h₂ h₃
    exact h₃.elim h₁ h₂
  | all_imp x _ _ =>
    intro h₁ h₂ a
    exact h₁ a (h₂ a)
  | all_vacuous x φ hx =>
    intro hφ a
    exact (holdsIn_update_of_hasFree_false v a hx).mpr hφ
  | all_elim x t φ hf =>
    intro hall
    exact (holdsIn_subst v hf).mpr (hall (PATerm.evalIn v t))
  | ex_intro x t φ hf =>
    intro hsub
    exact ⟨PATerm.evalIn v t, (holdsIn_subst v hf).mp hsub⟩
  | ex_elim x φ ψ hx =>
    rintro hall ⟨a, ha⟩
    exact (holdsIn_update_of_hasFree_false v a hx).mp (hall a ha)
  | eq_refl _ => rfl
  | eq_subst x s t φ hs ht =>
    intro heq hφs
    have h1 := (holdsIn_subst v hs).mp hφs
    rw [heq] at h1
    exact (holdsIn_subst v ht).mpr h1
  | pa_zero_ne_succ => exact PAModel.zero_ne_succ (v 0)
  | pa_succ_inj => exact PAModel.succ_inj
  | pa_add_zero => exact PAModel.add_zero (v 0)
  | pa_add_succ => exact PAModel.add_succ (v 0) (v 1)
  | pa_mul_zero => exact PAModel.mul_zero (v 0)
  | pa_mul_succ => exact PAModel.mul_succ (v 0) (v 1)
  | pa_ind x φ =>
    intro h0 hs a
    have h0' : PAFormula.HoldsIn (Function.update v x PAStructure.zero) φ :=
      (holdsIn_subst v (freeFor_zero x φ)).mp h0
    have hs' : ∀ b : M, PAFormula.HoldsIn (Function.update v x b) φ →
        PAFormula.HoldsIn (Function.update v x (PAStructure.succ b)) φ := by
      intro b hb
      have hstep := hs b hb
      have hsub := (holdsIn_subst (Function.update v x b) (freeFor_succ_self x φ)).mp hstep
      simpa [PATerm.evalIn] using hsub
    exact PAModel.ind x φ v h0' hs' a

/-- Soundness of `PAProvable` in the standard model `ℕ`. -/
theorem paProvable_sound_nat (φ : PAFormula) (h : PAProvable φ) (v : ℕ → ℕ) : φ.Holds v :=
  (holdsIn_nat_iff v φ).mp (paProvable_sound h v)

/-! ## Section 4: Zero-Axiom Consistency via Negative Translation (`not_paProvable_false`) -/

/-- Environment update avoiding `Function.update` so `not_paProvable_false` uses zero axioms. -/
def envUpdate (v : ℕ → ℕ) (x a y : ℕ) : ℕ :=
  match Nat.decEq y x with
  | isTrue _ => a
  | isFalse _ => v y

private theorem envUpdate_self (v : ℕ → ℕ) (x a : ℕ) : envUpdate v x a x = a := by
  dsimp only [envUpdate]
  cases Nat.decEq x x with
  | isTrue _ => rfl
  | isFalse h => exact False.elim (h rfl)

private theorem envUpdate_of_ne (v : ℕ → ℕ) {x y : ℕ} (h : y ≠ x) (a : ℕ) :
    envUpdate v x a y = v y := by
  dsimp only [envUpdate]
  cases Nat.decEq y x with
  | isTrue he => exact False.elim (h he)
  | isFalse _ => rfl

/-- Gödel–Gentzen negative satisfaction of a `PAFormula` in `ℕ`, replacing positive disjunction
and existential quantification by their double-negated counterparts so every formula is
constructively `¬¬`-stable with zero axioms (`[]`). -/
def PAFormula.NHolds (v : ℕ → ℕ) : PAFormula → Prop
  | .bot => False
  | .eq t₁ t₂ => t₁.eval v = t₂.eval v
  | .and φ ψ => PAFormula.NHolds v φ ∧ PAFormula.NHolds v ψ
  | .or φ ψ => ¬¬ (PAFormula.NHolds v φ ∨ PAFormula.NHolds v ψ)
  | .imp φ ψ => PAFormula.NHolds v φ → PAFormula.NHolds v ψ
  | .all x φ => ∀ a : ℕ, PAFormula.NHolds (envUpdate v x a) φ
  | .ex x φ => ¬¬ ∃ a : ℕ, PAFormula.NHolds (envUpdate v x a) φ

private theorem nat_beq_refl : ∀ x : ℕ, (x == x) = true
  | 0 => rfl
  | x + 1 => nat_beq_refl x

private theorem nat_beq_eq_false : ∀ {x y : ℕ}, x ≠ y → (x == y) = false
  | 0, 0, h => False.elim (h rfl)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | x + 1, y + 1, h => nat_beq_eq_false (x := x) (y := y) fun heq ↦ h (congrArg (· + 1) heq)

private theorem bool_or_inl {a b : Bool} (ha : a = true) : (a || b) = true := by
  rw [ha]; rfl

private theorem bool_or_inr {a b : Bool} (hb : b = true) : (a || b) = true := by
  cases a with
  | true => rfl
  | false => exact hb

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact h

private theorem bool_or_false_left {a b : Bool} (h : (a || b) = false) : a = false := by
  cases a with
  | false => rfl
  | true => exact Bool.noConfusion h

private theorem bool_or_false_right {a b : Bool} (h : (a || b) = false) : b = false := by
  cases a with
  | false => exact h
  | true => exact Bool.noConfusion h

private theorem bool_or_cases {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

private theorem bool_not_eq_true_iff {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => exact Bool.noConfusion h

private theorem iff_and_zero {A B C D : Prop} (h₁ : A ↔ C) (h₂ : B ↔ D) :
    (A ∧ B) ↔ (C ∧ D) :=
  ⟨fun ⟨a, b⟩ ↦ ⟨h₁.mp a, h₂.mp b⟩, fun ⟨c, d⟩ ↦ ⟨h₁.mpr c, h₂.mpr d⟩⟩

private theorem iff_imp_zero {A B C D : Prop} (h₁ : A ↔ C) (h₂ : B ↔ D) :
    (A → B) ↔ (C → D) :=
  ⟨fun f c ↦ h₂.mp (f (h₁.mpr c)), fun g a ↦ h₂.mpr (g (h₁.mp a))⟩

private theorem iff_nn_or_zero {A B C D : Prop} (h₁ : A ↔ C) (h₂ : B ↔ D) :
    ¬¬ (A ∨ B) ↔ ¬¬ (C ∨ D) :=
  ⟨fun h hn ↦ h fun d ↦ hn (d.elim (fun a ↦ Or.inl (h₁.mp a)) (fun b ↦ Or.inr (h₂.mp b))),
   fun h hn ↦ h fun d ↦ hn (d.elim (fun c ↦ Or.inl (h₁.mpr c)) (fun d ↦ Or.inr (h₂.mpr d)))⟩

private theorem iff_all_zero {P Q : ℕ → Prop} (h : ∀ a, P a ↔ Q a) :
    (∀ a, P a) ↔ (∀ a, Q a) :=
  ⟨fun f a ↦ (h a).mp (f a), fun g a ↦ (h a).mpr (g a)⟩

private theorem iff_nn_ex_zero {P Q : ℕ → Prop} (h : ∀ a, P a ↔ Q a) :
    (¬¬ ∃ a, P a) ↔ (¬¬ ∃ a, Q a) :=
  ⟨fun f hn ↦ f fun ⟨a, pa⟩ ↦ hn ⟨a, (h a).mp pa⟩,
   fun g hn ↦ g fun ⟨a, qa⟩ ↦ hn ⟨a, (h a).mpr qa⟩⟩

theorem nHolds_stable (φ : PAFormula) (v : ℕ → ℕ) :
    ¬¬ PAFormula.NHolds v φ → PAFormula.NHolds v φ := by
  induction φ generalizing v with
  | bot => intro h; exact h id
  | eq t₁ t₂ =>
    intro h
    cases Nat.decEq (t₁.eval v) (t₂.eval v) with
    | isFalse hne => exact False.elim (h hne)
    | isTrue he => exact he
  | and φ ψ ih₁ ih₂ =>
    intro h
    exact ⟨ih₁ v fun h₁ ↦ h fun hp ↦ h₁ hp.1, ih₂ v fun h₂ ↦ h fun hp ↦ h₂ hp.2⟩
  | or _ _ _ _ =>
    intro h hn
    exact h fun hnn ↦ hnn hn
  | imp _ ψ _ ih₂ =>
    intro h hφ
    exact ih₂ v fun hψ ↦ h fun himp ↦ hψ (himp hφ)
  | all x φ ih =>
    intro h a
    exact ih (envUpdate v x a) fun ha ↦ h fun hall ↦ ha (hall a)
  | ex _ _ _ =>
    intro h hn
    exact h fun hnn ↦ hnn hn

private theorem eval_congr_zero {v₁ v₂ : ℕ → ℕ} :
    ∀ {t : PATerm}, (∀ x, t.hasVar x = true → v₁ x = v₂ x) → t.eval v₁ = t.eval v₂
  | .var x, h => h x (nat_beq_refl x)
  | .zero, _ => rfl
  | .succ _, h => congrArg (· + 1) (eval_congr_zero h)
  | .add _ _, h =>
    congrArg₂ (· + ·)
      (eval_congr_zero fun x hx ↦ h x (bool_or_inl hx))
      (eval_congr_zero fun x hx ↦ h x (bool_or_inr hx))
  | .mul _ _, h =>
    congrArg₂ (· * ·)
      (eval_congr_zero fun x hx ↦ h x (bool_or_inl hx))
      (eval_congr_zero fun x hx ↦ h x (bool_or_inr hx))

private theorem eval_update_of_hasVar_false_zero (v : ℕ → ℕ) {x : ℕ} (a : ℕ) {t : PATerm}
    (hx : t.hasVar x = false) : t.eval (envUpdate v x a) = t.eval v :=
  eval_congr_zero fun y hy ↦
    have hne : y ≠ x := fun h ↦ by subst h; rw [hx] at hy; exact Bool.noConfusion hy
    envUpdate_of_ne v hne a

private theorem eval_subst_zero (v : ℕ → ℕ) (x : ℕ) (s : PATerm) :
    ∀ t : PATerm, (t.subst x s).eval v = t.eval (envUpdate v x (s.eval v))
  | .var y => by
    dsimp only [PATerm.subst]
    cases Nat.decEq y x with
    | isTrue h =>
      subst h
      rw [nat_beq_refl]
      exact (envUpdate_self v y (s.eval v)).symm
    | isFalse h =>
      rw [nat_beq_eq_false h]
      exact (envUpdate_of_ne v h (s.eval v)).symm
  | .zero => rfl
  | .succ t => congrArg (· + 1) (eval_subst_zero v x s t)
  | .add t₁ t₂ => congrArg₂ (· + ·) (eval_subst_zero v x s t₁) (eval_subst_zero v x s t₂)
  | .mul t₁ t₂ => congrArg₂ (· * ·) (eval_subst_zero v x s t₁) (eval_subst_zero v x s t₂)

private theorem term_subst_eq_self_zero {x : ℕ} (s : PATerm) :
    ∀ {t : PATerm}, t.hasVar x = false → t.subst x s = t
  | .var y, ht => by
    dsimp only [PATerm.subst]
    have hyx : (y == x) = false := by
      cases Nat.decEq y x with
      | isTrue h =>
        subst h
        change (y == y) = false at ht
        rw [nat_beq_refl] at ht
        exact Bool.noConfusion ht
      | isFalse h => exact nat_beq_eq_false h
    rw [hyx]
    rfl
  | .zero, _ => rfl
  | .succ _, ht => congrArg PATerm.succ (term_subst_eq_self_zero s ht)
  | .add _ _, ht =>
    congrArg₂ PATerm.add
      (term_subst_eq_self_zero s (bool_or_false_left ht))
      (term_subst_eq_self_zero s (bool_or_false_right ht))
  | .mul _ _, ht =>
    congrArg₂ PATerm.mul
      (term_subst_eq_self_zero s (bool_or_false_left ht))
      (term_subst_eq_self_zero s (bool_or_false_right ht))

private theorem subst_eq_self_zero {x : ℕ} (s : PATerm) :
    ∀ {φ : PAFormula}, φ.hasFree x = false → φ.subst x s = φ
  | .bot, _ => rfl
  | .eq _ _, hx =>
    congrArg₂ PAFormula.eq
      (term_subst_eq_self_zero s (bool_or_false_left hx))
      (term_subst_eq_self_zero s (bool_or_false_right hx))
  | .and _ _, hx =>
    congrArg₂ PAFormula.and
      (subst_eq_self_zero s (bool_or_false_left hx))
      (subst_eq_self_zero s (bool_or_false_right hx))
  | .or _ _, hx =>
    congrArg₂ PAFormula.or
      (subst_eq_self_zero s (bool_or_false_left hx))
      (subst_eq_self_zero s (bool_or_false_right hx))
  | .imp _ _, hx =>
    congrArg₂ PAFormula.imp
      (subst_eq_self_zero s (bool_or_false_left hx))
      (subst_eq_self_zero s (bool_or_false_right hx))
  | .all y φ, hx => by
    dsimp only [PAFormula.subst]
    cases Nat.decEq y x with
    | isTrue h =>
      subst h
      rw [nat_beq_refl]
      rfl
    | isFalse h =>
      have hb : (y == x) = false := nat_beq_eq_false h
      rw [hb]
      have hfree : φ.hasFree x = false := by
        change (!(y == x) && φ.hasFree x) = false at hx
        rw [hb] at hx
        exact hx
      exact congrArg (PAFormula.all y) (subst_eq_self_zero s hfree)
  | .ex y φ, hx => by
    dsimp only [PAFormula.subst]
    cases Nat.decEq y x with
    | isTrue h =>
      subst h
      rw [nat_beq_refl]
      rfl
    | isFalse h =>
      have hb : (y == x) = false := nat_beq_eq_false h
      rw [hb]
      have hfree : φ.hasFree x = false := by
        change (!(y == x) && φ.hasFree x) = false at hx
        rw [hb] at hx
        exact hx
      exact congrArg (PAFormula.ex y) (subst_eq_self_zero s hfree)

private theorem freeFor_zero_zero (x : ℕ) : ∀ φ : PAFormula, φ.freeFor x .zero = true
  | .bot | .eq _ _ => rfl
  | .and φ ψ | .or φ ψ | .imp φ ψ => by
    change (φ.freeFor x .zero && ψ.freeFor x .zero) = true
    rw [freeFor_zero_zero x φ, freeFor_zero_zero x ψ]
    rfl
  | .all y φ | .ex y φ => by
    change ((y == x) || ((!φ.hasFree x || !PATerm.zero.hasVar y) && φ.freeFor x .zero)) = true
    have hor : (!φ.hasFree x || !PATerm.zero.hasVar y) = true := bool_or_inr rfl
    rw [hor, freeFor_zero_zero x φ]
    exact bool_or_inr rfl

private theorem freeFor_succ_self_zero (x : ℕ) :
    ∀ φ : PAFormula, φ.freeFor x (.succ (.var x)) = true
  | .bot | .eq _ _ => rfl
  | .and φ ψ | .or φ ψ | .imp φ ψ => by
    change (φ.freeFor x (.succ (.var x)) && ψ.freeFor x (.succ (.var x))) = true
    rw [freeFor_succ_self_zero x φ, freeFor_succ_self_zero x ψ]
    rfl
  | .all y φ | .ex y φ => by
    change ((y == x) ||
        ((!φ.hasFree x || !(PATerm.succ (.var x)).hasVar y) &&
          φ.freeFor x (.succ (.var x)))) = true
    cases Nat.decEq y x with
    | isTrue h =>
      subst h
      exact bool_or_inl (nat_beq_refl y)
    | isFalse h =>
      have hxy : (x == y) = false := nat_beq_eq_false (Ne.symm h)
      have hnot : (!(PATerm.succ (.var x)).hasVar y) = true := by
        change (!(x == y)) = true
        rw [hxy]
        rfl
      have hor : (!φ.hasFree x || !(PATerm.succ (.var x)).hasVar y) = true := bool_or_inr hnot
      rw [hor, freeFor_succ_self_zero x φ]
      exact bool_or_inr rfl

private theorem nHolds_congr {v₁ v₂ : ℕ → ℕ} {φ : PAFormula}
    (h : ∀ x, φ.hasFree x = true → v₁ x = v₂ x) :
    PAFormula.NHolds v₁ φ ↔ PAFormula.NHolds v₂ φ := by
  induction φ generalizing v₁ v₂ with
  | bot => exact ⟨id, id⟩
  | eq t₁ t₂ =>
    have e₁ : t₁.eval v₁ = t₁.eval v₂ := eval_congr_zero fun x hx ↦ h x (bool_or_inl hx)
    have e₂ : t₂.eval v₁ = t₂.eval v₂ := eval_congr_zero fun x hx ↦ h x (bool_or_inr hx)
    exact ⟨fun he ↦ e₁.symm.trans (he.trans e₂), fun he ↦ e₁.trans (he.trans e₂.symm)⟩
  | and _ _ ih₁ ih₂ =>
    exact iff_and_zero
      (ih₁ fun x hx ↦ h x (bool_or_inl hx))
      (ih₂ fun x hx ↦ h x (bool_or_inr hx))
  | or _ _ ih₁ ih₂ =>
    exact iff_nn_or_zero
      (ih₁ fun x hx ↦ h x (bool_or_inl hx))
      (ih₂ fun x hx ↦ h x (bool_or_inr hx))
  | imp _ _ ih₁ ih₂ =>
    exact iff_imp_zero
      (ih₁ fun x hx ↦ h x (bool_or_inl hx))
      (ih₂ fun x hx ↦ h x (bool_or_inr hx))
  | all y _ ih =>
    refine iff_all_zero fun a ↦ ih fun x hx ↦ ?_
    cases Nat.decEq x y with
    | isTrue heq =>
      subst heq
      exact (envUpdate_self v₁ x a).trans (envUpdate_self v₂ x a).symm
    | isFalse hxy =>
      have hu₁ := envUpdate_of_ne v₁ hxy a
      have hu₂ := envUpdate_of_ne v₂ hxy a
      refine hu₁.trans ((h x ?_).trans hu₂.symm)
      change (!(y == x) && _) = true
      rw [nat_beq_eq_false (Ne.symm hxy)]
      exact hx
  | ex y _ ih =>
    refine iff_nn_ex_zero fun a ↦ ih fun x hx ↦ ?_
    cases Nat.decEq x y with
    | isTrue heq =>
      subst heq
      exact (envUpdate_self v₁ x a).trans (envUpdate_self v₂ x a).symm
    | isFalse hxy =>
      have hu₁ := envUpdate_of_ne v₁ hxy a
      have hu₂ := envUpdate_of_ne v₂ hxy a
      refine hu₁.trans ((h x ?_).trans hu₂.symm)
      change (!(y == x) && _) = true
      rw [nat_beq_eq_false (Ne.symm hxy)]
      exact hx

private theorem nHolds_update_of_hasFree_false (v : ℕ → ℕ) {x : ℕ} (a : ℕ) {φ : PAFormula}
    (hx : φ.hasFree x = false) :
    PAFormula.NHolds (envUpdate v x a) φ ↔ PAFormula.NHolds v φ :=
  nHolds_congr fun y hy ↦
    have hne : y ≠ x := fun h ↦ by subst h; rw [hx] at hy; exact Bool.noConfusion hy
    envUpdate_of_ne v hne a

private theorem nHolds_update_idem (v : ℕ → ℕ) (x a b : ℕ) (φ : PAFormula) :
    PAFormula.NHolds (envUpdate (envUpdate v x a) x b) φ ↔
      PAFormula.NHolds (envUpdate v x b) φ :=
  nHolds_congr fun z _ ↦ by
    cases Nat.decEq z x with
    | isTrue h =>
      subst h
      exact (envUpdate_self (envUpdate v z a) z b).trans (envUpdate_self v z b).symm
    | isFalse hzx =>
      exact (envUpdate_of_ne (envUpdate v x a) hzx b).trans
        ((envUpdate_of_ne v hzx a).trans (envUpdate_of_ne v hzx b).symm)

private theorem nHolds_update_comm (v : ℕ → ℕ) {x y : ℕ} (hxy : x ≠ y) (a b : ℕ) (φ : PAFormula) :
    PAFormula.NHolds (envUpdate (envUpdate v x a) y b) φ ↔
      PAFormula.NHolds (envUpdate (envUpdate v y b) x a) φ :=
  nHolds_congr fun z _ ↦ by
    cases Nat.decEq z y with
    | isTrue hzy =>
      subst hzy
      exact (envUpdate_self (envUpdate v x a) z b).trans
        ((envUpdate_of_ne (envUpdate v z b) (Ne.symm hxy) a).trans
          (envUpdate_self v z b)).symm
    | isFalse hzy =>
      cases Nat.decEq z x with
      | isTrue hzx =>
        subst hzx
        exact (envUpdate_of_ne (envUpdate v z a) hzy b).trans
          ((envUpdate_self v z a).trans (envUpdate_self (envUpdate v y b) z a).symm)
      | isFalse hzx =>
        exact (envUpdate_of_ne (envUpdate v x a) hzy b).trans
          ((envUpdate_of_ne v hzx a).trans
            ((envUpdate_of_ne (envUpdate v y b) hzx a).trans (envUpdate_of_ne v hzy b)).symm)

private theorem nHolds_subst (v : ℕ → ℕ) {x : ℕ} {s : PATerm} {φ : PAFormula}
    (hf : φ.freeFor x s = true) :
    PAFormula.NHolds v (φ.subst x s) ↔
      PAFormula.NHolds (envUpdate v x (s.eval v)) φ := by
  induction φ generalizing v with
  | bot => exact ⟨id, id⟩
  | eq t₁ t₂ =>
    have e₁ := eval_subst_zero v x s t₁
    have e₂ := eval_subst_zero v x s t₂
    exact ⟨fun he ↦ e₁.symm.trans (he.trans e₂), fun he ↦ e₁.trans (he.trans e₂.symm)⟩
  | and _ _ ih₁ ih₂ =>
    exact iff_and_zero (ih₁ v (bool_and_left hf)) (ih₂ v (bool_and_right hf))
  | or _ _ ih₁ ih₂ =>
    exact iff_nn_or_zero (ih₁ v (bool_and_left hf)) (ih₂ v (bool_and_right hf))
  | imp _ _ ih₁ ih₂ =>
    exact iff_imp_zero (ih₁ v (bool_and_left hf)) (ih₂ v (bool_and_right hf))
  | all y φ ih =>
    cases Nat.decEq y x with
    | isTrue heq =>
      subst heq
      have hsub : (PAFormula.all y φ).subst y s = PAFormula.all y φ := by
        dsimp only [PAFormula.subst]
        rw [nat_beq_refl]
        rfl
      rw [hsub]
      exact iff_all_zero fun a ↦
        have hid := nHolds_update_idem v y (s.eval v) a φ
        ⟨hid.mpr, hid.mp⟩
    | isFalse hxy =>
      have hb : (y == x) = false := nat_beq_eq_false hxy
      have hsub : (PAFormula.all y φ).subst x s = PAFormula.all y (φ.subst x s) := by
        dsimp only [PAFormula.subst]
        rw [hb]
        rfl
      rw [hsub]
      have hconj : ((!φ.hasFree x || !s.hasVar y) && φ.freeFor x s) = true := by
        change ((y == x) || ((!φ.hasFree x || !s.hasVar y) && φ.freeFor x s)) = true at hf
        rw [hb] at hf
        exact hf
      have hf' : φ.freeFor x s = true := bool_and_right hconj
      rcases bool_or_cases (bool_and_left hconj) with hno | hsy
      · have hno' : φ.hasFree x = false := bool_not_eq_true_iff hno
        refine iff_all_zero fun a ↦ ?_
        rw [subst_eq_self_zero s hno']
        have h₁ := nHolds_update_of_hasFree_false (envUpdate v y a) (s.eval v) hno'
        have h₂ := nHolds_update_comm v hxy a (s.eval v) φ
        exact ⟨fun u ↦ h₂.mp (h₁.mpr u), fun w ↦ h₁.mp (h₂.mpr w)⟩
      · have hsy' : s.hasVar y = false := bool_not_eq_true_iff hsy
        refine iff_all_zero fun a ↦ ?_
        have hev : s.eval (envUpdate v y a) = s.eval v :=
          eval_update_of_hasVar_false_zero v a hsy'
        have hstep := ih (envUpdate v y a) hf'
        rw [hev] at hstep
        have hcomm := nHolds_update_comm v hxy a (s.eval v) φ
        exact ⟨fun u ↦ hcomm.mp (hstep.mp u), fun w ↦ hstep.mpr (hcomm.mpr w)⟩
  | ex y φ ih =>
    cases Nat.decEq y x with
    | isTrue heq =>
      subst heq
      have hsub : (PAFormula.ex y φ).subst y s = PAFormula.ex y φ := by
        dsimp only [PAFormula.subst]
        rw [nat_beq_refl]
        rfl
      rw [hsub]
      exact iff_nn_ex_zero fun a ↦
        have hid := nHolds_update_idem v y (s.eval v) a φ
        ⟨hid.mpr, hid.mp⟩
    | isFalse hxy =>
      have hb : (y == x) = false := nat_beq_eq_false hxy
      have hsub : (PAFormula.ex y φ).subst x s = PAFormula.ex y (φ.subst x s) := by
        dsimp only [PAFormula.subst]
        rw [hb]
        rfl
      rw [hsub]
      have hconj : ((!φ.hasFree x || !s.hasVar y) && φ.freeFor x s) = true := by
        change ((y == x) || ((!φ.hasFree x || !s.hasVar y) && φ.freeFor x s)) = true at hf
        rw [hb] at hf
        exact hf
      have hf' : φ.freeFor x s = true := bool_and_right hconj
      rcases bool_or_cases (bool_and_left hconj) with hno | hsy
      · have hno' : φ.hasFree x = false := bool_not_eq_true_iff hno
        refine iff_nn_ex_zero fun a ↦ ?_
        rw [subst_eq_self_zero s hno']
        have h₁ := nHolds_update_of_hasFree_false (envUpdate v y a) (s.eval v) hno'
        have h₂ := nHolds_update_comm v hxy a (s.eval v) φ
        exact ⟨fun u ↦ h₂.mp (h₁.mpr u), fun w ↦ h₁.mp (h₂.mpr w)⟩
      · have hsy' : s.hasVar y = false := bool_not_eq_true_iff hsy
        refine iff_nn_ex_zero fun a ↦ ?_
        have hev : s.eval (envUpdate v y a) = s.eval v :=
          eval_update_of_hasVar_false_zero v a hsy'
        have hstep := ih (envUpdate v y a) hf'
        rw [hev] at hstep
        have hcomm := nHolds_update_comm v hxy a (s.eval v) φ
        exact ⟨fun u ↦ hcomm.mp (hstep.mp u), fun w ↦ hstep.mpr (hcomm.mpr w)⟩

/-- Soundness of `PAProvable` under Gödel–Gentzen negative satisfaction `NHolds` (zero axioms). -/
theorem paProvable_nSound {φ : PAFormula} (h : PAProvable φ) (v : ℕ → ℕ) :
    PAFormula.NHolds v φ := by
  induction h generalizing v with
  | mp _ _ ihφ ihimp => exact ihimp v (ihφ v)
  | gen x _ ih => intro a; exact ih (envUpdate v x a)
  | imp_k _ _ => intro h₁ _; exact h₁
  | imp_s _ _ _ => intro h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)
  | dne φ => exact nHolds_stable φ v
  | and_intro _ _ => exact And.intro
  | and_left _ _ => exact And.left
  | and_right _ _ => exact And.right
  | or_left _ _ => intro hφ hn; exact hn (Or.inl hφ)
  | or_right _ _ => intro hψ hn; exact hn (Or.inr hψ)
  | or_elim _ _ χ =>
    intro h₁ h₂ hor
    refine nHolds_stable χ v fun hnχ ↦ hor fun hdisj ↦ ?_
    exact hdisj.elim (fun hφ ↦ hnχ (h₁ hφ)) (fun hψ ↦ hnχ (h₂ hψ))
  | all_imp x _ _ => intro h₁ h₂ a; exact h₁ a (h₂ a)
  | all_vacuous x φ hx =>
    intro hφ a
    exact (nHolds_update_of_hasFree_false v a hx).mpr hφ
  | all_elim x t φ hf =>
    intro hall
    exact (nHolds_subst v hf).mpr (hall (t.eval v))
  | ex_intro x t φ hf =>
    intro hsub hn
    exact hn ⟨t.eval v, (nHolds_subst v hf).mp hsub⟩
  | ex_elim x φ ψ hx =>
    intro hall hex
    refine nHolds_stable ψ v fun hnψ ↦ hex fun ⟨a, ha⟩ ↦ ?_
    exact hnψ ((nHolds_update_of_hasFree_false v a hx).mp (hall a ha))
  | eq_refl _ => rfl
  | eq_subst x s t φ hs ht =>
    intro heq hφs
    have h1 := (nHolds_subst v hs).mp hφs
    rw [heq] at h1
    exact (nHolds_subst v ht).mpr h1
  | pa_zero_ne_succ => exact fun h ↦ Nat.noConfusion h
  | pa_succ_inj => exact Nat.succ.inj
  | pa_add_zero => exact Nat.add_zero (v 0)
  | pa_add_succ => exact Nat.add_succ (v 0) (v 1)
  | pa_mul_zero => exact Nat.mul_zero (v 0)
  | pa_mul_succ => exact Nat.mul_succ (v 0) (v 1)
  | pa_ind x φ =>
    intro h0 hs a
    have h0' : PAFormula.NHolds (envUpdate v x 0) φ :=
      (nHolds_subst v (freeFor_zero_zero x φ)).mp h0
    have hs' : ∀ b : ℕ, PAFormula.NHolds (envUpdate v x b) φ →
        PAFormula.NHolds (envUpdate v x (b + 1)) φ := by
      intro b hb
      have hstep := hs b hb
      have hsub := (nHolds_subst (envUpdate v x b) (freeFor_succ_self_zero x φ)).mp hstep
      have hev : (PATerm.succ (.var x)).eval (envUpdate v x b) = b + 1 :=
        congrArg (· + 1) (envUpdate_self v x b)
      rw [hev] at hsub
      exact (nHolds_update_idem v x b (b + 1) φ).mp hsub
    induction a with
    | zero => exact h0'
    | succ a ih => exact hs' a ih

/-- Consistency of first-order Peano Arithmetic (`¬ PAProvable .bot`), proved with **zero axioms**
(`[]`) in Lean's Calculus of Inductive Constructions. -/
theorem not_paProvable_false : ¬ PAProvable .bot :=
  fun h ↦ paProvable_nSound h (fun _ ↦ 0)

end ConjectureMachines.Semantics.PA
