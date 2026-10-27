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

/-! ## Section 4: Constructive Consistency via Negative Translation (`not_paProvable_false`) -/

/-- Gödel–Gentzen negative satisfaction of a `PAFormula` in `ℕ`, replacing positive disjunction
and existential quantification by their double-negated counterparts so every formula is
constructively `¬¬`-stable without `Classical.choice`. -/
def PAFormula.NHolds (v : ℕ → ℕ) : PAFormula → Prop
  | .bot => False
  | .eq t₁ t₂ => t₁.eval v = t₂.eval v
  | .and φ ψ => PAFormula.NHolds v φ ∧ PAFormula.NHolds v ψ
  | .or φ ψ => ¬¬ (PAFormula.NHolds v φ ∨ PAFormula.NHolds v ψ)
  | .imp φ ψ => PAFormula.NHolds v φ → PAFormula.NHolds v ψ
  | .all x φ => ∀ a : ℕ, PAFormula.NHolds (Function.update v x a) φ
  | .ex x φ => ¬¬ ∃ a : ℕ, PAFormula.NHolds (Function.update v x a) φ

theorem nHolds_stable (φ : PAFormula) (v : ℕ → ℕ) :
    ¬¬ PAFormula.NHolds v φ → PAFormula.NHolds v φ := by
  induction φ generalizing v with
  | bot => intro h; exact h id
  | eq t₁ t₂ =>
    intro h
    by_cases he : t₁.eval v = t₂.eval v
    · exact he
    · exact False.elim (h he)
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
    exact ih (Function.update v x a) fun ha ↦ h fun hall ↦ ha (hall a)
  | ex _ _ _ =>
    intro h hn
    exact h fun hnn ↦ hnn hn

private theorem nHolds_congr {v₁ v₂ : ℕ → ℕ} {φ : PAFormula}
    (h : ∀ x, φ.hasFree x = true → v₁ x = v₂ x) :
    PAFormula.NHolds v₁ φ ↔ PAFormula.NHolds v₂ φ := by
  induction φ generalizing v₁ v₂ with
  | bot => exact Iff.rfl
  | eq t₁ t₂ =>
    have e₁ : t₁.eval v₁ = t₁.eval v₂ := by
      rw [← evalIn_nat_eq, ← evalIn_nat_eq]
      exact evalIn_congr fun x hx ↦ h x (by simp [PAFormula.hasFree, hx])
    have e₂ : t₂.eval v₁ = t₂.eval v₂ := by
      rw [← evalIn_nat_eq, ← evalIn_nat_eq]
      exact evalIn_congr fun x hx ↦ h x (by simp [PAFormula.hasFree, hx])
    simp only [PAFormula.NHolds, e₁, e₂]
  | and _ _ ih₁ ih₂ =>
    refine and_congr (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | or _ _ ih₁ ih₂ =>
    have c₁ := ih₁ (v₁ := v₁) (v₂ := v₂) fun x hx ↦ h x (by simp [PAFormula.hasFree, hx])
    have c₂ := ih₂ (v₁ := v₁) (v₂ := v₂) fun x hx ↦ h x (by simp [PAFormula.hasFree, hx])
    exact not_congr (not_congr (or_congr c₁ c₂))
  | imp _ _ ih₁ ih₂ =>
    refine imp_congr (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | all y _ ih =>
    refine forall_congr' fun a ↦ ih fun x hx ↦ ?_
    rcases Decidable.eq_or_ne x y with rfl | hxy
    · simp
    · simp only [Function.update_of_ne hxy]
      exact h x (by simp [PAFormula.hasFree, Ne.symm hxy, hx])
  | ex y _ ih =>
    refine not_congr (not_congr (exists_congr fun a ↦ ih fun x hx ↦ ?_))
    rcases Decidable.eq_or_ne x y with rfl | hxy
    · simp
    · simp only [Function.update_of_ne hxy]
      exact h x (by simp [PAFormula.hasFree, Ne.symm hxy, hx])

private theorem nHolds_update_of_hasFree_false (v : ℕ → ℕ) {x : ℕ} (a : ℕ) {φ : PAFormula}
    (hx : φ.hasFree x = false) :
    PAFormula.NHolds (Function.update v x a) φ ↔ PAFormula.NHolds v φ := by
  refine nHolds_congr fun y hy ↦ ?_
  have hne : y ≠ x := fun h ↦ by subst h; rw [hx] at hy; cases hy
  exact Function.update_of_ne hne a v

private theorem nHolds_update_idem (v : ℕ → ℕ) (x a b : ℕ) (φ : PAFormula) :
    PAFormula.NHolds (Function.update (Function.update v x a) x b) φ ↔
      PAFormula.NHolds (Function.update v x b) φ := by
  refine nHolds_congr fun z _ ↦ ?_
  rcases Decidable.eq_or_ne z x with rfl | hzx
  · simp only [Function.update_self]
  · simp only [Function.update_of_ne hzx]

private theorem nHolds_update_comm (v : ℕ → ℕ) {x y : ℕ} (hxy : x ≠ y) (a b : ℕ) (φ : PAFormula) :
    PAFormula.NHolds (Function.update (Function.update v x a) y b) φ ↔
      PAFormula.NHolds (Function.update (Function.update v y b) x a) φ := by
  refine nHolds_congr fun z _ ↦ ?_
  rcases Decidable.eq_or_ne z y with rfl | hzy
  · rw [Function.update_self, Function.update_of_ne hxy.symm, Function.update_self]
  · rw [Function.update_of_ne hzy]
    rcases Decidable.eq_or_ne z x with rfl | hzx
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx, Function.update_of_ne hzy]

private theorem nHolds_subst (v : ℕ → ℕ) {x : ℕ} {s : PATerm} {φ : PAFormula}
    (hf : φ.freeFor x s = true) :
    PAFormula.NHolds v (φ.subst x s) ↔
      PAFormula.NHolds (Function.update v x (s.eval v)) φ := by
  induction φ generalizing v with
  | bot => exact Iff.rfl
  | eq t₁ t₂ =>
    simp only [PAFormula.subst, PAFormula.NHolds, ← evalIn_nat_eq, evalIn_subst]
  | and _ _ ih₁ ih₂ =>
    simp only [PAFormula.freeFor, Bool.and_eq_true] at hf
    exact and_congr (ih₁ v hf.1) (ih₂ v hf.2)
  | or _ _ ih₁ ih₂ =>
    simp only [PAFormula.freeFor, Bool.and_eq_true] at hf
    exact not_congr (not_congr (or_congr (ih₁ v hf.1) (ih₂ v hf.2)))
  | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.freeFor, Bool.and_eq_true] at hf
    exact imp_congr (ih₁ v hf.1) (ih₂ v hf.2)
  | all y φ ih =>
    simp only [PAFormula.subst]
    rcases Decidable.eq_or_ne y x with rfl | hxy
    · simp only [beq_self_eq_true, ↓reduceIte, PAFormula.NHolds]
      refine forall_congr' fun a ↦ ?_
      exact (nHolds_update_idem v y (s.eval v) a φ).symm
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [hb, Bool.false_eq_true, ↓reduceIte, PAFormula.NHolds]
      simp only [PAFormula.freeFor, hb, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true'] at hf
      rcases hf with ⟨hno | hsy, hf'⟩
      · refine forall_congr' fun a ↦ ?_
        rw [subst_eq_self_of_hasFree_false s hno,
          nHolds_update_comm v (Ne.symm hxy),
          nHolds_update_of_hasFree_false _ _ hno]
      · refine forall_congr' fun a ↦ ?_
        have hev : s.eval (Function.update v y a) = s.eval v := by
          rw [← evalIn_nat_eq, ← evalIn_nat_eq]
          exact evalIn_update_of_hasVar_false v a hsy
        rw [ih (Function.update v y a) hf', hev, nHolds_update_comm v hxy]
  | ex y φ ih =>
    simp only [PAFormula.subst]
    rcases Decidable.eq_or_ne y x with rfl | hxy
    · simp only [beq_self_eq_true, ↓reduceIte, PAFormula.NHolds]
      refine not_congr (not_congr (exists_congr fun a ↦ ?_))
      exact (nHolds_update_idem v y (s.eval v) a φ).symm
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [hb, Bool.false_eq_true, ↓reduceIte, PAFormula.NHolds]
      simp only [PAFormula.freeFor, hb, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true'] at hf
      rcases hf with ⟨hno | hsy, hf'⟩
      · refine not_congr (not_congr (exists_congr fun a ↦ ?_))
        rw [subst_eq_self_of_hasFree_false s hno,
          nHolds_update_comm v (Ne.symm hxy),
          nHolds_update_of_hasFree_false _ _ hno]
      · refine not_congr (not_congr (exists_congr fun a ↦ ?_))
        have hev : s.eval (Function.update v y a) = s.eval v := by
          rw [← evalIn_nat_eq, ← evalIn_nat_eq]
          exact evalIn_update_of_hasVar_false v a hsy
        rw [ih (Function.update v y a) hf', hev, nHolds_update_comm v hxy]

/-- Constructive soundness of `PAProvable` under `NHolds` (zero `Classical.choice`). -/
theorem paProvable_nSound {φ : PAFormula} (h : PAProvable φ) (v : ℕ → ℕ) :
    PAFormula.NHolds v φ := by
  induction h generalizing v with
  | mp _ _ ihφ ihimp => exact ihimp v (ihφ v)
  | gen x _ ih => intro a; exact ih (Function.update v x a)
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
  | pa_zero_ne_succ => exact Nat.succ_ne_zero (v 0)
  | pa_succ_inj => exact Nat.succ.inj
  | pa_add_zero => exact Nat.add_zero (v 0)
  | pa_add_succ => exact Nat.add_succ (v 0) (v 1)
  | pa_mul_zero => exact Nat.mul_zero (v 0)
  | pa_mul_succ => exact Nat.mul_succ (v 0) (v 1)
  | pa_ind x φ =>
    intro h0 hs a
    have h0' : PAFormula.NHolds (Function.update v x 0) φ :=
      (nHolds_subst v (freeFor_zero x φ)).mp h0
    have hs' : ∀ b : ℕ, PAFormula.NHolds (Function.update v x b) φ →
        PAFormula.NHolds (Function.update v x (b + 1)) φ := by
      intro b hb
      have hstep := hs b hb
      have hsub := (nHolds_subst (Function.update v x b) (freeFor_succ_self x φ)).mp hstep
      simp only [PATerm.eval, Function.update_self] at hsub
      exact (nHolds_update_idem v x b (b + 1) φ).mp hsub
    induction a with
    | zero => exact h0'
    | succ a ih => exact hs' a ih

/-- Consistency of first-order Peano Arithmetic (`¬ PAProvable .bot`), proved constructively
without `Classical.choice`. -/
theorem not_paProvable_false : ¬ PAProvable .bot :=
  fun h ↦ paProvable_nSound h (fun _ ↦ 0)

end ConjectureMachines.Semantics.PA
