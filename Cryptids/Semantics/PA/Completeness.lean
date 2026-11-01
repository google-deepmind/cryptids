/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Syntax
public import Mathlib.Data.Nat.Pairing

/-!
# Gödel–Henkin Completeness of `PAProvable`

This module proves Gödel's first-order completeness theorem specialized to Peano Arithmetic
(`PAProvable`): a `PAFormula` is provable in `PAProvable` if and only if it holds in every
first-order `PAModel` `M` (`Type`) under every variable assignment:

- `paProvable_iff_holdsIn_all_models`:
  `PAProvable φ ↔ ∀ (M : Type) [PAStructure M] [PAModel M] (v : ℕ → M), PAFormula.HoldsIn v φ`

This bridge allows semantic proofs in an arbitrary first-order model `[PAModel M]` to be compiled
directly into formal Hilbert derivations `PAProvable φ`.
-/

@[expose] public section

namespace ConjectureMachines

/-- Smallest variable index strictly greater than every variable (free or bound) occurring in a
`PAFormula`. -/
def PAFormula.maxVar : PAFormula → ℕ
  | .bot => 0
  | .eq t₁ t₂ => max t₁.freshVar t₂.freshVar
  | .and φ ψ | .or φ ψ | .imp φ ψ => max φ.maxVar ψ.maxVar
  | .all x φ | .ex x φ => max (x + 1) φ.maxVar

/-- Simultaneous variable-to-variable renaming on `PATerm`. -/
def PATerm.vsubst (ρ : ℕ → ℕ) : PATerm → PATerm
  | .var x => .var (ρ x)
  | .zero => .zero
  | .succ t => .succ (t.vsubst ρ)
  | .add t₁ t₂ => .add (t₁.vsubst ρ) (t₂.vsubst ρ)
  | .mul t₁ t₂ => .mul (t₁.vsubst ρ) (t₂.vsubst ρ)

/-- Simultaneous variable-to-variable renaming on `PAFormula`, preserving bound variable names. -/
def PAFormula.vsubst (ρ : ℕ → ℕ) : PAFormula → PAFormula
  | .bot => .bot
  | .eq t₁ t₂ => .eq (t₁.vsubst ρ) (t₂.vsubst ρ)
  | .and φ ψ => .and (φ.vsubst ρ) (ψ.vsubst ρ)
  | .or φ ψ => .or (φ.vsubst ρ) (ψ.vsubst ρ)
  | .imp φ ψ => .imp (φ.vsubst ρ) (ψ.vsubst ρ)
  | .all y φ => .all y (φ.vsubst (Function.update ρ y y))
  | .ex y φ => .ex y (φ.vsubst (Function.update ρ y y))

end ConjectureMachines

namespace ConjectureMachines.Semantics.PA

/-! ## Section 1: Variable Bounds and Simultaneous Variable Renaming -/

private theorem term_subst_eq_self_of_hasVar_false {t : PATerm} {x : ℕ} (s : PATerm)
    (hx : t.hasVar x = false) : t.subst x s = t := by
  induction t with
  | var y =>
    simp only [PATerm.hasVar, beq_eq_false_iff_ne] at hx
    simp [PATerm.subst, hx]
  | zero => rfl
  | succ _ ih => exact congrArg PATerm.succ (ih hx)
  | add _ _ ih₁ ih₂ =>
    simp only [PATerm.hasVar, Bool.or_eq_false_iff] at hx
    exact congrArg₂ PATerm.add (ih₁ hx.1) (ih₂ hx.2)
  | mul _ _ ih₁ ih₂ =>
    simp only [PATerm.hasVar, Bool.or_eq_false_iff] at hx
    exact congrArg₂ PATerm.mul (ih₁ hx.1) (ih₂ hx.2)

private theorem lt_freshVar_of_hasVar {t : PATerm} {x : ℕ} (h : t.hasVar x = true) :
    x < t.freshVar := by
  by_contra hge
  have hf := hasVar_false_of_freshVar_le (Nat.le_of_not_lt hge)
  rw [hf] at h
  cases h

private theorem hasFree_false_of_maxVar_le {φ : PAFormula} {w : ℕ} (h : φ.maxVar ≤ w) :
    φ.hasFree w = false := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp only [PAFormula.hasFree, Bool.or_eq_false_iff]
    exact ⟨hasVar_false_of_freshVar_le h.1, hasVar_false_of_freshVar_le h.2⟩
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp only [PAFormula.hasFree, Bool.or_eq_false_iff]
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | all x _ ih | ex x _ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp only [PAFormula.hasFree, Bool.and_eq_false_iff]
    exact Or.inr (ih h.2)

private theorem lt_maxVar_of_hasFree {φ : PAFormula} {x : ℕ} (h : φ.hasFree x = true) :
    x < φ.maxVar := by
  by_contra hge
  have hf := hasFree_false_of_maxVar_le (Nat.le_of_not_lt hge)
  rw [hf] at h
  cases h

private theorem freeFor_var_self (x : ℕ) (φ : PAFormula) :
    φ.freeFor x (.var x) = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp [PAFormula.freeFor, ih₁, ih₂]
  | all y _ ih | ex y _ ih =>
    simp only [PAFormula.freeFor, PATerm.hasVar]
    by_cases hxy : y = x
    · simp [hxy]
    · simp [hxy, Ne.symm hxy, ih]

private theorem term_subst_var_self (x : ℕ) (t : PATerm) :
    t.subst x (.var x) = t := by
  induction t with
  | var y =>
    simp only [PATerm.subst]
    by_cases hxy : y = x
    · subst hxy; simp
    · simp [hxy]
  | zero => rfl
  | succ _ ih => exact congrArg PATerm.succ ih
  | add _ _ ih₁ ih₂ => exact congrArg₂ PATerm.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact congrArg₂ PATerm.mul ih₁ ih₂

private theorem subst_var_self (x : ℕ) (φ : PAFormula) :
    φ.subst x (.var x) = φ := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ => exact congrArg₂ PAFormula.eq (term_subst_var_self x t₁) (term_subst_var_self x t₂)
  | and _ _ ih₁ ih₂ => exact congrArg₂ PAFormula.and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact congrArg₂ PAFormula.or ih₁ ih₂
  | imp _ _ ih₁ ih₂ => exact congrArg₂ PAFormula.imp ih₁ ih₂
  | all y φ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · simp [hxy]
    · simp [hxy, ih]
  | ex y φ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · simp [hxy]
    · simp [hxy, ih]

private theorem freeFor_var_of_maxVar_le (x : ℕ) {w : ℕ} {φ : PAFormula} (hw : φ.maxVar ≤ w) :
    φ.freeFor x (.var w) = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    simp [PAFormula.freeFor, ih₁ hw.1, ih₂ hw.2]
  | all y _ ih | ex y _ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    have hwy : w ≠ y := by omega
    simp [PAFormula.freeFor, PATerm.hasVar, hwy, ih hw.2]

private theorem freeFor_of_hasFree_false {w : ℕ} (s : PATerm) {φ : PAFormula}
    (hw : φ.maxVar ≤ w) : φ.freeFor w s = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    simp [PAFormula.freeFor, ih₁ hw.1, ih₂ hw.2]
  | all y φ ih | ex y φ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    simp [PAFormula.freeFor, hasFree_false_of_maxVar_le hw.2, ih hw.2]

private theorem freeFor_inverse_var {x w : ℕ} {φ : PAFormula} (hw : φ.maxVar ≤ w) :
    (φ.subst x (.var w)).freeFor w (.var x) = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    simp [PAFormula.subst, PAFormula.freeFor, ih₁ hw.1, ih₂ hw.2]
  | all y φ ih | ex y φ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · subst hxy
      simp only [beq_self_eq_true, ↓reduceIte]
      exact freeFor_of_hasFree_false (.var y) (Nat.max_le.mpr hw)
    · have hb : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp [hb, PAFormula.freeFor, PATerm.hasVar, Ne.symm hxy, ih hw.2]

private theorem term_subst_inverse_var {x w : ℕ} {t : PATerm} (hw : t.freshVar ≤ w) :
    (t.subst x (.var w)).subst w (.var x) = t := by
  induction t with
  | var z =>
    simp only [PATerm.freshVar] at hw
    simp only [PATerm.subst]
    by_cases hzx : z = x
    · subst hzx; simp [PATerm.subst]
    · have hzw : z ≠ w := by omega
      simp [hzx, PATerm.subst, hzw]
  | zero => rfl
  | succ _ ih => exact congrArg PATerm.succ (ih hw)
  | add _ _ ih₁ ih₂ =>
    simp only [PATerm.freshVar, Nat.max_le] at hw
    exact congrArg₂ PATerm.add (ih₁ hw.1) (ih₂ hw.2)
  | mul _ _ ih₁ ih₂ =>
    simp only [PATerm.freshVar, Nat.max_le] at hw
    exact congrArg₂ PATerm.mul (ih₁ hw.1) (ih₂ hw.2)

private theorem subst_inverse_var {x w : ℕ} {φ : PAFormula} (hw : φ.maxVar ≤ w) :
    (φ.subst x (.var w)).subst w (.var x) = φ := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    exact congrArg₂ PAFormula.eq (term_subst_inverse_var hw.1) (term_subst_inverse_var hw.2)
  | and _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    exact congrArg₂ PAFormula.and (ih₁ hw.1) (ih₂ hw.2)
  | or _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    exact congrArg₂ PAFormula.or (ih₁ hw.1) (ih₂ hw.2)
  | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    exact congrArg₂ PAFormula.imp (ih₁ hw.1) (ih₂ hw.2)
  | all y φ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    have hyw : y ≠ w := by omega
    have hbw : (y == w) = false := beq_eq_false_iff_ne.mpr hyw
    by_cases hxy : y = x
    · subst hxy
      simp [PAFormula.subst, hbw,
        subst_eq_self_of_hasFree_false (.var y) (hasFree_false_of_maxVar_le hw.2)]
    · have hbx : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp [PAFormula.subst, hbx, hbw, ih hw.2]
  | ex y φ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    have hyw : y ≠ w := by omega
    have hbw : (y == w) = false := beq_eq_false_iff_ne.mpr hyw
    by_cases hxy : y = x
    · subst hxy
      simp [PAFormula.subst, hbw,
        subst_eq_self_of_hasFree_false (.var y) (hasFree_false_of_maxVar_le hw.2)]
    · have hbx : (y == x) = false := beq_eq_false_iff_ne.mpr hxy
      simp [PAFormula.subst, hbx, hbw, ih hw.2]

private theorem hasVar_subst_var_self_false {t : PATerm} {x w : ℕ} (hwx : w ≠ x) :
    (t.subst x (.var w)).hasVar x = false := by
  induction t with
  | var z =>
    simp only [PATerm.subst]
    by_cases hzx : z = x
    · subst hzx; simp [PATerm.hasVar, hwx]
    · simp [hzx, PATerm.hasVar]
  | zero => rfl
  | succ _ ih => exact ih
  | add _ _ ih₁ ih₂ | mul _ _ ih₁ ih₂ =>
    simp [PATerm.subst, PATerm.hasVar, ih₁, ih₂]

private theorem hasFree_subst_var_self_false {φ : PAFormula} {x w : ℕ} (hwx : w ≠ x) :
    (φ.subst x (.var w)).hasFree x = false := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ =>
    simp [PAFormula.subst, PAFormula.hasFree, hasVar_subst_var_self_false hwx]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp [PAFormula.subst, PAFormula.hasFree, ih₁, ih₂]
  | all y _ ih | ex y _ ih =>
    simp only [PAFormula.subst]
    by_cases hxy : y = x
    · subst hxy; simp [PAFormula.hasFree]
    · simp [hxy, PAFormula.hasFree, ih]

private theorem update_id_self (y : ℕ) : Function.update (id : ℕ → ℕ) y y = id := by
  funext x
  by_cases h : x = y
  · subst h; simp
  · simp [h]

private theorem term_vsubst_id (t : PATerm) : t.vsubst id = t := by
  induction t with
  | var _ | zero => rfl
  | succ _ ih => exact congrArg PATerm.succ ih
  | add _ _ ih₁ ih₂ => exact congrArg₂ PATerm.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact congrArg₂ PATerm.mul ih₁ ih₂

private theorem vsubst_id (φ : PAFormula) : φ.vsubst id = φ := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ => exact congrArg₂ PAFormula.eq (term_vsubst_id t₁) (term_vsubst_id t₂)
  | and _ _ ih₁ ih₂ => exact congrArg₂ PAFormula.and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact congrArg₂ PAFormula.or ih₁ ih₂
  | imp _ _ ih₁ ih₂ => exact congrArg₂ PAFormula.imp ih₁ ih₂
  | all y _ ih =>
    simp only [PAFormula.vsubst, update_id_self]
    exact congrArg (PAFormula.all y) ih
  | ex y _ ih =>
    simp only [PAFormula.vsubst, update_id_self]
    exact congrArg (PAFormula.ex y) ih

private theorem term_vsubst_subst_var {t : PATerm} {ρ : ℕ → ℕ} {y w : ℕ}
    (h : ∀ x, t.hasVar x = true → x ≠ y → ρ x ≠ y) :
    (t.vsubst (Function.update ρ y y)).subst y (.var w) = t.vsubst (Function.update ρ y w) := by
  induction t with
  | var x =>
    simp only [PATerm.vsubst]
    by_cases hxy : x = y
    · subst hxy; simp [PATerm.subst]
    · have hρ : ρ x ≠ y := h x (by simp [PATerm.hasVar]) hxy
      simp [hxy, PATerm.subst, hρ]
  | zero => rfl
  | succ _ ih =>
    exact congrArg PATerm.succ (ih h)
  | add t₁ t₂ ih₁ ih₂ =>
    refine congrArg₂ PATerm.add (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PATerm.hasVar, hx]
  | mul t₁ t₂ ih₁ ih₂ =>
    refine congrArg₂ PATerm.mul (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PATerm.hasVar, hx]

private theorem vsubst_subst_var {φ : PAFormula} {ρ : ℕ → ℕ} {y w : ℕ}
    (h : ∀ x, φ.hasFree x = true → x ≠ y → ρ x ≠ y) :
    (φ.vsubst (Function.update ρ y y)).subst y (.var w) = φ.vsubst (Function.update ρ y w) := by
  induction φ generalizing ρ with
  | bot => rfl
  | eq t₁ t₂ =>
    refine congrArg₂ PAFormula.eq
      (term_vsubst_subst_var fun x hx ↦ h x ?_)
      (term_vsubst_subst_var fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | and _ _ ih₁ ih₂ =>
    refine congrArg₂ PAFormula.and (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | or _ _ ih₁ ih₂ =>
    refine congrArg₂ PAFormula.or (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | imp _ _ ih₁ ih₂ =>
    refine congrArg₂ PAFormula.imp (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | all z χ ih =>
    simp only [PAFormula.vsubst]
    by_cases hzy : z = y
    · subst hzy
      simp [PAFormula.subst, Function.update_idem]
    · have hb : (z == y) = false := beq_eq_false_iff_ne.mpr hzy
      simp only [PAFormula.subst, hb, Bool.false_eq_true, ↓reduceIte,
        Function.update_comm (Ne.symm hzy)]
      refine congrArg (PAFormula.all z) (ih fun x hx hxy ↦ ?_)
      by_cases hxz : x = z
      · subst hxz; simp [hzy]
      · simp only [Function.update_of_ne hxz]
        exact h x (by simp [PAFormula.hasFree, Ne.symm hxz, hx]) hxy
  | ex z χ ih =>
    simp only [PAFormula.vsubst]
    by_cases hzy : z = y
    · subst hzy
      simp [PAFormula.subst, Function.update_idem]
    · have hb : (z == y) = false := beq_eq_false_iff_ne.mpr hzy
      simp only [PAFormula.subst, hb, Bool.false_eq_true, ↓reduceIte,
        Function.update_comm (Ne.symm hzy)]
      refine congrArg (PAFormula.ex z) (ih fun x hx hxy ↦ ?_)
      by_cases hxz : x = z
      · subst hxz; simp [hzy]
      · simp only [Function.update_of_ne hxz]
        exact h x (by simp [PAFormula.hasFree, Ne.symm hxz, hx]) hxy

private theorem vsubst_update_id_eq_subst (ψ : PAFormula) (x w : ℕ) :
    ψ.vsubst (Function.update id x w) = ψ.subst x (.var w) := by
  have heq := vsubst_subst_var (φ := ψ) (ρ := id) (y := x) (w := w)
    (fun z _ hzx ↦ hzx)
  rw [update_id_self, vsubst_id] at heq
  exact heq.symm

/-- Variable renaming `ρ` is capture-safe for `φ`: every free variable `x` of `φ` is either left
fixed (`ρ x = x`) or mapped to a variable ≥ `φ.maxVar` (disjoint from all variables of `φ`). -/
private def SafeFor (ρ : ℕ → ℕ) (φ : PAFormula) : Prop :=
  ∀ x, φ.hasFree x = true → ρ x = x ∨ φ.maxVar ≤ ρ x

private theorem safeFor_id (φ : PAFormula) : SafeFor id φ :=
  fun _ _ ↦ Or.inl rfl

private theorem safeFor_mono {ρ : ℕ → ℕ} {φ ψ : PAFormula} (h : SafeFor ρ ψ)
    (hmax : φ.maxVar ≤ ψ.maxVar) (hfree : ∀ x, φ.hasFree x = true → ψ.hasFree x = true) :
    SafeFor ρ φ := by
  intro x hx
  rcases h x (hfree x hx) with heq | hge
  · exact Or.inl heq
  · exact Or.inr (le_trans hmax hge)

private theorem safeFor_update_fresh {ρ : ℕ → ℕ} {y w : ℕ} {φ : PAFormula}
    (h : ∀ x, φ.hasFree x = true → x ≠ y → ρ x = x ∨ φ.maxVar ≤ ρ x)
    (hw : φ.maxVar ≤ w) :
    SafeFor (Function.update ρ y w) φ := by
  intro x hx
  by_cases hxy : x = y
  · subst hxy; simp [hw]
  · simp only [Function.update_of_ne hxy]
    exact h x hx hxy

private theorem freshVar_le_vsubst {t : PATerm} {σ : ℕ → ℕ}
    (h : ∀ x, t.hasVar x = true → x ≤ σ x) :
    t.freshVar ≤ (t.vsubst σ).freshVar := by
  induction t with
  | var x =>
    simp only [PATerm.freshVar, PATerm.vsubst]
    have hx := h x (by simp [PATerm.hasVar])
    omega
  | zero => exact Nat.le_refl 0
  | succ _ ih => exact ih h
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    refine max_le_max (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PATerm.hasVar, hx]

private theorem maxVar_le_vsubst_maxVar {φ : PAFormula} {σ : ℕ → ℕ}
    (h : ∀ x, φ.hasFree x = true → x ≤ σ x) :
    φ.maxVar ≤ (φ.vsubst σ).maxVar := by
  induction φ generalizing σ with
  | bot => exact Nat.le_refl 0
  | eq t₁ t₂ =>
    refine max_le_max
      (freshVar_le_vsubst fun x hx ↦ h x ?_)
      (freshVar_le_vsubst fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    refine max_le_max (ih₁ fun x hx ↦ h x ?_) (ih₂ fun x hx ↦ h x ?_) <;>
      simp [PAFormula.hasFree, hx]
  | all z χ ih | ex z χ ih =>
    refine max_le_max (Nat.le_refl (z + 1)) (ih fun x hx ↦ ?_)
    by_cases hxz : x = z
    · subst hxz; simp
    · simp only [Function.update_of_ne hxz]
      exact h x (by simp [PAFormula.hasFree, Ne.symm hxz, hx])

/-! ## Section 2: Finite-Context Derivability, Deduction Theorem, and FOL Lemmas -/

/-- Derivability from a finite hypothesis list `Δ` over `PAProvable` using only modus ponens
(with universal generalization restricted to theorems of `PAProvable`, ensuring the unconditional
deduction theorem). -/
private inductive CtxProvable (Δ : List PAFormula) : PAFormula → Prop where
  | ax {φ : PAFormula} : PAProvable φ → CtxProvable Δ φ
  | hyp {φ : PAFormula} : φ ∈ Δ → CtxProvable Δ φ
  | mp {φ ψ : PAFormula} : CtxProvable Δ φ → CtxProvable Δ (.imp φ ψ) → CtxProvable Δ ψ

private theorem ctx_nil_iff {φ : PAFormula} : CtxProvable [] φ ↔ PAProvable φ := by
  refine ⟨fun h ↦ ?_, CtxProvable.ax⟩
  induction h with
  | ax hp => exact hp
  | hyp hm => cases hm
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

private theorem ctx_mono {Δ₁ Δ₂ : List PAFormula} (hsub : ∀ γ ∈ Δ₁, γ ∈ Δ₂)
    {φ : PAFormula} (h : CtxProvable Δ₁ φ) : CtxProvable Δ₂ φ := by
  induction h with
  | ax hp => exact .ax hp
  | hyp hm => exact .hyp (hsub _ hm)
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

private theorem ctx_imp_refl (Δ : List PAFormula) (φ : PAFormula) :
    CtxProvable Δ (.imp φ φ) :=
  .mp (.ax (.imp_k φ φ))
    (.mp (.ax (.imp_k φ (.imp φ φ))) (.ax (.imp_s φ (.imp φ φ) φ)))

private theorem ctx_deduction {Δ : List PAFormula} {α β : PAFormula}
    (h : CtxProvable (α :: Δ) β) : CtxProvable Δ (.imp α β) := by
  induction h with
  | ax hp => exact .mp (.ax hp) (.ax (.imp_k _ α))
  | hyp hm =>
    rcases List.mem_cons.mp hm with heq | hm'
    · subst heq; exact ctx_imp_refl Δ _
    · exact .mp (.hyp hm') (.ax (.imp_k _ α))
  | mp _ _ ih₁ ih₂ =>
    exact .mp ih₁ (.mp ih₂ (.ax (.imp_s α _ _)))

private theorem ctx_by_contra {Δ : List PAFormula} {φ : PAFormula}
    (h : CtxProvable (φ.not :: Δ) .bot) : CtxProvable Δ φ :=
  .mp (ctx_deduction h) (.ax (.dne φ))

private theorem ctx_exfalso {Δ : List PAFormula} (φ : PAFormula)
    (h : CtxProvable Δ .bot) : CtxProvable Δ φ :=
  ctx_by_contra (ctx_mono (fun _ hm ↦ List.mem_cons_of_mem _ hm) h)

private theorem ctx_gen (w : ℕ) {Δ : List PAFormula} {α : PAFormula}
    (hf : ∀ γ ∈ Δ, γ.hasFree w = false) (h : CtxProvable Δ α) :
    CtxProvable Δ (.all w α) := by
  induction Δ generalizing α with
  | nil =>
    exact .ax (.gen w (ctx_nil_iff.mp h))
  | cons δ Δ' ih =>
    have hded : CtxProvable Δ' (.imp δ α) := ctx_deduction h
    have hall : CtxProvable Δ' (.all w (.imp δ α)) :=
      ih (fun γ hγ ↦ hf γ (List.mem_cons_of_mem _ hγ)) hded
    have himp : CtxProvable Δ' (.imp (.all w δ) (.all w α)) :=
      .mp hall (.ax (.all_imp w δ α))
    have himp' : CtxProvable (δ :: Δ') (.imp (.all w δ) (.all w α)) :=
      ctx_mono (fun _ hm ↦ List.mem_cons_of_mem _ hm) himp
    have hvac : PAProvable (.imp δ (.all w δ)) :=
      .all_vacuous w δ (hf δ (List.mem_cons_self ..))
    exact .mp (.mp (.hyp (List.mem_cons_self ..)) (.ax hvac)) himp'

private theorem pa_all_not_subst_imp_not_ex {x w : ℕ} {ψ : PAFormula}
    (hw : (PAFormula.ex x ψ).maxVar ≤ w) :
    PAProvable (.imp (.all w (.not (ψ.subst x (.var w)))) (.not (.ex x ψ))) := by
  simp only [PAFormula.maxVar, Nat.max_le] at hw
  have hwx : w ≠ x := by omega
  let γ : PAFormula := .all w (.not (ψ.subst x (.var w)))
  have hγx : γ.hasFree x = false := by
    simp [γ, PAFormula.hasFree, hasFree_subst_var_self_false hwx]
  have hfree : (PAFormula.not (ψ.subst x (.var w))).freeFor w (.var x) = true := by
    simp [PAFormula.freeFor, freeFor_inverse_var hw.2]
  have hsub : (PAFormula.not (ψ.subst x (.var w))).subst w (.var x) = ψ.not := by
    simp [PAFormula.subst, subst_inverse_var hw.2]
  have helim : PAProvable (.imp γ ψ.not) := by
    have h := PAProvable.all_elim w (.var x) (.not (ψ.subst x (.var w))) hfree
    rwa [hsub] at h
  have h1 : CtxProvable [γ] ψ.not :=
    .mp (.hyp (List.mem_singleton.mpr rfl)) (.ax helim)
  have h2 : CtxProvable [γ] (.all x (.imp ψ .bot)) :=
    ctx_gen x (fun δ hδ ↦ by rw [List.mem_singleton.mp hδ]; exact hγx) h1
  have h3 : CtxProvable [γ] (.not (.ex x ψ)) :=
    .mp h2 (.ax (.ex_elim x ψ .bot rfl))
  exact ctx_nil_iff.mp (ctx_deduction h3)

private theorem pa_de_morgan_all (y : ℕ) (ψ : PAFormula) :
    PAProvable (.imp (.not (.all y ψ)) (.ex y (.not ψ))) := by
  let γ₁ : PAFormula := (PAFormula.ex y ψ.not).not
  let γ₂ : PAFormula := (PAFormula.all y ψ).not
  have hfree : ψ.not.freeFor y (.var y) = true := freeFor_var_self y ψ.not
  have hex : PAProvable (.imp ψ.not (.ex y ψ.not)) := by
    have h := PAProvable.ex_intro y (.var y) ψ.not hfree
    rwa [subst_var_self] at h
  have hbot₁ : CtxProvable [ψ.not, γ₁, γ₂] .bot := by
    have hn : CtxProvable [ψ.not, γ₁, γ₂] ψ.not := .hyp (by simp)
    have hg₁ : CtxProvable [ψ.not, γ₁, γ₂] γ₁ := .hyp (by simp)
    exact .mp (.mp hn (.ax hex)) hg₁
  have hψ : CtxProvable [γ₁, γ₂] ψ := ctx_by_contra hbot₁
  have hall : CtxProvable [γ₁, γ₂] (.all y ψ) := by
    refine ctx_gen y (fun δ hδ ↦ ?_) hψ
    rcases List.mem_cons.mp hδ with rfl | hδ'
    · simp [γ₁, PAFormula.hasFree]
    · rw [List.mem_singleton.mp hδ']
      simp [γ₂, PAFormula.hasFree]
  have hbot₂ : CtxProvable [γ₁, γ₂] .bot :=
    .mp hall (.hyp (by simp [γ₂]))
  exact ctx_nil_iff.mp (ctx_deduction (ctx_by_contra hbot₂))

private theorem pa_eq_symm (s t : PATerm) :
    PAProvable (.imp (.eq s t) (.eq t s)) := by
  let x := max s.freshVar t.freshVar
  have hsx : s.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_max_left ..)
  let φ : PAFormula := .eq (.var x) s
  have hsub_s : φ.subst x s = .eq s s := by
    simp [φ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false s hsx]
  have hsub_t : φ.subst x t = .eq t s := by
    simp [φ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false t hsx]
  have heq := PAProvable.eq_subst x s t φ rfl rfl
  rw [hsub_s, hsub_t] at heq
  have hctx : CtxProvable [.eq s t] (.eq t s) :=
    .mp (.ax (.eq_refl s)) (.mp (.hyp (List.mem_singleton.mpr rfl)) (.ax heq))
  exact ctx_nil_iff.mp (ctx_deduction hctx)

private theorem pa_eq_trans (r s t : PATerm) :
    PAProvable (.imp (.eq r s) (.imp (.eq s t) (.eq r t))) := by
  let x := r.freshVar
  have hrx : r.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_refl _)
  let φ : PAFormula := .eq r (.var x)
  have hsub_s : φ.subst x s = .eq r s := by
    simp [φ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false s hrx]
  have hsub_t : φ.subst x t = .eq r t := by
    simp [φ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false t hrx]
  have heq := PAProvable.eq_subst x s t φ rfl rfl
  rw [hsub_s, hsub_t] at heq
  have hctx : CtxProvable [.eq s t, .eq r s] (.eq r t) :=
    .mp (.hyp (by simp)) (.mp (.hyp (by simp)) (.ax heq))
  exact ctx_nil_iff.mp (ctx_deduction (ctx_deduction hctx))

private theorem pa_eq_succ (s t : PATerm) :
    PAProvable (.imp (.eq s t) (.eq (.succ s) (.succ t))) := by
  let x := s.freshVar
  have hsx : s.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_refl _)
  let φ : PAFormula := .eq (.succ s) (.succ (.var x))
  have hsub_s : φ.subst x s = .eq (.succ s) (.succ s) := by
    simp [φ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false s hsx]
  have hsub_t : φ.subst x t = .eq (.succ s) (.succ t) := by
    simp [φ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false t hsx]
  have heq := PAProvable.eq_subst x s t φ rfl rfl
  rw [hsub_s, hsub_t] at heq
  have hctx : CtxProvable [.eq s t] (.eq (.succ s) (.succ t)) :=
    .mp (.ax (.eq_refl (.succ s))) (.mp (.hyp (List.mem_singleton.mpr rfl)) (.ax heq))
  exact ctx_nil_iff.mp (ctx_deduction hctx)

private theorem pa_eq_add (s₁ t₁ s₂ t₂ : PATerm) :
    PAProvable (.imp (.eq s₁ t₁) (.imp (.eq s₂ t₂) (.eq (.add s₁ s₂) (.add t₁ t₂)))) := by
  let x := max s₁.freshVar s₂.freshVar
  have hs₁x : s₁.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_max_left ..)
  have hs₂x : s₂.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_max_right ..)
  let φ₁ : PAFormula := .eq (.add s₁ s₂) (.add (.var x) s₂)
  have heq₁ := PAProvable.eq_subst x s₁ t₁ φ₁ rfl rfl
  simp only [φ₁, PAFormula.subst, PATerm.subst, beq_self_eq_true, ↓reduceIte,
    term_subst_eq_self_of_hasVar_false s₁ hs₁x, term_subst_eq_self_of_hasVar_false t₁ hs₁x,
    term_subst_eq_self_of_hasVar_false s₁ hs₂x, term_subst_eq_self_of_hasVar_false t₁ hs₂x] at heq₁
  let y := max t₁.freshVar s₂.freshVar
  have ht₁y : t₁.hasVar y = false := hasVar_false_of_freshVar_le (Nat.le_max_left ..)
  have hs₂y : s₂.hasVar y = false := hasVar_false_of_freshVar_le (Nat.le_max_right ..)
  let φ₂ : PAFormula := .eq (.add t₁ s₂) (.add t₁ (.var y))
  have heq₂ := PAProvable.eq_subst y s₂ t₂ φ₂ rfl rfl
  simp only [φ₂, PAFormula.subst, PATerm.subst, beq_self_eq_true, ↓reduceIte,
    term_subst_eq_self_of_hasVar_false s₂ ht₁y, term_subst_eq_self_of_hasVar_false t₂ ht₁y,
    term_subst_eq_self_of_hasVar_false s₂ hs₂y, term_subst_eq_self_of_hasVar_false t₂ hs₂y] at heq₂
  have hctx : CtxProvable [.eq s₂ t₂, .eq s₁ t₁] (.eq (.add s₁ s₂) (.add t₁ t₂)) := by
    have hA : CtxProvable [.eq s₂ t₂, .eq s₁ t₁] (.eq (.add s₁ s₂) (.add t₁ s₂)) :=
      .mp (.ax (.eq_refl (.add s₁ s₂))) (.mp (.hyp (by simp)) (.ax heq₁))
    have hB : CtxProvable [.eq s₂ t₂, .eq s₁ t₁] (.eq (.add t₁ s₂) (.add t₁ t₂)) :=
      .mp (.ax (.eq_refl (.add t₁ s₂))) (.mp (.hyp (by simp)) (.ax heq₂))
    exact .mp hB (.mp hA (.ax (pa_eq_trans (.add s₁ s₂) (.add t₁ s₂) (.add t₁ t₂))))
  exact ctx_nil_iff.mp (ctx_deduction (ctx_deduction hctx))

private theorem pa_eq_mul (s₁ t₁ s₂ t₂ : PATerm) :
    PAProvable (.imp (.eq s₁ t₁) (.imp (.eq s₂ t₂) (.eq (.mul s₁ s₂) (.mul t₁ t₂)))) := by
  let x := max s₁.freshVar s₂.freshVar
  have hs₁x : s₁.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_max_left ..)
  have hs₂x : s₂.hasVar x = false := hasVar_false_of_freshVar_le (Nat.le_max_right ..)
  let φ₁ : PAFormula := .eq (.mul s₁ s₂) (.mul (.var x) s₂)
  have heq₁ := PAProvable.eq_subst x s₁ t₁ φ₁ rfl rfl
  simp only [φ₁, PAFormula.subst, PATerm.subst, beq_self_eq_true, ↓reduceIte,
    term_subst_eq_self_of_hasVar_false s₁ hs₁x, term_subst_eq_self_of_hasVar_false t₁ hs₁x,
    term_subst_eq_self_of_hasVar_false s₁ hs₂x, term_subst_eq_self_of_hasVar_false t₁ hs₂x] at heq₁
  let y := max t₁.freshVar s₂.freshVar
  have ht₁y : t₁.hasVar y = false := hasVar_false_of_freshVar_le (Nat.le_max_left ..)
  have hs₂y : s₂.hasVar y = false := hasVar_false_of_freshVar_le (Nat.le_max_right ..)
  let φ₂ : PAFormula := .eq (.mul t₁ s₂) (.mul t₁ (.var y))
  have heq₂ := PAProvable.eq_subst y s₂ t₂ φ₂ rfl rfl
  simp only [φ₂, PAFormula.subst, PATerm.subst, beq_self_eq_true, ↓reduceIte,
    term_subst_eq_self_of_hasVar_false s₂ ht₁y, term_subst_eq_self_of_hasVar_false t₂ ht₁y,
    term_subst_eq_self_of_hasVar_false s₂ hs₂y, term_subst_eq_self_of_hasVar_false t₂ hs₂y] at heq₂
  have hctx : CtxProvable [.eq s₂ t₂, .eq s₁ t₁] (.eq (.mul s₁ s₂) (.mul t₁ t₂)) := by
    have hA : CtxProvable [.eq s₂ t₂, .eq s₁ t₁] (.eq (.mul s₁ s₂) (.mul t₁ s₂)) :=
      .mp (.ax (.eq_refl (.mul s₁ s₂))) (.mp (.hyp (by simp)) (.ax heq₁))
    have hB : CtxProvable [.eq s₂ t₂, .eq s₁ t₁] (.eq (.mul t₁ s₂) (.mul t₁ t₂)) :=
      .mp (.ax (.eq_refl (.mul t₁ s₂))) (.mp (.hyp (by simp)) (.ax heq₂))
    exact .mp hB (.mp hA (.ax (pa_eq_trans (.mul s₁ s₂) (.mul t₁ s₂) (.mul t₁ t₂))))
  exact ctx_nil_iff.mp (ctx_deduction (ctx_deduction hctx))

private theorem pa_exists_var_eq (B : ℕ) (t : PATerm) :
    let y := max B t.freshVar
    PAProvable (.ex y (.eq (.var y) t)) := by
  intro y
  have hty : t.hasVar y = false := hasVar_false_of_freshVar_le (Nat.le_max_right ..)
  let ψ : PAFormula := .eq (.var y) t
  have hsub : ψ.subst y t = .eq t t := by
    simp [ψ, PAFormula.subst, PATerm.subst, term_subst_eq_self_of_hasVar_false t hty]
  have hex := PAProvable.ex_intro y t ψ rfl
  rw [hsub] at hex
  exact .mp (.eq_refl t) hex

/-! ## Section 3: Countable Formula Enumeration and Henkin–Lindenbaum Saturation -/

private def encodeTerm : PATerm → ℕ
  | .zero => 0
  | .var x => Nat.pair 0 x + 1
  | .succ t => Nat.pair 1 (encodeTerm t) + 1
  | .add t₁ t₂ => Nat.pair 2 (Nat.pair (encodeTerm t₁) (encodeTerm t₂)) + 1
  | .mul t₁ t₂ => Nat.pair 3 (Nat.pair (encodeTerm t₁) (encodeTerm t₂)) + 1

private def decodeTerm : ℕ → PATerm
  | 0 => .zero
  | n + 1 =>
    let p := Nat.unpair n
    let q := Nat.unpair p.2
    match p.1 with
    | 0 => .var p.2
    | 1 => .succ (decodeTerm p.2)
    | 2 => .add (decodeTerm q.1) (decodeTerm q.2)
    | 3 => .mul (decodeTerm q.1) (decodeTerm q.2)
    | _ => .zero
termination_by k => k
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.unpair_right_le n)
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le n))
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le n))
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le n))
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le n))

private theorem decodeTerm_encodeTerm (t : PATerm) : decodeTerm (encodeTerm t) = t := by
  induction t with
  | zero => simp [encodeTerm, decodeTerm]
  | var x => simp [encodeTerm, decodeTerm, Nat.unpair_pair]
  | succ t ih => simp [encodeTerm, decodeTerm, Nat.unpair_pair, ih]
  | add t₁ t₂ ih₁ ih₂ => simp [encodeTerm, decodeTerm, Nat.unpair_pair, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => simp [encodeTerm, decodeTerm, Nat.unpair_pair, ih₁, ih₂]

private def encodeForm : PAFormula → ℕ
  | .bot => 0
  | .eq t₁ t₂ => Nat.pair 0 (Nat.pair (encodeTerm t₁) (encodeTerm t₂)) + 1
  | .and φ ψ => Nat.pair 1 (Nat.pair (encodeForm φ) (encodeForm ψ)) + 1
  | .or φ ψ => Nat.pair 2 (Nat.pair (encodeForm φ) (encodeForm ψ)) + 1
  | .imp φ ψ => Nat.pair 3 (Nat.pair (encodeForm φ) (encodeForm ψ)) + 1
  | .all x φ => Nat.pair 4 (Nat.pair x (encodeForm φ)) + 1
  | .ex x φ => Nat.pair 5 (Nat.pair x (encodeForm φ)) + 1

private def decodeForm : ℕ → PAFormula
  | 0 => .bot
  | n + 1 =>
    let p := Nat.unpair n
    let q := Nat.unpair p.2
    match p.1 with
    | 0 => .eq (decodeTerm q.1) (decodeTerm q.2)
    | 1 => .and (decodeForm q.1) (decodeForm q.2)
    | 2 => .or (decodeForm q.1) (decodeForm q.2)
    | 3 => .imp (decodeForm q.1) (decodeForm q.2)
    | 4 => .all q.1 (decodeForm q.2)
    | 5 => .ex q.1 (decodeForm q.2)
    | _ => .bot
termination_by k => k
decreasing_by
  all_goals
    first
    | exact Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le n))
    | exact Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le n))

private theorem decodeForm_encodeForm (φ : PAFormula) : decodeForm (encodeForm φ) = φ := by
  induction φ with
  | bot => simp [encodeForm, decodeForm]
  | eq t₁ t₂ =>
    simp [encodeForm, decodeForm, Nat.unpair_pair, decodeTerm_encodeTerm]
  | and _ _ ih₁ ih₂ => simp [encodeForm, decodeForm, Nat.unpair_pair, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [encodeForm, decodeForm, Nat.unpair_pair, ih₁, ih₂]
  | imp _ _ ih₁ ih₂ => simp [encodeForm, decodeForm, Nat.unpair_pair, ih₁, ih₂]
  | all _ _ ih => simp [encodeForm, decodeForm, Nat.unpair_pair, ih]
  | ex _ _ ih => simp [encodeForm, decodeForm, Nat.unpair_pair, ih]

private def maxVarList : List PAFormula → ℕ
  | [] => 0
  | φ :: rest => max φ.maxVar (maxVarList rest)

private theorem maxVar_le_maxVarList {Δ : List PAFormula} {φ : PAFormula} (h : φ ∈ Δ) :
    φ.maxVar ≤ maxVarList Δ := by
  induction Δ with
  | nil => cases h
  | cons δ rest ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact Nat.le_max_left ..
    · exact le_trans (ih hm) (Nat.le_max_right ..)

private theorem henkin_step_consistent {Δ : List PAFormula} (x : ℕ) (ψ : PAFormula)
    (hcons : ¬ CtxProvable Δ .bot) :
    let w := max (maxVarList Δ) (PAFormula.ex x ψ).maxVar
    ¬ CtxProvable ((.imp (.ex x ψ) (ψ.subst x (.var w))) :: Δ) .bot := by
  intro w hbot
  apply hcons
  let θ := PAFormula.imp (.ex x ψ) (ψ.subst x (.var w))
  have hθ_not : CtxProvable Δ θ.not := ctx_deduction hbot
  have hex : CtxProvable Δ (.ex x ψ) := by
    refine ctx_by_contra ?_
    have h1 : CtxProvable [.ex x ψ, (PAFormula.ex x ψ).not] (ψ.subst x (.var w)) :=
      ctx_exfalso _ (.mp (φ := PAFormula.ex x ψ) (.hyp (by simp)) (.hyp (by simp)))
    have h2 : CtxProvable [(PAFormula.ex x ψ).not] θ := ctx_deduction h1
    have h3 : CtxProvable ((PAFormula.ex x ψ).not :: Δ) θ :=
      ctx_mono (fun _ hm ↦ by simp [List.mem_singleton.mp hm]) h2
    have h4 : CtxProvable ((PAFormula.ex x ψ).not :: Δ) θ.not :=
      ctx_mono (fun _ hm ↦ List.mem_cons_of_mem _ hm) hθ_not
    exact .mp h3 h4
  have hn_sub : CtxProvable Δ (ψ.subst x (.var w)).not := by
    refine ctx_deduction ?_
    have h1 : CtxProvable (ψ.subst x (.var w) :: Δ) θ :=
      .mp (.hyp (List.mem_cons_self ..)) (.ax (.imp_k _ _))
    have h2 : CtxProvable (ψ.subst x (.var w) :: Δ) θ.not :=
      ctx_mono (fun _ hm ↦ List.mem_cons_of_mem _ hm) hθ_not
    exact .mp h1 h2
  have hfresh : ∀ γ ∈ Δ, γ.hasFree w = false := fun γ hγ ↦
    hasFree_false_of_maxVar_le (le_trans (maxVar_le_maxVarList hγ) (Nat.le_max_left ..))
  have hall : CtxProvable Δ (.all w (ψ.subst x (.var w)).not) := ctx_gen w hfresh hn_sub
  have hn_ex : CtxProvable Δ (PAFormula.ex x ψ).not :=
    .mp hall (.ax (pa_all_not_subst_imp_not_ex (Nat.le_max_right ..)))
  exact .mp hex hn_ex

/-- Add Henkin witness if `ψ` is existential. -/
private def extendWithWitness (ψ : PAFormula) (Δ : List PAFormula) : List PAFormula :=
  match ψ with
  | .ex x χ =>
    let w := max (maxVarList (ψ :: Δ)) (PAFormula.ex x χ).maxVar
    (.imp (.ex x χ) (χ.subst x (.var w))) :: ψ :: Δ
  | _ => ψ :: Δ

/-- Single-pass Henkin–Lindenbaum chain starting from `[φ₀]`. -/
private noncomputable def henkinChain (φ₀ : PAFormula) : ℕ → List PAFormula
  | 0 => [φ₀]
  | n + 1 =>
    let Δ := henkinChain φ₀ n
    let ψ := decodeForm n
    open Classical in
    if CtxProvable (ψ :: Δ) .bot then
      ψ.not :: Δ
    else
      extendWithWitness ψ Δ

private theorem henkinChain_subset_succ (φ₀ : PAFormula) (n : ℕ) :
    ∀ α ∈ henkinChain φ₀ n, α ∈ henkinChain φ₀ (n + 1) := by
  intro α hα
  simp only [henkinChain]
  split_ifs
  · exact List.mem_cons_of_mem _ hα
  · unfold extendWithWitness
    cases decodeForm n <;> simp [hα]

private theorem henkinChain_mono (φ₀ : PAFormula) {m n : ℕ} (h : m ≤ n) :
    ∀ α ∈ henkinChain φ₀ m, α ∈ henkinChain φ₀ n := by
  induction h with
  | refl => exact fun _ hα ↦ hα
  | step _ ih => exact fun α hα ↦ henkinChain_subset_succ φ₀ _ α (ih α hα)

private theorem henkinChain_consistent {φ₀ : PAFormula} (h₀ : ¬ CtxProvable [φ₀] .bot) :
    ∀ n, ¬ CtxProvable (henkinChain φ₀ n) .bot := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    simp only [henkinChain]
    split_ifs with hbot_ψ
    · have hnψ : CtxProvable (henkinChain φ₀ n) (decodeForm n).not := ctx_deduction hbot_ψ
      intro hbot
      exact ih (.mp hnψ (ctx_deduction hbot))
    · unfold extendWithWitness
      cases hdec : decodeForm n with
      | ex x χ =>
        rw [hdec] at hbot_ψ
        exact henkin_step_consistent x χ hbot_ψ
      | _ =>
        rwa [hdec] at hbot_ψ

/-- Maximal consistent Henkin-saturated theory extending `φ₀`. -/
private def henkinTheory (φ₀ : PAFormula) : Set PAFormula :=
  { α | ∃ n, α ∈ henkinChain φ₀ n }

private theorem henkinTheory_mem_zero (φ₀ : PAFormula) :
    φ₀ ∈ henkinTheory φ₀ :=
  ⟨0, List.mem_singleton.mpr rfl⟩

private theorem henkinTheory_not_bot {φ₀ : PAFormula} (h₀ : ¬ CtxProvable [φ₀] .bot) :
    PAFormula.bot ∉ henkinTheory φ₀ := by
  rintro ⟨n, hn⟩
  exact henkinChain_consistent h₀ n (.hyp hn)

private theorem henkinTheory_complete (φ₀ : PAFormula) (ψ : PAFormula) :
    ψ ∈ henkinTheory φ₀ ∨ ψ.not ∈ henkinTheory φ₀ := by
  let n := encodeForm ψ
  have hdec : decodeForm n = ψ := decodeForm_encodeForm ψ
  by_cases hbot : CtxProvable (ψ :: henkinChain φ₀ n) .bot
  · refine Or.inr ⟨n + 1, ?_⟩
    simp only [henkinChain, hdec, hbot, ↓reduceIte]
    exact List.mem_cons_self ..
  · refine Or.inl ⟨n + 1, ?_⟩
    simp only [henkinChain, hdec, hbot, ↓reduceIte]
    unfold extendWithWitness
    cases ψ <;> simp

private theorem henkinChain_fin_subset {φ₀ : PAFormula} (Γ : List PAFormula)
    (hΓ : ∀ γ ∈ Γ, γ ∈ henkinTheory φ₀) :
    ∃ N, ∀ γ ∈ Γ, γ ∈ henkinChain φ₀ N := by
  induction Γ with
  | nil => exact ⟨0, fun _ hm ↦ False.elim (List.not_mem_nil hm)⟩
  | cons δ rest ih =>
    obtain ⟨n₁, hn₁⟩ := hΓ δ (List.mem_cons_self ..)
    obtain ⟨n₂, hn₂⟩ := ih fun γ hγ ↦ hΓ γ (List.mem_cons_of_mem _ hγ)
    refine ⟨max n₁ n₂, fun γ hγ ↦ ?_⟩
    rcases List.mem_cons.mp hγ with heq | hm
    · subst heq
      exact henkinChain_mono φ₀ (Nat.le_max_left ..) _ hn₁
    · exact henkinChain_mono φ₀ (Nat.le_max_right ..) γ (hn₂ γ hm)

private theorem henkinTheory_closed {φ₀ : PAFormula} (h₀ : ¬ CtxProvable [φ₀] .bot)
    {Γ : List PAFormula} {α : PAFormula} (hprov : CtxProvable Γ α)
    (hΓ : ∀ γ ∈ Γ, γ ∈ henkinTheory φ₀) :
    α ∈ henkinTheory φ₀ := by
  obtain ⟨N, hN⟩ := henkinChain_fin_subset Γ hΓ
  have hctx : CtxProvable (henkinChain φ₀ N) α := ctx_mono hN hprov
  rcases henkinTheory_complete φ₀ α with hα | hnα
  · exact hα
  · obtain ⟨M, hM⟩ := hnα
    let K := max N M
    have h₁ : CtxProvable (henkinChain φ₀ K) α :=
      ctx_mono (henkinChain_mono φ₀ (Nat.le_max_left ..)) hctx
    have h₂ : α.not ∈ henkinChain φ₀ K :=
      henkinChain_mono φ₀ (Nat.le_max_right ..) _ hM
    exact False.elim (henkinChain_consistent h₀ K (.mp h₁ (.hyp h₂)))

private theorem henkinTheory_ax {φ₀ : PAFormula} (h₀ : ¬ CtxProvable [φ₀] .bot)
    {α : PAFormula} (hp : PAProvable α) : α ∈ henkinTheory φ₀ :=
  henkinTheory_closed h₀ (Γ := []) (.ax hp) (fun _ hm ↦ False.elim (List.not_mem_nil hm))

private theorem henkinTheory_mp {φ₀ : PAFormula} (h₀ : ¬ CtxProvable [φ₀] .bot)
    {α β : PAFormula} (hα : α ∈ henkinTheory φ₀) (himp : .imp α β ∈ henkinTheory φ₀) :
    β ∈ henkinTheory φ₀ :=
  henkinTheory_closed h₀ (Γ := [α, .imp α β])
    (.mp (φ := α) (.hyp (by simp)) (.hyp (by simp))) (by
      intro γ hγ
      rcases List.mem_cons.mp hγ with heq | hγ'
      · subst heq; exact hα
      · rw [List.mem_singleton.mp hγ']
        exact himp)

private theorem henkinTheory_witness {φ₀ : PAFormula} (h₀ : ¬ CtxProvable [φ₀] .bot)
    {x : ℕ} {χ : PAFormula} (hex : .ex x χ ∈ henkinTheory φ₀) :
    ∃ w : ℕ, (PAFormula.ex x χ).maxVar ≤ w ∧ χ.subst x (.var w) ∈ henkinTheory φ₀ := by
  let n := encodeForm (.ex x χ)
  have hdec : decodeForm n = .ex x χ := decodeForm_encodeForm (.ex x χ)
  by_cases hbot : CtxProvable (PAFormula.ex x χ :: henkinChain φ₀ n) .bot
  · have hn : (PAFormula.ex x χ).not ∈ henkinTheory φ₀ := by
      refine ⟨n + 1, ?_⟩
      simp only [henkinChain, hdec, hbot, ↓reduceIte]
      exact List.mem_cons_self ..
    exact False.elim (henkinTheory_not_bot h₀ (henkinTheory_mp h₀ hex hn))
  · let w := max (maxVarList (PAFormula.ex x χ :: henkinChain φ₀ n)) (PAFormula.ex x χ).maxVar
    have himp : PAFormula.imp (.ex x χ) (χ.subst x (.var w)) ∈ henkinTheory φ₀ := by
      refine ⟨n + 1, ?_⟩
      simp only [henkinChain, hdec, hbot, ↓reduceIte, extendWithWitness]
      exact List.mem_cons_self ..
    exact ⟨w, Nat.le_max_right .., henkinTheory_mp h₀ hex himp⟩

/-! ## Section 4: Quotient Henkin Model, Truth Lemma, and Completeness -/

section HenkinModel

variable {φ₀ : PAFormula}

private def HenkinSetoid (h₀ : ¬ CtxProvable [φ₀] .bot) : Setoid PATerm where
  r s t := PAFormula.eq s t ∈ henkinTheory φ₀
  iseqv := {
    refl := fun t ↦ henkinTheory_ax h₀ (.eq_refl t)
    symm := fun {s t} h ↦ henkinTheory_mp h₀ h (henkinTheory_ax h₀ (pa_eq_symm s t))
    trans := fun {r s t} h₁ h₂ ↦
      henkinTheory_mp h₀ h₂ (henkinTheory_mp h₀ h₁ (henkinTheory_ax h₀ (pa_eq_trans r s t)))
  }

private abbrev HenkinCarrier (h₀ : ¬ CtxProvable [φ₀] .bot) : Type :=
  Quotient (HenkinSetoid h₀)

private instance instPAStructureHenkin (h₀ : ¬ CtxProvable [φ₀] .bot) :
    PAStructure (HenkinCarrier h₀) where
  zero := Quotient.mk (HenkinSetoid h₀) .zero
  succ := Quotient.lift (fun t ↦ Quotient.mk (HenkinSetoid h₀) (.succ t))
    fun s t hst ↦ Quotient.sound (henkinTheory_mp h₀ hst (henkinTheory_ax h₀ (pa_eq_succ s t)))
  add := Quotient.lift₂ (fun s t ↦ Quotient.mk (HenkinSetoid h₀) (.add s t))
    fun s₁ s₂ t₁ t₂ h₁ h₂ ↦ Quotient.sound
      (henkinTheory_mp h₀ h₂ (henkinTheory_mp h₀ h₁ (henkinTheory_ax h₀ (pa_eq_add s₁ t₁ s₂ t₂))))
  mul := Quotient.lift₂ (fun s t ↦ Quotient.mk (HenkinSetoid h₀) (.mul s t))
    fun s₁ s₂ t₁ t₂ h₁ h₂ ↦ Quotient.sound
      (henkinTheory_mp h₀ h₂ (henkinTheory_mp h₀ h₁ (henkinTheory_ax h₀ (pa_eq_mul s₁ t₁ s₂ t₂))))

private theorem evalIn_henkin_vsubst (h₀ : ¬ CtxProvable [φ₀] .bot) (ρ : ℕ → ℕ) (t : PATerm) :
    PATerm.evalIn (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (ρ x))) t =
      Quotient.mk (HenkinSetoid h₀) (t.vsubst ρ) := by
  induction t with
  | var _ | zero => rfl
  | succ _ ih =>
    simp only [PATerm.evalIn, ih, PATerm.vsubst]
    rfl
  | add _ _ ih₁ ih₂ =>
    simp only [PATerm.evalIn, ih₁, ih₂, PATerm.vsubst]
    rfl
  | mul _ _ ih₁ ih₂ =>
    simp only [PATerm.evalIn, ih₁, ih₂, PATerm.vsubst]
    rfl

private theorem exists_var_rep (h₀ : ¬ CtxProvable [φ₀] .bot) (B : ℕ) (a : HenkinCarrier h₀) :
    ∃ w : ℕ, B ≤ w ∧ Quotient.mk (HenkinSetoid h₀) (.var w) = a := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep a
  let y := max B t.freshVar
  have hex : PAFormula.ex y (.eq (.var y) t) ∈ henkinTheory φ₀ :=
    henkinTheory_ax h₀ (pa_exists_var_eq B t)
  obtain ⟨w, hw, hsub⟩ := henkinTheory_witness h₀ hex
  have hty : t.hasVar y = false := hasVar_false_of_freshVar_le (Nat.le_max_right ..)
  have ht_w : t.subst y (.var w) = t := term_subst_eq_self_of_hasVar_false (.var w) hty
  simp only [PAFormula.subst, PATerm.subst, beq_self_eq_true, ↓reduceIte, ht_w] at hsub
  have hBw : B ≤ w := by
    simp only [PAFormula.maxVar, Nat.max_le] at hw
    have : B ≤ y := Nat.le_max_left ..
    omega
  exact ⟨w, hBw, Quotient.sound hsub⟩

private theorem henkin_truth_vsubst (h₀ : ¬ CtxProvable [φ₀] .bot) (φ : PAFormula) :
    ∀ {ρ : ℕ → ℕ}, SafeFor ρ φ →
      (PAFormula.HoldsIn (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (ρ x))) φ ↔
        φ.vsubst ρ ∈ henkinTheory φ₀) := by
  induction φ with
  | bot =>
    intro ρ _
    exact ⟨False.elim, fun h ↦ henkinTheory_not_bot h₀ h⟩
  | eq t₁ t₂ =>
    intro ρ _
    simp only [PAFormula.HoldsIn, evalIn_henkin_vsubst, PAFormula.vsubst, Quotient.eq]
    rfl
  | and φ ψ ih₁ ih₂ =>
    intro ρ hsafe
    have hs₁ : SafeFor ρ φ :=
      safeFor_mono hsafe (Nat.le_max_left ..) (fun x hx ↦ by simp [PAFormula.hasFree, hx])
    have hs₂ : SafeFor ρ ψ :=
      safeFor_mono hsafe (Nat.le_max_right ..) (fun x hx ↦ by simp [PAFormula.hasFree, hx])
    simp only [PAFormula.HoldsIn, ih₁ hs₁, ih₂ hs₂, PAFormula.vsubst]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ henkinTheory_mp h₀ h₂
      (henkinTheory_mp h₀ h₁ (henkinTheory_ax h₀ (.and_intro _ _))), fun h ↦
      ⟨henkinTheory_mp h₀ h (henkinTheory_ax h₀ (.and_left _ _)),
        henkinTheory_mp h₀ h (henkinTheory_ax h₀ (.and_right _ _))⟩⟩
  | or φ ψ ih₁ ih₂ =>
    intro ρ hsafe
    have hs₁ : SafeFor ρ φ :=
      safeFor_mono hsafe (Nat.le_max_left ..) (fun x hx ↦ by simp [PAFormula.hasFree, hx])
    have hs₂ : SafeFor ρ ψ :=
      safeFor_mono hsafe (Nat.le_max_right ..) (fun x hx ↦ by simp [PAFormula.hasFree, hx])
    simp only [PAFormula.HoldsIn, ih₁ hs₁, ih₂ hs₂, PAFormula.vsubst]
    refine ⟨fun h ↦ ?_, fun hor ↦ ?_⟩
    · rcases h with h₁ | h₂
      · exact henkinTheory_mp h₀ h₁ (henkinTheory_ax h₀ (.or_left _ _))
      · exact henkinTheory_mp h₀ h₂ (henkinTheory_ax h₀ (.or_right _ _))
    · rcases henkinTheory_complete φ₀ (φ.vsubst ρ) with h₁ | hn₁
      · exact Or.inl h₁
      · rcases henkinTheory_complete φ₀ (ψ.vsubst ρ) with h₂ | hn₂
        · exact Or.inr h₂
        · exfalso
          have helim := henkinTheory_ax h₀ (.or_elim (φ.vsubst ρ) (ψ.vsubst ρ) .bot)
          exact henkinTheory_not_bot h₀
            (henkinTheory_mp h₀ hor (henkinTheory_mp h₀ hn₂ (henkinTheory_mp h₀ hn₁ helim)))
  | imp φ ψ ih₁ ih₂ =>
    intro ρ hsafe
    have hs₁ : SafeFor ρ φ :=
      safeFor_mono hsafe (Nat.le_max_left ..) (fun x hx ↦ by simp [PAFormula.hasFree, hx])
    have hs₂ : SafeFor ρ ψ :=
      safeFor_mono hsafe (Nat.le_max_right ..) (fun x hx ↦ by simp [PAFormula.hasFree, hx])
    simp only [PAFormula.HoldsIn, ih₁ hs₁, ih₂ hs₂, PAFormula.vsubst]
    refine ⟨fun h ↦ ?_, fun himp h₁ ↦ henkinTheory_mp h₀ h₁ himp⟩
    rcases henkinTheory_complete φ₀ (φ.vsubst ρ) with h₁ | hn₁
    · exact henkinTheory_mp h₀ (h h₁) (henkinTheory_ax h₀ (.imp_k _ _))
    · have hctx : CtxProvable [(φ.vsubst ρ).not] (.imp (φ.vsubst ρ) (ψ.vsubst ρ)) :=
        ctx_deduction (ctx_exfalso _ (.mp (φ := φ.vsubst ρ) (.hyp (by simp)) (.hyp (by simp))))
      exact henkinTheory_closed h₀ hctx (fun γ hγ ↦ by rw [List.mem_singleton.mp hγ]; exact hn₁)
  | all y φ ih =>
    intro ρ hsafe
    let ψ' := φ.vsubst (Function.update ρ y y)
    have hno_cap : ∀ x, φ.hasFree x = true → x ≠ y → ρ x ≠ y := by
      intro x hx hxy
      have hall_free : (PAFormula.all y φ).hasFree x = true := by
        simp [PAFormula.hasFree, Ne.symm hxy, hx]
      rcases hsafe x hall_free with heq | hge
      · rw [heq]; exact hxy
      · simp only [PAFormula.maxVar, Nat.max_le] at hge
        omega
    have hsafe_base : ∀ x, φ.hasFree x = true → x ≠ y → ρ x = x ∨ φ.maxVar ≤ ρ x := by
      intro x hx hxy
      have hall_free : (PAFormula.all y φ).hasFree x = true := by
        simp [PAFormula.hasFree, Ne.symm hxy, hx]
      rcases hsafe x hall_free with heq | hge
      · exact Or.inl heq
      · simp only [PAFormula.maxVar, Nat.max_le] at hge
        exact Or.inr hge.2
    have hmax_le : φ.maxVar ≤ ψ'.maxVar := by
      refine maxVar_le_vsubst_maxVar fun x hx ↦ ?_
      by_cases hxy : x = y
      · subst hxy; simp
      · simp only [Function.update_of_ne hxy]
        rcases hsafe_base x hx hxy with heq | hge
        · omega
        · exact le_trans (Nat.le_of_lt (lt_maxVar_of_hasFree hx)) hge
    simp only [PAFormula.HoldsIn, PAFormula.vsubst]
    refine ⟨fun hsem ↦ ?_, fun hall a ↦ ?_⟩
    · rcases henkinTheory_complete φ₀ (.all y ψ') with hmem | hnmem
      · exact hmem
      · exfalso
        have hex : PAFormula.ex y ψ'.not ∈ henkinTheory φ₀ :=
          henkinTheory_mp h₀ hnmem (henkinTheory_ax h₀ (pa_de_morgan_all y ψ'))
        obtain ⟨w, hw, hsub⟩ := henkinTheory_witness h₀ hex
        simp only [PAFormula.maxVar, Nat.max_le] at hw
        have hw_φ : φ.maxVar ≤ w := le_trans hmax_le hw.2.1
        have hsub_eq : ψ'.subst y (.var w) = φ.vsubst (Function.update ρ y w) :=
          vsubst_subst_var hno_cap
        simp only [PAFormula.subst, hsub_eq] at hsub
        have hval := hsem (Quotient.mk (HenkinSetoid h₀) (.var w))
        have hfun : Function.update (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (ρ x))) y
            (Quotient.mk (HenkinSetoid h₀) (.var w)) =
            fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (Function.update ρ y w x)) := by
          funext x
          by_cases hxy : x = y
          · subst hxy; simp
          · simp [hxy]
        rw [hfun, ih (safeFor_update_fresh hsafe_base hw_φ)] at hval
        exact henkinTheory_not_bot h₀ (henkinTheory_mp h₀ hval hsub)
    · obtain ⟨w, hw, hrep⟩ := exists_var_rep h₀ (max φ.maxVar ψ'.maxVar) a
      have hw_φ : φ.maxVar ≤ w := le_trans (Nat.le_max_left ..) hw
      have hw_ψ' : ψ'.maxVar ≤ w := le_trans (Nat.le_max_right ..) hw
      have helim := henkinTheory_ax h₀ (.all_elim y (.var w) ψ' (freeFor_var_of_maxVar_le y hw_ψ'))
      have hinst : ψ'.subst y (.var w) ∈ henkinTheory φ₀ := henkinTheory_mp h₀ hall helim
      rw [vsubst_subst_var hno_cap] at hinst
      have hhold := (ih (safeFor_update_fresh hsafe_base hw_φ)).mpr hinst
      have hfun : (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (Function.update ρ y w x))) =
          Function.update (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (ρ x))) y a := by
        funext x
        by_cases hxy : x = y
        · subst hxy; simp [hrep]
        · simp [hxy]
      rwa [hfun] at hhold
  | ex y φ ih =>
    intro ρ hsafe
    let ψ' := φ.vsubst (Function.update ρ y y)
    have hno_cap : ∀ x, φ.hasFree x = true → x ≠ y → ρ x ≠ y := by
      intro x hx hxy
      have hex_free : (PAFormula.ex y φ).hasFree x = true := by
        simp [PAFormula.hasFree, Ne.symm hxy, hx]
      rcases hsafe x hex_free with heq | hge
      · rw [heq]; exact hxy
      · simp only [PAFormula.maxVar, Nat.max_le] at hge
        omega
    have hsafe_base : ∀ x, φ.hasFree x = true → x ≠ y → ρ x = x ∨ φ.maxVar ≤ ρ x := by
      intro x hx hxy
      have hex_free : (PAFormula.ex y φ).hasFree x = true := by
        simp [PAFormula.hasFree, Ne.symm hxy, hx]
      rcases hsafe x hex_free with heq | hge
      · exact Or.inl heq
      · simp only [PAFormula.maxVar, Nat.max_le] at hge
        exact Or.inr hge.2
    have hmax_le : φ.maxVar ≤ ψ'.maxVar := by
      refine maxVar_le_vsubst_maxVar fun x hx ↦ ?_
      by_cases hxy : x = y
      · subst hxy; simp
      · simp only [Function.update_of_ne hxy]
        rcases hsafe_base x hx hxy with heq | hge
        · omega
        · exact le_trans (Nat.le_of_lt (lt_maxVar_of_hasFree hx)) hge
    simp only [PAFormula.HoldsIn, PAFormula.vsubst]
    refine ⟨?_, fun hex ↦ ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨w, hw, hrep⟩ := exists_var_rep h₀ (max φ.maxVar ψ'.maxVar) a
      have hw_φ : φ.maxVar ≤ w := le_trans (Nat.le_max_left ..) hw
      have hw_ψ' : ψ'.maxVar ≤ w := le_trans (Nat.le_max_right ..) hw
      have hfun : Function.update (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (ρ x))) y a =
          fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (Function.update ρ y w x)) := by
        funext x
        by_cases hxy : x = y
        · subst hxy; simp [hrep]
        · simp [hxy]
      rw [hfun, ih (safeFor_update_fresh hsafe_base hw_φ)] at ha
      rw [← vsubst_subst_var hno_cap] at ha
      have hintro := henkinTheory_ax h₀ (.ex_intro y (.var w) ψ' (freeFor_var_of_maxVar_le y hw_ψ'))
      exact henkinTheory_mp h₀ ha hintro
    · obtain ⟨w, hw, hsub⟩ := henkinTheory_witness h₀ hex
      simp only [PAFormula.maxVar, Nat.max_le] at hw
      have hw_φ : φ.maxVar ≤ w := le_trans hmax_le hw.2
      rw [vsubst_subst_var hno_cap] at hsub
      have hhold := (ih (safeFor_update_fresh hsafe_base hw_φ)).mpr hsub
      refine ⟨Quotient.mk (HenkinSetoid h₀) (.var w), ?_⟩
      have hfun : (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (Function.update ρ y w x))) =
          Function.update (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var (ρ x))) y
            (Quotient.mk (HenkinSetoid h₀) (.var w)) := by
        funext x
        by_cases hxy : x = y
        · subst hxy; simp
        · simp [hxy]
      rwa [hfun] at hhold

private theorem henkin_truth_id (h₀ : ¬ CtxProvable [φ₀] .bot) (φ : PAFormula) :
    PAFormula.HoldsIn (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var x)) φ ↔
      φ ∈ henkinTheory φ₀ := by
  have h := henkin_truth_vsubst h₀ φ (safeFor_id φ)
  rwa [vsubst_id] at h

private theorem henkin_holds_of_provable (h₀ : ¬ CtxProvable [φ₀] .bot) {φ : PAFormula}
    (hp : PAProvable φ) :
    PAFormula.HoldsIn (fun x ↦ Quotient.mk (HenkinSetoid h₀) (.var x)) φ :=
  (henkin_truth_id h₀ φ).mpr (henkinTheory_ax h₀ hp)

private instance instPAModelHenkin (h₀ : ¬ CtxProvable [φ₀] .bot) :
    PAModel (HenkinCarrier h₀) where
  zero_ne_succ a := by
    have h := henkin_holds_of_provable h₀ (.gen 0 .pa_zero_ne_succ)
    exact h a
  succ_inj {a b} hab := by
    have h := henkin_holds_of_provable h₀ (.gen 0 (.gen 1 .pa_succ_inj))
    have h1 := h a b
    have h01 : (0 : ℕ) ≠ 1 := by decide
    simp only [PAFormula.HoldsIn, PATerm.evalIn, Function.update_self,
      Function.update_of_ne h01] at h1
    exact h1 hab
  add_zero a := by
    have h := henkin_holds_of_provable h₀ (.gen 0 .pa_add_zero)
    exact h a
  add_succ a b := by
    have h := henkin_holds_of_provable h₀ (.gen 0 (.gen 1 .pa_add_succ))
    have h1 := h a b
    have h01 : (0 : ℕ) ≠ 1 := by decide
    simp only [PAFormula.HoldsIn, PATerm.evalIn, Function.update_self,
      Function.update_of_ne h01] at h1
    exact h1
  mul_zero a := by
    have h := henkin_holds_of_provable h₀ (.gen 0 .pa_mul_zero)
    exact h a
  mul_succ a b := by
    have h := henkin_holds_of_provable h₀ (.gen 0 (.gen 1 .pa_mul_succ))
    have h1 := h a b
    have h01 : (0 : ℕ) ≠ 1 := by decide
    simp only [PAFormula.HoldsIn, PATerm.evalIn, Function.update_self,
      Function.update_of_ne h01] at h1
    exact h1
  ind x φ v hbase hstep a := by
    have hex_ρ : ∀ z : ℕ, ∃ w : ℕ, max φ.maxVar (x + 1) ≤ w ∧
        Quotient.mk (HenkinSetoid h₀) (.var w) = v z :=
      fun z ↦ exists_var_rep h₀ (max φ.maxVar (x + 1)) (v z)
    choose ρ hρ_ge hρ_eq using hex_ρ
    let ψ := φ.vsubst (Function.update ρ x x)
    let v₀ : ℕ → HenkinCarrier h₀ := fun z ↦ Quotient.mk (HenkinSetoid h₀) (.var z)
    have hiff : ∀ b : HenkinCarrier h₀,
        PAFormula.HoldsIn (Function.update v x b) φ ↔
          PAFormula.HoldsIn (Function.update v₀ x b) ψ := by
      intro b
      obtain ⟨w, hw, hrep⟩ := exists_var_rep h₀ (max φ.maxVar ψ.maxVar) b
      have hw_φ : φ.maxVar ≤ w := le_trans (Nat.le_max_left ..) hw
      have hw_ψ : ψ.maxVar ≤ w := le_trans (Nat.le_max_right ..) hw
      have hv_eq : Function.update v x b =
          fun z ↦ Quotient.mk (HenkinSetoid h₀) (.var (Function.update ρ x w z)) := by
        funext z
        by_cases hzx : z = x
        · subst hzx; simp [hrep]
        · simp [hzx, hρ_eq z]
      have hv₀_eq : Function.update v₀ x b =
          fun z ↦ Quotient.mk (HenkinSetoid h₀) (.var (Function.update id x w z)) := by
        funext z
        by_cases hzx : z = x
        · subst hzx; simp [hrep]
        · simp [hzx, v₀]
      have hsafe_φ : SafeFor (Function.update ρ x w) φ :=
        safeFor_update_fresh (fun z _ _ ↦ Or.inr (le_trans (Nat.le_max_left ..) (hρ_ge z))) hw_φ
      have hsafe_ψ : SafeFor (Function.update id x w) ψ :=
        safeFor_update_fresh (fun _ _ _ ↦ Or.inl rfl) hw_ψ
      have hno_cap : ∀ z, φ.hasFree z = true → z ≠ x → ρ z ≠ x := by
        intro z _ _
        have hge := hρ_ge z
        simp only [Nat.max_le] at hge
        omega
      have heq_form : ψ.vsubst (Function.update id x w) = φ.vsubst (Function.update ρ x w) := by
        rw [vsubst_update_id_eq_subst, vsubst_subst_var hno_cap]
      rw [hv_eq, hv₀_eq, henkin_truth_vsubst h₀ φ hsafe_φ, henkin_truth_vsubst h₀ ψ hsafe_ψ,
        heq_form]
    have hind := henkin_holds_of_provable h₀ (.pa_ind x ψ)
    simp only [PAFormula.HoldsIn] at hind
    have hbase_ψ : PAFormula.HoldsIn v₀ (ψ.subst x .zero) := by
      rw [holdsIn_subst v₀ (freeFor_zero x ψ)]
      exact (hiff PAStructure.zero).mp hbase
    have hstep_ψ : ∀ b : HenkinCarrier h₀,
        PAFormula.HoldsIn (Function.update v₀ x b) ψ →
          PAFormula.HoldsIn (Function.update v₀ x b) (ψ.subst x (.succ (.var x))) := by
      intro b hb
      rw [holdsIn_subst (Function.update v₀ x b) (freeFor_succ_self x ψ)]
      simp only [PATerm.evalIn, Function.update_self, Function.update_idem]
      exact (hiff (PAStructure.succ b)).mp (hstep b ((hiff b).mpr hb))
    exact (hiff a).mpr (hind hbase_ψ hstep_ψ a)

end HenkinModel

/-- Gödel–Henkin soundness and completeness for first-order Peano Arithmetic (`PAProvable`):
a `PAFormula` is provable in `PAProvable` if and only if it holds in every first-order `PAModel`
`M` (`Type`) under every variable assignment. -/
theorem paProvable_iff_holdsIn_all_models (φ : PAFormula) :
    PAProvable φ ↔
      ∀ (M : Type) [PAStructure M] [PAModel M] (v : ℕ → M), PAFormula.HoldsIn v φ := by
  refine ⟨fun h M _ _ v ↦ paProvable_sound h v, fun hall ↦ ?_⟩
  by_contra hnp
  have hcons : ¬ CtxProvable [φ.not] .bot := by
    intro hbot
    exact hnp (ctx_nil_iff.mp (ctx_by_contra hbot))
  have hn_mem : φ.not ∈ henkinTheory φ.not := henkinTheory_mem_zero φ.not
  have hn_sem : PAFormula.HoldsIn (fun x ↦ Quotient.mk (HenkinSetoid hcons) (.var x)) φ.not :=
    (henkin_truth_id hcons φ.not).mpr hn_mem
  have hp_sem : PAFormula.HoldsIn (fun x ↦ Quotient.mk (HenkinSetoid hcons) (.var x)) φ :=
    hall (HenkinCarrier hcons) (fun x ↦ Quotient.mk (HenkinSetoid hcons) (.var x))
  exact hn_sem hp_sem

end ConjectureMachines.Semantics.PA
