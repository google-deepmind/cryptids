/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Syntax
public import Cryptids.Semantics.PA.Adequacy
public import Cryptids.Semantics.PA.Completeness
public import Cryptids.Semantics.Riemann.Gadgets
public import Mathlib.Tactic.Ring

/-!
# Internal Arithmetic, Sequences, Exponentiation, and Execution in `PAModel`s

This module develops the internal arithmetic and computability toolkit inside an arbitrary
first-order model `[PAStructure M] [PAModel M]` of Peano Arithmetic, bridged to `PAProvable` via
Gödel–Henkin completeness (`paProvable_iff_holdsIn_all_models`):

1. **Nominal model carrier `PAM M`**:
   Equips `M` with `CommSemiring`, `LinearOrder`, truncated subtraction (`-`), Euclidean division
   (`/`, `%`), and `ℕ` initial-segment embedding without colliding with `ℕ`'s standard instances.
2. **Definable induction (`pam_ind_pred`, `pam_strong_ind_pred`)**:
   Ordinary and strong induction principles on `PAM M` for any predicate first-order definable by a
   `PAFormula` with parameters in `PAM M`.
3. **Bijective Cantor pairing (`mPair`, `mUnpair`)**:
   Injectivity, diagonal surjectivity, and `PAZFTerm.eqFormula` evaluation in `PAM M`.
4. **Gödel's $\beta$-sequences (`mBeta`, `mBeta_snoc`, `mBeta_concat`)**:
   Single-element extension and sequence concatenation inside `PAM M` via explicit polynomial
   Bézout identities and unsigned Chinese Remainder Theorem steps.
5. **Internal base-2 exponentiation (`mPow2`, `paPow2Eq`) and unary blocks (`mRep0`, `mRep1`)**:
   First-order definable $2^r$ and binary half-tape run-length helpers $0^r :: R$, $1^r :: R$.
6. **Internal Turing machine execution (`MCfg`, `mStep`, `mTracesTo`) and `ZF` step evaluation**:
   Semantic characterizations of `(paHalts tm).HoldsIn` and `paZFInconsistent.HoldsIn` in `PAM M`,
   plus standard-trace lifting (`embedCfg`, `mTracesTo_of_nSteps`).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.PA

open Turing (Dir)
open ConjectureMachines.Semantics.Riemann.Layer1 (nSteps)

/-! ## Section 1: Nominal Carrier `PAM M` and Isomorphism with `M` -/

/-- Nominal wrapper around the carrier of a first-order `PAModel M`, allowing `CommSemiring`,
`LinearOrder`, `-`, `/`, and `%` instances without creating instance diamonds on `ℕ`. -/
@[ext]
structure PAM (M : Type*) where
  /-- Underlying element of `M`. -/
  raw : M

namespace PAM

section Structure
variable {M : Type*} [PAStructure M]

instance : Zero (PAM M) := ⟨⟨PAStructure.zero⟩⟩
instance : One (PAM M) := ⟨⟨PAStructure.succ PAStructure.zero⟩⟩
instance : Add (PAM M) := ⟨fun a b ↦ ⟨PAStructure.add a.raw b.raw⟩⟩
instance : Mul (PAM M) := ⟨fun a b ↦ ⟨PAStructure.mul a.raw b.raw⟩⟩

/-- Successor operation on `PAM M`. -/
def succ (a : PAM M) : PAM M := ⟨PAStructure.succ a.raw⟩

instance : PAStructure (PAM M) where
  zero := 0
  succ := succ
  add := (· + ·)
  mul := (· * ·)

@[simp] theorem raw_zero : (0 : PAM M).raw = PAStructure.zero := rfl
@[simp] theorem raw_one : (1 : PAM M).raw = PAStructure.succ PAStructure.zero := rfl
@[simp] theorem raw_add (a b : PAM M) : (a + b).raw = PAStructure.add a.raw b.raw := rfl
@[simp] theorem raw_mul (a b : PAM M) : (a * b).raw = PAStructure.mul a.raw b.raw := rfl
@[simp] theorem raw_succ (a : PAM M) : (succ a).raw = PAStructure.succ a.raw := rfl

private theorem evalIn_raw (v : ℕ → PAM M) (t : PATerm) :
    (PATerm.evalIn v t).raw = PATerm.evalIn (fun x ↦ (v x).raw) t := by
  induction t with
  | var _ | zero => rfl
  | succ _ ih => exact congrArg PAStructure.succ ih
  | add _ _ ih₁ ih₂ => exact congrArg₂ PAStructure.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact congrArg₂ PAStructure.mul ih₁ ih₂

theorem holdsIn_iff_raw (v : ℕ → PAM M) (φ : PAFormula) :
    PAFormula.HoldsIn v φ ↔ PAFormula.HoldsIn (fun x ↦ (v x).raw) φ := by
  induction φ generalizing v with
  | bot => exact Iff.rfl
  | eq t₁ t₂ =>
    simp only [PAFormula.HoldsIn, PAM.ext_iff, evalIn_raw]
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ v) (ih₂ v)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ v) (ih₂ v)
  | imp _ _ ih₁ ih₂ => exact imp_congr (ih₁ v) (ih₂ v)
  | all x _ ih =>
    constructor
    · intro h a
      have h' := (ih (Function.update v x ⟨a⟩)).mp (h ⟨a⟩)
      refine (holdsIn_congr (fun y _ ↦ ?_)).mp h'
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx]
    · intro h a
      refine (ih (Function.update v x a)).mpr ?_
      have h' := h a.raw
      refine (holdsIn_congr (fun y _ ↦ ?_)).mp h'
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx]
  | ex x _ ih =>
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a.raw, ?_⟩
      have h' := (ih (Function.update v x a)).mp ha
      refine (holdsIn_congr (fun y _ ↦ ?_)).mp h'
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx]
    · rintro ⟨a, ha⟩
      refine ⟨⟨a⟩, (ih (Function.update v x ⟨a⟩)).mpr ?_⟩
      refine (holdsIn_congr (fun y _ ↦ ?_)).mp ha
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx]

end Structure

section Model
variable {M : Type*} [PAStructure M] [PAModel M]

instance : PAModel (PAM M) where
  zero_ne_succ a h := PAModel.zero_ne_succ a.raw (congrArg PAM.raw h)
  succ_inj h := PAM.ext (PAModel.succ_inj (congrArg PAM.raw h))
  add_zero a := PAM.ext (PAModel.add_zero a.raw)
  add_succ a b := PAM.ext (PAModel.add_succ a.raw b.raw)
  mul_zero a := PAM.ext (PAModel.mul_zero a.raw)
  mul_succ a b := PAM.ext (PAModel.mul_succ a.raw b.raw)
  ind x φ v h0 hs a := by
    let vr : ℕ → M := fun y ↦ (v y).raw
    have upd_eq : ∀ b : M,
        (fun y ↦ (Function.update v x ⟨b⟩ y).raw) = Function.update vr x b := by
      intro b
      funext y
      by_cases hyx : y = x
      · subst hyx; simp [vr]
      · simp [hyx, vr]
    have h0' : PAFormula.HoldsIn (Function.update vr x PAStructure.zero) φ := by
      have h0r := (holdsIn_iff_raw (Function.update v x 0) φ).mp h0
      change PAFormula.HoldsIn (fun y ↦ (Function.update v x ⟨PAStructure.zero⟩ y).raw) φ at h0r
      rwa [upd_eq PAStructure.zero] at h0r
    have hs' : ∀ b : M, PAFormula.HoldsIn (Function.update vr x b) φ →
        PAFormula.HoldsIn (Function.update vr x (PAStructure.succ b)) φ := by
      intro b hb
      have hb_pam : PAFormula.HoldsIn (Function.update v x ⟨b⟩) φ := by
        rw [holdsIn_iff_raw, upd_eq b]
        exact hb
      have hstep := (holdsIn_iff_raw (Function.update v x (succ ⟨b⟩)) φ).mp (hs ⟨b⟩ hb_pam)
      change PAFormula.HoldsIn (fun y ↦ (Function.update v x ⟨PAStructure.succ b⟩ y).raw) φ at hstep
      rwa [upd_eq (PAStructure.succ b)] at hstep
    have hres := PAModel.ind x φ vr h0' hs' a.raw
    rw [holdsIn_iff_raw]
    change PAFormula.HoldsIn (fun y ↦ (Function.update v x ⟨a.raw⟩ y).raw) φ
    rwa [upd_eq a.raw]

theorem succ_eq_add_one (a : PAM M) : succ a = a + 1 := by
  change PAStructure.succ a = PAStructure.add a (PAStructure.succ PAStructure.zero)
  rw [PAModel.add_succ, PAModel.add_zero]

theorem pam_add_zero (a : PAM M) : a + 0 = a := PAModel.add_zero a
private theorem pam_add_succ (a b : PAM M) : a + succ b = succ (a + b) := PAModel.add_succ a b
theorem pam_mul_zero (a : PAM M) : a * 0 = 0 := PAModel.mul_zero a
private theorem pam_mul_succ (a b : PAM M) : a * succ b = a * b + a := PAModel.mul_succ a b

/-- First-order induction on `PAM M` for any predicate equivalent to a `PAFormula`. -/
private theorem ind_pred {P : PAM M → Prop}
    (hdef : ∃ (x : ℕ) (φ : PAFormula) (v : ℕ → PAM M),
      ∀ a : PAM M, PAFormula.HoldsIn (Function.update v x a) φ ↔ P a)
    (h0 : P 0) (hs : ∀ a : PAM M, P a → P (a + 1)) :
    ∀ a : PAM M, P a := by
  rcases hdef with ⟨x, φ, v, hiff⟩
  intro a
  refine (hiff a).mp (PAModel.ind x φ v ((hiff 0).mpr h0) (fun b hb ↦ ?_) a)
  rw [show PAStructure.succ b = b + 1 from succ_eq_add_one b]
  exact (hiff (b + 1)).mpr (hs b ((hiff b).mp hb))

theorem pam_zero_add (a : PAM M) : 0 + a = a := by
  refine ind_pred (P := fun b : PAM M ↦ 0 + b = b)
    ⟨0, .eq (.add .zero (.var 0)) (.var 0), fun _ ↦ 0, fun b ↦ ?_⟩
    (pam_add_zero 0) (fun b ih ↦ ?_) a
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [← succ_eq_add_one, pam_add_succ, ih]

private theorem pam_succ_add (a b : PAM M) : succ a + b = succ (a + b) := by
  refine ind_pred (P := fun c : PAM M ↦ succ a + c = succ (a + c))
    ⟨0, .eq (.add (.succ (.var 1)) (.var 0)) (.succ (.add (.var 1) (.var 0))),
      fun | 1 => a | _ => 0, fun c ↦ ?_⟩ ?_ (fun c ih ↦ ?_) b
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_add_zero, pam_add_zero]
  · rw [← succ_eq_add_one, pam_add_succ, pam_add_succ, ih]

theorem pam_add_comm (a b : PAM M) : a + b = b + a := by
  refine ind_pred (P := fun c : PAM M ↦ a + c = c + a)
    ⟨0, .eq (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1)),
      fun | 1 => a | _ => 0, fun c ↦ ?_⟩ ?_ (fun c ih ↦ ?_) b
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_add_zero, pam_zero_add]
  · rw [← succ_eq_add_one, pam_add_succ, pam_succ_add, ih]

theorem pam_add_assoc (a b c : PAM M) : a + b + c = a + (b + c) := by
  refine ind_pred (P := fun d : PAM M ↦ a + b + d = a + (b + d))
    ⟨0, .eq (.add (.add (.var 1) (.var 2)) (.var 0)) (.add (.var 1) (.add (.var 2) (.var 0))),
      fun | 1 => a | 2 => b | _ => 0, fun d ↦ ?_⟩ ?_ (fun d ih ↦ ?_) c
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_add_zero, pam_add_zero]
  · rw [← succ_eq_add_one, pam_add_succ, pam_add_succ, pam_add_succ, ih]

theorem pam_zero_mul (a : PAM M) : 0 * a = 0 := by
  refine ind_pred (P := fun b : PAM M ↦ 0 * b = 0)
    ⟨0, .eq (.mul .zero (.var 0)) .zero, fun _ ↦ 0, fun b ↦ ?_⟩
    (pam_mul_zero 0) (fun b ih ↦ ?_) a
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [← succ_eq_add_one, pam_mul_succ, ih, pam_add_zero]

private theorem pam_succ_mul (a b : PAM M) : succ a * b = a * b + b := by
  refine ind_pred (P := fun c : PAM M ↦ succ a * c = a * c + c)
    ⟨0, .eq (.mul (.succ (.var 1)) (.var 0)) (.add (.mul (.var 1) (.var 0)) (.var 0)),
      fun | 1 => a | _ => 0, fun c ↦ ?_⟩ ?_ (fun c ih ↦ ?_) b
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_mul_zero, pam_mul_zero, pam_add_zero]
  · rw [← succ_eq_add_one, pam_mul_succ, pam_mul_succ, ih, succ_eq_add_one a, succ_eq_add_one c]
    calc a * c + c + (a + 1)
      _ = a * c + (c + (a + 1)) := pam_add_assoc _ _ _
      _ = a * c + (a + (c + 1)) := by
          rw [← pam_add_assoc c a 1, pam_add_comm c a, pam_add_assoc a c 1]
      _ = a * c + a + (c + 1) := (pam_add_assoc _ _ _).symm

theorem pam_mul_comm (a b : PAM M) : a * b = b * a := by
  refine ind_pred (P := fun c : PAM M ↦ a * c = c * a)
    ⟨0, .eq (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)),
      fun | 1 => a | _ => 0, fun c ↦ ?_⟩ ?_ (fun c ih ↦ ?_) b
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_mul_zero, pam_zero_mul]
  · rw [← succ_eq_add_one, pam_mul_succ, pam_succ_mul, ih]

theorem pam_left_distrib (a b c : PAM M) : a * (b + c) = a * b + a * c := by
  refine ind_pred (P := fun d : PAM M ↦ a * (b + d) = a * b + a * d)
    ⟨0, .eq (.mul (.var 1) (.add (.var 2) (.var 0)))
      (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 0))),
      fun | 1 => a | 2 => b | _ => 0, fun d ↦ ?_⟩ ?_ (fun d ih ↦ ?_) c
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_add_zero, pam_mul_zero, pam_add_zero]
  · rw [← succ_eq_add_one, pam_add_succ, pam_mul_succ, pam_mul_succ, ih, pam_add_assoc]

theorem pam_right_distrib (a b c : PAM M) : (a + b) * c = a * c + b * c := by
  rw [pam_mul_comm, pam_left_distrib, pam_mul_comm c a, pam_mul_comm c b]

theorem pam_mul_assoc (a b c : PAM M) : a * b * c = a * (b * c) := by
  refine ind_pred (P := fun d : PAM M ↦ a * b * d = a * (b * d))
    ⟨0, .eq (.mul (.mul (.var 1) (.var 2)) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 0))),
      fun | 1 => a | 2 => b | _ => 0, fun d ↦ ?_⟩ ?_ (fun d ih ↦ ?_) c
  · simp [PAFormula.HoldsIn, PATerm.evalIn]; rfl
  · rw [pam_mul_zero, pam_mul_zero, pam_mul_zero]
  · rw [← succ_eq_add_one, pam_mul_succ, pam_mul_succ, pam_left_distrib, ih]

theorem pam_mul_one (a : PAM M) : a * 1 = a := by
  change a * succ 0 = a
  rw [pam_mul_succ, pam_mul_zero, pam_zero_add]

theorem pam_one_mul (a : PAM M) : 1 * a = a := by
  rw [pam_mul_comm, pam_mul_one]

/-- Standard natural cast into `PAM M`. -/
def ofNat (n : ℕ) : PAM M :=
  match n with
  | 0 => 0
  | n + 1 => ofNat n + 1

instance : CommSemiring (PAM M) where
  add := (· + ·)
  add_assoc := pam_add_assoc
  zero := 0
  zero_add := pam_zero_add
  add_zero := pam_add_zero
  nsmul := nsmulRec
  add_comm := pam_add_comm
  mul := (· * ·)
  left_distrib := pam_left_distrib
  right_distrib := pam_right_distrib
  zero_mul := pam_zero_mul
  mul_zero := pam_mul_zero
  mul_assoc := pam_mul_assoc
  one := 1
  one_mul := pam_one_mul
  mul_one := pam_mul_one
  natCast := ofNat
  natCast_zero := rfl
  natCast_succ _ := rfl
  npow := npowRec
  mul_comm := pam_mul_comm

omit [PAModel M] in
@[simp]
theorem evalIn_zero (v : ℕ → PAM M) : PATerm.evalIn v .zero = 0 := rfl

omit [PAModel M] in
@[simp]
theorem evalIn_var (v : ℕ → PAM M) (x : ℕ) : PATerm.evalIn v (.var x) = v x := rfl

@[simp]
theorem evalIn_succ (v : ℕ → PAM M) (t : PATerm) :
    PATerm.evalIn v (.succ t) = PATerm.evalIn v t + 1 :=
  succ_eq_add_one (PATerm.evalIn v t)

omit [PAModel M] in
@[simp]
theorem evalIn_add (v : ℕ → PAM M) (t₁ t₂ : PATerm) :
    PATerm.evalIn v (.add t₁ t₂) = PATerm.evalIn v t₁ + PATerm.evalIn v t₂ := rfl

omit [PAModel M] in
@[simp]
theorem evalIn_mul (v : ℕ → PAM M) (t₁ t₂ : PATerm) :
    PATerm.evalIn v (.mul t₁ t₂) = PATerm.evalIn v t₁ * PATerm.evalIn v t₂ := rfl

@[simp]
theorem evalIn_ofNat (v : ℕ → PAM M) (n : ℕ) :
    PATerm.evalIn v (.ofNat n) = (n : PAM M) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [PATerm.ofNat, ih]

/-- Every element of `PAM M` is either `0` or a successor `b + 1`. -/
theorem eq_zero_or_exists_succ (a : PAM M) : a = 0 ∨ ∃ b : PAM M, a = b + 1 := by
  refine ind_pred (P := fun c : PAM M ↦ c = 0 ∨ ∃ b : PAM M, c = b + 1)
    ⟨0, .or (.eq (.var 0) .zero) (.ex 1 (.eq (.var 0) (.succ (.var 1)))),
      fun _ ↦ 0, fun c ↦ ?_⟩ (Or.inl rfl) (fun c _ ↦ Or.inr ⟨c, rfl⟩) a
  simp [PAFormula.HoldsIn]

theorem add_one_ne_zero (a : PAM M) : a + 1 ≠ 0 := by
  rw [← succ_eq_add_one]
  exact PAModel.zero_ne_succ a

theorem add_right_inj_pam {a b : PAM M} (c : PAM M) : a + c = b + c ↔ a = b := by
  refine ⟨?_, fun h ↦ h ▸ rfl⟩
  refine ind_pred (P := fun d ↦ a + d = b + d → a = b)
    ⟨0, .imp (.eq (.add (.var 1) (.var 0)) (.add (.var 2) (.var 0)))
      (.eq (.var 1) (.var 2)), fun | 1 => a | 2 => b | _ => 0, fun d ↦ ?_⟩
    (fun h ↦ by simpa using h) (fun d ih h ↦ ?_) c
  · simp [PAFormula.HoldsIn]
  · have h' : succ (a + d) = succ (b + d) := by
      rw [succ_eq_add_one, succ_eq_add_one, add_assoc, add_assoc]
      exact h
    exact ih (PAModel.succ_inj h')

theorem add_left_inj_pam {a b : PAM M} (c : PAM M) : c + a = c + b ↔ a = b := by
  rw [add_comm c a, add_comm c b]
  exact add_right_inj_pam c

theorem add_eq_zero_iff_pam {a b : PAM M} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ ↦ by rw [ha, hb, add_zero]⟩
  rcases eq_zero_or_exists_succ b with rfl | ⟨b', rfl⟩
  · rw [add_zero] at h
    exact ⟨h, rfl⟩
  · rw [← add_assoc] at h
    exact absurd h (add_one_ne_zero (a + b'))

theorem mul_eq_zero_iff_pam {a b : PAM M} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (fun ha ↦ by rw [ha, zero_mul])
    (fun hb ↦ by rw [hb, mul_zero])⟩
  rcases eq_zero_or_exists_succ a with rfl | ⟨a', rfl⟩
  · exact Or.inl rfl
  · rcases eq_zero_or_exists_succ b with rfl | ⟨b', rfl⟩
    · exact Or.inr rfl
    · have hexp : (a' + 1) * (b' + 1) = (a' * b' + a' + b') + 1 := by ring
      rw [hexp] at h
      exact absurd h (add_one_ne_zero _)

/-! ## Section 2: Total Linear Order, Truncated Subtraction, and `ℕ` Embedding -/

instance : LE (PAM M) := ⟨fun a b ↦ ∃ k : PAM M, a + k = b⟩
instance : LT (PAM M) := ⟨fun a b ↦ a + 1 ≤ b⟩

omit [PAModel M] in
theorem le_def {a b : PAM M} : a ≤ b ↔ ∃ k : PAM M, a + k = b := Iff.rfl

omit [PAModel M] in
theorem lt_def {a b : PAM M} : a < b ↔ a + 1 ≤ b := Iff.rfl

omit [PAModel M] in
private theorem evalIn_update_of_freshVar_le (v : ℕ → PAM M) {t : PATerm} {x : ℕ} (a : PAM M)
    (h : t.freshVar ≤ x) : PATerm.evalIn (Function.update v x a) t = PATerm.evalIn v t :=
  evalIn_update_of_hasVar_false v a (hasVar_false_of_freshVar_le h)

omit [PAModel M] in
private theorem paLe_holdsIn_iff (v : ℕ → PAM M) (a b : PATerm) :
    PAFormula.HoldsIn v (paLe a b) ↔ PATerm.evalIn v a ≤ PATerm.evalIn v b := by
  unfold paLe
  set k := max a.freshVar b.freshVar
  have ha : a.freshVar ≤ k := Nat.le_max_left _ _
  have hb : b.freshVar ≤ k := Nat.le_max_right _ _
  simp only [PAFormula.HoldsIn, evalIn_add, evalIn_var,
    evalIn_update_of_freshVar_le v _ ha, evalIn_update_of_freshVar_le v _ hb,
    Function.update_self]
  rfl

private theorem paLt_holdsIn_iff (v : ℕ → PAM M) (a b : PATerm) :
    PAFormula.HoldsIn v (paLt a b) ↔ PATerm.evalIn v a < PATerm.evalIn v b := by
  unfold paLt
  rw [paLe_holdsIn_iff, evalIn_succ]
  rfl

theorem pam_le_refl (a : PAM M) : a ≤ a := ⟨0, add_zero a⟩

theorem pam_le_trans {a b c : PAM M} : a ≤ b → b ≤ c → a ≤ c := by
  rintro ⟨k₁, rfl⟩ ⟨k₂, rfl⟩
  exact ⟨k₁ + k₂, (add_assoc a k₁ k₂).symm⟩

theorem pam_le_antisymm {a b : PAM M} : a ≤ b → b ≤ a → a = b := by
  rintro ⟨k₁, rfl⟩ ⟨k₂, h⟩
  have hk : a + (k₁ + k₂) = a + 0 := by rw [← add_assoc, h, add_zero]
  have h0 : k₁ + k₂ = 0 := (add_left_inj_pam a).mp hk
  rw [(add_eq_zero_iff_pam.mp h0).1, add_zero]

theorem zero_le_pam (a : PAM M) : 0 ≤ a := ⟨a, zero_add a⟩

theorem pam_le_total (a b : PAM M) : a ≤ b ∨ b ≤ a := by
  refine ind_pred (P := fun c : PAM M ↦ a ≤ c ∨ c ≤ a)
    ⟨0, .or (paLe (.var 1) (.var 0)) (paLe (.var 0) (.var 1)),
      fun | 1 => a | _ => 0, fun c ↦ ?_⟩ (Or.inr (zero_le_pam a)) (fun c ih ↦ ?_) b
  · simp [PAFormula.HoldsIn, paLe_holdsIn_iff]
  · rcases ih with ⟨k, rfl⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k + 1, by ring⟩
    · rcases eq_zero_or_exists_succ k with rfl | ⟨k', rfl⟩
      · rw [add_zero] at hk
        subst hk
        exact Or.inl ⟨1, rfl⟩
      · exact Or.inr ⟨k', by rw [← hk]; ring⟩

theorem pam_lt_iff_le_not_ge (a b : PAM M) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨1 + k, by ring⟩, ?_⟩
    rintro ⟨m, hm⟩
    have h0 : a + ((k + m) + 1) = a + 0 := by
      calc a + ((k + m) + 1)
        _ = a + 1 + k + m := by ring
        _ = a := hm
        _ = a + 0 := (add_zero a).symm
    exact add_one_ne_zero (k + m) ((add_left_inj_pam a).mp h0)
  · rintro ⟨⟨k, rfl⟩, hnot⟩
    rcases eq_zero_or_exists_succ k with rfl | ⟨k', rfl⟩
    · rw [add_zero] at hnot
      exact absurd (pam_le_refl a) hnot
    · exact ⟨k', by ring⟩

noncomputable instance : LinearOrder (PAM M) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := pam_le_refl
  le_trans := @pam_le_trans M _ _
  lt_iff_le_not_ge := pam_lt_iff_le_not_ge
  le_antisymm := @pam_le_antisymm M _ _
  le_total := pam_le_total
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _
  toDecidableLT := Classical.decRel _

@[simp]
theorem not_lt_zero_pam (a : PAM M) : ¬ a < 0 :=
  not_lt_of_ge (zero_le_pam a)

theorem le_zero_iff_pam {a : PAM M} : a ≤ 0 ↔ a = 0 :=
  ⟨fun h ↦ le_antisymm h (zero_le_pam a), fun h ↦ h ▸ le_rfl⟩

private theorem pos_iff_ne_zero_pam {a : PAM M} : 0 < a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    exact lt_irrefl 0 h
  · intro h
    rcases eq_zero_or_exists_succ a with rfl | ⟨b, rfl⟩
    · exact absurd rfl h
    · exact ⟨b, by ring⟩

@[simp]
theorem lt_succ_self_pam (a : PAM M) : a < a + 1 :=
  ⟨0, add_zero (a + 1)⟩

theorem lt_add_one_iff_le {a b : PAM M} : a < b + 1 ↔ a ≤ b := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (add_right_inj_pam 1).mp (by rw [← hk]; ring)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

private theorem le_add_one_iff {a b : PAM M} : a ≤ b + 1 ↔ a ≤ b ∨ a = b + 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases eq_zero_or_exists_succ k with rfl | ⟨k', rfl⟩
    · rw [add_zero] at hk
      exact Or.inr hk
    · exact Or.inl ⟨k', (add_right_inj_pam 1).mp (by rw [← hk]; ring)⟩
  · rintro (⟨k, rfl⟩ | rfl)
    · exact ⟨k + 1, by ring⟩
    · exact le_rfl

theorem add_le_add_pam {a b c d : PAM M} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rcases h₁ with ⟨k₁, rfl⟩
  rcases h₂ with ⟨k₂, rfl⟩
  exact ⟨k₁ + k₂, by ring⟩

theorem add_lt_add_left_pam {a b : PAM M} (h : a < b) (c : PAM M) : c + a < c + b := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k, by ring⟩

theorem add_lt_add_right_pam {a b : PAM M} (h : a < b) (c : PAM M) : a + c < b + c := by
  rw [add_comm a c, add_comm b c]
  exact add_lt_add_left_pam h c

omit [PAModel M] in
theorem le_add_right_pam (a b : PAM M) : a ≤ a + b := ⟨b, rfl⟩
private theorem le_add_left_pam (a b : PAM M) : a ≤ b + a := ⟨b, add_comm a b⟩

private theorem mul_le_mul_pam {a b c d : PAM M} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := by
  rcases h₁ with ⟨k₁, rfl⟩
  rcases h₂ with ⟨k₂, rfl⟩
  exact ⟨a * k₂ + k₁ * c + k₁ * k₂, by ring⟩

private theorem mul_lt_mul_of_pos_left_pam {a b c : PAM M} (h : a < b) (hc : 0 < c) :
    c * a < c * b := by
  rcases h with ⟨k, rfl⟩
  rcases eq_zero_or_exists_succ c with rfl | ⟨c', rfl⟩
  · exact absurd rfl (ne_of_gt hc)
  · exact ⟨c' + (c' + 1) * k, by ring⟩

theorem mul_left_cancel_pam {a b c : PAM M} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  have hc_pos : 0 < c := pos_iff_ne_zero_pam.mpr hc
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact absurd h (ne_of_lt (mul_lt_mul_of_pos_left_pam hlt hc_pos))
  · rfl
  · exact absurd h (ne_of_gt (mul_lt_mul_of_pos_left_pam hgt hc_pos))

/-- Truncated subtraction on `PAM M`: returns the unique `k` with `b + k = a` when `b ≤ a`,
and `0` otherwise. -/
noncomputable instance : Sub (PAM M) :=
  ⟨fun a b ↦ if h : b ≤ a then Classical.choose h else 0⟩

theorem add_sub_of_le_pam {a b : PAM M} (h : b ≤ a) : b + (a - b) = a := by
  change b + (if h' : b ≤ a then Classical.choose h' else 0) = a
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

private theorem sub_add_cancel_pam {a b : PAM M} (h : b ≤ a) : a - b + b = a := by
  rw [add_comm]
  exact add_sub_of_le_pam h

theorem sub_eq_iff_eq_add_pam {a b c : PAM M} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  constructor
  · rintro rfl
    exact (add_sub_of_le_pam h).symm
  · intro heq
    exact (add_left_inj_pam b).mp (by rw [add_sub_of_le_pam h, heq])

@[simp]
theorem add_sub_cancel_right_pam (a b : PAM M) : a + b - b = a := by
  rw [sub_eq_iff_eq_add_pam (le_add_left_pam b a), add_comm]

@[simp]
theorem add_sub_cancel_left_pam (a b : PAM M) : a + b - a = b :=
  (sub_eq_iff_eq_add_pam (le_add_right_pam a b)).mpr rfl

theorem sub_eq_zero_of_le_pam {a b : PAM M} (h : a ≤ b) : a - b = 0 := by
  by_cases hba : b ≤ a
  · have hab : a = b := le_antisymm h hba
    subst hab
    exact (sub_eq_iff_eq_add_pam le_rfl).mpr (add_zero a).symm
  · change (if h' : b ≤ a then Classical.choose h' else 0) = 0
    exact dite_eq_right_of_eq_false (eq_false hba)

@[simp]
theorem sub_self_pam (a : PAM M) : a - a = 0 :=
  sub_eq_zero_of_le_pam le_rfl

/-- Initial-segment property: any element of `PAM M` strictly below a standard numeral `(n : PAM M)`
is itself a standard numeral `(k : PAM M)` with `k < n`. -/
theorem lt_natCast_iff {a : PAM M} {n : ℕ} :
    a < (n : PAM M) ↔ ∃ k : ℕ, k < n ∧ a = (k : PAM M) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, not_lt_zero_pam, Nat.not_lt_zero, false_and, exists_false]
  | succ n ih =>
    rw [Nat.cast_succ, lt_add_one_iff_le, le_iff_lt_or_eq, ih]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact Or.inl ⟨k, hlt, rfl⟩
      · exact Or.inr rfl

theorem le_natCast_iff {a : PAM M} {n : ℕ} :
    a ≤ (n : PAM M) ↔ ∃ k : ℕ, k ≤ n ∧ a = (k : PAM M) := by
  rw [← lt_add_one_iff_le, ← Nat.cast_succ, lt_natCast_iff]
  exact exists_congr fun k ↦ and_congr Nat.lt_succ_iff Iff.rfl

@[simp]
theorem natCast_lt_iff {m n : ℕ} : (m : PAM M) < (n : PAM M) ↔ m < n := by
  constructor
  · intro h
    obtain ⟨k, hk, heq⟩ := lt_natCast_iff.mp h
    by_contra hge
    have hle : (n : PAM M) ≤ (m : PAM M) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hge)
      rw [Nat.cast_add]
      exact le_add_right_pam _ _
    exact not_lt_of_ge hle h
  · intro h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
    exact ⟨(d : PAM M), by ring⟩

@[simp]
theorem natCast_le_iff {m n : ℕ} : (m : PAM M) ≤ (n : PAM M) ↔ m ≤ n := by
  rw [← not_lt, ← Nat.not_lt, natCast_lt_iff]

@[simp]
theorem natCast_inj_pam {m n : ℕ} : (m : PAM M) = (n : PAM M) ↔ m = n := by
  constructor
  · intro h
    exact Nat.le_antisymm (natCast_le_iff.mp (le_of_eq h)) (natCast_le_iff.mp (le_of_eq h.symm))
  · rintro rfl; rfl

theorem zero_lt_one_pam : (0 : PAM M) < 1 := by
  simpa using (natCast_lt_iff (M := M) (m := 0) (n := 1)).mpr (by decide)

private theorem zero_lt_two_pam : (0 : PAM M) < 2 := by
  simpa using (natCast_lt_iff (M := M) (m := 0) (n := 2)).mpr (by decide)

theorem one_ne_zero_pam : (1 : PAM M) ≠ 0 :=
  ne_of_gt zero_lt_one_pam

theorem two_ne_zero_pam : (2 : PAM M) ≠ 0 :=
  ne_of_gt zero_lt_two_pam

omit [PAStructure M] [PAModel M] in
private theorem hasFree_false_of_maxVar_le_pam {φ : PAFormula} {w : ℕ} (h : φ.maxVar ≤ w) :
    φ.hasFree w = false := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp [PAFormula.hasFree, hasVar_false_of_freshVar_le h.1, hasVar_false_of_freshVar_le h.2]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp [PAFormula.hasFree, ih₁ h.1, ih₂ h.2]
  | all _ _ ih | ex _ _ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp [PAFormula.hasFree, ih h.2]

omit [PAStructure M] [PAModel M] in
private theorem freeFor_var_of_maxVar_le_pam {φ : PAFormula} {x w : ℕ} (h : φ.maxVar ≤ w) :
    φ.freeFor x (.var w) = true := by
  induction φ with
  | bot | eq _ _ => rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    simp [PAFormula.freeFor, ih₁ h.1, ih₂ h.2]
  | all z _ ih | ex z _ ih =>
    simp only [PAFormula.maxVar, Nat.max_le] at h
    have hwz : w ≠ z := by omega
    simp [PAFormula.freeFor, PATerm.hasVar, hwz, ih h.2]

/-- Strong first-order induction on `PAM M` for any predicate equivalent to a `PAFormula`. -/
private theorem strong_ind_pred {P : PAM M → Prop}
    (hdef : ∃ (x : ℕ) (φ : PAFormula) (v : ℕ → PAM M),
      ∀ a : PAM M, PAFormula.HoldsIn (Function.update v x a) φ ↔ P a)
    (hstep : ∀ a : PAM M, (∀ b < a, P b) → P a) :
    ∀ a : PAM M, P a := by
  rcases hdef with ⟨x, φ, v, hiff⟩
  let y := max (x + 1) φ.maxVar
  have hyx : y ≠ x := by omega
  have hmax : φ.maxVar ≤ y := Nat.le_max_right _ _
  have hf_xy : φ.freeFor x (.var y) = true := freeFor_var_of_maxVar_le_pam hmax
  have hno_y : φ.hasFree y = false := hasFree_false_of_maxVar_le_pam hmax
  let ψ : PAFormula := .all y (.imp (paLe (.var y) (.var x)) (φ.subst x (.var y)))
  have hψ : ∀ n : PAM M,
      PAFormula.HoldsIn (Function.update v x n) ψ ↔ ∀ b ≤ n, P b := by
    intro n
    simp only [ψ, PAFormula.HoldsIn]
    refine forall_congr' fun b ↦ ?_
    set u := Function.update (Function.update v x n) y b
    have hu_y : u y = b := by simp [u]
    have hu_x : u x = n := by simp [u, hyx.symm]
    have hsub := holdsIn_subst u hf_xy
    have heq_u : Function.update u x (PATerm.evalIn u (.var y)) =
        Function.update (Function.update v y b) x b := by
      funext z
      by_cases hzx : z = x
      · subst hzx; simp [u]
      · by_cases hzy : z = y
        · subst hzy; simp [u, hzx]
        · simp [u, hzx, hzy]
    have hy_drop : PAFormula.HoldsIn (Function.update (Function.update v y b) x b) φ ↔
        PAFormula.HoldsIn (Function.update v x b) φ := by
      rw [Function.update_comm hyx]
      exact holdsIn_update_of_hasFree_false _ b hno_y
    rw [paLe_holdsIn_iff, evalIn_var, evalIn_var, hu_y, hu_x, hsub, heq_u, hy_drop, hiff b]
  have hall : ∀ n : PAM M, ∀ b ≤ n, P b := by
    refine ind_pred (P := fun n ↦ ∀ b ≤ n, P b) ⟨x, ψ, v, hψ⟩ ?_ ?_
    · intro b hb
      rw [le_zero_iff_pam.mp hb]
      exact hstep 0 fun c hc ↦ absurd hc (not_lt_zero_pam c)
    · intro n ih b hb
      rcases le_iff_lt_or_eq.mp hb with hlt | rfl
      · exact ih b (lt_add_one_iff_le.mp hlt)
      · exact hstep (n + 1) fun c hc ↦ ih c (lt_add_one_iff_le.mp hc)
  exact fun a ↦ hall a a le_rfl

/-! ## Section 3: Euclidean Division, Parity, and Binary Half-Tapes -/

theorem div_mod_exists {b : PAM M} (hb : 0 < b) (a : PAM M) :
    ∃ q r : PAM M, a = b * q + r ∧ r < b := by
  refine ind_pred (P := fun c ↦ ∃ q r : PAM M, c = b * q + r ∧ r < b)
    ⟨0, .ex 2 (.ex 3 (.and (.eq (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
      (paLt (.var 3) (.var 1)))),
      fun | 1 => b | _ => 0, fun c ↦ ?_⟩ ⟨0, 0, by simp, hb⟩ (fun c ih ↦ ?_) a
  · simp [PAFormula.HoldsIn, paLt_holdsIn_iff]
  · rcases ih with ⟨q, r, rfl, hr⟩
    by_cases hrb : r + 1 = b
    · exact ⟨q + 1, 0, by rw [← hrb]; ring, hb⟩
    · refine ⟨q, r + 1, by ring, ?_⟩
      exact lt_of_le_of_ne hr hrb

private theorem div_mod_unique {b q₁ r₁ q₂ r₂ : PAM M} (hr₁ : r₁ < b) (hr₂ : r₂ < b)
    (h : b * q₁ + r₁ = b * q₂ + r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  have hq : q₁ = q₂ := by
    rcases lt_trichotomy q₁ q₂ with hlt | rfl | hgt
    · rcases hlt with ⟨k, rfl⟩
      rcases hr₁ with ⟨m, hm⟩
      have hbad : b * q₁ + r₁ + (m + 1 + b * k + r₂) = b * q₁ + r₁ + 0 := by
        calc b * q₁ + r₁ + (m + 1 + b * k + r₂)
          _ = b * q₁ + (r₁ + 1 + m) + b * k + r₂ := by ring
          _ = b * q₁ + b + b * k + r₂ := by rw [hm]
          _ = b * (q₁ + 1 + k) + r₂ := by ring
          _ = b * q₁ + r₁ := h.symm
          _ = b * q₁ + r₁ + 0 := (add_zero _).symm
      have h0 : m + b * k + r₂ + 1 = 0 := by
        have := (add_left_inj_pam (b * q₁ + r₁)).mp hbad
        rw [show m + b * k + r₂ + 1 = m + 1 + b * k + r₂ by ring]
        exact this
      exact absurd h0 (add_one_ne_zero _)
    · rfl
    · rcases hgt with ⟨k, rfl⟩
      rcases hr₂ with ⟨m, hm⟩
      have hbad : b * q₂ + r₂ + (m + 1 + b * k + r₁) = b * q₂ + r₂ + 0 := by
        calc b * q₂ + r₂ + (m + 1 + b * k + r₁)
          _ = b * q₂ + (r₂ + 1 + m) + b * k + r₁ := by ring
          _ = b * q₂ + b + b * k + r₁ := by rw [hm]
          _ = b * (q₂ + 1 + k) + r₁ := by ring
          _ = b * q₂ + r₂ := h
          _ = b * q₂ + r₂ + 0 := (add_zero _).symm
      have h0 : m + b * k + r₁ + 1 = 0 := by
        have := (add_left_inj_pam (b * q₂ + r₂)).mp hbad
        rw [show m + b * k + r₁ + 1 = m + 1 + b * k + r₁ by ring]
        exact this
      exact absurd h0 (add_one_ne_zero _)
  subst hq
  exact ⟨rfl, (add_left_inj_pam (b * q₁)).mp h⟩

noncomputable instance : Div (PAM M) :=
  ⟨fun a b ↦ if hb : 0 < b then Classical.choose (div_mod_exists hb a) else 0⟩

noncomputable instance : Mod (PAM M) :=
  ⟨fun a b ↦ if hb : 0 < b then
    Classical.choose (Classical.choose_spec (div_mod_exists hb a)) else a⟩

theorem div_add_mod_pam (a b : PAM M) : b * (a / b) + a % b = a := by
  by_cases hb : 0 < b
  · have hq : a / b = Classical.choose (div_mod_exists hb a) :=
      dite_eq_left_of_eq_true (eq_true hb)
    have hr : a % b = Classical.choose (Classical.choose_spec (div_mod_exists hb a)) :=
      dite_eq_left_of_eq_true (eq_true hb)
    rw [hq, hr]
    exact (Classical.choose_spec (Classical.choose_spec (div_mod_exists hb a))).1.symm
  · have h0 : b = 0 := le_zero_iff_pam.mp (le_of_not_gt hb)
    subst h0
    have hr : a % (0 : PAM M) = a := dite_eq_right_of_eq_false (eq_false (lt_irrefl 0))
    rw [hr, zero_mul, zero_add]

theorem mod_lt_pam (a : PAM M) {b : PAM M} (hb : 0 < b) : a % b < b := by
  have hr : a % b = Classical.choose (Classical.choose_spec (div_mod_exists hb a)) :=
    dite_eq_left_of_eq_true (eq_true hb)
  rw [hr]
  exact (Classical.choose_spec (Classical.choose_spec (div_mod_exists hb a))).2

theorem div_mod_eq_iff {a b q r : PAM M} (hr : r < b) :
    a / b = q ∧ a % b = r ↔ a = b * q + r := by
  have hb : 0 < b := lt_of_le_of_lt (zero_le_pam r) hr
  constructor
  · rintro ⟨rfl, rfl⟩
    exact (div_add_mod_pam a b).symm
  · intro ha
    exact div_mod_unique (mod_lt_pam a hb) hr (by rw [div_add_mod_pam, ha])

private theorem mod_eq_of_lt_pam {a b : PAM M} (h : a < b) : a % b = a :=
  ((div_mod_eq_iff (q := 0) h).mpr (by ring)).2

theorem add_mul_mod_self_left_pam (r m q : PAM M) : (r + m * q) % m = r % m := by
  by_cases hm : 0 < m
  · have h1 := div_add_mod_pam r m
    refine ((div_mod_eq_iff (q := r / m + q) (mod_lt_pam r hm)).mpr ?_).2
    calc r + m * q
      _ = (m * (r / m) + r % m) + m * q := congrArg (· + m * q) h1.symm
      _ = m * (r / m + q) + r % m := by ring
  · have hm0 : m = 0 := le_zero_iff_pam.mp (le_of_not_gt hm)
    subst hm0
    simp

@[simp]
theorem natCast_div_mod (a b : ℕ) (hb : 0 < b) :
    ((a : PAM M) / (b : PAM M)) = ((a / b : ℕ) : PAM M) ∧
      ((a : PAM M) % (b : PAM M)) = ((a % b : ℕ) : PAM M) := by
  refine (div_mod_eq_iff (natCast_lt_iff.mpr (Nat.mod_lt a hb))).mpr ?_
  rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]

/-- Low bit (`Fin 2`) of an element of `PAM M`. -/
noncomputable def mBit (a : PAM M) : Fin 2 :=
  if a % 2 = 0 then 0 else 1

/-- Halving `a / 2` on `PAM M`. -/
noncomputable def mHalf (a : PAM M) : PAM M :=
  a / 2

/-- Binary half-tape cons `2 * x + b.val` on `PAM M`. -/
def mCons (b : Fin 2) (x : PAM M) : PAM M :=
  2 * x + (b.val : PAM M)

private theorem mod_two_eq_zero_or_one (a : PAM M) : a % 2 = 0 ∨ a % 2 = 1 := by
  have hlt : a % 2 < ((2 : ℕ) : PAM M) := by simpa using mod_lt_pam a zero_lt_two_pam
  obtain ⟨k, hk, heq⟩ := lt_natCast_iff.mp hlt
  rcases k with _ | _ | k
  · exact Or.inl (by simpa using heq)
  · exact Or.inr (by simpa using heq)
  · omega

theorem mBit_val_eq_mod (a : PAM M) : ((mBit a).val : PAM M) = a % 2 := by
  unfold mBit
  rcases mod_two_eq_zero_or_one a with h0 | h1
  · simp [h0]
  · simp [h1, one_ne_zero_pam]

@[simp]
theorem mCons_mBit_mHalf (a : PAM M) : mCons (mBit a) (mHalf a) = a := by
  unfold mCons mHalf
  rw [mBit_val_eq_mod]
  exact div_add_mod_pam a 2

@[simp]
theorem mBit_mCons (b : Fin 2) (x : PAM M) : mBit (mCons b x) = b := by
  rcases b with ⟨_ | _ | k, hk⟩
  · change mBit (mCons 0 x) = 0
    have hdm := (div_mod_eq_iff (a := mCons 0 x) (b := 2) (q := x) zero_lt_two_pam).mpr
      (by simp [mCons])
    simp [mBit, hdm.2]
  · change mBit (mCons 1 x) = 1
    have hlt : (1 : PAM M) < 2 := ⟨0, by ring⟩
    have hdm := (div_mod_eq_iff (a := mCons 1 x) (b := 2) (q := x) hlt).mpr
      (by simp [mCons])
    simp [mBit, hdm.2, one_ne_zero_pam]
  · omega

@[simp]
theorem mHalf_mCons (b : Fin 2) (x : PAM M) : mHalf (mCons b x) = x := by
  have hlt : (b.val : PAM M) < 2 := by
    simpa using (natCast_lt_iff (M := M) (m := b.val) (n := 2)).mpr b.isLt
  exact ((div_mod_eq_iff (a := mCons b x) (b := 2) (q := x) hlt).mpr rfl).1

@[simp]
theorem mBit_zero : mBit (0 : PAM M) = 0 := by
  have := mBit_mCons (M := M) 0 0
  simpa [mCons] using this

@[simp]
theorem mHalf_zero : mHalf (0 : PAM M) = 0 := by
  have := mHalf_mCons (M := M) 0 0
  simpa [mCons] using this

/-! ## Section 4: Bijective Cantor Pairing `mPair` / `mUnpair` -/

private theorem two_dvd_mul_succ_pam (s : PAM M) : ∃ k : PAM M, s * (s + 1) = 2 * k := by
  have hs := div_add_mod_pam s 2
  rcases mod_two_eq_zero_or_one s with h0 | h1
  · refine ⟨(s / 2) * (2 * (s / 2) + 1), ?_⟩
    rw [h0, add_zero] at hs
    conv_lhs => rw [← hs]
    ring
  · refine ⟨(2 * (s / 2) + 1) * (s / 2 + 1), ?_⟩
    rw [h1] at hs
    conv_lhs => rw [← hs]
    ring

/-- Cantor pairing $x + \frac{(x + y)(x + y + 1)}{2}$ on `PAM M`. -/
noncomputable def mPair (x y : PAM M) : PAM M :=
  x + ((x + y) * (x + y + 1)) / 2

theorem two_mul_mPair (x y : PAM M) :
    2 * mPair x y = 2 * x + (x + y) * (x + y + 1) := by
  obtain ⟨k, hk⟩ := two_dvd_mul_succ_pam (x + y)
  have hdiv : ((x + y) * (x + y + 1)) / 2 = k :=
    ((div_mod_eq_iff (r := 0) zero_lt_two_pam).mpr (by rw [hk, add_zero])).1
  unfold mPair
  rw [hdiv, hk]
  ring

@[simp]
theorem mPair_zero_zero : mPair (0 : PAM M) 0 = 0 := by
  apply mul_left_cancel_pam two_ne_zero_pam
  rw [two_mul_mPair]
  ring

@[simp]
theorem mPair_natCast (x y : ℕ) : mPair (x : PAM M) (y : PAM M) = (cantorPair x y : PAM M) := by
  apply mul_left_cancel_pam two_ne_zero_pam
  rw [two_mul_mPair]
  have hnat : 2 * cantorPair x y = 2 * x + (x + y) * (x + y + 1) := by
    unfold cantorPair
    set s := x + y
    have hs := (Nat.div_add_mod s 2).symm
    rcases Nat.mod_two_eq_zero_or_one s with h0 | h1
    · have hev : s * (s + 1) = 2 * ((s / 2) * (2 * (s / 2) + 1)) := by
        conv_lhs => rw [hs, h0]
        ring
      rw [hev, Nat.mul_div_right _ (by decide : 0 < 2)]
      ring
    · have hev : s * (s + 1) = 2 * ((2 * (s / 2) + 1) * (s / 2 + 1)) := by
        conv_lhs => rw [hs, h1]
        ring
      rw [hev, Nat.mul_div_right _ (by decide : 0 < 2)]
      ring
  have hcast := congrArg (Nat.cast (R := PAM M)) hnat.symm
  simpa [Nat.cast_add, Nat.cast_mul] using hcast

private theorem paCantorPairEq_holdsIn_iff (v : ℕ → PAM M) (x y z : PATerm) :
    PAFormula.HoldsIn v (paCantorPairEq x y z) ↔
      PATerm.evalIn v z = mPair (PATerm.evalIn v x) (PATerm.evalIn v y) := by
  unfold paCantorPairEq
  simp only [PAFormula.HoldsIn, evalIn_mul, evalIn_add, evalIn_succ, evalIn_ofNat, Nat.cast_ofNat]
  rw [← two_mul_mPair]
  exact ⟨mul_left_cancel_pam two_ne_zero_pam, fun h ↦ h ▸ rfl⟩

theorem mPair_injective {x₁ y₁ x₂ y₂ : PAM M} (h : mPair x₁ y₁ = mPair x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have h2 : 2 * x₁ + (x₁ + y₁) * (x₁ + y₁ + 1) = 2 * x₂ + (x₂ + y₂) * (x₂ + y₂ + 1) := by
    rw [← two_mul_mPair, ← two_mul_mPair, h]
  have hnotlt : ∀ {a₁ b₁ a₂ b₂ : PAM M},
      2 * a₁ + (a₁ + b₁) * (a₁ + b₁ + 1) = 2 * a₂ + (a₂ + b₂) * (a₂ + b₂ + 1) →
      ¬ (a₁ + b₁ < a₂ + b₂) := by
    intro a₁ b₁ a₂ b₂ heq hlt
    rcases hlt with ⟨d, hd⟩
    have hexp : 2 * a₂ + (a₂ + b₂) * (a₂ + b₂ + 1) =
        (2 * a₁ + (a₁ + b₁) * (a₁ + b₁ + 1)) +
          ((2 * a₂ + 2 * b₁ + (2 * (a₁ + b₁) + 3 + d) * d + 1) + 1) := by
      rw [← hd]
      ring
    rw [heq] at hexp
    have h0 : (2 * a₂ + 2 * b₁ + (2 * (a₁ + b₁) + 3 + d) * d + 1) + 1 = 0 :=
      (add_left_inj_pam (2 * a₂ + (a₂ + b₂) * (a₂ + b₂ + 1))).mp
        (by rw [← hexp, add_zero])
    exact add_one_ne_zero _ h0
  have hs : x₁ + y₁ = x₂ + y₂ :=
    le_antisymm (le_of_not_gt (hnotlt h2.symm)) (le_of_not_gt (hnotlt h2))
  rw [hs] at h2
  have hx2 : 2 * x₁ = 2 * x₂ := (add_right_inj_pam _).mp h2
  have hx : x₁ = x₂ := mul_left_cancel_pam two_ne_zero_pam hx2
  subst hx
  exact ⟨rfl, (add_left_inj_pam x₁).mp hs⟩

theorem mPair_surjective (z : PAM M) : ∃ x y : PAM M, mPair x y = z := by
  refine ind_pred (P := fun w ↦ ∃ x y : PAM M, mPair x y = w)
    ⟨0, .ex 1 (.ex 2 (paCantorPairEq (.var 1) (.var 2) (.var 0))),
      fun _ ↦ 0, fun w ↦ ?_⟩ ⟨0, 0, mPair_zero_zero⟩ (fun w ih ↦ ?_) z
  · simp only [PAFormula.HoldsIn, paCantorPairEq_holdsIn_iff, evalIn_var]
    refine exists_congr fun x ↦ exists_congr fun y ↦ ?_
    simp [eq_comm]
  · rcases ih with ⟨x, y, rfl⟩
    rcases eq_zero_or_exists_succ y with rfl | ⟨y₀, rfl⟩
    · refine ⟨0, x + 1, ?_⟩
      apply mul_left_cancel_pam two_ne_zero_pam
      rw [mul_add, two_mul_mPair, two_mul_mPair]
      ring
    · refine ⟨x + 1, y₀, ?_⟩
      apply mul_left_cancel_pam two_ne_zero_pam
      rw [mul_add, two_mul_mPair, two_mul_mPair]
      ring

/-- Inverse Cantor unpairing on `PAM M`. -/
noncomputable def mUnpair (z : PAM M) : PAM M × PAM M :=
  (Classical.choose (mPair_surjective z),
   Classical.choose (Classical.choose_spec (mPair_surjective z)))

@[simp]
theorem mPair_mUnpair (z : PAM M) : mPair (mUnpair z).1 (mUnpair z).2 = z :=
  Classical.choose_spec (Classical.choose_spec (mPair_surjective z))

@[simp]
theorem mUnpair_mPair (x y : PAM M) : mUnpair (mPair x y) = (x, y) := by
  obtain ⟨hx, hy⟩ := mPair_injective (mPair_mUnpair (mPair x y))
  exact Prod.ext hx hy

theorem le_mPair_left (x y : PAM M) : x ≤ mPair x y :=
  ⟨((x + y) * (x + y + 1)) / 2, rfl⟩

private theorem mul_le_mul_iff_of_pos_left_pam {a b c : PAM M} (hc : 0 < c) :
    c * a ≤ c * b ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ mul_le_mul_pam le_rfl h⟩
  by_contra hnot
  exact not_lt_of_ge h (mul_lt_mul_of_pos_left_pam (lt_of_not_ge hnot) hc)

theorem le_mPair_right (x y : PAM M) : y ≤ mPair x y := by
  rcases eq_zero_or_exists_succ y with rfl | ⟨y', rfl⟩
  · exact zero_le_pam _
  · refine (mul_le_mul_iff_of_pos_left_pam zero_lt_two_pam).mp ?_
    rw [two_mul_mPair]
    exact ⟨5 * x + (x + y') * (x + y') + y', by ring⟩

omit [PAModel M] in
private theorem paDisjList_holdsIn_iff (v : ℕ → PAM M) (L : List PAFormula) :
    PAFormula.HoldsIn v (paDisjList L) ↔ ∃ φ ∈ L, PAFormula.HoldsIn v φ := by
  match L with
  | [] => simp [paDisjList, PAFormula.HoldsIn]
  | [φ] => simp [paDisjList]
  | φ :: ψ :: rest =>
    simp only [paDisjList, PAFormula.HoldsIn, paDisjList_holdsIn_iff v (ψ :: rest),
      List.mem_cons, exists_eq_or_imp]

/-- Evaluate a symbolic `PAZFTerm` in `PAM M`. -/
private noncomputable def evalPAZFTerm (v : ℕ → PAM M) : PAZFTerm → PAM M
  | .var x => v x
  | .const n => (n : PAM M)
  | .pair a b => mPair (evalPAZFTerm v a) (evalPAZFTerm v b)

private theorem evalPAZFTerm_congr {v₁ v₂ : ℕ → PAM M} {e : PAZFTerm}
    (h : ∀ x < e.freshVar, v₁ x = v₂ x) :
    evalPAZFTerm v₁ e = evalPAZFTerm v₂ e := by
  induction e with
  | var x => exact h x (Nat.lt_succ_self x)
  | const _ => rfl
  | pair a b iha ihb =>
    refine congrArg₂ mPair (iha fun x hx ↦ h x ?_) (ihb fun x hx ↦ h x ?_)
    · exact lt_of_lt_of_le hx (Nat.le_max_left _ _)
    · exact lt_of_lt_of_le hx (Nat.le_max_right _ _)

private theorem evalPAZFTerm_update_fresh (v : ℕ → PAM M) {e : PAZFTerm} {x : ℕ} (a : PAM M)
    (h : e.freshVar ≤ x) : evalPAZFTerm (Function.update v x a) e = evalPAZFTerm v e :=
  evalPAZFTerm_congr fun (y : ℕ) _ ↦ Function.update_of_ne (by omega : y ≠ x) a v

private theorem eqFormula_holdsIn_iff (e : PAZFTerm) (out : PATerm) (base : ℕ) (v : ℕ → PAM M)
    (he : e.freshVar ≤ base) (hout : out.freshVar ≤ base) :
    PAFormula.HoldsIn v (e.eqFormula out base) ↔ PATerm.evalIn v out = evalPAZFTerm v e := by
  induction e generalizing out base v with
  | var x =>
    simp [PAZFTerm.eqFormula, PAFormula.HoldsIn, evalPAZFTerm]
  | const n =>
    simp [PAZFTerm.eqFormula, PAFormula.HoldsIn, evalPAZFTerm]
  | pair a b iha ihb =>
    simp only [PAZFTerm.freshVar, Nat.max_le] at he
    rcases he with ⟨ha, hb⟩
    simp only [PAZFTerm.eqFormula, PAFormula.HoldsIn]
    constructor
    · rintro ⟨va, vb, hpair, haeq, hbeq⟩
      set v' := Function.update (Function.update v base va) (base + 1) vb
      have hv_base : v' base = va := by simp [v']
      have hv_base1 : v' (base + 1) = vb := by simp [v']
      have hout_eq : PATerm.evalIn v' out = PATerm.evalIn v out := by
        dsimp only [v']
        rw [evalIn_update_of_freshVar_le _ _ (by omega),
          evalIn_update_of_freshVar_le _ _ hout]
      have hpair' : PATerm.evalIn v out = mPair va vb := by
        have hp := (paCantorPairEq_holdsIn_iff v' (.var base) (.var (base + 1)) out).mp hpair
        simpa [hv_base, hv_base1, hout_eq] using hp
      have ha' : va = evalPAZFTerm v a := by
        have h1 := (iha (.var base) (base + 2) v' (by omega)
          (by simp [PATerm.freshVar])).mp haeq
        dsimp only [v'] at h1
        rw [evalIn_var, evalPAZFTerm_update_fresh _ _ (by omega),
          evalPAZFTerm_update_fresh _ _ ha] at h1
        simpa [Function.update_of_ne (by omega : base ≠ base + 1)] using h1
      have hb' : vb = evalPAZFTerm v b := by
        have h2 := (ihb (.var (base + 1)) (base + 2 + a.numVars) v' (by omega)
          (by simp [PATerm.freshVar]; omega)).mp hbeq
        dsimp only [v'] at h2
        rw [evalIn_var, evalPAZFTerm_update_fresh _ _ (by omega),
          evalPAZFTerm_update_fresh _ _ hb] at h2
        simpa using h2
      rw [hpair', ha', hb', evalPAZFTerm]
    · intro heq
      refine ⟨evalPAZFTerm v a, evalPAZFTerm v b, ?_⟩
      set v' := Function.update (Function.update v base (evalPAZFTerm v a))
        (base + 1) (evalPAZFTerm v b)
      have hv_base : v' base = evalPAZFTerm v a := by simp [v']
      have hv_base1 : v' (base + 1) = evalPAZFTerm v b := by simp [v']
      have hout_eq : PATerm.evalIn v' out = PATerm.evalIn v out := by
        dsimp only [v']
        rw [evalIn_update_of_freshVar_le _ _ (by omega),
          evalIn_update_of_freshVar_le _ _ hout]
      refine ⟨?_, ?_, ?_⟩
      · rw [paCantorPairEq_holdsIn_iff]
        simp only [evalIn_var, hv_base, hv_base1, hout_eq]
        exact heq
      · rw [iha (.var base) (base + 2) v' (by omega) (by simp [PATerm.freshVar]),
          evalIn_var, hv_base]
        dsimp only [v']
        rw [evalPAZFTerm_update_fresh _ _ (by omega), evalPAZFTerm_update_fresh _ _ ha]
      · rw [ihb (.var (base + 1)) (base + 2 + a.numVars) v' (by omega)
          (by simp [PATerm.freshVar]; omega), evalIn_var, hv_base1]
        dsimp only [v']
        rw [evalPAZFTerm_update_fresh _ _ (by omega), evalPAZFTerm_update_fresh _ _ hb]

/-! ## Section 4b: Compositional First-Order Definability (`PADefN`, `PAFunN`) -/

private def renameAllTerm (σ : ℕ → ℕ) : PATerm → PATerm
  | .var x => .var (σ x)
  | .zero => .zero
  | .succ t => .succ (renameAllTerm σ t)
  | .add t₁ t₂ => .add (renameAllTerm σ t₁) (renameAllTerm σ t₂)
  | .mul t₁ t₂ => .mul (renameAllTerm σ t₁) (renameAllTerm σ t₂)

private def renameAllFormula (σ : ℕ → ℕ) : PAFormula → PAFormula
  | .bot => .bot
  | .eq t₁ t₂ => .eq (renameAllTerm σ t₁) (renameAllTerm σ t₂)
  | .and φ ψ => .and (renameAllFormula σ φ) (renameAllFormula σ ψ)
  | .or φ ψ => .or (renameAllFormula σ φ) (renameAllFormula σ ψ)
  | .imp φ ψ => .imp (renameAllFormula σ φ) (renameAllFormula σ ψ)
  | .all x φ => .all (σ x) (renameAllFormula σ φ)
  | .ex x φ => .ex (σ x) (renameAllFormula σ φ)

omit [PAModel M] in
private theorem evalIn_renameAllTerm (σ : ℕ → ℕ) (u : ℕ → PAM M) (t : PATerm) :
    PATerm.evalIn u (renameAllTerm σ t) = PATerm.evalIn (u ∘ σ) t := by
  induction t with
  | var _ | zero => rfl
  | succ _ ih => exact congrArg PAStructure.succ ih
  | add _ _ ih₁ ih₂ => exact congrArg₂ PAStructure.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact congrArg₂ PAStructure.mul ih₁ ih₂

omit [PAModel M] in
private theorem holdsIn_renameAllFormula {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (u : ℕ → PAM M) (φ : PAFormula) :
    PAFormula.HoldsIn u (renameAllFormula σ φ) ↔ PAFormula.HoldsIn (u ∘ σ) φ := by
  induction φ generalizing u with
  | bot => exact Iff.rfl
  | eq t₁ t₂ =>
    simp only [renameAllFormula, PAFormula.HoldsIn, evalIn_renameAllTerm]
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ u) (ih₂ u)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ u) (ih₂ u)
  | imp _ _ ih₁ ih₂ => exact imp_congr (ih₁ u) (ih₂ u)
  | all x φ ih =>
    simp only [renameAllFormula, PAFormula.HoldsIn]
    refine forall_congr' fun a ↦ (ih (Function.update u (σ x) a)).trans ?_
    have heq : Function.update u (σ x) a ∘ σ = Function.update (u ∘ σ) x a := by
      funext z
      by_cases hzx : z = x
      · subst hzx; simp
      · simp [hzx, hσ.ne hzx]
    rw [heq]
  | ex x φ ih =>
    simp only [renameAllFormula, PAFormula.HoldsIn]
    refine exists_congr fun a ↦ (ih (Function.update u (σ x) a)).trans ?_
    have heq : Function.update u (σ x) a ∘ σ = Function.update (u ∘ σ) x a := by
      funext z
      by_cases hzx : z = x
      · subst hzx; simp
      · simp [hzx, hσ.ne hzx]
    rw [heq]

/-- Environment mapping `0..k-1` to `args` and `≥ k` to parameter assignment `v`. -/
def paEnv {k : ℕ} (v : ℕ → PAM M) (args : Fin k → PAM M) (x : ℕ) : PAM M :=
  if h : x < k then args ⟨x, h⟩ else v x

omit [PAStructure M] [PAModel M] in
private theorem paEnv_lt {k : ℕ} (v : ℕ → PAM M) (args : Fin k → PAM M) {x : ℕ} (h : x < k) :
    paEnv v args x = args ⟨x, h⟩ :=
  dite_eq_left_of_eq_true (eq_true h)

omit [PAStructure M] [PAModel M] in
private theorem paEnv_ge {k : ℕ} (v : ℕ → PAM M) (args : Fin k → PAM M) {x : ℕ} (h : ¬ x < k) :
    paEnv v args x = v x :=
  dite_eq_right_of_eq_false (eq_false h)

omit [PAStructure M] [PAModel M] in
theorem fin_snoc_lt {k : ℕ} {α : Type*} (args : Fin k → α) (a : α) {x : ℕ}
    (hx : x < k + 1) (hlt : x < k) :
    (Fin.snoc args a : Fin (k + 1) → α) ⟨x, hx⟩ = args ⟨x, hlt⟩ :=
  Fin.snoc_castSucc (α := fun _ ↦ α) a args ⟨x, hlt⟩

omit [PAStructure M] [PAModel M] in
theorem fin_snoc_eq {k : ℕ} {α : Type*} (args : Fin k → α) (a : α)
    (hx : k < k + 1 := Nat.lt_succ_self k) :
    (Fin.snoc args a : Fin (k + 1) → α) ⟨k, hx⟩ = a :=
  Fin.snoc_last (α := fun _ ↦ α) a args

/-- `k`-ary first-order definability with parameters in `PAM M`. -/
def PADefN (k : ℕ) (P : (Fin k → PAM M) → Prop) : Prop :=
  ∃ (φ : PAFormula) (v : ℕ → PAM M), ∀ args : Fin k → PAM M,
    PAFormula.HoldsIn (paEnv v args) φ ↔ P args

/-- `k`-ary first-order definable function on `PAM M` (via its `(k + 1)`-ary graph). -/
def PAFunN (k : ℕ) (f : (Fin k → PAM M) → PAM M) : Prop :=
  PADefN (k + 1) fun args ↦ args (Fin.last k) = f (Fin.init args)

/-- Unary first-order definability on `PAM M`. -/
abbrev PADef1 (P : PAM M → Prop) : Prop :=
  PADefN 1 fun args ↦ P (args 0)

omit [PAModel M] in
theorem paDefN_congr {k : ℕ} {P Q : (Fin k → PAM M) → Prop}
    (h : ∀ args, P args ↔ Q args) (hP : PADefN k P) : PADefN k Q := by
  rcases hP with ⟨φ, v, hφ⟩
  exact ⟨φ, v, fun args ↦ (hφ args).trans (h args)⟩

omit [PAModel M] in
theorem paFunN_congr {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (h : ∀ args, f args = g args) (hf : PAFunN k f) : PAFunN k g :=
  paDefN_congr (fun args ↦ by rw [h (Fin.init args)]) hf

theorem ind1 {P : PAM M → Prop} (hP : PADef1 P) (h0 : P 0) (hs : ∀ a : PAM M, P a → P (a + 1)) :
    ∀ a : PAM M, P a := by
  rcases hP with ⟨φ, v, hφ⟩
  refine ind_pred (P := P) ⟨0, φ, v, fun a ↦ ?_⟩ h0 hs
  have heq : Function.update v 0 a = paEnv v (fun _ : Fin 1 ↦ a) := by
    funext x
    rcases x with _ | x
    · rw [Function.update_self, paEnv_lt _ _ (Nat.zero_lt_one)]
    · rw [Function.update_of_ne (Nat.succ_ne_zero x), paEnv_ge _ _ (by omega)]
  rw [heq]
  exact hφ _

theorem strong_ind1 {P : PAM M → Prop} (hP : PADef1 P)
    (hstep : ∀ a : PAM M, (∀ b < a, P b) → P a) : ∀ a : PAM M, P a := by
  rcases hP with ⟨φ, v, hφ⟩
  refine strong_ind_pred (P := P) ⟨0, φ, v, fun a ↦ ?_⟩ hstep
  have heq : Function.update v 0 a = paEnv v (fun _ : Fin 1 ↦ a) := by
    funext x
    rcases x with _ | x
    · rw [Function.update_self, paEnv_lt _ _ (Nat.zero_lt_one)]
    · rw [Function.update_of_ne (Nat.succ_ne_zero x), paEnv_ge _ _ (by omega)]
  rw [heq]
  exact hφ _

omit [PAModel M] in
theorem paDef_false (k : ℕ) : PADefN k (fun _ : Fin k → PAM M ↦ False) :=
  ⟨.bot, fun _ ↦ 0, fun _ ↦ Iff.rfl⟩

omit [PAModel M] in
theorem paDef_true (k : ℕ) : PADefN k (fun _ : Fin k → PAM M ↦ True) :=
  ⟨.eq .zero .zero, fun _ ↦ 0, fun _ ↦ by simp [PAFormula.HoldsIn]⟩

omit [PAModel M] in
theorem paDef_not {k : ℕ} {P : (Fin k → PAM M) → Prop} (hP : PADefN k P) :
    PADefN k (fun args ↦ ¬ P args) := by
  rcases hP with ⟨φ, v, hφ⟩
  exact ⟨φ.not, v, fun args ↦ not_congr (hφ args)⟩

omit [PAModel M] in
private theorem paDef_merge {k : ℕ} {P Q : (Fin k → PAM M) → Prop}
    (hP : PADefN k P) (hQ : PADefN k Q) :
    ∃ (φ₁ φ₂ : PAFormula) (v : ℕ → PAM M), ∀ args : Fin k → PAM M,
      (PAFormula.HoldsIn (paEnv v args) φ₁ ↔ P args) ∧
      (PAFormula.HoldsIn (paEnv v args) φ₂ ↔ Q args) := by
  rcases hP with ⟨φ₁, v₁, h₁⟩
  rcases hQ with ⟨φ₂, v₂, h₂⟩
  let m := max k φ₁.maxVar
  let σ : ℕ → ℕ := fun x ↦ if x < k then x else x + m
  have hσ_inj : Function.Injective σ := by
    intro x y hxy
    dsimp only [σ] at hxy
    split_ifs at hxy with hx hy hy <;> omega
  let v : ℕ → PAM M := fun z ↦ if z < m then v₁ z else v₂ (z - m)
  refine ⟨φ₁, renameAllFormula σ φ₂, v, fun args ↦ ⟨?_, ?_⟩⟩
  · refine (holdsIn_congr (fun z hz ↦ ?_)).trans (h₁ args)
    have hlt : z < m := by
      have : z < φ₁.maxVar := by
        by_contra hge
        rw [hasFree_false_of_maxVar_le_pam (Nat.le_of_not_lt hge)] at hz
        cases hz
      exact lt_of_lt_of_le this (Nat.le_max_right _ _)
    by_cases hzk : z < k
    · rw [paEnv_lt _ _ hzk, paEnv_lt _ _ hzk]
    · rw [paEnv_ge _ _ hzk, paEnv_ge _ _ hzk]
      simp [v, hlt]
  · rw [holdsIn_renameAllFormula hσ_inj]
    refine (holdsIn_congr (fun z _ ↦ ?_)).trans (h₂ args)
    by_cases hzk : z < k
    · change paEnv v args (if z < k then z else z + m) = paEnv v₂ args z
      simp only [hzk, ↓reduceIte]
      rw [paEnv_lt _ _ hzk, paEnv_lt _ _ hzk]
    · change paEnv v args (if z < k then z else z + m) = paEnv v₂ args z
      have hge : ¬ (z + m < k) := by omega
      have hge_m : ¬ (z + m < m) := by omega
      simp only [hzk, ↓reduceIte]
      rw [paEnv_ge _ _ hge, paEnv_ge _ _ hzk]
      simp [v, hge_m]

omit [PAModel M] in
theorem paDef_and {k : ℕ} {P Q : (Fin k → PAM M) → Prop}
    (hP : PADefN k P) (hQ : PADefN k Q) : PADefN k (fun args ↦ P args ∧ Q args) := by
  obtain ⟨φ₁, φ₂, v, h⟩ := paDef_merge hP hQ
  exact ⟨.and φ₁ φ₂, v, fun args ↦ and_congr (h args).1 (h args).2⟩

omit [PAModel M] in
theorem paDef_or {k : ℕ} {P Q : (Fin k → PAM M) → Prop}
    (hP : PADefN k P) (hQ : PADefN k Q) : PADefN k (fun args ↦ P args ∨ Q args) := by
  obtain ⟨φ₁, φ₂, v, h⟩ := paDef_merge hP hQ
  exact ⟨.or φ₁ φ₂, v, fun args ↦ or_congr (h args).1 (h args).2⟩

omit [PAModel M] in
theorem paDef_imp {k : ℕ} {P Q : (Fin k → PAM M) → Prop}
    (hP : PADefN k P) (hQ : PADefN k Q) : PADefN k (fun args ↦ P args → Q args) := by
  obtain ⟨φ₁, φ₂, v, h⟩ := paDef_merge hP hQ
  exact ⟨.imp φ₁ φ₂, v, fun args ↦ imp_congr (h args).1 (h args).2⟩

omit [PAModel M] in
theorem paDef_iff {k : ℕ} {P Q : (Fin k → PAM M) → Prop}
    (hP : PADefN k P) (hQ : PADefN k Q) : PADefN k (fun args ↦ P args ↔ Q args) :=
  paDefN_congr (fun _ ↦ iff_iff_implies_and_implies.symm)
    (paDef_and (paDef_imp hP hQ) (paDef_imp hQ hP))

omit [PAStructure M] [PAModel M] in
private theorem update_paEnv_eq_snoc {k : ℕ} (v : ℕ → PAM M) (args : Fin k → PAM M) (a : PAM M) :
    Function.update (paEnv v args) k a = paEnv v (Fin.snoc args a) := by
  funext x
  by_cases hxk : x = k
  · subst hxk
    rw [Function.update_self, paEnv_lt _ _ (Nat.lt_succ_self x), fin_snoc_eq]
  · rw [Function.update_of_ne hxk]
    by_cases hlt : x < k
    · have hlt' : x < k + 1 := Nat.lt_succ_of_lt hlt
      rw [paEnv_lt _ _ hlt, paEnv_lt _ _ hlt', fin_snoc_lt _ _ hlt' hlt]
    · have hlt' : ¬ (x < k + 1) := by omega
      rw [paEnv_ge _ _ hlt, paEnv_ge _ _ hlt']

omit [PAModel M] in
theorem paDef_ex {k : ℕ} {P : (Fin (k + 1) → PAM M) → Prop} (hP : PADefN (k + 1) P) :
    PADefN k (fun args ↦ ∃ a : PAM M, P (Fin.snoc args a)) := by
  rcases hP with ⟨φ, v, hφ⟩
  refine ⟨.ex k φ, v, fun args ↦ ?_⟩
  simp only [PAFormula.HoldsIn]
  exact exists_congr fun a ↦ by rw [update_paEnv_eq_snoc]; exact hφ (Fin.snoc args a)

omit [PAModel M] in
theorem paDef_all {k : ℕ} {P : (Fin (k + 1) → PAM M) → Prop} (hP : PADefN (k + 1) P) :
    PADefN k (fun args ↦ ∀ a : PAM M, P (Fin.snoc args a)) := by
  rcases hP with ⟨φ, v, hφ⟩
  refine ⟨.all k φ, v, fun args ↦ ?_⟩
  simp only [PAFormula.HoldsIn]
  exact forall_congr' fun a ↦ by rw [update_paEnv_eq_snoc]; exact hφ (Fin.snoc args a)

omit [PAModel M] in
theorem paDef_weaken {k : ℕ} {P : (Fin k → PAM M) → Prop} (hP : PADefN k P) :
    PADefN (k + 1) (fun args ↦ P (Fin.init args)) := by
  rcases hP with ⟨φ, v, hφ⟩
  let σ : ℕ → ℕ := fun x ↦ if x < k then x else x + 1
  have hσ_inj : Function.Injective σ := by
    intro x y hxy
    dsimp only [σ] at hxy
    split_ifs at hxy with hx hy hy <;> omega
  let v' : ℕ → PAM M := fun z ↦ v (z - 1)
  refine ⟨renameAllFormula σ φ, v', fun args ↦ ?_⟩
  rw [holdsIn_renameAllFormula hσ_inj]
  refine (holdsIn_congr (fun z _ ↦ ?_)).trans (hφ (Fin.init args))
  by_cases hzk : z < k
  · have hzk1 : z < k + 1 := Nat.lt_succ_of_lt hzk
    change paEnv v' args (if z < k then z else z + 1) = paEnv v (Fin.init args) z
    simp only [hzk, ↓reduceIte]
    rw [paEnv_lt _ _ hzk1, paEnv_lt _ _ hzk]
    rfl
  · have hge : ¬ (z + 1 < k + 1) := by omega
    change paEnv v' args (if z < k then z else z + 1) = paEnv v (Fin.init args) z
    simp only [hzk, ↓reduceIte]
    rw [paEnv_ge _ _ hge, paEnv_ge _ _ hzk]
    rfl

omit [PAModel M] in
private theorem paDef_subst_last {k : ℕ} {f : (Fin k → PAM M) → PAM M}
    {R : (Fin (k + 1) → PAM M) → Prop} (hf : PAFunN k f) (hR : PADefN (k + 1) R) :
    PADefN k (fun args ↦ R (Fin.snoc args (f args))) := by
  refine paDefN_congr (fun args ↦ ?_) (paDef_ex (paDef_and hf hR))
  constructor
  · rintro ⟨a, ha, hr⟩
    rw [Fin.snoc_last, Fin.init_snoc] at ha
    rwa [← ha]
  · intro hr
    exact ⟨f args, by rw [Fin.snoc_last, Fin.init_snoc], hr⟩

omit [PAModel M] in
theorem paFun_weaken {k : ℕ} {f : (Fin k → PAM M) → PAM M} (hf : PAFunN k f) :
    PAFunN (k + 1) (fun args ↦ f (Fin.init args)) := by
  rcases hf with ⟨φ, v, hφ⟩
  let σ : ℕ → ℕ := fun x ↦ if x < k then x else x + 1
  have hσ_inj : Function.Injective σ := by
    intro x y hxy
    dsimp only [σ] at hxy
    split_ifs at hxy with hx hy hy <;> omega
  let v' : ℕ → PAM M := fun z ↦ v (z - 1)
  refine ⟨renameAllFormula σ φ, v', fun args ↦ ?_⟩
  rw [holdsIn_renameAllFormula hσ_inj]
  let args₀ : Fin (k + 1) → PAM M :=
    Fin.snoc (Fin.init (Fin.init args)) (args (Fin.last (k + 1)))
  have htran : PAFormula.HoldsIn (paEnv v' args ∘ σ) φ ↔ PAFormula.HoldsIn (paEnv v args₀) φ := by
    refine holdsIn_congr fun z _ ↦ ?_
    by_cases hzk : z < k
    · have hzk1 : z < k + 1 := Nat.lt_succ_of_lt hzk
      have hzk2 : z < k + 2 := Nat.lt_succ_of_lt hzk1
      change paEnv v' args (if z < k then z else z + 1) = paEnv v args₀ z
      simp only [hzk, ↓reduceIte]
      rw [paEnv_lt _ _ hzk2, paEnv_lt _ _ hzk1]
      dsimp only [args₀]
      rw [fin_snoc_lt _ _ hzk1 hzk]
      rfl
    · by_cases heq : z = k
      · subst heq
        change paEnv v' args (if z < z then z else z + 1) = paEnv v args₀ z
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rw [paEnv_lt _ _ (Nat.lt_succ_self (z + 1)), paEnv_lt _ _ (Nat.lt_succ_self z)]
        dsimp only [args₀]
        rw [fin_snoc_eq]
        rfl
      · have hge2 : ¬ (z + 1 < k + 2) := by omega
        have hge1 : ¬ (z < k + 1) := by omega
        change paEnv v' args (if z < k then z else z + 1) = paEnv v args₀ z
        simp only [hzk, ↓reduceIte]
        rw [paEnv_ge _ _ hge2, paEnv_ge _ _ hge1]
        rfl
  rw [htran, hφ args₀]
  dsimp only [args₀]
  rw [Fin.snoc_last, Fin.init_snoc]

omit [PAModel M] in
theorem paFun_proj {k : ℕ} (i : Fin k) : PAFunN k (fun args : Fin k → PAM M ↦ args i) := by
  refine ⟨.eq (.var k) (.var i.val), fun _ ↦ 0, fun args ↦ ?_⟩
  simp only [PAFormula.HoldsIn, evalIn_var]
  rw [paEnv_lt _ _ (Nat.lt_succ_self k), paEnv_lt _ _ (Nat.lt_succ_of_lt i.isLt)]
  rfl

omit [PAModel M] in
theorem paFun_const {k : ℕ} (c : PAM M) : PAFunN k (fun _ : Fin k → PAM M ↦ c) := by
  refine ⟨.eq (.var k) (.var (k + 1)), fun _ ↦ c, fun args ↦ ?_⟩
  simp only [PAFormula.HoldsIn, evalIn_var]
  rw [paEnv_lt _ _ (Nat.lt_succ_self k), paEnv_ge _ _ (Nat.lt_irrefl (k + 1))]
  rfl

omit [PAModel M] in
theorem paDef_eq {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PADefN k (fun args ↦ f args = g args) := by
  refine paDefN_congr (fun args ↦ ?_) (paDef_ex (paDef_and hf hg))
  exact ⟨fun ⟨a, ha, hb⟩ ↦ by
    rw [Fin.snoc_last, Fin.init_snoc] at ha hb
    exact ha.symm.trans hb,
    fun h ↦ ⟨f args, by rw [Fin.snoc_last, Fin.init_snoc],
      by rw [Fin.snoc_last, Fin.init_snoc, h]⟩⟩

omit [PAModel M] in
theorem paDef_le {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PADefN k (fun args ↦ f args ≤ g args) := by
  have hbase : PADefN (k + 2) (fun args : Fin (k + 2) → PAM M ↦
      args ⟨k, by omega⟩ ≤ args (Fin.last (k + 1))) := by
    refine ⟨paLe (.var k) (.var (k + 1)), fun _ ↦ 0, fun args ↦ ?_⟩
    rw [paLe_holdsIn_iff, evalIn_var, evalIn_var,
      paEnv_lt _ _ (by omega : k < k + 2), paEnv_lt _ _ (Nat.lt_succ_self (k + 1))]
    rfl
  have h1 := paDef_subst_last (paFun_weaken hg) hbase
  have h2 := paDef_subst_last hf h1
  refine paDefN_congr (fun args ↦ ?_) h2
  rw [Fin.snoc_last, Fin.init_snoc, fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq]

theorem paDef_lt {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PADefN k (fun args ↦ f args < g args) :=
  paDefN_congr (fun _ ↦ lt_iff_le_and_ne.symm)
    (paDef_and (paDef_le hf hg) (paDef_not (paDef_eq hf hg)))

omit [PAModel M] in
theorem paFun_add {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PAFunN k (fun args ↦ f args + g args) := by
  have hbase : PADefN (k + 3) (fun args : Fin (k + 3) → PAM M ↦
      args ⟨k, by omega⟩ = args ⟨k + 1, by omega⟩ + args (Fin.last (k + 2))) := by
    refine ⟨.eq (.var k) (.add (.var (k + 1)) (.var (k + 2))), fun _ ↦ 0, fun args ↦ ?_⟩
    simp only [PAFormula.HoldsIn, evalIn_add, evalIn_var]
    rw [paEnv_lt _ _ (by omega : k < k + 3), paEnv_lt _ _ (by omega : k + 1 < k + 3),
      paEnv_lt _ _ (Nat.lt_succ_self (k + 2))]
    rfl
  have h1 := paDef_subst_last (paFun_weaken (paFun_weaken hg)) hbase
  have h2 := paDef_subst_last (paFun_weaken hf) h1
  refine paDefN_congr (fun args ↦ ?_) h2
  simp only [Fin.snoc_last, Fin.init_snoc]
  rw [fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k),
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_eq]
  rfl

omit [PAModel M] in
theorem paFun_mul {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PAFunN k (fun args ↦ f args * g args) := by
  have hbase : PADefN (k + 3) (fun args : Fin (k + 3) → PAM M ↦
      args ⟨k, by omega⟩ = args ⟨k + 1, by omega⟩ * args (Fin.last (k + 2))) := by
    refine ⟨.eq (.var k) (.mul (.var (k + 1)) (.var (k + 2))), fun _ ↦ 0, fun args ↦ ?_⟩
    simp only [PAFormula.HoldsIn, evalIn_mul, evalIn_var]
    rw [paEnv_lt _ _ (by omega : k < k + 3), paEnv_lt _ _ (by omega : k + 1 < k + 3),
      paEnv_lt _ _ (Nat.lt_succ_self (k + 2))]
    rfl
  have h1 := paDef_subst_last (paFun_weaken (paFun_weaken hg)) hbase
  have h2 := paDef_subst_last (paFun_weaken hf) h1
  refine paDefN_congr (fun args ↦ ?_) h2
  simp only [Fin.snoc_last, Fin.init_snoc]
  rw [fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k),
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_eq]
  rfl

theorem paFun_sub {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PAFunN k (fun args ↦ f args - g args) := by
  let z : (Fin (k + 1) → PAM M) → PAM M := fun a ↦ a (Fin.last k)
  let f' : (Fin (k + 1) → PAM M) → PAM M := fun a ↦ f (Fin.init a)
  let g' : (Fin (k + 1) → PAM M) → PAM M := fun a ↦ g (Fin.init a)
  have hz : PAFunN (k + 1) z := paFun_proj (Fin.last k)
  have hf' : PAFunN (k + 1) f' := paFun_weaken hf
  have hg' : PAFunN (k + 1) g' := paFun_weaken hg
  refine paDefN_congr (fun a ↦ ?_)
    (paDef_or
      (paDef_and (paDef_le hg' hf') (paDef_eq (paFun_add hg' hz) hf'))
      (paDef_and (paDef_lt hf' hg') (paDef_eq hz (paFun_const 0))))
  dsimp only [z, f', g']
  by_cases hle : g (Fin.init a) ≤ f (Fin.init a)
  · have hnotlt : ¬ f (Fin.init a) < g (Fin.init a) := not_lt_of_ge hle
    simp only [hle, true_and, hnotlt, false_and, or_false]
    rw [eq_comm (a := a (Fin.last k)), sub_eq_iff_eq_add_pam hle, eq_comm]
  · have hlt : f (Fin.init a) < g (Fin.init a) := lt_of_not_ge hle
    have hsub0 : f (Fin.init a) - g (Fin.init a) = 0 := sub_eq_zero_of_le_pam (le_of_lt hlt)
    simp [hle, hlt, hsub0]

theorem paFun_div {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PAFunN k (fun args ↦ f args / g args) := by
  let q : (Fin (k + 1) → PAM M) → PAM M := fun a ↦ a (Fin.last k)
  let f' : (Fin (k + 1) → PAM M) → PAM M := fun a ↦ f (Fin.init a)
  let g' : (Fin (k + 1) → PAM M) → PAM M := fun a ↦ g (Fin.init a)
  have hq : PAFunN (k + 1) q := paFun_proj (Fin.last k)
  have hf' : PAFunN (k + 1) f' := paFun_weaken hf
  have hg' : PAFunN (k + 1) g' := paFun_weaken hg
  have hrem : PADefN (k + 2) (fun b : Fin (k + 2) → PAM M ↦
      f' (Fin.init b) = g' (Fin.init b) * q (Fin.init b) + b (Fin.last (k + 1)) ∧
        b (Fin.last (k + 1)) < g' (Fin.init b)) := by
    have hr : PAFunN (k + 2) (fun b : Fin (k + 2) → PAM M ↦ b (Fin.last (k + 1))) :=
      paFun_proj (Fin.last (k + 1))
    exact paDef_and
      (paDef_eq (paFun_weaken hf') (paFun_add (paFun_mul (paFun_weaken hg') (paFun_weaken hq)) hr))
      (paDef_lt hr (paFun_weaken hg'))
  refine paDefN_congr (fun a ↦ ?_)
    (paDef_or
      (paDef_and (paDef_eq hg' (paFun_const 0)) (paDef_eq hq (paFun_const 0)))
      (paDef_and (paDef_lt (paFun_const 0) hg') (paDef_ex hrem)))
  dsimp only [q, f', g']
  by_cases hg0 : g (Fin.init a) = 0
  · have hdiv0 : f (Fin.init a) / 0 = 0 := dite_eq_right_of_eq_false (eq_false (lt_irrefl 0))
    simp [hg0, hdiv0]
  · have hpos : 0 < g (Fin.init a) := pos_iff_ne_zero_pam.mpr hg0
    simp only [hg0, false_and, hpos, true_and, false_or]
    constructor
    · rintro ⟨r, heq, hrlt⟩
      simp only [Fin.init_snoc, Fin.snoc_last] at heq hrlt
      exact ((div_mod_eq_iff hrlt).mpr heq).1.symm
    · intro hqeq
      refine ⟨f (Fin.init a) % g (Fin.init a), ?_⟩
      simp only [Fin.init_snoc, Fin.snoc_last, hqeq]
      exact ⟨(div_add_mod_pam _ _).symm, mod_lt_pam _ hpos⟩

theorem paFun_mod {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PAFunN k (fun args ↦ f args % g args) := by
  refine paFunN_congr (fun args ↦ ?_) (paFun_sub hf (paFun_mul hg (paFun_div hf hg)))
  exact (sub_eq_iff_eq_add_pam ⟨f args % g args, div_add_mod_pam _ _⟩).mpr
    (div_add_mod_pam _ _).symm

theorem paFun_mPair {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PAFunN k (fun args ↦ mPair (f args) (g args)) := by
  unfold mPair
  exact paFun_add hf
    (paFun_div (paFun_mul (paFun_add hf hg) (paFun_add (paFun_add hf hg) (paFun_const 1)))
      (paFun_const 2))

theorem paFun_mUnpair_fst {k : ℕ} {f : (Fin k → PAM M) → PAM M} (hf : PAFunN k f) :
    PAFunN k (fun args ↦ (mUnpair (f args)).1) := by
  have hpair : PADefN (k + 2) (fun b : Fin (k + 2) → PAM M ↦
      mPair (b ⟨k, by omega⟩) (b (Fin.last (k + 1))) = f (Fin.init (Fin.init b))) :=
    paDef_eq (paFun_mPair (paFun_proj ⟨k, by omega⟩) (paFun_proj (Fin.last (k + 1))))
      (paFun_weaken (paFun_weaken hf))
  refine paDefN_congr (fun a ↦ ?_) (paDef_ex hpair)
  constructor
  · rintro ⟨y, hy⟩
    rw [Fin.snoc_last, Fin.init_snoc, fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k)] at hy
    change mPair (a (Fin.last k)) y = f (Fin.init a) at hy
    dsimp only
    rw [← hy, mUnpair_mPair]
  · intro hx
    refine ⟨(mUnpair (f (Fin.init a))).2, ?_⟩
    rw [Fin.snoc_last, Fin.init_snoc, fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k)]
    change mPair (a (Fin.last k)) (mUnpair (f (Fin.init a))).2 = f (Fin.init a)
    rw [hx, mPair_mUnpair]

theorem paFun_mUnpair_snd {k : ℕ} {f : (Fin k → PAM M) → PAM M} (hf : PAFunN k f) :
    PAFunN k (fun args ↦ (mUnpair (f args)).2) := by
  have hpair : PADefN (k + 2) (fun b : Fin (k + 2) → PAM M ↦
      mPair (b (Fin.last (k + 1))) (b ⟨k, by omega⟩) = f (Fin.init (Fin.init b))) :=
    paDef_eq (paFun_mPair (paFun_proj (Fin.last (k + 1))) (paFun_proj ⟨k, by omega⟩))
      (paFun_weaken (paFun_weaken hf))
  refine paDefN_congr (fun a ↦ ?_) (paDef_ex hpair)
  constructor
  · rintro ⟨x, hx⟩
    rw [Fin.snoc_last, Fin.init_snoc, fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k)] at hx
    change mPair x (a (Fin.last k)) = f (Fin.init a) at hx
    dsimp only
    rw [← hx, mUnpair_mPair]
  · intro hy
    refine ⟨(mUnpair (f (Fin.init a))).1, ?_⟩
    rw [Fin.snoc_last, Fin.init_snoc, fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k)]
    change mPair (mUnpair (f (Fin.init a))).1 (a (Fin.last k)) = f (Fin.init a)
    rw [hy, mPair_mUnpair]

omit [PAModel M] in
theorem paDef_fin_exists {k m : ℕ} {P : Fin m → (Fin k → PAM M) → Prop}
    (hP : ∀ i : Fin m, PADefN k (P i)) :
    PADefN k (fun args ↦ ∃ i : Fin m, P i args) := by
  induction m with
  | zero =>
    exact paDefN_congr (fun _ ↦ ⟨fun h ↦ h.elim, fun ⟨i, _⟩ ↦ Fin.elim0 i⟩) (paDef_false k)
  | succ m ih =>
    have hlast : PADefN k (P (Fin.last m)) := hP (Fin.last m)
    have hinit : PADefN k (fun args ↦ ∃ j : Fin m, P j.castSucc args) :=
      ih (fun j ↦ hP j.castSucc)
    refine paDefN_congr (fun args ↦ ?_) (paDef_or hinit hlast)
    constructor
    · rintro (⟨j, hj⟩ | hl)
      · exact ⟨j.castSucc, hj⟩
      · exact ⟨Fin.last m, hl⟩
    · rintro ⟨i, hi⟩
      revert hi
      exact Fin.lastCases (fun hl ↦ Or.inr hl) (fun j hj ↦ Or.inl ⟨j, hj⟩) i

omit [PAModel M] in
theorem paDef_fin_forall {k m : ℕ} {P : Fin m → (Fin k → PAM M) → Prop}
    (hP : ∀ i : Fin m, PADefN k (P i)) :
    PADefN k (fun args ↦ ∀ i : Fin m, P i args) := by
  induction m with
  | zero =>
    exact paDefN_congr (fun _ ↦ ⟨fun _ i ↦ Fin.elim0 i, fun _ ↦ trivial⟩) (paDef_true k)
  | succ m ih =>
    have hlast : PADefN k (P (Fin.last m)) := hP (Fin.last m)
    have hinit : PADefN k (fun args ↦ ∀ j : Fin m, P j.castSucc args) :=
      ih (fun j ↦ hP j.castSucc)
    refine paDefN_congr (fun args ↦ ?_) (paDef_and hinit hlast)
    constructor
    · rintro ⟨hi, hl⟩ i
      exact Fin.lastCases hl hi i
    · intro hall
      exact ⟨fun j ↦ hall j.castSucc, hall (Fin.last m)⟩

/-! ## Section 5: Gödel's $\beta$-Function, `mBeta_snoc`, and `mBeta_concat` -/

/-- Gödel's $\beta$-function $c \bmod (1 + (i + 1) d)$ on `PAM M`. -/
noncomputable def mBeta (c d i : PAM M) : PAM M :=
  c % (1 + (i + 1) * d)

theorem paFun_mBeta {k : ℕ} {fc fd fi : (Fin k → PAM M) → PAM M}
    (hc : PAFunN k fc) (hd : PAFunN k fd) (hi : PAFunN k fi) :
    PAFunN k (fun args ↦ mBeta (fc args) (fd args) (fi args)) :=
  paFun_mod hc (paFun_add (paFun_const 1) (paFun_mul (paFun_add hi (paFun_const 1)) hd))

private theorem paBetaEq_holdsIn_iff (v : ℕ → PAM M) (c d i r : PATerm) :
    PAFormula.HoldsIn v (paBetaEq c d i r) ↔
      mBeta (PATerm.evalIn v c) (PATerm.evalIn v d) (PATerm.evalIn v i) =
        PATerm.evalIn v r := by
  let m := PATerm.succ (.mul (.succ i) d)
  let q := max (max c.freshVar m.freshVar) r.freshVar
  have hc : c.freshVar ≤ q := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hm : m.freshVar ≤ q := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hr : r.freshVar ≤ q := Nat.le_max_right _ _
  have hmev : PATerm.evalIn v m = 1 + (PATerm.evalIn v i + 1) * PATerm.evalIn v d := by
    simp only [m, evalIn_succ, evalIn_mul]
    ring
  change PAFormula.HoldsIn v (.ex q (.and (.eq c (.add (.mul (.var q) m) r)) (paLt r m))) ↔ _
  simp only [PAFormula.HoldsIn, paLt_holdsIn_iff, evalIn_add, evalIn_mul, evalIn_var, mBeta]
  set mod := 1 + (PATerm.evalIn v i + 1) * PATerm.evalIn v d
  have hpos : 0 < mod := ⟨(PATerm.evalIn v i + 1) * PATerm.evalIn v d, by ring⟩
  constructor
  · rintro ⟨w, hcw, hrlt⟩
    rw [evalIn_update_of_freshVar_le v w hc, evalIn_update_of_freshVar_le v w hm,
      evalIn_update_of_freshVar_le v w hr, Function.update_self, hmev] at hcw
    rw [evalIn_update_of_freshVar_le v w hr, evalIn_update_of_freshVar_le v w hm, hmev] at hrlt
    exact ((div_mod_eq_iff (q := w) hrlt).mpr (by rw [hcw]; ring)).2
  · intro hrem
    refine ⟨PATerm.evalIn v c / mod, ?_, ?_⟩
    · rw [evalIn_update_of_freshVar_le v _ hc, evalIn_update_of_freshVar_le v _ hm,
        evalIn_update_of_freshVar_le v _ hr, Function.update_self, hmev, ← hrem]
      calc PATerm.evalIn v c
        _ = mod * (PATerm.evalIn v c / mod) + PATerm.evalIn v c % mod :=
            (div_add_mod_pam _ mod).symm
        _ = PATerm.evalIn v c / mod * mod + PATerm.evalIn v c % mod := by ring
    · rw [evalIn_update_of_freshVar_le v _ hr, evalIn_update_of_freshVar_le v _ hm,
        hmev, ← hrem]
      exact mod_lt_pam _ hpos

/-- Singleton $\beta$-code representing `[val]` at index `0`. -/
theorem mBeta_singleton (val : PAM M) : mBeta val (val + 1) 0 = val := by
  unfold mBeta
  exact mod_eq_of_lt_pam ⟨1, by ring⟩

private def DvdPAM (a b : PAM M) : Prop := ∃ q : PAM M, b = a * q

private def BezoutPAM (a b : PAM M) : Prop := ∃ u v : PAM M, u * a = v * b + 1

omit [PAModel M] in
private theorem paDef_dvd {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PADefN k (fun args ↦ DvdPAM (f args) (g args)) := by
  refine paDefN_congr (fun args ↦ ?_)
    (paDef_ex (paDef_eq (paFun_weaken hg)
      (paFun_mul (paFun_weaken hf) (paFun_proj (Fin.last k)))))
  simp only [DvdPAM, Fin.snoc_last, Fin.init_snoc]

omit [PAModel M] in
private theorem paDef_bezout {k : ℕ} {f g : (Fin k → PAM M) → PAM M}
    (hf : PAFunN k f) (hg : PAFunN k g) : PADefN k (fun args ↦ BezoutPAM (f args) (g args)) := by
  have hu : PAFunN (k + 2) (fun b : Fin (k + 2) → PAM M ↦ b ⟨k, by omega⟩) :=
    paFun_proj ⟨k, by omega⟩
  have hv : PAFunN (k + 2) (fun b : Fin (k + 2) → PAM M ↦ b (Fin.last (k + 1))) :=
    paFun_proj (Fin.last (k + 1))
  have hf2 : PAFunN (k + 2) (fun b : Fin (k + 2) → PAM M ↦ f (Fin.init (Fin.init b))) :=
    paFun_weaken (paFun_weaken hf)
  have hg2 : PAFunN (k + 2) (fun b : Fin (k + 2) → PAM M ↦ g (Fin.init (Fin.init b))) :=
    paFun_weaken (paFun_weaken hg)
  refine paDefN_congr (fun args ↦ ?_)
    (paDef_ex (paDef_ex
      (paDef_eq (paFun_mul hu hf2) (paFun_add (paFun_mul hv hg2) (paFun_const 1)))))
  refine exists_congr fun u ↦ exists_congr fun v ↦ ?_
  rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
    fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq]

private theorem bezout_one_left (b : PAM M) : BezoutPAM 1 b :=
  ⟨1, 0, by ring⟩

private theorem bezout_mul_left {a₁ a₂ b : PAM M} (h₁ : BezoutPAM a₁ b)
    (h₂ : BezoutPAM a₂ b) : BezoutPAM (a₁ * a₂) b := by
  rcases h₁ with ⟨u₁, v₁, e₁⟩
  rcases h₂ with ⟨u₂, v₂, e₂⟩
  refine ⟨u₁ * u₂, v₁ * v₂ * b + v₁ + v₂, ?_⟩
  calc (u₁ * u₂) * (a₁ * a₂)
    _ = (u₁ * a₁) * (u₂ * a₂) := by ring
    _ = (v₁ * b + 1) * (v₂ * b + 1) := by rw [e₁, e₂]
    _ = (v₁ * v₂ * b + v₁ + v₂) * b + 1 := by ring

private theorem bezout_beta_moduli {d i k : PAM M} (hd : 0 < d) (hik : i < k)
    (hdvd : DvdPAM (k - i) d) :
    BezoutPAM (1 + (i + 1) * d) (1 + (k + 1) * d) := by
  rcases hdvd with ⟨q, hq⟩
  have hki_le : i ≤ k := le_of_lt hik
  have hq_pos : 0 < q := by
    rcases eq_zero_or_exists_succ q with rfl | ⟨q', rfl⟩
    · rw [mul_zero] at hq
      exact absurd hq (ne_of_gt hd)
    · exact ⟨q', by ring⟩
  set a := i + 1
  set b := k + 1
  set δ := k - i
  set si := 1 + a * d
  set sk := 1 + b * d
  have hb_eq : b = a + δ := by
    dsimp only [a, b, δ]
    calc k + 1
      _ = (i + (k - i)) + 1 := congrArg (· + 1) (add_sub_of_le_pam hki_le).symm
      _ = (i + 1) + (k - i) := by ring
  have habq_pos : 1 ≤ a * b * q := by
    rcases eq_zero_or_exists_succ q with rfl | ⟨q', rfl⟩
    · exact absurd rfl (ne_of_gt hq_pos)
    · exact ⟨i * (k + 1) * (q' + 1) + k * (q' + 1) + q', by dsimp only [a, b]; ring⟩
  set U := a * a * q
  set V := a * b * q - 1
  have hV : V + 1 = a * b * q := sub_add_cancel_pam habq_pos
  have hUV : V * si + 1 = U * sk := by
    apply (add_right_inj_pam si).mp
    calc (V * si + 1) + si
      _ = (V + 1) * si + 1 := by ring
      _ = a * (a + δ) * q * (1 + a * (δ * q)) + 1 := by rw [hV, hb_eq, ← hq]
      _ = a * a * q * (1 + (a + δ) * (δ * q)) + (1 + a * (δ * q)) := by ring
      _ = U * sk + si := by dsimp only [U, si, sk]; rw [hb_eq, ← hq]
  have hu_le : V ≤ (V + 1) * sk :=
    ⟨(V + 1) * b * d + 1, by dsimp only [sk]; ring⟩
  set u := (V + 1) * sk - V
  have hu : u + V = (V + 1) * sk := sub_add_cancel_pam hu_le
  have hv_le : U ≤ (V + 1) * si := by
    have hU_le : U ≤ U * sk := ⟨U * (b * d), by dsimp only [sk]; ring⟩
    refine le_trans hU_le ?_
    rw [← hUV]
    exact ⟨a * d, by dsimp only [si]; ring⟩
  set v := (V + 1) * si - U
  have hv : v + U = (V + 1) * si := sub_add_cancel_pam hv_le
  refine ⟨u, v, ?_⟩
  apply (add_right_inj_pam (U * sk)).mp
  calc u * si + U * sk
    _ = u * si + (V * si + 1) := by rw [← hUV]
    _ = (u + V) * si + 1 := by ring
    _ = (V + 1) * si * sk + 1 := by rw [hu]; ring
    _ = (v + U) * sk + 1 := by rw [← hv]
    _ = (v * sk + 1) + U * sk := by ring

private theorem exists_common_multiple (B : PAM M) :
    ∃ D : PAM M, 0 < D ∧ ∀ k : PAM M, 0 < k → k ≤ B → DvdPAM k D := by
  have hdef : PADef1 (fun b : PAM M ↦
      ∃ D : PAM M, 0 < D ∧ ∀ k : PAM M, 0 < k → k ≤ b → DvdPAM k D) := by
    have hb2 : PAFunN 3 (fun a : Fin 3 → PAM M ↦ a 0) := paFun_proj 0
    have hD2 : PAFunN 3 (fun a : Fin 3 → PAM M ↦ a 1) := paFun_proj 1
    have hk2 : PAFunN 3 (fun a : Fin 3 → PAM M ↦ a 2) := paFun_proj 2
    have hbody : PADefN 2 (fun a : Fin 2 → PAM M ↦ 0 < a 1 ∧
        ∀ k : PAM M, 0 < k → k ≤ a 0 → DvdPAM k (a 1)) := by
      refine paDefN_congr (fun a ↦ ?_)
        (paDef_and (paDef_lt (paFun_const 0) (paFun_proj 1))
          (paDef_all (paDef_imp (paDef_lt (paFun_const 0) hk2)
            (paDef_imp (paDef_le hk2 hb2) (paDef_dvd hk2 hD2)))))
      simp [Fin.snoc]
    refine paDefN_congr (fun a ↦ ?_) (paDef_ex hbody)
    simp [Fin.snoc]
  refine ind1 hdef ?_ ?_ B
  · refine ⟨1, zero_lt_one_pam, fun k hk hle ↦ ?_⟩
    rw [le_zero_iff_pam.mp hle] at hk
    exact absurd hk (lt_irrefl 0)
  · rintro b ⟨D, hD_pos, hD⟩
    refine ⟨D * (b + 1), ?_, fun k hk hle ↦ ?_⟩
    · rcases hD_pos with ⟨d', hd'⟩
      exact ⟨d' * (b + 1) + b, by rw [← hd']; ring⟩
    · rcases le_add_one_iff.mp hle with hkb | rfl
      · rcases hD k hk hkb with ⟨q, hq⟩
        exact ⟨q * (b + 1), by rw [hq]; ring⟩
      · exact ⟨D, mul_comm D (b + 1)⟩

/-- Extend a $\beta$-coded sequence `(c, d)` of length `n` in `PAM M` by appending `val` at index
`n`. -/
theorem mBeta_snoc (n c d val : PAM M) :
    ∃ c' d' : PAM M, (∀ i < n, mBeta c' d' i = mBeta c d i) ∧ mBeta c' d' n = val := by
  obtain ⟨D₀, hD₀_pos, hD₀_dvd⟩ := exists_common_multiple (n + 1)
  let d' := D₀ * (c + val + 1)
  have hd'_pos : 0 < d' := by
    rcases hD₀_pos with ⟨m, hm⟩
    exact ⟨m * (c + val + 1) + c + val, by dsimp only [d']; rw [← hm]; ring⟩
  have hd'_dvd : ∀ k : PAM M, 0 < k → k ≤ n + 1 → DvdPAM k d' := by
    intro k hk hle
    rcases hD₀_dvd k hk hle with ⟨q, hq⟩
    exact ⟨q * (c + val + 1), by dsimp only [d']; rw [hq]; ring⟩
  have hd'_gt_c : c < d' := by
    rcases eq_zero_or_exists_succ D₀ with rfl | ⟨m, rfl⟩
    · exact absurd rfl (ne_of_gt hD₀_pos)
    · exact ⟨val + m * (c + val + 1), by dsimp only [d']; ring⟩
  have hd'_gt_val : val < d' := by
    rcases eq_zero_or_exists_succ D₀ with rfl | ⟨m, rfl⟩
    · exact absurd rfl (ne_of_gt hD₀_pos)
    · exact ⟨c + m * (c + val + 1), by dsimp only [d']; ring⟩
  let s : PAM M → PAM M := fun i ↦ 1 + (i + 1) * d'
  have hs_pos : ∀ i : PAM M, 0 < s i := fun i ↦ ⟨(i + 1) * d', by dsimp only [s]; ring⟩
  have hbez_step : ∀ k : PAM M, k ≤ n →
      ∃ Mk : PAM M, 0 < Mk ∧ (∀ i < k, DvdPAM (s i) Mk) ∧ BezoutPAM Mk (s k) := by
    intro k hkn
    have hdef_bez : PADef1 (fun j : PAM M ↦ j ≤ k →
        ∃ Mj : PAM M, 0 < Mj ∧ (∀ i < j, DvdPAM (s i) Mj) ∧ BezoutPAM Mj (s k)) := by
      have hs_fun : PAFunN 3 (fun a : Fin 3 → PAM M ↦ s (a 2)) :=
        paFun_add (paFun_const 1)
          (paFun_mul (paFun_add (paFun_proj 2) (paFun_const 1)) (paFun_const d'))
      have hinner : PADefN 2 (fun a : Fin 2 → PAM M ↦ 0 < a 1 ∧
          (∀ i < a 0, DvdPAM (s i) (a 1)) ∧ BezoutPAM (a 1) (s k)) := by
        have hforall : PADefN 2 (fun a : Fin 2 → PAM M ↦
            ∀ i : PAM M, i < a 0 → DvdPAM (s i) (a 1)) := by
          refine paDefN_congr (fun a ↦ ?_)
            (paDef_all (paDef_imp (paDef_lt (paFun_proj 2) (paFun_proj 0))
              (paDef_dvd hs_fun (paFun_proj 1))))
          simp [Fin.snoc]
        exact paDef_and (paDef_lt (paFun_const 0) (paFun_proj 1))
          (paDef_and hforall (paDef_bezout (paFun_proj 1) (paFun_const (s k))))
      refine paDefN_congr (fun a ↦ ?_)
        (paDef_imp (paDef_le (paFun_proj 0) (paFun_const k)) (paDef_ex hinner))
      simp [Fin.snoc]
    refine ind1 hdef_bez ?_ ?_ k le_rfl
    · intro _
      exact ⟨1, zero_lt_one_pam, fun _ hi ↦ absurd hi (not_lt_zero_pam _), bezout_one_left (s k)⟩
    · intro j ih hjk
      have hj_lt_k : j < k := hjk
      obtain ⟨Mj, hMj_pos, hMj_dvd, hMj_bez⟩ := ih (le_of_lt hj_lt_k)
      have hkj_pos : 0 < k - j := by
        have ⟨m, hm⟩ := hj_lt_k
        have hsub : k - j = 1 + m :=
          (sub_eq_iff_eq_add_pam (le_of_lt hj_lt_k)).mpr (by rw [← hm]; ring)
        rw [hsub]
        exact ⟨m, by ring⟩
      have hkj_le : k - j ≤ n + 1 := by
        refine le_trans (b := k) ?_ (le_trans hkn ⟨1, rfl⟩)
        exact ⟨j, sub_add_cancel_pam (le_of_lt hj_lt_k)⟩
      have hbez_jk : BezoutPAM (s j) (s k) :=
        bezout_beta_moduli hd'_pos hj_lt_k (hd'_dvd (k - j) hkj_pos hkj_le)
      refine ⟨Mj * s j, ?_, ?_, bezout_mul_left hMj_bez hbez_jk⟩
      · rcases hMj_pos with ⟨m₁, hm₁⟩
        rcases hs_pos j with ⟨m₂, hm₂⟩
        exact ⟨m₁ * (1 + m₂) + m₂, by rw [← hm₁, ← hm₂]; ring⟩
      · intro i hi
        rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hi) with hilt | rfl
        · rcases hMj_dvd i hilt with ⟨q, hq⟩
          exact ⟨q * s j, by rw [hq]; ring⟩
        · exact ⟨Mj, mul_comm Mj (s i)⟩
  let target : PAM M → PAM M := fun i ↦ if i < n then mBeta c d i else val
  have htarget_lt : ∀ i : PAM M, target i < s i := by
    intro i
    dsimp only [target, s]
    split_ifs with hin
    · have hle_c : mBeta c d i ≤ c := by
        unfold mBeta
        have hdiv := div_add_mod_pam c (1 + (i + 1) * d)
        exact ⟨(1 + (i + 1) * d) * (c / (1 + (i + 1) * d)), by rw [add_comm]; exact hdiv⟩
      exact lt_of_le_of_lt hle_c (lt_of_lt_of_le hd'_gt_c ⟨1 + i * d', by ring⟩)
    · exact lt_of_lt_of_le hd'_gt_val ⟨1 + i * d', by ring⟩
  have hdef_crt : PADef1 (fun k : PAM M ↦ k ≤ n + 1 →
      ∃ x : PAM M, ∀ i < k, x % s i = target i) := by
    have hsi : PAFunN 3 (fun a : Fin 3 → PAM M ↦ s (a 2)) :=
      paFun_add (paFun_const 1)
        (paFun_mul (paFun_add (paFun_proj 2) (paFun_const 1)) (paFun_const d'))
    have htar : PADefN 3 (fun a : Fin 3 → PAM M ↦ a 1 % s (a 2) = target (a 2)) := by
      have hmod_x : PAFunN 3 (fun a : Fin 3 → PAM M ↦ a 1 % s (a 2)) :=
        paFun_mod (paFun_proj 1) hsi
      have hbeta_cd : PAFunN 3 (fun a : Fin 3 → PAM M ↦ mBeta c d (a 2)) :=
        paFun_mBeta (paFun_const c) (paFun_const d) (paFun_proj 2)
      refine paDefN_congr (fun a ↦ ?_)
        (paDef_and
          (paDef_imp (paDef_lt (paFun_proj 2) (paFun_const n)) (paDef_eq hmod_x hbeta_cd))
          (paDef_imp (paDef_not (paDef_lt (paFun_proj 2) (paFun_const n)))
            (paDef_eq hmod_x (paFun_const val))))
      dsimp only [target]
      split_ifs with hlt <;> simp [hlt]
    have hex_x : PADefN 1 (fun a : Fin 1 → PAM M ↦
        ∃ x : PAM M, ∀ i < a 0, x % s i = target i) := by
      have hfor_i : PADefN 2 (fun a : Fin 2 → PAM M ↦
          ∀ i : PAM M, i < a 0 → a 1 % s i = target i) := by
        refine paDefN_congr (fun a ↦ ?_)
          (paDef_all (paDef_imp (paDef_lt (paFun_proj 2) (paFun_proj 0)) htar))
        simp [Fin.snoc]
      refine paDefN_congr (fun a ↦ ?_) (paDef_ex hfor_i)
      simp [Fin.snoc]
    exact paDef_imp (paDef_le (paFun_proj 0) (paFun_const (n + 1))) hex_x
  have hcrt := ind1 hdef_crt
    (fun _ ↦ ⟨0, fun _ hi ↦ absurd hi (not_lt_zero_pam _)⟩)
    (fun k ih hk1 ↦ ?_) (n + 1) le_rfl
  · obtain ⟨c', hc'⟩ := hcrt
    refine ⟨c', d', fun i hi ↦ ?_, ?_⟩
    · have h := hc' i (lt_trans hi (lt_succ_self_pam n))
      simpa [mBeta, s, target, hi] using h
    · have h := hc' n (lt_succ_self_pam n)
      simpa [mBeta, s, target, lt_irrefl n] using h
  · have hkn : k ≤ n := by
      rcases hk1 with ⟨m, hm⟩
      exact ⟨m, (add_right_inj_pam 1).mp (by rw [← hm]; ring)⟩
    obtain ⟨xk, hxk⟩ := ih (le_trans ⟨1, rfl⟩ hk1)
    obtain ⟨Mk, _, hMk_dvd, ⟨u, v, huv⟩⟩ := hbez_step k hkn
    let rem := xk % s k
    have hrem_le : rem ≤ s k := le_of_lt (mod_lt_pam xk (hs_pos k))
    let δmod := (s k - rem) + target k
    have hxδ : xk + δmod = s k * (xk / s k + 1) + target k := by
      calc xk + δmod
        _ = (s k * (xk / s k) + rem) + ((s k - rem) + target k) := by
            conv_lhs => rw [← div_add_mod_pam xk (s k)]
        _ = s k * (xk / s k) + (rem + (s k - rem)) + target k := by ring
        _ = s k * (xk / s k) + s k + target k := by rw [add_sub_of_le_pam hrem_le]
        _ = s k * (xk / s k + 1) + target k := by ring
    let x' := xk + Mk * (u * δmod)
    refine ⟨x', fun i hi ↦ ?_⟩
    rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hi) with hilt | rfl
    · obtain ⟨wi, hwi⟩ := hMk_dvd i hilt
      have hxi : xk = s i * (xk / s i) + target i := by
        rw [← hxk i hilt]
        exact (div_add_mod_pam xk (s i)).symm
      refine ((div_mod_eq_iff (q := xk / s i + wi * (u * δmod)) (htarget_lt i)).mpr ?_).2
      calc x'
        _ = (s i * (xk / s i) + target i) + (s i * wi) * (u * δmod) := by
            dsimp only [x']
            rw [← hxi, hwi]
        _ = s i * (xk / s i + wi * (u * δmod)) + target i := by ring
    · refine ((div_mod_eq_iff (q := xk / s i + 1 + v * δmod) (htarget_lt i)).mpr ?_).2
      calc x'
        _ = xk + (u * Mk) * δmod := by dsimp only [x']; ring
        _ = xk + (v * s i + 1) * δmod := by rw [huv]
        _ = (xk + δmod) + s i * (v * δmod) := by ring
        _ = (s i * (xk / s i + 1) + target i) + s i * (v * δmod) := by rw [hxδ]
        _ = s i * (xk / s i + 1 + v * δmod) + target i := by ring

/-- Concatenate two $\beta$-coded sequences of lengths `n₁` and `n₂` in `PAM M`. -/
theorem mBeta_concat (n₁ c₁ d₁ n₂ c₂ d₂ : PAM M) :
    ∃ c' d' : PAM M,
      (∀ i < n₁, mBeta c' d' i = mBeta c₁ d₁ i) ∧
      (∀ j < n₂, mBeta c' d' (n₁ + j) = mBeta c₂ d₂ j) := by
  have hdef : PADef1 (fun k : PAM M ↦
      ∃ c' d' : PAM M,
        (∀ i < n₁, mBeta c' d' i = mBeta c₁ d₁ i) ∧
        (∀ j < k, mBeta c' d' (n₁ + j) = mBeta c₂ d₂ j)) := by
    have hp1 : PADefN 3 (fun a : Fin 3 → PAM M ↦ ∀ i : PAM M, i < n₁ →
        mBeta (a 1) (a 2) i = mBeta c₁ d₁ i) := by
      refine paDefN_congr (fun a ↦ ?_)
        (paDef_all (paDef_imp (paDef_lt (paFun_proj 3) (paFun_const n₁))
          (paDef_eq
            (paFun_mBeta (paFun_proj 1) (paFun_proj 2) (paFun_proj 3))
            (paFun_mBeta (paFun_const c₁) (paFun_const d₁) (paFun_proj 3)))))
      simp [Fin.snoc]; rfl
    have hp2 : PADefN 3 (fun a : Fin 3 → PAM M ↦ ∀ j : PAM M, j < a 0 →
        mBeta (a 1) (a 2) (n₁ + j) = mBeta c₂ d₂ j) := by
      refine paDefN_congr (fun a ↦ ?_)
        (paDef_all (paDef_imp (paDef_lt (paFun_proj 3) (paFun_proj 0))
          (paDef_eq
            (paFun_mBeta (paFun_proj 1) (paFun_proj 2)
              (paFun_add (paFun_const n₁) (paFun_proj 3)))
            (paFun_mBeta (paFun_const c₂) (paFun_const d₂) (paFun_proj 3)))))
      simp [Fin.snoc]; rfl
    refine paDefN_congr (fun a ↦ ?_) (paDef_ex (paDef_ex (paDef_and hp1 hp2)))
    simp [Fin.snoc]
  refine ind1 hdef ⟨c₁, d₁, fun _ _ ↦ rfl, fun _ hj ↦ absurd hj (not_lt_zero_pam _)⟩
    (fun k ⟨c', d', h1, h2⟩ ↦ ?_) n₂
  obtain ⟨c'', d'', hprev, hlast⟩ := mBeta_snoc (n₁ + k) c' d' (mBeta c₂ d₂ k)
  refine ⟨c'', d'', fun i hi ↦ ?_, fun j hj ↦ ?_⟩
  · rw [hprev i (lt_of_lt_of_le hi (le_add_right_pam n₁ k)), h1 i hi]
  · rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hj) with hjlt | rfl
    · rw [hprev (n₁ + j) (add_lt_add_left_pam hjlt n₁), h2 j hjlt]
    · exact hlast

/-! ## Section 6: Internal Base-2 Exponentiation (`mPow2`) and Unary Blocks (`mRep0`, `mRep1`) -/

/-- $\beta$-coded base-2 power table witness up to `r` with output `y = 2^r`. -/
def IsPow2Seq (c d r y : PAM M) : Prop :=
  mBeta c d 0 = 1 ∧ (∀ j < r, mBeta c d (j + 1) = 2 * mBeta c d j) ∧ mBeta c d r = y

private theorem paDef_isPow2Seq {k : ℕ} {fc fd fr fy : (Fin k → PAM M) → PAM M}
    (hc : PAFunN k fc) (hd : PAFunN k fd) (hr : PAFunN k fr) (hy : PAFunN k fy) :
    PADefN k (fun a ↦ IsPow2Seq (fc a) (fd a) (fr a) (fy a)) := by
  have h0 : PADefN k (fun a ↦ mBeta (fc a) (fd a) 0 = 1) :=
    paDef_eq (paFun_mBeta hc hd (paFun_const 0)) (paFun_const 1)
  have hlast : PADefN k (fun a ↦ mBeta (fc a) (fd a) (fr a) = fy a) :=
    paDef_eq (paFun_mBeta hc hd hr) hy
  have hstep : PADefN k (fun a ↦ ∀ j : PAM M, j < fr a →
      mBeta (fc a) (fd a) (j + 1) = 2 * mBeta (fc a) (fd a) j) := by
    let jProj : (Fin (k + 1) → PAM M) → PAM M := fun b ↦ b (Fin.last k)
    have hj : PAFunN (k + 1) jProj := paFun_proj (Fin.last k)
    have hc' : PAFunN (k + 1) (fun b ↦ fc (Fin.init b)) := paFun_weaken hc
    have hd' : PAFunN (k + 1) (fun b ↦ fd (Fin.init b)) := paFun_weaken hd
    have hr' : PAFunN (k + 1) (fun b ↦ fr (Fin.init b)) := paFun_weaken hr
    refine paDefN_congr (fun a ↦ ?_)
      (paDef_all (paDef_imp (paDef_lt hj hr')
        (paDef_eq
          (paFun_mBeta hc' hd' (paFun_add hj (paFun_const 1)))
          (paFun_mul (paFun_const 2) (paFun_mBeta hc' hd' hj)))))
    simp [jProj, Fin.snoc_last, Fin.init_snoc]
  exact paDef_and h0 (paDef_and hstep hlast)

theorem exists_pow2Seq (r : PAM M) : ∃ y c d : PAM M, IsPow2Seq c d r y := by
  have hdef : PADef1 (fun r₀ : PAM M ↦ ∃ y c d : PAM M, IsPow2Seq c d r₀ y) := by
    have h4 : PADefN 4 (fun a : Fin 4 → PAM M ↦ IsPow2Seq (a 2) (a 3) (a 0) (a 1)) :=
      paDef_isPow2Seq (paFun_proj 2) (paFun_proj 3) (paFun_proj 0) (paFun_proj 1)
    refine paDefN_congr (fun a ↦ ?_) (paDef_ex (paDef_ex (paDef_ex h4)))
    simp [Fin.snoc]
  refine ind1 hdef ?_ ?_ r
  · exact ⟨1, 1, 1 + 1, mBeta_singleton 1, fun _ hj ↦ absurd hj (not_lt_zero_pam _),
      mBeta_singleton 1⟩
  · rintro r₀ ⟨y, c, d, h0, hstep, hr⟩
    obtain ⟨c', d', hprev, hlast⟩ := mBeta_snoc (r₀ + 1) c d (2 * y)
    refine ⟨2 * y, c', d', ?_, ?_, hlast⟩
    · rw [hprev 0 ⟨r₀, by ring⟩, h0]
    · intro j hj
      rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hj) with hjlt | rfl
      · rw [hprev (j + 1) (add_lt_add_right_pam hjlt 1),
          hprev j (lt_trans hjlt (lt_succ_self_pam r₀)), hstep j hjlt]
      · rw [hlast, hprev j (lt_succ_self_pam j), hr]

private theorem isPow2Seq_unique {c₁ d₁ r y₁ c₂ d₂ y₂ : PAM M}
    (h₁ : IsPow2Seq c₁ d₁ r y₁) (h₂ : IsPow2Seq c₂ d₂ r y₂) : y₁ = y₂ := by
  have hdef : PADef1 (fun j : PAM M ↦ j ≤ r → mBeta c₁ d₁ j = mBeta c₂ d₂ j) :=
    paDef_imp (paDef_le (paFun_proj 0) (paFun_const r))
      (paDef_eq
        (paFun_mBeta (paFun_const c₁) (paFun_const d₁) (paFun_proj 0))
        (paFun_mBeta (paFun_const c₂) (paFun_const d₂) (paFun_proj 0)))
  have hall := ind1 hdef (fun _ ↦ by rw [h₁.1, h₂.1]) (fun j ih hj1 ↦ ?_) r le_rfl
  · rw [← h₁.2.2, ← h₂.2.2, hall]
  · have hjlt : j < r := hj1
    rw [h₁.2.1 j hjlt, h₂.2.1 j hjlt, ih (le_of_lt hjlt)]

/-- Internal base-2 exponentiation $2^r$ on `PAM M`. -/
noncomputable def mPow2 (r : PAM M) : PAM M :=
  Classical.choose (exists_pow2Seq r)

private theorem exists_isPow2Seq_mPow2 (r : PAM M) : ∃ c d : PAM M, IsPow2Seq c d r (mPow2 r) :=
  Classical.choose_spec (exists_pow2Seq r)

theorem paFun_mPow2 {k : ℕ} {fr : (Fin k → PAM M) → PAM M} (hr : PAFunN k fr) :
    PAFunN k (fun a ↦ mPow2 (fr a)) := by
  have hseq : PADefN (k + 3) (fun b : Fin (k + 3) → PAM M ↦
      IsPow2Seq (b ⟨k + 1, by omega⟩) (b (Fin.last (k + 2)))
        (fr (Fin.init (Fin.init (Fin.init b)))) (b ⟨k, by omega⟩)) :=
    paDef_isPow2Seq
      (paFun_proj ⟨k + 1, by omega⟩)
      (paFun_proj (Fin.last (k + 2)))
      (paFun_weaken (paFun_weaken (paFun_weaken hr)))
      (paFun_proj ⟨k, by omega⟩)
  refine paDefN_congr (fun a ↦ ?_) (paDef_ex (paDef_ex hseq))
  constructor
  · rintro ⟨c, d, h⟩
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (by omega), fin_snoc_eq,
      fin_snoc_lt _ _ (by omega) (by omega), fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k)] at h
    obtain ⟨c₀, d₀, h₀⟩ := exists_isPow2Seq_mPow2 (fr (Fin.init a))
    exact isPow2Seq_unique h h₀
  · intro hy
    obtain ⟨c₀, d₀, h₀⟩ := exists_isPow2Seq_mPow2 (fr (Fin.init a))
    refine ⟨c₀, d₀, ?_⟩
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (by omega), fin_snoc_eq,
      fin_snoc_lt _ _ (by omega) (by omega), fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k)]
    change IsPow2Seq c₀ d₀ (fr (Fin.init a)) (a (Fin.last k))
    rwa [hy]

@[simp]
theorem mPow2_zero : mPow2 (0 : PAM M) = 1 := by
  obtain ⟨c, d, h⟩ := exists_isPow2Seq_mPow2 (0 : PAM M)
  exact h.2.2.symm.trans h.1

@[simp]
theorem mPow2_succ (r : PAM M) : mPow2 (r + 1) = 2 * mPow2 r := by
  obtain ⟨c, d, h0, hstep, hr⟩ := exists_isPow2Seq_mPow2 r
  obtain ⟨c', d', hprev, hlast⟩ := mBeta_snoc (r + 1) c d (2 * mPow2 r)
  have hseq : IsPow2Seq c' d' (r + 1) (2 * mPow2 r) := by
    refine ⟨?_, ?_, hlast⟩
    · rw [hprev 0 ⟨r, by ring⟩, h0]
    · intro j hj
      rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hj) with hjlt | rfl
      · rw [hprev (j + 1) (add_lt_add_right_pam hjlt 1),
          hprev j (lt_trans hjlt (lt_succ_self_pam r)), hstep j hjlt]
      · rw [hlast, hprev j (lt_succ_self_pam j), hr]
  obtain ⟨c₂, d₂, h₂⟩ := exists_isPow2Seq_mPow2 (r + 1)
  exact isPow2Seq_unique h₂ hseq

theorem mPow2_add (a b : PAM M) : mPow2 (a + b) = mPow2 a * mPow2 b := by
  have hdef : PADef1 (fun x : PAM M ↦ mPow2 (a + x) = mPow2 a * mPow2 x) :=
    paDef_eq
      (paFun_mPow2 (paFun_add (paFun_const a) (paFun_proj 0)))
      (paFun_mul (paFun_const (mPow2 a)) (paFun_mPow2 (paFun_proj 0)))
  refine ind1 hdef (by simp) (fun x ih ↦ ?_) b
  rw [← add_assoc, mPow2_succ, mPow2_succ, ih]
  ring

theorem one_le_mPow2 (r : PAM M) : 1 ≤ mPow2 r := by
  have hdef : PADef1 (fun x : PAM M ↦ 1 ≤ mPow2 x) :=
    paDef_le (paFun_const 1) (paFun_mPow2 (paFun_proj 0))
  refine ind1 hdef (by simp) (fun x ih ↦ ?_) r
  rw [mPow2_succ]
  rcases ih with ⟨k, hk⟩
  exact ⟨1 + 2 * k, by rw [← hk]; ring⟩

theorem mPow2_pos (r : PAM M) : 0 < mPow2 r :=
  lt_of_lt_of_le zero_lt_one_pam (one_le_mPow2 r)

@[simp]
theorem mPow2_natCast (n : ℕ) : mPow2 (n : PAM M) = ((2 ^ n : ℕ) : PAM M) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, mPow2_succ, ih, Nat.pow_succ]
    push_cast
    ring

/-- Unary `0`-block $0^r :: R = 2^r R$ on binary half-tape codes in `PAM M`. -/
noncomputable def mRep0 (r R : PAM M) : PAM M :=
  mPow2 r * R

/-- Unary `1`-block $1^r :: R = 2^r (R + 1) - 1$ on binary half-tape codes in `PAM M`. -/
noncomputable def mRep1 (r R : PAM M) : PAM M :=
  mPow2 r * R + (mPow2 r - 1)

theorem paFun_mRep0 {k : ℕ} {fr fR : (Fin k → PAM M) → PAM M}
    (hr : PAFunN k fr) (hR : PAFunN k fR) :
    PAFunN k (fun a ↦ mRep0 (fr a) (fR a)) :=
  paFun_mul (paFun_mPow2 hr) hR

theorem paFun_mRep1 {k : ℕ} {fr fR : (Fin k → PAM M) → PAM M}
    (hr : PAFunN k fr) (hR : PAFunN k fR) :
    PAFunN k (fun a ↦ mRep1 (fr a) (fR a)) :=
  paFun_add (paFun_mul (paFun_mPow2 hr) hR)
    (paFun_sub (paFun_mPow2 hr) (paFun_const 1))

@[simp]
theorem mRep0_zero (R : PAM M) : mRep0 0 R = R := by
  simp [mRep0]

theorem mRep0_succ (r R : PAM M) : mRep0 (r + 1) R = mCons 0 (mRep0 r R) := by
  simp only [mRep0, mPow2_succ, mCons, Fin.val_zero, Nat.cast_zero, add_zero]
  ring

theorem mRep0_mCons_zero (r R : PAM M) : mRep0 r (mCons 0 R) = mRep0 (r + 1) R := by
  simp only [mRep0, mPow2_succ, mCons, Fin.val_zero, Nat.cast_zero, add_zero]
  ring

theorem mRep0_add (a b R : PAM M) : mRep0 (a + b) R = mRep0 a (mRep0 b R) := by
  simp only [mRep0, mPow2_add]
  ring

@[simp]
theorem mRep1_zero (R : PAM M) : mRep1 0 R = R := by
  simp [mRep1]

private theorem mRep1_add_one (r R : PAM M) : mRep1 r R + 1 = mPow2 r * (R + 1) := by
  unfold mRep1
  have h1 := sub_add_cancel_pam (one_le_mPow2 r)
  calc mPow2 r * R + (mPow2 r - 1) + 1
    _ = mPow2 r * R + ((mPow2 r - 1) + 1) := by ring
    _ = mPow2 r * R + mPow2 r := by rw [h1]
    _ = mPow2 r * (R + 1) := by ring

theorem mRep1_succ (r R : PAM M) : mRep1 (r + 1) R = mCons 1 (mRep1 r R) := by
  apply (add_right_inj_pam 1).mp
  rw [mRep1_add_one, mPow2_succ]
  have h1 := mRep1_add_one r R
  calc 2 * mPow2 r * (R + 1)
    _ = 2 * (mPow2 r * (R + 1)) := by ring
    _ = 2 * (mRep1 r R + 1) := by rw [← h1]
    _ = (2 * mRep1 r R + 1) + 1 := by ring
    _ = mCons 1 (mRep1 r R) + 1 := by simp [mCons]

theorem mRep1_mCons_one (r R : PAM M) : mRep1 r (mCons 1 R) = mRep1 (r + 1) R := by
  apply (add_right_inj_pam 1).mp
  rw [mRep1_add_one, mRep1_add_one, mPow2_succ]
  simp only [mCons, Fin.val_one, Nat.cast_one]
  ring

theorem mRep1_add (a b R : PAM M) : mRep1 (a + b) R = mRep1 a (mRep1 b R) := by
  apply (add_right_inj_pam 1).mp
  rw [mRep1_add_one, mRep1_add_one, mRep1_add_one, mPow2_add]
  ring

end Model
end PAM





/-! ## Section 7: Internal Turing Machine Execution in `PAM M` -/

/-- Binary Turing machine configuration over `PAM M` half-tapes. -/
@[ext]
structure MCfg (states : ℕ) (M : Type*) where
  /-- Standard control state `Fin states`. -/
  state : Fin states
  /-- Standard head symbol `Fin 2`. -/
  head : Fin 2
  /-- Binary-encoded left half-tape in `PAM M`. -/
  left : PAM M
  /-- Binary-encoded non-head right half-tape in `PAM M`. -/
  right : PAM M

section Execution
variable {M : Type*} [PAStructure M] [PAModel M]
open PAM

/-- Nested Cantor configuration code `(q, (h, (L, R)))` of an `MCfg states M`. -/
noncomputable def mEncodeCfg {states : ℕ} (c : MCfg states M) : PAM M :=
  mPair (c.state.val : PAM M) (mPair (c.head.val : PAM M) (mPair c.left c.right))

theorem mEncodeCfg_injective {states : ℕ} {c₁ c₂ : MCfg states M}
    (h : mEncodeCfg c₁ = mEncodeCfg c₂) : c₁ = c₂ := by
  obtain ⟨hq, h1⟩ := mPair_injective h
  obtain ⟨hh, h2⟩ := mPair_injective h1
  obtain ⟨hl, hr⟩ := mPair_injective h2
  cases c₁
  cases c₂
  simp only [MCfg.mk.injEq]
  exact ⟨Fin.ext (natCast_inj_pam.mp hq), Fin.ext (natCast_inj_pam.mp hh), hl, hr⟩

/-- Blank initial configuration in `MCfg states M`. -/
def mInit {states : ℕ} [NeZero states] : MCfg states M :=
  ⟨0, 0, 0, 0⟩

@[simp]
theorem mEncodeCfg_mInit {states : ℕ} [NeZero states] :
    mEncodeCfg (mInit : MCfg states M) = 0 := by
  simp [mEncodeCfg, mInit]

/-- Single Turing machine step on `MCfg states M`. -/
noncomputable def mStep {states : ℕ} (tm : Machine states 2)
    (c : MCfg states M) : Option (MCfg states M) :=
  match tm.transition c.state c.head with
  | none => none
  | some (w, .right, q') =>
    some ⟨q', mBit c.right, mCons w c.left, mHalf c.right⟩
  | some (w, .left, q') =>
    some ⟨q', mBit c.left, mHalf c.left, mCons w c.right⟩

/-- Deterministically iterate `mStep tm` for `k : ℕ` standard steps. -/
noncomputable def mNSteps {states : ℕ} (tm : Machine states 2) :
    ℕ → MCfg states M → Option (MCfg states M)
  | 0, c => some c
  | k + 1, c => (mStep tm c).bind (mNSteps tm k)

theorem mNSteps_add {states : ℕ} (tm : Machine states 2) (j k : ℕ) (c : MCfg states M) :
    mNSteps tm (j + k) c = (mNSteps tm j c).bind (mNSteps tm k) := by
  induction j generalizing c with
  | zero => simp [mNSteps]
  | succ j ih =>
    simp only [Nat.succ_add, mNSteps]
    cases mStep tm c with
    | none => rfl
    | some c' => exact ih c'

private theorem pzPackCfg_evalPAM (v : ℕ → PAM M) (q h : ℕ) (L R : PAZFTerm) :
    evalPAZFTerm v (pzPackCfg q h L R) =
      mPair (q : PAM M) (mPair (h : PAM M) (mPair (evalPAZFTerm v L) (evalPAZFTerm v R))) :=
  rfl

omit [PAStructure M] [PAModel M] in
private theorem pzPackCfg_fresh_le (q h x y : ℕ) (hx : x < 10) (hy : y < 10) :
    (pzPackCfg q h (.var x) (.var y)).freshVar ≤ 10 := by
  simp only [pzPackCfg, PAZFTerm.freshVar]
  omega

private theorem paStep_holdsIn_iff {states : ℕ} (tm : Machine states 2) (v : ℕ → PAM M) :
    PAFormula.HoldsIn v (paStep tm) ↔
      ∃ c c' : MCfg states M,
        v 4 = mEncodeCfg c ∧ v 5 = mEncodeCfg c' ∧ mStep tm c = some c' := by
  unfold paStep
  rw [paDisjList_holdsIn_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨φ, ⟨q, _, h, _, hmem⟩, hholds⟩
    cases htr : tm.transition q h with
    | none => rw [htr] at hmem; cases hmem
    | some val =>
      rcases val with ⟨w, d, q'⟩
      cases d with
      | left =>
        rw [htr, List.mem_map] at hmem
        rcases hmem with ⟨h', hh'mem, rfl⟩
        have hh'lt : h' < 2 := by simp at hh'mem; omega
        let hFin : Fin 2 := ⟨h', hh'lt⟩
        simp only [PAFormula.HoldsIn] at hholds
        rcases hholds with ⟨n6, n7, n8, n9, hc_eq, hc'_eq, hn6, hn9⟩
        set v' := Function.update (Function.update
          (Function.update (Function.update v 6 n6) 7 n7) 8 n8) 9 n9
        have hv4 : v' 4 = v 4 := by simp [v']
        have hv5 : v' 5 = v 5 := by simp [v']
        have hv6 : v' 6 = n6 := by simp [v']
        have hv7 : v' 7 = n7 := by simp [v']
        have hv8 : v' 8 = n8 := by simp [v']
        have hv9 : v' 9 = n9 := by simp [v']
        have e1 := (eqFormula_holdsIn_iff _ (.var 4) 10 v'
          (pzPackCfg_fresh_le q.val h.val 6 7 (by decide) (by decide)) (by decide)).mp hc_eq
        have e2 := (eqFormula_holdsIn_iff _ (.var 5) 10 v'
          (pzPackCfg_fresh_le q'.val h' 8 9 (by decide) (by decide)) (by decide)).mp hc'_eq
        simp only [evalIn_var, evalIn_add, evalIn_mul, evalIn_ofNat, pzPackCfg_evalPAM,
          evalPAZFTerm, Nat.cast_ofNat, hv4, hv5, hv6, hv7, hv8, hv9] at e1 e2 hn6 hn9
        have hn6' : n6 = mCons hFin n8 := hn6
        have hn9' : n9 = mCons w n7 := hn9
        refine ⟨⟨q, h, n6, n7⟩, ⟨q', hFin, n8, n9⟩, e1, e2, ?_⟩
        simp [mStep, htr, hn6', hn9']
      | right =>
        rw [htr, List.mem_map] at hmem
        rcases hmem with ⟨h', hh'mem, rfl⟩
        have hh'lt : h' < 2 := by simp at hh'mem; omega
        let hFin : Fin 2 := ⟨h', hh'lt⟩
        simp only [PAFormula.HoldsIn] at hholds
        rcases hholds with ⟨n6, n7, n8, n9, hc_eq, hc'_eq, hn8, hn7⟩
        set v' := Function.update (Function.update
          (Function.update (Function.update v 6 n6) 7 n7) 8 n8) 9 n9
        have hv4 : v' 4 = v 4 := by simp [v']
        have hv5 : v' 5 = v 5 := by simp [v']
        have hv6 : v' 6 = n6 := by simp [v']
        have hv7 : v' 7 = n7 := by simp [v']
        have hv8 : v' 8 = n8 := by simp [v']
        have hv9 : v' 9 = n9 := by simp [v']
        have e1 := (eqFormula_holdsIn_iff _ (.var 4) 10 v'
          (pzPackCfg_fresh_le q.val h.val 6 7 (by decide) (by decide)) (by decide)).mp hc_eq
        have e2 := (eqFormula_holdsIn_iff _ (.var 5) 10 v'
          (pzPackCfg_fresh_le q'.val h' 8 9 (by decide) (by decide)) (by decide)).mp hc'_eq
        simp only [evalIn_var, evalIn_add, evalIn_mul, evalIn_ofNat, pzPackCfg_evalPAM,
          evalPAZFTerm, Nat.cast_ofNat, hv4, hv5, hv6, hv7, hv8, hv9] at e1 e2 hn8 hn7
        have hn8' : n8 = mCons w n6 := hn8
        have hn7' : n7 = mCons hFin n9 := hn7
        refine ⟨⟨q, h, n6, n7⟩, ⟨q', hFin, n8, n9⟩, e1, e2, ?_⟩
        simp [mStep, htr, hn8', hn7']
  · rintro ⟨⟨q, h, L, R⟩, c', hv4, hv5, hstep⟩
    dsimp only [mStep] at hstep
    cases htr : tm.transition q h with
    | none => simp [htr] at hstep
    | some val =>
      rcases val with ⟨w, d, q'⟩
      cases d with
      | left =>
        simp only [htr, Option.some.injEq] at hstep
        subst hstep
        let h' := (mBit L).val
        have hh'mem : h' ∈ ([0, 1] : List ℕ) := by
          have := (mBit L).isLt
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          omega
        let φ := PAFormula.ex 6 (.ex 7 (.ex 8 (.ex 9
          (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
            (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
              (.and (.eq (.var 6) (.add (.mul (.ofNat 2) (.var 8)) (.ofNat h')))
                (.eq (.var 9) (.add (.mul (.ofNat 2) (.var 7)) (.ofNat w.val)))))))))
        refine ⟨φ, ⟨q, List.mem_finRange q, h, List.mem_finRange h, ?_⟩, ?_⟩
        · rw [htr, List.mem_map]
          exact ⟨h', hh'mem, rfl⟩
        · simp only [φ, PAFormula.HoldsIn]
          refine ⟨L, R, mHalf L, mCons w R, ?_⟩
          set v' := Function.update (Function.update
            (Function.update (Function.update v 6 L) 7 R) 8 (mHalf L)) 9 (mCons w R)
          have hv4' : v' 4 = v 4 := by simp [v']
          have hv5' : v' 5 = v 5 := by simp [v']
          have hv6' : v' 6 = L := by simp [v']
          have hv7' : v' 7 = R := by simp [v']
          have hv8' : v' 8 = mHalf L := by simp [v']
          have hv9' : v' 9 = mCons w R := by simp [v']
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [eqFormula_holdsIn_iff _ (.var 4) 10 v'
              (pzPackCfg_fresh_le q.val h.val 6 7 (by decide) (by decide)) (by decide)]
            simp [pzPackCfg_evalPAM, evalPAZFTerm, hv4', hv6', hv7', hv4, mEncodeCfg]
          · rw [eqFormula_holdsIn_iff _ (.var 5) 10 v'
              (pzPackCfg_fresh_le q'.val h' 8 9 (by decide) (by decide)) (by decide)]
            simp [pzPackCfg_evalPAM, evalPAZFTerm, hv5', hv8', hv9', hv5, mEncodeCfg, h']
          · simp only [evalIn_var, evalIn_add, evalIn_mul, evalIn_ofNat, Nat.cast_ofNat,
              hv6', hv8', h']
            exact (mCons_mBit_mHalf L).symm
          · simp [hv7', hv9', mCons]
      | right =>
        simp only [htr, Option.some.injEq] at hstep
        subst hstep
        let h' := (mBit R).val
        have hh'mem : h' ∈ ([0, 1] : List ℕ) := by
          have := (mBit R).isLt
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          omega
        let φ := PAFormula.ex 6 (.ex 7 (.ex 8 (.ex 9
          (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
            (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
              (.and (.eq (.var 8) (.add (.mul (.ofNat 2) (.var 6)) (.ofNat w.val)))
                (.eq (.var 7) (.add (.mul (.ofNat 2) (.var 9)) (.ofNat h')))))))))
        refine ⟨φ, ⟨q, List.mem_finRange q, h, List.mem_finRange h, ?_⟩, ?_⟩
        · rw [htr, List.mem_map]
          exact ⟨h', hh'mem, rfl⟩
        · simp only [φ, PAFormula.HoldsIn]
          refine ⟨L, R, mCons w L, mHalf R, ?_⟩
          set v' := Function.update (Function.update
            (Function.update (Function.update v 6 L) 7 R) 8 (mCons w L)) 9 (mHalf R)
          have hv4' : v' 4 = v 4 := by simp [v']
          have hv5' : v' 5 = v 5 := by simp [v']
          have hv6' : v' 6 = L := by simp [v']
          have hv7' : v' 7 = R := by simp [v']
          have hv8' : v' 8 = mCons w L := by simp [v']
          have hv9' : v' 9 = mHalf R := by simp [v']
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [eqFormula_holdsIn_iff _ (.var 4) 10 v'
              (pzPackCfg_fresh_le q.val h.val 6 7 (by decide) (by decide)) (by decide)]
            simp [pzPackCfg_evalPAM, evalPAZFTerm, hv4', hv6', hv7', hv4, mEncodeCfg]
          · rw [eqFormula_holdsIn_iff _ (.var 5) 10 v'
              (pzPackCfg_fresh_le q'.val h' 8 9 (by decide) (by decide)) (by decide)]
            simp [pzPackCfg_evalPAM, evalPAZFTerm, hv5', hv8', hv9', hv5, mEncodeCfg, h']
          · simp [hv6', hv8', mCons]
          · simp only [evalIn_var, evalIn_add, evalIn_mul, evalIn_ofNat, Nat.cast_ofNat,
              hv7', hv9', h']
            exact (mCons_mBit_mHalf R).symm

private theorem paHalted_holdsIn_iff {states : ℕ} (tm : Machine states 2) (v : ℕ → PAM M) :
    PAFormula.HoldsIn v (paHalted tm) ↔
      ∃ c : MCfg states M, v 4 = mEncodeCfg c ∧ mStep tm c = none := by
  unfold paHalted
  rw [paDisjList_holdsIn_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨φ, ⟨q, _, h, _, hmem⟩, hholds⟩
    cases htr : tm.transition q h with
    | some _ => rw [htr] at hmem; cases hmem
    | none =>
      rw [htr, List.mem_singleton] at hmem
      subst hmem
      simp only [PAFormula.HoldsIn] at hholds
      rcases hholds with ⟨n6, n7, heq⟩
      set v' := Function.update (Function.update v 6 n6) 7 n7
      have e1 := (eqFormula_holdsIn_iff _ (.var 4) 10 v'
        (pzPackCfg_fresh_le q.val h.val 6 7 (by decide) (by decide)) (by decide)).mp heq
      have hv4 : v' 4 = v 4 := by simp [v']
      have hv6 : v' 6 = n6 := by simp [v']
      have hv7 : v' 7 = n7 := by simp [v']
      simp only [evalIn_var, pzPackCfg_evalPAM, evalPAZFTerm, hv4, hv6, hv7] at e1
      exact ⟨⟨q, h, n6, n7⟩, e1, by simp [mStep, htr]⟩
  · rintro ⟨⟨q, h, L, R⟩, hv4, hstep⟩
    dsimp only [mStep] at hstep
    cases htr : tm.transition q h with
    | some val =>
      rcases val with ⟨w, d, q'⟩
      cases d <;> simp [htr] at hstep
    | none =>
      let φ := PAFormula.ex 6
        (.ex 7 ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10))
      refine ⟨φ, ⟨q, List.mem_finRange q, h, List.mem_finRange h, ?_⟩, ?_⟩
      · simp [htr, φ]
      · simp only [φ, PAFormula.HoldsIn]
        refine ⟨L, R, ?_⟩
        set v' := Function.update (Function.update v 6 L) 7 R
        rw [eqFormula_holdsIn_iff _ (.var 4) 10 v'
          (pzPackCfg_fresh_le q.val h.val 6 7 (by decide) (by decide)) (by decide)]
        have hv4' : v' 4 = v 4 := by simp [v']
        have hv6' : v' 6 = L := by simp [v']
        have hv7' : v' 7 = R := by simp [v']
        simp [pzPackCfg_evalPAM, evalPAZFTerm, hv4', hv6', hv7', hv4, mEncodeCfg]

/-- A $\beta$-coded `n`-step `mStep` execution trace from `a` to `b` in `PAM M`. -/
def MValidTrace {states : ℕ} (tm : Machine states 2)
    (n c d : PAM M) (a b : MCfg states M) : Prop :=
  mBeta c d 0 = mEncodeCfg a ∧
  (∀ i < n, ∃ x y : MCfg states M,
    mBeta c d i = mEncodeCfg x ∧ mBeta c d (i + 1) = mEncodeCfg y ∧ mStep tm x = some y) ∧
  mBeta c d n = mEncodeCfg b

/-- Configuration `a` reaches `b` in `n : PAM M` steps of `tm` via a $\beta$-coded trace. -/
def mTracesTo {states : ℕ} (tm : Machine states 2)
    (n : PAM M) (a b : MCfg states M) : Prop :=
  ∃ c d : PAM M, MValidTrace tm n c d a b

/-- Machine `tm` halts from configuration `a` inside `PAM M`. -/
def mHaltsFrom {states : ℕ} (tm : Machine states 2) (a : MCfg states M) : Prop :=
  ∃ (n : PAM M) (f : MCfg states M), mTracesTo tm n a f ∧ mStep tm f = none

/-- Machine `tm` halts from the blank initial configuration `mInit` inside `PAM M`. -/
def mHalts (M : Type*) [PAStructure M] [PAModel M] {states : ℕ} [NeZero states]
    (tm : Machine states 2) : Prop :=
  mHaltsFrom tm (mInit : MCfg states M)

private theorem paDef_mStepCode {states : ℕ} (tm : Machine states 2) {k : ℕ}
    {fx fy : (Fin k → PAM M) → PAM M} (hx : PAFunN k fx) (hy : PAFunN k fy) :
    PADefN k (fun a ↦ ∃ x y : MCfg states M,
      fx a = mEncodeCfg x ∧ fy a = mEncodeCfg y ∧ mStep tm x = some y) := by
  have hbase : PADefN (k + 2) (fun b : Fin (k + 2) → PAM M ↦ ∃ x y : MCfg states M,
      b ⟨k, by omega⟩ = mEncodeCfg x ∧ b (Fin.last (k + 1)) = mEncodeCfg y ∧
        mStep tm x = some y) := by
    let σ : ℕ → ℕ := fun z ↦
      if z = 4 then k else if z = 5 then k + 1 else z + k + 2
    have hσ_inj : Function.Injective σ := by
      intro x y hxy
      dsimp only [σ] at hxy
      split_ifs at hxy <;> omega
    refine ⟨renameAllFormula σ (paStep tm), fun _ ↦ 0, fun b ↦ ?_⟩
    rw [holdsIn_renameAllFormula hσ_inj, paStep_holdsIn_iff]
    have h4 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 4 = b ⟨k, by omega⟩ :=
      paEnv_lt _ _ (by omega : k < k + 2)
    have h5 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 5 = b (Fin.last (k + 1)) :=
      paEnv_lt _ _ (Nat.lt_succ_self (k + 1))
    rw [h4, h5]
  have h1 := paDef_subst_last (paFun_weaken hy) hbase
  have h2 := paDef_subst_last hx h1
  refine paDefN_congr (fun a ↦ ?_) h2
  refine exists_congr fun x ↦ exists_congr fun y ↦ ?_
  rw [Fin.snoc_last, Fin.init_snoc, fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq]

theorem paDef_mHaltedCode {states : ℕ} (tm : Machine states 2) {k : ℕ}
    {fx : (Fin k → PAM M) → PAM M} (hx : PAFunN k fx) :
    PADefN k (fun a ↦ ∃ x : MCfg states M, fx a = mEncodeCfg x ∧ mStep tm x = none) := by
  have hbase : PADefN (k + 1) (fun b : Fin (k + 1) → PAM M ↦ ∃ x : MCfg states M,
      b (Fin.last k) = mEncodeCfg x ∧ mStep tm x = none) := by
    let σ : ℕ → ℕ := fun z ↦ if z = 4 then k else z + k + 1
    have hσ_inj : Function.Injective σ := by
      intro x y hxy
      dsimp only [σ] at hxy
      split_ifs at hxy <;> omega
    refine ⟨renameAllFormula σ (paHalted tm), fun _ ↦ 0, fun b ↦ ?_⟩
    rw [holdsIn_renameAllFormula hσ_inj, paHalted_holdsIn_iff]
    have h4 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 4 = b (Fin.last k) :=
      paEnv_lt _ _ (Nat.lt_succ_self k)
    rw [h4]
  refine paDefN_congr (fun a ↦ ?_) (paDef_subst_last hx hbase)
  simp only [Fin.snoc_last]

theorem paDef_mTracesToCode {states : ℕ} (tm : Machine states 2) {k : ℕ}
    {fn fa fb : (Fin k → PAM M) → PAM M}
    (hn : PAFunN k fn) (ha : PAFunN k fa) (hb : PAFunN k fb) :
    PADefN k (fun args ↦ ∃ a b : MCfg states M,
      fa args = mEncodeCfg a ∧ fb args = mEncodeCfg b ∧ mTracesTo tm (fn args) a b) := by
  have validCode : ∀ {m : ℕ} {f : (Fin m → PAM M) → PAM M}, PAFunN m f →
      PADefN m (fun u ↦ ∃ x : MCfg states M, f u = mEncodeCfg x) := by
    intro m f hf
    have hqh : ∀ (q : Fin states) (h : Fin 2),
        PADefN m (fun u ↦ ∃ L R : PAM M,
          f u = mPair (q.val : PAM M) (mPair (h.val : PAM M) (mPair L R))) := by
      intro q h
      have heq : PADefN (m + 2) (fun w : Fin (m + 2) → PAM M ↦
          f (Fin.init (Fin.init w)) =
            mPair (q.val : PAM M)
              (mPair (h.val : PAM M) (mPair (w ⟨m, by omega⟩) (w (Fin.last (m + 1)))))) :=
        paDef_eq (paFun_weaken (paFun_weaken hf))
          (paFun_mPair (paFun_const _)
            (paFun_mPair (paFun_const _)
              (paFun_mPair (paFun_proj ⟨m, by omega⟩) (paFun_proj (Fin.last (m + 1))))))
      refine paDefN_congr (fun u ↦ ?_) (paDef_ex (paDef_ex heq))
      refine exists_congr fun L ↦ exists_congr fun R ↦ ?_
      rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
        fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self m), fin_snoc_eq]
    refine paDefN_congr (fun u ↦ ?_)
      (paDef_fin_exists fun q ↦ paDef_fin_exists fun h ↦ hqh q h)
    constructor
    · rintro ⟨q, h, L, R, heq⟩
      exact ⟨⟨q, h, L, R⟩, heq⟩
    · rintro ⟨⟨q, h, L, R⟩, heq⟩
      exact ⟨q, h, L, R, heq⟩
  have hbody : PADefN (k + 2) (fun w : Fin (k + 2) → PAM M ↦
      mBeta (w ⟨k, by omega⟩) (w (Fin.last (k + 1))) 0 = fa (Fin.init (Fin.init w)) ∧
      (∀ i < fn (Fin.init (Fin.init w)), ∃ x y : MCfg states M,
        mBeta (w ⟨k, by omega⟩) (w (Fin.last (k + 1))) i = mEncodeCfg x ∧
        mBeta (w ⟨k, by omega⟩) (w (Fin.last (k + 1))) (i + 1) = mEncodeCfg y ∧
        mStep tm x = some y) ∧
      mBeta (w ⟨k, by omega⟩) (w (Fin.last (k + 1))) (fn (Fin.init (Fin.init w))) =
        fb (Fin.init (Fin.init w))) := by
    let fc : (Fin (k + 2) → PAM M) → PAM M := fun w ↦ w ⟨k, by omega⟩
    let fd : (Fin (k + 2) → PAM M) → PAM M := fun w ↦ w (Fin.last (k + 1))
    have hc : PAFunN (k + 2) fc := paFun_proj ⟨k, by omega⟩
    have hd : PAFunN (k + 2) fd := paFun_proj (Fin.last (k + 1))
    have hn2 : PAFunN (k + 2) (fun w ↦ fn (Fin.init (Fin.init w))) :=
      paFun_weaken (paFun_weaken hn)
    have ha2 : PAFunN (k + 2) (fun w ↦ fa (Fin.init (Fin.init w))) :=
      paFun_weaken (paFun_weaken ha)
    have hb2 : PAFunN (k + 2) (fun w ↦ fb (Fin.init (Fin.init w))) :=
      paFun_weaken (paFun_weaken hb)
    have h0 := paDef_eq (paFun_mBeta hc hd (paFun_const 0)) ha2
    have hlast := paDef_eq (paFun_mBeta hc hd hn2) hb2
    have hfor : PADefN (k + 2) (fun w ↦ ∀ i < fn (Fin.init (Fin.init w)),
        ∃ x y : MCfg states M,
          mBeta (fc w) (fd w) i = mEncodeCfg x ∧
          mBeta (fc w) (fd w) (i + 1) = mEncodeCfg y ∧ mStep tm x = some y) := by
      let fi : (Fin (k + 3) → PAM M) → PAM M := fun z ↦ z (Fin.last (k + 2))
      have hi : PAFunN (k + 3) fi := paFun_proj (Fin.last (k + 2))
      have hc3 := paFun_weaken hc
      have hd3 := paFun_weaken hd
      have hn3 := paFun_weaken hn2
      refine paDefN_congr (fun w ↦ ?_)
        (paDef_all (paDef_imp (paDef_lt hi hn3)
          (paDef_mStepCode tm
            (paFun_mBeta hc3 hd3 hi)
            (paFun_mBeta hc3 hd3 (paFun_add hi (paFun_const 1))))))
      simp only [fi, Fin.snoc_last, Fin.init_snoc]
    exact paDef_and h0 (paDef_and hfor hlast)
  refine paDefN_congr (fun args ↦ ?_)
    (paDef_and (validCode ha) (paDef_and (validCode hb) (paDef_ex (paDef_ex hbody))))
  constructor
  · rintro ⟨⟨a, ha_eq⟩, ⟨b, hb_eq⟩, c, d, h0, hfor, hlast⟩
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq] at h0 hfor hlast
    rw [ha_eq] at h0
    rw [hb_eq] at hlast
    exact ⟨a, b, ha_eq, hb_eq, c, d, h0, hfor, hlast⟩
  · rintro ⟨a, b, ha_eq, hb_eq, c, d, h0, hfor, hlast⟩
    refine ⟨⟨a, ha_eq⟩, ⟨b, hb_eq⟩, c, d, ?_⟩
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq]
    exact ⟨h0.trans ha_eq.symm, hfor, hlast.trans hb_eq.symm⟩

theorem paHalts_holdsIn_iff {states : ℕ} [NeZero states] (tm : Machine states 2)
    (v : ℕ → PAM M) :
    PAFormula.HoldsIn v (paHalts tm) ↔ mHalts M tm := by
  unfold paHalts mHalts mHaltsFrom mTracesTo MValidTrace
  simp only [PAFormula.HoldsIn]
  constructor
  · rintro ⟨n, c, d, h0, hsteps, hhalt⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    have hb0 : mBeta c d 0 = 0 := by
      have := (paBetaEq_holdsIn_iff v2 (.var 1) (.var 2) .zero .zero).mp h0
      simpa [v2] using this
    rcases hhalt with ⟨x4, hb_n, hhalted⟩
    set v4 := Function.update v2 4 x4
    have hx4 : mBeta c d n = x4 := by
      have := (paBetaEq_holdsIn_iff v4 (.var 1) (.var 2) (.var 0) (.var 4)).mp hb_n
      simpa [v4, v2] using this
    obtain ⟨f, hxf, hnone⟩ := (paHalted_holdsIn_iff tm v4).mp hhalted
    simp only [v4, Function.update_self] at hxf
    refine ⟨n, f, ⟨c, d, ?_, ?_, hx4.trans hxf⟩, hnone⟩
    · simpa [mEncodeCfg_mInit] using hb0
    · intro i hilt
      have hilt' : PAFormula.HoldsIn (Function.update v2 3 i) (paLt (.var 3) (.var 0)) := by
        rw [paLt_holdsIn_iff]
        simpa [v2] using hilt
      obtain ⟨y4, y5, hbi, hbi1, hst⟩ := hsteps i hilt'
      set v5 := Function.update (Function.update (Function.update v2 3 i) 4 y4) 5 y5
      have hy4 : mBeta c d i = y4 := by
        have := (paBetaEq_holdsIn_iff v5 (.var 1) (.var 2) (.var 3) (.var 4)).mp hbi
        simpa [v5, v2] using this
      have hy5 : mBeta c d (i + 1) = y5 := by
        have := (paBetaEq_holdsIn_iff v5 (.var 1) (.var 2) (.succ (.var 3)) (.var 5)).mp hbi1
        simpa [v5, v2] using this
      obtain ⟨x, y, hx, hy, hstep⟩ := (paStep_holdsIn_iff tm v5).mp hst
      simp only [v5, Function.update_self,
        Function.update_of_ne (by decide : (4 : ℕ) ≠ 5)] at hx hy
      exact ⟨x, y, hy4.trans hx, hy5.trans hy, hstep⟩
  · rintro ⟨n, f, ⟨c, d, h0, hsteps, hn⟩, hnone⟩
    refine ⟨n, c, d, ?_⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    refine ⟨?_, ?_, ?_⟩
    · rw [paBetaEq_holdsIn_iff]
      simpa [v2, mEncodeCfg_mInit] using h0
    · intro i hilt
      rw [paLt_holdsIn_iff] at hilt
      have hi_lt : i < n := by simpa [v2] using hilt
      obtain ⟨x, y, hx, hy, hstep⟩ := hsteps i hi_lt
      refine ⟨mEncodeCfg x, mEncodeCfg y, ?_⟩
      set v5 := Function.update (Function.update
        (Function.update v2 3 i) 4 (mEncodeCfg x)) 5 (mEncodeCfg y)
      refine ⟨?_, ?_, ?_⟩
      · rw [paBetaEq_holdsIn_iff]
        simpa [v5, v2] using hx
      · rw [paBetaEq_holdsIn_iff]
        simpa [v5, v2] using hy
      · rw [paStep_holdsIn_iff]
        exact ⟨x, y, by simp [v5], by simp [v5], hstep⟩
    · refine ⟨mEncodeCfg f, ?_⟩
      set v4 := Function.update v2 4 (mEncodeCfg f)
      refine ⟨?_, ?_⟩
      · rw [paBetaEq_holdsIn_iff]
        simpa [v4, v2] using hn
      · rw [paHalted_holdsIn_iff]
        exact ⟨f, by simp [v4], hnone⟩

theorem mTracesTo_zero {states : ℕ} (tm : Machine states 2) (a : MCfg states M) :
    mTracesTo tm 0 a a :=
  ⟨mEncodeCfg a, mEncodeCfg a + 1, mBeta_singleton _,
    fun _ hi ↦ absurd hi (not_lt_zero_pam _), mBeta_singleton _⟩

theorem mTracesTo_snoc {states : ℕ} {tm : Machine states 2} {n : PAM M} {a b c : MCfg states M}
    (htr : mTracesTo tm n a b) (hst : mStep tm b = some c) :
    mTracesTo tm (n + 1) a c := by
  rcases htr with ⟨c₀, d₀, h0, hsteps, hn⟩
  obtain ⟨c', d', hprev, hlast⟩ := mBeta_snoc (n + 1) c₀ d₀ (mEncodeCfg c)
  refine ⟨c', d', ?_, ?_, hlast⟩
  · rw [hprev 0 ⟨n, by ring⟩, h0]
  · intro i hi
    rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hi) with hilt | rfl
    · rw [hprev i (lt_trans hilt (lt_succ_self_pam n)),
        hprev (i + 1) (add_lt_add_right_pam hilt 1)]
      exact hsteps i hilt
    · rw [hprev i (lt_succ_self_pam i), hlast]
      exact ⟨b, c, hn, rfl, hst⟩

theorem mTracesTo_one {states : ℕ} {tm : Machine states 2} {a b : MCfg states M}
    (hst : mStep tm a = some b) : mTracesTo tm 1 a b := by
  simpa using mTracesTo_snoc (mTracesTo_zero tm a) hst

theorem mTracesTo_trans {states : ℕ} {tm : Machine states 2} {n₁ n₂ : PAM M}
    {a b c : MCfg states M} (h₁ : mTracesTo tm n₁ a b) (h₂ : mTracesTo tm n₂ b c) :
    mTracesTo tm (n₁ + n₂) a c := by
  rcases eq_zero_or_exists_succ n₂ with rfl | ⟨m₂, rfl⟩
  · rw [add_zero]
    rcases h₁ with ⟨c₁, d₁, ha₁, hst₁, hb₁⟩
    rcases h₂ with ⟨c₂, d₂, hb₂, _, hc₂⟩
    have hbc : b = c := mEncodeCfg_injective (hb₂.symm.trans hc₂)
    subst hbc
    exact ⟨c₁, d₁, ha₁, hst₁, hb₁⟩
  · rcases h₁ with ⟨c₁, d₁, ha₁, hst₁, hb₁⟩
    rcases h₂ with ⟨c₂, d₂, hb₂, hst₂, hc₂⟩
    obtain ⟨c', d', hleft, hright⟩ := mBeta_concat n₁ c₁ d₁ (m₂ + 1 + 1) c₂ d₂
    refine ⟨c', d', ?_, ?_, ?_⟩
    · rcases eq_zero_or_exists_succ n₁ with rfl | ⟨m₁, rfl⟩
      · have h0 := hright 0 ⟨m₂ + 1, by ring⟩
        rw [zero_add] at h0
        have hab : a = b := mEncodeCfg_injective (ha₁.symm.trans hb₁)
        subst hab
        exact h0.trans hb₂
      · exact (hleft 0 ⟨m₁, by ring⟩).trans ha₁
    · intro i hi
      rcases lt_or_ge i n₁ with hilt | hige
      · obtain ⟨x, y, hx, hy, hxy⟩ := hst₁ i hilt
        refine ⟨x, y, (hleft i hilt).trans hx, ?_, hxy⟩
        rcases lt_or_eq_of_le (show i + 1 ≤ n₁ from hilt) with hilt1 | hi1_eq
        · exact (hleft (i + 1) hilt1).trans hy
        · rw [hi1_eq] at hy ⊢
          have h0 := hright 0 ⟨m₂ + 1, by ring⟩
          rw [add_zero] at h0
          exact h0.trans (hb₂.trans (hb₁.symm.trans hy))
      · let j := i - n₁
        have hij : n₁ + j = i := add_sub_of_le_pam hige
        have hjlt : j < m₂ + 1 := by
          rcases hi with ⟨w, hw⟩
          exact ⟨w, (add_left_inj_pam n₁).mp (by
            calc n₁ + (j + 1 + w)
              _ = (n₁ + j) + 1 + w := by ring
              _ = i + 1 + w := by rw [hij]
              _ = n₁ + (m₂ + 1) := hw)⟩
        obtain ⟨x, y, hx, hy, hxy⟩ := hst₂ j hjlt
        refine ⟨x, y, ?_, ?_, hxy⟩
        · rw [← hij]
          exact (hright j (lt_trans hjlt (lt_succ_self_pam (m₂ + 1)))).trans hx
        · have hij1 : i + 1 = n₁ + (j + 1) := by rw [← hij]; ring
          rw [hij1]
          exact (hright (j + 1) (add_lt_add_right_pam hjlt 1)).trans hy
    · exact (hright (m₂ + 1) (lt_succ_self_pam (m₂ + 1))).trans hc₂

/-- Determinism of $\beta$-coded traces: any two valid traces from `a` agree at every common step
index. -/
theorem mValidTrace_agree {states : ℕ} {tm : Machine states 2}
    {n₁ c₁ d₁ n₂ c₂ d₂ : PAM M} {a b₁ b₂ : MCfg states M}
    (h₁ : MValidTrace tm n₁ c₁ d₁ a b₁) (h₂ : MValidTrace tm n₂ c₂ d₂ a b₂) :
    ∀ i : PAM M, i ≤ n₁ → i ≤ n₂ → mBeta c₁ d₁ i = mBeta c₂ d₂ i := by
  have hdef : PADef1 (fun i : PAM M ↦ i ≤ n₁ → i ≤ n₂ → mBeta c₁ d₁ i = mBeta c₂ d₂ i) :=
    paDef_imp (paDef_le (paFun_proj 0) (paFun_const n₁))
      (paDef_imp (paDef_le (paFun_proj 0) (paFun_const n₂))
        (paDef_eq
          (paFun_mBeta (paFun_const c₁) (paFun_const d₁) (paFun_proj 0))
          (paFun_mBeta (paFun_const c₂) (paFun_const d₂) (paFun_proj 0))))
  refine ind1 hdef (fun _ _ ↦ h₁.1.trans h₂.1.symm) (fun i ih hi1 hi2 ↦ ?_)
  have hilt1 : i < n₁ := hi1
  have hilt2 : i < n₂ := hi2
  have heq_i := ih (le_of_lt hilt1) (le_of_lt hilt2)
  obtain ⟨x₁, y₁, hx₁, hy₁, hst₁⟩ := h₁.2.1 i hilt1
  obtain ⟨x₂, y₂, hx₂, hy₂, hst₂⟩ := h₂.2.1 i hilt2
  have hx : x₁ = x₂ := mEncodeCfg_injective (hx₁.symm.trans (heq_i.trans hx₂))
  subst hx
  have hy : y₁ = y₂ := Option.some.inj (hst₁.symm.trans hst₂)
  subst hy
  exact hy₁.trans hy₂.symm

theorem mTracesTo_unique {states : ℕ} {tm : Machine states 2} {n : PAM M}
    {a b₁ b₂ : MCfg states M} (h₁ : mTracesTo tm n a b₁) (h₂ : mTracesTo tm n a b₂) :
    b₁ = b₂ := by
  rcases h₁ with ⟨c₁, d₁, hv₁⟩
  rcases h₂ with ⟨c₂, d₂, hv₂⟩
  have hag := mValidTrace_agree hv₁ hv₂ n le_rfl le_rfl
  exact mEncodeCfg_injective (hv₁.2.2.symm.trans (hag.trans hv₂.2.2))

/-- If `a` reaches `mid` in `k` steps, then `a` halts iff `mid` halts. -/
theorem mHaltsFrom_iff_of_mTracesTo {states : ℕ} {tm : Machine states 2}
    {k : PAM M} {a mid : MCfg states M} (hpre : mTracesTo tm k a mid) :
    mHaltsFrom tm a ↔ mHaltsFrom tm mid := by
  constructor
  · rintro ⟨N, f, htot, hnone⟩
    rcases hpre with ⟨c₁, d₁, hv₁⟩
    rcases htot with ⟨c₂, d₂, hv₂⟩
    have hk_le_N : k ≤ N := by
      by_contra hgt
      have hN_lt_k : N < k := lt_of_not_ge hgt
      have hag := mValidTrace_agree hv₁ hv₂ N (le_of_lt hN_lt_k) le_rfl
      obtain ⟨x, y, hx, _, hst⟩ := hv₁.2.1 N hN_lt_k
      have hxf : x = f := mEncodeCfg_injective (hx.symm.trans (hag.trans hv₂.2.2))
      subst hxf
      rw [hnone] at hst
      cases hst
    -- Extract suffix trace of length `N - k` from `mid` to `f`
    have hdef : PADef1 (fun m : PAM M ↦ m ≤ N - k →
        ∃ b : MCfg states M, mBeta c₂ d₂ (k + m) = mEncodeCfg b ∧ mTracesTo tm m mid b) := by
      have hm_le : PADefN 1 (fun u ↦ u 0 ≤ N - k) :=
        paDef_le (paFun_proj 0) (paFun_const (N - k))
      have htr : PADefN 1 (fun u ↦ ∃ a₀ b : MCfg states M,
          mEncodeCfg mid = mEncodeCfg a₀ ∧
          mBeta c₂ d₂ (k + u 0) = mEncodeCfg b ∧
          mTracesTo tm (u 0) a₀ b) :=
        paDef_mTracesToCode tm (paFun_proj 0) (paFun_const (mEncodeCfg mid))
          (paFun_mBeta (paFun_const c₂) (paFun_const d₂)
            (paFun_add (paFun_const k) (paFun_proj 0)))
      refine paDefN_congr (fun u ↦ ?_) (paDef_imp hm_le htr)
      refine imp_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨a₀, b, ha₀, hb, htr₀⟩
        rw [← mEncodeCfg_injective ha₀] at htr₀
        exact ⟨b, hb, htr₀⟩
      · rintro ⟨b, hb, htr₀⟩
        exact ⟨mid, b, rfl, hb, htr₀⟩
    have hsuf := ind1 hdef ?_ ?_ (N - k) le_rfl
    · obtain ⟨b, hb, htr_b⟩ := hsuf
      rw [add_sub_of_le_pam hk_le_N] at hb
      have hbf : b = f := mEncodeCfg_injective (hb.symm.trans hv₂.2.2)
      subst hbf
      exact ⟨N - k, b, htr_b, hnone⟩
    · intro _
      have hag := mValidTrace_agree hv₁ hv₂ k le_rfl hk_le_N
      exact ⟨mid, by rw [add_zero]; exact hag.symm.trans hv₁.2.2, mTracesTo_zero tm mid⟩
    · intro m ih hm1
      have hmlt : m < N - k := hm1
      obtain ⟨b, hb, htr_b⟩ := ih (le_of_lt hmlt)
      have hkm_lt : k + m < N := by
        have := add_lt_add_left_pam hmlt k
        rwa [add_sub_of_le_pam hk_le_N] at this
      obtain ⟨x, y, hx, hy, hst⟩ := hv₂.2.1 (k + m) hkm_lt
      have hxb : x = b := mEncodeCfg_injective (hx.symm.trans hb)
      subst hxb
      exact ⟨y, by rw [← add_assoc]; exact hy, mTracesTo_snoc htr_b hst⟩
  · rintro ⟨n', f, hsuf, hnone⟩
    exact ⟨k + n', f, mTracesTo_trans hpre hsuf, hnone⟩

theorem mTracesTo_of_mNSteps {states : ℕ} {tm : Machine states 2} :
    ∀ {k : ℕ} {a b : MCfg states M},
      mNSteps tm k a = some b → mTracesTo tm (k : PAM M) a b
  | 0, a, b, h => by
    simp only [mNSteps, Option.some.injEq] at h
    subst h
    simpa using mTracesTo_zero tm a
  | k + 1, a, b, h => by
    simp only [mNSteps, Option.bind_eq_some_iff] at h
    rcases h with ⟨mid, hst, hrest⟩
    have h1 := mTracesTo_one hst
    have h2 := mTracesTo_of_mNSteps hrest
    have htr := mTracesTo_trans h1 h2
    rw [show (1 : PAM M) + (k : PAM M) = ((k + 1 : ℕ) : PAM M) by push_cast; ring] at htr
    exact htr

/-- Embed a standard `ListBlank (Fin 2)` half-tape into `PAM M`. -/
def embedHalf (L : ListBlank (Fin 2)) : PAM M :=
  (encodeHalf L : PAM M)

/-- Embed a standard `Cfg states 2` configuration into `MCfg states M`. -/
def embedCfg {states : ℕ} (c : Cfg states 2) : MCfg states M :=
  ⟨c.state, c.tape.head, embedHalf c.tape.left, embedHalf c.tape.right⟩

@[simp]
theorem embedCfg_init {states : ℕ} [NeZero states] :
    embedCfg (init : Cfg states 2) = (mInit : MCfg states M) := by
  have henc0 : encodeListBin [] = 0 := rfl
  simp [embedCfg, embedHalf, mInit, init, Tape.mk₁, Tape.mk₂, Tape.mk', henc0]

theorem embedHalf_cons (L : ListBlank (Fin 2)) (a : Fin 2) :
    embedHalf (M := M) (L.cons a) = mCons a (embedHalf (M := M) L) := by
  unfold embedHalf mCons
  rw [encodeHalf_cons]
  push_cast
  rfl

theorem mBit_embedHalf (L : ListBlank (Fin 2)) : mBit (embedHalf (M := M) L) = L.head := by
  have h : embedHalf (M := M) L = mCons L.head (embedHalf (M := M) L.tail) := by
    unfold embedHalf mCons
    rw [encodeHalf_eq_tail_head]
    push_cast
    rfl
  rw [h, mBit_mCons]

theorem mHalf_embedHalf (L : ListBlank (Fin 2)) :
    mHalf (embedHalf (M := M) L) = embedHalf (M := M) L.tail := by
  have h : embedHalf (M := M) L = mCons L.head (embedHalf (M := M) L.tail) := by
    unfold embedHalf mCons
    rw [encodeHalf_eq_tail_head]
    push_cast
    rfl
  rw [h, mHalf_mCons]

private theorem mStep_embedCfg_some {states : ℕ} {tm : Machine states 2} {c c' : Cfg states 2}
    (h : step tm c = some c') :
    mStep tm (embedCfg (M := M) c) = some (embedCfg (M := M) c') := by
  rcases c with ⟨q, hd, L, R⟩
  simp only [step] at h
  cases htr : tm.transition q hd with
  | none => simp [htr] at h
  | some val =>
    rcases val with ⟨w, d, q'⟩
    rw [htr, Option.map_some, Option.some.injEq] at h
    subst h
    cases d <;>
      simp [embedCfg, mStep, htr, Tape.write, Tape.move,
        mBit_embedHalf, mHalf_embedHalf, embedHalf_cons]

theorem mTracesTo_of_nSteps {states : ℕ} [NeZero states] {tm : Machine states 2} :
    ∀ {k : ℕ} {c c' : Cfg states 2},
      nSteps tm k c = some c' →
      mTracesTo tm (k : PAM M) (embedCfg (M := M) c) (embedCfg (M := M) c')
  | 0, c, c', h => by
    simp only [ConjectureMachines.Semantics.Riemann.Layer1.nSteps_zero, Option.some.injEq] at h
    subst h
    simpa using mTracesTo_zero tm (embedCfg c)
  | k + 1, c, c', h => by
    simp only [ConjectureMachines.Semantics.Riemann.Layer1.nSteps_succ,
      Option.bind_eq_some_iff] at h
    rcases h with ⟨mid, hst, hrest⟩
    have h1 := mTracesTo_one (mStep_embedCfg_some (M := M) hst)
    have h2 := mTracesTo_of_nSteps hrest
    have htr := mTracesTo_trans h1 h2
    rw [show (1 : PAM M) + (k : PAM M) = ((k + 1 : ℕ) : PAM M) by push_cast; ring] at htr
    exact htr

end Execution

/-! ## Section 8: Internal `ZF` Formula Constructors and `paZFInconsistent` in `PAM M` -/

section ZFInternal
variable {M : Type*} [PAStructure M] [PAModel M]
open PAM

noncomputable def mZfEq (x y : PAM M) : PAM M := mPair (mPair x y) 0
noncomputable def mZfMem (x y : PAM M) : PAM M := mPair (mPair x y) 1
noncomputable def mZfImp (φ ψ : PAM M) : PAM M := mPair (mPair φ ψ) 2
noncomputable def mZfNot (φ : PAM M) : PAM M := mPair φ 3
noncomputable def mZfAll (x φ : PAM M) : PAM M := mPair (mPair x φ) 4
noncomputable def mZfEx (x φ : PAM M) : PAM M := mZfNot (mZfAll x (mZfNot φ))
noncomputable def mZfAnd (φ ψ : PAM M) : PAM M := mZfNot (mZfImp φ (mZfNot ψ))

noncomputable def mAxB1 (φ ψ χ : PAM M) : PAM M :=
  mZfImp (mZfImp φ ψ) (mZfImp (mZfImp ψ χ) (mZfImp φ χ))
noncomputable def mAxB2 (φ : PAM M) : PAM M := mZfImp (mZfImp (mZfNot φ) φ) φ
noncomputable def mAxB3 (φ ψ : PAM M) : PAM M := mZfImp φ (mZfImp (mZfNot φ) ψ)
noncomputable def mAxB4 (x φ ψ : PAM M) : PAM M :=
  mZfImp (mZfAll x (mZfImp φ ψ)) (mZfImp (mZfAll x φ) (mZfAll x ψ))
noncomputable def mAxB6a (x y z : PAM M) : PAM M :=
  mZfAnd (mZfImp (mZfEq x y) (mZfAll z (mZfEq x y)))
    (mZfImp (mZfMem x y) (mZfAll z (mZfMem x y)))
noncomputable def mAxB6b (x y φ : PAM M) : PAM M :=
  mZfImp (mZfAll x (mZfAll y φ)) (mZfAll y (mZfAll x φ))
noncomputable def mAxB6c (x φ : PAM M) : PAM M := mZfImp (mZfEx x (mZfAll x φ)) φ
noncomputable def mAxB7 (x y : PAM M) : PAM M := mZfEx x (mZfEq x y)
noncomputable def mAxB8a (x y z : PAM M) : PAM M :=
  mZfImp (mZfEq x y) (mZfImp (mZfEq x z) (mZfEq y z))
noncomputable def mAxB8b (x y z : PAM M) : PAM M :=
  mZfImp (mZfEq x y) (mZfImp (mZfMem x z) (mZfMem y z))
noncomputable def mAxB8c (x y z : PAM M) : PAM M :=
  mZfImp (mZfEq x y) (mZfImp (mZfMem z x) (mZfMem z y))

noncomputable def mAxExt : PAM M :=
  mZfImp
    (mZfAll 2 (mZfAnd (mZfImp (mZfMem 2 0) (mZfMem 2 1)) (mZfImp (mZfMem 2 1) (mZfMem 2 0))))
    (mZfEq 0 1)

noncomputable def mAxRepRhs (φ : PAM M) : PAM M :=
  mZfEx 3 (mZfAnd (mZfMem 3 0) (mZfAll 1 φ))

noncomputable def mAxRep (φ : PAM M) : PAM M :=
  mZfImp
    (mZfAll 3 (mZfEx 1 (mZfAll 2 (mZfImp (mZfAll 1 φ) (mZfEq 2 1)))))
    (mZfEx 1 (mZfAll 2
      (mZfAnd (mZfImp (mZfMem 2 1) (mAxRepRhs φ)) (mZfImp (mAxRepRhs φ) (mZfMem 2 1)))))

noncomputable def mAxPow : PAM M :=
  mZfEx 1 (mZfAll 2 (mZfImp (mZfAll 3 (mZfImp (mZfMem 3 2) (mZfMem 3 0))) (mZfMem 2 1)))

noncomputable def mAxUni : PAM M :=
  mZfEx 1 (mZfAll 2 (mZfImp (mZfEx 3 (mZfAnd (mZfMem 2 3) (mZfMem 3 0))) (mZfMem 2 1)))

noncomputable def mAxInfSingleton : PAM M :=
  mZfAll 1 (mZfAnd (mZfImp (mZfMem 1 2) (mZfEq 1 0)) (mZfImp (mZfEq 1 0) (mZfMem 1 2)))

noncomputable def mAxInf : PAM M :=
  mZfEx 1
    (mZfAnd (mZfMem 0 1)
      (mZfAll 0 (mZfImp (mZfMem 0 1) (mZfEx 2 (mZfAnd (mZfMem 2 1) mAxInfSingleton)))))

@[simp]
theorem mZfMem_zero_zero : mZfMem (0 : PAM M) 0 = 1 := by
  have h : mZfMem (0 : PAM M) 0 = mZfMem ((0 : ℕ) : PAM M) ((0 : ℕ) : PAM M) := rfl
  simp only [mZfMem, mPair_zero_zero]
  have h1 : mPair ((0 : ℕ) : PAM M) ((1 : ℕ) : PAM M) = (cantorPair 0 1 : PAM M) :=
    mPair_natCast 0 1
  have hc : cantorPair 0 1 = 1 := rfl
  rw [hc] at h1
  simpa using h1

private theorem pzEq_evalPAM (v : ℕ → PAM M) (x y : PAZFTerm) :
    evalPAZFTerm v (pzEq x y) = mZfEq (evalPAZFTerm v x) (evalPAZFTerm v y) := by
  simp [pzEq, mZfEq, evalPAZFTerm]
private theorem pzMem_evalPAM (v : ℕ → PAM M) (x y : PAZFTerm) :
    evalPAZFTerm v (pzMem x y) = mZfMem (evalPAZFTerm v x) (evalPAZFTerm v y) := by
  simp [pzMem, mZfMem, evalPAZFTerm]
private theorem pzImp_evalPAM (v : ℕ → PAM M) (φ ψ : PAZFTerm) :
    evalPAZFTerm v (pzImp φ ψ) = mZfImp (evalPAZFTerm v φ) (evalPAZFTerm v ψ) := by
  simp [pzImp, mZfImp, evalPAZFTerm]
private theorem pzNot_evalPAM (v : ℕ → PAM M) (φ : PAZFTerm) :
    evalPAZFTerm v (pzNot φ) = mZfNot (evalPAZFTerm v φ) := by
  simp [pzNot, mZfNot, evalPAZFTerm]
private theorem pzAll_evalPAM (v : ℕ → PAM M) (x φ : PAZFTerm) :
    evalPAZFTerm v (pzAll x φ) = mZfAll (evalPAZFTerm v x) (evalPAZFTerm v φ) := by
  simp [pzAll, mZfAll, evalPAZFTerm]
private theorem pzEx_evalPAM (v : ℕ → PAM M) (x φ : PAZFTerm) :
    evalPAZFTerm v (pzEx x φ) = mZfEx (evalPAZFTerm v x) (evalPAZFTerm v φ) := by
  simp [pzEx, mZfEx, pzNot_evalPAM, pzAll_evalPAM]
private theorem pzAnd_evalPAM (v : ℕ → PAM M) (φ ψ : PAZFTerm) :
    evalPAZFTerm v (pzAnd φ ψ) = mZfAnd (evalPAZFTerm v φ) (evalPAZFTerm v ψ) := by
  simp [pzAnd, mZfAnd, pzNot_evalPAM, pzImp_evalPAM]

private theorem pzB1_evalPAM (v : ℕ → PAM M) (φ ψ χ : PAZFTerm) :
    evalPAZFTerm v (pzB1 φ ψ χ) =
      mAxB1 (evalPAZFTerm v φ) (evalPAZFTerm v ψ) (evalPAZFTerm v χ) := by
  simp only [pzB1, mAxB1, pzImp_evalPAM]
private theorem pzB2_evalPAM (v : ℕ → PAM M) (φ : PAZFTerm) :
    evalPAZFTerm v (pzB2 φ) = mAxB2 (evalPAZFTerm v φ) := by
  simp only [pzB2, mAxB2, pzImp_evalPAM, pzNot_evalPAM]
private theorem pzB3_evalPAM (v : ℕ → PAM M) (φ ψ : PAZFTerm) :
    evalPAZFTerm v (pzB3 φ ψ) = mAxB3 (evalPAZFTerm v φ) (evalPAZFTerm v ψ) := by
  simp only [pzB3, mAxB3, pzImp_evalPAM, pzNot_evalPAM]
private theorem pzB4_evalPAM (v : ℕ → PAM M) (x φ ψ : PAZFTerm) :
    evalPAZFTerm v (pzB4 x φ ψ) =
      mAxB4 (evalPAZFTerm v x) (evalPAZFTerm v φ) (evalPAZFTerm v ψ) := by
  simp only [pzB4, mAxB4, pzImp_evalPAM, pzAll_evalPAM]
private theorem pzB6a_evalPAM (v : ℕ → PAM M) (x y z : PAZFTerm) :
    evalPAZFTerm v (pzB6a x y z) =
      mAxB6a (evalPAZFTerm v x) (evalPAZFTerm v y) (evalPAZFTerm v z) := by
  simp only [pzB6a, mAxB6a, pzAnd_evalPAM, pzImp_evalPAM, pzAll_evalPAM, pzEq_evalPAM,
    pzMem_evalPAM]
private theorem pzB6b_evalPAM (v : ℕ → PAM M) (x y φ : PAZFTerm) :
    evalPAZFTerm v (pzB6b x y φ) =
      mAxB6b (evalPAZFTerm v x) (evalPAZFTerm v y) (evalPAZFTerm v φ) := by
  simp only [pzB6b, mAxB6b, pzImp_evalPAM, pzAll_evalPAM]
private theorem pzB6c_evalPAM (v : ℕ → PAM M) (x φ : PAZFTerm) :
    evalPAZFTerm v (pzB6c x φ) = mAxB6c (evalPAZFTerm v x) (evalPAZFTerm v φ) := by
  simp only [pzB6c, mAxB6c, pzImp_evalPAM, pzEx_evalPAM, pzAll_evalPAM]
private theorem pzB7_evalPAM (v : ℕ → PAM M) (x y : PAZFTerm) :
    evalPAZFTerm v (pzB7 x y) = mAxB7 (evalPAZFTerm v x) (evalPAZFTerm v y) := by
  simp only [pzB7, mAxB7, pzEx_evalPAM, pzEq_evalPAM]
private theorem pzB8a_evalPAM (v : ℕ → PAM M) (x y z : PAZFTerm) :
    evalPAZFTerm v (pzB8a x y z) =
      mAxB8a (evalPAZFTerm v x) (evalPAZFTerm v y) (evalPAZFTerm v z) := by
  simp only [pzB8a, mAxB8a, pzImp_evalPAM, pzEq_evalPAM]
private theorem pzB8b_evalPAM (v : ℕ → PAM M) (x y z : PAZFTerm) :
    evalPAZFTerm v (pzB8b x y z) =
      mAxB8b (evalPAZFTerm v x) (evalPAZFTerm v y) (evalPAZFTerm v z) := by
  simp only [pzB8b, mAxB8b, pzImp_evalPAM, pzEq_evalPAM, pzMem_evalPAM]
private theorem pzB8c_evalPAM (v : ℕ → PAM M) (x y z : PAZFTerm) :
    evalPAZFTerm v (pzB8c x y z) =
      mAxB8c (evalPAZFTerm v x) (evalPAZFTerm v y) (evalPAZFTerm v z) := by
  simp only [pzB8c, mAxB8c, pzImp_evalPAM, pzEq_evalPAM, pzMem_evalPAM]
private theorem pzExt_evalPAM (v : ℕ → PAM M) : evalPAZFTerm v pzExt = mAxExt := by
  simp only [pzExt, mAxExt, pzImp_evalPAM, pzAll_evalPAM, pzAnd_evalPAM, pzMem_evalPAM,
    pzEq_evalPAM, evalPAZFTerm, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
private theorem pzRep_evalPAM (v : ℕ → PAM M) (φ : PAZFTerm) :
    evalPAZFTerm v (pzRep φ) = mAxRep (evalPAZFTerm v φ) := by
  simp only [pzRep, pzRepRhs, mAxRep, mAxRepRhs, pzImp_evalPAM, pzAll_evalPAM, pzEx_evalPAM,
    pzAnd_evalPAM, pzMem_evalPAM, pzEq_evalPAM, evalPAZFTerm, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
private theorem pzPow_evalPAM (v : ℕ → PAM M) : evalPAZFTerm v pzPow = mAxPow := by
  simp only [pzPow, mAxPow, pzEx_evalPAM, pzAll_evalPAM, pzImp_evalPAM, pzMem_evalPAM,
    evalPAZFTerm, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
private theorem pzUni_evalPAM (v : ℕ → PAM M) : evalPAZFTerm v pzUni = mAxUni := by
  simp only [pzUni, mAxUni, pzEx_evalPAM, pzAll_evalPAM, pzImp_evalPAM, pzAnd_evalPAM,
    pzMem_evalPAM, evalPAZFTerm, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
private theorem pzInf_evalPAM (v : ℕ → PAM M) : evalPAZFTerm v pzInf = mAxInf := by
  simp only [pzInf, pzInfSingleton, mAxInf, mAxInfSingleton, pzEx_evalPAM, pzAnd_evalPAM,
    pzAll_evalPAM, pzImp_evalPAM, pzMem_evalPAM, pzEq_evalPAM, evalPAZFTerm, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat]

/-- Whether `w : PAM M` is an axiom instance of `ZFProvable` inside `PAM M`. -/
def MIsZFAxiom (w : PAM M) : Prop :=
  w = mZfEq 0 0 ∨
  (∃ φ ψ χ : PAM M, w = mAxB1 φ ψ χ) ∨
  (∃ φ : PAM M, w = mAxB2 φ) ∨
  (∃ φ ψ : PAM M, w = mAxB3 φ ψ) ∨
  (∃ x φ ψ : PAM M, w = mAxB4 x φ ψ) ∨
  (∃ x y z : PAM M, x ≠ z ∧ z ≠ y ∧ w = mAxB6a x y z) ∨
  (∃ x y φ : PAM M, w = mAxB6b x y φ) ∨
  (∃ x φ : PAM M, w = mAxB6c x φ) ∨
  (∃ x y : PAM M, w = mAxB7 x y) ∨
  (∃ x y z : PAM M, w = mAxB8a x y z) ∨
  (∃ x y z : PAM M, w = mAxB8b x y z) ∨
  (∃ x y z : PAM M, w = mAxB8c x y z) ∨
  w = mAxExt ∨
  (∃ φ : PAM M, w = mAxRep φ) ∨
  w = mAxPow ∨
  w = mAxUni ∨
  w = mAxInf

/-- Validity of step `i` (formula `w`) in a $\beta$-coded `ZF` derivation `(c, d)` in `PAM M`. -/
def MIsZFStep (c d i w : PAM M) : Prop :=
  MIsZFAxiom w ∨
  (∃ φ χ j₁ j₂ : PAM M, j₁ < i ∧ j₂ < i ∧
    mBeta c d j₁ = φ ∧ mBeta c d j₂ = χ ∧ χ = mZfImp φ w) ∨
  (∃ x φ j : PAM M, j < i ∧ mBeta c d j = φ ∧ w = mZfAll x φ)

/-- Semantic `paZFInconsistent` witness in `PAM M`. -/
def MZFInconsistent (M : Type*) [PAStructure M] [PAModel M] : Prop :=
  ∃ n c d : PAM M,
    (∀ i ≤ n, MIsZFStep c d i (mBeta c d i)) ∧
    mBeta c d n = mZfMem 0 0

private theorem paIsZFStep_holdsIn_iff (v : ℕ → PAM M) :
    PAFormula.HoldsIn v paIsZFStep ↔ MIsZFStep (v 1) (v 2) (v 3) (v 4) := by
  unfold paIsZFStep MIsZFStep MIsZFAxiom
  rw [paDisjList_holdsIn_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  have eq_iff : ∀ (e : PAZFTerm) (out : PATerm) (u : ℕ → PAM M),
      e.freshVar ≤ 10 → out.freshVar ≤ 10 →
      (PAFormula.HoldsIn u (e.eqFormula out 10) ↔ PATerm.evalIn u out = evalPAZFTerm u e) :=
    fun e out u he ho ↦ eqFormula_holdsIn_iff e out 10 u he ho
  constructor
  · rintro (h0 | hmp | hgen | hb1 | hb2 | hb3 | hb4 | hb6a | hb6b | hb6c | hb7 |
      hb8a | hb8b | hb8c | hext | hrep | hpow | huni | hinf)
    · rw [eq_iff _ _ _ (by decide) (by decide)] at h0
      exact Or.inl (Or.inl (by simpa [pzEq_evalPAM, evalPAZFTerm] using h0))
    · simp only [PAFormula.HoldsIn] at hmp
      rcases hmp with ⟨n5, n6, n8, n9, h8, h9, hb8, hb9, himp⟩
      set u := Function.update (Function.update
        (Function.update (Function.update v 5 n5) 6 n6) 8 n8) 9 n9
      rw [paLt_holdsIn_iff] at h8 h9
      rw [paBetaEq_holdsIn_iff] at hb8 hb9
      rw [eq_iff _ _ _ (by decide) (by decide)] at himp
      refine Or.inr (Or.inl ⟨n5, n6, n8, n9, ?_, ?_, ?_, ?_, ?_⟩)
      · simpa [u] using h8
      · simpa [u] using h9
      · simpa [u] using hb8
      · simpa [u] using hb9
      · simpa [u, pzImp_evalPAM, evalPAZFTerm] using himp
    · simp only [PAFormula.HoldsIn] at hgen
      rcases hgen with ⟨n5, n6, n8, h8, hb8, hall⟩
      set u := Function.update (Function.update (Function.update v 5 n5) 6 n6) 8 n8
      rw [paLt_holdsIn_iff] at h8
      rw [paBetaEq_holdsIn_iff] at hb8
      rw [eq_iff _ _ _ (by decide) (by decide)] at hall
      refine Or.inr (Or.inr ⟨n5, n6, n8, ?_, ?_, ?_⟩)
      · simpa [u] using h8
      · simpa [u] using hb8
      · simpa [u, pzAll_evalPAM, evalPAZFTerm] using hall
    · simp only [PAFormula.HoldsIn] at hb1
      rcases hb1 with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inl ⟨n5, n6, n7,
        by simpa [pzB1_evalPAM, evalPAZFTerm] using h⟩))
    · simp only [PAFormula.HoldsIn] at hb2
      rcases hb2 with ⟨n5, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨n5,
        by simpa [pzB2_evalPAM, evalPAZFTerm] using h⟩)))
    · simp only [PAFormula.HoldsIn] at hb3
      rcases hb3 with ⟨n5, n6, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6,
        by simpa [pzB3_evalPAM, evalPAZFTerm] using h⟩))))
    · simp only [PAFormula.HoldsIn] at hb4
      rcases hb4 with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6, n7,
        by simpa [pzB4_evalPAM, evalPAZFTerm] using h⟩)))))
    · simp only [PAFormula.HoldsIn] at hb6a
      rcases hb6a with ⟨n5, n6, n7, hne1, hne2, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n5, n6, n7, by simpa using hne1, by simpa using hne2,
          by simpa [pzB6a_evalPAM, evalPAZFTerm] using h⟩))))))
    · simp only [PAFormula.HoldsIn] at hb6b
      rcases hb6b with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6, n7,
        by simpa [pzB6b_evalPAM, evalPAZFTerm] using h⟩)))))))
    · simp only [PAFormula.HoldsIn] at hb6c
      rcases hb6c with ⟨n5, n6, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6,
        by simpa [pzB6c_evalPAM, evalPAZFTerm] using h⟩))))))))
    · simp only [PAFormula.HoldsIn] at hb7
      rcases hb7 with ⟨n5, n6, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n5, n6, by simpa [pzB7_evalPAM, evalPAZFTerm] using h⟩)))))))))
    · simp only [PAFormula.HoldsIn] at hb8a
      rcases hb8a with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨n5, n6, n7, by simpa [pzB8a_evalPAM, evalPAZFTerm] using h⟩))))))))))
    · simp only [PAFormula.HoldsIn] at hb8b
      rcases hb8b with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨n5, n6, n7,
          by simpa [pzB8b_evalPAM, evalPAZFTerm] using h⟩)))))))))))
    · simp only [PAFormula.HoldsIn] at hb8c
      rcases hb8c with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨n5, n6, n7,
          by simpa [pzB8c_evalPAM, evalPAZFTerm] using h⟩))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at hext
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl
          (by simpa [pzExt_evalPAM] using hext))))))))))))))
    · simp only [PAFormula.HoldsIn] at hrep
      rcases hrep with ⟨n5, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5,
          by simpa [pzRep_evalPAM, evalPAZFTerm] using h⟩))))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at hpow
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by simpa [pzPow_evalPAM] using hpow))))))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at huni
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by simpa [pzUni_evalPAM] using huni)))))))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at hinf
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by simpa [pzInf_evalPAM] using hinf)))))))))))))))))
  · rintro (hax | ⟨φ, χ, j₁, j₂, hj₁, hj₂, hb₁, hb₂, hχ⟩ | ⟨x, φ, j, hj, hbj, hall⟩)
    · rcases hax with h0 | ⟨a, b, c, h⟩ | ⟨a, h⟩ | ⟨a, b, h⟩ | ⟨a, b, c, h⟩ |
        ⟨a, b, c, hac, hcb, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, h⟩ | ⟨a, b, h⟩ |
        ⟨a, b, c, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, c, h⟩ | hext | ⟨a, h⟩ | hpow | huni | hinf
      · refine Or.inl ?_
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzEq_evalPAM, evalPAZFTerm] using h0
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩)))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB1_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ?_⟩))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB2_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ?_⟩)))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB3_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB4_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨a, b, c, ?_, ?_, ?_⟩)))))))
        · simpa [PAFormula.HoldsIn] using hac
        · simpa [PAFormula.HoldsIn] using hcb
        · rw [eq_iff _ _ _ (by decide) (by decide)]
          simpa [pzB6a_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨a, b, c, ?_⟩))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB6b_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨a, b, ?_⟩)))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB6c_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl ⟨a, b, ?_⟩))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB7_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩)))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB8a_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB8b_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩)))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzB8c_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzExt_evalPAM] using hext
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ?_⟩)))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzRep_evalPAM, evalPAZFTerm] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ?_))))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzPow_evalPAM] using hpow
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ?_)))))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzUni_evalPAM] using huni
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr ?_)))))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzInf_evalPAM] using hinf
    · refine Or.inr (Or.inl ⟨φ, χ, j₁, j₂, ?_, ?_, ?_, ?_, ?_⟩)
      · rw [paLt_holdsIn_iff]; simpa using hj₁
      · rw [paLt_holdsIn_iff]; simpa using hj₂
      · rw [paBetaEq_holdsIn_iff]; simpa using hb₁
      · rw [paBetaEq_holdsIn_iff]; simpa using hb₂
      · rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzImp_evalPAM, evalPAZFTerm] using hχ
    · refine Or.inr (Or.inr (Or.inl ⟨x, φ, j, ?_, ?_, ?_⟩))
      · rw [paLt_holdsIn_iff]; simpa using hj
      · rw [paBetaEq_holdsIn_iff]; simpa using hbj
      · rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [pzAll_evalPAM, evalPAZFTerm] using hall

theorem paDef_mIsZFStep {k : ℕ} {fc fd fi fw : (Fin k → PAM M) → PAM M}
    (hc : PAFunN k fc) (hd : PAFunN k fd) (hi : PAFunN k fi) (hw : PAFunN k fw) :
    PADefN k (fun a ↦ MIsZFStep (fc a) (fd a) (fi a) (fw a)) := by
  have hbase : PADefN (k + 4) (fun b : Fin (k + 4) → PAM M ↦
      MIsZFStep (b ⟨k, by omega⟩) (b ⟨k + 1, by omega⟩)
        (b ⟨k + 2, by omega⟩) (b (Fin.last (k + 3)))) := by
    let σ : ℕ → ℕ := fun z ↦
      if z = 1 then k
      else if z = 2 then k + 1
      else if z = 3 then k + 2
      else if z = 4 then k + 3
      else z + k + 4
    have hσ_inj : Function.Injective σ := by
      intro x y hxy
      dsimp only [σ] at hxy
      split_ifs at hxy <;> omega
    refine ⟨renameAllFormula σ paIsZFStep, fun _ ↦ 0, fun b ↦ ?_⟩
    rw [holdsIn_renameAllFormula hσ_inj, paIsZFStep_holdsIn_iff]
    have h1 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 1 = b ⟨k, by omega⟩ :=
      paEnv_lt _ _ (by omega : k < k + 4)
    have h2 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 2 = b ⟨k + 1, by omega⟩ :=
      paEnv_lt _ _ (by omega : k + 1 < k + 4)
    have h3 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 3 = b ⟨k + 2, by omega⟩ :=
      paEnv_lt _ _ (by omega : k + 2 < k + 4)
    have h4 : (paEnv (fun _ ↦ (0 : PAM M)) b ∘ σ) 4 = b (Fin.last (k + 3)) :=
      paEnv_lt _ _ (Nat.lt_succ_self (k + 3))
    rw [h1, h2, h3, h4]
  have s1 := paDef_subst_last (paFun_weaken (paFun_weaken (paFun_weaken hw))) hbase
  have s2 := paDef_subst_last (paFun_weaken (paFun_weaken hi)) s1
  have s3 := paDef_subst_last (paFun_weaken hd) s2
  have s4 := paDef_subst_last hc s3
  refine paDefN_congr (fun a ↦ ?_) s4
  simp only [Fin.snoc_last, Fin.init_snoc]
  rw [fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_eq,
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_eq,
    fin_snoc_lt _ _ (by omega) (by omega),
    fin_snoc_eq]

theorem paZFInconsistent_holdsIn_iff (v : ℕ → PAM M) :
    PAFormula.HoldsIn v paZFInconsistent ↔ MZFInconsistent M := by
  unfold paZFInconsistent MZFInconsistent
  simp only [PAFormula.HoldsIn]
  constructor
  · rintro ⟨n, c, d, hsteps, hfinal⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    rcases hfinal with ⟨w, hbw, hmem⟩
    set v4 := Function.update v2 4 w
    have hw_eq : mBeta c d n = w := by
      have := (paBetaEq_holdsIn_iff v4 (.var 1) (.var 2) (.var 0) (.var 4)).mp hbw
      simpa [v4, v2] using this
    have hw_mem : w = mZfMem 0 0 := by
      have := (eqFormula_holdsIn_iff (pzMem (.const 0) (.const 0)) (.var 4) 10 v4
        (by decide) (by decide)).mp hmem
      simpa [v4, pzMem_evalPAM, evalPAZFTerm] using this
    refine ⟨n, c, d, ?_, hw_eq.trans hw_mem⟩
    intro i hle
    have hle' : PAFormula.HoldsIn (Function.update v2 3 i) (paLe (.var 3) (.var 0)) := by
      rw [paLe_holdsIn_iff]
      simpa [v2] using hle
    obtain ⟨wi, hbwi, hst⟩ := hsteps i hle'
    set u4 := Function.update (Function.update v2 3 i) 4 wi
    have hwi_eq : mBeta c d i = wi := by
      have := (paBetaEq_holdsIn_iff u4 (.var 1) (.var 2) (.var 3) (.var 4)).mp hbwi
      simpa [u4, v2] using this
    have hst' := (paIsZFStep_holdsIn_iff u4).mp hst
    simp only [u4, v2, Function.update_self,
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (1 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (1 : ℕ) ≠ 3),
      Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
      Function.update_of_ne (by decide : (2 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)] at hst'
    rwa [hwi_eq]
  · rintro ⟨n, c, d, hsteps, hfinal⟩
    refine ⟨n, c, d, ?_⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    refine ⟨?_, ?_⟩
    · intro i hle
      rw [paLe_holdsIn_iff] at hle
      have hi_le : i ≤ n := by simpa [v2] using hle
      refine ⟨mBeta c d i, ?_⟩
      set u4 := Function.update (Function.update v2 3 i) 4 (mBeta c d i)
      refine ⟨?_, ?_⟩
      · rw [paBetaEq_holdsIn_iff]
        simp [u4, v2]
      · rw [paIsZFStep_holdsIn_iff]
        simpa [u4, v2] using hsteps i hi_le
    · refine ⟨mZfMem 0 0, ?_⟩
      set v4 := Function.update v2 4 (mZfMem 0 0)
      refine ⟨?_, ?_⟩
      · rw [paBetaEq_holdsIn_iff]
        simpa [v4, v2] using hfinal
      · rw [eqFormula_holdsIn_iff _ (.var 4) 10 v4 (by decide) (by decide)]
        simp [v4, pzMem_evalPAM, evalPAZFTerm]

end ZFInternal

end ConjectureMachines.Semantics.PA
