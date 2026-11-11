module

public import BusyBeaver.Basic
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.PairStack


-- ============================================================================
-- Section 1: Tape & List Algebra Helpers
-- ============================================================================

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

theorem pow_zero_list (u : List (Fin 2)) : u ^ (0 : Nat) = [] := rfl
theorem pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
theorem nil_append_list (l : List (Fin 2)) : ([] : List (Fin 2)) ++ l = l := rfl
theorem cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
theorem append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l

attribute [scoped simp]
  pow_zero_list
  pow_succ_list
  nil_append_list
  cons_append_list
  append_nil_list
  listblank_append_nil
  listblank_append_cons
  zero_cons_default
  ListBlank.head_default
  ListBlank.tail_default

omit [Inhabited Γ] in
theorem list_pow_add (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m :=
  BusyBeaver.list_pow_add l n m

theorem listblank_append_right_assoc (l₁ l₂ : List Γ) (s : ListBlank Γ) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, ListBlank.append, ih]

theorem listblank_eq_one_cons_tail {Z : ListBlank (Fin 2)} (hZ : Z.head = 1) :
    Z = (1 : Fin 2) >> Z.tail := by
  rw [← hZ, Turing.ListBlank.cons_head_tail]

@[simp] theorem zeros_append_default (n : ℕ) :
    (([0] : List (Fin 2)) ^ n) +> (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons,
      ih, zero_cons_default]

-- ============================================================================
-- Section 2: Universal Stack Combinators
-- ============================================================================

/-- Increment the primary coordinate of the top stack element (or push `(0, 0)` if empty). -/
def bumpHead : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: L => (a + 1, b) :: L

/-- Increment the primary coordinate of the top stack element `n` times. -/
def bumpN : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, L => L
  | n + 1, L => bumpHead (bumpN n L)

/-- Ensure a stack is non-empty by appending `(0, 0)` if empty. -/
def ensureNonEmpty : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | p :: R => p :: R

@[simp] theorem bumpN_zero (L : List (ℕ × ℕ)) : bumpN 0 L = L := rfl
@[simp] theorem bumpN_succ (n : ℕ) (L : List (ℕ × ℕ)) :
    bumpN (n + 1) L = bumpHead (bumpN n L) := rfl

theorem bumpHead_ne_nil (L : List (ℕ × ℕ)) : bumpHead L ≠ [] := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩ <;> simp [bumpHead]

theorem bumpN_succ_ne_nil (n : ℕ) (L : List (ℕ × ℕ)) : bumpN (n + 1) L ≠ [] := by
  simp only [bumpN_succ]; exact bumpHead_ne_nil (bumpN n L)

theorem ensureNonEmpty_ne_nil (R : List (ℕ × ℕ)) : ensureNonEmpty R ≠ [] := by
  rcases R with _ | ⟨p, R'⟩ <;> simp [ensureNonEmpty]

-- ============================================================================
-- Section 3: Parametric Stack Encodings
-- ============================================================================

/-- Generic parametric left stack encoding:
    `encLeft ((a, b) :: L) =
      encLeft L <+ (sSym ^ (sep + b % maxSep)) <+ (dSym ^ (stride * a + offset))`. -/
def encLeftParam (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ) :
    List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L =>
    (encLeftParam dSym sSym stride offset sep maxSep L <+
      (([sSym] : List (Fin 2)) ^ (sep + b % maxSep))) <+
        (([dSym] : List (Fin 2)) ^ (stride * a + offset))

/-- Generic parametric right stack encoding:
    `encRight ((d, b) :: R) =
      (dSym ^ (stride * d + offset)) +> ((sSym ^ (sep + b % maxSep)) +> encRight R)`. -/
def encRightParam (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ) :
    List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R =>
    (([dSym] : List (Fin 2)) ^ (stride * d + offset)) +>
      ((([sSym] : List (Fin 2)) ^ (sep + b % maxSep)) +>
        encRightParam dSym sSym stride offset sep maxSep R)

@[simp] theorem encLeftParam_nil (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ) :
    encLeftParam dSym sSym stride offset sep maxSep [] = default := rfl

@[simp] theorem encRightParam_nil (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ) :
    encRightParam dSym sSym stride offset sep maxSep [] = default := rfl

@[simp] theorem encLeftParam_cons (dSym sSym : Fin 2) (stride offset sep maxSep a b : ℕ)
    (L : List (ℕ × ℕ)) :
    encLeftParam dSym sSym stride offset sep maxSep ((a, b) :: L) =
      (encLeftParam dSym sSym stride offset sep maxSep L <+
        (([sSym] : List (Fin 2)) ^ (sep + b % maxSep))) <+
          (([dSym] : List (Fin 2)) ^ (stride * a + offset)) := rfl

@[simp] theorem encRightParam_cons (dSym sSym : Fin 2) (stride offset sep maxSep d b : ℕ)
    (R : List (ℕ × ℕ)) :
    encRightParam dSym sSym stride offset sep maxSep ((d, b) :: R) =
      (([dSym] : List (Fin 2)) ^ (stride * d + offset)) +>
        ((([sSym] : List (Fin 2)) ^ (sep + b % maxSep)) +>
          encRightParam dSym sSym stride offset sep maxSep R) := rfl

-- ============================================================================
-- Section 4: Head & Successor Theorems
-- ============================================================================

theorem encLeftParam_head (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (h_offset : offset > 0) (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeftParam dSym sSym stride offset sep maxSep ((a, b) :: L)).head = dSym := by
  obtain ⟨off', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_offset)
  rw [encLeftParam_cons, show stride * a + (off' + 1) = (stride * a + off') + 1 by omega,
      pow_succ_list, cons_append_list]
  simp only [listblank_append_cons, Turing.ListBlank.head_cons]

theorem encRightParam_head (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (h_offset : offset > 0) (d b : ℕ) (R : List (ℕ × ℕ)) :
    (encRightParam dSym sSym stride offset sep maxSep ((d, b) :: R)).head = dSym := by
  obtain ⟨off', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_offset)
  rw [encRightParam_cons, show stride * d + (off' + 1) = (stride * d + off') + 1 by omega,
      pow_succ_list, cons_append_list]
  simp only [listblank_append_cons, Turing.ListBlank.head_cons]

theorem encLeftParam_succ (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeftParam dSym sSym stride offset sep maxSep ((a + 1, b) :: L) =
      (([dSym] : List (Fin 2)) ^ stride) +>
        encLeftParam dSym sSym stride offset sep maxSep ((a, b) :: L) := by
  simp only [encLeftParam_cons]
  rw [show stride * (a + 1) + offset = stride + (stride * a + offset) by ring,
      list_pow_add, listblank_append_right_assoc]

theorem encRightParam_succ (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRightParam dSym sSym stride offset sep maxSep ((d + 1, b) :: R) =
      (([dSym] : List (Fin 2)) ^ stride) +>
        encRightParam dSym sSym stride offset sep maxSep ((d, b) :: R) := by
  simp only [encRightParam_cons]
  rw [show stride * (d + 1) + offset = stride + (stride * d + offset) by ring,
      list_pow_add, listblank_append_right_assoc]

theorem encLeftParam_cons_dSym (dSym : Fin 2) (sep maxSep : ℕ)
    (L : List (ℕ × ℕ)) :
    dSym >> encLeftParam dSym 0 1 1 sep maxSep L =
      encLeftParam dSym 0 1 1 sep maxSep (bumpHead L) := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · simp [bumpHead, encLeftParam, zeros_append_default]
  · have h := encLeftParam_succ dSym 0 1 1 sep maxSep a b L'
    simp only [show (([dSym] : List (Fin 2)) ^ 1) = [dSym] by rfl,
               listblank_append_cons, listblank_append_nil] at h
    exact h.symm

theorem encRightParam_cons_dSym (dSym : Fin 2) (sep maxSep : ℕ)
    (R : List (ℕ × ℕ)) :
    dSym >> encRightParam dSym 0 1 1 sep maxSep R =
      encRightParam dSym 0 1 1 sep maxSep (bumpHead R) := by
  rcases R with _ | ⟨⟨d, b⟩, R'⟩
  · simp [bumpHead, encRightParam, zeros_append_default]
  · have h := encRightParam_succ dSym 0 1 1 sep maxSep d b R'
    simp only [show (([dSym] : List (Fin 2)) ^ 1) = [dSym] by rfl,
               listblank_append_cons, listblank_append_nil] at h
    exact h.symm

theorem encLeftParam_bumpN (dSym : Fin 2) (sep maxSep : ℕ)
    (n : ℕ) (L : List (ℕ × ℕ)) :
    (([dSym] : List (Fin 2)) ^ n) +> encLeftParam dSym 0 1 1 sep maxSep L =
      encLeftParam dSym 0 1 1 sep maxSep (bumpN n L) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_list, cons_append_list, nil_append_list,
               listblank_append_cons, ih, bumpN, encLeftParam_cons_dSym]

theorem encRightParam_bumpN (dSym : Fin 2) (sep maxSep : ℕ)
    (n : ℕ) (R : List (ℕ × ℕ)) :
    (([dSym] : List (Fin 2)) ^ n) +> encRightParam dSym 0 1 1 sep maxSep R =
      encRightParam dSym 0 1 1 sep maxSep (bumpN n R) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_list, cons_append_list, nil_append_list,
               listblank_append_cons, ih, bumpN, encRightParam_cons_dSym]

-- ============================================================================
-- Section 5: Modulo & Canonical Shorthands
-- ============================================================================

theorem mod2_cases (b : ℕ) : b % 2 = 0 ∨ b % 2 = 1 := by omega
theorem mod3_cases (b : ℕ) : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
theorem mod4_cases (b : ℕ) : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega

theorem encLeftParam_mod (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeftParam dSym sSym stride offset sep maxSep ((a, b) :: L) =
      encLeftParam dSym sSym stride offset sep maxSep ((a, b % maxSep) :: L) := by
  simp only [encLeftParam_cons, Nat.mod_mod]

theorem encRightParam_mod (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRightParam dSym sSym stride offset sep maxSep ((d, b) :: R) =
      encRightParam dSym sSym stride offset sep maxSep ((d, b % maxSep) :: R) := by
  simp only [encRightParam_cons, Nat.mod_mod]

-- ============================================================================
-- Section 6: Normalization & AllSep Predicates
-- ============================================================================

/-- Normalize a stack by reducing second coordinates modulo `maxSep`. -/
def normStack (maxSep : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) :=
  List.map (fun p => (p.1, p.2 % maxSep))

/-- Predicate: every element's secondary coordinate is strictly bounded by `maxSep`. -/
def AllSep (maxSep : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ L, p.2 < maxSep

theorem encLeftParam_norm (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (L : List (ℕ × ℕ)) :
    encLeftParam dSym sSym stride offset sep maxSep (normStack maxSep L) =
      encLeftParam dSym sSym stride offset sep maxSep L := by
  induction L with
  | nil => rfl
  | cons p L' ih =>
    rcases p with ⟨a, b⟩
    change encLeftParam dSym sSym stride offset sep maxSep
      ((a, b % maxSep) :: normStack maxSep L') =
      encLeftParam dSym sSym stride offset sep maxSep ((a, b) :: L')
    simp only [encLeftParam_cons, Nat.mod_mod, ih]

theorem encRightParam_norm (dSym sSym : Fin 2) (stride offset sep maxSep : ℕ)
    (R : List (ℕ × ℕ)) :
    encRightParam dSym sSym stride offset sep maxSep (normStack maxSep R) =
      encRightParam dSym sSym stride offset sep maxSep R := by
  induction R with
  | nil => rfl
  | cons p R' ih =>
    rcases p with ⟨d, b⟩
    change encRightParam dSym sSym stride offset sep maxSep
      ((d, b % maxSep) :: normStack maxSep R') =
      encRightParam dSym sSym stride offset sep maxSep ((d, b) :: R')
    simp only [encRightParam_cons, Nat.mod_mod, ih]

theorem allSep_normStack (maxSep : ℕ) (h_pos : maxSep > 0) (L : List (ℕ × ℕ)) :
    AllSep maxSep (normStack maxSep L) := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, _, rfl⟩
  exact Nat.mod_lt q.2 h_pos

-- ============================================================================
-- Section 7: View Combinators
-- ============================================================================

theorem applyView_id_nil (s : ListBlank Γ) :
    applyView (.id []) s = s :=
  rfl

theorem applyView_id_cons (x : Γ) (xs : List Γ) (s : ListBlank Γ) :
    applyView (.id (x :: xs)) s = (x :: xs) +> s :=
  rfl

theorem applyView_tail_nil (s : ListBlank Γ) :
    applyView (.tail []) s = s.tail :=
  rfl

theorem applyView_tail_cons (x : Γ) (xs : List Γ) (s : ListBlank Γ) :
    applyView (.tail (x :: xs)) s = (x :: xs) +> s.tail :=
  rfl

theorem applyView_tail_one (enc : List (ℕ × ℕ) → ListBlank (Fin 2))
    (h_head : ∀ d b R, (enc ((d, b) :: R)).head = 1)
    (h_nil : applyView (.tail [1]) (enc []) = enc (ensureNonEmpty []))
    (R : List (ℕ × ℕ)) :
    applyView (.tail [1]) (enc R) = enc (ensureNonEmpty R) := by
  rcases R with _ | ⟨⟨d, b⟩, R'⟩
  · exact h_nil
  · simp only [applyView, listblank_append_cons, listblank_append_nil, ensureNonEmpty]
    exact (listblank_eq_one_cons_tail (h_head d b R')).symm

theorem applyView_tail_zero_one (enc : List (ℕ × ℕ) → ListBlank (Fin 2))
    (h_head : ∀ d b R, (enc ((d, b) :: R)).head = 1)
    (h_nil : applyView (.tail [0, 1]) (enc []) = (0 : Fin 2) >> enc (ensureNonEmpty []))
    (R : List (ℕ × ℕ)) :
    applyView (.tail [0, 1]) (enc R) = (0 : Fin 2) >> enc (ensureNonEmpty R) := by
  rcases R with _ | ⟨⟨d, b⟩, R'⟩
  · exact h_nil
  · simp only [applyView, listblank_append_cons, listblank_append_nil, ensureNonEmpty]
    exact congrArg (ListBlank.cons 0) (listblank_eq_one_cons_tail (h_head d b R')).symm

theorem applyView_tail_one_one (enc : List (ℕ × ℕ) → ListBlank (Fin 2))
    (h_head : ∀ d b R, (enc ((d, b) :: R)).head = 1)
    (h_nil : applyView (.tail [1, 1]) (enc []) = (1 : Fin 2) >> enc (ensureNonEmpty []))
    (R : List (ℕ × ℕ)) :
    applyView (.tail [1, 1]) (enc R) = (1 : Fin 2) >> enc (ensureNonEmpty R) := by
  rcases R with _ | ⟨⟨d, b⟩, R'⟩
  · exact h_nil
  · simp only [applyView, listblank_append_cons, listblank_append_nil, ensureNonEmpty]
    exact congrArg (ListBlank.cons 1) (listblank_eq_one_cons_tail (h_head d b R')).symm

-- ============================================================================
-- Section 8: Block Encoding Audit Helper
-- ============================================================================

theorem blockEncodingParam
    (strideL offsetL sepL maxSepL strideR offsetR sepR maxSepR : ℕ)
    (h_sL : strideL > 0) (h_oL : offsetL > 0) (h_sepL : sepL > 0)
    (h_m1L : 1 ≤ maxSepL) (h_m2L : maxSepL ≤ 4)
    (h_sR : strideR > 0) (h_oR : offsetR > 0) (h_sepR : sepR > 0)
    (h_m1R : 1 ≤ maxSepR) (h_m2R : maxSepR ≤ 4)
    (dSym sSym : Fin 2) :
    ∃ strideL' offsetL' sepL' maxSepL' strideR' offsetR' sepR' maxSepR' : ℕ,
      strideL' > 0 ∧ offsetL' > 0 ∧ sepL' > 0 ∧ 1 ≤ maxSepL' ∧ maxSepL' ≤ 4 ∧
      strideR' > 0 ∧ offsetR' > 0 ∧ sepR' > 0 ∧ 1 ≤ maxSepR' ∧ maxSepR' ≤ 4 ∧
      (∀ a (b : StackTuple 1) L, encLeftParam dSym sSym strideL offsetL sepL maxSepL ((a, b) :: L) =
        (encLeftParam dSym sSym strideL offsetL sepL maxSepL L <+
          (([sSym] : List (Fin 2)) ^ (stackSepLen sepL' maxSepL' b))) <+
            (([dSym] : List (Fin 2)) ^ (strideL' * a + offsetL'))) ∧
      (∀ d (b : StackTuple 1) R,
        encRightParam dSym sSym strideR offsetR sepR maxSepR ((d, b) :: R) =
        (([dSym] : List (Fin 2)) ^ (strideR' * d + offsetR')) +>
          ((([sSym] : List (Fin 2)) ^ (stackSepLen sepR' maxSepR' b)) +>
            encRightParam dSym sSym strideR offsetR sepR maxSepR R)) :=
  ⟨strideL, offsetL, sepL, maxSepL, strideR, offsetR, sepR, maxSepR,
   h_sL, h_oL, h_sepL, h_m1L, h_m2L,
   h_sR, h_oR, h_sepR, h_m1R, h_m2R,
   fun _ _ _ => rfl, fun _ _ _ => rfl⟩

-- ============================================================================
-- Section 9: 1-Digit Stack Lift Infrastructure
-- ============================================================================

/-- Lift a 1-digit stack `List ℕ` to a 2-digit stack `List (ℕ × ℕ)` by appending `0` second
    components. -/
def liftPairList : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs => (x, 0) :: liftPairList xs

@[simp] theorem map_fst_liftPairList : ∀ L1 : List ℕ, (liftPairList L1).map Prod.fst = L1
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (map_fst_liftPairList xs)

/-- Canonical proposition package for 1-digit stack cryptids on 2-symbol machines (`Fin 2`). -/
def OneDigitStackCryptidProp {Λ : Type*} [Inhabited Λ]
    (target_tm : Machine (Fin 2) Λ)
    (StackMode : Type)
    (encLeft1 encRight1 : List ℕ → ListBlank (Fin 2))
    (evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) Λ)
    (IsInStackSystem1 : Cfg (Fin 2) Λ → Prop) : Prop :=
  encLeft1 [] = default ∧
  encRight1 [] = default ∧
  (∀ a L, (encLeft1 (a :: L)).head = (1 : Fin 2)) ∧
  (∀ d R, (encRight1 (d :: R)).head = (1 : Fin 2)) ∧
  (∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ L : List ℕ, encLeft1 L ≠ t) ∧
  (∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ R : List ℕ, encRight1 R ≠ t) ∧
  (∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
    strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
    strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
    (∀ a L, encLeft1 (a :: L) = (encLeft1 L <+ (([0] : List (Fin 2)) ^ sepL)) <+
      (([1] : List (Fin 2)) ^ (strideL * a + offsetL))) ∧
    (∀ d R, encRight1 (d :: R) = (([1] : List (Fin 2)) ^ (strideR * d + offsetR)) +>
      ((([0] : List (Fin 2)) ^ sepR) +> encRight1 R))) ∧
  (∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes) ∧
  IsValidStackModes encLeft1 encRight1 evalStackCfg1 ∧
  (∀ cfg, IsInStackSystem1 cfg ↔ ∃ m L R, cfg = evalStackCfg1 m L R) ∧
  (∀ m L R, IsInStackSystem1 (evalStackCfg1 m L R)) ∧
  (∃ cfg₀, ((init []) [target_tm]⊢⁺ cfg₀) ∧ IsInStackSystem1 cfg₀) ∧
  (∀ cfg, IsInStackSystem1 cfg →
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem1 cfg' ∨ (step target_tm cfg').isNone))

/-- Universal lift theorem from 1-digit stack cryptid to 2-digit `IsStackCryptid`. -/
theorem lift_one_digit_prop {Λ : Type*} [Inhabited Λ]
    (target_tm : Machine (Fin 2) Λ)
    (StackMode : Type)
    (encLeft1 encRight1 : List ℕ → ListBlank (Fin 2))
    (evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) Λ)
    (IsInStackSystem1 : Cfg (Fin 2) Λ → Prop)
    (h : OneDigitStackCryptidProp target_tm StackMode encLeft1 encRight1
      evalStackCfg1 IsInStackSystem1) :
    IsStackCryptid target_tm := by
  refine ⟨StackMode, 1, 0,
    fun (L : List (ℕ × ℕ)) => encLeft1 (L.map Prod.fst),
    fun (R : List (ℕ × ℕ)) => encRight1 (R.map Prod.fst),
    fun (m : StackMode) (L R : List (ℕ × ℕ)) =>
      evalStackCfg1 m (L.map Prod.fst) (R.map Prod.fst),
    fun (cfg : Cfg (Fin 2) Λ) => ∃ (m : StackMode) (L R : List (ℕ × ℕ)),
      cfg = evalStackCfg1 m (L.map Prod.fst) (R.map Prod.fst),
    ?_⟩
  rcases h with ⟨hnilL, hnilR, hheadL, hheadR, ⟨tL, htL, hnsL⟩, ⟨tR, htR, hnsR⟩,
    ⟨sL, oL, sepL, sR, oR, sepR, hsL, hoL, hsepL, hsR, hoR, hsepR, hblkL, hblkR⟩,
    hmodes, hvalid1, hiff1, _, ⟨cfg₀, hinit0, hsys0⟩, hclosed1⟩
  refine ⟨Or.inl ⟨rfl, rfl⟩, hnilL, hnilR,
    fun a _ L => hheadL a (L.map Prod.fst),
    fun d _ R => hheadR d (R.map Prod.fst),
    ⟨tL, htL, fun L => hnsL (L.map Prod.fst)⟩,
    ⟨tR, htR, fun R => hnsR (R.map Prod.fst)⟩,
    ⟨sL, oL, sepL, 1, sR, oR, sepR, 1,
      hsL, hoL, hsepL, le_refl 1, by decide,
      hsR, hoR, hsepR, le_refl 1, by decide,
      fun a b L => by simpa [Nat.mod_one] using hblkL a (L.map Prod.fst),
      fun d b R => by simpa [Nat.mod_one] using hblkR d (R.map Prod.fst)⟩,
    hmodes,
    fun m => ?_,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    ?_,
    ?_⟩
  · rcases hvalid1 m with ⟨q, vL, vR, hl, hr, h1 | h2 | h3⟩
    · exact ⟨q, vL, vR, hl, hr, Or.inl (fun L R => h1 (L.map Prod.fst) (R.map Prod.fst))⟩
    · exact ⟨q, vL, vR, hl, hr, Or.inr (Or.inl (fun L R => h2 (L.map Prod.fst) (R.map Prod.fst)))⟩
    · exact ⟨q, vL, vR, hl, hr, Or.inr (Or.inr (fun L R => h3 (L.map Prod.fst) (R.map Prod.fst)))⟩
  · rcases (hiff1 cfg₀).mp hsys0 with ⟨m, L1, R1, hcfg0⟩
    refine ⟨cfg₀, hinit0, m, liftPairList L1, liftPairList R1, ?_⟩
    try dsimp
    rw [map_fst_liftPairList, map_fst_liftPairList]
    exact hcfg0
  · intro cfg ⟨m, L, R, hcfg⟩
    have hsys1 : IsInStackSystem1 cfg := (hiff1 cfg).mpr ⟨m, L.map Prod.fst, R.map Prod.fst, hcfg⟩
    rcases hclosed1 cfg hsys1 with ⟨cfg', hstep, hnext | hhalt⟩
    · rcases (hiff1 cfg').mp hnext with ⟨m', L1', R1', hcfg'⟩
      refine ⟨cfg', hstep, Or.inl ⟨m', liftPairList L1', liftPairList R1', ?_⟩⟩
      try dsimp
      rw [map_fst_liftPairList, map_fst_liftPairList]
      exact hcfg'
    · exact ⟨cfg', hstep, Or.inr hhalt⟩

end BusyBeaver.PairStack
