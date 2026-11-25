/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Stack

/-!
# Busy Beaver Holdout `1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA` (#543)

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA` (bbchallenge holdout #543).
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LDHHH_0LB1LA

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => none
  | 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.left)

private theorem target_eq_target_tm : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl


private def A : Fin 6 := 0
private def B : Fin 6 := 1
private def C : Fin 6 := 2
private def D : Fin 6 := 3
private def E : Fin 6 := 4
private def F : Fin 6 := 5

open BusyBeaver.PairStack Counter

local macro "normalize" : tactic => `(tactic| (
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
          pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
              zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero,
                  Nat.mul_add, Nat.mul_one]))
local macro "normalize_at" h:ident : tactic => `(tactic| (
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
          pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
              zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero,
                  Nat.mul_add, Nat.mul_one] at $h:ident))
local macro "walk" t:term : tactic => `(tactic| (
  (first | refine stepStar_trans $t ?_ | refine stepStar_stepPlus_stepPlus $t ?_)
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
          pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
              zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero,
                  Nat.mul_add, Nat.mul_one]))
local macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
          pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
              zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero,
                  Nat.mul_add, Nat.mul_one]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, Tape.write, listblank_append_cons, listblank_append_nil,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
          zero_cons_default, pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
              ones_append_cons_one, zeros_append_cons_zero, pow_append_pow, zeros_append_default,
                  Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

-- ============================================================================
-- 2nd-Order Digit-Stack Encodings (left: stride 1, offset 1, maxSep 4;
--                                  right: stride 1, offset 1, maxSep 2)
-- ============================================================================

private def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L => (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 4))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1))

private def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R => (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 2)) +>
      encRight R)

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl
@[simp] private theorem encLeft_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) =
        (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 4))) <+
            (([1] : List (Fin 2)) ^ (1 * a + 1)) := rfl
@[simp] private theorem encRight_nil : encRight [] = default := rfl
@[simp] private theorem encRight_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d, b) :: R) =
        (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 2)) +>
            encRight R) := rfl

private theorem encLeft_mod4 (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = encLeft ((a, b % 4) :: L) := by
  simp only [encLeft_cons, Nat.mod_mod]

private theorem encLeft_succ (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a + 1, b) :: L) = (1 : Fin 2) >> encLeft ((a, b) :: L) := by
  simp only [encLeft_cons]
  rw [show 1 * (a + 1) + 1 = 1 + (1 * a + 1) by omega, list_pow_add, listblank_append_right_assoc]
  rfl

private theorem encLeft_d0_s0 (L : List (ℕ × ℕ)) :
    encLeft ((0, 0) :: L) = (1 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d0_s1 (L : List (ℕ × ℕ)) :
    encLeft ((0, 1) :: L) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d0_s2 (L : List (ℕ × ℕ)) :
    encLeft ((0, 2) :: L) =
        (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d0_s3 (L : List (ℕ × ℕ)) :
    encLeft ((0, 3) :: L) =
        (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d1_s0 (L : List (ℕ × ℕ)) :
    encLeft ((1, 0) :: L) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d1_s1 (L : List (ℕ × ℕ)) :
    encLeft ((1, 1) :: L) =
        (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d1_s2 (L : List (ℕ × ℕ)) :
    encLeft ((1, 2) :: L) =
        (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d1_s3 (L : List (ℕ × ℕ)) :
    encLeft ((1, 3) :: L) =
        (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
            encLeft L := rfl

private theorem encLeft_run_s0 (a : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, 0) :: L) =
        (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >> encLeft L) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encLeft_succ, ih]; normalize

private theorem encLeft_run_s1 (a : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, 1) :: L) =
        (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >> (0 : Fin 2) >> encLeft L) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encLeft_succ, ih]; normalize

private theorem encLeft_run_s2 (a : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, 2) :: L) =
        (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +>
            ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encLeft_succ, ih]; normalize

private theorem encLeft_run_s3 (a : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, 3) :: L) =
        (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +>
            ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encLeft_succ, ih]; normalize

private theorem encRight_mod2 (a b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, b) :: R) = encRight ((a, b % 2) :: R) := by
  simp only [encRight_cons, Nat.mod_mod]

private theorem encRight_succ (a b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a + 1, b) :: R) = (1 : Fin 2) >> encRight ((a, b) :: R) := by
  simp only [encRight_cons]
  rw [show 1 * (a + 1) + 1 = 1 + (1 * a + 1) by omega, list_pow_add, listblank_append_right_assoc]
  rfl

private theorem encRight_d0_s0 (R : List (ℕ × ℕ)) :
    encRight ((0, 0) :: R) = (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d0_s1 (R : List (ℕ × ℕ)) :
    encRight ((0, 1) :: R) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d1_s0 (R : List (ℕ × ℕ)) :
    encRight ((1, 0) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d2_s0 (R : List (ℕ × ℕ)) :
    encRight ((2, 0) :: R) =
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d3_s0 (R : List (ℕ × ℕ)) :
    encRight ((3, 0) :: R) =
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_run_s0 (a : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, 0) :: R) =
        (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >> encRight R) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encRight_succ, ih]; normalize

private theorem encRight_run_s1 (a : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, 1) :: R) =
        (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +>
            ((0 : Fin 2) >> (0 : Fin 2) >> encRight R) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encRight_succ, ih]; normalize

private theorem mod2_cases (b : ℕ) : b % 2 = 0 ∨ b % 2 = 1 := by
  omega

private theorem mod4_cases (b : ℕ) : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
  omega

private def bumpHead : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: L => (a + 1, b) :: L

private def bumpN : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, L => L
  | n + 1, L => bumpHead (bumpN n L)

@[simp] private theorem encLeft_cons_one (L : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encLeft L = encLeft (bumpHead L) := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · simp [bumpHead, encLeft]
  · exact (encLeft_succ a b L').symm

@[simp] private theorem encRight_cons_one (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encRight R = encRight (bumpHead R) := by
  rcases R with _ | ⟨⟨a, b⟩, R'⟩
  · simp [bumpHead, encRight]
  · exact (encRight_succ a b R').symm

private theorem encRight_bumpN (n : ℕ) (R : List (ℕ × ℕ)) :
    (([1] : List (Fin 2)) ^ n) +> encRight R = encRight (bumpN n R) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [pow_succ_list, cons_append_list, nil_append_list,
      listblank_append_cons, ih, bumpN, encRight_cons_one]

private theorem mod2_div (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩

local macro "finish" : tactic => `(tactic| (refine ⟨0, ?_⟩; simp only [encLeft_nil, encRight_nil,
    encLeft_cons_one, encRight_cons_one, multiStep_zero, listblank_append_cons,
        listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head,
            default_tail, zero_cons_default, pow_zero_list, pow_succ_list, nil_append_list,
                cons_append_list, ones_append_cons_one, zeros_append_cons_zero, pow_append_pow,
                    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]; try rfl))
local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

private def cfg_BR_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) {{B}}> (encRight R)

private def cfg_FR_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) {{F}}> (encRight R)

private def cfg_AL_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) <{{A}} (encRight R)

private def cfg_DB_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encLeft L, encRight R⟩⟩

private def cfg_CR_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) {{C}}> (encRight R)

private def cfg_FB_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨0, encLeft L, encRight R⟩⟩

private inductive StackMode
  | BR_n_n
  | FR_n_n
  | AL_n_n
  | DB_n_n
  | CR_n_n
  | FB_n_n
deriving DecidableEq

private def evalStackCfg : StackMode → List (ℕ × ℕ) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .BR_n_n, L, R => cfg_BR_n_n L R
  | .FR_n_n, L, R => cfg_FR_n_n L R
  | .AL_n_n, L, R => cfg_AL_n_n L R
  | .DB_n_n, L, R => cfg_DB_n_n L R
  | .CR_n_n, L, R => cfg_CR_n_n L R
  | .FB_n_n, L, R => cfg_FB_n_n L R

private def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

-- ============================================================================
-- Uniform cyclic walk lemmas
-- ============================================================================

private theorem cyc_R_B_1_11_11_1 (n : ℕ) : ∀ (T S : ListBlank (Fin 2)),
    (⟨some B, ⟨1, T, (([1] : List (Fin 2)) ^ n) +> S⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
      ⟨some B, ⟨1, (([1] : List (Fin 2)) ^ n) +> T, S⟩⟩ := by
  induction n with
  | zero =>
    intro T S
    normalize
    finish
  | succ j ih =>
    intro T S
    have h := ih ((1 : Fin 2) >> T) S
    normalize_at h
    normalize
    iterate 1 step
    exact h

private theorem cyc_R_C_1_11_01_1 (n : ℕ) : ∀ (T S : ListBlank (Fin 2)),
    (⟨some C, ⟨1, T, (([1] : List (Fin 2)) ^ n) +> S⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
      ⟨some C, ⟨1, (([0] : List (Fin 2)) ^ n) +> T, S⟩⟩ := by
  induction n with
  | zero =>
    intro T S
    normalize
    finish
  | succ j ih =>
    intro T S
    have h := ih ((0 : Fin 2) >> T) S
    normalize_at h
    normalize
    iterate 1 step
    exact h

private theorem cyc_L_D_0_02_12_2 (n : ℕ) : ∀ (T S : ListBlank (Fin 2)),
    (⟨some D, ⟨0, (([0] : List (Fin 2)) ^ (2 * n)) +> S, T⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
      ⟨some D, ⟨0, S, (([1] : List (Fin 2)) ^ (2 * n)) +> T⟩⟩ := by
  induction n with
  | zero =>
    intro T S
    normalize
    finish
  | succ j ih =>
    intro T S
    have h := ih ((1 : Fin 2) >> (1 : Fin 2) >> T) S
    normalize_at h
    normalize
    iterate 2 step
    exact h

private theorem cyc_L_E_0_02_12_2 (n : ℕ) : ∀ (T S : ListBlank (Fin 2)),
    (⟨some E, ⟨0, (([0] : List (Fin 2)) ^ (2 * n)) +> S, T⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
      ⟨some E, ⟨0, S, (([1] : List (Fin 2)) ^ (2 * n)) +> T⟩⟩ := by
  induction n with
  | zero =>
    intro T S
    normalize
    finish
  | succ j ih =>
    intro T S
    have h := ih ((1 : Fin 2) >> (1 : Fin 2) >> T) S
    normalize_at h
    normalize
    iterate 2 step
    exact h

-- ============================================================================
-- Inductive Left-Sweep Helpers for `mode_CR_n_n_closed`
-- ============================================================================

private def encLeftU : List (ℕ × ℕ) → List (ℕ × ℕ) → ListBlank (Fin 2)
  | [], L3 => encLeft L3
  | (a, z) :: U, L3 =>
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ a) +>
        ((0 : Fin 2) >> ((([0] : List (Fin 2)) ^ z) +> encLeftU U L3)))

@[simp] private theorem encLeftU_nil (L3 : List (ℕ × ℕ)) : encLeftU [] L3 = encLeft L3 := rfl

@[simp] private theorem encLeftU_cons (a z : ℕ) (U L3 : List (ℕ × ℕ)) :
    encLeftU ((a, z) :: U) L3 =
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ a) +>
        ((0 : Fin 2) >> ((([0] : List (Fin 2)) ^ z) +> encLeftU U L3))) := rfl

private def cfg_CR_U (U L3 R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeftU U L3) {{C}}> (encRight R)

private def cfg_D1 (U L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin
    6) :=
  ⟨some D, ⟨1, (encLeftU U L3).tail,
    (([1] : List (Fin 2)) ^ d_acc) +> ((([0] : List (Fin 2)) ^ (1 + w)) +> encRight R_next)⟩⟩

private theorem encLeftU_add_ones (k a z : ℕ) (U L3 : List (ℕ × ℕ)) :
    (([1] : List (Fin 2)) ^ k) +> encLeftU ((a, z) :: U) L3 =
      encLeftU ((a + k, z) :: U) L3 := by
  simp only [encLeftU_cons, ones_append_cons_one, pow_append_pow]
  rw [Nat.add_comm k a]

private theorem encLeftU_cons_one (a z : ℕ) (U L3 : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encLeftU ((a, z) :: U) L3 = encLeftU ((a + 1, z) :: U) L3 := by
  simp

private theorem encLeftU_eq_encLeft_of_lt4 (U L3 : List (ℕ × ℕ)) (h : ∀ p ∈ U, p.2 < 4) :
    encLeftU U L3 = encLeft (U ++ L3) := by
  induction U with
  | nil => rfl
  | cons p U' ih =>
    rcases p with ⟨a, z⟩
    have hz : z < 4 := h (a, z) (by simp)
    have ih' : encLeftU U' L3 = encLeft (U' ++ L3) :=
      ih (fun q hq => h q (by simp [hq]))
    rcases z with _ | _ | _ | _ | z4
    · simp only [encLeftU_cons, List.cons_append, ih', pow_zero_list, listblank_append_nil]
      exact (encLeft_run_s0 a (U' ++ L3)).symm
    · simp only [encLeftU_cons, List.cons_append, ih']
      normalize
      exact (encLeft_run_s1 a (U' ++ L3)).symm
    · simp only [encLeftU_cons, List.cons_append, ih']
      normalize
      exact (encLeft_run_s2 a (U' ++ L3)).symm
    · simp only [encLeftU_cons, List.cons_append, ih']
      normalize
      exact (encLeft_run_s3 a (U' ++ L3)).symm
    · omega

private theorem encLeft_eq_encLeftU_singleton (aL bL : ℕ) (L' : List (ℕ × ℕ)) :
    encLeft ((aL, bL) :: L') = encLeftU [(aL, bL % 4)] L' := by
  rw [encLeft_mod4 aL bL L']
  exact (encLeftU_eq_encLeft_of_lt4 [(aL, bL % 4)] L' (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    omega)).symm

private theorem all_lt4_or_exists_ge4 (U : List (ℕ × ℕ)) :
    (∀ p ∈ U, p.2 < 4) ∨ (∃ p ∈ U, p.2 ≥ 4) := by
  induction U with
  | nil => exact Or.inl (by intro p hp; cases hp)
  | cons p U' ih =>
    rcases Nat.lt_or_ge p.2 4 with hp | hp
    · rcases ih with h_all | ⟨q, hq_mem, hq_ge⟩
      · exact Or.inl (by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact hp
          · exact h_all q hq')
      · exact Or.inr ⟨q, by simp [hq_mem], hq_ge⟩
    · exact Or.inr ⟨p, by simp, hp⟩

private theorem tail_ge4_of_head_lt4 {a0 z0 : ℕ} {U1 : List (ℕ × ℕ)}
    (h_ge4 : ∃ p ∈ (a0, z0) :: U1, p.2 ≥ 4) (hz0 : z0 < 4) :
    ∃ a1 z1 U2, U1 = (a1, z1) :: U2 ∧ (∃ p ∈ (a1, z1) :: U2, p.2 ≥ 4) := by
  rcases h_ge4 with ⟨p, hp_mem, hp_ge⟩
  rcases List.mem_cons.mp hp_mem with rfl | hp_tail
  · simp at hp_ge; omega
  · rcases U1 with _ | ⟨⟨a1, z1⟩, U2⟩
    · cases hp_tail
    · exact ⟨a1, z1, U2, rfl, ⟨p, hp_tail, hp_ge⟩⟩

private theorem encRight_expose_one (d2 b2 : ℕ) (R2 : List (ℕ × ℕ)) :
    ∃ TR, encRight ((d2, b2) :: R2) = (1 : Fin 2) >> TR := by
  rcases mod2_cases b2 with h | h
  · rw [encRight_mod2 d2 b2 R2, h, encRight_run_s0 d2 R2]; exact ⟨_, rfl⟩
  · rw [encRight_mod2 d2 b2 R2, h, encRight_run_s1 d2 R2]; exact ⟨_, rfl⟩

private def prependZeroBlocks : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, R => R
  | m + 1, R => prependZeroBlocks m ((0, 0) :: R)

private theorem prependZeroBlocks_succ_head (m : ℕ) (R : List (ℕ × ℕ)) :
    prependZeroBlocks (m + 1) R = (0, 0) :: prependZeroBlocks m R := by
  induction m generalizing R with
  | zero => rfl
  | succ m' ih => exact ih ((0, 0) :: R)

private theorem prependZeroBlocks_nonempty (m d b : ℕ) (R : List (ℕ × ℕ)) :
    ∃ d' b' R', prependZeroBlocks m ((d, b) :: R) = (d', b') :: R' := by
  cases m with
  | zero => exact ⟨d, b, R, rfl⟩
  | succ m' => rw [prependZeroBlocks_succ_head]; exact ⟨0, 0, _, rfl⟩

private theorem walk_A_pairs (m : ℕ) : ∀ (S : ListBlank (Fin 2)) (R : List (ℕ × ℕ)),
    (⟨some A, ⟨1, (([1] : List (Fin 2)) ^ (2 * m)) +>
        S, encRight R⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
      ⟨some A, ⟨1, S, encRight (prependZeroBlocks m R)⟩⟩ := by
  induction m with
  | zero =>
    intro S R
    normalize
    finish
  | succ m' ih =>
    intro S R
    rw [show 2 * (m' + 1) = 2 + 2 * m' by omega, list_pow_add, listblank_append_right_assoc]
    normalize
    iterate 2 step
    rw [← encRight_d0_s0 R]
    exact ih S ((0, 0) :: R)

private theorem carry_d0_plus (a0 z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (bR d2 b2 : ℕ) (R2 : List (ℕ × ℕ))
    (hbR : bR % 2 = 0) :
    (cfg_CR_U ((a0, z0) :: U1) L3 ((0, bR) :: (d2, b2) :: R2)) [target_tm]⊢⁺
      cfg_CR_U ((a0 + 2, z0) :: U1) L3 ((d2, b2) :: R2) := by
  obtain ⟨TR, hTR⟩ := encRight_expose_one d2 b2 R2
  unfold cfg_CR_U
  rw [encRight_mod2 0 bR ((d2, b2) :: R2), hbR, encRight_d0_s0 ((d2, b2) :: R2), hTR]
  rw [encLeftU_cons a0 z0 U1 L3, encLeftU_cons (a0 + 2) z0 U1 L3]
  execute 10

private theorem carry_d0 (a0 z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (bR d2 b2 : ℕ) (R2 : List (ℕ × ℕ))
    (hbR : bR % 2 = 0) :
    (cfg_CR_U ((a0, z0) :: U1) L3 ((0, bR) :: (d2, b2) :: R2)) [target_tm]⊢*
      cfg_CR_U ((a0 + 2, z0) :: U1) L3 ((d2, b2) :: R2) :=
  stepPlus_stepStar (carry_d0_plus a0 z0 U1 L3 bR d2 b2 R2 hbR)

private theorem carry_dsucc (d' : ℕ) (U L3 : List (ℕ × ℕ)) (bR d2 b2 : ℕ) (R2 : List (ℕ × ℕ))
    (hbR : bR % 2 = 0) :
    (cfg_CR_U U L3 ((d' + 1, bR) :: (d2, b2) :: R2)) [target_tm]⊢⁺
      cfg_CR_U ((1, d') :: U) L3 ((d2, b2) :: R2) := by
  obtain ⟨TR, hTR⟩ := encRight_expose_one d2 b2 R2
  unfold cfg_CR_U
  rw [encRight_mod2 (d' + 1) bR ((d2, b2) :: R2), hbR, encRight_run_s0 (d' + 1) ((d2, b2) :: R2),
      hTR]
  normalize
  walk (cyc_R_C_1_11_01_1 (d' + 1) (encLeftU U L3) ((0 : Fin 2) >> (1 : Fin 2) >> TR))
  rw [encLeftU_cons 1 d' U L3]
  execute 10

private theorem carry_zero_blocks (m : ℕ) : ∀ (a0 z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (db bb : ℕ) (Rb :
    List (ℕ × ℕ)),
    (cfg_CR_U ((a0, z0) :: U1) L3 (prependZeroBlocks m ((db, bb) :: Rb))) [target_tm]⊢*
      cfg_CR_U ((a0 + 2 * m, z0) :: U1) L3 ((db, bb) :: Rb) := by
  induction m with
  | zero =>
    intro a0 z0 U1 L3 db bb Rb
    simp only [prependZeroBlocks, Nat.mul_zero, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ m' ih =>
    intro a0 z0 U1 L3 db bb Rb
    rw [prependZeroBlocks_succ_head]
    obtain ⟨dm, bm, Rm, hne⟩ := prependZeroBlocks_nonempty m' db bb Rb
    rw [hne]
    refine stepStar_trans (carry_d0 a0 z0 U1 L3 0 dm bm Rm rfl) ?_
    rw [← hne, show a0 + 2 * (m' + 1) = (a0 + 2) + 2 * m' by omega]
    exact ih (a0 + 2) z0 U1 L3 db bb Rb

-- ============================================================================
-- 4-Tuple Termination Measure & Reduced Right-Stack Predicate
-- ============================================================================

private def wU : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, z) :: U => (z / 4 + 1) + wU U

private def bitsU : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a, z) :: U => (a + z + 2) + bitsU U

private def phiU : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a0, z0) :: U1 => (if a0 % 2 = 0 then z0 + 4 else z0 + 3) + bitsU U1

private def tailOnesU : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a, _) :: U => (a + 1) + tailOnesU U

private def onesU : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a0, _) :: U1 => (if a0 = 0 then 3 else a0 + 1) + tailOnesU U1

private def remTailLen : List (ℕ × ℕ) → ℕ
  | [] => 0
  | [_] => 0
  | (_, bR) :: R' => if bR % 2 = 1 then R'.length else remTailLen R'

private def IsReducedR : List (ℕ × ℕ) → Prop
  | [] => True
  | [(_, _)] => True
  | (_, bR) :: _ :: _ => bR % 2 = 1

private theorem carry_to_reduced : ∀ (R : List (ℕ × ℕ)) (a0 z0 : ℕ) (U1 L3 : List (ℕ × ℕ)),
    ∃ a0' z0' U1' R',
      ((cfg_CR_U ((a0, z0) :: U1) L3 R) [target_tm]⊢* cfg_CR_U ((a0', z0') :: U1') L3 R') ∧
      IsReducedR R' ∧
      remTailLen R' = remTailLen R ∧
      ((∀ p ∈ (a0', z0') :: U1', p.2 < 4) ∨ (∃ p ∈ (a0', z0') :: U1', p.2 ≥ 4)) := by
  intro R
  induction R with
  | nil =>
    intro a0 z0 U1 L3
    exact ⟨a0, z0, U1, [], ⟨0, rfl⟩, trivial, rfl, all_lt4_or_exists_ge4 _⟩
  | cons hd tl ih =>
    rcases hd with ⟨d, bR⟩
    intro a0 z0 U1 L3
    rcases tl with _ | ⟨⟨d2, b2⟩, R2⟩
    · exact ⟨a0, z0, U1, [(d, bR)], ⟨0, rfl⟩, trivial, rfl, all_lt4_or_exists_ge4 _⟩
    · rcases mod2_cases bR with hbR_0 | hbR_1
      · rcases d with _ | d'
        · obtain ⟨a0', z0', U1', R', hst, hred, hlen, hlt⟩ := ih (a0 + 2) z0 U1 L3
          refine ⟨a0', z0', U1', R', stepStar_trans (carry_d0 a0 z0 U1 L3 bR d2 b2 R2 hbR_0) hst,
              hred, ?_, hlt⟩
          simp [remTailLen, hbR_0, hlen]
        · obtain ⟨a0', z0', U1', R', hst, hred, hlen, hlt⟩ := ih 1 d' ((a0, z0) :: U1) L3
          refine ⟨a0', z0', U1', R',
            stepStar_trans (stepPlus_stepStar (carry_dsucc d' ((a0,
                z0) :: U1) L3 bR d2 b2 R2 hbR_0)) hst,
            hred, ?_, hlt⟩
          simp [remTailLen, hbR_0, hlen]
      · exact ⟨a0, z0, U1, (d, bR) :: (d2, b2) :: R2, ⟨0, rfl⟩, hbR_1, rfl, all_lt4_or_exists_ge4 _⟩

-- ============================================================================
-- Micro-Step Helpers for `d_sweep_u`
-- ============================================================================

private theorem d1_a0_z0 (a1 z1 : ℕ) (U2 L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List (ℕ × ℕ))
    (hw : w = 0 ∨ w = 1) :
    (cfg_D1 ((0, 0) :: (a1, z1) :: U2) L3 d_acc w R_next) [target_tm]⊢*
      cfg_CR_U ((a1 + 1, z1) :: U2) L3 ((d_acc, w) :: R_next) := by
  unfold cfg_D1 cfg_CR_U
  rw [encLeftU_cons 0 0 ((a1, z1) :: U2) L3, encLeftU_cons a1 z1 U2 L3,
      encLeftU_cons (a1 + 1) z1 U2 L3]
  rcases hw with rfl | rfl
  · rw [encRight_run_s0 d_acc R_next]
    normalize
    execute 4
  · rw [encRight_run_s1 d_acc R_next]
    normalize
    execute 4

private theorem d1_a0_z1 (a1 z1 : ℕ) (U2 L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List (ℕ × ℕ))
    (hw : w = 0 ∨ w = 1) :
    (cfg_D1 ((0, 1) :: (a1, z1) :: U2) L3 d_acc w R_next) [target_tm]⊢*
      cfg_CR_U ((a1 + 2, z1) :: U2) L3 ((d_acc, w) :: R_next) := by
  unfold cfg_D1 cfg_CR_U
  rw [encLeftU_cons 0 1 ((a1, z1) :: U2) L3, encLeftU_cons a1 z1 U2 L3,
      encLeftU_cons (a1 + 2) z1 U2 L3]
  rcases hw with rfl | rfl
  · rw [encRight_run_s0 d_acc R_next]
    normalize
    execute 8
  · rw [encRight_run_s1 d_acc R_next]
    normalize
    execute 8

private theorem d1_a0_zge2 (z' : ℕ) (U1 L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List (ℕ × ℕ))
    (hw : w = 0 ∨ w = 1) :
    (cfg_D1 ((0, z' + 2) :: U1) L3 d_acc w R_next) [target_tm]⊢*
      cfg_CR_U ((1, z') :: U1) L3 ((d_acc, w) :: R_next) := by
  unfold cfg_D1 cfg_CR_U
  rw [encLeftU_cons 0 (z' + 2) U1 L3, encLeftU_cons 1 z' U1 L3]
  rcases hw with rfl | rfl
  · rw [encRight_run_s0 d_acc R_next]
    normalize
    execute 8
  · rw [encRight_run_s1 d_acc R_next]
    normalize
    execute 8

private theorem d1_a1_w0 (z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (d_acc : ℕ) (R_next : List (ℕ × ℕ)) :
    (cfg_D1 ((1, z0) :: U1) L3 d_acc 0 R_next) [target_tm]⊢*
      (⟨some C, ⟨(encRight R_next).head,
        (([1] : List (Fin 2)) ^ (d_acc + 4)) +> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3),
        (encRight R_next).tail⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  unfold cfg_D1
  rw [encLeftU_cons 1 z0 U1 L3]
  normalize
  iterate 3 step
  walk (cyc_R_B_1_11_11_1 (d_acc + 1)
    ((1 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3))
    ((0 : Fin 2) >> encRight R_next))
  execute 2

private theorem d1_a1_w1 (z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (d_acc : ℕ) (d3 b3 : ℕ) (R3 : List (ℕ ×
    ℕ)) :
    (cfg_D1 ((1, z0) :: U1) L3 d_acc 1 ((d3, b3) :: R3)) [target_tm]⊢*
      (⟨some C, ⟨(encRight ((d3, b3) :: R3)).head,
        (([1] : List (Fin 2)) ^ (d_acc + 5)) +> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3),
        (encRight ((d3, b3) :: R3)).tail⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  obtain ⟨TR, hTR⟩ := encRight_expose_one d3 b3 R3
  unfold cfg_D1
  rw [encLeftU_cons 1 z0 U1 L3, hTR]
  normalize
  iterate 3 step
  walk (cyc_R_B_1_11_11_1 (d_acc + 1)
    ((1 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3))
    ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> TR))
  execute 7

private theorem d1_a_odd_ge3 (m' z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List (ℕ ×
    ℕ))
    (hw : w = 0 ∨ w = 1) :
    (cfg_D1 ((2 * m' + 3, z0) :: U1) L3 d_acc w R_next) [target_tm]⊢*
      (⟨some C, ⟨(encRight (prependZeroBlocks m' ((d_acc + 1, w) :: R_next))).head,
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +>
            encLeftU U1 L3),
        (encRight (prependZeroBlocks m' ((d_acc + 1,
            w) :: R_next))).tail⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  unfold cfg_D1
  rw [encLeftU_cons (2 * m' + 3) z0 U1 L3]
  have hR_acc : (1 : Fin 2) >> (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ d_acc) +>
      ((([0] : List (Fin 2)) ^ (1 + w)) +> encRight R_next)) =
      encRight ((d_acc + 1, w) :: R_next) := by
    rcases hw with rfl | rfl
    · rw [encRight_succ d_acc 0 R_next, encRight_run_s0 d_acc R_next]; normalize
    · rw [encRight_succ d_acc 1 R_next, encRight_run_s1 d_acc R_next]; normalize
  normalize
  iterate 2 step
  rw [hR_acc, ← ones_append_cons_one (2 * m') ((0 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +>
      encLeftU U1 L3))]
  walk (walk_A_pairs m'
    ((1 : Fin 2) >> (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3))
    ((d_acc + 1, w) :: R_next))
  obtain ⟨dm, bm, Rm, hne⟩ := prependZeroBlocks_nonempty m' (d_acc + 1) w R_next
  obtain ⟨TR, hTR⟩ := encRight_expose_one dm bm Rm
  rw [hne, hTR]
  normalize
  execute 5

private theorem d1_a_even_ge2_prefix (m z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List
    (ℕ × ℕ))
    (hw : w = 0 ∨ w = 1) :
    (cfg_D1 ((2 * m + 2, z0) :: U1) L3 d_acc w R_next) [target_tm]⊢*
      ⟨some A, ⟨1, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3),
        encRight (prependZeroBlocks m ((d_acc + 1, w) :: R_next))⟩⟩ := by
  unfold cfg_D1
  rw [encLeftU_cons (2 * m + 2) z0 U1 L3]
  rw [show 2 * m + 2 = 2 + 2 * m by omega, list_pow_add, listblank_append_right_assoc]
  have hR_acc : (1 : Fin 2) >> (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ d_acc) +>
      ((([0] : List (Fin 2)) ^ (1 + w)) +> encRight R_next)) =
      encRight ((d_acc + 1, w) :: R_next) := by
    rcases hw with rfl | rfl
    · rw [encRight_succ d_acc 0 R_next, encRight_run_s0 d_acc R_next]; normalize
    · rw [encRight_succ d_acc 1 R_next, encRight_run_s1 d_acc R_next]; normalize
  normalize
  iterate 2 step
  rw [hR_acc]
  exact walk_A_pairs m
    ((0 : Fin 2) >> ((([0] : List (Fin 2)) ^ z0) +> encLeftU U1 L3))
    ((d_acc + 1, w) :: R_next)

-- ============================================================================
-- Main Inductive Left-Sweep Lemma (`d_sweep_u`)
-- ============================================================================

private theorem d_sweep_u : ∀ (n : ℕ) (U L3 : List (ℕ × ℕ)) (d_acc w : ℕ) (R_next : List (ℕ × ℕ)),
    U.length ≤ n →
    (∃ p ∈ U, p.2 ≥ 4) →
    d_acc ≥ 2 →
    (w = 0 ∨ w = 1) →
    (w = 1 → R_next ≠ []) →
    ∃ U_out R_out,
      U_out ≠ [] ∧
      ((cfg_D1 U L3 d_acc w R_next) [target_tm]⊢* cfg_CR_U U_out L3 R_out) ∧
      ((R_out = R_next ∧
          (w = 0 → wU U_out ≤ wU U ∧ (d_acc % 2 = 0 → wU U_out = wU U → phiU U_out < phiU U))) ∨
       (∃ d_out ≥ d_acc, R_out = (d_out, w) :: R_next ∧
          (w = 0 →
            ((wU U_out < wU U) ∨
             (wU U_out = wU U ∧ phiU U_out < phiU U) ∨
             (wU U_out = wU U ∧ phiU U_out = phiU U ∧ onesU U_out < onesU U)) ∧
            ((d_out - d_acc + 2) / 4 + wU U_out ≤ wU U) ∧
            ((d_out - d_acc + 2) / 4 + wU U_out = wU U →
              (d_out - d_acc) + bitsU U_out + 1 ≤ bitsU U) ∧
            ((d_out - d_acc + 2) / 4 + wU U_out = wU U →
              (d_out - d_acc) + bitsU U_out + 1 = bitsU U →
              tailOnesU U_out ≤ tailOnesU U + 1)))) := by
  intro n
  induction n with
  | zero =>
    intro U L3 d_acc w R_next hlen h_ge4
    rcases U with _ | ⟨p, U1⟩
    · rcases h_ge4 with ⟨q, hq, _⟩; cases hq
    · simp at hlen
  | succ n' ih =>
    intro U L3 d_acc w R_next hlen h_ge4 hd_acc hw hw_ne
    rcases U with _ | ⟨⟨a0, z0⟩, U1⟩
    · rcases h_ge4 with ⟨q, hq, _⟩; cases hq
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
    rcases a0 with _ | _ | a2
    · -- Case 1: a0 = 0
      rcases z0 with _ | _ | z'
      · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
        refine ⟨(a1 + 1, z1) :: U2, (d_acc, w) :: R_next, by simp,
          d1_a0_z0 a1 z1 U2 L3 d_acc w R_next hw, Or.inr ⟨d_acc, le_rfl, rfl, fun _ => ?_⟩⟩
        simp only [wU, bitsU, phiU, onesU, tailOnesU]
        refine ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
      · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
        refine ⟨(a1 + 2, z1) :: U2, (d_acc, w) :: R_next, by simp,
          d1_a0_z1 a1 z1 U2 L3 d_acc w R_next hw, Or.inr ⟨d_acc, le_rfl, rfl, fun _ => ?_⟩⟩
        simp only [wU, bitsU, phiU, onesU, tailOnesU]
        refine ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
      · refine ⟨(1, z') :: U1, (d_acc, w) :: R_next, by simp,
          d1_a0_zge2 z' U1 L3 d_acc w R_next hw, Or.inr ⟨d_acc, le_rfl, rfl, fun _ => ?_⟩⟩
        simp only [wU, bitsU, phiU, onesU, tailOnesU]
        refine ⟨?_, by omega, by intro _; omega, by intro _ _; omega⟩
        by_cases hdiv : z' / 4 < (z' + 2) / 4
        · exact Or.inl (by omega)
        · refine Or.inr (Or.inl ?_)
          split_ifs <;> omega
    · -- Case 2: a0 = 1 (absorbs head block into U_out!)
      rcases hw with rfl | rfl
      · -- w = 0
        rcases z0 with _ | z'
        · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
          have hst : (cfg_D1 ((1, 0) :: (a1, z1) :: U2) L3 d_acc 0 R_next) [target_tm]⊢*
              cfg_CR_U ((a1 + (d_acc + 4), z1) :: U2) L3 R_next := by
            refine stepStar_trans (d1_a1_w0 0 ((a1, z1) :: U2) L3 d_acc R_next) ?_
            unfold cfg_CR_U
            simp only [pow_zero_list, listblank_append_nil, encLeftU_add_ones]
            exact ⟨0, rfl⟩
          refine ⟨(a1 + (d_acc + 4), z1) :: U2, R_next, by simp, hst, Or.inl ⟨rfl, fun _ => ?_⟩⟩
          simp only [wU]
          exact ⟨by omega, fun _ _ => by omega⟩
        · have hst : (cfg_D1 ((1, z' + 1) :: U1) L3 d_acc 0 R_next) [target_tm]⊢*
              cfg_CR_U ((d_acc + 3, z') :: U1) L3 R_next := by
            refine stepStar_trans (d1_a1_w0 (z' + 1) U1 L3 d_acc R_next) ?_
            unfold cfg_CR_U
            rw [encLeftU_cons (d_acc + 3) z' U1 L3]
            finish
          refine ⟨(d_acc + 3, z') :: U1, R_next, by simp, hst, Or.inl ⟨rfl, fun _ => ?_⟩⟩
          simp only [wU, phiU]
          refine ⟨by omega, fun hd_ev _ => ?_⟩
          split_ifs <;> omega
      · -- w = 1
        rcases R_next with _ | ⟨⟨d3, b3⟩, R3⟩
        · exact False.elim (hw_ne rfl rfl)
        rcases z0 with _ | z'
        · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
          have hst : (cfg_D1 ((1, 0) :: (a1, z1) :: U2) L3 d_acc 1 ((d3, b3) :: R3)) [target_tm]⊢*
              cfg_CR_U ((a1 + (d_acc + 5), z1) :: U2) L3 ((d3, b3) :: R3) := by
            refine stepStar_trans (d1_a1_w1 0 ((a1, z1) :: U2) L3 d_acc d3 b3 R3) ?_
            unfold cfg_CR_U
            simp only [pow_zero_list, listblank_append_nil, encLeftU_add_ones]
            exact ⟨0, rfl⟩
          exact ⟨(a1 + (d_acc + 5), z1) :: U2, (d3, b3) :: R3, by simp, hst,
            Or.inl ⟨rfl, fun h0 => by cases h0⟩⟩
        · have hst : (cfg_D1 ((1, z' + 1) :: U1) L3 d_acc 1 ((d3, b3) :: R3)) [target_tm]⊢*
              cfg_CR_U ((d_acc + 4, z') :: U1) L3 ((d3, b3) :: R3) := by
            refine stepStar_trans (d1_a1_w1 (z' + 1) U1 L3 d_acc d3 b3 R3) ?_
            unfold cfg_CR_U
            rw [encLeftU_cons (d_acc + 4) z' U1 L3]
            finish
          exact ⟨(d_acc + 4, z') :: U1, (d3, b3) :: R3, by simp, hst,
            Or.inl ⟨rfl, fun h0 => by cases h0⟩⟩
    · -- Split a2 parity: a0 = a2 + 2 is either 2*m + 2 (even >= 2) or 2*m' + 3 (odd >= 3)
      rcases mod2_div a2 with ⟨m, rfl | rfl⟩
      · -- Case 3: a0 = 2 * m + 2 (even >= 2)
        have hpref := d1_a_even_ge2_prefix m z0 U1 L3 d_acc w R_next hw
        rcases z0 with _ | _ | z''
        · -- z0 = 0
          obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
          have hmid : (⟨some A, ⟨1, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ 0) +>
              encLeftU ((a1, z1) :: U2) L3),
              encRight (prependZeroBlocks m ((d_acc + 1,
                  w) :: R_next))⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
                cfg_CR_U ((a1 + 2, z1) :: U2) L3 (prependZeroBlocks m ((d_acc + 1,
                    w) :: R_next)) := by
            obtain ⟨dm, bm, Rm, hne⟩ := prependZeroBlocks_nonempty m (d_acc + 1) w R_next
            obtain ⟨TR, hTR⟩ := encRight_expose_one dm bm Rm
            unfold cfg_CR_U
            rw [hne, hTR, encLeftU_cons a1 z1 U2 L3, encLeftU_cons (a1 + 2) z1 U2 L3]
            normalize
            execute 9
          have hfin : (cfg_D1 ((2 * m + 2, 0) :: (a1, z1) :: U2) L3 d_acc w R_next) [target_tm]⊢*
              cfg_CR_U ((a1 + 2 + 2 * m, z1) :: U2) L3 ((d_acc + 1, w) :: R_next) :=
            stepStar_trans hpref (stepStar_trans hmid
              (carry_zero_blocks m (a1 + 2) z1 U2 L3 (d_acc + 1) w R_next))
          refine ⟨(a1 + 2 + 2 * m, z1) :: U2, (d_acc + 1, w) :: R_next, by simp, hfin,
            Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
          simp only [wU, bitsU, phiU, onesU, tailOnesU]
          refine ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
        · -- z0 = 1 (RECURSIVE CASE!)
          obtain ⟨a1, z1, U2, rfl, h_ge4_tail⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
          have h_ge4_rec : ∃ p ∈ (a1 + 1, z1) :: U2, p.2 ≥ 4 := by
            rcases h_ge4_tail with ⟨p, hp_mem, hp_ge⟩
            rcases List.mem_cons.mp hp_mem with rfl | hp_u2
            · exact ⟨(a1 + 1, z1), by simp, hp_ge⟩
            · exact ⟨p, by simp [hp_u2], hp_ge⟩
          rcases m with _ | m'
          · -- Subcase m = 0 (a0 = 2, z0 = 1): recurse with d_acc + 4, w, R_next!
            have h6 : (⟨some A, ⟨1, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ 1) +>
                encLeftU ((a1, z1) :: U2) L3),
                encRight (prependZeroBlocks 0 ((d_acc + 1,
                    w) :: R_next))⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
                  cfg_D1 ((a1 + 1, z1) :: U2) L3 (d_acc + 4) w R_next := by
              simp only [prependZeroBlocks]
              unfold cfg_D1
              rw [encLeftU_cons a1 z1 U2 L3, encLeftU_cons (a1 + 1) z1 U2 L3]
              rcases hw with rfl | rfl
              · rw [encRight_run_s0 (d_acc + 1) R_next]; normalize; execute 6
              · rw [encRight_run_s1 (d_acc + 1) R_next]; normalize; execute 6
            obtain ⟨U_out, R_out, hU_ne, hrec, hpost⟩ :=
              ih ((a1 + 1, z1) :: U2) L3 (d_acc + 4) w R_next (by simpa using hlen)
                h_ge4_rec (by omega) hw hw_ne
            refine ⟨U_out, R_out, hU_ne, stepStar_trans hpref (stepStar_trans h6 hrec), ?_⟩
            rcases hpost with ⟨rfl, habs⟩ | ⟨d_out, hd_out, rfl, hnonabs⟩
            · refine Or.inl ⟨rfl, fun hw0 => ?_⟩
              obtain ⟨hw_le, _⟩ := habs hw0
              simp only [wU] at hw_le ⊢
              exact ⟨by omega, fun _ _ => by omega⟩
            · refine Or.inr ⟨d_out, by omega, rfl, fun hw0 => ?_⟩
              obtain ⟨_, hw_dd, hbits_dd, hones_dd⟩ := hnonabs hw0
              simp only [wU, bitsU, tailOnesU] at hw_dd hbits_dd hones_dd ⊢
              have hdiv_eq : (d_out - d_acc + 2) / 4 = (d_out - (d_acc + 4) + 2) / 4 + 1 := by omega
              refine ⟨Or.inl (by omega), by omega, ?_, ?_⟩
              · intro heq
                have h1 := hbits_dd (by omega)
                omega
              · intro heq hbeq
                have h2 := hones_dd (by omega) (by omega)
                omega
          · -- Subcase m = m' + 1 (a0 = 2 * m' + 4, z0 = 1): recurse with d_pushed = 3, w = 0!
            let R_sub := prependZeroBlocks m' ((d_acc + 1, w) :: R_next)
            have h6 : (⟨some A, ⟨1, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ 1) +>
                encLeftU ((a1, z1) :: U2) L3),
                encRight (prependZeroBlocks (m' + 1) ((d_acc + 1,
                    w) :: R_next))⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
                  cfg_D1 ((a1 + 1, z1) :: U2) L3 3 0 R_sub := by
              rw [prependZeroBlocks_succ_head]
              unfold cfg_D1
              rw [encRight_d0_s0 R_sub, encLeftU_cons a1 z1 U2 L3, encLeftU_cons (a1 + 1) z1 U2 L3]
              normalize
              execute 6
            obtain ⟨U_mid, R_mid, hU_mid_ne, hrec, hpost⟩ :=
              ih ((a1 + 1, z1) :: U2) L3 3 0 R_sub (by simpa using hlen)
                h_ge4_rec (by omega) (Or.inl rfl) (fun h => by cases h)
            rcases U_mid with _ | ⟨⟨am, zm⟩, U_mid'⟩
            · exact False.elim (hU_mid_ne rfl)
            rcases hpost with ⟨rfl, habs⟩ | ⟨d_mid, hd_mid, rfl, hnonabs⟩
            · -- Sub-subcase: inner call absorbed (3, 0), so R_mid = R_sub!
              obtain ⟨hw_le, _⟩ := habs rfl
              have hfin : (cfg_D1 ((2 * (m' + 1) + 2, 1) :: (a1,
                  z1) :: U2) L3 d_acc w R_next) [target_tm]⊢*
                  cfg_CR_U ((am + 2 * m', zm) :: U_mid') L3 ((d_acc + 1, w) :: R_next) :=
                stepStar_trans hpref (stepStar_trans h6 (stepStar_trans hrec
                  (carry_zero_blocks m' am zm U_mid' L3 (d_acc + 1) w R_next)))
              refine ⟨(am + 2 * m', zm) :: U_mid', (d_acc + 1, w) :: R_next, by simp, hfin,
                Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU] at hw_le ⊢
              exact ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
            · -- Sub-subcase: inner call produced R_mid = (d_mid, 0) :: R_sub with d_mid >= 3!
              obtain ⟨_, hw_dd, hbits_dd, hones_dd⟩ := hnonabs rfl
              obtain ⟨dm, bm, Rm, hne⟩ := prependZeroBlocks_nonempty m' (d_acc + 1) w R_next
              have hc1 : (cfg_CR_U ((am, zm) :: U_mid') L3 ((d_mid, 0) :: R_sub)) [target_tm]⊢*
                  cfg_CR_U ((1, d_mid - 1) :: (am, zm) :: U_mid') L3 R_sub := by
                dsimp only [R_sub]
                rw [show d_mid = (d_mid - 1) + 1 by omega, hne]
                exact stepPlus_stepStar (carry_dsucc (d_mid - 1) ((am,
                    zm) :: U_mid') L3 0 dm bm Rm rfl)
              have hc2 := carry_zero_blocks m' 1 (d_mid - 1) ((am,
                  zm) :: U_mid') L3 (d_acc + 1) w R_next
              have hfin : (cfg_D1 ((2 * (m' + 1) + 2, 1) :: (a1,
                  z1) :: U2) L3 d_acc w R_next) [target_tm]⊢*
                  cfg_CR_U ((1 + 2 * m', d_mid - 1) :: (am, zm) :: U_mid') L3 ((d_acc + 1,
                      w) :: R_next) :=
                stepStar_trans hpref (stepStar_trans h6 (stepStar_trans hrec (stepStar_trans hc1
                    hc2)))
              refine ⟨(1 + 2 * m', d_mid - 1) :: (am, zm) :: U_mid', (d_acc + 1, w) :: R_next,
                by simp, hfin, Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
              have hd_sub : d_mid - 1 = d_mid - 3 + 2 := by omega
              simp only [wU, bitsU, phiU, onesU, tailOnesU] at hw_dd hbits_dd hones_dd ⊢
              refine ⟨?_, by omega, ?_, ?_⟩
              · by_cases hlt_w : (d_mid - 1) / 4 + (1 + (zm / 4 + 1 + wU U_mid')) < 1 + (z1 / 4 + 1
                    + wU U2)
                · exact Or.inl (by omega)
                · have heq_w : (d_mid - 3 + 2) / 4 + (zm / 4 + 1 + wU U_mid') =
                      z1 / 4 + 1 + wU U2 := by omega
                  have hb1 := hbits_dd heq_w
                  by_cases hlt_p : d_mid - 1 + 3 + (am + zm + 2 + bitsU U_mid') < 1 + 4 + (a1 + z1
                      + 2 + bitsU U2)
                  · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
                    (try split_ifs) <;> first | trivial | contradiction | omega
                  · have heq_b : d_mid - 3 + (am + zm + 2 + bitsU U_mid') + 1 =
                        a1 + 1 + z1 + 2 + bitsU U2 := by omega
                    have ho1 := hones_dd heq_w heq_b
                    refine Or.inr (Or.inr ⟨by omega, ?_,
                        ?_⟩) <;> ((try split_ifs) <;> first | trivial | contradiction | omega)
              · intro heq_outer
                have hb1 := hbits_dd (by omega)
                omega
              · intro heq_outer hbeq_outer
                have ho1 := hones_dd (by omega) (by omega)
                omega
        · -- z0 = z'' + 2 (steps in 6 steps to cfg_D1 ((0, z'') :: U1)!)
          rcases m with _ | m'
          · -- m = 0: steps to cfg_D1 ((0, z'') :: U1) L3 (d_acc + 4) w R_next
            have h6 : (⟨some A, ⟨1, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ (z'' + 2)) +>
                encLeftU U1 L3),
                encRight (prependZeroBlocks 0 ((d_acc + 1,
                    w) :: R_next))⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
                  cfg_D1 ((0, z'') :: U1) L3 (d_acc + 4) w R_next := by
              simp only [prependZeroBlocks]
              unfold cfg_D1
              rw [encLeftU_cons 0 z'' U1 L3]
              rcases hw with rfl | rfl
              · rw [encRight_run_s0 (d_acc + 1) R_next]; normalize; execute 6
              · rw [encRight_run_s1 (d_acc + 1) R_next]; normalize; execute 6
            rcases z'' with _ | _ | z3
            · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
              refine ⟨(a1 + 1, z1) :: U2, (d_acc + 4, w) :: R_next, by simp,
                stepStar_trans hpref (stepStar_trans h6 (d1_a0_z0 a1 z1 U2 L3 (d_acc + 4) w R_next
                    hw)),
                Or.inr ⟨d_acc + 4, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU, bitsU, tailOnesU]
              exact ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
            · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
              refine ⟨(a1 + 2, z1) :: U2, (d_acc + 4, w) :: R_next, by simp,
                stepStar_trans hpref (stepStar_trans h6 (d1_a0_z1 a1 z1 U2 L3 (d_acc + 4) w R_next
                    hw)),
                Or.inr ⟨d_acc + 4, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU, bitsU, tailOnesU]
              exact ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
            · refine ⟨(1, z3) :: U1, (d_acc + 4, w) :: R_next, by simp,
                stepStar_trans hpref (stepStar_trans h6 (d1_a0_zge2 z3 U1 L3 (d_acc + 4) w R_next
                    hw)),
                Or.inr ⟨d_acc + 4, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU, bitsU, tailOnesU]
              exact ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
          · -- m = m' + 1: steps to cfg_D1 ((0, z'') :: U1) L3 3 0 R_sub, then carries (3, 0) + m'
            -- (0, 0)s!
            let R_sub := prependZeroBlocks m' ((d_acc + 1, w) :: R_next)
            obtain ⟨dm, bm, Rm, hne⟩ := prependZeroBlocks_nonempty m' (d_acc + 1) w R_next
            have h6 : (⟨some A, ⟨1, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ (z'' + 2)) +>
                encLeftU U1 L3),
                encRight (prependZeroBlocks (m' + 1) ((d_acc + 1,
                    w) :: R_next))⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
                  cfg_D1 ((0, z'') :: U1) L3 3 0 R_sub := by
              rw [prependZeroBlocks_succ_head]
              unfold cfg_D1
              rw [encRight_d0_s0 R_sub, encLeftU_cons 0 z'' U1 L3]
              normalize
              execute 6
            rcases z'' with _ | _ | z3
            · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
              have hc1 : (cfg_CR_U ((a1 + 1, z1) :: U2) L3 ((3, 0) :: R_sub)) [target_tm]⊢*
                  cfg_CR_U ((1, 2) :: (a1 + 1, z1) :: U2) L3 R_sub := by
                dsimp only [R_sub]
                rw [hne]
                exact stepPlus_stepStar (carry_dsucc 2 ((a1 + 1, z1) :: U2) L3 0 dm bm Rm rfl)
              have hc2 := carry_zero_blocks m' 1 2 ((a1 + 1, z1) :: U2) L3 (d_acc + 1) w R_next
              refine ⟨(1 + 2 * m', 2) :: (a1 + 1, z1) :: U2, (d_acc + 1, w) :: R_next, by simp,
                stepStar_trans hpref (stepStar_trans h6 (stepStar_trans
                  (d1_a0_z0 a1 z1 U2 L3 3 0 R_sub (Or.inl rfl)) (stepStar_trans hc1 hc2))),
                Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU, bitsU, phiU, onesU, tailOnesU]
              refine ⟨Or.inr (Or.inr ⟨?_, ?_, ?_⟩), ?_, fun _ => ?_,
                  fun _ _ => ?_⟩ <;> ((try split_ifs) <;> first | trivial | contradiction | omega)
            · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
              have hc1 : (cfg_CR_U ((a1 + 2, z1) :: U2) L3 ((3, 0) :: R_sub)) [target_tm]⊢*
                  cfg_CR_U ((1, 2) :: (a1 + 2, z1) :: U2) L3 R_sub := by
                dsimp only [R_sub]
                rw [hne]
                exact stepPlus_stepStar (carry_dsucc 2 ((a1 + 2, z1) :: U2) L3 0 dm bm Rm rfl)
              have hc2 := carry_zero_blocks m' 1 2 ((a1 + 2, z1) :: U2) L3 (d_acc + 1) w R_next
              refine ⟨(1 + 2 * m', 2) :: (a1 + 2, z1) :: U2, (d_acc + 1, w) :: R_next, by simp,
                stepStar_trans hpref (stepStar_trans h6 (stepStar_trans
                  (d1_a0_z1 a1 z1 U2 L3 3 0 R_sub (Or.inl rfl)) (stepStar_trans hc1 hc2))),
                Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU, bitsU, phiU, onesU, tailOnesU]
              refine ⟨Or.inr (Or.inr ⟨?_, ?_, ?_⟩), ?_, fun _ => ?_,
                  fun _ _ => ?_⟩ <;> ((try split_ifs) <;> first | trivial | contradiction | omega)
            · have hc1 : (cfg_CR_U ((1, z3) :: U1) L3 ((3, 0) :: R_sub)) [target_tm]⊢*
                  cfg_CR_U ((1, 2) :: (1, z3) :: U1) L3 R_sub := by
                dsimp only [R_sub]
                rw [hne]
                exact stepPlus_stepStar (carry_dsucc 2 ((1, z3) :: U1) L3 0 dm bm Rm rfl)
              have hc2 := carry_zero_blocks m' 1 2 ((1, z3) :: U1) L3 (d_acc + 1) w R_next
              refine ⟨(1 + 2 * m', 2) :: (1, z3) :: U1, (d_acc + 1, w) :: R_next, by simp,
                stepStar_trans hpref (stepStar_trans h6 (stepStar_trans
                  (d1_a0_zge2 z3 U1 L3 3 0 R_sub (Or.inl rfl)) (stepStar_trans hc1 hc2))),
                Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
              simp only [wU, bitsU, phiU, onesU, tailOnesU]
              refine ⟨?_, by omega, by intro _; omega, by intro _ _; omega⟩
              by_cases hdiv : 1 + (z3 / 4 + 1) < (z3 + 4) / 4 + 1
              · exact Or.inl (by omega)
              · refine Or.inr (Or.inr ⟨?_, ?_,
                    ?_⟩) <;> ((try split_ifs) <;> first | trivial | contradiction | omega)
      · -- Case 4: a0 = 2 * m + 3 (odd >= 3)
        have hodd := d1_a_odd_ge3 m z0 U1 L3 d_acc w R_next hw
        rcases z0 with _ | z'
        · obtain ⟨a1, z1, U2, rfl, _⟩ := tail_ge4_of_head_lt4 h_ge4 (by omega)
          have hmid : (cfg_D1 ((2 * m + 1 + 2, 0) :: (a1,
              z1) :: U2) L3 d_acc w R_next) [target_tm]⊢*
              cfg_CR_U ((a1 + 3, z1) :: U2) L3 (prependZeroBlocks m ((d_acc + 1,
                  w) :: R_next)) := by
            refine stepStar_trans hodd ?_
            unfold cfg_CR_U
            have hcons3 : (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encLeftU ((a1,
                z1) :: U2) L3 =
                encLeftU ((a1 + 3, z1) :: U2) L3 := by
              rw [show a1 + 3 = ((a1 + 1) + 1) + 1 by omega,
                  ← encLeftU_cons_one ((a1 + 1) + 1) z1 U2 L3,
                  ← encLeftU_cons_one (a1 + 1) z1 U2 L3,
                  ← encLeftU_cons_one a1 z1 U2 L3]
            simp only [pow_zero_list, listblank_append_nil, hcons3]
            exact ⟨0, rfl⟩
          refine ⟨(a1 + 3 + 2 * m, z1) :: U2, (d_acc + 1, w) :: R_next, by simp,
            stepStar_trans hmid (carry_zero_blocks m (a1 + 3) z1 U2 L3 (d_acc + 1) w R_next),
            Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
          simp only [wU, bitsU, tailOnesU]
          exact ⟨Or.inl (by omega), by omega, by intro _; omega, by intro _ _; omega⟩
        · have hmid : (cfg_D1 ((2 * m + 1 + 2, z' + 1) :: U1) L3 d_acc w R_next) [target_tm]⊢*
              cfg_CR_U ((2, z') :: U1) L3 (prependZeroBlocks m ((d_acc + 1, w) :: R_next)) := by
            refine stepStar_trans hodd ?_
            unfold cfg_CR_U
            rw [encLeftU_cons 2 z' U1 L3]
            finish
          refine ⟨(2 + 2 * m, z') :: U1, (d_acc + 1, w) :: R_next, by simp,
            stepStar_trans hmid (carry_zero_blocks m 2 z' U1 L3 (d_acc + 1) w R_next),
            Or.inr ⟨d_acc + 1, by omega, rfl, fun _ => ?_⟩⟩
          simp only [wU, bitsU, phiU, onesU, tailOnesU]
          refine ⟨?_, by omega, by intro _; omega, by intro _ _; omega⟩
          by_cases hdiv : z' / 4 < (z' + 1) / 4
          · exact Or.inl (by omega)
          · refine Or.inr (Or.inr ⟨?_, ?_,
                ?_⟩) <;> ((try split_ifs) <;> first | trivial | contradiction | omega)

-- ============================================================================
-- Right-to-Left Drain & 4-Level Strong Induction Closure of `cfg_CR_U`
-- ============================================================================

private theorem drain_r_nil (a0 z0 : ℕ) (U1 L3 : List (ℕ × ℕ)) :
    (cfg_CR_U ((a0, z0) :: U1) L3 []) [target_tm]⊢⁺
      cfg_D1 ((a0, z0) :: U1) L3 2 0 [] := by
  unfold cfg_CR_U cfg_D1
  rw [encLeftU_cons a0 z0 U1 L3]
  normalize
  execute 3

private theorem drain_even_halts (a0 z0 k : ℕ) (U1 L3 : List (ℕ × ℕ)) (S_zero : ListBlank (Fin 2))
    (hS : ∃ T_rest, S_zero = (0 : Fin 2) >> (0 : Fin 2) >> T_rest) :
    ∃ cfg', ((⟨some C, ⟨1, encLeftU ((a0, z0) :: U1) L3,
      (([1] : List (Fin 2)) ^ (2 * k)) +> S_zero⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone := by
  obtain ⟨T_rest, rfl⟩ := hS
  refine ⟨⟨some E, ⟨1, (encLeftU ((a0, z0) :: U1) L3).tail,
    (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ (2 * k)) +>
        ((1 : Fin 2) >> (1 : Fin 2) >> T_rest))⟩⟩, ?_, rfl⟩
  walk (cyc_R_C_1_11_01_1 (2 * k) (encLeftU ((a0,
      z0) :: U1) L3) ((0 : Fin 2) >> (0 : Fin 2) >> T_rest))
  iterate 4 step
  walk (cyc_L_D_0_02_12_2 k ((1 : Fin 2) >> (1 : Fin 2) >> T_rest) (encLeftU ((a0, z0) :: U1) L3))
  rw [encLeftU_cons a0 z0 U1 L3]
  normalize
  execute 1

private theorem drain_odd_to_d1 (a0 z0 k : ℕ) (U1 L3 : List (ℕ × ℕ)) (T_rest : ListBlank (Fin 2)) :
    (⟨some C, ⟨1, encLeftU ((a0, z0) :: U1) L3,
      (([1] : List (Fin 2)) ^ (2 * k + 1)) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> T_rest)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
    ⟨some D, ⟨1, (encLeftU ((a0, z0) :: U1) L3).tail,
      (([1] : List (Fin 2)) ^ (2 * k + 4)) +> T_rest⟩⟩ := by
  walk (cyc_R_C_1_11_01_1 (2 * k + 1) (encLeftU ((a0,
      z0) :: U1) L3) ((0 : Fin 2) >> (0 : Fin 2) >> T_rest))
  iterate 5 step
  walk (cyc_L_E_0_02_12_2 k ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> T_rest) (encLeftU ((a0,
      z0) :: U1) L3))
  rw [encLeftU_cons a0 z0 U1 L3]
  normalize
  execute 1

private theorem cr_u_reduced_step (U L3 R : List (ℕ × ℕ)) (h_red : IsReducedR R) (h_ge4 : ∃ p ∈ U,
    p.2 ≥ 4) :
    (∃ cfg', ((cfg_CR_U U L3 R) [target_tm]⊢⁺ cfg') ∧ (step target_tm cfg').isNone) ∨
    (∃ U' R',
      ((cfg_CR_U U L3 R) [target_tm]⊢⁺ cfg_CR_U U' L3 R') ∧
      IsReducedR R' ∧
      ((remTailLen R' < remTailLen R) ∨
       (remTailLen R' = remTailLen R ∧ wU U' < wU U) ∨
       (remTailLen R' = remTailLen R ∧ wU U' = wU U ∧ phiU U' < phiU U) ∨
       (remTailLen R' = remTailLen R ∧ wU U' = wU U ∧ phiU U' = phiU U ∧ onesU U' < onesU U))) := by
  rcases U with _ | ⟨⟨a0, z0⟩, U1⟩
  · rcases h_ge4 with ⟨q, hq, _⟩; cases hq
  have finish_w0_nil : ∀ (d_acc : ℕ), d_acc ≥ 2 → d_acc % 2 = 0 →
      ((cfg_CR_U ((a0, z0) :: U1) L3 R) [target_tm]⊢⁺ cfg_D1 ((a0, z0) :: U1) L3 d_acc 0 []) →
      remTailLen R = 0 →
      ∃ U' R',
        ((cfg_CR_U ((a0, z0) :: U1) L3 R) [target_tm]⊢⁺ cfg_CR_U U' L3 R') ∧
        IsReducedR R' ∧
        ((remTailLen R' < remTailLen R) ∨
         (remTailLen R' = remTailLen R ∧ wU U' < wU ((a0, z0) :: U1)) ∨
         (remTailLen R' = remTailLen R ∧ wU U' = wU ((a0, z0) :: U1) ∧
             phiU U' < phiU ((a0, z0) :: U1)) ∨
         (remTailLen R' = remTailLen R ∧ wU U' = wU ((a0, z0) :: U1) ∧
             phiU U' = phiU ((a0, z0) :: U1) ∧ onesU U' < onesU ((a0, z0) :: U1))) := by
    intro d_acc hd_ge hd_ev h_to_d1 h_rem0
    obtain ⟨U_out, R_out, _, h_sw, h_post⟩ :=
      d_sweep_u (((a0, z0) :: U1).length) ((a0, z0) :: U1) L3 d_acc 0 [] le_rfl h_ge4
        hd_ge (Or.inl rfl) (fun h => by cases h)
    refine ⟨U_out, R_out, stepPlus_stepStar_stepPlus h_to_d1 h_sw, ?_, ?_⟩
    · rcases h_post with ⟨rfl, _⟩ | ⟨d_out, _, rfl, _⟩ <;> trivial
    · rcases h_post with ⟨rfl, habs⟩ | ⟨d_out, _, rfl, hnonabs⟩
      · obtain ⟨hw_le, hphi_lt⟩ := habs rfl
        have hr0 : remTailLen ([] : List (ℕ × ℕ)) = remTailLen R := h_rem0.symm
        by_cases hlt_w : wU U_out < wU ((a0, z0) :: U1)
        · exact Or.inr (Or.inl ⟨hr0, hlt_w⟩)
        · have heq_w : wU U_out = wU ((a0, z0) :: U1) := by omega
          exact Or.inr (Or.inr (Or.inl ⟨hr0, heq_w, hphi_lt hd_ev heq_w⟩))
      · obtain ⟨h_lex, _, _, _⟩ := hnonabs rfl
        have hr0 : remTailLen [(d_out, 0)] = remTailLen R := h_rem0.symm
        rcases h_lex with hw_lt | ⟨hw_eq, hp_lt⟩ | ⟨hw_eq, hp_eq, ho_lt⟩
        · exact Or.inr (Or.inl ⟨hr0, hw_lt⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hr0, hw_eq, hp_lt⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hr0, hw_eq, hp_eq, ho_lt⟩))
  rcases R with _ | ⟨⟨d, bR⟩, R'⟩
  · exact Or.inr (finish_w0_nil 2 (by omega) (by omega) (drain_r_nil a0 z0 U1 L3) rfl)
  · rcases R' with _ | ⟨⟨d2, b2⟩, R2⟩
    · rcases mod2_cases bR with hbR_0 | hbR_1
      · rcases mod2_div d with ⟨k, rfl | rfl⟩
        · refine Or.inl ?_
          unfold cfg_CR_U
          rw [encRight_mod2 (2 * k) bR [], hbR_0, encRight_run_s0 (2 * k) [], encRight_nil]
          normalize
          exact drain_even_halts a0 z0 k U1 L3 default ⟨default, by simp⟩
        · refine Or.inr (finish_w0_nil (2 * k + 4) (by omega) (by omega) ?_ rfl)
          unfold cfg_CR_U cfg_D1
          rw [encRight_mod2 (2 * k + 1) bR [], hbR_0, encRight_run_s0 (2 * k + 1) [], encRight_nil]
          normalize
          have hd1 := drain_odd_to_d1 a0 z0 k U1 L3 default
          normalize_at hd1
          exact hd1
      · rcases mod2_div d with ⟨k, rfl | rfl⟩
        · refine Or.inl ?_
          unfold cfg_CR_U
          rw [encRight_mod2 (2 * k) bR [], hbR_1, encRight_run_s1 (2 * k) [], encRight_nil]
          normalize
          exact drain_even_halts a0 z0 k U1 L3 default ⟨default, by simp⟩
        · refine Or.inr (finish_w0_nil (2 * k + 4) (by omega) (by omega) ?_ rfl)
          unfold cfg_CR_U cfg_D1
          rw [encRight_mod2 (2 * k + 1) bR [], hbR_1, encRight_run_s1 (2 * k + 1) [], encRight_nil]
          normalize
          have hd1 := drain_odd_to_d1 a0 z0 k U1 L3 default
          normalize_at hd1
          exact hd1
    · have hbR_1 : bR % 2 = 1 := h_red
      rcases mod2_div d with ⟨k, rfl | rfl⟩
      · refine Or.inl ?_
        unfold cfg_CR_U
        rw [encRight_mod2 (2 * k) bR ((d2, b2) :: R2), hbR_1, encRight_run_s1 (2 * k) ((d2,
            b2) :: R2)]
        normalize
        exact drain_even_halts a0 z0 k U1 L3 ((0 : Fin 2) >> (0 : Fin 2) >> encRight ((d2,
            b2) :: R2)) ⟨_, rfl⟩
      · refine Or.inr ?_
        let w2 := if R2 = [] then 0 else b2 % 2
        have hw2 : w2 = 0 ∨ w2 = 1 := by
          dsimp only [w2]
          split_ifs
          · exact Or.inl rfl
          · exact mod2_cases b2
        have hw2_ne : w2 = 1 → R2 ≠ [] := by
          dsimp only [w2]
          split_ifs with hnil
          · intro h; cases h
          · intro _; exact hnil
        have h_enc_r2 : encRight ((d2, b2) :: R2) =
            (([1] : List (Fin 2)) ^ (d2 + 1)) +> ((([0] : List (Fin 2)) ^ (1 + w2)) +>
                encRight R2) := by
          dsimp only [w2]
          split_ifs with hnil
          · subst hnil
            rcases mod2_cases b2 with hb2 | hb2
            · rw [encRight_mod2 d2 b2 [], hb2, encRight_run_s0 d2 [], encRight_nil]; normalize
            · rw [encRight_mod2 d2 b2 [], hb2, encRight_run_s1 d2 [], encRight_nil]; normalize
          · simp only [encRight_cons, Nat.one_mul]
        have h_to_d1 : (cfg_CR_U ((a0, z0) :: U1) L3 ((2 * k + 1, bR) :: (d2,
            b2) :: R2)) [target_tm]⊢⁺
            cfg_D1 ((a0, z0) :: U1) L3 (2 * k + d2 + 5) w2 R2 := by
          unfold cfg_CR_U cfg_D1
          rw [encRight_mod2 (2 * k + 1) bR ((d2, b2) :: R2), hbR_1,
              encRight_run_s1 (2 * k + 1) ((d2, b2) :: R2), h_enc_r2]
          normalize
          have hd1 := drain_odd_to_d1 a0 z0 k U1 L3 (encRight ((d2, b2) :: R2))
          rw [h_enc_r2, pow_append_pow, show 2 * k + 4 + (d2 + 1) = 2 * k + d2 + 5 by omega] at hd1
          normalize_at hd1
          exact hd1
        obtain ⟨U_mid, R_mid, hU_mid_ne, h_sw, h_post⟩ :=
          d_sweep_u (((a0, z0) :: U1).length) ((a0, z0) :: U1) L3 (2 * k + d2 + 5) w2 R2
            le_rfl h_ge4 (by omega) hw2 hw2_ne
        rcases U_mid with _ | ⟨⟨am, zm⟩, U_mid'⟩
        · exact False.elim (hU_mid_ne rfl)
        obtain ⟨a_f, z_f, U_f, R_f, h_carry, h_red_f, h_len_f, _⟩ :=
          carry_to_reduced R_mid am zm U_mid' L3
        have h_rem_mid : remTailLen R_mid ≤ R2.length := by
          have h_any : ∀ L_any : List (ℕ × ℕ), remTailLen L_any ≤ L_any.length := by
            intro L_any
            induction L_any with
            | nil => simp [remTailLen]
            | cons x xs ih_l =>
              rcases xs with _ | ⟨y, ys⟩
              · simp [remTailLen]
              · simp only [remTailLen, List.length_cons] at ih_l ⊢
                split_ifs <;> omega
          rcases h_post with ⟨hR_eq, _⟩ | ⟨d_out, _, hR_eq, _⟩
          · rw [hR_eq]
            exact h_any R2
          · rw [hR_eq]
            rcases R2 with _ | ⟨y, ys⟩
            · simp [remTailLen]
            · simp only [remTailLen, List.length_cons]
              split_ifs
              · omega
              · have h_ys := h_any (y :: ys)
                simp only [List.length_cons] at h_ys
                omega
        have h_rem_orig : remTailLen ((2 * k + 1, bR) :: (d2, b2) :: R2) = R2.length + 1 := by
          simp [remTailLen, hbR_1]
        refine ⟨(a_f, z_f) :: U_f, R_f,
          stepPlus_stepStar_stepPlus h_to_d1 (stepStar_trans h_sw h_carry),
          h_red_f, Or.inl (by omega)⟩

private theorem cr_u_reduced_closed : ∀ (t : ℕ),
    ∀ (w : ℕ),
    ∀ (p : ℕ),
    ∀ (o : ℕ),
    ∀ (U L3 R : List (ℕ × ℕ)),
      remTailLen R = t →
      wU U = w →
      phiU U = p →
      onesU U = o →
      IsReducedR R →
      (∃ q ∈ U, q.2 ≥ 4) →
      ∃ cfg', ((cfg_CR_U U L3 R) [target_tm]⊢⁺ cfg') ∧
              (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih_t =>
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih_w =>
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih_p =>
        intro o
        induction o using Nat.strong_induction_on with
        | h o ih_o =>
          intro U L3 R ht hw hp ho h_red h_ge4
          rcases cr_u_reduced_step U L3 R h_red h_ge4 with ⟨cfg', hst, hhalt⟩ | ⟨U', R', hst,
              h_red', hdec⟩
          · exact ⟨cfg', hst, Or.inr hhalt⟩
          · rcases all_lt4_or_exists_ge4 U' with h_lt4 | h_ge4'
            · refine ⟨cfg_CR_n_n (U' ++ L3) R', ?_, Or.inl ⟨.CR_n_n, U' ++ L3, R', rfl⟩⟩
              have heq : cfg_CR_U U' L3 R' = cfg_CR_n_n (U' ++ L3) R' := by
                unfold cfg_CR_U cfg_CR_n_n
                rw [encLeftU_eq_encLeft_of_lt4 U' L3 h_lt4]
              rwa [← heq]
            · have h_next : ∃ cfg', ((cfg_CR_U U' L3 R') [target_tm]⊢⁺ cfg') ∧
                  (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
                rcases hdec with ht_lt | ⟨ht_eq, hw_lt⟩ | ⟨ht_eq, hw_eq, hp_lt⟩ | ⟨ht_eq, hw_eq,
                    hp_eq, ho_lt⟩
                · exact ih_t (remTailLen R') (ht ▸ ht_lt) (wU U') (phiU U') (onesU U') U' L3 R' rfl
                      rfl rfl rfl h_red' h_ge4'
                · exact ih_w (wU U') (hw ▸ hw_lt) (phiU U') (onesU U') U' L3 R' (ht_eq.trans ht)
                      rfl rfl rfl h_red' h_ge4'
                · exact ih_p (phiU U') (hp ▸ hp_lt) (onesU U') U' L3 R' (ht_eq.trans ht)
                      (hw_eq.trans hw) rfl rfl h_red' h_ge4'
                · exact ih_o (onesU U') (ho ▸ ho_lt) U' L3 R' (ht_eq.trans ht) (hw_eq.trans hw)
                      (hp_eq.trans hp) rfl h_red' h_ge4'
              obtain ⟨cfg', hst2, hgoal⟩ := h_next
              exact ⟨cfg', stepPlus_stepStar_stepPlus hst (stepPlus_stepStar hst2), hgoal⟩

private theorem cr_dge5_w0_closed (d' aL bL bR d2 b2 : ℕ) (L' R2 : List (ℕ × ℕ)) (hbR_0 : bR % 2 =
    0) :
    ∃ cfg', ((cfg_CR_n_n ((aL, bL) :: L') ((d' + 5, bR) :: (d2, b2) :: R2)) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  have h1 : (cfg_CR_n_n ((aL, bL) :: L') ((d' + 5, bR) :: (d2, b2) :: R2)) [target_tm]⊢⁺
      cfg_CR_U [(1, d' + 4)] ((aL, bL) :: L') ((d2, b2) :: R2) := by
    change ((cfg_CR_U [] ((aL, bL) :: L') (((d' + 4) + 1, bR) :: (d2, b2) :: R2)) [target_tm]⊢⁺ _)
    exact carry_dsucc (d' + 4) [] ((aL, bL) :: L') bR d2 b2 R2 hbR_0
  obtain ⟨a0', z0', U1', R', h_carry, h_red, _, h_split⟩ :=
    carry_to_reduced ((d2, b2) :: R2) 1 (d' + 4) [] ((aL, bL) :: L')
  have h12 : (cfg_CR_n_n ((aL, bL) :: L') ((d' + 5, bR) :: (d2, b2) :: R2)) [target_tm]⊢⁺
      cfg_CR_U ((a0', z0') :: U1') ((aL, bL) :: L') R' :=
    stepPlus_stepStar_stepPlus h1 h_carry
  rcases h_split with h_lt4 | h_ge4
  · refine ⟨cfg_CR_n_n (((a0', z0') :: U1') ++ ((aL, bL) :: L')) R', ?_,
      Or.inl ⟨.CR_n_n, ((a0', z0') :: U1') ++ ((aL, bL) :: L'), R', rfl⟩⟩
    have heq : cfg_CR_U ((a0', z0') :: U1') ((aL, bL) :: L') R' =
        cfg_CR_n_n (((a0', z0') :: U1') ++ ((aL, bL) :: L')) R' := by
      unfold cfg_CR_U cfg_CR_n_n
      rw [encLeftU_eq_encLeft_of_lt4 _ _ h_lt4]
    rwa [← heq]
  · obtain ⟨cfg', hst2, hgoal⟩ :=
      cr_u_reduced_closed (remTailLen R') (wU ((a0', z0') :: U1'))
        (phiU ((a0', z0') :: U1')) (onesU ((a0', z0') :: U1'))
        ((a0', z0') :: U1') ((aL, bL) :: L') R' rfl rfl rfl rfl h_red h_ge4
    exact ⟨cfg', stepPlus_stepStar_stepPlus h12 (stepPlus_stepStar hst2), hgoal⟩

private theorem cr_odd_drain_exit (aL bL k : ℕ) (L' R_rest : List (ℕ × ℕ))
    (hd1 : (⟨some C, ⟨1, encLeft ((aL, bL) :: L'),
      (([1] : List (Fin 2)) ^ (2 * k + 1)) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> encRight R_rest)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some D, ⟨1, (encLeft ((aL, bL) :: L')).tail,
        (([1] : List (Fin 2)) ^ (2 * k + 4)) +> encRight R_rest⟩⟩) :
    ∃ cfg', ((⟨some C, ⟨1, encLeft ((aL, bL) :: L'),
      (([1] : List (Fin 2)) ^ (2 * k + 1)) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> encRight R_rest)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
              cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases aL with _ | _ | a2
  · rcases mod4_cases bL with hb0 | hb1 | hb2 | hb3
    · refine ⟨cfg_FB_n_n L' (bumpN (2 * k + 5) R_rest), stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.FB_n_n, L', bumpN (2 * k + 5) R_rest, rfl⟩⟩
      unfold cfg_FB_n_n
      rw [encLeft_mod4 0 bL L', hb0, encLeft_d0_s0 L', ← encRight_bumpN (2 * k + 5) R_rest]
      normalize
      execute 1
    · refine ⟨cfg_FB_n_n (bumpHead L') (bumpN (2 * k + 5) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.FB_n_n, bumpHead L', bumpN (2 * k + 5) R_rest, rfl⟩⟩
      unfold cfg_FB_n_n
      rw [encLeft_mod4 0 bL L', hb1, encLeft_d0_s1 L', ← encLeft_cons_one L',
          ← encRight_bumpN (2 * k + 5) R_rest]
      normalize
      execute 5
    · refine ⟨cfg_FB_n_n ((0, 0) :: L') (bumpN (2 * k + 5) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.FB_n_n, (0, 0) :: L', bumpN (2 * k + 5) R_rest, rfl⟩⟩
      unfold cfg_FB_n_n
      rw [encLeft_mod4 0 bL L', hb2, encLeft_d0_s2 L', encLeft_d0_s0 L',
          ← encRight_bumpN (2 * k + 5) R_rest]
      normalize
      execute 5
    · refine ⟨cfg_FB_n_n ((0, 1) :: L') (bumpN (2 * k + 5) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.FB_n_n, (0, 1) :: L', bumpN (2 * k + 5) R_rest, rfl⟩⟩
      unfold cfg_FB_n_n
      rw [encLeft_mod4 0 bL L', hb3, encLeft_d0_s3 L', encLeft_d0_s1 L',
          ← encRight_bumpN (2 * k + 5) R_rest]
      normalize
      execute 5
  · rcases mod4_cases bL with hb0 | hb1 | hb2 | hb3
    · refine ⟨cfg_BR_n_n (bumpHead L') (bumpN (2 * k + 6) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.BR_n_n, bumpHead L', bumpN (2 * k + 6) R_rest, rfl⟩⟩
      unfold cfg_BR_n_n
      rw [encLeft_mod4 1 bL L', hb0, encLeft_d1_s0 L', ← encLeft_cons_one L',
          ← encRight_bumpN (2 * k + 6) R_rest]
      normalize
      execute 3
    · refine ⟨cfg_BR_n_n ((0, 0) :: L') (bumpN (2 * k + 6) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.BR_n_n, (0, 0) :: L', bumpN (2 * k + 6) R_rest, rfl⟩⟩
      unfold cfg_BR_n_n
      rw [encLeft_mod4 1 bL L', hb1, encLeft_d1_s1 L', encLeft_d0_s0 L',
          ← encRight_bumpN (2 * k + 6) R_rest]
      normalize
      execute 3
    · refine ⟨cfg_BR_n_n ((0, 1) :: L') (bumpN (2 * k + 6) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.BR_n_n, (0, 1) :: L', bumpN (2 * k + 6) R_rest, rfl⟩⟩
      unfold cfg_BR_n_n
      rw [encLeft_mod4 1 bL L', hb2, encLeft_d1_s2 L', encLeft_d0_s1 L',
          ← encRight_bumpN (2 * k + 6) R_rest]
      normalize
      execute 3
    · refine ⟨cfg_BR_n_n ((0, 2) :: L') (bumpN (2 * k + 6) R_rest),
          stepPlus_stepStar_stepPlus hd1 ?_,
        Or.inl ⟨.BR_n_n, (0, 2) :: L', bumpN (2 * k + 6) R_rest, rfl⟩⟩
      unfold cfg_BR_n_n
      rw [encLeft_mod4 1 bL L', hb3, encLeft_d1_s3 L', encLeft_d0_s2 L',
          ← encRight_bumpN (2 * k + 6) R_rest]
      normalize
      execute 3
  · refine ⟨cfg_AL_n_n ((a2, bL) :: L') (bumpN (2 * k + 6) R_rest),
        stepPlus_stepStar_stepPlus hd1 ?_,
      Or.inl ⟨.AL_n_n, (a2, bL) :: L', bumpN (2 * k + 6) R_rest, rfl⟩⟩
    obtain ⟨TL, hTL⟩ : ∃ (TL : ListBlank (Fin 2)), encLeft ((a2, bL) :: L') =
        (1 : Fin 2) >> TL := by
      rcases mod4_cases bL with h | h | h | h
      · rw [encLeft_mod4 a2 bL L', h, encLeft_run_s0 a2 L']; exact ⟨_, rfl⟩
      · rw [encLeft_mod4 a2 bL L', h, encLeft_run_s1 a2 L']; exact ⟨_, rfl⟩
      · rw [encLeft_mod4 a2 bL L', h, encLeft_run_s2 a2 L']; exact ⟨_, rfl⟩
      · rw [encLeft_mod4 a2 bL L', h, encLeft_run_s3 a2 L']; exact ⟨_, rfl⟩
    unfold cfg_AL_n_n
    rw [encLeft_succ (a2 + 1) bL L', encLeft_succ a2 bL L', hTL,
        ← encRight_bumpN (2 * k + 6) R_rest]
    normalize
    execute 2

-- ============================================================================
-- Mode Closure Lemmas
-- ============================================================================

private theorem mode_BR_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_BR_n_n L R) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases R with _ | ⟨⟨a1, b2⟩, R3⟩
  · refine ⟨cfg_CR_n_n (bumpHead L) [], ?_, Or.inl ⟨.CR_n_n, bumpHead L, [], rfl⟩⟩
    unfold cfg_BR_n_n cfg_CR_n_n
    rw [← encLeft_cons_one L]
    iterate 1 step
    finish
  · rcases mod2_cases b2 with hb4_0 | hb4_1
    · rcases a1 with _ | a7
      · rcases R3 with _ | ⟨⟨a8, b9⟩, R10⟩
        · refine ⟨cfg_CR_n_n (bumpHead (bumpHead L)) [], ?_, Or.inl ⟨.CR_n_n,
              bumpHead (bumpHead L), [], rfl⟩⟩
          unfold cfg_BR_n_n cfg_CR_n_n
          rw [encRight_mod2 0 b2 [], hb4_0, encRight_d0_s0 [], ← encLeft_cons_one (bumpHead L),
              ← encLeft_cons_one L]
          iterate 2 step
          finish
        · rcases mod2_cases b9 with hb11_0 | hb11_1
          · refine ⟨cfg_CR_n_n (bumpHead (bumpHead L)) ((a8, 0) :: R10), ?_, Or.inl ⟨.CR_n_n,
                bumpHead (bumpHead L), (a8, 0) :: R10, rfl⟩⟩
            unfold cfg_BR_n_n cfg_CR_n_n
            rw [encRight_mod2 0 b2 ((a8, b9) :: R10), hb4_0, encRight_d0_s0 ((a8, b9) :: R10),
                encRight_mod2 a8 b9 R10, hb11_0, encRight_run_s0 a8 R10,
                    ← encLeft_cons_one (bumpHead L), ← encLeft_cons_one L]
            iterate 2 step
            finish
          · refine ⟨cfg_CR_n_n (bumpHead (bumpHead L)) ((a8, 1) :: R10), ?_, Or.inl ⟨.CR_n_n,
                bumpHead (bumpHead L), (a8, 1) :: R10, rfl⟩⟩
            unfold cfg_BR_n_n cfg_CR_n_n
            rw [encRight_mod2 0 b2 ((a8, b9) :: R10), hb4_0, encRight_d0_s0 ((a8, b9) :: R10),
                encRight_mod2 a8 b9 R10, hb11_1, encRight_run_s1 a8 R10,
                    ← encLeft_cons_one (bumpHead L), ← encLeft_cons_one L]
            iterate 2 step
            finish
      · refine ⟨cfg_BR_n_n (bumpHead L) ((a7, 0) :: R3), ?_, Or.inl ⟨.BR_n_n, bumpHead L, (a7,
            0) :: R3, rfl⟩⟩
        unfold cfg_BR_n_n
        rw [encRight_mod2 (a7 + 1) b2 R3, hb4_0, encRight_succ a7 0 R3, encRight_run_s0 a7 R3,
            ← encLeft_cons_one L]
        iterate 1 step
        finish
    · rcases a1 with _ | a14
      · rcases R3 with _ | ⟨⟨a15, b16⟩, R17⟩
        · refine ⟨cfg_FR_n_n L [(3, 0)], ?_, Or.inl ⟨.FR_n_n, L, [(3, 0)], rfl⟩⟩
          unfold cfg_BR_n_n cfg_FR_n_n
          rw [encRight_mod2 0 b2 [], hb4_1, encRight_d0_s1 [], encRight_d3_s0 []]
          iterate 6 step
          finish
        · rcases mod2_cases b16 with hb18_0 | hb18_1
          · refine ⟨cfg_FB_n_n (bumpHead (bumpHead L)) ((a15, 0) :: R17), ?_, Or.inl ⟨.FB_n_n,
                bumpHead (bumpHead L), (a15, 0) :: R17, rfl⟩⟩
            unfold cfg_BR_n_n cfg_FB_n_n
            rw [encRight_mod2 0 b2 ((a15, b16) :: R17), hb4_1, encRight_d0_s1 ((a15, b16) :: R17),
                encRight_mod2 a15 b16 R17, hb18_0, encRight_run_s0 a15 R17,
                    ← encLeft_cons_one (bumpHead L), ← encLeft_cons_one L]
            iterate 4 step
            finish
          · refine ⟨cfg_FB_n_n (bumpHead (bumpHead L)) ((a15, 1) :: R17), ?_, Or.inl ⟨.FB_n_n,
                bumpHead (bumpHead L), (a15, 1) :: R17, rfl⟩⟩
            unfold cfg_BR_n_n cfg_FB_n_n
            rw [encRight_mod2 0 b2 ((a15, b16) :: R17), hb4_1, encRight_d0_s1 ((a15, b16) :: R17),
                encRight_mod2 a15 b16 R17, hb18_1, encRight_run_s1 a15 R17,
                    ← encLeft_cons_one (bumpHead L), ← encLeft_cons_one L]
            iterate 4 step
            finish
      · refine ⟨cfg_BR_n_n (bumpHead L) ((a14, 1) :: R3), ?_, Or.inl ⟨.BR_n_n, bumpHead L, (a14,
            1) :: R3, rfl⟩⟩
        unfold cfg_BR_n_n
        rw [encRight_mod2 (a14 + 1) b2 R3, hb4_1, encRight_succ a14 1 R3, encRight_run_s1 a14 R3,
            ← encLeft_cons_one L]
        iterate 1 step
        finish

private theorem mode_FR_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_FR_n_n L R) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases R with _ | ⟨⟨a1, b2⟩, R3⟩
  · rcases L with _ | ⟨⟨a7, b8⟩, L9⟩
    · refine ⟨cfg_BR_n_n [] [], ?_, Or.inl ⟨.BR_n_n, [], [], rfl⟩⟩
      unfold cfg_FR_n_n cfg_BR_n_n
      iterate 1 step
      finish
    · rcases mod4_cases b8 with hb10_0 | hb10_1 | hb10_2 | hb10_3
      · rcases a7 with _ | a15
        · refine ⟨cfg_BR_n_n ((0, 0) :: L9) [], ?_, Or.inl ⟨.BR_n_n, (0, 0) :: L9, [], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 0 b8 L9, hb10_0, encLeft_d0_s0 L9]
          iterate 2 step
          finish
        · refine ⟨cfg_BR_n_n ((a15, 0) :: L9) [(0, 0)], ?_, Or.inl ⟨.BR_n_n, (a15, 0) :: L9, [(0,
              0)], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 (a15 + 1) b8 L9, hb10_0, encLeft_succ a15 0 L9, encLeft_run_s0 a15 L9,
              encRight_d0_s0 []]
          iterate 1 step
          finish
      · rcases a7 with _ | a16
        · refine ⟨cfg_BR_n_n ((0, 1) :: L9) [], ?_, Or.inl ⟨.BR_n_n, (0, 1) :: L9, [], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 0 b8 L9, hb10_1, encLeft_d0_s1 L9]
          iterate 2 step
          finish
        · refine ⟨cfg_BR_n_n ((a16, 1) :: L9) [(0, 0)], ?_, Or.inl ⟨.BR_n_n, (a16, 1) :: L9, [(0,
              0)], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 (a16 + 1) b8 L9, hb10_1, encLeft_succ a16 1 L9, encLeft_run_s1 a16 L9,
              encRight_d0_s0 []]
          iterate 1 step
          finish
      · rcases a7 with _ | a17
        · refine ⟨cfg_BR_n_n ((0, 2) :: L9) [], ?_, Or.inl ⟨.BR_n_n, (0, 2) :: L9, [], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 0 b8 L9, hb10_2, encLeft_d0_s2 L9]
          iterate 2 step
          finish
        · refine ⟨cfg_BR_n_n ((a17, 2) :: L9) [(0, 0)], ?_, Or.inl ⟨.BR_n_n, (a17, 2) :: L9, [(0,
              0)], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 (a17 + 1) b8 L9, hb10_2, encLeft_succ a17 2 L9, encLeft_run_s2 a17 L9,
              encRight_d0_s0 []]
          iterate 1 step
          finish
      · rcases a7 with _ | a18
        · refine ⟨cfg_BR_n_n ((0, 3) :: L9) [], ?_, Or.inl ⟨.BR_n_n, (0, 3) :: L9, [], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 0 b8 L9, hb10_3, encLeft_d0_s3 L9]
          iterate 2 step
          finish
        · refine ⟨cfg_BR_n_n ((a18, 3) :: L9) [(0, 0)], ?_, Or.inl ⟨.BR_n_n, (a18, 3) :: L9, [(0,
              0)], rfl⟩⟩
          unfold cfg_FR_n_n cfg_BR_n_n
          rw [encLeft_mod4 (a18 + 1) b8 L9, hb10_3, encLeft_succ a18 3 L9, encLeft_run_s3 a18 L9,
              encRight_d0_s0 []]
          iterate 1 step
          finish
  · rcases mod2_cases b2 with hb4_0 | hb4_1
    · rcases L with _ | ⟨⟨a19, b20⟩, L21⟩
      · refine ⟨cfg_AL_n_n [] ((a1, 0) :: R3), ?_, Or.inl ⟨.AL_n_n, [], (a1, 0) :: R3, rfl⟩⟩
        unfold cfg_FR_n_n cfg_AL_n_n
        rw [encRight_mod2 a1 b2 R3, hb4_0, encRight_run_s0 a1 R3]
        iterate 1 step
        finish
      · rcases mod4_cases b20 with hb22_0 | hb22_1 | hb22_2 | hb22_3
        · refine ⟨cfg_AL_n_n ((a19, 0) :: L21) ((a1, 0) :: R3), ?_, Or.inl ⟨.AL_n_n, (a19,
              0) :: L21, (a1, 0) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_0, encRight_run_s0 a1 R3, encLeft_mod4 a19 b20 L21,
              hb22_0, encLeft_run_s0 a19 L21]
          iterate 1 step
          finish
        · refine ⟨cfg_AL_n_n ((a19, 1) :: L21) ((a1, 0) :: R3), ?_, Or.inl ⟨.AL_n_n, (a19,
              1) :: L21, (a1, 0) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_0, encRight_run_s0 a1 R3, encLeft_mod4 a19 b20 L21,
              hb22_1, encLeft_run_s1 a19 L21]
          iterate 1 step
          finish
        · refine ⟨cfg_AL_n_n ((a19, 2) :: L21) ((a1, 0) :: R3), ?_, Or.inl ⟨.AL_n_n, (a19,
              2) :: L21, (a1, 0) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_0, encRight_run_s0 a1 R3, encLeft_mod4 a19 b20 L21,
              hb22_2, encLeft_run_s2 a19 L21]
          iterate 1 step
          finish
        · refine ⟨cfg_AL_n_n ((a19, 3) :: L21) ((a1, 0) :: R3), ?_, Or.inl ⟨.AL_n_n, (a19,
              3) :: L21, (a1, 0) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_0, encRight_run_s0 a1 R3, encLeft_mod4 a19 b20 L21,
              hb22_3, encLeft_run_s3 a19 L21]
          iterate 1 step
          finish
    · rcases L with _ | ⟨⟨a27, b28⟩, L29⟩
      · refine ⟨cfg_AL_n_n [] ((a1, 1) :: R3), ?_, Or.inl ⟨.AL_n_n, [], (a1, 1) :: R3, rfl⟩⟩
        unfold cfg_FR_n_n cfg_AL_n_n
        rw [encRight_mod2 a1 b2 R3, hb4_1, encRight_run_s1 a1 R3]
        iterate 1 step
        finish
      · rcases mod4_cases b28 with hb30_0 | hb30_1 | hb30_2 | hb30_3
        · refine ⟨cfg_AL_n_n ((a27, 0) :: L29) ((a1, 1) :: R3), ?_, Or.inl ⟨.AL_n_n, (a27,
              0) :: L29, (a1, 1) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_1, encRight_run_s1 a1 R3, encLeft_mod4 a27 b28 L29,
              hb30_0, encLeft_run_s0 a27 L29]
          iterate 1 step
          finish
        · refine ⟨cfg_AL_n_n ((a27, 1) :: L29) ((a1, 1) :: R3), ?_, Or.inl ⟨.AL_n_n, (a27,
              1) :: L29, (a1, 1) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_1, encRight_run_s1 a1 R3, encLeft_mod4 a27 b28 L29,
              hb30_1, encLeft_run_s1 a27 L29]
          iterate 1 step
          finish
        · refine ⟨cfg_AL_n_n ((a27, 2) :: L29) ((a1, 1) :: R3), ?_, Or.inl ⟨.AL_n_n, (a27,
              2) :: L29, (a1, 1) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_1, encRight_run_s1 a1 R3, encLeft_mod4 a27 b28 L29,
              hb30_2, encLeft_run_s2 a27 L29]
          iterate 1 step
          finish
        · refine ⟨cfg_AL_n_n ((a27, 3) :: L29) ((a1, 1) :: R3), ?_, Or.inl ⟨.AL_n_n, (a27,
              3) :: L29, (a1, 1) :: R3, rfl⟩⟩
          unfold cfg_FR_n_n cfg_AL_n_n
          rw [encRight_mod2 a1 b2 R3, hb4_1, encRight_run_s1 a1 R3, encLeft_mod4 a27 b28 L29,
              hb30_3, encLeft_run_s3 a27 L29]
          iterate 1 step
          finish

private theorem mode_AL_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_AL_n_n L R) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
  · rcases R with _ | ⟨⟨a9, b10⟩, R11⟩
    · refine ⟨cfg_BR_n_n [(0, 0)] [], ?_, Or.inl ⟨.BR_n_n, [(0, 0)], [], rfl⟩⟩
      unfold cfg_AL_n_n cfg_BR_n_n
      rw [encLeft_d0_s0 []]
      iterate 1 step
      finish
    · rcases mod2_cases b10 with hb12_0 | hb12_1
      · refine ⟨cfg_BR_n_n [(0, 0)] ((a9, 0) :: R11), ?_, Or.inl ⟨.BR_n_n, [(0, 0)], (a9,
            0) :: R11, rfl⟩⟩
        unfold cfg_AL_n_n cfg_BR_n_n
        rw [encRight_mod2 a9 b10 R11, hb12_0, encRight_run_s0 a9 R11, encLeft_d0_s0 []]
        iterate 1 step
        finish
      · refine ⟨cfg_BR_n_n [(0, 0)] ((a9, 1) :: R11), ?_, Or.inl ⟨.BR_n_n, [(0, 0)], (a9,
            1) :: R11, rfl⟩⟩
        unfold cfg_AL_n_n cfg_BR_n_n
        rw [encRight_mod2 a9 b10 R11, hb12_1, encRight_run_s1 a9 R11, encLeft_d0_s0 []]
        iterate 1 step
        finish
  · rcases mod4_cases b2 with hb4_0 | hb4_1 | hb4_2 | hb4_3
    · rcases a1 with _ | a15
      · rcases L3 with _ | ⟨⟨a16, b17⟩, L18⟩
        · refine ⟨cfg_FB_n_n [] (bumpHead (bumpHead (bumpHead R))), ?_, Or.inl ⟨.FB_n_n, [],
              bumpHead (bumpHead (bumpHead R)), rfl⟩⟩
          unfold cfg_AL_n_n cfg_FB_n_n
          rw [encLeft_mod4 0 b2 [], hb4_0, encLeft_d0_s0 [],
              ← encRight_cons_one (bumpHead (bumpHead R)), ← encRight_cons_one (bumpHead R),
                  ← encRight_cons_one R]
          iterate 7 step
          finish
        · rcases mod4_cases b17 with hb19_0 | hb19_1 | hb19_2 | hb19_3
          · rcases a16 with _ | a24
            · rcases R with _ | ⟨⟨a25, b26⟩, R27⟩
              · refine ⟨cfg_BR_n_n (bumpHead L18) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, bumpHead L18, [(3,
                    0)], rfl⟩⟩
                unfold cfg_AL_n_n cfg_BR_n_n
                rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                    b17) :: L18), encLeft_mod4 0 b17 L18, hb19_0, encLeft_d0_s0 L18,
                        ← encLeft_cons_one L18, encRight_d3_s0 []]
                iterate 10 step
                finish
              · rcases mod2_cases b26 with hb28_0 | hb28_1
                · refine ⟨cfg_FB_n_n ((1, 0) :: L18) ((a25, 0) :: R27), ?_, Or.inl ⟨.FB_n_n, (1,
                      0) :: L18, (a25, 0) :: R27, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_0, encLeft_d0_s0 L18,
                          encRight_mod2 a25 b26 R27, hb28_0, encRight_run_s0 a25 R27,
                              encLeft_d1_s0 L18]
                  iterate 6 step
                  finish
                · refine ⟨cfg_FB_n_n ((1, 0) :: L18) ((a25, 1) :: R27), ?_, Or.inl ⟨.FB_n_n, (1,
                      0) :: L18, (a25, 1) :: R27, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_0, encLeft_d0_s0 L18,
                          encRight_mod2 a25 b26 R27, hb28_1, encRight_run_s1 a25 R27,
                              encLeft_d1_s0 L18]
                  iterate 6 step
                  finish
            · refine ⟨cfg_BR_n_n ((a24, 0) :: L18) ((0, 1) :: R), ?_, Or.inl ⟨.BR_n_n, (a24,
                  0) :: L18, (0, 1) :: R, rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((a24 + 1), b17) :: L18), hb4_0, encLeft_d0_s0 (((a24 + 1),
                  b17) :: L18), encLeft_mod4 (a24 + 1) b17 L18, hb19_0, encLeft_succ a24 0 L18,
                      encLeft_run_s0 a24 L18, encRight_d0_s1 R]
              iterate 2 step
              finish
          · rcases a16 with _ | a31
            · rcases R with _ | ⟨⟨a32, b33⟩, R34⟩
              · refine ⟨cfg_BR_n_n ((0, 0) :: L18) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, (0, 0) :: L18,
                    [(3, 0)], rfl⟩⟩
                unfold cfg_AL_n_n cfg_BR_n_n
                rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                    b17) :: L18), encLeft_mod4 0 b17 L18, hb19_1, encLeft_d0_s1 L18,
                        encLeft_d0_s0 L18, encRight_d3_s0 []]
                iterate 10 step
                finish
              · rcases mod2_cases b33 with hb35_0 | hb35_1
                · refine ⟨cfg_FB_n_n ((1, 1) :: L18) ((a32, 0) :: R34), ?_, Or.inl ⟨.FB_n_n, (1,
                      1) :: L18, (a32, 0) :: R34, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_1, encLeft_d0_s1 L18,
                          encRight_mod2 a32 b33 R34, hb35_0, encRight_run_s0 a32 R34,
                              encLeft_d1_s1 L18]
                  iterate 6 step
                  finish
                · refine ⟨cfg_FB_n_n ((1, 1) :: L18) ((a32, 1) :: R34), ?_, Or.inl ⟨.FB_n_n, (1,
                      1) :: L18, (a32, 1) :: R34, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_1, encLeft_d0_s1 L18,
                          encRight_mod2 a32 b33 R34, hb35_1, encRight_run_s1 a32 R34,
                              encLeft_d1_s1 L18]
                  iterate 6 step
                  finish
            · refine ⟨cfg_BR_n_n ((a31, 1) :: L18) ((0, 1) :: R), ?_, Or.inl ⟨.BR_n_n, (a31,
                  1) :: L18, (0, 1) :: R, rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((a31 + 1), b17) :: L18), hb4_0, encLeft_d0_s0 (((a31 + 1),
                  b17) :: L18), encLeft_mod4 (a31 + 1) b17 L18, hb19_1, encLeft_succ a31 1 L18,
                      encLeft_run_s1 a31 L18, encRight_d0_s1 R]
              iterate 2 step
              finish
          · rcases a16 with _ | a38
            · rcases R with _ | ⟨⟨a39, b40⟩, R41⟩
              · refine ⟨cfg_BR_n_n ((0, 1) :: L18) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, (0, 1) :: L18,
                    [(3, 0)], rfl⟩⟩
                unfold cfg_AL_n_n cfg_BR_n_n
                rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                    b17) :: L18), encLeft_mod4 0 b17 L18, hb19_2, encLeft_d0_s2 L18,
                        encLeft_d0_s1 L18, encRight_d3_s0 []]
                iterate 10 step
                finish
              · rcases mod2_cases b40 with hb42_0 | hb42_1
                · refine ⟨cfg_FB_n_n ((1, 2) :: L18) ((a39, 0) :: R41), ?_, Or.inl ⟨.FB_n_n, (1,
                      2) :: L18, (a39, 0) :: R41, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_2, encLeft_d0_s2 L18,
                          encRight_mod2 a39 b40 R41, hb42_0, encRight_run_s0 a39 R41,
                              encLeft_d1_s2 L18]
                  iterate 6 step
                  finish
                · refine ⟨cfg_FB_n_n ((1, 2) :: L18) ((a39, 1) :: R41), ?_, Or.inl ⟨.FB_n_n, (1,
                      2) :: L18, (a39, 1) :: R41, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_2, encLeft_d0_s2 L18,
                          encRight_mod2 a39 b40 R41, hb42_1, encRight_run_s1 a39 R41,
                              encLeft_d1_s2 L18]
                  iterate 6 step
                  finish
            · refine ⟨cfg_BR_n_n ((a38, 2) :: L18) ((0, 1) :: R), ?_, Or.inl ⟨.BR_n_n, (a38,
                  2) :: L18, (0, 1) :: R, rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((a38 + 1), b17) :: L18), hb4_0, encLeft_d0_s0 (((a38 + 1),
                  b17) :: L18), encLeft_mod4 (a38 + 1) b17 L18, hb19_2, encLeft_succ a38 2 L18,
                      encLeft_run_s2 a38 L18, encRight_d0_s1 R]
              iterate 2 step
              finish
          · rcases a16 with _ | a45
            · rcases R with _ | ⟨⟨a46, b47⟩, R48⟩
              · refine ⟨cfg_BR_n_n ((0, 2) :: L18) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, (0, 2) :: L18,
                    [(3, 0)], rfl⟩⟩
                unfold cfg_AL_n_n cfg_BR_n_n
                rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                    b17) :: L18), encLeft_mod4 0 b17 L18, hb19_3, encLeft_d0_s3 L18,
                        encLeft_d0_s2 L18, encRight_d3_s0 []]
                iterate 10 step
                finish
              · rcases mod2_cases b47 with hb49_0 | hb49_1
                · refine ⟨cfg_FB_n_n ((1, 3) :: L18) ((a46, 0) :: R48), ?_, Or.inl ⟨.FB_n_n, (1,
                      3) :: L18, (a46, 0) :: R48, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_3, encLeft_d0_s3 L18,
                          encRight_mod2 a46 b47 R48, hb49_0, encRight_run_s0 a46 R48,
                              encLeft_d1_s3 L18]
                  iterate 6 step
                  finish
                · refine ⟨cfg_FB_n_n ((1, 3) :: L18) ((a46, 1) :: R48), ?_, Or.inl ⟨.FB_n_n, (1,
                      3) :: L18, (a46, 1) :: R48, rfl⟩⟩
                  unfold cfg_AL_n_n cfg_FB_n_n
                  rw [encLeft_mod4 0 b2 (((0), b17) :: L18), hb4_0, encLeft_d0_s0 (((0),
                      b17) :: L18), encLeft_mod4 0 b17 L18, hb19_3, encLeft_d0_s3 L18,
                          encRight_mod2 a46 b47 R48, hb49_1, encRight_run_s1 a46 R48,
                              encLeft_d1_s3 L18]
                  iterate 6 step
                  finish
            · refine ⟨cfg_BR_n_n ((a45, 3) :: L18) ((0, 1) :: R), ?_, Or.inl ⟨.BR_n_n, (a45,
                  3) :: L18, (0, 1) :: R, rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((a45 + 1), b17) :: L18), hb4_0, encLeft_d0_s0 (((a45 + 1),
                  b17) :: L18), encLeft_mod4 (a45 + 1) b17 L18, hb19_3, encLeft_succ a45 3 L18,
                      encLeft_run_s3 a45 L18, encRight_d0_s1 R]
              iterate 2 step
              finish
      · rcases a15 with _ | a52
        · refine ⟨cfg_BR_n_n (bumpHead L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, bumpHead L3, (0,
              0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_BR_n_n
          rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_0, encLeft_d1_s0 L3, ← encLeft_cons_one L3,
              encRight_d0_s0 R]
          iterate 3 step
          finish
        · refine ⟨cfg_FR_n_n ((a52, 0) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.FR_n_n, (a52, 0) :: L3,
              (0, 0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_FR_n_n
          rw [encLeft_mod4 ((a52 + 1) + 1) b2 L3, hb4_0, encLeft_succ (a52 + 1) 0 L3,
              encLeft_succ a52 0 L3, encLeft_run_s0 a52 L3, encRight_d0_s0 R]
          iterate 1 step
          finish
    · rcases a1 with _ | a53
      · rcases L3 with _ | ⟨⟨a54, b55⟩, L56⟩
        · refine ⟨cfg_FB_n_n [] (bumpHead (bumpHead (bumpHead R))), ?_, Or.inl ⟨.FB_n_n, [],
              bumpHead (bumpHead (bumpHead R)), rfl⟩⟩
          unfold cfg_AL_n_n cfg_FB_n_n
          rw [encLeft_mod4 0 b2 [], hb4_1, encLeft_d0_s1 [],
              ← encRight_cons_one (bumpHead (bumpHead R)), ← encRight_cons_one (bumpHead R),
                  ← encRight_cons_one R]
          iterate 7 step
          finish
        · rcases mod4_cases b55 with hb57_0 | hb57_1 | hb57_2 | hb57_3
          · rcases a54 with _ | a62
            · refine ⟨cfg_BR_n_n (bumpHead L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))), ?_,
                  Or.inl ⟨.BR_n_n, bumpHead L56, bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((0), b55) :: L56), hb4_1, encLeft_d0_s1 (((0), b55) :: L56),
                  encLeft_mod4 0 b55 L56, hb57_0, encLeft_d0_s0 L56, ← encLeft_cons_one L56,
                      ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                          ← encRight_cons_one (bumpHead (bumpHead R)),
                              ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 9 step
              finish
            · refine ⟨cfg_FR_n_n ((a62, 0) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))),
                  ?_, Or.inl ⟨.FR_n_n, (a62, 0) :: L56,
                      bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_FR_n_n
              rw [encLeft_mod4 0 b2 (((a62 + 1), b55) :: L56), hb4_1, encLeft_d0_s1 (((a62 + 1),
                  b55) :: L56), encLeft_mod4 (a62 + 1) b55 L56, hb57_0, encLeft_succ a62 0 L56,
                      encLeft_run_s0 a62 L56,
                          ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                              ← encRight_cons_one (bumpHead (bumpHead R)),
                                  ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 7 step
              finish
          · rcases a54 with _ | a63
            · refine ⟨cfg_BR_n_n ((0, 0) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))), ?_,
                  Or.inl ⟨.BR_n_n, (0, 0) :: L56, bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((0), b55) :: L56), hb4_1, encLeft_d0_s1 (((0), b55) :: L56),
                  encLeft_mod4 0 b55 L56, hb57_1, encLeft_d0_s1 L56, encLeft_d0_s0 L56,
                      ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                          ← encRight_cons_one (bumpHead (bumpHead R)),
                              ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 9 step
              finish
            · refine ⟨cfg_FR_n_n ((a63, 1) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))),
                  ?_, Or.inl ⟨.FR_n_n, (a63, 1) :: L56,
                      bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_FR_n_n
              rw [encLeft_mod4 0 b2 (((a63 + 1), b55) :: L56), hb4_1, encLeft_d0_s1 (((a63 + 1),
                  b55) :: L56), encLeft_mod4 (a63 + 1) b55 L56, hb57_1, encLeft_succ a63 1 L56,
                      encLeft_run_s1 a63 L56,
                          ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                              ← encRight_cons_one (bumpHead (bumpHead R)),
                                  ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 7 step
              finish
          · rcases a54 with _ | a64
            · refine ⟨cfg_BR_n_n ((0, 1) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))), ?_,
                  Or.inl ⟨.BR_n_n, (0, 1) :: L56, bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((0), b55) :: L56), hb4_1, encLeft_d0_s1 (((0), b55) :: L56),
                  encLeft_mod4 0 b55 L56, hb57_2, encLeft_d0_s2 L56, encLeft_d0_s1 L56,
                      ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                          ← encRight_cons_one (bumpHead (bumpHead R)),
                              ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 9 step
              finish
            · refine ⟨cfg_FR_n_n ((a64, 2) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))),
                  ?_, Or.inl ⟨.FR_n_n, (a64, 2) :: L56,
                      bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_FR_n_n
              rw [encLeft_mod4 0 b2 (((a64 + 1), b55) :: L56), hb4_1, encLeft_d0_s1 (((a64 + 1),
                  b55) :: L56), encLeft_mod4 (a64 + 1) b55 L56, hb57_2, encLeft_succ a64 2 L56,
                      encLeft_run_s2 a64 L56,
                          ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                              ← encRight_cons_one (bumpHead (bumpHead R)),
                                  ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 7 step
              finish
          · rcases a54 with _ | a65
            · refine ⟨cfg_BR_n_n ((0, 2) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))), ?_,
                  Or.inl ⟨.BR_n_n, (0, 2) :: L56, bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_BR_n_n
              rw [encLeft_mod4 0 b2 (((0), b55) :: L56), hb4_1, encLeft_d0_s1 (((0), b55) :: L56),
                  encLeft_mod4 0 b55 L56, hb57_3, encLeft_d0_s3 L56, encLeft_d0_s2 L56,
                      ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                          ← encRight_cons_one (bumpHead (bumpHead R)),
                              ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 9 step
              finish
            · refine ⟨cfg_FR_n_n ((a65, 3) :: L56) (bumpHead (bumpHead (bumpHead (bumpHead R)))),
                  ?_, Or.inl ⟨.FR_n_n, (a65, 3) :: L56,
                      bumpHead (bumpHead (bumpHead (bumpHead R))), rfl⟩⟩
              unfold cfg_AL_n_n cfg_FR_n_n
              rw [encLeft_mod4 0 b2 (((a65 + 1), b55) :: L56), hb4_1, encLeft_d0_s1 (((a65 + 1),
                  b55) :: L56), encLeft_mod4 (a65 + 1) b55 L56, hb57_3, encLeft_succ a65 3 L56,
                      encLeft_run_s3 a65 L56,
                          ← encRight_cons_one (bumpHead (bumpHead (bumpHead R))),
                              ← encRight_cons_one (bumpHead (bumpHead R)),
                                  ← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
              iterate 7 step
              finish
      · rcases a53 with _ | a66
        · refine ⟨cfg_BR_n_n ((0, 0) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (0, 0) :: L3, (0,
              0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_BR_n_n
          rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_1, encLeft_d1_s1 L3, encLeft_d0_s0 L3,
              encRight_d0_s0 R]
          iterate 3 step
          finish
        · refine ⟨cfg_FR_n_n ((a66, 1) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.FR_n_n, (a66, 1) :: L3,
              (0, 0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_FR_n_n
          rw [encLeft_mod4 ((a66 + 1) + 1) b2 L3, hb4_1, encLeft_succ (a66 + 1) 1 L3,
              encLeft_succ a66 1 L3, encLeft_run_s1 a66 L3, encRight_d0_s0 R]
          iterate 1 step
          finish
    · rcases a1 with _ | a67
      · refine ⟨cfg_FB_n_n L3 (bumpHead (bumpHead (bumpHead R))), ?_, Or.inl ⟨.FB_n_n, L3,
            bumpHead (bumpHead (bumpHead R)), rfl⟩⟩
        unfold cfg_AL_n_n cfg_FB_n_n
        rw [encLeft_mod4 0 b2 L3, hb4_2, encLeft_d0_s2 L3,
            ← encRight_cons_one (bumpHead (bumpHead R)), ← encRight_cons_one (bumpHead R),
                ← encRight_cons_one R]
        iterate 7 step
        finish
      · rcases a67 with _ | a68
        · refine ⟨cfg_BR_n_n ((0, 1) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (0, 1) :: L3, (0,
              0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_BR_n_n
          rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_2, encLeft_d1_s2 L3, encLeft_d0_s1 L3,
              encRight_d0_s0 R]
          iterate 3 step
          finish
        · refine ⟨cfg_FR_n_n ((a68, 2) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.FR_n_n, (a68, 2) :: L3,
              (0, 0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_FR_n_n
          rw [encLeft_mod4 ((a68 + 1) + 1) b2 L3, hb4_2, encLeft_succ (a68 + 1) 2 L3,
              encLeft_succ a68 2 L3, encLeft_run_s2 a68 L3, encRight_d0_s0 R]
          iterate 1 step
          finish
    · rcases a1 with _ | a69
      · refine ⟨cfg_FB_n_n (bumpHead L3) (bumpHead (bumpHead (bumpHead R))), ?_, Or.inl ⟨.FB_n_n,
            bumpHead L3, bumpHead (bumpHead (bumpHead R)), rfl⟩⟩
        unfold cfg_AL_n_n cfg_FB_n_n
        rw [encLeft_mod4 0 b2 L3, hb4_3, encLeft_d0_s3 L3, ← encLeft_cons_one L3,
            ← encRight_cons_one (bumpHead (bumpHead R)), ← encRight_cons_one (bumpHead R),
                ← encRight_cons_one R]
        iterate 11 step
        finish
      · rcases a69 with _ | a70
        · refine ⟨cfg_BR_n_n ((0, 2) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (0, 2) :: L3, (0,
              0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_BR_n_n
          rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_3, encLeft_d1_s3 L3, encLeft_d0_s2 L3,
              encRight_d0_s0 R]
          iterate 3 step
          finish
        · refine ⟨cfg_FR_n_n ((a70, 3) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.FR_n_n, (a70, 3) :: L3,
              (0, 0) :: R, rfl⟩⟩
          unfold cfg_AL_n_n cfg_FR_n_n
          rw [encLeft_mod4 ((a70 + 1) + 1) b2 L3, hb4_3, encLeft_succ (a70 + 1) 3 L3,
              encLeft_succ a70 3 L3, encLeft_run_s3 a70 L3, encRight_d0_s0 R]
          iterate 1 step
          finish

private theorem mode_DB_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_DB_n_n L R) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
  · refine ⟨cfg_DB_n_n [] (bumpHead (bumpHead R)), ?_, Or.inl ⟨.DB_n_n, [], bumpHead (bumpHead R),
        rfl⟩⟩
    unfold cfg_DB_n_n
    rw [← encRight_cons_one (bumpHead R), ← encRight_cons_one R]
    iterate 2 step
    finish
  · rcases mod4_cases b2 with hb4_0 | hb4_1 | hb4_2 | hb4_3
    · refine ⟨⟨some E, ⟨1, (([1] : List (Fin 2)) ^ a1) +>
          ((0 : Fin 2) >> encLeft L3), (1 : Fin 2) >> encRight R⟩⟩, ?_, Or.inr rfl⟩
      unfold cfg_DB_n_n
      rw [encLeft_mod4 a1 b2 L3, hb4_0, encLeft_run_s0 a1 L3]
      iterate 1 step
      finish
    · refine ⟨⟨some E, ⟨1, (([1] : List (Fin 2)) ^ a1) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> encLeft L3), (1 : Fin 2) >> encRight R⟩⟩, ?_, Or.inr rfl⟩
      unfold cfg_DB_n_n
      rw [encLeft_mod4 a1 b2 L3, hb4_1, encLeft_run_s1 a1 L3]
      iterate 1 step
      finish
    · refine ⟨⟨some E, ⟨1, (([1] : List (Fin 2)) ^ a1) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L3), (1 : Fin 2) >> encRight R⟩⟩,
              ?_, Or.inr rfl⟩
      unfold cfg_DB_n_n
      rw [encLeft_mod4 a1 b2 L3, hb4_2, encLeft_run_s2 a1 L3]
      iterate 1 step
      finish
    · refine ⟨⟨some E, ⟨1, (([1] : List (Fin 2)) ^ a1) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L3),
              (1 : Fin 2) >> encRight R⟩⟩, ?_, Or.inr rfl⟩
      unfold cfg_DB_n_n
      rw [encLeft_mod4 a1 b2 L3, hb4_3, encLeft_run_s3 a1 L3]
      iterate 1 step
      finish

private theorem mode_CR_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_CR_n_n L R) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases R with _ | ⟨⟨d, bR⟩, R'⟩
  · rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
    · refine ⟨cfg_DB_n_n [] [(1, 0)], ?_, Or.inl ⟨.DB_n_n, [], [(1, 0)], rfl⟩⟩
      unfold cfg_CR_n_n cfg_DB_n_n
      rw [encRight_d1_s0 []]
      iterate 3 step
      finish
    · rcases mod4_cases b2 with hb4_0 | hb4_1 | hb4_2 | hb4_3
      · rcases a1 with _ | a9
        · refine ⟨cfg_FB_n_n L3 [(2, 0)], ?_, Or.inl ⟨.FB_n_n, L3, [(2, 0)], rfl⟩⟩
          unfold cfg_CR_n_n cfg_FB_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_0, encLeft_d0_s0 L3, encRight_d2_s0 []]
          iterate 4 step
          finish
        · rcases a9 with _ | a10
          · refine ⟨cfg_BR_n_n (bumpHead L3) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, bumpHead L3, [(3, 0)],
                rfl⟩⟩
            unfold cfg_CR_n_n cfg_BR_n_n
            rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_0, encLeft_d1_s0 L3, ← encLeft_cons_one L3,
                encRight_d3_s0 []]
            iterate 6 step
            finish
          · refine ⟨cfg_FR_n_n ((a10, 0) :: L3) [(3, 0)], ?_, Or.inl ⟨.FR_n_n, (a10, 0) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_FR_n_n
            rw [encLeft_mod4 ((a10 + 1) + 1) b2 L3, hb4_0, encLeft_succ (a10 + 1) 0 L3,
                encLeft_succ a10 0 L3, encLeft_run_s0 a10 L3, encRight_d3_s0 []]
            iterate 4 step
            finish
      · rcases a1 with _ | a11
        · refine ⟨cfg_FB_n_n (bumpHead L3) [(2, 0)], ?_, Or.inl ⟨.FB_n_n, bumpHead L3, [(2, 0)],
              rfl⟩⟩
          unfold cfg_CR_n_n cfg_FB_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_1, encLeft_d0_s1 L3, ← encLeft_cons_one L3,
              encRight_d2_s0 []]
          iterate 8 step
          finish
        · rcases a11 with _ | a12
          · refine ⟨cfg_BR_n_n ((0, 0) :: L3) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, (0, 0) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_BR_n_n
            rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_1, encLeft_d1_s1 L3, encLeft_d0_s0 L3,
                encRight_d3_s0 []]
            iterate 6 step
            finish
          · refine ⟨cfg_FR_n_n ((a12, 1) :: L3) [(3, 0)], ?_, Or.inl ⟨.FR_n_n, (a12, 1) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_FR_n_n
            rw [encLeft_mod4 ((a12 + 1) + 1) b2 L3, hb4_1, encLeft_succ (a12 + 1) 1 L3,
                encLeft_succ a12 1 L3, encLeft_run_s1 a12 L3, encRight_d3_s0 []]
            iterate 4 step
            finish
      · rcases a1 with _ | a13
        · refine ⟨cfg_FB_n_n ((0, 0) :: L3) [(2, 0)], ?_, Or.inl ⟨.FB_n_n, (0, 0) :: L3, [(2, 0)],
              rfl⟩⟩
          unfold cfg_CR_n_n cfg_FB_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_2, encLeft_d0_s2 L3, encLeft_d0_s0 L3, encRight_d2_s0 []]
          iterate 8 step
          finish
        · rcases a13 with _ | a14
          · refine ⟨cfg_BR_n_n ((0, 1) :: L3) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, (0, 1) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_BR_n_n
            rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_2, encLeft_d1_s2 L3, encLeft_d0_s1 L3,
                encRight_d3_s0 []]
            iterate 6 step
            finish
          · refine ⟨cfg_FR_n_n ((a14, 2) :: L3) [(3, 0)], ?_, Or.inl ⟨.FR_n_n, (a14, 2) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_FR_n_n
            rw [encLeft_mod4 ((a14 + 1) + 1) b2 L3, hb4_2, encLeft_succ (a14 + 1) 2 L3,
                encLeft_succ a14 2 L3, encLeft_run_s2 a14 L3, encRight_d3_s0 []]
            iterate 4 step
            finish
      · rcases a1 with _ | a15
        · refine ⟨cfg_FB_n_n ((0, 1) :: L3) [(2, 0)], ?_, Or.inl ⟨.FB_n_n, (0, 1) :: L3, [(2, 0)],
              rfl⟩⟩
          unfold cfg_CR_n_n cfg_FB_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_3, encLeft_d0_s3 L3, encLeft_d0_s1 L3, encRight_d2_s0 []]
          iterate 8 step
          finish
        · rcases a15 with _ | a16
          · refine ⟨cfg_BR_n_n ((0, 2) :: L3) [(3, 0)], ?_, Or.inl ⟨.BR_n_n, (0, 2) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_BR_n_n
            rw [encLeft_mod4 ((0) + 1) b2 L3, hb4_3, encLeft_d1_s3 L3, encLeft_d0_s2 L3,
                encRight_d3_s0 []]
            iterate 6 step
            finish
          · refine ⟨cfg_FR_n_n ((a16, 3) :: L3) [(3, 0)], ?_, Or.inl ⟨.FR_n_n, (a16, 3) :: L3, [(3,
                0)], rfl⟩⟩
            unfold cfg_CR_n_n cfg_FR_n_n
            rw [encLeft_mod4 ((a16 + 1) + 1) b2 L3, hb4_3, encLeft_succ (a16 + 1) 3 L3,
                encLeft_succ a16 3 L3, encLeft_run_s3 a16 L3, encRight_d3_s0 []]
            iterate 4 step
            finish
  · -- R = (d, bR) :: R'
    rcases L with _ | ⟨⟨aL, bL⟩, L'⟩
    · -- L = []
      rcases d with _ | d'
      · rcases mod2_cases bR with hbR_0 | hbR_1
        · rcases R' with _ | ⟨⟨d2, b2⟩, R2⟩
          · refine ⟨cfg_DB_n_n [] [], ?_, Or.inl ⟨.DB_n_n, [], [], rfl⟩⟩
            unfold cfg_CR_n_n cfg_DB_n_n
            rw [encRight_mod2 0 bR [], hbR_0, encRight_d0_s0 []]
            execute 2
          · rcases mod2_cases b2 with hb2_0 | hb2_1
            · refine ⟨cfg_FB_n_n [] ((d2, 0) :: R2), ?_, Or.inl ⟨.FB_n_n, [], (d2, 0) :: R2, rfl⟩⟩
              unfold cfg_CR_n_n cfg_FB_n_n
              rw [encRight_mod2 0 bR ((d2, b2) :: R2), hbR_0, encRight_d0_s0 ((d2, b2) :: R2),
                  encRight_mod2 d2 b2 R2, hb2_0, encRight_run_s0 d2 R2]
              execute 3
            · refine ⟨cfg_FB_n_n [] ((d2, 1) :: R2), ?_, Or.inl ⟨.FB_n_n, [], (d2, 1) :: R2, rfl⟩⟩
              unfold cfg_CR_n_n cfg_FB_n_n
              rw [encRight_mod2 0 bR ((d2, b2) :: R2), hbR_0, encRight_d0_s0 ((d2, b2) :: R2),
                  encRight_mod2 d2 b2 R2, hb2_1, encRight_run_s1 d2 R2]
              execute 3
        · refine ⟨cfg_DB_n_n [] R', ?_, Or.inl ⟨.DB_n_n, [], R', rfl⟩⟩
          unfold cfg_CR_n_n cfg_DB_n_n
          rw [encRight_mod2 0 bR R', hbR_1, encRight_d0_s1 R']
          execute 2
      · refine ⟨cfg_CR_n_n [] ((d', bR) :: R'), ?_, Or.inl ⟨.CR_n_n, [], (d', bR) :: R', rfl⟩⟩
        unfold cfg_CR_n_n
        rw [encRight_succ d' bR R']
        execute 1
    · -- L = (aL, bL) :: L'
      rcases mod2_cases bR with hbR_0 | hbR_1
      · rcases R' with _ | ⟨⟨d2, b2⟩, R2⟩
        · -- R = [(d, bR)], hbR_0 : bR % 2 = 0
          rcases mod2_div d with ⟨k, rfl | rfl⟩
          · have h_halt : ∃ cfg', (((cfg_CR_n_n ((aL, bL) :: L') [(2 * k, bR)]) [target_tm]⊢⁺
                cfg') ∧
                (step target_tm cfg').isNone) := by
              unfold cfg_CR_n_n
              rw [encLeft_eq_encLeftU_singleton aL bL L', encRight_mod2 (2 * k) bR [], hbR_0,
                  encRight_run_s0 (2 * k) [], encRight_nil]
              normalize
              exact drain_even_halts aL (bL % 4) k [] L' default ⟨default, by simp⟩
            obtain ⟨cfg', hst, hh⟩ := h_halt
            exact ⟨cfg', hst, Or.inr hh⟩
          · have h_nil0 : (0 : Fin 2) >> encRight [] =
                (0 : Fin 2) >> (0 : Fin 2) >> encRight [] := by
              simp only [encRight_nil, zero_cons_default]
            unfold cfg_CR_n_n
            rw [encRight_mod2 (2 * k + 1) bR [], hbR_0, encRight_run_s0 (2 * k + 1) [], h_nil0]
            simp only [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
            have hd1 : (⟨some C, ⟨1, encLeft ((aL, bL) :: L'),
                (([1] : List (Fin 2)) ^ (2 * k + 1)) +>
                    ((0 : Fin 2) >> (0 : Fin 2) >> encRight [])⟩⟩ : Cfg (Fin 2) (Fin 6))
                        [target_tm]⊢⁺
              ⟨some D, ⟨1, (encLeft ((aL, bL) :: L')).tail,
                (([1] : List (Fin 2)) ^ (2 * k + 4)) +> encRight []⟩⟩ := by
              rw [encLeft_eq_encLeftU_singleton aL bL L']
              exact drain_odd_to_d1 aL (bL % 4) k [] L' (encRight [])
            exact cr_odd_drain_exit aL bL k L' [] hd1
        · -- R = (d, bR) :: (d2, b2) :: R2, hbR_0 : bR % 2 = 0
          rcases d with _ | _ | _ | _ | _ | d'
          · refine ⟨cfg_CR_n_n ((aL + 2, bL % 4) :: L') ((d2, b2) :: R2), ?_,
              Or.inl ⟨.CR_n_n, (aL + 2, bL % 4) :: L', (d2, b2) :: R2, rfl⟩⟩
            have h := carry_d0_plus aL (bL % 4) [] L' bR d2 b2 R2 hbR_0
            unfold cfg_CR_U at h
            rwa [← encLeft_eq_encLeftU_singleton aL bL L',
                 encLeftU_eq_encLeft_of_lt4 [(aL + 2, bL % 4)] L' (by
                   intro p hp; simp only [List.mem_singleton] at hp; subst hp; omega)] at h
          · refine ⟨cfg_CR_n_n ((1, 0) :: (aL, bL % 4) :: L') ((d2, b2) :: R2), ?_,
              Or.inl ⟨.CR_n_n, (1, 0) :: (aL, bL % 4) :: L', (d2, b2) :: R2, rfl⟩⟩
            have h := carry_dsucc 0 [(aL, bL % 4)] L' bR d2 b2 R2 hbR_0
            unfold cfg_CR_U at h
            rwa [← encLeft_eq_encLeftU_singleton aL bL L',
                 encLeftU_eq_encLeft_of_lt4 [(1, 0), (aL, bL % 4)] L' (by
                   intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl <;> omega)] at h
          · refine ⟨cfg_CR_n_n ((1, 1) :: (aL, bL % 4) :: L') ((d2, b2) :: R2), ?_,
              Or.inl ⟨.CR_n_n, (1, 1) :: (aL, bL % 4) :: L', (d2, b2) :: R2, rfl⟩⟩
            have h := carry_dsucc 1 [(aL, bL % 4)] L' bR d2 b2 R2 hbR_0
            unfold cfg_CR_U at h
            rwa [← encLeft_eq_encLeftU_singleton aL bL L',
                 encLeftU_eq_encLeft_of_lt4 [(1, 1), (aL, bL % 4)] L' (by
                   intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl <;> omega)] at h
          · refine ⟨cfg_CR_n_n ((1, 2) :: (aL, bL % 4) :: L') ((d2, b2) :: R2), ?_,
              Or.inl ⟨.CR_n_n, (1, 2) :: (aL, bL % 4) :: L', (d2, b2) :: R2, rfl⟩⟩
            have h := carry_dsucc 2 [(aL, bL % 4)] L' bR d2 b2 R2 hbR_0
            unfold cfg_CR_U at h
            rwa [← encLeft_eq_encLeftU_singleton aL bL L',
                 encLeftU_eq_encLeft_of_lt4 [(1, 2), (aL, bL % 4)] L' (by
                   intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl <;> omega)] at h
          · refine ⟨cfg_CR_n_n ((1, 3) :: (aL, bL % 4) :: L') ((d2, b2) :: R2), ?_,
              Or.inl ⟨.CR_n_n, (1, 3) :: (aL, bL % 4) :: L', (d2, b2) :: R2, rfl⟩⟩
            have h := carry_dsucc 3 [(aL, bL % 4)] L' bR d2 b2 R2 hbR_0
            unfold cfg_CR_U at h
            rwa [← encLeft_eq_encLeftU_singleton aL bL L',
                 encLeftU_eq_encLeft_of_lt4 [(1, 3), (aL, bL % 4)] L' (by
                   intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl <;> omega)] at h
          · exact cr_dge5_w0_closed d' aL bL bR d2 b2 L' R2 hbR_0
      · -- R = (d, bR) :: R', hbR_1 : bR % 2 = 1
        rcases mod2_div d with ⟨k, rfl | rfl⟩
        · have h_halt : ∃ cfg', (((cfg_CR_n_n ((aL, bL) :: L') ((2 * k, bR) :: R')) [target_tm]⊢⁺
              cfg') ∧
              (step target_tm cfg').isNone) := by
            unfold cfg_CR_n_n
            rw [encLeft_eq_encLeftU_singleton aL bL L', encRight_mod2 (2 * k) bR R', hbR_1,
                encRight_run_s1 (2 * k) R']
            normalize
            exact drain_even_halts aL (bL % 4) k [] L' ((0 : Fin 2) >> (0 : Fin 2) >> encRight R')
                ⟨_, rfl⟩
          obtain ⟨cfg', hst, hh⟩ := h_halt
          exact ⟨cfg', hst, Or.inr hh⟩
        · unfold cfg_CR_n_n
          rw [encRight_mod2 (2 * k + 1) bR R', hbR_1, encRight_run_s1 (2 * k + 1) R']
          simp only [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
          have hd1 : (⟨some C, ⟨1, encLeft ((aL, bL) :: L'),
              (([1] : List (Fin 2)) ^ (2 * k + 1)) +>
                  ((0 : Fin 2) >> (0 : Fin 2) >> encRight R')⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
            ⟨some D, ⟨1, (encLeft ((aL, bL) :: L')).tail,
              (([1] : List (Fin 2)) ^ (2 * k + 4)) +> encRight R'⟩⟩ := by
            rw [encLeft_eq_encLeftU_singleton aL bL L']
            exact drain_odd_to_d1 aL (bL % 4) k [] L' (encRight R')
          exact cr_odd_drain_exit aL bL k L' R' hd1


private theorem mode_FB_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_FB_n_n L R) [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
  · rcases R with _ | ⟨⟨a9, b10⟩, R11⟩
    · refine ⟨cfg_FB_n_n [] [(2, 0)], ?_, Or.inl ⟨.FB_n_n, [], [(2, 0)], rfl⟩⟩
      unfold cfg_FB_n_n
      rw [encRight_d2_s0 []]
      iterate 6 step
      finish
    · rcases mod2_cases b10 with hb12_0 | hb12_1
      · refine ⟨cfg_FB_n_n [(0, 0)] ((a9, 0) :: R11), ?_, Or.inl ⟨.FB_n_n, [(0, 0)], (a9,
            0) :: R11, rfl⟩⟩
        unfold cfg_FB_n_n
        rw [encRight_mod2 a9 b10 R11, hb12_0, encRight_run_s0 a9 R11, encLeft_d0_s0 []]
        iterate 4 step
        finish
      · refine ⟨cfg_FB_n_n [(0, 0)] ((a9, 1) :: R11), ?_, Or.inl ⟨.FB_n_n, [(0, 0)], (a9,
            1) :: R11, rfl⟩⟩
        unfold cfg_FB_n_n
        rw [encRight_mod2 a9 b10 R11, hb12_1, encRight_run_s1 a9 R11, encLeft_d0_s0 []]
        iterate 4 step
        finish
  · rcases mod4_cases b2 with hb4_0 | hb4_1 | hb4_2 | hb4_3
    · rcases a1 with _ | a15
      · rcases R with _ | ⟨⟨a16, b17⟩, R18⟩
        · refine ⟨cfg_CR_n_n ((1, 0) :: L3) [], ?_, Or.inl ⟨.CR_n_n, (1, 0) :: L3, [], rfl⟩⟩
          unfold cfg_FB_n_n cfg_CR_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_0, encLeft_d0_s0 L3, encLeft_d1_s0 L3]
          iterate 3 step
          finish
        · rcases mod2_cases b17 with hb19_0 | hb19_1
          · refine ⟨cfg_CR_n_n ((1, 0) :: L3) ((a16, 0) :: R18), ?_, Or.inl ⟨.CR_n_n, (1, 0) :: L3,
                (a16, 0) :: R18, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_0, encLeft_d0_s0 L3, encRight_mod2 a16 b17 R18, hb19_0,
                encRight_run_s0 a16 R18, encLeft_d1_s0 L3]
            iterate 3 step
            finish
          · refine ⟨cfg_CR_n_n ((1, 0) :: L3) ((a16, 1) :: R18), ?_, Or.inl ⟨.CR_n_n, (1, 0) :: L3,
                (a16, 1) :: R18, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_0, encLeft_d0_s0 L3, encRight_mod2 a16 b17 R18, hb19_1,
                encRight_run_s1 a16 R18, encLeft_d1_s0 L3]
            iterate 3 step
            finish
      · refine ⟨cfg_BR_n_n ((a15, 0) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (a15, 0) :: L3, (0,
            0) :: R, rfl⟩⟩
        unfold cfg_FB_n_n cfg_BR_n_n
        rw [encLeft_mod4 (a15 + 1) b2 L3, hb4_0, encLeft_succ a15 0 L3, encLeft_run_s0 a15 L3,
            encRight_d0_s0 R]
        iterate 1 step
        finish
    · rcases a1 with _ | a22
      · rcases R with _ | ⟨⟨a23, b24⟩, R25⟩
        · refine ⟨cfg_CR_n_n ((1, 1) :: L3) [], ?_, Or.inl ⟨.CR_n_n, (1, 1) :: L3, [], rfl⟩⟩
          unfold cfg_FB_n_n cfg_CR_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_1, encLeft_d0_s1 L3, encLeft_d1_s1 L3]
          iterate 3 step
          finish
        · rcases mod2_cases b24 with hb26_0 | hb26_1
          · refine ⟨cfg_CR_n_n ((1, 1) :: L3) ((a23, 0) :: R25), ?_, Or.inl ⟨.CR_n_n, (1, 1) :: L3,
                (a23, 0) :: R25, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_1, encLeft_d0_s1 L3, encRight_mod2 a23 b24 R25, hb26_0,
                encRight_run_s0 a23 R25, encLeft_d1_s1 L3]
            iterate 3 step
            finish
          · refine ⟨cfg_CR_n_n ((1, 1) :: L3) ((a23, 1) :: R25), ?_, Or.inl ⟨.CR_n_n, (1, 1) :: L3,
                (a23, 1) :: R25, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_1, encLeft_d0_s1 L3, encRight_mod2 a23 b24 R25, hb26_1,
                encRight_run_s1 a23 R25, encLeft_d1_s1 L3]
            iterate 3 step
            finish
      · refine ⟨cfg_BR_n_n ((a22, 1) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (a22, 1) :: L3, (0,
            0) :: R, rfl⟩⟩
        unfold cfg_FB_n_n cfg_BR_n_n
        rw [encLeft_mod4 (a22 + 1) b2 L3, hb4_1, encLeft_succ a22 1 L3, encLeft_run_s1 a22 L3,
            encRight_d0_s0 R]
        iterate 1 step
        finish
    · rcases a1 with _ | a29
      · rcases R with _ | ⟨⟨a30, b31⟩, R32⟩
        · refine ⟨cfg_CR_n_n ((1, 2) :: L3) [], ?_, Or.inl ⟨.CR_n_n, (1, 2) :: L3, [], rfl⟩⟩
          unfold cfg_FB_n_n cfg_CR_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_2, encLeft_d0_s2 L3, encLeft_d1_s2 L3]
          iterate 3 step
          finish
        · rcases mod2_cases b31 with hb33_0 | hb33_1
          · refine ⟨cfg_CR_n_n ((1, 2) :: L3) ((a30, 0) :: R32), ?_, Or.inl ⟨.CR_n_n, (1, 2) :: L3,
                (a30, 0) :: R32, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_2, encLeft_d0_s2 L3, encRight_mod2 a30 b31 R32, hb33_0,
                encRight_run_s0 a30 R32, encLeft_d1_s2 L3]
            iterate 3 step
            finish
          · refine ⟨cfg_CR_n_n ((1, 2) :: L3) ((a30, 1) :: R32), ?_, Or.inl ⟨.CR_n_n, (1, 2) :: L3,
                (a30, 1) :: R32, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_2, encLeft_d0_s2 L3, encRight_mod2 a30 b31 R32, hb33_1,
                encRight_run_s1 a30 R32, encLeft_d1_s2 L3]
            iterate 3 step
            finish
      · refine ⟨cfg_BR_n_n ((a29, 2) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (a29, 2) :: L3, (0,
            0) :: R, rfl⟩⟩
        unfold cfg_FB_n_n cfg_BR_n_n
        rw [encLeft_mod4 (a29 + 1) b2 L3, hb4_2, encLeft_succ a29 2 L3, encLeft_run_s2 a29 L3,
            encRight_d0_s0 R]
        iterate 1 step
        finish
    · rcases a1 with _ | a36
      · rcases R with _ | ⟨⟨a37, b38⟩, R39⟩
        · refine ⟨cfg_CR_n_n ((1, 3) :: L3) [], ?_, Or.inl ⟨.CR_n_n, (1, 3) :: L3, [], rfl⟩⟩
          unfold cfg_FB_n_n cfg_CR_n_n
          rw [encLeft_mod4 0 b2 L3, hb4_3, encLeft_d0_s3 L3, encLeft_d1_s3 L3]
          iterate 3 step
          finish
        · rcases mod2_cases b38 with hb40_0 | hb40_1
          · refine ⟨cfg_CR_n_n ((1, 3) :: L3) ((a37, 0) :: R39), ?_, Or.inl ⟨.CR_n_n, (1, 3) :: L3,
                (a37, 0) :: R39, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_3, encLeft_d0_s3 L3, encRight_mod2 a37 b38 R39, hb40_0,
                encRight_run_s0 a37 R39, encLeft_d1_s3 L3]
            iterate 3 step
            finish
          · refine ⟨cfg_CR_n_n ((1, 3) :: L3) ((a37, 1) :: R39), ?_, Or.inl ⟨.CR_n_n, (1, 3) :: L3,
                (a37, 1) :: R39, rfl⟩⟩
            unfold cfg_FB_n_n cfg_CR_n_n
            rw [encLeft_mod4 0 b2 L3, hb4_3, encLeft_d0_s3 L3, encRight_mod2 a37 b38 R39, hb40_1,
                encRight_run_s1 a37 R39, encLeft_d1_s3 L3]
            iterate 3 step
            finish
      · refine ⟨cfg_BR_n_n ((a36, 3) :: L3) ((0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (a36, 3) :: L3, (0,
            0) :: R, rfl⟩⟩
        unfold cfg_FB_n_n cfg_BR_n_n
        rw [encLeft_mod4 (a36 + 1) b2 L3, hb4_3, encLeft_succ a36 3 L3, encLeft_run_s3 a36 L3,
            encRight_d0_s0 R]
        iterate 1 step
        finish

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | BR_n_n => exact mode_BR_n_n_closed L R
  | FR_n_n => exact mode_FR_n_n_closed L R
  | AL_n_n => exact mode_AL_n_n_closed L R
  | DB_n_n => exact mode_DB_n_n_closed L R
  | CR_n_n => exact mode_CR_n_n_closed L R
  | FB_n_n => exact mode_FB_n_n_closed L R

private theorem init_reaches_stack_system :
    ∃ (m_g : StackMode) (L_g R_g : List (ℕ × ℕ)),
      ReachesPlus target_tm (init []) (evalStackCfg m_g L_g R_g) ∧
      3 ≤ L_g.length + R_g.length ∧ (∃ x ∈ L_g ++ R_g, 1 ≤ x.1) := by
  refine ⟨.FR_n_n, [(1, 0)], [(0, 0), (3, 0)], ?_, by decide, ⟨(3, 0), by decide, by decide⟩⟩
  dsimp only [evalStackCfg]
  rw [init_nil]
  unfold cfg_FR_n_n
  rw [encLeft_succ 0 0 [], encLeft_d0_s0 [], encLeft_nil, encRight_d0_s0 [(3, 0)],
      encRight_succ 2 0 [], encRight_succ 1 0 [], encRight_succ 0 0 [], encRight_d0_s0 [],
          encRight_nil]
  execute 19

private theorem stack_transfer :
    (∃ (m m' : StackMode) (x : ℕ × ℕ) (g : ℕ × ℕ → ℕ × ℕ) (f : List (ℕ × ℕ) → List (ℕ × ℕ)),
      (∀ s, s.length ≤ (f s).length) ∧
      ∀ z L R,
        ReachesPlus target_tm (evalStackCfg m (x :: z :: L) R) (evalStackCfg m' (g z :: L) (f R))) ∨
    (∃ (m m' : StackMode) (x : ℕ × ℕ) (g : ℕ × ℕ → ℕ × ℕ) (f : List (ℕ × ℕ) → List (ℕ × ℕ)),
      (∀ s, s.length ≤ (f s).length) ∧
      ∀ z L R,
        ReachesPlus target_tm (evalStackCfg m L (x :: z :: R)) (evalStackCfg m' (f L) (g z :: R)))
            := by
  refine Or.inl ⟨.AL_n_n, .BR_n_n, (1, 0), fun p => (p.1 + 1, p.2), fun R => (0, 0) :: R,
      fun s => by simp, ?_⟩
  intro z L R
  rcases z with ⟨a, b⟩
  dsimp only [evalStackCfg]
  unfold cfg_AL_n_n cfg_BR_n_n
  rw [encLeft_d1_s0 ((a, b) :: L), encLeft_succ a b L, encRight_d0_s0 R]
  execute 3

private theorem audit_encLeft_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: L)).head = 1 := by
  rw [encLeft_cons, show 1 * a + 1 = (1 * a + 0) + 1 by omega, pow_succ_list, cons_append_list]
  simp only [listblank_append_cons, Turing.ListBlank.head_cons]

private theorem audit_encLeft_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ L : List (ℕ × ℕ), encLeft L ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> default, rfl, ?_⟩
  intro L h
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rw [encLeft_mod4] at h
    rcases mod4_cases b with hb0 | hb1 | hb2 | hb3
    · rw [hb0, encLeft_run_s0] at h
      rcases a with _ | a'
      · rcases L' with _ | ⟨⟨a', b'⟩, L''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.head) h
          normalize_at h1
          rw [audit_encLeft_head a' b' L''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction
    · rw [hb1, encLeft_run_s1] at h
      rcases a with _ | a'
      · rcases L' with _ | ⟨⟨a', b'⟩, L''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.tail.head) h
          normalize_at h1
          rw [audit_encLeft_head a' b' L''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction
    · rw [hb2, encLeft_run_s2] at h
      rcases a with _ | a'
      · rcases L' with _ | ⟨⟨a', b'⟩, L''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.tail.tail.head) h
          normalize_at h1
          rw [audit_encLeft_head a' b' L''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction
    · rw [hb3, encLeft_run_s3] at h
      rcases a with _ | a'
      · rcases L' with _ | ⟨⟨a', b'⟩, L''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.tail.tail.tail.head) h
          normalize_at h1
          rw [audit_encLeft_head a' b' L''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction

private theorem audit_encRight_head (a b : ℕ) (R : List (ℕ × ℕ)) :
    (encRight ((a, b) :: R)).head = 1 := by
  rw [encRight_cons, show 1 * a + 1 = (1 * a + 0) + 1 by omega, pow_succ_list, cons_append_list]
  simp only [listblank_append_cons, Turing.ListBlank.head_cons]

private theorem audit_encRight_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ R : List (ℕ × ℕ), encRight R ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl,
      ?_⟩
  intro R h
  rcases R with _ | ⟨⟨a, b⟩, R'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rw [encRight_mod2] at h
    rcases mod2_cases b with hb0 | hb1
    · rw [hb0, encRight_run_s0] at h
      rcases a with _ | a'
      · rcases R' with _ | ⟨⟨a', b'⟩, R''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.head) h
          normalize_at h1
          rw [audit_encRight_head a' b' R''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction
    · rw [hb1, encRight_run_s1] at h
      rcases a with _ | a'
      · rcases R' with _ | ⟨⟨a', b'⟩, R''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.tail.head) h
          normalize_at h1
          rw [audit_encRight_head a' b' R''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction

private theorem valid_stack_modes : IsValidStackModes encLeft encRight evalStackCfg := by
  intro m
  cases m with
  | BR_n_n => exact ⟨B, .id [], .id [], by decide, by decide, Or.inr (Or.inr (fun _ _ => rfl))⟩
  | FR_n_n => exact ⟨F, .id [], .id [], by decide, by decide, Or.inr (Or.inr (fun _ _ => rfl))⟩
  | AL_n_n => exact ⟨A, .id [], .id [], by decide, by decide, Or.inr (Or.inl (fun _ _ => rfl))⟩
  | DB_n_n => exact ⟨D, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | CR_n_n => exact ⟨C, .id [], .id [], by decide, by decide, Or.inr (Or.inr (fun _ _ => rfl))⟩
  | FB_n_n => exact ⟨F, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩


/-- Closed 2nd-order stack reduction for `#543`. -/
theorem has_stack_reduction : HasStackReduction target := by
  rw [target_eq_target_tm]
  refine ⟨StackMode, 1, 0, encLeft, encRight, evalStackCfg, IsInStackSystem,
    Or.inl ⟨rfl, rfl⟩,
    rfl, rfl, audit_encLeft_head, audit_encRight_head,
    audit_encLeft_not_surjective, audit_encRight_not_surjective,
    ⟨1, 1, 1, 4, 1, 1, 1, 2, by decide, by decide, by decide, by decide, by decide,
     by decide, by decide, by decide, by decide, by decide,
     fun a b L => rfl, fun d b R => rfl⟩,
    ⟨[.BR_n_n, .FR_n_n, .AL_n_n, .DB_n_n, .CR_n_n, .FB_n_n], by decide,
        by intro m; cases m <;> decide⟩,
    valid_stack_modes,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    init_reaches_stack_system,
    stack_transfer,
    stack_system_closed⟩


end BusyBeaver.M_1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LDHHH_0LB1LA
