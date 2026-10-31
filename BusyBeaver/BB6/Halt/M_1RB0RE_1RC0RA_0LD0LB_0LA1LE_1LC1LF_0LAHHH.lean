/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxRecDepth 20000000
set_option maxHeartbeats 40000000

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def F : Fin 6 := 5

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl

@[simp] lemma pow_zero_list (u : List (Fin 2)) : u ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
@[simp] lemma nil_append_list (l : List (Fin 2)) : ([] : List (Fin 2)) ++ l = l := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
@[simp] lemma init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

omit [Inhabited Γ] in
@[simp]
theorem list_pow_add (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, ← add_assoc, add_comm 1 m, list_pow_add]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [← List.append_assoc, ← List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa

omit [Inhabited Γ] in
theorem list_pow_add_comm (l : List Γ) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [← list_pow_add, add_comm, list_pow_add]

lemma listblank_append_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (s <+ (([1] : List (Fin 2)) ^ n)) <+ (([1] : List (Fin 2)) ^ m) =
    s <+ (([1] : List (Fin 2)) ^ (n + m)) := by
  rw [listblank_append_append, list_pow_add_comm, ← list_pow_add]

lemma listblank_right_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (([1] : List (Fin 2)) ^ n) +> ((([1] : List (Fin 2)) ^ m) +> s) =
    (([1] : List (Fin 2)) ^ (n + m)) +> s := by
  rw [← listblank_append_right_assoc, ← list_pow_add]

-- ============================================================================
-- Section 1: 2nd-Order Digit-Stack Encodings & 18 Local Separator Rules
-- ============================================================================

def encLeft1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))

def encRight1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | d :: R => (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0)

@[simp] lemma encLeft_nil : encLeft1 [] = default := rfl
@[simp] lemma encLeft_cons (a : ℕ) (L : List ℕ) :
    encLeft1 (a :: L) = ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) := rfl
@[simp] lemma encRight_nil : encRight1 [] = default := rfl
@[simp] lemma encRight_cons (d : ℕ) (R : List ℕ) :
    encRight1 (d :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0) := rfl

def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | b :: L => (b + 1) :: L

@[simp] lemma encLeft_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encLeft1 L = encLeft1 (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encLeft1]
  | cons b L' => rfl

@[simp] lemma encRight_cons_one (R : List ℕ) :
    (1 : Fin 2) >> encRight1 R = encRight1 (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encRight1]
  | cons d R' => rfl

macro "finish" : tactic => `(tactic| (refine ⟨0, ?_⟩; simp only [listblank_append_cons, listblank_append_nil, zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one, encRight_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]; try rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

def cfg_BR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encLeft1 L) {{B}}> (encRight1 R)

def cfg_C (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encLeft1 L, encRight1 R⟩⟩

def cfg_B (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encLeft1 L, encRight1 R⟩⟩

def cfg_DR0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encLeft1 L, (0 : Fin 2) >> encRight1 R⟩⟩

def cfg_Halt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨1, l, r⟩⟩

inductive StackMode
  | BR
  | C
  | B
  | DR0
  deriving DecidableEq

def evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .BR, L, R => cfg_BR L R
  | .C, L, R => cfg_C L R
  | .B, L, R => cfg_B L R
  | .DR0, L, R => cfg_DR0 L R

lemma encLeft_zero (L : List ℕ) :
    encLeft1 (0 :: L) = (1 : Fin 2) >> ((0 : Fin 2) >> encLeft1 L) := rfl
lemma encLeft_succ (a : ℕ) (L : List ℕ) :
    encLeft1 ((a + 1) :: L) = (1 : Fin 2) >> encLeft1 (a :: L) := rfl
lemma encRight_zero (R : List ℕ) :
    encRight1 (0 :: R) = (1 : Fin 2) >> ((0 : Fin 2) >> encRight1 R) := rfl
lemma encRight_succ (d : ℕ) (R : List ℕ) :
    encRight1 ((d + 1) :: R) = (1 : Fin 2) >> encRight1 (d :: R) := rfl

lemma encRight_expose (d : ℕ) (R : List ℕ) :
    encRight1 (d :: R) = (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ d) +> ((encRight1 R).cons 0)) := by
  rw [encRight_cons d R, Nat.add_comm d 1, ← listblank_right_pow_add ((encRight1 R).cons 0) 1 d]
  rfl

lemma encLeft_expose (a : ℕ) (L : List ℕ) :
    encLeft1 (a :: L) = (1 : Fin 2) >> (((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a)) := by
  rw [encLeft_cons a L, ← listblank_append_pow_add ((encLeft1 L).cons 0) a 1]
  rfl

theorem init_reaches_stack : (init []) [target_tm]⊢⁺ (cfg_B [0] []) := by
  rw [init_nil]; unfold cfg_B
  rw [encLeft_zero, encLeft_nil, encRight_nil]; execute 1

theorem rule_B_nil (L : List ℕ) :
    (cfg_B L []) [target_tm]⊢⁺ (cfg_C (bumpHead L) []) := by
  unfold cfg_B cfg_C; rw [encRight_nil]; execute 1

theorem rule_B_zero (L R : List ℕ) :
    (cfg_B L (0 :: R)) [target_tm]⊢⁺ (cfg_B (0 :: L) R) := by
  unfold cfg_B; rw [encRight_zero R, encLeft_zero L]; execute 4

theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR L (0 :: d :: R)) := by
  unfold cfg_B cfg_BR
  rw [encRight_succ d R, encRight_zero (d :: R), encRight_expose d R]; execute 2

theorem rule_BR_nil (L : List ℕ) :
    (cfg_BR L []) [target_tm]⊢⁺ (cfg_C (bumpHead L) []) :=
  rule_B_nil L

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR L (0 :: R)) [target_tm]⊢⁺ (cfg_BR (0 :: L) R) := by
  unfold cfg_BR; rw [encRight_zero R, encLeft_zero L]; execute 2

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR L (1 :: R)) [target_tm]⊢⁺ (cfg_DR0 L (bumpHead R)) := by
  unfold cfg_BR cfg_DR0; rw [encRight_succ 0 R, encRight_zero R]; execute 4

theorem rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR L ((d + 2) :: R)) [target_tm]⊢⁺ (cfg_B (bumpHead L) (d :: R)) := by
  unfold cfg_BR cfg_B
  rw [encRight_succ (d + 1) R, encRight_succ d R, encRight_expose d R]; execute 5

theorem rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 [] R) [target_tm]⊢⁺ (cfg_C [1] R) := by
  unfold cfg_DR0 cfg_C
  rw [encLeft_nil, encLeft_succ 0 [], encLeft_zero [], encLeft_nil]; execute 3

theorem rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 (0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 L (0 :: R)) := by
  unfold cfg_DR0; rw [encLeft_zero L, encRight_zero R]; execute 4

theorem rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 ((a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C (a :: L) (0 :: R)) := by
  unfold cfg_DR0 cfg_C; rw [encLeft_succ a L, encRight_zero R]; execute 3

theorem rule_C_nil (R : List ℕ) :
    (cfg_C [] R) [target_tm]⊢⁺ (cfg_DR0 [] R) := by
  unfold cfg_C cfg_DR0; rw [encLeft_nil]; execute 1

theorem rule_C_zero_nil (R : List ℕ) :
    (cfg_C [0] R) [target_tm]⊢⁺ (cfg_C [] (1 :: R)) := by
  unfold cfg_C
  rw [encLeft_zero [], encLeft_nil, encRight_succ 0 R, encRight_zero R]; execute 3

theorem rule_C_zero_zero (L R : List ℕ) :
    (cfg_C (0 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_C (bumpHead L) (1 :: R)) := by
  unfold cfg_C
  rw [encLeft_zero (0 :: L), encLeft_zero L, encRight_succ 0 R, encRight_zero R]; execute 5

theorem rule_C_zero_one (L R : List ℕ) :
    (cfg_C (0 :: 1 :: L) R) [target_tm]⊢⁺
    (cfg_C (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_C
  rw [encLeft_zero (1 :: L), encLeft_succ 0 L, encLeft_zero L, encRight_zero (bumpHead R)]
  execute 17

theorem rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C (0 :: (a + 2) :: L) R) [target_tm]⊢⁺ (cfg_BR (a :: L) (0 :: 1 :: R)) := by
  unfold cfg_C cfg_BR
  rw [encLeft_zero ((a + 2) :: L), encLeft_succ (a + 1) L, encLeft_succ a L,
    encRight_zero (1 :: R), encRight_succ 0 R, encRight_zero R]; execute 4

theorem rule_C_one_nil (R : List ℕ) :
    (cfg_C [1] R) [target_tm]⊢⁺ (cfg_B [0] (1 :: R)) := by
  unfold cfg_C cfg_B
  rw [encLeft_succ 0 [], encLeft_zero [], encLeft_nil, encRight_succ 0 R, encRight_zero R]
  execute 5

theorem rule_C_one_zero (L R : List ℕ) :
    (cfg_C (1 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 L (2 :: R)) := by
  unfold cfg_C cfg_DR0
  rw [encLeft_succ 0 (0 :: L), encLeft_zero (0 :: L), encLeft_zero L,
    encRight_succ 1 R, encRight_succ 0 R, encRight_zero R]; execute 7

theorem rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C (1 :: (a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C (a :: L) (2 :: R)) := by
  unfold cfg_C
  rw [encLeft_succ 0 ((a + 1) :: L), encLeft_zero ((a + 1) :: L), encLeft_succ a L,
    encRight_succ 1 R, encRight_succ 0 R, encRight_zero R]; execute 6

theorem rule_C_add_two_step (a : ℕ) (L R : List ℕ) :
    (cfg_C ((a + 2) :: L) R) [target_tm]⊢⁺
    (cfg_Halt ((([1] : List (Fin 2)) ^ a) +> ((encLeft1 L).cons 0))
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight1 R)) := by
  unfold cfg_C cfg_Halt
  rw [encLeft_succ (a + 1) L, encLeft_succ a L, encLeft_expose a L]; execute 3

theorem rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C ((a + 2) :: L) R) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone :=
  ⟨cfg_Halt ((([1] : List (Fin 2)) ^ a) +> ((encLeft1 L).cons 0))
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight1 R),
   rule_C_add_two_step a L R, rfl⟩






-- ============================================================================
-- Section 2: Semantic Multi-Step Contractions on `List ℕ`
-- ============================================================================

@[simp] lemma stepStar_refl {M : Machine Γ Λ} (c : Cfg Γ Λ) : c [M]⊢* c := ⟨0, rfl⟩
lemma pow_zero_list_gen {α : Type*} (l : List α) : l ^ (0 : ℕ) = [] := rfl
lemma pow_succ_list_gen {α : Type*} (l : List α) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := rfl

lemma pow_succ_right_list {α : Type*} (l : List α) : ∀ (n : ℕ),
    l ^ (n + 1) = l ^ n ++ l
  | 0 => List.append_nil l
  | n + 1 => by
    change l ++ l ^ (n + 1) = (l ++ l ^ n) ++ l
    rw [pow_succ_right_list l n, List.append_assoc]

abbrev rep0 (n : ℕ) : List ℕ := List.replicate n 0
def blkL (r : ℕ) : List ℕ := rep0 (r + 2) ++ [1]
def blkR (r : ℕ) : List ℕ := rep0 r ++ [2, 1]

lemma rep0_zero : rep0 0 = [] := rfl
lemma rep0_succ (n : ℕ) : rep0 (n + 1) = 0 :: rep0 n := rfl

lemma rep0_append_zero_cons (k : ℕ) (L : List ℕ) :
    rep0 k ++ (0 :: L) = 0 :: (rep0 k ++ L) := by
  induction k with
  | zero => rfl
  | succ k' ih => simp only [List.replicate_succ, List.cons_append]; rw [ih]

lemma rep0_add_split (a b : ℕ) : rep0 (a + b) = rep0 a ++ rep0 b :=
  List.replicate_add a b 0

macro "norm_list" : tactic => `(tactic|
  simp only [HPow.hPow, list_nat_repeat, List.append_eq,
    blkL, blkR, bumpHead,
    List.replicate_succ, List.replicate_zero, rep0_add_split,
    List.nil_append, List.cons_append, List.append_nil, List.append_assoc,
    rep0_append_zero_cons])

theorem rule_BR_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_BR L (rep0 k ++ R)) [target_tm]⊢* (cfg_BR (rep0 k ++ L) R) := by
  induction k generalizing L with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (rule_BR_zero L (rep0 k ++ R))
    have h2 := ih (0 :: L)
    rw [rep0_append_zero_cons k L] at h2
    exact stepStar_trans h1 h2

theorem rule_B_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_B L (rep0 k ++ R)) [target_tm]⊢* (cfg_B (rep0 k ++ L) R) := by
  induction k generalizing L with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (rule_B_zero L (rep0 k ++ R))
    have h2 := ih (0 :: L)
    rw [rep0_append_zero_cons k L] at h2
    exact stepStar_trans h1 h2

theorem rule_DR0_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_DR0 (rep0 k ++ L) R) [target_tm]⊢* (cfg_DR0 L (rep0 k ++ R)) := by
  induction k generalizing R with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (rule_DR0_zero (rep0 k ++ L) R)
    have h2 := ih (0 :: R)
    rw [rep0_append_zero_cons k R] at h2
    exact stepStar_trans h1 h2

theorem rule_B_succ_step (d : ℕ) (L R : List ℕ) :
    (cfg_B L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR (0 :: L) (d :: R)) :=
  stepPlus_trans (rule_B_succ d L R) (rule_BR_zero L (d :: R))

theorem rule_C_one_prefix (c0 : ℕ) (L R : List ℕ) :
    (cfg_C (1 :: (rep0 c0 ++ 1 :: L)) R) [target_tm]⊢*
    (cfg_C (0 :: L) (rep0 c0 ++ 2 :: R)) := by
  cases c0 with
  | zero => exact stepPlus_stepStar (rule_C_one_succ 0 L R)
  | succ n =>
    have h1 := stepPlus_stepStar (rule_C_one_zero (rep0 n ++ 1 :: L) R)
    have h2 := rule_DR0_zeros_all (1 :: L) (2 :: R) n
    have h3 := stepPlus_stepStar (rule_DR0_succ 0 L (rep0 n ++ 2 :: R))
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem rule_C_r_add_three (r : ℕ) (L R : List ℕ) :
    (cfg_C (rep0 (r + 3) ++ 1 :: L) R) [target_tm]⊢*
    (cfg_C (0 :: L) (blkR r ++ R)) := by
  have heq1 : rep0 (r + 3) ++ 1 :: L = 0 :: 0 :: 0 :: (rep0 r ++ 1 :: L) := by norm_list
  rw [heq1]
  have h1 := stepPlus_stepStar (rule_C_zero_zero (0 :: (rep0 r ++ 1 :: L)) R)
  have h2 := rule_C_one_prefix r L (1 :: R)
  have heq2 : rep0 r ++ 2 :: 1 :: R = blkR r ++ R := by norm_list
  rw [heq2] at h2
  exact stepStar_trans h1 h2

theorem rule_C_blkL_pow : ∀ (c r : ℕ) (L R : List ℕ),
    (cfg_C (0 :: ((blkL r) ^ c ++ L)) R) [target_tm]⊢*
    (cfg_C (0 :: L) ((blkR r) ^ c ++ R))
  | 0, r, L, R => ⟨0, rfl⟩
  | c + 1, r, L, R => by
    have heq : 0 :: ((blkL r) ^ (c + 1) ++ L) =
        rep0 (r + 3) ++ 1 :: ((blkL r) ^ c ++ L) := by norm_list
    rw [heq]
    have h1 := rule_C_r_add_three r ((blkL r) ^ c ++ L) R
    have h2 := rule_C_blkL_pow c r L (blkR r ++ R)
    have h3 : (blkR r) ^ c ++ (blkR r ++ R) = (blkR r) ^ (c + 1) ++ R := by
      rw [← List.append_assoc, ← pow_succ_right_list]
    rw [h3] at h2
    exact stepStar_trans h1 h2

theorem rule_C_bot_four (r : ℕ) (R : List ℕ) :
    (cfg_C (rep0 (r + 4)) R) [target_tm]⊢*
    (cfg_DR0 [] (blkR r ++ R)) := by
  have heq : rep0 (r + 4) = 0 :: 0 :: 0 :: 0 :: rep0 r := by norm_list
  rw [heq]
  have h1 := stepPlus_stepStar (rule_C_zero_zero (0 :: 0 :: rep0 r) R)
  have h2 := stepPlus_stepStar (rule_C_one_zero (rep0 r) (1 :: R))
  have h3 := rule_DR0_zeros_all [] (2 :: 1 :: R) r
  have heq0 : rep0 r ++ [] = rep0 r := List.append_nil _
  have heq2 : rep0 r ++ 2 :: 1 :: R = blkR r ++ R := by norm_list
  rw [heq0, heq2] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem rule_DR0_bot (k : ℕ) (R : List ℕ) :
    (cfg_DR0 (rep0 k) R) [target_tm]⊢* (cfg_BR (rep0 (k + 3)) R) := by
  have h0 : rep0 k = rep0 k ++ [] := (List.append_nil _).symm
  rw [h0]
  have h1 := rule_DR0_zeros_all [] R k
  have h2 := stepPlus_stepStar (rule_DR0_nil (rep0 k ++ R))
  have h3 := stepPlus_stepStar (rule_C_one_nil (rep0 k ++ R))
  have h4 := stepPlus_stepStar (rule_B_succ_step 0 [0] (rep0 k ++ R))
  have h5 := rule_BR_zeros_all [0, 0] R (k + 1)
  have heqR : 0 :: (rep0 k ++ R) = rep0 (k + 1) ++ R := rfl
  have heqL : rep0 (k + 1) ++ [0, 0] = rep0 (k + 3) := by norm_list
  rw [heqR] at h4; rw [heqL] at h5
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem rule_DR0_bot_zeros : ∀ (q k : ℕ) (R : List ℕ),
    (cfg_DR0 (rep0 k) (1 :: (rep0 q ++ R))) [target_tm]⊢*
    (cfg_DR0 (rep0 (k + 3 * q)) (1 :: R))
  | 0, k, R => by simp
  | q + 1, k, R => by
    have h1 := rule_DR0_bot k (1 :: (0 :: (rep0 q ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_one (rep0 (k + 3)) (0 :: (rep0 q ++ R)))
    have h3 := rule_DR0_bot_zeros q (k + 3) R
    have heq : k + 3 + 3 * q = k + 3 * (q + 1) := by omega
    rw [heq] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem rule_BR_blkR_one (r : ℕ) (L R : List ℕ) :
    (cfg_BR (0 :: L) (blkR r ++ R)) [target_tm]⊢*
    (cfg_BR (rep0 3 ++ 1 :: (rep0 r ++ L)) R) := by
  have h0 : blkR r ++ R = rep0 r ++ (2 :: 1 :: R) := by norm_list
  rw [h0]
  have h1 := rule_BR_zeros_all (0 :: L) (2 :: 1 :: R) r
  rw [rep0_append_zero_cons r L] at h1
  have h2 := stepPlus_stepStar (rule_BR_add_two 0 (0 :: (rep0 r ++ L)) (1 :: R))
  have h3 := stepPlus_stepStar (rule_B_zero (1 :: (rep0 r ++ L)) (1 :: R))
  have h4 := stepPlus_stepStar (rule_B_succ_step 0 (0 :: 1 :: (rep0 r ++ L)) R)
  have h5 := stepPlus_stepStar (rule_BR_zero (0 :: 0 :: 1 :: (rep0 r ++ L)) R)
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem rule_BR_blkR_succ : ∀ (k r : ℕ) (L R : List ℕ),
    (cfg_BR (0 :: L) ((blkR r) ^ (k + 1) ++ R)) [target_tm]⊢*
    (cfg_BR (rep0 3 ++ 1 :: ((blkL r) ^ k ++ (rep0 r ++ L))) R)
  | 0, r, L, R => by
    simpa [HPow.hPow, list_nat_repeat, List.append_eq] using rule_BR_blkR_one r L R
  | k + 1, r, L, R => by
    have heqR : (blkR r) ^ (k + 2) ++ R = blkR r ++ ((blkR r) ^ (k + 1) ++ R) := by
      simp [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [heqR]
    have h1 := rule_BR_blkR_one r L ((blkR r) ^ (k + 1) ++ R)
    have h2 := rule_BR_blkR_succ k r (0 :: 0 :: 1 :: (rep0 r ++ L)) R
    have heqL1 : rep0 3 ++ 1 :: (rep0 r ++ L) = 0 :: (0 :: 0 :: 1 :: (rep0 r ++ L)) := rfl
    rw [heqL1] at h1
    have heqL2 : (blkL r) ^ k ++ (rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L))) =
        (blkL r) ^ (k + 1) ++ (rep0 r ++ L) := by
      have hb : rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L)) = blkL r ++ (rep0 r ++ L) := by norm_list
      rw [hb, ← List.append_assoc, ← pow_succ_right_list]
    rw [heqL2] at h2
    exact stepStar_trans h1 h2

theorem rule_BR_blkR_clean (c r : ℕ) (L R : List ℕ) :
    (cfg_BR (rep0 3 ++ 1 :: L) ((blkR r) ^ c ++ R)) [target_tm]⊢*
    (cfg_BR (rep0 3 ++ 1 :: ((blkL r) ^ c ++ L)) R) := by
  cases c with
  | zero => exact ⟨0, rfl⟩
  | succ k =>
    have h := rule_BR_blkR_succ k r (0 :: 0 :: 1 :: L) R
    have heq1 : (blkL r) ^ k ++ (rep0 r ++ (0 :: 0 :: 1 :: L)) =
        (blkL r) ^ (k + 1) ++ L := by
      have hb : rep0 r ++ (0 :: 0 :: 1 :: L) = blkL r ++ L := by norm_list
      rw [hb, ← List.append_assoc, ← pow_succ_right_list]
    rw [heq1] at h
    exact h

-- ============================================================================
-- Section 3: Clean-Mode Invariant Structure & O(1) Contraction Theorems
-- ============================================================================

def decSegs : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (r, c) :: ss => (blkL r) ^ c ++ decSegs ss

inductive Item where
  | z (c : ℕ)
  | d (v : ℕ)
  | k (r c : ℕ)

inductive LState where
  | raw (items : List Item)
  | clean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ)

def decL : List Item → List ℕ
  | [] => []
  | .z c :: xs => rep0 c ++ decL xs
  | .d v :: xs => v :: decL xs
  | .k r c :: xs => (blkL r) ^ c ++ decL xs

def decR : List Item → List ℕ
  | [] => []
  | .z c :: xs => rep0 c ++ decR xs
  | .d v :: xs => v :: decR xs
  | .k r c :: xs => (blkR r) ^ c ++ decR xs

def decLState : LState → List ℕ
  | .raw items => decL items
  | .clean c0 segs bot => rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))

def pushSeg (r c : ℕ) (segs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if Nat.beq c 0 then segs
  else match segs with
    | (r2, c2) :: ss => if Nat.beq r r2 then (r, c + c2) :: ss else (r, c) :: segs
    | [] => [(r, c)]

lemma decSegs_pushSeg (r c : ℕ) (segs : List (ℕ × ℕ)) :
    decSegs (pushSeg r c segs) = (blkL r) ^ c ++ decSegs segs := by
  unfold pushSeg
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases segs with
    | nil => rfl
    | cons hd ss =>
      rcases hd with ⟨r2, c2⟩
      dsimp only
      split
      · next hr =>
        rw [Nat.beq_eq] at hr; subst hr
        simp [decSegs, list_pow_add, List.append_assoc]
      · rfl

macro "norm_all" : tactic => `(tactic|
  simp only [decL, decR, decSegs, decLState, decSegs_pushSeg,
    HPow.hPow, list_nat_repeat, List.append_eq,
    blkL, blkR, bumpHead,
    List.replicate_succ, List.replicate_zero, rep0_add_split,
    List.nil_append, List.cons_append, List.append_nil, List.append_assoc,
    rep0_append_zero_cons])

theorem clean_sweep_core : ∀ (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_C (0 :: (decSegs segs ++ rep0 (bot + 3))) R) [target_tm]⊢*
    (cfg_BR (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R)
  | [], bot, R => by
    dsimp only [decSegs]
    have heq : (0 :: ([] ++ rep0 (bot + 3))) = rep0 (bot + 4) := by norm_all
    rw [heq]
    have h1 := rule_C_bot_four bot R
    have h2 := rule_DR0_bot 0 (blkR bot ++ R)
    have h3 := rule_BR_blkR_one bot [0, 0] R
    have heq2 : rep0 bot ++ [0, 0] = rep0 (bot + 2) := by norm_all
    rw [heq2] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)
  | (r, c) :: ss, bot, R => by
    dsimp only [decSegs]
    rw [List.append_assoc]
    have h1 := rule_C_blkL_pow c r (decSegs ss ++ rep0 (bot + 3)) R
    have h2 := clean_sweep_core ss bot ((blkR r) ^ c ++ R)
    have h3 := rule_BR_blkR_clean c r (decSegs ss ++ rep0 (bot + 2)) R
    rw [← List.append_assoc] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem clean_DR0_one (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_DR0 (decLState (.clean c0 segs (bot + 1))) R) [target_tm]⊢*
    (cfg_BR (decLState (.clean (c0 + 4) segs bot)) R) := by
  dsimp only [decLState]
  have h1 := rule_DR0_zeros_all (1 :: (decSegs segs ++ rep0 (bot + 3))) R c0
  have h2 := stepPlus_stepStar (rule_DR0_succ 0 (decSegs segs ++ rep0 (bot + 3)) (rep0 c0 ++ R))
  have h3 := clean_sweep_core segs bot (0 :: (rep0 c0 ++ R))
  have h4 := rule_BR_zeros_all (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R (c0 + 1)
  have heqL : rep0 (c0 + 1) ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      rep0 (c0 + 4) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)) := by norm_all
  rw [heqL] at h4
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem clean_DR0_zeros : ∀ (q c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_DR0 (decLState (.clean c0 segs (bot + q))) (1 :: (rep0 q ++ R))) [target_tm]⊢*
    (cfg_DR0 (decLState (.clean (c0 + 4 * q) segs bot)) (1 :: R))
  | 0, c0, segs, bot, R => ⟨0, rfl⟩
  | q + 1, c0, segs, bot, R => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have h1 := clean_DR0_one c0 segs (bot + q) (1 :: (0 :: (rep0 q ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_one (decLState (.clean (c0 + 4) segs (bot + q))) (0 :: (rep0 q ++ R)))
    have h3 := clean_DR0_zeros q (c0 + 4) segs bot R
    have heq : c0 + 4 + 4 * q = c0 + 4 * (q + 1) := by omega
    rw [heq] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem clean_RNIL_one (m : StackMode) (hm : m = .B ∨ m = .BR)
    (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) :
    (evalStackCfg1 m (decLState (.clean (c0 + 1) segs (bot + 1))) []) [target_tm]⊢*
    (cfg_B (decLState (.clean 1 (pushSeg c0 1 segs) bot)) []) := by
  have h0 : (evalStackCfg1 m (decLState (.clean (c0 + 1) segs (bot + 1))) []) [target_tm]⊢*
      (cfg_C (1 :: (rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3)))) []) := by
    have heqL : bumpHead (decLState (.clean (c0 + 1) segs (bot + 1))) =
        1 :: (rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3))) := by norm_all
    rcases hm with rfl | rfl
    · rw [← heqL]; exact stepPlus_stepStar (rule_B_nil _)
    · rw [← heqL]; exact stepPlus_stepStar (rule_BR_nil _)
  have h1 := rule_C_one_prefix c0 (decSegs segs ++ rep0 (bot + 3)) []
  have h2 := clean_sweep_core segs bot (rep0 c0 ++ [2])
  have h3 := rule_BR_zeros_all (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) [2] c0
  have heq3 : rep0 c0 ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      0 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) := by norm_all
  rw [heq3] at h3
  have h4 := stepPlus_stepStar (rule_BR_add_two 0 (0 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])
  have h5 := stepPlus_stepStar (rule_B_zero (1 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])
  have heq5 : 0 :: 1 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      decLState (.clean 1 (pushSeg c0 1 segs) bot) := by norm_all
  rw [heq5] at h5
  exact stepStar_trans h0 (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5))))

lemma decSegs_pushSeg_succ (r q : ℕ) (segs : List (ℕ × ℕ)) :
    decSegs (pushSeg r q (pushSeg r 1 segs)) = decSegs (pushSeg r (q + 1) segs) := by
  rw [decSegs_pushSeg, decSegs_pushSeg, decSegs_pushSeg, ← List.append_assoc,
      ← list_pow_add]

theorem clean_RNIL_zero_pow : ∀ (q : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ),
    (cfg_B (decLState (.clean 1 segs (bot + q))) []) [target_tm]⊢*
    (cfg_B (decLState (.clean 1 (pushSeg 0 q segs) bot)) [])
  | 0, segs, bot => by simp [pushSeg]
  | q + 1, segs, bot => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have h1 := clean_RNIL_one .B (Or.inl rfl) 0 segs (bot + q)
    have h2 := clean_RNIL_zero_pow q (pushSeg 0 1 segs) bot
    have heqL : decLState (.clean 1 (pushSeg 0 q (pushSeg 0 1 segs)) bot) =
        decLState (.clean 1 (pushSeg 0 (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    exact stepStar_trans h1 h2

theorem clean_P1_one (r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_B (decLState (.clean 0 segs (bot + 1))) (0 :: (blkR r ++ R))) [target_tm]⊢*
    (cfg_B (decLState (.clean 0 (pushSeg (r + 3) 1 segs) bot)) (0 :: R)) := by
  have heqR : 0 :: (blkR r ++ R) = rep0 (r + 1) ++ (2 :: 1 :: R) := by norm_all
  rw [heqR]
  have h1 := rule_B_zeros_all (decLState (.clean 0 segs (bot + 1))) (2 :: 1 :: R) (r + 1)
  have h2 := stepPlus_stepStar (rule_B_succ_step 1 (rep0 (r + 1) ++ decLState (.clean 0 segs (bot + 1))) (1 :: R))
  have heq2 : 0 :: (rep0 (r + 1) ++ decLState (.clean 0 segs (bot + 1))) =
      decLState (.clean (r + 2) segs (bot + 1)) := by norm_all
  rw [heq2] at h2
  have h3 := stepPlus_stepStar (rule_BR_one (decLState (.clean (r + 2) segs (bot + 1))) (1 :: R))
  have h4 := clean_DR0_one (r + 2) segs bot (2 :: R)
  have h5 := stepPlus_stepStar (rule_BR_add_two 0 (decLState (.clean (r + 6) segs bot)) R)
  have heq5 : bumpHead (decLState (.clean (r + 6) segs bot)) =
      decLState (.clean 0 (pushSeg (r + 3) 1 segs) bot) := by norm_all
  rw [heq5] at h5
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem clean_P1_pow : ∀ (q r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_B (decLState (.clean 0 segs (bot + q))) (0 :: ((blkR r) ^ q ++ R))) [target_tm]⊢*
    (cfg_B (decLState (.clean 0 (pushSeg (r + 3) q segs) bot)) (0 :: R))
  | 0, r, segs, bot, R => by simp [pushSeg, HPow.hPow, list_nat_repeat]
  | q + 1, r, segs, bot, R => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have heqR : (blkR r) ^ (q + 1) ++ R = blkR r ++ ((blkR r) ^ q ++ R) := by
      simp [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [heqR]
    have h1 := clean_P1_one r segs (bot + q) ((blkR r) ^ q ++ R)
    have h2 := clean_P1_pow q r (pushSeg (r + 3) 1 segs) bot R
    have heqL : decLState (.clean 0 (pushSeg (r + 3) q (pushSeg (r + 3) 1 segs)) bot) =
        decLState (.clean 0 (pushSeg (r + 3) (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    exact stepStar_trans h1 h2

theorem clean_P2_one (r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_B (decLState (.clean 0 segs (bot + (r + 1)))) (1 :: 1 :: (blkR r ++ R))) [target_tm]⊢*
    (cfg_B (decLState (.clean 0 (pushSeg (4 * r + 3) 1 segs) bot)) (1 :: 1 :: R)) := by
  cases r with
  | zero =>
    have h1 := stepPlus_stepStar (rule_B_succ_step 0 (decLState (.clean 0 segs (bot + 1))) (1 :: (blkR 0 ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_zero (0 :: decLState (.clean 0 segs (bot + 1))) (1 :: (blkR 0 ++ R)))
    have heq2 : 0 :: 0 :: decLState (.clean 0 segs (bot + 1)) =
        decLState (.clean 2 segs (bot + 1)) := rfl
    rw [heq2] at h2
    have h3 := stepPlus_stepStar (rule_BR_one (decLState (.clean 2 segs (bot + 1))) (blkR 0 ++ R))
    have hb0 : bumpHead (blkR 0 ++ R) = 3 :: 1 :: R := rfl
    rw [hb0] at h3
    have h4 := clean_DR0_one 2 segs bot (3 :: 1 :: R)
    have h5 := stepPlus_stepStar (rule_BR_add_two 1 (decLState (.clean 6 segs bot)) (1 :: R))
    have heq5 : bumpHead (decLState (.clean 6 segs bot)) =
        decLState (.clean 0 (pushSeg 3 1 segs) bot) := by norm_all
    rw [heq5] at h5
    exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))
  | succ r' =>
    rw [show bot + (r' + 1 + 1) = (bot + 2) + r' by omega]
    have h1 := stepPlus_stepStar (rule_B_succ_step 0 (decLState (.clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_zero (0 :: decLState (.clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))
    have heq2 : 0 :: 0 :: decLState (.clean 0 segs ((bot + 2) + r')) =
        decLState (.clean 2 segs ((bot + 2) + r')) := rfl
    rw [heq2] at h2
    have h3 := stepPlus_stepStar (rule_BR_one (decLState (.clean 2 segs ((bot + 2) + r'))) (blkR (r' + 1) ++ R))
    have hb : bumpHead (blkR (r' + 1) ++ R) = 1 :: (rep0 r' ++ (2 :: 1 :: R)) := by norm_all
    rw [hb] at h3
    have h4 := clean_DR0_zeros r' 2 segs (bot + 2) (2 :: 1 :: R)
    have h5 := clean_DR0_one (2 + 4 * r') segs (bot + 1) (1 :: 2 :: 1 :: R)
    have h6 := stepPlus_stepStar (rule_BR_one (decLState (.clean (2 + 4 * r' + 4) segs (bot + 1))) (2 :: 1 :: R))
    have h7 := clean_DR0_one (2 + 4 * r' + 4) segs bot (3 :: 1 :: R)
    have h8 := stepPlus_stepStar (rule_BR_add_two 1 (decLState (.clean (2 + 4 * r' + 8) segs bot)) (1 :: R))
    have heq8 : bumpHead (decLState (.clean (2 + 4 * r' + 8) segs bot)) =
        decLState (.clean 0 (pushSeg (4 * (r' + 1) + 3) 1 segs) bot) := by
      rw [show 4 * (r' + 1) + 3 = 4 * r' + 7 by omega]
      norm_all
    rw [heq8] at h8
    exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3
      (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 (stepStar_trans h7 h8))))))

theorem clean_P2_pow : ∀ (q r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_B (decLState (.clean 0 segs (bot + q * (r + 1)))) (1 :: 1 :: ((blkR r) ^ q ++ R))) [target_tm]⊢*
    (cfg_B (decLState (.clean 0 (pushSeg (4 * r + 3) q segs) bot)) (1 :: 1 :: R))
  | 0, r, segs, bot, R => by simp [pushSeg, HPow.hPow, list_nat_repeat]
  | q + 1, r, segs, bot, R => by
    rw [show bot + (q + 1) * (r + 1) = (bot + q * (r + 1)) + (r + 1) by
      rw [Nat.succ_mul, Nat.add_assoc]]
    have heqR : (blkR r) ^ (q + 1) ++ R = blkR r ++ ((blkR r) ^ q ++ R) := by
      simp [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [heqR]
    have h1 := clean_P2_one r segs (bot + q * (r + 1)) ((blkR r) ^ q ++ R)
    have h2 := clean_P2_pow q r (pushSeg (4 * r + 3) 1 segs) bot R
    have heqL : decLState (.clean 0 (pushSeg (4 * r + 3) q (pushSeg (4 * r + 3) 1 segs)) bot) =
        decLState (.clean 0 (pushSeg (4 * r + 3) (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    exact stepStar_trans h1 h2

-- ============================================================================
-- Section 4: Executable RLE Stack Engine & Denotational Soundness
-- ============================================================================

def pushL0 (c : ℕ) (L : List Item) : List Item :=
  if Nat.beq c 0 then L
  else match L with
    | .z c2 :: xs => .z (c + c2) :: xs
    | _ => .z c :: L

def pushLk2 (r c : ℕ) (L : List Item) : List Item :=
  if Nat.beq c 0 then L
  else match L with
    | .k r2 c2 :: xs => if Nat.beq r r2 then .k r (c + c2) :: xs else .k r c :: L
    | _ => .k r c :: L

def pushLd (v : ℕ) (L : List Item) : List Item :=
  if Nat.beq v 0 then pushL0 1 L
  else if Nat.beq v 1 then
    match L with
    | .z c :: .d v2 :: xs =>
      if Nat.beq v2 1 && Nat.ble 2 c then .d 1 :: pushLk2 (c - 2) 1 xs
      else .d 1 :: L
    | _ => .d 1 :: L
  else .d v :: L

def popKTail (r c : ℕ) (xs : List Item) : List Item :=
  if Nat.beq c 1 then xs else .k r (c - 1) :: xs

def popL1 : List Item → Option (ℕ × List Item)
  | [] => none
  | .z c :: xs =>
    if Nat.beq c 0 then popL1 xs
    else if Nat.beq c 1 then some (0, xs)
    else some (0, .z (c - 1) :: xs)
  | .k r c :: xs =>
    if Nat.beq c 0 then popL1 xs
    else some (0, pushL0 (r + 1) (pushLd 1 (popKTail r c xs)))
  | .d v :: xs => some (v, xs)

def bumpL (L : List Item) : List Item :=
  match popL1 L with
  | none => [.z 1]
  | some (a, L1) => pushLd (a + 1) L1

def pushR0 (c : ℕ) (R : List Item) : List Item :=
  if Nat.beq c 0 then R
  else match R with
    | .z c2 :: xs => .z (c + c2) :: xs
    | _ => .z c :: R

def mergeRk2Pre (r c : ℕ) (R : List Item) : ℕ × List Item :=
  if Nat.ble 1 r then
    match R with
    | .z rz :: .d v2 :: .d v1 :: xs =>
      if Nat.beq rz r && Nat.beq v2 2 && Nat.beq v1 1 then (c + 1, xs) else (c, R)
    | _ => (c, R)
  else (c, R)

def pushRk2 (r c : ℕ) (R : List Item) : List Item :=
  if Nat.beq c 0 then R
  else
    let p := mergeRk2Pre r c R
    match p.2 with
    | .k r2 c2 :: xs => if Nat.beq r r2 then .k r (p.1 + c2) :: xs else .k r p.1 :: p.2
    | _ => .k r p.1 :: p.2

def pushRd (v : ℕ) (R : List Item) : List Item :=
  if Nat.beq v 0 then pushR0 1 R
  else if Nat.beq v 2 then
    match R with
    | .d v1 :: xs => if Nat.beq v1 1 then pushRk2 0 1 xs else .d 2 :: R
    | _ => .d 2 :: R
  else .d v :: R

def popR1 : List Item → Option (ℕ × List Item)
  | [] => none
  | .z c :: xs =>
    if Nat.beq c 0 then popR1 xs
    else if Nat.beq c 1 then some (0, xs)
    else some (0, .z (c - 1) :: xs)
  | .k r c :: xs =>
    if Nat.beq c 0 then popR1 xs
    else if Nat.beq r 0 then some (2, .d 1 :: popKTail r c xs)
    else some (0, pushR0 (r - 1) (.d 2 :: .d 1 :: popKTail r c xs))
  | .d v :: xs => some (v, xs)

def bumpR (R : List Item) : List Item :=
  match popR1 R with
  | none => [.z 1]
  | some (d, R1) => pushRd (d + 1) R1

def segsToItems : List (ℕ × ℕ) → List Item → List Item
  | [], acc => acc
  | (r, c) :: ss, acc =>
    if Nat.beq c 0 then segsToItems ss acc
    else .k r c :: segsToItems ss acc

def unpackClean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) : List Item :=
  let tail := segsToItems segs [.z (bot + 2)]
  if Nat.beq c0 0 then .d 1 :: tail else .z c0 :: .d 1 :: tail

def packTail (cur0 : ℕ) : List Item → Option (List (ℕ × ℕ) × ℕ)
  | [] => if Nat.ble 2 cur0 then some ([], cur0 - 2) else none
  | .z c :: rest => packTail (cur0 + c) rest
  | .d v :: rest =>
    if Nat.beq v 1 && Nat.ble 2 cur0 then
      match packTail 0 rest with
      | some (segs, bot) => some (pushSeg (cur0 - 2) 1 segs, bot)
      | none => none
    else none
  | .k r c :: rest =>
    if Nat.beq c 0 then packTail cur0 rest
    else
      match packTail 0 rest with
      | some (segs, bot) =>
        some (pushSeg (cur0 + r) 1 (pushSeg r (c - 1) segs), bot)
      | none => none

def packHead (cur0 : ℕ) : List Item → Option LState
  | [] => none
  | .z c :: rest => packHead (cur0 + c) rest
  | .d v :: rest =>
    if Nat.beq v 1 then
      match packTail 0 rest with
      | some (segs, bot) => some (.clean cur0 segs bot)
      | none => none
    else none
  | .k r c :: rest =>
    if Nat.beq c 0 then packHead cur0 rest
    else
      match packTail 0 rest with
      | some (segs, bot) =>
        some (.clean (cur0 + r + 2) (pushSeg r (c - 1) segs) bot)
      | none => none

lemma decL_pushL0 (c : ℕ) (L : List Item) :
    decL (pushL0 c L) = rep0 c ++ decL L := by
  unfold pushL0
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases L with
    | nil => rfl
    | cons hd xs =>
      cases hd with
      | z c2 => norm_all
      | d _ => rfl
      | k _ _ => rfl

lemma decL_pushLk2 (r c : ℕ) (L : List Item) :
    decL (pushLk2 r c L) = (blkL r) ^ c ++ decL L := by
  unfold pushLk2
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases L with
    | nil => rfl
    | cons hd xs =>
      cases hd with
      | z _ => rfl
      | d _ => rfl
      | k r2 c2 =>
        dsimp only; split
        · next hr =>
          rw [Nat.beq_eq] at hr; subst hr
          simp [decL, list_pow_add, List.append_assoc]
        · rfl

lemma decL_pushLd (v : ℕ) (L : List Item) :
    decL (pushLd v L) = v :: decL L := by
  unfold pushLd
  split
  · next h => rw [Nat.beq_eq] at h; subst h; simpa using decL_pushL0 1 L
  · split
    · next h =>
      rw [Nat.beq_eq] at h; subst h
      rcases L with _ | ⟨hd1, _ | ⟨hd2, xs⟩⟩
      · rfl
      · cases hd1 <;> rfl
      · cases hd1 with
        | z c =>
          cases hd2 with
          | d v2 =>
            dsimp only; split
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
              rcases hb with ⟨rfl, hc⟩
              simp only [decL, decL_pushLk2]
              conv_rhs => rw [show c = (c - 2) + 2 by omega]
              norm_all
            · rfl
          | _ => rfl
        | _ => rfl
    · rfl

lemma decL_popKTail (r c : ℕ) (xs : List Item) :
    decL (popKTail r c xs) = (blkL r) ^ (c - 1) ++ decL xs := by
  unfold popKTail; split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · rfl

lemma decR_popKTail (r c : ℕ) (xs : List Item) :
    decR (popKTail r c xs) = (blkR r) ^ (c - 1) ++ decR xs := by
  unfold popKTail; split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · rfl

lemma decL_popL1_none : ∀ (L : List Item), popL1 L = none → decL L = []
  | [], _ => rfl
  | .z c :: xs, h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_none xs h
    · split at h <;> cases h
  | .d _ :: _, h => by cases h
  | .k r c :: xs, h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_none xs h
    · cases h

lemma decL_popL1_some : ∀ (L : List Item) (a : ℕ) (L' : List Item),
    popL1 L = some (a, L') → decL L = a :: decL L'
  | [], _, _, h => by cases h
  | .z c :: xs, a, L', h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_some xs a L' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      split at h
      · next hc1 =>
        rw [Nat.beq_eq] at hc1; subst hc1
        cases h; rfl
      · cases h
        conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
        norm_all
  | .d v :: xs, a, L', h => by cases h; rfl
  | .k r c :: xs, a, L', h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_some xs a L' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      cases h
      rw [decL_pushL0, decL_pushLd, decL_popKTail]
      conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
      norm_all

lemma decL_bumpL (L : List Item) : decL (bumpL L) = bumpHead (decL L) := by
  unfold bumpL
  cases hp : popL1 L with
  | none => rw [decL_popL1_none L hp]; rfl
  | some p =>
    rcases p with ⟨a, L1⟩
    rw [decL_popL1_some L a L1 hp, decL_pushLd]; rfl

lemma decR_pushR0 (c : ℕ) (R : List Item) :
    decR (pushR0 c R) = rep0 c ++ decR R := by
  unfold pushR0
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases R with
    | nil => rfl
    | cons hd xs =>
      cases hd with
      | z c2 => norm_all
      | d _ => rfl
      | k _ _ => rfl

lemma mergeRk2Pre_spec (r c : ℕ) (R : List Item) :
    (blkR r) ^ (mergeRk2Pre r c R).1 ++ decR (mergeRk2Pre r c R).2 =
    (blkR r) ^ c ++ decR R := by
  unfold mergeRk2Pre
  split
  · rcases R with _ | ⟨hd1, _ | ⟨hd2, _ | ⟨hd3, xs⟩⟩⟩
    · rfl
    · cases hd1 <;> rfl
    · cases hd1 <;> cases hd2 <;> rfl
    · cases hd1 with
      | z rz =>
        cases hd2 with
        | d v2 =>
          cases hd3 with
          | d v1 =>
            dsimp only; split
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq] at hb
              rcases hb with ⟨⟨rfl, rfl⟩, rfl⟩
              rw [pow_succ_right_list]
              norm_all
            · rfl
          | _ => rfl
        | _ => rfl
      | _ => rfl
  · rfl

lemma decR_pushRk2 (r c : ℕ) (R : List Item) :
    decR (pushRk2 r c R) = (blkR r) ^ c ++ decR R := by
  unfold pushRk2
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · have key := mergeRk2Pre_spec r c R
    generalize mergeRk2Pre r c R = p at key ⊢
    rcases p with ⟨c', R'⟩
    dsimp only at key ⊢
    cases R' with
    | nil => exact key
    | cons hd xs =>
      cases hd with
      | z _ => exact key
      | d _ => exact key
      | k r2 c2 =>
        dsimp only; split
        · next hr =>
          rw [Nat.beq_eq] at hr; subst hr
          rw [← key]; simp [decR, list_pow_add, List.append_assoc]
        · exact key

lemma decR_pushRd (v : ℕ) (R : List Item) :
    decR (pushRd v R) = v :: decR R := by
  unfold pushRd
  split
  · next h => rw [Nat.beq_eq] at h; subst h; simpa using decR_pushR0 1 R
  · split
    · next h =>
      rw [Nat.beq_eq] at h; subst h
      cases R with
      | nil => rfl
      | cons hd xs =>
        cases hd with
        | d v1 =>
          dsimp only; split
          · next hv =>
            rw [Nat.beq_eq] at hv; subst hv
            rw [decR_pushRk2]; norm_all
          · rfl
        | _ => rfl
    · rfl

lemma decR_popR1_none : ∀ (R : List Item), popR1 R = none → decR R = []
  | [], _ => rfl
  | .z c :: xs, h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_none xs h
    · split at h <;> cases h
  | .d _ :: _, h => by cases h
  | .k r c :: xs, h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_none xs h
    · split at h <;> cases h

lemma decR_popR1_some : ∀ (R : List Item) (d : ℕ) (R' : List Item),
    popR1 R = some (d, R') → decR R = d :: decR R'
  | [], _, _, h => by cases h
  | .z c :: xs, d, R', h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_some xs d R' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      split at h
      · next hc1 => rw [Nat.beq_eq] at hc1; subst hc1; cases h; rfl
      · cases h
        conv_lhs => rw [decR, show c = (c - 1) + 1 by omega]
        norm_all
  | .d v :: xs, d, R', h => by cases h; rfl
  | .k r c :: xs, d, R', h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_some xs d R' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      split at h
      · next hr0 =>
        rw [Nat.beq_eq] at hr0; subst hr0; cases h
        rw [decR, decR_popKTail]
        conv_lhs => rw [decR, show c = (c - 1) + 1 by omega]
        norm_all
      · next hr0 =>
        have hrne : r ≠ 0 := fun heq => hr0 (Nat.beq_eq.mpr heq)
        cases h
        have hc : (blkR r) ^ c = rep0 ((r - 1) + 1) ++ ([2, 1] ++ (blkR r) ^ (c - 1)) := by
          conv_lhs =>
            rw [show c = (c - 1) + 1 by omega, pow_succ_list_gen]
            arg 1
            rw [blkR, show r = (r - 1) + 1 by omega]
          exact List.append_assoc _ _ _
        rw [decR_pushR0, decR, decR, decR_popKTail, decR, hc]
        simp only [rep0, List.replicate_succ, List.cons_append, List.nil_append, List.append_assoc]

lemma decR_bumpR (R : List Item) : decR (bumpR R) = bumpHead (decR R) := by
  unfold bumpR
  cases hp : popR1 R with
  | none => rw [decR_popR1_none R hp]; rfl
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [decR_popR1_some R d R1 hp, decR_pushRd]; rfl

lemma decL_segsToItems : ∀ (segs : List (ℕ × ℕ)) (acc : List Item),
    decL (segsToItems segs acc) = decSegs segs ++ decL acc
  | [], acc => rfl
  | (r, c) :: ss, acc => by
    unfold segsToItems; split
    · next hc =>
      rw [Nat.beq_eq] at hc; subst hc
      simpa [decSegs, HPow.hPow, list_nat_repeat] using decL_segsToItems ss acc
    · simp [decL, decSegs, decL_segsToItems ss acc, List.append_assoc]

lemma decL_unpackClean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) :
    decL (unpackClean c0 segs bot) = decLState (.clean c0 segs bot) := by
  unfold unpackClean
  split
  · next hc => rw [Nat.beq_eq] at hc; subst hc; simp [decL, decLState, decL_segsToItems]
  · simp [decL, decLState, decL_segsToItems]

lemma packTail_spec : ∀ (items : List Item) (cur0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ),
    packTail cur0 items = some (segs, bot) →
    rep0 cur0 ++ decL items = decSegs segs ++ rep0 (bot + 2)
  | [], cur0, segs, bot, h => by
    unfold packTail at h; split at h
    · next hb =>
      have hge : 2 ≤ cur0 := Nat.ble_eq.mp hb
      cases h
      rw [show cur0 - 2 + 2 = cur0 by omega]; norm_all
    · cases h
  | .z c :: rest, cur0, segs, bot, h => by
    unfold packTail at h
    have ih := packTail_spec rest (cur0 + c) segs bot h
    rw [decL, ← List.append_assoc, ← rep0_add_split]; exact ih
  | .d v :: rest, cur0, segs, bot, h => by
    unfold packTail at h; split at h
    · next hb =>
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
      rcases hb with ⟨rfl, hge⟩
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        have ih := packTail_spec rest 0 ss b hp
        rw [hp] at h; cases h
        rw [rep0_zero, List.nil_append] at ih
        rw [decSegs_pushSeg]
        conv_lhs => rw [decL, show cur0 = (cur0 - 2) + 2 by omega]
        rw [ih]; norm_all
    · cases h
  | .k r c :: rest, cur0, segs, bot, h => by
    unfold packTail at h; split at h
    · next hc =>
      rw [Nat.beq_eq] at hc; subst hc
      simpa [decL, HPow.hPow, list_nat_repeat] using packTail_spec rest cur0 segs bot h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        have ih := packTail_spec rest 0 ss b hp
        rw [hp] at h; cases h
        rw [rep0_zero, List.nil_append] at ih
        conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
        rw [ih]; norm_all

lemma packHead_spec : ∀ (items : List Item) (cur0 : ℕ) (ls : LState),
    packHead cur0 items = some ls →
    rep0 cur0 ++ decL items = decLState ls
  | [], _, _, h => by cases h
  | .z c :: rest, cur0, ls, h => by
    unfold packHead at h
    have ih := packHead_spec rest (cur0 + c) ls h
    rw [decL, ← List.append_assoc, ← rep0_add_split]; exact ih
  | .d v :: rest, cur0, ls, h => by
    unfold packHead at h; split at h
    · next hv =>
      rw [Nat.beq_eq] at hv; subst hv
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        rw [hp] at h; cases h
        have ih := packTail_spec rest 0 ss b hp
        rw [rep0_zero, List.nil_append] at ih
        simp [decL, decLState, ih]
    · cases h
  | .k r c :: rest, cur0, ls, h => by
    unfold packHead at h; split at h
    · next hc =>
      rw [Nat.beq_eq] at hc; subst hc
      simpa [decL, HPow.hPow, list_nat_repeat] using packHead_spec rest cur0 ls h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        rw [hp] at h; cases h
        have ih := packTail_spec rest 0 ss b hp
        rw [rep0_zero, List.nil_append] at ih
        conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
        rw [ih]; norm_all

-- ============================================================================
-- Section 5: Modular Transition Engine `rleStep` & Per-Mode Soundness
-- ============================================================================

structure RleFullState where
  mode : StackMode
  ls : LState
  R : List Item
  halted : Bool

def CanHalt (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg, (c [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone

lemma canHalt_of_stepStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [target_tm]⊢* c₂) (hc : CanHalt c₂) : CanHalt c₁ := by
  obtain ⟨cfg, h₂, hnone⟩ := hc
  exact ⟨cfg, stepStar_trans h h₂, hnone⟩

lemma canHalt_of_stepPlus {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [target_tm]⊢⁺ c₂) (hc : CanHalt c₂) : CanHalt c₁ :=
  canHalt_of_stepStar (stepPlus_stepStar h) hc

def evalRle (s : RleFullState) : Cfg (Fin 2) (Fin 6) :=
  evalStackCfg1 s.mode (decLState s.ls) (decR s.R)

def StateHalts (s : RleFullState) : Prop :=
  s.halted = true ∨ CanHalt (evalRle s)

lemma stateHalts_of_stepStar {c : Cfg (Fin 2) (Fin 6)} {s' : RleFullState}
    (hf : s'.halted = false)
    (hstep : c [target_tm]⊢* evalRle s')
    (hh : StateHalts s') : CanHalt c := by
  rcases hh with hh | hh
  · rw [hf] at hh; cases hh
  · exact canHalt_of_stepStar hstep hh

def isTopD1 : List Item → Bool
  | .d v :: _ => Nat.beq v 1
  | _ => false

def modeCanPack (m : StackMode) (items R : List Item) : Bool :=
  match m with
  | .B => R.isEmpty || isTopD1 items
  | .BR => R.isEmpty
  | .DR0 => true
  | .C => false

def minNat (a b : ℕ) : ℕ := if Nat.ble a b then a else b

lemma minNat_le_left (a b : ℕ) : minNat a b ≤ a := by
  unfold minNat; split
  · exact le_rfl
  · next h => have : ¬ a ≤ b := fun hab => h (Nat.ble_eq.mpr hab); omega

lemma minNat_le_right (a b : ℕ) : minNat a b ≤ b := by
  unfold minNat; split
  · next h => exact Nat.ble_eq.mp h
  · exact le_rfl

-- 5.1 Raw B
def stepRawB (items R : List Item) : RleFullState :=
  match R with
  | [] => ⟨.C, .raw (bumpL items), [], false⟩
  | .z c :: R1 => ⟨.B, .raw (pushL0 c items), R1, false⟩
  | _ =>
    match popR1 R with
    | none => ⟨.C, .raw (bumpL items), [], false⟩
    | some (d, R1) =>
      if Nat.beq d 0 then ⟨.B, .raw (pushL0 1 items), R1, false⟩
      else ⟨.BR, .raw items, pushR0 1 (pushRd (d - 1) R1), false⟩

lemma stepRawB_halts (items R : List Item) (hh : StateHalts (stepRawB items R)) :
    CanHalt (cfg_B (decL items) (decR R)) := by
  unfold stepRawB at hh
  cases R with
  | nil =>
    refine stateHalts_of_stepStar rfl ?_ hh
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      stepPlus_stepStar (rule_B_nil (decL items))
  | cons hd R1 =>
    cases hd with
    | z c =>
      refine stateHalts_of_stepStar rfl ?_ hh
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR] using
        rule_B_zeros_all (decL items) (decR R1) c
    | d v =>
      dsimp only at hh
      cases hp : popR1 (.d v :: R1) with
      | none => cases hp
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR]
          simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
            stepPlus_stepStar (rule_B_zero (decL items) (decR R2))
        · next hd0 =>
          have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR, show d = (d - 1) + 1 by omega]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0, decR_pushRd] using
            stepPlus_stepStar (rule_B_succ (d - 1) (decL items) (decR R2))
    | k r c =>
      dsimp only at hh
      cases hp : popR1 (.k r c :: R1) with
      | none =>
        rw [hp] at hh
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [decR_popR1_none _ hp]
        simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
          stepPlus_stepStar (rule_B_nil (decL items))
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR]
          simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
            stepPlus_stepStar (rule_B_zero (decL items) (decR R2))
        · next hd0 =>
          have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR, show d = (d - 1) + 1 by omega]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0, decR_pushRd] using
            stepPlus_stepStar (rule_B_succ (d - 1) (decL items) (decR R2))

-- 5.2 Raw BR
def stepRawBRPop (items R : List Item) : RleFullState :=
  match popR1 R with
  | none => ⟨.C, .raw (bumpL items), [], false⟩
  | some (d, R1) =>
    if Nat.beq d 0 then ⟨.BR, .raw (pushL0 1 items), R1, false⟩
    else if Nat.beq d 1 then ⟨.DR0, .raw items, bumpR R1, false⟩
    else ⟨.B, .raw (bumpL items), pushRd (d - 2) R1, false⟩

lemma stepRawBRPop_halts (items R : List Item) (hh : StateHalts (stepRawBRPop items R)) :
    CanHalt (cfg_BR (decL items) (decR R)) := by
  unfold stepRawBRPop at hh
  cases hp : popR1 R with
  | none =>
    rw [hp] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    rw [decR_popR1_none R hp]
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      stepPlus_stepStar (rule_BR_nil (decL items))
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [hp] at hh
    have hR := decR_popR1_some R d R1 hp
    dsimp only at hh; split at hh
    · next hd0 =>
      rw [Nat.beq_eq] at hd0; subst hd0
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hR]
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
        stepPlus_stepStar (rule_BR_zero (decL items) (decR R1))
    · next hd0 =>
      have hdne0 : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
      split at hh
      · next hd1 =>
        rw [Nat.beq_eq] at hd1; subst hd1
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [hR]
        simpa [evalRle, evalStackCfg1, decLState, decR_bumpR] using
          stepPlus_stepStar (rule_BR_one (decL items) (decR R1))
      · next hd1 =>
        have hdne1 : d ≠ 1 := fun h => hd1 (Nat.beq_eq.mpr h)
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [hR, show d = (d - 2) + 2 by omega]
        simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushRd] using
          stepPlus_stepStar (rule_BR_add_two (d - 2) (decL items) (decR R1))

def stepRawBR (items R : List Item) : RleFullState :=
  match R with
  | [] => ⟨.C, .raw (bumpL items), [], false⟩
  | .z c :: R1 => ⟨.BR, .raw (pushL0 c items), R1, false⟩
  | .k r m :: R1 =>
    if Nat.ble 1 m then
      match popL1 items with
      | some (a, L1) =>
        if Nat.beq a 0 then
          ⟨.BR, .raw (pushL0 3 (pushLd 1 (pushLk2 r (m - 1) (pushL0 r L1)))), R1, false⟩
        else stepRawBRPop items (.k r m :: R1)
      | none => stepRawBRPop items (.k r m :: R1)
    else ⟨.BR, .raw items, R1, false⟩
  | .d v :: R1 => stepRawBRPop items (.d v :: R1)

lemma stepRawBR_halts (items R : List Item) (hh : StateHalts (stepRawBR items R)) :
    CanHalt (cfg_BR (decL items) (decR R)) := by
  unfold stepRawBR at hh
  cases R with
  | nil =>
    refine stateHalts_of_stepStar rfl ?_ hh
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      stepPlus_stepStar (rule_BR_nil (decL items))
  | cons hd R1 =>
    cases hd with
    | z c =>
      refine stateHalts_of_stepStar rfl ?_ hh
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR] using
        rule_BR_zeros_all (decL items) (decR R1) c
    | d v => exact stepRawBRPop_halts items (.d v :: R1) hh
    | k r m =>
      dsimp only at hh; split at hh
      · next hm1 =>
        have hmge : 1 ≤ m := Nat.ble_eq.mp hm1
        cases hpL : popL1 items with
        | none =>
          rw [hpL] at hh
          exact stepRawBRPop_halts items (.k r m :: R1) hh
        | some pL =>
          rcases pL with ⟨a, L1⟩
          rw [hpL] at hh; dsimp only at hh; split at hh
          · next ha0 =>
            rw [Nat.beq_eq] at ha0; subst ha0
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [decL_popL1_some items 0 L1 hpL, decR, show m = (m - 1) + 1 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decL_pushLd,
              decL_pushLk2, List.append_assoc] using
              rule_BR_blkR_succ (m - 1) r (decL L1) (decR R1)
          · exact stepRawBRPop_halts items (.k r m :: R1) hh
      · next hm0 =>
        have hmeq : m = 0 := by
          have : ¬ 1 ≤ m := fun h => hm0 (Nat.ble_eq.mpr h); omega
        subst hmeq
        refine stateHalts_of_stepStar rfl ?_ hh
        exact ⟨0, rfl⟩

-- 5.3 Raw DR0
def stepRawDR0Atomic (items R : List Item) : RleFullState :=
  match popL1 items with
  | none => ⟨.C, .raw [.d 1], R, false⟩
  | some (a, L1) =>
    if Nat.beq a 0 then
      match items with
      | .z c :: Lrest => ⟨.DR0, .raw Lrest, pushR0 c R, false⟩
      | _ => ⟨.DR0, .raw L1, pushR0 1 R, false⟩
    else ⟨.C, .raw (pushLd (a - 1) L1), pushR0 1 R, false⟩

lemma stepRawDR0Atomic_halts (items R : List Item) (hh : StateHalts (stepRawDR0Atomic items R)) :
    CanHalt (cfg_DR0 (decL items) (decR R)) := by
  unfold stepRawDR0Atomic at hh
  cases hpL : popL1 items with
  | none =>
    rw [hpL] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    rw [decL_popL1_none items hpL]
    simpa [evalRle, evalStackCfg1, decLState, decL] using
      stepPlus_stepStar (rule_DR0_nil (decR R))
  | some pL =>
    rcases pL with ⟨a, L1⟩
    rw [hpL] at hh
    have hL := decL_popL1_some items a L1 hpL
    dsimp only at hh; split at hh
    · next ha0 =>
      rw [Nat.beq_eq] at ha0; subst ha0
      cases items with
      | nil => cases hpL
      | cons hd Lrest =>
        cases hd with
        | z c =>
          refine stateHalts_of_stepStar rfl ?_ hh
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushR0] using
            rule_DR0_zeros_all (decL Lrest) (decR R) c
        | d _ =>
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0] using
            stepPlus_stepStar (rule_DR0_zero (decL L1) (decR R))
        | k _ _ =>
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0] using
            stepPlus_stepStar (rule_DR0_zero (decL L1) (decR R))
    · next ha0 =>
      have hane : a ≠ 0 := fun h => ha0 (Nat.beq_eq.mpr h)
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hL, show a = (a - 1) + 1 by omega]
      simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushR0] using
        stepPlus_stepStar (rule_DR0_succ (a - 1) (decL L1) (decR R))

def stepRawDR0 (items R : List Item) : RleFullState :=
  match items with
  | [.z c] =>
    match R with
    | .d v1 :: .z q :: R2 =>
      if Nat.beq v1 1 then ⟨.DR0, .raw [.z (c + 3 * q)], .d 1 :: R2, false⟩
      else ⟨.BR, .raw [.z (c + 3)], R, false⟩
    | _ => ⟨.BR, .raw [.z (c + 3)], R, false⟩
  | _ => stepRawDR0Atomic items R

lemma stepRawDR0_halts (items R : List Item) (hh : StateHalts (stepRawDR0 items R)) :
    CanHalt (cfg_DR0 (decL items) (decR R)) := by
  unfold stepRawDR0 at hh
  rcases items with _ | ⟨hd1, _ | ⟨hd2, xs⟩⟩
  · exact stepRawDR0Atomic_halts [] R hh
  · cases hd1 with
    | z c =>
      have hbot : ∀ (hhb : StateHalts ⟨.BR, .raw [.z (c + 3)], R, false⟩),
          CanHalt (cfg_DR0 (decL [.z c]) (decR R)) := by
        intro hhb
        refine stateHalts_of_stepStar rfl ?_ hhb
        simpa [evalRle, evalStackCfg1, decLState, decL] using rule_DR0_bot c (decR R)
      rcases R with _ | ⟨r1, _ | ⟨r2, R2⟩⟩
      · exact hbot hh
      · cases r1 <;> exact hbot hh
      · cases r1 with
        | d v1 =>
          cases r2 with
          | z q =>
            dsimp only at hh; split at hh
            · next hv1 =>
              rw [Nat.beq_eq] at hv1; subst hv1
              refine stateHalts_of_stepStar rfl ?_ hh
              simpa [evalRle, evalStackCfg1, decLState, decL, decR] using
                rule_DR0_bot_zeros q c (decR R2)
            · exact hbot hh
          | _ => exact hbot hh
        | _ => exact hbot hh
    | d _ => exact stepRawDR0Atomic_halts _ R hh
    | k _ _ => exact stepRawDR0Atomic_halts _ R hh
  · cases hd1 <;> exact stepRawDR0Atomic_halts _ R hh

-- 5.4 Raw C
def stepRawCAtomic (items R : List Item) : RleFullState :=
  match popL1 items with
  | none => ⟨.DR0, .raw [], R, false⟩
  | some (a, L1) =>
    if Nat.beq a 0 then
      match popL1 L1 with
      | none => ⟨.C, .raw [], pushRd 1 R, false⟩
      | some (a1, L3) =>
        if Nat.beq a1 0 then ⟨.C, .raw (bumpL L3), pushRd 1 R, false⟩
        else if Nat.beq a1 1 then ⟨.C, .raw (bumpL (bumpL L3)), pushR0 1 (bumpR R), false⟩
        else ⟨.BR, .raw (pushLd (a1 - 2) L3), pushR0 1 (pushRd 1 R), false⟩
    else if Nat.beq a 1 then
      match popL1 L1 with
      | none => ⟨.B, .raw [.z 1], pushRd 1 R, false⟩
      | some (a1, L3) =>
        if Nat.beq a1 0 then ⟨.DR0, .raw L3, pushRd 2 R, false⟩
        else ⟨.C, .raw (pushLd (a1 - 1) L3), pushRd 2 R, false⟩
    else ⟨.C, .raw (pushLd a L1), R, true⟩

lemma stepRawCAtomic_halts (items R : List Item) (hh : StateHalts (stepRawCAtomic items R)) :
    CanHalt (cfg_C (decL items) (decR R)) := by
  unfold stepRawCAtomic at hh
  cases hp1 : popL1 items with
  | none =>
    rw [hp1] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    rw [decL_popL1_none items hp1]
    exact stepPlus_stepStar (rule_C_nil _)
  | some p1 =>
    rcases p1 with ⟨a, L1⟩
    rw [hp1] at hh
    have hL1 := decL_popL1_some items a L1 hp1
    dsimp only at hh; split at hh
    · next ha0 =>
      rw [Nat.beq_eq] at ha0; subst ha0
      cases hp2 : popL1 L1 with
      | none =>
        rw [hp2] at hh
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [hL1, decL_popL1_none L1 hp2]
        simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRd] using
          stepPlus_stepStar (rule_C_zero_nil (decR R))
      | some p2 =>
        rcases p2 with ⟨a1, L3⟩
        rw [hp2] at hh
        have hL2 := decL_popL1_some L1 a1 L3 hp2
        dsimp only at hh; split at hh
        · next ha10 =>
          rw [Nat.beq_eq] at ha10; subst ha10
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL1, hL2]
          simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushRd] using
            stepPlus_stepStar (rule_C_zero_zero (decL L3) (decR R))
        · next ha10 =>
          have hne0 : a1 ≠ 0 := fun h => ha10 (Nat.beq_eq.mpr h)
          split at hh
          · next ha11 =>
            rw [Nat.beq_eq] at ha11; subst ha11
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2]
            simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushR0, decR_bumpR] using
              stepPlus_stepStar (rule_C_zero_one (decL L3) (decR R))
          · next ha11 =>
            have hne1 : a1 ≠ 1 := fun h => ha11 (Nat.beq_eq.mpr h)
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2, show a1 = (a1 - 2) + 2 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushR0, decR_pushRd] using
              stepPlus_stepStar (rule_C_zero_add_two (a1 - 2) (decL L3) (decR R))
    · next ha0 =>
      have hane0 : a ≠ 0 := fun h => ha0 (Nat.beq_eq.mpr h)
      split at hh
      · next ha1 =>
        rw [Nat.beq_eq] at ha1; subst ha1
        cases hp2 : popL1 L1 with
        | none =>
          rw [hp2] at hh
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL1, decL_popL1_none L1 hp2]
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRd] using
            stepPlus_stepStar (rule_C_one_nil (decR R))
        | some p2 =>
          rcases p2 with ⟨a1, L3⟩
          rw [hp2] at hh
          have hL2 := decL_popL1_some L1 a1 L3 hp2
          dsimp only at hh; split at hh
          · next ha10 =>
            rw [Nat.beq_eq] at ha10; subst ha10
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2]
            simpa [evalRle, evalStackCfg1, decLState, decR_pushRd] using
              stepPlus_stepStar (rule_C_one_zero (decL L3) (decR R))
          · next ha10 =>
            have hne0 : a1 ≠ 0 := fun h => ha10 (Nat.beq_eq.mpr h)
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2, show a1 = (a1 - 1) + 1 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushRd] using
              stepPlus_stepStar (rule_C_one_succ (a1 - 1) (decL L3) (decR R))
      · next ha1 =>
        have hane1 : a ≠ 1 := fun h => ha1 (Nat.beq_eq.mpr h)
        rw [hL1, show a = (a - 2) + 2 by omega]
        obtain ⟨cfg', hstep, hnone⟩ := rule_C_add_two_halt (a - 2) (decL L1) (decR R)
        exact ⟨cfg', stepPlus_stepStar hstep, hnone⟩

def stepRawC (items R : List Item) : RleFullState :=
  match items with
  | .z cz :: .k r m :: L2 =>
    if Nat.beq cz 1 then ⟨.C, .raw (pushL0 1 L2), pushRk2 r m R, false⟩
    else stepRawCAtomic items R
  | .z cz :: .d v1 :: L2 =>
    if Nat.ble 4 cz && Nat.beq v1 1 then
      ⟨.C, .raw (pushL0 1 L2), pushRk2 (cz - 3) 1 R, false⟩
    else stepRawCAtomic items R
  | [.z cz] =>
    if Nat.ble 4 cz then ⟨.DR0, .raw [], pushRk2 (cz - 4) 1 R, false⟩
    else stepRawCAtomic items R
  | _ => stepRawCAtomic items R

lemma stepRawC_halts (items R : List Item) (hh : StateHalts (stepRawC items R)) :
    CanHalt (cfg_C (decL items) (decR R)) := by
  unfold stepRawC at hh
  rcases items with _ | ⟨hd1, rest1⟩
  · exact stepRawCAtomic_halts [] R hh
  · cases hd1 with
    | z cz =>
      rcases rest1 with _ | ⟨hd2, L2⟩
      · dsimp only at hh; split at hh
        · next h4 =>
          have hge4 : 4 ≤ cz := Nat.ble_eq.mp h4
          refine stateHalts_of_stepStar rfl ?_ hh
          have heq : decL [.z cz] = rep0 ((cz - 4) + 4) := by
            rw [decL, decL, List.append_nil, show cz - 4 + 4 = cz by omega]
          rw [heq]
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRk2,
            HPow.hPow, list_nat_repeat, List.append_eq] using
            rule_C_bot_four (cz - 4) (decR R)
        · exact stepRawCAtomic_halts [.z cz] R hh
      · cases hd2 with
        | k r m =>
          dsimp only at hh; split at hh
          · next hcz =>
            rw [Nat.beq_eq] at hcz; subst hcz
            refine stateHalts_of_stepStar rfl ?_ hh
            simpa [evalRle, evalStackCfg1, decLState, decL, decL_pushL0, decR_pushRk2] using
              rule_C_blkL_pow m r (decL L2) (decR R)
          · exact stepRawCAtomic_halts _ R hh
        | d v1 =>
          dsimp only at hh; split at hh
          · next hb =>
            simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hb
            rcases hb with ⟨hge4, rfl⟩
            refine stateHalts_of_stepStar rfl ?_ hh
            have heq : decL (.z cz :: .d 1 :: L2) = rep0 ((cz - 3) + 3) ++ 1 :: decL L2 := by
              rw [decL, decL, show cz - 3 + 3 = cz by omega]
            rw [heq]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR_pushRk2,
              HPow.hPow, list_nat_repeat, List.append_eq] using
              rule_C_r_add_three (cz - 3) (decL L2) (decR R)
          · exact stepRawCAtomic_halts _ R hh
        | z _ => exact stepRawCAtomic_halts _ R hh
    | d _ => exact stepRawCAtomic_halts _ R hh
    | k _ _ => exact stepRawCAtomic_halts _ R hh

-- 5.5 Clean B
def stepCleanBPop (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match popR1 R with
  | none => ⟨.B, .raw (unpackClean c0 segs bot), R, false⟩
  | some (d, R1) =>
    if Nat.beq d 0 then ⟨.B, .clean (c0 + 1) segs bot, R1, false⟩
    else ⟨.BR, .clean c0 segs bot, pushR0 1 (pushRd (d - 1) R1), false⟩

lemma stepCleanBPop_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts (stepCleanBPop c0 segs bot R)) :
    CanHalt (cfg_B (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanBPop at hh
  cases hp : popR1 R with
  | none =>
    rw [hp] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [hp] at hh
    have hR := decR_popR1_some R d R1 hp
    dsimp only at hh; split at hh
    · next hd0 =>
      rw [Nat.beq_eq] at hd0; subst hd0
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hR]
      have heq : 0 :: decLState (.clean c0 segs bot) = decLState (.clean (c0 + 1) segs bot) := by
        norm_all
      simpa [evalRle, evalStackCfg1, ← heq] using
        stepPlus_stepStar (rule_B_zero (decLState (.clean c0 segs bot)) (decR R1))
    · next hd0 =>
      have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hR, show d = (d - 1) + 1 by omega]
      simpa [evalRle, evalStackCfg1, decR_pushR0, decR_pushRd] using
        stepPlus_stepStar (rule_B_succ (d - 1) (decLState (.clean c0 segs bot)) (decR R1))

def stepCleanB (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then
      ⟨.B, .clean 1 (pushSeg 0 (bot - 1) (pushSeg (c0 - 1) 1 segs)) 0, [], false⟩
    else ⟨.B, .raw (unpackClean c0 segs bot), [], false⟩
  | .z cz :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.ble 1 bot && Nat.beq cz 1 then
      let q := minNat cnt bot
      if Nat.ble 1 q then
        let Rnew := if Nat.beq cnt q then .z 1 :: Rrem else .z 1 :: .k r (cnt - q) :: Rrem
        ⟨.B, .clean 0 (pushSeg (r + 3) q segs) (bot - q), Rnew, false⟩
      else ⟨.B, .clean (c0 + cz) segs bot, .k r cnt :: Rrem, false⟩
    else ⟨.B, .clean (c0 + cz) segs bot, .k r cnt :: Rrem, false⟩
  | .z cz :: R1 =>
    ⟨.B, .clean (c0 + cz) segs bot, R1, false⟩
  | .d v1 :: .d v2 :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.beq v1 1 && Nat.beq v2 1 then
      let q := minNat cnt (bot / (r + 1))
      if Nat.ble 1 q then
        let Rnew := if Nat.beq cnt q then .d 1 :: .d 1 :: Rrem else .d 1 :: .d 1 :: .k r (cnt - q) :: Rrem
        ⟨.B, .clean 0 (pushSeg (4 * r + 3) q segs) (bot - q * (r + 1)), Rnew, false⟩
      else ⟨.BR, .clean c0 segs bot, pushR0 1 (pushRd 0 (.d v2 :: .k r cnt :: Rrem)), false⟩
    else stepCleanBPop c0 segs bot (.d v1 :: .d v2 :: .k r cnt :: Rrem)
  | _ => stepCleanBPop c0 segs bot R

lemma stepCleanB_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts (stepCleanB c0 segs bot R)) :
    CanHalt (cfg_B (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanB at hh
  rcases R with _ | ⟨hd1, R1⟩
  · dsimp only at hh; split at hh
    · next hb =>
      simp only [Bool.and_eq_true, Nat.ble_eq] at hb
      rcases hb with ⟨hc0, hbot⟩
      refine stateHalts_of_stepStar rfl ?_ hh
      have h1 := clean_RNIL_one .B (Or.inl rfl) (c0 - 1) segs (bot - 1)
      have h2 := clean_RNIL_zero_pow (bot - 1) (pushSeg (c0 - 1) 1 segs) 0
      rw [show c0 - 1 + 1 = c0 by omega, show bot - 1 + 1 = bot by omega] at h1
      rw [show 0 + (bot - 1) = bot - 1 by omega] at h2
      exact stepStar_trans h1 h2
    · refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  · cases hd1 with
    | z cz =>
      have h_zonly : ∀ (Rtail : List Item)
          (hhz : StateHalts ⟨.B, .clean (c0 + cz) segs bot, Rtail, false⟩),
          CanHalt (cfg_B (decLState (.clean c0 segs bot)) (decR (.z cz :: Rtail))) := by
        intro Rtail hhz
        refine stateHalts_of_stepStar rfl ?_ hhz
        have hstep := rule_B_zeros_all (decLState (.clean c0 segs bot)) (decR Rtail) cz
        have heq : rep0 cz ++ decLState (.clean c0 segs bot) =
            decLState (.clean (c0 + cz) segs bot) := by
          rw [Nat.add_comm c0 cz]; norm_all
        rw [heq] at hstep
        exact hstep
      rcases R1 with _ | ⟨hd2, Rrem⟩
      · exact h_zonly [] hh
      · cases hd2 with
        | k r cnt =>
          dsimp only at hh; split at hh
          · next hb =>
            simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
            rcases hb with ⟨⟨rfl, hbot⟩, rfl⟩
            split at hh
            · next hq1 =>
              set q := minNat cnt bot
              have hqcnt : q ≤ cnt := minNat_le_left cnt bot
              have hqbot : q ≤ bot := minNat_le_right cnt bot
              refine stateHalts_of_stepStar rfl ?_ hh
              have hstep := clean_P1_pow q r segs (bot - q) ((blkR r) ^ (cnt - q) ++ decR Rrem)
              rw [show bot - q + q = bot by omega] at hstep
              have heqR1 : 0 :: ((blkR r) ^ q ++ ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                  decR (.z 1 :: .k r cnt :: Rrem) := by
                rw [← List.append_assoc, ← list_pow_add, show q + (cnt - q) = cnt by omega]
                norm_all
              have heqR2 : (0 :: ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                  decR (if Nat.beq cnt q then .z 1 :: Rrem else .z 1 :: .k r (cnt - q) :: Rrem) := by
                split
                · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; norm_all
                · norm_all
              rw [heqR1, heqR2] at hstep
              exact hstep
            · exact h_zonly _ hh
          · exact h_zonly _ hh
        | _ => exact h_zonly _ hh
    | d v1 =>
      rcases R1 with _ | ⟨hd2, _ | ⟨hd3, Rrem⟩⟩
      · exact stepCleanBPop_halts c0 segs bot _ hh
      · cases hd2 <;> exact stepCleanBPop_halts c0 segs bot _ hh
      · cases hd2 with
        | d v2 =>
          cases hd3 with
          | k r cnt =>
            dsimp only at hh; split at hh
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq] at hb
              rcases hb with ⟨⟨rfl, rfl⟩, rfl⟩
              split at hh
              · next hq1 =>
                set q := minNat cnt (bot / (r + 1))
                have hqcnt : q ≤ cnt := minNat_le_left cnt _
                have hqdiv : q ≤ bot / (r + 1) := minNat_le_right cnt _
                have hqmul : q * (r + 1) ≤ bot :=
                  Nat.le_trans (Nat.mul_le_mul_right (r + 1) hqdiv) (Nat.div_mul_le_self bot (r + 1))
                refine stateHalts_of_stepStar rfl ?_ hh
                have hstep := clean_P2_pow q r segs (bot - q * (r + 1)) ((blkR r) ^ (cnt - q) ++ decR Rrem)
                rw [show bot - q * (r + 1) + q * (r + 1) = bot by omega] at hstep
                have heqR1 : 1 :: 1 :: ((blkR r) ^ q ++ ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                    decR (.d 1 :: .d 1 :: .k r cnt :: Rrem) := by
                  rw [← List.append_assoc, ← list_pow_add, show q + (cnt - q) = cnt by omega]
                  norm_all
                have heqR2 : (1 :: 1 :: ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                    decR (if Nat.beq cnt q then .d 1 :: .d 1 :: Rrem else .d 1 :: .d 1 :: .k r (cnt - q) :: Rrem) := by
                  split
                  · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; norm_all
                  · norm_all
                rw [heqR1, heqR2] at hstep
                exact hstep
              · refine stateHalts_of_stepStar rfl ?_ hh
                simpa [evalRle, evalStackCfg1, decR_pushR0, decR_pushRd, decR] using
                  stepPlus_stepStar (rule_B_succ 0 (decLState (.clean 0 segs bot)) (decR (.d 1 :: .k r cnt :: Rrem)))
            · exact stepCleanBPop_halts c0 segs bot _ hh
          | _ => exact stepCleanBPop_halts c0 segs bot _ hh
        | _ => exact stepCleanBPop_halts c0 segs bot _ hh
    | k _ _ => exact stepCleanBPop_halts c0 segs bot _ hh

-- 5.6 Clean BR
def stepCleanBR (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then
      ⟨.B, .clean 1 (pushSeg 0 (bot - 1) (pushSeg (c0 - 1) 1 segs)) 0, [], false⟩
    else ⟨.BR, .raw (unpackClean c0 segs bot), [], false⟩
  | .z cz :: R1 =>
    ⟨.BR, .clean (c0 + cz) segs bot, R1, false⟩
  | .k r m :: R1 =>
    if Nat.ble 1 m && Nat.ble 1 c0 && Nat.ble 3 (r + c0) then
      ⟨.BR, .clean 3 (pushSeg r (m - 1) (pushSeg (r + c0 - 3) 1 segs)) bot, R1, false⟩
    else ⟨.BR, .raw (unpackClean c0 segs bot), .k r m :: R1, false⟩
  | .d v :: R1 =>
    match popR1 (.d v :: R1) with
    | none => ⟨.BR, .raw (unpackClean c0 segs bot), .d v :: R1, false⟩
    | some (d, R2) =>
      if Nat.beq d 0 then ⟨.BR, .clean (c0 + 1) segs bot, R2, false⟩
      else if Nat.beq d 1 then ⟨.DR0, .clean c0 segs bot, bumpR R2, false⟩
      else if Nat.ble 3 c0 then
        ⟨.B, .clean 0 (pushSeg (c0 - 3) 1 segs) bot, pushRd (d - 2) R2, false⟩
      else ⟨.BR, .raw (unpackClean c0 segs bot), .d v :: R1, false⟩

lemma stepCleanBR_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts (stepCleanBR c0 segs bot R)) :
    CanHalt (cfg_BR (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanBR at hh
  rcases R with _ | ⟨hd1, R1⟩
  · dsimp only at hh; split at hh
    · next hb =>
      simp only [Bool.and_eq_true, Nat.ble_eq] at hb
      rcases hb with ⟨hc0, hbot⟩
      refine stateHalts_of_stepStar rfl ?_ hh
      have h1 := clean_RNIL_one .BR (Or.inr rfl) (c0 - 1) segs (bot - 1)
      have h2 := clean_RNIL_zero_pow (bot - 1) (pushSeg (c0 - 1) 1 segs) 0
      rw [show c0 - 1 + 1 = c0 by omega, show bot - 1 + 1 = bot by omega] at h1
      rw [show 0 + (bot - 1) = bot - 1 by omega] at h2
      exact stepStar_trans h1 h2
    · refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  · cases hd1 with
    | z cz =>
      refine stateHalts_of_stepStar rfl ?_ hh
      have hstep := rule_BR_zeros_all (decLState (.clean c0 segs bot)) (decR R1) cz
      have heq : rep0 cz ++ decLState (.clean c0 segs bot) =
          decLState (.clean (c0 + cz) segs bot) := by
        rw [Nat.add_comm c0 cz]; norm_all
      rw [heq] at hstep
      exact hstep
    | k r m =>
      dsimp only at hh; split at hh
      · next hb =>
        simp only [Bool.and_eq_true, Nat.ble_eq] at hb
        rcases hb with ⟨⟨hm, hc0⟩, hrc⟩
        refine stateHalts_of_stepStar rfl ?_ hh
        have heqL0 : decLState (.clean c0 segs bot) =
            0 :: (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) := by
          conv_lhs => rw [decLState, show c0 = (c0 - 1) + 1 by omega]
          norm_all
        have hstep := rule_BR_blkR_succ (m - 1) r (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) (decR R1)
        have heqR : decR (.k r m :: R1) = (blkR r) ^ ((m - 1) + 1) ++ decR R1 := by
          rw [decR, show m - 1 + 1 = m by omega]
        have heqL1 : rep0 3 ++ 1 :: ((blkL r) ^ (m - 1) ++ (rep0 r ++ (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))))) =
            decLState (.clean 3 (pushSeg r (m - 1) (pushSeg (r + c0 - 3) 1 segs)) bot) := by
          have hmerge : rep0 r ++ (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
              rep0 ((r + c0 - 3) + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)) := by
            rw [← List.append_assoc, ← rep0_add_split, show r + (c0 - 1) = (r + c0 - 3) + 2 by omega]
          rw [hmerge]
          norm_all
        dsimp only [evalRle, evalStackCfg1]
        rw [heqL0, heqR, ← heqL1]
        exact hstep
      · refine stateHalts_of_stepStar rfl ?_ hh
        simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
    | d v =>
      dsimp only at hh
      cases hp : popR1 (.d v :: R1) with
      | none => cases hp
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR]
          have heq : 0 :: decLState (.clean c0 segs bot) = decLState (.clean (c0 + 1) segs bot) := by
            norm_all
          simpa [evalRle, evalStackCfg1, ← heq] using
            stepPlus_stepStar (rule_BR_zero (decLState (.clean c0 segs bot)) (decR R2))
        · next hd0 =>
          have hdne0 : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          split at hh
          · next hd1 =>
            rw [Nat.beq_eq] at hd1; subst hd1
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hR]
            simpa [evalRle, evalStackCfg1, decR_bumpR] using
              stepPlus_stepStar (rule_BR_one (decLState (.clean c0 segs bot)) (decR R2))
          · next hd1 =>
            have hdne1 : d ≠ 1 := fun h => hd1 (Nat.beq_eq.mpr h)
            split at hh
            · next hc3 =>
              have hcge : 3 ≤ c0 := Nat.ble_eq.mp hc3
              refine stateHalts_of_stepStar rfl ?_ hh
              rw [hR, show d = (d - 2) + 2 by omega]
              have hstep := stepPlus_stepStar (rule_BR_add_two (d - 2) (decLState (.clean c0 segs bot)) (decR R2))
              have heq : bumpHead (decLState (.clean c0 segs bot)) =
                  decLState (.clean 0 (pushSeg (c0 - 3) 1 segs) bot) := by
                conv_lhs => rw [decLState, show c0 = (c0 - 3) + 3 by omega]
                norm_all
              rw [heq] at hstep
              simpa [evalRle, evalStackCfg1, decR_pushRd] using hstep
            · refine stateHalts_of_stepStar rfl ?_ hh
              simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

-- 5.7 Clean DR0
def stepCleanDR0 (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  if Nat.ble 1 bot then
    match R with
    | .d v1 :: .z rz :: R2 =>
      if Nat.beq v1 1 then
        let q := minNat rz bot
        if Nat.ble 1 q then
          let Rnew := if Nat.beq rz q then .d 1 :: R2 else .d 1 :: .z (rz - q) :: R2
          ⟨.DR0, .clean (c0 + 4 * q) segs (bot - q), Rnew, false⟩
        else ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
      else ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
    | _ => ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
  else ⟨.DR0, .raw (unpackClean c0 segs bot), R, false⟩

lemma stepCleanDR0_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts (stepCleanDR0 c0 segs bot R)) :
    CanHalt (cfg_DR0 (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanDR0 at hh
  split at hh
  · next hbot =>
    have hbge : 1 ≤ bot := Nat.ble_eq.mp hbot
    have h_one : ∀ (hh1 : StateHalts ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩),
        CanHalt (cfg_DR0 (decLState (.clean c0 segs bot)) (decR R)) := by
      intro hh1
      refine stateHalts_of_stepStar rfl ?_ hh1
      have hstep := clean_DR0_one c0 segs (bot - 1) (decR R)
      rw [show bot - 1 + 1 = bot by omega] at hstep
      exact hstep
    rcases R with _ | ⟨r1, _ | ⟨r2, R2⟩⟩
    · exact h_one hh
    · cases r1 <;> exact h_one hh
    · cases r1 with
      | d v1 =>
        cases r2 with
        | z rz =>
          dsimp only at hh; split at hh
          · next hv1 =>
            rw [Nat.beq_eq] at hv1; subst hv1
            split at hh
            · next hq1 =>
              set q := minNat rz bot
              have hqrz : q ≤ rz := minNat_le_left rz bot
              have hqbot : q ≤ bot := minNat_le_right rz bot
              refine stateHalts_of_stepStar rfl ?_ hh
              have hstep := clean_DR0_zeros q c0 segs (bot - q) (rep0 (rz - q) ++ decR R2)
              rw [show bot - q + q = bot by omega] at hstep
              have heqR1 : 1 :: (rep0 q ++ (rep0 (rz - q) ++ decR R2)) =
                  decR (.d 1 :: .z rz :: R2) := by
                rw [← List.append_assoc, ← rep0_add_split, show q + (rz - q) = rz by omega]
                norm_all
              have heqR2 : (1 :: (rep0 (rz - q) ++ decR R2)) =
                  decR (if Nat.beq rz q then .d 1 :: R2 else .d 1 :: .z (rz - q) :: R2) := by
                split
                · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; norm_all
                · norm_all
              rw [heqR1, heqR2] at hstep
              exact hstep
            · exact h_one hh
          · exact h_one hh
        | _ => exact h_one hh
      | _ => exact h_one hh
  · refine stateHalts_of_stepStar rfl ?_ hh
    simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

-- 5.8 Top-Level Dispatch `rleStep`
def tryPack (m : StackMode) (items R : List Item) : Option LState :=
  if modeCanPack m items R then
    match packHead 0 items with
    | some (LState.clean c0 segs bot) =>
      if Nat.ble 1 bot then some (LState.clean c0 segs bot) else none
    | _ => none
  else none

lemma tryPack_spec (m : StackMode) (items R : List Item) (ls' : LState)
    (h : tryPack m items R = some ls') : decL items = decLState ls' := by
  unfold tryPack at h
  split at h
  · cases hph : packHead 0 items with
    | none => rw [hph] at h; cases h
    | some l0 =>
      rw [hph] at h
      cases l0 with
      | raw _ => cases h
      | clean c0 segs bot =>
        dsimp only at h; split at h
        · cases h
          have hspec := packHead_spec items 0 (LState.clean c0 segs bot) hph
          simpa using hspec
        · cases h
  · cases h

def rleStep (s : RleFullState) : RleFullState :=
  match s.ls with
  | .raw items =>
    match tryPack s.mode items s.R with
    | some ls' => ⟨s.mode, ls', s.R, false⟩
    | none =>
      match s.mode with
      | .B => stepRawB items s.R
      | .BR => stepRawBR items s.R
      | .DR0 => stepRawDR0 items s.R
      | .C => stepRawC items s.R
  | .clean c0 segs bot =>
    match s.mode with
    | .B => stepCleanB c0 segs bot s.R
    | .BR => stepCleanBR c0 segs bot s.R
    | .DR0 => stepCleanDR0 c0 segs bot s.R
    | .C => ⟨.C, .raw (unpackClean c0 segs bot), s.R, false⟩

theorem rleStep_halts (s : RleFullState) (hh : StateHalts (rleStep s)) :
    CanHalt (evalRle s) := by
  rcases s with ⟨mode, ls, R, halted⟩
  unfold rleStep at hh
  dsimp only at hh
  cases ls with
  | raw items =>
    dsimp only at hh
    cases hpk : tryPack mode items R with
    | some ls' =>
      rw [hpk] at hh
      refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, decLState, tryPack_spec mode items R ls' hpk]
    | none =>
      rw [hpk] at hh
      cases mode with
      | B => exact stepRawB_halts items R hh
      | BR => exact stepRawBR_halts items R hh
      | DR0 => exact stepRawDR0_halts items R hh
      | C => exact stepRawC_halts items R hh
  | clean c0 segs bot =>
    dsimp only at hh
    cases mode with
    | B => exact stepCleanB_halts c0 segs bot R hh
    | BR => exact stepCleanBR_halts c0 segs bot R hh
    | DR0 => exact stepCleanDR0_halts c0 segs bot R hh
    | C =>
      refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

-- ============================================================================
-- Section 6: Strict Evaluation + 19 Checkpointed 500-Step Chunks (`9,500 > 9,101`)
-- ============================================================================

def strictNat {α : Type*} (n : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn (Nat.add n 1) (f 0) (fun m => f m)

@[simp] lemma strictNat_eq {α : Type*} (n : ℕ) (f : ℕ → α) :
    strictNat n f = f n := rfl

def strictItem {α : Type*} (it : Item) (f : Item → α) : α :=
  match it with
  | .z c => strictNat c (fun c' => f (.z c'))
  | .d v => strictNat v (fun v' => f (.d v'))
  | .k r c => strictNat r (fun r' => strictNat c (fun c' => f (.k r' c')))

@[simp] lemma strictItem_eq {α : Type*} (it : Item) (f : Item → α) :
    strictItem it f = f it := by
  cases it <;> simp [strictItem]

def strictItems {α : Type*} : List Item → (List Item → α) → α
  | [], f => f []
  | x :: xs, f => strictItem x (fun x' => strictItems xs (fun xs' => f (x' :: xs')))

@[simp] lemma strictItems_eq {α : Type*} :
    ∀ (xs : List Item) (f : List Item → α), strictItems xs f = f xs
  | [], _ => rfl
  | x :: xs, f => by simp [strictItems, strictItems_eq xs]

def strictSegs {α : Type*} : List (ℕ × ℕ) → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | (r, c) :: xs, f =>
    strictNat r (fun r' => strictNat c (fun c' => strictSegs xs (fun xs' => f ((r', c') :: xs'))))

@[simp] lemma strictSegs_eq {α : Type*} :
    ∀ (xs : List (ℕ × ℕ)) (f : List (ℕ × ℕ) → α), strictSegs xs f = f xs
  | [], _ => rfl
  | (r, c) :: xs, f => by simp [strictSegs, strictSegs_eq xs]

def strictLState {α : Type*} (ls : LState) (f : LState → α) : α :=
  match ls with
  | .raw items => strictItems items (fun items' => f (.raw items'))
  | .clean c0 segs bot =>
    strictNat c0 (fun c0' =>
      strictSegs segs (fun segs' =>
        strictNat bot (fun bot' => f (.clean c0' segs' bot'))))

@[simp] lemma strictLState_eq {α : Type*} (ls : LState) (f : LState → α) :
    strictLState ls f = f ls := by
  cases ls <;> simp [strictLState]

def strictMode {α : Type*} (m : StackMode) (f : StackMode → α) : α :=
  match m with
  | .B => f .B
  | .BR => f .BR
  | .DR0 => f .DR0
  | .C => f .C

@[simp] lemma strictMode_eq {α : Type*} (m : StackMode) (f : StackMode → α) :
    strictMode m f = f m := by
  cases m <;> rfl

def strictState {α : Type*} (s : RleFullState) (f : RleFullState → α) : α :=
  match s with
  | ⟨m, ls, R, h⟩ =>
    strictMode m (fun m' =>
      strictLState ls (fun ls' =>
        strictItems R (fun R' =>
          Bool.casesOn h (f ⟨m', ls', R', false⟩) (f ⟨m', ls', R', true⟩))))

@[simp] lemma strictState_eq {α : Type*} (s : RleFullState) (f : RleFullState → α) :
    strictState s f = f s := by
  rcases s with ⟨m, ls, R, h⟩
  cases h <;> simp [strictState]

def strictItems4 {α : Type*} : List Item → (List Item → α) → α
  | [], f => f []
  | [x0], f => strictItem x0 (fun y0 => f [y0])
  | [x0, x1], f => strictItem x0 (fun y0 => strictItem x1 (fun y1 => f [y0, y1]))
  | [x0, x1, x2], f =>
    strictItem x0 (fun y0 => strictItem x1 (fun y1 => strictItem x2 (fun y2 => f [y0, y1, y2])))
  | x0 :: x1 :: x2 :: x3 :: xs, f =>
    strictItem x0 (fun y0 => strictItem x1 (fun y1 => strictItem x2 (fun y2 =>
      strictItem x3 (fun y3 => f (y0 :: y1 :: y2 :: y3 :: xs)))))

@[simp] lemma strictItems4_eq {α : Type*} (xs : List Item) (f : List Item → α) :
    strictItems4 xs f = f xs := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;> simp [strictItems4]

def strictSegs3 {α : Type*} : List (ℕ × ℕ) → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | [(r0, c0)], f => strictNat r0 (fun r0' => strictNat c0 (fun c0' => f [(r0', c0')]))
  | [(r0, c0), (r1, c1)], f =>
    strictNat r0 (fun r0' => strictNat c0 (fun c0' =>
      strictNat r1 (fun r1' => strictNat c1 (fun c1' => f [(r0', c0'), (r1', c1')]))))
  | (r0, c0) :: (r1, c1) :: (r2, c2) :: xs, f =>
    strictNat r0 (fun r0' => strictNat c0 (fun c0' =>
      strictNat r1 (fun r1' => strictNat c1 (fun c1' =>
        strictNat r2 (fun r2' => strictNat c2 (fun c2' =>
          f ((r0', c0') :: (r1', c1') :: (r2', c2') :: xs)))))))

@[simp] lemma strictSegs3_eq {α : Type*} (xs : List (ℕ × ℕ)) (f : List (ℕ × ℕ) → α) :
    strictSegs3 xs f = f xs := by
  rcases xs with _ | ⟨⟨r0, c0⟩, _ | ⟨⟨r1, c1⟩, _ | ⟨⟨r2, c2⟩, xs⟩⟩⟩ <;> simp [strictSegs3]

def strictStateFast {α : Type*} (s : RleFullState) (f : RleFullState → α) : α :=
  match s with
  | ⟨m, .raw items, R, h⟩ =>
    strictMode m (fun m' =>
      strictItems4 items (fun items' =>
        strictItems4 R (fun R' =>
          Bool.casesOn h (f ⟨m', .raw items', R', false⟩) (f ⟨m', .raw items', R', true⟩))))
  | ⟨m, .clean c0 segs bot, R, h⟩ =>
    strictMode m (fun m' =>
      strictNat c0 (fun c0' =>
        strictSegs3 segs (fun segs' =>
          strictNat bot (fun bot' =>
            strictItems4 R (fun R' =>
              Bool.casesOn h (f ⟨m', .clean c0' segs' bot', R', false⟩)
                             (f ⟨m', .clean c0' segs' bot', R', true⟩))))))

@[simp] lemma strictStateFast_eq {α : Type*} (s : RleFullState) (f : RleFullState → α) :
    strictStateFast s f = f s := by
  rcases s with ⟨m, (_ | ⟨c0, segs, bot⟩), R, h⟩ <;> cases h <;> simp [strictStateFast]

def runStepsInner (n : ℕ) (s : RleFullState) : RleFullState :=
  Nat.rec
    (fun s => s)
    (fun _ ih s =>
      match s with
      | ⟨m, ls, R, true⟩ => ⟨m, ls, R, true⟩
      | ⟨m, ls, R, false⟩ => strictStateFast (rleStep ⟨m, ls, R, false⟩) ih)
    n s

lemma runStepsInner_succ (n : ℕ) (s : RleFullState) :
    runStepsInner (n + 1) s =
      match s with
      | ⟨m, ls, R, true⟩ => ⟨m, ls, R, true⟩
      | ⟨m, ls, R, false⟩ => strictStateFast (rleStep ⟨m, ls, R, false⟩) (runStepsInner n) := rfl

lemma runStepsInner_halts : ∀ (n : ℕ) (s : RleFullState),
    StateHalts (runStepsInner n s) → StateHalts s
  | 0, _, h => h
  | n + 1, ⟨m, ls, R, true⟩, _ => Or.inl rfl
  | n + 1, ⟨m, ls, R, false⟩, h => by
    rw [runStepsInner_succ] at h
    dsimp only at h
    rw [strictStateFast_eq] at h
    exact Or.inr (rleStep_halts ⟨m, ls, R, false⟩ (runStepsInner_halts n (rleStep ⟨m, ls, R, false⟩) h))

def runBatches (b : ℕ) (s : RleFullState) : RleFullState :=
  Nat.rec
    (fun s => s)
    (fun _ ih s => strictState (runStepsInner 25 s) ih)
    b s

lemma runBatches_succ (b : ℕ) (s : RleFullState) :
    runBatches (b + 1) s = strictState (runStepsInner 25 s) (runBatches b) := rfl

lemma runBatches_halts : ∀ (b : ℕ) (s : RleFullState),
    StateHalts (runBatches b s) → StateHalts s
  | 0, _, h => h
  | b + 1, s, h => by
    rw [runBatches_succ, strictState_eq] at h
    exact runStepsInner_halts 25 s (runBatches_halts b (runStepsInner 25 s) h)

def runSteps (s : RleFullState) : RleFullState :=
  runBatches 20 s

lemma runSteps_halts (s : RleFullState) (h : StateHalts (runSteps s)) :
    StateHalts s :=
  runBatches_halts 20 s h

lemma chunk_back {s₁ s₂ : RleFullState} (heq : runSteps s₁ = s₂) (h : StateHalts s₂) :
    StateHalts s₁ := by
  rw [← heq] at h
  exact runSteps_halts s₁ h

def ckpt0 : RleFullState := ⟨.B, .raw [.z 1], [], false⟩
def ckpt1 : RleFullState := ⟨.BR, .clean 5 [(6, 1618), (7, 1), (9, 6526), (13, 1), (21, 812), (2, 1), (303, 258), (1839, 1), (1071, 5), (1327, 1), (1839, 1), (1583, 1), (4655, 1)] 17045, [.d 1, .k 0 34340, .d 2], false⟩
def ckpt2 : RleFullState := ⟨.BR, .clean 5230798 [] 11874397, [.d 1, .d 1, .z 1558014, .d 2, .d 1, .k 312075 6, .k 225803 1, .k 77835 222, .k 55943 1, .k 19455 28, .k 191 1, .k 1407 812, .k 895 1, .k 639 2872, .k 383 1, .k 27 1, .k 51 3653, .k 43 1, .k 39 1619, .k 27 34340, .k 19 1, .k 15 24417, .k 27 1, .k 3 473610, .z 3, .d 3, .d 1, .k 0 2212068, .d 2], false⟩
def ckpt3 : RleFullState := ⟨.DR0, .raw [.z 958707300], [.d 3, .d 1, .k 231226571 1, .k 79707339 5, .z 9365511, .d 1, .z 17585456, .d 2, .d 1, .k 19926834 27, .k 6342242 1, .k 4981698 188, .k 3580610 1, .k 1245378 28, .k 12482 1, .k 90306 812, .k 57538 1, .k 41154 2872, .k 24770 1, .k 1986 1, .k 3522 3653, .k 3010 1, .k 2754 1619, .k 1986 13, .z 1986, .d 2, .k 1983 34326, .k 1471 1, .k 1215 24417, .k 1983 1, .k 447 473610, .k 191 1, .k 63 2829536, .k 2 1, .k 6 3190216, .k 2 1, .k 0 323903799, .d 2], false⟩
def ckpt4 : RleFullState := ⟨.B, .clean 0 [(44130, 1619), (48226, 1), (56418, 3653), (31842, 1), (396386, 1), (658530, 2872), (920674, 1), (1444962, 812), (199778, 1), (19926114, 28), (57289826, 1), (79707234, 71), (237159362, 1), (318828978, 116), (405903794, 1), (1275317682, 27), (1125469490, 1), (2397571122, 1), (20405078305, 1)] 19, [.z 1, .k 31839 13, .k 158751 1, .k 126975 34325, .k 94207 1, .k 77823 24417, .k 126975 1, .k 28671 473610, .k 12287 1, .k 4095 2829536, .k 191 1, .k 447 3190216, .k 191 1, .k 63 323903800, .k 31 1, .k 15 4583538500, .k 7 1, .k 3 26276947360, .k 1 1, .k 0 160451158237, .d 2], false⟩
def ckpt5 : RleFullState := ⟨.B, .clean 0 [(10160322, 1), (2037954, 13), (2824386, 1619), (3086530, 1), (3610818, 3653), (2037954, 1), (25368770, 1), (42145986, 2872), (58923202, 1), (92477634, 812), (12785858, 1), (1275271362, 28), (3666548930, 1), (5101263042, 71), (15178199234, 1), (20405054658, 116), (25977842882, 1), (81620331714, 22), (248318268209, 1), (300302521103, 1)] 3842700283260, [.z 1, .k 8126655 6, .k 2031599 1, .k 2031615 34318, .k 1507327 1, .k 1245183 24417, .k 2031615 1, .k 458751 473610, .k 196607 1, .k 65535 2829536, .k 3071 1, .k 7167 3190216, .k 3071 1, .k 1023 323903800, .k 511 1, .k 255 4583538500, .k 127 1, .k 63 26276947360, .k 31 1, .k 15 56657308304, .z 3, .d 1, .z 2, .d 2, .d 1, .k 3 133852318911, .z 3, .d 3, .d 1, .k 0 56344583818, .d 2], false⟩
def ckpt6 : RleFullState := ⟨.C, .raw [.z 1, .k 326481326883 14, .k 1493434491 1, .k 5199806278283 1, .k 5223701229771 2, .k 5223701229767 1, .k 63 1, .k 83579219676159 1, .z 2], [.k 103911371555 1, .k 81620218659 116, .k 60712796963 1, .k 20405052195 71, .k 14666195747 1, .k 5101085475 28, .k 51143459 1, .k 369910563 812, .k 235692835 1, .k 168583971 2872, .k 101475107 1, .k 8151843 1, .k 14443299 3653, .k 12346147 1, .k 11297571 1619, .k 8151843 13, .k 40641315 1, .k 32506659 6, .k 8126435 1, .k 8126499 34318, .k 6029347 1, .k 4980771 24417, .k 8126499 1, .k 1835043 473610, .k 786467 1, .k 262179 2829536, .k 12323 1, .k 28707 3190216, .k 12323 1, .k 4131 323903800, .k 2083 1, .k 1059 4583538500, .k 547 1, .k 291 26276947360, .k 163 1, .k 99 56657308304, .k 47 1, .k 39 190196902731, .k 31 1, .k 27 91416876092, .k 15 3607090573272, .k 7 1, .k 3 1247148618371, .k 1 1, .k 0 8777991210831, .d 2], false⟩
def ckpt7 : RleFullState := ⟨.C, .raw [.z 1, .k 650120007 1, .k 130024023 9, .k 130022999 1, .k 520106583 6, .k 650261079 1, .k 130429527 13, .k 180761175 1619, .k 197538391 1, .k 231092823 3653, .k 130429527 1, .k 1623601751 1, .k 2697343575 2872, .k 3771085399 1, .k 5918569047 812, .k 818295383 1, .k 81617367639 28, .k 234659131991 1, .k 326480835159 71, .k 971404751447 1, .k 1305923498583 116, .k 1662581944919 1, .k 5223701230167 13, .k 4865276967659 1, .k 5734788200127 1, .k 382319230143 1, .k 1331150407240895 1, .z 2], [.k 520095999 34307, .k 385878271 1, .k 318769407 24417, .k 520095999 1, .k 117442815 473610, .k 50333951 1, .k 16779519 2829536, .k 788735 1, .k 1837311 3190216, .k 788735 1, .k 264447 323903800, .k 133375 1, .k 67839 4583538500, .k 35071 1, .k 18687 26276947360, .k 10495 1, .k 6399 49220528784, .k 5599 1, .k 52 1, .k 402 7436779519, .k 194 1, .k 162 190196902731, .k 130 1, .k 114 91416876092, .k 66 3607090573272, .k 34 1, .k 18 1247148618371, .k 10 1, .k 6 8777991210832, .k 4 1, .k 3 109913193308653, .k 6 1, .k 0 143908026682961, .d 2], false⟩
def ckpt8 : RleFullState := ⟨.BR, .raw [.z 3], [.d 1, .k 334316878730799 1, .k 235168853200655 1, .k 6196751595636 1, .k 20894804920677 11, .k 6650327779685 1, .k 5223693994341 116, .k 3885619005797 1, .k 1305923340645 71, .k 938636527973 1, .k 326469470565 28, .k 3273181541 1, .k 23674276197 812, .k 15084341605 1, .k 10789374309 2872, .k 6494407013 1, .k 521718117 1, .k 924371301 3653, .k 790153573 1, .k 723044709 1619, .k 521718117 13, .k 2601044325 1, .k 2080426341 6, .k 520092005 1, .k 520096101 9, .k 2600480037 1, .k 2080384005 34307, .k 1543513093 1, .k 1275077637 24417, .k 2080384005 1, .k 469771269 473610, .k 201335813 1, .k 67118085 2829536, .k 3154949 1, .k 7349253 3190216, .k 3154949 1, .k 1057797 323903800, .k 533509 1, .k 271365 4583538500, .k 140293 1, .k 74757 26276947360, .k 41989 1, .k 25605 49220528784, .k 22405 1, .k 217 1, .k 1617 7436779519, .k 785 1, .k 657 190196902731, .k 529 1, .k 465 91416876092, .k 273 3607090573272, .k 145 1, .k 81 1247148618371, .k 49 1, .k 33 8777991210832, .k 25 1, .k 21 41052276700161, .k 81 1, .k 63 2256743270255, .z 47, .d 1, .z 3, .d 2, .d 1, .k 15 66604173338234, .k 27 1, .k 3 143908026682962, .k 1 1, .k 0 1428879399713869, .d 2], false⟩
def ckpt9 : RleFullState := ⟨.C, .raw [.z 1, .k 52 1, .k 84 1247148618371, .k 148 1, .k 276 3607090573272, .k 468 91416876092, .k 532 1, .k 660 190196902731, .k 788 1, .k 1620 7436779519, .k 220 1, .k 22408 1, .k 25608 49220528784, .k 41992 1, .k 74760 10196059880, .k 283148 1, .k 299037 16080887479, .k 561181 1, .k 1085469 4583538500, .k 2134045 1, .k 4231197 323903800, .k 12619805 1, .k 29397021 3190216, .k 12619805 1, .k 268472349 2829536, .k 805343261 1, .k 1879085085 473610, .k 8321536029 1, .k 5100310557 24417, .k 6174052381 1, .k 8321536029 34307, .k 10401920157 1, .k 2080384413 9, .k 2080368029 1, .k 8321705373 6, .k 10404177309 1, .k 2086872477 13, .k 2892178845 1619, .k 3160614301 1, .k 3697485213 3653, .k 2086872477 1, .k 25977628061 1, .k 43157497245 2872, .k 60337366429 1, .k 94697104797 812, .k 13092726173 1, .k 1305877882269 28, .k 3754546111901 1, .k 5223693362589 71, .k 15542476023197 1, .k 20894775977373 27, .k 58473431142467 1, .k 83579103909480 88, .k 106405244474984 1, .k 334316878730856 6, .k 331855219262470 1, .k 39386551494175 1, .k 5349070059693663 1, .z 2], [.k 36 8777991210832, .k 28 1, .k 24 41052276700161, .k 84 1, .k 66 68860916608490, .k 114 1, .k 18 65433277186752, .k 5 1, .k 3 78474749496209, .k 1 1, .k 0 3904219628751174, .d 2], false⟩
def ckpt10 : RleFullState := ⟨.C, .raw [.z 1, .k 20401242237 24417, .k 24696209533 1, .k 33286144125 34307, .k 41607680637 1, .k 8321537661 9, .k 8321472125 1, .k 33286821501 6, .k 41616709245 1, .k 8347489917 13, .k 11568715389 1619, .k 12642457213 1, .k 14789940861 3653, .k 8347489917 1, .k 103910512253 1, .k 172629988989 2872, .k 241349465725 1, .k 378788419197 812, .k 52370904701 1, .k 5223511529085 28, .k 15018184447613 1, .k 20894773450365 71, .k 62169904092797 1, .k 83579103909501 27, .k 233893724569877 1, .k 334316415637929 88, .k 425620977899945 1, .k 1337267514923433 4, .k 110188252487541 1, .k 19633268198974271 1, .z 2], [.k 33286144125 1, .k 7516340349 473610, .k 3221373053 1, .k 1073889405 2829536, .k 50479229 1, .k 117588093 3190216, .k 50479229 1, .k 16924797 323903800, .k 8536189 1, .k 4341885 1304636057, .k 1720010 1, .k 1085472 3278902442, .k 561184 1, .k 299040 16080887479, .k 283151 1, .k 74763 10196059880, .k 41995 1, .k 25611 49220528784, .k 22411 1, .k 223 1, .k 1623 7436779519, .k 791 1, .k 663 190196902731, .k 535 1, .k 471 91416876092, .k 279 3607090573272, .k 151 1, .k 87 1247148618371, .k 55 1, .k 39 8777991210832, .k 31 1, .k 27 41052276700161, .k 87 1, .k 69 68860916608490, .k 117 1, .k 21 65433277186752, .k 8 1, .k 6 78474749496209, .k 4 1, .k 3 9575881408811365, .k 6 1, .k 0 1295188808094044, .d 2], false⟩
def ckpt11 : RleFullState := ⟨.C, .raw [.z 1, .k 690519955965 2872, .k 965397862909 1, .k 1515153676797 812, .k 209483618813 1, .k 20894046116349 28, .k 60072737790461 1, .k 83579093801469 71, .k 248679616371197 1, .k 334316415638013 27, .k 935574898279517 1, .k 1337265662551725 88, .k 1702483911599789 1, .k 3966777089551516 1, .k 22116687522275599 1, .k 85585120955099823 1, .z 2], [.k 415642049021 1, .k 33389959677 1, .k 59159763453 3653, .k 50569828861 1, .k 46274861565 1619, .k 33389959677 13, .k 166466836989 1, .k 133147286013 6, .k 33285888509 1, .k 33286150653 9, .k 166430722557 1, .k 133144576509 34307, .k 98784838141 1, .k 81604968957 24417, .k 133144576509 1, .k 30065361405 473610, .k 12885492221 1, .k 4295557629 2829536, .k 201916925 1, .k 470352381 3190216, .k 201916925 1, .k 67699197 323903800, .k 34144765 1, .k 17367549 1019107586, .k 10522268 1, .k 4341888 285528470, .k 1720013 1, .k 1085475 3278902442, .k 561187 1, .k 299043 16080887479, .k 283154 1, .k 74766 10196059880, .k 41998 1, .k 25614 49220528784, .k 22414 1, .k 226 1, .k 1626 7436779519, .k 794 1, .k 666 190196902731, .k 538 1, .k 474 91416876092, .k 282 3607090573272, .k 154 1, .k 90 1247148618371, .k 58 1, .k 42 8777991210832, .k 34 1, .k 30 41052276700161, .k 90 1, .k 72 68860916608490, .k 120 1, .k 24 65433277186752, .k 11 1, .k 9 78474749496209, .k 7 1, .k 6 9575881408811365, .k 9 1, .k 3 17162295816727413, .k 6 1, .k 0 10257388459010042, .d 2], false⟩
def ckpt12 : RleFullState := ⟨.B, .clean 0 [(1283881819051443, 1), (321797900508418943, 1), (342340009613241855, 48), (985146577953219359, 1), (1369360038452967471, 3), (247409577377314847, 1), (17951207377210441983, 1)] 6420508988519869567, [.d 1, .d 1, .k 5349062650206906 31, .k 3742299593118074 1, .k 1337265662552058 27, .k 994718465484794 1, .k 334316375205882 71, .k 240290951161850 1, .k 83576184465402 28, .k 837934475258 1, .k 6060614707194 812, .k 3861591451642 1, .k 2762079823866 2872, .k 1662568196090 1, .k 133559838714 1, .k 236639053818 3653, .k 202279315450 1, .k 185099446266 1619, .k 133559838714 13, .k 665867347962 1, .k 532589144058 6, .k 133143554042 1, .k 133144602618 9, .k 665722890234 1, .k 532578306042 34307, .k 395139352570 1, .k 326419875834 24417, .k 532578306042 1, .k 120261445626 473610, .k 51541968890 1, .k 17182230522 2829536, .k 807667706 1, .k 1881409530 3190216, .k 807667706 1, .k 270796794 323903800, .k 136579066 1, .k 69470202 1019107586, .k 42089078 1, .k 17367558 285528470, .k 6880058 1, .k 4341906 3278902442, .k 2244754 1, .k 1196178 16080887479, .k 1132622 1, .k 299070 10196059880, .k 167998 1, .k 102462 49220528784, .k 89662 1, .k 910 1, .k 6510 7436779519, .k 3182 1, .k 2670 190196902731, .k 2158 1, .k 1902 91416876092, .k 1134 3607090573272, .k 622 1, .k 366 1247148618371, .k 238 1, .k 174 8777991210832, .k 142 1, .k 126 41052276700161, .k 366 1, .k 294 31671798164438, .k 230 1, .k 72 37189118444051, .k 120 1, .k 24 65433277186752, .k 11 1, .k 9 78474749496209, .k 7 1, .k 6 9575881408811365, .k 9 1, .k 3 17162295816727413, .k 6 1, .k 0 246018113982395611, .d 2], false⟩
def ckpt13 : RleFullState := ⟨.C, .raw [.z 1, .k 2290 1, .k 2802 8777991210832, .k 3826 1, .k 5874 1247148618371, .k 9970 1, .k 18162 3607090573272, .k 30450 91416876092, .k 34546 1, .k 42738 190196902731, .k 50930 1, .k 104178 7436779519, .k 14578 1, .k 1434610 1, .k 1639410 49220528784, .k 2687986 1, .k 4785138 10196059880, .k 18121970 1, .k 19138866 16080887479, .k 35916082 1, .k 69470514 3278902442, .k 110080946 1, .k 277880946 285528470, .k 673425266 1, .k 1111523250 1019107586, .k 2185265074 1, .k 4332748722 323903800, .k 12922683314 1, .k 30102552498 3190216, .k 12922683314 1, .k 274915688370 2829536, .k 824671502258 1, .k 1924183130034 473610, .k 8521252896690 1, .k 5222718013362 24417, .k 6322229641138 1, .k 8521252896690 34307, .k 10651566243762 1, .k 2130313641906 9, .k 2130296864690 1, .k 8521426304946 6, .k 10653877567410 1, .k 2136957419442 13, .k 2961591140274 1619, .k 3236469047218 1, .k 3786224861106 3653, .k 2136957419442 1, .k 26601091137458 1, .k 44193277181874 2872, .k 61785463226290 1, .k 96969835315122 812, .k 13406951604146 1, .k 1337218951446450 28, .k 3844655218589618 1, .k 5349062003294130 71, .k 15915495447756722 1, .k 21396250600832946 27, .k 59876793489889202 1, .k 85585002403310514 31, .k 5135527276205778 1, .k 1287191602033675778 1, .k 1369360038452967426 48, .k 3940586311812877442 1, .k 5477440153811869890 2, .k 2508525225284091713 1, .z 2], [.k 2034 41052276700161, .k 5874 1, .k 4722 31671798164438, .k 3698 1, .k 1170 37189118444051, .k 1938 1, .k 402 65433277186752, .k 194 1, .k 162 78474749496209, .k 130 1, .k 114 9575881408811365, .k 162 1, .k 66 17162295816727413, .k 114 1, .k 18 246018113982395612, .k 10 1, .k 6 5422433872730225880, .k 4 1, .k 3 22342849281290009221, .k 6 1, .k 0 7588671874192736443, .d 2], false⟩
def ckpt14 : RleFullState := ⟨.B, .clean 0 [] 189148142967018117408, [.d 1, .d 1, .k 21909760615247478879 4, .z 13918198875034348163, .d 1, .z 1997890435053282678, .d 2, .d 1, .k 5477440153811869719 43, .k 5148766408134703127 1, .k 20542109104823127 1, .k 342340009613242071 31, .k 239507173959556823 1, .k 85585002403331799 27, .k 63661981791026903 1, .k 21396248013176535 71, .k 15378620874358487 1, .k 5348875805785815 28, .k 53627806416599 1, .k 387879341260503 812, .k 247141852905175 1, .k 176773108727511 2872, .k 106404364549847 1, .k 8547829677783 1, .k 15144899444439 3653, .k 12945876188887 1, .k 11846364561111 1619, .k 8547829677783 13, .k 42615510269655 1, .k 34085705219799 6, .k 8521187458775 1, .k 8521254567639 9, .k 42606264975063 1, .k 34085011586775 34307, .k 25288918564567 1, .k 20890872053463 24417, .k 34085011586775 1, .k 7696732520151 473610, .k 3298686009047 1, .k 1099662753495 2829536, .k 51690733271 1, .k 120410210007 3190216, .k 51690733271 1, .k 17330994903 323903800, .k 8741060311 1, .k 4446093015 1019107586, .k 2693701079 1, .k 1111523799 285528470, .k 440323799 1, .k 277882071 3278902442, .k 143664343 1, .k 76555479 16080887479, .k 72487895 1, .k 19140567 10196059880, .k 10751959 1, .k 6557655 49220528784, .k 5738455 1, .k 58327 1, .k 416727 7436779519, .k 203735 1, .k 170967 190196902731, .k 138199 1, .k 121815 91416876092, .k 72663 3607090573272, .k 39895 1, .k 23511 1247148618371, .k 15319 1, .k 11223 8777991210832, .k 9175 1, .k 8151 41052276700161, .k 23511 1, .k 18903 31671798164438, .k 14807 1, .k 4695 37189118444051, .k 7767 1, .k 1623 65433277186752, .k 791 1, .k 663 78474749496209, .k 535 1, .k 471 9575881408811365, .k 663 1, .k 279 17162295816727413, .k 471 1, .k 87 246018113982395612, .k 55 1, .k 39 631165860194629366, .z 27, .d 1, .z 2, .d 2, .d 1, .k 9 4791268012535596513, .k 7 1, .k 6 22342849281290009221, .k 9 1, .k 3 7588671874192736443, .k 6 1, .k 0 21909760615247479561, .d 2], false⟩
def ckpt15 : RleFullState := ⟨.B, .clean 0 [(26230647, 49220528784), (43007863, 1), (76562295, 10196059880), (289951607, 1), (306221943, 16080887479), (574657399, 1), (1111528311, 3278902442), (1761295223, 1), (4446095223, 285528470), (10774804343, 1), (17784372087, 1019107586), (34964241271, 1), (69323979639, 323903800), (206762933111, 1), (481640840055, 3190216), (206762933111, 1), (4398651014007, 2829536), (13194744036215, 1), (30786930080631, 473610), (136340046347127, 1), (83563488213879, 24417), (101155674258295, 1), (136340046347127, 34307), (170425059900279, 1), (34085018270583, 9), (34084749835127, 1), (136342820879223, 6), (170462041078647, 1), (34191318711159, 13), (47385458244471, 1619), (51783504755575, 1), (60579597777783, 3653), (34191318711159, 1), (425617458199415, 1), (707092434910071, 2872), (988567411620727, 1), (1551517365042039, 812), (214511225666423, 1), (21395503223143287, 28), (61514483497433975, 1), (85584992052706167, 71), (254647927164107639, 1), (342340009613327223, 27), (958028695838227319, 1), (1369360038452968311, 31), (82168436419292535, 1), (20595065632538812535, 1), (21909760615247478903, 43), (7991561740213130739, 1), (222691182000549570631, 1), (63, 1), (5608898717503354593279, 1)] 2468328002243313095983, [.d 1, .d 1, .k 5738461 1, .k 58333 1, .k 416733 7436779519, .k 203741 1, .k 170973 190196902731, .k 138205 1, .k 121821 91416876092, .k 72669 3607090573272, .k 39901 1, .k 23517 1247148618371, .k 15325 1, .k 11229 8777991210832, .k 9181 1, .k 8157 41052276700161, .k 23517 1, .k 18909 31671798164438, .k 14813 1, .k 4701 37189118444051, .k 7773 1, .k 1629 65433277186752, .k 797 1, .k 669 78474749496209, .k 541 1, .k 477 9575881408811365, .k 669 1, .k 285 17162295816727413, .k 477 1, .k 93 246018113982395612, .k 61 1, .k 45 631165860194629366, .k 32 1, .k 12 4791268012535596513, .k 10 1, .k 9 22342849281290009221, .k 12 1, .k 6 7588671874192736443, .k 9 1, .k 3 108596472271926337351, .k 6 1, .k 0 206332718429699986606, .d 2], false⟩
def ckpt16 : RleFullState := ⟨.BR, .raw [.z 3], [.d 1, .k 1402224679375838649903 1, .z 132155174745082452323, .d 1, .z 317517376157689049394, .d 2, .d 1, .k 350556169843959662475 28, .z 44626652864179415015, .d 1, .z 76482379244945061864, .d 2, .d 1, .k 87639042460989915618 12, .k 82380262530155250146 1, .k 328673745677170146 1, .k 5477440153811873250 31, .k 3832114783352909282 1, .k 1369360038453308898 27, .k 1018591708656430562 1, .k 342339968210824674 71, .k 246057933989735906 1, .k 85582012892573154 28, .k 858044902665698 1, .k 6206069460168162 812, .k 3954269646482914 1, .k 2828369739640290 2872, .k 1702469832797666 1, .k 136765274844642 1, .k 242318391111138 3653, .k 207134019022306 1, .k 189541832977890 1619, .k 136765274844642 13, .k 681848164314594 1, .k 545371283516898 6, .k 136338999340514 1, .k 136340073082338 9, .k 681700239601122 1, .k 545360185388514 29, .z 545360185388514, .d 2, .k 545360185388511 34277, .k 404622697033183 1, .k 334253952855519 24417, .k 545360185388511 1, .k 123147720322527 473610, .k 52778976144863 1, .k 17594604056031 2829536, .k 827051732447 1, .k 1926563360223 3190216, .k 827051732447 1, .k 277295918559 323903800, .k 139856965087 1, .k 71137488351 1019107586, .k 43099217375 1, .k 17784380895 285528470, .k 7045180895 1, .k 4446113247 3278902442, .k 2298629599 1, .k 1224887775 16080887479, .k 1159806431 1, .k 306249183 10196059880, .k 172031455 1, .k 104922591 49220528784, .k 91815391 1, .k 933343 1, .k 6667743 7436779519, .k 3259871 1, .k 2735583 190196902731, .k 2211295 1, .k 1949151 91416876092, .k 1162719 3607090573272, .k 638431 1, .k 376287 1247148618371, .k 245215 1, .k 179679 8777991210832, .k 146911 1, .k 130527 41052276700161, .k 376287 1, .k 302559 31671798164438, .k 237023 1, .k 75231 37189118444051, .k 124383 1, .k 26079 65433277186752, .k 12767 1, .k 10719 78474749496209, .k 8671 1, .k 7647 9575881408811365, .k 10719 1, .k 4575 17162295816727413, .k 7647 1, .k 1503 246018113982395612, .k 991 1, .k 735 631165860194629366, .k 527 1, .k 207 4791268012535596513, .k 175 1, .k 159 22342849281290009221, .k 207 1, .k 111 7588671874192736443, .k 159 1, .k 63 108596472271926337351, .k 111 1, .k 15 206332718429699986607, .k 7 1, .k 3 1425423989669618216204, .k 1 1, .k 0 9885170686512209241889, .d 2], false⟩
def ckpt17 : RleFullState := ⟨.C, .raw [.z 1, .k 350556169843959662478 24, .k 1000584803598223835639 1, .k 396465524235247356973 1, .k 16092146482249460687119 1, .k 22435594870013418398655 1, .z 2], [.k 121109032109124476879 1, .k 87639042460989915618 12, .k 82380262530155250146 1, .k 328673745677170146 1, .k 5477440153811873250 31, .k 3832114783352909282 1, .k 1369360038453308898 27, .k 1018591708656430562 1, .k 342339968210824674 71, .k 246057933989735906 1, .k 85582012892573154 28, .k 858044902665698 1, .k 6206069460168162 812, .k 3954269646482914 1, .k 2828369739640290 2872, .k 1702469832797666 1, .k 136765274844642 1, .k 242318391111138 3653, .k 207134019022306 1, .k 189541832977890 1619, .k 136765274844642 13, .k 681848164314594 1, .k 545371283516898 6, .k 136338999340514 1, .k 136340073082338 9, .k 681700239601122 1, .k 545360185388514 34307, .k 404622697033186 1, .k 334253952855522 24417, .k 545360185388514 1, .k 123147720322530 473610, .k 52778976144866 1, .k 17594604056034 2829536, .k 827051732450 1, .k 1926563360226 3190216, .k 827051732450 1, .k 277295918562 323903800, .k 139856965090 1, .k 71137488354 1019107586, .k 43099217378 1, .k 17784380898 285528470, .k 7045180898 1, .k 4446113250 3278902442, .k 2298629602 1, .k 1224887778 16080887479, .k 1159806434 1, .k 306249186 10196059880, .k 172031458 1, .k 104922594 49220528784, .k 91815394 1, .k 933346 1, .k 6667746 7436779519, .k 3259874 1, .k 2735586 190196902731, .k 2211298 1, .k 1949154 91416876092, .k 1162722 3607090573272, .k 638434 1, .k 376290 1247148618371, .k 245218 1, .k 179682 8777991210832, .k 146914 1, .k 130530 41052276700161, .k 376290 1, .k 302562 31671798164438, .k 237026 1, .k 75234 37189118444051, .k 124386 1, .k 26082 65433277186752, .k 12770 1, .k 10722 78474749496209, .k 8674 1, .k 7650 9575881408811365, .k 10722 1, .k 4578 17162295816727413, .k 7650 1, .k 1506 246018113982395612, .k 994 1, .k 738 631165860194629366, .k 530 1, .k 210 4791268012535596513, .k 178 1, .k 162 22342849281290009221, .k 210 1, .k 114 7588671874192736443, .k 162 1, .k 66 108596472271926337351, .k 114 1, .k 18 206332718429699986607, .k 10 1, .k 6 1425423989669618216204, .k 4 1, .k 3 9493299518313199655854, .z 3, .d 2, .k 0 391871168199009586034, .d 2], false⟩
def ckpt18 : RleFullState := ⟨.B, .clean 0 [(8725762966216242, 34307), (10907203833617970, 1), (2181441169317426, 9), (2181423989448242, 1), (8725940536270386, 6), (10909570629033522, 1), (2188244397514290, 13), (3032669327646258, 1619), (3314144304356914, 1), (3877094257778226, 3653), (2188244397514290, 1), (27239517324762674, 1), (45253915834244658, 2872), (63268314343726642, 1), (99297111362690610, 812), (13728718442651186, 1), (1369312206281170482, 28), (3936926943835774514, 1), (5477439491373194802, 71), (16297467338502889010, 1), (21909760615252942386, 27), (61313836533646548530, 1), (87639042460989972018, 31), (5258779930834722354, 1), (1318084200482484002354, 1), (1402224679375838649906, 12), (1937744513745991630082, 1), (5608898717503354599666, 23), (2587910411783062835153, 1), (48335812891524668232207, 1)] 180028329067977809341330, [.z 1, .k 6473963152530991 1, .k 5348063245688367 24417, .k 8725762966216239 1, .k 1970363525160495 473610, .k 844463618317871 1, .k 281513664896559 2829536, .k 13232827719215 1, .k 30825013763631 3190216, .k 13232827719215 1, .k 4436734697007 323903800, .k 2237711441455 1, .k 1138199813679 1019107586, .k 689587478063 1, .k 284550094383 285528470, .k 112722894383 1, .k 71137812015 3278902442, .k 36778073647 1, .k 19598204463 16080887479, .k 18556902959 1, .k 4899986991 10196059880, .k 2752503343 1, .k 1678761519 49220528784, .k 1469046319 1, .k 14933551 1, .k 106683951 7436779519, .k 52157999 1, .k 43769391 190196902731, .k 35380783 1, .k 31186479 91416876092, .k 18603567 3607090573272, .k 10214959 1, .k 6020655 1247148618371, .k 3923503 1, .k 2874927 8777991210832, .k 2350639 1, .k 2088495 41052276700161, .k 6020655 1, .k 4841007 31671798164438, .k 3792431 1, .k 1203759 37189118444051, .k 1990191 1, .k 417327 65433277186752, .k 204335 1, .k 171567 78474749496209, .k 138799 1, .k 122415 9575881408811365, .k 171567 1, .k 73263 17162295816727413, .k 122415 1, .k 24111 246018113982395612, .k 15919 1, .k 11823 631165860194629366, .k 8495 1, .k 3375 4791268012535596513, .k 2863 1, .k 2607 22342849281290009221, .k 3375 1, .k 1839 7588671874192736443, .k 2607 1, .k 1071 108596472271926337351, .k 1839 1, .k 303 206332718429699986607, .k 175 1, .k 111 1425423989669618216204, .k 79 1, .k 63 2222607739818085223915, .z 19, .d 1, .z 10, .d 2, .d 1, .k 15 734549670260603111871, .z 7, .d 1, .z 1, .d 2, .d 1, .k 3 6536142108234511320066, .z 3, .d 2, .k 0 391871168199009586034, .d 2], false⟩

lemma chunk_0 : runSteps ckpt0 = ckpt1 := rfl
lemma chunk_1 : runSteps ckpt1 = ckpt2 := rfl
lemma chunk_2 : runSteps ckpt2 = ckpt3 := rfl
lemma chunk_3 : runSteps ckpt3 = ckpt4 := rfl
lemma chunk_4 : runSteps ckpt4 = ckpt5 := rfl
lemma chunk_5 : runSteps ckpt5 = ckpt6 := rfl
lemma chunk_6 : runSteps ckpt6 = ckpt7 := rfl
lemma chunk_7 : runSteps ckpt7 = ckpt8 := rfl
lemma chunk_8 : runSteps ckpt8 = ckpt9 := rfl
lemma chunk_9 : runSteps ckpt9 = ckpt10 := rfl
lemma chunk_10 : runSteps ckpt10 = ckpt11 := rfl
lemma chunk_11 : runSteps ckpt11 = ckpt12 := rfl
lemma chunk_12 : runSteps ckpt12 = ckpt13 := rfl
lemma chunk_13 : runSteps ckpt13 = ckpt14 := rfl
lemma chunk_14 : runSteps ckpt14 = ckpt15 := rfl
lemma chunk_15 : runSteps ckpt15 = ckpt16 := rfl
lemma chunk_16 : runSteps ckpt16 = ckpt17 := rfl
lemma chunk_17 : runSteps ckpt17 = ckpt18 := rfl
lemma chunk_18 : (runSteps ckpt18).halted = true := rfl

lemma reach_18 : StateHalts ckpt18 := runSteps_halts ckpt18 (Or.inl chunk_18)
lemma reach_17 : StateHalts ckpt17 := chunk_back chunk_17 reach_18
lemma reach_16 : StateHalts ckpt16 := chunk_back chunk_16 reach_17
lemma reach_15 : StateHalts ckpt15 := chunk_back chunk_15 reach_16
lemma reach_14 : StateHalts ckpt14 := chunk_back chunk_14 reach_15
lemma reach_13 : StateHalts ckpt13 := chunk_back chunk_13 reach_14
lemma reach_12 : StateHalts ckpt12 := chunk_back chunk_12 reach_13
lemma reach_11 : StateHalts ckpt11 := chunk_back chunk_11 reach_12
lemma reach_10 : StateHalts ckpt10 := chunk_back chunk_10 reach_11
lemma reach_9 : StateHalts ckpt9 := chunk_back chunk_9 reach_10
lemma reach_8 : StateHalts ckpt8 := chunk_back chunk_8 reach_9
lemma reach_7 : StateHalts ckpt7 := chunk_back chunk_7 reach_8
lemma reach_6 : StateHalts ckpt6 := chunk_back chunk_6 reach_7
lemma reach_5 : StateHalts ckpt5 := chunk_back chunk_5 reach_6
lemma reach_4 : StateHalts ckpt4 := chunk_back chunk_4 reach_5
lemma reach_3 : StateHalts ckpt3 := chunk_back chunk_3 reach_4
lemma reach_2 : StateHalts ckpt2 := chunk_back chunk_2 reach_3
lemma reach_1 : StateHalts ckpt1 := chunk_back chunk_1 reach_2
lemma reach_0 : StateHalts ckpt0 := chunk_back chunk_0 reach_1

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  rcases reach_0 with hfalse | hcan
  · simp [ckpt0] at hfalse
  · exact canHalt_of_stepPlus init_reaches_stack hcan

end BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH
