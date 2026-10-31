/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxRecDepth 20000000
set_option maxHeartbeats 40000000

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def E : Fin 6 := 4
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
  (encLeft1 R) <{{E}} (encRight1 L)

def cfg_C (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encLeft1 R, encRight1 L⟩⟩

def cfg_B (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encLeft1 R, encRight1 L⟩⟩

def cfg_DR0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, (0 : Fin 2) >> encLeft1 R, encRight1 L⟩⟩

def cfg_Halt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨1, r, l⟩⟩

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

theorem init_reaches_stack : (init []) [target_tm]⊢⁺ (cfg_C [] [0]) := by
  rw [init_nil]; unfold cfg_C
  rw [encLeft_zero, encLeft_nil, encRight_nil]; execute 1

theorem rule_B_nil (L : List ℕ) :
    (cfg_B L []) [target_tm]⊢⁺ (cfg_C (bumpHead L) []) := by
  unfold cfg_B cfg_C; rw [encLeft_nil]; execute 1

theorem rule_B_zero (L R : List ℕ) :
    (cfg_B L (0 :: R)) [target_tm]⊢⁺ (cfg_B (0 :: L) R) := by
  unfold cfg_B; rw [encLeft_zero R, encRight_zero L]; execute 4

theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR L (0 :: d :: R)) := by
  unfold cfg_B cfg_BR
  rw [encLeft_succ d R, encLeft_zero (d :: R), encLeft_expose d R]; execute 2

theorem rule_BR_nil (L : List ℕ) :
    (cfg_BR L []) [target_tm]⊢⁺ (cfg_C (bumpHead L) []) :=
  rule_B_nil L

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR L (0 :: R)) [target_tm]⊢⁺ (cfg_BR (0 :: L) R) := by
  unfold cfg_BR; rw [encLeft_zero R, encRight_zero L]; execute 2

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR L (1 :: R)) [target_tm]⊢⁺ (cfg_DR0 L (bumpHead R)) := by
  unfold cfg_BR cfg_DR0; rw [encLeft_succ 0 R, encLeft_zero R]; execute 4

theorem rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR L ((d + 2) :: R)) [target_tm]⊢⁺ (cfg_B (bumpHead L) (d :: R)) := by
  unfold cfg_BR cfg_B
  rw [encLeft_succ (d + 1) R, encLeft_succ d R, encLeft_expose d R]; execute 5

theorem rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 [] R) [target_tm]⊢⁺ (cfg_C [1] R) := by
  unfold cfg_DR0 cfg_C
  rw [encRight_nil, encRight_succ 0 [], encRight_zero [], encRight_nil]; execute 3

theorem rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 (0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 L (0 :: R)) := by
  unfold cfg_DR0; rw [encRight_zero L, encLeft_zero R]; execute 4

theorem rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 ((a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C (a :: L) (0 :: R)) := by
  unfold cfg_DR0 cfg_C; rw [encRight_succ a L, encLeft_zero R]; execute 3

theorem rule_C_nil (R : List ℕ) :
    (cfg_C [] R) [target_tm]⊢⁺ (cfg_DR0 [] R) := by
  unfold cfg_C cfg_DR0; rw [encRight_nil]; execute 1

theorem rule_C_zero_nil (R : List ℕ) :
    (cfg_C [0] R) [target_tm]⊢⁺ (cfg_C [] (1 :: R)) := by
  unfold cfg_C
  rw [encRight_zero [], encRight_nil, encLeft_succ 0 R, encLeft_zero R]; execute 3

theorem rule_C_zero_zero (L R : List ℕ) :
    (cfg_C (0 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_C (bumpHead L) (1 :: R)) := by
  unfold cfg_C
  rw [encRight_zero (0 :: L), encRight_zero L, encLeft_succ 0 R, encLeft_zero R]; execute 5

theorem rule_C_zero_one (L R : List ℕ) :
    (cfg_C (0 :: 1 :: L) R) [target_tm]⊢⁺
    (cfg_C (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_C
  rw [encRight_zero (1 :: L), encRight_succ 0 L, encRight_zero L, encLeft_zero (bumpHead R)]
  execute 17

theorem rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C (0 :: (a + 2) :: L) R) [target_tm]⊢⁺ (cfg_BR (a :: L) (0 :: 1 :: R)) := by
  unfold cfg_C cfg_BR
  rw [encRight_zero ((a + 2) :: L), encRight_succ (a + 1) L, encRight_succ a L,
    encLeft_zero (1 :: R), encLeft_succ 0 R, encLeft_zero R]; execute 4

theorem rule_C_one_nil (R : List ℕ) :
    (cfg_C [1] R) [target_tm]⊢⁺ (cfg_B [0] (1 :: R)) := by
  unfold cfg_C cfg_B
  rw [encRight_succ 0 [], encRight_zero [], encRight_nil, encLeft_succ 0 R, encLeft_zero R]
  execute 5

theorem rule_C_one_zero (L R : List ℕ) :
    (cfg_C (1 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 L (2 :: R)) := by
  unfold cfg_C cfg_DR0
  rw [encRight_succ 0 (0 :: L), encRight_zero (0 :: L), encRight_zero L,
    encLeft_succ 1 R, encLeft_succ 0 R, encLeft_zero R]; execute 7

theorem rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C (1 :: (a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C (a :: L) (2 :: R)) := by
  unfold cfg_C
  rw [encRight_succ 0 ((a + 1) :: L), encRight_zero ((a + 1) :: L), encRight_succ a L,
    encLeft_succ 1 R, encLeft_succ 0 R, encLeft_zero R]; execute 6

theorem rule_C_add_two_step (a : ℕ) (L R : List ℕ) :
    (cfg_C ((a + 2) :: L) R) [target_tm]⊢⁺
    (cfg_Halt (((encRight1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a))
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft1 R)) := by
  unfold cfg_C cfg_Halt
  rw [encRight_succ (a + 1) L, encRight_succ a L, encRight_expose a L]; execute 3

theorem rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C ((a + 2) :: L) R) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone :=
  ⟨cfg_Halt (((encRight1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a))
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft1 R),
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


def ckpt0 : RleFullState := ⟨.C, .raw [], [.z 1], false⟩
def ckpt1 : RleFullState := ⟨.DR0, .raw [.d 1, .k 16575 7, .k 18623 1, .k 68799 1, .z 2], [.z 2946, .d 1, .z 3406, .d 2, .d 1, .k 4143 6, .z 3683, .d 1, .z 114, .d 2, .d 1, .k 1035 6, .z 431, .d 1, .z 150, .d 2, .d 1, .k 258 4, .k 130 1, .k 66 21, .k 34 1, .k 18 950, .k 10 1, .k 6 6175, .k 4 1, .k 3 2047, .z 3, .d 2, .k 0 32858, .d 2], false⟩
def ckpt2 : RleFullState := ⟨.B, .clean 0 [(973067, 1), (1062411, 6), (873739, 1), (3019531, 1), (16974603, 1), (1900551, 1)] 173359632, [.d 1, .d 1, .k 66498 11, .k 33730 1, .k 17346 21, .k 9154 1, .k 5058 950, .k 3010 1, .k 1986 6175, .k 1474 1, .k 1218 1184, .k 770 1, .k 258 33721, .k 450 1, .k 66 125691, .k 34 1, .k 18 876511, .k 10 1, .k 6 1737322, .k 2 1, .k 0 38203783, .d 2], false⟩
def ckpt3 : RleFullState := ⟨.B, .clean 0 [(2603553551, 1)] 2612851068, [.z 109256191, .d 2, .d 1, .k 271978287 1, .k 249106223 1, .k 68095791 3, .k 24570335 1, .k 17023935 7, .k 8635327 1, .k 4441023 21, .k 2343871 1, .k 1295295 950, .k 771007 1, .k 508863 6175, .k 377791 1, .k 312255 203, .z 241331, .d 1, .z 17730, .d 2, .d 1, .k 78063 980, .k 49391 1, .k 16623 33721, .k 28911 1, .k 4335 48275, .k 2175 1, .k 137 1, .k 273 77415, .k 145 1, .k 81 876511, .k 49 1, .k 33 1737322, .k 17 1, .k 9 38203784, .k 7 1, .k 6 27434495, .k 3 27667739, .z 3, .d 3, .d 1, .k 0 14420122, .d 2], false⟩
def ckpt4 : RleFullState := ⟨.C, .raw [.z 1, .k 56357045 1, .k 82899186 98, .k 150008050 1, .k 284225778 21, .k 552661234 1, .k 1089532146 4, .k 482967249 1, .k 9705038351 1, .k 17432514303 2, .k 25160027903 1, .k 69730094847 1, .z 2], [.k 20724795 851, .k 12336187 1, .k 8141883 6175, .k 6044731 1, .k 4996155 203, .k 4145003 1, .k 1249035 980, .k 790283 1, .k 265995 33721, .k 462603 1, .k 69387 48275, .k 34827 1, .k 2219 1, .k 4395 77415, .k 2347 1, .k 1323 876511, .k 811 1, .k 555 1737322, .k 299 1, .k 171 38203784, .k 139 1, .k 123 27434495, .k 75 42087863, .k 43 1, .k 27 73686092, .z 7, .d 1, .z 4, .d 2, .d 1, .k 6 475716378, .k 2 1, .k 0 13551424202, .d 2], false⟩
def ckpt5 : RleFullState := ⟨.B, .clean 0 [(1110210, 48275), (7401666, 1), (4255938, 33721), (12644546, 1), (19984578, 980), (66320066, 1), (79938498, 203), (96715714, 1), (130270146, 6175), (197379010, 1), (331596738, 309), (567673274, 1), (1326386958, 277), (277743562, 1), (16778294338, 1), (21222191106, 263), (57709615106, 1), (84888767490, 98), (153608244226, 1), (291047197698, 21), (565925104642, 1), (1115680918530, 2), (747686445057, 1), (5887911575567, 1)] 11916193038108, [.z 1, .k 557247 1, .k 35519 1, .k 70335 77415, .k 37567 1, .k 21183 876511, .k 12991 1, .k 8895 1737322, .k 4799 1, .k 2751 38203784, .k 2239 1, .k 1983 27434495, .k 1215 42087863, .k 703 1, .k 447 73686092, .k 127 1, .k 31 1, .k 39 475716378, .k 23 1, .k 15 13551424202, .k 27 1, .k 3 505632912192, .z 3, .d 3, .d 1, .k 0 615592097523, .d 2], false⟩
def ckpt6 : RleFullState := ⟨.C, .raw [.z 1, .k 281358 77415, .k 142094 1, .k 2229006 1, .k 4440846 48275, .k 29606670 1, .k 17023758 33721, .k 50578190 1, .k 79938318 980, .k 265280270 1, .k 319753998 203, .k 386862862 1, .k 521080590 6175, .k 789516046 1, .k 1326386958 309, .k 2270693102 1, .k 5305547838 277, .k 1110974254 1, .k 67113177358 1, .k 84888764430 263, .k 230838460430 1, .k 339555069966 5, .k 860299088330 1, .k 1358220279870 92, .k 2457731907646 1, .k 4656755163198 20, .k 4540718317493 1, .k 1856589531279 1, .z 2], [.k 150286 1, .k 84750 876511, .k 51982 1, .k 35598 1737322, .k 19214 1, .k 11022 38203784, .k 8974 1, .k 7950 27434495, .k 4878 42087863, .k 2830 1, .k 1806 73686092, .k 526 1, .k 142 1, .k 174 475716378, .k 110 1, .k 78 13551424202, .k 126 1, .k 30 505632912192, .k 14 1, .k 6 47526570402450, .k 4 1, .k 3 57901138422179, .z 3, .d 2, .k 0 37610989893458, .d 2], false⟩
def ckpt7 : RleFullState := ⟨.DR0, .raw [.z 1205456128635837], [.d 1, .d 2, .d 1, .k 49394413264663 1, .k 74508082611243 6, .k 64897963560611 1, .k 18627020652807 9, .k 9830927630599 1, .k 5432881119495 92, .k 3441196353335 1, .k 1358220279879 5, .k 923353841735 1, .k 339555057735 263, .k 268452709447 1, .k 4443897031 1, .k 21222191367 277, .k 9082772423 1, .k 5305547847 309, .k 3158064199 1, .k 2084322375 6175, .k 1547451463 1, .k 1279016007 203, .k 1061121095 1, .k 319753287 980, .k 202312775 1, .k 68095047 33721, .k 118426695 1, .k 17763399 48275, .k 8916039 1, .k 568391 1, .k 1125447 77415, .k 601159 1, .k 339015 876511, .k 207943 1, .k 142407 1737322, .k 76871 1, .k 44103 38203784, .k 35911 1, .k 31815 27434495, .k 19527 42087863, .k 11335 1, .k 7239 73686092, .k 2119 1, .k 583 1, .k 711 475716378, .k 455 1, .k 327 13551424202, .k 519 1, .k 135 505632912192, .k 71 1, .k 39 43324314296590, .z 15, .d 1, .z 5, .d 2, .d 1, .k 9 4202256105859, .k 7 1, .k 6 57901138422180, .k 3 37610989893458, .k 1 1, .k 0 30716371615731, .d 2], false⟩
def ckpt8 : RleFullState := ⟨.C, .raw [.z 1, .k 1192129321779918 3, .k 1152148901212085 1, .z 2], [.k 1038367416969806 1, .k 298032330444942 9, .k 157294842089614 1, .k 86926097911950 85, .k 79886494238810 1, .k 21731524477986 6, .k 13764785413346 1, .k 5432881119522 5, .k 3693415366946 1, .k 1358220230946 263, .k 1073810837794 1, .k 17775588130 1, .k 84888765474 277, .k 36331089698 1, .k 21222191394 309, .k 12632256802 1, .k 8337289506 6175, .k 6189805858 1, .k 5116064034 203, .k 4244484386 1, .k 1279013154 980, .k 809251106 1, .k 272380194 33721, .k 473706786 1, .k 71053602 48275, .k 35664162 1, .k 2273570 1, .k 4501794 77415, .k 2404642 1, .k 1356066 876511, .k 831778 1, .k 569634 1737322, .k 307490 1, .k 176418 38203784, .k 143650 1, .k 127266 27434495, .k 78114 42087863, .k 45346 1, .k 28962 73686092, .k 8482 1, .k 2338 1, .k 2850 475716378, .k 1826 1, .k 1314 13551424202, .k 2082 1, .k 546 505632912192, .k 290 1, .k 162 47526570402450, .k 130 1, .k 114 57901138422180, .k 66 37610989893458, .k 34 1, .k 18 30716371615732, .k 10 1, .k 6 305490132233582, .z 6, .d 2, .k 3 1463604456978626, .k 1 1, .k 0 3861945115594672, .d 2], false⟩
def ckpt9 : RleFullState := ⟨.C, .raw [.z 3], [.z 23028722247072195, .d 1, .z 10856698109748910, .d 2, .d 1, .k 4768517287119135 9, .k 2516717473433887 1, .k 1390817566591263 85, .k 1278183907821023 1, .k 347704391647839 6, .k 220236566613599 1, .k 86926097912415 5, .k 59094645871199 1, .k 21731523695199 263, .k 17180973404767 1, .k 284409410143 1, .k 1358220247647 277, .k 581297435231 1, .k 339555062367 309, .k 202116108895 1, .k 133396632159 6175, .k 99036893791 1, .k 81857024607 203, .k 67911750239 1, .k 20464210527 980, .k 12948017759 1, .k 4358083167 33721, .k 7579308639 1, .k 1136857695 48275, .k 570626655 1, .k 36377183 1, .k 72028767 77415, .k 38474335 1, .k 21697119 876511, .k 13308511 1, .k 9114207 1737322, .k 4919903 1, .k 2822751 38203784, .k 2298463 1, .k 2036319 27434495, .k 1249887 42087863, .k 725599 1, .k 463455 73686092, .k 135775 1, .k 37471 1, .k 45663 475716378, .k 29279 1, .k 21087 13551424202, .k 33375 1, .k 8799 505632912192, .k 4703 1, .k 2655 47526570402450, .k 2143 1, .k 1887 57901138422180, .k 1119 37610989893458, .k 607 1, .k 351 30716371615732, .k 223 1, .k 159 305490132233582, .k 351 1, .k 255 410636788096503, .k 95 1, .k 12 1, .k 18 781492533683413, .k 14 1, .k 3 271475135198707, .k 1 1, .k 0 48671766179730583, .d 2], false⟩
def ckpt10 : RleFullState := ⟨.C, .raw [.z 1, .k 880946266454411 1, .k 1390817566591371 6, .k 5112735631284107 1, .k 5563270266365067 85, .k 10066869893735563 1, .k 19074069148476555 2, .k 66581956426859459 1, .k 76296276593906235 1, .k 76296276593906231 1, .k 63 1, .k 1220740425502499583 1, .z 2], [.k 347704391649675 5, .k 236378583484811 1, .k 86926094780811 263, .k 68723893619083 1, .k 1137637640587 1, .k 5432880990603 277, .k 2325189740939 1, .k 1358220249483 309, .k 808464435595 1, .k 533586528651 6175, .k 396147575179 1, .k 327428098443 203, .k 271647000971 1, .k 81856842123 980, .k 51792071051 1, .k 17432332683 33721, .k 30317234571 1, .k 4547430795 48275, .k 2282506635 1, .k 145508747 1, .k 288115083 77415, .k 153897355 1, .k 86788491 876511, .k 53234059 1, .k 36456843 1737322, .k 19679627 1, .k 11291019 38203784, .k 9193867 1, .k 8145291 27434495, .k 4999563 42087863, .k 2902411 1, .k 1853835 73686092, .k 543115 1, .k 149899 1, .k 182667 475716378, .k 117131 1, .k 84363 13551424202, .k 133515 1, .k 35211 505632912192, .k 18827 1, .k 10635 47526570402450, .k 8587 1, .k 7563 57901138422180, .k 4491 37610989893458, .k 2443 1, .k 1419 30716371615732, .k 907 1, .k 651 305490132233582, .k 1419 1, .k 1035 270647459772345, .z 979, .d 1, .z 13, .d 2, .d 1, .k 258 139989328324157, .k 98 1, .k 15 1, .k 21 781492533683413, .k 17 1, .k 6 271475135198707, .k 4 1, .k 3 48671766179730583, .k 6 1, .k 0 94767307651599602, .d 2], false⟩
def ckpt11 : RleFullState := ⟨.B, .clean 0 [(9849430783, 1), (18439365375, 77415), (9312559871, 1), (146080424703, 1), (291035570943, 48275), (1940303012607, 1), (1115669291775, 32810), (1394586614727, 1), (278917322967, 909), (828673136855, 1), (1309709474007, 980), (4346352015575, 1), (5238849575127, 203), (6338361202903, 1), (8537384458455, 6175), (12935430969559, 1), (21731523991767, 309), (37203035855063, 1), (86926095849687, 277), (18202202249431, 1), (1099582297905367, 1), (1390817516493015, 263), (3782057335757015, 1), (5563270266394839, 5), (14095140263270615, 1), (22253081065461975, 6), (81803770100545751, 1), (89012324261841111, 78), (18356852708667775, 1), (1130487544850773375, 1), (1424197188189457599, 6), (2577118692796304575, 1), (4882961702009998527, 2)] 5347183269983473252, [.d 1, .d 1, .k 1388615871 876511, .k 851744959 1, .k 583309503 1737322, .k 314874047 1, .k 180656319 38203784, .k 147101887 1, .k 130324671 27434495, .k 79993023 42087863, .k 46438591 1, .k 29661375 73686092, .k 8689855 1, .k 2398399 1, .k 2922687 475716378, .k 1874111 1, .k 1349823 13551424202, .k 2136255 1, .k 563391 505632912192, .k 301247 1, .k 170175 26720150428303, .z 84051, .d 1, .z 21530, .d 2, .d 1, .k 42543 20806419974146, .k 34351 1, .k 30255 57901138422180, .k 17967 37610989893458, .k 9775 1, .k 5679 30716371615732, .k 3631 1, .k 2607 305490132233582, .k 5679 1, .k 4143 270647459772345, .k 3919 1, .k 16 1, .k 261 139989328324157, .k 101 1, .k 18 1, .k 24 781492533683413, .k 20 1, .k 9 271475135198707, .k 7 1, .k 6 48671766179730583, .k 9 1, .k 3 94767307651599602, .k 6 1, .k 0 1076108394673963110, .d 2], false⟩
def ckpt12 : RleFullState := ⟨.BR, .clean 3 [(5399298, 13551424202), (7496450, 1), (11690754, 475716378), (9593602, 1), (34759426, 1), (118645506, 73686092), (185754370, 1), (319972098, 42087863), (521298690, 27434495), (588407554, 1), (722625282, 38203784), (1259496194, 1), (2333238018, 1737322), (3406979842, 1), (5554463490, 876511), (9849430786, 1), (18439365378, 77415), (9312559874, 1), (146080424706, 1), (291035570946, 48275), (1940303012610, 1), (1115669291778, 32810), (1394586614730, 1), (278917322970, 909), (828673136858, 1), (1309709474010, 980), (4346352015578, 1), (5238849575130, 203), (6338361202906, 1), (8537384458458, 6175), (12935430969562, 1), (21731523991770, 309), (37203035855066, 1), (86926095849690, 277), (18202202249434, 1), (1099582297905370, 1), (1390817516493018, 263), (3782057335757018, 1), (5563270266394842, 5), (14095140263270618, 1), (22253081065461978, 6), (81803770100545754, 1), (89012324261841114, 8), (190258379573867327, 1), (356049297047364462, 69), (73427410834671118, 1), (4521950179403093518, 1), (5425513671652212490, 1), (4340401297689886786, 1), (91148620044125286401, 1), (15, 1), (1458377920706004582399, 2)] 364594480176501145522, [.k 8545026 1, .k 2253570 505632912192, .k 1204994 1, .k 680706 26720150428303, .k 336210 1, .k 21536 1, .k 42549 20806419974146, .k 34357 1, .k 30261 57901138422180, .k 17973 37610989893458, .k 9781 1, .k 5685 30716371615732, .k 3637 1, .k 2613 305490132233582, .k 5685 1, .k 4149 270647459772345, .k 3925 1, .k 22 1, .k 267 139989328324157, .k 107 1, .k 24 1, .k 30 781492533683413, .k 26 1, .k 15 271475135198707, .k 13 1, .k 12 48671766179730583, .k 15 1, .k 9 94767307651599602, .k 12 1, .k 6 331887753716974115, .k 3 744220640956988995, .k 1 1, .k 0 18310355970030908204, .d 2], false⟩
def ckpt13 : RleFullState := ⟨.C, .raw [.z 1, .k 60512917372112303 1, .k 89012324262317487 5, .k 225522244212329903 1, .k 356049297047391663 6, .k 1308860321608732079 1, .k 1424197188189457839 8, .k 3044134073181877247 1, .k 5696788752757831407 69, .k 1174838573354737903 1, .k 72351202870449496303 1, .k 86808218746435399855 1, .k 69446420763038188591 1, .k 1458377920706004582431 1, .k 255 1, .z 2], [.k 22253080263888303 263, .k 17593316766485935 1, .k 291235235990959 1, .k 1390817533595055 277, .k 595248573681071 1, .k 347704383868335 309, .k 206966895513007 1, .k 136598151335343 6175, .k 101413779246511 1, .k 83821593202095 203, .k 69541632249263 1, .k 20955351584175 980, .k 13258770189743 1, .k 4462677167535 909, .k 22313385835695 1, .k 17850708668463 32810, .k 31044848201775 1, .k 4656569135151 48275, .k 2337286795311 1, .k 149000957999 1, .k 295029846063 77415, .k 157590892591 1, .k 88871415855 876511, .k 54511677487 1, .k 37331808303 1737322, .k 20151939119 1, .k 11562004527 38203784, .k 9414520879 1, .k 8340779055 27434495, .k 5119553583 42087863, .k 2972069935 1, .k 1898328111 73686092, .k 556150831 1, .k 153497647 1, .k 187052079 475716378, .k 119943215 1, .k 86388783 13551424202, .k 136720431 1, .k 36057135 505632912192, .k 19279919 1, .k 10891311 26720150428303, .k 5379375 1, .k 344591 1, .k 680799 20806419974146, .k 549727 1, .k 484191 57901138422180, .k 287583 37610989893458, .k 156511 1, .k 90975 30716371615732, .k 58207 1, .k 41823 305490132233582, .k 90975 1, .k 66399 270647459772345, .k 62815 1, .k 367 1, .k 4287 139989328324157, .k 1727 1, .k 399 1, .k 495 781492533683413, .k 431 1, .k 255 271475135198707, .k 223 1, .k 207 48671766179730583, .k 255 1, .k 159 94767307651599602, .k 207 1, .k 111 331887753716974115, .k 63 744220640956988995, .k 31 1, .k 15 382904836146532053728, .k 7 1, .k 3 2370268793986893518021, .k 1 1, .k 0 12944318064784698883660, .d 2], false⟩
def ckpt14 : RleFullState := ⟨.C, .raw [.z 1, .k 153497650 1, .k 556150834 1, .k 1898328114 73686092, .k 2972069938 1, .k 5119553586 42087863, .k 8340779058 27434495, .k 9414520882 1, .k 11562004530 38203784, .k 20151939122 1, .k 37331808306 1737322, .k 54511677490 1, .k 88871415858 876511, .k 157590892594 1, .k 295029846066 77415, .k 149000958002 1, .k 2337286795314 1, .k 4656569135154 48275, .k 31044848201778 1, .k 17850708668466 32801, .k 17850708668465 1, .k 71402834673870 8, .k 89253543342798 1, .k 17850708670158 909, .k 53035080758990 1, .k 83821406336718 980, .k 278166528997070 1, .k 335286372808398 203, .k 405655116986062 1, .k 546392605341390 6175, .k 827867582052046 1, .k 1390817535473358 309, .k 2380994294724302 1, .k 5563270134380238 277, .k 1164940943963854 1, .k 70373267065943758 1, .k 89012321055553230 263, .k 242051669488449230 1, .k 356049297049269966 5, .k 902088976849319630 1, .k 1424197188189566670 6, .k 5235441286434928334 1, .k 5696788752757831374 8, .k 12176536292727509006 1, .k 22787155011031325646 60, .k 13064386703782203949 1, .k 155564292915985947151 1, .k 364594480176501210303 8, .k 75189668694703226047 1, .k 4630476983708767763647 1, .z 2], [.k 187052082 475716378, .k 119943218 1, .k 86388786 13551424202, .k 136720434 1, .k 36057138 505632912192, .k 19279922 1, .k 10891314 26720150428303, .k 5379378 1, .k 344594 1, .k 680802 20806419974146, .k 549730 1, .k 484194 57901138422180, .k 287586 37610989893458, .k 156514 1, .k 90978 30716371615732, .k 58210 1, .k 41826 305490132233582, .k 90978 1, .k 66402 270647459772345, .k 62818 1, .k 370 1, .k 4290 139989328324157, .k 1730 1, .k 402 1, .k 498 781492533683413, .k 434 1, .k 258 271475135198707, .k 226 1, .k 210 48671766179730583, .k 258 1, .k 162 94767307651599602, .k 210 1, .k 114 331887753716974115, .k 66 744220640956988995, .k 34 1, .k 18 382904836146532053728, .k 10 1, .k 6 1838171476161491398790, .z 6, .d 2, .k 3 532097317825402119230, .k 1 1, .k 0 16670729362036111891903, .d 2], false⟩
def ckpt15 : RleFullState := ⟨.B, .clean 0 [] 17500535048472058094628, [.d 1, .d 1, .z 839711073610774178831, .d 1, .z 1248450152303311296510, .d 2, .d 1, .k 1458377920706004841218 5, .k 622257171663943788610 1, .k 52257546815128815802 1, .k 91148620044125302590 60, .k 48706145170910036030 1, .k 22787155011031325502 8, .k 20941765145739713342 1, .k 5696788752758266686 6, .k 3608355907397278526 1, .k 1424197188197079870 5, .k 968206677953796926 1, .k 356049284222212926 263, .k 281493068263775038 1, .k 4659763775855422 1, .k 22253080537520958 277, .k 9523977178897214 1, .k 5563270141893438 309, .k 3311470328208190 1, .k 2185570421365566 6175, .k 1622620467944254 1, .k 1341145491233598 203, .k 1112666115988286 1, .k 335285625346878 980, .k 212140323035966 1, .k 71402834680638 909, .k 357014173371198 1, .k 285611338695486 8, .k 71402834673866 1, .k 71402834673870 32801, .k 124179392807118 1, .k 18626276540622 48275, .k 9349147181262 1, .k 596003832014 1, .k 1180119384270 77415, .k 630363570382 1, .k 355485663438 876511, .k 218046709966 1, .k 149327233230 1737322, .k 80607756494 1, .k 46248018126 38203784, .k 37658083534 1, .k 33363116238 27434495, .k 20478214350 42087863, .k 11888279758 1, .k 7593312462 73686092, .k 2224603342 1, .k 613990606 1, .k 748208334 475716378, .k 479772878 1, .k 345555150 13551424202, .k 546881742 1, .k 144228558 505632912192, .k 77119694 1, .k 43565262 26720150428303, .k 21517518 1, .k 1378382 1, .k 2723214 20806419974146, .k 2198926 1, .k 1936782 57901138422180, .k 1150350 37610989893458, .k 626062 1, .k 363918 30716371615732, .k 232846 1, .k 167310 305490132233582, .k 363918 1, .k 265614 270647459772345, .k 251278 1, .k 1486 1, .k 17166 139989328324157, .k 6926 1, .k 1614 1, .k 1998 781492533683413, .k 1742 1, .k 1038 271475135198707, .k 910 1, .k 846 48671766179730583, .k 1038 1, .k 654 94767307651599602, .k 846 1, .k 462 331887753716974115, .k 270 744220640956988995, .k 142 1, .k 78 382904836146532053728, .k 46 1, .k 30 210157523808992004318, .k 26 1, .k 6 2160111270177901513702, .k 4 1, .k 3 9700931123418329287744, .z 3, .d 2, .k 0 6969798238617782604158, .d 2], false⟩
def ckpt16 : RleFullState := ⟨.BR, .raw [.z 280008560775552929514624], [.d 1, .d 2, .d 1, .k 53030055391867149254287 1, .k 2519133220832322536497 1, .k 5833511682824019364890 2, .k 2489028686655775154458 1, .k 209030187260515263226 1, .k 364594480176501210378 9, .k 215171105903388249377 1, .k 91148620044125302593 50, .k 48706145170910036033 1, .k 22787155011031325505 8, .k 20941765145739713345 1, .k 5696788752758266689 6, .k 3608355907397278529 1, .k 1424197188197079873 5, .k 968206677953796929 1, .k 356049284222212929 263, .k 281493068263775041 1, .k 4659763775855425 1, .k 22253080537520961 277, .k 9523977178897217 1, .k 5563270141893441 309, .k 3311470328208193 1, .k 2185570421365569 6175, .k 1622620467944257 1, .k 1341145491233601 203, .k 1112666115988289 1, .k 335285625346881 980, .k 212140323035969 1, .k 71402834680641 909, .k 357014173371201 1, .k 285611338695489 8, .k 71402834673869 1, .k 71402834673873 32801, .k 124179392807121 1, .k 18626276540625 48275, .k 9349147181265 1, .k 596003832017 1, .k 1180119384273 77415, .k 630363570385 1, .k 355485663441 876511, .k 218046709969 1, .k 149327233233 1737322, .k 80607756497 1, .k 46248018129 38203784, .k 37658083537 1, .k 33363116241 27434495, .k 20478214353 42087863, .k 11888279761 1, .k 7593312465 73686092, .k 2224603345 1, .k 613990609 1, .k 748208337 475716378, .k 479772881 1, .k 345555153 13551424202, .k 546881745 1, .k 144228561 505632912192, .k 77119697 1, .k 43565265 26720150428303, .k 21517521 1, .k 1378385 1, .k 2723217 20806419974146, .k 2198929 1, .k 1936785 57901138422180, .k 1150353 37610989893458, .k 626065 1, .k 363921 30716371615732, .k 232849 1, .k 167313 305490132233582, .k 363921 1, .k 265617 270647459772345, .k 251281 1, .k 1489 1, .k 17169 139989328324157, .k 6929 1, .k 1617 1, .k 2001 781492533683413, .k 1745 1, .k 1041 271475135198707, .k 913 1, .k 849 48671766179730583, .k 1041 1, .k 657 94767307651599602, .k 849 1, .k 465 331887753716974115, .k 273 744220640956988995, .k 145 1, .k 81 382904836146532053728, .k 49 1, .k 33 210157523808992004318, .k 29 1, .k 9 2160111270177901513702, .k 7 1, .k 6 9700931123418329287745, .k 3 6969798238617782604158, .k 1 1, .k 0 30646279106479104971760, .d 2], false⟩
def ckpt17 : RleFullState := ⟨.B, .clean 0 [(602529336610, 1), (739968290082, 38203784), (1289724103970, 1), (2389235731746, 1737322), (3488747359522, 1), (5687770615074, 876511), (10085817126178, 1), (18881910148386, 77415), (9536061312290, 1), (149586354900258, 1), (298020424650018, 48275), (1986870284913954, 1), (1142445354781986, 32801), (1142445354781922, 1), (4569781419127842, 8), (5712226773939234, 1), (1142445354890274, 909), (3394245168575522, 1), (5364570005550114, 980), (17802657855812642, 1), (21458327859737634, 203), (25961927487108130, 1), (34969126741849122, 6175), (52983525251331106, 1), (89012322270295074, 309), (152383634862355490, 1), (356049288600335394, 277), (74556220413686818, 1), (4503889092220400674, 1), (5696788547555406882, 263), (15491306847260750882, 1), (22787155011153277986, 5), (57733694518356456482, 1), (91148620044132267042, 6), (335068242331835413538, 1), (364594480176501208098, 8), (779298322734560576546, 1), (1458377920706004841506, 50), (3442737694454211990050, 1), (5833511682824019366066, 9), (3344482996168244211634, 1), (39824458986492402471346, 1), (65753979250417137924609, 1), (441315322796274750618383, 1)] 1009705412403142989419142, [.z 1, .k 533809859871 27434495, .k 327651429663 42087863, .k 190212476191 1, .k 121492999455 73686092, .k 35593653535 1, .k 9823849759 1, .k 11971333407 475716378, .k 7676366111 1, .k 5528882463 13551424202, .k 8750107935 1, .k 2307656991 505632912192, .k 1233915167 1, .k 697044255 26720150428303, .k 344280351 1, .k 22054175 1, .k 43571487 20806419974146, .k 35182879 1, .k 30988575 57901138422180, .k 18405663 37610989893458, .k 10017055 1, .k 5822751 30716371615732, .k 3725599 1, .k 2677023 305490132233582, .k 5822751 1, .k 4249887 270647459772345, .k 4020511 1, .k 23839 1, .k 274719 139989328324157, .k 110879 1, .k 25887 1, .k 32031 781492533683413, .k 27935 1, .k 16671 271475135198707, .k 14623 1, .k 13599 48671766179730583, .k 16671 1, .k 10527 94767307651599602, .k 13599 1, .k 7455 331887753716974115, .k 4383 744220640956988995, .k 2335 1, .k 1311 382904836146532053728, .k 799 1, .k 543 210157523808992004318, .k 479 1, .k 159 2160111270177901513702, .k 127 1, .k 111 9700931123418329287745, .k 63 906038693021585505429, .z 35, .d 1, .z 6, .d 2, .d 1, .k 15 6063759545596197098728, .k 7 1, .k 3 30646279106479104971761, .k 1 1, .k 0 12987021919220439130794, .d 2], false⟩
def ckpt18 : RleFullState := ⟨.DR0, .raw [.z 3], [.d 1, .z 637191343783878439541550, .d 2, .d 1, .k 53511727938691907386159 1, .k 93336186925184309857071 9, .k 55083803111267391840815 1, .k 23334046731296077464111 50, .k 12468773163752969224751 1, .k 5833511682824019329583 8, .k 5361091877309366616623 1, .k 1458377920706116272687 6, .k 923739112293703303727 1, .k 364594480178452447791 5, .k 247860909556172014127 1, .k 91148616760886510127 263, .k 72062225475526410799 1, .k 1192899526618989103 1, .k 5696788617605366319 277, .k 2438138157797687855 1, .k 1424197156324721199 309, .k 847736404021297711 1, .k 559506027869585967 6175, .k 415390839793730095 1, .k 343333245755802159 203, .k 284842525693002287 1, .k 85833120088801839 980, .k 54307922697208367 1, .k 18279125678244399 909, .k 91395628383027759 1, .k 73116502706045487 8, .k 18279125676510767 1, .k 18279125676511791 32801, .k 31789924558623279 1, .k 4768326794400303 48275, .k 2393381678404143 1, .k 152576980996655 1, .k 302110562374191 77415, .k 161373074018863 1, .k 91004329841199 876511, .k 55819957752367 1, .k 38227771707951 1737322, .k 20635585663535 1, .k 11839492641327 38203784, .k 9640469385775 1, .k 8540957757999 27434495, .k 5242422874671 42087863, .k 3043399619119 1, .k 1943887991343 73686092, .k 569498456623 1, .k 157181596207 1, .k 191541334575 475716378, .k 122821857839 1, .k 88462119471 13551424202, .k 140001727023 1, .k 36922511919 505632912192, .k 19742642735 1, .k 11152708143 24723210206458, .z 9034176083, .d 1, .z 529633014, .d 2, .d 1, .k 2788177035 1996940221844, .k 1377121419 1, .k 88216715 1, .k 174285963 20806419974146, .k 140731531 1, .k 123954315 57901138422180, .k 73622667 37610989893458, .k 40068235 1, .k 23291019 30716371615732, .k 14902411 1, .k 10708107 305490132233582, .k 23291019 1, .k 16999563 270647459772345, .k 16082059 1, .k 95371 1, .k 1098891 139989328324157, .k 443531 1, .k 103563 1, .k 128139 781492533683413, .k 111755 1, .k 66699 271475135198707, .k 58507 1, .k 54411 48671766179730583, .k 66699 1, .k 42123 94767307651599602, .k 54411 1, .k 29835 331887753716974115, .k 17547 744220640956988995, .k 9355 1, .k 5259 382904836146532053728, .k 3211 1, .k 2187 210157523808992004318, .k 1931 1, .k 651 2160111270177901513702, .k 523 1, .k 459 660481848050345900758, .z 87, .d 1, .z 92, .d 2, .d 1, .k 114 9040449275367983386986, .k 66 906038693021585505429, .k 41 1, .k 15 6063759545596197098728, .k 7 1, .k 3 30646279106479104971761, .k 1 1, .k 0 1009331069384952120084451, .d 2], false⟩
def ckpt19 : RleFullState := ⟨.B, .clean 0 [(1458377920713809791170, 5), (3694956449174813214914, 1), (5833511682824465090754, 6), (21444367509237466466498, 1), (23334046731296077318338, 8), (49875092655011876899010, 1), (93336186925184309856450, 8), (168419010827720965721738, 1), (373344747700737239425806, 41), (881340849780278269453070, 1), (1493378990802948957713166, 6), (238793869156889875041269, 1)] 15055021459752708992062684, [.z 1, .k 991443638224688056511 1, .k 364594467043546040511 263, .k 288248901902105643199 1, .k 4771598106475956415 1, .k 22787154470421465279 277, .k 9752552631190751423 1, .k 5696788625298884799 309, .k 3390945616085190847 1, .k 2238024111478343871 6175, .k 1661563359174920383 1, .k 1373332983023208639 203, .k 1139370102772009151 1, .k 343332480355207359 980, .k 217231690788833471 1, .k 73116502712977599 909, .k 365582513532111039 1, .k 292466010824181951 8, .k 73116502706043071 1, .k 73116502706047167 32801, .k 127159698234493119 1, .k 19073307177601215 48275, .k 9573526713616575 1, .k 610307923986623 1, .k 1208442249496767 77415, .k 645492296075455 1, .k 364017319364799 876511, .k 223279831009471 1, .k 152911086831807 1737322, .k 82542342654143 1, .k 47357970565311 38203784, .k 38561877543103 1, .k 34163831031999 27434495, .k 20969691498687 42087863, .k 12173598476479 1, .k 7775551965375 73686092, .k 2277993826495 1, .k 628726384831 1, .k 766165338303 475716378, .k 491287431359 1, .k 353848477887 13551424202, .k 560006908095 1, .k 147690047679 505632912192, .k 78970570943 1, .k 44610832575 26720150428303, .k 22033942719 1, .k 1411467455 1, .k 2788575423 20806419974146, .k 2251704511 1, .k 1983269055 57901138422180, .k 1177962687 37610989893458, .k 641091775 1, .k 372656319 30716371615732, .k 238438591 1, .k 171329727 305490132233582, .k 372656319 1, .k 271993023 270647459772345, .k 257312959 1, .k 1525951 1, .k 17582271 139989328324157, .k 7096511 1, .k 1657023 1, .k 2050239 781492533683413, .k 1788095 1, .k 1067199 271475135198707, .k 936127 1, .k 870591 48671766179730583, .k 1067199 1, .k 673983 94767307651599602, .k 870591 1, .k 477375 331887753716974115, .k 280767 744220640956988995, .k 149695 1, .k 84159 250678026022842983755, .z 13223, .d 1, .z 17733, .d 2, .d 1, .k 21039 132226810123689069972, .k 12847 1, .k 8751 210157523808992004318, .k 7727 1, .k 2607 1339642660836061927872, .z 1903, .d 1, .z 175, .d 2, .d 1, .k 651 820468609341839585829, .k 523 1, .k 459 660481848050345900758, .z 87, .d 1, .z 92, .d 2, .d 1, .k 114 9040449275367983386986, .k 66 906038693021585505429, .k 41 1, .k 15 6063759545596197098728, .k 7 1, .k 3 30646279106479104971761, .k 1 1, .k 0 1009331069384952120084451, .d 2], false⟩
def ckpt20 : RleFullState := ⟨.DR0, .clean 3350452636775556160219630 [(5973515963211795830852679, 1)] 0, [.d 1, .z 655765831609059917658261, .d 2, .d 1, .k 1493378990802948957713169 3, .k 881340849780278269453073 1, .k 373344747700737239425809 41, .k 168419010827720965721741 1, .k 93336186925184309856453 8, .k 49875092655011876899013 1, .k 23334046731296077318341 8, .k 21444367509237466466501 1, .k 5833511682824465090757 6, .k 3694956449174813214917 1, .k 1458377920713809791173 5, .k 991443638224688056517 1, .k 364594467043546040517 263, .k 288248901902105643205 1, .k 4771598106475956421 1, .k 22787154470421465285 277, .k 9752552631190751429 1, .k 5696788625298884805 309, .k 3390945616085190853 1, .k 2238024111478343877 6175, .k 1661563359174920389 1, .k 1373332983023208645 203, .k 1139370102772009157 1, .k 343332480355207365 980, .k 217231690788833477 1, .k 73116502712977605 909, .k 365582513532111045 1, .k 292466010824181957 8, .k 73116502706043077 1, .k 73116502706047173 32801, .k 127159698234493125 1, .k 19073307177601221 48275, .k 9573526713616581 1, .k 610307923986629 1, .k 1208442249496773 77415, .k 645492296075461 1, .k 364017319364805 876511, .k 223279831009477 1, .k 152911086831813 1737322, .k 82542342654149 1, .k 47357970565317 38203784, .k 38561877543109 1, .k 34163831032005 27434495, .k 20969691498693 42087863, .k 12173598476485 1, .k 7775551965381 73686092, .k 2277993826501 1, .k 628726384837 1, .k 766165338309 475716378, .k 491287431365 1, .k 353848477893 13551424202, .k 560006908101 1, .k 147690047685 505632912192, .k 78970570949 1, .k 44610832581 26720150428303, .k 22033942725 1, .k 1411467461 1, .k 2788575429 20806419974146, .k 2251704517 1, .k 1983269061 57901138422180, .k 1177962693 37610989893458, .k 641091781 1, .k 372656325 30716371615732, .k 238438597 1, .k 171329733 305490132233582, .k 372656325 1, .k 271993029 270647459772345, .k 257312965 1, .k 1525957 1, .k 17582277 139989328324157, .k 7096517 1, .k 1657029 1, .k 2050245 781492533683413, .k 1788101 1, .k 1067205 271475135198707, .k 936133 1, .k 870597 48671766179730583, .k 1067205 1, .k 673989 94767307651599602, .k 870597 1, .k 477381 331887753716974115, .k 280773 744220640956988995, .k 149701 1, .k 84165 250678026022842983755, .k 30959 1, .k 21042 132226810123689069972, .k 12850 1, .k 8754 210157523808992004318, .k 7730 1, .k 2610 2160111270177901513702, .k 2098 1, .k 1842 660481848050345900758, .k 354 1, .k 98 1, .k 120 9040449275367983386986, .k 72 906038693021585505429, .k 47 1, .k 21 6063759545596197098728, .k 13 1, .k 9 30646279106479104971761, .k 7 1, .k 6 1009331069384952120084451, .k 9 1, .k 3 7537176816673596729879973, .z 3, .d 2, .k 0 5622837964162795894755808, .d 2], false⟩
def ckpt21 : RleFullState := ⟨.B, .clean 0 [(199500370620047507596070, 1), (373344747700737239425830, 8), (673676043310883862886982, 1), (1493378990802948957703254, 41), (3525363399121113077812310, 1), (5973515963211795830852694, 1), (4077841947114872649806205, 1), (30330784257550770896743823, 1)] 64099495494153857246046294, [.z 1, .k 93336186925184309273379 8, .k 85777470036949865866019 1, .k 23334046731297860363043 6, .k 14779825796699252859683 1, .k 5833511682855239164707 5, .k 3965774552898752226083 1, .k 1458377868174184162083 263, .k 1152995607608422572835 1, .k 19086392425903825699 1, .k 91148617881685861155 277, .k 39010210524763005731 1, .k 22787154501195539235 309, .k 13563782464340763427 1, .k 8952096445913375523 6175, .k 6646253436699681571 1, .k 5493331932092834595 203, .k 4557480411088036643 1, .k 1373329921420829475 980, .k 868926763155333923 1, .k 292466010851910435 909, .k 1462330054128444195 1, .k 1169864043296727843 8, .k 292466010824172323 1, .k 292466010824188707 32801, .k 508638792937972515 1, .k 76293228710404899 48275, .k 38294106854466339 1, .k 2441231695946531 1, .k 4833768997987107 77415, .k 2581969184301859 1, .k 1456069277459235 876511, .k 893119324037923 1, .k 611644347327267 1737322, .k 330169370616611 1, .k 189431882261283 38203784, .k 154247510172451 1, .k 136655324128035 27434495, .k 83878765994787 42087863, .k 48694393905955 1, .k 31102207861539 73686092, .k 9111975306019 1, .k 2514905539363 1, .k 3064661353251 475716378, .k 1965149725475 1, .k 1415393911587 13551424202, .k 2240027632419 1, .k 590760190755 505632912192, .k 315882283811 1, .k 178443330339 26720150428303, .k 88135770915 1, .k 5645869859 1, .k 11154301731 20806419974146, .k 9006818083 1, .k 7933076259 57901138422180, .k 4711850787 37610989893458, .k 2564367139 1, .k 1490625315 30716371615732, .k 953754403 1, .k 685318947 305490132233582, .k 1490625315 1, .k 1087972131 270647459772345, .k 1029251875 1, .k 6103843 1, .k 70329123 139989328324157, .k 28386083 1, .k 6628131 1, .k 8200995 781492533683413, .k 7152419 1, .k 4268835 271475135198707, .k 3744547 1, .k 3482403 48671766179730583, .k 4268835 1, .k 2695971 94767307651599602, .k 3482403 1, .k 1909539 331887753716974115, .k 1123107 744220640956988995, .k 598819 1, .k 336675 183316884814105133485, .z 4611, .d 1, .z 83015, .d 2, .d 1, .k 84168 67361141208737850269, .k 30962 1, .k 21045 132226810123689069972, .k 12853 1, .k 8757 210157523808992004318, .k 7733 1, .k 2613 2160111270177901513702, .k 2101 1, .k 1845 660481848050345900758, .k 357 1, .k 101 1, .k 123 9040449275367983386986, .k 75 906038693021585505429, .k 50 1, .k 24 6063759545596197098728, .k 16 1, .k 12 30646279106479104971761, .k 10 1, .k 9 1009331069384952120084451, .k 12 1, .k 6 7537176816673596729879974, .k 3 5622837964162795894755808, .k 1 1, .k 0 350677999048999936096868, .d 2], false⟩
def ckpt22 : RleFullState := ⟨.B, .clean 0 [(10327876737207454, 1), (19335075991948446, 77415), (9764926783786142, 1), (153176427417865374, 1), (305172914841619614, 48275), (2034555171751890078, 1), (1169864043296754846, 32801), (1169864043296689310, 1), (4679456173186911390, 8), (5849320216513776798, 1), (1169864043407641758, 909), (3475707052621335710, 1), (5493319685683317918, 980), (18229921644352146590, 1), (21973327728371338398, 203), (26585013746798726302, 1), (35808385783653502110, 6175), (54255129857363053726, 1), (91148618004782156958, 309), (156040842099052022942, 1), (364594471526743444638, 277), (76345569703615302814, 1), (4611982430433690291358, 1), (5833511472696736648350, 263), (15863098211595008904350, 1), (23334046731420956658846, 5), (59119303186797011438750, 1), (93336186925191441452190, 6), (343109880147799463464094, 1), (373344747700737237093534, 8), (798001482480190030384286, 1), (1493378990802948957703326, 8), (2694704173243535451547934, 1), (5973515963211795830813022, 39), (1008446010376755498611593, 1), (79441119245360645315222863, 1), (95576255411388733293008319, 1), (225623257543751236979987903, 1)] 186568608184041045983706888, [.z 1, .k 5824277109836955 876511, .k 3572477296151707 1, .k 2446577389309083 1737322, .k 1320677482466459 1, .k 757727529045147 38203784, .k 616990040689819 1, .k 546621296512155 27434495, .k 335515063979163 42087863, .k 194777575623835 1, .k 124408831446171 73686092, .k 36447901224091 1, .k 10059622157467 1, .k 12258645413019 475716378, .k 7860598901915 1, .k 5661575646363 13551424202, .k 8960110529691 1, .k 2363040763035 505632912192, .k 1263529135259 1, .k 713773321371 26720150428303, .k 352543083675 1, .k 22583479451 1, .k 44617206939 20806419974146, .k 36027272347 1, .k 31732305051 57901138422180, .k 18847403163 37610989893458, .k 10257468571 1, .k 5962501275 30716371615732, .k 3815017627 1, .k 2741275803 305490132233582, .k 5962501275 1, .k 4351888539 270647459772345, .k 4117007515 1, .k 24415387 1, .k 281316507 139989328324157, .k 113544347 1, .k 26512539 1, .k 32803995 781492533683413, .k 28609691 1, .k 17075355 271475135198707, .k 14978203 1, .k 13929627 48671766179730583, .k 17075355 1, .k 10783899 94767307651599602, .k 13929627 1, .k 7638171 331887753716974115, .k 4492443 744220640956988995, .k 2395291 1, .k 1346715 7072824145170092509, .z 1306319, .d 1, .z 10098, .d 2, .d 1, .k 336678 176244060668935040975, .k 87626 1, .k 84168 67361141208737850269, .k 30962 1, .k 21045 132226810123689069972, .k 12853 1, .k 8757 210157523808992004318, .k 7733 1, .k 2613 2160111270177901513702, .k 2101 1, .k 1845 660481848050345900758, .k 357 1, .k 101 1, .k 123 9040449275367983386986, .k 75 906038693021585505429, .k 50 1, .k 24 6063759545596197098728, .k 16 1, .k 12 30646279106479104971761, .k 10 1, .k 9 1009331069384952120084451, .k 12 1, .k 6 7537176816673596729879974, .k 3 5622837964162795894755808, .k 1 1, .k 0 64449988954827205067923847, .d 2], false⟩
def ckpt23 : RleFullState := ⟨.B, .clean 0 [(373344747700765765808766, 6), (1372439520591197853856382, 1), (1493378990802948948374142, 8), (3192005929920760121537150, 1), (5973515963211795830813310, 8), (10778816692974141806191742, 1), (23894063852847183323252094, 4), (11175430935936220053061213, 1), (203498126670575412323054095, 1), (382305021645554933172033471, 34), (64540544664112351911142015, 1)] 496571371956422102109863902, [.z 1, .k 236477212747188045755003 1, .k 93336186925683826635387 5, .k 63452392846380035617403 1, .k 23334045890786946593403 263, .k 18447929721734761165435 1, .k 305382278814461211259 1, .k 1458377886106973778555 277, .k 624163368396208091771 1, .k 364594472019128627835 309, .k 217020519429452214907 1, .k 143233543134614008443 6175, .k 106340054987194905211 1, .k 87893310913485353595 203, .k 72919686577408586363 1, .k 21973278742733271675 980, .k 13902828210485342843 1, .k 4679456173630567035 909, .k 23397280866055107195 1, .k 18717824692747645563 8, .k 4679456173186757243 1, .k 4679456173187019387 32801, .k 8138220687007560315 1, .k 1220691659366478459 48275, .k 612705709671461499 1, .k 39059707135144571 1, .k 77340303967793787 77415, .k 41311506948829819 1, .k 23297108439347835 876511, .k 14289909184606843 1, .k 9786309557236347 1737322, .k 5282709929865851 1, .k 3030910116180603 38203784, .k 2467960162759291 1, .k 2186485186048635 27434495, .k 1342060255916667 42087863, .k 779110302495355 1, .k 497635325784699 73686092, .k 145791604896379 1, .k 40238488629883 1, .k 49034581652091 475716378, .k 31442395607675 1, .k 22646302585467 13551424202, .k 35840442118779 1, .k 9452163052155 505632912192, .k 5054116541051 1, .k 2855093285499 26720150428303, .k 1410172334715 1, .k 90333917819 1, .k 178468827771 20806419974146, .k 144109089403 1, .k 126929220219 57901138422180, .k 75389612667 37610989893458, .k 41029874299 1, .k 23850005115 30716371615732, .k 15260070523 1, .k 10965103227 305490132233582, .k 23850005115 1, .k 17407554171 270647459772345, .k 16468030075 1, .k 97661563 1, .k 1125266043 139989328324157, .k 454177403 1, .k 106050171 1, .k 131215995 781492533683413, .k 114438779 1, .k 68301435 271475135198707, .k 59912827 1, .k 55718523 48671766179730583, .k 68301435 1, .k 43135611 94767307651599602, .k 55718523 1, .k 30552699 331887753716974115, .k 17969787 744220640956988995, .k 9581179 1, .k 5386875 7072824145170092509, .k 5265671 1, .k 1346715 176244060668935040975, .k 350507 1, .k 336675 67361141208737850269, .k 123851 1, .k 84183 132226810123689069972, .k 51415 1, .k 35031 210157523808992004318, .k 30935 1, .k 10455 2160111270177901513702, .k 8407 1, .k 7383 660481848050345900758, .k 1431 1, .k 407 1, .k 495 9040449275367983386986, .k 303 906038693021585505429, .k 203 1, .k 99 6063759545596197098728, .k 67 1, .k 51 30646279106479104971761, .k 43 1, .k 39 1009331069384952120084451, .k 51 1, .k 27 7537176816673596729879974, .k 15 5622837964162795894755808, .k 7 1, .k 3 39547083232249886800713772, .z 3, .d 3, .d 1, .k 0 211471505612303381071906273, .d 2], false⟩
def ckpt24 : RleFullState := ⟨.C, .raw [.z 1, .k 11175430935936220053061216 1, .k 203498126670575412323054098 1, .k 382305021645554933172033474 33, .k 188683387653217877438607425 1, .z 2], [.k 23894063852847183323252097 4, .k 10778816692974141806191745 1, .k 5973515963211795830813313 8, .k 3192005929920760121537153 1, .k 1493378990802948948374145 8, .k 1372439520591197853856385 1, .k 373344747700765765808769 6, .k 236477212747188045755009 1, .k 93336186925683826635393 5, .k 63452392846380035617409 1, .k 23334045890786946593409 263, .k 18447929721734761165441 1, .k 305382278814461211265 1, .k 1458377886106973778561 277, .k 624163368396208091777 1, .k 364594472019128627841 309, .k 217020519429452214913 1, .k 143233543134614008449 6175, .k 106340054987194905217 1, .k 87893310913485353601 203, .k 72919686577408586369 1, .k 21973278742733271681 980, .k 13902828210485342849 1, .k 4679456173630567041 909, .k 23397280866055107201 1, .k 18717824692747645569 8, .k 4679456173186757249 1, .k 4679456173187019393 32801, .k 8138220687007560321 1, .k 1220691659366478465 48275, .k 612705709671461505 1, .k 39059707135144577 1, .k 77340303967793793 77415, .k 41311506948829825 1, .k 23297108439347841 876511, .k 14289909184606849 1, .k 9786309557236353 1737322, .k 5282709929865857 1, .k 3030910116180609 38203784, .k 2467960162759297 1, .k 2186485186048641 27434495, .k 1342060255916673 42087863, .k 779110302495361 1, .k 497635325784705 73686092, .k 145791604896385 1, .k 40238488629889 1, .k 49034581652097 475716378, .k 31442395607681 1, .k 22646302585473 13551424202, .k 35840442118785 1, .k 9452163052161 505632912192, .k 5054116541057 1, .k 2855093285505 26720150428303, .k 1410172334721 1, .k 90333917825 1, .k 178468827777 20806419974146, .k 144109089409 1, .k 126929220225 57901138422180, .k 75389612673 37610989893458, .k 41029874305 1, .k 23850005121 30716371615732, .k 15260070529 1, .k 10965103233 305490132233582, .k 23850005121 1, .k 17407554177 270647459772345, .k 16468030081 1, .k 97661569 1, .k 1125266049 139989328324157, .k 454177409 1, .k 106050177 1, .k 131216001 781492533683413, .k 114438785 1, .k 68301441 271475135198707, .k 59912833 1, .k 55718529 48671766179730583, .k 68301441 1, .k 43135617 94767307651599602, .k 55718529 1, .k 30552705 331887753716974115, .k 17969793 744220640956988995, .k 9581185 1, .k 5386881 7072824145170092509, .k 5265677 1, .k 1346721 176244060668935040975, .k 350513 1, .k 336681 67361141208737850269, .k 123857 1, .k 84189 132226810123689069972, .k 51421 1, .k 35037 210157523808992004318, .k 30941 1, .k 10461 2160111270177901513702, .k 8413 1, .k 7389 660481848050345900758, .k 1437 1, .k 413 1, .k 501 9040449275367983386986, .k 309 906038693021585505429, .k 209 1, .k 105 6063759545596197098728, .k 73 1, .k 57 30646279106479104971761, .k 49 1, .k 45 1009331069384952120084451, .k 57 1, .k 33 7537176816673596729879974, .k 21 5622837964162795894755808, .k 13 1, .k 9 39547083232249886800713772, .k 5 1, .k 3 654276377082664764984814935, .k 6 1, .k 0 1615416730339319185619342344, .d 2], false⟩
def ckpt25 : RleFullState := ⟨.C, .raw [.z 1, .k 8 1, .k 12 39547083232249886800713772, .k 16 1, .k 24 5622837964162795894755808, .k 36 7537176816673596729879974, .k 60 1, .k 48 1009331069384952120084451, .k 52 1, .k 60 30646279106479104971761, .k 76 1, .k 108 6063759545596197098728, .k 212 1, .k 312 906038693021585505429, .k 504 9040449275367983386986, .k 416 1, .k 1440 1, .k 7392 660481848050345900758, .k 8416 1, .k 10464 2160111270177901513702, .k 30944 1, .k 35040 210157523808992004318, .k 51424 1, .k 84192 132226810123689069972, .k 123860 1, .k 336684 67361141208737850269, .k 350516 1, .k 1346724 176244060668935040975, .k 5265680 1, .k 5386884 7072824145170092509, .k 9581188 1, .k 17969796 744220640956988995, .k 30552708 331887753716974115, .k 55718532 1, .k 43135620 94767307651599602, .k 68301444 1, .k 55718532 48671766179730583, .k 59912836 1, .k 68301444 271475135198707, .k 114438788 1, .k 131216004 781492533683413, .k 106050180 1, .k 454177412 1, .k 1125266052 139989328324157, .k 97661572 1, .k 16468030084 1, .k 17407554180 270647459772345, .k 23850005124 1, .k 10965103236 305490132233582, .k 15260070532 1, .k 23850005124 30716371615732, .k 41029874308 1, .k 75389612676 37610989893458, .k 126929220228 57901138422180, .k 144109089412 1, .k 178468827780 20806419974146, .k 90333917828 1, .k 1410172334724 1, .k 2855093285508 26720150428303, .k 5054116541060 1, .k 9452163052164 505632912192, .k 35840442118788 1, .k 22646302585476 13551424202, .k 31442395607684 1, .k 49034581652100 475716378, .k 40238488629892 1, .k 145791604896388 1, .k 497635325784708 73686092, .k 779110302495364 1, .k 1342060255916676 42087863, .k 2186485186048644 27434495, .k 2467960162759300 1, .k 3030910116180612 38203784, .k 5282709929865860 1, .k 9786309557236356 1737322, .k 14289909184606852 1, .k 23297108439347844 876511, .k 41311506948829828 1, .k 77340303967793796 77415, .k 39059707135144580 1, .k 612705709671461508 1, .k 1220691659366478468 48275, .k 8138220687007560324 1, .k 4679456173187019396 32801, .k 4679456173186757252 1, .k 18717824692747645572 8, .k 23397280866055107204 1, .k 4679456173630567044 909, .k 13902828210485342852 1, .k 21973278742733271684 980, .k 72919686577408586372 1, .k 87893310913485353604 203, .k 106340054987194905220 1, .k 143233543134614008452 6175, .k 217020519429452214916 1, .k 364594472019128627844 309, .k 624163368396208091780 1, .k 1458377886106973778564 277, .k 305382278814461211268 1, .k 18447929721734761165444 1, .k 23334045890786946593412 263, .k 63452392846380035617412 1, .k 93336186925683826635396 5, .k 236477212747188045755012 1, .k 373344747700765765808772 6, .k 1372439520591197853856388 1, .k 1493378990802948948374148 8, .k 3192005929920760121537156 1, .k 5973515963211795830813316 8, .k 10778816692974141806191748 1, .k 23894063852847183323252100 4, .k 11175430935936220053061219 1, .k 203498126670575412323054101 1, .k 382305021645554933172033477 8, .k 1013794301274773318438677685 1, .k 1529220086582219732688133914 20, .k 675721609186964657037331737 1, .k 13655975638324081210412834831 1, .z 2], [.k 6 654276377082664764984814935, .k 9 1, .k 3 1615416730339319185619342344, .k 6 1, .k 0 16465867215987836222342532113, .d 2], false⟩
def ckpt26 : RleFullState := ⟨.B, .clean 0 [(38324758, 1), (71879190, 744220640956988995), (122210838, 331887753716974115), (222874134, 1), (172542486, 94767307651599602), (273205782, 1), (222874134, 48671766179730583), (239651350, 1), (273205782, 271475135198707), (457755158, 1), (524864022, 781492533683413), (424200726, 1), (1816709654, 1), (4501064214, 139989328324157), (390646294, 1), (65872120342, 1), (69630216726, 270647459772345), (95400020502, 1), (43860412950, 305490132233582), (61040282134, 1), (95400020502, 30716371615732), (164119497238, 1), (301558450710, 37610989893458), (507716880918, 57901138422180), (576436357654, 1), (713875311126, 20806419974146), (361335671318, 1), (5640689338902, 1), (11420373142038, 26720150428303), (20216466164246, 1), (37808652208662, 505632912192), (143361768475158, 1), (90585210341910, 13551424202), (125769582430742, 1), (196138326608406, 475716378), (160953954519574, 1), (583166419585558, 1), (1990541303138838, 73686092), (3116441209981462, 1), (5368241023666710, 42087863), (8745940744194582, 27434495), (9871840651037206, 1), (12123640464722454, 38203784), (21130839719463446, 1), (39145238228945430, 1737322), (57159636738427414, 1), (93188433757391382, 876511), (165246027795319318, 1), (309361215871175190, 77415), (156238828540578326, 1), (2450822838685846038, 1), (4882766637465913878, 48275), (32552882748030241302, 1), (18717824692748077590, 32801), (18717824692747029014, 1), (74871298770990582294, 8), (93589123464220428822, 1), (18717824694522268182, 909), (55611312841941371414, 1), (87893114970933086742, 980), (291678746309634345494, 1), (351573243653941414422, 203), (425360219948779620886, 1), (572934172538456033814, 6175), (868082077717808859670, 1), (1458377888076514511382, 309), (2496653473584832367126, 1), (5833511544427895114262, 277), (1221529115257844845078, 1), (73791718886939044661782, 1), (93336183563147786373654, 263), (253809571385520142469654, 1), (373344747702735306541590, 5), (945908850988752183020054, 1), (1493378990803063063235094, 6), (5489758082364791415425558, 1), (5973515963211795793496598, 8), (12768023719683040486148630, 1), (23894063852847183323253270, 8), (43115266771896567224766998, 1), (95576255411388733293008406, 4), (44701723743744880212244882, 1), (813992506682301649292216410, 1), (1529220086582219732688133914, 8), (4055177205099093273754710746, 1), (6116880346328878930752535662, 18), (4125101382414181977057090465, 1), (31868463422635151259127123151, 1)] 65435448299066268516239561257, [.z 1, .k 21547539 7072824145170092509, .k 21062723 1, .k 5386899 176244060668935040975, .k 1402067 1, .k 1346739 67361141208737850269, .k 495443 1, .k 336771 132226810123689069972, .k 205699 1, .k 140163 210157523808992004318, .k 123779 1, .k 41859 2160111270177901513702, .k 33667 1, .k 29571 660481848050345900758, .k 5763 1, .k 1667 1, .k 2019 9040449275367983386986, .k 1251 906038693021585505429, .k 851 1, .k 435 6063759545596197098728, .k 307 1, .k 243 30646279106479104971761, .k 211 1, .k 195 1009331069384952120084451, .k 243 1, .k 147 7537176816673596729879974, .k 99 5622837964162795894755808, .k 67 1, .k 51 39547083232249886800713772, .k 35 1, .k 27 538559066387679221350882238, .z 23, .d 1, .d 2, .d 1, .k 6 115717310694985543633932696, .k 9 1, .k 3 1615416730339319185619342344, .k 6 1, .k 0 16465867215987836222342532113, .d 2], false⟩
def ckpt27 : RleFullState := ⟨.C, .raw [.z 1, .k 23648772456989779240118874788 1, .k 24467521385315515723010142654 11, .k 23901347566976363444345342365 1, .k 9058781093426436458636804623 1, .k 391480342165048251568162282431 1, .z 2], [.k 6116880346328878930752535662 3, .k 4055177205099093273754710746 1, .k 1529220086582219732688133914 8, .k 813992506682301649292216410 1, .k 44701723743744880212244882 1, .k 95576255411388733293008406 4, .k 43115266771896567224766998 1, .k 23894063852847183323253270 8, .k 12768023719683040486148630 1, .k 5973515963211795793496598 8, .k 5489758082364791415425558 1, .k 1493378990803063063235094 6, .k 945908850988752183020054 1, .k 373344747702735306541590 5, .k 253809571385520142469654 1, .k 93336183563147786373654 263, .k 73791718886939044661782 1, .k 1221529115257844845078 1, .k 5833511544427895114262 277, .k 2496653473584832367126 1, .k 1458377888076514511382 309, .k 868082077717808859670 1, .k 572934172538456033814 6175, .k 425360219948779620886 1, .k 351573243653941414422 203, .k 291678746309634345494 1, .k 87893114970933086742 980, .k 55611312841941371414 1, .k 18717824694522268182 909, .k 93589123464220428822 1, .k 74871298770990582294 8, .k 18717824692747029014 1, .k 18717824692748077590 32801, .k 32552882748030241302 1, .k 4882766637465913878 48275, .k 2450822838685846038 1, .k 156238828540578326 1, .k 309361215871175190 77415, .k 165246027795319318 1, .k 93188433757391382 876511, .k 57159636738427414 1, .k 39145238228945430 1737322, .k 21130839719463446 1, .k 12123640464722454 38203784, .k 9871840651037206 1, .k 8745940744194582 27434495, .k 5368241023666710 42087863, .k 3116441209981462 1, .k 1990541303138838 73686092, .k 583166419585558 1, .k 160953954519574 1, .k 196138326608406 475716378, .k 125769582430742 1, .k 90585210341910 13551424202, .k 143361768475158 1, .k 37808652208662 505632912192, .k 20216466164246 1, .k 11420373142038 26720150428303, .k 5640689338902 1, .k 361335671318 1, .k 713875311126 20806419974146, .k 576436357654 1, .k 507716880918 57901138422180, .k 301558450710 37610989893458, .k 164119497238 1, .k 95400020502 30716371615732, .k 61040282134 1, .k 43860412950 305490132233582, .k 95400020502 1, .k 69630216726 270647459772345, .k 65872120342 1, .k 390646294 1, .k 4501064214 139989328324157, .k 1816709654 1, .k 424200726 1, .k 524864022 781492533683413, .k 457755158 1, .k 273205782 271475135198707, .k 239651350 1, .k 222874134 48671766179730583, .k 273205782 1, .k 172542486 94767307651599602, .k 222874134 1, .k 122210838 331887753716974115, .k 71879190 744220640956988995, .k 38324758 1, .k 21547542 7072824145170092509, .k 21062726 1, .k 5386902 176244060668935040975, .k 1402070 1, .k 1346742 67361141208737850269, .k 495446 1, .k 336774 132226810123689069972, .k 205702 1, .k 140166 210157523808992004318, .k 123782 1, .k 41862 2160111270177901513702, .k 33670 1, .k 29574 660481848050345900758, .k 5766 1, .k 1670 1, .k 2022 9040449275367983386986, .k 1254 906038693021585505429, .k 854 1, .k 438 6063759545596197098728, .k 310 1, .k 246 30646279106479104971761, .k 214 1, .k 198 1009331069384952120084451, .k 246 1, .k 150 7537176816673596729879974, .k 102 5622837964162795894755808, .k 70 1, .k 54 39547083232249886800713772, .k 38 1, .k 30 538559066387679221350882238, .k 23 1, .k 6 115717310694985543633932696, .k 9 1, .k 3 1615416730339319185619342344, .k 6 1, .k 0 274784465758569372306465281756, .d 2], false⟩
def ckpt28 : RleFullState := ⟨.C, .raw [.z 1, .k 84250910 1, .k 86190174 7072824145170092509, .k 153299038 1, .k 287516766 744220640956988995, .k 488843358 331887753716974115, .k 891496542 1, .k 690169950 94767307651599602, .k 1092823134 1, .k 891496542 48671766179730583, .k 958605406 1, .k 1092823134 271475135198707, .k 1831020638 1, .k 2099456094 781492533683413, .k 1696802910 1, .k 7266838622 1, .k 18004256862 139989328324157, .k 1562585182 1, .k 263488481374 1, .k 278520866910 270647459772345, .k 381600082014 1, .k 175441651806 305490132233582, .k 244161128542 1, .k 381600082014 30716371615732, .k 656477988958 1, .k 1206233802846 37610989893458, .k 2030867523678 57901138422180, .k 2305745430622 1, .k 2855501244510 20806419974146, .k 1445342685278 1, .k 22562757355614 1, .k 45681492568158 26720150428303, .k 80865864656990 1, .k 151234608834654 505632912192, .k 573447073900638 1, .k 362340841367646 13551424202, .k 503078329722974 1, .k 784553306433630 475716378, .k 643815818078302 1, .k 2332665678342238 1, .k 7962165212555358 73686092, .k 12465764839925854 1, .k 21472964094666846 42087863, .k 34983762976778334 27434495, .k 39487362604148830 1, .k 48494561858889822 38203784, .k 84523358877853790 1, .k 156580952915781726 1737322, .k 228638546953709662 1, .k 372753735029565534 876511, .k 660984111181277278 1, .k 1237444863484700766 77415, .k 624955314162313310 1, .k 9803291354743384158 1, .k 19531066549863655518 48275, .k 130211530992120965214 1, .k 74871298770992310366 32801, .k 74871298770988116062 1, .k 299485195083962329182 8, .k 374356493856881715294 1, .k 74871298778089072734 909, .k 222445251367765485662 1, .k 351572459883732346974 980, .k 1166714985238537381982 1, .k 1406292974615765657694 203, .k 1701440879795118483550 1, .k 2291736690153824135262 6175, .k 3472328310871235438686 1, .k 5833511552306058045534 309, .k 9986613894339329468510 1, .k 23334046177711580457054 277, .k 4886116461031379380318 1, .k 295166875547756178647134 1, .k 373344734252591145494622 263, .k 1015238285542080569878622 1, .k 1493378990810941226166366 5, .k 3783635403955008732080222 1, .k 5973515963212252252940382 6, .k 21959032329459165661702238 1, .k 23894063852847183173986398 8, .k 51072094878732161944594526 1, .k 95576255411388733293013086 8, .k 172461067087586268899067998 1, .k 382305021645554933172033630 4, .k 178806894974979520848979534 1, .k 3255970026729206597168865646 1, .k 6116880346328878930752535662 8, .k 16220708820396373095018842990 1, .k 24467521385315515723010142654 3, .k 94595089827959116960475499158 1, .k 97870085541262062892040570622 10, .k 84770102688050279165780284597 1, .k 209599725651388539620164576399 1, .z 2], [.k 21547614 176244060668935040975, .k 5608286 1, .k 5386974 67361141208737850269, .k 1981790 1, .k 1347102 132226810123689069972, .k 822814 1, .k 560670 210157523808992004318, .k 495134 1, .k 167454 2160111270177901513702, .k 134686 1, .k 118302 660481848050345900758, .k 23070 1, .k 6686 1, .k 8094 9040449275367983386986, .k 5022 906038693021585505429, .k 3422 1, .k 1758 6063759545596197098728, .k 1246 1, .k 990 30646279106479104971761, .k 862 1, .k 798 1009331069384952120084451, .k 990 1, .k 606 7537176816673596729879974, .k 414 5622837964162795894755808, .k 286 1, .k 222 39547083232249886800713772, .k 158 1, .k 126 538559066387679221350882238, .k 98 1, .k 30 115717310694985543633932696, .k 42 1, .k 18 1615416730339319185619342344, .k 30 1, .k 6 274784465758569372306465281757, .k 4 1, .k 3 507674404248318560861238978904, .k 6 1, .k 0 310082422187222332587029916226, .d 2], false⟩
def ckpt29 : RleFullState := ⟨.B, .clean 0 [(85891856378667387, 42087863), (139935051907113339, 27434495), (157949450416595323, 1), (193978247435559291, 38203784), (338093435511415163, 1), (626323811663126907, 1737322), (914554187814838651, 1), (1491014940118262139, 876511), (2643936444725109115, 1), (4949779453938803067, 77415), (2499821256649253243, 1), (39213165418973536635, 1), (78124266199454622075, 48275), (520846123968483860859, 1), (299485195083969241467, 32801), (299485195083952464251, 1), (1197940780335849316731, 8), (1497425975427526861179, 1), (299485195112356290939, 909), (889781005471061942651, 1), (1406289839534929387899, 980), (4666859940954149527931, 1), (5625171898463062630779, 203), (6805763519180473934203, 1), (9166946760615296541051, 6175), (13889313243484941754747, 1), (23334046209224232182139, 309), (39946455577357317874043, 1), (93336184710846321828219, 277), (19544465844125517521275, 1), (1180667502191024714588539, 1), (1493378937010364581978491, 263), (4060953142168322279514491, 1), (5973515963243764904665467, 5), (15134541615820034928320891, 1), (23894063852849009011761531, 6), (87836129317836662646808955, 1), (95576255411388732695945595, 8), (204288379514928647778378107, 1), (382305021645554933172052347, 8), (689844268350345075596271995, 1), (1529220086582219732688134523, 4), (715227579899918083395918139, 1), (13023880106916826388675462587, 1), (24467521385315515723010142651, 8), (64882835281585492380075371963, 1), (97870085541262062892040570619, 3), (378380359311836467841901996635, 1), (391480342165048251568162282491, 4), (1047624100882708554382289380343, 1), (1565921368660193006272649129979, 2), (628799176954165618860493729207, 1), (14993955067296438198594486412351, 1)] 13209524612601372991514644324363, [.d 1, .d 1, .k 12465764839925854 1, .k 7962165212555358 73686092, .k 2332665678342238 1, .k 643815818078302 1, .k 784553306433630 475716378, .k 503078329722974 1, .k 362340841367646 13551424202, .k 573447073900638 1, .k 151234608834654 505632912192, .k 80865864656990 1, .k 45681492568158 26720150428303, .k 22562757355614 1, .k 1445342685278 1, .k 2855501244510 20806419974146, .k 2305745430622 1, .k 2030867523678 57901138422180, .k 1206233802846 37610989893458, .k 656477988958 1, .k 381600082014 30716371615732, .k 244161128542 1, .k 175441651806 305490132233582, .k 381600082014 1, .k 278520866910 270647459772345, .k 263488481374 1, .k 1562585182 1, .k 18004256862 139989328324157, .k 7266838622 1, .k 1696802910 1, .k 2099456094 781492533683413, .k 1831020638 1, .k 1092823134 271475135198707, .k 958605406 1, .k 891496542 48671766179730583, .k 1092823134 1, .k 690169950 94767307651599602, .k 891496542 1, .k 488843358 331887753716974115, .k 287516766 744220640956988995, .k 153299038 1, .k 86190174 7072824145170092509, .k 84250910 1, .k 21547614 176244060668935040975, .k 5608286 1, .k 5386974 67361141208737850269, .k 1981790 1, .k 1347102 132226810123689069972, .k 822814 1, .k 560670 210157523808992004318, .k 495134 1, .k 167454 2160111270177901513702, .k 134686 1, .k 118302 660481848050345900758, .k 23070 1, .k 6686 1, .k 8094 9040449275367983386986, .k 5022 906038693021585505429, .k 3422 1, .k 1758 6063759545596197098728, .k 1246 1, .k 990 30646279106479104971761, .k 862 1, .k 798 1009331069384952120084451, .k 990 1, .k 606 7537176816673596729879974, .k 414 5622837964162795894755808, .k 286 1, .k 222 39547083232249886800713772, .k 158 1, .k 126 538559066387679221350882238, .k 98 1, .k 30 115717310694985543633932696, .k 42 1, .k 18 1615416730339319185619342344, .k 30 1, .k 6 274784465758569372306465281757, .k 4 1, .k 3 507674404248318560861238978904, .k 6 1, .k 0 2504802967801580957720172775388, .d 2], false⟩
def ckpt30 : RleFullState := ⟨.C, .raw [.z 1, .k 817153518059714591113512431 1, .k 1529220086582219732688209391 8, .k 2759377073401380302385087983 1, .k 6116880346328878930752538095 4, .k 2860910319599672333583672559 1, .k 52095520427667305554701850351 1, .k 97870085541262062892040570607 8, .k 259531341126341969520301487855 1, .k 391480342165048251568162282479 3, .k 1513521437247345871367607986543 1, .k 1565921368660193006272649129967 4, .k 4190496403530834217529157521375 1, .k 6263685474640772025090596519919 2, .k 2515196707816662475441974916831 1, .z 2], [.k 382305021645554930783782383 8, .k 351344517271346650587235823 1, .k 95576255411396036047046127 6, .k 60538166463280139713283567 1, .k 23894063852975059618661871 5, .k 16243812568673289118057967 1, .k 5973515748041458327913967 263, .k 4722670008764098858354159 1, .k 78177863376502070085103 1, .k 373344738843385287312879 277, .k 159785822309429271496175 1, .k 93336184836896928728559 309, .k 55557252973939767018991 1, .k 36667787042461186164207 6175, .k 27223054076721895736815 1, .k 22500687593852250523119 203, .k 18667439763816598111727 1, .k 5625159358139717551599 980, .k 3559124021884247770607 1, .k 1197940780449425163759 909, .k 5989703901710107444719 1, .k 4791763121343397266927 8, .k 1197940780335809857007 1, .k 1197940780335876965871 32801, .k 2083384495873935443439 1, .k 312497064797818488303 48275, .k 156852661675894146543 1, .k 9999285026597012975 1, .k 19799117815755212271 77415, .k 10575745778900436463 1, .k 5964059760473048559 876511, .k 3658216751259354607 1, .k 2505295246652507631 1737322, .k 1352373742045660655 1, .k 775912989742237167 38203784, .k 631797801666381295 1, .k 559740207628453359 27434495, .k 343567425514669551 42087863, .k 199452237438813679 1, .k 127394643400885743 73686092, .k 37322650853475823 1, .k 10301053089252847 1, .k 12552852902938095 475716378, .k 8049253275567599 1, .k 5797453461882351 13551424202, .k 9175153182410223 1, .k 2419753741354479 505632912192, .k 1293853834511855 1, .k 730903881090543 26720150428303, .k 361004117689839 1, .k 23125482964463 1, .k 45688019912175 20806419974146, .k 36891926889967 1, .k 32493880378863 57901138422180, .k 19299740845551 37610989893458, .k 10503647823343 1, .k 6105601312239 30716371615732, .k 3906578056687 1, .k 2807066428911 305490132233582, .k 6105601312239 1, .k 4456333870575 270647459772345, .k 4215815701999 1, .k 25001362927 1, .k 288068109807 139989328324157, .k 116269417967 1, .k 27148846575 1, .k 33591297519 781492533683413, .k 29296330223 1, .k 17485170159 271475135198707, .k 15337686511 1, .k 14263944687 48671766179730583, .k 17485170159 1, .k 11042719215 94767307651599602, .k 14263944687 1, .k 7821493743 331887753716974115, .k 4600268271 744220640956988995, .k 2452784623 1, .k 1379042799 7072824145170092509, .k 1348014575 1, .k 344761839 176244060668935040975, .k 89732591 1, .k 86191599 67361141208737850269, .k 31708655 1, .k 21553647 132226810123689069972, .k 13165039 1, .k 8970735 210157523808992004318, .k 7922159 1, .k 2679279 2160111270177901513702, .k 2154991 1, .k 1892847 660481848050345900758, .k 369135 1, .k 106991 1, .k 129519 9040449275367983386986, .k 80367 906038693021585505429, .k 54767 1, .k 28143 6063759545596197098728, .k 19951 1, .k 15855 30646279106479104971761, .k 13807 1, .k 12783 1009331069384952120084451, .k 15855 1, .k 9711 7537176816673596729879974, .k 6639 5622837964162795894755808, .k 4591 1, .k 3567 39547083232249886800713772, .k 2543 1, .k 2031 538559066387679221350882238, .k 1583 1, .k 495 115717310694985543633932696, .k 687 1, .k 303 1615416730339319185619342344, .k 495 1, .k 111 274784465758569372306465281757, .k 79 1, .k 63 507674404248318560861238978904, .k 111 1, .k 15 2504802967801580957720172775389, .k 7 1, .k 3 6623541416857744891568440848885, .k 1 1, .k 0 4682218824069723167996109957596, .d 2], false⟩
def ckpt31 : RleFullState := ⟨.C, .raw [.z 1, .k 51147 1009331069384952120084451, .k 55243 1, .k 63435 30646279106479104971761, .k 79819 1, .k 112587 6063759545596197098728, .k 219083 1, .k 321483 906038693021585505429, .k 518091 9040449275367983386986, .k 427979 1, .k 1476555 1, .k 7571403 660481848050345900758, .k 8619979 1, .k 10717131 2160111270177901513702, .k 31688651 1, .k 35882955 210157523808992004318, .k 52660171 1, .k 86214603 132226810123689069972, .k 126834635 1, .k 344766411 67361141208737850269, .k 358930379 1, .k 1379047371 176244060668935040975, .k 5392058315 1, .k 5516171211 7072824145170092509, .k 9811138507 1, .k 18401073099 744220640956988995, .k 31285974987 331887753716974115, .k 57055778763 1, .k 44170876875 94767307651599602, .k 69940680651 1, .k 57055778763 48671766179730583, .k 61350746059 1, .k 69940680651 271475135198707, .k 117185320907 1, .k 134365190091 781492533683413, .k 108595386315 1, .k 465077671883 1, .k 1152272439243 139989328324157, .k 100005451723 1, .k 16863262808011 1, .k 17825335482315 270647459772345, .k 24422405248971 1, .k 11228265715659 305490132233582, .k 15626312226763 1, .k 24422405248971 30716371615732, .k 42014591293387 1, .k 77198963382219 37610989893458, .k 129975521515467 57901138422180, .k 147567707559883 1, .k 182752079648715 20806419974146, .k 92501931857867 1, .k 1444016470759371 1, .k 2923615524362187 26720150428303, .k 5175415338047435 1, .k 9679014965417931 505632912192, .k 36700612729640907 1, .k 23189813847529419 13551424202, .k 32197013102270411 1, .k 50211411611752395 475716378, .k 41204212357011403 1, .k 149290603413903307 1, .k 509578573603542987 73686092, .k 797808949755254731 1, .k 1374269702058678219 42087863, .k 2238960830513813451 27434495, .k 2527191206665525195 1, .k 3103651958968948683 38203784, .k 5409494968182642635 1, .k 10021180986610030539 1737322, .k 14632867005037418443 1, .k 23856239041892194251 876511, .k 42302983115601745867 1, .k 79196471263020849099 77415, .k 39997140106388051915 1, .k 627410646703576586187 1, .k 1249988259191273953227 48275, .k 8333537983495741773771 1, .k 4791763121343507863499 32801, .k 4791763121343239428043 1, .k 19167052485373589067723 8, .k 23958815606840429778891 1, .k 4791763121797700655051 909, .k 14236496087536991082443 1, .k 22500637432558870206411 980, .k 74669759055266392446923 1, .k 90002750375409002092491 203, .k 108892216306887582947275 1, .k 146671148169844744656843 6175, .k 222229011895759068075979 1, .k 373344739347587714914251 309, .k 639143289237717085984715 1, .k 1493378955373541149251531 277, .k 312711453506008280340427 1, .k 18890680035056395433416651 1, .k 23894062992165833311655883 263, .k 64975250274693156472231883 1, .k 95576255411900238474647499 5, .k 242152665853120558853134283 1, .k 382305021645584144188184523 6, .k 1405378069085386602348943307 1, .k 1529220086582219723135129547 8, .k 3268614072238858364454049739 1, .k 6116880346328878930752837579 8, .k 11037508293605521209540351947 1, .k 24467521385315515723010152395 4, .k 11443641278398689334334690251 1, .k 208382081710669222218807401419 1, .k 391480342165048251568162282443 8, .k 1038125364505367878081205951435 1, .k 1565921368660193006272649129931 3, .k 6054085748989383485470431946187 1, .k 6263685474640772025090596519883 4, .k 16761985614123336870116630085515 1, .k 19927123303326226495421073157383 1, .z 2], [.k 63435 1, .k 38859 7537176816673596729879974, .k 26571 5622837964162795894755808, .k 18379 1, .k 14283 39547083232249886800713772, .k 10187 1, .k 8139 538559066387679221350882238, .k 6347 1, .k 1995 115717310694985543633932696, .k 2763 1, .k 1227 1615416730339319185619342344, .k 1995 1, .k 459 274784465758569372306465281757, .k 331 1, .k 267 128723518072833641550810162476, .z 179, .d 1, .z 21, .d 2, .d 1, .k 66 378950886175484919310428816427, .k 114 1, .k 18 2504802967801580957720172775389, .k 10 1, .k 6 6623541416857744891568440848885, .k 4 1, .k 3 4682218824069723167996109957596, .k 6 1, .k 0 55441261562108557701024616361622, .d 2], false⟩
def ckpt32 : RleFullState := ⟨.BR, .clean 2 [(130239, 132694352800547924806202579), (163007, 1), (228543, 39547083232249886800713772), (294079, 1), (425151, 5622837964162795894755808), (621759, 7537176816673596729879974), (1014975, 1), (818367, 1009331069384952120084451), (883903, 1), (1014975, 30646279106479104971761), (1277119, 1), (1801407, 6063759545596197098728), (3505343, 1), (5143743, 906038693021585505429), (8289471, 9040449275367983386986), (6847679, 1), (23624895, 1), (121142463, 660481848050345900758), (137919679, 1), (171474111, 2160111270177901513702), (507018431, 1), (574127295, 210157523808992004318), (842562751, 1), (1379433663, 132226810123689069972), (2029354175, 1), (5516262591, 67361141208737850269), (5742886079, 1), (22064757951, 176244060668935040975), (86272933055, 1), (88258739391, 7072824145170092509), (156978216127, 1), (294417169599, 744220640956988995), (500575599807, 331887753716974115), (912892460223, 1), (706734030015, 94767307651599602), (1119050890431, 1), (912892460223, 48671766179730583), (981611936959, 1), (1119050890431, 271475135198707), (1874965134527, 1), (2149843041471, 781492533683413), (1737526181055, 1), (7441242750143, 1), (18436359027903, 139989328324157), (1600087227583, 1), (269812204928191, 1), (285205367717055, 270647459772345), (390758483983551, 1), (179652251450559, 305490132233582), (250020995628223, 1), (390758483983551, 30716371615732), (672233460694207, 1), (1235183414115519, 37610989893458), (2079608344247487, 57901138422180), (2361083320958143, 1), (2924033274379455, 20806419974146), (1480030909725887, 1), (23104263532149951, 1), (46777848389795007, 26720150428303), (82806645408758975, 1), (154864239446686911, 505632912192), (587209803674254527, 1), (371037021560470719, 13551424202), (515152209636326591, 1), (803382585788038335, 475716378), (659267397712182463, 1), (2388649654622452927, 1), (8153257177656687807, 73686092), (12764943196084075711, 1), (21988315232938851519, 42087863), (35823373288221015231, 27434495), (40435059306648403135, 1), (49658431343503178943, 38203784), (86551919490922282175, 1), (160338895785760488639, 1737322), (234125872080598695103, 1), (381699824670275108031, 876511), (676847729849627933887, 1), (1267143540208333585599, 77415), (639954241702208830655, 1), (10038570347257225379007, 1), (19999812147060383251647, 48275), (133336607735931868380351, 1), (76668209941496125815999, 32801), (76668209941491830848703, 1), (306672839765977425083583, 8), (383341049709446876462271, 1), (76668209948763210480831, 909), (227783937400591857319103, 1), (360010198920941923302591, 980), (1194716144884262279150783, 1), (1440044006006544033479871, 203), (1742275460910201327156415, 1), (2346738370717515914509503, 6175), (3555664190332145089215679, 1), (5973515829561403438628031, 309), (10226292627803473375755455, 1), (23894063285976658388024511, 277), (5003383256096132485446847, 1), (302250880560902326934666431, 1), (382305007874653332986494143, 263), (1039604004395090503555710143, 1), (1529220086590403815594359999, 5), (3874442653649928941650148543, 1), (6116880346329346307010952383, 6), (22486049105366185637583092927, 1), (24467521385315515570162072767, 8), (52297825155821733831264795839, 1), (97870085541262062892045401279, 8), (176600132697688339352645631167, 1), (391480342165048251568162438335, 4), (183098260454379029349355044031, 1), (3334113307370707555500918422719, 1), (6263685474640772025090596519103, 8), (16610005832085886049299295222975, 1), (25054741898563088100362386078911, 3), (96865371983830135767526911139007, 1), (100218967594252352401449544318143, 4)] 29066290186058671976813203503904, [.d 1, .z 24259, .d 1, .z 2074, .d 2, .d 1, .k 8139 405864713587131296544679658, .k 6347 1, .k 1995 115717310694985543633932696, .k 2763 1, .k 1227 1615416730339319185619342344, .k 1995 1, .k 459 274784465758569372306465281757, .k 331 1, .k 267 128723518072833641550810162476, .z 179, .d 1, .z 21, .d 2, .d 1, .k 66 378950886175484919310428816427, .k 114 1, .k 18 2504802967801580957720172775389, .k 10 1, .k 6 6623541416857744891568440848885, .k 4 1, .k 3 4682218824069723167996109957596, .k 6 1, .k 0 55441261562108557701024616361622, .d 2], false⟩
def ckpt33 : RleFullState := ⟨.C, .raw [.z 1, .k 1529220086590403815594360002 5, .k 3874442653649928941650148546 1, .k 6116880346329346307010952386 6, .k 22486049105366185637583092930 1, .k 24467521385315515570162072770 8, .k 52297825155821733831264795842 1, .k 97870085541262062892045401282 8, .k 176600132697688339352645631170 1, .k 391480342165048251568162438338 4, .k 183098260454379029349355044034 1, .k 3334113307370707555500918422722 1, .k 6263685474640772025090596519106 8, .k 16610005832085886049299295222978 1, .k 25054741898563088100362386078914 3, .k 96865371983830135767526911139009 1, .k 15 1, .k 1603503481508037638423192709090303 2, .z 2], [.k 1039604004395090503555710146 1, .k 382305007874653332986494146 263, .k 302250880560902326934666434 1, .k 5003383256096132485446850 1, .k 23894063285976658388024514 277, .k 10226292627803473375755458 1, .k 5973515829561403438628034 309, .k 3555664190332145089215682 1, .k 2346738370717515914509506 6175, .k 1742275460910201327156418 1, .k 1440044006006544033479874 203, .k 1194716144884262279150786 1, .k 360010198920941923302594 980, .k 227783937400591857319106 1, .k 76668209948763210480834 909, .k 383341049709446876462274 1, .k 306672839765977425083586 8, .k 76668209941491830848706 1, .k 76668209941496125816002 32801, .k 133336607735931868380354 1, .k 19999812147060383251650 48275, .k 10038570347257225379010 1, .k 639954241702208830658 1, .k 1267143540208333585602 77415, .k 676847729849627933890 1, .k 381699824670275108034 876511, .k 234125872080598695106 1, .k 160338895785760488642 1737322, .k 86551919490922282178 1, .k 49658431343503178946 38203784, .k 40435059306648403138 1, .k 35823373288221015234 27434495, .k 21988315232938851522 42087863, .k 12764943196084075714 1, .k 8153257177656687810 73686092, .k 2388649654622452930 1, .k 659267397712182466 1, .k 803382585788038338 475716378, .k 515152209636326594 1, .k 371037021560470722 13551424202, .k 587209803674254530 1, .k 154864239446686914 505632912192, .k 82806645408758978 1, .k 46777848389795010 26720150428303, .k 23104263532149954 1, .k 1480030909725890 1, .k 2924033274379458 20806419974146, .k 2361083320958146 1, .k 2079608344247490 57901138422180, .k 1235183414115522 37610989893458, .k 672233460694210 1, .k 390758483983554 30716371615732, .k 250020995628226 1, .k 179652251450562 305490132233582, .k 390758483983554 1, .k 285205367717058 270647459772345, .k 269812204928194 1, .k 1600087227586 1, .k 18436359027906 139989328324157, .k 7441242750146 1, .k 1737526181058 1, .k 2149843041474 781492533683413, .k 1874965134530 1, .k 1119050890434 271475135198707, .k 981611936962 1, .k 912892460226 48671766179730583, .k 1119050890434 1, .k 706734030018 94767307651599602, .k 912892460226 1, .k 500575599810 331887753716974115, .k 294417169602 744220640956988995, .k 156978216130 1, .k 88258739394 7072824145170092509, .k 86272933058 1, .k 22064757954 176244060668935040975, .k 5742886082 1, .k 5516262594 67361141208737850269, .k 2029354178 1, .k 1379433666 132226810123689069972, .k 842562754 1, .k 574127298 210157523808992004318, .k 507018434 1, .k 171474114 2160111270177901513702, .k 137919682 1, .k 121142466 660481848050345900758, .k 23624898 1, .k 6847682 1, .k 8289474 9040449275367983386986, .k 5143746 906038693021585505429, .k 3505346 1, .k 1801410 6063759545596197098728, .k 1277122 1, .k 1014978 30646279106479104971761, .k 883906 1, .k 818370 1009331069384952120084451, .k 1014978 1, .k 621762 7537176816673596729879974, .k 425154 5622837964162795894755808, .k 294082 1, .k 228546 39547083232249886800713772, .k 163010 1, .k 130242 132694352800547924806202579, .k 97042 1, .k 2080 1, .k 8145 405864713587131296544679658, .k 6353 1, .k 2001 115717310694985543633932696, .k 2769 1, .k 1233 1615416730339319185619342344, .k 2001 1, .k 465 274784465758569372306465281757, .k 337 1, .k 273 128723518072833641550810162476, .k 203 1, .k 69 378950886175484919310428816427, .k 117 1, .k 21 2504802967801580957720172775389, .k 13 1, .k 9 6623541416857744891568440848885, .k 7 1, .k 6 4682218824069723167996109957596, .k 9 1, .k 3 84101906765581205227954746442331, .k 6 1, .k 0 302178618073084359382722201875135, .d 2], false⟩
def ckpt34 : RleFullState := ⟨.C, .raw [.z 1, .k 159 6623541416857744891568440848885, .k 223 1, .k 351 2504802967801580957720172775389, .k 1887 1, .k 1119 378950886175484919310428816427, .k 3263 1, .k 4383 128723518072833641550810162476, .k 5407 1, .k 7455 274784465758569372306465281757, .k 32031 1, .k 19743 1615416730339319185619342344, .k 44319 1, .k 32031 115717310694985543633932696, .k 101663 1, .k 130335 405864713587131296544679658, .k 33295 1, .k 1552687 1, .k 2083887 132694352800547924806202579, .k 2608175 1, .k 3656751 39547083232249886800713772, .k 4705327 1, .k 6802479 5622837964162795894755808, .k 9948207 7537176816673596729879974, .k 16239663 1, .k 13093935 1009331069384952120084451, .k 14142511 1, .k 16239663 30646279106479104971761, .k 20433967 1, .k 28822575 6063759545596197098728, .k 56085551 1, .k 82299951 906038693021585505429, .k 132631599 9040449275367983386986, .k 109562927 1, .k 377998383 1, .k 1938279471 660481848050345900758, .k 2206714927 1, .k 2743585839 2160111270177901513702, .k 8112294959 1, .k 9186036783 210157523808992004318, .k 13481004079 1, .k 22070938671 132226810123689069972, .k 32469666863 1, .k 88260201519 67361141208737850269, .k 91886177327 1, .k 353036127279 176244060668935040975, .k 1380366928943 1, .k 1412139830319 7072824145170092509, .k 2511651458095 1, .k 4710674713647 744220640956988995, .k 8009209596975 331887753716974115, .k 14606279363631 1, .k 11307744480303 94767307651599602, .k 17904814246959 1, .k 14606279363631 48671766179730583, .k 15705790991407 1, .k 17904814246959 271475135198707, .k 29999442152495 1, .k 34397488663599 781492533683413, .k 27800418896943 1, .k 119059884002351 1, .k 294981744446511 139989328324157, .k 25601395641391 1, .k 4316995278851119 1, .k 4563285883472943 270647459772345, .k 6252135743736879 1, .k 2874436023209007 305490132233582, .k 4000335930051631 1, .k 6252135743736879 30716371615732, .k 10755735371107375 1, .k 19762934625848367 37610989893458, .k 33273733507959855 57901138422180, .k 37777333135330351 1, .k 46784532390071343 20806419974146, .k 23680494555614255 1, .k 369668216514399279 1, .k 748445574236720175 26720150428303, .k 1324906326540143663 1, .k 2477827831146990639 505632912192, .k 9395356858788072495 1, .k 5936592344967531567 13551424202, .k 8242435354181225519 1, .k 12854121372608613423 475716378, .k 10548278363394919471 1, .k 38218394473959246895 1, .k 130452114842507004975 73686092, .k 204239091137345211439 1, .k 351813043727021624367 42087863, .k 573173972611536243759 27434495, .k 646960948906374450223 1, .k 794534901496050863151 38203784, .k 1384830711854756514863 1, .k 2565422332572167818287 1737322, .k 3746013953289579121711 1, .k 6107197194724401728559 876511, .k 10829563677594046942255 1, .k 20274296643333337369647 77415, .k 10239267867235341290543 1, .k 160617125556115606064175 1, .k 319996994352966132026415 48275, .k 2133385723774909894085679 1, .k 1226691359063938013056047 32801, .k 1226691359063869293579311 1, .k 4906765436255638801337391 8, .k 6133456795351150023396399 1, .k 1226691359180211367693359 909, .k 3644542998409469717105711 1, .k 5760163182735070772841519 980, .k 19115458318148196466412591 1, .k 23040704096104704535677999 203, .k 27876407374563221234502703 1, .k 37547813931480254632152111 6175, .k 56890627045314321427450927 1, .k 95576253272982455018048559 309, .k 163620682044855574012087343 1, .k 382305012575626534208392239 277, .k 80054132097538119767149615 1, .k 4836014088974437230954662959 1, .k 6116880125994453327783906351 263, .k 16633664070321448056891362351 1, .k 24467521385446461049509760047 5, .k 61991082458398863066402376751 1, .k 97870085541269540912175238191 6, .k 359776785685858970201329486895 1, .k 391480342165048249122593164335 8, .k 836765202493147741300236733487 1, .k 1565921368660193006272726420527 8, .k 2825602123163013429642330098735 1, .k 6263685474640772025090599013423 4, .k 2929572167270064469589680704559 1, .k 53345812917931320888014694763567 1, .k 100218967594252352401449544305711 8, .k 265760093313374176788788723567663 1, .k 400875870377009409605798177262639 3, .k 1549845951741282172280430578224159 1, .k 255 1, .z 2], [.k 127 1, .k 111 4682218824069723167996109957596, .k 159 1, .k 63 84101906765581205227954746442331, .k 111 1, .k 15 302178618073084359382722201875136, .k 7 1, .k 3 1931491637626865330205339803713401, .k 1 1, .k 0 12208488838912746544308790247501416, .d 2], false⟩
def ckpt35 : RleFullState := ⟨.C, .raw [.z 1, .k 23680494555614255 1, .k 369668216514399279 1, .k 748445574236720175 26720150428303, .k 1324906326540143663 1, .k 2477827831146990639 505632912192, .k 9395356858788072495 1, .k 5936592344967531567 13551424202, .k 8242435354181225519 1, .k 12854121372608613423 475716378, .k 10548278363394919471 1, .k 38218394473959246895 1, .k 130452114842507004975 73686092, .k 204239091137345211439 1, .k 351813043727021624367 42087863, .k 573173972611536243759 27434495, .k 646960948906374450223 1, .k 794534901496050863151 38203784, .k 1384830711854756514863 1, .k 2565422332572167818287 1737322, .k 3746013953289579121711 1, .k 6107197194724401728559 876511, .k 10829563677594046942255 1, .k 20274296643333337369647 77415, .k 10239267867235341290543 1, .k 160617125556115606064175 1, .k 319996994352966132026415 48275, .k 2133385723774909894085679 1, .k 1226691359063938013056047 32755, .k 1226691359063938013056046 1, .k 4906765436255752052224203 45, .k 4906765436255477174317259 1, .k 19627061745022555205349579 8, .k 24533827181404600093585611 1, .k 4906765436720845470773451 909, .k 14578171993637878868422859 1, .k 23040652730940283091366091 980, .k 76461833272592785865650379 1, .k 92162816384418818142712011 203, .k 111505629498252884938010827 1, .k 150191255725921018528608459 6175, .k 227562508181257285709803723 1, .k 382305013091929820072194251 309, .k 654482728179422296048349387 1, .k 1529220050302506136833568971 277, .k 320216528390152479068598475 1, .k 19344056355897748923818651851 1, .k 24467520503977813311135625419 263, .k 66534656281285792227565449419 1, .k 97870085541785844198039040203 5, .k 247964329833595452265609507019 1, .k 391480342165078163648700952779 6, .k 1439107142743435880805317947595 1, .k 1565921368660192996490372657355 8, .k 3347060809972590965200946933963 1, .k 6263685474640772025090905682123 8, .k 11302408492652053718569320394955 1, .k 25054741898563088100362396053707 4, .k 11718288669080257878358722818251 1, .k 213383251671725283552058779054283 1, .k 400875870377009409605798177222859 8, .k 1063040373253496707155154894270667 1, .k 1603503481508037638423192709050571 3, .z 2], [.k 46784532390071343 20806419974146, .k 37777333135330351 1, .k 33273733507959855 57901138422180, .k 19762934625848367 37610989893458, .k 10755735371107375 1, .k 6252135743736879 30716371615732, .k 4000335930051631 1, .k 2874436023209007 305490132233582, .k 6252135743736879 1, .k 4563285883472943 270647459772345, .k 4316995278851119 1, .k 25601395641391 1, .k 294981744446511 139989328324157, .k 119059884002351 1, .k 27800418896943 1, .k 34397488663599 781492533683413, .k 29999442152495 1, .k 17904814246959 271475135198707, .k 15705790991407 1, .k 14606279363631 48671766179730583, .k 17904814246959 1, .k 11307744480303 94767307651599602, .k 14606279363631 1, .k 8009209596975 331887753716974115, .k 4710674713647 744220640956988995, .k 2511651458095 1, .k 1412139830319 7072824145170092509, .k 1380366928943 1, .k 353036127279 176244060668935040975, .k 91886177327 1, .k 88260201519 67361141208737850269, .k 32469666863 1, .k 22070938671 132226810123689069972, .k 13481004079 1, .k 9186036783 210157523808992004318, .k 8112294959 1, .k 2743585839 2160111270177901513702, .k 2206714927 1, .k 1938279471 660481848050345900758, .k 377998383 1, .k 109562927 1, .k 132631599 9040449275367983386986, .k 82299951 906038693021585505429, .k 56085551 1, .k 28822575 6063759545596197098728, .k 20433967 1, .k 16239663 30646279106479104971761, .k 14142511 1, .k 13093935 1009331069384952120084451, .k 16239663 1, .k 9948207 7537176816673596729879974, .k 6802479 5622837964162795894755808, .k 4705327 1, .k 3656751 39547083232249886800713772, .k 2608175 1, .k 2083887 132694352800547924806202579, .k 1552687 1, .k 33295 1, .k 130335 405864713587131296544679658, .k 101663 1, .k 32031 115717310694985543633932696, .k 44319 1, .k 19743 1615416730339319185619342344, .k 32031 1, .k 7455 274784465758569372306465281757, .k 5407 1, .k 4383 128723518072833641550810162476, .k 3263 1, .k 1119 378950886175484919310428816427, .k 1887 1, .k 351 2504802967801580957720172775389, .k 223 1, .k 159 6623541416857744891568440848885, .k 127 1, .k 111 4682218824069723167996109957596, .k 159 1, .k 63 84101906765581205227954746442331, .k 111 1, .k 15 302178618073084359382722201875136, .k 7 1, .k 3 1931491637626865330205339803713401, .k 1 1, .k 0 14484094826198233870862062990379883, .d 2], false⟩
def ckpt36 : RleFullState := ⟨.B, .clean 0 [(1179926977786059, 139989328324157), (102405582565579, 1), (17267981115404491, 1), (18253143533891787, 270647459772345), (25008542974947531, 1), (11497744092836043, 305490132233582), (16001343720206539, 1), (25008542974947531, 30716371615732), (43022941484429515, 1), (79051738503393483, 37610989893458), (133094934031839435, 57901138422180), (151109332541321419, 1), (187138129560285387, 20806419974146), (94721978222457035, 1), (1478672866057597131, 1), (2993782296946880715, 26720150428303), (5299625306160574667, 1), (9911311324587962571, 505632912192), (37581427435152289995, 1), (23746369379870126283, 13551424202), (32969741416724902091, 1), (51416485490434453707, 475716378), (42193113453579677899, 1), (152873577895836987595, 1), (521808459370028019915, 73686092), (816956364549380845771, 1), (1407252174908086497483, 42087863), (2292695890446144975051, 27434495), (2587843795625497800907, 1), (3178139605984203452619, 38203784), (5539322847419026059467, 1), (10261689330288671273163, 1737322), (14984055813158316486859, 1), (24428788778897606914251, 876511), (43318254710376187769035, 1), (81097186573333349478603, 77415), (40957071468941365162187, 1), (642468502224462424256715, 1), (1279987977411864528105675, 48275), (8533542895099639576342731, 1), (4906765436255752052224203, 32755), (4906765436255752052224199, 1), (19627061745023008208896827, 45), (19627061745021908697269051, 1), (78508246980090220821398331, 8), (98135308725618400374342459, 1), (19627061746883381883093819, 909), (58312687974551515473691451, 1), (92162610923761132365464379, 980), (305847333090371143462601531, 1), (368651265537675272570848059, 203), (446022517993011539752043323, 1), (600765022903684074114433851, 6175), (910250032725029142839214907, 1), (1529220052367719280288777019, 309), (2617930912717689184193397563, 1), (6116880201210024547334275899, 277), (1280866113560609916274393915, 1), (77376225423590995695274607419, 1), (97870082015911253244542501691, 263), (266138625125143168910261797691, 1), (391480342167143376792156160827, 5), (991857319334381809062438028091, 1), (1565921368660312654594803811131, 6), (5756428570973743523221271790395, 1), (6263685474640771985961490629435, 8), (13388243239890363860803787735867, 1), (25054741898563088100363622728507, 8), (45209633970608214874277281579835, 1), (100218967594252352401449584214843, 4), (46873154676321031513434891273019, 1), (853533006686901134208235116217147, 1), (1603503481508037638423192708891451, 6), (1045154529997911551774234158663271, 1), (8933583224162017386383336803650879, 1), (25656055704128602214771083342263039, 1), (68034583888223789257929913233322751, 1)] 48202932538950579704383293939180994, [.d 1, .d 1, .k 119059884002354 1, .k 27800418896946 1, .k 34397488663602 781492533683413, .k 29999442152498 1, .k 17904814246962 271475135198707, .k 15705790991410 1, .k 14606279363634 48671766179730583, .k 17904814246962 1, .k 11307744480306 94767307651599602, .k 14606279363634 1, .k 8009209596978 331887753716974115, .k 4710674713650 744220640956988995, .k 2511651458098 1, .k 1412139830322 7072824145170092509, .k 1380366928946 1, .k 353036127282 176244060668935040975, .k 91886177330 1, .k 88260201522 67361141208737850269, .k 32469666866 1, .k 22070938674 132226810123689069972, .k 13481004082 1, .k 9186036786 210157523808992004318, .k 8112294962 1, .k 2743585842 2160111270177901513702, .k 2206714930 1, .k 1938279474 660481848050345900758, .k 377998386 1, .k 109562930 1, .k 132631602 9040449275367983386986, .k 82299954 906038693021585505429, .k 56085554 1, .k 28822578 6063759545596197098728, .k 20433970 1, .k 16239666 30646279106479104971761, .k 14142514 1, .k 13093938 1009331069384952120084451, .k 16239666 1, .k 9948210 7537176816673596729879974, .k 6802482 5622837964162795894755808, .k 4705330 1, .k 3656754 39547083232249886800713772, .k 2608178 1, .k 2083890 132694352800547924806202579, .k 1552690 1, .k 33298 1, .k 130338 405864713587131296544679658, .k 101666 1, .k 32034 115717310694985543633932696, .k 44322 1, .k 19746 1615416730339319185619342344, .k 32034 1, .k 7458 274784465758569372306465281757, .k 5410 1, .k 4386 128723518072833641550810162476, .k 3266 1, .k 1122 378950886175484919310428816427, .k 1890 1, .k 354 2504802967801580957720172775389, .k 226 1, .k 162 6623541416857744891568440848885, .k 130 1, .k 114 4682218824069723167996109957596, .k 162 1, .k 66 84101906765581205227954746442331, .k 114 1, .k 18 302178618073084359382722201875136, .k 10 1, .k 6 1931491637626865330205339803713401, .k 4 1, .k 3 4081646418028275813881632855216315, .z 3, .d 2, .k 0 10402448408169958056980430135163567, .d 2], false⟩

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
lemma chunk_18 : runSteps ckpt18 = ckpt19 := rfl
lemma chunk_19 : runSteps ckpt19 = ckpt20 := rfl
lemma chunk_20 : runSteps ckpt20 = ckpt21 := rfl
lemma chunk_21 : runSteps ckpt21 = ckpt22 := rfl
lemma chunk_22 : runSteps ckpt22 = ckpt23 := rfl
lemma chunk_23 : runSteps ckpt23 = ckpt24 := rfl
lemma chunk_24 : runSteps ckpt24 = ckpt25 := rfl
lemma chunk_25 : runSteps ckpt25 = ckpt26 := rfl
lemma chunk_26 : runSteps ckpt26 = ckpt27 := rfl
lemma chunk_27 : runSteps ckpt27 = ckpt28 := rfl
lemma chunk_28 : runSteps ckpt28 = ckpt29 := rfl
lemma chunk_29 : runSteps ckpt29 = ckpt30 := rfl
lemma chunk_30 : runSteps ckpt30 = ckpt31 := rfl
lemma chunk_31 : runSteps ckpt31 = ckpt32 := rfl
lemma chunk_32 : runSteps ckpt32 = ckpt33 := rfl
lemma chunk_33 : runSteps ckpt33 = ckpt34 := rfl
lemma chunk_34 : runSteps ckpt34 = ckpt35 := rfl
lemma chunk_35 : runSteps ckpt35 = ckpt36 := rfl
lemma chunk_36 : (runSteps ckpt36).halted = true := rfl

lemma reach_36 : StateHalts ckpt36 := runSteps_halts ckpt36 (Or.inl chunk_36)
lemma reach_35 : StateHalts ckpt35 := chunk_back chunk_35 reach_36
lemma reach_34 : StateHalts ckpt34 := chunk_back chunk_34 reach_35
lemma reach_33 : StateHalts ckpt33 := chunk_back chunk_33 reach_34
lemma reach_32 : StateHalts ckpt32 := chunk_back chunk_32 reach_33
lemma reach_31 : StateHalts ckpt31 := chunk_back chunk_31 reach_32
lemma reach_30 : StateHalts ckpt30 := chunk_back chunk_30 reach_31
lemma reach_29 : StateHalts ckpt29 := chunk_back chunk_29 reach_30
lemma reach_28 : StateHalts ckpt28 := chunk_back chunk_28 reach_29
lemma reach_27 : StateHalts ckpt27 := chunk_back chunk_27 reach_28
lemma reach_26 : StateHalts ckpt26 := chunk_back chunk_26 reach_27
lemma reach_25 : StateHalts ckpt25 := chunk_back chunk_25 reach_26
lemma reach_24 : StateHalts ckpt24 := chunk_back chunk_24 reach_25
lemma reach_23 : StateHalts ckpt23 := chunk_back chunk_23 reach_24
lemma reach_22 : StateHalts ckpt22 := chunk_back chunk_22 reach_23
lemma reach_21 : StateHalts ckpt21 := chunk_back chunk_21 reach_22
lemma reach_20 : StateHalts ckpt20 := chunk_back chunk_20 reach_21
lemma reach_19 : StateHalts ckpt19 := chunk_back chunk_19 reach_20
lemma reach_18 : StateHalts ckpt18 := chunk_back chunk_18 reach_19
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

end BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH
