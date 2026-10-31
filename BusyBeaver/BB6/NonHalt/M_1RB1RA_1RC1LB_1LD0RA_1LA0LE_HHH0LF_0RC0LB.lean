/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RA_1RC1LB_1LD0RA_1LA0LE_---0LF_0RC0LB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RA_1RC1LB_1LD0RA_1LA0LE_---0LF_0RC0LB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RA_1RC1LB_1LD0RA_1LA0LE_HHH0LF_0RC0LB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RA_1RC1LB_1LD0RA_1LA0LE_---0LF_0RC0LB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 1 = step M c := rfl

lemma multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  simp only [multiStep, Function.iterate_succ_apply']

lemma multiStep_add (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) :
    c₁ [M]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

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
-- Section 6: 2nd-Order Digit-Stack Encodings & Inner Walk Lemmas
-- ============================================================================

/-- Left digit stack (inside-out order: head `a` is closest to the TM head).
    Each digit `a : ℕ` encodes a separator `0` followed by `1^{a+1}`. -/
def encLeft : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => ((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))

/-- Right digit stack (inside-out order: head `d` is closest to the TM head).
    Each digit `d : ℕ` encodes `1^{d+1}` followed by a `00` separator. -/
def encRight : List ℕ → ListBlank (Fin 2)
  | [] => default
  | d :: R => (([1] : List (Fin 2)) ^ (d + 1)) +> (((encRight R).cons 0).cons 0)

@[simp] lemma encLeft_nil : encLeft [] = default := rfl
@[simp] lemma encLeft_cons (a : ℕ) (L : List ℕ) :
    encLeft (a :: L) = ((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) := rfl
@[simp] lemma encRight_nil : encRight [] = default := rfl
@[simp] lemma encRight_cons (d : ℕ) (R : List ℕ) :
    encRight (d :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> (((encRight R).cons 0).cons 0) := rfl

/-- Increment the head digit of a stack (or push `0` if empty), corresponding to `.cons 1`. -/
def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | b :: L => (b + 1) :: L

@[simp] lemma encLeft_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encLeft L = encLeft (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encLeft]
  | cons b L' => rfl

@[simp] lemma encRight_cons_one (R : List ℕ) :
    (1 : Fin 2) >> encRight R = encRight (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encRight]
  | cons d R' => rfl

/-- Head digit of a right stack under `.tail` (`0` if empty, `d` if `d :: _`), so `(1 : Fin 2) >> (encRight R).tail = encRight (tailWeight R :: R.tail)`. -/
def tailWeight : List ℕ → ℕ
  | [] => 0
  | d :: _ => d

@[simp] lemma encRight_tail_cons_one (R : List ℕ) :
    (1 : Fin 2) >> (encRight R).tail = encRight (tailWeight R :: R.tail) := by
  cases R with
  | nil => simp [tailWeight, encRight]
  | cons d R' => dsimp [tailWeight, List.tail]; simp

lemma encRight_tail_decomp (R : List ℕ) :
    (encRight R).tail = (([1] : List (Fin 2)) ^ (tailWeight R)) +> (((encRight R.tail).cons 0).cons 0) := by
  cases R with
  | nil => simp [tailWeight, encRight]
  | cons d R' => rw [encRight_cons, Nat.add_comm d 1]; simp [tailWeight]

macro "finish" : tactic => `(tactic| (refine ⟨0, ?_⟩; simp only [zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one, encRight_cons_one, encRight_tail_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]; try rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

/-- State `B` separator configuration: state `B` scanning the `0` separator between `L` and `R`. -/
def cfg_B (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encLeft L, encRight R⟩⟩

/-- Unified state-`C` separator configuration: state `C` scanning the `0` separator between `L` and `(encRight R).tail`. -/
def cfg_CR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encLeft L, (encRight R).tail⟩⟩

/-- State `C` separator configuration: state `C` scanning the `0` separator between `L` and `R`. -/
def cfg_C (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encLeft L, encRight R⟩⟩

/-- Specialization of `cfg_CR` to `0 :: R` (triple-zero `000` separator before `encRight R`). -/
def cfg_C000 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_CR L (0 :: R)

/-- Canonical B-turnaround configuration at the right blank (`R = []`), with rightmost digit `a`. -/
def cfg_TurnB (L : List ℕ) (a : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_B (a :: L) []

/-- Complete 2nd-order stack configuration space `(mode, L, R)`. -/
inductive StackMode
  | B
  | CR

def evalStackCfg : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .B, L, R => cfg_B L R
  | .CR, L, R => cfg_CR L R

def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

/-- State `A` walks right across `1^k` (`A, 1 -> 1RA`). -/
lemma a_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((l <+ (([1] : List (Fin 2)) ^ k)) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    dsimp [HPow.hPow, list_nat_repeat]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, listblank_append_right_assoc]
    have h1 : (l {{A}}> (([1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ k +> r)))
        [target_tm]⊢⁺
        ((l <+ (([1] : List (Fin 2)) ^ 1)) {{A}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      dsimp [HPow.hPow, list_nat_repeat]
      execute 1
    refine stepStar_trans (stepPlus_stepStar h1) ?_
    refine stepStar_trans (ih (l <+ (([1] : List (Fin 2)) ^ 1)) r) ?_
    rw [← listblank_append_right_assoc, list_pow_add_comm]
    exact ⟨0, rfl⟩

/-- State `B` walks left across `1^k` (`B, 1 -> 1LB`). -/
lemma b_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{B}} r) [target_tm]⊢*
    (l <{{B}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero =>
    dsimp [HPow.hPow, list_nat_repeat]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, listblank_append_right_assoc]
    have h1 : (((l <+ (([1] : List (Fin 2)) ^ k)) <+ (([1] : List (Fin 2)) ^ 1)) <{{B}} r)
        [target_tm]⊢⁺
        ((l <+ (([1] : List (Fin 2)) ^ k)) <{{B}} (([1] : List (Fin 2)) ^ 1 +> r)) := by
      dsimp [HPow.hPow, list_nat_repeat]
      execute 1
    refine stepStar_trans (stepPlus_stepStar h1) ?_
    refine stepStar_trans (ih l (([1] : List (Fin 2)) ^ 1 +> r)) ?_
    rw [← listblank_append_right_assoc, list_pow_add_comm]
    exact ⟨0, rfl⟩

-- ============================================================================
-- Section 6B: Complete Local Separator Rules (8 Rules across 2 Modes)
-- ============================================================================

-- 1. Mode B rules (2 Rules)

/-- From `cfg_B L []`, the TM increments the head of `L` and enters `cfg_CR (bumpHead L) []` in 1 step. -/
theorem rule_B_nil (L : List ℕ) :
    (cfg_B L []) [target_tm]⊢⁺ (cfg_CR (bumpHead L) []) := by
  unfold cfg_B cfg_CR
  rw [encRight_nil]
  execute 1

/-- Helper: from state `C` on `1` with `encLeft K` on the left and `1^d 00 encRight R` on the right,
    the TM walks right across `1^d` and enters `cfg_B (d :: K) R`. -/
lemma c_sweep_right (K R : List ℕ) (d : ℕ) :
    (⟨some C, ⟨1, encLeft K, (([1] : List (Fin 2)) ^ d) +> (((encRight R).cons 0).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
    [target_tm]⊢⁺ (cfg_B (d :: K) R) := by
  unfold cfg_B
  have h_pre : (⟨some C, ⟨1, encLeft K, (([1] : List (Fin 2)) ^ d) +> (((encRight R).cons 0).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      (((encLeft K).cons 0) {{A}}> ((([1] : List (Fin 2)) ^ d) +> (((encRight R).cons 0).cons 0))) := by
    execute 1
  refine stepPlus_stepStar_stepPlus h_pre ?_
  refine stepStar_trans (a_walk_right d ((encLeft K).cons 0) (((encRight R).cons 0).cons 0)) ?_
  have h_post : ((((encLeft K).cons 0) <+ (([1] : List (Fin 2)) ^ d)) {{A}}> (((encRight R).cons 0).cons 0))
      [target_tm]⊢⁺
      (⟨some B, ⟨0, (((encLeft K).cons 0) <+ (([1] : List (Fin 2)) ^ d)) <+ (([1] : List (Fin 2)) ^ 1), encRight R⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 1
  refine stepStar_trans (stepPlus_stepStar h_post) ?_
  rw [listblank_append_pow_add, ← encLeft_cons d K]
  exact ⟨0, rfl⟩

/-- From `cfg_B L (d :: R)`, the TM increments the head of `L`, shifts `d` onto `L`, and enters `cfg_B (d :: bumpHead L) R`. -/
theorem rule_B_cons (L R : List ℕ) (d : ℕ) :
    (cfg_B L (d :: R)) [target_tm]⊢⁺ (cfg_B (d :: bumpHead L) R) := by
  unfold cfg_B
  rw [encRight_cons d R]
  have h_split : d + 1 = 1 + d := by omega
  rw [h_split, list_pow_add, listblank_append_right_assoc]
  have h_step1 : (⟨some B, ⟨0, encLeft L, (([1] : List (Fin 2)) ^ 1) +> ((([1] : List (Fin 2)) ^ d) +> (((encRight R).cons 0).cons 0))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      (⟨some C, ⟨1, encLeft (bumpHead L), (([1] : List (Fin 2)) ^ d) +> (((encRight R).cons 0).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 1
  exact stepPlus_trans h_step1 (c_sweep_right (bumpHead L) R d)

-- 2. Mode CR rules (6 Unified Rules)

/-- From `cfg_CR [] R`, the TM bounces off the left blank and enters `cfg_B [] ((tailWeight R + 2) :: R.tail)` in 5 steps. -/
theorem rule_CR_nil (R : List ℕ) :
    (cfg_CR [] R) [target_tm]⊢⁺ (cfg_B [] ((tailWeight R + 2) :: R.tail)) := by
  unfold cfg_CR cfg_B
  have h_pre : (⟨some C, ⟨0, encLeft [], (encRight R).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      (⟨some D, ⟨0, default, encRight (tailWeight R :: R.tail)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    rw [encLeft_nil]
    execute 1
  refine stepPlus_trans h_pre ?_
  rw [encLeft_nil, encRight_cons (tailWeight R) R.tail, encRight_cons (tailWeight R + 2) R.tail]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 4

/-- Halting configuration reached when `cfg_CR (0 :: L) R` steps left across `1` onto `0` in 2 steps. -/
def cfg_Halt_CR_zero (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encLeft L, (0 : Fin 2) >> encRight (tailWeight R :: R.tail)⟩⟩

/-- From `cfg_CR (0 :: L) R`, the TM halts in 2 steps at state `E` on `0`. -/
theorem rule_CR_zero (L R : List ℕ) :
    ((cfg_CR (0 :: L) R) [target_tm]⊢⁺ (cfg_Halt_CR_zero L R)) ∧
    (step target_tm (cfg_Halt_CR_zero L R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_CR cfg_Halt_CR_zero
  rw [encLeft_cons 0 L]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 2

/-- From `cfg_CR [1] R`, the TM bounces at the left boundary and enters `cfg_B [0] ((tailWeight R + 3) :: R.tail)` in 18 steps. -/
theorem rule_CR_one_nil (R : List ℕ) :
    (cfg_CR [1] R) [target_tm]⊢⁺ (cfg_B [0] ((tailWeight R + 3) :: R.tail)) := by
  unfold cfg_CR cfg_B
  have h_pre : (⟨some C, ⟨0, encLeft [1], (encRight R).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      (⟨some D, ⟨0, default, (1 : Fin 2) >> (0 : Fin 2) >> encRight (tailWeight R :: R.tail)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    rw [encLeft_cons 1 [], encLeft_nil]
    dsimp [HPow.hPow, list_nat_repeat]
    execute 5
  refine stepPlus_trans h_pre ?_
  rw [encLeft_cons 0 [], encLeft_nil, encRight_cons (tailWeight R) R.tail, encRight_cons (tailWeight R + 3) R.tail]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 13

/-- From `cfg_CR (1 :: b :: L) R`, the TM merges `1` and `b` across the separator and walks left in state `B`,
    entering `cfg_B L ((b + tailWeight R + 4) :: R.tail)` in `b + 15` steps. -/
theorem rule_CR_one_cons (b : ℕ) (L R : List ℕ) :
    (cfg_CR (1 :: b :: L) R) [target_tm]⊢⁺ (cfg_B L ((b + tailWeight R + 4) :: R.tail)) := by
  unfold cfg_CR cfg_B
  have h_pre : (⟨some C, ⟨0, encLeft (1 :: b :: L), (encRight R).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      (⟨some A, ⟨0, (((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ b)) <+ (([1] : List (Fin 2)) ^ 3), encRight (tailWeight R :: R.tail)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    rw [encLeft_cons 1 (b :: L), encLeft_cons b L]
    dsimp [HPow.hPow, list_nat_repeat]
    execute 9
  refine stepPlus_stepStar_stepPlus h_pre ?_
  have h_mid : (⟨some A, ⟨0, (((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ b)) <+ (([1] : List (Fin 2)) ^ 3), encRight (tailWeight R :: R.tail)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      (((((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ b)) <+ (([1] : List (Fin 2)) ^ 4)) <{{B}} encRight (tailWeight R :: R.tail)) := by
    rw [encRight_cons (tailWeight R) R.tail]
    dsimp [HPow.hPow, list_nat_repeat]
    execute 2
  refine stepStar_trans (stepPlus_stepStar h_mid) ?_
  rw [listblank_append_pow_add]
  refine stepStar_trans (b_walk_left (b + 4) ((encLeft L).cons 0) (encRight (tailWeight R :: R.tail))) ?_
  rw [encRight_cons (tailWeight R) R.tail, listblank_right_pow_add]
  have h_add : (b + 4) + (tailWeight R + 1) = (b + tailWeight R + 4) + 1 := by omega
  rw [h_add, ← encRight_cons (b + tailWeight R + 4) R.tail]
  finish

/-- From `cfg_CR (2 :: L) R`, the TM increments the head of `L`, normalizes `R` with a leading `0`,
    and enters `cfg_CR (bumpHead L) (0 :: tailWeight R :: R.tail)` in 5 steps. -/
theorem rule_CR_two (L R : List ℕ) :
    (cfg_CR (2 :: L) R) [target_tm]⊢⁺ (cfg_CR (bumpHead L) (0 :: tailWeight R :: R.tail)) := by
  unfold cfg_CR
  rw [encLeft_cons 2 L, encRight_cons 0 (tailWeight R :: R.tail)]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 5

/-- General helper for `L = (a + 3) :: L'` in state `C` with arbitrary right tape `r`. -/
lemma c_ge3_gen (L : List ℕ) (a : ℕ) (r : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, encLeft ((a + 3) :: L), r⟩⟩ : Cfg (Fin 2) (Fin 6))
    [target_tm]⊢⁺
    (⟨some C, ⟨0, encLeft ((a + 1) :: bumpHead L), (1 : Fin 2) >> r⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  rw [encLeft_cons (a + 3) L]
  have h_split : a + 3 + 1 = 3 + (a + 1) := by omega
  rw [h_split, list_pow_add, listblank_append_right_assoc]
  have h_pre : (⟨some C, ⟨0, (((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <+ (([1] : List (Fin 2)) ^ 3), r⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      ((((encLeft L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <{{B}} ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 4
  refine stepPlus_stepStar_stepPlus h_pre ?_
  refine stepStar_trans (b_walk_left (a + 1) ((encLeft L).cons 0) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) ?_
  have h_split2 : a + 1 = 1 + a := by omega
  rw [h_split2, list_pow_add, listblank_append_right_assoc]
  have h_mid : (((encLeft L).cons 0) <{{B}} ((([1] : List (Fin 2)) ^ 1) +> ((([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))))
      [target_tm]⊢⁺
      (((encLeft (bumpHead L)).cons 0) {{A}}> ((([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 2
  refine stepStar_trans (stepPlus_stepStar h_mid) ?_
  refine stepStar_trans (a_walk_right a ((encLeft (bumpHead L)).cons 0) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) ?_
  have h_post : ((((encLeft (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ a)) {{A}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))
      [target_tm]⊢⁺
      (⟨some C, ⟨0, (((encLeft (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ a)) <+ (([1] : List (Fin 2)) ^ 2), (1 : Fin 2) >> r⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 2
  refine stepStar_trans (stepPlus_stepStar h_post) ?_
  rw [listblank_append_pow_add]
  have h_add : a + 2 = (1 + a) + 1 := by omega
  rw [h_add, ← encLeft_cons (1 + a) (bumpHead L)]
  exact ⟨0, rfl⟩

/-- From `cfg_CR ((a + 3) :: L) R`, the TM decrements the top block by 2, increments the next block of `L`,
    and increments the top block of `R`. -/
theorem rule_CR_ge3 (L R : List ℕ) (a : ℕ) :
    (cfg_CR ((a + 3) :: L) R) [target_tm]⊢⁺
    (cfg_CR ((a + 1) :: bumpHead L) ((tailWeight R + 1) :: R.tail)) := by
  unfold cfg_CR
  have h_eq : (1 : Fin 2) >> (encRight R).tail = (encRight ((tailWeight R + 1) :: R.tail)).tail := by
    rw [encRight_tail_cons_one, encRight_cons (tailWeight R + 1) R.tail, Nat.add_comm (tailWeight R + 1) 1]
    simp [encRight]
  rw [← h_eq]
  exact c_ge3_gen L a (encRight R).tail

-- ============================================================================
-- Section 6C: Initial Reachability & 2nd-Order Stack Cryptid Closure
-- ============================================================================

theorem init_to_cfg_B :
    (init []) [target_tm]⊢⁺ (cfg_B [3, 1] []) := by
  unfold cfg_B
  rw [encLeft_cons, encLeft_cons, encLeft_nil, encRight_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 26

theorem init_reaches_stack_system :
    ∃ cfg₀, ((init []) [target_tm]⊢⁺ cfg₀) ∧ IsInStackSystem cfg₀ := by
  refine ⟨cfg_B [3, 1] [], init_to_cfg_B, ?_⟩
  exact ⟨.B, [3, 1], [], rfl⟩

lemma bumpHead_eq_cons (S : List ℕ) : bumpHead S = tailWeight (bumpHead S) :: S.tail := by
  cases S <;> rfl

/-- Inductive peel contraction: `k` iterations of `rule_CR_ge3` peel `2 * k` from the top block of `L`,
    adding `k` to the second block of `L` and `k` to the top block of `R`. -/
theorem rule_CR_peel_all (L R : List ℕ) (a b d k : ℕ) :
    (cfg_CR ((a + 1 + 2 * k) :: b :: L) (d :: R)) [target_tm]⊢*
    (cfg_CR ((a + 1) :: (b + k) :: L) ((d + k) :: R)) := by
  induction k generalizing a b d with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : a + 1 + 2 * (k + 1) = (a + 2 * k) + 3 := by omega
    rw [h_split]
    refine stepStar_trans (stepPlus_stepStar (rule_CR_ge3 (b :: L) (d :: R) (a + 2 * k))) ?_
    dsimp [bumpHead, tailWeight, List.tail]
    have h_next : a + 2 * k + 1 = a + 1 + 2 * k := by omega
    rw [h_next]
    refine stepStar_trans (ih a (b + 1) (d + 1)) ?_
    have hb : b + 1 + k = b + (k + 1) := by omega
    have hd : d + 1 + k = d + (k + 1) := by omega
    rw [hb, hd]
    exact ⟨0, rfl⟩

/-- Complete 2nd-order stack cryptid closure theorem (`stack_system_closed`). -/
theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | B =>
    cases R with
    | nil =>
      exact ⟨cfg_CR (bumpHead L) [], rule_B_nil L, Or.inl ⟨.CR, bumpHead L, [], rfl⟩⟩
    | cons d R' =>
      exact ⟨cfg_B (d :: bumpHead L) R', rule_B_cons L R' d,
        Or.inl ⟨.B, d :: bumpHead L, R', rfl⟩⟩
  | CR =>
    cases L with
    | nil =>
      exact ⟨cfg_B [] ((tailWeight R + 2) :: R.tail), rule_CR_nil R,
        Or.inl ⟨.B, [], (tailWeight R + 2) :: R.tail, rfl⟩⟩
    | cons a L' =>
      rcases a with _ | _ | _ | a
      · -- a = 0
        obtain ⟨hstep, hnone⟩ := rule_CR_zero L' R
        exact ⟨cfg_Halt_CR_zero L' R, hstep, Or.inr hnone⟩
      · -- a = 1
        cases L' with
        | nil =>
          exact ⟨cfg_B [0] ((tailWeight R + 3) :: R.tail), rule_CR_one_nil R,
            Or.inl ⟨.B, [0], (tailWeight R + 3) :: R.tail, rfl⟩⟩
        | cons b L'' =>
          exact ⟨cfg_B L'' ((b + tailWeight R + 4) :: R.tail), rule_CR_one_cons b L'' R,
            Or.inl ⟨.B, L'', (b + tailWeight R + 4) :: R.tail, rfl⟩⟩
      · -- a = 2
        exact ⟨cfg_CR (bumpHead L') (0 :: tailWeight R :: R.tail), rule_CR_two L' R,
          Or.inl ⟨.CR, bumpHead L', 0 :: tailWeight R :: R.tail, rfl⟩⟩
      · -- a + 3
        have h_div : a = (a % 2) + 2 * (a / 2) := (Nat.mod_add_div a 2).symm
        rw [h_div]
        have h1 := rule_CR_ge3 L' R ((a % 2) + 2 * (a / 2))
        have h_add : (a % 2) + 2 * (a / 2) + 1 = (a % 2) + 1 + 2 * (a / 2) := by omega
        rw [h_add, bumpHead_eq_cons L'] at h1
        have h2 := rule_CR_peel_all L'.tail R.tail (a % 2) (tailWeight (bumpHead L')) (tailWeight R + 1) (a / 2)
        exact ⟨cfg_CR (((a % 2) + 1) :: (tailWeight (bumpHead L') + a / 2) :: L'.tail) ((tailWeight R + 1 + a / 2) :: R.tail),
          stepPlus_stepStar_stepPlus h1 h2,
          Or.inl ⟨.CR, ((a % 2) + 1) :: (tailWeight (bumpHead L') + a / 2) :: L'.tail, (tailWeight R + 1 + a / 2) :: R.tail, rfl⟩⟩

/-- Multi-block chain split contraction in `cfg_C000`:
    `cfg_C000 (2 :: (1^k ++ b :: L)) R ⊢* cfg_C000 ((b + 1) :: L) (0^(k+1) ++ R)`. -/
theorem rule_C000_ones_all (L R : List ℕ) (b k : ℕ) :
    (cfg_C000 (2 :: (List.replicate k 1 ++ b :: L)) R) [target_tm]⊢*
    (cfg_C000 ((b + 1) :: L) (List.replicate (k + 1) 0 ++ R)) := by
  induction k generalizing R with
  | zero =>
    simp only [List.replicate, List.nil_append, List.singleton_append]
    exact stepPlus_stepStar (rule_CR_two (b :: L) (0 :: R))
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    refine stepStar_trans (stepPlus_stepStar (rule_CR_two (1 :: (List.replicate k 1 ++ b :: L)) (0 :: R))) ?_
    dsimp [bumpHead, tailWeight, List.tail]
    refine stepStar_trans (ih (0 :: R)) ?_
    have h_rep : List.replicate (k + 1 + 1) 0 ++ R = List.replicate (k + 1) 0 ++ (0 :: R) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [← h_rep]
    exact ⟨0, rfl⟩

/-- Universal odd-CR turnaround helper:
    `cfg_CR ((2 * k + 3) :: b :: L) [] ⊢⁺ cfg_B ((b + 2 * k + 6) :: bumpHead L) []`. -/
lemma cr_odd_turnaround (L : List ℕ) (b k : ℕ) :
    (cfg_CR ((2 * k + 3) :: b :: L) []) [target_tm]⊢⁺
    (cfg_B ((b + 2 * k + 6) :: bumpHead L) []) := by
  have h_cr0 : cfg_CR ((2 * k + 3) :: b :: L) [] = cfg_CR ((2 * k + 3) :: b :: L) [0] := by
    simp [cfg_CR, encRight]
  rw [h_cr0]
  have h1 : 2 * k + 3 = 0 + 1 + 2 * (k + 1) := by omega
  rw [h1]
  refine stepStar_stepPlus_stepPlus (rule_CR_peel_all L [] 0 b 0 (k + 1)) ?_
  simp only [Nat.zero_add]
  refine stepPlus_trans (rule_CR_one_cons (b + (k + 1)) L [k + 1]) ?_
  dsimp [tailWeight, List.tail]
  have hk : b + (k + 1) + (k + 1) + 4 = b + 2 * k + 6 := by omega
  rw [hk]
  exact rule_B_cons L [] (b + 2 * k + 6)

/-- Universal even-block turnaround theorem:
    `cfg_TurnB (b :: L) (2 * k + 2) ⊢⁺ cfg_TurnB (bumpHead L) (b + 2 * k + 6)`. -/
theorem turnaround_even_gen (L : List ℕ) (b k : ℕ) :
    (cfg_TurnB (b :: L) (2 * k + 2)) [target_tm]⊢⁺
    (cfg_TurnB (bumpHead L) (b + 2 * k + 6)) := by
  unfold cfg_TurnB
  exact stepPlus_trans (rule_B_nil ((2 * k + 2) :: b :: L)) (cr_odd_turnaround L b k)

/-- Canonical 3-block `B`-turnaround cycle configuration `cfg_CapB k := cfg_B [2k+4, 2k+8, 0] []`. -/
def cfg_CapB (k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_B [2 * k + 4, 2 * k + 8, 0] []

/-- Canonical 2-block `CR`-turnaround cycle configuration `cfg_CapCR k := cfg_CR [4k+5, 1] []`. -/
def cfg_CapCR (k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_CR [4 * k + 5, 1] []

/-- First half of the asymptotic cycle: `cfg_CapCR k ⊢⁺ cfg_CapB k`. -/
theorem cap_cr_to_cap_b (k : ℕ) :
    (cfg_CapCR k) [target_tm]⊢⁺ (cfg_CapB k) := by
  unfold cfg_CapCR cfg_CapB
  have h_start : 4 * k + 5 = 2 * (2 * k + 1) + 3 := by omega
  rw [h_start]
  have h1 := cr_odd_turnaround [] 1 (2 * k + 1)
  dsimp [bumpHead] at h1
  have h_mid1 : 1 + 2 * (2 * k + 1) + 6 = 4 * k + 9 := by omega
  rw [h_mid1] at h1
  refine stepPlus_trans h1 ?_
  refine stepPlus_trans (rule_B_nil [4 * k + 9, 0]) ?_
  dsimp [bumpHead]
  have h_cr0 : cfg_CR [4 * k + 9 + 1, 0] [] = cfg_CR [4 * k + 9 + 1, 0] [0] := by
    simp [cfg_CR, encRight]
  rw [h_cr0]
  have h2 : 4 * k + 9 + 1 = 1 + 1 + 2 * (2 * k + 4) := by omega
  rw [h2]
  refine stepStar_stepPlus_stepPlus (rule_CR_peel_all [] [] 1 0 0 (2 * k + 4)) ?_
  simp only [Nat.zero_add]
  refine stepPlus_trans (rule_CR_two [2 * k + 4] [2 * k + 4]) ?_
  dsimp [bumpHead, tailWeight, List.tail]
  have h3 : 2 * k + 4 + 1 = (2 * k + 2) + 3 := by omega
  rw [h3]
  refine stepPlus_trans (rule_CR_ge3 [] [0, 2 * k + 4] (2 * k + 2)) ?_
  dsimp [bumpHead, tailWeight, List.tail]
  have h4 : 2 * k + 2 + 1 = 0 + 1 + 2 * (k + 1) := by omega
  rw [h4]
  refine stepStar_stepPlus_stepPlus (rule_CR_peel_all [] [2 * k + 4] 0 0 1 (k + 1)) ?_
  simp only [Nat.zero_add]
  refine stepPlus_trans (rule_CR_one_cons (k + 1) [] [1 + (k + 1), 2 * k + 4]) ?_
  dsimp [tailWeight, List.tail]
  have h5 : (k + 1) + (1 + (k + 1)) + 4 = 2 * k + 7 := by omega
  rw [h5]
  refine stepPlus_trans (rule_B_cons [] [2 * k + 4] (2 * k + 7)) ?_
  dsimp [bumpHead]
  refine stepPlus_stepStar_stepPlus (rule_B_cons [2 * k + 7, 0] [] (2 * k + 4)) ?_
  dsimp [bumpHead]
  have h6 : 2 * k + 7 + 1 = 2 * k + 8 := by omega
  rw [h6]
  exact ⟨0, rfl⟩

/-- Second half of the asymptotic cycle: `cfg_CapB k ⊢⁺ cfg_CapCR (k + 3)`. -/
theorem cap_b_to_cap_cr (k : ℕ) :
    (cfg_CapB k) [target_tm]⊢⁺ (cfg_CapCR (k + 3)) := by
  unfold cfg_CapB cfg_CapCR
  have h_turn := turnaround_even_gen [0] (2 * k + 8) (k + 1)
  unfold cfg_TurnB at h_turn
  dsimp [bumpHead] at h_turn
  have h1 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  have h2 : (2 * k + 8) + 2 * (k + 1) + 6 = 4 * (k + 3) + 4 := by omega
  rw [h1, h2] at h_turn
  refine stepPlus_trans h_turn ?_
  have h_nil := rule_B_nil [4 * (k + 3) + 4, 1]
  dsimp [bumpHead] at h_nil
  exact h_nil

/-- Closed 2-block `CR` cycle recurrence: `cfg_CapCR k ⊢⁺ cfg_CapCR (k + 3)`. -/
theorem cap_cr_step (k : ℕ) :
    (cfg_CapCR k) [target_tm]⊢⁺ (cfg_CapCR (k + 3)) :=
  stepPlus_trans (cap_cr_to_cap_b k) (cap_b_to_cap_cr k)

/-- Closed 3-block `B` cycle recurrence: `cfg_CapB k ⊢⁺ cfg_CapB (k + 3)`. -/
theorem cap_b_step (k : ℕ) :
    (cfg_CapB k) [target_tm]⊢⁺ (cfg_CapB (k + 3)) :=
  stepPlus_trans (cap_b_to_cap_cr k) (cap_cr_to_cap_b (k + 3))

-- Call-by-value kernel evaluator for the finite prefix `cfg_CR [4, 1] [] ⊢* cfg_CapCR 38379`

def strictNat {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn (Nat.add n 1) (k 0) (fun m => k m)

@[simp] lemma strictNat_eq {α : Type} (n : ℕ) (k : ℕ → α) :
    strictNat n k = k n := rfl

def bumpHeadS (L : List ℕ) : List ℕ :=
  List.casesOn L [0] (fun b L' => strictNat (Nat.add b 1) (fun b1 => b1 :: L'))

@[simp] lemma bumpHeadS_eq (L : List ℕ) : bumpHeadS L = bumpHead L := by
  cases L <;> rfl

def tailWeightS (R : List ℕ) : ℕ :=
  List.casesOn R 0 (fun d _ => d)

@[simp] lemma tailWeightS_eq (R : List ℕ) : tailWeightS R = tailWeight R := by
  cases R <;> rfl

def tailS (R : List ℕ) : List ℕ :=
  List.casesOn R [] (fun _ R' => R')

@[simp] lemma tailS_eq (R : List ℕ) : tailS R = R.tail := by
  cases R <;> rfl

def sweepB : List ℕ → List ℕ → List ℕ
  | L, [] => L
  | L, d :: R => sweepB (d :: bumpHead L) R

def sweepBS (L R : List ℕ) : List ℕ :=
  List.rec
    (fun L => L)
    (fun d _ ih L => ih (d :: bumpHeadS L))
    R L

@[simp] lemma sweepBS_eq (R L : List ℕ) : sweepBS L R = sweepB L R := by
  induction R generalizing L with
  | nil => rfl
  | cons d R' ih =>
    change sweepBS (d :: bumpHeadS L) R' = sweepB (d :: bumpHead L) R'
    rw [bumpHeadS_eq]
    exact ih (d :: bumpHead L)

lemma rule_B_sweep_all (R L : List ℕ) :
    (cfg_B L R) [target_tm]⊢⁺ (cfg_CR (bumpHead (sweepB L R)) []) := by
  induction R generalizing L with
  | nil => exact rule_B_nil L
  | cons d R' ih => exact stepPlus_trans (rule_B_cons L R' d) (ih (d :: bumpHead L))

inductive CRRes
  | next (L R : List ℕ)
  | err

def stepCRBase (L R : List ℕ) : CRRes :=
  List.casesOn L .err (fun a L' =>
    Nat.casesOn a .err (fun a1 =>
      Nat.casesOn a1
        (List.casesOn L'
          (strictNat (Nat.add (tailWeightS R) 3) (fun d =>
            .next (bumpHeadS (sweepBS [0] (d :: tailS R))) []))
          (fun b L'' =>
            strictNat (Nat.add (Nat.add b (tailWeightS R)) 4) (fun d =>
              .next (bumpHeadS (sweepBS L'' (d :: tailS R))) [])))
        (fun a2 =>
          Nat.casesOn a2
            (.next (bumpHeadS L') (0 :: tailWeightS R :: tailS R))
            (fun _ => .err))))

def stepCR (L R : List ℕ) : CRRes :=
  List.casesOn L .err (fun a L' =>
    Nat.casesOn a .err (fun a1 =>
      Nat.casesOn a1
        (stepCRBase (1 :: L') R)
        (fun a2 =>
          Nat.casesOn a2
            (stepCRBase (2 :: L') R)
            (fun a₀ =>
              let bL := bumpHeadS L'
              strictNat (Nat.div a₀ 2) (fun q =>
                strictNat (Nat.add (Nat.mod a₀ 2) 1) (fun rem1 =>
                  strictNat (Nat.add (tailWeightS bL) q) (fun b1 =>
                    strictNat (Nat.add (Nat.add (tailWeightS R) 1) q) (fun d1 =>
                      stepCRBase (rem1 :: b1 :: tailS L') (d1 :: tailS R)))))))))

def CRResValid (L R : List ℕ) : CRRes → Prop
  | .next L' R' => (cfg_CR L R) [target_tm]⊢* (cfg_CR L' R')
  | .err => False

lemma crResValid_of_stepStar {L₁ R₁ L₂ R₂ : List ℕ} {res : CRRes}
    (h₁ : (cfg_CR L₁ R₁) [target_tm]⊢* (cfg_CR L₂ R₂))
    (h₂ : CRResValid L₂ R₂ res) :
    CRResValid L₁ R₁ res := by
  cases res with
  | next L₃ R₃ => exact stepStar_trans h₁ h₂
  | err => exact h₂

lemma stepCRBase_sound (L R : List ℕ) (h : stepCRBase L R ≠ .err) :
    CRResValid L R (stepCRBase L R) := by
  rcases L with _ | ⟨_ | _ | _ | a₀, L'⟩
  · exfalso; exact h rfl
  · exfalso; exact h rfl
  · cases L' with
    | nil =>
      change (cfg_CR [1] R) [target_tm]⊢*
        (cfg_CR (bumpHeadS (sweepBS [0] ((tailWeightS R + 3) :: tailS R))) [])
      simp only [bumpHeadS_eq, sweepBS_eq, tailWeightS_eq, tailS_eq]
      exact stepPlus_stepStar (stepPlus_trans (rule_CR_one_nil R)
        (rule_B_sweep_all ((tailWeight R + 3) :: R.tail) [0]))
    | cons b L'' =>
      change (cfg_CR (1 :: b :: L'') R) [target_tm]⊢*
        (cfg_CR (bumpHeadS (sweepBS L'' ((b + tailWeightS R + 4) :: tailS R))) [])
      simp only [bumpHeadS_eq, sweepBS_eq, tailWeightS_eq, tailS_eq]
      exact stepPlus_stepStar (stepPlus_trans (rule_CR_one_cons b L'' R)
        (rule_B_sweep_all ((b + tailWeight R + 4) :: R.tail) L''))
  · change (cfg_CR (2 :: L') R) [target_tm]⊢*
      (cfg_CR (bumpHeadS L') (0 :: tailWeightS R :: tailS R))
    simp only [bumpHeadS_eq, tailWeightS_eq, tailS_eq]
    exact stepPlus_stepStar (rule_CR_two L' R)
  · exfalso; exact h rfl

lemma cr_ge3_contract (L' R : List ℕ) (a₀ : ℕ) :
    (cfg_CR ((a₀ + 3) :: L') R) [target_tm]⊢⁺
    (cfg_CR (((a₀ % 2) + 1) :: (tailWeight (bumpHead L') + a₀ / 2) :: L'.tail)
      ((tailWeight R + 1 + a₀ / 2) :: R.tail)) := by
  have h1 := rule_CR_ge3 L' R a₀
  have h_add : a₀ + 1 = (a₀ % 2) + 1 + 2 * (a₀ / 2) := by omega
  rw [h_add, bumpHead_eq_cons L'] at h1
  have h2 := rule_CR_peel_all L'.tail R.tail (a₀ % 2) (tailWeight (bumpHead L')) (tailWeight R + 1) (a₀ / 2)
  exact stepPlus_stepStar_stepPlus h1 h2

lemma stepCR_sound (L R : List ℕ) (h : stepCR L R ≠ .err) :
    CRResValid L R (stepCR L R) := by
  rcases L with _ | ⟨_ | _ | _ | a₀, L'⟩
  · exfalso; exact h rfl
  · exfalso; exact h rfl
  · exact stepCRBase_sound (1 :: L') R h
  · exact stepCRBase_sound (2 :: L') R h
  · change stepCRBase (((a₀ % 2) + 1) :: (tailWeightS (bumpHeadS L') + a₀ / 2) :: tailS L')
      ((tailWeightS R + 1 + a₀ / 2) :: tailS R) ≠ .err at h
    change CRResValid ((a₀ + 3) :: L') R
      (stepCRBase (((a₀ % 2) + 1) :: (tailWeightS (bumpHeadS L') + a₀ / 2) :: tailS L')
        ((tailWeightS R + 1 + a₀ / 2) :: tailS R))
    simp only [bumpHeadS_eq, tailWeightS_eq, tailS_eq] at h ⊢
    have hbase := stepCRBase_sound _ _ h
    exact crResValid_of_stepStar (stepPlus_stepStar (cr_ge3_contract L' R a₀)) hbase

def runCRChunk (n : ℕ) (L R : List ℕ) : CRRes :=
  Nat.rec
    (fun L R => .next L R)
    (fun _ ih L R =>
      CRRes.casesOn (stepCR L R)
        (fun L' R' => ih L' R')
        .err)
    n L R

lemma runCRChunk_succ (n : ℕ) (L R : List ℕ) :
    runCRChunk (n + 1) L R =
      CRRes.casesOn (stepCR L R)
        (fun L' R' => runCRChunk n L' R')
        .err := rfl

lemma runCRChunk_sound : ∀ (n : ℕ) (L R : List ℕ),
    runCRChunk n L R ≠ .err →
    CRResValid L R (runCRChunk n L R)
  | 0, _, _, _ => ⟨0, rfl⟩
  | n + 1, L, R, hne => by
    rw [runCRChunk_succ] at hne ⊢
    cases hs : stepCR L R with
    | next L' R' =>
      rw [hs] at hne
      dsimp only at hne ⊢
      have hv := stepCR_sound L R (by rw [hs]; nofun)
      rw [hs] at hv
      exact crResValid_of_stepStar hv (runCRChunk_sound n L' R' hne)
    | err =>
      rw [hs] at hne
      dsimp only at hne
      exfalso; exact hne rfl

def runCRChunks (chunks chunkSize : ℕ) (L R : List ℕ) : CRRes :=
  Nat.rec
    (fun L R => .next L R)
    (fun _ ih L R =>
      CRRes.casesOn (runCRChunk chunkSize L R)
        (fun L' R' => ih L' R')
        .err)
    chunks L R

lemma runCRChunks_succ (chunks chunkSize : ℕ) (L R : List ℕ) :
    runCRChunks (chunks + 1) chunkSize L R =
      CRRes.casesOn (runCRChunk chunkSize L R)
        (fun L' R' => runCRChunks chunks chunkSize L' R')
        .err := rfl

lemma runCRChunks_sound : ∀ (chunks chunkSize : ℕ) (L R : List ℕ),
    runCRChunks chunks chunkSize L R ≠ .err →
    CRResValid L R (runCRChunks chunks chunkSize L R)
  | 0, _, _, _, _ => ⟨0, rfl⟩
  | chunks + 1, chunkSize, L, R, hne => by
    rw [runCRChunks_succ] at hne ⊢
    cases hc : runCRChunk chunkSize L R with
    | next L' R' =>
      rw [hc] at hne
      dsimp only at hne ⊢
      have hv := runCRChunk_sound chunkSize L R (by rw [hc]; nofun)
      rw [hc] at hv
      exact crResValid_of_stepStar hv (runCRChunks_sound chunks chunkSize L' R' hne)
    | err =>
      rw [hc] at hne
      dsimp only at hne
      exfalso; exact hne rfl

def runCRTwo (c1 s1 s2 : ℕ) (L R : List ℕ) : CRRes :=
  CRRes.casesOn (runCRChunks c1 s1 L R)
    (fun L' R' => runCRChunk s2 L' R')
    .err

lemma runCRTwo_sound (c1 s1 s2 : ℕ) (L R : List ℕ) (hne : runCRTwo c1 s1 s2 L R ≠ .err) :
    CRResValid L R (runCRTwo c1 s1 s2 L R) := by
  unfold runCRTwo at hne ⊢
  cases hc : runCRChunks c1 s1 L R with
  | next L' R' =>
    rw [hc] at hne
    dsimp only at hne ⊢
    have hv := runCRChunks_sound c1 s1 L R (by rw [hc]; nofun)
    rw [hc] at hv
    exact crResValid_of_stepStar hv (runCRChunk_sound s2 L' R' hne)
  | err =>
    rw [hc] at hne
    dsimp only at hne
    exfalso; exact hne rfl

lemma runCRTwo_reach {c1 s1 s2 : ℕ} {L R L' R' : List ℕ}
    (heq : runCRTwo c1 s1 s2 L R = .next L' R') :
    (cfg_CR L R) [target_tm]⊢* (cfg_CR L' R') := by
  have hne : runCRTwo c1 s1 s2 L R ≠ .err := by
    rw [heq]; intro h; nomatch h
  have hv := runCRTwo_sound c1 s1 s2 L R hne
  rw [heq] at hv
  exact hv

set_option maxRecDepth 400000 in
set_option maxHeartbeats 400000000 in
theorem runCRTwo_to_cap :
    runCRTwo 180 500 355 [4, 1] [] = .next [4 * 38379 + 5, 1] [] := rfl

/-- Blank tape reaches the closed cycle entry `cfg_CapCR 38379` (`cfg_CR [153521, 1] []`). -/
theorem init_reaches_cap_cr :
    (init []) [target_tm]⊢⁺ (cfg_CapCR 38379) :=
  stepPlus_stepStar_stepPlus
    (stepPlus_trans init_to_cfg_B (rule_B_nil [3, 1]))
    (runCRTwo_reach runCRTwo_to_cap)

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : ℕ}
    (h : multiStep target_tm c k = none) (d : ℕ) :
    multiStep target_tm c (k + d) = none := by
  rw [multiStep_add, h]; rfl

/-- For every `m : ℕ`, `init []` runs for at least `m` steps and reaches `cfg_CapCR (38379 + 3 * m)`. -/
theorem reach_arbitrarily_long :
    ∀ m : ℕ, ∃ N : ℕ, m ≤ N ∧
      multiStep target_tm (init []) N = some (cfg_CapCR (38379 + 3 * m))
  | 0 => by
    rcases init_reaches_cap_cr with ⟨N₀, hN₀_pos, hN₀⟩
    exact ⟨N₀, Nat.zero_le N₀, hN₀⟩
  | m + 1 => by
    rcases reach_arbitrarily_long m with ⟨N, h_le, hN⟩
    rcases cap_cr_step (38379 + 3 * m) with ⟨k, hk_pos, hk⟩
    have h_idx : 38379 + 3 * m + 3 = 38379 + 3 * (m + 1) := by omega
    rw [h_idx] at hk
    exact ⟨N + k, by omega, multiStep_trans target_tm _ _ _ N k hN hk⟩

end Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨k, hk⟩
  cases h_step : step target_tm cfg with
  | some cfg' => rfl
  | none =>
    have h_none : multiStep target_tm (init []) (k + 1) = none := by
      rw [multiStep_succ, hk]; exact h_step
    rcases reach_arbitrarily_long (k + 1) with ⟨N, h_ge, hN⟩
    have h_split : N = (k + 1) + (N - (k + 1)) := by omega
    have h_none_N : multiStep target_tm (init []) N = none := by
      rw [h_split]
      exact multiStep_none_add h_none (N - (k + 1))
    rw [h_none_N] at hN
    nomatch hN

end BusyBeaver.M_1RB1RA_1RC1LB_1LD0RA_1LA0LE_HHH0LF_0RC0LB
