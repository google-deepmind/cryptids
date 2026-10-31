/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

-- Holdout #117: 1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB---

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

def encRight : List Bool → ListBlank (Fin 2)
  | [] => default
  | false :: R => (1 : Fin 2) >> (0 : Fin 2) >> encRight R
  | true :: R => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight R

@[simp] lemma encRight_nil : encRight [] = default := rfl
@[simp] lemma encRight_false (R : List Bool) :
    encRight (false :: R) = (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl
@[simp] lemma encRight_true (R : List Bool) :
    encRight (true :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [zero_cons_default, encRight_nil, encRight_false, encRight_true,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]
  try rfl))

macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [encRight_nil, encRight_false, encRight_true,
    Turing.ListBlank.head_cons, default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, encRight_nil, encRight_false, encRight_true,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))

macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

abbrev LB := ListBlank (Fin 2)

def cfg_B (tl : LB) (R : List Bool) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, (0 : Fin 2) >> tl, encRight R⟩⟩

def cfg_C (tl : LB) (R : List Bool) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, tl, encRight R⟩⟩

def T2 (tl : LB) : LB := (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl
def T3 (tl : LB) : LB := (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl
def T4 (tl : LB) : LB := (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl
def T6 (tl : LB) : LB := (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl
def T12 (tl : LB) : LB := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl
def T322 (tl : LB) : LB := (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl

theorem rule_B_nil (tl : LB) :
    (cfg_B tl []) [target_tm]⊢⁺ cfg_C ((1 : Fin 2) >> (0 : Fin 2) >> tl) [] := by
  unfold cfg_B cfg_C; rw [encRight_nil]; execute 1

theorem rule_B_true (tl : LB) (R : List Bool) :
    (cfg_B tl (true :: R)) [target_tm]⊢⁺ cfg_B (T2 tl) R := by
  unfold cfg_B T2; rw [encRight_true]; execute 3

theorem rule_B_false_nil (tl : LB) :
    (cfg_B tl [false]) [target_tm]⊢⁺ cfg_C (T4 tl) [] := by
  unfold cfg_B cfg_C T4; rw [encRight_false, encRight_nil]; execute 4

theorem rule_B_false_false (tl : LB) (R : List Bool) :
    (cfg_B tl (false :: false :: R)) [target_tm]⊢⁺ cfg_B (T3 tl) R := by
  unfold cfg_B T3; rw [encRight_false, encRight_false]; execute 6

theorem rule_B_false_true (tl : LB) (R : List Bool) :
    (cfg_B tl (false :: true :: R)) [target_tm]⊢⁺ cfg_C (T3 tl) (false :: R) := by
  unfold cfg_B cfg_C T3; rw [encRight_false, encRight_true, encRight_false]; execute 7

theorem rule_C_110 (tl : LB) (R : List Bool) :
    (cfg_C (T2 tl) R) [target_tm]⊢⁺ cfg_C tl (true :: R) := by
  unfold cfg_C T2; rw [encRight_true]; execute 3

theorem rule_C_111 (tl : LB) (R : List Bool) :
    (cfg_C ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> tl) R) [target_tm]⊢⁺ cfg_C ((1 : Fin 2) >> tl) (false :: R) := by
  unfold cfg_C; rw [encRight_false]; execute 6

theorem rule_C_101 (tl : LB) (R : List Bool) :
    (cfg_C ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> tl) R) [target_tm]⊢⁺ cfg_B tl (false :: R) := by
  unfold cfg_C cfg_B; rw [encRight_false]; execute 4

theorem rule_C_100_false (tl : LB) (R : List Bool) :
    (cfg_C ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> tl) (false :: R)) [target_tm]⊢⁺
      cfg_B ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> tl) R := by
  unfold cfg_C cfg_B; rw [encRight_false]; execute 10

theorem rule_C_41 (tl : LB) (R : List Bool) :
    (cfg_C (T4 tl) R) [target_tm]⊢⁺ cfg_C (T2 tl) (false :: R) :=
  rule_C_111 ((1 : Fin 2) >> (0 : Fin 2) >> tl) R

theorem rule_C_61 (tl : LB) (R : List Bool) :
    (cfg_C (T6 tl) R) [target_tm]⊢⁺ cfg_C (T4 tl) (false :: R) :=
  rule_C_111 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl) R

theorem rule_C_32 (tl : LB) (R : List Bool) :
    (cfg_C ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> tl) R) [target_tm]⊢⁺
      cfg_B ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> tl) R :=
  stepPlus_trans (rule_C_111 ((0 : Fin 2) >> (0 : Fin 2) >> tl) R) (rule_C_100_false tl R)

theorem rule_C_31_1 (tl : LB) (R : List Bool) :
    (cfg_C (T3 ((1 : Fin 2) >> tl)) R) [target_tm]⊢⁺ cfg_B (T3 tl) R :=
  stepPlus_trans (rule_C_111 ((0 : Fin 2) >> (1 : Fin 2) >> tl) R)
    (stepPlus_trans (rule_C_101 tl (false :: R)) (rule_B_false_false tl R))

theorem rule_B_nil_1 (tl : LB) :
    (cfg_B ((1 : Fin 2) >> tl) []) [target_tm]⊢⁺ cfg_C (T4 tl) [] :=
  stepPlus_trans (rule_B_nil ((1 : Fin 2) >> tl))
    (stepPlus_trans (rule_C_101 tl []) (rule_B_false_nil tl))

theorem rule_B_carry_true (tl : LB) (R : List Bool) :
    (cfg_B ((1 : Fin 2) >> tl) (false :: true :: R)) [target_tm]⊢⁺ cfg_B (T3 tl) (false :: R) :=
  stepPlus_trans (rule_B_false_true ((1 : Fin 2) >> tl) R) (rule_C_31_1 tl (false :: R))

theorem rule_C_3_22 (tl : LB) (R : List Bool) :
    (cfg_C (T3 (T2 (T2 tl))) R) [target_tm]⊢⁺ cfg_B (T3 (T12 tl)) R :=
  rule_C_31_1 ((1 : Fin 2) >> (0 : Fin 2) >> T2 tl) R

theorem rule_C_3_12 (tl : LB) (R : List Bool) :
    (cfg_C (T3 (T12 tl)) R) [target_tm]⊢⁺ cfg_B (T322 tl) R :=
  rule_C_31_1 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl) R

theorem rule_C_322 (tl : LB) (R : List Bool) :
    (cfg_C (T322 tl) R) [target_tm]⊢⁺ cfg_B (T6 tl) R :=
  rule_C_32 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> tl) R

theorem rule_C_6 (tl : LB) (R : List Bool) :
    (cfg_C (T6 tl) R) [target_tm]⊢⁺ cfg_C tl (true :: false :: false :: R) :=
  stepPlus_trans (rule_C_61 tl R)
    (stepPlus_trans (rule_C_41 tl (false :: R)) (rule_C_110 tl (false :: false :: R)))

theorem rule_C_default (R : List Bool) :
    (cfg_C default R) [target_tm]⊢⁺ cfg_B default (true :: R) := by
  unfold cfg_C cfg_B; rw [encRight_true]; execute 3

theorem rule_B_norm_exit (tl : LB) :
    (cfg_B (T2 (T2 tl)) [false]) [target_tm]⊢⁺ cfg_C tl [true, true, true, false] :=
  stepPlus_trans (rule_B_false_nil (T2 (T2 tl)))
    (stepPlus_trans (rule_C_41 (T2 (T2 tl)) [])
      (stepPlus_trans (rule_C_110 (T2 (T2 tl)) [false])
        (stepPlus_trans (rule_C_110 (T2 tl) [true, false])
          (rule_C_110 tl [true, true, false]))))

theorem rule_B_carry_exit (tl : LB) :
    (cfg_B (T3 (T2 (T2 tl))) [false, false]) [target_tm]⊢⁺
      cfg_C (T3 (T12 tl)) [true, true, true, false] :=
  stepPlus_trans (rule_B_false_false (T3 (T2 (T2 tl))) [])
    (stepPlus_trans (rule_B_nil_1 (T2 (T3 (T2 (T2 tl)))))
      (stepPlus_trans (rule_C_41 (T2 (T3 (T2 (T2 tl)))) [])
        (stepPlus_trans (rule_C_110 (T2 (T3 (T2 (T2 tl)))) [false])
          (stepPlus_trans (rule_C_110 (T3 (T2 (T2 tl))) [true, false])
            (stepPlus_trans (rule_C_3_22 tl [true, true, false])
              (stepPlus_trans (rule_B_true (T3 (T12 tl)) [true, false])
                (stepPlus_trans (rule_B_true (T2 (T3 (T12 tl))) [false])
                  (stepPlus_trans (rule_B_false_nil (T2 (T2 (T3 (T12 tl)))))
                    (stepPlus_trans (rule_C_41 (T2 (T2 (T3 (T12 tl)))) [])
                      (stepPlus_trans (rule_C_110 (T2 (T2 (T3 (T12 tl)))) [false])
                        (stepPlus_trans (rule_C_110 (T2 (T3 (T12 tl))) [true, false])
                          (rule_C_110 (T3 (T12 tl)) [true, true, false]))))))))))))

theorem rule_C_3_0 (R : List Bool) :
    (cfg_C (T3 default) R) [target_tm]⊢⁺ cfg_B (T4 default) R := by
  have h := rule_C_32 default R
  unfold T3 T4
  simpa only [zero_cons_default] using h

theorem rule_C_6_3 (R : List Bool) :
    (cfg_C (T6 (T2 (T2 (T2 (T3 default))))) R) [target_tm]⊢⁺
      cfg_B (T3 (T2 (T2 (T2 (T2 (T4 default)))))) R :=
  stepPlus_trans (rule_C_6 (T2 (T2 (T2 (T3 default)))) R)
    (stepPlus_trans (rule_C_110 (T2 (T2 (T3 default))) (true :: false :: false :: R))
      (stepPlus_trans (rule_C_110 (T2 (T3 default)) (true :: true :: false :: false :: R))
        (stepPlus_trans (rule_C_110 (T3 default) (true :: true :: true :: false :: false :: R))
          (stepPlus_trans (rule_C_3_0 (true :: true :: true :: true :: false :: false :: R))
            (stepPlus_trans (rule_B_true (T4 default) (true :: true :: true :: false :: false :: R))
              (stepPlus_trans (rule_B_true (T2 (T4 default)) (true :: true :: false :: false :: R))
                (stepPlus_trans (rule_B_true (T2 (T2 (T4 default))) (true :: false :: false :: R))
                  (stepPlus_trans (rule_B_true (T2 (T2 (T2 (T4 default)))) (false :: false :: R))
                    (rule_B_false_false (T2 (T2 (T2 (T2 (T4 default))))) R)))))))))

theorem rule_B_carry_3_true (x : LB) (R : List Bool) :
    (cfg_B (T3 x) (false :: true :: R)) [target_tm]⊢⁺ cfg_B (T3 (T2 x)) (false :: R) :=
  rule_B_carry_true (T2 x) R

theorem rule_C_6_4 (R : List Bool) :
    (cfg_C (T6 (T2 (T2 (T4 default)))) R) [target_tm]⊢⁺
      cfg_B (T3 (T3 (T2 (T2 (T12 default))))) (false :: R) :=
  stepPlus_trans (rule_C_6 (T2 (T2 (T4 default))) R)
    (stepPlus_trans (rule_C_110 (T2 (T4 default)) (true :: false :: false :: R))
      (stepPlus_trans (rule_C_110 (T4 default) (true :: true :: false :: false :: R))
        (stepPlus_trans (rule_C_41 default (true :: true :: true :: false :: false :: R))
          (stepPlus_trans (rule_C_110 default (false :: true :: true :: true :: false :: false :: R))
            (stepPlus_trans (rule_C_default (true :: false :: true :: true :: true :: false :: false :: R))
              (stepPlus_trans (rule_B_true default (true :: false :: true :: true :: true :: false :: false :: R))
                (stepPlus_trans (rule_B_true (T2 default) (false :: true :: true :: true :: false :: false :: R))
                  (stepPlus_trans (rule_B_false_true (T2 (T2 default)) (true :: true :: false :: false :: R))
                    (stepPlus_trans (rule_C_3_22 default (false :: true :: true :: false :: false :: R))
                      (stepPlus_trans (rule_B_carry_3_true (T12 default) (true :: false :: false :: R))
                        (stepPlus_trans (rule_B_carry_3_true (T2 (T12 default)) (false :: false :: R))
                          (rule_B_false_false (T3 (T2 (T2 (T12 default)))) (false :: R)))))))))))))

theorem rule_C_12_0 (R : List Bool) :
    (cfg_C (T12 default) R) [target_tm]⊢⁺ cfg_B ((1 : Fin 2) >> default) (false :: R) := by
  have h := rule_C_101 ((1 : Fin 2) >> (0 : Fin 2) >> default) R
  unfold T12
  simpa only [zero_cons_default] using h

theorem rule_B_carry_1_0 (R : List Bool) :
    (cfg_B ((1 : Fin 2) >> default) (false :: true :: R)) [target_tm]⊢⁺ cfg_B (T3 default) (false :: R) :=
  rule_B_carry_true default R

theorem rule_C_6_12 (R : List Bool) :
    (cfg_C (T6 (T12 default)) R) [target_tm]⊢⁺
      cfg_B (T3 (T3 default)) (false :: R) :=
  stepPlus_trans (rule_C_6 (T12 default) R)
    (stepPlus_trans (rule_C_12_0 (true :: false :: false :: R))
      (stepPlus_trans (rule_B_carry_1_0 (false :: false :: R))
        (rule_B_false_false (T3 default) (false :: R))))

def powT2 : Nat → LB → LB
  | 0, x => x
  | n + 1, x => T2 (powT2 n x)

def powTrue : Nat → List Bool → List Bool
  | 0, R => R
  | n + 1, R => true :: powTrue n R

theorem powT2_comm (n : Nat) (x : LB) : powT2 n (T2 x) = T2 (powT2 n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [powT2, ih]

theorem powTrue_comm (n : Nat) (R : List Bool) : powTrue n (true :: R) = true :: powTrue n R := by
  induction n with
  | zero => rfl
  | succ n ih => simp [powTrue, ih]

theorem c_pop_T2 (n : Nat) (x : LB) (R : List Bool) :
    (cfg_C (powT2 n x) R) [target_tm]⊢* cfg_C x (powTrue n R) := by
  induction n generalizing R with
  | zero => finish
  | succ n ih =>
    simp only [powT2, powTrue, ← powTrue_comm]
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus (rule_C_110 (powT2 n x) R) (ih (true :: R)))

theorem b_push_T2 (n : Nat) (x : LB) (R : List Bool) :
    (cfg_B x (powTrue n R)) [target_tm]⊢* cfg_B (powT2 n x) R := by
  induction n generalizing x with
  | zero => finish
  | succ n ih =>
    simp only [powTrue, powT2, ← powT2_comm]
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus (rule_B_true x (powTrue n R)) (ih (T2 x)))

theorem b_carry_push_T2 (n : Nat) (x : LB) (R : List Bool) :
    (cfg_B (T3 x) (false :: powTrue n R)) [target_tm]⊢* cfg_B (T3 (powT2 n x)) (false :: R) := by
  induction n generalizing x with
  | zero => finish
  | succ n ih =>
    simp only [powTrue, powT2, ← powT2_comm]
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus (rule_B_carry_3_true x (powTrue n R)) (ih (T2 x)))

theorem c_pop_T6 (b : Nat) (tl : LB) (R : List Bool) :
    (cfg_C (T6 (powT2 b tl)) R) [target_tm]⊢⁺ cfg_C tl (powTrue (b + 1) (false :: false :: R)) := by
  refine stepPlus_stepStar_stepPlus (rule_C_6 (powT2 b tl) R) ?_
  have h := c_pop_T2 b tl (true :: false :: false :: R)
  rw [powTrue_comm] at h
  exact h

theorem b_norm_block (m : Nat) (x : LB) (R : List Bool) :
    (cfg_B x (powTrue m (false :: false :: R))) [target_tm]⊢⁺ cfg_B (T3 (powT2 m x)) R :=
  stepStar_stepPlus_stepPlus (b_push_T2 m x (false :: false :: R)) (rule_B_false_false (powT2 m x) R)

theorem b_carry_block (m : Nat) (x : LB) (R : List Bool) :
    (cfg_B (T3 x) (false :: powTrue m (false :: false :: R))) [target_tm]⊢⁺
      cfg_B (T3 (T3 (powT2 m x))) (false :: R) :=
  stepStar_stepPlus_stepPlus (b_carry_push_T2 m x (false :: false :: R))
    (rule_B_false_false (T3 (powT2 m x)) (false :: R))

theorem b_norm_end (a : Nat) (x : LB) :
    (cfg_B x (powTrue a [true, true, true, false])) [target_tm]⊢⁺
      cfg_C (powT2 (a + 1) x) [true, true, true, false] :=
  stepStar_stepPlus_stepPlus (b_push_T2 a x [true, true, true, false])
    (stepPlus_trans (rule_B_true (powT2 a x) [true, true, false])
      (stepPlus_trans (rule_B_true (T2 (powT2 a x)) [true, false])
        (stepPlus_trans (rule_B_true (T2 (T2 (powT2 a x))) [false])
          (rule_B_norm_exit (T2 (powT2 a x))))))

theorem b_carry_end (a : Nat) (x : LB) :
    (cfg_B (T3 x) (false :: powTrue a [true, true, true, false])) [target_tm]⊢⁺
      cfg_C (T3 (T12 (powT2 (a + 1) x))) [true, true, true, false] :=
  stepStar_stepPlus_stepPlus (b_carry_push_T2 a x [true, true, true, false])
    (stepPlus_trans (rule_B_carry_3_true (powT2 a x) [true, true, false])
      (stepPlus_trans (rule_B_carry_3_true (T2 (powT2 a x)) [true, false])
        (stepPlus_trans (rule_B_carry_3_true (T2 (T2 (powT2 a x))) [false])
          (rule_B_carry_exit (T2 (powT2 a x))))))

def StepNorm (s₁ s₂ : LB) : Prop :=
  ∀ R : List Bool, (cfg_C s₁ R) [target_tm]⊢⁺ cfg_B s₂ R

def StepCarry (s₁ s₂ : LB) : Prop :=
  ∀ R : List Bool, (cfg_C s₁ R) [target_tm]⊢⁺ cfg_B (T3 s₂) (false :: R)

abbrev NormSteps : Nat → LB → LB → Prop := Counter.IterRel StepNorm

theorem NormSteps.zero (s : LB) : NormSteps 0 s s := Counter.IterRel.zero s
theorem NormSteps.succ {n : Nat} {s₁ s₂ s₃ : LB} (h1 : StepNorm s₁ s₂) (h2 : NormSteps n s₂ s₃) :
    NormSteps (n + 1) s₁ s₃ := Counter.IterRel.succ h1 h2

def CarryRun (n : Nat) (s₁ s₂ : LB) : Prop :=
  ∃ mid : LB, NormSteps n s₁ mid ∧ StepCarry mid s₂

theorem NormSteps_trans {m n : Nat} {s₁ s₂ s₃ : LB}
    (h₁ : NormSteps m s₁ s₂) (h₂ : NormSteps n s₂ s₃) : NormSteps (m + n) s₁ s₃ :=
  Counter.IterRel_trans h₁ h₂

theorem CarryRun_prepend {m n : Nat} {s₁ s₂ s₃ : LB}
    (h₁ : NormSteps m s₁ s₂) (h₂ : CarryRun n s₂ s₃) : CarryRun (m + n) s₁ s₃ := by
  obtain ⟨mid, hm, hc⟩ := h₂
  exact ⟨mid, NormSteps_trans h₁ hm, hc⟩

theorem stepNorm_3_22 (b : Nat) (s : LB) :
    StepNorm (T3 (powT2 (b + 2) s)) (T3 (T12 (powT2 b s))) :=
  fun R => rule_C_3_22 (powT2 b s) R

theorem stepNorm_3_12 (s : LB) : StepNorm (T3 (T12 s)) (T322 s) :=
  fun R => rule_C_3_12 s R

theorem stepNorm_322 (s : LB) : StepNorm (T322 s) (T6 s) :=
  fun R => rule_C_322 s R

theorem stepNorm_T6 {s₁ s₂ : LB} (b : Nat) (h : StepNorm s₁ s₂) :
    StepNorm (T6 (powT2 b s₁)) (T3 (powT2 (b + 1) s₂)) :=
  fun R => stepPlus_trans (c_pop_T6 b s₁ R)
    (stepPlus_trans (h (powTrue (b + 1) (false :: false :: R))) (b_norm_block (b + 1) s₂ R))

theorem stepCarry_T6 {s₁ s₂ : LB} (b : Nat) (h : StepCarry s₁ s₂) :
    StepCarry (T6 (powT2 b s₁)) (T3 (powT2 (b + 1) s₂)) :=
  fun R => stepPlus_trans (c_pop_T6 b s₁ R)
    (stepPlus_trans (h (powTrue (b + 1) (false :: false :: R))) (b_carry_block (b + 1) s₂ R))

theorem normSteps_cycle_T3_12 {s₁ s₂ : LB} (b : Nat) (h : StepNorm s₁ s₂) :
    NormSteps 3 (T3 (T12 (powT2 b s₁))) (T3 (powT2 (b + 1) s₂)) :=
  NormSteps.succ (stepNorm_3_12 _)
    (NormSteps.succ (stepNorm_322 _)
      (NormSteps.succ (stepNorm_T6 b h) (NormSteps.zero _)))

theorem normSteps_cycle_T3 {s₁ s₂ : LB} (b : Nat) (h : StepNorm s₁ s₂) :
    NormSteps 4 (T3 (powT2 (b + 2) s₁)) (T3 (powT2 (b + 1) s₂)) :=
  NormSteps.succ (stepNorm_3_22 b s₁) (normSteps_cycle_T3_12 b h)

theorem carryRun_cycle_T3_12 {s₁ s₂ : LB} (b : Nat) (h : StepCarry s₁ s₂) :
    CarryRun 2 (T3 (T12 (powT2 b s₁))) (T3 (powT2 (b + 1) s₂)) :=
  ⟨T6 (powT2 b s₁),
    NormSteps.succ (stepNorm_3_12 _) (NormSteps.succ (stepNorm_322 _) (NormSteps.zero _)),
    stepCarry_T6 b h⟩

theorem carryRun_cycle_T3 {s₁ s₂ : LB} (b : Nat) (h : StepCarry s₁ s₂) :
    CarryRun 3 (T3 (powT2 (b + 2) s₁)) (T3 (powT2 (b + 1) s₂)) := by
  obtain ⟨mid, hm, hc⟩ := carryRun_cycle_T3_12 b h
  exact ⟨mid, NormSteps.succ (stepNorm_3_22 b s₁) hm, hc⟩

theorem lift_NormSteps {n : Nat} {s₁ s₂ : LB} (h : NormSteps n s₁ s₂) (b : Nat) :
    NormSteps (4 * n) (T3 (powT2 (b + n + 1) s₁)) (T3 (powT2 (b + 1) s₂)) := by
  induction h generalizing b with
  | zero s =>
    simpa only [Nat.mul_zero, Nat.add_zero] using NormSteps.zero (T3 (powT2 (b + 1) s))
  | @succ m s₁ s₂ s₃ hstep hrest ih =>
    have h1 : NormSteps 4 (T3 (powT2 (b + (m + 1) + 1) s₁)) (T3 (powT2 (b + m + 1) s₂)) := by
      have : b + (m + 1) + 1 = (b + m) + 2 := by omega
      rw [this]
      exact normSteps_cycle_T3 (b + m) hstep
    have h2 := NormSteps_trans h1 (ih b)
    have : 4 + 4 * m = 4 * (m + 1) := by omega
    rwa [this] at h2

theorem lift_NormSteps_T3_12 {n : Nat} {s₁ s₂ s₃ : LB}
    (h₁ : StepNorm s₁ s₂) (h₂ : NormSteps n s₂ s₃) (b : Nat) :
    NormSteps (4 * n + 3) (T3 (T12 (powT2 (b + n) s₁))) (T3 (powT2 (b + 1) s₃)) := by
  have h1 := normSteps_cycle_T3_12 (b + n) h₁
  have h2 := lift_NormSteps h₂ b
  have h3 := NormSteps_trans h1 h2
  have : 3 + 4 * n = 4 * n + 3 := by omega
  rwa [this] at h3

theorem lift_CarryRun {n : Nat} {s₁ s₂ : LB} (h : CarryRun n s₁ s₂) (b : Nat) :
    CarryRun (4 * n + 3) (T3 (powT2 (b + n + 2) s₁)) (T3 (powT2 (b + 1) s₂)) := by
  obtain ⟨mid, hm, hc⟩ := h
  have h1 : NormSteps (4 * n) (T3 (powT2 (b + n + 2) s₁)) (T3 (powT2 (b + 2) mid)) := by
    have : b + n + 2 = (b + 1) + n + 1 := by omega
    rw [this]
    exact lift_NormSteps hm (b + 1)
  exact CarryRun_prepend h1 (carryRun_cycle_T3 b hc)

theorem lift_CarryRun_T3_12 {n : Nat} {s₁ s₂ : LB} (h : CarryRun n s₁ s₂) (b : Nat) :
    CarryRun (4 * n + 2) (T3 (T12 (powT2 (b + n) s₁))) (T3 (powT2 (b + 1) s₂)) := by
  obtain ⟨mid, hm, hc⟩ := h
  cases hm with
  | zero =>
    simpa only [Nat.mul_zero, Nat.add_zero] using carryRun_cycle_T3_12 b hc
  | @succ m s₁ s_next _ hstep hrest =>
    have h1 : NormSteps 3 (T3 (T12 (powT2 (b + (m + 1)) s₁))) (T3 (powT2 (b + m + 2) s_next)) := by
      have : b + (m + 1) = (b + m) + 1 := by omega
      rw [this]
      exact normSteps_cycle_T3_12 (b + m + 1) hstep
    have h2 := lift_CarryRun ⟨mid, hrest, hc⟩ b
    have h3 := CarryRun_prepend h1 h2
    have : 3 + (4 * m + 3) = 4 * (m + 1) + 2 := by omega
    rwa [this] at h3

theorem run_StepNorm {s₁ s₂ : LB} (h : StepNorm s₁ s₂) (a : Nat) :
    (cfg_C (powT2 a s₁) [true, true, true, false]) [target_tm]⊢⁺
      cfg_C (powT2 (a + 1) s₂) [true, true, true, false] :=
  stepStar_stepPlus_stepPlus (c_pop_T2 a s₁ [true, true, true, false])
    (stepPlus_trans (h (powTrue a [true, true, true, false])) (b_norm_end a s₂))

theorem run_NormSteps {n : Nat} {s₁ s₂ : LB} (h : NormSteps n s₁ s₂) (a : Nat) :
    (cfg_C (powT2 a s₁) [true, true, true, false]) [target_tm]⊢*
      cfg_C (powT2 (a + n) s₂) [true, true, true, false] :=
  Counter.IterRel_lift_rc (fun s a => cfg_C (powT2 a s) [true, true, true, false])
    (fun h a => stepPlus_stepStar (run_StepNorm h a)) h a

theorem run_StepCarry {s₁ s₂ : LB} (h : StepCarry s₁ s₂) (a : Nat) :
    (cfg_C (powT2 a s₁) [true, true, true, false]) [target_tm]⊢⁺
      cfg_C (T3 (T12 (powT2 (a + 1) s₂))) [true, true, true, false] :=
  stepStar_stepPlus_stepPlus (c_pop_T2 a s₁ [true, true, true, false])
    (stepPlus_trans (h (powTrue a [true, true, true, false])) (b_carry_end a s₂))

theorem run_CarryRun {n : Nat} {s₁ s₂ : LB} (h : CarryRun n s₁ s₂) (a : Nat) :
    (cfg_C (powT2 a s₁) [true, true, true, false]) [target_tm]⊢⁺
      cfg_C (T3 (T12 (powT2 (a + n + 1) s₂))) [true, true, true, false] := by
  obtain ⟨mid, hm, hc⟩ := h
  exact stepStar_stepPlus_stepPlus (run_NormSteps hm a) (run_StepCarry hc (a + n))

def N : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * N k + 3

def ChainA : Nat → LB
  | 0 => T3 (powT2 2 (T12 default))
  | k + 1 => T3 (powT2 (2 * N (k + 1) + 3) (ChainA k))

def ChainB : Nat → LB
  | 0 => T3 default
  | k + 1 => T3 (powT2 (N (k + 1) + 2) (ChainB k))

def ChainC : Nat → LB
  | 0 => T3 (powT2 4 (T4 default))
  | k + 1 => T3 (powT2 (3 * N (k + 1) + 4) (ChainC k))

def TopA (k : Nat) : LB := T3 (T12 (powT2 (2 * N (k + 1) + 1) (ChainA k)))
def TopB (k : Nat) : LB := T3 (T12 (powT2 (N (k + 2)) (ChainB (k + 1))))
def State (k : Nat) : Cfg (Fin 2) (Fin 6) :=
  cfg_C (powT2 (N (k + 1)) (ChainC k)) [true, true, true, false]

theorem carryRun_base12 : CarryRun 2 (T3 (T12 (T12 default))) (T3 default) :=
  ⟨T6 (T12 default),
    NormSteps.succ (stepNorm_3_12 _) (NormSteps.succ (stepNorm_322 _) (NormSteps.zero _)),
    fun R => rule_C_6_12 R⟩

theorem normSteps_base3 : NormSteps 3 (T3 (T12 (powT2 3 (T3 default)))) (ChainC 0) :=
  NormSteps.succ (stepNorm_3_12 _)
    (NormSteps.succ (stepNorm_322 _)
      (NormSteps.succ (fun R => rule_C_6_3 R) (NormSteps.zero _)))

theorem carryRun_base4 : CarryRun 3 (ChainC 0) (ChainA 0) :=
  ⟨T6 (powT2 2 (T4 default)),
    NormSteps.succ (stepNorm_3_22 2 (T4 default))
      (NormSteps.succ (stepNorm_3_12 _)
        (NormSteps.succ (stepNorm_322 _) (NormSteps.zero _))),
    fun R => rule_C_6_4 R⟩

theorem phase1_chain (k : Nat) : CarryRun (N (k + 1)) (ChainA k) (ChainB k) := by
  induction k with
  | zero =>
    obtain ⟨mid, hm, hc⟩ := carryRun_base12
    exact ⟨mid, NormSteps.succ (stepNorm_3_22 0 (T12 default)) hm, hc⟩
  | succ k ih =>
    have h := lift_CarryRun ih (N (k + 1) + 1)
    have heq1 : 4 * N (k + 1) + 3 = N (k + 2) := rfl
    have heq2 : (N (k + 1) + 1) + N (k + 1) + 2 = 2 * N (k + 1) + 3 := by omega
    have heq3 : (N (k + 1) + 1) + 1 = N (k + 1) + 2 := by omega
    rw [heq1, heq2, heq3] at h
    exact h

theorem phase1_top (k : Nat) : CarryRun (4 * N (k + 1) + 2) (TopA k) (ChainB (k + 1)) := by
  have h := lift_CarryRun_T3_12 (phase1_chain k) (N (k + 1) + 1)
  have heq1 : (N (k + 1) + 1) + N (k + 1) = 2 * N (k + 1) + 1 := by omega
  have heq2 : (N (k + 1) + 1) + 1 = N (k + 1) + 2 := by omega
  rw [heq1, heq2] at h
  exact h

theorem phase2_chain (k : Nat) : NormSteps (N (k + 1) + 1) (ChainB (k + 1)) (ChainC k) := by
  induction k with
  | zero =>
    exact NormSteps.succ (stepNorm_3_22 3 (T3 default)) normSteps_base3
  | succ k ih =>
    have h := lift_NormSteps ih (3 * N (k + 1) + 3)
    have heq1 : 4 * (N (k + 1) + 1) = N (k + 2) + 1 := by simp [N]; omega
    have heq2 : (3 * N (k + 1) + 3) + (N (k + 1) + 1) + 1 = N (k + 2) + 2 := by simp [N]; omega
    have heq3 : (3 * N (k + 1) + 3) + 1 = 3 * N (k + 1) + 4 := by omega
    rw [heq1, heq2, heq3] at h
    exact h

theorem phase2_top (k : Nat) : NormSteps (N (k + 2)) (TopB k) (ChainC (k + 1)) := by
  have hchain := phase2_chain k
  cases hchain with
  | @succ m _ s_mid _ hstep hrest =>
    have h := lift_NormSteps_T3_12 hstep hrest (3 * N (k + 1) + 3)
    have heq1 : 4 * N (k + 1) + 3 = N (k + 2) := rfl
    have heq2 : (3 * N (k + 1) + 3) + N (k + 1) = N (k + 2) := by simp [N]; omega
    have heq3 : (3 * N (k + 1) + 3) + 1 = 3 * N (k + 1) + 4 := by omega
    rw [heq1, heq2, heq3] at h
    exact h

theorem phase3_chain (k : Nat) : CarryRun (N (k + 1)) (ChainC k) (ChainA k) := by
  induction k with
  | zero => exact carryRun_base4
  | succ k ih =>
    have h := lift_CarryRun ih (2 * N (k + 1) + 2)
    have heq1 : 4 * N (k + 1) + 3 = N (k + 2) := rfl
    have heq2 : (2 * N (k + 1) + 2) + N (k + 1) + 2 = 3 * N (k + 1) + 4 := by omega
    have heq3 : (2 * N (k + 1) + 2) + 1 = 2 * N (k + 1) + 3 := by omega
    rw [heq1, heq2, heq3] at h
    exact h

theorem state_step (k : Nat) : (State k) [target_tm]⊢⁺ State (k + 1) := by
  have h3 := run_CarryRun (phase3_chain k) (N (k + 1))
  have heq3 : N (k + 1) + N (k + 1) + 1 = 2 * N (k + 1) + 1 := by omega
  rw [heq3] at h3
  have h1 := run_CarryRun (phase1_top k) 0
  have heq1 : 0 + (4 * N (k + 1) + 2) + 1 = N (k + 2) := by simp [N]
  rw [heq1] at h1
  have h2 := run_NormSteps (phase2_top k) 0
  have heq2 : 0 + N (k + 2) = N (k + 2) := Nat.zero_add _
  rw [heq2] at h2
  exact stepPlus_trans h3 (stepPlus_stepStar_stepPlus h1 h2)

theorem init_step5 : (init []) [target_tm]⊢⁺ cfg_C default [true] := by
  unfold cfg_C; rw [init_nil, encRight_true, encRight_nil]; execute 5

theorem start_to_step127 :
    (cfg_C default [true]) [target_tm]⊢⁺ cfg_C (T4 default) [true, true, true, false] :=
  stepPlus_trans (rule_C_default [true])
    (stepPlus_trans (rule_B_true default [true])
      (stepPlus_trans (rule_B_true (T2 default) [])
        (stepPlus_trans (rule_B_nil_1 ((1 : Fin 2) >> (0 : Fin 2) >> T2 default))
          (stepPlus_trans (rule_C_41 (T12 default) [])
            (stepPlus_trans (rule_C_110 (T12 default) [false])
              (stepPlus_trans (rule_C_12_0 [true, false])
                (stepPlus_trans (rule_B_carry_1_0 [false])
                  (stepPlus_trans (rule_B_false_false (T3 default) [])
                    (stepPlus_trans (rule_B_nil_1 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> T3 default))
                      (stepPlus_trans (rule_C_41 (T2 (T3 default)) [])
                        (stepPlus_trans (rule_C_110 (T2 (T3 default)) [false])
                          (stepPlus_trans (rule_C_110 (T3 default) [true, false])
                            (stepPlus_trans (rule_C_3_0 [true, true, false])
                              (stepPlus_trans (rule_B_true (T4 default) [true, false])
                                (stepPlus_trans (rule_B_true (T2 (T4 default)) [false])
                                  (rule_B_norm_exit (T4 default)))))))))))))))))

theorem step127_to_start :
    (cfg_C (T4 default) [true, true, true, false]) [target_tm]⊢⁺
      cfg_C (T3 (T12 (T12 default))) [true, true, true, false] :=
  stepPlus_trans (rule_C_41 default [true, true, true, false])
    (stepPlus_trans (rule_C_110 default [false, true, true, true, false])
      (stepPlus_trans (rule_C_default [true, false, true, true, true, false])
        (stepPlus_trans (rule_B_true default [true, false, true, true, true, false])
          (stepPlus_trans (rule_B_true (T2 default) [false, true, true, true, false])
            (stepPlus_trans (rule_B_false_true (T2 (T2 default)) [true, true, false])
              (stepPlus_trans (rule_C_3_22 default [false, true, true, false])
                (stepPlus_trans (rule_B_carry_3_true (T12 default) [true, false])
                  (stepPlus_trans (rule_B_carry_3_true (T2 (T12 default)) [false])
                    (rule_B_carry_exit (T12 default))))))))))

theorem init_to_start :
    (init []) [target_tm]⊢⁺ cfg_C (T3 (T12 (T12 default))) [true, true, true, false] :=
  stepPlus_trans init_step5 (stepPlus_trans start_to_step127 step127_to_start)

theorem init_to_state0 : (init []) [target_tm]⊢⁺ State 0 := by
  have h0 := init_to_start
  have h1 := run_CarryRun carryRun_base12 0
  have h2 := run_NormSteps normSteps_base3 0
  exact stepPlus_trans h0 (stepPlus_stepStar_stepPlus h1 h2)

lemma inv_arb_long (Inv : Cfg (Fin 2) (Fin 6) → Prop)
    (h_init : ∃ c₀, Inv c₀ ∧ ((init []) [target_tm]⊢⁺ c₀))
    (h_step : ∀ c, Inv c → ∃ c', Inv c' ∧ (c [target_tm]⊢⁺ c')) (m : ℕ) :
    ∃ n c, m ≤ n ∧ Inv c ∧ ((init []) [target_tm]⊢^{n} c) := by
  induction m with
  | zero =>
    obtain ⟨c₀, hc₀, n, _, hn⟩ := h_init
    exact ⟨n, c₀, Nat.zero_le n, hc₀, hn⟩
  | succ m ih =>
    obtain ⟨n, c, hmn, hc, hn⟩ := ih
    obtain ⟨c', hc', k, hk_pos, hk⟩ := h_step c hc
    exact ⟨n + k, c', by omega, hc', multiStep_trans hn hk⟩

lemma not_halt_of_inv (Inv : Cfg (Fin 2) (Fin 6) → Prop)
    (h_init : ∃ c₀, Inv c₀ ∧ ((init []) [target_tm]⊢⁺ c₀))
    (h_step : ∀ c, Inv c → ∃ c', Inv c' ∧ (c [target_tm]⊢⁺ c')) :
    IsNotHalt target_tm := by
  intro c ⟨m, hm⟩
  obtain ⟨n, c', hmn, _, hn⟩ := inv_arb_long Inv h_init h_step (m + 1)
  have h_add := multiStep_add target_tm (init []) (m + 1) (n - (m + 1))
  rw [Nat.add_sub_of_le hmn, multiStep_succ, hm] at h_add
  change multiStep target_tm (init []) n =
    (step target_tm c).bind (fun c₂ => multiStep target_tm c₂ (n - (m + 1))) at h_add
  cases h_step_c : step target_tm c with
  | none =>
    change multiStep target_tm (init []) n = some c' at hn
    rw [h_step_c, hn] at h_add
    cases h_add
  | some c₁ => rfl

def Valid (c : Cfg (Fin 2) (Fin 6)) : Prop := ∃ k : Nat, c = State k

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  apply not_halt_of_inv Valid
  · exact ⟨State 0, ⟨0, rfl⟩, init_to_state0⟩
  · intro c ⟨k, hk⟩
    subst hk
    exact ⟨State (k + 1), ⟨k + 1, rfl⟩, state_step k⟩

end BusyBeaver.M_1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LBHHH
