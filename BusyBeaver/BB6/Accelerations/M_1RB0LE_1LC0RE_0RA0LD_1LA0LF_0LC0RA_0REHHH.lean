/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Stack
public import BusyBeaver.WordRunStack

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.deprecated false
set_option linter.flexible false

/-!
# Busy Beaver Machine `1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---` — `is_stack_cryptid` (`IsStackCryptid target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0REHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

open BusyBeaver.PairStack Counter

lemma zero_pow_one_add (n : ℕ) :
    (([0] : List (Fin 2)) ^ (1 + n)) = (0 : Fin 2) :: (([0] : List (Fin 2)) ^ n) := by
  rw [Nat.add_comm 1 n, pow_succ_list, cons_append_list, nil_append_list]

-- ============================================================================
-- 2nd-Order Digit-Stack Encodings (`pol = 0, maxSepL = 4, maxSepR = 4`)
-- ============================================================================

def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L => (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 4))) <+ (([1] : List (Fin 2)) ^ (1 * a + 1))

def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R => (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight R)

def encTail (S : List (ℕ × ℕ)) : ListBlank (Fin 2) := (encRight S).tail

@[simp] lemma encLeft_nil : encLeft [] = default := rfl
@[simp] lemma encLeft_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 4))) <+ (([1] : List (Fin 2)) ^ (1 * a + 1)) := rfl
@[simp] lemma encRight_nil : encRight [] = default := rfl
@[simp] lemma encRight_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d, b) :: R) = (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight R) := rfl

lemma encLeft_eq_encRight (S : List (ℕ × ℕ)) : encLeft S = encRight S := by
  induction S with
  | nil => rfl
  | cons p S' ih =>
    rcases p with ⟨a, b⟩
    simp only [encLeft, encRight, ih]

@[simp] lemma encLeft_tail (S : List (ℕ × ℕ)) : (encLeft S).tail = encTail S := by
  rw [encLeft_eq_encRight]; rfl

lemma encRight_tail (S : List (ℕ × ℕ)) : (encRight S).tail = encTail S := rfl

@[simp] lemma encTail_nil : encTail [] = default := rfl

lemma encRight_cons_simp (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d, b) :: R) = (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ d) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight R)) := by
  simp only [encRight_cons, Nat.one_mul]
  rw [Nat.add_comm d 1, list_pow_add, listblank_append_right_assoc]
  rfl

lemma encRight_succ (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d + 1, b) :: R) = (1 : Fin 2) >> encRight ((d, b) :: R) := by
  simp only [encRight_cons, Nat.one_mul]
  rw [Nat.add_comm (d + 1) 1, list_pow_add, listblank_append_right_assoc]
  rfl

lemma encTail_cons (a b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((a, b) :: S) = (([1] : List (Fin 2)) ^ a) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight S) := by
  unfold encTail
  rw [encRight_cons_simp, Turing.ListBlank.tail_cons]

lemma encRight_cons_eq_one_cons_encTail (a b : ℕ) (S : List (ℕ × ℕ)) :
    encRight ((a, b) :: S) = (1 : Fin 2) >> encTail ((a, b) :: S) := by
  unfold encTail
  rw [encRight_cons_simp, Turing.ListBlank.tail_cons]

lemma encTail_zero (b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((0, b) :: S) = (([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight S := by
  rw [encTail_cons]; rfl

lemma encTail_succ (a b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((a + 1, b) :: S) = (1 : Fin 2) >> encTail ((a, b) :: S) := by
  unfold encTail
  rw [encRight_succ, Turing.ListBlank.tail_cons, encRight_cons_simp, Turing.ListBlank.tail_cons]


def tailAsRight : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: S => (a, b) :: S

def rightAsTail : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b) :: S => (a + 1, b) :: S

def pushZeroSep (b : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b') :: S => (0, b) :: (a, b') :: S

def peelSep (k : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b') :: S =>
    if k % 4 = 0 then (a + 1, b') :: S
    else (0, k % 4 - 1) :: (a, b') :: S

def peelInner (b : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a₂, b₂) :: rs =>
    if b % 4 = 1 then (a₂ + 1, b₂) :: rs
    else if b % 4 = 2 then (0, 0) :: (a₂, b₂) :: rs
    else (0, 1) :: (a₂, b₂) :: rs

lemma encRight_bumpHead (S : List (ℕ × ℕ)) :
    encRight (bumpHead S) = (1 : Fin 2) >> encRight S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · simp [bumpHead]
  · exact encRight_succ a b S'

lemma encRight_tailAsRight (S : List (ℕ × ℕ)) :
    encRight (tailAsRight S) = (1 : Fin 2) >> encTail S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · simp [tailAsRight]
  · exact encRight_cons_eq_one_cons_encTail a b S'

lemma encTail_rightAsTail (S : List (ℕ × ℕ)) :
    encTail (rightAsTail S) = encRight S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · rfl
  · unfold encTail rightAsTail
    rw [encRight_succ, Turing.ListBlank.tail_cons]

lemma encTail_pushZeroSep (b : ℕ) (hb : b < 4) (S : List (ℕ × ℕ)) :
    encTail (pushZeroSep b S) = (([0] : List (Fin 2)) ^ (1 + b)) +> encRight S := by
  rcases S with _ | ⟨⟨a, b'⟩, S'⟩
  · simp [pushZeroSep]
  · rw [pushZeroSep, encTail_zero, Nat.mod_eq_of_lt hb]

lemma encTail_peelSep (k : ℕ) (S : List (ℕ × ℕ)) :
    encTail (peelSep k S) = (([0] : List (Fin 2)) ^ (k % 4)) +> encRight S := by
  rcases S with _ | ⟨⟨a, b'⟩, S'⟩
  · simp [peelSep]
  · rcases mod4_cases k with h0 | h1 | h2 | h3
    · rw [peelSep, if_pos h0, h0, encTail_succ, encRight_cons_eq_one_cons_encTail]
      rfl
    · simp [peelSep, h1, encTail_zero]
    · simp [peelSep, h2, encTail_zero]
    · simp [peelSep, h3, encTail_zero]

lemma peelInner_ne_nil (b : ℕ) (S : List (ℕ × ℕ)) : peelInner b S ≠ [] := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · simp [peelInner]
  · dsimp [peelInner]
    split_ifs <;> simp

lemma encRight_zero_peelInner (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    encRight ((0, b) :: S) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail (peelInner b S) := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · simp [peelInner, encTail_zero]
  · rcases mod4_cases b with h0 | h1 | h2 | h3
    · rcases h with hnil | hne
      · contradiction
      · exact False.elim (hne h0)
    · rw [peelInner, if_pos h1, encRight_cons_simp 0 b, h1, encTail_succ,
        encRight_cons_eq_one_cons_encTail]
      rfl
    · have h1 : b % 4 ≠ 1 := by omega
      rw [peelInner, if_neg h1, if_pos h2, encRight_cons_simp 0 b, h2, encTail_zero]
      rfl
    · have h1 : b % 4 ≠ 1 := by omega
      have h2 : b % 4 ≠ 2 := by omega
      rw [peelInner, if_neg h1, if_neg h2, encRight_cons_simp 0 b, h3, encTail_zero]
      rfl

lemma encRight_one_peelInner (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    encRight ((1, b) :: S) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail (peelInner b S) := by
  rw [encRight_succ 0 b S, encRight_zero_peelInner b S h]

-- ============================================================================
-- Stack System Definition & Witness Checks
-- ============================================================================

def cfg_M0 (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨0, (encLeft L).tail, (encRight R).tail⟩⟩

inductive StackMode
  | M0
deriving DecidableEq

def evalStackCfg : StackMode → List (ℕ × ℕ) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .M0, L, R => cfg_M0 L R

def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

lemma cfg_M0_eq (L R : List (ℕ × ℕ)) :
    cfg_M0 L R = ⟨some A, ⟨0, encTail L, encTail R⟩⟩ := by
  simp [cfg_M0, encRight_tail]

lemma valid_stack_modes : IsValidStackModes encLeft encRight evalStackCfg := by
  intro m
  cases m with
  | M0 => exact ⟨A, .tail [], .tail [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

theorem audit_encRight_head (d b : ℕ) (R : List (ℕ × ℕ)) :
    (encRight ((d, b) :: R)).head = 1 := by
  rw [encRight_cons_simp, Turing.ListBlank.head_cons]

theorem audit_encLeft_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: L)).head = 1 := by
  rw [encLeft_eq_encRight]
  exact audit_encRight_head a b L

theorem audit_encRight_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ R : List (ℕ × ℕ), encRight R ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro R h
  rcases R with _ | ⟨⟨_ | d, b⟩, R'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rcases R' with _ | ⟨⟨d', b'⟩, R''⟩
    · rw [encRight_cons_simp] at h
      have h1 := congrArg (fun s => s.tail.tail.tail.tail.tail.tail.head) h
      simp at h1
    · rcases mod4_cases b with h0 | h1 | h2 | h3
      · rw [encRight_cons_simp, h0] at h
        have hc := congrArg (fun s => s.tail.tail.head) h
        simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
          listblank_append_nil, listblank_append_cons, Turing.ListBlank.tail_cons,
          Turing.ListBlank.head_cons, audit_encRight_head] at hc
        contradiction
      · rw [encRight_cons_simp, h1] at h
        have hc := congrArg (fun s => s.tail.tail.tail.head) h
        simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
          listblank_append_nil, listblank_append_cons, Turing.ListBlank.tail_cons,
          Turing.ListBlank.head_cons, audit_encRight_head] at hc
        contradiction
      · rw [encRight_cons_simp, h2] at h
        have hc := congrArg (fun s => s.tail.tail.tail.tail.head) h
        simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
          listblank_append_nil, listblank_append_cons, Turing.ListBlank.tail_cons,
          Turing.ListBlank.head_cons, audit_encRight_head] at hc
        contradiction
      · rw [encRight_cons_simp, h3] at h
        have hc := congrArg (fun s => s.tail.tail.tail.tail.tail.head) h
        simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
          listblank_append_nil, listblank_append_cons, Turing.ListBlank.tail_cons,
          Turing.ListBlank.head_cons, audit_encRight_head] at hc
        contradiction
  · rw [encRight_succ] at h
    have hc := congrArg (fun s => s.tail.head) h
    simp only [Turing.ListBlank.tail_cons, Turing.ListBlank.head_cons, audit_encRight_head] at hc
    contradiction

theorem audit_encLeft_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ L : List (ℕ × ℕ), encLeft L ≠ t := by
  obtain ⟨t, ht, hR⟩ := audit_encRight_not_surjective
  exact ⟨t, ht, fun L hL => hR L (by rwa [← encLeft_eq_encRight])⟩

-- ============================================================================
-- Execution Tactics & Initial Reachability
-- ============================================================================

macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
    zero_cons_default, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]
  try rfl))

macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))

macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

lemma F_halt_on_one (tL rD : ListBlank (Fin 2)) :
    (step target_tm (((1 : Fin 2) >> tL) <{{F}} rD)).isNone = true := by
  unfold step
  simp only [Turing.ListBlank.head_cons, F, target_tm, Option.map_none, Option.isNone_none]

theorem init_reaches_stack_system :
    ∃ cfg₀, ((init []) [target_tm]⊢⁺ cfg₀) ∧ IsInStackSystem cfg₀ := by
  refine ⟨cfg_M0 [] [(1, 0), (0, 0)], ?_, ⟨.M0, [], [(1, 0), (0, 0)], rfl⟩⟩
  rw [init_nil, cfg_M0_eq, encTail_nil, encTail_succ, encTail_zero, encRight_cons_simp]
  simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
    listblank_append_nil, listblank_append_cons, encRight_nil, zero_cons_default]
  execute 4

-- ============================================================================
-- Intermediate Configurations (`cfg_D`, `wall`, `P_cfg`, `F_cfg`)
-- ============================================================================

def cfg_D (c : ℕ) (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encTail L) <{{D}} ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R))

def wall (L'' : List (ℕ × ℕ)) : ListBlank (Fin 2) :=
  (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail L''

def P_cfg (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨0, W +> wall L'', encRight R⟩⟩

inductive FState
  | F00 | F01 | F02 | F04 | F05 | F07
deriving DecidableEq

def F_cfg : FState → List (ℕ × ℕ) → List (Fin 2) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .F00, L'', W, R => (W +> wall L'') <{{E}} ((0 : Fin 2) >> encRight R)
  | .F01, L'', W, R => (W +> wall L'') <{{F}} ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F02, L'', W, R => (W +> wall L'') <{{C}} ((0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F04, L'', W, R => (W +> wall L'') <{{A}} ((1 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F05, L'', W, R => (W +> wall L'') <{{D}} ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F07, L'', W, R => (W +> wall L'') <{{A}} ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)

-- ============================================================================
-- Stage 1: `cfg_M0 L R` -> `cfg_M0` or `cfg_D 0`
-- ============================================================================

lemma M0_nil (L : List (ℕ × ℕ)) :
    (cfg_M0 L []) [target_tm]⊢⁺ cfg_D 0 L [] := by
  rw [cfg_M0_eq, cfg_D, encTail_nil]
  execute 3

lemma M0_zero (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((0, bR) :: R')) [target_tm]⊢⁺ cfg_D 0 L (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_D, encTail_zero, zero_pow_one_add (bR % 4),
    listblank_append_cons, ← encTail_peelSep]
  execute 3

lemma M0_one (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((1, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: tailAsRight L) (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ, encTail_zero, encTail_zero 0 (tailAsRight L),
    encRight_tailAsRight, zero_pow_one_add (bR % 4), listblank_append_cons,
    ← encTail_peelSep]
  execute 4

lemma M0_two (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((2, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 1) :: tailAsRight L) (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ 1, encTail_succ 0, encTail_zero bR,
    encTail_zero 1 (tailAsRight L), encRight_tailAsRight, zero_pow_one_add (bR % 4),
    listblank_append_cons, ← encTail_peelSep]
  execute 3

lemma M0_three_lt3 (L : List (ℕ × ℕ)) (bR : ℕ) (hb : bR % 4 < 3) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((3, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: tailAsRight L) (pushZeroSep (bR % 4 + 1) R') := by
  have hb4 : bR % 4 + 1 < 4 := by omega
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ 2, encTail_succ 1, encTail_succ 0,
    encTail_zero bR, encTail_zero 0 (tailAsRight L), encRight_tailAsRight, encTail_pushZeroSep _ hb4]
  have hpow : 1 + (bR % 4 + 1) = 1 + (1 + bR % 4) := by omega
  rw [hpow, zero_pow_one_add (1 + bR % 4), listblank_append_cons]
  execute 6

lemma M0_three_eq3_nil (L : List (ℕ × ℕ)) (bR : ℕ) (hb : bR % 4 = 3) :
    (cfg_M0 L [(3, bR)]) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: tailAsRight L) [] := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ 2, encTail_succ 1, encTail_succ 0,
    encTail_zero bR, hb, encTail_zero 0 (tailAsRight L), encRight_tailAsRight, encRight_nil, encTail_nil]
  execute 6

lemma M0_three_eq3_cons (L : List (ℕ × ℕ)) (bR : ℕ) (hb : bR % 4 = 3) (d₂ b₂ : ℕ) (R'' : List (ℕ × ℕ)) :
    (cfg_M0 L ((3, bR) :: (d₂, b₂) :: R'')) [target_tm]⊢⁺ cfg_D 0 ((0, 0) :: tailAsRight L) ((0, 3) :: (d₂, b₂) :: R'') := by
  rw [cfg_M0_eq, cfg_D, encTail_succ 2, encTail_succ 1, encTail_succ 0,
    encTail_zero bR, hb, encTail_zero 0 (tailAsRight L), encRight_tailAsRight, encTail_zero 3]
  execute 9

lemma M0_add4 (L : List (ℕ × ℕ)) (d bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((d + 4, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: tailAsRight L) ((0, 0) :: (d, bR) :: R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ (d + 3), encTail_succ (d + 2),
    encTail_succ (d + 1), encTail_succ d, encTail_zero 0 (tailAsRight L), encRight_tailAsRight,
    encTail_zero 0 ((d, bR) :: R'), encRight_cons_eq_one_cons_encTail]
  execute 6

theorem stage1_step (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_M0 L R) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ ∃ L' R', cfg' = cfg_D 0 L' R') := by
  rcases R with _ | ⟨⟨d, bR⟩, R'⟩
  · exact ⟨_, M0_nil L, Or.inr ⟨L, [], rfl⟩⟩
  · rcases d with _ | _ | _ | _ | d'
    · exact ⟨_, M0_zero L bR R', Or.inr ⟨L, peelSep bR R', rfl⟩⟩
    · exact ⟨_, M0_one L bR R', Or.inl ⟨.M0, (0, 0) :: tailAsRight L, peelSep bR R', rfl⟩⟩
    · exact ⟨_, M0_two L bR R', Or.inl ⟨.M0, (0, 1) :: tailAsRight L, peelSep bR R', rfl⟩⟩
    · rcases mod4_cases bR with h0 | h1 | h2 | h3
      · exact ⟨_, M0_three_lt3 L bR (by omega) R', Or.inl ⟨.M0, (0, 0) :: tailAsRight L, _, rfl⟩⟩
      · exact ⟨_, M0_three_lt3 L bR (by omega) R', Or.inl ⟨.M0, (0, 0) :: tailAsRight L, _, rfl⟩⟩
      · exact ⟨_, M0_three_lt3 L bR (by omega) R', Or.inl ⟨.M0, (0, 0) :: tailAsRight L, _, rfl⟩⟩
      · rcases R' with _ | ⟨⟨d₂, b₂⟩, R''⟩
        · exact ⟨_, M0_three_eq3_nil L bR h3, Or.inl ⟨.M0, (0, 0) :: tailAsRight L, [], rfl⟩⟩
        · exact ⟨_, M0_three_eq3_cons L bR h3 d₂ b₂ R'', Or.inr ⟨(0, 0) :: tailAsRight L, (0, 3) :: (d₂, b₂) :: R'', rfl⟩⟩
    · exact ⟨_, M0_add4 L d' bR R', Or.inl ⟨.M0, (0, 0) :: tailAsRight L, (0, 0) :: (d', bR) :: R', rfl⟩⟩

-- ============================================================================
-- Stage 2: `cfg_D c L R` (`c < 4`) -> `cfg_M0`, Halt, or `P_cfg`
-- ============================================================================

lemma RD_eq_encRight (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      encRight ((0, c) :: tailAsRight R) := by
  rw [encRight_cons_simp, Nat.mod_eq_of_lt hc, encRight_tailAsRight]
  rfl

lemma RD_eq_encTail_one (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      encTail ((1, c) :: tailAsRight R) := by
  rw [encTail_succ, encTail_zero, Nat.mod_eq_of_lt hc, encRight_tailAsRight]

lemma one_cons_RD_eq (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      (1 : Fin 2) >> encTail ((0, c) :: tailAsRight R) := by
  rw [encTail_zero, Nat.mod_eq_of_lt hc, encRight_tailAsRight]

lemma D_leaf_00 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (0 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, tL, (1 : Fin 2) >> rD⟩⟩ := by
  execute 1

lemma D_leaf_0100 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> tL, (0 : Fin 2) >> (1 : Fin 2) >> rD⟩⟩ := by
  execute 4

lemma D_leaf_0101 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      (tL <{{D}} ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rD)) := by
  execute 4

lemma D_leaf_011 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> tL, (1 : Fin 2) >> rD⟩⟩ := by
  execute 3

lemma D_leaf_10 (tL rD : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> (0 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> tL, rD⟩⟩ := by
  execute 4

lemma D_leaf_11 (tL rD : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> (1 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      (((1 : Fin 2) >> tL) <{{F}} ((0 : Fin 2) >> rD)) := by
  execute 1

lemma D_step_one (c : ℕ) (hc : c < 4) (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_D c L R) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone ∨
       (∃ L'' R_P, R_P ≠ [] ∧ cfg' = P_cfg L'' [] R_P) ∨
       (∃ c' L' R', c' < 4 ∧ L'.length < L.length ∧ cfg' = cfg_D c' L' R')) := by
  unfold cfg_D
  set rD := (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)
  have hrD_right : (1 : Fin 2) >> rD = encRight ((0, c) :: tailAsRight R) := RD_eq_encRight c hc R
  have hrD_tail : (1 : Fin 2) >> rD = encTail ((1, c) :: tailAsRight R) := RD_eq_encTail_one c hc R
  have hrD_one : (1 : Fin 2) >> rD = (1 : Fin 2) >> encTail ((0, c) :: tailAsRight R) := one_cons_RD_eq c hc R
  have hrD_zero : rD = encTail ((0, c) :: tailAsRight R) := by
    rw [encTail_zero, Nat.mod_eq_of_lt hc, encRight_tailAsRight]
  rcases L with _ | ⟨⟨a₁, b₁⟩, L'⟩
  · -- L = []
    have hL : encTail [] = (0 : Fin 2) >> (0 : Fin 2) >> encTail [] := by simp
    rw [hL]
    refine ⟨cfg_M0 [] ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, [], (1, c) :: tailAsRight R, rfl⟩⟩
    rw [cfg_M0_eq, ← hrD_tail]
    exact D_leaf_00 (encTail []) rD
  · rcases a₁ with _ | _ | a₁'
    · -- a₁ = 0
      rcases L' with _ | ⟨⟨a₂, b₂⟩, L''⟩
      · -- L = [(0, b₁)]
        have hL : encTail [(0, b₁)] = (0 : Fin 2) >> (0 : Fin 2) >> encTail [] := by
          simp [encTail_zero]
        rw [hL]
        refine ⟨cfg_M0 [] ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, [], (1, c) :: tailAsRight R, rfl⟩⟩
        rw [cfg_M0_eq, ← hrD_tail]
        exact D_leaf_00 (encTail []) rD
      · rcases mod4_cases b₁ with hb0 | hb1 | hb2 | hb3
        · -- b₁ % 4 = 0, L = (0, b₁) :: (a₂, b₂) :: L''
          rcases a₂ with _ | _ | a₂'
          · -- a₂ = 0
            rcases L'' with _ | ⟨⟨a₃, b₃⟩, L'''⟩
            · -- L = [(0, b₁), (0, b₂)]
              have hL : encTail [(0, b₁), (0, b₂)] =
                  (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default := by
                simp [encTail_zero, hb0]
              rw [hL]
              refine ⟨cfg_M0 [] ((0, 0) :: (0, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, [], _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_nil, encTail_zero, zero_pow_one_add 0, pow_zero_list,
                listblank_append_cons, listblank_append_nil, ← hrD_right]
              have hd := D_leaf_0100 default rD
              simpa using hd
            · rcases mod4_cases b₂ with h20 | h21 | h22 | h23
              · -- b₂ % 4 = 0 -> cfg_D 2 ((a₃, b₃) :: L''') ((0, c) :: tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₃, b₃) :: L''') := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h20,
                    encRight_cons_eq_one_cons_encTail]
                  rfl
                rw [hL]
                refine ⟨cfg_D 2 ((a₃, b₃) :: L''') ((0, c) :: tailAsRight R), ?_,
                  Or.inr (Or.inr (Or.inr ⟨2, (a₃, b₃) :: L''', (0, c) :: tailAsRight R, by decide, by simp, rfl⟩))⟩
                unfold cfg_D
                dsimp only [pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
                  listblank_append_cons, listblank_append_nil]
                rw [← hrD_one]
                exact D_leaf_0101 (encTail ((a₃, b₃) :: L''')) rD
              · -- b₂ % 4 = 1 -> cfg_M0 ((0, 0) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight ((a₃, b₃) :: L''') := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h21]
                  rfl
                rw [hL]
                refine ⟨cfg_M0 ((0, 0) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 0 ((a₃, b₃) :: L'''), encTail_zero 0 ((0, c) :: tailAsRight R)]
                simpa [hrD_right] using D_leaf_0100 (encRight ((a₃, b₃) :: L''')) rD
              · -- b₂ % 4 = 2 -> cfg_M0 ((0, 1) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> encRight ((a₃, b₃) :: L''')) := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h22]
                  rfl
                rw [hL]
                refine ⟨cfg_M0 ((0, 1) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 1 ((a₃, b₃) :: L'''), encTail_zero 0 ((0, c) :: tailAsRight R)]
                simpa [hrD_right] using D_leaf_0100 ((0 : Fin 2) >> encRight ((a₃, b₃) :: L''')) rD
              · -- b₂ % 4 = 3 -> cfg_M0 ((0, 2) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (0 : Fin 2) >> encRight ((a₃, b₃) :: L''')) := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h23]
                  rfl
                rw [hL]
                refine ⟨cfg_M0 ((0, 2) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 2 ((a₃, b₃) :: L'''), encTail_zero 0 ((0, c) :: tailAsRight R)]
                simpa [hrD_right] using D_leaf_0100 ((0 : Fin 2) >> (0 : Fin 2) >> encRight ((a₃, b₃) :: L''')) rD
          · -- a₂ = 1
            rcases mod4_cases b₂ with h20 | h21 | h22 | h23
            · -- b₂ % 4 = 0 -> pushZeroSep 1 L''
              have hL : encTail ((0, b₁) :: (1, b₂) :: L'') =
                  (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> encRight L'') := by
                rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ, encTail_zero, h20]
                rfl
              rw [hL]
              refine ⟨cfg_M0 (pushZeroSep 1 L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_pushZeroSep 1 (by decide) L'', ← hrD_tail]
              simpa using D_leaf_011 ((0 : Fin 2) >> encRight L'') rD
            · -- b₂ % 4 = 1 -> pushZeroSep 2 L''
              have hL : encTail ((0, b₁) :: (1, b₂) :: L'') =
                  (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (0 : Fin 2) >> encRight L'') := by
                rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ, encTail_zero, h21]
                rfl
              rw [hL]
              refine ⟨cfg_M0 (pushZeroSep 2 L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_pushZeroSep 2 (by decide) L'', ← hrD_tail]
              simpa using D_leaf_011 ((0 : Fin 2) >> (0 : Fin 2) >> encRight L'') rD
            · -- b₂ % 4 = 2 -> pushZeroSep 3 L''
              have hL : encTail ((0, b₁) :: (1, b₂) :: L'') =
                  (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight L'') := by
                rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ, encTail_zero, h22]
                rfl
              rw [hL]
              refine ⟨cfg_M0 (pushZeroSep 3 L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_pushZeroSep 3 (by decide) L'', ← hrD_tail]
              simpa using D_leaf_011 ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight L'') rD
            · -- b₂ % 4 = 3: split L'' = [] vs (a₃, b₃) :: L'''
              rcases L'' with _ | ⟨⟨a₃, b₃⟩, L'''⟩
              · have hL : encTail [(0, b₁), (1, b₂)] =
                    (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> default := by
                  simp [encTail_zero, hb0, h23]
                rw [hL]
                refine ⟨cfg_M0 [] ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, [], _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_nil, ← hrD_tail]
                simpa using D_leaf_011 default rD
              · -- P_cfg ((a₃, b₃) :: L''') [] ((0, c) :: tailAsRight R)
                have hL : encTail ((0, b₁) :: (1, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₃, b₃) :: L''')) := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ,
                    encTail_zero, h23, encRight_cons_eq_one_cons_encTail]
                  rfl
                rw [hL]
                refine ⟨P_cfg ((a₃, b₃) :: L''') [] ((0, c) :: tailAsRight R), ?_,
                  Or.inr (Or.inr (Or.inl ⟨(a₃, b₃) :: L''', (0, c) :: tailAsRight R, by simp, rfl⟩))⟩
                unfold P_cfg wall
                rw [listblank_append_nil, ← hrD_right]
                exact D_leaf_011 _ rD
          · -- a₂ = a₂' + 2 -> cfg_M0 ((0, 0) :: (a₂', b₂) :: L'') ((1, c) :: tailAsRight R)
            have hL : encTail ((0, b₁) :: (a₂' + 2, b₂) :: L'') =
                (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((1 : Fin 2) >> encTail ((a₂', b₂) :: L'')) := by
              rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ (a₂' + 1), encTail_succ a₂']
              rfl
            rw [hL]
            refine ⟨cfg_M0 ((0, 0) :: (a₂', b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
            rw [cfg_M0_eq, encTail_zero 0 ((a₂', b₂) :: L''), encRight_cons_eq_one_cons_encTail, ← hrD_tail]
            simpa using D_leaf_011 ((1 : Fin 2) >> encTail ((a₂', b₂) :: L'')) rD
        · -- b₁ % 4 = 1 -> Leaf 00, L' = (a₂ + 1, b₂) :: L''
          have hL : encTail ((0, b₁) :: (a₂, b₂) :: L'') =
              (0 : Fin 2) >> (0 : Fin 2) >> encTail ((a₂ + 1, b₂) :: L'') := by
            rw [encTail_zero, hb1, encTail_succ, encRight_cons_eq_one_cons_encTail]
            rfl
          rw [hL]
          refine ⟨cfg_M0 ((a₂ + 1, b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
          rw [cfg_M0_eq, ← hrD_tail]
          exact D_leaf_00 _ rD
        · -- b₁ % 4 = 2 -> Leaf 00, L' = (0, 0) :: (a₂, b₂) :: L''
          have hL : encTail ((0, b₁) :: (a₂, b₂) :: L'') =
              (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, 0) :: (a₂, b₂) :: L'') := by
            rw [encTail_zero, hb2, encTail_zero]
            rfl
          rw [hL]
          refine ⟨cfg_M0 ((0, 0) :: (a₂, b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
          rw [cfg_M0_eq, ← hrD_tail]
          exact D_leaf_00 _ rD
        · -- b₁ % 4 = 3 -> Leaf 00, L' = (0, 1) :: (a₂, b₂) :: L''
          have hL : encTail ((0, b₁) :: (a₂, b₂) :: L'') =
              (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, 1) :: (a₂, b₂) :: L'') := by
            rw [encTail_zero, hb3, encTail_zero]
            rfl
          rw [hL]
          refine ⟨cfg_M0 ((0, 1) :: (a₂, b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
          rw [cfg_M0_eq, ← hrD_tail]
          exact D_leaf_00 _ rD
    · -- a₁ = 1 -> Leaf 10 bounces directly in 4 steps to cfg_M0 ((0, b₁) :: L') ((0, c) :: tailAsRight R)
      have hL : encTail ((1, b₁) :: L') =
          (1 : Fin 2) >> (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ (b₁ % 4)) +> encRight L') := by
        rw [encTail_succ, encTail_zero, zero_pow_one_add (b₁ % 4), listblank_append_cons]
      have hL0 : (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ (b₁ % 4)) +> encRight L') = encTail ((0, b₁) :: L') := by
        rw [encTail_zero, zero_pow_one_add (b₁ % 4), listblank_append_cons]
      rw [hL]
      refine ⟨cfg_M0 ((0, b₁) :: L') ((0, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
      rw [cfg_M0_eq, ← hL0, ← hrD_zero]
      exact D_leaf_10 _ rD
    · -- a₁ = a₁' + 2 -> Leaf 11 -> Halts in 1 step!
      have hL : encTail ((a₁' + 2, b₁) :: L') =
          (1 : Fin 2) >> (1 : Fin 2) >> encTail ((a₁', b₁) :: L') := by
        rw [encTail_succ (a₁' + 1), encTail_succ a₁']
      rw [hL]
      refine ⟨((1 : Fin 2) >> encTail ((a₁', b₁) :: L')) <{{F}} ((0 : Fin 2) >> rD),
        D_leaf_11 _ rD, Or.inr (Or.inl (F_halt_on_one _ _))⟩

theorem stage2_closed (n : ℕ) :
    ∀ L, L.length ≤ n → ∀ c < 4, ∀ R,
      ∃ cfg', ((cfg_D c L R) [target_tm]⊢⁺ cfg') ∧
        (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone ∨
         (∃ L'' R_P, R_P ≠ [] ∧ cfg' = P_cfg L'' [] R_P)) := by
  induction n with
  | zero =>
    intro L hlen c hc R
    obtain ⟨cfg', hstep, hout⟩ := D_step_one c hc L R
    rcases hout with hM | hH | hP | ⟨c', L', R', _, hlt, _⟩
    · exact ⟨cfg', hstep, Or.inl hM⟩
    · exact ⟨cfg', hstep, Or.inr (Or.inl hH)⟩
    · exact ⟨cfg', hstep, Or.inr (Or.inr hP)⟩
    · omega
  | succ n' ih =>
    intro L hlen c hc R
    obtain ⟨cfg', hstep, hout⟩ := D_step_one c hc L R
    rcases hout with hM | hH | hP | ⟨c', L', R', hc', hlt, rfl⟩
    · exact ⟨cfg', hstep, Or.inl hM⟩
    · exact ⟨cfg', hstep, Or.inr (Or.inl hH)⟩
    · exact ⟨cfg', hstep, Or.inr (Or.inr hP)⟩
    · obtain ⟨cfg'', hstep2, hout2⟩ := ih L' (by omega) c' hc' R'
      exact ⟨cfg'', stepPlus_trans hstep hstep2, hout2⟩

-- ============================================================================
-- Stage 3: Pushdown Induction (`P_cfg` and `F_cfg` -> `cfg_M0` or Halt)
-- ============================================================================

def w : List (ℕ × ℕ) → ℕ
  | [] => 0
  | [(a, _)] => a
  | (a, b) :: r₂ :: rs => a + b % 2 + w (r₂ :: rs)

def C0 : FState → ℕ
  | .F00 => 0 | .F01 => 1 | .F02 => 1 | .F04 => 1 | .F05 => 0 | .F07 => 1

def C1 : FState → ℕ
  | .F00 => 1 | .F01 => 2 | .F02 => 0 | .F04 => 0 | .F05 => 1 | .F07 => 0

lemma C0_le_C1_succ (s : FState) : C0 s ≤ C1 s + 1 := by
  cases s <;> decide

lemma C1_le_C0_succ (s : FState) : C1 s ≤ C0 s + 1 := by
  cases s <;> decide

lemma w_cons_nonempty (a b : ℕ) (R : List (ℕ × ℕ)) (hR : R ≠ []) :
    w ((a, b) :: R) = a + b % 2 + w R := by
  rcases R with _ | ⟨r₂, rs⟩
  · contradiction
  · rfl

lemma w_bumpHead (R : List (ℕ × ℕ)) (hR : R ≠ []) :
    w (bumpHead R) = 1 + w R := by
  rcases R with _ | ⟨⟨a, b⟩, rs⟩
  · contradiction
  · rcases rs with _ | ⟨r₂, rs'⟩
    · simp [bumpHead, w]; omega
    · simp [bumpHead, w]; omega

lemma w_peelInner_zero (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    w ((0, 0) :: peelInner b S) = w ((0, b) :: S) := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · rfl
  · rcases mod4_cases b with h0 | h1 | h2 | h3
    · rcases h with hnil | hne
      · contradiction
      · exact False.elim (hne h0)
    · have hb2 : b % 2 = 1 := by omega
      have hne : ((a₂ + 1, b₂) :: rs) ≠ [] := by simp
      rw [peelInner, if_pos h1, w_cons_nonempty 0 0 _ hne, w_cons_nonempty 0 b _ (by simp)]
      have hbmp : w ((a₂ + 1, b₂) :: rs) = 1 + w ((a₂, b₂) :: rs) := w_bumpHead ((a₂, b₂) :: rs) (by simp)
      rw [hbmp, hb2]; omega
    · have hb2 : b % 2 = 0 := by omega
      have h1 : b % 4 ≠ 1 := by omega
      rw [peelInner, if_neg h1, if_pos h2]
      simp [w, hb2]
    · have hb2 : b % 2 = 1 := by omega
      have h1 : b % 4 ≠ 1 := by omega
      have h2 : b % 4 ≠ 2 := by omega
      rw [peelInner, if_neg h1, if_neg h2]
      simp [w, hb2]

lemma w_peelInner_one (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    w ((0, 0) :: peelInner b S) + 1 = w ((1, b) :: S) := by
  rw [w_peelInner_zero b S h]
  rcases S with _ | ⟨r₂, rs⟩
  · simp [w]
  · simp [w]; omega

lemma w_ge2 (a b : ℕ) (S : List (ℕ × ℕ)) :
    w ((0, 0) :: (a, b) :: S) + 2 = w ((a + 2, b) :: S) := by
  rcases S with _ | ⟨r₂, rs⟩
  · simp [w]
  · simp [w]; omega

-- Stage 3 P transitions
lemma P_step_0_rec (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (b : ℕ) (hb : b % 4 = 0)
    (R_tail : List (ℕ × ℕ)) (hR : R_tail ≠ []) :
    (P_cfg L'' W ((0, b) :: R_tail)) [target_tm]⊢⁺ P_cfg L'' (0 :: 1 :: W) R_tail := by
  rcases R_tail with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · contradiction
  · unfold P_cfg
    rw [encRight_cons_simp, hb, encRight_cons_eq_one_cons_encTail]
    execute 4

lemma P_step_0_other (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (b : ℕ)
    (R_tail : List (ℕ × ℕ)) (h : R_tail = [] ∨ b % 4 ≠ 0) :
    (P_cfg L'' W ((0, b) :: R_tail)) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: peelInner b R_tail) := by
  dsimp only [P_cfg, F_cfg]
  rw [encRight_zero_peelInner b R_tail h]
  rcases h_in : peelInner b R_tail with _ | ⟨⟨ai, bi⟩, rsi⟩
  · exact False.elim (peelInner_ne_nil b R_tail h_in)
  · rw [encRight_cons_simp 0 0, encRight_cons_eq_one_cons_encTail ai bi rsi]
    execute 9

lemma P_step_1_rec (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (b : ℕ) (hb : b % 4 = 0)
    (R_tail : List (ℕ × ℕ)) (hR : R_tail ≠ []) :
    (P_cfg L'' W ((1, b) :: R_tail)) [target_tm]⊢⁺ P_cfg L'' (0 :: 0 :: 1 :: W) R_tail := by
  rcases R_tail with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · contradiction
  · unfold P_cfg
    rw [encRight_succ 0 b, encRight_cons_simp, hb, encRight_cons_eq_one_cons_encTail]
    execute 3

lemma P_step_1_other (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (b : ℕ)
    (R_tail : List (ℕ × ℕ)) (h : R_tail = [] ∨ b % 4 ≠ 0) :
    (P_cfg L'' W ((1, b) :: R_tail)) [target_tm]⊢⁺ P_cfg L'' (1 :: W) ((0, 0) :: peelInner b R_tail) := by
  unfold P_cfg
  rw [encRight_one_peelInner b R_tail h]
  rcases h_in : peelInner b R_tail with _ | ⟨⟨ai, bi⟩, rsi⟩
  · exact False.elim (peelInner_ne_nil b R_tail h_in)
  · rw [encRight_cons_simp 0 0, encRight_cons_eq_one_cons_encTail ai bi rsi]
    execute 7

lemma P_step_ge2 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (a b : ℕ) (R_tail : List (ℕ × ℕ)) :
    (P_cfg L'' W ((a + 2, b) :: R_tail)) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: (a, b) :: R_tail) := by
  dsimp only [P_cfg, F_cfg]
  rw [encRight_succ (a + 1) b, encRight_succ a b, encRight_cons_simp 0 0,
    encRight_cons_eq_one_cons_encTail a b R_tail]
  execute 11

-- Stage 3 F transitions on bit 0
lemma F00_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F00 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F02 L'' W R := by dsimp only [F_cfg]; execute 1
lemma F01_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F01 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F04 L'' W ((0, 1) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 1]; execute 7
lemma F02_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F02 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F04 L'' W (bumpHead R) := by
  dsimp only [F_cfg]; rw [encRight_bumpHead]; execute 5
lemma F04_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F04 L'' (0 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: 1 :: W) R := by dsimp only [F_cfg, P_cfg]; execute 4
lemma F05_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F05 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F07 L'' W R := by dsimp only [F_cfg]; execute 1
lemma F07_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F07 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: (0, 0) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 0, encRight_cons_simp 0 0]; execute 9

-- Stage 3 F transitions on bit 1
lemma F00_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F00 L'' (1 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: W) R := by dsimp only [F_cfg, P_cfg]; execute 1
lemma F01_bit1_halt (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (step target_tm (F_cfg .F01 L'' (1 :: W) R)).isNone = true := by
  dsimp only [F_cfg]; rw [listblank_append_cons]; exact F_halt_on_one _ _
lemma F02_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F02 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F05 L'' W R := by dsimp only [F_cfg]; execute 1
lemma F04_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F04 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 0]; execute 1
lemma F05_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F05 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F01 L'' W R := by dsimp only [F_cfg]; execute 1
lemma F07_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F07 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 2) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 2]; execute 1

-- Pushdown predicate & bit-step combinators
def Stage3Out (start : Cfg (Fin 2) (Fin 6)) (L'' : List (ℕ × ℕ)) (W_out : List (Fin 2))
    (W_bound : ℕ) (C : FState → ℕ) : Prop :=
  (∃ cfg', (start [target_tm]⊢⁺ cfg') ∧ (step target_tm cfg').isNone) ∨
  (∃ s R_out, R_out ≠ [] ∧ w R_out + C s ≤ W_bound ∧
    (start [target_tm]⊢⁺ F_cfg s L'' W_out R_out))

def Q0 (R : List (ℕ × ℕ)) : Prop :=
  ∀ L'' W_base, Stage3Out (P_cfg L'' W_base R) L'' W_base (w R) C0

def Qz (R : List (ℕ × ℕ)) : Prop :=
  ∀ L'' W_base, Stage3Out (P_cfg L'' (0 :: W_base) R) L'' W_base (w R) C1

def Qz1 (R : List (ℕ × ℕ)) : Prop :=
  ∀ L'' W_base, Stage3Out (P_cfg L'' (0 :: 1 :: W_base) R) L'' W_base (w R) C0

lemma step_bit0 {start : Cfg (Fin 2) (Fin 6)} {L'' : List (ℕ × ℕ)} {W_out : List (Fin 2)}
    {W_bound : ℕ} {s : FState} {R₁ : List (ℕ × ℕ)}
    (h_reach : start [target_tm]⊢⁺ F_cfg s L'' (0 :: W_out) R₁)
    (hR₁ : R₁ ≠ []) (hw₁ : w R₁ + C0 s ≤ W_bound)
    (ih_z1 : ∀ R', R' ≠ [] → w R' < W_bound → Qz1 R') :
    Stage3Out start L'' W_out W_bound C1 := by
  cases s with
  | F00 =>
    exact Or.inr ⟨.F02, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega, stepPlus_trans h_reach (F00_bit0 L'' W_out R₁)⟩
  | F01 =>
    refine Or.inr ⟨.F04, (0, 1) :: R₁, by simp, ?_, stepPlus_trans h_reach (F01_bit0 L'' W_out R₁)⟩
    rw [w_cons_nonempty 0 1 R₁ hR₁]; dsimp [C0, C1] at hw₁ ⊢; omega
  | F02 =>
    have hne : bumpHead R₁ ≠ [] := by rcases R₁ with _ | ⟨⟨a, b⟩, rs⟩; contradiction; simp [bumpHead]
    refine Or.inr ⟨.F04, bumpHead R₁, hne, ?_, stepPlus_trans h_reach (F02_bit0 L'' W_out R₁)⟩
    rw [w_bumpHead R₁ hR₁]; dsimp [C0, C1] at hw₁ ⊢; omega
  | F04 =>
    have hlt : w R₁ < W_bound := by dsimp [C0] at hw₁; omega
    have h_p := stepPlus_trans h_reach (F04_bit0 L'' W_out R₁)
    rcases ih_z1 R₁ hR₁ hlt L'' W_out with ⟨cfg', h1, h2⟩ | ⟨s', R_out, hne, hw_out, h1⟩
    · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
    · have hc := C1_le_C0_succ s'
      exact Or.inr ⟨s', R_out, hne, by dsimp [C0] at hw₁; omega, stepPlus_trans h_p h1⟩
  | F05 =>
    exact Or.inr ⟨.F07, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega, stepPlus_trans h_reach (F05_bit0 L'' W_out R₁)⟩
  | F07 =>
    refine Or.inr ⟨.F00, (0, 0) :: (0, 0) :: R₁, by simp, ?_, stepPlus_trans h_reach (F07_bit0 L'' W_out R₁)⟩
    rw [w_cons_nonempty 0 0 _ (by simp), w_cons_nonempty 0 0 R₁ hR₁]; dsimp [C0, C1] at hw₁ ⊢; omega

lemma step_bit1 {start : Cfg (Fin 2) (Fin 6)} {L'' : List (ℕ × ℕ)} {W_out : List (Fin 2)}
    {W_bound : ℕ} {s : FState} {R₁ : List (ℕ × ℕ)}
    (h_reach : start [target_tm]⊢⁺ F_cfg s L'' (1 :: W_out) R₁)
    (hR₁ : R₁ ≠ []) (hw₁ : w R₁ + C1 s ≤ W_bound)
    (ih_z : ∀ R', R' ≠ [] → w R' < W_bound → Qz R') :
    Stage3Out start L'' W_out W_bound C0 := by
  cases s with
  | F00 =>
    have hlt : w R₁ < W_bound := by dsimp [C1] at hw₁; omega
    have h_p := stepPlus_trans h_reach (F00_bit1 L'' W_out R₁)
    rcases ih_z R₁ hR₁ hlt L'' W_out with ⟨cfg', h1, h2⟩ | ⟨s', R_out, hne, hw_out, h1⟩
    · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
    · have hc := C0_le_C1_succ s'
      exact Or.inr ⟨s', R_out, hne, by dsimp [C1] at hw₁; omega, stepPlus_trans h_p h1⟩
  | F01 =>
    exact Or.inl ⟨F_cfg .F01 L'' (1 :: W_out) R₁, h_reach, F01_bit1_halt L'' W_out R₁⟩
  | F02 =>
    exact Or.inr ⟨.F05, R₁, hR₁, by dsimp [C1, C0] at hw₁ ⊢; omega, stepPlus_trans h_reach (F02_bit1 L'' W_out R₁)⟩
  | F04 =>
    refine Or.inr ⟨.F00, (0, 0) :: R₁, by simp, ?_, stepPlus_trans h_reach (F04_bit1 L'' W_out R₁)⟩
    rw [w_cons_nonempty 0 0 R₁ hR₁]; dsimp [C1, C0] at hw₁ ⊢; omega
  | F05 =>
    exact Or.inr ⟨.F01, R₁, hR₁, by dsimp [C1, C0] at hw₁ ⊢; omega, stepPlus_trans h_reach (F05_bit1 L'' W_out R₁)⟩
  | F07 =>
    refine Or.inr ⟨.F00, (0, 2) :: R₁, by simp, ?_, stepPlus_trans h_reach (F07_bit1 L'' W_out R₁)⟩
    rw [w_cons_nonempty 0 2 R₁ hR₁]; dsimp [C1, C0] at hw₁ ⊢; omega

theorem stage3_ind (W_val : ℕ) :
    ∀ R, R ≠ [] → w R = W_val → Q0 R ∧ Qz R ∧ Qz1 R := by
  induction W_val using Nat.strong_induction_on with
  | h W_val ih_w =>
    intro R hR hw
    induction R with
    | nil => contradiction
    | cons hd R_tail ih_tail =>
      rcases hd with ⟨a, b⟩
      have hw_ab : w ((a, b) :: R_tail) = W_val := hw
      have ih_z : ∀ R', R' ≠ [] → w R' < W_val → Qz R' := fun R' hR' hlt =>
        (ih_w (w R') hlt R' hR' rfl).2.1
      have ih_z1 : ∀ R', R' ≠ [] → w R' < W_val → Qz1 R' := fun R' hR' hlt =>
        (ih_w (w R') hlt R' hR' rfl).2.2
      have hQ0 : Q0 ((a, b) :: R_tail) := by
        intro L'' W_base
        rw [hw_ab]
        rcases a with _ | _ | a'
        · -- a = 0
          have hw0 : w ((0, b) :: R_tail) = W_val := hw_ab
          rcases R_tail with _ | ⟨r₂, rs⟩
          · -- R = [(0, b)] -> P_step_0_other
            refine Or.inr ⟨.F00, (0, 0) :: peelInner b [], by simp, ?_,
              P_step_0_other L'' W_base b [] (Or.inl rfl)⟩
            rw [w_peelInner_zero b [] (Or.inl rfl), C0]; omega
          · rcases mod4_cases b with hb0 | hb1 | hb2 | hb3
            · -- P_step_0_rec -> calls Qz1 (r₂ :: rs) via ih_tail!
              have hne : (r₂ :: rs) ≠ [] := by simp
              have hb2 : b % 2 = 0 := by omega
              have hw_eq : w ((0, b) :: r₂ :: rs) = w (r₂ :: rs) := by simp [w, hb2]
              have hQz1_tail : Qz1 (r₂ :: rs) := (ih_tail hne (by omega)).2.2
              have h_p := P_step_0_rec L'' W_base b hb0 (r₂ :: rs) hne
              rcases hQz1_tail L'' W_base with ⟨cfg', h1, h2⟩ | ⟨s', R_out, hne_out, hw_out, h1⟩
              · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
              · exact Or.inr ⟨s', R_out, hne_out, by omega, stepPlus_trans h_p h1⟩
            · -- b % 4 = 1 -> P_step_0_other
              have hcond : (r₂ :: rs) = [] ∨ b % 4 ≠ 0 := Or.inr (by omega)
              refine Or.inr ⟨.F00, (0, 0) :: peelInner b (r₂ :: rs), by simp, ?_,
                P_step_0_other L'' W_base b (r₂ :: rs) hcond⟩
              rw [w_peelInner_zero b (r₂ :: rs) hcond, C0]; omega
            · -- b % 4 = 2 -> P_step_0_other
              have hcond : (r₂ :: rs) = [] ∨ b % 4 ≠ 0 := Or.inr (by omega)
              refine Or.inr ⟨.F00, (0, 0) :: peelInner b (r₂ :: rs), by simp, ?_,
                P_step_0_other L'' W_base b (r₂ :: rs) hcond⟩
              rw [w_peelInner_zero b (r₂ :: rs) hcond, C0]; omega
            · -- b % 4 = 3 -> P_step_0_other
              have hcond : (r₂ :: rs) = [] ∨ b % 4 ≠ 0 := Or.inr (by omega)
              refine Or.inr ⟨.F00, (0, 0) :: peelInner b (r₂ :: rs), by simp, ?_,
                P_step_0_other L'' W_base b (r₂ :: rs) hcond⟩
              rw [w_peelInner_zero b (r₂ :: rs) hcond, C0]; omega
        · -- a = 1
          have hw1_eq : w ((1, b) :: R_tail) = W_val := hw_ab
          by_cases h_rec : R_tail ≠ [] ∧ b % 4 = 0
          · -- P_step_1_rec: R_tail ≠ [] and b % 4 = 0
            obtain ⟨hne_tail, hb0⟩ := h_rec
            have h_p := P_step_1_rec L'' W_base b hb0 R_tail hne_tail
            have hw_tail : w R_tail + 1 = w ((1, b) :: R_tail) := by
              rw [w_cons_nonempty 1 b R_tail hne_tail]
              have hb2 : b % 2 = 0 := by omega
              omega
            rcases ih_z R_tail hne_tail (by omega) L'' (0 :: 1 :: W_base) with
              ⟨cfg', h1, h2⟩ | ⟨s1, R1, hR1, hw1, h1⟩
            · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
            · have h_reach1 := stepPlus_trans h_p h1
              have hc0 := C0_le_C1_succ s1
              have hw1_c0 : w R1 + C0 s1 ≤ W_val := by omega
              rcases step_bit0 h_reach1 hR1 hw1_c0 ih_z1 with
                ⟨cfg', h2, h3⟩ | ⟨s2, R2, hR2, hw2, h2⟩
              · exact Or.inl ⟨cfg', h2, h3⟩
              · exact step_bit1 h2 hR2 hw2 ih_z
          · -- P_step_1_other: R_tail = [] ∨ b % 4 ≠ 0
            have hcond : R_tail = [] ∨ b % 4 ≠ 0 := by
              rcases R_tail with _ | ⟨r₂, rs⟩
              · exact Or.inl rfl
              · exact Or.inr (fun h0 => h_rec ⟨by simp, h0⟩)
            have h_p := P_step_1_other L'' W_base b R_tail hcond
            set R1 := (0, 0) :: peelInner b R_tail
            have hR1 : R1 ≠ [] := by simp [R1]
            have hw1 : w R1 + 1 = w ((1, b) :: R_tail) := w_peelInner_one b R_tail hcond
            have hQ0_R1 : Q0 R1 := (ih_w (w R1) (by omega) R1 hR1 rfl).1
            rcases hQ0_R1 L'' (1 :: W_base) with ⟨cfg', h1, h2⟩ | ⟨s0, R2, hR2, hw2, h1⟩
            · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
            · have h_reach2 := stepPlus_trans h_p h1
              have hc1 := C1_le_C0_succ s0
              have hw2_c1 : w R2 + C1 s0 ≤ W_val := by omega
              exact step_bit1 h_reach2 hR2 hw2_c1 ih_z
        · -- a = a' + 2 -> P_step_ge2
          have hw2_eq : w ((a' + 2, b) :: R_tail) = W_val := hw_ab
          refine Or.inr ⟨.F00, (0, 0) :: (a', b) :: R_tail, by simp, ?_,
            P_step_ge2 L'' W_base a' b R_tail⟩
          have hw_g := w_ge2 a' b R_tail
          dsimp [C0]; omega
      have hQz : Qz ((a, b) :: R_tail) := fun L'' W_base => by
        rw [hw_ab]
        rcases hQ0 L'' (0 :: W_base) with ⟨cfg', h1, h2⟩ | ⟨s0, R1, hR1, hw1, h1⟩
        · exact Or.inl ⟨cfg', h1, h2⟩
        · rw [hw_ab] at hw1
          exact step_bit0 h1 hR1 hw1 ih_z1
      have hQz1 : Qz1 ((a, b) :: R_tail) := fun L'' W_base => by
        rw [hw_ab]
        rcases hQz L'' (1 :: W_base) with ⟨cfg', h1, h2⟩ | ⟨s1, R1, hR1, hw1, h1⟩
        · exact Or.inl ⟨cfg', h1, h2⟩
        · rw [hw_ab] at hw1
          exact step_bit1 h1 hR1 hw1 ih_z
      exact ⟨hQ0, hQz, hQz1⟩

-- Stage 3 exit: `F_cfg s L'' [] R` -> `cfg_M0`
lemma F00_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F00 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 3) :: tailAsRight L'') ((0, 0) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 3, encRight_tailAsRight, encTail_zero 0]; execute 2
lemma F01_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F01 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: (0, 0) :: (0, 2) :: tailAsRight L'') ((0, 0) :: R) := by
  dsimp only [F_cfg, wall]
  rw [cfg_M0_eq, listblank_append_nil, encTail_zero 0, encRight_cons_simp 0 0,
    encRight_cons_simp 0 2, encRight_tailAsRight, encTail_zero 0]
  execute 15
lemma F02_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F02 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((1, 0) :: bumpHead R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2, encRight_tailAsRight, encTail_succ 0, encTail_zero 0, encRight_bumpHead]; execute 5
lemma F04_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F04 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: (0, 3) :: tailAsRight L'') (rightAsTail R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 0, encRight_cons_simp 0 3, encRight_tailAsRight, encTail_rightAsTail]; execute 4
lemma F05_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F05 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((1, 2) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2, encRight_tailAsRight, encTail_succ 0, encTail_zero 2]; execute 1
lemma F07_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F07 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: (0, 3) :: tailAsRight L'') ((0, 1) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 0, encRight_cons_simp 0 3, encRight_tailAsRight, encTail_zero 1]; execute 4

lemma F_exit_all (s : FState) (L'' R : List (ℕ × ℕ)) :
    ∃ L_out R_out, (F_cfg s L'' [] R) [target_tm]⊢⁺ cfg_M0 L_out R_out := by
  cases s with
  | F00 => exact ⟨_, _, F00_exit L'' R⟩
  | F01 => exact ⟨_, _, F01_exit L'' R⟩
  | F02 => exact ⟨_, _, F02_exit L'' R⟩
  | F04 => exact ⟨_, _, F04_exit L'' R⟩
  | F05 => exact ⟨_, _, F05_exit L'' R⟩
  | F07 => exact ⟨_, _, F07_exit L'' R⟩

theorem stage3_closed (L'' R : List (ℕ × ℕ)) (hR : R ≠ []) :
    ∃ cfg', ((P_cfg L'' [] R) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  have hQ0 : Q0 R := (stage3_ind (w R) R hR rfl).1
  rcases hQ0 L'' [] with ⟨cfg', h1, h2⟩ | ⟨s, R_out, _, _, h1⟩
  · exact ⟨cfg', h1, Or.inr h2⟩
  · obtain ⟨L_out, R_out', h2⟩ := F_exit_all s L'' R_out
    exact ⟨cfg_M0 L_out R_out', stepPlus_trans h1 h2, Or.inl ⟨.M0, L_out, R_out', rfl⟩⟩

-- ============================================================================
-- Closure & Main Theorem
-- ============================================================================

theorem stack_system_closed :
    ∀ cfg, IsInStackSystem cfg →
      ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
              (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  intro cfg ⟨m, L, R, hcfg⟩
  subst hcfg
  cases m with
  | M0 =>
    obtain ⟨cfg₁, h₁, hout₁⟩ := stage1_step L R
    rcases hout₁ with hM₁ | ⟨L₁, R₁, rfl⟩
    · exact ⟨cfg₁, h₁, Or.inl hM₁⟩
    · obtain ⟨cfg₂, h₂, hout₂⟩ := stage2_closed L₁.length L₁ (Nat.le_refl _) 0 (by decide) R₁
      rcases hout₂ with hM₂ | hH₂ | ⟨L'', R_P, hRP, rfl⟩
      · exact ⟨cfg₂, stepPlus_trans h₁ h₂, Or.inl hM₂⟩
      · exact ⟨cfg₂, stepPlus_trans h₁ h₂, Or.inr hH₂⟩
      · obtain ⟨cfg₃, h₃, hout₃⟩ := stage3_closed L'' R_P hRP
        exact ⟨cfg₃, stepPlus_trans (stepPlus_trans h₁ h₂) h₃, hout₃⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_stack_cryptid : IsStackCryptid target_tm := by
  refine ⟨StackMode, 1, 0, encLeft, encRight, evalStackCfg, IsInStackSystem,
    Or.inl ⟨rfl, rfl⟩,
    rfl, rfl, audit_encLeft_head, audit_encRight_head,
    audit_encLeft_not_surjective, audit_encRight_not_surjective,
    ⟨1, 1, 1, 4, 1, 1, 1, 4,
     by decide, by decide, by decide, by decide, by decide,
     by decide, by decide, by decide, by decide, by decide,
     fun a b L => rfl, fun d b R => rfl⟩,
    ⟨[.M0], by decide, by intro m; cases m; decide⟩,
    valid_stack_modes,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    init_reaches_stack_system,
    stack_system_closed⟩

-- ============================================================================
-- Wave 16: Multi-Step Contractions, Non-Halting Closures & Trajectory Shield
-- ============================================================================

lemma stepPlus_stepStar_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢⁺ c₂) (h₂ : c₂ [target_tm]⊢* c₃) : c₁ [target_tm]⊢* c₃ :=
  stepPlus_stepStar (stepPlus_stepStar_stepPlus h₁ h₂)

/-- Multi-step Stage 3 pushdown contraction: draining `k` leading `(0, 0)` pairs
    in front of a non-empty tail `R_tail` pushes `0 :: 1` onto `W` `k` times. -/
lemma P_drain_0_rec_steps (k : ℕ) (L'' : List (ℕ × ℕ)) (W : List (Fin 2))
    (R_tail : List (ℕ × ℕ)) (hR : R_tail ≠ []) :
    (P_cfg L'' W (List.replicate k (0, 0) ++ R_tail)) [target_tm]⊢*
      P_cfg L'' ((fun w => 0 :: 1 :: w)^[k] W) R_tail := by
  induction k generalizing W with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Function.iterate_zero, id_eq]
    exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Function.iterate_succ_apply]
    have hne : List.replicate k (0, 0) ++ R_tail ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hR
    exact stepPlus_stepStar_trans
      (P_step_0_rec L'' W 0 rfl (List.replicate k (0, 0) ++ R_tail) hne)
      (ih (0 :: 1 :: W))

/-- Multi-step Stage 3 pushdown contraction: draining `k` leading `(1, 0)` pairs
    in front of a non-empty tail `R_tail` pushes `0 :: 0 :: 1` onto `W` `k` times. -/
lemma P_drain_1_rec_steps (k : ℕ) (L'' : List (ℕ × ℕ)) (W : List (Fin 2))
    (R_tail : List (ℕ × ℕ)) (hR : R_tail ≠ []) :
    (P_cfg L'' W (List.replicate k (1, 0) ++ R_tail)) [target_tm]⊢*
      P_cfg L'' ((fun w => 0 :: 0 :: 1 :: w)^[k] W) R_tail := by
  induction k generalizing W with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Function.iterate_zero, id_eq]
    exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Function.iterate_succ_apply]
    have hne : List.replicate k (1, 0) ++ R_tail ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hR
    exact stepPlus_stepStar_trans
      (P_step_1_rec L'' W 0 rfl (List.replicate k (1, 0) ++ R_tail) hne)
      (ih (0 :: 0 :: 1 :: W))

/-- Single-step Stage 2 double-zero pop on `cfg_D`. -/
lemma D_pop_double_zero (c : ℕ) (hc : c < 4) (L_rest R : List (ℕ × ℕ)) (hL : L_rest ≠ []) :
    (cfg_D c ((0, 0) :: (0, 0) :: L_rest) R) [target_tm]⊢⁺
      cfg_D 2 L_rest ((0, c) :: tailAsRight R) := by
  rcases L_rest with _ | ⟨⟨a₃, b₃⟩, L'''⟩
  · contradiction
  · unfold cfg_D
    set rD := (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)
    have hrD_one : (1 : Fin 2) >> rD = (1 : Fin 2) >> encTail ((0, c) :: tailAsRight R) :=
      one_cons_RD_eq c hc R
    have h0 : 0 % 4 = 0 := rfl
    have hL_enc : encTail ((0, 0) :: (0, 0) :: (a₃, b₃) :: L''') =
        (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₃, b₃) :: L''') := by
      rw [encTail_zero, h0, encRight_cons_eq_one_cons_encTail, encTail_zero, h0,
        encRight_cons_eq_one_cons_encTail]
      rfl
    rw [hL_enc]
    dsimp only [pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
      listblank_append_cons, listblank_append_nil]
    rw [← hrD_one]
    exact D_leaf_0101 (encTail ((a₃, b₃) :: L''')) rD

/-- Multi-step Stage 2 contraction: draining `2 * k` leading `(0, 0)` pairs from `cfg_D 2`. -/
lemma D_drain_double_zero_steps (k : ℕ) (L_rest R : List (ℕ × ℕ)) (hL : L_rest ≠ []) :
    (cfg_D 2 (List.replicate (2 * k) (0, 0) ++ L_rest) R) [target_tm]⊢*
      cfg_D 2 L_rest ((fun r => (0, 2) :: tailAsRight r)^[k] R) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, List.replicate_zero, List.nil_append,
      Function.iterate_zero, id_eq]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have h_rep : List.replicate (2 * (k + 1)) (0, 0) ++ L_rest =
        (0, 0) :: (0, 0) :: (List.replicate (2 * k) (0, 0) ++ L_rest) := by
      have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h2]
      rfl
    rw [h_rep]
    have hne : List.replicate (2 * k) (0, 0) ++ L_rest ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hL
    exact stepPlus_stepStar_trans
      (D_pop_double_zero 2 (by decide) (List.replicate (2 * k) (0, 0) ++ L_rest) R hne)
      (ih ((0, 2) :: tailAsRight R))

/-- Stage 2 empty-left-stack return to `cfg_M0`. -/
lemma D_nil_return (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (cfg_D c [] R) [target_tm]⊢⁺ cfg_M0 [] ((1, c) :: tailAsRight R) := by
  unfold cfg_D
  set rD := (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)
  have hrD_tail : (1 : Fin 2) >> rD = encTail ((1, c) :: tailAsRight R) := RD_eq_encTail_one c hc R
  have hL : encTail [] = (0 : Fin 2) >> (0 : Fin 2) >> encTail [] := by simp
  rw [hL, cfg_M0_eq, ← hrD_tail]
  exact D_leaf_00 (encTail []) rD

/-- Unconditional non-halting mode closure for `evalStackCfg .M0 L ((1, bR) :: R')`. -/
theorem mode_M0_head_one_nonhalting (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    ∃ cfg', ((evalStackCfg .M0 L ((1, bR) :: R')) [target_tm]⊢⁺ cfg') ∧
            IsInStackSystem cfg' :=
  ⟨evalStackCfg .M0 ((0, 0) :: tailAsRight L) (peelSep bR R'),
   M0_one L bR R', ⟨.M0, (0, 0) :: tailAsRight L, peelSep bR R', rfl⟩⟩

/-- Unconditional non-halting mode closure for `evalStackCfg .M0 L ((2, bR) :: R')`. -/
theorem mode_M0_head_two_nonhalting (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    ∃ cfg', ((evalStackCfg .M0 L ((2, bR) :: R')) [target_tm]⊢⁺ cfg') ∧
            IsInStackSystem cfg' :=
  ⟨evalStackCfg .M0 ((0, 1) :: tailAsRight L) (peelSep bR R'),
   M0_two L bR R', ⟨.M0, (0, 1) :: tailAsRight L, peelSep bR R', rfl⟩⟩

/-- Unconditional non-halting mode closure for `evalStackCfg .M0 L ((d + 4, bR) :: R')`. -/
theorem mode_M0_head_add4_nonhalting (L : List (ℕ × ℕ)) (d bR : ℕ) (R' : List (ℕ × ℕ)) :
    ∃ cfg', ((evalStackCfg .M0 L ((d + 4, bR) :: R')) [target_tm]⊢⁺ cfg') ∧
            IsInStackSystem cfg' :=
  ⟨evalStackCfg .M0 ((0, 0) :: tailAsRight L) ((0, 0) :: (d, bR) :: R'),
   M0_add4 L d bR R', ⟨.M0, (0, 0) :: tailAsRight L, (0, 0) :: (d, bR) :: R', rfl⟩⟩

/-- Unconditional non-halting mode closure for `evalStackCfg .M0 [] []`. -/
theorem mode_M0_nil_nil_nonhalting :
    ∃ cfg', ((evalStackCfg .M0 [] []) [target_tm]⊢⁺ cfg') ∧
            IsInStackSystem cfg' :=
  ⟨evalStackCfg .M0 [] ((1, 0) :: tailAsRight []),
   stepPlus_trans (M0_nil []) (D_nil_return 0 (by decide) []),
   ⟨.M0, [], (1, 0) :: tailAsRight [], rfl⟩⟩

/-- Refined reachable stack subset for Holdout `#223`: canonical `evalStackCfg m L R`
    configurations with at least one non-empty stack (`L ≠ [] ∨ R ≠ []`). -/
def ValidStack223 (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R ∧ (L ≠ [] ∨ R ≠ [])

theorem validStack223_subset_isInStackSystem :
    ∀ cfg, ValidStack223 cfg → IsInStackSystem cfg := by
  intro cfg ⟨m, L, R, hcfg, _⟩
  exact ⟨m, L, R, hcfg⟩

theorem init_reaches_validStack223 :
    ∃ cfg₀, ((init []) [target_tm]⊢⁺ cfg₀) ∧ ValidStack223 cfg₀ := by
  refine ⟨cfg_M0 [] [(1, 0), (0, 0)], ?_,
    ⟨.M0, [], [(1, 0), (0, 0)], rfl, Or.inr (by simp)⟩⟩
  rw [init_nil, cfg_M0_eq, encTail_nil, encTail_succ, encTail_zero, encRight_cons_simp]
  simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
    listblank_append_nil, listblank_append_cons, encRight_nil, zero_cons_default]
  execute 4

theorem cfg_M0_nil_nil_reaches_validStack223 :
    ∃ cfg', ((evalStackCfg .M0 [] []) [target_tm]⊢⁺ cfg') ∧ ValidStack223 cfg' :=
  ⟨evalStackCfg .M0 [] ((1, 0) :: tailAsRight []),
   stepPlus_trans (M0_nil []) (D_nil_return 0 (by decide) []),
   ⟨.M0, [], (1, 0) :: tailAsRight [], rfl, Or.inr (by simp)⟩⟩

theorem stack_system_steps_to_validStack223 :
    ∀ cfg, IsInStackSystem cfg →
      ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
              (ValidStack223 cfg' ∨ (step target_tm cfg').isNone) := by
  intro cfg hcfg
  obtain ⟨cfg₁, h₁, hout⟩ := stack_system_closed cfg hcfg
  rcases hout with ⟨m, L, R, rfl⟩ | hhalt
  · cases m with
    | M0 =>
      rcases L with _ | ⟨pL, L'⟩
      · rcases R with _ | ⟨pR, R'⟩
        · obtain ⟨cfg₂, h₂, hvalid₂⟩ := cfg_M0_nil_nil_reaches_validStack223
          exact ⟨cfg₂, stepPlus_trans h₁ h₂, Or.inl hvalid₂⟩
        · exact ⟨evalStackCfg .M0 [] (pR :: R'), h₁,
            Or.inl ⟨.M0, [], pR :: R', rfl, Or.inr (by simp)⟩⟩
      · exact ⟨evalStackCfg .M0 (pL :: L') R, h₁,
          Or.inl ⟨.M0, pL :: L', R, rfl, Or.inl (by simp)⟩⟩
  · exact ⟨cfg₁, h₁, Or.inr hhalt⟩

theorem validStack223_step_closed :
    ∀ cfg, ValidStack223 cfg →
      ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
              (ValidStack223 cfg' ∨ (step target_tm cfg').isNone) :=
  fun cfg hvalid =>
    stack_system_steps_to_validStack223 cfg (validStack223_subset_isInStackSystem cfg hvalid)

/-- Unconditional non-halting mode closure for `evalStackCfg .M0 L ((3, bR) :: R')`
    when `bR % 4 < 3`. -/
theorem mode_M0_head_three_lt3_nonhalting
    (L : List (ℕ × ℕ)) (bR : ℕ) (hb : bR % 4 < 3) (R' : List (ℕ × ℕ)) :
    ∃ cfg', ((evalStackCfg .M0 L ((3, bR) :: R')) [target_tm]⊢⁺ cfg') ∧
            ValidStack223 cfg' :=
  ⟨evalStackCfg .M0 ((0, 0) :: tailAsRight L) (pushZeroSep (bR % 4 + 1) R'),
   M0_three_lt3 L bR hb R',
   ⟨.M0, (0, 0) :: tailAsRight L, pushZeroSep (bR % 4 + 1) R', rfl, Or.inl (by simp)⟩⟩

/-- Unconditional non-halting mode closure for `evalStackCfg .M0 L [(3, bR)]`
    when `bR % 4 = 3`. -/
theorem mode_M0_head_three_eq3_nil_nonhalting
    (L : List (ℕ × ℕ)) (bR : ℕ) (hb : bR % 4 = 3) :
    ∃ cfg', ((evalStackCfg .M0 L [(3, bR)]) [target_tm]⊢⁺ cfg') ∧
            ValidStack223 cfg' :=
  ⟨evalStackCfg .M0 ((0, 0) :: tailAsRight L) [],
   M0_three_eq3_nil L bR hb,
   ⟨.M0, (0, 0) :: tailAsRight L, [], rfl, Or.inl (by simp)⟩⟩

/-- Stage 2 singleton-zero left-stack return to `cfg_M0`. -/
lemma D_singleton_zero_return (c : ℕ) (hc : c < 4) (b₁ : ℕ) (R : List (ℕ × ℕ)) :
    (cfg_D c [(0, b₁)] R) [target_tm]⊢⁺ cfg_M0 [] ((1, c) :: tailAsRight R) := by
  unfold cfg_D
  set rD := (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)
  have hrD_tail : (1 : Fin 2) >> rD = encTail ((1, c) :: tailAsRight R) :=
    RD_eq_encTail_one c hc R
  have hL : encTail [(0, b₁)] = (0 : Fin 2) >> (0 : Fin 2) >> encTail [] := by
    simp [encTail_zero]
  rw [hL, cfg_M0_eq, ← hrD_tail]
  exact D_leaf_00 (encTail []) rD

/-- Unconditional non-halting turnaround closure for `evalStackCfg .M0 [(0, b₁)] []`. -/
theorem mode_M0_singleton_zero_nil_nonhalting (b₁ : ℕ) :
    ∃ cfg', ((evalStackCfg .M0 [(0, b₁)] []) [target_tm]⊢⁺ cfg') ∧
            ValidStack223 cfg' :=
  ⟨evalStackCfg .M0 [] ((1, 0) :: tailAsRight []),
   stepPlus_trans (M0_nil [(0, b₁)]) (D_singleton_zero_return 0 (by decide) b₁ []),
   ⟨.M0, [], (1, 0) :: tailAsRight [], rfl, Or.inr (by simp)⟩⟩

/-- Stage 2 halting transition when `L` has head `a₁ ≥ 2`. -/
lemma D_head_ge2_halts (c : ℕ) (a₁' b₁ : ℕ) (L' R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_D c ((a₁' + 2, b₁) :: L') R) [target_tm]⊢⁺ cfg') ∧
            (step target_tm cfg').isNone = true := by
  unfold cfg_D
  set rD := (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)
  have hL : encTail ((a₁' + 2, b₁) :: L') =
      (1 : Fin 2) >> (1 : Fin 2) >> encTail ((a₁', b₁) :: L') := by
    rw [encTail_succ (a₁' + 1), encTail_succ a₁']
  rw [hL]
  exact ⟨((1 : Fin 2) >> encTail ((a₁', b₁) :: L')) <{{F}} ((0 : Fin 2) >> rD),
    D_leaf_11 _ rD, F_halt_on_one _ _⟩

/-- Stage 2 halting counterexample family in `ValidStack223` (`R = []`): any
    `evalStackCfg .M0 ((a₁' + 2, b₁) :: L') []` satisfies `ValidStack223` and halts
    in 4 steps via `M0_nil` followed by `D_head_ge2_halts`. -/
theorem counterexample_validStack223_M0_left_ge2_nil_halts
    (a₁' b₁ : ℕ) (L' : List (ℕ × ℕ)) :
    ValidStack223 (evalStackCfg .M0 ((a₁' + 2, b₁) :: L') []) ∧
    ∃ cfg', ((evalStackCfg .M0 ((a₁' + 2, b₁) :: L') []) [target_tm]⊢⁺ cfg') ∧
            (step target_tm cfg').isNone = true := by
  refine ⟨⟨.M0, (a₁' + 2, b₁) :: L', [], rfl, Or.inl (by simp)⟩, ?_⟩
  obtain ⟨cfg', hD, hhalt⟩ := D_head_ge2_halts 0 a₁' b₁ L' []
  exact ⟨cfg', stepPlus_trans (M0_nil ((a₁' + 2, b₁) :: L')) hD, hhalt⟩

/-- Stage 2 halting counterexample family in `ValidStack223` (`R = (0, bR) :: R'`): any
    `evalStackCfg .M0 ((a₁' + 2, b₁) :: L') ((0, bR) :: R')` satisfies `ValidStack223`
    and halts in 4 steps via `M0_zero` followed by `D_head_ge2_halts`. -/
theorem counterexample_validStack223_M0_left_ge2_zero_halts
    (a₁' b₁ bR : ℕ) (L' R' : List (ℕ × ℕ)) :
    ValidStack223 (evalStackCfg .M0 ((a₁' + 2, b₁) :: L') ((0, bR) :: R')) ∧
    ∃ cfg', ((evalStackCfg .M0 ((a₁' + 2, b₁) :: L') ((0, bR) :: R')) [target_tm]⊢⁺ cfg') ∧
            (step target_tm cfg').isNone = true := by
  refine ⟨⟨.M0, (a₁' + 2, b₁) :: L', (0, bR) :: R', rfl, Or.inl (by simp)⟩, ?_⟩
  obtain ⟨cfg', hD, hhalt⟩ := D_head_ge2_halts 0 a₁' b₁ L' (peelSep bR R')
  exact ⟨cfg', stepPlus_trans (M0_zero ((a₁' + 2, b₁) :: L') bR R') hD, hhalt⟩

/-- Multi-phase halting counterexample family in `ValidStack223` (`R = (3, 3) :: (d₂, b₂) :: R''`):
    `evalStackCfg .M0 ((0, 0) :: (a₁' + 2, b₁) :: L') ((3, 3) :: (d₂, b₂) :: R'')` enters Stage 2
    via `M0_three_eq3_cons`, pops the leading `(0, 0), (0, 0)` pair via `D_pop_double_zero`,
    and halts via `D_head_ge2_halts`. -/
theorem counterexample_validStack223_M0_three_eq3_cons_halts
    (a₁' b₁ d₂ b₂ : ℕ) (L' R'' : List (ℕ × ℕ)) :
    ValidStack223 (evalStackCfg .M0 ((0, 0) :: (a₁' + 2, b₁) :: L')
      ((3, 3) :: (d₂, b₂) :: R'')) ∧
    ∃ cfg', ((evalStackCfg .M0 ((0, 0) :: (a₁' + 2, b₁) :: L')
      ((3, 3) :: (d₂, b₂) :: R'')) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone = true := by
  refine ⟨⟨.M0, (0, 0) :: (a₁' + 2, b₁) :: L', (3, 3) :: (d₂, b₂) :: R'',
    rfl, Or.inl (by simp)⟩, ?_⟩
  have h1 := M0_three_eq3_cons ((0, 0) :: (a₁' + 2, b₁) :: L') 3 rfl d₂ b₂ R''
  have h2 := D_pop_double_zero 0 (by decide) ((a₁' + 2, b₁) :: L')
    ((0, 3) :: (d₂, b₂) :: R'') (by simp)
  obtain ⟨cfg', h3, hhalt⟩ := D_head_ge2_halts 2 a₁' b₁ L'
    ((0, 0) :: tailAsRight ((0, 3) :: (d₂, b₂) :: R''))
  exact ⟨cfg', stepPlus_trans (stepPlus_trans h1 h2) h3, hhalt⟩

end BusyBeaver.M_1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0REHHH
