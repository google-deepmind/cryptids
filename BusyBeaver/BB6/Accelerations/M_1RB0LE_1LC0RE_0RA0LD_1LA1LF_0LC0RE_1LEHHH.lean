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


/-!
# Busy Beaver Machine `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---` (`IsStackCryptid`)

Formal `IsStackCryptid` proof for `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---` (`target`).
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LEHHH

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 1 => none

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

private theorem zero_pow_one_add (n : ℕ) :
    (([0] : List (Fin 2)) ^ (1 + n)) = (0 : Fin 2) :: (([0] : List (Fin 2)) ^ n) := by
  rw [Nat.add_comm 1 n, pow_succ_list, cons_append_list, nil_append_list]

-- ============================================================================
-- 2nd-Order Digit-Stack Encodings (`pol = 0, maxSepL = 4, maxSepR = 4`)
-- ============================================================================

private def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L =>
    (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 4))) <+ (([1] : List (Fin 2)) ^ (1 * a + 1))

private def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R =>
    (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight R)

private def encTail (S : List (ℕ × ℕ)) : ListBlank (Fin 2) := (encRight S).tail

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl
@[simp] private theorem encLeft_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 4))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1)) := rfl
@[simp] private theorem encRight_nil : encRight [] = default := rfl
@[simp] private theorem encRight_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d,
      b) :: R) = (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +>
        encRight R) := rfl

private theorem encLeft_eq_encRight (S : List (ℕ × ℕ)) : encLeft S = encRight S := by
  induction S with
  | nil => rfl
  | cons p S' ih =>
    rcases p with ⟨a, b⟩
    simp only [encLeft, encRight, ih]

@[simp] private theorem encLeft_tail (S : List (ℕ × ℕ)) : (encLeft S).tail = encTail S := by
  rw [encLeft_eq_encRight]; rfl

private theorem encRight_tail (S : List (ℕ × ℕ)) : (encRight S).tail = encTail S := rfl

@[simp] private theorem encTail_nil : encTail [] = default := rfl

private theorem encRight_cons_simp (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d,
      b) :: R) = (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ d) +>
        ((([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight R)) := by
  simp only [encRight_cons, Nat.one_mul]
  rw [Nat.add_comm d 1, list_pow_add, listblank_append_right_assoc]
  rfl

private theorem encRight_succ (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d + 1, b) :: R) = (1 : Fin 2) >> encRight ((d, b) :: R) := by
  simp only [encRight_cons, Nat.one_mul]
  rw [Nat.add_comm (d + 1) 1, list_pow_add, listblank_append_right_assoc]
  rfl

private theorem encTail_cons (a b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((a, b) :: S) = (([1] : List (Fin 2)) ^ a) +> ((([0] : List (Fin 2)) ^ (1 + b % 4)) +>
      encRight S) := by
  unfold encTail
  rw [encRight_cons_simp, Turing.ListBlank.tail_cons]

private theorem encRight_cons_eq_one_cons_encTail (a b : ℕ) (S : List (ℕ × ℕ)) :
    encRight ((a, b) :: S) = (1 : Fin 2) >> encTail ((a, b) :: S) := by
  unfold encTail
  rw [encRight_cons_simp, Turing.ListBlank.tail_cons]

private theorem encTail_zero (b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((0, b) :: S) = (([0] : List (Fin 2)) ^ (1 + b % 4)) +> encRight S := by
  rw [encTail_cons]; rfl

private theorem encTail_succ (a b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((a + 1, b) :: S) = (1 : Fin 2) >> encTail ((a, b) :: S) := by
  unfold encTail
  rw [encRight_succ, Turing.ListBlank.tail_cons, encRight_cons_simp, Turing.ListBlank.tail_cons]

private theorem mod4_cases (b : ℕ) : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
  have := Nat.mod_lt b (by decide : 0 < 4)
  omega

private def bumpHead : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: S => (a + 1, b) :: S

private def tailAsRight : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: S => (a, b) :: S

private def rightAsTail : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b) :: S => (a + 1, b) :: S

private def pushZeroSep (b : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b') :: S => (0, b) :: (a, b') :: S

private def peelSep (k : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b') :: S =>
    if k % 4 = 0 then (a + 1, b') :: S
    else (0, k % 4 - 1) :: (a, b') :: S

private def peelInner (b : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a₂, b₂) :: rs =>
    if b % 4 = 1 then (a₂ + 1, b₂) :: rs
    else if b % 4 = 2 then (0, 0) :: (a₂, b₂) :: rs
    else (0, 1) :: (a₂, b₂) :: rs

private theorem encRight_bumpHead (S : List (ℕ × ℕ)) :
    encRight (bumpHead S) = (1 : Fin 2) >> encRight S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · simp [bumpHead]
  · exact encRight_succ a b S'

private theorem encRight_tailAsRight (S : List (ℕ × ℕ)) :
    encRight (tailAsRight S) = (1 : Fin 2) >> encTail S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · simp [tailAsRight]
  · exact encRight_cons_eq_one_cons_encTail a b S'

private theorem encTail_rightAsTail (S : List (ℕ × ℕ)) :
    encTail (rightAsTail S) = encRight S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · rfl
  · unfold encTail rightAsTail
    rw [encRight_succ, Turing.ListBlank.tail_cons]

private theorem encTail_pushZeroSep (b : ℕ) (hb : b < 4) (S : List (ℕ × ℕ)) :
    encTail (pushZeroSep b S) = (([0] : List (Fin 2)) ^ (1 + b)) +> encRight S := by
  rcases S with _ | ⟨⟨a, b'⟩, S'⟩
  · simp [pushZeroSep]
  · rw [pushZeroSep, encTail_zero, Nat.mod_eq_of_lt hb]

private theorem encTail_peelSep (k : ℕ) (S : List (ℕ × ℕ)) :
    encTail (peelSep k S) = (([0] : List (Fin 2)) ^ (k % 4)) +> encRight S := by
  rcases S with _ | ⟨⟨a, b'⟩, S'⟩
  · simp [peelSep]
  · rcases mod4_cases k with h0 | h1 | h2 | h3
    · rw [peelSep, ite_eq_left h0, h0, encTail_succ, encRight_cons_eq_one_cons_encTail]
      rfl
    · simp [peelSep, h1, encTail_zero]
    · simp [peelSep, h2, encTail_zero]
    · simp [peelSep, h3, encTail_zero]

private theorem peelInner_ne_nil (b : ℕ) (S : List (ℕ × ℕ)) : peelInner b S ≠ [] := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · simp [peelInner]
  · dsimp [peelInner]
    split_ifs <;> simp

private theorem encRight_zero_peelInner (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    encRight ((0,
      b) :: S) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail (peelInner b S) := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · simp [peelInner, encTail_zero]
  · rcases mod4_cases b with h0 | h1 | h2 | h3
    · rcases h with hnil | hne
      · contradiction
      · exact False.elim (hne h0)
    · rw [peelInner, ite_eq_left h1, encRight_cons_simp 0 b, h1, encTail_succ,
        encRight_cons_eq_one_cons_encTail]
      rfl
    · have h1 : b % 4 ≠ 1 := by omega
      rw [peelInner, ite_eq_right h1, ite_eq_left h2, encRight_cons_simp 0 b, h2, encTail_zero]
      rfl
    · have h1 : b % 4 ≠ 1 := by omega
      have h2 : b % 4 ≠ 2 := by omega
      rw [peelInner, ite_eq_right h1, ite_eq_right h2, encRight_cons_simp 0 b, h3, encTail_zero]
      rfl

private theorem encRight_one_peelInner (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    encRight ((1,
      b) :: S) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
        encTail (peelInner b S) := by
  rw [encRight_succ 0 b S, encRight_zero_peelInner b S h]

-- ============================================================================
-- Stack System Definition & Witness Checks
-- ============================================================================

private def cfg_M0 (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨0, (encLeft L).tail, (encRight R).tail⟩⟩

private inductive StackMode
  | M0
deriving DecidableEq

private def evalStackCfg : StackMode → List (ℕ × ℕ) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .M0, L, R => cfg_M0 L R

private def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

private theorem cfg_M0_eq (L R : List (ℕ × ℕ)) :
    cfg_M0 L R = ⟨some A, ⟨0, encTail L, encTail R⟩⟩ := by
  simp [cfg_M0, encRight_tail]

private theorem valid_stack_modes : IsValidStackModes encLeft encRight evalStackCfg := by
  intro m
  cases m with
  | M0 => exact ⟨A, .tail [], .tail [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

private theorem audit_encRight_head (d b : ℕ) (R : List (ℕ × ℕ)) :
    (encRight ((d, b) :: R)).head = 1 := by
  rw [encRight_cons_simp, Turing.ListBlank.head_cons]

private theorem audit_encLeft_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: L)).head = 1 := by
  rw [encLeft_eq_encRight]
  exact audit_encRight_head a b L

private theorem audit_encRight_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ R : List (ℕ × ℕ), encRight R ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
    (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
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

private theorem audit_encLeft_not_surjective :
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
  rfl))

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

private theorem F_halt_on_one (tL rD : ListBlank (Fin 2)) :
    (step target_tm (((1 : Fin 2) >> tL) <{{F}} rD)).isNone = true := by
  unfold step
  simp only [Turing.ListBlank.head_cons, F, target_tm, Option.map_none, Option.isNone_none]

private theorem init_reaches_stack_system :
    ∃ cfg₀, ((init []) [target_tm]⊢⁺ cfg₀) ∧ IsInStackSystem cfg₀ := by
  refine ⟨cfg_M0 [] [(1, 0), (0, 0)], ?_, ⟨.M0, [], [(1, 0), (0, 0)], rfl⟩⟩
  rw [init_nil, cfg_M0_eq, encTail_nil, encTail_succ, encTail_zero, encRight_cons_simp]
  simp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
    listblank_append_nil, listblank_append_cons, encRight_nil, zero_cons_default]
  execute 4

-- ============================================================================
-- Intermediate Configurations (`cfg_D`, `wall`, `P_cfg`, `F_cfg`)
-- ============================================================================

private def cfg_D (c : ℕ) (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encTail L) <{{D}} ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R))

private def wall (L'' : List (ℕ × ℕ)) : ListBlank (Fin 2) :=
  (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    encTail L''

private def P_cfg (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ))
    : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨0, W +> wall L'', encRight R⟩⟩

private inductive FState
  | F00 | F01 | F02 | F03 | F04 | F05 | F06 | F07 | F08 | F09 | F10 | F11
deriving DecidableEq

private def F_cfg : FState → List (ℕ × ℕ) → List (Fin 2) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .F00, L'', W, R => (W +> wall L'') <{{E}} ((0 : Fin 2) >> encRight R)
  | .F01, L'', W, R => (W +> wall L'') <{{C}} ((0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F02, L'', W, R => (W +> wall L'') <{{A}} ((1 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F03, L'', W, R =>
    (W +> wall L'') <{{D}} ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F04, L'', W, R =>
    (W +> wall L'') <{{A}} ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F05, L'', W, R =>
    (W +> wall L'') <{{F}} ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F06, L'', W, R =>
    (W +> wall L'') <{{E}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> encRight R)
  | .F07, L'', W, R => (W +> wall L'') <{{C}} ((0 : Fin 2) >> encRight R)
  | .F08, L'', W, R => (W +> wall L'') <{{D}} ((0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F09, L'', W, R =>
    (W +> wall L'') <{{A}} ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F10, L'', W, R =>
    (W +> wall L'') <{{F}} ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)
  | .F11, L'', W, R =>
    (W +> wall L'') <{{E}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R)

-- Stage 3: Pushdown Induction & Universal Wipe Helpers
-- ============================================================================

private theorem zero_pow_append_zero (n : ℕ) (r : ListBlank (Fin 2)) :
    (([0] : List (Fin 2)) ^ n) +> ((0 : Fin 2) >> r) = (([0] : List (Fin 2)) ^ (n + 1)) +> r := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons, ih]

private theorem zero_pow_wall (k : ℕ) (L : List (ℕ × ℕ)) :
    (([0] : List (Fin 2)) ^ (k + 5)) +> ((1 : Fin 2) >> encTail L) =
      (([0] : List (Fin 2)) ^ k) +> wall L := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    have hsucc : k' + 1 + 5 = (k' + 5) + 1 := by omega
    rw [hsucc, pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons, ih,
      pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]

private theorem E_wipe_ones_right : ∀ (k : ℕ) (l tR : ListBlank (Fin 2)),
    (⟨some E, ⟨(1 : Fin 2), l,
      ((([1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> tR))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺ ⟨some A, ⟨0, (([0] : List (Fin 2)) ^ (k + 1)) +> l, tR⟩⟩
  | 0, l, tR => by execute 3
  | k + 1, l, tR => by
    have h1 : (⟨some E, ⟨(1 : Fin 2), l,
      ((([1] : List (Fin 2)) ^ (k + 1)) +> ((0 : Fin 2) >> tR))⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢⁺ ⟨some E, ⟨(1 : Fin 2), (0 : Fin 2) >> l,
          ((([1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> tR))⟩⟩ := by
      execute 1
    have h2 := E_wipe_ones_right k ((0 : Fin 2) >> l) tR
    rw [zero_pow_append_zero (k + 1) l] at h2
    exact stepPlus_trans h1 h2

private theorem A_wipe_ones (n : ℕ) (tL tR : ListBlank (Fin 2)) :
    (⟨some A, ⟨0, tL,
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ (n + 1)) +> ((0 : Fin 2) >>
        tR))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺ ⟨some A, ⟨0, (([0] : List (Fin 2)) ^ (n + 2)) +> ((1 : Fin 2) >> tL), tR⟩⟩ := by
  have h1 : (⟨some A, ⟨0, tL,
    (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ (n + 1)) +> ((0 : Fin 2) >>
      tR))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺ ⟨some E, ⟨(1 : Fin 2), (0 : Fin 2) >> (1 : Fin 2) >> tL,
        ((([1] : List (Fin 2)) ^ n) +> ((0 : Fin 2) >> tR))⟩⟩ := by
    execute 2
  have h2 := E_wipe_ones_right n ((0 : Fin 2) >> (1 : Fin 2) >> tL) tR
  rw [zero_pow_append_zero (n + 1) ((1 : Fin 2) >> tL)] at h2
  exact stepPlus_trans h1 h2

private theorem encTail_zero_eq_zero_cons_peelSep (b : ℕ) (S : List (ℕ × ℕ)) :
    encTail ((0, b) :: S) = (0 : Fin 2) >> encTail (peelSep b S) := by
  rcases S with _ | ⟨⟨a, b'⟩, S'⟩
  · simp [peelSep, encTail_zero]
  · rw [encTail_zero, zero_pow_one_add (b % 4), listblank_append_cons,
      ← encTail_peelSep b ((a, b') :: S')]

private def w : List (ℕ × ℕ) → ℕ
  | [] => 0
  | [(a, _)] => a
  | (a, b) :: r₂ :: rs => a + b % 2 + w (r₂ :: rs)

private def C0 : FState → ℕ
  | .F00 =>
    0 | .F01 =>
      1 | .F02 =>
        1 | .F03 =>
          0 | .F04 =>
            1 | .F05 => 1 | .F06 => 2 | .F07 => 1 | .F08 => 1 | .F09 => 2 | .F10 => 2 | .F11 => 3

private def C1 : FState → ℕ
  | .F00 =>
    1 | .F01 =>
      0 | .F02 =>
        0 | .F03 =>
          1 | .F04 =>
            0 | .F05 => 0 | .F06 => 1 | .F07 => 1 | .F08 => 2 | .F09 => 1 | .F10 => 1 | .F11 => 2

private theorem C0_le_C1_succ (s : FState) : C0 s ≤ C1 s + 1 := by
  cases s <;> decide

private theorem C1_le_C0_succ (s : FState) : C1 s ≤ C0 s + 1 := by
  cases s <;> decide

private theorem w_cons_nonempty (a b : ℕ) (R : List (ℕ × ℕ)) (hR : R ≠ []) :
    w ((a, b) :: R) = a + b % 2 + w R := by
  rcases R with _ | ⟨r₂, rs⟩
  · contradiction
  · rfl

private theorem w_bumpHead (R : List (ℕ × ℕ)) (hR : R ≠ []) :
    w (bumpHead R) = 1 + w R := by
  rcases R with _ | ⟨⟨a, b⟩, rs⟩
  · contradiction
  · rcases rs with _ | ⟨r₂, rs'⟩
    · simp [bumpHead, w]; omega
    · simp [bumpHead, w]; omega

private theorem w_peelInner_zero (b : ℕ) (S : List (ℕ × ℕ)) (h : S = [] ∨ b % 4 ≠ 0) :
    w ((0, 0) :: peelInner b S) = w ((0, b) :: S) := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · rfl
  · rcases mod4_cases b with h0 | h1 | h2 | h3
    · rcases h with hnil | hne
      · contradiction
      · exact False.elim (hne h0)
    · have hb2 : b % 2 = 1 := by omega
      have hne : ((a₂ + 1, b₂) :: rs) ≠ [] := by simp
      rw [peelInner, ite_eq_left h1, w_cons_nonempty 0 0 _ hne, w_cons_nonempty 0 b _ (by simp)]
      have hbmp : w ((a₂ + 1, b₂) :: rs) = 1 + w ((a₂, b₂) :: rs) :=
        w_bumpHead ((a₂, b₂) :: rs) (by simp)
      rw [hbmp, hb2]; omega
    · have hb2 : b % 2 = 0 := by omega
      have h1 : b % 4 ≠ 1 := by omega
      rw [peelInner, ite_eq_right h1, ite_eq_left h2]
      simp [w, hb2]
    · have hb2 : b % 2 = 1 := by omega
      have h1 : b % 4 ≠ 1 := by omega
      have h2 : b % 4 ≠ 2 := by omega
      rw [peelInner, ite_eq_right h1, ite_eq_right h2]
      simp [w, hb2]

private theorem w_add_ge1 (k b : ℕ) (S : List (ℕ × ℕ)) :
    w ((0, b) :: S) + (k + 1) = w ((k + 1, b) :: S) := by
  rcases S with _ | ⟨r₂, rs⟩
  · simp [w]
  · simp [w]; omega

private theorem P_step_0_rec (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (b : ℕ) (hb : b % 4 = 0)
    (R_tail : List (ℕ × ℕ)) (hR : R_tail ≠ []) :
    (P_cfg L'' W ((0, b) :: R_tail)) [target_tm]⊢⁺ P_cfg L'' (0 :: 1 :: W) R_tail := by
  rcases R_tail with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · contradiction
  · unfold P_cfg
    rw [encRight_cons_simp, hb, encRight_cons_eq_one_cons_encTail]
    execute 4

private theorem P_step_0_other (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (b : ℕ)
    (R_tail : List (ℕ × ℕ)) (h : R_tail = [] ∨ b % 4 ≠ 0) :
    (P_cfg L'' W ((0, b) :: R_tail)) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0,
      0) :: peelInner b R_tail) := by
  dsimp only [P_cfg, F_cfg]
  rw [encRight_zero_peelInner b R_tail h]
  rcases h_in : peelInner b R_tail with _ | ⟨⟨ai, bi⟩, rsi⟩
  · exact False.elim (peelInner_ne_nil b R_tail h_in)
  · rw [encRight_cons_simp 0 0, encRight_cons_eq_one_cons_encTail ai bi rsi]
    execute 9

private theorem P_step_ge1_pre (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (k b : ℕ) (R_tail :
  List (ℕ × ℕ)) :
    (P_cfg L'' W ((k + 1, b) :: R_tail)) [target_tm]⊢⁺
      ⟨some A, ⟨0, ((([0] : List (Fin 2)) ^ (k + 2)) ++ (1 :: W)) +> wall L'',
        encTail (peelSep b R_tail)⟩⟩ := by
  have henc : encRight ((k + 1, b) :: R_tail) =
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ (k + 1)) +> ((0 : Fin 2) >>
        encTail (peelSep b R_tail))) := by
    rw [encRight_cons_eq_one_cons_encTail (k + 1) b R_tail, encTail_cons (k + 1) b R_tail,
      zero_pow_one_add (b % 4), listblank_append_cons, ← encTail_peelSep]
  unfold P_cfg
  rw [henc]
  have hwipe := A_wipe_ones k (W +> wall L'') (encTail (peelSep b R_tail))
  rw [listblank_append_right_assoc, listblank_append_cons]
  exact hwipe

private theorem A_peel_two_zeros (tL_rest tP : ListBlank (Fin 2)) :
    (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> tL_rest, (0 : Fin 2) >> tP⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺ ⟨some A, ⟨0, tL_rest, (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> tP⟩⟩ := by
  execute 4

private theorem F00_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F00 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F01 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F01_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F01 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F02 L'' W (bumpHead R) := by
  dsimp only [F_cfg]; rw [encRight_bumpHead]; execute 5
private theorem F02_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F02 L'' (0 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: 1 :: W) (R) := by
  dsimp only [F_cfg, P_cfg]; execute 4
private theorem F03_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F03 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F04 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F04_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F04 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: (0, 0) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 0, encRight_cons_simp 0 0]; execute 9
private theorem F05_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F05 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F06 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F06_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F06 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F07 L'' W ((1, 2) :: R) := by
  dsimp only [F_cfg]; rw [encRight_succ 0 2, encRight_cons_simp 0 2]; execute 1
private theorem F07_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F07 L'' (0 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: W) (R) := by
  dsimp only [F_cfg, P_cfg]; execute 1
private theorem F08_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F08 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F09 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F09_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F09 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: bumpHead R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 0, encRight_bumpHead]; execute 9
private theorem F10_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F10 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F11 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F11_bit0 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F11 L'' (0 :: W) R) [target_tm]⊢⁺ F_cfg .F07 L'' W ((1, 1) :: R) := by
  dsimp only [F_cfg]; rw [encRight_succ 0 1, encRight_cons_simp 0 1]; execute 1
private theorem F00_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F00 L'' (1 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: W) (R) := by
  dsimp only [F_cfg, P_cfg]; execute 3
private theorem F01_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F01 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F03 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F02_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F02 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 0) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 0]; execute 1
private theorem F03_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F03 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F05 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F04_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F04 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 2) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 2]; execute 1
private theorem F05_bit1_halt (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (step target_tm (F_cfg .F05 L'' (1 :: W) R)).isNone = true := by
  dsimp only [F_cfg]; rw [listblank_append_cons]; exact F_halt_on_one _ _
private theorem F06_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F06 L'' (1 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: W) ((0, 0) :: (0, 0) :: R) := by
  dsimp only [F_cfg, P_cfg]; rw [encRight_cons_simp 0 0, encRight_cons_simp 0 0]; execute 9
private theorem F07_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F07 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F08 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F08_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F08 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F10 L'' W (R) := by
  dsimp only [F_cfg]; execute 1
private theorem F09_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F09 L'' (1 :: W) R) [target_tm]⊢⁺ F_cfg .F00 L'' W ((0, 1) :: R) := by
  dsimp only [F_cfg]; rw [encRight_cons_simp 0 1]; execute 1
private theorem F10_bit1_halt (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (step target_tm (F_cfg .F10 L'' (1 :: W) R)).isNone = true := by
  dsimp only [F_cfg]; rw [listblank_append_cons]; exact F_halt_on_one _ _
private theorem F11_bit1 (L'' : List (ℕ × ℕ)) (W : List (Fin 2)) (R : List (ℕ × ℕ)) :
    (F_cfg .F11 L'' (1 :: W) R) [target_tm]⊢⁺ P_cfg L'' (0 :: W) ((0, 0) :: bumpHead R) := by
  dsimp only [F_cfg, P_cfg]; rw [encRight_cons_simp 0 0, encRight_bumpHead]; execute 9

private def Stage3Out (start : Cfg (Fin 2) (Fin 6)) (L'' : List (ℕ × ℕ)) (W_out : List (Fin 2))
    (W_bound : ℕ) (C : FState → ℕ) : Prop :=
  (∃ cfg', (start [target_tm]⊢⁺ cfg') ∧ (step target_tm cfg').isNone) ∨
  (∃ s R_out, R_out ≠ [] ∧ w R_out + C s ≤ W_bound ∧
    (start [target_tm]⊢⁺ F_cfg s L'' W_out R_out))

private def Q0 (R : List (ℕ × ℕ)) : Prop :=
  ∀ L'' W_base, Stage3Out (P_cfg L'' W_base R) L'' W_base (w R) C0

private def Qz (R : List (ℕ × ℕ)) : Prop :=
  ∀ L'' W_base, Stage3Out (P_cfg L'' (0 :: W_base) R) L'' W_base (w R) C1

private def Qz1 (R : List (ℕ × ℕ)) : Prop :=
  ∀ L'' W_base, Stage3Out (P_cfg L'' (0 :: 1 :: W_base) R) L'' W_base (w R) C0

private theorem step_bit0 {start : Cfg (Fin 2) (Fin 6)} {L'' : List (ℕ × ℕ)} {W_out : List (Fin 2)}
    {W_bound : ℕ} {s : FState} {R₁ : List (ℕ × ℕ)}
    (h_reach : start [target_tm]⊢⁺ F_cfg s L'' (0 :: W_out) R₁)
    (hR₁ : R₁ ≠ []) (hw₁ : w R₁ + C0 s ≤ W_bound)
    (_ih_z : ∀ R', R' ≠ [] → w R' < W_bound → Qz R')
    (ih_z1 : ∀ R', R' ≠ [] → w R' < W_bound → Qz1 R') :
    Stage3Out start L'' W_out W_bound C1 := by
  cases s with
  | F00 => exact Or.inr ⟨.F01, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F00_bit0 L'' W_out R₁)⟩
  | F01 =>
    have hne_0 : (bumpHead R₁) ≠ [] := by
      rcases R₁ with _ | ⟨_, _⟩
      · exact False.elim (hR₁ rfl)
      · simp [bumpHead]
    have hw_op_0 : w (bumpHead R₁) = 1 + w (R₁) := w_bumpHead (R₁) hR₁
    refine Or.inr ⟨.F02, bumpHead R₁, hne_0, ?_, stepPlus_trans h_reach (F01_bit0 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F02 =>
    have hlt : w R₁ < W_bound := by dsimp [C0] at hw₁; omega
    have h_p := stepPlus_trans h_reach (F02_bit0 L'' W_out R₁)
    rcases ih_z1 R₁ hR₁ hlt L'' W_out with ⟨cfg', h1, h2⟩ | ⟨s', R_out, hne, hw_out, h1⟩
    · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
    · have hc := C1_le_C0_succ s'
      exact Or.inr ⟨s', R_out, hne, by dsimp [C0] at hw₁; omega, stepPlus_trans h_p h1⟩
  | F03 => exact Or.inr ⟨.F04, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F03_bit0 L'' W_out R₁)⟩
  | F04 =>
    have hne_0 : ((0, 0) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((0, 0) :: R₁) = 0 + w (R₁) := by rw [w_cons_nonempty 0 0 (R₁) hR₁]; try omega
    have hne_1 : ((0, 0) :: (0, 0) :: R₁) ≠ [] := by simp
    have hw_op_1 : w ((0, 0) :: (0, 0) :: R₁) = 0 + w ((0, 0) :: R₁) := by
      rw [w_cons_nonempty 0 0 ((0, 0) :: R₁) hne_0]; try omega
    refine Or.inr ⟨.F00, (0, 0) :: (0, 0) :: R₁, hne_1, ?_,
      stepPlus_trans h_reach (F04_bit0 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F05 => exact Or.inr ⟨.F06, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F05_bit0 L'' W_out R₁)⟩
  | F06 =>
    have hne_0 : ((1, 2) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((1, 2) :: R₁) = 1 + w (R₁) := by rw [w_cons_nonempty 1 2 (R₁) hR₁]; try omega
    refine Or.inr ⟨.F07, (1, 2) :: R₁, hne_0, ?_, stepPlus_trans h_reach (F06_bit0 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F07 =>
    have hlt : w R₁ < W_bound := by dsimp [C0] at hw₁; omega
    have h_p := stepPlus_trans h_reach (F07_bit0 L'' W_out R₁)
    rcases _ih_z R₁ hR₁ hlt L'' W_out with ⟨cfg', h1, h2⟩ | ⟨s', R_out, hne, hw_out, h1⟩
    · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
    · exact Or.inr ⟨s', R_out, hne, by dsimp [C0] at hw₁; omega, stepPlus_trans h_p h1⟩
  | F08 => exact Or.inr ⟨.F09, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F08_bit0 L'' W_out R₁)⟩
  | F09 =>
    have hne_0 : (bumpHead R₁) ≠ [] := by
      rcases R₁ with _ | ⟨_, _⟩
      · exact False.elim (hR₁ rfl)
      · simp [bumpHead]
    have hw_op_0 : w (bumpHead R₁) = 1 + w (R₁) := w_bumpHead (R₁) hR₁
    have hne_1 : ((0, 0) :: bumpHead R₁) ≠ [] := by simp
    have hw_op_1 : w ((0, 0) :: bumpHead R₁) = 0 + w (bumpHead R₁) := by
      rw [w_cons_nonempty 0 0 (bumpHead R₁) hne_0]; try omega
    refine Or.inr ⟨.F00, (0, 0) :: bumpHead R₁, hne_1, ?_,
      stepPlus_trans h_reach (F09_bit0 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F10 => exact Or.inr ⟨.F11, R₁, hR₁, by dsimp [C0, C1] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F10_bit0 L'' W_out R₁)⟩
  | F11 =>
    have hne_0 : ((1, 1) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((1, 1) :: R₁) = 2 + w (R₁) := by rw [w_cons_nonempty 1 1 (R₁) hR₁]; try omega
    refine Or.inr ⟨.F07, (1, 1) :: R₁, hne_0, ?_, stepPlus_trans h_reach (F11_bit0 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega

private theorem step_bit1 {start : Cfg (Fin 2) (Fin 6)} {L'' : List (ℕ × ℕ)} {W_out : List (Fin 2)}
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
  | F01 => exact Or.inr ⟨.F03, R₁, hR₁, by dsimp [C1, C0] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F01_bit1 L'' W_out R₁)⟩
  | F02 =>
    have hne_0 : ((0, 0) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((0, 0) :: R₁) = 0 + w (R₁) := by rw [w_cons_nonempty 0 0 (R₁) hR₁]; try omega
    refine Or.inr ⟨.F00, (0, 0) :: R₁, hne_0, ?_, stepPlus_trans h_reach (F02_bit1 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F03 => exact Or.inr ⟨.F05, R₁, hR₁, by dsimp [C1, C0] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F03_bit1 L'' W_out R₁)⟩
  | F04 =>
    have hne_0 : ((0, 2) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((0, 2) :: R₁) = 0 + w (R₁) := by rw [w_cons_nonempty 0 2 (R₁) hR₁]; try omega
    refine Or.inr ⟨.F00, (0, 2) :: R₁, hne_0, ?_, stepPlus_trans h_reach (F04_bit1 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F05 => exact Or.inl ⟨F_cfg .F05 L'' (1 :: W_out) R₁, h_reach, F05_bit1_halt L'' W_out R₁⟩
  | F06 =>
    have hne_0 : ((0, 0) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((0, 0) :: R₁) = 0 + w (R₁) := by rw [w_cons_nonempty 0 0 (R₁) hR₁]; try omega
    have hne_1 : ((0, 0) :: (0, 0) :: R₁) ≠ [] := by simp
    have hw_op_1 : w ((0, 0) :: (0, 0) :: R₁) = 0 + w ((0, 0) :: R₁) := by
      rw [w_cons_nonempty 0 0 ((0, 0) :: R₁) hne_0]; try omega
    have hlt : w ((0, 0) :: (0, 0) :: R₁) < W_bound := by dsimp [C1] at hw₁; omega
    have h_p := stepPlus_trans h_reach (F06_bit1 L'' W_out R₁)
    rcases ih_z ((0, 0) :: (0, 0) :: R₁) hne_1 hlt L'' W_out with ⟨cfg', h1, h2⟩ | ⟨s', R_out,
      hne, hw_out, h1⟩
    · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
    · have hc := C0_le_C1_succ s'
      exact Or.inr ⟨s', R_out, hne, by dsimp [C1] at hw₁; omega, stepPlus_trans h_p h1⟩
  | F07 => exact Or.inr ⟨.F08, R₁, hR₁, by dsimp [C1, C0] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F07_bit1 L'' W_out R₁)⟩
  | F08 => exact Or.inr ⟨.F10, R₁, hR₁, by dsimp [C1, C0] at hw₁ ⊢; omega,
    stepPlus_trans h_reach (F08_bit1 L'' W_out R₁)⟩
  | F09 =>
    have hne_0 : ((0, 1) :: R₁) ≠ [] := by simp
    have hw_op_0 : w ((0, 1) :: R₁) = 1 + w (R₁) := by rw [w_cons_nonempty 0 1 (R₁) hR₁]; try omega
    refine Or.inr ⟨.F00, (0, 1) :: R₁, hne_0, ?_, stepPlus_trans h_reach (F09_bit1 L'' W_out R₁)⟩
    dsimp [C0, C1] at hw₁ ⊢; omega
  | F10 => exact Or.inl ⟨F_cfg .F10 L'' (1 :: W_out) R₁, h_reach, F10_bit1_halt L'' W_out R₁⟩
  | F11 =>
    have hne_0 : (bumpHead R₁) ≠ [] := by
      rcases R₁ with _ | ⟨_, _⟩
      · exact False.elim (hR₁ rfl)
      · simp [bumpHead]
    have hw_op_0 : w (bumpHead R₁) = 1 + w (R₁) := w_bumpHead (R₁) hR₁
    have hne_1 : ((0, 0) :: bumpHead R₁) ≠ [] := by simp
    have hw_op_1 : w ((0, 0) :: bumpHead R₁) = 0 + w (bumpHead R₁) := by
      rw [w_cons_nonempty 0 0 (bumpHead R₁) hne_0]; try omega
    have hlt : w ((0, 0) :: bumpHead R₁) < W_bound := by dsimp [C1] at hw₁; omega
    have h_p := stepPlus_trans h_reach (F11_bit1 L'' W_out R₁)
    rcases ih_z ((0, 0) :: bumpHead R₁) hne_1 hlt L'' W_out with ⟨cfg', h1, h2⟩ | ⟨s', R_out,
      hne, hw_out, h1⟩
    · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
    · have hc := C0_le_C1_succ s'
      exact Or.inr ⟨s', R_out, hne, by dsimp [C1] at hw₁; omega, stepPlus_trans h_p h1⟩

private theorem step_zeros_c1 : ∀ (m : ℕ) {start : Cfg (Fin 2) (Fin 6)} {L'' : List (ℕ × ℕ)}
    {W_rest : List (Fin 2)} {B W_max : ℕ} {s : FState} {R₁ : List (ℕ × ℕ)},
    (start [target_tm]⊢⁺ F_cfg s L'' ((([0] : List (Fin 2)) ^ m) ++ W_rest) R₁) →
    R₁ ≠ [] → w R₁ + C1 s ≤ B → B + m ≤ W_max →
    (∀ R', R' ≠ [] → w R' < W_max → Qz R') →
    (∀ R', R' ≠ [] → w R' < W_max → Qz1 R') →
    Stage3Out start L'' W_rest (B + m) C1
  | 0, start, L'', W_rest, B, _, s, R₁, h_reach, hR₁, hw₁, _, _, _ => by
    rw [pow_zero_list, nil_append_list] at h_reach
    exact Or.inr ⟨s, R₁, hR₁, by omega, h_reach⟩
  | m + 1, start, L'', W_rest, B, W_max, s, R₁, h_reach, hR₁, hw₁, hmax, ih_z, ih_z1 => by
    rw [pow_succ_list, cons_append_list, nil_append_list, cons_append_list] at h_reach
    have hc0 := C0_le_C1_succ s
    have hw0 : w R₁ + C0 s ≤ B + 1 := by omega
    rcases step_bit0 h_reach hR₁ hw0
        (fun R' hR' hlt => ih_z R' hR' (by omega))
        (fun R' hR' hlt => ih_z1 R' hR' (by omega)) with
      ⟨cfg', h1, h2⟩ | ⟨s', R₂, hR₂, hw₂, h1⟩
    · exact Or.inl ⟨cfg', h1, h2⟩
    · have hrec := step_zeros_c1 m h1 hR₂ hw₂ (by omega : (B + 1) + m ≤ W_max) ih_z ih_z1
      rcases hrec with ⟨cfg', g1, g2⟩ | ⟨sf, Rf, hRf, hwf, g1⟩
      · exact Or.inl ⟨cfg', g1, g2⟩
      · exact Or.inr ⟨sf, Rf, hRf, by omega, g1⟩

private theorem stage3_ind (W_val : ℕ) :
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
        rcases a with _ | k
        · -- a = 0
          rcases R_tail with _ | ⟨r₂, rs⟩
          · refine Or.inr ⟨.F00, (0, 0) :: peelInner b [], by simp, ?_,
              P_step_0_other L'' W_base b [] (Or.inl rfl)⟩
            rw [w_peelInner_zero b [] (Or.inl rfl), C0]; omega
          · rcases mod4_cases b with hb0 | hb1 | hb2 | hb3
            · have hne : (r₂ :: rs) ≠ [] := by simp
              have hb2 : b % 2 = 0 := by omega
              have hw_eq : w ((0, b) :: r₂ :: rs) = w (r₂ :: rs) := by simp [w, hb2]
              have hQz1_tail : Qz1 (r₂ :: rs) := (ih_tail hne (by omega)).2.2
              have h_p := P_step_0_rec L'' W_base b hb0 (r₂ :: rs) hne
              rcases hQz1_tail L'' W_base with ⟨cfg', h1, h2⟩ | ⟨s', R_out, hne_out, hw_out, h1⟩
              · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
              · exact Or.inr ⟨s', R_out, hne_out, by omega, stepPlus_trans h_p h1⟩
            · have hcond : (r₂ :: rs) = [] ∨ b % 4 ≠ 0 := Or.inr (by omega)
              refine Or.inr ⟨.F00, (0, 0) :: peelInner b (r₂ :: rs), by simp, ?_,
                P_step_0_other L'' W_base b (r₂ :: rs) hcond⟩
              rw [w_peelInner_zero b (r₂ :: rs) hcond, C0]; omega
            · have hcond : (r₂ :: rs) = [] ∨ b % 4 ≠ 0 := Or.inr (by omega)
              refine Or.inr ⟨.F00, (0, 0) :: peelInner b (r₂ :: rs), by simp, ?_,
                P_step_0_other L'' W_base b (r₂ :: rs) hcond⟩
              rw [w_peelInner_zero b (r₂ :: rs) hcond, C0]; omega
            · have hcond : (r₂ :: rs) = [] ∨ b % 4 ≠ 0 := Or.inr (by omega)
              refine Or.inr ⟨.F00, (0, 0) :: peelInner b (r₂ :: rs), by simp, ?_,
                P_step_0_other L'' W_base b (r₂ :: rs) hcond⟩
              rw [w_peelInner_zero b (r₂ :: rs) hcond, C0]; omega
        · -- a = k + 1
          have hpre := P_step_ge1_pre L'' W_base k b R_tail
          by_cases h_rec : R_tail ≠ [] ∧ b % 4 = 0
          · obtain ⟨hne_tail, hb0⟩ := h_rec
            have h_p : (P_cfg L'' W_base ((k + 1, b) :: R_tail)) [target_tm]⊢⁺
                P_cfg L'' (0 :: ((([0] : List (Fin 2)) ^ (k + 1)) ++ (1 :: W_base))) R_tail := by
              rcases R_tail with _ | ⟨⟨a₂, b₂⟩, rs⟩
              · contradiction
              · unfold P_cfg at hpre ⊢
                rw [peelSep, ite_eq_left hb0, encTail_succ,
                  ← encRight_cons_eq_one_cons_encTail] at hpre
                exact hpre
            have hw_tail : w R_tail + (k + 1) = W_val := by
              rw [← hw_ab, ← w_add_ge1 k b R_tail, w_cons_nonempty 0 b R_tail hne_tail]
              have : b % 2 = 0 := by omega
              omega
            rcases ih_z R_tail hne_tail (by omega) L'' ((([0] :
              List (Fin 2)) ^ (k + 1)) ++ (1 :: W_base)) with
              ⟨cfg', h1, h2⟩ | ⟨s1, R1, hR1, hw1, h1⟩
            · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
            · rcases step_zeros_c1 (k + 1) (stepPlus_trans h_p h1) hR1 hw1 (by omega :
                w R_tail + (k + 1) ≤ W_val) ih_z ih_z1 with
                ⟨cfg', h2, h3⟩ | ⟨s2, R2, hR2, hw2, h2⟩
              · exact Or.inl ⟨cfg', h2, h3⟩
              · rw [hw_tail] at hw2
                exact step_bit1 h2 hR2 hw2 ih_z
          · have hcond : R_tail = [] ∨ b % 4 ≠ 0 := by
              rcases R_tail with _ | ⟨r₂, rs⟩
              · exact Or.inl rfl
              · exact Or.inr (fun h0 => h_rec ⟨by simp, h0⟩)
            set R1 := (0, 0) :: peelInner b R_tail
            have hR1 : R1 ≠ [] := by simp [R1]
            have hz : encTail (peelSep b R_tail) = (0 : Fin 2) >> encTail (peelInner b R_tail) := by
              have hl := encRight_zero_peelInner b R_tail hcond
              rw [encRight_cons_eq_one_cons_encTail 0 b R_tail,
                encTail_zero_eq_zero_cons_peelSep] at hl
              simpa only [Turing.ListBlank.tail_cons] using congrArg (fun t => t.tail.tail) hl
            have hpost : ⟨some A, ⟨0,
              ((([0] : List (Fin 2)) ^ (k + 2)) ++ (1 :: W_base)) +> wall L'',
                encTail (peelSep b R_tail)⟩⟩ [target_tm]⊢⁺
                P_cfg L'' ((([0] : List (Fin 2)) ^ k) ++ (1 :: W_base)) R1 := by
              unfold P_cfg
              rw [hz]
              rcases h_in : peelInner b R_tail with _ | ⟨⟨ai, bi⟩, rsi⟩
              · exact False.elim (peelInner_ne_nil b R_tail h_in)
              · have hr1 : encRight R1 = (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                  encTail ((ai, bi) :: rsi) := by
                  rw [show R1 = (0, 0) :: (ai, bi) :: rsi from congrArg ((0, 0) :: ·) h_in,
                    encRight_cons_simp 0 0, encRight_cons_eq_one_cons_encTail]
                  rfl
                rw [hr1]
                exact A_peel_two_zeros (((([0] : List (Fin 2)) ^ k) ++ (1 :: W_base)) +> wall L'')
                  (encTail ((ai, bi) :: rsi))
            have hw1 : w R1 + (k + 1) = W_val := by
              rw [← hw_ab, ← w_add_ge1 k b R_tail, ← w_peelInner_zero b R_tail hcond]
            have hQ0_R1 : Q0 R1 := (ih_w (w R1) (by omega) R1 hR1 rfl).1
            have h_p := stepPlus_trans hpre hpost
            rcases hQ0_R1 L'' ((([0] : List (Fin 2)) ^ k) ++ (1 :: W_base)) with
              ⟨cfg', h1, h2⟩ | ⟨s1, R_out1, hne1, hw_out1, h1⟩
            · exact Or.inl ⟨cfg', stepPlus_trans h_p h1, h2⟩
            · have hc1 : w R_out1 + C1 s1 ≤ w R1 + 1 := by
                have := C1_le_C0_succ s1
                omega
              rcases step_zeros_c1 k (stepPlus_trans h_p h1) hne1 hc1 (by omega :
                (w R1 + 1) + k ≤ W_val) ih_z ih_z1 with
                ⟨cfg', h2, h3⟩ | ⟨s2, R_out2, hne2, hw_out2, h2⟩
              · exact Or.inl ⟨cfg', h2, h3⟩
              · have hw2 : w R_out2 + C1 s2 ≤ W_val := by omega
                exact step_bit1 h2 hne2 hw2 ih_z
      have hQz : Qz ((a, b) :: R_tail) := fun L'' W_base => by
        rw [hw_ab]
        rcases hQ0 L'' (0 :: W_base) with ⟨cfg', h1, h2⟩ | ⟨s0, R1, hR1, hw1, h1⟩
        · exact Or.inl ⟨cfg', h1, h2⟩
        · rw [hw_ab] at hw1
          exact step_bit0 h1 hR1 hw1 ih_z ih_z1
      have hQz1 : Qz1 ((a, b) :: R_tail) := fun L'' W_base => by
        rw [hw_ab]
        rcases hQz L'' (1 :: W_base) with ⟨cfg', h1, h2⟩ | ⟨s1, R1, hR1, hw1, h1⟩
        · exact Or.inl ⟨cfg', h1, h2⟩
        · rw [hw_ab] at hw1
          exact step_bit1 h1 hR1 hw1 ih_z
      exact ⟨hQ0, hQz, hQz1⟩

private theorem F00_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F00 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 3) :: tailAsRight L'') ((0, 0) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 3,
    encRight_tailAsRight, encTail_zero 0]; execute 2

private theorem F01_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F01 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((1,
      0) :: bumpHead R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2,
    encRight_tailAsRight, encTail_succ 0, encTail_zero 0, encRight_bumpHead]; execute 5

private theorem F02_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F02 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: (0,
      3) :: tailAsRight L'') (rightAsTail R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 0,
    encRight_cons_simp 0 3, encRight_tailAsRight, encTail_rightAsTail]; execute 4

private theorem F03_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F03 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((1, 2) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2,
    encRight_tailAsRight, encTail_succ 0, encTail_zero 2]; execute 1

private theorem F04_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F04 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: (0, 3) :: tailAsRight L'') ((0,
      1) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 0,
    encRight_cons_simp 0 3, encRight_tailAsRight, encTail_zero 1]; execute 4

private theorem F05_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F05 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((2, 2) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2,
    encRight_tailAsRight, encTail_succ 1, encTail_succ 0, encTail_zero 2]; execute 3

private theorem F06_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F06 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 3) :: tailAsRight L'') ((2, 2) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 3,
    encRight_tailAsRight, encTail_succ 1, encTail_succ 0, encTail_zero 2]; execute 2

private theorem F07_p_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F07 L'' [] R) [target_tm]⊢⁺ P_cfg L'' [] R := by
  dsimp only [F_cfg, P_cfg, wall]; rw [listblank_append_nil]; execute 1

private theorem F08_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F08 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((1, 1) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2,
    encRight_tailAsRight, encTail_succ 0, encTail_zero 1]; execute 1

private theorem F09_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F09 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: (0, 3) :: tailAsRight L'') ((0,
      0) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 0,
    encRight_cons_simp 0 3, encRight_tailAsRight, encTail_zero 0]; execute 4

private theorem F10_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F10 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L'') ((2, 1) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 2,
    encRight_tailAsRight, encTail_succ 1, encTail_succ 0, encTail_zero 1]; execute 3

private theorem F11_exit (L'' R : List (ℕ × ℕ)) :
    (F_cfg .F11 L'' [] R) [target_tm]⊢⁺ cfg_M0 ((0, 3) :: tailAsRight L'') ((2, 1) :: R) := by
  dsimp only [F_cfg, wall]; rw [cfg_M0_eq, listblank_append_nil, encTail_zero 3,
    encRight_tailAsRight, encTail_succ 1, encTail_succ 0, encTail_zero 1]; execute 2

private theorem stage3_closed_aux (W_val : ℕ) :
    ∀ L'' R, R ≠ [] → w R = W_val →
      ∃ cfg', ((P_cfg L'' [] R) [target_tm]⊢⁺ cfg') ∧
        (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  induction W_val using Nat.strong_induction_on with
  | h W_val ih_exit =>
    intro L'' R hR hw
    have hQ0 : Q0 R := (stage3_ind W_val R hR hw).1
    rcases hQ0 L'' [] with ⟨cfg', h1, h2⟩ | ⟨s, R_out, hR_out, hw_out, h1⟩
    · exact ⟨cfg', h1, Or.inr h2⟩
    · rw [hw] at hw_out
      cases s with
    | F00 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F00_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F01 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F01_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F02 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F02_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F03 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F03_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F04 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F04_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F05 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F05_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F06 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F06_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F07 =>
      have hlt_out : w R_out < W_val := by dsimp [C0] at hw_out; omega
      have hp := stepPlus_trans h1 (F07_p_exit L'' R_out)
      obtain ⟨cfg'', h2, hout2⟩ := ih_exit (w R_out) hlt_out L'' R_out hR_out rfl
      exact ⟨cfg'', stepPlus_trans hp h2, hout2⟩
    | F08 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F08_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F09 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F09_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F10 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F10_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩
    | F11 =>
      exact ⟨cfg_M0 _ _, stepPlus_trans h1 (F11_exit L'' R_out), Or.inl ⟨.M0, _, _, rfl⟩⟩

private theorem stage3_closed (L'' R : List (ℕ × ℕ)) (hR : R ≠ []) :
    ∃ cfg', ((P_cfg L'' [] R) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) :=
  stage3_closed_aux (w R) L'' R hR rfl

-- ============================================================================
-- Stage 1: Unified `cfg_M0 L R` -> `cfg_M0`, `cfg_D 0`, or Halt
-- ============================================================================

private theorem F_empty_closed {start : Cfg (Fin 2) (Fin 6)} (s : FState) (L'' R : List (ℕ × ℕ))
    (_hR : R ≠ []) (h_reach : start [target_tm]⊢⁺ F_cfg s L'' [] R) :
    ∃ cfg', (start [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  cases s with
  | F00 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F00_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F01 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F01_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F02 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F02_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F03 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F03_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F04 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F04_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F05 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F05_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F06 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F06_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F07 =>
    obtain ⟨cfg'', h3, hout3⟩ := stage3_closed L'' R _hR
    exact ⟨cfg'', stepPlus_trans (stepPlus_trans h_reach (F07_p_exit L'' R)) h3, hout3⟩
  | F08 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F08_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F09 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F09_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F10 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F10_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩
  | F11 => exact ⟨cfg_M0 _ _, stepPlus_trans h_reach (F11_exit L'' R), Or.inl ⟨.M0, _, _, rfl⟩⟩

private theorem P_drain_zeros : ∀ (k : ℕ) {start : Cfg (Fin 2) (Fin 6)} (L'' R : List (ℕ × ℕ)),
    R ≠ [] → (start [target_tm]⊢⁺ P_cfg L'' (([0] : List (Fin 2)) ^ k) R) →
    ∃ cfg', (start [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone)
  | 0, start, L'', R, hR, h_reach => by
    rw [pow_zero_list] at h_reach
    obtain ⟨cfg', h2, hout⟩ := stage3_closed L'' R hR
    exact ⟨cfg', stepPlus_trans h_reach h2, hout⟩
  | k + 1, start, L'', R, hR, h_reach => by
    rw [pow_succ_list, cons_append_list, nil_append_list] at h_reach
    rcases (stage3_ind (w R) R hR rfl).2.1 L'' (([0] : List (Fin 2)) ^ k) with
      ⟨cfg', h1, h2⟩ | ⟨s1, R1, hR1, hw1, h1⟩
    · exact ⟨cfg', stepPlus_trans h_reach h1, Or.inr h2⟩
    · have hp1 := stepPlus_trans h_reach h1
      rw [← append_nil_list (([0] : List (Fin 2)) ^ k)] at hp1
      rcases step_zeros_c1 k hp1 hR1 hw1 (Nat.le_refl _)
          (fun R' hR' _ => (stage3_ind (w R') R' hR' rfl).2.1)
          (fun R' hR' _ => (stage3_ind (w R') R' hR' rfl).2.2) with
        ⟨cfg', h2, h3⟩ | ⟨s2, R2, hR2, _, h2⟩
      · exact ⟨cfg', h2, Or.inr h3⟩
      · exact F_empty_closed s2 L'' R2 hR2 h2

private theorem M0_nil (L : List (ℕ × ℕ)) :
    (cfg_M0 L []) [target_tm]⊢⁺ cfg_D 0 L [] := by
  rw [cfg_M0_eq, cfg_D, encTail_nil]
  execute 3

private theorem M0_zero (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((0, bR) :: R')) [target_tm]⊢⁺ cfg_D 0 L (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_D, encTail_zero, zero_pow_one_add (bR % 4),
    listblank_append_cons, ← encTail_peelSep]
  execute 3

private theorem M0_one (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((1, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 0) :: tailAsRight L) (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ, encTail_zero, encTail_zero 0 (tailAsRight L),
    encRight_tailAsRight, zero_pow_one_add (bR % 4), listblank_append_cons,
    ← encTail_peelSep]
  execute 4

private theorem M0_two (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((2, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 1) :: tailAsRight L) (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ 1, encTail_succ 0, encTail_zero bR,
    encTail_zero 1 (tailAsRight L), encRight_tailAsRight, zero_pow_one_add (bR % 4),
    listblank_append_cons, ← encTail_peelSep]
  execute 5

private theorem M0_three (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((3, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 2) :: tailAsRight L) (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ 2, encTail_succ 1, encTail_succ 0,
    encTail_zero bR, encTail_zero 2 (tailAsRight L), encRight_tailAsRight,
      zero_pow_one_add (bR % 4),
    listblank_append_cons, ← encTail_peelSep]
  execute 6

private theorem M0_four (L : List (ℕ × ℕ)) (bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((4, bR) :: R')) [target_tm]⊢⁺ cfg_M0 ((0, 3) :: tailAsRight L) (peelSep bR R') := by
  rw [cfg_M0_eq, cfg_M0_eq, encTail_succ 3, encTail_succ 2, encTail_succ 1, encTail_succ 0,
    encTail_zero bR, encTail_zero 3 (tailAsRight L), encRight_tailAsRight,
      zero_pow_one_add (bR % 4),
    listblank_append_cons, ← encTail_peelSep]
  execute 7

private theorem M0_add5_pre (L : List (ℕ × ℕ)) (k bR : ℕ) (R' : List (ℕ × ℕ)) :
    (cfg_M0 L ((k + 5, bR) :: R')) [target_tm]⊢⁺
      ⟨some A, ⟨0, (([0] : List (Fin 2)) ^ k) +> wall L, encTail (peelSep bR R')⟩⟩ := by
  have htail : encTail ((k + 5, bR) :: R') =
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ (k + 4)) +> ((0 : Fin 2) >>
        encTail (peelSep bR R'))) := by
    rw [encTail_succ (k + 4), encTail_cons (k + 4) bR R',
      zero_pow_one_add (bR % 4), listblank_append_cons, ← encTail_peelSep]
  rw [cfg_M0_eq, htail]
  have hw := A_wipe_ones (k + 3) (encTail L) (encTail (peelSep bR R'))
  rw [zero_pow_wall k L] at hw
  exact hw

private theorem A_wall_peelSep_closed {start : Cfg (Fin 2) (Fin 6)} (L : List (ℕ × ℕ)) (k bR :
  ℕ) (R' : List (ℕ × ℕ))
    (hpre : start [target_tm]⊢⁺ ⟨some A, ⟨0, (([0] : List (Fin 2)) ^ k) +> wall L,
      encTail (peelSep bR R')⟩⟩) :
    ∃ cfg', (start [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  by_cases h_rec : R' ≠ [] ∧ bR % 4 = 0
  · obtain ⟨hne, hb0⟩ := h_rec
    rcases R' with _ | ⟨⟨a₂, b₂⟩, R''⟩
    · contradiction
    · have hpost : start [target_tm]⊢⁺
          P_cfg L (([0] : List (Fin 2)) ^ k) ((a₂, b₂) :: R'') := by
        unfold P_cfg
        rw [peelSep, ite_eq_left hb0, encTail_succ, ← encRight_cons_eq_one_cons_encTail] at hpre
        exact hpre
      exact P_drain_zeros k L ((a₂, b₂) :: R'') (by simp) hpost
  · have hcond : R' = [] ∨ bR % 4 ≠ 0 := by
      rcases R' with _ | ⟨r₂, rs⟩
      · exact Or.inl rfl
      · exact Or.inr (fun h0 => h_rec ⟨by simp, h0⟩)
    have hz : encTail (peelSep bR R') = (0 : Fin 2) >> encTail (peelInner bR R') := by
      have hl := encRight_zero_peelInner bR R' hcond
      rw [encRight_cons_eq_one_cons_encTail 0 bR R', encTail_zero_eq_zero_cons_peelSep] at hl
      simpa only [Turing.ListBlank.tail_cons] using congrArg (fun t => t.tail.tail) hl
    rcases h_in : peelInner bR R' with _ | ⟨⟨ai, bi⟩, rsi⟩
    · exact False.elim (peelInner_ne_nil bR R' h_in)
    · rcases k with _ | _ | k'
      · refine ⟨cfg_M0 ((0, 2) :: tailAsRight L) ((1, 0) :: (ai, bi) :: rsi), ?_,
          Or.inl ⟨.M0, _, _, rfl⟩⟩
        rw [hz, h_in] at hpre
        have hp2 :=
          A_peel_two_zeros ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail L)
          (encTail ((ai, bi) :: rsi))
        have hrhs : cfg_M0 ((0, 2) :: tailAsRight L) ((1, 0) :: (ai, bi) :: rsi) =
            ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail L,
              (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((ai, bi) :: rsi)⟩⟩ := by
          rw [cfg_M0_eq, encTail_zero 2 (tailAsRight L), encRight_tailAsRight,
            encTail_succ 0, encTail_zero 0 ((ai, bi) :: rsi), encRight_cons_eq_one_cons_encTail]
          rfl
        rw [hrhs]
        exact stepPlus_trans hpre hp2
      · refine ⟨cfg_M0 ((0, 3) :: tailAsRight L) ((1, 0) :: (ai, bi) :: rsi), ?_,
          Or.inl ⟨.M0, _, _, rfl⟩⟩
        rw [hz, h_in] at hpre
        have hp2 :=
          A_peel_two_zeros ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> encTail L)
          (encTail ((ai, bi) :: rsi))
        have hrhs : cfg_M0 ((0, 3) :: tailAsRight L) ((1, 0) :: (ai, bi) :: rsi) =
            ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
              (1 : Fin 2) >> encTail L,
              (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((ai, bi) :: rsi)⟩⟩ := by
          rw [cfg_M0_eq, encTail_zero 3 (tailAsRight L), encRight_tailAsRight,
            encTail_succ 0, encTail_zero 0 ((ai, bi) :: rsi), encRight_cons_eq_one_cons_encTail]
          rfl
        rw [hrhs]
        exact stepPlus_trans hpre hp2
      · rw [hz, h_in] at hpre
        have hp2 : start [target_tm]⊢⁺
            P_cfg L (([0] : List (Fin 2)) ^ k') ((0, 0) :: (ai, bi) :: rsi) := by
          unfold P_cfg
          rw [encRight_cons_simp 0 0, encRight_cons_eq_one_cons_encTail ai bi rsi]
          dsimp only [pow_zero_list, pow_succ_list, nil_append_list, cons_append_list,
            listblank_append_nil, listblank_append_cons] at hpre ⊢
          exact stepPlus_trans hpre (A_peel_two_zeros ((([0] : List (Fin 2)) ^ k') +>
            wall L) (encTail ((ai, bi) :: rsi)))
        exact P_drain_zeros k' L ((0, 0) :: (ai, bi) :: rsi) (by simp) hp2

private theorem M0_add5_closed (L : List (ℕ × ℕ)) (k bR : ℕ) (R' : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_M0 L ((k + 5, bR) :: R')) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) :=
  A_wall_peelSep_closed L k bR R' (M0_add5_pre L k bR R')

-- Stage 2: `cfg_D c L R` (`c < 4`) -> `cfg_M0`, Halt, or `P_cfg`
-- ============================================================================

private theorem RD_eq_encRight (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      encRight ((0, c) :: tailAsRight R) := by
  rw [encRight_cons_simp, Nat.mod_eq_of_lt hc, encRight_tailAsRight]
  rfl

private theorem RD_eq_encTail_one (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      encTail ((1, c) :: tailAsRight R) := by
  rw [encTail_succ, encTail_zero, Nat.mod_eq_of_lt hc, encRight_tailAsRight]

private theorem one_cons_RD_eq (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      (1 : Fin 2) >> encTail ((0, c) :: tailAsRight R) := by
  rw [encTail_zero, Nat.mod_eq_of_lt hc, encRight_tailAsRight]

private theorem RD_eq_encTail_two (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)) =
      encTail ((2, c) :: tailAsRight R) := by
  rw [encTail_succ 1, encTail_succ 0, encTail_zero, Nat.mod_eq_of_lt hc, encRight_tailAsRight]

private theorem rD_eq_zero_cons_peelSep (c : ℕ) (hc : c < 4) (R : List (ℕ × ℕ)) :
    (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R) =
      (0 : Fin 2) >> encTail (peelSep c (tailAsRight R)) := by
  rw [encTail_peelSep c (tailAsRight R), Nat.mod_eq_of_lt hc, encRight_tailAsRight,
    zero_pow_one_add c, listblank_append_cons]

private theorem D_leaf_00 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (0 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, tL, (1 : Fin 2) >> rD⟩⟩ := by
  execute 1

private theorem D_leaf_0100 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> tL, (0 : Fin 2) >> (1 : Fin 2) >> rD⟩⟩ := by
  execute 4

private theorem D_leaf_0101 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      (tL <{{D}} ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rD)) := by
  execute 4

private theorem D_leaf_011 (tL rD : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> tL, (1 : Fin 2) >> rD⟩⟩ := by
  execute 5

private theorem D_leaf_11 (tL rD : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> (1 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
      (((1 : Fin 2) >> tL) <{{F}} ((1 : Fin 2) >> rD)) := by
  execute 1

private theorem D_step_one (c : ℕ) (hc : c < 4) (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_D c L R) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone ∨
       (∃ L'' R_P, R_P ≠ [] ∧ cfg' = P_cfg L'' [] R_P) ∨
       (∃ c' L' R', c' < 4 ∧ L'.length < L.length ∧ cfg' = cfg_D c' L' R')) := by
  unfold cfg_D
  set rD := (([0] : List (Fin 2)) ^ (1 + c)) +> ((1 : Fin 2) >> encTail R)
  have hrD_right : (1 : Fin 2) >> rD = encRight ((0, c) :: tailAsRight R) := RD_eq_encRight c hc R
  have hrD_tail : (1 : Fin 2) >> rD = encTail ((1, c) :: tailAsRight R) := RD_eq_encTail_one c hc R
  have hrD_one : (1 : Fin 2) >> rD = (1 : Fin 2) >> encTail ((0, c) :: tailAsRight R) :=
    one_cons_RD_eq c hc R
  have hrD_two : (1 : Fin 2) >> (1 : Fin 2) >> rD = encTail ((2, c) :: tailAsRight R) :=
    RD_eq_encTail_two c hc R
  have hrD_peel : rD = (0 : Fin 2) >> encTail (peelSep c (tailAsRight R)) :=
    rD_eq_zero_cons_peelSep c hc R
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
        refine ⟨cfg_M0 [] ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, [], (1,
          c) :: tailAsRight R, rfl⟩⟩
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
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₃,
                      b₃) :: L''') := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h20,
                    encRight_cons_eq_one_cons_encTail]
                  rfl
                rw [hL]
                refine ⟨cfg_D 2 ((a₃, b₃) :: L''') ((0, c) :: tailAsRight R), ?_,
                  Or.inr (Or.inr (Or.inr ⟨2, (a₃, b₃) :: L''', (0, c) :: tailAsRight R,
                    by decide, by simp, rfl⟩))⟩
                unfold cfg_D
                dsimp only [pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
                  listblank_append_cons, listblank_append_nil]
                rw [← hrD_one]
                exact D_leaf_0101 (encTail ((a₃, b₃) :: L''')) rD
              · -- b₂ % 4 = 1 -> cfg_M0 ((0, 0) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) ::
                -- tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight ((a₃,
                      b₃) :: L''') := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h21]
                  rfl
                rw [hL]
                refine ⟨cfg_M0 ((0, 0) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R),
                  ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 0 ((a₃, b₃) :: L'''), encTail_zero 0 ((0,
                  c) :: tailAsRight R)]
                simpa [hrD_right] using D_leaf_0100 (encRight ((a₃, b₃) :: L''')) rD
              · -- b₂ % 4 = 2 -> cfg_M0 ((0, 1) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) ::
                -- tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >>
                      encRight ((a₃, b₃) :: L''')) := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h22]
                  rfl
                rw [hL]
                refine ⟨cfg_M0 ((0, 1) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R),
                  ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 1 ((a₃, b₃) :: L'''), encTail_zero 0 ((0,
                  c) :: tailAsRight R)]
                simpa [hrD_right] using D_leaf_0100 ((0 : Fin 2) >> encRight ((a₃, b₃) :: L''')) rD
              · -- b₂ % 4 = 3 -> cfg_M0 ((0, 2) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) ::
                -- tailAsRight R)
                have hL : encTail ((0, b₁) :: (0, b₂) :: (a₃, b₃) :: L''') =
                    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >>
                      (0 : Fin 2) >> encRight ((a₃, b₃) :: L''')) := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_zero, h23]
                  rfl
                rw [hL]
                refine ⟨cfg_M0 ((0, 2) :: (a₃, b₃) :: L''') ((0, 0) :: (0, c) :: tailAsRight R),
                  ?_, Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 2 ((a₃, b₃) :: L'''), encTail_zero 0 ((0,
                  c) :: tailAsRight R)]
                simpa [hrD_right] using D_leaf_0100 ((0 : Fin 2) >> (0 : Fin 2) >>
                  encRight ((a₃, b₃) :: L''')) rD
          · -- a₂ = 1
            rcases mod4_cases b₂ with h20 | h21 | h22 | h23
            · -- b₂ % 4 = 0 -> pushZeroSep 1 L''
              have hL : encTail ((0, b₁) :: (1, b₂) :: L'') =
                  (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> encRight L'') := by
                rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ,
                  encTail_zero, h20]
                rfl
              rw [hL]
              refine ⟨cfg_M0 (pushZeroSep 1 L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _,
                _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_pushZeroSep 1 (by decide) L'', ← hrD_tail]
              simpa using D_leaf_011 ((0 : Fin 2) >> encRight L'') rD
            · -- b₂ % 4 = 1 -> pushZeroSep 2 L''
              have hL : encTail ((0, b₁) :: (1, b₂) :: L'') =
                  (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (0 : Fin 2) >>
                    encRight L'') := by
                rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ,
                  encTail_zero, h21]
                rfl
              rw [hL]
              refine ⟨cfg_M0 (pushZeroSep 2 L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _,
                _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_pushZeroSep 2 (by decide) L'', ← hrD_tail]
              simpa using D_leaf_011 ((0 : Fin 2) >> (0 : Fin 2) >> encRight L'') rD
            · -- b₂ % 4 = 2 -> pushZeroSep 3 L''
              have hL : encTail ((0, b₁) :: (1, b₂) :: L'') =
                  (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (0 : Fin 2) >>
                    (0 : Fin 2) >> encRight L'') := by
                rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ,
                  encTail_zero, h22]
                rfl
              rw [hL]
              refine ⟨cfg_M0 (pushZeroSep 3 L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _,
                _, rfl⟩⟩
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
                      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                        encTail ((a₃, b₃) :: L''')) := by
                  rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ,
                    encTail_zero, h23, encRight_cons_eq_one_cons_encTail]
                  rfl
                rw [hL]
                refine ⟨P_cfg ((a₃, b₃) :: L''') [] ((0, c) :: tailAsRight R), ?_,
                  Or.inr (Or.inr (Or.inl ⟨(a₃, b₃) :: L''', (0, c) :: tailAsRight R, by simp,
                    rfl⟩))⟩
                unfold P_cfg wall
                rw [listblank_append_nil, ← hrD_right]
                exact D_leaf_011 _ rD
          · -- a₂ = a₂' + 2 -> cfg_M0 ((0, 0) :: (a₂', b₂) :: L'') ((1, c) :: tailAsRight R)
            have hL : encTail ((0, b₁) :: (a₂' + 2, b₂) :: L'') =
                (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((1 : Fin 2) >> encTail ((a₂',
                  b₂) :: L'')) := by
              rw [encTail_zero, hb0, encRight_cons_eq_one_cons_encTail, encTail_succ (a₂' + 1),
                encTail_succ a₂']
              rfl
            rw [hL]
            refine ⟨cfg_M0 ((0, 0) :: (a₂', b₂) :: L'') ((1, c) :: tailAsRight R), ?_,
              Or.inl ⟨.M0, _, _, rfl⟩⟩
            rw [cfg_M0_eq, encTail_zero 0 ((a₂', b₂) :: L''), encRight_cons_eq_one_cons_encTail,
              ← hrD_tail]
            simpa using D_leaf_011 ((1 : Fin 2) >> encTail ((a₂', b₂) :: L'')) rD
        · -- b₁ % 4 = 1 -> Leaf 00, L' = (a₂ + 1, b₂) :: L''
          have hL : encTail ((0, b₁) :: (a₂, b₂) :: L'') =
              (0 : Fin 2) >> (0 : Fin 2) >> encTail ((a₂ + 1, b₂) :: L'') := by
            rw [encTail_zero, hb1, encTail_succ, encRight_cons_eq_one_cons_encTail]
            rfl
          rw [hL]
          refine ⟨cfg_M0 ((a₂ + 1, b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, _, _,
            rfl⟩⟩
          rw [cfg_M0_eq, ← hrD_tail]
          exact D_leaf_00 _ rD
        · -- b₁ % 4 = 2 -> Leaf 00, L' = (0, 0) :: (a₂, b₂) :: L''
          have hL : encTail ((0, b₁) :: (a₂, b₂) :: L'') =
              (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, 0) :: (a₂, b₂) :: L'') := by
            rw [encTail_zero, hb2, encTail_zero]
            rfl
          rw [hL]
          refine ⟨cfg_M0 ((0, 0) :: (a₂, b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0,
            _, _, rfl⟩⟩
          rw [cfg_M0_eq, ← hrD_tail]
          exact D_leaf_00 _ rD
        · -- b₁ % 4 = 3 -> Leaf 00, L' = (0, 1) :: (a₂, b₂) :: L''
          have hL : encTail ((0, b₁) :: (a₂, b₂) :: L'') =
              (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, 1) :: (a₂, b₂) :: L'') := by
            rw [encTail_zero, hb3, encTail_zero]
            rfl
          rw [hL]
          refine ⟨cfg_M0 ((0, 1) :: (a₂, b₂) :: L'') ((1, c) :: tailAsRight R), ?_, Or.inl ⟨.M0,
            _, _, rfl⟩⟩
          rw [cfg_M0_eq, ← hrD_tail]
          exact D_leaf_00 _ rD
    · -- a₁ = 1 (F0 = 1LE -> 4-step and 7-step leaves!)
      have h1000 : ∀ (tL : ListBlank (Fin 2)),
          (((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> tL) <{{D}} rD) [target_tm]⊢⁺
            ⟨some A, ⟨0, (0 : Fin 2) >> tL, (1 : Fin 2) >> (1 : Fin 2) >> rD⟩⟩ := by
        intro tL; execute 4
      rcases L' with _ | ⟨⟨a₂, b₂⟩, L''⟩
      · have hL : encTail [(1,
          b₁)] = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default := by
          simp [encTail_succ, encTail_zero]
        rw [hL]
        refine ⟨cfg_M0 [] ((2, c) :: tailAsRight R), ?_, Or.inl ⟨.M0, [], _, rfl⟩⟩
        rw [cfg_M0_eq, encTail_nil, ← hrD_two]
        simpa using h1000 default
      · rcases mod4_cases b₁ with hb0 | hb1 | hb2 | hb3
        · have hL : encTail ((1, b₁) :: (a₂, b₂) :: L'') =
              (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₂, b₂) :: L'') := by
            rw [encTail_succ, encTail_zero, hb0, encRight_cons_eq_one_cons_encTail]; rfl
          rw [hL]
          have h7 : (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₂,
            b₂) :: L'')) <{{D}} rD) [target_tm]⊢⁺
              ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail ((a₂, b₂) :: L''),
                encTail (peelSep c (tailAsRight R))⟩⟩ := by
            rw [hrD_peel]
            execute 7
          rcases a₂ with _ | a₂'
          · rcases L'' with _ | ⟨⟨a₃, b₃⟩, L'''⟩
            · refine ⟨cfg_M0 [] (peelSep c (tailAsRight R)), ?_, Or.inl ⟨.M0, [], _, rfl⟩⟩
              rw [cfg_M0_eq, encTail_nil]
              have h0 : (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail [(0,
                b₂)] = default := by
                simp [encTail_zero]
              rw [← h0]
              exact h7
            · rcases mod4_cases b₂ with h20 | h21 | h22 | h23
              · refine ⟨cfg_M0 ((0, 3) :: (a₃, b₃) :: L''') (peelSep c (tailAsRight R)), ?_,
                  Or.inl ⟨.M0, _, _, rfl⟩⟩
                rw [cfg_M0_eq, encTail_zero 3 ((a₃, b₃) :: L''')]
                have h0 : (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, b₂) :: (a₃,
                  b₃) :: L''') =
                    (([0] : List (Fin 2)) ^ (1 + 3 % 4)) +> encRight ((a₃, b₃) :: L''') := by
                  rw [encTail_zero, h20]; rfl
                rw [← h0]
                exact h7
              · have h0 : (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, b₂) :: (a₃,
                  b₃) :: L''') =
                    (([0] : List (Fin 2)) ^ 0) +> wall ((a₃, b₃) :: L''') := by
                  rw [encTail_zero, h21, encRight_cons_eq_one_cons_encTail]; rfl
                rw [h0] at h7
                obtain ⟨cfg', hstep, hout⟩ :=
                  A_wall_peelSep_closed ((a₃, b₃) :: L''') 0 c (tailAsRight R) h7
                rcases hout with hM | hH
                · exact ⟨cfg', hstep, Or.inl hM⟩
                · exact ⟨cfg', hstep, Or.inr (Or.inl hH)⟩
              · have h0 : (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, b₂) :: (a₃,
                  b₃) :: L''') =
                    (([0] : List (Fin 2)) ^ 1) +> wall ((a₃, b₃) :: L''') := by
                  rw [encTail_zero, h22, encRight_cons_eq_one_cons_encTail]; rfl
                rw [h0] at h7
                obtain ⟨cfg', hstep, hout⟩ :=
                  A_wall_peelSep_closed ((a₃, b₃) :: L''') 1 c (tailAsRight R) h7
                rcases hout with hM | hH
                · exact ⟨cfg', hstep, Or.inl hM⟩
                · exact ⟨cfg', hstep, Or.inr (Or.inl hH)⟩
              · have h0 : (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail ((0, b₂) :: (a₃,
                  b₃) :: L''') =
                    (([0] : List (Fin 2)) ^ 2) +> wall ((a₃, b₃) :: L''') := by
                  rw [encTail_zero, h23, encRight_cons_eq_one_cons_encTail]; rfl
                rw [h0] at h7
                obtain ⟨cfg', hstep, hout⟩ :=
                  A_wall_peelSep_closed ((a₃, b₃) :: L''') 2 c (tailAsRight R) h7
                rcases hout with hM | hH
                · exact ⟨cfg', hstep, Or.inl hM⟩
                · exact ⟨cfg', hstep, Or.inr (Or.inl hH)⟩
          · refine ⟨cfg_M0 ((0, 2) :: (a₂', b₂) :: L'') (peelSep c (tailAsRight R)), ?_,
              Or.inl ⟨.M0, _, _, rfl⟩⟩
            rw [cfg_M0_eq, encTail_zero 2 ((a₂', b₂) :: L'')]
            have h0 : (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encTail ((a₂' + 1, b₂) :: L'') =
                (([0] : List (Fin 2)) ^ (1 + 2 % 4)) +> encRight ((a₂', b₂) :: L'') := by
              rw [encTail_succ, encRight_cons_eq_one_cons_encTail]; rfl
            rw [← h0]
            exact h7
        · have hL : encTail ((1, b₁) :: (a₂, b₂) :: L'') =
              (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₂,
                b₂) :: L'') := by
            rw [encTail_succ, encTail_zero, hb1, encRight_cons_eq_one_cons_encTail]; rfl
          rw [hL]
          refine ⟨cfg_D 1 ((a₂, b₂) :: L'') ((1, c) :: tailAsRight R), ?_,
            Or.inr (Or.inr (Or.inr ⟨1, (a₂, b₂) :: L'', (1, c) :: tailAsRight R, by decide,
              by simp, rfl⟩))⟩
          unfold cfg_D
          dsimp only [pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
            listblank_append_cons, listblank_append_nil]
          rw [← hrD_tail]
          execute 4
        · have hL : encTail ((1, b₁) :: (a₂, b₂) :: L'') =
              (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                encTail ((a₂, b₂) :: L'') := by
            rw [encTail_succ, encTail_zero, hb2, encRight_cons_eq_one_cons_encTail]; rfl
          rw [hL]
          refine ⟨cfg_M0 ((0, 0) :: (a₂, b₂) :: L'') ((2, c) :: tailAsRight R), ?_, Or.inl ⟨.M0,
            _, _, rfl⟩⟩
          rw [cfg_M0_eq, encTail_zero 0 ((a₂, b₂) :: L''), encRight_cons_eq_one_cons_encTail,
            ← hrD_two]
          simpa using h1000 ((1 : Fin 2) >> encTail ((a₂, b₂) :: L''))
        · have hL : encTail ((1, b₁) :: (a₂, b₂) :: L'') =
              (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                (1 : Fin 2) >> encTail ((a₂, b₂) :: L'') := by
            rw [encTail_succ, encTail_zero, hb3, encRight_cons_eq_one_cons_encTail]; rfl
          rw [hL]
          refine ⟨cfg_M0 ((0, 1) :: (a₂, b₂) :: L'') ((2, c) :: tailAsRight R), ?_, Or.inl ⟨.M0,
            _, _, rfl⟩⟩
          rw [cfg_M0_eq, encTail_zero 1 ((a₂, b₂) :: L''), encRight_cons_eq_one_cons_encTail,
            ← hrD_two]
          simpa using h1000 ((0 : Fin 2) >> (1 : Fin 2) >> encTail ((a₂, b₂) :: L''))
    · -- a₁ = a₁' + 2 -> Leaf 11 -> Halts in 1 step!
      have hL : encTail ((a₁' + 2, b₁) :: L') =
          (1 : Fin 2) >> (1 : Fin 2) >> encTail ((a₁', b₁) :: L') := by
        rw [encTail_succ (a₁' + 1), encTail_succ a₁']
      rw [hL]
      refine ⟨((1 : Fin 2) >> encTail ((a₁', b₁) :: L')) <{{F}} ((1 : Fin 2) >> rD),
        D_leaf_11 _ rD, Or.inr (Or.inl (F_halt_on_one _ _))⟩

private theorem stage2_closed (n : ℕ) :
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

-- ============================================================================


private theorem stage1_step_all (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_M0 L R) [target_tm]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone ∨ ∃ L' R', cfg' = cfg_D 0 L' R') := by
  rcases R with _ | ⟨⟨d, bR⟩, R'⟩
  · exact ⟨_, M0_nil L, Or.inr (Or.inr ⟨L, [], rfl⟩)⟩
  · rcases d with _ | _ | _ | _ | _ | k
    · exact ⟨_, M0_zero L bR R', Or.inr (Or.inr ⟨L, peelSep bR R', rfl⟩)⟩
    · exact ⟨_, M0_one L bR R', Or.inl ⟨.M0, (0, 0) :: tailAsRight L, peelSep bR R', rfl⟩⟩
    · exact ⟨_, M0_two L bR R', Or.inl ⟨.M0, (0, 1) :: tailAsRight L, peelSep bR R', rfl⟩⟩
    · exact ⟨_, M0_three L bR R', Or.inl ⟨.M0, (0, 2) :: tailAsRight L, peelSep bR R', rfl⟩⟩
    · exact ⟨_, M0_four L bR R', Or.inl ⟨.M0, (0, 3) :: tailAsRight L, peelSep bR R', rfl⟩⟩
    · obtain ⟨cfg', h, hout⟩ := M0_add5_closed L k bR R'
      rcases hout with hM | hH
      · exact ⟨cfg', h, Or.inl hM⟩
      · exact ⟨cfg', h, Or.inr (Or.inl hH)⟩

private theorem stack_system_closed :
    ∀ cfg, IsInStackSystem cfg →
      ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧
              (IsInStackSystem cfg' ∨ (step target_tm cfg').isNone) := by
  intro cfg ⟨m, L, R, hcfg⟩
  subst hcfg
  cases m with
  | M0 =>
    obtain ⟨cfg₁, h₁, hout₁⟩ := stage1_step_all L R
    rcases hout₁ with hM₁ | hH₁ | ⟨L₁, R₁, rfl⟩
    · exact ⟨cfg₁, h₁, Or.inl hM₁⟩
    · exact ⟨cfg₁, h₁, Or.inr hH₁⟩
    · obtain ⟨cfg₂, h₂, hout₂⟩ := stage2_closed L₁.length L₁ (Nat.le_refl _) 0 (by decide) R₁
      rcases hout₂ with hM₂ | hH₂ | ⟨L'', R_P, hRP, rfl⟩
      · exact ⟨cfg₂, stepPlus_trans h₁ h₂, Or.inl hM₂⟩
      · exact ⟨cfg₂, stepPlus_trans h₁ h₂, Or.inr hH₂⟩
      · obtain ⟨cfg₃, h₃, hout₃⟩ := stage3_closed L'' R_P hRP
        exact ⟨cfg₃, stepPlus_trans (stepPlus_trans h₁ h₂) h₃, hout₃⟩


theorem is_stack_cryptid : IsStackCryptid target := by
  rw [target_eq_target_tm]
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

end BusyBeaver.M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LEHHH

