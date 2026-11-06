/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC

end

namespace BusyBeaver.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5


@[simp] theorem multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 =
    some config := rfl
@[simp] theorem multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 =
    step M config := rfl
@[simp] theorem multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] theorem pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] theorem cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++
    ys) := rfl
@[simp] theorem append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] theorem listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] theorem listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x
    :: xs) +> b = x >> (xs +> b) := rfl
@[simp] theorem zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] theorem default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

theorem list_pow_append_one (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := list_pow_add_comm u k 1
  dsimp [HPow.hPow] at h ⊢
  rw [List.append_nil] at h
  exact h

theorem pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

theorem pow_succ_append_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

theorem pow_succ_append_right' (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [listblank_append_append, list_pow_append_one]

theorem pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

theorem multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

theorem multiStep_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

theorem stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

theorem stepPlus_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, _, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

theorem stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

theorem stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

theorem stepStar_stepPlus_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

theorem step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [BusyBeaver.Cfg.headRight,
        BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
        Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default,
        default_head, default_tail])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
      (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
      (any_goals (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

-- ============================================================================
-- Section 1: ListBlank Power Conversion Lemmas
-- ============================================================================

theorem cons_0_pow_10 (k : Nat) (r : ListBlank (Fin 2)) :
    [0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r) = (([0, 1] : List (Fin 2)) ^ k) +> ([0] +> r) := by
  induction k generalizing r with
  | zero => simp only [pow_zero_list, listblank_append_nil]
  | succ k ih =>
    rw [pow_succ_append_right, pow_succ_append_right, ← ih]
    rfl

theorem cons_1_pow_01 (k : Nat) (r : ListBlank (Fin 2)) :
    [1] +> ((([0, 1] : List (Fin 2)) ^ k) +> r) = (([1, 0] : List (Fin 2)) ^ k) +> ([1] +> r) := by
  induction k generalizing r with
  | zero => simp only [pow_zero_list, listblank_append_nil]
  | succ k ih =>
    rw [pow_succ_append_right, pow_succ_append_right, ← ih]
    rfl

theorem append_0_pow_01 (X : ListBlank (Fin 2)) (k : Nat) :
    (X <+ [0]) <+ (([0, 1] : List (Fin 2)) ^ k) = (X <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [0] :=
  (cons_0_pow_10 k X).symm

theorem append_1_pow_01 (X : ListBlank (Fin 2)) (k : Nat) :
    (X <+ (([0, 1] : List (Fin 2)) ^ k)) <+ [1] = (X <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ k) :=
  cons_1_pow_01 k X

theorem append_1_1 (X : ListBlank (Fin 2)) : (X <+ [1]) <+ [1] = X <+ [1, 1] := rfl

theorem append_11_1 (X : ListBlank (Fin 2)) : (X <+ [1, 1]) <+ [1] = X <+ [1, 1, 1] := rfl

theorem mul_pow2_ge (c k : Nat) : c ≤ c * (2 ^ k) :=
  Nat.le_mul_of_pos_right c (Nat.one_le_pow k 2 (by decide))

theorem cons_1_pow_11 (k : Nat) (r : ListBlank (Fin 2)) :
    [1] +> ((([1, 1] : List (Fin 2)) ^ k) +> r) = (([1, 1] : List (Fin 2)) ^ k) +> ([1] +> r) := by
  induction k generalizing r with
  | zero => simp only [pow_zero_list, listblank_append_nil]
  | succ k ih =>
    rw [pow_succ_append_right, pow_succ_append_right, ← ih]
    rfl

theorem pow_11_even (k : Nat) (r : ListBlank (Fin 2)) :
    (([1, 1] : List (Fin 2)) ^ (2 * k)) +> r = (([1, 1, 1, 1] : List (Fin 2)) ^ k) +> r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + (2 * k) := by omega
    rw [h2, pow_add_append_right, ih, pow_succ_append_right]
    rfl

-- ============================================================================
-- Section 2: Core Shift Lemmas
-- ============================================================================

theorem shift_E_right_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((l <+ (([0, 1] : List (Fin 2)) ^ k)) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{E}}> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> r)))
        [target_tm]⊢*
        ((l <+ [0, 1]) {{E}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by
      dsimp [ListBlank.append]; (iterate 2 step); finish
    have h2 := ih (l <+ [0, 1]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

theorem shift_B_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{B}} r) [target_tm]⊢*
    (l <{{B}} ((([1, 1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [1, 0]) <{{B}} r)
        [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{B}} ([1, 1] +> r)) := by
      dsimp [ListBlank.append]; (iterate 2 step); finish
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

theorem shift_E_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{E}} r) [target_tm]⊢*
    (l <{{E}} ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [1, 0]) <{{E}} r)
        [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{E}} ([1, 0] +> r)) := by
      dsimp [ListBlank.append]; (iterate 4 step); finish
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

-- ============================================================================
-- Section 3: Bounce Lemmas & Rule 1
-- ============================================================================

abbrev r0 : ListBlank (Fin 2) := [0, 1, 0, 1, 1, 0, 1] +> default

theorem bounce_E_01 (l : ListBlank (Fin 2)) (d : Nat) (r : ListBlank (Fin 2)) :
    ((l <+ [0, 1]) {{E}}> ((([0, 1] : List (Fin 2)) ^ d) +> ([1] +> r)))
    [target_tm]⊢⁺
    ((l <+ [1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 1)) +> r)) := by
  have h1 := shift_E_right_01 d (l <+ [0, 1]) ([1] +> r)
  have heq : (l <+ [0, 1]) <+ (([0, 1] : List (Fin 2)) ^ d) =
      ((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <+ [0] :=
    append_0_pow_01 (l <+ [1]) d
  rw [heq] at h1
  have h2 : ((((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <+ [0]) {{E}}> ([1] +> r))
      [target_tm]⊢⁺
      (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <{{E}} ([1, 0] +> r)) := by
    dsimp [ListBlank.append]; (iterate 4 step); finish
  have h3 := shift_E_left_10 d (l <+ [1]) ([1, 0] +> r)
  rw [pow_succ_append_right'] at h3
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

theorem bounce_E_end (l : ListBlank (Fin 2)) (d : Nat) :
    ((l <+ [0, 1]) {{E}}> ((([0, 1] : List (Fin 2)) ^ d) +> ([0, 0, 1] +> default)))
    [target_tm]⊢⁺
    ((l <+ [1]) <{{B}} ((([1, 1] : List (Fin 2)) ^ d) +> r0)) := by
  have h1 := shift_E_right_01 d (l <+ [0, 1]) ([0, 0, 1] +> default)
  have heq : (l <+ [0, 1]) <+ (([0, 1] : List (Fin 2)) ^ d) =
      ((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <+ [0] :=
    append_0_pow_01 (l <+ [1]) d
  rw [heq] at h1
  have h2 : ((((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <+ [0]) {{E}}> ([0, 0, 1] +> default))
      [target_tm]⊢⁺
      (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <{{B}} r0) := by
    dsimp [r0, ListBlank.append]; (iterate 24 step); finish
  have h3 := shift_B_left_10 d (l <+ [1]) r0
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

theorem rule1_step (a : Nat) (r : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 1)) +> ([1, 1] +> r)))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 3)) +> r)) := by
  rw [pow_succ_append_right]
  have h1 : (default <{{E}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ a) +> ([1, 1] +> r))))
      [target_tm]⊢⁺
      ((default <+ [0, 1]) {{E}}> ([0] +> ((([1, 0] : List (Fin 2)) ^ a) +> ([1, 1] +> r)))) := by
    dsimp [ListBlank.append]; (iterate 2 step); finish
  rw [cons_0_pow_10] at h1
  have heq : ([0] : List (Fin 2)) +> ([1, 1] +> r) = [0, 1] +> ([1] +> r) := rfl
  rw [heq, pow_succ_append_right'] at h1
  have h2 := bounce_E_01 default (a + 1) r
  have h3 : ((default <+ [1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> r))
      [target_tm]⊢⁺
      (default <{{E}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> r))) := by
    dsimp [ListBlank.append]; (iterate 4 step); finish
  rw [← pow_succ_append_right] at h3
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

theorem rule1_loop (k a : Nat) (r : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 1)) +> ((([1, 1] : List (Fin 2)) ^ k) +> r)))
    [target_tm]⊢*
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2 * k + 1)) +> r)) := by
  induction k generalizing a with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 := rule1_step a ((([1, 1] : List (Fin 2)) ^ k) +> r)
    have h2 := ih (a + 2)
    have heq : a + 2 + 2 * k + 1 = a + 2 * (k + 1) + 1 := by omega
    rw [heq] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

theorem finish_B_left (m : Nat) (r : ListBlank (Fin 2)) :
    (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ m)) <{{B}} r)
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * m + 2)) +> r)) := by
  have h1 := shift_B_left_10 m (default <+ [1]) r
  have h2 : ((default <+ [1]) <{{B}} ((([1, 1] : List (Fin 2)) ^ m) +> r))
      [target_tm]⊢⁺
      (default <{{E}} ((([1, 0] : List (Fin 2)) ^ 2) +> ((([1, 1] : List (Fin 2)) ^ m) +> r))) := by
    dsimp [ListBlank.append]; (iterate 12 step); finish
  have h3 := rule1_loop m 1 r
  have heq : 1 + 2 * m + 1 = 2 * m + 2 := by omega
  rw [heq] at h3
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

-- ============================================================================
-- Section 4: Initial Sweep & Local Half-Steps
-- ============================================================================

theorem sweep_mid (a b : Nat) (r' : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0,
        1] : List (Fin 2)) ^ (b + 1)) +> r')))
    [target_tm]⊢⁺
    ((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 0, 1]) <+ [0, 1]) {{E}}>
      ((([0, 1] : List (Fin 2)) ^ b) +> r')) := by
  rw [pow_succ_append_right]
  have h1 : (default <{{E}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ (a + 1)) +> ((([0,
      1] : List (Fin 2)) ^ (b + 1)) +> r'))))
      [target_tm]⊢⁺
      ((default <+ [0, 1]) {{E}}> ([0] +> ((([1, 0] : List (Fin 2)) ^ (a + 1)) +> ((([0,
          1] : List (Fin 2)) ^ (b + 1)) +> r')))) := by
    dsimp [ListBlank.append]; (iterate 2 step); finish
  rw [cons_0_pow_10] at h1
  have h2 :=
      shift_E_right_01 (a + 1) (default <+ [0, 1]) ([0] +> ((([0,
      1] : List (Fin 2)) ^ (b + 1)) +> r'))
  have heq1 : (default <+ [0, 1]) <+ (([0, 1] : List (Fin 2)) ^ (a + 1)) =
      (default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1] := by
    rw [pow_succ_append_right', ← pow_succ_append_right]
  rw [heq1, pow_succ_append_right] at h2
  have h3 : (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1]) {{E}}>
        ([0] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ b) +> r'))))
      [target_tm]⊢⁺
      ((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 0, 1]) <+ [0, 1]) {{E}}>
        ((([0, 1] : List (Fin 2)) ^ b) +> r')) := by
    dsimp [ListBlank.append]; (iterate 7 step); finish
  exact stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2) h3

theorem sweep_init (a b : Nat) (r : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0,
        1] : List (Fin 2)) ^ (b + 1)) +> ([1] +> r))))
    [target_tm]⊢⁺
    (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1]) <{{E}} ((([1,
        0] : List (Fin 2)) ^ (b + 2)) +> r)) := by
  have h1 := sweep_mid a b ([1] +> r)
  have h2 := bounce_E_01 ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 0, 1]) b r
  have h3 : ((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 0, 1]) <+ [1]) <{{E}}
        ((([1, 0] : List (Fin 2)) ^ (b + 1)) +> r))
      [target_tm]⊢⁺
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1]) <{{E}}
        ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ (b + 1)) +> r))) := by
    dsimp [ListBlank.append]; (iterate 4 step); finish
  rw [← pow_succ_append_right] at h3
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

theorem step14_E111 (l s : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) <{{E}} s)
    [target_tm]⊢⁺
    (((l <+ [0, 0, 1, 1]) <+ [0, 1]) {{E}}> ([0] +> s)) := by
  dsimp [ListBlank.append]; (iterate 14 step); finish

theorem half_E1_a (l : ListBlank (Fin 2)) (d : Nat) (r : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) <{{E}} ((([1,
        0] : List (Fin 2)) ^ d) +> ([1, 1] +> r)))
    [target_tm]⊢⁺
    ((l <+ [0, 1, 1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 3)) +> r)) := by
  have h1 := step14_E111 l ((([1, 0] : List (Fin 2)) ^ d) +> ([1, 1] +> r))
  rw [cons_0_pow_10] at h1
  have heq : ([0] : List (Fin 2)) +> ([1, 1] +> r) = [0, 1] +> ([1] +> r) := rfl
  rw [heq, pow_succ_append_right'] at h1
  have h2 := bounce_E_01 (l <+ [0, 0, 1, 1]) (d + 1) r
  have h3 : (((l <+ [0, 0, 1, 1]) <+ [1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 2)) +> r))
      [target_tm]⊢⁺
      ((l <+ [0, 1, 1]) <{{E}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ (d + 2)) +> r))) := by
    dsimp [ListBlank.append]; (iterate 4 step); finish
  rw [← pow_succ_append_right] at h3
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

theorem half_E1_b (l : ListBlank (Fin 2)) (d : Nat) (r : ListBlank (Fin 2)) :
    ((l <+ [0]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 1)) +> ([1, 1] +> r)))
    [target_tm]⊢⁺
    ((l <+ [1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 2)) +> r)) := by
  rw [pow_succ_append_right]
  have h1 : ((l <+ [0]) <{{E}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ d) +> ([1, 1] +> r))))
      [target_tm]⊢⁺
      ((l <+ [0, 1]) {{E}}> ([0] +> ((([1, 0] : List (Fin 2)) ^ d) +> ([1, 1] +> r)))) := by
    dsimp [ListBlank.append]; (iterate 2 step); finish
  rw [cons_0_pow_10] at h1
  have heq : ([0] : List (Fin 2)) +> ([1, 1] +> r) = [0, 1] +> ([1] +> r) := rfl
  rw [heq, pow_succ_append_right'] at h1
  have h2 := bounce_E_01 l (d + 1) r
  exact stepPlus_trans h1 h2

theorem loop_E1_step (l : ListBlank (Fin 2)) (d : Nat) (r : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) <{{E}} ((([1,
        0] : List (Fin 2)) ^ d) +> ([1, 1, 1, 1] +> r)))
    [target_tm]⊢⁺
    ((l <+ [1, 1, 1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 4)) +> r)) := by
  have heq_r : ([1, 1, 1, 1] : List (Fin 2)) +> r = [1, 1] +> ([1, 1] +> r) := rfl
  rw [heq_r]
  have h1 := half_E1_a l d ([1, 1] +> r)
  have heq_l : (l <+ [0, 1, 1]) = ((l <+ [1, 1]) <+ [0]) := rfl
  rw [heq_l] at h1
  have h2 := half_E1_b (l <+ [1, 1]) (d + 2) r
  exact stepPlus_trans h1 h2

theorem loop_E1_iter (k : Nat) (l : ListBlank (Fin 2)) (d : Nat) (r : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ (2 * k))) <+ [1, 1, 1]) <{{E}}
      ((([1, 0] : List (Fin 2)) ^ d) +> ((([1, 1, 1, 1] : List (Fin 2)) ^ k) +> r)))
    [target_tm]⊢*
    ((l <+ [1, 1, 1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ (d + 4 * k)) +> r)) := by
  induction k generalizing l d with
  | zero =>
    simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2k, pow_add_append_left, pow_succ_append_right]
    have h1 :=
        loop_E1_step (l <+ (([0, 1] : List (Fin 2)) ^ (2 * k))) d ((([1, 1, 1,
        1] : List (Fin 2)) ^ k) +> r)
    have h2 := ih l (d + 4)
    have hd : d + 4 + 4 * k = d + 4 * (k + 1) := by omega
    rw [hd] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

-- ============================================================================
-- Section 5: Rule 2 & c = 2 Transitions
-- ============================================================================

theorem rule2_gen (a b m : Nat) (r : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0, 1] : List (Fin 2)) ^ (b + 1)) +>
      ([1] +> ((([1, 0] : List (Fin 2)) ^ m) +> ([1, 1] +> r))))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * a + 4)) +> ((([0,
        1] : List (Fin 2)) ^ (b + m + 3)) +> ([0] +> r)))) := by
  have h1 := sweep_init a b ((([1, 0] : List (Fin 2)) ^ m) +> ([1, 1] +> r))
  rw [← pow_add_append_right] at h1
  have heq_bm : b + 2 + m = (b + m + 1) + 1 := by omega
  rw [heq_bm] at h1
  have heq_l : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [1]) <+ [0]) := rfl
  rw [heq_l] at h1
  have h2 := half_E1_b ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [1]) (b + m + 1) r
  have heq_bm2 : b + m + 1 + 2 = b + m + 3 := by omega
  rw [heq_bm2] at h2
  have h3 : ((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [1]) <+ [1]) <{{E}}
        ((([1, 0] : List (Fin 2)) ^ (b + m + 3)) +> r))
      [target_tm]⊢⁺
      (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (a + 1))) <{{B}}
        ((([0, 1] : List (Fin 2)) ^ (b + m + 3)) +> ([0] +> r))) := by
    rw [← cons_0_pow_10, ← append_1_pow_01]
    dsimp [ListBlank.append]; (iterate 1 step); finish
  have h4 := finish_B_left (a + 1) ((([0, 1] : List (Fin 2)) ^ (b + m + 3)) +> ([0] +> r))
  have ha : 2 * (a + 1) + 2 = 2 * a + 4 := by omega
  rw [ha] at h4
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 h4))

theorem rule2_step (a b : Nat) (r : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0, 1] : List (Fin 2)) ^ (b + 1)) +>
      ([1, 1, 1, 1] +> r))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * a + 4)) +> ((([0,
        1] : List (Fin 2)) ^ (b + 4)) +> r))) := by
  have h1 := rule2_gen a b 0 ([1] +> r)
  simp only [pow_zero_list, listblank_append_nil, Nat.add_zero] at h1
  have heq1 : ([1] : List (Fin 2)) +> ([1, 1] +> ([1] +> r)) = [1, 1, 1, 1] +> r := rfl
  have heq2 : ([0] : List (Fin 2)) +> ([1] +> r) = [0, 1] +> r := rfl
  rw [heq1, heq2, pow_succ_append_right'] at h1
  exact h1

theorem rule2_loop (k a b : Nat) (r : ListBlank (Fin 2)) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0, 1] : List (Fin 2)) ^ (b + 1)) +>
      ((([1, 1, 1, 1] : List (Fin 2)) ^ k) +> r))))
    [target_tm]⊢*
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ ((a + 2) * (2 ^ k))) +>
      ((([0, 1] : List (Fin 2)) ^ (b + 3 * k + 1)) +> r))) := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil, Nat.pow_zero, Nat.mul_one, Nat.mul_zero,
        Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 := rule2_step a b ((([1, 1, 1, 1] : List (Fin 2)) ^ k) +> r)
    have h2 := ih (2 * a + 2) (b + 3)
    have ha : (2 * a + 2 + 2) * (2 ^ k) = (a + 2) * (2 ^ (k + 1)) := by
      have : 2 * a + 2 + 2 = (a + 2) * 2 := by omega
      rw [this, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k), ← Nat.pow_succ]
    have hb : b + 3 + 3 * k + 1 = b + 3 * (k + 1) + 1 := by omega
    rw [ha, hb] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

theorem trans_c2_v1 (a b : Nat) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0,
        1] : List (Fin 2)) ^ (b + 1)) +> ([1, 1] +> r0))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * a + 4)) +> ((([0,
        1] : List (Fin 2)) ^ (b + 5)) +> ([0, 0, 1] +> default)))) := by
  have heq_r0 : ([1, 1] : List (Fin 2)) +> r0 =
      [1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default))) := rfl
  rw [heq_r0]
  have h1 := rule2_gen a b 2 ([0, 1] +> default)
  have hb : b + 2 + 3 = b + 5 := by omega
  have hr : ([0] : List (Fin 2)) +> ([0, 1] +> default) = [0, 0, 1] +> default := rfl
  rw [hb, hr] at h1
  exact h1

theorem trans_c2_v2 (a b : Nat) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0,
        1] : List (Fin 2)) ^ (b + 2)) +> ([0, 0, 1] +> default))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * a + 4)) +>
      ((([0, 1] : List (Fin 2)) ^ 2) +> ((([1, 1] : List (Fin 2)) ^ b) +> ([1] +> r0))))) := by
  have h1 := sweep_mid a (b + 1) ([0, 0, 1] +> default)
  have h2 := bounce_E_end ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 0, 1]) (b + 1)
  rw [pow_succ_append_right] at h2
  have h3 : ((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 0, 1]) <+ [1]) <{{B}}
        ([1, 1] +> ((([1, 1] : List (Fin 2)) ^ b) +> r0)))
      [target_tm]⊢⁺
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [1]) <{{B}}
        ((([0, 1] : List (Fin 2)) ^ 2) +> ([1] +> ((([1, 1] : List (Fin 2)) ^ b) +> r0)))) := by
    dsimp [ListBlank.append]; (iterate 9 step); finish
  rw [append_1_pow_01, cons_1_pow_11] at h3
  have h4 :=
      finish_B_left (a + 1) ((([0, 1] : List (Fin 2)) ^ 2) +> ((([1,
      1] : List (Fin 2)) ^ b) +> ([1] +> r0)))
  have ha : 2 * (a + 1) + 2 = 2 * a + 4 := by omega
  rw [ha] at h4
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 h4))

theorem stepPlus_E_congr {M : Machine (Fin 2) (Fin 6)} {c0 : Cfg (Fin 2) (Fin 6)}
    {A A' : Nat} {R R' : ListBlank (Fin 2)}
    (hA : A = A') (hR : R = R')
    (h : c0 [M]⊢⁺ (default <{{E}} ((([1, 0] : List (Fin 2)) ^ A) +> R))) :
    c0 [M]⊢⁺ (default <{{E}} ((([1, 0] : List (Fin 2)) ^ A') +> R')) := by
  subst hA; subst hR; exact h

theorem stepStar_E_congr {M : Machine (Fin 2) (Fin 6)} {c0 : Cfg (Fin 2) (Fin 6)}
    {A A' : Nat} {R R' : ListBlank (Fin 2)}
    (hA : A = A') (hR : R = R')
    (h : c0 [M]⊢* (default <{{E}} ((([1, 0] : List (Fin 2)) ^ A) +> R))) :
    c0 [M]⊢* (default <{{E}} ((([1, 0] : List (Fin 2)) ^ A') +> R')) := by
  subst hA; subst hR; exact h

theorem tail_01_congr {B B' : Nat} {r r' : ListBlank (Fin 2)}
    (hB : B = B') (hr : r = r') :
    ((([0, 1] : List (Fin 2)) ^ B) +> r) = ((([0, 1] : List (Fin 2)) ^ B') +> r') := by
  subst hB; subst hr; rfl

theorem cycle_c2_to_c1 (a k : Nat) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2)) +> ((([0,
        1] : List (Fin 2)) ^ (2 * k + 2)) +> ([1, 1] +> r0))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ ((4 * a + 8) * (2 ^ (k + 2)))) +>
      ((([0, 1] : List (Fin 2)) ^ (3 * k + 8)) +> ([1] +> r0)))) := by
  have hb1 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  have ha2 : 2 * a + 4 = (2 * a + 2) + 2 := by omega
  have hb2 : 2 * k + 1 + 5 = (2 * (k + 2)) + 2 := by omega
  have ha3 : 2 * (2 * a + 2) + 4 = (4 * a + 6) + 2 := by omega
  have ha4 : (4 * a + 6 + 2) * (2 ^ (k + 2)) = (4 * a + 8) * (2 ^ (k + 2)) := by
    have : 4 * a + 6 + 2 = 4 * a + 8 := by omega
    rw [this]
  have hb4 : 1 + 3 * (k + 2) + 1 = 3 * k + 8 := by omega
  rw [hb1]
  have h1 := trans_c2_v1 a (2 * k + 1)
  rw [ha2, hb2] at h1
  have h2 := trans_c2_v2 (2 * a + 2) (2 * (k + 2))
  rw [ha3, pow_11_even] at h2
  have h3' :=
      stepStar_E_congr ha4 (tail_01_congr hb4 rfl) (rule2_loop (k + 2) (4 * a + 6) 1 ([1] +> r0))
  exact stepPlus_stepStar_stepPlus (stepPlus_trans h1 h2) h3'

-- ============================================================================
-- Section 6: c = 1 Even & Odd Transition Lemmas
-- ============================================================================

set_option maxRecDepth 4000 in
theorem cap_c1_part1 (Y : ListBlank (Fin 2)) :
    ((Y <+ [0, 1, 0]) {{E}}> ((([0, 1] : List (Fin 2)) ^ 5) +> ([0] +> r0)))
    [target_tm]⊢⁺
    ((Y <+ [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]) {{E}}> ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
        1] +> default)) := by
  dsimp [r0, ListBlank.append]
  (iterate 120 step); finish

set_option maxRecDepth 4000 in
theorem cap_c1_part2 (Y : ListBlank (Fin 2)) :
    ((Y <+ [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]) {{E}}> ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
        1] +> default))
    [target_tm]⊢⁺
    ((Y <+ [1, 0]) <{{B}} ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
        1] : List (Fin 2)) ^ 5) +> r0))) := by
  dsimp [r0, ListBlank.append]
  (iterate 128 step); finish

theorem cap_c1_248 (Y : ListBlank (Fin 2)) :
    ((Y <+ [0, 1, 0]) {{E}}> ((([0, 1] : List (Fin 2)) ^ 5) +> ([0] +> r0)))
    [target_tm]⊢⁺
    ((Y <+ [1, 0]) <{{B}} ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
        1] : List (Fin 2)) ^ 5) +> r0))) :=
  stepPlus_trans (cap_c1_part1 Y) (cap_c1_part2 Y)

theorem pass_cap_c1 (X : ListBlank (Fin 2)) (d : Nat) :
    ((X <+ [0, 1]) {{E}}> ((([0, 1] : List (Fin 2)) ^ (d + 6)) +> ([0] +> r0)))
    [target_tm]⊢⁺
    ((X <+ [1]) <{{B}} ((([1, 1] : List (Fin 2)) ^ (d + 1)) +> ((([0,
        1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))) := by
  have hd : d + 6 = (d + 1) + 5 := by omega
  rw [hd, pow_add_append_right]
  have h1 := shift_E_right_01 (d + 1) (X <+ [0, 1]) ((([0, 1] : List (Fin 2)) ^ 5) +> ([0] +> r0))
  have heq1 : (X <+ [0, 1]) <+ (([0, 1] : List (Fin 2)) ^ (d + 1)) =
      ((X <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <+ [0, 1, 0] := by
    have := append_0_pow_01 (X <+ [1]) (d + 1)
    rw [pow_succ_list, ← listblank_append_append] at this
    exact this
  rw [heq1] at h1
  have h2 := cap_c1_248 ((X <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d))
  have heq2 : (((X <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ d)) <+ [1, 0]) =
      (X <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (d + 1)) := by
    rw [pow_succ_list, ← listblank_append_append]
  rw [heq2] at h2
  have h3 :=
      shift_B_left_10 (d + 1) (X <+ [1]) ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
      1] : List (Fin 2)) ^ 5) +> r0))
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

theorem glue_B_11_to_E011 (l s : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1]) <{{B}} ([1, 1, 1, 1] +> s))
    [target_tm]⊢⁺
    ((l <+ [0, 1, 1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([1] +> s)))) := by
  dsimp [ListBlank.append]; (iterate 21 step); finish

theorem glue_B_111_to_E111 (l s : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1]) <{{B}} ([1, 1, 1, 1] +> s))
    [target_tm]⊢⁺
    ((l <+ [1, 1, 1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ 3) +> ([1] +> s))) := by
  have h1 := glue_B_11_to_E011 l s
  have heq : (l <+ [0, 1, 1]) = ((l <+ [1, 1]) <+ [0]) := rfl
  rw [heq] at h1
  have h2 := half_E1_b (l <+ [1, 1]) 1 ([1] +> s)
  exact stepPlus_trans h1 h2

theorem glue_B10011_to_E111 (l s : ListBlank (Fin 2)) :
    (((l <+ [0, 0, 1, 1]) <+ [1]) <{{B}} s)
    [target_tm]⊢⁺
    ((l <+ [1, 1, 1]) <{{E}} ([1, 0] +> s)) := by
  dsimp [ListBlank.append]; (iterate 8 step); finish

theorem bounce_E111_end (l : ListBlank (Fin 2)) (d : Nat) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) <{{E}}
      ((([1, 0] : List (Fin 2)) ^ (d + 1)) +> ([0, 1] +> default)))
    [target_tm]⊢⁺
    ((l <+ [1, 1, 1]) <{{E}} ((([1, 0] : List (Fin 2)) ^ 1) +> ((([1,
        1] : List (Fin 2)) ^ (d + 1)) +> r0))) := by
  have h1 := step14_E111 l ((([1, 0] : List (Fin 2)) ^ (d + 1)) +> ([0, 1] +> default))
  rw [cons_0_pow_10] at h1
  have heq : ([0] : List (Fin 2)) +> ([0, 1] +> default) = [0, 0, 1] +> default := rfl
  rw [heq] at h1
  have h2 := bounce_E_end (l <+ [0, 0, 1, 1]) (d + 1)
  have h3 := glue_B10011_to_E111 l ((([1, 1] : List (Fin 2)) ^ (d + 1)) +> r0)
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

theorem glue_B_11101_to_B1 (l s : ListBlank (Fin 2)) :
    (((l <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) <{{B}} ([1, 1, 1, 1] +> s))
    [target_tm]⊢⁺
    (((l <+ [0, 1]) <+ [1]) <{{B}} ((([0, 1] : List (Fin 2)) ^ 4) +> s)) := by
  dsimp [ListBlank.append]; (iterate 32 step); finish

theorem step_E01_10 (X Y : ListBlank (Fin 2)) :
    ((X <+ [0, 1]) <{{E}} ([1, 0] +> Y))
    [target_tm]⊢⁺
    (((X <+ [1]) <+ [0, 1]) {{E}}> ([0] +> Y)) := by
  dsimp [ListBlank.append]; (iterate 2 step); finish

theorem step_E011_10 (X Y : ListBlank (Fin 2)) :
    ((X <+ [0, 1, 1]) <{{E}} ([1, 0] +> Y))
    [target_tm]⊢⁺
    (((X <+ [1, 1]) <+ [0, 1]) {{E}}> ([0] +> Y)) := by
  dsimp [ListBlank.append]; (iterate 2 step); finish

theorem append_011 (X : ListBlank (Fin 2)) : X <+ [0, 1, 1] = (X <+ [1, 1]) <+ [0] := rfl

theorem pow2_11_append (X : ListBlank (Fin 2)) :
    (([1, 1] : List (Fin 2)) ^ 2) +> X = [1, 1, 1, 1] +> X := rfl

theorem r0_11_pow5_1 :
    ((([1, 1] : List (Fin 2)) ^ 5) +> ([1] +> r0)) =
    [1, 1] +> ([1, 1, 1, 1] +> ([1, 1, 1, 1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0,
        1] +> default))))) := rfl

theorem r0_11_pow5_2 :
    ((([1, 1] : List (Fin 2)) ^ 5) +> ([1] +> r0)) =
    [1, 1, 1, 1] +> ([1, 1, 1, 1] +> ([1, 1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0,
        1] +> default))))) := rfl

theorem r0_11_pow5_3 :
    ((([1, 1] : List (Fin 2)) ^ 5) +> r0) =
    (([1, 1, 1, 1] : List (Fin 2)) ^ 2) +> ([1, 1] +> r0) := rfl

set_option maxRecDepth 4000 in
theorem stem_part1 :
    (init []) [target_tm]⊢⁺
    ((default <+ [1]) <{{E}} ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0,
        1] +> default)) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]; dsimp [ListBlank.append]
  (iterate 200 step); finish

set_option maxRecDepth 4000 in
theorem stem_part2 :
    ((default <+ [1]) <{{E}} ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0,
        1] +> default))
    [target_tm]⊢⁺
    ((default <+ [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) {{E}}> ([0, 1,
        0, 0, 1, 0, 1, 1, 0, 1] +> default)) := by
  dsimp [ListBlank.append]
  (iterate 200 step); finish

set_option maxRecDepth 4000 in
theorem stem_part3 :
    ((default <+ [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) {{E}}> ([0, 1,
        0, 0, 1, 0, 1, 1, 0, 1] +> default))
    [target_tm]⊢⁺
    ((default <+ [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
        1]) <{{B}} ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1] +> default)) := by
  dsimp [ListBlank.append]
  (iterate 200 step); finish

set_option maxRecDepth 4000 in
theorem stem_part4 :
    ((default <+ [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
        1]) <{{B}} ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1] +> default))
    [target_tm]⊢⁺
    ((default <+ [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) <{{E}} ([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0,
        1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1] +> default)) := by
  dsimp [ListBlank.append]
  (iterate 200 step); finish

set_option maxRecDepth 4000 in
theorem stem_part5 :
    ((default <+ [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) <{{E}} ([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0,
        1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1] +> default))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ 14) +> ((([0, 1] : List (Fin 2)) ^ 4) +>
      ((([1, 1, 1, 1] : List (Fin 2)) ^ 2) +> ([1, 1] +> r0))))) := by
  dsimp [r0, ListBlank.append]
  (iterate 176 step); finish


theorem trans_c1_even (a m : Nat) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2 * m + 17)) +>
      ((([0, 1] : List (Fin 2)) ^ (2 * m + 8)) +> ([1] +> r0))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * a + 12)) +>
      ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ (4 * m + 21)) +> r0)))) := by
  have ha0 : a + 2 * m + 17 = (a + 2 * m + 15) + 2 := by omega
  have hb0 : 2 * m + 8 = (2 * m + 7) + 1 := by omega
  rw [ha0, hb0]
  have h1 := sweep_init (a + 2 * m + 15) (2 * m + 7) r0
  have hd1 : 2 * m + 7 + 2 = (2 * m + 8) + 1 := by omega
  rw [hd1, pow_succ_append_right [1, 0] (2 * m + 8) r0] at h1
  have h2 := step_E01_10
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 2 * m + 15 + 1)))
    ((([1, 0] : List (Fin 2)) ^ (2 * m + 8)) +> r0)
  rw [cons_0_pow_10] at h2
  have hd2 : 2 * m + 8 = (2 * m + 2) + 6 := by omega
  rw [hd2] at h2
  have h3 :=
      pass_cap_c1 ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 2 * m + 15 + 1))) <+ [1]) (2 * m + 2)
  have heq3 : (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 2 * m + 15 + 1))) <+ [1]) <+ [1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 14))) <+ (([0, 1] : List (Fin 2)) ^ (2 * m))) <+
        (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1] := by
    have h_exp : a + 2 * m + 15 + 1 = ((a + 14) + 2 * m) + 2 := by omega
    rw [h_exp, pow_add_append_left, pow_add_append_left, append_1_1]
  have hr3 : ((([1, 1] : List (Fin 2)) ^ (2 * m + 2 + 1)) +> ((([0,
      1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) =
      [1, 1, 1, 1] +> ((([1, 1] : List (Fin 2)) ^ (2 * m)) +> ([1, 1] +> ((([0,
          1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))) := by
    have : 2 * m + 2 + 1 = 2 + (2 * m + 1) := by omega
    rw [this, pow_add_append_right, pow_succ_append_right', pow2_11_append]
  rw [heq3, hr3] at h3
  have h4 := glue_B_111_to_E111
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 14))) <+ (([0, 1] : List (Fin 2)) ^ (2 * m)))
    ((([1, 1] : List (Fin 2)) ^ (2 * m)) +> ([1, 1] +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
        1] : List (Fin 2)) ^ 5) +> r0))))
  rw [cons_1_pow_11, pow_11_even m ([1] +> ([1, 1] +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
      1] : List (Fin 2)) ^ 5) +> r0))))] at h4
  have h5 := loop_E1_iter m (default <+ (([0, 1] : List (Fin 2)) ^ (a + 14))) 3
    ([1] +> ([1, 1] +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))))
  have hl5 : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 14))) <+ [1, 1, 1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (((a + 6) + 2) + 2 + 2))) <+ (([0,
          1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) := by
    have ha5 : a + 14 = (((a + 6) + 2) + 2 + 2) + 2 := by omega
    rw [ha5, pow_add_append_left]
  have hr5 : ((([1, 0] : List (Fin 2)) ^ (3 + 4 * m)) +> ([1] +> ([1, 1] +> ((([0,
      1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))))) =
      ((([1, 0] : List (Fin 2)) ^ (3 + 4 * m)) +> ([1, 1] +> ([1] +> ((([0,
          1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))))) := rfl
  rw [hl5, hr5] at h5
  have h6 := half_E1_a
    (default <+ (([0, 1] : List (Fin 2)) ^ (((a + 6) + 2) + 2 + 2)))
    (3 + 4 * m)
    ([1] +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))
  have hl6 : ((default <+ (([0, 1] : List (Fin 2)) ^ (((a + 6) + 2) + 2 + 2))) <+ [0, 1, 1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (((a + 6) + 2) + 2 + 2))) <+ [1, 1]) <+ [0]) :=
    append_011 _
  have hr6' : ((([1, 0] : List (Fin 2)) ^ (3 + 4 * m + 3)) +> ([1] +> ((([0,
      1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))) =
      ((([1, 0] : List (Fin 2)) ^ ((4 * m + 9) + 1)) +> ([1, 1] +> ([1, 1, 1, 1] +> ([1, 1, 1,
          1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default))))))) := by
    have hd6 : 3 + 4 * m + 3 + 4 = (4 * m + 9) + 1 := by omega
    have hr6 := r0_11_pow5_1
    rw [cons_1_pow_01, cons_1_pow_11, ← pow_add_append_right [1, 0], hd6, hr6]
  rw [hl6, hr6'] at h6
  have h7 := half_E1_b
    ((default <+ (([0, 1] : List (Fin 2)) ^ (((a + 6) + 2) + 2 + 2))) <+ [1, 1])
    (4 * m + 9)
    ([1, 1, 1, 1] +> ([1, 1, 1, 1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0,
        1] +> default)))))
  have hl7 : (((default <+ (([0, 1] : List (Fin 2)) ^ (((a + 6) + 2) + 2 + 2))) <+ [1, 1]) <+ [1]) =
      ((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 6))) <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ (([0,
          1] : List (Fin 2)) ^ 2)) <+
        (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1] := by
    rw [pow_add_append_left, pow_add_append_left, pow_add_append_left, append_11_1]
  rw [hl7] at h7
  have h8 := loop_E1_step
    (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 6))) <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ (([0,
        1] : List (Fin 2)) ^ 2))
    (4 * m + 9 + 2)
    ([1, 1, 1, 1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default))))
  have h9 := loop_E1_step
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 6))) <+ (([0, 1] : List (Fin 2)) ^ 2))
    (4 * m + 9 + 2 + 4)
    ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default)))
  rw [← pow_add_append_right [1, 0]] at h9
  have h10 := half_E1_a
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 6)))
    (4 * m + 9 + 2 + 4 + 4 + 2)
    ([0, 1] +> default)
  have hd10 : 4 * m + 9 + 2 + 4 + 4 + 2 + 3 = (4 * m + 23) + 1 := by omega
  rw [hd10, pow_succ_append_right [1, 0] (4 * m + 23) ([0, 1] +> default)] at h10
  have h11 := step_E011_10
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 6)))
    ((([1, 0] : List (Fin 2)) ^ (4 * m + 23)) +> ([0, 1] +> default))
  rw [cons_0_pow_10] at h11
  have hr11 : ([0] : List (Fin 2)) +> ([0, 1] +> default) = [0, 0, 1] +> default := rfl
  rw [hr11] at h11
  have h12 := bounce_E_end
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 6))) <+ [1, 1])
    (4 * m + 23)
  have ha12 : a + 6 = (a + 4) + 2 := by omega
  have hl12 : (((default <+ (([0, 1] : List (Fin 2)) ^ ((a + 4) + 2))) <+ [1, 1]) <+ [1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4))) <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1,
          1]) := by
    rw [pow_add_append_left, append_11_1]
  have hr12 : ((([1, 1] : List (Fin 2)) ^ (4 * m + 23)) +> r0) =
      [1, 1, 1, 1] +> ((([1, 1] : List (Fin 2)) ^ (4 * m + 21)) +> r0) := by
    have : 4 * m + 23 = 2 + (4 * m + 21) := by omega
    rw [this, pow_add_append_right, pow2_11_append]
  rw [ha12, hl12, hr12] at h12
  have h13 := glue_B_11101_to_B1
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 4)))
    ((([1, 1] : List (Fin 2)) ^ (4 * m + 21)) +> r0)
  have hl13 : (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4))) <+ [0, 1]) <+ [1]) =
      (default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (a + 5)) := by
    have : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4))) <+ [0, 1]) =
        default <+ (([0, 1] : List (Fin 2)) ^ (a + 5)) := by
      exact (pow_succ_append_right [0, 1] (a + 4) default).symm
    rw [this, append_1_pow_01]
  rw [hl13] at h13
  have h14 := finish_B_left (a + 5)
    ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ (4 * m + 21)) +> r0))
  have ha14 : 2 * (a + 5) + 2 = 2 * a + 12 := by omega
  rw [ha14] at h14
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 (stepPlus_trans h4
    (stepStar_stepPlus_stepPlus h5 (stepPlus_trans h6 (stepPlus_trans h7 (stepPlus_trans h8
      (stepPlus_trans h9 (stepPlus_trans h10 (stepPlus_trans h11 (stepPlus_trans h12
        (stepPlus_trans h13 h14))))))))))))

theorem trans_c1_odd (a m : Nat) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 6 * m + 36)) +>
      ((([0, 1] : List (Fin 2)) ^ (2 * m + 7)) +> ([1] +> r0))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (2 * a + 6)) +>
      ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ (8 * m + 36)) +>
        ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))))) := by
  have ha0 : a + 6 * m + 36 = (a + 6 * m + 34) + 2 := by omega
  have hb0 : 2 * m + 7 = (2 * m + 6) + 1 := by omega
  rw [ha0, hb0]
  have h1 := sweep_init (a + 6 * m + 34) (2 * m + 6) r0
  have hd1 : 2 * m + 6 + 2 = (2 * m + 7) + 1 := by omega
  rw [hd1, pow_succ_append_right [1, 0] (2 * m + 7) r0] at h1
  have h2 := step_E01_10
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 6 * m + 34 + 1)))
    ((([1, 0] : List (Fin 2)) ^ (2 * m + 7)) +> r0)
  rw [cons_0_pow_10] at h2
  have hd2 : 2 * m + 7 = (2 * m + 1) + 6 := by omega
  rw [hd2] at h2
  have h3 :=
      pass_cap_c1 ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 6 * m + 34 + 1))) <+ [1]) (2 * m + 1)
  have heq3 : (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 6 * m + 34 + 1))) <+ [1]) <+ [1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 33))) <+ (([0,
          1] : List (Fin 2)) ^ (2 * m))) <+
        (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1] := by
    have h_exp : a + 6 * m + 34 + 1 = ((a + 4 * m + 33) + 2 * m) + 2 := by omega
    rw [h_exp, pow_add_append_left, pow_add_append_left, append_1_1]
  have hr3 : ((([1, 1] : List (Fin 2)) ^ (2 * m + 1 + 1)) +> ((([0,
      1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) =
      [1, 1, 1, 1] +> ((([1, 1] : List (Fin 2)) ^ (2 * m)) +> ((([0,
          1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) := by
    have : 2 * m + 1 + 1 = 2 + 2 * m := by omega
    rw [this, pow_add_append_right, pow2_11_append]
  rw [heq3, hr3] at h3
  have h4 := glue_B_111_to_E111
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 33))) <+ (([0,
        1] : List (Fin 2)) ^ (2 * m)))
    ((([1, 1] : List (Fin 2)) ^ (2 * m)) +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
        1] : List (Fin 2)) ^ 5) +> r0)))
  rw [cons_1_pow_11, pow_11_even m ([1] +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
      1] : List (Fin 2)) ^ 5) +> r0)))] at h4
  have h5 := loop_E1_iter m (default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 33))) 3
    ([1] +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))
  have hl5 : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 33))) <+ [1, 1, 1]) =
      (((((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27))) <+ (([0,
          1] : List (Fin 2)) ^ 2)) <+
        (([0, 1] : List (Fin 2)) ^ 2)) <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) := by
    have ha5 : a + 4 * m + 33 = (((a + 4 * m + 27) + 2) + 2) + 2 := by omega
    rw [ha5, pow_add_append_left, pow_add_append_left, pow_add_append_left]
  have hr5' : ((([1, 0] : List (Fin 2)) ^ (3 + 4 * m)) +> ([1] +> ((([0,
      1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)))) =
      ((([1, 0] : List (Fin 2)) ^ (4 * m + 7)) +> ([1, 1, 1, 1] +> ([1, 1, 1, 1] +> ([1,
          1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default))))))) := by
    have hd5 : 3 + 4 * m + 4 = 4 * m + 7 := by omega
    have hr5 := r0_11_pow5_2
    rw [cons_1_pow_01, cons_1_pow_11, ← pow_add_append_right [1, 0], hd5, hr5]
  rw [hl5, hr5'] at h5
  have h6 := loop_E1_step
    (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27))) <+ (([0,
        1] : List (Fin 2)) ^ 2)) <+ (([0, 1] : List (Fin 2)) ^ 2))
    (4 * m + 7)
    ([1, 1, 1, 1] +> ([1, 1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default)))))
  have h7 := loop_E1_step
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27))) <+ (([0, 1] : List (Fin 2)) ^ 2))
    (4 * m + 7 + 4)
    ([1, 1] +> ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default))))
  have h8 := half_E1_a
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27)))
    (4 * m + 7 + 4 + 4)
    ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1] +> ([0, 1] +> default)))
  rw [← pow_add_append_right [1, 0]] at h8
  have hd8 : 4 * m + 7 + 4 + 4 + 3 + 2 = (4 * m + 19) + 1 := by omega
  have hl8 : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27))) <+ [0, 1, 1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27))) <+ [1, 1]) <+ [0]) :=
    append_011 _
  rw [hd8, hl8] at h8
  have h9 := half_E1_b
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 27))) <+ [1, 1])
    (4 * m + 19)
    ([0, 1] +> default)
  have hd9 : 4 * m + 19 + 2 = (4 * m + 20) + 1 := by omega
  have ha9 : a + 4 * m + 27 = (a + 4 * m + 25) + 2 := by omega
  have hl9 : (((default <+ (([0, 1] : List (Fin 2)) ^ ((a + 4 * m + 25) + 2))) <+ [1, 1]) <+ [1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 25))) <+ (([0,
          1] : List (Fin 2)) ^ 2)) <+ [1, 1, 1]) := by
    rw [pow_add_append_left, append_11_1]
  rw [hd9, ha9, hl9] at h9
  have h10 := bounce_E111_end
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 25)))
    (4 * m + 20)
  have ha10 : a + 4 * m + 25 = (a + 5) + 2 * (2 * m + 10) := by omega
  have hl10 : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 4 * m + 25))) <+ [1, 1, 1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 5))) <+ (([0,
          1] : List (Fin 2)) ^ (2 * (2 * m + 10)))) <+ [1, 1, 1]) := by
    rw [ha10, pow_add_append_left]
  have hr10 : ((([1, 1] : List (Fin 2)) ^ (4 * m + 20 + 1)) +> r0) =
      (([1, 1, 1, 1] : List (Fin 2)) ^ (2 * m + 10)) +> ([1, 1] +> r0) := by
    have : 4 * m + 20 + 1 = 2 * (2 * m + 10) + 1 := by omega
    rw [this, ← pow_succ_append_right', pow_11_even]
  rw [hl10, hr10] at h10
  have h11 := loop_E1_iter (2 * m + 10)
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 5)))
    1
    ([1, 1] +> r0)
  have ha11 : a + 5 = (a + 3) + 2 := by omega
  have hl11 : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 5))) <+ [1, 1, 1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 3))) <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1,
          1]) := by
    rw [ha11, pow_add_append_left]
  rw [hl11] at h11
  have h12 := half_E1_a
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 3)))
    (1 + 4 * (2 * m + 10))
    r0
  have hd12 : 1 + 4 * (2 * m + 10) + 3 = (8 * m + 43) + 1 := by omega
  rw [hd12, pow_succ_append_right [1, 0]] at h12
  have h13 := step_E011_10
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 3)))
    ((([1, 0] : List (Fin 2)) ^ (8 * m + 43)) +> r0)
  rw [cons_0_pow_10] at h13
  have hd13 : 8 * m + 43 = (8 * m + 37) + 6 := by omega
  rw [hd13] at h13
  have h14 := pass_cap_c1
    ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 3))) <+ [1, 1])
    (8 * m + 37)
  have ha14 : a + 3 = (a + 1) + 2 := by omega
  have hl14 : (((default <+ (([0, 1] : List (Fin 2)) ^ ((a + 1) + 2))) <+ [1, 1]) <+ [1]) =
      (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ (([0, 1] : List (Fin 2)) ^ 2)) <+ [1, 1,
          1]) := by
    rw [pow_add_append_left, append_11_1]
  have hr14 : ((([1, 1] : List (Fin 2)) ^ (8 * m + 37 + 1)) +> ((([0,
      1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) =
      [1, 1, 1, 1] +> ((([1, 1] : List (Fin 2)) ^ (8 * m + 36)) +> ((([0,
          1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) := by
    have : 8 * m + 37 + 1 = 2 + (8 * m + 36) := by omega
    rw [this, pow_add_append_right, pow2_11_append]
  rw [ha14, hl14, hr14] at h14
  have h15 := glue_B_11101_to_B1
    (default <+ (([0, 1] : List (Fin 2)) ^ (a + 1)))
    ((([1, 1] : List (Fin 2)) ^ (8 * m + 36)) +> ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
        1] : List (Fin 2)) ^ 5) +> r0)))
  have hl15 : (((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1]) <+ [1]) =
      (default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (a + 2)) := by
    have : ((default <+ (([0, 1] : List (Fin 2)) ^ (a + 1))) <+ [0, 1]) =
        default <+ (([0, 1] : List (Fin 2)) ^ (a + 2)) := by
      exact (pow_succ_append_right [0, 1] (a + 1) default).symm
    rw [this, append_1_pow_01]
  rw [hl15] at h15
  have h16 := finish_B_left (a + 2)
    ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ (8 * m + 36)) +>
      ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))))
  have ha16 : 2 * (a + 2) + 2 = 2 * a + 6 := by omega
  rw [ha16] at h16
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 (stepPlus_trans h4
    (stepStar_stepPlus_stepPlus h5 (stepPlus_trans h6 (stepPlus_trans h7 (stepPlus_trans h8
      (stepPlus_trans h9 (stepPlus_trans h10 (stepStar_stepPlus_stepPlus h11
        (stepPlus_trans h12 (stepPlus_trans h13 (stepPlus_trans h14 (stepPlus_trans h15
            h16))))))))))))))

-- ============================================================================
-- Section 7: Stem (init [] -> P a₀ 81) & Full Macro-Cycle
-- ============================================================================

def P (a j : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 18 * j + 100)) +>
    ((([0, 1] : List (Fin 2)) ^ (4 * j + 16)) +> ([1, 1] +> r0)))

theorem hide_mul_pow2 (X p : Nat) : ∃ N, X * (2 ^ p) = N ∧ X ≤ N :=
  ⟨X * (2 ^ p), rfl, mul_pow2_ge X p⟩

theorem drain_c1_even (a m : Nat) :
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ (a + 2 * m + 17)) +>
      ((([0, 1] : List (Fin 2)) ^ (2 * m + 8)) +> ([1] +> r0))))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ ((2 * a + 12) * (2 ^ (2 * m + 10)))) +>
      ((([0, 1] : List (Fin 2)) ^ (6 * m + 34)) +> ([1, 1] +> r0)))) := by
  have ha1 : 2 * a + 12 = (2 * a + 10) + 2 := by omega
  have hr1 : ((([1, 1] : List (Fin 2)) ^ (4 * m + 21)) +> r0) =
      (([1, 1, 1, 1] : List (Fin 2)) ^ (2 * m + 10)) +> ([1, 1] +> r0) := by
    have : 4 * m + 21 = 2 * (2 * m + 10) + 1 := by omega
    rw [this, ← pow_succ_append_right', pow_11_even]
  have ha2 : (2 * a + 10 + 2) * (2 ^ (2 * m + 10)) = (2 * a + 12) * (2 ^ (2 * m + 10)) := by
    have : 2 * a + 10 + 2 = 2 * a + 12 := by omega
    rw [this]
  have hb2 : 3 + 3 * (2 * m + 10) + 1 = 6 * m + 34 := by omega
  have h1' := stepPlus_E_congr ha1 (tail_01_congr rfl hr1) (trans_c1_even a m)
  have h2' :=
      stepStar_E_congr ha2 (tail_01_congr hb2 rfl) (rule2_loop (2 * m + 10) (2 * a + 10) 3 ([1,
      1] +> r0))
  exact stepPlus_stepStar_stepPlus h1' h2'

theorem init_to_P :
    ∃ a₀, (init []) [target_tm]⊢⁺ P a₀ 81 := by
  have heq1 : (4 * 54 + 8) * (2 ^ (4 + 2)) = 14307 + 2 * 6 + 17 := by decide
  have heq1_b : 3 * 4 + 8 = 2 * 6 + 8 := rfl
  rcases hide_mul_pow2 (2 * 14307 + 12) (2 * 6 + 10) with ⟨N1, hN1_eq, hN1_ge⟩
  have hN1_split : N1 = (N1 - 2) + 2 := by clear hN1_eq; omega
  have ha_split1 : (2 * 14307 + 12) * (2 ^ (2 * 6 + 10)) = (N1 - 2) + 2 := hN1_eq.trans hN1_split
  have hb_next : 6 * 6 + 34 = 2 * 34 + 2 := rfl
  rcases hide_mul_pow2 (4 * (N1 - 2) + 8) (34 + 2) with ⟨N2, hN2_eq, hN2_ge⟩
  have hN2_split : N2 = (N2 - 119) + 2 * 51 + 17 := by clear hN1_eq ha_split1 hN2_eq; omega
  have ha_split2 : (4 * (N1 - 2) + 8) * (2 ^ (34 + 2)) = (N2 - 119) + 2 * 51 + 17 :=
      hN2_eq.trans hN2_split
  have hb_split2 : 3 * 34 + 8 = 2 * 51 + 8 := rfl
  rcases hide_mul_pow2 (2 * (N2 - 119) + 12) (2 * 51 + 10) with ⟨N3, hN3_eq, hN3_ge⟩
  let a₀ := N3 - (18 * 81 + 100)
  have hN3_split : N3 = a₀ + 18 * 81 + 100 := by
    dsimp [a₀]; clear hN1_eq ha_split1 hN2_eq ha_split2 hN3_eq; omega
  have ha_final : (2 * (N2 - 119) + 12) * (2 ^ (2 * 51 + 10)) = a₀ + 18 * 81 + 100 :=
      hN3_eq.trans hN3_split
  have hb_final : 6 * 51 + 34 = 4 * 81 + 16 := rfl
  have h_stem :=
      stepPlus_trans stem_part1 (stepPlus_trans stem_part2 (stepPlus_trans stem_part3
      (stepPlus_trans stem_part4 stem_part5)))
  have h_r2 := rule2_loop 2 12 3 ([1, 1] +> r0)
  have h_ev4 := stepPlus_stepStar_stepPlus h_stem h_r2
  have h_c2_1 := stepPlus_E_congr heq1 (tail_01_congr heq1_b rfl) (cycle_c2_to_c1 54 4)
  have h_c1_1 := stepPlus_E_congr ha_split1 (tail_01_congr hb_next rfl) (drain_c1_even 14307 6)
  have h_c2_2 :=
      stepPlus_E_congr ha_split2 (tail_01_congr hb_split2 rfl) (cycle_c2_to_c1 (N1 - 2) 34)
  have h_c1_2 :=
      stepPlus_E_congr ha_final (tail_01_congr hb_final rfl) (drain_c1_even (N2 - 119) 51)
  exact ⟨a₀,
      stepPlus_trans h_ev4 (stepPlus_trans h_c2_1 (stepPlus_trans h_c1_1 (stepPlus_trans h_c2_2
      h_c1_2)))⟩

theorem P_step (a j : Nat) :
    ∃ a', (P a j) [target_tm]⊢⁺ (P a' (9 * j + 46)) := by
  unfold P
  have ha0 : a + 18 * j + 100 = (a + 18 * j + 98) + 2 := by omega
  have hb0 : 4 * j + 16 = 2 * (2 * j + 7) + 2 := by omega
  rcases hide_mul_pow2 (4 * (a + 18 * j + 98) + 8) (2 * j + 7 + 2) with ⟨M1, hM1_eq, hM1_ge⟩
  let a1 := M1 - (6 * (3 * j + 11) + 36)
  have hM1_split : M1 = a1 + 6 * (3 * j + 11) + 36 := by dsimp [a1]; clear hM1_eq; omega
  have ha1 : (4 * (a + 18 * j + 98) + 8) * (2 ^ (2 * j + 7 + 2)) = a1 + 6 * (3 * j + 11) + 36 :=
    hM1_eq.trans hM1_split
  have hb1 : 3 * (2 * j + 7) + 8 = 2 * (3 * j + 11) + 7 := by clear hM1_eq ha1; omega
  have ha2 : 2 * a1 + 6 = (2 * a1 + 4) + 2 := by clear hM1_eq ha1; omega
  have hr2 : ((([1, 1] : List (Fin 2)) ^ (8 * (3 * j + 11) + 36)) +>
        ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) =
      (([1, 1, 1, 1] : List (Fin 2)) ^ (12 * j + 62)) +>
        ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0)) := by
    have : 8 * (3 * j + 11) + 36 = 2 * (12 * j + 62) := by clear hM1_eq ha1; omega
    rw [this, pow_11_even]
  rcases hide_mul_pow2 (2 * a1 + 4 + 2) (12 * j + 62) with ⟨M2, hM2_eq, hM2_ge⟩
  have hM2_split : M2 = (M2 - 2) + 2 := by dsimp [a1] at hM2_ge; clear hM1_eq ha1 hr2 hM2_eq; omega
  have ha3 : (2 * a1 + 4 + 2) * (2 ^ (12 * j + 62)) = (M2 - 2) + 2 := hM2_eq.trans hM2_split
  have hr3_full : ((([0, 1] : List (Fin 2)) ^ (3 + 3 * (12 * j + 62) + 1)) +>
        ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1, 1] : List (Fin 2)) ^ 5) +> r0))) =
      ((([0, 1] : List (Fin 2)) ^ ((36 * j + 193) + 1)) +>
        ((([1, 1, 1, 1] : List (Fin 2)) ^ 2) +> ([1, 1] +> r0))) := by
    rw [← pow_add_append_right [0, 1]]
    have hb3 : 3 + 3 * (12 * j + 62) + 1 + 4 = (36 * j + 193) + 1 := by
      clear hM1_eq ha1 hr2 hM2_eq ha3; omega
    rw [hb3, r0_11_pow5_3]
  let a' := (M2 - 2 + 2) * 4 - (18 * (9 * j + 46) + 100)
  have ha4 : (M2 - 2 + 2) * (2 ^ 2) = a' + 18 * (9 * j + 46) + 100 := by
    change (M2 - 2 + 2) * 4 = a' + 18 * (9 * j + 46) + 100
    dsimp [a', a1] at hM2_ge ⊢; clear hM1_eq ha1 hr2 hM2_eq ha3 hr3_full; omega
  have hb4 : 36 * j + 193 + 3 * 2 + 1 = 4 * (9 * j + 46) + 16 := by
    clear hM1_eq ha1 hr2 hM2_eq ha3 hr3_full ha4; omega
  rw [ha0, hb0]
  have h1 :=
      stepPlus_E_congr ha1 (tail_01_congr hb1 rfl) (cycle_c2_to_c1 (a + 18 * j + 98) (2 * j + 7))
  have h2 := stepPlus_E_congr ha2 (tail_01_congr rfl hr2) (trans_c1_odd a1 (3 * j + 11))
  have h3 := stepStar_E_congr ha3 hr3_full
    (rule2_loop (12 * j + 62) (2 * a1 + 4) 3 ((([0, 1] : List (Fin 2)) ^ 4) +> ((([1,
        1] : List (Fin 2)) ^ 5) +> r0)))
  have h4 :=
      stepStar_E_congr ha4 (tail_01_congr hb4 rfl) (rule2_loop 2 (M2 - 2) (36 * j + 193) ([1,
      1] +> r0))
  exact ⟨a', stepPlus_stepStar_stepPlus (stepPlus_trans h1 h2) (stepStar_trans h3 h4)⟩

-- ============================================================================
-- Section 8: Top-Level Non-Halting Theorem
-- ============================================================================

theorem multiStep_prefix_isSome {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [multiStep_add] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

theorem P_reaches (m : Nat) :
    ∃ N ≥ m, ∃ a j, multiStep target_tm (init []) N = some (P a j) := by
  induction m with
  | zero =>
    rcases init_to_P with ⟨a₀, k, _, hk⟩
    exact ⟨k, Nat.zero_le k, a₀, 81, hk⟩
  | succ m ih =>
    rcases ih with ⟨N, hN, a, j, h_ms⟩
    rcases P_step a j with ⟨a', k, hk_pos, hk⟩
    exact ⟨N + k, Nat.add_le_add hN hk_pos, a', 9 * j + 46,
        multiStep_trans target_tm _ _ _ N k h_ms hk⟩



set_option maxRecDepth 4000 in
theorem stem_0426_part1 :
    (((default : ListBlank (Fin 2)) {{5}}> default) : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
    (([1, 1, 0, 1, 0, 1, 0, 1] +> default) <{{D}}
      (default <+ [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1])) := by
  have h_init : (((default : ListBlank (Fin 2)) {{5}}> default) : Cfg (Fin 2) (Fin 6)) =
      (default <{{F}} default) := rfl
  rw [h_init]; dsimp [ListBlank.append]
  (iterate 180 step); finish

set_option maxRecDepth 4000 in
theorem stem_0426_part2 :
    (([1, 1, 0, 1, 0, 1, 0, 1] +> default) <{{D}}
      (default <+ [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]))
    [target_tm]⊢⁺
    (([0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] +> default) <{{B}}
      (default <+ [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1])) := by
  dsimp [ListBlank.append]
  (iterate 170 step); finish

set_option maxRecDepth 4000 in
theorem stem_0426_part3 :
    (([0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] +> default) <{{B}}
      (default <+ [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1]))
    [target_tm]⊢⁺
    (default <{{E}} ((([1, 0] : List (Fin 2)) ^ 6) +> ((([0, 1] : List (Fin 2)) ^ 4) +>
      ((([1, 1, 1, 1] : List (Fin 2)) ^ 2) +> ([1, 1] +> r0))))) := by
  dsimp [r0, ListBlank.append]
  (iterate 173 step); finish

theorem c_523_0829_to_P :
    ∃ a₀, (default <{{E}} ((([1, 0] : List (Fin 2)) ^ 6) +> ((([0, 1] : List (Fin 2)) ^ 4) +>
      ((([1, 1, 1, 1] : List (Fin 2)) ^ 2) +> ([1, 1] +> r0))))) [target_tm]⊢⁺ P a₀ 81 := by
  have heq1 : (4 * 22 + 8) * (2 ^ (4 + 2)) = 6115 + 2 * 6 + 17 := by decide
  have heq1_b : 3 * 4 + 8 = 2 * 6 + 8 := rfl
  rcases hide_mul_pow2 (2 * 6115 + 12) (2 * 6 + 10) with ⟨N1, hN1_eq, hN1_ge⟩
  have hN1_split : N1 = (N1 - 2) + 2 := by clear hN1_eq; omega
  have ha_split1 : (2 * 6115 + 12) * (2 ^ (2 * 6 + 10)) = (N1 - 2) + 2 := hN1_eq.trans hN1_split
  have hb_next : 6 * 6 + 34 = 2 * 34 + 2 := rfl
  rcases hide_mul_pow2 (4 * (N1 - 2) + 8) (34 + 2) with ⟨N2, hN2_eq, hN2_ge⟩
  have hN2_split : N2 = (N2 - 119) + 2 * 51 + 17 := by clear hN1_eq ha_split1 hN2_eq; omega
  have ha_split2 : (4 * (N1 - 2) + 8) * (2 ^ (34 + 2)) = (N2 - 119) + 2 * 51 + 17 :=
    hN2_eq.trans hN2_split
  have hb_split2 : 3 * 34 + 8 = 2 * 51 + 8 := rfl
  rcases hide_mul_pow2 (2 * (N2 - 119) + 12) (2 * 51 + 10) with ⟨N3, hN3_eq, hN3_ge⟩
  let a₀ := N3 - (18 * 81 + 100)
  have hN3_split : N3 = a₀ + 18 * 81 + 100 := by
    dsimp [a₀]; clear hN1_eq ha_split1 hN2_eq ha_split2 hN3_eq; omega
  have ha_final : (2 * (N2 - 119) + 12) * (2 ^ (2 * 51 + 10)) = a₀ + 18 * 81 + 100 :=
    hN3_eq.trans hN3_split
  have hb_final : 6 * 51 + 34 = 4 * 81 + 16 := rfl
  have h_r2 := rule2_loop 2 4 3 ([1, 1] +> r0)
  have h_c2_1 := cycle_c2_to_c1 22 4
  have h_ev4_c1_raw := stepStar_stepPlus_stepPlus h_r2 h_c2_1
  have h_ev4_c1 := stepPlus_E_congr heq1 (tail_01_congr heq1_b rfl) h_ev4_c1_raw
  have h_c1_1 := stepPlus_E_congr ha_split1 (tail_01_congr hb_next rfl) (drain_c1_even 6115 6)
  have h_c2_2 := stepPlus_E_congr ha_split2 (tail_01_congr hb_split2 rfl)
    (cycle_c2_to_c1 (N1 - 2) 34)
  have h_c1_2 := stepPlus_E_congr ha_final (tail_01_congr hb_final rfl)
    (drain_c1_even (N2 - 119) 51)
  exact ⟨a₀, stepPlus_trans h_ev4_c1 (stepPlus_trans h_c1_1 (stepPlus_trans h_c2_2 h_c1_2))⟩

theorem init_to_P_0426 :
    ∃ a₀, (((default : ListBlank (Fin 2)) {{5}}> default) : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      P a₀ 81 := by
  have h_stem := stepPlus_trans stem_0426_part1 (stepPlus_trans stem_0426_part2 stem_0426_part3)
  rcases c_523_0829_to_P with ⟨a₀, h_to_P⟩
  exact ⟨a₀, stepPlus_trans h_stem h_to_P⟩

theorem P_reaches_0426 (m : Nat) :
    ∃ N ≥ m, ∃ a j,
      multiStep target_tm ((default : ListBlank (Fin 2)) {{5}}> default) N = some (P a j) := by
  induction m with
  | zero =>
    rcases init_to_P_0426 with ⟨a₀, k, _, hk⟩
    exact ⟨k, Nat.zero_le k, a₀, 81, hk⟩
  | succ m ih =>
    rcases ih with ⟨N, hN, a, j, h_ms⟩
    rcases P_step a j with ⟨a', k, hk_pos, hk⟩
    exact ⟨N + k, Nat.add_le_add hN hk_pos, a', 9 * j + 46,
      multiStep_trans target_tm _ _ _ N k h_ms hk⟩

theorem is_not_halt_from_0426_tm :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{5}}> default) [target_tm]⊢* cfg) →
      (step target_tm cfg).isSome := by
  intro cfg ⟨n, hn⟩
  rcases P_reaches_0426 (n + 1) with ⟨N, hN, a, j, h_N⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [← h_eq] at h_N
  have h_some := multiStep_prefix_isSome h_N
  rw [multiStep_succ, hn] at h_some
  exact h_some

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨n, hn⟩
  rcases P_reaches (n + 1) with ⟨N, hN, a, j, h_N⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [← h_eq] at h_N
  have h_some := multiStep_prefix_isSome h_N
  rw [multiStep_succ, hn] at h_some
  exact h_some

end Solution

public section

theorem is_not_halt_from_0426 :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{5}}> default) [target]⊢* cfg) →
      (step target cfg).isSome :=
  Solution.is_not_halt_from_0426_tm

theorem is_not_halt : IsNotHalt target := Solution.is_does_not_halt

end

end BusyBeaver.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC
