/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedTactic false

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

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

lemma list_pow_append_one (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := list_pow_add_comm u k 1
  dsimp [HPow.hPow, list_nat_repeat] at h ⊢
  rw [List.append_nil] at h
  exact h

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

lemma pow_succ_append_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

lemma pow_succ_append_right' (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [listblank_append_append, list_pow_append_one]

lemma pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

lemma pow_succ_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (k : Nat) :
    s <+ (u ^ (k + 1)) = (s <+ (u ^ k)) <+ u := by
  rw [pow_succ_list, ← listblank_append_append]

lemma multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)

local macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])

local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))

local macro "execute" : tactic =>
  `(tactic| (try simp only [listblank_append_cons, listblank_append_nil]) <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

lemma multiStep_step_isSome {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₀ cfg cfg' : Cfg Γ Λ) (n m : Nat)
    (hn : multiStep M c₀ n = some cfg)
    (hnm : multiStep M c₀ (n + (1 + m)) = some cfg') :
    (step M cfg).isSome := by
  rw [multiStep_add M c₀ n (1 + m), hn] at hnm
  dsimp [Option.bind] at hnm
  rw [multiStep_add M cfg 1 m, multiStep_one] at hnm
  cases hs : step M cfg with
  | none => rw [hs] at hnm; nomatch hnm
  | some c₁ => rfl

lemma inv_reaches_beyond {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ cfg₀, ((init []) [M]⊢* cfg₀) ∧ Inv cfg₀)
    (h_step : ∀ cfg, Inv cfg → ∃ cfg', (cfg [M]⊢⁺ cfg') ∧ Inv cfg')
    (N : Nat) :
    ∃ (m : Nat) (cfg' : Cfg Γ Λ), multiStep M (init []) (N + m) = some cfg' ∧ Inv cfg' := by
  induction N with
  | zero =>
    obtain ⟨cfg₀, ⟨n₀, hn₀⟩, h_inv₀⟩ := h_init
    refine ⟨n₀, cfg₀, ?_, h_inv₀⟩
    rwa [Nat.zero_add]
  | succ N ih =>
    obtain ⟨m, cfg₁, hm, h_inv₁⟩ := ih
    cases m with
    | zero =>
      obtain ⟨cfg₂, ⟨k, hk_pos, hk⟩, h_inv₂⟩ := h_step cfg₁ h_inv₁
      cases k with
      | zero => omega
      | succ k' =>
        refine ⟨k', cfg₂, ?_, h_inv₂⟩
        have h_trans := multiStep_trans M (init []) cfg₁ cfg₂ N (k' + 1) hm hk
        have h_eq : (N + 1) + k' = N + (k' + 1) := by omega
        rwa [h_eq]
    | succ m' =>
      refine ⟨m', cfg₁, ?_, h_inv₁⟩
      have h_eq : (N + 1) + m' = N + (m' + 1) := by omega
      rwa [h_eq]

theorem closed_inv_does_not_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ cfg₀, ((init []) [M]⊢* cfg₀) ∧ Inv cfg₀)
    (h_step : ∀ cfg, Inv cfg → ∃ cfg', (cfg [M]⊢⁺ cfg') ∧ Inv cfg') :
    IsNotHalt M := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome M (init []) cfg cfg' n m hn hnm

-- State abbreviations for 1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD---
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

-- List rotation lemmas
lemma list_one_append_01_pow (k : Nat) :
    ([1] : List (Fin 2)) ++ (([0, 1] : List (Fin 2)) ^ k) = (([1, 0] : List (Fin 2)) ^ k) ++ [1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, pow_succ_list]
    rw [← List.append_assoc ([1] : List (Fin 2)) [0, 1], List.append_assoc ([1, 0] : List (Fin 2))]
    change ([1, 0] : List (Fin 2)) ++ ([1] ++ ([0, 1] : List (Fin 2)) ^ k) =
      ([1, 0] : List (Fin 2)) ++ ((([1, 0] : List (Fin 2)) ^ k) ++ [1])
    rw [ih]

lemma list_zero_append_10_pow (k : Nat) :
    ([0] : List (Fin 2)) ++ (([1, 0] : List (Fin 2)) ^ k) = (([0, 1] : List (Fin 2)) ^ k) ++ [0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, pow_succ_list]
    rw [← List.append_assoc ([0] : List (Fin 2)) [1, 0], List.append_assoc ([0, 1] : List (Fin 2))]
    change ([0, 1] : List (Fin 2)) ++ ([0] ++ ([1, 0] : List (Fin 2)) ^ k) =
      ([0, 1] : List (Fin 2)) ++ ((([0, 1] : List (Fin 2)) ^ k) ++ [0])
    rw [ih]

lemma rotR_1_01 (k : Nat) (r : ListBlank (Fin 2)) :
    ([1] : List (Fin 2)) +> ((([0, 1] : List (Fin 2)) ^ k) +> r) =
    ((([1, 0] : List (Fin 2)) ^ k) +> (([1] : List (Fin 2)) +> r)) := by
  rw [listblank_append_append, list_one_append_01_pow, ← listblank_append_append]

lemma rotR_01_0 (k : Nat) (r : ListBlank (Fin 2)) :
    ((([0, 1] : List (Fin 2)) ^ k) +> (([0] : List (Fin 2)) +> r)) =
    ([0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ k) +> r) := by
  rw [listblank_append_append, ← list_zero_append_10_pow, ← listblank_append_append]

lemma rotL_10_0_default (k : Nat) :
    ((default : ListBlank (Fin 2)) <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [0] =
    (default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ k) := by
  rw [listblank_append_append, list_zero_append_10_pow, ← listblank_append_append]
  have h0 : (default : ListBlank (Fin 2)) <+ [0] = default := by
    simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]
  rw [h0]

-- The 5 shift lemmas
lemma shiftR_D_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) {{D}}> r) := by
  induction k generalizing l r with
  | zero => simp only [pow_zero_list, listblank_append_nil]; exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{D}}> ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r))) [target_tm]⊢*
        ((l <+ [1, 0]) {{D}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by execute
    have h2 := ih (l <+ [1, 0]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

lemma shiftR_C_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{C}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((l <+ (([0, 1] : List (Fin 2)) ^ k)) {{C}}> r) := by
  induction k generalizing l r with
  | zero => simp only [pow_zero_list, listblank_append_nil]; exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{C}}> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> r))) [target_tm]⊢*
        ((l <+ [0, 1]) {{C}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by execute
    have h2 := ih (l <+ [0, 1]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

lemma shiftL_B_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([0, 1] : List (Fin 2)) ^ k)) <{{B}} r) [target_tm]⊢*
    (l <{{B}} ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => simp only [pow_zero_list, listblank_append_nil]; exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_left]
    have h1 : (((l <+ (([0, 1] : List (Fin 2)) ^ k)) <+ [0, 1]) <{{B}} r) [target_tm]⊢*
        ((l <+ (([0, 1] : List (Fin 2)) ^ k)) <{{B}} ([0, 1] +> r)) := by execute
    have h2 := ih l ([0, 1] +> r)
    rw [pow_succ_append_right'] at h2
    exact stepStar_trans h1 h2

lemma shiftL_C_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{C}} r) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => simp only [pow_zero_list, listblank_append_nil]; exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_left]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [1, 0]) <{{C}} r) [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{C}} ([1, 0] +> r)) := by execute
    have h2 := ih l ([1, 0] +> r)
    rw [pow_succ_append_right'] at h2
    exact stepStar_trans h1 h2

lemma shiftL6_B_10_look1 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{B}} ([1] +> r)) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ k) +> ([1] +> r))) := by
  induction k generalizing l r with
  | zero => simp only [pow_zero_list, listblank_append_nil]; exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_left]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [1, 0]) <{{B}} ([1] +> r)) [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{B}} ([1] +> ([0, 1] +> r))) := by execute
    have h2 := ih l ([0, 1] +> r)
    have hr : ([1] : List (Fin 2)) +> ([0, 1] +> r) = [1, 0] +> ([1] +> r) := rfl
    rw [← pow_succ_append_right' ([1, 0] : List (Fin 2)) k ([1] +> r)]
    rw [← hr]
    exact stepStar_trans h1 h2
-- The 14 low-level sweep lemmas
lemma Start (h : Nat) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) <{{C}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    (((((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) {{D}}> r) := by
  have s1 : ((default : ListBlank (Fin 2)) <{{C}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> r))) [target_tm]⊢⁺
      ((default <+ [1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> r))) := by execute
  have s2 := shiftR_D_10 h (default <+ [1]) ([1, 1, 0, 0, 1] +> r)
  have s3 : (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ h)) {{D}}> ([1, 1, 0, 0, 1] +> r)) [target_tm]⊢*
      (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ h)) <{{C}} ([1, 0, 0, 0, 1] +> r)) := by execute
  have s4 := shiftL_C_10 h (default <+ [1]) ([1, 0, 0, 0, 1] +> r)
  have s5 : ((default <+ [1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 0, 0, 0, 1] +> r))) [target_tm]⊢*
      ((default <+ [1, 0, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 0, 0, 0, 1] +> r))) := by execute
  have s6 := shiftR_D_10 h (default <+ [1, 0, 1]) ([1, 0, 0, 0, 1] +> r)
  have s7 : (((default <+ [1, 0, 1]) <+ (([1, 0] : List (Fin 2)) ^ h)) {{D}}> ([1, 0, 0, 0, 1] +> r)) [target_tm]⊢*
      (((default <+ [1, 0, 1]) <+ (([1, 0] : List (Fin 2)) ^ h)) <{{C}} ([1, 1, 0, 1, 0] +> r)) := by execute
  have s8 := shiftL_C_10 h (default <+ [1, 0, 1]) ([1, 1, 0, 1, 0] +> r)
  have s9 : ((default <+ [1, 0, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 1, 0] +> r))) [target_tm]⊢*
      ((default <+ [1, 0, 1, 0, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 1, 0] +> r))) := by execute
  have s10 := shiftR_D_10 h (default <+ [1, 0, 1, 0, 1]) ([1, 1, 0, 1, 0] +> r)
  have s11 : (((default <+ [1, 0, 1, 0, 1]) <+ (([1, 0] : List (Fin 2)) ^ h)) {{D}}> ([1, 1, 0, 1, 0] +> r)) [target_tm]⊢*
      (((default <+ [1, 0, 1, 0, 1]) <+ (([1, 0] : List (Fin 2)) ^ h)) <{{C}} ([1, 0, 0, 1, 0] +> r)) := by execute
  have s12 := shiftL_C_10 h (default <+ [1, 0, 1, 0, 1]) ([1, 0, 0, 1, 0] +> r)
  have s13 : ((default <+ [1, 0, 1, 0, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 0, 0, 1, 0] +> r))) [target_tm]⊢*
      ((default <+ [1, 0, 1, 0, 1, 0, 1, 0]) {{D}}> ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 0, 0, 1, 0] +> r))) := by execute
  have h13_eq : ((default : ListBlank (Fin 2)) <+ [1, 0, 1, 0, 1, 0, 1, 0]) =
      ((default : ListBlank (Fin 2)) <+ (([1, 0] : List (Fin 2)) ^ 4)) := rfl
  rw [h13_eq] at s13
  have s14 := shiftR_D_10 h (default <+ (([1, 0] : List (Fin 2)) ^ 4)) ([1, 0, 0, 1, 0] +> r)
  rw [← pow_add_append_left default ([1, 0] : List (Fin 2)) 4 h] at s14
  have s15 : (((default : ListBlank (Fin 2)) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) {{D}}> ([1, 0, 0, 1, 0] +> r)) [target_tm]⊢*
      ((((((default : ListBlank (Fin 2)) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) <+ [0]) <+ [1, 1, 1]) <+ [0]) {{D}}> r) := by execute
  rw [rotL_10_0_default (4 + h)] at s15
  exact stepPlus_stepStar_stepPlus s1
    (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 (stepStar_trans s5
    (stepStar_trans s6 (stepStar_trans s7 (stepStar_trans s8 (stepStar_trans s9
    (stepStar_trans s10 (stepStar_trans s11 (stepStar_trans s12 (stepStar_trans s13
    (stepStar_trans s14 s15)))))))))))))

lemma PassR (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) [target_tm]⊢*
    (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <+ [0]) {{D}}> r) := by
  rw [pow_succ_append_right]
  have s1 := shiftR_D_10 p (l <+ [0]) ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 1, 0] +> r)))
  have s2 : (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) {{D}}> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 1, 0] +> r)))) [target_tm]⊢*
      ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1]) {{F}}> ((([0, 1] : List (Fin 2)) ^ q) +> ([0] +> ([0, 1, 0] +> r)))) := by execute
  rw [rotR_01_0 q ([0, 1, 0] +> r)] at s2
  have s3 : ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1]) {{F}}> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([0, 1, 0] +> r)))) [target_tm]⊢*
      ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ q) +> ([0, 1, 0] +> r))) := by execute
  have s4 := shiftR_D_10 q (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) ([0, 1, 0] +> r)
  have s5 : (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) {{D}}> ([0, 1, 0] +> r)) [target_tm]⊢*
      (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <+ [0]) {{D}}> r) := by execute
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 s5)))

lemma Borrow (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    (l {{D}}> ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ (q + 2)) +> ([0, 0, 0, 1] +> r)))) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) := by
  rw [pow_succ_append_right ([0, 1] : List (Fin 2)) (q + 1), pow_succ_append_right ([0, 1] : List (Fin 2)) q]
  have s1 := shiftR_D_10 p l ([0, 1] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 0, 1] +> r))))
  have s2 : ((l <+ (([1, 0] : List (Fin 2)) ^ p)) {{D}}> ([0, 1] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 0, 1] +> r))))) [target_tm]⊢*
      (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 0, 1, 1]) {{C}}> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 0, 1] +> r))) := by execute
  have s3 := shiftR_C_01 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 0, 1, 1]) ([0, 0, 0, 1] +> r)
  have s4 : ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 0, 1, 1]) <+ (([0, 1] : List (Fin 2)) ^ q)) {{C}}> ([0, 0, 0, 1] +> r)) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 0, 1, 1]) <+ (([0, 1] : List (Fin 2)) ^ q)) <{{B}} ([1, 0, 1, 0] +> r)) := by execute
  have s5 := shiftL_B_01 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 0, 1, 1]) ([1, 0, 1, 0] +> r)
  have s6 : (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 0, 1, 1]) <{{B}} ((([0, 1] : List (Fin 2)) ^ q) +> ([1, 0, 1, 0] +> r))) [target_tm]⊢*
      (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1, 1]) {{C}}> ((([0, 1] : List (Fin 2)) ^ q) +> ([1, 0, 1, 0] +> r))) := by execute
  have s7 := shiftR_C_01 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1, 1]) ([1, 0, 1, 0] +> r)
  have s8 : ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1, 1]) <+ (([0, 1] : List (Fin 2)) ^ q)) {{C}}> ([1, 0, 1, 0] +> r)) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1, 1]) <+ (([0, 1] : List (Fin 2)) ^ q)) <{{B}} ([0, 0, 1, 0] +> r)) := by execute
  have s9 := shiftL_B_01 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1, 1]) ([0, 0, 1, 0] +> r)
  have s10 : (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1, 1]) <{{B}} ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 1, 0] +> r))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 1, 0] +> r)))))) := by execute
  have s11 := shiftL6_B_10_look1 p l ([0] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 1, 0] +> r))))
  have hr : ([1] : List (Fin 2)) +> ([0] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ([0, 0, 1, 0] +> r)))) =
      [1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)) := by
    rw [pow_succ_append_right]; rfl
  rw [← pow_succ_append_right' ([1, 0] : List (Fin 2)) p, ← hr]
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 (stepStar_trans s5
    (stepStar_trans s6 (stepStar_trans s7 (stepStar_trans s8 (stepStar_trans s9 (stepStar_trans s10 s11)))))))))

lemma PassL (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) <{{B}} r) [target_tm]⊢*
    ((l <+ [0]) <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r)))) := by
  rw [pow_succ_append_left _ ([1, 0] : List (Fin 2)) q]
  have s1 : ((((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 0]) <+ [1, 1]) <+ [0]) <{{B}} r) [target_tm]⊢*
      (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{C}} ([1, 1, 0, 0, 1] +> r)) := by execute
  have s2 := shiftL_C_10 q (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) ([1, 1, 0, 0, 1] +> r)
  have s3 : ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 1, 0, 0, 1] +> r))) [target_tm]⊢*
      ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 1, 0, 0, 1] +> r))) := by execute
  have s4 := shiftR_D_10 q (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) ([1, 1, 0, 0, 1] +> r)
  have s5 : (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) {{D}}> ([1, 1, 0, 0, 1] +> r)) [target_tm]⊢*
      (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{C}} ([1, 0, 0, 0, 1] +> r)) := by execute
  have s6 := shiftL_C_10 q (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) ([1, 0, 0, 0, 1] +> r)
  have s7 : ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 0, 0, 0, 1] +> r))) [target_tm]⊢*
      (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 0, 1] +> r))))))) := by execute
  have s8 := shiftL6_B_10_look1 p (l <+ [0]) ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 0, 1] +> r)))))
  have hr : ([1] : List (Fin 2)) +> ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 0, 1] +> r))))) =
      [1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r)) := by
    rw [← rotR_01_0 q ([1] +> ([0, 0, 0, 1] +> r))]
    have h01 : ([0] : List (Fin 2)) +> ([1] +> ([0, 0, 0, 1] +> r)) = [0, 1] +> ([0, 0, 0, 1] +> r) := rfl
    rw [h01, pow_succ_append_right']; rfl
  rw [← pow_succ_append_right' ([1, 0] : List (Fin 2)) p, ← hr]
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4
    (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7 s8))))))

lemma EndPh (h : Nat) (r : ListBlank (Fin 2)) :
    (((((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) <{{B}} r) [target_tm]⊢*
    ((default : ListBlank (Fin 2)) <{{C}} ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ([1, 1, 0, 0, 1] +> r))) := by
  have s1 : (((((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) <{{B}} r) [target_tm]⊢*
      (((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <{{B}} ([1, 0, 0, 1] +> r)) := by execute
  have s2 := shiftL_B_01 (4 + h) default ([1, 0, 0, 1] +> r)
  have s3 : ((default : ListBlank (Fin 2)) <{{B}} ((([0, 1] : List (Fin 2)) ^ (4 + h)) +> ([1, 0, 0, 1] +> r))) [target_tm]⊢*
      ((default : ListBlank (Fin 2)) <{{C}} ([1] +> ((([0, 1] : List (Fin 2)) ^ (4 + h)) +> ([1, 0, 0, 1] +> r)))) := by execute
  rw [rotR_1_01 (4 + h) ([1, 0, 0, 1] +> r)] at s3
  exact stepStar_trans s1 (stepStar_trans s2 s3)

lemma EndT (l : ListBlank (Fin 2)) (p q : Nat) :
    ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{D}}> default) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))) := by
  rw [pow_succ_append_left _ ([1, 0] : List (Fin 2)) q]
  have s1 : (((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 0]) <+ [1, 1]) <+ [0]) {{D}}> default) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{C}} ([1, 1, 0, 1, 0, 1, 0, 1] +> default)) := by execute
  have s2 := shiftL_C_10 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) ([1, 1, 0, 1, 0, 1, 0, 1] +> default)
  have s3 : (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 1, 0, 1, 0, 1, 0, 1] +> default))) [target_tm]⊢*
      (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 1, 0, 1, 0, 1, 0, 1] +> default))) := by execute
  have s4 := shiftR_D_10 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) ([1, 1, 0, 1, 0, 1, 0, 1] +> default)
  have s5 : ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) {{D}}> ([1, 1, 0, 1, 0, 1, 0, 1] +> default)) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{C}} ([1, 0, 0, 1, 0, 1, 0, 1] +> default)) := by execute
  have s6 := shiftL_C_10 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) ([1, 0, 0, 1, 0, 1, 0, 1] +> default)
  have s7 : (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 0, 0, 1, 0, 1, 0, 1] +> default))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default)))))))) := by execute
  have s8 := shiftL6_B_10_look1 p l ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))))
  have hr : ([1] : List (Fin 2)) +> ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default)))))) =
      [1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))) := by
    rw [← rotR_01_0 q ([1] +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default)))]
    have h01 : ([0] : List (Fin 2)) +> ([1] +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))) = [0, 1] +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default)) := rfl
    rw [h01, pow_succ_append_right']; rfl
  rw [← pow_succ_append_right' ([1, 0] : List (Fin 2)) p, ← hr]
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4
    (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7 s8))))))

lemma EndLastT (l : ListBlank (Fin 2)) (p : Nat) :
    (((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) {{D}}> default) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + 4)) +> ([1] +> default))) := by
  have s1 : (((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) {{D}}> default) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0, 1, 0, 1, 0, 1, 0, 1] +> default))) := by execute
  have s2 := shiftL6_B_10_look1 p l ([0, 1, 0, 1, 0, 1, 0, 1] +> default)
  have hr : ([1] : List (Fin 2)) +> ([0, 1, 0, 1, 0, 1, 0, 1] +> default) =
      (([1, 0] : List (Fin 2)) ^ 4) +> ([1] +> default) := rfl
  rw [pow_add_append_right ([1, 0] : List (Fin 2)) p 4, ← hr]
  exact stepStar_trans s1 s2

lemma MergeB (l : ListBlank (Fin 2)) (p p' : Nat) (r : ListBlank (Fin 2)) :
    (l {{D}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r))))) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + p' + 3)) +> r)) := by
  have s1 := shiftR_D_10 p l ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))
  have s2 : ((l <+ (([1, 0] : List (Fin 2)) ^ p)) {{D}}> ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0, 1, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))) := by execute
  have s3 := shiftL6_B_10_look1 p l ([0, 1, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ p') +> r))
  have hr : ([1] : List (Fin 2)) +> ([0, 1, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ p') +> r)) =
      (([1, 0] : List (Fin 2)) ^ 3) +> ((([1, 0] : List (Fin 2)) ^ p') +> r) := rfl
  have hp : p + p' + 3 = p + (3 + p') := by omega
  rw [hp, pow_add_append_right ([1, 0] : List (Fin 2)) p (3 + p'), pow_add_append_right ([1, 0] : List (Fin 2)) 3 p', ← hr]
  exact stepStar_trans s1 (stepStar_trans s2 s3)

lemma MergeE (l : ListBlank (Fin 2)) (p : Nat) :
    (l {{D}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([0, 1] +> ([0, 0, 0, 1] +> default)))) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + 2)) +> ([1] +> default))) := by
  have s1 := shiftR_D_10 p l ([0, 1] +> ([0, 0, 0, 1] +> default))
  have s2 : ((l <+ (([1, 0] : List (Fin 2)) ^ p)) {{D}}> ([0, 1] +> ([0, 0, 0, 1] +> default))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0, 1, 0, 1] +> default))) := by execute
  have s3 := shiftL6_B_10_look1 p l ([0, 1, 0, 1] +> default)
  have hr : ([1] : List (Fin 2)) +> ([0, 1, 0, 1] +> default) =
      (([1, 0] : List (Fin 2)) ^ 2) +> ([1] +> default) := rfl
  rw [pow_add_append_right ([1, 0] : List (Fin 2)) p 2, ← hr]
  exact stepStar_trans s1 (stepStar_trans s2 s3)

lemma OvT (l : ListBlank (Fin 2)) (t : Nat) :
    ((l <+ [0]) {{D}}> ((([1, 0] : List (Fin 2)) ^ t) +> ([1] +> default))) [target_tm]⊢*
    (l <{{B}} ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default))) := by
  have s1 := shiftR_D_10 t (l <+ [0]) ([1] +> default)
  have s2 : (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ t)) {{D}}> ([1] +> default)) [target_tm]⊢*
      (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ t)) <{{C}} ([1, 1, 0, 0, 1] +> default)) := by execute
  have s3 := shiftL_C_10 t (l <+ [0]) ([1, 1, 0, 0, 1] +> default)
  have s4 : ((l <+ [0]) <{{C}} ((([1, 0] : List (Fin 2)) ^ t) +> ([1, 1, 0, 0, 1] +> default))) [target_tm]⊢*
      ((l <+ [1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ t) +> ([1, 1, 0, 0, 1] +> default))) := by execute
  have s5 := shiftR_D_10 t (l <+ [1]) ([1, 1, 0, 0, 1] +> default)
  have s6 : (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ t)) {{D}}> ([1, 1, 0, 0, 1] +> default)) [target_tm]⊢*
      (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ t)) <{{C}} ([1, 0, 0, 0, 1] +> default)) := by execute
  have s7 := shiftL_C_10 t (l <+ [1]) ([1, 0, 0, 0, 1] +> default)
  have s8 : ((l <+ [1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ t) +> ([1, 0, 0, 0, 1] +> default))) [target_tm]⊢*
      (l <{{B}} ([0] +> ((([1, 0] : List (Fin 2)) ^ t) +> ([1] +> ([0, 0, 0, 1] +> default))))) := by execute
  rw [← rotR_01_0 t ([1] +> ([0, 0, 0, 1] +> default))] at s8
  have h01 : ([0] : List (Fin 2)) +> ([1] +> ([0, 0, 0, 1] +> default)) = [0, 1] +> ([0, 0, 0, 1] +> default) := rfl
  rw [h01, pow_succ_append_right'] at s8
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4
    (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7 s8))))))

lemma OvL (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <{{B}} r) [target_tm]⊢*
    (l <{{B}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))) := by
  rw [pow_succ_append_left _ ([1, 0] : List (Fin 2)) p]
  have s1 : (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 0]) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <{{B}} r) [target_tm]⊢*
      ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 0]) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{B}} ([1] +> ([0] +> r))) := by execute
  have s2 := shiftL6_B_10_look1 q ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 0]) <+ [0, 1, 1]) ([0] +> r)
  have hq : ([1] : List (Fin 2)) +> ([0] +> r) = [1, 0] +> r := rfl
  rw [hq, pow_succ_append_right' ([1, 0] : List (Fin 2)) q r] at s2
  have s3 : (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 0]) <+ [0, 1, 1]) <{{B}} ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)) [target_tm]⊢*
      (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <{{C}} ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))) := by execute
  have s4 := shiftL_C_10 p (l <+ [0]) ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))
  have s5 : ((l <+ [0]) <{{C}} ((([1, 0] : List (Fin 2)) ^ p) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))) [target_tm]⊢*
      ((l <+ [1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))) := by execute
  have s6 := shiftR_D_10 p (l <+ [1]) ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))
  have s7 : (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ p)) {{D}}> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))) [target_tm]⊢*
      (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ p)) <{{C}} ([1, 0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))) := by execute
  have s8 := shiftL_C_10 p (l <+ [1]) ([1, 0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))
  have s9 : ((l <+ [1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ p) +> ([1, 0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))) [target_tm]⊢*
      (l <{{B}} ([0] +> ((([1, 0] : List (Fin 2)) ^ p) +> ([1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))))) := by execute
  rw [← rotR_01_0 p ([1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))] at s9
  have h01 : ([0] : List (Fin 2)) +> ([1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))) =
      [0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)) := rfl
  rw [h01, pow_succ_append_right'] at s9
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4
    (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7 (stepStar_trans s8 s9)))))))

lemma OvEnd (h p : Nat) (r : ListBlank (Fin 2)) :
    ((((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <{{B}} ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))) [target_tm]⊢*
    ((default : ListBlank (Fin 2)) <{{C}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))))) := by
  have hp2 : ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r)) =
      [0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)) := by
    rw [pow_succ_append_right ([0, 1] : List (Fin 2)) (p + 1), pow_succ_append_right ([0, 1] : List (Fin 2)) p]; rfl
  rw [hp2]
  have s1 : ((((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <{{B}} ([0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)))) [target_tm]⊢*
      (((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <{{E}} ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)))) := by execute
  have s2 : ((((default : ListBlank (Fin 2)) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) <+ [0]) <{{E}} ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)))) [target_tm]⊢*
      (((default : ListBlank (Fin 2)) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) <{{B}} ([1] +> ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r))))) := by execute
  rw [rotL_10_0_default (4 + h)] at s2
  have s3 := shiftL6_B_10_look1 (4 + h) default ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)))
  have h4h_eq : ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ([1] +> ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r))))) =
      ([1, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (h + 2)) +> ([1] +> ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)))))) := by
    have h4h : 4 + h = 2 + (h + 2) := by omega
    rw [h4h, pow_add_append_right ([1, 0] : List (Fin 2)) 2 (h + 2)]; rfl
  rw [h4h_eq] at s3
  have s4 : ((default : ListBlank (Fin 2)) <{{B}} ([1, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (h + 2)) +> ([1] +> ([0, 1, 0, 0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r))))))) [target_tm]⊢*
      (((default : ListBlank (Fin 2)) <+ [0, 1, 1, 1, 0, 1, 0, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ (h + 2)) +> ([1, 0, 1, 0] +> ([0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r)))))) := by execute
  have h_mid : ((([1, 0] : List (Fin 2)) ^ (h + 2)) +> ([1, 0, 1, 0] +> ([0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r))))) =
      ((([1, 0] : List (Fin 2)) ^ (h + 4)) +> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))) := by
    have ha : ([1, 0, 1, 0] : List (Fin 2)) +> ([0, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> r))) =
        (([1, 0] : List (Fin 2)) ^ 2) +> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r)) := by
      rw [hp2]; rfl
    rw [ha, ← pow_add_append_right]
  rw [h_mid] at s4
  have s5 := Borrow ((default : ListBlank (Fin 2)) <+ [0, 1, 1, 1, 0, 1, 0, 1]) (h + 4) p r
  have s6 : (((default : ListBlank (Fin 2)) <+ [0, 1, 1, 1, 0, 1, 0, 1]) <{{B}} ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))) [target_tm]⊢*
      ((default : ListBlank (Fin 2)) <{{C}} ([1, 0, 1, 0] +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))))) := by execute
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 (stepStar_trans s5 s6))))

lemma X1Sw (l : ListBlank (Fin 2)) (p : Nat) (r : ListBlank (Fin 2)) :
    ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) <{{B}} r) [target_tm]⊢*
    (l <{{B}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> r))) := by
  rw [pow_succ_append_left _ ([1, 0] : List (Fin 2)) p]
  have s1 : (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 0]) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) <{{B}} r) [target_tm]⊢*
      (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <{{C}} ([1, 1, 0, 1, 0, 1, 0, 1] +> r)) := by execute
  have s2 := shiftL_C_10 p (l <+ [0]) ([1, 1, 0, 1, 0, 1, 0, 1] +> r)
  have s3 : ((l <+ [0]) <{{C}} ((([1, 0] : List (Fin 2)) ^ p) +> ([1, 1, 0, 1, 0, 1, 0, 1] +> r))) [target_tm]⊢*
      ((l <+ [1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([1, 1, 0, 1, 0, 1, 0, 1] +> r))) := by execute
  have s4 := shiftR_D_10 p (l <+ [1]) ([1, 1, 0, 1, 0, 1, 0, 1] +> r)
  have s5 : (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ p)) {{D}}> ([1, 1, 0, 1, 0, 1, 0, 1] +> r)) [target_tm]⊢*
      (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ p)) <{{C}} ([1, 0, 0, 1, 0, 1, 0, 1] +> r)) := by execute
  have s6 := shiftL_C_10 p (l <+ [1]) ([1, 0, 0, 1, 0, 1, 0, 1] +> r)
  have s7 : ((l <+ [1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ p) +> ([1, 0, 0, 1, 0, 1, 0, 1] +> r))) [target_tm]⊢*
      (l <{{B}} ([0] +> ((([1, 0] : List (Fin 2)) ^ p) +> ([1] +> ([0, 0, 1, 0, 1, 0, 1] +> r))))) := by execute
  rw [← rotR_01_0 p ([1] +> ([0, 0, 1, 0, 1, 0, 1] +> r))] at s7
  have h01 : ([0] : List (Fin 2)) +> ([1] +> ([0, 0, 1, 0, 1, 0, 1] +> r)) = [0, 1] +> ([0, 0, 1, 0, 1, 0, 1] +> r) := rfl
  rw [h01, pow_succ_append_right'] at s7
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4
    (stepStar_trans s5 (stepStar_trans s6 s7)))))

lemma X2T (l : ListBlank (Fin 2)) (p q k : Nat) :
    ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{D}}> ([1, 0, 1, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> default))) [target_tm]⊢*
    (l <{{B}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))))) := by
  rw [pow_succ_append_left _ ([1, 0] : List (Fin 2)) q, pow_succ_append_right ([0, 1] : List (Fin 2)) k]
  set lq := (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q))
  have s1 : ((((lq <+ [1, 0]) <+ [1, 1]) <+ [0]) {{D}}> ([1, 0, 1, 1, 0, 1] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> default)))) [target_tm]⊢*
      ((lq <+ [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) {{C}}> ((([0, 1] : List (Fin 2)) ^ k) +> default)) := by execute
  have s2 := shiftR_C_01 k (lq <+ [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) default
  have s3 : (((lq <+ [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) <+ (([0, 1] : List (Fin 2)) ^ k)) {{C}}> default) [target_tm]⊢*
      (((lq <+ [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) <+ (([0, 1] : List (Fin 2)) ^ k)) <{{B}} ([1, 0, 0, 1] +> default)) := by execute
  have s4 := shiftL_B_01 k (lq <+ [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) ([1, 0, 0, 1] +> default)
  have s5 : ((lq <+ [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) <{{B}} ((([0, 1] : List (Fin 2)) ^ k) +> ([1, 0, 0, 1] +> default))) [target_tm]⊢*
      ((lq <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) {{C}}> ((([0, 1] : List (Fin 2)) ^ k) +> ([1, 0, 0, 1] +> default))) := by execute
  have s6 := shiftR_C_01 k (lq <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) ([1, 0, 0, 1] +> default)
  have s7 : (((lq <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) <+ (([0, 1] : List (Fin 2)) ^ k)) {{C}}> ([1, 0, 0, 1] +> default)) [target_tm]⊢*
      (((lq <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) <+ (([0, 1] : List (Fin 2)) ^ k)) <{{B}} ([0, 0, 0, 1] +> default)) := by execute
  have s8 := shiftL_B_01 k (lq <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) ([0, 0, 0, 1] +> default)
  have s9 : ((lq <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) <{{B}} ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))) [target_tm]⊢*
      (lq <{{C}} ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))) := by execute
  have s10 := shiftL_C_10 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))
  have s11 : (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))) [target_tm]⊢*
      (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) {{D}}> ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))) := by execute
  have s12 := shiftR_D_10 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))
  have s13 : ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) {{D}}> ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{C}} ([1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))) := by execute
  have s14 := shiftL_C_10 q ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) ([1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))
  have s15 : (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [1, 1, 1]) <{{C}} ((([1, 0] : List (Fin 2)) ^ q) +> ([1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{B}} ([1] +> ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))))))))) := by execute
  have s16 := shiftL6_B_10_look1 p l ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))))))))
  have hr : ([1] : List (Fin 2)) +> ([0] +> ([0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([1] +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))))))) =
      [1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))))) := by
    rw [← rotR_01_0 q ([1] +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))))]
    have h01 : ([0] : List (Fin 2)) +> ([1] +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default)))))) =
        [0, 1] +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> ([0, 0, 0, 1] +> default))))) := rfl
    rw [h01, pow_succ_append_right']; rfl
  rw [pow_succ_append_right ([0, 1] : List (Fin 2)) k, ← pow_succ_append_right' ([1, 0] : List (Fin 2)) p, ← hr]
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4
    (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7 (stepStar_trans s8
    (stepStar_trans s9 (stepStar_trans s10 (stepStar_trans s11 (stepStar_trans s12
    (stepStar_trans s13 (stepStar_trans s14 (stepStar_trans s15 s16))))))))))))))
-- The family K and macro rules (Skelet1LikeC2_1RB1RF.v lines 104-360)
abbrev Tri := Nat × Nat × Bool

def sd (d : Bool) : List (Fin 2) :=
  if d then [0, 0, 0, 1] else [0, 0, 1, 0]

def RP : List Tri → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | (p, q, d) :: P', r =>
    ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ q) +> (sd d +> RP P' r)))

inductive Tl where
  | TN
  | TA (t : Nat)
  | TB (k : Nat)

def RT : Tl → ListBlank (Fin 2)
  | .TN => default
  | .TA t => ((([1, 0] : List (Fin 2)) ^ t) +> ([1] +> default))
  | .TB k => ([1, 0, 1, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> default))

def K (h : Nat) (P : List Tri) (T : Tl) : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) <{{C}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> RP P (RT T)))

def reg (p q : Nat) (l : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q - 1))) <+ [1, 1])

def LP : List Tri → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], l => l
  | (p, q, _) :: Z', l => LP Z' (reg p q l)

def OvR : List Tri → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | (p, q, _) :: Z', r =>
    ((([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ q) +> OvR Z' r)))

def touch (x : Tri) : Tri :=
  match x with
  | (p, q, d) => (p + 1, q - 1, !d)

abbrev okR (x : Tri) : Prop := x.2.2 = false ∧ 1 ≤ x.2.1

abbrev okL (x : Tri) : Prop := x.2.2 = false ∧ 2 ≤ x.2.1

abbrev okO (x : Tri) : Prop := 1 ≤ x.1 ∧ 1 ≤ x.2.1

lemma RP_app (Z W : List Tri) (r : ListBlank (Fin 2)) :
    RP (Z ++ W) r = RP Z (RP W r) := by
  induction Z with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    simp only [List.cons_append, RP, ih]

lemma LP_app (Z W : List Tri) (l : ListBlank (Fin 2)) :
    LP (Z ++ W) l = LP W (LP Z l) := by
  induction Z generalizing l with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    simp only [List.cons_append, LP, ih]

lemma PassesR (Z : List Tri) (hZ : List.Forall okR Z) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> RP Z r) [target_tm]⊢* ((LP Z l <+ [0]) {{D}}> r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨⟨rfl, hq⟩, hZ'⟩
    dsimp at hq
    cases q with
    | zero => omega
    | succ q =>
      dsimp [RP, LP, sd]
      have h1 := PassR l p q (RP Z r)
      have h2 := ih hZ' (reg p (q + 1) l) r
      dsimp [reg] at h2
      exact stepStar_trans h1 h2

lemma PassesL (Z : List Tri) (hZ : List.Forall okL Z) (l r : ListBlank (Fin 2)) :
    ((LP Z l <+ [0]) <{{B}} r) [target_tm]⊢* ((l <+ [0]) <{{B}} RP (Z.map touch) r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨⟨rfl, hq⟩, hZ'⟩
    dsimp at hq
    cases q with
    | zero => omega
    | succ q =>
      cases q with
      | zero => omega
      | succ q =>
        dsimp [LP, RP, List.map, touch, sd]
        have h1 := ih hZ' (reg p (q + 2) l) r
        have h2 := PassL l p q (RP (Z.map touch) r)
        dsimp [reg] at h1
        exact stepStar_trans h1 h2

lemma OvPasses (Z : List Tri) (hZ : List.Forall okO Z) (l r : ListBlank (Fin 2)) :
    (LP Z l <{{B}} r) [target_tm]⊢* (l <{{B}} OvR Z r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨⟨hp, hq⟩, hZ'⟩
    dsimp at hp hq
    cases p with
    | zero => omega
    | succ p =>
      cases q with
      | zero => omega
      | succ q =>
        dsimp [LP, OvR]
        have h1 := ih hZ' (reg (p + 1) (q + 1) l) r
        have h2 := OvL l p q (OvR Z r)
        dsimp [reg] at h1
        exact stepStar_trans h1 h2

lemma okL_R (Z : List Tri) (hZ : List.Forall okL Z) : List.Forall okR Z := by
  induction Z with
  | nil => trivial
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ ⊢
    dsimp [okL, okR] at hZ ⊢
    exact ⟨⟨hZ.1.1, by omega⟩, ih hZ.2⟩

lemma Forall_snoc {α : Type*} (P : α → Prop) (Z : List α) (x : α)
    (hZ : List.Forall P Z) (hx : P x) : List.Forall P (Z ++ [x]) := by
  rw [List.forall_append]
  exact ⟨hZ, by simp [hx]⟩

lemma Dec (h : Nat) (Z : List Tri) (p q : Nat) (R : List Tri) (T : Tl) (hZ : List.Forall okL Z) :
    (K h (Z ++ (p, q + 2, true) :: R) T) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ (p + 1, q + 1, false) :: R) T) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (Borrow _ p q _)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _))))

lemma DecMerge (h : Nat) (Z : List Tri) (p p' q' : Nat) (d' : Bool) (R : List Tri) (T : Tl)
    (hZ : List.Forall okL Z) :
    (K h (Z ++ (p, 1, true) :: (p', q', d') :: R) T) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ (p + p' + 3, q', d') :: R) T) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (MergeB _ p p' _)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _))))

lemma DecMergeTail (h : Nat) (Z : List Tri) (p t : Nat) (hZ : List.Forall okL Z) :
    (K h (Z ++ [(p, 1, true)]) (.TA t)) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch) (.TA (p + t + 3))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (MergeB _ p t _)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _))))

lemma DecMergeEmpty (h : Nat) (Z : List Tri) (p : Nat) (hZ : List.Forall okL Z) :
    (K h (Z ++ [(p, 1, true)]) .TN) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch) (.TA (p + 2))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (MergeE _ p)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _))))

lemma EndR (h : Nat) (Z : List Tri) (p q : Nat) (hZ : List.Forall okL Z) :
    (K h (Z ++ [(p, q + 2, false)]) .TN) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ [(p + 1, q + 1, false)]) (.TA 1)) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (PassR _ p (q + 1) default)
    (stepStar_trans (EndT _ p q)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _)))))

lemma EndLast (h : Nat) (Z : List Tri) (p : Nat) (hZ : List.Forall okL Z) :
    (K h (Z ++ [(p, 1, false)]) .TN) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch) (.TA (p + 4))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (PassR _ p 0 default)
    (stepStar_trans (EndLastT _ p)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _)))))

lemma X2 (h : Nat) (Z : List Tri) (p q k : Nat) (hZ : List.Forall okL Z) :
    (K h (Z ++ [(p, q + 2, false)]) (.TB (k + 1))) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)]) .TN) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) _ _)
    (stepStar_trans (PassR _ p (q + 1) _)
    (stepStar_trans (X2T _ p q k)
    (stepStar_trans (PassesL Z hZ _ _) (EndPh h _)))))

def ovp (q : Nat) : List Tri → Nat → List Tri
  | [], t => [(q, t + 1, true)]
  | (p', q', _) :: Z', t => (q, p', true) :: ovp q' Z' t

lemma ovp_eq (Z : List Tri) (q t : Nat) :
    RP (ovp q Z t) default =
    ((([1, 0] : List (Fin 2)) ^ q) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default))) := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    simp only [ovp, RP, OvR, sd, ↓reduceIte, ih q']

lemma Ov (h p1 q1 : Nat) (Z : List Tri) (t : Nat)
    (hq : 1 ≤ q1) (hR : List.Forall okR Z) (hO : List.Forall okO Z) :
    (K h ((p1 + 2, q1, false) :: Z) (.TA t)) [target_tm]⊢⁺
    (K 2 ((h + 5, p1 + 1, false) :: ovp q1 Z t) .TN) := by
  cases q1 with
  | zero => omega
  | succ q1' =>
    unfold K
    simp only [RP, sd, RT]
    rw [ovp_eq Z (q1' + 1) t]
    exact stepPlus_stepStar_stepPlus (Start h _)
      (stepStar_trans (PassR _ (p1 + 2) q1' _)
      (stepStar_trans (PassesR Z hR _ _)
      (stepStar_trans (OvT _ t)
      (stepStar_trans (OvPasses Z hO _ _)
      (stepStar_trans (OvL _ (p1 + 1) q1' _)
      (OvEnd h p1 _))))))

lemma OvEmpty (h p : Nat) :
    (K h [] (.TA (p + 1))) [target_tm]⊢⁺
    (K 2 [(h + 5, p + 1, false)] .TN) := by
  unfold K
  dsimp [RP, RT, sd]
  have s1 := Start h ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ([1] +> default))
  have s2 := OvT (((default : ListBlank (Fin 2)) <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) (p + 1)
  have s3 := OvEnd h p default
  exact stepPlus_stepStar_stepPlus s1 (stepStar_trans s2 s3)

def ovpX (q : Nat) : List Tri → Nat → List Tri
  | [], pa => [(q, pa, false)]
  | (p', q', _) :: Z', pa => (q, p', true) :: ovpX q' Z' pa

lemma ovpX_eq (Z : List Tri) (q pa : Nat) (r : ListBlank (Fin 2)) :
    RP (ovpX q Z pa) r =
    ((([1, 0] : List (Fin 2)) ^ q) +> OvR Z ((([0, 1] : List (Fin 2)) ^ pa) +> ([0, 0, 1, 0] +> r))) := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    simp only [ovpX, RP, OvR, sd, ↓reduceIte, ih q']

lemma tailB_eq (n : Nat) :
    ([0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (n + 1)) +> ([1] +> default))) =
    ([0, 0, 1, 0] +> RT (.TB n)) := by
  rw [pow_succ_append_right ([1, 0] : List (Fin 2)) n ([1] +> default)]
  rw [← rotR_1_01 n default]
  rfl

lemma X1 (h p1 q1 : Nat) (Z : List Tri) (pa pb : Nat)
    (hq : 1 ≤ q1) (hR : List.Forall okR Z) (hO : List.Forall okO Z) :
    (K h ((p1 + 2, q1, false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) .TN) [target_tm]⊢⁺
    (K 2 ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) (.TB (pb + 3))) := by
  cases q1 with
  | zero => omega
  | succ q1' =>
    unfold K
    simp only [RP, sd]
    rw [RP_app]
    simp only [RP, sd]
    rw [ovpX_eq Z (q1' + 1) (pa + 1) (RT (.TB (pb + 3))), ← tailB_eq (pb + 3)]
    have hpb : pb + 3 + 1 = pb + 4 := by omega
    rw [hpb]
    have htn : RT .TN = default := rfl
    rw [htn]
    exact stepPlus_stepStar_stepPlus (Start h _)
      (stepStar_trans (PassR _ (p1 + 2) q1' _)
      (stepStar_trans (PassesR Z hR _ _)
      (stepStar_trans (PassR _ (pa + 1) 0 _)
      (stepStar_trans (PassR _ pb 0 default)
      (stepStar_trans (EndLastT _ pb)
      (stepStar_trans (X1Sw _ pa _)
      (stepStar_trans (OvPasses Z hO _ _)
      (stepStar_trans (OvL _ (p1 + 1) q1' _)
      (OvEnd h p1 _)))))))))
-- Initial trajectory: 359 steps to K 2 [(9, 1, false)] .TN, then 2 macro steps to K 2 [(11, 13, false)] .TN, then 57 macro steps to base
def cfg_step_33 : Cfg (Fin 2) (Fin 6) :=
  ((default) {{(1 : Fin 6)}}> ([0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] +> default))
def cfg_step_66 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [0, 1, 0, 1, 0, 1, 0, 1]) {{(2 : Fin 6)}}> ([0, 1, 1, 0, 1] +> default))
def cfg_step_99 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) {{(2 : Fin 6)}}> ([1, 1] +> default))
def cfg_step_132 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [0, 1, 0, 1, 0, 1, 0, 1]) {{(2 : Fin 6)}}> ([0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] +> default))
def cfg_step_165 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) {{(3 : Fin 6)}}> ([1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1] +> default))
def cfg_step_198 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]) {{(1 : Fin 6)}}> ([1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1] +> default))
def cfg_step_231 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [1, 1, 1, 0, 1, 0, 1]) {{(4 : Fin 6)}}> ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1] +> default))
def cfg_step_264 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [1, 0, 1, 0, 1]) {{(3 : Fin 6)}}> ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1] +> default))
def cfg_step_297 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1]) {{(2 : Fin 6)}}> ([1, 0, 1] +> default))
def cfg_step_330 : Cfg (Fin 2) (Fin 6) :=
  ((default <+ [1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1]) {{(1 : Fin 6)}}> ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] +> default))

lemma init_to_359 : (init []) [target_tm]⊢* K 2 [(9, 1, false)] .TN := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{(0 : Fin 6)}}> default) := rfl
  rw [h0]
  have c1 : (default {{(0 : Fin 6)}}> default) [target_tm]⊢* cfg_step_33 := by dsimp [cfg_step_33]; execute
  have c2 : cfg_step_33 [target_tm]⊢* cfg_step_66 := by dsimp [cfg_step_33, cfg_step_66]; execute
  have c3 : cfg_step_66 [target_tm]⊢* cfg_step_99 := by dsimp [cfg_step_66, cfg_step_99]; execute
  have c4 : cfg_step_99 [target_tm]⊢* cfg_step_132 := by dsimp [cfg_step_99, cfg_step_132]; execute
  have c5 : cfg_step_132 [target_tm]⊢* cfg_step_165 := by dsimp [cfg_step_132, cfg_step_165]; execute
  have c6 : cfg_step_165 [target_tm]⊢* cfg_step_198 := by dsimp [cfg_step_165, cfg_step_198]; execute
  have c7 : cfg_step_198 [target_tm]⊢* cfg_step_231 := by dsimp [cfg_step_198, cfg_step_231]; execute
  have c8 : cfg_step_231 [target_tm]⊢* cfg_step_264 := by dsimp [cfg_step_231, cfg_step_264]; execute
  have c9 : cfg_step_264 [target_tm]⊢* cfg_step_297 := by dsimp [cfg_step_264, cfg_step_297]; execute
  have c10 : cfg_step_297 [target_tm]⊢* cfg_step_330 := by dsimp [cfg_step_297, cfg_step_330]; execute
  have c11 : cfg_step_330 [target_tm]⊢* K 2 [(9, 1, false)] .TN := by
    dsimp [cfg_step_330, K, RP, RT, sd]; execute
  exact stepStar_trans c1 (stepStar_trans c2 (stepStar_trans c3 (stepStar_trans c4
    (stepStar_trans c5 (stepStar_trans c6 (stepStar_trans c7 (stepStar_trans c8
    (stepStar_trans c9 (stepStar_trans c10 c11)))))))))

lemma init0 : (init []) [target_tm]⊢* K 2 [(11, 13, false)] .TN := by
  have s1 := init_to_359
  have s2 := stepPlus_stepStar (EndLast 2 [] 9 (by decide))
  have s3 := stepPlus_stepStar (OvEmpty 6 12)
  exact stepStar_trans s1 (stepStar_trans s2 s3)

def base : List Tri :=
  [(95, 68, false), (34, 33, true), (10, 15, true), (1, 26, true)]
lemma init_to_base : (init []) [target_tm]⊢* K 2 base .TN := by
  have ms0 := init0
  have ms1 : (K 2 [(11, 13, false)] .TN) [target_tm]⊢* (K 6 [(12, 12, false)] (.TA 1)) :=
    stepPlus_stepStar (EndR 2 [] 11 11 (by decide))
  have ms2 : (K 6 [(12, 12, false)] (.TA 1)) [target_tm]⊢* (K 2 [(11, 11, false), (12, 2, true)] .TN) :=
    stepPlus_stepStar (Ov 6 10 12 [] 1 (by decide) (by decide) (by decide))
  have ms3 : (K 2 [(11, 11, false), (12, 2, true)] .TN) [target_tm]⊢* (K 6 [(12, 10, true), (13, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 2 [(11, 11, false)] 12 0 [] .TN (by decide))
  have ms4 : (K 6 [(12, 10, true), (13, 1, false)] .TN) [target_tm]⊢* (K 10 [(13, 9, false), (13, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 6 [] 12 8 [(13, 1, false)] .TN (by decide))
  have ms5 : (K 10 [(13, 9, false), (13, 1, false)] .TN) [target_tm]⊢* (K 14 [(14, 8, true)] (.TA 17)) :=
    stepPlus_stepStar (EndLast 10 [(13, 9, false)] 13 (by decide))
  have ms6 : (K 14 [(14, 8, true)] (.TA 17)) [target_tm]⊢* (K 18 [(15, 7, false)] (.TA 17)) :=
    stepPlus_stepStar (Dec 14 [] 14 6 [] (.TA 17) (by decide))
  have ms7 : (K 18 [(15, 7, false)] (.TA 17)) [target_tm]⊢* (K 2 [(23, 14, false), (7, 18, true)] .TN) :=
    stepPlus_stepStar (Ov 18 13 7 [] 17 (by decide) (by decide) (by decide))
  have ms8 : (K 2 [(23, 14, false), (7, 18, true)] .TN) [target_tm]⊢* (K 6 [(24, 13, true), (8, 17, false)] .TN) :=
    stepPlus_stepStar (Dec 2 [(23, 14, false)] 7 16 [] .TN (by decide))
  have ms9 : (K 6 [(24, 13, true), (8, 17, false)] .TN) [target_tm]⊢* (K 10 [(25, 12, false), (8, 17, false)] .TN) :=
    stepPlus_stepStar (Dec 6 [] 24 11 [(8, 17, false)] .TN (by decide))
  have ms10 : (K 10 [(25, 12, false), (8, 17, false)] .TN) [target_tm]⊢* (K 14 [(26, 11, true), (9, 16, false)] (.TA 1)) :=
    stepPlus_stepStar (EndR 10 [(25, 12, false)] 8 15 (by decide))
  have ms11 : (K 14 [(26, 11, true), (9, 16, false)] (.TA 1)) [target_tm]⊢* (K 18 [(27, 10, false), (9, 16, false)] (.TA 1)) :=
    stepPlus_stepStar (Dec 14 [] 26 9 [(9, 16, false)] (.TA 1) (by decide))
  have ms12 : (K 18 [(27, 10, false), (9, 16, false)] (.TA 1)) [target_tm]⊢* (K 2 [(23, 26, false), (10, 9, true), (16, 2, true)] .TN) :=
    stepPlus_stepStar (Ov 18 25 10 [(9, 16, false)] 1 (by decide) (by decide) (by decide))
  have ms13 : (K 2 [(23, 26, false), (10, 9, true), (16, 2, true)] .TN) [target_tm]⊢* (K 6 [(24, 25, true), (11, 8, false), (16, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 2 [(23, 26, false)] 10 7 [(16, 2, true)] .TN (by decide))
  have ms14 : (K 6 [(24, 25, true), (11, 8, false), (16, 2, true)] .TN) [target_tm]⊢* (K 10 [(25, 24, false), (11, 8, false), (16, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 6 [] 24 23 [(11, 8, false), (16, 2, true)] .TN (by decide))
  have ms15 : (K 10 [(25, 24, false), (11, 8, false), (16, 2, true)] .TN) [target_tm]⊢* (K 14 [(26, 23, true), (12, 7, true), (17, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 10 [(25, 24, false), (11, 8, false)] 16 0 [] .TN (by decide))
  have ms16 : (K 14 [(26, 23, true), (12, 7, true), (17, 1, false)] .TN) [target_tm]⊢* (K 18 [(27, 22, false), (12, 7, true), (17, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 14 [] 26 21 [(12, 7, true), (17, 1, false)] .TN (by decide))
  have ms17 : (K 18 [(27, 22, false), (12, 7, true), (17, 1, false)] .TN) [target_tm]⊢* (K 22 [(28, 21, true), (13, 6, false), (17, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 18 [(27, 22, false)] 12 5 [(17, 1, false)] .TN (by decide))
  have ms18 : (K 22 [(28, 21, true), (13, 6, false), (17, 1, false)] .TN) [target_tm]⊢* (K 26 [(29, 20, false), (13, 6, false), (17, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 22 [] 28 19 [(13, 6, false), (17, 1, false)] .TN (by decide))
  have ms19 : (K 26 [(29, 20, false), (13, 6, false), (17, 1, false)] .TN) [target_tm]⊢* (K 30 [(30, 19, true), (14, 5, true)] (.TA 21)) :=
    stepPlus_stepStar (EndLast 26 [(29, 20, false), (13, 6, false)] 17 (by decide))
  have ms20 : (K 30 [(30, 19, true), (14, 5, true)] (.TA 21)) [target_tm]⊢* (K 34 [(31, 18, false), (14, 5, true)] (.TA 21)) :=
    stepPlus_stepStar (Dec 30 [] 30 17 [(14, 5, true)] (.TA 21) (by decide))
  have ms21 : (K 34 [(31, 18, false), (14, 5, true)] (.TA 21)) [target_tm]⊢* (K 38 [(32, 17, true), (15, 4, false)] (.TA 21)) :=
    stepPlus_stepStar (Dec 34 [(31, 18, false)] 14 3 [] (.TA 21) (by decide))
  have ms22 : (K 38 [(32, 17, true), (15, 4, false)] (.TA 21)) [target_tm]⊢* (K 42 [(33, 16, false), (15, 4, false)] (.TA 21)) :=
    stepPlus_stepStar (Dec 38 [] 32 15 [(15, 4, false)] (.TA 21) (by decide))
  have ms23 : (K 42 [(33, 16, false), (15, 4, false)] (.TA 21)) [target_tm]⊢* (K 2 [(47, 32, false), (16, 15, true), (4, 22, true)] .TN) :=
    stepPlus_stepStar (Ov 42 31 16 [(15, 4, false)] 21 (by decide) (by decide) (by decide))
  have ms24 : (K 2 [(47, 32, false), (16, 15, true), (4, 22, true)] .TN) [target_tm]⊢* (K 6 [(48, 31, true), (17, 14, false), (4, 22, true)] .TN) :=
    stepPlus_stepStar (Dec 2 [(47, 32, false)] 16 13 [(4, 22, true)] .TN (by decide))
  have ms25 : (K 6 [(48, 31, true), (17, 14, false), (4, 22, true)] .TN) [target_tm]⊢* (K 10 [(49, 30, false), (17, 14, false), (4, 22, true)] .TN) :=
    stepPlus_stepStar (Dec 6 [] 48 29 [(17, 14, false), (4, 22, true)] .TN (by decide))
  have ms26 : (K 10 [(49, 30, false), (17, 14, false), (4, 22, true)] .TN) [target_tm]⊢* (K 14 [(50, 29, true), (18, 13, true), (5, 21, false)] .TN) :=
    stepPlus_stepStar (Dec 10 [(49, 30, false), (17, 14, false)] 4 20 [] .TN (by decide))
  have ms27 : (K 14 [(50, 29, true), (18, 13, true), (5, 21, false)] .TN) [target_tm]⊢* (K 18 [(51, 28, false), (18, 13, true), (5, 21, false)] .TN) :=
    stepPlus_stepStar (Dec 14 [] 50 27 [(18, 13, true), (5, 21, false)] .TN (by decide))
  have ms28 : (K 18 [(51, 28, false), (18, 13, true), (5, 21, false)] .TN) [target_tm]⊢* (K 22 [(52, 27, true), (19, 12, false), (5, 21, false)] .TN) :=
    stepPlus_stepStar (Dec 18 [(51, 28, false)] 18 11 [(5, 21, false)] .TN (by decide))
  have ms29 : (K 22 [(52, 27, true), (19, 12, false), (5, 21, false)] .TN) [target_tm]⊢* (K 26 [(53, 26, false), (19, 12, false), (5, 21, false)] .TN) :=
    stepPlus_stepStar (Dec 22 [] 52 25 [(19, 12, false), (5, 21, false)] .TN (by decide))
  have ms30 : (K 26 [(53, 26, false), (19, 12, false), (5, 21, false)] .TN) [target_tm]⊢* (K 30 [(54, 25, true), (20, 11, true), (6, 20, false)] (.TA 1)) :=
    stepPlus_stepStar (EndR 26 [(53, 26, false), (19, 12, false)] 5 19 (by decide))
  have ms31 : (K 30 [(54, 25, true), (20, 11, true), (6, 20, false)] (.TA 1)) [target_tm]⊢* (K 34 [(55, 24, false), (20, 11, true), (6, 20, false)] (.TA 1)) :=
    stepPlus_stepStar (Dec 30 [] 54 23 [(20, 11, true), (6, 20, false)] (.TA 1) (by decide))
  have ms32 : (K 34 [(55, 24, false), (20, 11, true), (6, 20, false)] (.TA 1)) [target_tm]⊢* (K 38 [(56, 23, true), (21, 10, false), (6, 20, false)] (.TA 1)) :=
    stepPlus_stepStar (Dec 34 [(55, 24, false)] 20 9 [(6, 20, false)] (.TA 1) (by decide))
  have ms33 : (K 38 [(56, 23, true), (21, 10, false), (6, 20, false)] (.TA 1)) [target_tm]⊢* (K 42 [(57, 22, false), (21, 10, false), (6, 20, false)] (.TA 1)) :=
    stepPlus_stepStar (Dec 38 [] 56 21 [(21, 10, false), (6, 20, false)] (.TA 1) (by decide))
  have ms34 : (K 42 [(57, 22, false), (21, 10, false), (6, 20, false)] (.TA 1)) [target_tm]⊢* (K 2 [(47, 56, false), (22, 21, true), (10, 6, true), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Ov 42 55 22 [(21, 10, false), (6, 20, false)] 1 (by decide) (by decide) (by decide))
  have ms35 : (K 2 [(47, 56, false), (22, 21, true), (10, 6, true), (20, 2, true)] .TN) [target_tm]⊢* (K 6 [(48, 55, true), (23, 20, false), (10, 6, true), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 2 [(47, 56, false)] 22 19 [(10, 6, true), (20, 2, true)] .TN (by decide))
  have ms36 : (K 6 [(48, 55, true), (23, 20, false), (10, 6, true), (20, 2, true)] .TN) [target_tm]⊢* (K 10 [(49, 54, false), (23, 20, false), (10, 6, true), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 6 [] 48 53 [(23, 20, false), (10, 6, true), (20, 2, true)] .TN (by decide))
  have ms37 : (K 10 [(49, 54, false), (23, 20, false), (10, 6, true), (20, 2, true)] .TN) [target_tm]⊢* (K 14 [(50, 53, true), (24, 19, true), (11, 5, false), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 10 [(49, 54, false), (23, 20, false)] 10 4 [(20, 2, true)] .TN (by decide))
  have ms38 : (K 14 [(50, 53, true), (24, 19, true), (11, 5, false), (20, 2, true)] .TN) [target_tm]⊢* (K 18 [(51, 52, false), (24, 19, true), (11, 5, false), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 14 [] 50 51 [(24, 19, true), (11, 5, false), (20, 2, true)] .TN (by decide))
  have ms39 : (K 18 [(51, 52, false), (24, 19, true), (11, 5, false), (20, 2, true)] .TN) [target_tm]⊢* (K 22 [(52, 51, true), (25, 18, false), (11, 5, false), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 18 [(51, 52, false)] 24 17 [(11, 5, false), (20, 2, true)] .TN (by decide))
  have ms40 : (K 22 [(52, 51, true), (25, 18, false), (11, 5, false), (20, 2, true)] .TN) [target_tm]⊢* (K 26 [(53, 50, false), (25, 18, false), (11, 5, false), (20, 2, true)] .TN) :=
    stepPlus_stepStar (Dec 22 [] 52 49 [(25, 18, false), (11, 5, false), (20, 2, true)] .TN (by decide))
  have ms41 : (K 26 [(53, 50, false), (25, 18, false), (11, 5, false), (20, 2, true)] .TN) [target_tm]⊢* (K 30 [(54, 49, true), (26, 17, true), (12, 4, true), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 26 [(53, 50, false), (25, 18, false), (11, 5, false)] 20 0 [] .TN (by decide))
  have ms42 : (K 30 [(54, 49, true), (26, 17, true), (12, 4, true), (21, 1, false)] .TN) [target_tm]⊢* (K 34 [(55, 48, false), (26, 17, true), (12, 4, true), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 30 [] 54 47 [(26, 17, true), (12, 4, true), (21, 1, false)] .TN (by decide))
  have ms43 : (K 34 [(55, 48, false), (26, 17, true), (12, 4, true), (21, 1, false)] .TN) [target_tm]⊢* (K 38 [(56, 47, true), (27, 16, false), (12, 4, true), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 34 [(55, 48, false)] 26 15 [(12, 4, true), (21, 1, false)] .TN (by decide))
  have ms44 : (K 38 [(56, 47, true), (27, 16, false), (12, 4, true), (21, 1, false)] .TN) [target_tm]⊢* (K 42 [(57, 46, false), (27, 16, false), (12, 4, true), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 38 [] 56 45 [(27, 16, false), (12, 4, true), (21, 1, false)] .TN (by decide))
  have ms45 : (K 42 [(57, 46, false), (27, 16, false), (12, 4, true), (21, 1, false)] .TN) [target_tm]⊢* (K 46 [(58, 45, true), (28, 15, true), (13, 3, false), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 42 [(57, 46, false), (27, 16, false)] 12 2 [(21, 1, false)] .TN (by decide))
  have ms46 : (K 46 [(58, 45, true), (28, 15, true), (13, 3, false), (21, 1, false)] .TN) [target_tm]⊢* (K 50 [(59, 44, false), (28, 15, true), (13, 3, false), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 46 [] 58 43 [(28, 15, true), (13, 3, false), (21, 1, false)] .TN (by decide))
  have ms47 : (K 50 [(59, 44, false), (28, 15, true), (13, 3, false), (21, 1, false)] .TN) [target_tm]⊢* (K 54 [(60, 43, true), (29, 14, false), (13, 3, false), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 50 [(59, 44, false)] 28 13 [(13, 3, false), (21, 1, false)] .TN (by decide))
  have ms48 : (K 54 [(60, 43, true), (29, 14, false), (13, 3, false), (21, 1, false)] .TN) [target_tm]⊢* (K 58 [(61, 42, false), (29, 14, false), (13, 3, false), (21, 1, false)] .TN) :=
    stepPlus_stepStar (Dec 54 [] 60 41 [(29, 14, false), (13, 3, false), (21, 1, false)] .TN (by decide))
  have ms49 : (K 58 [(61, 42, false), (29, 14, false), (13, 3, false), (21, 1, false)] .TN) [target_tm]⊢* (K 62 [(62, 41, true), (30, 13, true), (14, 2, true)] (.TA 25)) :=
    stepPlus_stepStar (EndLast 58 [(61, 42, false), (29, 14, false), (13, 3, false)] 21 (by decide))
  have ms50 : (K 62 [(62, 41, true), (30, 13, true), (14, 2, true)] (.TA 25)) [target_tm]⊢* (K 66 [(63, 40, false), (30, 13, true), (14, 2, true)] (.TA 25)) :=
    stepPlus_stepStar (Dec 62 [] 62 39 [(30, 13, true), (14, 2, true)] (.TA 25) (by decide))
  have ms51 : (K 66 [(63, 40, false), (30, 13, true), (14, 2, true)] (.TA 25)) [target_tm]⊢* (K 70 [(64, 39, true), (31, 12, false), (14, 2, true)] (.TA 25)) :=
    stepPlus_stepStar (Dec 66 [(63, 40, false)] 30 11 [(14, 2, true)] (.TA 25) (by decide))
  have ms52 : (K 70 [(64, 39, true), (31, 12, false), (14, 2, true)] (.TA 25)) [target_tm]⊢* (K 74 [(65, 38, false), (31, 12, false), (14, 2, true)] (.TA 25)) :=
    stepPlus_stepStar (Dec 70 [] 64 37 [(31, 12, false), (14, 2, true)] (.TA 25) (by decide))
  have ms53 : (K 74 [(65, 38, false), (31, 12, false), (14, 2, true)] (.TA 25)) [target_tm]⊢* (K 78 [(66, 37, true), (32, 11, true), (15, 1, false)] (.TA 25)) :=
    stepPlus_stepStar (Dec 74 [(65, 38, false), (31, 12, false)] 14 0 [] (.TA 25) (by decide))
  have ms54 : (K 78 [(66, 37, true), (32, 11, true), (15, 1, false)] (.TA 25)) [target_tm]⊢* (K 82 [(67, 36, false), (32, 11, true), (15, 1, false)] (.TA 25)) :=
    stepPlus_stepStar (Dec 78 [] 66 35 [(32, 11, true), (15, 1, false)] (.TA 25) (by decide))
  have ms55 : (K 82 [(67, 36, false), (32, 11, true), (15, 1, false)] (.TA 25)) [target_tm]⊢* (K 86 [(68, 35, true), (33, 10, false), (15, 1, false)] (.TA 25)) :=
    stepPlus_stepStar (Dec 82 [(67, 36, false)] 32 9 [(15, 1, false)] (.TA 25) (by decide))
  have ms56 : (K 86 [(68, 35, true), (33, 10, false), (15, 1, false)] (.TA 25)) [target_tm]⊢* (K 90 [(69, 34, false), (33, 10, false), (15, 1, false)] (.TA 25)) :=
    stepPlus_stepStar (Dec 86 [] 68 33 [(33, 10, false), (15, 1, false)] (.TA 25) (by decide))
  have ms57 : (K 90 [(69, 34, false), (33, 10, false), (15, 1, false)] (.TA 25)) [target_tm]⊢* (K 2 [(95, 68, false), (34, 33, true), (10, 15, true), (1, 26, true)] .TN) :=
    stepPlus_stepStar (Ov 90 67 34 [(33, 10, false), (15, 1, false)] 25 (by decide) (by decide) (by decide))
  exact stepStar_trans ms0 (stepStar_trans ms1 (stepStar_trans ms2 (stepStar_trans ms3
    (stepStar_trans ms4 (stepStar_trans ms5 (stepStar_trans ms6 (stepStar_trans ms7
    (stepStar_trans ms8 (stepStar_trans ms9 (stepStar_trans ms10 (stepStar_trans ms11
    (stepStar_trans ms12 (stepStar_trans ms13 (stepStar_trans ms14 (stepStar_trans ms15
    (stepStar_trans ms16 (stepStar_trans ms17 (stepStar_trans ms18 (stepStar_trans ms19
    (stepStar_trans ms20 (stepStar_trans ms21 (stepStar_trans ms22 (stepStar_trans ms23
    (stepStar_trans ms24 (stepStar_trans ms25 (stepStar_trans ms26 (stepStar_trans ms27
    (stepStar_trans ms28 (stepStar_trans ms29 (stepStar_trans ms30 (stepStar_trans ms31
    (stepStar_trans ms32 (stepStar_trans ms33 (stepStar_trans ms34 (stepStar_trans ms35
    (stepStar_trans ms36 (stepStar_trans ms37 (stepStar_trans ms38 (stepStar_trans ms39
    (stepStar_trans ms40 (stepStar_trans ms41 (stepStar_trans ms42 (stepStar_trans ms43
    (stepStar_trans ms44 (stepStar_trans ms45 (stepStar_trans ms46 (stepStar_trans ms47
    (stepStar_trans ms48 (stepStar_trans ms49 (stepStar_trans ms50 (stepStar_trans ms51
    (stepStar_trans ms52 (stepStar_trans ms53 (stepStar_trans ms54 (stepStar_trans ms55
    (stepStar_trans ms56 ms57))))))))))))))))))))))))))))))))))))))))))))))))))))))))
-- ============================================================================
-- Arithmetic Invariant Layer (Skelet1LikeC2_1RB1RF.v lines 369-862)
-- ============================================================================

def bv (d : Bool) : Nat := if d then 1 else 0

def dv : List Tri → Nat
  | [] => 0
  | (_, _, d) :: P' => bv d + 2 * dv P'

abbrev dig (x : Tri) : Bool := x.2.2
abbrev dig0 (x : Tri) : Prop := dig x = false

lemma pow_pos (n : Nat) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

lemma pow_S (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by ring

lemma nat_ge_or_mod2 (a b c : Nat) (h : ¬(a ≥ b) → c % 2 = 0) : a ≥ b ∨ c % 2 = 0 :=
  if hab : a ≥ b then Or.inl hab else Or.inr (h hab)

lemma dv_lt (P : List Tri) : dv P < 2 ^ P.length := by
  induction P with
  | nil => decide
  | cons x P ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [dv, List.length, bv]
    rw [pow_S]
    cases d <;> dsimp <;> omega

lemma dv_zeros (Z R : List Tri) (hZ : List.Forall dig0 Z) :
    dv (Z ++ R) = 2 ^ Z.length * dv R := by
  induction Z with
  | nil => simp [dv]
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨hd, hZ'⟩
    dsimp [dig0, dig] at hd
    subst hd
    dsimp [dv, bv, List.length]
    rw [pow_S, ih hZ']
    ring

lemma dv_tz (Z R : List Tri) (hZ : List.Forall dig0 Z) :
    dv (Z.map touch ++ R) + 1 = 2 ^ Z.length + 2 ^ Z.length * dv R := by
  induction Z with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.length_nil, pow_zero]
    omega
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨hd, hZ'⟩
    dsimp [dig0, dig] at hd
    subst hd
    simp only [List.map_cons, List.cons_append, touch, Bool.not_false, dv, bv, ↓reduceIte, List.length_cons, pow_S]
    have ih' := ih hZ'
    have hmul : (2 * 2 ^ Z.length) * dv R = 2 * (2 ^ Z.length * dv R) := by ring
    omega

def AllI (Pr : Nat → Tri → List Tri → Prop) : Nat → List Tri → Prop
  | _, [] => True
  | i, x :: Y => Pr i x Y ∧ AllI Pr (i + 1) Y

lemma AllI_app (Pr : Nat → Tri → List Tri → Prop) (Z : List Tri) (i : Nat) (R : List Tri)
    (h : AllI Pr i (Z ++ R)) : AllI Pr (i + Z.length) R := by
  induction Z generalizing i with
  | nil => simpa using h
  | cons x Z ih =>
    dsimp [AllI, List.length] at h ⊢
    have h' := ih (i + 1) h.2
    have heq : i + 1 + Z.length = i + (Z.length + 1) := by omega
    rwa [heq] at h'

lemma AllI_mono (Pr Pr' : Nat → Tri → List Tri → Prop) (P : List Tri) (i : Nat)
    (hm : ∀ j x Y, i ≤ j → Pr j x Y → Pr' j x Y) (h : AllI Pr i P) : AllI Pr' i P := by
  induction P generalizing i with
  | nil => trivial
  | cons x P ih =>
    dsimp [AllI] at h ⊢
    exact ⟨hm i x P (Nat.le_refl i) h.1, ih (i + 1) (fun j y Y hj => hm j y Y (by omega)) h.2⟩

lemma AllI_shift (Pr Pr' : Nat → Tri → List Tri → Prop) (P : List Tri) (i : Nat)
    (hm : ∀ j x Y, i ≤ j → Pr (j + 1) x Y → Pr' j x Y) (h : AllI Pr (i + 1) P) : AllI Pr' i P := by
  induction P generalizing i with
  | nil => trivial
  | cons x P ih =>
    dsimp [AllI] at h ⊢
    exact ⟨hm i x P (Nat.le_refl i) h.1, ih (i + 1) (fun j y Y hj => hm j y Y (by omega)) h.2⟩

lemma AllI_touchZ (Pr Pr' : Nat → Tri → List Tri → Prop) (R R' Z : List Tri) (i : Nat)
    (hZ : List.Forall dig0 Z)
    (hob : ∀ j p q Zr, List.Forall dig0 Zr → j + (Zr.length + 1) = i + Z.length →
      Pr j (p, q, false) (Zr ++ R) → Pr' j (p + 1, q - 1, true) (Zr.map touch ++ R'))
    (hA : AllI Pr i (Z ++ R))
    (hR : AllI Pr' (i + Z.length) R') :
    AllI Pr' i (Z.map touch ++ R') := by
  induction Z generalizing i with
  | nil => simpa using hR
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨hd, hZ'⟩
    dsimp [dig0, dig] at hd
    subst hd
    simp only [List.length_cons] at hob hR ⊢
    dsimp [AllI, List.map, touch] at hA ⊢
    refine ⟨hob i p q Z hZ' (by omega) hA.1, ?_⟩
    have heq : i + (Z.length + 1) = (i + 1) + Z.length := by omega
    rw [heq] at hR
    exact ih (i + 1) hZ' (fun j p' q' Zr hZr hj => hob j p' q' Zr hZr (by omega)) hA.2 hR

inductive Phase where
  | E1 | E2 | E1t | E2t | T0 | L1 | L2 | LX
  deriving DecidableEq

def PN (ph : Phase) (c4 : Bool) (p q n tv : Nat) : Prop :=
  match ph with
  | .E1 => match n with
           | 0 => q ≥ tv + 2 ^ n + 1 ∧ p + tv + 2 ^ n ≥ 3
           | _ + 1 => q ≥ tv + 3 * 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv + 2 ^ n ≥ 3 * 2 ^ n
  | .E2 => match n with
           | 0 => q ≥ tv + 1 ∧ p + tv ≥ 3
           | _ + 1 => q ≥ tv + 2 * 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv ≥ 3 * 2 ^ n
  | .E1t => match n with
            | 0 => q ≥ tv + 2 ^ n + 1 ∧ p + tv + 2 ^ n = 5
            | _ + 1 => q ≥ tv + 2 * 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv + 2 ^ n ≥ 3 * 2 ^ n
  | .E2t => match n with
            | 0 => q ≥ tv + 1 ∧ p + tv = 5
            | _ + 1 => q ≥ tv + 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv ≥ 3 * 2 ^ n
  | .T0 => q ≥ tv + 7 * 2 ^ n + 1 ∧ p + tv + 5 * 2 ^ n ≥ 6 * 2 ^ n ∧
           match n with
           | 0 => tv = 0 ∧ p % 2 = 0
           | _ + 1 => (p + tv) % 2 = 1
  | .L1 => q + 2 ^ n ≥ tv + 2 ∧
           match n with
           | 0 => q = tv + 2 ^ n
           | 1 => p + tv + 2 ^ n ≥ (if c4 then 4 else 5) * 2 ^ n ∧
                  (q ≥ tv + 2 ^ n + 1 ∨ (q + tv) % 2 = 0) ∧ (if c4 then q = tv + 2 ^ n else True)
           | _ + 2 => p + tv + 2 ^ n ≥ (if c4 then 4 else 5) * 2 ^ n ∧ (q + tv) % 2 = 0
  | .LX => match n with
           | 0 => q = tv + 1
           | 1 => p + tv ≥ 4 * 2 ^ n ∧ q = tv + 1
           | _ + 2 => p + tv ≥ 4 * 2 ^ n ∧ (q + tv) % 2 = 0
  | .L2 => p + tv ≥ (if c4 then 4 else 5) * (2 * 2 ^ n) ∧
           match n with
           | 0 => (q ≥ tv + 1 ∨ (q + tv) % 2 = 0) ∧ (if c4 then q = tv else True)
           | _ + 1 => (q + tv) % 2 = 0

def PI (ph : Phase) (h i p q n tv : Nat) : Prop :=
  match i with
  | 1 => h % 2 = 0 ∧
         match ph with
         | .E1 | .E1t => 2 ≤ n ∧ p + tv + 2 ^ n + 3 ≥ 11 * 2 ^ n ∧ h + 4 * (tv + 2 ^ n) + 6 ≥ 12 * 2 ^ n
         | .E2 | .E2t => 2 ≤ n ∧ p + tv + 3 ≥ 11 * 2 ^ n ∧ h + 4 * tv + 6 ≥ 12 * 2 ^ n
         | .T0 => 2 ≤ n ∧ p + tv + 5 * 2 ^ n + 3 ≥ 22 * 2 ^ n ∧ h + 4 * (tv + 5 * 2 ^ n) + 6 ≥ 24 * 2 ^ n
         | .L1 => 2 ≤ n ∧ q ≥ tv + 3 * 2 ^ n ∧ h + 4 * (tv + 2 ^ n) + 6 ≥ 8 * 2 ^ n
         | .LX => 3 ≤ n ∧ q ≥ tv + 2 * 2 ^ n ∧ h + 4 * tv + 6 ≥ 8 * 2 ^ n
         | .L2 => 1 ≤ n ∧ q ≥ tv + 4 * 2 ^ n ∧ h + 4 * tv + 6 ≥ 16 * 2 ^ n
  | 2 => match ph with
         | .E1 | .E1t => p + tv + 2 ^ n + 1 ≥ 7 * 2 ^ n
         | .E2 | .E2t => p + tv + 1 ≥ 7 * 2 ^ n
         | .T0 => p + tv + 5 * 2 ^ n + 1 ≥ 14 * 2 ^ n
         | .L1 => q ≥ tv + 2 ^ n + 1
         | .LX | .L2 => q ≥ tv + 1
  | _ => True

def PC (ph : Phase) (c4 : Bool) (h i p q n tv : Nat) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ PN ph c4 p q n tv ∧ PI ph h i p q n tv

def Lift (Pr : Nat → Nat → Nat → Nat → Nat → Prop) (i : Nat) (x : Tri) (Y : List Tri) : Prop :=
  match x with
  | (p, q, _) => Pr i p q Y.length (dv (x :: Y))

def PCx (ph : Phase) (c4 : Bool) (h : Nat) : Nat → Tri → List Tri → Prop :=
  Lift (PC ph c4 h)
-- Per-pair obligation lemmas (Skelet1LikeC2_1RB1RF.v lines 539-717)

lemma ob_touch (ph : Phase) (c4 : Bool) (h i p q n tv : Nat)
    (ht : 1 ≤ tv) (hq : 2 ≤ q) (hPC : PC ph c4 h i p q n tv) :
    PC ph c4 (4 + h) i (p + 1) (q - 1) n (tv - 1) := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    cases ph <;> cases c4 <;> rcases n with _ | _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;>
      ((repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega)
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢
    rcases i with _ | _ | _ | i <;> try trivial
    all_goals (cases ph <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢) <;> omega)

lemma ob_merge (ph : Phase) (c4 : Bool) (h i p q n u U : Nat)
    (hph : ph = .L1 ∨ ph = .L2 ∨ ph = .LX)
    (hn : 1 ≤ n) (hu : 2 ≤ u) (hu2 : u % 2 = 0) (hU2 : U % 2 = 0) (hUu : U + u ≤ 2 * 2 ^ n)
    (hL1 : ph = .L1 → U + u ≤ 2 ^ n) (hLX : ph = .LX → 2 ≤ n) (hc4 : ph = .L1 → c4 = true → 2 ≤ n)
    (hi1 : i = 1 → 2 ≤ n) (hiX : ph = .LX → i = 1 → 3 ≤ n) (hq : 2 ≤ q)
    (hPC : PC ph c4 h i p q (n + 1) (u + 2 * U)) :
    PC ph c4 (4 + h) i (p + 1) (q - 1) n (u - 1 + U) := by
  have hpow := pow_pos n
  have hpowS := pow_S n
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rw [hpowS] at hN
    rcases hph with rfl | rfl | rfl
    · have hL1' := hL1 rfl
      have hc4' := hc4 rfl
      cases c4 <;> (rcases n with _ | _ | n <;> try omega)
      all_goals (
        (try have := hc4' rfl)
        (try rw [pow_S] at hN hUu hL1' hpow ⊢)
        (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hUu hL1' hpow ⊢)
        (repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega)
    · cases c4 <;> (rcases n with _ | _ | n <;> try omega)
      all_goals (
        (try rw [pow_S] at hN hUu hpow ⊢)
        (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢)
        omega)
    · have hLX' := hLX rfl
      rcases n with _ | _ | n <;> omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢
    rw [hpowS] at hI
    rcases i with _ | _ | _ | i <;> try trivial
    · have hi1' := hi1 rfl
      rcases hph with rfl | rfl | rfl
      · have hL1' := hL1 rfl; (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢); omega
      · (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢); omega
      · have hLX' := hLX rfl; have hiX' := hiX rfl rfl; (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢); omega
    · rcases hph with rfl | rfl | rfl <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢) <;> omega

lemma ob_mt (c4 : Bool) (h i p q n : Nat) (hq : 2 ≤ q) (hi1 : i = 1 → 1 ≤ n)
    (hPC : PC .L2 c4 h i p q (n + 1) (2 * 2 ^ n)) :
    PC .L2 false (4 + h) i (p + 1) (q - 1) n (2 * 2 ^ n - 1) := by
  have hpow := pow_pos n
  have hpowS := pow_S n
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rw [hpowS] at hN
    cases c4 <;> rcases n with _ | n <;> (try rw [pow_S] at hN hpow ⊢) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;>
      ((repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega)
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢
    rw [hpowS] at hI
    rcases i with _ | _ | _ | i <;> try trivial
    · have := hi1 rfl; (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢); omega
    · (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢); omega

lemma ob_fuse (ph : Phase) (c4 : Bool) (h h' k p p' q' n tv : Nat)
    (hph : ph = .L1 ∨ ph = .L2 ∨ ph = .LX) (hk : 3 ≤ k)
    (hPC : PC ph c4 h (k + 1) p' q' n tv) :
    PC ph c4 h' k (p + p' + 3) q' n tv := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rcases hph with rfl | rfl | rfl <;> cases c4 <;> rcases n with _ | _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;>
      ((repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega)
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
    rcases k with _ | _ | _ | k <;> try omega
    trivial

lemma ob_far (ph : Phase) (c4 : Bool) (h h' i j p q n tv : Nat)
    (_hi : 3 ≤ i) (hj : 3 ≤ j) (hPC : PC ph c4 h i p q n tv) :
    PC ph c4 h' j p q n tv := by
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨hp1, hq1, hN, ?_⟩
  simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
  rcases j with _ | _ | _ | j <;> try omega
  trivial

def endtr (ph ph' : Phase) : Prop :=
  (ph = .E1 ∧ ph' = .E2) ∨ (ph = .E1t ∧ ph' = .E2t)

lemma ob_end (ph ph' : Phase) (h i p q n : Nat) (hph : endtr ph ph') (hn : 1 ≤ n) (hq : 2 ≤ q)
    (hPC : PC ph false h i p q n 0) :
    PC ph' false (4 + h) i (p + 1) (q - 1) n (2 ^ n - 1) := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases n with _ | n <;> (try rw [pow_S] at hN hpow ⊢) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;> omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢
    rcases i with _ | _ | _ | i <;> try trivial
    all_goals (rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢) <;> omega)

lemma ob_end_top (ph ph' : Phase) (h i p q : Nat) (hph : endtr ph ph') (hi : 3 ≤ i)
    (hPC : PC ph false h i p (q + 2) 0 0) :
    PC ph' false (4 + h) i (p + 1) (q + 1) 0 0 := by
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;> omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
    rcases i with _ | _ | _ | i <;> try omega
    trivial

lemma ob_endlast (c4 : Bool) (h i p q n : Nat) (hq : 2 ≤ q)
    (hPC : PC .L1 c4 h i p q (n + 1) 0) :
    PC .L2 c4 (4 + h) i (p + 1) (q - 1) n (2 * 2 ^ n - 1) := by
  have hpow := pow_pos n
  have hpowS := pow_S n
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rw [hpowS] at hN
    cases c4 <;> rcases n with _ | n <;> (try rw [pow_S] at hN hpow ⊢) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;>
      ((repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega)
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢
    rw [hpowS] at hI
    rcases i with _ | _ | _ | i <;> (try trivial) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢) <;> omega

lemma ob_x2 (h i p q n : Nat) (hn : 1 ≤ n) (hq : 2 ≤ q)
    (hPC : PC .T0 false h i p q n 0) :
    PC .E1t false (4 + h) i (p + 1) (q - 1) (n + 1) (3 * 2 ^ n - 1) := by
  have hpow := pow_pos n
  have hpowS := pow_S n
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢
    rw [hpowS]
    rcases n with _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;> omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢
    rw [hpowS]
    rcases i with _ | _ | _ | i <;> (try trivial) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI ⊢) <;> omega

lemma ob_x2_top (h i p q : Nat) (hi : 3 ≤ i)
    (hPC : PC .T0 false h i p (q + 2) 0 0) :
    PC .E1t false (4 + h) i (p + 1) (q + 1) 1 2 := by
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢; omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
    rcases i with _ | _ | _ | i <;> try omega
    trivial

lemma ob_x2_new (h i k : Nat) (hi : 3 ≤ i) (hk : 3 ≤ k) :
    PC .E1t false h i 3 k 0 1 := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]; omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
    rcases i with _ | _ | _ | i <;> try omega
    trivial

def ovtr (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) : Prop :=
  (ph = .E2 ∧ ph' = .L1 ∧ c4' = false ∧ Xp = (fun x => x ≠ 4)) ∨
  (ph = .E2 ∧ ph' = .LX ∧ c4' = false ∧ Xp = (fun x => x = 4)) ∨
  (ph = .E2t ∧ ph' = .L1 ∧ c4' = true ∧ Xp = (fun _ => True)) ∨
  (ph = .L2 ∧ ph' = .E1 ∧ c4' = false ∧ Xp = (fun _ => True))

lemma ob_ov_head (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h p1 q1 n : Nat)
    (htr : ovtr ph ph' c4' Xp)
    (hPC : PC ph false h 1 (p1 + 2) q1 n 0) :
    PC ph' c4' 2 1 (h + 5) (p1 + 1) (n + 1) (2 * (2 * 2 ^ n) - 2) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
      simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at * <;>
      ((repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega)
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
      simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at * <;>
      ((repeat' apply And.intro) <;> (try trivial) <;> omega)

lemma ob_ov_step (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h i pp q p' q' m : Nat)
    (htr : ovtr ph ph' c4' Xp) (hi : 1 ≤ i)
    (hPC : PC ph false h i pp q (m + 1) 0)
    (hPC' : PC ph false h (i + 1) p' q' m 0)
    (hX : m = 0 → Xp p') :
    PC ph' c4' 2 (i + 1) q p' (m + 1) (2 * (2 * 2 ^ m) - 1) := by
  have hpow := pow_pos m
  have hpowS := pow_S m
  rcases hPC with ⟨hpp, hq, hN, hI⟩
  rcases hPC' with ⟨hp', hq', hN', hI'⟩
  refine ⟨hq, hp', ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' ⊢
    rw [hpowS] at hN ⊢
    rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    all_goals (rcases m with _ | _ | m <;> (try have := hX rfl) <;> (try rw [pow_S] at hN hN' hpow ⊢) <;> (try rw [pow_S] at hN hN' hpow ⊢) <;>
      (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' hX ⊢) <;> ((repeat' apply And.intro) <;> (try trivial) <;> (try (apply nat_ge_or_mod2; intro _)) <;> omega))
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
    rcases i with _ | _ | i
    · omega
    · simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' hI hI' ⊢
      rw [hpowS] at hN hI ⊢
      rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      all_goals (rcases m with _ | _ | m <;> (try rw [pow_S] at hN hN' hI hI' hpow ⊢) <;> (try rw [pow_S] at hN hN' hI hI' hpow ⊢) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' hI hI' hX ⊢) <;> omega)
    · trivial

lemma ob_ov_base (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h i pp q t : Nat)
    (htr : ovtr ph ph' c4' Xp) (hi : 1 ≤ i)
    (ht1 : ph = .L2 → 2 ≤ t) (ht2 : ph ≠ .L2 → t = 1)
    (hPC : PC ph false h i pp q 0 0) :
    PC ph' c4' 2 (i + 1) q (t + 1) 0 1 := by
  rcases hPC with ⟨hpp, hq, hN, hI⟩
  refine ⟨hq, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI ⊢
    rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have := ht2 (by decide); omega
    · have := ht2 (by decide); omega
    · have := ht2 (by decide); omega
    · have := ht1 rfl; omega
  · simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI ⊢
    rcases i with _ | _ | i
    · omega
    · rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · have := ht2 (by decide); (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI ⊢); omega
      · have := ht2 (by decide); (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI ⊢); omega
      · have := ht2 (by decide); (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI ⊢); omega
      · have := ht1 rfl; (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI ⊢); omega
    · trivial

lemma ob_x1_head (h p1 q1 n : Nat)
    (hPC : PC .LX false h 1 (p1 + 2) q1 (n + 2) 0) :
    PC .T0 false 2 1 (h + 5) (p1 + 1) (n + 1) (2 * 2 ^ n - 2) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false, true_and, and_true] at * <;>
      omega
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false, true_and, and_true] at * <;>
      omega

lemma ob_x1_step (h i pp q p' q' m : Nat) (hi : 1 ≤ i)
    (hPC : PC .LX false h i pp q (m + 3) 0)
    (hPC' : PC .LX false h (i + 1) p' q' (m + 2) 0) :
    PC .T0 false 2 (i + 1) q p' (m + 1) (2 * 2 ^ m - 1) := by
  have hpow := pow_pos m
  rcases hPC with ⟨hpp, hq, hN, hI⟩
  rcases hPC' with ⟨hp', hq', hN', hI'⟩
  refine ⟨hq, hp', ?_, ?_⟩
  · simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' ⊢
    rw [pow_S (m + 2), pow_S (m + 1), pow_S m] at hN
    rw [pow_S (m + 1), pow_S m] at hN'
    rw [pow_S m]
    rcases m with _ | m <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' ⊢) <;> omega
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
    rcases i with _ | _ | i
    · omega
    · simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' hI hI' ⊢
      rw [pow_S (m + 2), pow_S (m + 1), pow_S m] at hN hI
      rw [pow_S (m + 1), pow_S m] at hN'
      rw [pow_S m]
      rcases m with _ | m <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hN' hI hI' ⊢) <;> omega
    · trivial

lemma ob_x1_base (h i pp q pa : Nat) (hi : 1 ≤ i)
    (hPC : PC .LX false h i pp q 2 0)
    (hPC' : PC .LX false h (i + 1) (pa + 1) 1 1 0) :
    PC .T0 false 2 (i + 1) q (pa + 1) 0 0 := by
  rcases hPC with ⟨hpp, hq, hN, hI⟩
  rcases hPC' with ⟨hp', hq', hN', hI'⟩
  refine ⟨hq, by omega, ?_, ?_⟩
  · simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at *
    (repeat' apply And.intro) <;> (try trivial) <;> omega
  · rcases i with _ | _ | i
    · omega
    · simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at *
      omega
    · trivial
-- List-level preservation and Jstep (Skelet1LikeC2_1RB1RF.v lines 720-1280)

lemma dv_zero (Z : List Tri) (hZ : List.Forall dig0 Z) : dv Z = 0 := by
  have h := dv_zeros Z [] hZ
  rw [List.append_nil] at h
  dsimp [dv] at h
  omega

lemma dv_tz' (Z R : List Tri) (hZ : List.Forall dig0 Z) :
    dv (Z.map touch ++ R) = 2 ^ Z.length - 1 + 2 ^ Z.length * dv R := by
  have h := dv_tz Z R hZ
  have hp := pow_pos Z.length
  omega

lemma ovp_len (q : Nat) (Z : List Tri) (t : Nat) :
    (ovp q Z t).length = Z.length + 1 := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    dsimp [ovp, List.length]
    rw [ih q']

lemma ovp_dv (q : Nat) (Z : List Tri) (t : Nat) :
    dv (ovp q Z t) + 1 = 2 ^ (Z.length + 1) := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    dsimp [ovp, dv, bv, List.length]
    have h := ih q'
    rw [pow_S (Z.length + 1)]
    omega

lemma ovpX_len (q : Nat) (Z : List Tri) (pa : Nat) :
    (ovpX q Z pa).length = Z.length + 1 := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    dsimp [ovpX, List.length]
    rw [ih q']

lemma ovpX_dv (q : Nat) (Z : List Tri) (pa : Nat) :
    dv (ovpX q Z pa) + 1 = 2 ^ Z.length := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    dsimp [ovpX, dv, bv, List.length]
    have h := ih q'
    rw [pow_S Z.length]
    omega

def lastOK (Xp : Nat → Prop) : List Tri → Prop
  | [] => True
  | [(p, _, _)] => Xp p
  | _ :: Z' => lastOK Xp Z'

lemma lastOK_cons (Xp : Nat → Prop) (p q : Nat) (d : Bool) (Z : List Tri)
    (h : lastOK Xp ((p, q, d) :: Z)) : (Z = [] → Xp p) ∧ lastOK Xp Z := by
  cases Z with
  | nil => exact ⟨fun _ => h, trivial⟩
  | cons z Z' => exact ⟨(fun h' => nomatch h'), h⟩

lemma lastOK_dec (Z : List Tri) :
    lastOK (fun x => x = 4) Z ∨ lastOK (fun x => x ≠ 4) Z := by
  induction Z with
  | nil => exact Or.inl trivial
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    cases Z with
    | nil =>
      dsimp [lastOK]
      if hp : p = 4 then exact Or.inl hp else exact Or.inr hp
    | cons z Z' => exact ih

lemma lastOK_True (Z : List Tri) : lastOK (fun _ => True) Z := by
  induction Z with
  | nil => trivial
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    cases Z with
    | nil => trivial
    | cons z Z' => exact ih

lemma AllI_ovp (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h t : Nat)
    (htr : ovtr ph ph' c4' Xp) (ht1 : ph = .L2 → 2 ≤ t) (ht2 : ph ≠ .L2 → t = 1)
    (Z : List Tri) (i pp q : Nat) (hi : 1 ≤ i) (hZ : List.Forall dig0 Z)
    (hX : lastOK Xp Z) (hPC : PC ph false h i pp q Z.length 0)
    (hA : AllI (PCx ph false h) (i + 1) Z) :
    AllI (PCx ph' c4' 2) (i + 1) (ovp q Z t) := by
  induction Z generalizing i pp q with
  | nil =>
    dsimp [ovp, AllI, PCx, Lift, List.length, dv, bv]
    exact ⟨ob_ov_base ph ph' c4' Xp h i pp q t htr hi ht1 ht2 hPC, trivial⟩
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨hd', hZ'⟩
    dsimp [dig0, dig] at hd'
    subst hd'
    rcases hA with ⟨hH, hA'⟩
    rcases lastOK_cons Xp p' q' false Z hX with ⟨hX1, hX2⟩
    dsimp [PCx, Lift, List.length] at hH hPC
    have hz0 : List.Forall dig0 ((p', q', false) :: Z) := by
      rw [List.forall_cons]; exact ⟨rfl, hZ'⟩
    rw [dv_zero _ hz0] at hH
    dsimp [ovp, AllI]
    refine ⟨?_, ih (i + 1) p' q' (by omega) hZ' hX2 hH hA'⟩
    dsimp [PCx, Lift]
    rw [ovp_len]
    have hdv : dv ((q, p', true) :: ovp q' Z t) = 2 * (2 * 2 ^ Z.length) - 1 := by
      dsimp [dv, bv]
      have E := ovp_dv q' Z t
      rw [pow_S] at E
      omega
    rw [hdv]
    exact ob_ov_step ph ph' c4' Xp h i pp q p' q' Z.length htr hi hPC hH
      (fun hm => hX1 (by cases Z <;> first | rfl | nomatch hm))

lemma AllI_ovpX (h pa pb : Nat) (Z : List Tri) (i pp q : Nat) (hi : 1 ≤ i)
    (hZ : List.Forall dig0 Z)
    (hPC : PC .LX false h i pp q (Z.length + 2) 0)
    (hA : AllI (PCx .LX false h) (i + 1) (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) :
    AllI (PCx .T0 false 2) (i + 1) (ovpX q Z (pa + 1)) := by
  induction Z generalizing i pp q with
  | nil =>
    dsimp [ovpX, AllI, List.nil_append] at hA ⊢
    rcases hA with ⟨hHa, _⟩
    dsimp [PCx, Lift, List.length, dv, bv] at hHa ⊢
    exact ⟨ob_x1_base h i pp q pa hi hPC hHa, trivial⟩
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨hd', hZ'⟩
    dsimp [dig0, dig] at hd'
    subst hd'
    dsimp [List.cons_append, AllI] at hA
    rcases hA with ⟨hH, hA'⟩
    dsimp [PCx, Lift] at hH
    rw [List.length_append] at hH
    dsimp [List.length] at hH hPC
    have hz0 : List.Forall dig0 ((p', q', false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) := by
      rw [List.forall_cons]; refine ⟨rfl, ?_⟩
      rw [List.forall_append]; exact ⟨hZ', by simp [dig0, dig]⟩
    rw [dv_zero _ hz0] at hH
    dsimp [ovpX, AllI]
    refine ⟨?_, ih (i + 1) p' q' (by omega) hZ' hH hA'⟩
    dsimp [PCx, Lift]
    rw [ovpX_len]
    have hdv : dv ((q, p', true) :: ovpX q' Z (pa + 1)) = 2 * 2 ^ Z.length - 1 := by
      dsimp [dv, bv]
      have E := ovpX_dv q' Z (pa + 1)
      omega
    rw [hdv]
    exact ob_x1_step h i pp q p' q' Z.length hi hPC hH

lemma passq (ph : Phase) (c4 : Bool) (h i p q n tv : Nat)
    (hPC : PC ph c4 h i p q n tv) (ht : 2 ≤ tv) (ht2 : tv % 2 = 0) : 2 ≤ q := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp, hq, hN, _⟩
  simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN
  cases ph <;> cases c4 <;> rcases n with _ | _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN) <;> omega

lemma Z_okL (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (i : Nat) (x : Tri) (R : List Tri)
    (hZ : List.Forall dig0 Z) (hx : dig x = true)
    (hA : AllI (PCx ph c4 h) i (Z ++ x :: R)) : List.Forall okL Z := by
  induction Z generalizing i with
  | nil => trivial
  | cons z Z ih =>
    rcases z with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ ⊢
    rcases hZ with ⟨hd, hZ'⟩
    dsimp [dig0, dig] at hd
    subst hd
    dsimp [List.cons_append, AllI] at hA
    rcases hA with ⟨hH, hA'⟩
    refine ⟨⟨rfl, ?_⟩, ih (i + 1) hZ' hA'⟩
    dsimp [PCx, Lift] at hH
    apply passq ph c4 h i p q (Z ++ x :: R).length (dv ((p, q, false) :: (Z ++ x :: R))) hH
    · dsimp [dv, bv]
      rw [dv_zeros Z (x :: R) hZ']
      rcases x with ⟨px, qx, dx⟩
      dsimp [dig] at hx
      subst hx
      dsimp [dv, bv]
      have hp := pow_pos Z.length
      have hmul : 2 ^ Z.length * 1 ≤ 2 ^ Z.length * (1 + 2 * dv R) :=
        Nat.mul_le_mul_left (2 ^ Z.length) (by omega)
      omega
    · dsimp [dv, bv]; omega

lemma borrow1 (ph : Phase) (c4 : Bool) (h k p n tv : Nat)
    (hk : 1 ≤ k) (ht : tv % 2 = 1) (hPC : PC ph c4 h k p 1 n tv) :
    (ph = .L1 ∨ ph = .L2 ∨ ph = .LX) ∧ 3 ≤ k ∧
    (ph = .L1 → 1 ≤ n ∧ tv + 1 ≤ 2 ^ n ∧ (c4 = true → 2 ≤ n)) ∧
    (ph = .LX → 2 ≤ n) := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp, hq, hN, hI⟩
  have hph : ph = .L1 ∨ ph = .L2 ∨ ph = .LX := by
    simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN
    cases ph <;> try (first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))
    all_goals (rcases n with _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN) <;> omega)
  refine ⟨hph, ?_, ?_, ?_⟩
  · simp -failIfUnchanged only [PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI
    rcases k with _ | _ | _ | k <;> try omega
    all_goals (rcases hph with rfl | rfl | rfl <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hI) <;> omega)
  · intro hL1; subst hL1
    simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN
    cases c4 <;> rcases n with _ | _ | n <;> (try rw [pow_S] at hN hpow ⊢) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN ⊢) <;>
      ((repeat' apply And.intro) <;> (try intro _) <;> (try contradiction) <;> omega)
  · intro hLX; subst hLX
    simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN
    rcases n with _ | _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN) <;> omega

lemma inv_Dec (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p q : Nat) (R : List Tri)
    (hZ : List.Forall dig0 Z)
    (hA : AllI (PCx ph c4 h) 1 (Z ++ (p, q + 2, true) :: R)) :
    AllI (PCx ph c4 (4 + h)) 1 (Z.map touch ++ (p + 1, q + 1, false) :: R) := by
  have hB := AllI_app (PCx ph c4 h) Z 1 ((p, q + 2, true) :: R) hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, hR⟩
  apply AllI_touchZ (PCx ph c4 h) (PCx ph c4 (4 + h)) ((p, q + 2, true) :: R) ((p + 1, q + 1, false) :: R) Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    simp only [List.length_append, List.length_map, List.length_cons, dv, bv] at h0 ⊢
    rw [dv_zeros Zr ((p, q + 2, true) :: R) hZr] at h0
    rw [dv_tz' Zr ((p + 1, q + 1, false) :: R) hZr]
    dsimp [dv, bv] at h0 ⊢
    have hp := pow_pos Zr.length
    have heq : 1 + 2 * (2 ^ Zr.length - 1 + 2 ^ Zr.length * (0 + 2 * dv R)) =
        0 + 2 * (2 ^ Zr.length * (1 + 2 * dv R)) - 1 := by
      have hm1 : 2 ^ Zr.length * (0 + 2 * dv R) = 2 * (2 ^ Zr.length * dv R) := by ring
      have hm2 : 2 ^ Zr.length * (1 + 2 * dv R) = 2 ^ Zr.length + 2 * (2 ^ Zr.length * dv R) := by ring
      rw [hm1, hm2]; omega
    rw [heq]
    have htv2 : 2 ≤ 0 + 2 * (2 ^ Zr.length * (1 + 2 * dv R)) := by
      have hm2 : 2 ^ Zr.length * (1 + 2 * dv R) = 2 ^ Zr.length + 2 * (2 ^ Zr.length * dv R) := by ring
      omega
    have hq0 : 2 ≤ q0 := passq ph c4 h j p0 q0 (Zr.length + (R.length + 1)) _ h0 htv2 (by omega)
    exact ob_touch ph c4 h j p0 q0 (Zr.length + (R.length + 1)) _ (by omega) hq0 h0
  · exact hA
  · dsimp [AllI]
    refine ⟨?_, ?_⟩
    · dsimp [PCx, Lift, dv, bv] at hx ⊢
      have heq : 0 + 2 * dv R = (1 + 2 * dv R) - 1 := by omega
      rw [heq]
      exact ob_touch ph c4 h (1 + Z.length) p (q + 2) R.length (1 + 2 * dv R) (by omega) (by omega) hx
    · refine AllI_mono (PCx ph c4 h) (PCx ph c4 (4 + h)) R (1 + Z.length + 1) ?_ hR
      intro j y Y hj hy
      rcases y with ⟨py, qy, dy⟩
      dsimp [PCx, Lift] at hy ⊢
      rcases hy with ⟨hp, hq, hN, hI⟩
      refine ⟨hp, hq, hN, ?_⟩
      rcases j with _ | _ | _ | j <;> first | omega | exact hI
-- Remaining inv_* lemmas, J, Jstep, J_base, and is_does_not_halt (Skelet1LikeC2_1RB1RF.v lines 863-1280)

lemma snoc_nn (Z : List Tri) (y : Tri) : Z ++ [y] ≠ [] := by
  cases Z <;> (intro h; nomatch h)

def minlen : Phase → Nat
  | .LX => 3
  | .L2 => 1
  | _ => 2

lemma head_len (ph : Phase) (c4 : Bool) (h : Nat) (x : Tri) (Y : List Tri)
    (hPC : PCx ph c4 h 1 x Y) : minlen ph ≤ Y.length := by
  rcases x with ⟨p, q, d⟩
  simp -failIfUnchanged only [PCx, Lift, PC, PI] at hPC
  rcases hPC with ⟨_, _, _, _, hI⟩
  cases ph <;> dsimp [minlen] at hI ⊢ <;> omega

lemma AllI_len (ph : Phase) (c4 : Bool) (h : Nat) (P : List Tri)
    (hne : P ≠ []) (hA : AllI (PCx ph c4 h) 1 P) : minlen ph + 1 ≤ P.length := by
  cases P with
  | nil => contradiction
  | cons x Y =>
    have := head_len ph c4 h x Y hA.1
    dsimp [List.length]
    omega

lemma q2_V0 (ph : Phase) (c4 : Bool) (h i p q n : Nat)
    (hPC : PC ph c4 h i p q n 0) (hn : 1 ≤ n) (hX : ph = .LX → 2 ≤ n) : 2 ≤ q := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp, hq, hN, _⟩
  simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN
  cases ph <;> cases c4 <;> rcases n with _ | _ | n <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN) <;> try omega
  all_goals (have := hX rfl; omega)

lemma p1_V0 (ph : Phase) (c4 : Bool) (h p q n : Nat)
    (hPC : PC ph c4 h 1 p q n 0) (hph : ph = .E2 ∨ ph = .E2t ∨ ph = .L2 ∨ ph = .LX) : 2 ≤ p := by
  have hpow := pow_pos n
  rcases hPC with ⟨hp, hq, hN, hI⟩
  simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI
  rcases hph with rfl | rfl | rfl | rfl <;> cases c4 <;> rcases n with _ | _ | n <;>
    (try rw [pow_S] at hN hI hpow) <;> (try simp -failIfUnchanged only [PN, PI, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN hI) <;> omega

lemma L2_c4_V0 (h i p q : Nat) (hPC : PC .L2 true h i p q 0 0) : False := by
  rcases hPC with ⟨_, _, hN, _⟩
  simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN
  omega

lemma AllI_okRO (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (i : Nat)
    (hZ : List.Forall dig0 Z) (hA : AllI (PCx ph c4 h) i Z) :
    List.Forall okR Z ∧ List.Forall okO Z := by
  induction Z generalizing i with
  | nil => exact ⟨trivial, trivial⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rw [List.forall_cons] at hZ
    rcases hZ with ⟨hd, hZ'⟩
    dsimp [dig0, dig] at hd
    subst hd
    dsimp [AllI] at hA
    rcases hA with ⟨hH, hA'⟩
    rcases ih (i + 1) hZ' hA' with ⟨hR, hO⟩
    dsimp [PCx, Lift, PC] at hH
    rcases hH with ⟨hp, hq, _⟩
    rw [List.forall_cons, List.forall_cons]
    exact ⟨⟨⟨rfl, hq⟩, hR⟩, ⟨⟨hp, hq⟩, hO⟩⟩

lemma inv_Merge (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p p' q' : Nat) (d' : Bool) (R0 : List Tri)
    (hZ : List.Forall dig0 Z)
    (hA : AllI (PCx ph c4 h) 1 (Z ++ (p, 1, true) :: (p', q', d') :: R0)) :
    AllI (PCx ph c4 (4 + h)) 1 (Z.map touch ++ (p + p' + 3, q', d') :: R0) := by
  have hB := AllI_app (PCx ph c4 h) Z 1 ((p, 1, true) :: (p', q', d') :: R0) hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, hy, hR⟩
  have hlt := dv_lt ((p', q', d') :: R0)
  dsimp [List.length] at hlt
  set Hd := dv ((p', q', d') :: R0)
  have hx' := hx
  dsimp [PCx, Lift, List.length] at hx'
  change PC ph c4 h (1 + Z.length) p 1 (R0.length + 1) (1 + 2 * Hd) at hx'
  rcases borrow1 ph c4 h (1 + Z.length) p (R0.length + 1) (1 + 2 * Hd) (by omega) (by omega) hx' with
    ⟨hph, hk, hL1, hLX⟩
  apply AllI_touchZ (PCx ph c4 h) (PCx ph c4 (4 + h))
    ((p, 1, true) :: (p', q', d') :: R0) ((p + p' + 3, q', d') :: R0) Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    simp only [List.length_append, List.length_map, List.length_cons, dv, bv] at h0 ⊢
    rw [dv_zeros Zr ((p, 1, true) :: (p', q', d') :: R0) hZr] at h0
    rw [dv_tz' Zr ((p + p' + 3, q', d') :: R0) hZr]
    change PC ph c4 h j p0 q0 (Zr.length + (R0.length + 2)) (0 + 2 * (2 ^ Zr.length * (1 + 2 * Hd))) at h0
    change PC ph c4 (4 + h) j (p0 + 1) (q0 - 1) (Zr.length + (R0.length + 1)) (1 + 2 * (2 ^ Zr.length - 1 + 2 ^ Zr.length * Hd))
    set A := 2 ^ Zr.length
    set B := 2 ^ R0.length
    have hA1 : 1 ≤ A := pow_pos Zr.length
    have hB1 : 1 ≤ B := pow_pos R0.length
    have hpow_add : 2 ^ (Zr.length + (R0.length + 1)) = A * (2 * B) := by
      rw [Nat.pow_add, pow_S]
    rw [pow_S] at hlt
    change Hd < 2 * B at hlt
    have hn_eq : Zr.length + (R0.length + 2) = (Zr.length + (R0.length + 1)) + 1 := by omega
    have htv_in : 0 + 2 * (A * (1 + 2 * Hd)) = (2 * A) + 2 * (2 * A * Hd) := by ring
    have htv_out : 1 + 2 * (A - 1 + A * Hd) = (2 * A) - 1 + (2 * A * Hd) := by
      have hm : 2 * (A - 1 + A * Hd) = 2 * (A - 1) + 2 * (A * Hd) := by ring
      have hm2 : 2 * A * Hd = 2 * (A * Hd) := by ring
      omega
    rw [hn_eq, htv_in] at h0
    rw [htv_out]
    have hq2 : 2 ≤ q0 := by
      apply passq ph c4 h j p0 q0 ((Zr.length + (R0.length + 1)) + 1) ((2 * A) + 2 * (2 * A * Hd)) h0
      · omega
      · omega
    have hU2 : (2 * A * Hd) % 2 = 0 := by
      have hmul : 2 * A * Hd = 2 * (A * Hd) := by ring
      omega
    apply ob_merge ph c4 h j p0 q0 (Zr.length + (R0.length + 1)) (2 * A) (2 * A * Hd) hph (by omega) (by omega)
      (by omega) hU2
    · rw [hpow_add]
      have hmul : (2 * A) * (Hd + 1) ≤ (2 * A) * (2 * B) := Nat.mul_le_mul_left (2 * A) (by omega)
      have hring : (2 * A) * (Hd + 1) = 2 * A * Hd + 2 * A := by ring
      have hring2 : (2 * A) * (2 * B) = 2 * (A * (2 * B)) := by ring
      omega
    · intro hpL1
      rcases hL1 hpL1 with ⟨_, hb, _⟩
      rw [pow_S] at hb
      change (1 + 2 * Hd) + 1 ≤ 2 * B at hb
      rw [hpow_add]
      have hmul : A * (2 * Hd + 2) ≤ A * (2 * B) := Nat.mul_le_mul_left A (by omega)
      have hring : A * (2 * Hd + 2) = 2 * A * Hd + 2 * A := by ring
      omega
    · intro hpLX; have := hLX hpLX; omega
    · intro hpL1 hc4; rcases hL1 hpL1 with ⟨_, _, hc2⟩; have := hc2 hc4; omega
    · intro hi1; omega
    · intro hpLX hi1; have := hLX hpLX; omega
    · exact hq2
    · exact h0
  · exact hA
  · dsimp [AllI]
    refine ⟨?_, ?_⟩
    · dsimp [PCx, Lift] at hy ⊢
      change PC ph c4 h (1 + Z.length + 1) p' q' R0.length Hd at hy
      change PC ph c4 (4 + h) (1 + Z.length) (p + p' + 3) q' R0.length Hd
      exact ob_fuse ph c4 h (4 + h) (1 + Z.length) p p' q' R0.length Hd hph (by omega) hy
    · refine AllI_shift (PCx ph c4 h) (PCx ph c4 (4 + h)) R0 (1 + Z.length + 1) ?_ hR
      intro j y Y hj hy0
      rcases y with ⟨py, qy, dy⟩
      dsimp [PCx, Lift] at hy0 ⊢
      exact ob_far ph c4 h (4 + h) (j + 1) j py qy Y.length (dv ((py, qy, dy) :: Y)) (by omega) (by omega) hy0

lemma inv_MT (c4 : Bool) (h : Nat) (Z : List Tri) (p : Nat)
    (hZ : List.Forall dig0 Z)
    (hA : AllI (PCx .L2 c4 h) 1 (Z ++ [(p, 1, true)])) :
    AllI (PCx .L2 false (4 + h)) 1 (Z.map touch) ∧ 2 ≤ Z.length := by
  have hB := AllI_app (PCx .L2 c4 h) Z 1 [(p, 1, true)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  dsimp [PCx, Lift, List.length, dv, bv] at hx
  rcases borrow1 .L2 c4 h (1 + Z.length) p 0 1 (by omega) (by omega) hx with ⟨_, hk, _⟩
  refine ⟨?_, by omega⟩
  have hnil : Z.map touch = Z.map touch ++ [] := (List.append_nil _).symm
  rw [hnil]
  apply AllI_touchZ (PCx .L2 c4 h) (PCx .L2 false (4 + h)) [(p, 1, true)] [] Z 1 hZ _ hA trivial
  intro j p0 q0 Zr hZr hj h0
  dsimp [PCx, Lift] at h0 ⊢
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, dv, bv] at h0 ⊢
  rw [dv_zeros Zr [(p, 1, true)] hZr] at h0
  rw [dv_tz' Zr [] hZr]
  dsimp [dv, bv] at h0 ⊢
  have hp := pow_pos Zr.length
  have htv_in : 0 + 2 * 2 ^ Zr.length = 2 * 2 ^ Zr.length := by omega
  have htv_out : 1 + 2 * (2 ^ Zr.length - 1) = 2 * 2 ^ Zr.length - 1 := by omega
  try rw [Nat.mul_one] at h0
  rw [htv_in] at h0
  rw [htv_out]
  have hq0 : 2 ≤ q0 := passq .L2 c4 h j p0 q0 (Zr.length + 1) (2 * 2 ^ Zr.length) h0 (by omega) (by omega)
  exact ob_mt c4 h j p0 q0 Zr.length hq0 (by omega) h0

lemma inv_End (ph ph' : Phase) (h : Nat) (Z : List Tri) (p q : Nat)
    (htr : endtr ph ph') (hZ : List.Forall dig0 Z)
    (hA : AllI (PCx ph false h) 1 (Z ++ [(p, q + 2, false)])) :
    AllI (PCx ph' false (4 + h)) 1 (Z.map touch ++ [(p + 1, q + 1, false)]) := by
  have hlen := AllI_len ph false h (Z ++ [(p, q + 2, false)]) (snoc_nn Z _) hA
  rw [List.length_append] at hlen
  dsimp [List.length] at hlen
  have hm : minlen ph = 2 := by
    rcases htr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hB := AllI_app (PCx ph false h) Z 1 [(p, q + 2, false)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  apply AllI_touchZ (PCx ph false h) (PCx ph' false (4 + h)) [(p, q + 2, false)] [(p + 1, q + 1, false)] Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, q + 2, false)] hZr] at h0
    rw [dv_tz' Zr [(p + 1, q + 1, false)] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hp := pow_pos Zr.length
    have htv_out : 1 + 2 * (2 ^ Zr.length - 1) = 2 ^ (Zr.length + 1) - 1 := by
      rw [pow_S]; omega
    rw [htv_out]
    have hq0 : 2 ≤ q0 := q2_V0 ph false h j p0 q0 (Zr.length + 1) h0 (by omega)
      (by intro hX; rcases htr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> nomatch hX)
    exact ob_end ph ph' h j p0 q0 (Zr.length + 1) htr (by omega) hq0 h0
  · exact hA
  · dsimp [AllI, PCx, Lift, List.length, dv, bv] at hx ⊢
    exact ⟨ob_end_top ph ph' h (1 + Z.length) p q htr (by omega) hx, trivial⟩

lemma inv_X2 (h : Nat) (Z : List Tri) (p q k : Nat)
    (hZ : List.Forall dig0 Z) (hk : 3 ≤ k)
    (hA : AllI (PCx .T0 false h) 1 (Z ++ [(p, q + 2, false)])) :
    AllI (PCx .E1t false (4 + h)) 1 (Z.map touch ++ [(p + 1, q + 1, false), (3, k, true)]) := by
  have hlen := AllI_len .T0 false h (Z ++ [(p, q + 2, false)]) (snoc_nn Z _) hA
  rw [List.length_append] at hlen
  dsimp [List.length, minlen] at hlen
  have hB := AllI_app (PCx .T0 false h) Z 1 [(p, q + 2, false)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  apply AllI_touchZ (PCx .T0 false h) (PCx .E1t false (4 + h))
    [(p, q + 2, false)] [(p + 1, q + 1, false), (3, k, true)] Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, q + 2, false)] hZr] at h0
    rw [dv_tz' Zr [(p + 1, q + 1, false), (3, k, true)] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hp := pow_pos Zr.length
    have htv_out : 1 + 2 * (2 ^ Zr.length - 1 + 2 ^ Zr.length * 2) =
        3 * 2 ^ (Zr.length + 1) - 1 := by
      rw [pow_S]; omega
    rw [htv_out]
    have hlen_eq : Zr.length + 2 = (Zr.length + 1) + 1 := by omega
    rw [hlen_eq]
    have hq0 : 2 ≤ q0 := q2_V0 .T0 false h j p0 q0 (Zr.length + 1) h0 (by omega) (by intro hX; nomatch hX)
    exact ob_x2 h j p0 q0 (Zr.length + 1) (by omega) hq0 h0
  · exact hA
  · dsimp [AllI, PCx, Lift, List.length, dv, bv] at hx ⊢
    exact ⟨ob_x2_top h (1 + Z.length) p q (by omega) hx,
           ob_x2_new (4 + h) (1 + Z.length + 1) k (by omega) hk,
           trivial⟩

lemma inv_EndLast (c4 : Bool) (h : Nat) (Z : List Tri) (p : Nat)
    (hZ : List.Forall dig0 Z)
    (hA : AllI (PCx .L1 c4 h) 1 (Z ++ [(p, 1, false)])) :
    AllI (PCx .L2 c4 (4 + h)) 1 (Z.map touch) ∧ 2 ≤ Z.length := by
  have hlen := AllI_len .L1 c4 h (Z ++ [(p, 1, false)]) (snoc_nn Z _) hA
  rw [List.length_append] at hlen
  dsimp [List.length, minlen] at hlen
  refine ⟨?_, by omega⟩
  have hnil : Z.map touch = Z.map touch ++ [] := (List.append_nil _).symm
  rw [hnil]
  apply AllI_touchZ (PCx .L1 c4 h) (PCx .L2 c4 (4 + h)) [(p, 1, false)] [] Z 1 hZ _ hA trivial
  intro j p0 q0 Zr hZr hj h0
  dsimp [PCx, Lift] at h0 ⊢
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, dv, bv] at h0 ⊢
  rw [dv_zeros Zr [(p, 1, false)] hZr] at h0
  rw [dv_tz' Zr [] hZr]
  dsimp [dv, bv] at h0 ⊢
  have hp := pow_pos Zr.length
  have htv_out : 1 + 2 * (2 ^ Zr.length - 1) = 2 * 2 ^ Zr.length - 1 := by omega
  rw [htv_out]
  have hq0 : 2 ≤ q0 := q2_V0 .L1 c4 h j p0 q0 (Zr.length + 1) h0 (by omega) (by intro hX; nomatch hX)
  exact ob_endlast c4 h j p0 q0 Zr.length hq0 h0

lemma inv_Ov (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h p1 q1 : Nat) (Z : List Tri) (t : Nat)
    (htr : ovtr ph ph' c4' Xp) (ht1 : ph = .L2 → 2 ≤ t) (ht2 : ph ≠ .L2 → t = 1)
    (hZ : List.Forall dig0 Z) (hX : lastOK Xp Z)
    (hA : AllI (PCx ph false h) 1 ((p1 + 2, q1, false) :: Z)) :
    AllI (PCx ph' c4' 2) 1 ((h + 5, p1 + 1, false) :: ovp q1 Z t) := by
  dsimp [AllI] at hA ⊢
  rcases hA with ⟨hH, hA'⟩
  have hH' := hH
  dsimp [PCx, Lift] at hH'
  have hz0 : List.Forall dig0 ((p1 + 2, q1, false) :: Z) := by
    rw [List.forall_cons]; exact ⟨rfl, hZ⟩
  rw [dv_zero _ hz0] at hH'
  refine ⟨?_, AllI_ovp ph ph' c4' Xp h t htr ht1 ht2 Z 1 (p1 + 2) q1 (by omega) hZ hX hH' hA'⟩
  dsimp [PCx, Lift]
  rw [ovp_len]
  have hdv : dv ((h + 5, p1 + 1, false) :: ovp q1 Z t) = 2 * (2 * 2 ^ Z.length) - 2 := by
    dsimp [dv, bv]
    have E := ovp_dv q1 Z t
    rw [pow_S] at E
    omega
  rw [hdv]
  exact ob_ov_head ph ph' c4' Xp h p1 q1 Z.length htr hH'

lemma inv_X1 (h p1 q1 : Nat) (Z : List Tri) (pa pb : Nat)
    (hZ : List.Forall dig0 Z)
    (hA : AllI (PCx .LX false h) 1 ((p1 + 2, q1, false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)]))) :
    AllI (PCx .T0 false 2) 1 ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) := by
  dsimp [AllI] at hA ⊢
  rcases hA with ⟨hH, hA'⟩
  have hH' := hH
  dsimp [PCx, Lift] at hH'
  have hz0 : List.Forall dig0 ((p1 + 2, q1, false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) := by
    rw [List.forall_cons]; refine ⟨rfl, ?_⟩
    rw [List.forall_append]; exact ⟨hZ, by simp [dig0, dig]⟩
  rw [dv_zero _ hz0] at hH'
  rw [List.length_append] at hH'
  dsimp [List.length] at hH'
  refine ⟨?_, AllI_ovpX h pa pb Z 1 (p1 + 2) q1 (by omega) hZ hH' hA'⟩
  dsimp [PCx, Lift]
  rw [ovpX_len]
  have hdv : dv ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) = 2 * 2 ^ Z.length - 2 := by
    dsimp [dv, bv]
    have E := ovpX_dv q1 Z (pa + 1)
    omega
  rw [hdv]
  exact ob_x1_head h p1 q1 Z.length hH'

structure St where
  sh : Nat
  sP : List Tri
  sT : Tl
  sph : Phase
  sc4 : Bool

def Cf (s : St) : Cfg (Fin 2) (Fin 6) :=
  K s.sh s.sP s.sT

def TC (ph : Phase) (c4 : Bool) (T : Tl) : Prop :=
  match ph with
  | .E1 | .E1t | .LX => T = .TN ∧ c4 = false
  | .L1 => T = .TN
  | .E2 | .E2t => T = .TA 1 ∧ c4 = false
  | .T0 => (∃ k, T = .TB k ∧ 3 ≤ k) ∧ c4 = false
  | .L2 => ∃ t, T = .TA t ∧ 2 ≤ t

def J (s : St) : Prop :=
  s.sP ≠ [] ∧ TC s.sph s.sc4 s.sT ∧ AllI (PCx s.sph s.sc4 s.sh) 1 s.sP

lemma split1 (P : List Tri) :
    (∃ Z x R, P = Z ++ x :: R ∧ List.Forall dig0 Z ∧ dig x = true) ∨ List.Forall dig0 P := by
  induction P with
  | nil => exact Or.inr trivial
  | cons x P ih =>
    rcases x with ⟨p, q, d⟩
    cases d with
    | true => exact Or.inl ⟨[], (p, q, true), P, rfl, trivial, rfl⟩
    | false =>
      rcases ih with ⟨Z, x, R, rfl, hZ, hx⟩ | h0
      · refine Or.inl ⟨(p, q, false) :: Z, x, R, rfl, ?_, hx⟩
        rw [List.forall_cons]; exact ⟨rfl, hZ⟩
      · refine Or.inr ?_
        rw [List.forall_cons]; exact ⟨rfl, h0⟩

lemma exists_last {α : Type*} {P : List α} (hne : P ≠ []) :
    ∃ Z y, P = Z ++ [y] := by
  induction P with
  | nil => contradiction
  | cons x P ih =>
    cases P with
    | nil => exact ⟨[], x, rfl⟩
    | cons y P' =>
      rcases ih (by intro h; nomatch h) with ⟨Z, last, hP⟩
      refine ⟨x :: Z, last, ?_⟩
      simp [hP]

lemma Forall_snoc_inv {α : Type*} (Pr : α → Prop) (Z : List α) (y : α)
    (h : List.Forall Pr (Z ++ [y])) : List.Forall Pr Z ∧ Pr y := by
  rw [List.forall_append] at h
  rcases h with ⟨h1, h2⟩
  rw [List.forall_cons] at h2
  exact ⟨h1, h2.1⟩

lemma Z_okL_V0 (ph : Phase) (c4 : Bool) (h : Nat) (y : Tri) (hph : ph ≠ .LX)
    (Z : List Tri) (i : Nat) (hZ : List.Forall dig0 (Z ++ [y]))
    (hA : AllI (PCx ph c4 h) i (Z ++ [y])) : List.Forall okL Z := by
  induction Z generalizing i with
  | nil => trivial
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [List.cons_append] at hZ hA
    rw [List.forall_cons] at hZ ⊢
    rcases hZ with ⟨hd, hZ'⟩
    dsimp [dig0, dig] at hd
    subst hd
    dsimp [AllI] at hA
    rcases hA with ⟨hH, hA'⟩
    refine ⟨⟨rfl, ?_⟩, ih (i + 1) hZ' hA'⟩
    dsimp [PCx, Lift] at hH
    have hz0 : List.Forall dig0 ((p, q, false) :: (Z ++ [y])) := by
      rw [List.forall_cons]; exact ⟨rfl, hZ'⟩
    rw [dv_zero _ hz0] at hH
    apply q2_V0 ph c4 h i p q (Z ++ [y]).length hH
    · rw [List.length_append]; dsimp [List.length]; omega
    · intro hX; contradiction

lemma last_pc (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p q : Nat) (d : Bool)
    (hZ : List.Forall dig0 (Z ++ [(p, q, d)]))
    (hA : AllI (PCx ph c4 h) 1 (Z ++ [(p, q, d)])) :
    d = false ∧ PC ph c4 h (1 + Z.length) p q 0 0 := by
  rcases Forall_snoc_inv dig0 Z (p, q, d) hZ with ⟨_, hd⟩
  dsimp [dig0, dig] at hd
  subst hd
  have hB := AllI_app (PCx ph c4 h) Z 1 [(p, q, false)] hA
  dsimp [AllI, PCx, Lift, List.length, dv, bv] at hB
  exact ⟨rfl, hB.1⟩

lemma first_pc (ph : Phase) (c4 : Bool) (h p q : Nat) (d : Bool) (Z : List Tri)
    (hZ : List.Forall dig0 ((p, q, d) :: Z))
    (hA : AllI (PCx ph c4 h) 1 ((p, q, d) :: Z)) :
    d = false ∧ PC ph c4 h 1 p q Z.length 0 ∧ List.Forall dig0 Z ∧ AllI (PCx ph c4 h) 2 Z := by
  rw [List.forall_cons] at hZ
  rcases hZ with ⟨hd, hZ'⟩
  dsimp [dig0, dig] at hd
  subst hd
  dsimp [AllI] at hA
  rcases hA with ⟨hH, hA'⟩
  dsimp [PCx, Lift] at hH
  have hz0 : List.Forall dig0 ((p, q, false) :: Z) := by
    rw [List.forall_cons]; exact ⟨rfl, hZ'⟩
  rw [dv_zero _ hz0] at hH
  exact ⟨rfl, hH, hZ', hA'⟩

lemma Jstep (s : St) (hs : J s) : ∃ s', ((Cf s) [target_tm]⊢⁺ (Cf s')) ∧ J s' := by
  rcases s with ⟨h, P, T, ph, c4⟩
  rcases hs with ⟨hP, hT, hA⟩
  dsimp [Cf] at hP hT hA ⊢
  rcases split1 P with ⟨Z, ⟨p, q, d⟩, R, rfl, hZ, hd⟩ | h0
  · dsimp [dig] at hd; subst hd
    have hZL : List.Forall okL Z := Z_okL ph c4 h Z 1 (p, q, true) R hZ rfl hA
    have hB := AllI_app (PCx ph c4 h) Z 1 ((p, q, true) :: R) hA
    dsimp [AllI] at hB
    rcases hB with ⟨hx, hR⟩
    have hx' := hx
    dsimp [PCx, Lift] at hx'
    rcases q with _ | _ | q
    · rcases hx' with ⟨_, hq, _⟩; omega
    · rcases borrow1 ph c4 h (1 + Z.length) p R.length (dv ((p, 1, true) :: R))
        (by omega) (by dsimp [dv, bv]; omega) hx' with ⟨hph, hk, hL1, hLX⟩
      cases R with
      | nil =>
        cases T with
        | TN =>
          exfalso
          rcases hph with rfl | rfl | rfl
          · rcases hL1 rfl with ⟨hn, _⟩; dsimp [List.length] at hn; omega
          · rcases hT with ⟨t, ht, _⟩; nomatch ht
          · have hX := hLX rfl; dsimp [List.length] at hX; omega
        | TA t =>
          have hphL2 : ph = .L2 := by
            rcases hph with rfl | rfl | rfl
            · dsimp [TC] at hT; nomatch hT
            · rfl
            · dsimp [TC] at hT; nomatch hT.1
          subst hphL2
          rcases hT with ⟨t', ht, ht2⟩
          cases ht
          rcases inv_MT c4 h Z p hZ hA with ⟨hA', hlen⟩
          refine ⟨⟨4 + h, Z.map touch, .TA (p + t + 3), .L2, false⟩, ?_, ?_⟩
          · exact DecMergeTail h Z p t hZL
          · refine ⟨by cases Z <;> dsimp [List.length] at hlen ⊢ <;> first | omega | (intro h; nomatch h), ?_, hA'⟩
            exact ⟨p + t + 3, rfl, by omega⟩
        | TB k =>
          exfalso
          rcases hph with rfl | rfl | rfl
          · dsimp [TC] at hT; nomatch hT
          · rcases hT with ⟨t, ht, _⟩; nomatch ht
          · dsimp [TC] at hT; nomatch hT.1
      | cons r1 R0 =>
        rcases r1 with ⟨p', q', d'⟩
        refine ⟨⟨4 + h, Z.map touch ++ (p + p' + 3, q', d') :: R0, T, ph, c4⟩, ?_, ?_⟩
        · exact DecMerge h Z p p' q' d' R0 T hZL
        · refine ⟨by cases Z <;> (intro h; nomatch h), hT, inv_Merge ph c4 h Z p p' q' d' R0 hZ hA⟩
    · refine ⟨⟨4 + h, Z.map touch ++ (p + 1, q + 1, false) :: R, T, ph, c4⟩, ?_, ?_⟩
      · exact Dec h Z p q R T hZL
      · refine ⟨by cases Z <;> (intro h; nomatch h), hT, inv_Dec ph c4 h Z p q R hZ hA⟩
  · cases ph with
    | E1 =>
      rcases hT with ⟨rfl, rfl⟩
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc .E1 false h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN; omega
      rcases q with _ | _ | q; · omega
      · omega
      have hZL : List.Forall okL Z := Z_okL_V0 .E1 false h (p, q + 2, false) (by decide) Z 1 h0 hA
      rcases Forall_snoc_inv dig0 Z (p, q + 2, false) h0 with ⟨hZ, _⟩
      refine ⟨⟨4 + h, Z.map touch ++ [(p + 1, q + 1, false)], .TA 1, .E2, false⟩, ?_, ?_⟩
      · exact EndR h Z p q hZL
      · refine ⟨snoc_nn _ _, ⟨rfl, rfl⟩, inv_End .E1 .E2 h Z p q (Or.inl ⟨rfl, rfl⟩) hZ hA⟩
    | E2 =>
      rcases hT with ⟨rfl, rfl⟩
      cases P with
      | nil => contradiction
      | cons x Z =>
        rcases x with ⟨p1, q1, d1⟩
        rcases first_pc .E2 false h p1 q1 d1 Z h0 hA with ⟨rfl, hH, hZ, hA2⟩
        have hp1 := p1_V0 .E2 false h p1 q1 Z.length hH (Or.inl rfl)
        rcases p1 with _ | _ | p1; · omega
        · omega
        rcases AllI_okRO .E2 false h Z 2 hZ hA2 with ⟨hR, hO⟩
        have hq1 : 1 ≤ q1 := hH.2.1
        rcases lastOK_dec Z with hX | hX
        · refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, .TN, .LX, false⟩, ?_, ?_⟩
          · exact Ov h p1 q1 Z 1 hq1 hR hO
          · refine ⟨(by intro h'; nomatch h'), ⟨rfl, rfl⟩, inv_Ov .E2 .LX false (fun x => x = 4) h p1 q1 Z 1
              (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (by decide) (fun _ => rfl) hZ hX hA⟩
        · refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, .TN, .L1, false⟩, ?_, ?_⟩
          · exact Ov h p1 q1 Z 1 hq1 hR hO
          · refine ⟨(by intro h'; nomatch h'), rfl, inv_Ov .E2 .L1 false (fun x => x ≠ 4) h p1 q1 Z 1
              (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by decide) (fun _ => rfl) hZ hX hA⟩
    | E1t =>
      rcases hT with ⟨rfl, rfl⟩
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc .E1t false h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN; omega
      rcases q with _ | _ | q; · omega
      · omega
      have hZL : List.Forall okL Z := Z_okL_V0 .E1t false h (p, q + 2, false) (by decide) Z 1 h0 hA
      rcases Forall_snoc_inv dig0 Z (p, q + 2, false) h0 with ⟨hZ, _⟩
      refine ⟨⟨4 + h, Z.map touch ++ [(p + 1, q + 1, false)], .TA 1, .E2t, false⟩, ?_, ?_⟩
      · exact EndR h Z p q hZL
      · refine ⟨snoc_nn _ _, ⟨rfl, rfl⟩, inv_End .E1t .E2t h Z p q (Or.inr ⟨rfl, rfl⟩) hZ hA⟩
    | E2t =>
      rcases hT with ⟨rfl, rfl⟩
      cases P with
      | nil => contradiction
      | cons x Z =>
        rcases x with ⟨p1, q1, d1⟩
        rcases first_pc .E2t false h p1 q1 d1 Z h0 hA with ⟨rfl, hH, hZ, hA2⟩
        have hp1 := p1_V0 .E2t false h p1 q1 Z.length hH (Or.inr (Or.inl rfl))
        rcases p1 with _ | _ | p1; · omega
        · omega
        rcases AllI_okRO .E2t false h Z 2 hZ hA2 with ⟨hR, hO⟩
        have hq1 : 1 ≤ q1 := hH.2.1
        refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, .TN, .L1, true⟩, ?_, ?_⟩
        · exact Ov h p1 q1 Z 1 hq1 hR hO
        · refine ⟨(by intro h'; nomatch h'), rfl, inv_Ov .E2t .L1 true (fun _ => True) h p1 q1 Z 1
            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))) (by decide) (fun _ => rfl) hZ (lastOK_True Z) hA⟩
    | T0 =>
      rcases hT with ⟨⟨k, rfl, hk⟩, rfl⟩
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc .T0 false h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN; omega
      rcases q with _ | _ | q; · omega
      · omega
      rcases k with _ | k; · omega
      have hZL : List.Forall okL Z := Z_okL_V0 .T0 false h (p, q + 2, false) (by decide) Z 1 h0 hA
      rcases Forall_snoc_inv dig0 Z (p, q + 2, false) h0 with ⟨hZ, _⟩
      refine ⟨⟨4 + h, Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)], .TN, .E1t, false⟩, ?_, ?_⟩
      · exact X2 h Z p q k hZL
      · refine ⟨(by cases Z <;> (intro h'; nomatch h')), ⟨rfl, rfl⟩, inv_X2 h Z p q (k + 1) hZ hk hA⟩
    | L1 =>
      dsimp [TC] at hT; subst hT
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc .L1 c4 h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : q = 1 := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN; omega
      subst hq
      have hZL : List.Forall okL Z := Z_okL_V0 .L1 c4 h (p, 1, false) (by decide) Z 1 h0 hA
      rcases Forall_snoc_inv dig0 Z (p, 1, false) h0 with ⟨hZ, _⟩
      rcases inv_EndLast c4 h Z p hZ hA with ⟨hA', hlen⟩
      refine ⟨⟨4 + h, Z.map touch, .TA (p + 4), .L2, c4⟩, ?_, ?_⟩
      · exact EndLast h Z p hZL
      · refine ⟨(by cases Z <;> dsimp [List.length] at hlen ⊢ <;> first | omega | (intro h'; nomatch h')), ?_, hA'⟩
        exact ⟨p + 4, rfl, by omega⟩
    | L2 =>
      rcases hT with ⟨t, rfl, ht⟩
      cases c4 with
      | true =>
        exfalso
        rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
        rcases last_pc .L2 true h Z p q d h0 hA with ⟨rfl, hy⟩
        exact L2_c4_V0 h (1 + Z.length) p q hy
      | false =>
        cases P with
        | nil => contradiction
        | cons x Z =>
          rcases x with ⟨p1, q1, d1⟩
          rcases first_pc .L2 false h p1 q1 d1 Z h0 hA with ⟨rfl, hH, hZ, hA2⟩
          have hp1 := p1_V0 .L2 false h p1 q1 Z.length hH (Or.inr (Or.inr (Or.inl rfl)))
          rcases p1 with _ | _ | p1; · omega
          · omega
          rcases AllI_okRO .L2 false h Z 2 hZ hA2 with ⟨hR, hO⟩
          have hq1 : 1 ≤ q1 := hH.2.1
          refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z t, .TN, .E1, false⟩, ?_, ?_⟩
          · exact Ov h p1 q1 Z t hq1 hR hO
          · refine ⟨(by intro h'; nomatch h'), ⟨rfl, rfl⟩, inv_Ov .L2 .E1 false (fun _ => True) h p1 q1 Z t
              (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))) (fun _ => ht) (fun h' => (h' rfl).elim)
              hZ (lastOK_True Z) hA⟩
    | LX =>
      rcases hT with ⟨rfl, rfl⟩
      have hlen := AllI_len .LX false h P hP hA
      dsimp [minlen] at hlen
      rcases exists_last hP with ⟨P1, ⟨pb, qb, db⟩, rfl⟩
      have hP1 : P1 ≠ [] := by
        cases P1 <;> dsimp [List.length] at hlen <;> first | omega | (intro h'; nomatch h')
      rcases exists_last hP1 with ⟨P2, ⟨pa, qa, da⟩, rfl⟩
      cases P2 with
      | nil => dsimp [List.length] at hlen; omega
      | cons x Z =>
        rcases x with ⟨p1, q1, d1⟩
        simp only [List.cons_append, List.append_assoc, List.nil_append] at h0 hA ⊢
        rcases first_pc .LX false h p1 q1 d1 (Z ++ [(pa, qa, da), (pb, qb, db)]) h0 hA with
          ⟨rfl, hH, hZab, hA2⟩
        rw [List.forall_append] at hZab
        rcases hZab with ⟨hZ, hab⟩
        rw [List.forall_cons, List.forall_cons] at hab
        rcases hab with ⟨hda, hdb, _⟩
        dsimp [dig0, dig] at hda hdb
        subst hda; subst hdb
        have hB := AllI_app (PCx .LX false h) Z 2 [(pa, qa, false), (pb, qb, false)] hA2
        dsimp [AllI, PCx, Lift, List.length, dv, bv] at hB
        rcases hB with ⟨ha, hb, _⟩
        have hqa : qa = 1 := by rcases ha with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN; omega
        have hqb : qb = 1 := by rcases hb with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] at hN; omega
        subst hqa; subst hqb
        have hpa : 1 ≤ pa := ha.1
        rcases pa with _ | pa; · omega
        have hp1 := p1_V0 .LX false h p1 q1 (Z ++ [(pa + 1, 1, false), (pb, 1, false)]).length hH
          (Or.inr (Or.inr (Or.inr rfl)))
        rcases p1 with _ | _ | p1; · omega
        · omega
        have hZab' : List.Forall dig0 (Z ++ [(pa + 1, 1, false), (pb, 1, false)]) := by
          rw [List.forall_append]; exact ⟨hZ, by simp [dig0, dig]⟩
        rcases AllI_okRO .LX false h (Z ++ [(pa + 1, 1, false), (pb, 1, false)]) 2 hZab' hA2 with ⟨hR, hO⟩
        rw [List.forall_append] at hR hO
        have hq1 : 1 ≤ q1 := hH.2.1
        refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1), .TB (pb + 3), .T0, false⟩, ?_, ?_⟩
        · exact X1 h p1 q1 Z pa pb hq1 hR.1 hO.1
        · refine ⟨(by intro h'; nomatch h'), ⟨⟨pb + 3, rfl, by omega⟩, rfl⟩, inv_X1 h p1 q1 Z pa pb hZ hA⟩

lemma J_base : J ⟨2, base, .TN, .E1, false⟩ := by
  dsimp [J, base, TC, AllI, PCx, Lift, PC, PN, PI, dv, bv, List.length]
  refine ⟨(by intro h'; nomatch h'), ⟨rfl, rfl⟩, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]; decide
def InvCfg (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ s : St, cfg = Cf s ∧ J s

lemma inv_init : ∃ cfg₀, ((init []) [target_tm]⊢* cfg₀) ∧ InvCfg cfg₀ :=
  ⟨Cf ⟨2, base, .TN, .E1, false⟩, init_to_base, ⟨⟨2, base, .TN, .E1, false⟩, rfl, J_base⟩⟩

lemma inv_step (cfg : Cfg (Fin 2) (Fin 6)) (h : InvCfg cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧ InvCfg cfg' := by
  rcases h with ⟨s, rfl, hs⟩
  rcases Jstep s hs with ⟨s', hstep, hs'⟩
  exact ⟨Cf s', hstep, ⟨s', rfl, hs'⟩⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  closed_inv_does_not_halt target_tm InvCfg inv_init inv_step

end BusyBeaver.M_1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RDHHH
