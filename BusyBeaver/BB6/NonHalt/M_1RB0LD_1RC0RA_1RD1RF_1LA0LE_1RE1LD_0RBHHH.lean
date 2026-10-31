/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

-- ============================================================================
-- Section 1: Step Infrastructure, ListBlank Rotation Identities, Shifts & Bounces
-- ============================================================================

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
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
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
    (s <+ u) <+ (u ^ k) = s <+ (u ^ (k + 1)) := by
  rw [listblank_append_append, list_pow_append_one]

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

lemma stepPlus_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, _, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))
local macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

lemma multiStep_step_isSome {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₀ cfg cfg' : Cfg Γ Λ) (n m : Nat)
    (hn : multiStep M c₀ n = some cfg)
    (hnm : multiStep M c₀ (n + (1 + m)) = some cfg') :
    (step M cfg).isSome := by
  rw [multiStep_add M c₀ n (1 + m), hn] at hnm
  dsimp [Option.bind] at hnm
  rw [multiStep_add M cfg 1 m, multiStep_one] at hnm
  cases hs : step M cfg with
  | none =>
    rw [hs] at hnm
    nomatch hnm
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
    IsDoesNotHalt M := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome M (init []) cfg cfg' n m hn hnm

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl

lemma pow_01_cons_zero (k : Nat) (r : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> r) =
    (0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_append_right, pow_succ_append_right]
    dsimp [ListBlank.append]
    rw [ih]

lemma pow_01_cons_one (k : Nat) (r : ListBlank (Fin 2)) :
    (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> r) =
    (([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_append_right, pow_succ_append_right]
    dsimp [ListBlank.append]
    rw [← ih]

lemma pow_10_cons_one (k : Nat) (r : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> r) =
    (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> r) :=
  (pow_01_cons_one k r).symm

lemma left_pow_10_succ (l : ListBlank (Fin 2)) (k : Nat) :
    l <+ (([1, 0] : List (Fin 2)) ^ (k + 1)) =
    ((l <+ [0]) <+ (([0, 1] : List (Fin 2)) ^ k)) <+ [1] := by
  change (([1, 0] : List (Fin 2)) ^ (k + 1)) +> l = (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> l))
  rw [pow_01_cons_one]
  exact (pow_succ_append_right' [1, 0] k l).symm

lemma left_pow_01_one (l : ListBlank (Fin 2)) (k : Nat) :
    (l <+ (([0, 1] : List (Fin 2)) ^ k)) <+ [1] =
    (l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ k) := by
  change (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> l) = (([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> l)
  exact pow_01_cons_one k l

-- 5 Elementary Shift Lemmas
lemma shift_AB_R (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((l <+ (([0, 1] : List (Fin 2)) ^ k)) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{A}}> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> r))) [target_tm]⊢*
        ((l <+ [0, 1]) {{A}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih (l <+ [0, 1]) r
    rw [pow_succ_append_left] at h2
    exact stepStar_trans h1 h2

lemma shift_BA_R (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) {{B}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{B}}> ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r))) [target_tm]⊢*
        ((l <+ [1, 0]) {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih (l <+ [1, 0]) r
    rw [pow_succ_append_left] at h2
    exact stepStar_trans h1 h2

lemma shift_AD_L (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{A}} r) [target_tm]⊢*
    (l <{{A}} ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [1, 0]) <{{A}} r) [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{A}} ([1, 0] +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([1, 0] +> r)
    rw [pow_succ_append_right'] at h2
    exact stepStar_trans h1 h2

lemma shift_DA_L (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([0, 1] : List (Fin 2)) ^ k)) <{{D}} r) [target_tm]⊢*
    (l <{{D}} ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([0, 1] : List (Fin 2)) ^ k)) <+ [0, 1]) <{{D}} r) [target_tm]⊢*
        ((l <+ (([0, 1] : List (Fin 2)) ^ k)) <{{D}} ([0, 1] +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([0, 1] +> r)
    rw [pow_succ_append_right'] at h2
    exact stepStar_trans h1 h2

lemma shift_DE_L1 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{D}} ((1 : Fin 2) >> r)) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ k)) <+ [1, 0]) <{{D}} ((1 : Fin 2) >> r)) [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ k)) <{{D}} ((1 : Fin 2) >> ([0, 1] +> r))) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([0, 1] +> r)
    rw [pow_10_cons_one k ([0, 1] +> r), pow_succ_append_right', ← pow_10_cons_one (k + 1) r] at h2
    exact stepStar_trans h1 h2

-- 3 Bounce Helpers
lemma bounce_00_01_cap1 (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ k)) <{{D}} ((1 : Fin 2) >> r)) [target_tm]⊢⁺
    ((l <+ [1]) <{{A}} ((([1, 0] : List (Fin 2)) ^ (k + 1)) +> r)) := by
  have h1 := shift_DA_L k (l <+ [0, 0]) ((1 : Fin 2) >> r)
  have h2 : ((l <+ [0, 0]) <{{D}} ((([0, 1] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> r))) [target_tm]⊢⁺
      ((l <+ [1]) {{B}}> ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> r)))) := by
    dsimp [ListBlank.append]; execute
  rw [pow_01_cons_one k ((1 : Fin 2) >> r)] at h2
  have h3 := shift_BA_R k (l <+ [1]) ((1 : Fin 2) >> ((1 : Fin 2) >> r))
  have h4 : (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ k)) {{B}}> ((1 : Fin 2) >> ((1 : Fin 2) >> r))) [target_tm]⊢⁺
      (((l <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ k)) <{{A}} ([1, 0] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h5 := shift_AD_L k (l <+ [1]) ([1, 0] +> r)
  rw [pow_succ_append_right'] at h5
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_trans h2 (stepStar_stepPlus_stepPlus h3 (stepPlus_stepStar_stepPlus h4 h5)))

lemma sweep_E_left_011_10 (q : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <{{E}} r) [target_tm]⊢⁺
    (l <{{D}} ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ((0 : Fin 2) >> r)))) := by
  have h_lhs : ((l <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) =
      ((((l <+ [1, 1]) <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ q)) <+ [1]) := by
    rw [left_pow_10_succ]
    simp only [listblank_append_append]; rfl
  rw [h_lhs]
  have h1 : (((((l <+ [1, 1]) <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ q)) <+ [1]) <{{E}} r) [target_tm]⊢⁺
      ((((l <+ [1, 1]) <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ q)) <{{D}} ((1 : Fin 2) >> r)) := by
    dsimp [ListBlank.append]; execute
  have h2 := bounce_00_01_cap1 q (l <+ [1, 1]) r
  have h_rhs : ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r) =
      (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ q) +> ((0 : Fin 2) >> r)) := by
    rw [pow_01_cons_one]
    exact (pow_succ_append_right' [1, 0] q r).symm
  rw [h_rhs] at h2
  have h3 : (((l <+ [1, 1]) <+ [1]) <{{A}} ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ q) +> ((0 : Fin 2) >> r)))) [target_tm]⊢⁺
      (l <{{D}} ([1, 0] +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ q) +> ((0 : Fin 2) >> r))))) := by
    dsimp [ListBlank.append]; execute
  rw [← pow_succ_append_right [0, 1] q ((0 : Fin 2) >> r)] at h3
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

lemma sweep_E_left_0_10 (p : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <{{E}} r) [target_tm]⊢⁺
    (l <{{D}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ((0 : Fin 2) >> r))) := by
  have h_lhs : ((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) =
      (((l <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ p)) <+ [1]) := by
    rw [left_pow_10_succ]
    simp only [listblank_append_append]; rfl
  rw [h_lhs]
  have h1 : ((((l <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ p)) <+ [1]) <{{E}} r) [target_tm]⊢⁺
      (((l <+ [0, 0]) <+ (([0, 1] : List (Fin 2)) ^ p)) <{{D}} ((1 : Fin 2) >> r)) := by
    dsimp [ListBlank.append]; execute
  have h2 := bounce_00_01_cap1 p l r
  have h_rhs : ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> r) =
      (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ p) +> ((0 : Fin 2) >> r)) := by
    rw [pow_01_cons_one]
    exact (pow_succ_append_right' [1, 0] p r).symm
  rw [h_rhs] at h2
  have h3 : ((l <+ [1]) <{{A}} ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ p) +> ((0 : Fin 2) >> r)))) [target_tm]⊢⁺
      (l <{{D}} ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ p) +> ((0 : Fin 2) >> r)))) := by
    dsimp [ListBlank.append]; execute
  rw [← pow_succ_append_right [0, 1] p ((0 : Fin 2) >> r)] at h3
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

lemma round_A_10_cap11 (k : Nat) (r : ListBlank (Fin 2)) :
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ k) +> ([1, 1] +> r))) [target_tm]⊢⁺
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ (k + 2)) +> r)) := by
  have h1 : (default <{{A}} ((([1, 0] : List (Fin 2)) ^ k) +> ([1, 1] +> r))) [target_tm]⊢⁺
      ((default <+ [1]) {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> ([1, 1] +> r))) := by
    dsimp [ListBlank.append]; execute
  have h2 := shift_BA_R k (default <+ [1]) ([1, 1] +> r)
  have h3 : (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ k)) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
      (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ k)) <{{A}} ([1, 0] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h4 := shift_AD_L k (default <+ [1]) ([1, 0] +> r)
  rw [pow_succ_append_right'] at h4
  have h5 : ((default <+ [1]) <{{A}} ((([1, 0] : List (Fin 2)) ^ (k + 1)) +> r)) [target_tm]⊢⁺
      (default <{{A}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ (k + 1)) +> r))) := by
    dsimp [ListBlank.append]; execute
  rw [← pow_succ_append_right [1, 0] (k + 1) r] at h5
  exact stepPlus_trans h1 (stepStar_stepPlus_stepPlus h2 (stepPlus_trans h3 (stepStar_stepPlus_stepPlus h4 h5)))

lemma round_A_10_cap001 (k : Nat) (r : ListBlank (Fin 2)) :
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ k) +> ([0, 0, 1] +> r))) [target_tm]⊢⁺
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ k) +> ([1, 1] +> ([0, 1, 0] +> r)))) := by
  have h1 : (default <{{A}} ((([1, 0] : List (Fin 2)) ^ k) +> ([0, 0, 1] +> r))) [target_tm]⊢⁺
      ((default <+ [1]) {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> ([0, 0, 1] +> r))) := by
    dsimp [ListBlank.append]; execute
  have h2 := shift_BA_R k (default <+ [1]) ([0, 0, 1] +> r)
  rw [← left_pow_01_one default k] at h2
  have h3 : (((default <+ (([0, 1] : List (Fin 2)) ^ k)) <+ [1]) {{B}}> ([0, 0, 1] +> r)) [target_tm]⊢⁺
      ((default <+ (([0, 1] : List (Fin 2)) ^ k)) <{{D}} ([1, 0, 1, 0] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h4 := shift_DA_L k default ([1, 0, 1, 0] +> r)
  have h5 : (default <{{D}} ((([0, 1] : List (Fin 2)) ^ k) +> ([1, 0, 1, 0] +> r))) [target_tm]⊢⁺
      (default <{{A}} ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> ([1, 0, 1, 0] +> r)))) := by
    dsimp [ListBlank.append]; execute
  rw [pow_01_cons_one k ([1, 0, 1, 0] +> r)] at h5
  have h_eq : ((1 : Fin 2) >> ([1, 0, 1, 0] +> r)) = ([1, 1] +> ([0, 1, 0] +> r)) := rfl
  rw [h_eq] at h5
  exact stepPlus_trans h1 (stepStar_stepPlus_stepPlus h2 (stepPlus_trans h3 (stepStar_stepPlus_stepPlus h4 h5)))

-- ============================================================================
-- Section 2: The 14 Low-Level Sweeps
-- ============================================================================

-- 1. Start
lemma Start (h : Nat) (r : ListBlank (Fin 2)) :
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) {{B}}> r) := by
  have h_eq1 : ([1, 1, 0, 0, 1] +> r) = ([1, 1] +> ([0, 0, 1] +> r)) := rfl
  rw [h_eq1]
  have h1 := round_A_10_cap11 h ([0, 0, 1] +> r)
  have h2 := round_A_10_cap001 (h + 2) r
  have h3 := round_A_10_cap11 (h + 2) ([0, 1, 0] +> r)
  have h_add : (h + 2) + 2 = 4 + h := by omega
  rw [h_add] at h3
  have h4 : (default <{{A}} ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ([0, 1, 0] +> r))) [target_tm]⊢⁺
      ((default <+ [1]) {{B}}> ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ([0, 1, 0] +> r))) := by
    dsimp [ListBlank.append]; execute
  have h5 := shift_BA_R (4 + h) (default <+ [1]) ([0, 1, 0] +> r)
  rw [← left_pow_01_one default (4 + h)] at h5
  have h6 : (((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1]) {{B}}> ([0, 1, 0] +> r)) [target_tm]⊢⁺
      ((((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) {{B}}> r) := by
    dsimp [ListBlank.append]; execute
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3
    (stepPlus_trans h4 (stepStar_stepPlus_stepPlus h5 h6))))

-- 2. PassR
lemma PassR (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{B}}> ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) [target_tm]⊢*
    (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <+ [0]) {{B}}> r) := by
  have h_mid : ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)) =
      [0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([0, 1, 0] +> r)) := by
    rw [pow_succ_append_right]
    dsimp [ListBlank.append]
    rw [pow_01_cons_zero]
  rw [h_mid]
  have h1 := shift_BA_R p (l <+ [0]) ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([0, 1, 0] +> r)))
  have h2 : (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) {{B}}>
      ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ q) +> ([0, 1, 0] +> r)))) [target_tm]⊢*
      ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) {{B}}>
      ((([1, 0] : List (Fin 2)) ^ q) +> ([0, 1, 0] +> r))) := by
    dsimp [ListBlank.append]; execute
  have h3 := shift_BA_R q (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) ([0, 1, 0] +> r)
  have h4 : (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) {{B}}>
      ([0, 1, 0] +> r)) [target_tm]⊢*
      (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <+ [0]) {{B}}> r) := by
    dsimp [ListBlank.append]; execute
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

-- 3. Borrow
lemma Borrow (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    (l {{B}}> ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ (q + 2)) +> ([0, 0, 0, 1] +> r)))) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) := by
  have h_mid : ((([0, 1] : List (Fin 2)) ^ (q + 2)) +> ([0, 0, 0, 1] +> r)) =
      [0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1] +> r)) := by
    rw [pow_succ_append_right]
    dsimp [ListBlank.append]
    rw [pow_01_cons_zero]
  rw [h_mid]
  have h1 := shift_BA_R p l ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1] +> r)))
  have h2 : ((l <+ (([1, 0] : List (Fin 2)) ^ p)) {{B}}>
      ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1] +> r)))) [target_tm]⊢*
      (((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) {{B}}>
      ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1] +> r))) := by
    dsimp [ListBlank.append]; execute
  have h3 := shift_BA_R (q + 1) ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) ([0, 0, 1] +> r)
  have h4 : ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) {{B}}>
      ([0, 0, 1] +> r)) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <{{E}}
      ([0, 1, 0] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h5 := stepPlus_stepStar (sweep_E_left_011_10 q (l <+ (([1, 0] : List (Fin 2)) ^ p)) ([0, 1, 0] +> r))
  have h_eq5 : ((0 : Fin 2) >> ([0, 1, 0] +> r)) = ([0, 0, 1, 0] +> r) := rfl
  rw [h_eq5] at h5
  have h6 := shift_DE_L1 p l ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))
  have h_eq6 : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) =
      ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r))) := rfl
  rw [h_eq6, pow_succ_append_right' [1, 0] p] at h6
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- 4. PassL
lemma PassL (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) <{{D}} r) [target_tm]⊢*
    ((l <+ [0]) <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r)))) := by
  have h1 : (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) <{{D}} r) [target_tm]⊢*
      (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <{{E}} ([0, 0, 1] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h2 := stepPlus_stepStar (sweep_E_left_011_10 q ((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) ([0, 0, 1] +> r))
  have h_eq2 : ((0 : Fin 2) >> ([0, 0, 1] +> r)) = ([0, 0, 0, 1] +> r) := rfl
  rw [h_eq2] at h2
  have h3 := shift_DE_L1 p (l <+ [0]) ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r)))
  have h_eq3 : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r)))) =
      ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r))) := rfl
  rw [h_eq3, pow_succ_append_right' [1, 0] p] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 5. EndPh
lemma EndPh (h : Nat) (r : ListBlank (Fin 2)) :
    ((((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) <{{D}} r) [target_tm]⊢*
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ([1, 1, 0, 0, 1] +> r))) := by
  have h1 : ((((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <+ [0]) <{{D}} r) [target_tm]⊢*
      ((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <{{D}} ([1, 0, 0, 1] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h2 := shift_DA_L (4 + h) default ([1, 0, 0, 1] +> r)
  have h3 : (default <{{D}} ((([0, 1] : List (Fin 2)) ^ (4 + h)) +> ([1, 0, 0, 1] +> r))) [target_tm]⊢*
      (default <{{A}} ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (4 + h)) +> ([1, 0, 0, 1] +> r)))) := by
    dsimp [ListBlank.append]; execute
  rw [pow_01_cons_one (4 + h) ([1, 0, 0, 1] +> r)] at h3
  have h_eq : ((1 : Fin 2) >> ([1, 0, 0, 1] +> r)) = ([1, 1, 0, 0, 1] +> r) := rfl
  rw [h_eq] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 6. EndT
lemma EndT (l : ListBlank (Fin 2)) (p q : Nat) :
    ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{B}}> default) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))) := by
  have h1 : ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{B}}> default) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <{{E}} ([0, 1, 0] +> ([1, 0, 1] +> default))) := by
    dsimp [ListBlank.append]; execute
  have h2 := stepPlus_stepStar (sweep_E_left_011_10 q (l <+ (([1, 0] : List (Fin 2)) ^ p)) ([0, 1, 0] +> ([1, 0, 1] +> default)))
  have h_eq2 : ((0 : Fin 2) >> ([0, 1, 0] +> ([1, 0, 1] +> default))) = ([0, 0, 1, 0] +> ([1, 0, 1] +> default)) := rfl
  rw [h_eq2] at h2
  have h3 := shift_DE_L1 p l ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))
  have h_eq3 : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))) =
      ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default)))) := rfl
  rw [h_eq3, pow_succ_append_right' [1, 0] p] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 7. EndLastT
lemma EndLastT (l : ListBlank (Fin 2)) (p : Nat) :
    (((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) {{B}}> default) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + 4)) +> ([1] +> default))) := by
  have h1 : (((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) {{B}}> default) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{D}} ((([1, 0] : List (Fin 2)) ^ 4) +> ([1] +> default))) := by
    dsimp [ListBlank.append]; execute
  have h2 := shift_DE_L1 p l ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ 3) +> ([1] +> default)))
  have h_eq : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ 3) +> ([1] +> default)))) =
      ((([1, 0] : List (Fin 2)) ^ 4) +> ([1] +> default)) := rfl
  rw [h_eq, ← pow_add_append_right [1, 0] p 4 ([1] +> default)] at h2
  exact stepStar_trans h1 h2

-- 8. MergeB
lemma MergeB (l : ListBlank (Fin 2)) (p p' : Nat) (r : ListBlank (Fin 2)) :
    (l {{B}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r))))) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + p' + 3)) +> r)) := by
  have h1 := shift_BA_R p l ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))
  have h2 : ((l <+ (([1, 0] : List (Fin 2)) ^ p)) {{B}}>
      ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{D}} ((([1, 0] : List (Fin 2)) ^ 3) +> ((([1, 0] : List (Fin 2)) ^ p') +> r))) := by
    dsimp [ListBlank.append]; execute
  have h3 := shift_DE_L1 p l ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ 2) +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))
  have h_eq : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ 2) +> ((([1, 0] : List (Fin 2)) ^ p') +> r)))) =
      ((([1, 0] : List (Fin 2)) ^ 3) +> ((([1, 0] : List (Fin 2)) ^ p') +> r)) := rfl
  rw [← pow_add_append_right [1, 0] 3 p' r] at h2
  rw [h_eq, ← pow_add_append_right [1, 0] 3 p' r, ← pow_add_append_right [1, 0] p (3 + p') r] at h3
  have h_add : p + (3 + p') = p + p' + 3 := by omega
  rw [h_add] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 9. MergeE
lemma MergeE (l : ListBlank (Fin 2)) (p : Nat) :
    (l {{B}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([0, 1] +> ([0, 0, 0, 1] +> default)))) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + 2)) +> ([1] +> default))) := by
  have h1 := shift_BA_R p l ([0, 1] +> ([0, 0, 0, 1] +> default))
  have h2 : ((l <+ (([1, 0] : List (Fin 2)) ^ p)) {{B}}> ([0, 1] +> ([0, 0, 0, 1] +> default))) [target_tm]⊢*
      ((l <+ (([1, 0] : List (Fin 2)) ^ p)) <{{D}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1] +> default))) := by
    dsimp [ListBlank.append]; execute
  have h3 := shift_DE_L1 p l ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ 1) +> ([1] +> default)))
  have h_eq : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ 1) +> ([1] +> default)))) =
      ((([1, 0] : List (Fin 2)) ^ 2) +> ([1] +> default)) := rfl
  rw [h_eq, ← pow_add_append_right [1, 0] p 2 ([1] +> default)] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 10. OvT
lemma OvT (l : ListBlank (Fin 2)) (t : Nat) :
    ((l <+ [0]) {{B}}> ((([1, 0] : List (Fin 2)) ^ t) +> ([1] +> default))) [target_tm]⊢*
    (l <{{D}} ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default))) := by
  have h1 := shift_BA_R t (l <+ [0]) ([1] +> default)
  have h2 : (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ t)) {{B}}> ([1] +> default)) [target_tm]⊢*
      ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ t)) <+ [1, 0]) <{{E}} ([0, 0, 1] +> default)) := by
    dsimp [ListBlank.append]; execute
  have h_lhs : (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ t)) <+ [1, 0]) =
      ((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (t + 1))) := by
    rw [listblank_append_append, ← pow_succ_list]
  rw [h_lhs] at h2
  have h3 := stepPlus_stepStar (sweep_E_left_0_10 t l ([0, 0, 1] +> default))
  have h_eq3 : ((0 : Fin 2) >> ([0, 0, 1] +> default)) = ([0, 0, 0, 1] +> default) := rfl
  rw [h_eq3] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 11. OvL
lemma OvL (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <{{D}} r) [target_tm]⊢*
    (l <{{D}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))) := by
  have h1 : ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <{{D}} r) [target_tm]⊢*
      (((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <{{D}} ((1 : Fin 2) >> ((0 : Fin 2) >> r))) := by
    dsimp [ListBlank.append]; execute
  have h2 := shift_DE_L1 q (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) ((0 : Fin 2) >> r)
  have h_eq2 : ((1 : Fin 2) >> ((0 : Fin 2) >> r)) = ([1, 0] +> r) := rfl
  rw [h_eq2, pow_succ_append_right' [1, 0] q r] at h2
  have h3 : ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <{{D}} ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)) [target_tm]⊢*
      (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <{{E}} ([0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))) := by
    dsimp [ListBlank.append]; execute
  have h4 := stepPlus_stepStar (sweep_E_left_0_10 p l ([0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))
  have h_eq4 : ((0 : Fin 2) >> ([0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r))) =
      ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)) := rfl
  rw [h_eq4] at h4
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

-- Helper for OvEnd (and step 178 -> 275 of init stem)
lemma OvEnd_tail (h p : Nat) (r : ListBlank (Fin 2)) :
    ((default <+ [1]) <{{D}} ((([1, 0] : List (Fin 2)) ^ (5 + h)) +> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r)))) [target_tm]⊢*
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))))) := by
  have h_eq1 : (5 + h) = (4 + h) + 1 := by omega
  rw [h_eq1, pow_succ_append_right]
  have h1 : ((default <+ [1]) <{{D}} ([1, 0] +> ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))))) [target_tm]⊢*
      ((default <+ [0, 1, 1, 1, 0, 1, 0, 1]) {{B}}> ((([1, 0] : List (Fin 2)) ^ (4 + h)) +> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r)))) := by
    dsimp [ListBlank.append]; execute
  have h2 := Borrow (default <+ [0, 1, 1, 1, 0, 1, 0, 1]) (4 + h) p r
  have h_add : (4 + h) + 1 = h + 5 := by omega
  rw [h_add] at h2
  have h3 : ((default <+ [0, 1, 1, 1, 0, 1, 0, 1]) <{{D}} ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))) [target_tm]⊢*
      (default <{{A}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))))) := by
    dsimp [ListBlank.append]; execute
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- 12. OvEnd
lemma OvEnd (h p : Nat) (r : ListBlank (Fin 2)) :
    (((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) <{{D}} ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))) [target_tm]⊢*
    (default <{{A}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))))) := by
  have h_lhs : ((default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]) =
      (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) <+ [1, 1]) := by
    rw [← left_pow_01_one default (4 + h)]
    simp only [listblank_append_append]; rfl
  rw [h_lhs]
  have h1 : ((((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) <+ [1, 1]) <{{D}} ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))) [target_tm]⊢*
      (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (4 + h))) <{{D}} ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))))) := by
    dsimp [ListBlank.append]; execute
  have h2 := shift_DE_L1 (4 + h) (default <+ [1]) ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r)))
  have h_eq2 : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r)))) =
      ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))) := rfl
  rw [h_eq2, pow_succ_append_right' [1, 0] (4 + h)] at h2
  have h_add : (4 + h) + 1 = 5 + h := by omega
  rw [h_add] at h2
  exact stepStar_trans h1 (stepStar_trans h2 (OvEnd_tail h p r))

-- 13. X1Sw
lemma X1Sw (l : ListBlank (Fin 2)) (p : Nat) (r : ListBlank (Fin 2)) :
    ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) <{{D}} r) [target_tm]⊢*
    (l <{{D}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> r))) := by
  have h1 : ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) <{{D}} r) [target_tm]⊢*
      (((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <{{E}} ([0, 1, 0, 1, 0, 1] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h2 := stepPlus_stepStar (sweep_E_left_0_10 p l ([0, 1, 0, 1, 0, 1] +> r))
  have h_eq : ((0 : Fin 2) >> ([0, 1, 0, 1, 0, 1] +> r)) = ([0, 0, 1, 0, 1, 0, 1] +> r) := rfl
  rw [h_eq] at h2
  exact stepStar_trans h1 h2

-- 14. X2T
lemma X2T (l : ListBlank (Fin 2)) (p q k : Nat) :
    ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{B}}>
      ([1, 0, 1, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> default))) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))))) := by
  have h_rhs1 : ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> default) =
      (0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> ([1] +> default)) := by
    have h_def : ([1] +> (default : ListBlank (Fin 2))) = (1 : Fin 2) >> ((0 : Fin 2) >> default) := by
      simp [ListBlank.append]
    rw [h_def, ← pow_01_cons_one k ((0 : Fin 2) >> default), zero_cons_default]
    exact pow_succ_append_right [0, 1] k default
  rw [h_rhs1]
  let L_pre := ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1])
  have h1 : ((L_pre <+ [0]) {{B}}> ([1, 0, 1, 1, 0, 1] +> ((0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> ([1] +> default))))) [target_tm]⊢*
      (((L_pre <+ [1, 1, 1, 0, 1, 0, 1]) <+ [0]) {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> ([1] +> default))) := by
    dsimp [ListBlank.append]; execute
  have h2 := OvT (L_pre <+ [1, 1, 1, 0, 1, 0, 1]) k
  have h3 : ((L_pre <+ [1, 1, 1, 0, 1, 0, 1]) <{{D}} ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))) [target_tm]⊢*
      ((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <{{E}}
      ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))) := by
    dsimp [L_pre, ListBlank.append]; execute
  have h4 := stepPlus_stepStar (sweep_E_left_011_10 q (l <+ (([1, 0] : List (Fin 2)) ^ p))
      ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default)))))
  have h_eq4 : ((0 : Fin 2) >> ([0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))) =
      ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default)))) := rfl
  rw [h_eq4] at h4
  have h5 := shift_DE_L1 p l ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))))
  have h_eq5 : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))))) =
      ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default)))))) := rfl
  rw [h_eq5, pow_succ_append_right' [1, 0] p] at h5
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

-- ============================================================================
-- Section 3: Canonical Family K, Multi-Pair Sweeps, 9 Macro Rules & Base Stem
-- ============================================================================

abbrev Tri := Nat × Nat × Bool

def sd (d : Bool) : List (Fin 2) := if d then [0, 0, 0, 1] else [0, 0, 1, 0]

def RP : List Tri → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | (p, q, d) :: P', r =>
    ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ q) +> (sd d +> RP P' r)))

inductive Tl where
  | TN
  | TA (t : Nat)
  | TB (k : Nat)

open Tl

def RT : Tl → ListBlank (Fin 2)
  | TN => default
  | TA t => ((([1, 0] : List (Fin 2)) ^ t) +> ([1] +> default))
  | TB k => ([1, 0, 1, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> default))

def K (h : Nat) (P : List Tri) (T : Tl) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> RP P (RT T)))

def pre (h : Nat) : ListBlank (Fin 2) :=
  (default <+ (([0, 1] : List (Fin 2)) ^ (4 + h))) <+ [1, 1, 1]

def reg (p q : Nat) (l : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q - 1))) <+ [1, 1]

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

def okR (x : Tri) : Prop := x.2.2 = false ∧ 1 ≤ x.2.1
def okL (x : Tri) : Prop := x.2.2 = false ∧ 2 ≤ x.2.1
def okO (x : Tri) : Prop := 1 ≤ x.1 ∧ 1 ≤ x.2.1

lemma RP_app (Z W : List Tri) (r : ListBlank (Fin 2)) :
    RP (Z ++ W) r = RP Z (RP W r) := by
  induction Z with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [RP]
    rw [ih]

lemma LP_app (Z W : List Tri) (l : ListBlank (Fin 2)) :
    LP (Z ++ W) l = LP W (LP Z l) := by
  induction Z generalizing l with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [LP]
    exact ih (reg p q l)

lemma PassesR (Z : List Tri) (hZ : ∀ x ∈ Z, okR x) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{B}}> RP Z r) [target_tm]⊢* ((LP Z l <+ [0]) {{B}}> r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hx := hZ (p, q, d) List.mem_cons_self
    rcases hx with ⟨hd, hq⟩
    dsimp at hd hq
    subst hd
    cases q with
    | zero => omega
    | succ q =>
      simp only [RP, LP, sd]
      have h1 := PassR l p q (RP Z r)
      have h2 := ih (fun y hy => hZ y (List.mem_cons_of_mem _ hy)) (reg p (q + 1) l) r
      simp only [reg] at h2
      exact stepStar_trans h1 h2

lemma PassesL (Z : List Tri) (hZ : ∀ x ∈ Z, okL x) (l r : ListBlank (Fin 2)) :
    ((LP Z l <+ [0]) <{{D}} r) [target_tm]⊢* ((l <+ [0]) <{{D}} RP (Z.map touch) r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hx := hZ (p, q, d) List.mem_cons_self
    rcases hx with ⟨hd, hq⟩
    dsimp at hd hq
    subst hd
    cases q with
    | zero => omega
    | succ q =>
      cases q with
      | zero => omega
      | succ q =>
        simp only [LP, RP, touch, sd]
        have h1 := ih (fun y hy => hZ y (List.mem_cons_of_mem _ hy)) (reg p (q + 2) l) r
        have h2 := PassL l p q (RP (Z.map touch) r)
        simp only [reg] at h1
        exact stepStar_trans h1 h2

lemma OvPasses (Z : List Tri) (hZ : ∀ x ∈ Z, okO x) (l r : ListBlank (Fin 2)) :
    (LP Z l <{{D}} r) [target_tm]⊢* (l <{{D}} OvR Z r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hx := hZ (p, q, d) List.mem_cons_self
    rcases hx with ⟨hp, hq⟩
    dsimp at hp hq
    cases p with
    | zero => omega
    | succ p =>
      cases q with
      | zero => omega
      | succ q =>
        simp only [LP, OvR]
        have h1 := ih (fun y hy => hZ y (List.mem_cons_of_mem _ hy)) (reg (p + 1) (q + 1) l) r
        have h2 := OvL l p q (OvR Z r)
        simp only [reg] at h1
        exact stepStar_trans h1 h2

lemma okL_R (Z : List Tri) (hZ : ∀ x ∈ Z, okL x) : ∀ x ∈ Z, okR x := by
  intro x hx
  obtain ⟨h1, h2⟩ := hZ x hx
  exact ⟨h1, by omega⟩

-- Macro Rules
lemma Dec (h : Nat) (Z : List Tri) (p q : Nat) (R : List Tri) (T : Tl)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ (p, q + 2, true) :: R) T) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ (p + 1, q + 1, false) :: R) T) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) (pre h) _)
      (stepStar_trans (Borrow _ p q _)
        (stepStar_trans (PassesL Z hZ (pre h) _)
          (EndPh h _))))

lemma DecMerge (h : Nat) (Z : List Tri) (p p' q' : Nat) (d' : Bool) (R : List Tri) (T : Tl)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ (p, 1, true) :: (p', q', d') :: R) T) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ (p + p' + 3, q', d') :: R) T) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) (pre h) _)
      (stepStar_trans (MergeB _ p p' _)
        (stepStar_trans (PassesL Z hZ (pre h) _)
          (EndPh h _))))

lemma DecMergeTail (h : Nat) (Z : List Tri) (p t : Nat) (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, 1, true)]) (TA t)) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch) (TA (p + t + 3))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) (pre h) _)
      (stepStar_trans (MergeB _ p t _)
        (stepStar_trans (PassesL Z hZ (pre h) _)
          (EndPh h _))))

lemma DecMergeEmpty (h : Nat) (Z : List Tri) (p : Nat) (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, 1, true)]) TN) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch) (TA (p + 2))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  exact stepPlus_stepStar_stepPlus (Start h _)
    (stepStar_trans (PassesR Z (okL_R Z hZ) (pre h) _)
      (stepStar_trans (MergeE _ p)
        (stepStar_trans (PassesL Z hZ (pre h) _)
          (EndPh h _))))

lemma EndR (h : Nat) (Z : List Tri) (p q : Nat) (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, q + 2, false)]) TN) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ [(p + 1, q + 1, false)]) (TA 1)) := by
  unfold K
  have hZ_snoc : ∀ x ∈ Z ++ [(p, q + 2, false)], okR x := by
    intro x hx
    rcases List.mem_append.mp hx with hxZ | hxp
    · exact okL_R Z hZ x hxZ
    · rcases List.mem_singleton.mp hxp with rfl
      exact ⟨rfl, by dsimp; omega⟩
  have h1 := Start h (RP (Z ++ [(p, q + 2, false)]) (RT TN))
  have h2 := PassesR (Z ++ [(p, q + 2, false)]) hZ_snoc (pre h) (RT TN)
  rw [LP_app] at h2
  simp only [LP, RT, reg] at h2
  have h3 := EndT (LP Z (pre h) <+ [0]) p q
  have h4 := PassesL Z hZ (pre h) ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))
  have h5 := EndPh h (RP (Z.map touch ++ [(p + 1, q + 1, false)]) (RT (TA 1)))
  have h_rp : RP (Z.map touch ++ [(p + 1, q + 1, false)]) (RT (TA 1)) =
      RP (Z.map touch) ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default)))) := by
    rw [RP_app]; rfl
  rw [← h_rp] at h4
  exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

lemma EndLast (h : Nat) (Z : List Tri) (p : Nat) (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, 1, false)]) TN) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch) (TA (p + 4))) := by
  unfold K
  have hZ_snoc : ∀ x ∈ Z ++ [(p, 1, false)], okR x := by
    intro x hx
    rcases List.mem_append.mp hx with hxZ | hxp
    · exact okL_R Z hZ x hxZ
    · rcases List.mem_singleton.mp hxp with rfl
      exact ⟨rfl, by dsimp; omega⟩
  have h1 := Start h (RP (Z ++ [(p, 1, false)]) (RT TN))
  have h2 := PassesR (Z ++ [(p, 1, false)]) hZ_snoc (pre h) (RT TN)
  rw [LP_app] at h2
  simp only [LP, RT, reg] at h2
  have h3 := EndLastT (LP Z (pre h) <+ [0]) p
  have h4 := PassesL Z hZ (pre h) ((([1, 0] : List (Fin 2)) ^ (p + 4)) +> ([1] +> default))
  have h5 := EndPh h (RP (Z.map touch) (RT (TA (p + 4))))
  exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

lemma X2 (h : Nat) (Z : List Tri) (p q k : Nat) (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, q + 2, false)]) (TB (k + 1))) [target_tm]⊢⁺
    (K (4 + h) (Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)]) TN) := by
  unfold K
  have hZ_snoc : ∀ x ∈ Z ++ [(p, q + 2, false)], okR x := by
    intro x hx
    rcases List.mem_append.mp hx with hxZ | hxp
    · exact okL_R Z hZ x hxZ
    · rcases List.mem_singleton.mp hxp with rfl
      exact ⟨rfl, by dsimp; omega⟩
  have h1 := Start h (RP (Z ++ [(p, q + 2, false)]) (RT (TB (k + 1))))
  have h2 := PassesR (Z ++ [(p, q + 2, false)]) hZ_snoc (pre h) (RT (TB (k + 1)))
  rw [LP_app] at h2
  simp only [LP, RT, reg] at h2
  have h3 := X2T (LP Z (pre h) <+ [0]) p q k
  have h4 := PassesL Z hZ (pre h) ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))))
  have h5 := EndPh h (RP (Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)]) (RT TN))
  have h_rp : RP (Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)]) (RT TN) =
      RP (Z.map touch) ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default)))))) := by
    rw [RP_app]; rfl
  rw [← h_rp] at h4
  exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

def ovp (q : Nat) : List Tri → Nat → List Tri
  | [], t => [(q, t + 1, true)]
  | (p', q', _) :: Z', t => (q, p', true) :: ovp q' Z' t

lemma ovp_eq (Z : List Tri) (q t : Nat) :
    RP (ovp q Z t) default =
    ((([1, 0] : List (Fin 2)) ^ q) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default))) := by
  induction Z generalizing q t with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d⟩
    simp only [ovp, RP, OvR, sd]
    rw [ih]
    rfl

lemma Ov (h p1 q1 : Nat) (Z : List Tri) (t : Nat)
    (hq1 : 1 ≤ q1) (hR : ∀ x ∈ Z, okR x) (hO : ∀ x ∈ Z, okO x) :
    (K h ((p1 + 2, q1, false) :: Z) (TA t)) [target_tm]⊢⁺
    (K 2 ((h + 5, p1 + 1, false) :: ovp q1 Z t) TN) := by
  unfold K
  have hR_all : ∀ x ∈ (p1 + 2, q1, false) :: Z, okR x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxZ
    · exact ⟨rfl, hq1⟩
    · exact hR x hxZ
  have h1 := Start h (RP ((p1 + 2, q1, false) :: Z) (RT (TA t)))
  have h2 := PassesR ((p1 + 2, q1, false) :: Z) hR_all (pre h) (RT (TA t))
  simp only [LP, RT] at h2
  have h3 := OvT (LP Z (reg (p1 + 2) q1 (pre h))) t
  have h4 := OvPasses Z hO (reg (p1 + 2) q1 (pre h)) ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default))
  cases q1 with
  | zero => omega
  | succ q1 =>
    simp only [reg] at h4
    have h5 := OvL (pre h) (p1 + 1) q1 (OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default)))
    have h6 := OvEnd h p1 ((([1, 0] : List (Fin 2)) ^ (q1 + 1)) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default)))
    have h_end : RP ((h + 5, p1 + 1, false) :: ovp (q1 + 1) Z t) (RT TN) =
        ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p1 + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (q1 + 1)) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default)))))) := by
      simp only [RP, sd, RT]
      rw [ovp_eq]
      rfl
    rw [← h_end] at h6
    exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

def ovpX (q : Nat) : List Tri → Nat → List Tri
  | [], pa => [(q, pa, false)]
  | (p', q', _) :: Z', pa => (q, p', true) :: ovpX q' Z' pa

lemma ovpX_eq (Z : List Tri) (q pa : Nat) (r : ListBlank (Fin 2)) :
    RP (ovpX q Z pa) r =
    ((([1, 0] : List (Fin 2)) ^ q) +> OvR Z ((([0, 1] : List (Fin 2)) ^ pa) +> ([0, 0, 1, 0] +> r))) := by
  induction Z generalizing q pa r with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d⟩
    simp only [ovpX, RP, OvR, sd]
    rw [ih]
    rfl

lemma tailB_eq (n : Nat) :
    ([0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (n + 1)) +> ([1] +> default))) =
    ([0, 0, 1, 0] +> RT (TB n)) := by
  unfold RT
  rw [pow_succ_append_right]
  have h_def : ([1] +> (default : ListBlank (Fin 2))) = (1 : Fin 2) >> ((0 : Fin 2) >> default) := by
    simp [ListBlank.append]
  rw [h_def, pow_10_cons_one n ((0 : Fin 2) >> default), zero_cons_default]
  rfl

lemma X1 (h p1 q1 : Nat) (Z : List Tri) (pa pb : Nat)
    (hq1 : 1 ≤ q1) (hR : ∀ x ∈ Z, okR x) (hO : ∀ x ∈ Z, okO x) :
    (K h ((p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)]) TN) [target_tm]⊢⁺
    (K 2 ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) (TB (pb + 3))) := by
  unfold K
  have hR_all : ∀ x ∈ (p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)], okR x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact ⟨rfl, hq1⟩
    · rcases List.mem_append.mp hx_tail with hxZ | hx2
      · exact hR x hxZ
      · rcases List.mem_cons.mp hx2 with rfl | hx1
        · exact ⟨rfl, by dsimp; omega⟩
        · rcases List.mem_singleton.mp hx1 with rfl
          exact ⟨rfl, by dsimp; omega⟩
  have h1 := Start h (RP ((p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)]) (RT TN))
  have h2 := PassesR ((p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)]) hR_all (pre h) (RT TN)
  rw [LP_app] at h2
  simp only [LP, RT, reg] at h2
  have h3 := EndLastT ((((((LP Z (reg (p1 + 2) q1 (pre h)) <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (pa + 1))) <+ [0, 1, 1]) <+ [1, 1]) <+ [0])) pb
  have h4 := X1Sw (LP Z (reg (p1 + 2) q1 (pre h))) pa ((([1, 0] : List (Fin 2)) ^ (pb + 4)) +> ([1] +> default))
  have h5 := OvPasses Z hO (reg (p1 + 2) q1 (pre h)) ((([0, 1] : List (Fin 2)) ^ (pa + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (pb + 4)) +> ([1] +> default))))
  cases q1 with
  | zero => omega
  | succ q1 =>
    simp only [reg] at h5
    have h6 := OvL (pre h) (p1 + 1) q1 (OvR Z ((([0, 1] : List (Fin 2)) ^ (pa + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (pb + 4)) +> ([1] +> default)))))
    have h7 := OvEnd h p1 ((([1, 0] : List (Fin 2)) ^ (q1 + 1)) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (pa + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (pb + 4)) +> ([1] +> default)))))
    have h_end : RP ((h + 5, p1 + 1, false) :: ovpX (q1 + 1) Z (pa + 1)) (RT (TB (pb + 3))) =
        ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p1 + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ (q1 + 1)) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (pa + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (pb + 4)) +> ([1] +> default)))))))) := by
      simp only [RP, sd]
      have h_pb : pb + 4 = (pb + 3) + 1 := by omega
      rw [h_pb, tailB_eq (pb + 3), ovpX_eq]
      rfl
    rw [← h_end] at h7
    exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))

lemma OvEmpty (h t : Nat) :
    (K h [] (TA (t + 1))) [target_tm]⊢⁺ (K 2 [(h + 5, t + 1, false)] TN) := by
  unfold K
  dsimp [RP, sd, RT]
  have h1 := Start h ((([1, 0] : List (Fin 2)) ^ (t + 1)) +> ([1] +> default))
  have h2 := OvT (pre h) (t + 1)
  have h3 := OvEnd h t default
  exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 h3)

-- Stem from init [] to K 2 [(47, 32, false), (16, 15, true), (4, 20, true)] TN
lemma init_to_step275 :
    (init []) [target_tm]⊢* (K 2 [(7, 1, false)] TN) := by
  have h1 : (init []) [target_tm]⊢* (K 0 [] TN) := by
    rw [init_nil]; unfold K; dsimp [RP, RT, ListBlank.append]; execute
  have h2 : (K 0 [] TN) [target_tm]⊢* ((((default <+ (([0, 1] : List (Fin 2)) ^ 4)) <+ [1, 1, 1]) <+ [0]) {{B}}> default) :=
    stepPlus_stepStar (Start 0 default)
  have h3 : ((((default <+ (([0, 1] : List (Fin 2)) ^ 4)) <+ [1, 1, 1]) <+ [0]) {{B}}> default) [target_tm]⊢*
      (default <{{A}} ((([1, 0] : List (Fin 2)) ^ 4) +> ([1, 1] +> ((([0, 1] : List (Fin 2)) ^ 3) +> default)))) := by
    dsimp [ListBlank.append]; execute
  have h4 := stepPlus_stepStar (round_A_10_cap11 4 ((([0, 1] : List (Fin 2)) ^ 3) +> default))
  have h5 : (default <{{A}} ((([1, 0] : List (Fin 2)) ^ 6) +> ((([0, 1] : List (Fin 2)) ^ 3) +> default))) [target_tm]⊢*
      ((default <+ [1]) {{B}}> ((([1, 0] : List (Fin 2)) ^ 6) +> ((([0, 1] : List (Fin 2)) ^ 3) +> default))) := by
    dsimp [ListBlank.append]; execute
  have h6 := shift_BA_R 6 (default <+ [1]) ((([0, 1] : List (Fin 2)) ^ 3) +> default)
  have h7 : (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ 6)) {{B}}> ((([0, 1] : List (Fin 2)) ^ 3) +> default)) [target_tm]⊢*
      (((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ 6)) <{{D}} ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ 2) +> ([0, 0, 0, 1] +> default))))) := by
    dsimp [ListBlank.append]; execute
  have h8 := shift_DE_L1 6 (default <+ [1]) ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ 2) +> ([0, 0, 0, 1] +> default)))
  have h_eq8 : ((1 : Fin 2) >> ((0 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ 2) +> ([0, 0, 0, 1] +> default)))) =
      ([1, 0] +> ((([0, 1] : List (Fin 2)) ^ 2) +> ([0, 0, 0, 1] +> default))) := rfl
  rw [h_eq8, pow_succ_append_right' [1, 0] 6] at h8
  have h9 := OvEnd_tail 2 0 default
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4
    (stepStar_trans h5 (stepStar_trans h6 (stepStar_trans h7 (stepStar_trans h8 h9)))))))

lemma init_to_K0 :
    (init []) [target_tm]⊢* (K 2 [(11, 11, false)] TN) := by
  have h1 := init_to_step275
  have h2 := stepPlus_stepStar (EndLast 2 [] 7 (by intro x hx; nomatch hx))
  have h3 := stepPlus_stepStar (OvEmpty 6 10)
  exact stepStar_trans h1 (stepStar_trans h2 h3)

lemma okL_nil : ∀ x ∈ ([] : List Tri), okL x := by intro x hx; nomatch hx
lemma okR_nil : ∀ x ∈ ([] : List Tri), okR x := by intro x hx; nomatch hx
lemma okO_nil : ∀ x ∈ ([] : List Tri), okO x := by intro x hx; nomatch hx

lemma okL_cons {p q : Nat} {Z : List Tri} (hq : 2 ≤ q) (hZ : ∀ x ∈ Z, okL x) :
    ∀ x ∈ (p, q, false) :: Z, okL x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hxZ
  · exact ⟨rfl, hq⟩
  · exact hZ x hxZ

lemma okR_cons {p q : Nat} {Z : List Tri} (hq : 1 ≤ q) (hZ : ∀ x ∈ Z, okR x) :
    ∀ x ∈ (p, q, false) :: Z, okR x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hxZ
  · exact ⟨rfl, hq⟩
  · exact hZ x hxZ

lemma okO_cons {p q : Nat} {d : Bool} {Z : List Tri} (hp : 1 ≤ p) (hq : 1 ≤ q) (hZ : ∀ x ∈ Z, okO x) :
    ∀ x ∈ (p, q, d) :: Z, okO x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hxZ
  · exact ⟨hp, hq⟩
  · exact hZ x hxZ

def base23 : List Tri := [(47, 32, false), (16, 15, true), (4, 20, true)]

lemma init_to_base23 :
    (init []) [target_tm]⊢* (K 2 base23 TN) := by
  have s0 := init_to_K0
  have s1 := stepPlus_stepStar (EndR 2 [] 11 9 okL_nil)
  have s2 := stepPlus_stepStar (Ov 6 10 10 [] 1 (by omega) okR_nil okO_nil)
  have s3 := stepPlus_stepStar (Dec 2 [(11, 11, false)] 10 0 [] TN (okL_cons (by omega) okL_nil))
  have s4 := stepPlus_stepStar (Dec 6 [] 12 8 [(11, 1, false)] TN okL_nil)
  have s5 := stepPlus_stepStar (EndLast 10 [(13, 9, false)] 11 (okL_cons (by omega) okL_nil))
  have s6 := stepPlus_stepStar (Dec 14 [] 14 6 [] (TA 15) okL_nil)
  have s7 := stepPlus_stepStar (Ov 18 13 7 [] 15 (by omega) okR_nil okO_nil)
  have s8 := stepPlus_stepStar (Dec 2 [(23, 14, false)] 7 14 [] TN (okL_cons (by omega) okL_nil))
  have s9 := stepPlus_stepStar (Dec 6 [] 24 11 [(8, 15, false)] TN okL_nil)
  have s10 := stepPlus_stepStar (EndR 10 [(25, 12, false)] 8 13 (okL_cons (by omega) okL_nil))
  have s11 := stepPlus_stepStar (Dec 14 [] 26 9 [(9, 14, false)] (TA 1) okL_nil)
  have s12 := stepPlus_stepStar (Ov 18 25 10 [(9, 14, false)] 1 (by omega)
    (okR_cons (by omega) okR_nil) (okO_cons (by omega) (by omega) okO_nil))
  have s13 := stepPlus_stepStar (Dec 2 [(23, 26, false)] 10 7 [(14, 2, true)] TN (okL_cons (by omega) okL_nil))
  have s14 := stepPlus_stepStar (Dec 6 [] 24 23 [(11, 8, false), (14, 2, true)] TN okL_nil)
  have s15 := stepPlus_stepStar (Dec 10 [(25, 24, false), (11, 8, false)] 14 0 [] TN
    (okL_cons (by omega) (okL_cons (by omega) okL_nil)))
  have s16 := stepPlus_stepStar (Dec 14 [] 26 21 [(12, 7, true), (15, 1, false)] TN okL_nil)
  have s17 := stepPlus_stepStar (Dec 18 [(27, 22, false)] 12 5 [(15, 1, false)] TN (okL_cons (by omega) okL_nil))
  have s18 := stepPlus_stepStar (Dec 22 [] 28 19 [(13, 6, false), (15, 1, false)] TN okL_nil)
  have s19 := stepPlus_stepStar (EndLast 26 [(29, 20, false), (13, 6, false)] 15
    (okL_cons (by omega) (okL_cons (by omega) okL_nil)))
  have s20 := stepPlus_stepStar (Dec 30 [] 30 17 [(14, 5, true)] (TA 19) okL_nil)
  have s21 := stepPlus_stepStar (Dec 34 [(31, 18, false)] 14 3 [(14, 5, true)].tail (TA 19) (okL_cons (by omega) okL_nil))
  have s22 := stepPlus_stepStar (Dec 38 [] 32 15 [(15, 4, false)] (TA 19) okL_nil)
  have s23 := stepPlus_stepStar (Ov 42 31 16 [(15, 4, false)] 19 (by omega)
    (okR_cons (by omega) okR_nil) (okO_cons (by omega) (by omega) okO_nil))
  exact stepStar_trans s0 (stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3
    (stepStar_trans s4 (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7
    (stepStar_trans s8 (stepStar_trans s9 (stepStar_trans s10 (stepStar_trans s11
    (stepStar_trans s12 (stepStar_trans s13 (stepStar_trans s14 (stepStar_trans s15
    (stepStar_trans s16 (stepStar_trans s17 (stepStar_trans s18 (stepStar_trans s19
    (stepStar_trans s20 (stepStar_trans s21 (stepStar_trans s22 s23))))))))))))))))))))))

-- ============================================================================
-- Section 4: Closed Invariant J, Per-Pair Arithmetic Lemmas & Jstep
-- ============================================================================

def bv (d : Bool) : Nat := if d then 1 else 0

def dv : List Tri → Nat
  | [] => 0
  | (_, _, d) :: P' => bv d + 2 * dv P'

def dig (x : Tri) : Bool := x.2.2
def dig0 (x : Tri) : Prop := x.2.2 = false

lemma pow_pos (n : Nat) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

lemma pow_S (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ]; omega

lemma dv_lt (P : List Tri) : dv P < 2 ^ P.length := by
  induction P with
  | nil => simp [dv]
  | cons x P ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [dv]
    rw [pow_S]
    cases d <;> dsimp [bv] <;> omega

lemma dv_zeros (Z R : List Tri) (hZ : ∀ x ∈ Z, dig0 x) :
    dv (Z ++ R) = 2 ^ Z.length * dv R := by
  induction Z with
  | nil => simp [dv]; try omega
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hd : d = false := hZ (p, q, d) List.mem_cons_self
    subst hd
    dsimp [dv, bv]
    rw [ih (fun y hy => hZ y (List.mem_cons_of_mem _ hy)), pow_S]
    ring

lemma dv_tz (Z R : List Tri) (hZ : ∀ x ∈ Z, dig0 x) :
    dv (Z.map touch ++ R) + 1 = 2 ^ Z.length + 2 ^ Z.length * dv R := by
  induction Z with
  | nil => simp [dv]; omega
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hd : d = false := hZ (p, q, d) List.mem_cons_self
    subst hd
    simp [dv, touch, bv]
    have ih' := ih (fun y hy => hZ y (List.mem_cons_of_mem _ hy))
    rw [pow_S, Nat.mul_assoc]
    omega

lemma dv_zero (Z : List Tri) (hZ : ∀ x ∈ Z, dig0 x) : dv Z = 0 := by
  have h := dv_zeros Z [] hZ
  rw [List.append_nil] at h
  dsimp [dv] at h
  omega

lemma dv_tz' (Z R : List Tri) (hZ : ∀ x ∈ Z, dig0 x) :
    dv (Z.map touch ++ R) = 2 ^ Z.length - 1 + 2 ^ Z.length * dv R := by
  have h := dv_tz Z R hZ
  have hpos := pow_pos Z.length
  omega

def AllI (Pr : Nat → Tri → List Tri → Prop) (i : Nat) : List Tri → Prop
  | [] => True
  | x :: Y => Pr i x Y ∧ AllI Pr (i + 1) Y

lemma AllI_app (Pr : Nat → Tri → List Tri → Prop) (Z : List Tri) (i : Nat) (R : List Tri)
    (h : AllI Pr i (Z ++ R)) : AllI Pr (i + Z.length) R := by
  induction Z generalizing i with
  | nil => simpa using! h
  | cons x Z ih =>
    dsimp [AllI] at h
    have h_eq : i + (Z.length + 1) = (i + 1) + Z.length := by omega
    rw [List.length_cons, h_eq]
    exact ih (i + 1) h.2

lemma AllI_mono (Pr Pr' : Nat → Tri → List Tri → Prop) (P : List Tri) (i : Nat)
    (hm : ∀ j x Y, i ≤ j → Pr j x Y → Pr' j x Y) (h : AllI Pr i P) :
    AllI Pr' i P := by
  induction P generalizing i with
  | nil => exact trivial
  | cons x P ih =>
    dsimp [AllI] at h ⊢
    exact ⟨hm i x P (by omega) h.1, ih (i + 1) (fun j y Y hj => hm j y Y (by omega)) h.2⟩

lemma AllI_shift (Pr Pr' : Nat → Tri → List Tri → Prop) (P : List Tri) (i : Nat)
    (hm : ∀ j x Y, i ≤ j → Pr (j + 1) x Y → Pr' j x Y) (h : AllI Pr (i + 1) P) :
    AllI Pr' i P := by
  induction P generalizing i with
  | nil => exact trivial
  | cons x P ih =>
    dsimp [AllI] at h ⊢
    exact ⟨hm i x P (by omega) h.1, ih (i + 1) (fun j y Y hj => hm j y Y (by omega)) h.2⟩

lemma AllI_touchZ (Pr Pr' : Nat → Tri → List Tri → Prop) (R R' Z : List Tri) (i : Nat)
    (hZ : ∀ x ∈ Z, dig0 x)
    (hob : ∀ j p q Zr, (∀ x ∈ Zr, dig0 x) → j + (Zr.length + 1) = i + Z.length →
      Pr j (p, q, false) (Zr ++ R) → Pr' j (p + 1, q - 1, true) (Zr.map touch ++ R'))
    (hA : AllI Pr i (Z ++ R))
    (hR : AllI Pr' (i + Z.length) R') :
    AllI Pr' i (Z.map touch ++ R') := by
  induction Z generalizing i with
  | nil => simpa using! hR
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hd : d = false := hZ (p, q, d) List.mem_cons_self
    subst hd
    have hZ' : ∀ y ∈ Z, dig0 y := fun y hy => hZ y (List.mem_cons_of_mem _ hy)
    dsimp [AllI, touch] at hA ⊢
    refine ⟨hob i p q Z hZ' rfl hA.1, ?_⟩
    apply ih (i + 1) hZ'
    · intro j p' q' Zr hZr hj
      exact hob j p' q' Zr hZr (by dsimp; omega)
    · exact hA.2
    · have h_eq : (i + 1) + Z.length = i + (Z.length + 1) := by omega
      rw [h_eq]
      exact hR

inductive Phase where
  | E1 | E2 | E1t | E2t | T0 | L1 | L2 | LX
  deriving DecidableEq

open Phase

def PN (ph : Phase) (c4 : Bool) (p q n tv : Nat) : Prop :=
  match ph with
  | E1 =>
    match n with
    | 0 => tv + 2 ^ n + 1 ≤ q ∧ 3 ≤ p + tv + 2 ^ n
    | _ + 1 => tv + 3 * 2 ^ n + 1 ≤ q ∧ (p + tv) % 2 = 1 ∧ 3 * 2 ^ n ≤ p + tv + 2 ^ n
  | E2 =>
    match n with
    | 0 => tv + 1 ≤ q ∧ 3 ≤ p + tv
    | _ + 1 => tv + 2 * 2 ^ n + 1 ≤ q ∧ (p + tv) % 2 = 1 ∧ 3 * 2 ^ n ≤ p + tv
  | E1t =>
    match n with
    | 0 => tv + 2 ^ n + 1 ≤ q ∧ p + tv + 2 ^ n = 5
    | _ + 1 => tv + 2 * 2 ^ n + 1 ≤ q ∧ (p + tv) % 2 = 1 ∧ 3 * 2 ^ n ≤ p + tv + 2 ^ n
  | E2t =>
    match n with
    | 0 => tv + 1 ≤ q ∧ p + tv = 5
    | _ + 1 => tv + 2 ^ n + 1 ≤ q ∧ (p + tv) % 2 = 1 ∧ 3 * 2 ^ n ≤ p + tv
  | T0 =>
    tv + 7 * 2 ^ n + 1 ≤ q ∧ 6 * 2 ^ n ≤ p + tv + 5 * 2 ^ n ∧
    match n with
    | 0 => tv = 0 ∧ p % 2 = 0
    | _ + 1 => (p + tv) % 2 = 1
  | L1 =>
    tv + 2 ≤ q + 2 ^ n ∧
    match n with
    | 0 => q = tv + 2 ^ n
    | 1 => (if c4 then 4 else 5) * 2 ^ n ≤ p + tv + 2 ^ n ∧
           (tv + 2 ^ n + 1 ≤ q ∨ (q + tv) % 2 = 0) ∧ (if c4 then q = tv + 2 ^ n else True)
    | _ + 2 => (if c4 then 4 else 5) * 2 ^ n ≤ p + tv + 2 ^ n ∧ (q + tv) % 2 = 0
  | LX =>
    match n with
    | 0 => q = tv + 1
    | 1 => 4 * 2 ^ n ≤ p + tv ∧ q = tv + 1
    | _ + 2 => 4 * 2 ^ n ≤ p + tv ∧ (q + tv) % 2 = 0
  | L2 =>
    (if c4 then 4 else 5) * (2 * 2 ^ n) ≤ p + tv ∧
    match n with
    | 0 => (tv + 1 ≤ q ∨ (q + tv) % 2 = 0) ∧ (if c4 then q = tv else True)
    | _ + 1 => (q + tv) % 2 = 0

def PI (ph : Phase) (h i p q n tv : Nat) : Prop :=
  match i with
  | 1 =>
    h % 2 = 0 ∧
    match ph with
    | E1 | E1t => 2 ≤ n ∧ 11 * 2 ^ n ≤ p + tv + 2 ^ n + 3 ∧ 12 * 2 ^ n ≤ h + 4 * (tv + 2 ^ n) + 6
    | E2 | E2t => 2 ≤ n ∧ 11 * 2 ^ n ≤ p + tv + 3 ∧ 12 * 2 ^ n ≤ h + 4 * tv + 6
    | T0 => 2 ≤ n ∧ 22 * 2 ^ n ≤ p + tv + 5 * 2 ^ n + 3 ∧ 24 * 2 ^ n ≤ h + 4 * (tv + 5 * 2 ^ n) + 6
    | L1 => 2 ≤ n ∧ tv + 3 * 2 ^ n ≤ q ∧ 8 * 2 ^ n ≤ h + 4 * (tv + 2 ^ n) + 6
    | LX => 3 ≤ n ∧ tv + 2 * 2 ^ n ≤ q ∧ 8 * 2 ^ n ≤ h + 4 * tv + 6
    | L2 => 1 ≤ n ∧ tv + 4 * 2 ^ n ≤ q ∧ 16 * 2 ^ n ≤ h + 4 * tv + 6
  | 2 =>
    match ph with
    | E1 | E1t => 7 * 2 ^ n ≤ p + tv + 2 ^ n + 1
    | E2 | E2t => 7 * 2 ^ n ≤ p + tv + 1
    | T0 => 14 * 2 ^ n ≤ p + tv + 5 * 2 ^ n + 1
    | L1 => tv + 2 ^ n + 1 ≤ q
    | LX | L2 => tv + 1 ≤ q
  | _ => True

def PC (ph : Phase) (c4 : Bool) (h i p q n tv : Nat) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ PN ph c4 p q n tv ∧ PI ph h i p q n tv

def Lift (Pr : Nat → Nat → Nat → Nat → Nat → Prop) (i : Nat) (x : Tri) (Y : List Tri) : Prop :=
  Pr i x.1 x.2.1 Y.length (dv (x :: Y))

def PCx (ph : Phase) (c4 : Bool) (h : Nat) := Lift (PC ph c4 h)

local macro "split_and" : tactic =>
  `(tactic| repeat' (refine And.intro ?_ ?_))

local macro "cr" : tactic =>
  `(tactic| (simp -failIfUnchanged only [PN, PI, pow_S, Nat.pow_zero, Bool.false_eq_true, ite_true, ite_false] at *; split_and <;> first | trivial | omega))

lemma ob_touch (ph : Phase) (c4 : Bool) (h i p q n tv : Nat)
    (ht : 1 ≤ tv) (hq : 2 ≤ q) (hpc : PC ph c4 h i p q n tv) :
    PC ph c4 (4 + h) i (p + 1) (q - 1) n (tv - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      cases ph <;> cases c4 <;> cr
  · have := pow_pos n
    rcases i with _ | _ | _ | i <;> try trivial
    · cases ph <;> cr
    · cases ph <;> cr

lemma ob_merge (ph : Phase) (c4 : Bool) (h i p q n u U : Nat)
    (hph : ph = L1 ∨ ph = L2 ∨ ph = LX)
    (hn : 1 ≤ n) (hu : 2 ≤ u) (hu2 : u % 2 = 0) (hU2 : U % 2 = 0) (hUu : U + u ≤ 2 * 2 ^ n)
    (hL1 : ph = L1 → U + u ≤ 2 ^ n) (hLX : ph = LX → 2 ≤ n) (hc4 : ph = L1 → c4 = true → 2 ≤ n)
    (hi1 : i = 1 → 2 ≤ n) (hiX : ph = LX → i = 1 → 3 ≤ n) (hq : 2 ≤ q)
    (hpc : PC ph c4 h i p q (n + 1) (u + 2 * U)) :
    PC ph c4 (4 + h) i (p + 1) (q - 1) n (u - 1 + U) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [omega; skip; have := pow_pos n] <;>
      rcases hph with rfl | rfl | rfl <;> cases c4 <;>
      (try have := hL1 rfl) <;> (try have := hLX rfl) <;> (try have := hc4 rfl rfl) <;> cr
  · have := pow_pos n
    rcases i with _ | _ | _ | i <;> try trivial
    · rcases hph with rfl | rfl | rfl <;>
        (try have := hL1 rfl) <;> (try have := hi1 rfl) <;> (try have := hiX rfl rfl) <;> cr
    · rcases hph with rfl | rfl | rfl <;> cr

lemma ob_mt (c4 : Bool) (h i p q n : Nat) (hq : 2 ≤ q) (hi1 : i = 1 → 1 ≤ n)
    (hpc : PC L2 c4 h i p q (n + 1) (2 * 2 ^ n)) :
    PC L2 false (4 + h) i (p + 1) (q - 1) n (2 * 2 ^ n - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | n <;> [skip; have := pow_pos n] <;> cases c4 <;> cr
  · have := pow_pos n
    rcases i with _ | _ | _ | i <;> (try have := hi1 rfl) <;> first | trivial | cr

lemma ob_fuse (ph : Phase) (c4 : Bool) (h h' k p p' q' n tv : Nat)
    (hph : ph = L1 ∨ ph = L2 ∨ ph = LX) (hk : 3 ≤ k)
    (hpc : PC ph c4 h (k + 1) p' q' n tv) :
    PC ph c4 h' k (p + p' + 3) q' n tv := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      rcases hph with rfl | rfl | rfl <;> cases c4 <;> cr
  · rcases k with _ | _ | _ | k <;> [omega; omega; omega; trivial]

lemma ob_far (ph : Phase) (c4 : Bool) (h h' i j p q n tv : Nat)
    (_hi : 3 ≤ i) (hj : 3 ≤ j) (hpc : PC ph c4 h i p q n tv) :
    PC ph c4 h' j p q n tv := by
  rcases hpc with ⟨hp, hq0, hN, _⟩
  refine ⟨hp, hq0, hN, ?_⟩
  rcases j with _ | _ | _ | j <;> [omega; omega; omega; trivial]

def endtr (ph ph' : Phase) : Prop := (ph = E1 ∧ ph' = E2) ∨ (ph = E1t ∧ ph' = E2t)

lemma ob_end (ph ph' : Phase) (h i p q n : Nat)
    (hph : endtr ph ph') (hn : 1 ≤ n) (hq : 2 ≤ q)
    (hpc : PC ph false h i p q n 0) :
    PC ph' false (4 + h) i (p + 1) (q - 1) n (2 ^ n - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | n
    · omega
    · have := pow_pos n; rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cr
  · have := pow_pos n
    rcases i with _ | _ | _ | i <;>
      first | trivial | (rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cr)

lemma ob_end_top (ph ph' : Phase) (h i p q : Nat)
    (hph : endtr ph ph') (hi : 3 ≤ i)
    (hpc : PC ph false h i p (q + 2) 0 0) :
    PC ph' false (4 + h) i (p + 1) (q + 1) 0 0 := by
  rcases hpc with ⟨hp, hq0, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cr
  · rcases i with _ | _ | _ | i <;> [omega; omega; omega; trivial]

lemma ob_endlast (c4 : Bool) (h i p q n : Nat) (hq : 2 ≤ q)
    (hpc : PC L1 c4 h i p q (n + 1) 0) :
    PC L2 c4 (4 + h) i (p + 1) (q - 1) n (2 * 2 ^ n - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | n <;> [skip; have := pow_pos n] <;> cases c4 <;> cr
  · have := pow_pos n
    rcases i with _ | _ | _ | i <;> first | trivial | cr

lemma ob_x2 (h i p q n : Nat) (hn : 1 ≤ n) (hq : 2 ≤ q)
    (hpc : PC T0 false h i p q n 0) :
    PC E1t false (4 + h) i (p + 1) (q - 1) (n + 1) (3 * 2 ^ n - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | n
    · omega
    · have := pow_pos n; cr
  · have := pow_pos n
    rcases i with _ | _ | _ | i <;> first | trivial | cr

lemma ob_x2_top (h i p q : Nat) (hi : 3 ≤ i)
    (hpc : PC T0 false h i p (q + 2) 0 0) :
    PC E1t false (4 + h) i (p + 1) (q + 1) 1 2 := by
  rcases hpc with ⟨hp, hq0, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cr
  · rcases i with _ | _ | _ | i <;> [omega; omega; omega; trivial]

lemma ob_x2_new (h i k : Nat) (hi : 3 ≤ i) (hk : 3 ≤ k) :
    PC E1t false h i 3 k 0 1 := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cr
  · rcases i with _ | _ | _ | i <;> [omega; omega; omega; trivial]

def ovtr (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) : Prop :=
  (ph = E2 ∧ ph' = L1 ∧ c4' = false ∧ Xp = (fun x => x ≠ 4)) ∨
  (ph = E2 ∧ ph' = LX ∧ c4' = false ∧ Xp = (fun x => x = 4)) ∨
  (ph = E2t ∧ ph' = L1 ∧ c4' = true ∧ Xp = (fun _ => True)) ∨
  (ph = L2 ∧ ph' = E1 ∧ c4' = false ∧ Xp = (fun _ => True))

lemma ob_ov_head (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h p1 q1 n : Nat)
    (htr : ovtr ph ph' c4' Xp)
    (hpc : PC ph false h 1 (p1 + 2) q1 n 0) :
    PC ph' c4' 2 1 (h + 5) (p1 + 1) (n + 1) (2 * (2 * 2 ^ n) - 2) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;> cr
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;> cr

lemma ob_ov_step (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h i pp q p' q' m : Nat)
    (htr : ovtr ph ph' c4' Xp) (hi : 1 ≤ i)
    (hpc : PC ph false h i pp q (m + 1) 0)
    (hpc' : PC ph false h (i + 1) p' q' m 0)
    (hX : m = 0 → Xp p') :
    PC ph' c4' 2 (i + 1) q p' (m + 1) (2 * (2 * 2 ^ m) - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  rcases hpc' with ⟨hp', hq0', hN', hI'⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases m with _ | _ | m <;> [skip; skip; have := pow_pos m] <;>
      rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      (try have := hX rfl) <;> cr
  · rcases i with _ | _ | i <;> [omega; skip; trivial]
    rcases m with _ | _ | m <;> [skip; skip; have := pow_pos m] <;>
      rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      (try have := hX rfl) <;> cr

lemma ob_ov_base (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h i pp q t : Nat)
    (htr : ovtr ph ph' c4' Xp) (hi : 1 ≤ i)
    (ht1 : ph = L2 → 2 ≤ t) (ht2 : ph ≠ L2 → t = 1)
    (hpc : PC ph false h i pp q 0 0) :
    PC ph' c4' 2 (i + 1) q (t + 1) 0 1 := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have := ht2 (by decide); cr
    · have := ht2 (by decide); cr
    · have := ht2 (by decide); cr
    · have := ht1 rfl; cr
  · rcases i with _ | _ | i <;> [omega; skip; trivial]
    rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have := ht2 (by decide); cr
    · have := ht2 (by decide); cr
    · have := ht2 (by decide); cr
    · have := ht1 rfl; cr

lemma ob_x1_head (h p1 q1 n : Nat)
    (hpc : PC LX false h 1 (p1 + 2) q1 (n + 2) 0) :
    PC T0 false 2 1 (h + 5) (p1 + 1) (n + 1) (2 * 2 ^ n - 2) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;> cr
  · rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;> cr

lemma ob_x1_step (h i pp q p' q' m : Nat) (hi : 1 ≤ i)
    (hpc : PC LX false h i pp q (m + 3) 0)
    (hpc' : PC LX false h (i + 1) p' q' (m + 2) 0) :
    PC T0 false 2 (i + 1) q p' (m + 1) (2 * 2 ^ m - 1) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  rcases hpc' with ⟨hp', hq0', hN', hI'⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases m with _ | m <;> [skip; have := pow_pos m] <;> cr
  · rcases i with _ | _ | i <;> [omega; skip; trivial]
    rcases m with _ | m <;> [skip; have := pow_pos m] <;> cr

lemma ob_x1_base (h i pp q pa : Nat) (hi : 1 ≤ i)
    (hpc : PC LX false h i pp q 2 0)
    (hpc' : PC LX false h (i + 1) (pa + 1) 1 1 0) :
    PC T0 false 2 (i + 1) q (pa + 1) 0 0 := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  rcases hpc' with ⟨hp', hq0', hN', hI'⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cr
  · rcases i with _ | _ | i <;> [omega; cr; trivial]

lemma passq (ph : Phase) (c4 : Bool) (h i p q n tv : Nat)
    (hpc : PC ph c4 h i p q n tv) (ht : 2 ≤ tv) (ht2 : tv % 2 = 0) : 2 ≤ q := by
  rcases hpc with ⟨hp, hq0, hN, _⟩
  rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
    cases ph <;> cases c4 <;> simp -failIfUnchanged only [PN] at hN <;>
    (try simp only [pow_S, Nat.pow_zero, Bool.false_eq_true, ite_true, ite_false] at hN) <;> omega

lemma borrow1 (ph : Phase) (c4 : Bool) (h k p n tv : Nat)
    (hk : 1 ≤ k) (ht : tv % 2 = 1) (hpc : PC ph c4 h k p 1 n tv) :
    (ph = L1 ∨ ph = L2 ∨ ph = LX) ∧ 3 ≤ k ∧
    (ph = L1 → 1 ≤ n ∧ tv + 1 ≤ 2 ^ n ∧ (c4 = true → 2 ≤ n)) ∧ (ph = LX → 2 ≤ n) := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  have hph : ph = L1 ∨ ph = L2 ∨ ph = LX := by
    cases ph <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
      | (exfalso; rcases n with _ | n <;> [skip; have := pow_pos n] <;>
          simp -failIfUnchanged only [PN] at hN <;> (try simp only [pow_S, Nat.pow_zero] at hN) <;> omega)
  refine ⟨hph, ?_, ?_, ?_⟩
  · rcases k with _ | _ | _ | k <;> [omega; skip; skip; omega] <;>
      (exfalso; have := pow_pos n; rcases hph with rfl | rfl | rfl <;>
        simp -failIfUnchanged only [PI] at hI <;> omega)
  · rintro rfl
    rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
      cases c4 <;> simp -failIfUnchanged only [PN] at hN <;>
      (try simp only [pow_S, Nat.pow_zero, Bool.false_eq_true, ite_true, ite_false] at hN) <;>
      (split_and <;> first | omega | (intro hc; nomatch hc))
  · rintro rfl
    rcases n with _ | _ | n <;> [skip; skip; omega] <;>
      simp -failIfUnchanged only [PN] at hN <;> (try simp only [pow_S, Nat.pow_zero] at hN) <;> omega

lemma q2_V0 (ph : Phase) (c4 : Bool) (h i p q n : Nat)
    (hpc : PC ph c4 h i p q n 0) (hn : 1 ≤ n) (hX : ph = LX → 2 ≤ n) : 2 ≤ q := by
  rcases hpc with ⟨hp, hq0, hN, _⟩
  rcases n with _ | _ | n <;> [omega; skip; have := pow_pos n] <;>
    cases ph <;> cases c4 <;> simp -failIfUnchanged only [PN] at hN <;>
    simp -failIfUnchanged only [pow_S, Nat.pow_zero, Bool.false_eq_true, ite_true, ite_false] at hN <;>
    (try have := hX rfl) <;> omega

lemma p1_V0 (ph : Phase) (c4 : Bool) (h p q n : Nat)
    (hpc : PC ph c4 h 1 p q n 0) (hph : ph = E2 ∨ ph = E2t ∨ ph = L2 ∨ ph = LX) : 2 ≤ p := by
  rcases hpc with ⟨hp, hq0, hN, hI⟩
  rcases n with _ | _ | n <;> [skip; skip; have := pow_pos n] <;>
    rcases hph with rfl | rfl | rfl | rfl <;> cases c4 <;>
    simp -failIfUnchanged only [PN, PI] at hN hI <;>
    simp -failIfUnchanged only [pow_S, Nat.pow_zero, Bool.false_eq_true, ite_true, ite_false] at hN hI <;> omega

lemma L2_c4_V0 (h i p q : Nat) (hpc : PC L2 true h i p q 0 0) : False := by
  rcases hpc with ⟨hp, hq0, hN, _⟩
  simp -failIfUnchanged only [PN] at hN
  simp -failIfUnchanged only [ite_true] at hN
  omega

-- ============================================================================
-- Section 4b: List-Level Preservation Lemmas, Invariant J, Jstep & J_base23
-- ============================================================================

lemma ovp_len (q : Nat) (Z : List Tri) (t : Nat) :
    (ovp q Z t).length = Z.length + 1 := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d⟩
    dsimp [ovp]
    rw [ih q']

lemma ovp_dv (q : Nat) (Z : List Tri) (t : Nat) :
    dv (ovp q Z t) + 1 = 2 ^ (Z.length + 1) := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d⟩
    dsimp [ovp, dv, bv]
    have ih' := ih q'
    rw [pow_S (Z.length + 1)]
    omega

lemma ovpX_len (q : Nat) (Z : List Tri) (pa : Nat) :
    (ovpX q Z pa).length = Z.length + 1 := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d⟩
    dsimp [ovpX]
    rw [ih q']

lemma ovpX_dv (q : Nat) (Z : List Tri) (pa : Nat) :
    dv (ovpX q Z pa) + 1 = 2 ^ Z.length := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p', q', d⟩
    dsimp [ovpX, dv, bv]
    have ih' := ih q'
    rw [pow_S Z.length]
    omega

def lastOK (Xp : Nat → Prop) : List Tri → Prop
  | [] => True
  | [(p, _, _)] => Xp p
  | _ :: Z' => lastOK Xp Z'

lemma lastOK_cons (Xp : Nat → Prop) (p q : Nat) (d : Bool) (Z : List Tri)
    (h : lastOK Xp ((p, q, d) :: Z)) : (Z = [] → Xp p) ∧ lastOK Xp Z := by
  cases Z with
  | nil => exact And.intro (fun _ => h) trivial
  | cons z Z' => exact And.intro (fun h' => by nomatch h') h

lemma lastOK_dec (Z : List Tri) : lastOK (fun x => x = 4) Z ∨ lastOK (fun x => x ≠ 4) Z := by
  induction Z with
  | nil => exact Or.inl trivial
  | cons x Z' ih =>
    rcases x with ⟨p, q, d⟩
    cases Z' with
    | nil =>
      dsimp [lastOK]
      match decEq p 4 with
      | isTrue h => exact Or.inl h
      | isFalse h => exact Or.inr h
    | cons z Z'' => exact ih

lemma lastOK_True (Z : List Tri) : lastOK (fun _ => True) Z := by
  induction Z with
  | nil => exact trivial
  | cons x Z' ih =>
    rcases x with ⟨p, q, d⟩
    cases Z' with
    | nil => exact trivial
    | cons z Z'' => exact ih

lemma AllI_ovp (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h t : Nat)
    (htr : ovtr ph ph' c4' Xp) (ht1 : ph = L2 → 2 ≤ t) (ht2 : ph ≠ L2 → t = 1)
    (Z : List Tri) (i pp q : Nat) (hi : 1 ≤ i)
    (hZ : ∀ x ∈ Z, dig0 x) (hX : lastOK Xp Z)
    (hpc : PC ph false h i pp q Z.length 0)
    (hA : AllI (PCx ph false h) (i + 1) Z) :
    AllI (PCx ph' c4' 2) (i + 1) (ovp q Z t) := by
  induction Z generalizing i pp q with
  | nil =>
    dsimp [ovp, AllI]
    refine ⟨?_, trivial⟩
    dsimp [PCx, Lift, dv, bv]
    exact ob_ov_base ph ph' c4' Xp h i pp q t htr hi ht1 ht2 hpc
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    have hd' : d' = false := hZ (p', q', d') List.mem_cons_self
    subst hd'
    have hZ' : ∀ y ∈ Z, dig0 y := fun y hy => hZ y (List.mem_cons_of_mem _ hy)
    rcases lastOK_cons Xp p' q' false Z hX with ⟨hX1, hX2⟩
    dsimp [AllI] at hA
    rcases hA with ⟨hhead, htail⟩
    dsimp [PCx, Lift] at hhead
    rw [dv_zero ((p', q', false) :: Z) hZ] at hhead
    dsimp [ovp, AllI]
    refine ⟨?_, ?_⟩
    · dsimp [PCx, Lift]
      rw [ovp_len]
      have h_dv : dv ((q, p', true) :: ovp q' Z t) = 2 * (2 * 2 ^ Z.length) - 1 := by
        dsimp [dv, bv]
        have E := ovp_dv q' Z t
        rw [pow_S Z.length] at E
        omega
      rw [h_dv]
      refine ob_ov_step ph ph' c4' Xp h i pp q p' q' Z.length htr hi hpc hhead ?_
      intro hm
      apply hX1
      cases Z with
      | nil => rfl
      | cons _ _ => nomatch hm
    · exact ih (i + 1) p' q' (by omega) hZ' hX2 hhead htail

lemma AllI_ovpX (h pa pb : Nat) (Z : List Tri) (i pp q : Nat) (hi : 1 ≤ i)
    (hZ : ∀ x ∈ Z, dig0 x)
    (hpc : PC LX false h i pp q (Z.length + 2) 0)
    (hA : AllI (PCx LX false h) (i + 1) (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) :
    AllI (PCx T0 false 2) (i + 1) (ovpX q Z (pa + 1)) := by
  induction Z generalizing i pp q with
  | nil =>
    dsimp [ovpX, AllI] at hA ⊢
    refine ⟨?_, trivial⟩
    rcases hA with ⟨ha, _⟩
    dsimp [PCx, Lift, dv, bv] at ha ⊢
    exact ob_x1_base h i pp q pa hi hpc ha
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    have hd' : d' = false := hZ (p', q', d') List.mem_cons_self
    subst hd'
    have hZ' : ∀ y ∈ Z, dig0 y := fun y hy => hZ y (List.mem_cons_of_mem _ hy)
    dsimp [AllI] at hA
    rcases hA with ⟨hhead, htail⟩
    have hZ_all : ∀ y ∈ (p', q', false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)]), dig0 y := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · rcases List.mem_append.mp hy' with hyZ | hy2
        · exact hZ' y hyZ
        · rcases List.mem_cons.mp hy2 with rfl | hy1
          · rfl
          · rcases List.mem_singleton.mp hy1 with rfl; rfl
    dsimp [PCx, Lift] at hhead
    rw [dv_zero _ hZ_all, List.length_append] at hhead
    dsimp at hhead
    dsimp [ovpX, AllI]
    refine ⟨?_, ?_⟩
    · dsimp [PCx, Lift]
      rw [ovpX_len]
      have h_dv : dv ((q, p', true) :: ovpX q' Z (pa + 1)) = 2 * 2 ^ Z.length - 1 := by
        dsimp [dv, bv]
        have E := ovpX_dv q' Z (pa + 1)
        omega
      rw [h_dv]
      exact ob_x1_step h i pp q p' q' Z.length hi hpc hhead
    · exact ih (i + 1) p' q' (by omega) hZ' hhead htail

lemma Z_okL (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (i : Nat) (x : Tri) (R : List Tri)
    (hZ : ∀ y ∈ Z, dig0 y) (hx : dig x = true)
    (hA : AllI (PCx ph c4 h) i (Z ++ x :: R)) :
    ∀ y ∈ Z, okL y := by
  induction Z generalizing i with
  | nil => intro y hy; nomatch hy
  | cons z Z ih =>
    rcases z with ⟨p, q, d⟩
    have hd : d = false := hZ (p, q, d) List.mem_cons_self
    subst hd
    have hZ' : ∀ y ∈ Z, dig0 y := fun y hy => hZ y (List.mem_cons_of_mem _ hy)
    dsimp [AllI] at hA
    rcases hA with ⟨hhead, htail⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hyZ
    · refine ⟨rfl, ?_⟩
      dsimp [PCx, Lift] at hhead
      rcases x with ⟨px, qx, dx⟩
      dsimp [dig] at hx
      subst hx
      have h_dv : dv ((p, q, false) :: (Z ++ (px, qx, true) :: R)) = 2 * (2 ^ Z.length * (1 + 2 * dv R)) := by
        dsimp [dv, bv]
        rw [dv_zeros Z ((px, qx, true) :: R) hZ']
        dsimp [dv, bv]
        ring
      have h_pos : 1 ≤ 2 ^ Z.length * (1 + 2 * dv R) := Nat.mul_pos (pow_pos Z.length) (by omega)
      exact passq ph c4 h i p q (Z ++ (px, qx, true) :: R).length
        (dv ((p, q, false) :: (Z ++ (px, qx, true) :: R))) hhead (by omega) (by omega)
    · exact ih (i + 1) hZ' htail y hyZ

lemma AllI_okRO (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (i : Nat)
    (hZ : ∀ y ∈ Z, dig0 y) (hA : AllI (PCx ph c4 h) i Z) :
    (∀ y ∈ Z, okR y) ∧ (∀ y ∈ Z, okO y) := by
  induction Z generalizing i with
  | nil => exact ⟨okR_nil, okO_nil⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hd : d = false := hZ (p, q, d) List.mem_cons_self
    subst hd
    have hZ' : ∀ y ∈ Z, dig0 y := fun y hy => hZ y (List.mem_cons_of_mem _ hy)
    dsimp [AllI] at hA
    rcases hA with ⟨hhead, htail⟩
    rcases ih (i + 1) hZ' htail with ⟨hR, hO⟩
    dsimp [PCx, Lift, PC] at hhead
    rcases hhead with ⟨hp, hq, _⟩
    exact ⟨okR_cons hq hR, okO_cons hp hq hO⟩

lemma inv_Dec (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p q : Nat) (R : List Tri)
    (hZ : ∀ y ∈ Z, dig0 y)
    (hA : AllI (PCx ph c4 h) 1 (Z ++ (p, q + 2, true) :: R)) :
    AllI (PCx ph c4 (4 + h)) 1 (Z.map touch ++ (p + 1, q + 1, false) :: R) := by
  have hB := AllI_app (PCx ph c4 h) Z 1 ((p, q + 2, true) :: R) hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, hR⟩
  apply AllI_touchZ (PCx ph c4 h) (PCx ph c4 (4 + h)) ((p, q + 2, true) :: R) ((p + 1, q + 1, false) :: R) Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    rw [List.length_append, List.length_cons] at h0
    rw [List.length_append, List.length_map, List.length_cons]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr ((p, q + 2, true) :: R) hZr] at h0
    rw [dv_tz' Zr ((p + 1, q + 1, false) :: R) hZr]
    dsimp [dv, bv] at h0 ⊢
    set A := 2 ^ Zr.length
    set M := 2 ^ Zr.length * dv R
    have hA1 : 1 ≤ A := pow_pos Zr.length
    have h_tv0 : 0 + 2 * (A * (1 + 2 * dv R)) = 2 * (A + 2 * M) := by dsimp [A, M]; ring
    have h_tv1 : 1 + 2 * (A - 1 + A * (0 + 2 * dv R)) = 2 * (A + 2 * M) - 1 := by
      have : A * (0 + 2 * dv R) = 2 * M := by dsimp [A, M]; ring
      omega
    rw [h_tv0] at h0
    rw [h_tv1]
    have hq0 : 2 ≤ q0 := passq ph c4 h j p0 q0 (Zr.length + (R.length + 1)) (2 * (A + 2 * M)) h0 (by omega) (by omega)
    exact ob_touch ph c4 h j p0 q0 (Zr.length + (R.length + 1)) (2 * (A + 2 * M)) (by omega) hq0 h0
  · exact hA
  · dsimp [AllI]
    refine ⟨?_, ?_⟩
    · dsimp [PCx, Lift, dv, bv] at hx ⊢
      have h_eq : 0 + 2 * dv R = (1 + 2 * dv R) - 1 := by omega
      rw [h_eq]
      exact ob_touch ph c4 h (1 + Z.length) p (q + 2) R.length (1 + 2 * dv R) (by omega) (by omega) hx
    · refine AllI_mono (PCx ph c4 h) (PCx ph c4 (4 + h)) R (1 + Z.length + 1) ?_ hR
      intro j y Y hj hy
      rcases y with ⟨py, qy, dy⟩
      dsimp [PCx, Lift, PC] at hy ⊢
      rcases hy with ⟨hp, hq, hN, hI⟩
      refine ⟨hp, hq, hN, ?_⟩
      rcases j with _ | _ | _ | j <;> [omega; omega; exact hI; trivial]

lemma snoc_nn (Z : List Tri) (y : Tri) : Z ++ [y] ≠ [] := by
  cases Z <;> intro h <;> nomatch h

def minlen : Phase → Nat
  | LX => 3
  | L2 => 1
  | _ => 2

lemma head_len (ph : Phase) (c4 : Bool) (h : Nat) (x : Tri) (Y : List Tri)
    (hx : PCx ph c4 h 1 x Y) : minlen ph ≤ Y.length := by
  rcases x with ⟨p, q, d⟩
  dsimp [PCx, Lift, PC] at hx
  rcases hx with ⟨_, _, _, hI⟩
  cases ph <;> simp only [PI, minlen] at hI ⊢ <;> omega

lemma AllI_len (ph : Phase) (c4 : Bool) (h : Nat) (P : List Tri)
    (hP : P ≠ []) (hA : AllI (PCx ph c4 h) 1 P) : minlen ph + 1 ≤ P.length := by
  cases P with
  | nil => exact False.elim (hP rfl)
  | cons x Y =>
    dsimp [AllI] at hA
    have := head_len ph c4 h x Y hA.1
    dsimp
    omega

lemma inv_Merge (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p p' q' : Nat) (d' : Bool) (R0 : List Tri)
    (hZ : ∀ y ∈ Z, dig0 y)
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
  rcases borrow1 ph c4 h (1 + Z.length) p (R0.length + 1) (1 + 2 * Hd) (by omega) (by omega) hx' with ⟨hph, hk, hL1, hLX⟩
  apply AllI_touchZ (PCx ph c4 h) (PCx ph c4 (4 + h)) ((p, 1, true) :: (p', q', d') :: R0)
    ((p + p' + 3, q', d') :: R0) Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    rw [List.length_append, List.length_cons, List.length_cons] at h0
    rw [List.length_append, List.length_map, List.length_cons]
    dsimp only [dv] at h0 ⊢
    rw [dv_zeros Zr ((p, 1, true) :: (p', q', d') :: R0) hZr] at h0
    rw [dv_tz' Zr ((p + p' + 3, q', d') :: R0) hZr]
    dsimp only [dv] at h0 ⊢
    have hHd_eq : bv d' + 2 * dv R0 = Hd := rfl
    rw [hHd_eq] at h0 ⊢
    dsimp [bv] at h0 ⊢
    set A := 2 ^ Zr.length
    set B := 2 ^ R0.length
    have hA1 : 1 ≤ A := pow_pos Zr.length
    have hB1 : 1 ≤ B := pow_pos R0.length
    have hn : 2 ^ (Zr.length + (R0.length + 1)) = A * (2 * B) := by
      rw [Nat.pow_add, pow_S]
    rw [pow_S] at hlt
    change Hd < 2 * B at hlt
    have h_len : Zr.length + (R0.length + 1 + 1) = (Zr.length + (R0.length + 1)) + 1 := by omega
    rw [h_len] at h0
    set M := A * Hd
    have h_tv0 : 0 + 2 * (A * (1 + 2 * Hd)) = (2 * A) + 2 * (2 * M) := by dsimp [M]; ring
    have h_tv1 : 1 + 2 * (A - 1 + A * Hd) = (2 * A) - 1 + (2 * M) := by dsimp [M]; omega
    rw [h_tv0] at h0
    rw [h_tv1]
    have hq2 : 2 ≤ q0 := passq ph c4 h j p0 q0 ((Zr.length + (R0.length + 1)) + 1)
      ((2 * A) + 2 * (2 * M)) h0 (by omega) (by omega)
    refine ob_merge ph c4 h j p0 q0 (Zr.length + (R0.length + 1)) (2 * A) (2 * M)
      hph (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ hq2 h0
    · rw [hn]
      have h_le := Nat.mul_le_mul_left (2 * A) (by omega : Hd + 1 ≤ 2 * B)
      have h_lhs : 2 * A * (Hd + 1) = 2 * M + 2 * A := by dsimp [M]; ring
      have h_rhs : 2 * A * (2 * B) = 2 * (A * (2 * B)) := by ring
      omega
    · rintro rfl
      rcases hL1 rfl with ⟨_, hb, _⟩
      rw [pow_S] at hb
      change (1 + 2 * Hd) + 1 ≤ 2 * B at hb
      rw [hn]
      have h_le := Nat.mul_le_mul_left (2 * A) (by omega : Hd + 1 ≤ B)
      have h_lhs : 2 * A * (Hd + 1) = 2 * M + 2 * A := by dsimp [M]; ring
      have h_rhs : 2 * A * B = A * (2 * B) := by ring
      omega
    · rintro rfl; have := hLX rfl; omega
    · rintro rfl hc; rcases hL1 rfl with ⟨_, _, hc2⟩; have := hc2 hc; omega
    · rintro rfl; omega
    · rintro rfl rfl; have := hLX rfl; omega
  · exact hA
  · dsimp [AllI]
    refine ⟨?_, ?_⟩
    · dsimp [PCx, Lift] at hy ⊢
      have hHd_goal : dv ((p + p' + 3, q', d') :: R0) = Hd := rfl
      rw [hHd_goal]
      exact ob_fuse ph c4 h (4 + h) (1 + Z.length) p p' q' R0.length Hd hph hk hy
    · refine AllI_shift (PCx ph c4 h) (PCx ph c4 (4 + h)) R0 (1 + Z.length + 1) ?_ hR
      intro j y Y hj hy0
      rcases y with ⟨py, qy, dy⟩
      dsimp [PCx, Lift] at hy0 ⊢
      exact ob_far ph c4 h (4 + h) (j + 1) j py qy Y.length (dv ((py, qy, dy) :: Y)) (by omega) (by omega) hy0

lemma inv_MT (c4 : Bool) (h : Nat) (Z : List Tri) (p : Nat)
    (hZ : ∀ y ∈ Z, dig0 y)
    (hA : AllI (PCx L2 c4 h) 1 (Z ++ [(p, 1, true)])) :
    AllI (PCx L2 false (4 + h)) 1 (Z.map touch) ∧ 2 ≤ Z.length := by
  have hB := AllI_app (PCx L2 c4 h) Z 1 [(p, 1, true)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  dsimp [PCx, Lift, List.length, dv, bv] at hx
  rcases borrow1 L2 c4 h (1 + Z.length) p 0 (1 + 2 * 0) (by omega) (by omega) hx with ⟨_, hk, _⟩
  refine ⟨?_, by omega⟩
  rw [← List.append_nil (Z.map touch)]
  apply AllI_touchZ (PCx L2 c4 h) (PCx L2 false (4 + h)) [(p, 1, true)] [] Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    rw [List.length_append, List.length_singleton] at h0
    rw [List.length_append, List.length_map, List.length_nil, Nat.add_zero]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, 1, true)] hZr] at h0
    rw [dv_tz' Zr [] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hpos := pow_pos Zr.length
    have h_tv0 : 0 + 2 * (2 ^ Zr.length * 1) = 2 * 2 ^ Zr.length := by ring
    have h_tv1 : 1 + 2 * (2 ^ Zr.length - 1) = 2 * 2 ^ Zr.length - 1 := by omega
    rw [h_tv0] at h0
    rw [h_tv1]
    have hq0 : 2 ≤ q0 := passq L2 c4 h j p0 q0 (Zr.length + 1) (2 * 2 ^ Zr.length) h0 (by omega) (by omega)
    exact ob_mt c4 h j p0 q0 Zr.length hq0 (by omega) h0
  · exact hA
  · exact trivial

lemma inv_End (ph ph' : Phase) (h : Nat) (Z : List Tri) (p q : Nat)
    (htr : endtr ph ph') (hZ : ∀ y ∈ Z, dig0 y)
    (hA : AllI (PCx ph false h) 1 (Z ++ [(p, q + 2, false)])) :
    AllI (PCx ph' false (4 + h)) 1 (Z.map touch ++ [(p + 1, q + 1, false)]) := by
  have hlen := AllI_len ph false h (Z ++ [(p, q + 2, false)]) (snoc_nn Z _) hA
  rw [List.length_append, List.length_singleton] at hlen
  have hm : minlen ph = 2 := by rcases htr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hB := AllI_app (PCx ph false h) Z 1 [(p, q + 2, false)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  apply AllI_touchZ (PCx ph false h) (PCx ph' false (4 + h)) [(p, q + 2, false)] [(p + 1, q + 1, false)] Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    rw [List.length_append, List.length_singleton] at h0
    rw [List.length_append, List.length_map, List.length_singleton]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, q + 2, false)] hZr] at h0
    rw [dv_tz' Zr [(p + 1, q + 1, false)] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hpos := pow_pos Zr.length
    have h_tv1 : 1 + 2 * (2 ^ Zr.length - 1) = 2 ^ (Zr.length + 1) - 1 := by
      rw [pow_S]; omega
    rw [h_tv1]
    have hq0 : 2 ≤ q0 := q2_V0 ph false h j p0 q0 (Zr.length + 1) h0 (by omega)
      (by rintro rfl; rcases htr with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1)
    exact ob_end ph ph' h j p0 q0 (Zr.length + 1) htr (by omega) hq0 h0
  · exact hA
  · dsimp [AllI]
    refine ⟨?_, trivial⟩
    dsimp [PCx, Lift, List.length, dv, bv] at hx ⊢
    exact ob_end_top ph ph' h (1 + Z.length) p q htr (by omega) hx

lemma inv_X2 (h : Nat) (Z : List Tri) (p q k : Nat)
    (hZ : ∀ y ∈ Z, dig0 y) (hk : 3 ≤ k)
    (hA : AllI (PCx T0 false h) 1 (Z ++ [(p, q + 2, false)])) :
    AllI (PCx E1t false (4 + h)) 1 (Z.map touch ++ [(p + 1, q + 1, false), (3, k, true)]) := by
  have hlen := AllI_len T0 false h (Z ++ [(p, q + 2, false)]) (snoc_nn Z _) hA
  rw [List.length_append, List.length_singleton] at hlen
  dsimp [minlen] at hlen
  have hB := AllI_app (PCx T0 false h) Z 1 [(p, q + 2, false)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  apply AllI_touchZ (PCx T0 false h) (PCx E1t false (4 + h)) [(p, q + 2, false)]
    [(p + 1, q + 1, false), (3, k, true)] Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    rw [List.length_append, List.length_singleton] at h0
    rw [List.length_append, List.length_map]
    dsimp [List.length, dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, q + 2, false)] hZr] at h0
    rw [dv_tz' Zr [(p + 1, q + 1, false), (3, k, true)] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hpos := pow_pos Zr.length
    have h_tv1 : 1 + 2 * (2 ^ Zr.length - 1 + 2 ^ Zr.length * 2) = 3 * 2 ^ (Zr.length + 1) - 1 := by
      rw [pow_S]; omega
    rw [h_tv1]
    have hq0 : 2 ≤ q0 := q2_V0 T0 false h j p0 q0 (Zr.length + 1) h0 (by omega) (by intro h'; nomatch h')
    exact ob_x2 h j p0 q0 (Zr.length + 1) (by omega) hq0 h0
  · exact hA
  · dsimp [AllI]
    refine ⟨?_, ?_, trivial⟩
    · dsimp [PCx, Lift, List.length, dv, bv] at hx ⊢
      exact ob_x2_top h (1 + Z.length) p q (by omega) hx
    · dsimp [PCx, Lift, List.length, dv, bv]
      exact ob_x2_new (4 + h) (1 + Z.length + 1) k (by omega) hk

lemma inv_EndLast (c4 : Bool) (h : Nat) (Z : List Tri) (p : Nat)
    (hZ : ∀ y ∈ Z, dig0 y)
    (hA : AllI (PCx L1 c4 h) 1 (Z ++ [(p, 1, false)])) :
    AllI (PCx L2 c4 (4 + h)) 1 (Z.map touch) ∧ 2 ≤ Z.length := by
  have hlen := AllI_len L1 c4 h (Z ++ [(p, 1, false)]) (snoc_nn Z _) hA
  rw [List.length_append, List.length_singleton] at hlen
  dsimp [minlen] at hlen
  refine ⟨?_, by omega⟩
  rw [← List.append_nil (Z.map touch)]
  apply AllI_touchZ (PCx L1 c4 h) (PCx L2 c4 (4 + h)) [(p, 1, false)] [] Z 1 hZ
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx, Lift] at h0 ⊢
    rw [List.length_append, List.length_singleton] at h0
    rw [List.length_append, List.length_map, List.length_nil, Nat.add_zero]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, 1, false)] hZr] at h0
    rw [dv_tz' Zr [] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hpos := pow_pos Zr.length
    have h_tv1 : 1 + 2 * (2 ^ Zr.length - 1) = 2 * 2 ^ Zr.length - 1 := by omega
    rw [h_tv1]
    have hq0 : 2 ≤ q0 := q2_V0 L1 c4 h j p0 q0 (Zr.length + 1) h0 (by omega) (by intro h'; nomatch h')
    exact ob_endlast c4 h j p0 q0 Zr.length hq0 h0
  · exact hA
  · exact trivial

lemma inv_Ov (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h p1 q1 : Nat) (Z : List Tri) (t : Nat)
    (htr : ovtr ph ph' c4' Xp) (ht1 : ph = L2 → 2 ≤ t) (ht2 : ph ≠ L2 → t = 1)
    (hZ : ∀ y ∈ Z, dig0 y) (hX : lastOK Xp Z)
    (hA : AllI (PCx ph false h) 1 ((p1 + 2, q1, false) :: Z)) :
    AllI (PCx ph' c4' 2) 1 ((h + 5, p1 + 1, false) :: ovp q1 Z t) := by
  dsimp [AllI] at hA ⊢
  rcases hA with ⟨hhead, htail⟩
  have hhead' := hhead
  dsimp [PCx, Lift] at hhead'
  have hZ_cons : ∀ y ∈ (p1 + 2, q1, false) :: Z, dig0 y := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hyZ
    · rfl
    · exact hZ y hyZ
  rw [dv_zero _ hZ_cons] at hhead'
  refine ⟨?_, ?_⟩
  · dsimp [PCx, Lift]
    rw [ovp_len]
    have h_dv : dv ((h + 5, p1 + 1, false) :: ovp q1 Z t) = 2 * (2 * 2 ^ Z.length) - 2 := by
      dsimp [dv, bv]
      have E := ovp_dv q1 Z t
      rw [pow_S Z.length] at E
      omega
    rw [h_dv]
    exact ob_ov_head ph ph' c4' Xp h p1 q1 Z.length htr hhead'
  · exact AllI_ovp ph ph' c4' Xp h t htr ht1 ht2 Z 1 (p1 + 2) q1 (by omega) hZ hX hhead' htail

lemma inv_X1 (h p1 q1 : Nat) (Z : List Tri) (pa pb : Nat)
    (hZ : ∀ y ∈ Z, dig0 y)
    (hA : AllI (PCx LX false h) 1 ((p1 + 2, q1, false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)]))) :
    AllI (PCx T0 false 2) 1 ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) := by
  dsimp [AllI] at hA ⊢
  rcases hA with ⟨hhead, htail⟩
  have hhead' := hhead
  dsimp [PCx, Lift] at hhead'
  have hZ_all : ∀ y ∈ (p1 + 2, q1, false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)]), dig0 y := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · rcases List.mem_append.mp hy' with hyZ | hy2
      · exact hZ y hyZ
      · rcases List.mem_cons.mp hy2 with rfl | hy1
        · rfl
        · rcases List.mem_singleton.mp hy1 with rfl; rfl
  rw [dv_zero _ hZ_all, List.length_append] at hhead'
  dsimp at hhead'
  refine ⟨?_, ?_⟩
  · dsimp [PCx, Lift]
    rw [ovpX_len]
    have h_dv : dv ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) = 2 * 2 ^ Z.length - 2 := by
      dsimp [dv, bv]
      have E := ovpX_dv q1 Z (pa + 1)
      omega
    rw [h_dv]
    exact ob_x1_head h p1 q1 Z.length hhead'
  · exact AllI_ovpX h pa pb Z 1 (p1 + 2) q1 (by omega) hZ hhead' htail

structure St where
  sh : Nat
  sP : List Tri
  sT : Tl
  sph : Phase
  sc4 : Bool

def Cf (s : St) : Cfg (Fin 2) (Fin 6) := K s.sh s.sP s.sT

def TC (ph : Phase) (c4 : Bool) (T : Tl) : Prop :=
  match ph with
  | E1 | E1t | LX => T = TN ∧ c4 = false
  | L1 => T = TN
  | E2 | E2t => T = TA 1 ∧ c4 = false
  | T0 => (∃ k, T = TB k ∧ 3 ≤ k) ∧ c4 = false
  | L2 => ∃ t, T = TA t ∧ 2 ≤ t

def J (s : St) : Prop :=
  s.sP ≠ [] ∧ TC s.sph s.sc4 s.sT ∧ AllI (PCx s.sph s.sc4 s.sh) 1 s.sP

lemma split1 (P : List Tri) :
    (∃ Z x R, P = Z ++ x :: R ∧ (∀ y ∈ Z, dig0 y) ∧ dig x = true) ∨ (∀ y ∈ P, dig0 y) := by
  induction P with
  | nil => exact Or.inr (by intro y hy; nomatch hy)
  | cons x P' ih =>
    rcases x with ⟨p, q, d⟩
    cases d with
    | true =>
      exact Or.inl ⟨[], (p, q, true), P', rfl, (by intro y hy; nomatch hy), rfl⟩
    | false =>
      rcases ih with ⟨Z, x, R, rfl, hZ, hx⟩ | h0
      · refine Or.inl ⟨(p, q, false) :: Z, x, R, rfl, ?_, hx⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hyZ
        · rfl
        · exact hZ y hyZ
      · refine Or.inr ?_
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hyP
        · rfl
        · exact h0 y hyP

lemma exists_last {P : List Tri} (hP : P ≠ []) : ∃ (Z : List Tri) (y : Tri), P = Z ++ [y] := by
  induction P with
  | nil => exact False.elim (hP rfl)
  | cons x P' ih =>
    cases P' with
    | nil => exact ⟨[], x, rfl⟩
    | cons x' P'' =>
      obtain ⟨Z, y, h_eq⟩ := ih (by intro h; nomatch h)
      exact ⟨x :: Z, y, by rw [h_eq]; rfl⟩

lemma Z_okL_V0 (ph : Phase) (c4 : Bool) (h : Nat) (y : Tri) (hph : ph ≠ LX)
    (Z : List Tri) (i : Nat)
    (hZ : ∀ x ∈ Z ++ [y], dig0 x)
    (hA : AllI (PCx ph c4 h) i (Z ++ [y])) :
    ∀ x ∈ Z, okL x := by
  induction Z generalizing i with
  | nil => exact okL_nil
  | cons z Z ih =>
    rcases z with ⟨p, q, d⟩
    have hd : d = false := hZ (p, q, d) List.mem_cons_self
    subst hd
    have hZ' : ∀ x ∈ Z ++ [y], dig0 x := fun x hx => hZ x (List.mem_cons_of_mem _ hx)
    have hZ_cons : ∀ x ∈ (p, q, false) :: (Z ++ [y]), dig0 x := hZ
    dsimp [AllI] at hA
    rcases hA with ⟨hhead, htail⟩
    dsimp [PCx, Lift] at hhead
    rw [dv_zero _ hZ_cons, List.length_append, List.length_singleton] at hhead
    have hq2 : 2 ≤ q := q2_V0 ph c4 h i p q (Z.length + 1) hhead (by omega) (fun h' => False.elim (hph h'))
    exact okL_cons hq2 (ih (i + 1) hZ' htail)

lemma last_pc (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p q : Nat) (d : Bool)
    (hZ : ∀ x ∈ Z ++ [(p, q, d)], dig0 x)
    (hA : AllI (PCx ph c4 h) 1 (Z ++ [(p, q, d)])) :
    d = false ∧ PC ph c4 h (1 + Z.length) p q 0 0 := by
  have hd : d = false := hZ (p, q, d) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  subst hd
  refine ⟨rfl, ?_⟩
  have hB := AllI_app (PCx ph c4 h) Z 1 [(p, q, false)] hA
  dsimp [AllI, PCx, Lift, List.length, dv, bv] at hB
  exact hB.1

lemma first_pc (ph : Phase) (c4 : Bool) (h p q : Nat) (d : Bool) (Z : List Tri)
    (hZ : ∀ x ∈ (p, q, d) :: Z, dig0 x)
    (hA : AllI (PCx ph c4 h) 1 ((p, q, d) :: Z)) :
    d = false ∧ PC ph c4 h 1 p q Z.length 0 ∧ (∀ x ∈ Z, dig0 x) ∧ AllI (PCx ph c4 h) 2 Z := by
  have hd : d = false := hZ (p, q, d) List.mem_cons_self
  subst hd
  have hZ' : ∀ x ∈ Z, dig0 x := fun x hx => hZ x (List.mem_cons_of_mem _ hx)
  dsimp [AllI] at hA
  rcases hA with ⟨hhead, htail⟩
  dsimp [PCx, Lift] at hhead
  rw [dv_zero _ hZ] at hhead
  exact ⟨rfl, hhead, hZ', htail⟩

lemma cons_nn (x : Tri) (Z : List Tri) : x :: Z ≠ [] := by
  intro h; nomatch h

lemma app_cons_nn (Z : List Tri) (x : Tri) (R : List Tri) : Z ++ x :: R ≠ [] := by
  cases Z <;> intro h <;> nomatch h

lemma Jstep (s : St) (hs : J s) : ∃ s', ((Cf s) [target_tm]⊢⁺ (Cf s')) ∧ J s' := by
  rcases s with ⟨h, P, T, ph, c4⟩
  rcases hs with ⟨hP, hT, hA⟩
  dsimp [Cf] at hP hT hA ⊢
  rcases split1 P with ⟨Z, ⟨p, q, d⟩, R, rfl, hZ, hd⟩ | h0
  · dsimp [dig] at hd
    subst hd
    have hZL : ∀ y ∈ Z, okL y := Z_okL ph c4 h Z 1 (p, q, true) R hZ rfl hA
    have hB := AllI_app (PCx ph c4 h) Z 1 ((p, q, true) :: R) hA
    dsimp [AllI] at hB
    rcases hB with ⟨hx, hR⟩
    have hx' := hx
    dsimp [PCx, Lift] at hx'
    rcases q with _ | _ | q
    · exfalso; rcases hx' with ⟨_, hq, _⟩; omega
    · rcases borrow1 ph c4 h (1 + Z.length) p R.length (dv ((p, 1, true) :: R)) (by omega)
        (by dsimp [dv, bv]; omega) hx' with ⟨hph, hk, hL1, hLX⟩
      cases R with
      | nil =>
        cases T with
        | TN =>
          exfalso
          rcases hph with rfl | rfl | rfl
          · rcases hL1 rfl with ⟨hn, _⟩; dsimp at hn; omega
          · rcases hT with ⟨t, ht, _⟩; nomatch ht
          · have hn := hLX rfl; dsimp at hn; omega
        | TA t =>
          have h_ph : ph = L2 := by
            rcases hph with rfl | rfl | rfl
            · dsimp [TC] at hT; nomatch hT
            · rfl
            · dsimp [TC] at hT; nomatch hT.1
          subst h_ph
          rcases hT with ⟨t', ht, ht2⟩
          cases ht
          rcases inv_MT c4 h Z p hZ hA with ⟨hA', hlen⟩
          refine ⟨⟨4 + h, Z.map touch, TA (p + t + 3), L2, false⟩, ?_, ?_⟩
          · exact DecMergeTail h Z p t hZL
          · refine ⟨?_, ⟨p + t + 3, rfl, by omega⟩, hA'⟩
            cases Z with
            | nil => dsimp at hlen; omega
            | cons _ _ => exact cons_nn _ _
        | TB k =>
          exfalso
          rcases hph with rfl | rfl | rfl
          · dsimp [TC] at hT; nomatch hT
          · rcases hT with ⟨t, ht, _⟩; nomatch ht
          · dsimp [TC] at hT; nomatch hT.1
      | cons y R0 =>
        rcases y with ⟨p', q', d'⟩
        refine ⟨⟨4 + h, Z.map touch ++ (p + p' + 3, q', d') :: R0, T, ph, c4⟩, ?_, ?_⟩
        · exact DecMerge h Z p p' q' d' R0 T hZL
        · exact ⟨app_cons_nn _ _ _, hT, inv_Merge ph c4 h Z p p' q' d' R0 hZ hA⟩
    · refine ⟨⟨4 + h, Z.map touch ++ (p + 1, q + 1, false) :: R, T, ph, c4⟩, ?_, ?_⟩
      · exact Dec h Z p q R T hZL
      · exact ⟨app_cons_nn _ _ _, hT, inv_Dec ph c4 h Z p q R hZ hA⟩
  · cases ph with
    | E1 =>
      rcases hT with ⟨rfl, rfl⟩
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc E1 false h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN] at hN; omega
      rcases q with _ | _ | q <;> [omega; omega; skip]
      have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 E1 false h (p, q + 2, false) (by decide) Z 1 h0 hA
      have hZ : ∀ x ∈ Z, dig0 x := fun x hx => h0 x (List.mem_append_left _ hx)
      refine ⟨⟨4 + h, Z.map touch ++ [(p + 1, q + 1, false)], TA 1, E2, false⟩, ?_, ?_⟩
      · exact EndR h Z p q hZL
      · exact ⟨snoc_nn _ _, ⟨rfl, rfl⟩, inv_End E1 E2 h Z p q (Or.inl ⟨rfl, rfl⟩) hZ hA⟩
    | E2 =>
      rcases hT with ⟨rfl, rfl⟩
      cases P with
      | nil => exact False.elim (hP rfl)
      | cons x Z =>
        rcases x with ⟨p1, q1, d1⟩
        rcases first_pc E2 false h p1 q1 d1 Z h0 hA with ⟨rfl, hh, hZ, hA2⟩
        have hp1 : 2 ≤ p1 := p1_V0 E2 false h p1 q1 Z.length hh (Or.inl rfl)
        rcases p1 with _ | _ | p1 <;> [omega; omega; skip]
        rcases AllI_okRO E2 false h Z 2 hZ hA2 with ⟨hR, hO⟩
        have hq1 : 1 ≤ q1 := hh.2.1
        rcases lastOK_dec Z with hX | hX
        · refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, TN, LX, false⟩, ?_, ?_⟩
          · exact Ov h p1 q1 Z 1 hq1 hR hO
          · refine ⟨cons_nn _ _, ⟨rfl, rfl⟩, ?_⟩
            exact inv_Ov E2 LX false (fun x => x = 4) h p1 q1 Z 1
              (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (by intro h'; nomatch h') (fun _ => rfl) hZ hX hA
        · refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, TN, L1, false⟩, ?_, ?_⟩
          · exact Ov h p1 q1 Z 1 hq1 hR hO
          · refine ⟨cons_nn _ _, rfl, ?_⟩
            exact inv_Ov E2 L1 false (fun x => x ≠ 4) h p1 q1 Z 1
              (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by intro h'; nomatch h') (fun _ => rfl) hZ hX hA
    | E1t =>
      rcases hT with ⟨rfl, rfl⟩
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc E1t false h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN] at hN; omega
      rcases q with _ | _ | q <;> [omega; omega; skip]
      have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 E1t false h (p, q + 2, false) (by decide) Z 1 h0 hA
      have hZ : ∀ x ∈ Z, dig0 x := fun x hx => h0 x (List.mem_append_left _ hx)
      refine ⟨⟨4 + h, Z.map touch ++ [(p + 1, q + 1, false)], TA 1, E2t, false⟩, ?_, ?_⟩
      · exact EndR h Z p q hZL
      · exact ⟨snoc_nn _ _, ⟨rfl, rfl⟩, inv_End E1t E2t h Z p q (Or.inr ⟨rfl, rfl⟩) hZ hA⟩
    | E2t =>
      rcases hT with ⟨rfl, rfl⟩
      cases P with
      | nil => exact False.elim (hP rfl)
      | cons x Z =>
        rcases x with ⟨p1, q1, d1⟩
        rcases first_pc E2t false h p1 q1 d1 Z h0 hA with ⟨rfl, hh, hZ, hA2⟩
        have hp1 : 2 ≤ p1 := p1_V0 E2t false h p1 q1 Z.length hh (Or.inr (Or.inl rfl))
        rcases p1 with _ | _ | p1 <;> [omega; omega; skip]
        rcases AllI_okRO E2t false h Z 2 hZ hA2 with ⟨hR, hO⟩
        have hq1 : 1 ≤ q1 := hh.2.1
        refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, TN, L1, true⟩, ?_, ?_⟩
        · exact Ov h p1 q1 Z 1 hq1 hR hO
        · refine ⟨cons_nn _ _, rfl, ?_⟩
          exact inv_Ov E2t L1 true (fun _ => True) h p1 q1 Z 1
            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))) (by intro h'; nomatch h') (fun _ => rfl)
            hZ (lastOK_True Z) hA
    | T0 =>
      rcases hT with ⟨⟨k, rfl, hk⟩, rfl⟩
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc T0 false h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN] at hN; omega
      rcases q with _ | _ | q <;> [omega; omega; skip]
      rcases k with _ | k <;> [omega; skip]
      have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 T0 false h (p, q + 2, false) (by decide) Z 1 h0 hA
      have hZ : ∀ x ∈ Z, dig0 x := fun x hx => h0 x (List.mem_append_left _ hx)
      refine ⟨⟨4 + h, Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)], TN, E1t, false⟩, ?_, ?_⟩
      · exact X2 h Z p q k hZL
      · exact ⟨app_cons_nn _ _ _, ⟨rfl, rfl⟩, inv_X2 h Z p q (k + 1) hZ hk hA⟩
    | L1 =>
      dsimp [TC] at hT
      subst hT
      rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
      rcases last_pc L1 c4 h Z p q d h0 hA with ⟨rfl, hy⟩
      have hq : q = 1 := by rcases hy with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN] at hN; omega
      subst hq
      have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 L1 c4 h (p, 1, false) (by decide) Z 1 h0 hA
      have hZ : ∀ x ∈ Z, dig0 x := fun x hx => h0 x (List.mem_append_left _ hx)
      rcases inv_EndLast c4 h Z p hZ hA with ⟨hA', hlen⟩
      refine ⟨⟨4 + h, Z.map touch, TA (p + 4), L2, c4⟩, ?_, ?_⟩
      · exact EndLast h Z p hZL
      · refine ⟨?_, ⟨p + 4, rfl, by omega⟩, hA'⟩
        cases Z with
        | nil => dsimp at hlen; omega
        | cons _ _ => exact cons_nn _ _
    | L2 =>
      rcases hT with ⟨t, rfl, ht⟩
      cases c4 with
      | true =>
        exfalso
        rcases exists_last hP with ⟨Z, ⟨p, q, d⟩, rfl⟩
        rcases last_pc L2 true h Z p q d h0 hA with ⟨rfl, hy⟩
        exact L2_c4_V0 h (1 + Z.length) p q hy
      | false =>
        cases P with
        | nil => exact False.elim (hP rfl)
        | cons x Z =>
          rcases x with ⟨p1, q1, d1⟩
          rcases first_pc L2 false h p1 q1 d1 Z h0 hA with ⟨rfl, hh, hZ, hA2⟩
          have hp1 : 2 ≤ p1 := p1_V0 L2 false h p1 q1 Z.length hh (Or.inr (Or.inr (Or.inl rfl)))
          rcases p1 with _ | _ | p1 <;> [omega; omega; skip]
          rcases AllI_okRO L2 false h Z 2 hZ hA2 with ⟨hR, hO⟩
          have hq1 : 1 ≤ q1 := hh.2.1
          refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z t, TN, E1, false⟩, ?_, ?_⟩
          · exact Ov h p1 q1 Z t hq1 hR hO
          · refine ⟨cons_nn _ _, ⟨rfl, rfl⟩, ?_⟩
            exact inv_Ov L2 E1 false (fun _ => True) h p1 q1 Z t
              (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))) (fun _ => ht) (fun h' => False.elim (h' rfl))
              hZ (lastOK_True Z) hA
    | LX =>
      rcases hT with ⟨rfl, rfl⟩
      have hlen := AllI_len LX false h P hP hA
      dsimp [minlen] at hlen
      rcases exists_last hP with ⟨P1, ⟨pb, qb, db⟩, rfl⟩
      have hP1 : P1 ≠ [] := by
        cases P1 with
        | nil => dsimp at hlen; omega
        | cons _ _ => exact cons_nn _ _
      rcases exists_last hP1 with ⟨P2, ⟨pa, qa, da⟩, rfl⟩
      cases P2 with
      | nil => dsimp at hlen; omega
      | cons x Z =>
        rcases x with ⟨p1, q1, d1⟩
        have h_assoc : (p1, q1, d1) :: Z ++ [(pa, qa, da)] ++ [(pb, qb, db)] =
            (p1, q1, d1) :: (Z ++ [(pa, qa, da), (pb, qb, db)]) := by simp
        rw [h_assoc] at h0 hA ⊢
        rcases first_pc LX false h p1 q1 d1 (Z ++ [(pa, qa, da), (pb, qb, db)]) h0 hA with ⟨rfl, hh, hZab, hA2⟩
        have hZ : ∀ x ∈ Z, dig0 x := fun x hx => hZab x (List.mem_append_left _ hx)
        have hda : da = false := hZab (pa, qa, da) (List.mem_append_right _ List.mem_cons_self)
        have hdb : db = false := hZab (pb, qb, db) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
        subst hda hdb
        have hB := AllI_app (PCx LX false h) Z 2 [(pa, qa, false), (pb, qb, false)] hA2
        dsimp [AllI, PCx, Lift, List.length, dv, bv] at hB
        rcases hB with ⟨ha, hb, _⟩
        have hqa : qa = 1 := by rcases ha with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN] at hN; omega
        have hqb : qb = 1 := by rcases hb with ⟨_, _, hN, _⟩; simp -failIfUnchanged only [PN] at hN; omega
        subst hqa hqb
        have hpa : 1 ≤ pa := ha.1
        rcases pa with _ | pa <;> [omega; skip]
        have hp1 : 2 ≤ p1 := p1_V0 LX false h p1 q1 (Z ++ [(pa + 1, 1, false), (pb, 1, false)]).length hh
          (Or.inr (Or.inr (Or.inr rfl)))
        rcases p1 with _ | _ | p1 <;> [omega; omega; skip]
        rcases AllI_okRO LX false h (Z ++ [(pa + 1, 1, false), (pb, 1, false)]) 2 hZab hA2 with ⟨hR_all, hO_all⟩
        have hR : ∀ x ∈ Z, okR x := fun x hx => hR_all x (List.mem_append_left _ hx)
        have hO : ∀ x ∈ Z, okO x := fun x hx => hO_all x (List.mem_append_left _ hx)
        have hq1 : 1 ≤ q1 := hh.2.1
        refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1), TB (pb + 3), T0, false⟩, ?_, ?_⟩
        · exact X1 h p1 q1 Z pa pb hq1 hR hO
        · exact ⟨cons_nn _ _, ⟨⟨pb + 3, rfl, by omega⟩, rfl⟩, inv_X1 h p1 q1 Z pa pb hZ hA⟩

lemma J_base23 : J ⟨2, base23, TN, E1, false⟩ := by
  refine ⟨by decide, ⟨rfl, rfl⟩, ?_⟩
  simp only [base23, AllI, PCx, Lift, PC, PN, PI, dv, bv]
  split_and <;> decide

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine closed_inv_does_not_halt target_tm (fun cfg => ∃ s, cfg = Cf s ∧ J s) ?_ ?_
  · exact ⟨Cf ⟨2, base23, TN, E1, false⟩, init_to_base23, ⟨2, base23, TN, E1, false⟩, rfl, J_base23⟩
  · rintro cfg ⟨s, rfl, hs⟩
    obtain ⟨s', hstep, hs'⟩ := Jstep s hs
    exact ⟨Cf s', hstep, s', rfl, hs'⟩

end BusyBeaver.M_1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RBHHH
