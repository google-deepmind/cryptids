/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RA---_0RE0LB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RA---_0RE0LB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RA---_0RE0LB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => none
  | 5, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

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

lemma pow_add3_append_right (u : List (Fin 2)) (k₁ k₂ k₃ : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (k₁ + k₂ + k₃)) +> r = (u ^ k₁) +> ((u ^ k₂) +> ((u ^ k₃) +> r)) := by
  rw [pow_add_append_right u (k₁ + k₂) k₃ r, pow_add_append_right u k₁ k₂ ((u ^ k₃) +> r)]

lemma pow_add3_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (k₁ k₂ k₃ : Nat) :
    s <+ (u ^ (k₁ + k₂ + k₃)) = ((s <+ (u ^ k₁)) <+ (u ^ k₂)) <+ (u ^ k₃) := by
  rw [pow_add_append_left s u (k₁ + k₂) k₃, pow_add_append_left s u k₁ k₂]

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

lemma step_some {c c' : Cfg (Fin 2) (Fin 6)} (h : step target_tm c = some c') :
    c [target_tm]⊢⁺ c' := ⟨1, Nat.zero_lt_one, h⟩

lemma stepPlus_step_left {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h1 : step target_tm c₁ = some c₂) (h2 : c₂ [target_tm]⊢⁺ c₃) :
    c₁ [target_tm]⊢⁺ c₃ := step_stepStar_stepPlus h1 (stepPlus_stepStar h2)

lemma stepStar_step_left {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h1 : step target_tm c₁ = some c₂) (h2 : c₂ [target_tm]⊢* c₃) :
    c₁ [target_tm]⊢* c₃ := stepStar_trans (step_stepStar target_tm c₁ c₂ h1) h2

lemma stepPlus_stepStar_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h1 : c₁ [target_tm]⊢⁺ c₂) (h2 : c₂ [target_tm]⊢* c₃) :
    c₁ [target_tm]⊢⁺ c₃ := stepPlus_stepStar_stepPlus h1 h2

lemma stepStar_stepPlus_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h1 : c₁ [target_tm]⊢* c₂) (h2 : c₂ [target_tm]⊢⁺ c₃) :
    c₁ [target_tm]⊢⁺ c₃ := stepStar_stepPlus_stepPlus h1 h2

lemma stepPlus_of_step {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [target_tm]⊢ c₂) :
    c₁ [target_tm]⊢⁺ c₂ := step_stepPlus target_tm c₁ c₂ h

lemma stepStar_of_stepPlus {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [target_tm]⊢⁺ c₂) :
    c₁ [target_tm]⊢* c₂ := stepPlus_stepStar h

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))
macro "execute" : tactic =>
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

theorem closed_hub_does_not_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (hub : Nat → Cfg Γ Λ)
    (n₀ : Nat) (h_init : (init []) [M]⊢* hub n₀)
    (h_step : ∀ n, ∃ n', (hub n) [M]⊢⁺ (hub n')) :
    IsDoesNotHalt M := by
  refine closed_inv_does_not_halt M (fun cfg => ∃ n, cfg = hub n) ⟨hub n₀, h_init, ⟨n₀, rfl⟩⟩ ?_
  intro cfg ⟨n, hcfg⟩
  subst hcfg
  obtain ⟨n', hn'⟩ := h_step n
  exact ⟨hub n', hn', ⟨n', rfl⟩⟩

theorem closed_guarded_hub_does_not_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (hub : Nat → Cfg Γ Λ) (P : Nat → Prop)
    (n₀ : Nat) (h_P₀ : P n₀) (h_init : (init []) [M]⊢* hub n₀)
    (h_step : ∀ n, P n → ∃ n', P n' ∧ ((hub n) [M]⊢⁺ (hub n'))) :
    IsDoesNotHalt M := by
  refine closed_inv_does_not_halt M (fun cfg => ∃ n, P n ∧ cfg = hub n) ⟨hub n₀, h_init, ⟨n₀, h_P₀, rfl⟩⟩ ?_
  intro cfg ⟨n, hPn, hcfg⟩
  subst hcfg
  obtain ⟨n', hPn', hn'⟩ := h_step n hPn
  exact ⟨hub n', hn', ⟨n', hPn', rfl⟩⟩

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
abbrev sA : Fin 6 := 0
abbrev sB : Fin 6 := 1
abbrev sC : Fin 6 := 2
abbrev sD : Fin 6 := 3
abbrev sE : Fin 6 := 4
abbrev sF : Fin 6 := 5
abbrev holdout_0446_tm : Machine (Fin 2) (Fin 6) := target_tm
abbrev M : Machine (Fin 2) (Fin 6) := target_tm
@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl

-- ============================================================================
-- Sweeps Transducer & Valid Token-List Closure for Holdout 0446
-- ============================================================================

lemma rule_B_000 (l r : ListBlank (Fin 2)) :
    (l {{A}}> ([0, 0, 0] +> r)) [target_tm]⊢⁺ (l <{{D}} ([0, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_001 (l r : ListBlank (Fin 2)) :
    (l {{A}}> ([0, 0, 1] +> r)) [target_tm]⊢⁺ ((l <+ [1, 1, 1]) {{A}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_010 (l r : ListBlank (Fin 2)) :
    (l {{A}}> ([0, 1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [1, 0, 1]) {{A}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_100 (l r : ListBlank (Fin 2)) :
    (l {{A}}> ([1, 0, 0] +> r)) [target_tm]⊢⁺ ((l <+ [1, 0, 0]) {{A}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_111 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 1]) <{{D}} r) [target_tm]⊢⁺ (l <{{D}} ([0, 0, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_101 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 0, 1]) <{{D}} r) [target_tm]⊢⁺ (l <{{D}} ([0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_100 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 0, 0]) <{{D}} r) [target_tm]⊢⁺ (l {{A}}> ([0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_nil (r : ListBlank (Fin 2)) :
    (default <{{D}} ((0 : Fin 2) >> r)) [target_tm]⊢⁺ ((default <+ [1, 0, 1]) {{A}}> r) := by
  dsimp [ListBlank.append]; execute

abbrev Round (r r' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2), (l {{A}}> r) [target_tm]⊢⁺ (l <{{D}} r')

inductive Sweeps : Nat → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | zero (r : ListBlank (Fin 2)) : Sweeps 0 r r
  | succ {n : Nat} {r r₁ r₂ : ListBlank (Fin 2)} :
      Round r r₁ → Sweeps n r₁ r₂ → Sweeps (n + 1) r r₂

lemma Sweeps.trans {a b : Nat} {r₁ r₂ r₃ : ListBlank (Fin 2)}
    (h₁ : Sweeps a r₁ r₂) (h₂ : Sweeps b r₂ r₃) : Sweeps (a + b) r₁ r₃ := by
  induction h₁ with
  | zero _ => simpa using h₂
  | succ hr _ ih =>
    rw [Nat.succ_add]
    exact Sweeps.succ hr (ih h₂)

lemma round_000 (r : ListBlank (Fin 2)) :
    Round ([0, 0, 0] +> r) ([0, 0, 1] +> r) :=
  fun l => rule_B_000 l r

lemma round_001 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 0, 1] +> r) ([0, 0, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_001 l r) (stepPlus_trans (h (l <+ [1, 1, 1])) (rule_E_111 l r'))

lemma round_010 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 1, 0] +> r) ([0, 1, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_010 l r) (stepPlus_trans (h (l <+ [1, 0, 1])) (rule_E_101 l r'))

lemma round_100 {r r₁ r₂ : ListBlank (Fin 2)} (h₁ : Round r r₁) (h₂ : Round r₁ r₂) :
    Round ([1, 0, 0] +> r) ([0, 1, 0] +> r₂) :=
  fun l => stepPlus_trans (rule_B_100 l r)
    (stepPlus_trans (h₁ (l <+ [1, 0, 0]))
      (stepPlus_trans (rule_E_100 l r₁) (round_010 h₂ l)))

lemma sweeps_010 {n : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps n r r') :
    Sweeps n ([0, 1, 0] +> r) ([0, 1, 0] +> r') := by
  induction h with
  | zero r => exact Sweeps.zero _
  | succ hr _ ih => exact Sweeps.succ (round_010 hr) ih

lemma sweeps_100 {n : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps (n + 2) r r') :
    Sweeps (n + 1) ([1, 0, 0] +> r) ([0, 1, 0] +> r') := by
  cases h with
  | succ hr₁ hrest =>
    cases hrest with
    | succ hr₂ hs =>
      exact Sweeps.succ (round_100 hr₁ hr₂) (sweeps_010 hs)

lemma sweeps_000_even {k : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps k r r') :
    Sweeps (2 * k) ([0, 0, 0] +> r) ([0, 0, 0] +> r') := by
  induction h with
  | zero r => exact Sweeps.zero _
  | @succ m r₀ r₁ r₂ hr _ ih =>
    have h2 : Sweeps 2 ([0, 0, 0] +> r₀) ([0, 0, 0] +> r₁) :=
      Sweeps.succ (round_000 r₀) (Sweeps.succ (round_001 hr) (Sweeps.zero _))
    have htr := Sweeps.trans h2 ih
    rw [show 2 + 2 * m = 2 * (m + 1) by omega] at htr
    exact htr

lemma sweeps_000_odd {k : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps k r r') :
    Sweeps (2 * k + 1) ([0, 0, 0] +> r) ([0, 0, 1] +> r') := by
  have he := sweeps_000_even h
  have h1 : Sweeps 1 ([0, 0, 0] +> r') ([0, 0, 1] +> r') :=
    Sweeps.succ (round_000 r') (Sweeps.zero _)
  exact Sweeps.trans he h1

inductive Tok
  | t0
  | t1
  | t2

def enc : List Tok → ListBlank (Fin 2)
  | [] => default
  | .t0 :: t => [0, 0, 0] +> enc t
  | .t1 :: t => [0, 0, 1] +> enc t
  | .t2 :: t => [0, 1, 0] +> enc t

def rest_of : List Tok → ListBlank (Fin 2)
  | [] => default
  | .t0 :: t => [0, 0, 0] +> rest_of t
  | .t1 :: t => [0, 1, 0] +> rest_of t
  | .t2 :: t => [1, 0, 0] +> rest_of t

lemma enc_eq_zero_cons_rest (t : List Tok) :
    enc t = (0 : Fin 2) >> rest_of t := by
  induction t with
  | nil => exact zero_cons_default.symm
  | cons x t ih =>
    cases x <;>
    · simp only [enc, rest_of, listblank_append_cons, listblank_append_nil]
      rw [ih]

lemma rest_of_nil_eq :
    rest_of [] = [0, 0, 0] +> rest_of [] := by
  simp only [rest_of, listblank_append_cons, listblank_append_nil, zero_cons_default]

inductive Valid : Nat → List Tok → Prop
  | nil {n : Nat} (hn : n ≥ 1) : Valid n []
  | t0 {n : Nat} {t : List Tok} (hn : n ≥ 2) (ht : Valid (n / 2) t) : Valid n (.t0 :: t)
  | t1 {n : Nat} {t : List Tok} (hn : n ≥ 1) (ht : Valid n t) : Valid n (.t1 :: t)
  | t2 {n : Nat} {t : List Tok} (hn : n ≥ 1) (ht : Valid (n + 1) t) : Valid n (.t2 :: t)

lemma Valid.mono {n : Nat} {t : List Tok} (h : Valid n t) {n' : Nat} (hle : n ≤ n') :
    Valid n' t := by
  induction h generalizing n' with
  | nil hn => exact Valid.nil (by omega)
  | t0 hn _ ih => exact Valid.t0 (by omega) (ih (by omega))
  | t1 hn _ ih => exact Valid.t1 (by omega) (ih (by omega))
  | t2 hn _ ih => exact Valid.t2 (by omega) (ih (by omega))

lemma valid_sweeps_nil : ∀ n : Nat, n ≥ 1 →
    ∃ t' : List Tok, Valid n t' ∧ Sweeps n (rest_of []) (enc t') := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases ( by omega : n = 1 ∨ (n ≥ 2 ∧ n % 2 = 0) ∨ (n ≥ 2 ∧ n % 2 = 1) ) with rfl | ⟨hn2, hev⟩ | ⟨hn2, hod⟩
    · refine ⟨[.t1], Valid.t1 (by omega) (Valid.nil (by omega)), ?_⟩
      rw [rest_of_nil_eq]
      exact Sweeps.succ (round_000 (enc [])) (Sweeps.zero _)
    · obtain ⟨t', ht', hs'⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨.t0 :: t', Valid.t0 hn2 ht', ?_⟩
      have he := sweeps_000_even hs'
      rw [← rest_of_nil_eq, show 2 * (n / 2) = n by omega] at he
      exact he
    · obtain ⟨t', ht', hs'⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨.t1 :: t', Valid.t1 (by omega) (ht'.mono (by omega)), ?_⟩
      have ho := sweeps_000_odd hs'
      rw [← rest_of_nil_eq, show 2 * (n / 2) + 1 = n by omega] at ho
      exact ho

lemma valid_sweeps {n : Nat} {t : List Tok} (h : Valid n t) :
    ∃ t' : List Tok, Valid n t' ∧ Sweeps n (rest_of t) (enc t') := by
  induction h with
  | @nil n hn => exact valid_sweeps_nil n hn
  | @t0 n t hn ht ih =>
    obtain ⟨t', ht', hs'⟩ := ih
    rcases ( by omega : n % 2 = 0 ∨ n % 2 = 1 ) with hev | hod
    · refine ⟨.t0 :: t', Valid.t0 hn ht', ?_⟩
      have he := sweeps_000_even hs'
      rw [show 2 * (n / 2) = n by omega] at he
      exact he
    · refine ⟨.t1 :: t', Valid.t1 (by omega) (ht'.mono (by omega)), ?_⟩
      have ho := sweeps_000_odd hs'
      rw [show 2 * (n / 2) + 1 = n by omega] at ho
      exact ho
  | @t1 n t hn ht ih =>
    obtain ⟨t', ht', hs'⟩ := ih
    exact ⟨.t2 :: t', Valid.t2 hn (ht'.mono (by omega)), sweeps_010 hs'⟩
  | @t2 n t hn ht ih =>
    obtain ⟨t', ht', hs'⟩ := ih
    refine ⟨.t2 :: t', Valid.t2 hn ht', ?_⟩
    rw [show n + 1 = (n - 1) + 2 by omega] at hs'
    have h100 := sweeps_100 hs'
    rw [show (n - 1) + 1 = n by omega] at h100
    exact h100

lemma sweeps_one_round {r r' : ListBlank (Fin 2)} (h : Sweeps 1 r r') :
    Round r r' := by
  cases h with
  | succ hr h0 =>
    cases h0 with
    | zero _ => exact hr

lemma era_step {t : List Tok} (h : Valid 1 t) :
    ∃ t' : List Tok, Valid 1 t' ∧
      ((default <{{D}} enc t) [target_tm]⊢⁺ (default <{{D}} enc t')) := by
  obtain ⟨t₁, ht₁, hs₁⟩ := valid_sweeps h
  refine ⟨.t2 :: t₁, Valid.t2 (by omega) (ht₁.mono (by omega)), ?_⟩
  rw [enc_eq_zero_cons_rest t]
  have s1 := rule_E_nil (rest_of t)
  have s2 := sweeps_one_round hs₁ (default <+ [1, 0, 1])
  have s3 := rule_E_101 default (enc t₁)
  exact stepPlus_trans s1 (stepPlus_trans s2 s3)

lemma init_reaches_era0 :
    (init []) [target_tm]⊢* (default <{{D}} enc [.t1]) := by
  apply stepPlus_stepStar
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  dsimp [enc, ListBlank.append]
  execute

lemma valid_era0 : Valid 1 [.t1] :=
  Valid.t1 (by omega) (Valid.nil (by omega))

theorem holdout_0446_nonhalt : IsDoesNotHalt holdout_0446_tm := by
  refine closed_inv_does_not_halt target_tm
    (fun cfg => ∃ t : List Tok, Valid 1 t ∧ cfg = (default <{{D}} enc t))
    ⟨default <{{D}} enc [.t1], init_reaches_era0, ⟨[.t1], valid_era0, rfl⟩⟩ ?_
  intro cfg ⟨t, ht, hcfg⟩
  subst hcfg
  obtain ⟨t', ht', hstep⟩ := era_step ht
  exact ⟨default <{{D}} enc t', hstep, ⟨t', ht', rfl⟩⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  holdout_0446_nonhalt

end BusyBeaver.M_1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB
