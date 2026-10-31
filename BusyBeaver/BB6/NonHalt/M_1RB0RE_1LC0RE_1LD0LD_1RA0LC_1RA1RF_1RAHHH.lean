/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RE_1LC0RE_1LD0LD_1RA0LC_1RA1RF_1RA---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RE_1LC0RE_1LD0LD_1RA0LC_1RA1RF_1RA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1LC0RE_1LD0LD_1RA0LC_1RA1RF_1RAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RE_1LC0RE_1LD0LD_1RA0LC_1RA1RF_1RA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option linter.unnecessarySeqFocus false

set_option linter.unnecessarySeqFocus false

set_option linter.unnecessarySeqFocus false






set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000


set_option linter.unusedSimpArgs false

set_option maxHeartbeats 2000000

set_option maxRecDepth 200000


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
  `(tactic| exists 0 <;> rfl)

local macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])

local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))

local macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)


def A : Fin 6 := 0

def B : Fin 6 := 1

def C : Fin 6 := 2

def D : Fin 6 := 3

def E : Fin 6 := 4

def F : Fin 6 := 5




/-- `A` shifts rightward over `[1, 0]^k` in `2 * k` steps, writing `[1, 0]^k` to the left tape. -/
lemma shift_A_right_10_0036 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([1, 0] : List (Fin 2)) ^ k +> r)) [target_tm]⊢*
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{A}}> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
        [target_tm]⊢*
        ((l <+ [1, 0]) {{A}}> (([1, 0] : List (Fin 2)) ^ k +> r)) := by
      dsimp [ListBlank.append]; step; step; exact ⟨0, rfl⟩
    have h2 := ih (l <+ [1, 0]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2



/-- `E` shifts rightward over `[0, 1]^k` in `2 * k` steps, writing `[0, 1]^k` to the left tape. -/
lemma shift_E_right_01_0036 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([0, 1] : List (Fin 2)) ^ k +> r)) [target_tm]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{E}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ k +> r)))
        [target_tm]⊢*
        ((l <+ [0, 1]) {{E}}> (([0, 1] : List (Fin 2)) ^ k +> r)) := by
      dsimp [ListBlank.append]; step; step; exact ⟨0, rfl⟩
    have h2 := ih (l <+ [0, 1]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2



/-- `<{{D}}` shifts leftward over `[1, 0]^k` in `2 * k` steps, writing `[1, 0]^k` to the right tape. -/
lemma shift_D_left_10_0036 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) <{{D}} r) [target_tm]⊢*
    (l <{{D}} (([1, 0] : List (Fin 2)) ^ k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) <{{D}} r)
        [target_tm]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) <{{D}} ([1, 0] +> r)) := by
      dsimp [ListBlank.append]; step; step; exact ⟨0, rfl⟩
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2



lemma multiStep_step_isSome_0036 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
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

lemma inv_reaches_beyond_0036 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
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
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond_0036 M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome_0036 M (init []) cfg cfg' n m hn hnm


/-- `6`-step contextual leftward shift step of `<{{C}}` over `[1, 0]` with 1-cell right lookahead `[0]`. -/
lemma step_C_left_10_look0_0036 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 0]) <{{C}} ([0] +> r)) [target_tm]⊢⁺
    (l <{{C}} ([0] +> ([0, 1] +> r))) := by
  dsimp [ListBlank.append]; execute

/-- `6 * k`-step contextual leftward shift of `<{{C}}` over `[1, 0]^k` with 1-cell right lookahead `[0]`,
converting `[1, 0]^k` on the left stack into `[0, 1]^k` behind `[0]` on the right stack. -/
lemma shift_C_left_10_look0_0036 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) <{{C}} ([0] +> r)) [target_tm]⊢*
    (l <{{C}} ([0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 := stepPlus_stepStar (step_C_left_10_look0_0036 (l <+ ([1, 0] : List (Fin 2)) ^ k) r)
    have h2 := ih l (([0, 1] : List (Fin 2)) +> r)
    rw [pow_succ_append_right' ([0, 1] : List (Fin 2)) k r] at h2
    exact stepStar_trans h1 h2

/-- `8`-step leftward pass of `<{{C}}` over the `[0, 1, 1, 0]` divider, exposing the `[0]` lookahead cell. -/

-- ============================================================================
-- Section 16: 2-Mode Stack Configuration Model & 7 Macro Transitions (`holdout_0036`)
-- ============================================================================

inductive RItem
  | item00 (d c : Nat)
  | item01 (d c : Nat)

def encL : List Nat → ListBlank (Fin 2)
  | [] => default
  | c :: cs => ((encL cs) <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ c)

def encR : List RItem → ListBlank (Fin 2)
  | [] => [1, 0, 0, 1] +> default
  | .item00 d c :: rs => (([1, 0] : List (Fin 2)) ^ d) +> ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))
  | .item01 d c :: rs => (([1, 0] : List (Fin 2)) ^ d) +> ((([0, 1] : List (Fin 2)) ^ (c + 1)) +> encR rs)

def cfgC (cs : List Nat) (rs : List RItem) : Cfg (Fin 2) (Fin 6) :=
  (encL cs) <{{C}} ([0] +> encR rs)

def cfgD (cs : List Nat) (c : Nat) (rs : List RItem) : Cfg (Fin 2) (Fin 6) :=
  (encL cs) <{{D}} ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))

def cfgE (cs : List Nat) (c : Nat) (rs : List RItem) : Cfg (Fin 2) (Fin 6) :=
  ((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) {{E}}> encR rs

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

lemma cfgE_left_append_one (cs : List Nat) (c : Nat) :
    (((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) <+ [1]) = encL ((c + 1) :: cs) := by
  change (((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) <+ [1]) =
    ((encL cs) <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (c + 1))
  rw [listblank_append_append, listblank_append_append, list_one_append_01_pow]

lemma shift_E_01_succ (l : ListBlank (Fin 2)) (c : Nat) (r : ListBlank (Fin 2)) :
    ((l <+ [0, 1]) {{E}}> ((([0, 1] : List (Fin 2)) ^ c) +> r)) [target_tm]⊢*
    ((l <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) {{E}}> r) := by
  have h := shift_E_right_01_0036 c (l <+ [0, 1]) r
  rw [listblank_append_append, list_pow_append_one] at h
  exact h

theorem init_to_cfgD : (init []) [target_tm]⊢* cfgD [] 0 [] := by
  apply stepPlus_stepStar
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  dsimp [cfgD, encL, encR, ListBlank.append]
  step; step; step; step; step; step; step; step; step; step; step; step; step; step; exact ⟨0, rfl⟩

lemma step_D0_base (r : ListBlank (Fin 2)) :
    (default <{{D}} ([0, 0] +> r)) [target_tm]⊢⁺
    (((encL [1]) <+ [0, 1]) {{E}}> r) := by
  dsimp [encL, ListBlank.append]
  step; step; step; step; step; step; step; step; step; step; step; exact ⟨0, rfl⟩

theorem step_D0 (c : Nat) (rs : List RItem) :
    (cfgD [] c rs) [target_tm]⊢⁺ (cfgE [1] c rs) := by
  dsimp [cfgD, cfgE]
  exact stepPlus_stepStar_stepPlus
    (step_D0_base ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))
    (shift_E_01_succ (encL [1]) c (encR rs))

lemma step_D_one_to_C (l r : ListBlank (Fin 2)) :
    ((l <+ [1]) <{{D}} r) [target_tm]⊢⁺ (l <{{C}} ([0] +> r)) := by
  dsimp [ListBlank.append]; step; exact ⟨0, rfl⟩

lemma step_D_cons_to_C (d : Nat) (cs : List Nat) (c : Nat) (rs : List RItem) :
    (cfgD (d :: cs) c rs) [target_tm]⊢⁺ (cfgC cs (.item00 d c :: rs)) := by
  dsimp [cfgD, cfgC, encL, encR]
  exact stepStar_stepPlus_stepPlus
    (shift_D_left_10_0036 d ((encL cs) <+ [1]) ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs)))
    (step_D_one_to_C (encL cs) ((([1, 0] : List (Fin 2)) ^ d) +> ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))))

lemma step_C_one_to_D (l r : ListBlank (Fin 2)) :
    ((l <+ [1]) <{{C}} ([0] +> r)) [target_tm]⊢⁺ (l <{{D}} ([0, 0] +> r)) := by
  dsimp [ListBlank.append]; step; exact ⟨0, rfl⟩

lemma step_C_cons_to_D (c' : Nat) (cs : List Nat) (rs : List RItem) :
    (cfgC (c' :: cs) rs) [target_tm]⊢⁺ (cfgD cs c' rs) := by
  dsimp [cfgC, cfgD, encL]
  exact stepStar_stepPlus_stepPlus
    (shift_C_left_10_look0_0036 c' ((encL cs) <+ [1]) (encR rs))
    (step_C_one_to_D (encL cs) ((([0, 1] : List (Fin 2)) ^ c') +> encR rs))

theorem step_D2 (d c' : Nat) (cs : List Nat) (c : Nat) (rs : List RItem) :
    (cfgD (d :: c' :: cs) c rs) [target_tm]⊢⁺ (cfgD cs c' (.item00 d c :: rs)) :=
  stepPlus_trans (step_D_cons_to_C d (c' :: cs) c rs) (step_C_cons_to_D c' cs (.item00 d c :: rs))

lemma step_C_nil_to_A (r : ListBlank (Fin 2)) :
    (default <{{C}} ([0] +> r)) [target_tm]⊢⁺ (((default <+ [1]) <+ [1, 0]) {{A}}> r) := by
  dsimp [ListBlank.append]; step; step; step; step; exact ⟨0, rfl⟩

lemma step_A_00_to_D (l r : ListBlank (Fin 2)) :
    (l {{A}}> ([0, 0] +> r)) [target_tm]⊢⁺ (l <{{D}} ([0, 1] +> r)) := by
  dsimp [ListBlank.append]; step; step; step; exact ⟨0, rfl⟩

lemma step_D_1_bounce_to_A (r : ListBlank (Fin 2)) :
    ((default <+ [1]) <{{D}} r) [target_tm]⊢⁺ ((default <+ [1]) {{A}}> ([1, 0] +> r)) := by
  dsimp [ListBlank.append]; step; step; step; exact ⟨0, rfl⟩

lemma step_A_01_to_E (l r : ListBlank (Fin 2)) :
    (l {{A}}> ([0, 1] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1]) {{E}}> r) := by
  dsimp [ListBlank.append]; step; step; exact ⟨0, rfl⟩

lemma step_C_nil_item00_to_E (d c : Nat) (rs : List RItem) :
    (cfgC [] (.item00 d c :: rs)) [target_tm]⊢⁺ (cfgE [d + 2] c rs) := by
  dsimp [cfgC, cfgE, encL, encR]
  have h1 := step_C_nil_to_A ((([1, 0] : List (Fin 2)) ^ d) +> ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs)))
  have h2 := shift_A_right_10_0036 d ((default <+ [1]) <+ [1, 0]) ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))
  rw [pow_succ_append_right' ([1, 0] : List (Fin 2)) d (default <+ [1])] at h2
  have h3 := step_A_00_to_D ((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (d + 1))) ((([0, 1] : List (Fin 2)) ^ c) +> encR rs)
  have h4 := shift_D_left_10_0036 (d + 1) (default <+ [1]) ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))
  have h5 := step_D_1_bounce_to_A ((([1, 0] : List (Fin 2)) ^ (d + 1)) +> ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs)))
  rw [← pow_succ_append_right ([1, 0] : List (Fin 2)) (d + 1)] at h5
  have h6 := shift_A_right_10_0036 (d + 2) (default <+ [1]) ([0, 1] +> ((([0, 1] : List (Fin 2)) ^ c) +> encR rs))
  have h7 := step_A_01_to_E ((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (d + 2))) ((([0, 1] : List (Fin 2)) ^ c) +> encR rs)
  have h8 := shift_E_01_succ ((default <+ [1]) <+ (([1, 0] : List (Fin 2)) ^ (d + 2))) c (encR rs)
  exact stepPlus_stepStar_stepPlus
    (stepPlus_trans
      (stepPlus_stepStar_stepPlus
        (stepPlus_trans
          (stepPlus_trans
            (stepPlus_stepStar_stepPlus h1 h2)
            h3)
          (stepStar_stepPlus_stepPlus h4 h5))
        h6)
      h7)
    h8

theorem step_D1 (d c : Nat) (rs : List RItem) :
    (cfgD [d] c rs) [target_tm]⊢⁺ (cfgE [d + 2] c rs) :=
  stepPlus_trans (step_D_cons_to_C d [] c rs) (step_C_nil_item00_to_E d c rs)

lemma step_E0_base (l : ListBlank (Fin 2)) :
    (l {{E}}> ([1, 0, 0, 1] +> default)) [target_tm]⊢⁺
    ((l <+ [1]) <{{D}} ([0, 0] +> ([1, 0, 0, 1] +> default))) := by
  dsimp [ListBlank.append]
  step; step; step; step; step; step; step; step; step; step; step; step; exact ⟨0, rfl⟩

theorem step_E0 (cs : List Nat) (c : Nat) :
    (cfgE cs c []) [target_tm]⊢⁺ (cfgD ((c + 1) :: cs) 0 []) := by
  unfold cfgE cfgD encR
  simp only [pow_zero_list, listblank_append_nil]
  have h := step_E0_base ((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1)))
  rw [cfgE_left_append_one cs c] at h
  exact h

lemma step_E_10_to_A (l r : ListBlank (Fin 2)) :
    (l {{E}}> ([1, 0] +> r)) [target_tm]⊢⁺ (((l <+ [1]) <+ [1]) {{A}}> r) := by
  dsimp [ListBlank.append]; step; step; exact ⟨0, rfl⟩

lemma step_E_10_pow_succ_to_A (cs : List Nat) (c d : Nat) (r : ListBlank (Fin 2)) :
    (((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) {{E}}> ((([1, 0] : List (Fin 2)) ^ (d + 1)) +> r)) [target_tm]⊢⁺
    ((encL (d :: (c + 1) :: cs)) {{A}}> r) := by
  rw [pow_succ_append_right ([1, 0] : List (Fin 2)) d r]
  have h1 := step_E_10_to_A ((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) ((([1, 0] : List (Fin 2)) ^ d) +> r)
  rw [cfgE_left_append_one cs c] at h1
  have h2 := shift_A_right_10_0036 d ((encL ((c + 1) :: cs)) <+ [1]) r
  exact stepPlus_stepStar_stepPlus h1 h2

lemma step_E_item00_to_C (cs : List Nat) (c d c₂ : Nat) (rs : List RItem) :
    (cfgE cs c (.item00 (d + 1) c₂ :: rs)) [target_tm]⊢⁺ (cfgC ((c + 1) :: cs) (.item01 d c₂ :: rs)) := by
  dsimp [cfgE, cfgC, encR]
  have h1 := step_E_10_pow_succ_to_A cs c d ([0, 0] +> ((([0, 1] : List (Fin 2)) ^ c₂) +> encR rs))
  have h2 := step_A_00_to_D (encL (d :: (c + 1) :: cs)) ((([0, 1] : List (Fin 2)) ^ c₂) +> encR rs)
  rw [← pow_succ_append_right ([0, 1] : List (Fin 2)) c₂ (encR rs)] at h2
  dsimp [encL] at h2
  have h3 := shift_D_left_10_0036 d ((encL ((c + 1) :: cs)) <+ [1]) ((([0, 1] : List (Fin 2)) ^ (c₂ + 1)) +> encR rs)
  have h4 := step_D_one_to_C (encL ((c + 1) :: cs)) ((([1, 0] : List (Fin 2)) ^ d) +> ((([0, 1] : List (Fin 2)) ^ (c₂ + 1)) +> encR rs))
  exact stepPlus_trans
    (stepPlus_stepStar_stepPlus (stepPlus_trans h1 h2) h3)
    h4

theorem step_E1 (cs : List Nat) (c d c₂ : Nat) (rs : List RItem) :
    (cfgE cs c (.item00 (d + 1) c₂ :: rs)) [target_tm]⊢⁺ (cfgD cs (c + 1) (.item01 d c₂ :: rs)) :=
  stepPlus_trans (step_E_item00_to_C cs c d c₂ rs) (step_C_cons_to_D (c + 1) cs (.item01 d c₂ :: rs))

lemma step_E_01_one (l r : ListBlank (Fin 2)) :
    (l {{E}}> ([0, 1] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1]) {{E}}> r) := by
  dsimp [ListBlank.append]; step; step; exact ⟨0, rfl⟩

theorem step_E2 (cs : List Nat) (c c₂ : Nat) (rs : List RItem) :
    (cfgE cs c (.item01 0 c₂ :: rs)) [target_tm]⊢⁺ (cfgE cs (c + c₂ + 1) rs) := by
  dsimp [cfgE, encR]
  have h1 := step_E_01_one ((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) ((([0, 1] : List (Fin 2)) ^ c₂) +> encR rs)
  have h2 := shift_E_01_succ ((encL cs) <+ (([0, 1] : List (Fin 2)) ^ (c + 1))) c₂ (encR rs)
  rw [← pow_add_append_left (encL cs) ([0, 1] : List (Fin 2)) (c + 1) (c₂ + 1)] at h2
  have h_eq : (c + 1) + (c₂ + 1) = c + c₂ + 1 + 1 := by omega
  rw [h_eq] at h2
  exact stepPlus_stepStar_stepPlus h1 h2

theorem step_E3 (cs : List Nat) (c d c₂ : Nat) (rs : List RItem) :
    (cfgE cs c (.item01 (d + 1) c₂ :: rs)) [target_tm]⊢⁺ (cfgE (d :: (c + 1) :: cs) c₂ rs) := by
  dsimp [cfgE, encR]
  have h1 := step_E_10_pow_succ_to_A cs c d ((([0, 1] : List (Fin 2)) ^ (c₂ + 1)) +> encR rs)
  rw [pow_succ_append_right ([0, 1] : List (Fin 2)) c₂ (encR rs)] at h1
  have h2 := step_A_01_to_E (encL (d :: (c + 1) :: cs)) ((([0, 1] : List (Fin 2)) ^ c₂) +> encR rs)
  have h3 := shift_E_01_succ (encL (d :: (c + 1) :: cs)) c₂ (encR rs)
  exact stepPlus_stepStar_stepPlus (stepPlus_trans h1 h2) h3

-- ============================================================================
-- Section 17: Step-0 Closed Invariant and Non-Halting Proof
-- ============================================================================

abbrev condC (rem re rc c : Nat) : Prop :=
  c + rem > 2 * re ∨ (re = rc ∧ re > 0)



def remSweeps : List RItem → Nat
  | [] => 0
  | .item00 _ _ :: rs => 2 * remSweeps rs + 1
  | .item01 _ _ :: rs => 2 * remSweeps rs

def remE : List RItem → Nat
  | [] => 0
  | .item00 d _ :: rs => if d > 2 * remSweeps rs + 1 then 2 * remE rs + 1 else remE rs
  | .item01 d _ :: rs => if d > 2 * remSweeps rs then 2 * remE rs + 1 else remE rs

def remC : List RItem → Nat
  | [] => 0
  | .item00 d c :: rs =>
    if d > 2 * remSweeps rs + 1 ∧ condC (remSweeps rs) (remE rs) (remC rs) c then 2 * remC rs + 1 else remC rs
  | .item01 d c :: rs =>
    if d > 2 * remSweeps rs ∧ condC (remSweeps rs) (remE rs) (remC rs) c then 2 * remC rs + 1 else remC rs

def lastD : List RItem → Nat
  | [] => 0
  | .item00 d _ :: rs => if d > 2 * remSweeps rs + 1 then max (d - 2 - 2 * remSweeps rs) (2 * remE rs + 1) else lastD rs
  | .item01 d _ :: rs => if d > 2 * remSweeps rs then max (d - 1 - 2 * remSweeps rs) (2 * remE rs + 1) else lastD rs

def remCC : List RItem → Nat
  | [] => 0
  | .item00 d c :: rs =>
    if d > 2 * remSweeps rs + 1 ∧ condC (remSweeps rs) (remE rs) (remC rs) c ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs)
    then 2 * remCC rs + 1 else remCC rs
  | .item01 d c :: rs =>
    if d > 2 * remSweeps rs ∧ condC (remSweeps rs) (remE rs) (remC rs) c ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs)
    then 2 * remCC rs + 1 else remCC rs

lemma rem_bounds (rs : List RItem) :
    (remE rs = 0 ∧ remC rs = 0 ∧ remCC rs = 0 ∧ lastD rs = 0) ∨
    (remE rs = remC rs ∧ 2 * remCC rs + 1 ≤ remE rs ∧ lastD rs ≥ remE rs ∧
     ∃ m : Nat, remE rs = 2 * remCC rs + 1 + m * (2 * remCC rs + 2)) ∨
    (2 * remC rs + 1 ≤ remE rs ∧ remCC rs = remC rs ∧ lastD rs ≥ remE rs ∧
     ∃ m : Nat, remE rs = 2 * remC rs + 1 + m * (2 * remC rs + 2)) := by
  induction rs with
  | nil => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | cons item rs ih =>
    rcases ih with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, h2, h3, m, hm⟩
    · rcases item with ⟨d, c⟩ | ⟨d, c⟩ <;>
      dsimp [remE, remC, remCC, lastD, condC] <;>
      split_ifs
      all_goals try (exact Or.inl ⟨by omega, by omega, by omega, by omega⟩)
      all_goals try (exact Or.inr (Or.inl ⟨by omega, by omega, by omega, 0, by omega⟩))
      all_goals try (exact Or.inr (Or.inr ⟨by omega, by omega, by omega, 0, by omega⟩))
    · have h_mul1 : m * (2 * (2 * remCC rs + 1) + 2) = 2 * (m * (2 * remCC rs + 2)) := by ring
      have h_mul2 : (2 * m + 1) * (2 * remCC rs + 2) = 2 * (m * (2 * remCC rs + 2)) + (2 * remCC rs + 2) := by ring
      rcases item with ⟨d, c⟩ | ⟨d, c⟩ <;>
      dsimp [remE, remC, remCC, lastD, condC] <;>
      split_ifs
      all_goals try (exact Or.inr (Or.inl ⟨by omega, by omega, by omega, m, by omega⟩))
      all_goals try (exact Or.inr (Or.inl ⟨by omega, by omega, by omega, 2 * m + 1, by omega⟩))
    · have h_mul1 : m * (2 * (2 * remC rs + 1) + 2) = 2 * (m * (2 * remC rs + 2)) := by ring
      have h_mul2 : (2 * m + 1) * (2 * remC rs + 2) = 2 * (m * (2 * remC rs + 2)) + (2 * remC rs + 2) := by ring
      rcases item with ⟨d, c⟩ | ⟨d, c⟩ <;>
      dsimp [remE, remC, remCC, lastD, condC] <;>
      split_ifs
      all_goals try (exact Or.inr (Or.inr ⟨by omega, by omega, by omega, m, by omega⟩))
      all_goals try (exact Or.inr (Or.inr ⟨by omega, by omega, by omega, 2 * m + 1, by omega⟩))

lemma mul_bound (m x : Nat) : m * x = 0 ∨ m * x ≥ x := by
  rcases m with _ | m'
  · left; ring
  · right; have : (m' + 1) * x = m' * x + x := by ring
    omega

def validC (re rc x : Nat) : Prop :=
  if 2 * rc + 1 ≤ re then
    ∃ k : Nat, x = 2 * re + 1 + k * (2 * rc + 2)
  else
    (re = 0 ∧ x = 1) ∨ x = 4 * re + 3 ∨ (re = 0 ∧ x = 4) ∨ x ≥ 6 * re + 5

def validD (rem re rc c d : Nat) : Prop :=
  if 2 * rc + 1 ≤ re then
    d = 2 * rem + 2 * re + 3 ∨ d ≥ 2 * rem + 4 * re + 5
  else
    d = 2 * rem + 1 ∨
    (rem = 0 ∧ re = 0 ∧ c = 0 ∧ d ≥ 3) ∨
    (condC rem re rc c ∧ ∃ k : Nat, d = 2 * rem + 2 * re + 3 + k * (2 * re + 2))

def above00 (rem re rc x : Nat) : Prop :=
  (re = 0 ∧ x > 0) ∨ x + 2 * rem > 2 * re + 2 * rc + 1

def above01 (rem re rc x : Nat) : Prop :=
  (re = 0 ∧ x > 1) ∨ x + 2 * rem > 2 * re + 2 * rc + 2

def validBase (re rc x : Nat) : Prop :=
  if 2 * rc + 1 ≤ re then
    x + 1 = 2 * re
  else
    ∃ k : Nat, x = 4 * re + 1 + k * (2 * re + 2)

def GoodCSD (rem re rc c : Nat) : List Nat → Prop
  | [] => rem ≥ re ∧ (rem > 0 ∨ c = 0) ∧ (re = 0 ∨ c + rem > 2 * re) ∧ (rem = 0 ∨ validBase re rc (2 * rem - 1))
  | [d] => (re = 0 ∨ c + rem > 2 * re) ∧ validBase re rc (d + 2 * rem)
  | d :: cp :: cs =>
    let rem_n := 2 * rem + 1
    let re_n := if d > 2 * rem + 1 then 2 * re + 1 else re
    let rc_n := if d > 2 * rem + 1 ∧ condC rem re rc c then 2 * rc + 1 else rc
    validD rem re rc c d ∧
    (d > 2 * rem + 1 ∨ above00 rem re rc cp) ∧
    validC re_n rc_n (cp + rem_n + 1) ∧
    GoodCSD rem_n re_n rc_n cp cs

def topAbove (c : Nat) : List RItem → Prop
  | [] => True
  | .item00 d _ :: rs => d > 2 * remSweeps rs + 1 ∨ above00 (remSweeps rs) (remE rs) (remC rs) c
  | .item01 d _ :: rs => d > 2 * remSweeps rs ∨ above01 (remSweeps rs) (remE rs) (remC rs) c

def P01 (d c : Nat) (rs : List RItem) : Prop :=
  validD (remSweeps rs) (remE rs) (remC rs) c (d + 1) ∧
  validC (remE rs) (remC rs) (c + remSweeps rs + 1) ∧
  topAbove c rs

def GoodRS : List RItem → Prop
  | [] => True
  | .item00 d c :: rs => d ≥ 1 ∧ P01 (d - 1) c rs ∧ GoodRS rs
  | .item01 d c :: rs => P01 d c rs ∧ GoodRS rs

def InvD (cs : List Nat) (c : Nat) (rs : List RItem) : Prop :=
  GoodRS rs ∧
  topAbove c rs ∧
  validC (remE rs) (remC rs) (c + remSweeps rs + 1) ∧
  GoodCSD (remSweeps rs) (remE rs) (remC rs) c cs

def InvE (cs : List Nat) (c : Nat) (rs : List RItem) : Prop :=
  GoodRS rs ∧
  topAbove c rs ∧
  cs ≠ [] ∧
  if remSweeps rs = 0 then
    GoodCSD (remE rs) (remC rs) (remCC rs) (lastD rs) ((c + 1) :: cs)
  else
    validC (remE rs) (remC rs) ((c + 1) + (remSweeps rs - 1) + 1) ∧
    GoodCSD (remSweeps rs - 1) (remE rs) (remC rs) (c + 1) cs

lemma validC_to_validD (rs : List RItem) (x : Nat) (h : validC (remE rs) (remC rs) x) :
    validD (remE rs) (remC rs) (remCC rs) (lastD rs) x := by
  have hb := rem_bounds rs
  dsimp [validC, validD, condC] at h ⊢
  rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, h2, h3, m, hm⟩
  · split_ifs at h ⊢ <;> omega
  · split_ifs at h ⊢ <;> omega
  · rw [if_pos h1] at h
    have h_not : ¬(2 * remCC rs + 1 ≤ remC rs) := by omega
    rw [if_neg h_not]
    rcases h with ⟨k, hk⟩
    rcases k with _ | k'
    · left; omega
    · right; right
      have h_mul : (k' + 1) * (2 * remC rs + 2) = k' * (2 * remC rs + 2) + (2 * remC rs + 2) := by ring
      refine ⟨by omega, k', by omega⟩

lemma validBase_next (rs : List RItem) (c d' : Nat)
    (h_vc : validC (remE rs) (remC rs) (c + 1))
    (h_c : remE rs = 0 ∨ c > 2 * remE rs)
    (h_d' : (remE rs = 0 ∧ c = 0 ∧ d' = 1) ∨ (d' ≥ 4 * remC rs + 3 ∧ d' ≥ 2 * remE rs + 1)) :
    let rem_n := 2 * remE rs + 1
    let re_n := if c + 1 > 2 * remE rs + 1 then 2 * remC rs + 1 else remC rs
    let rc_n := if c + 1 > 2 * remE rs + 1 ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs) then 2 * remCC rs + 1 else remCC rs
    rem_n ≥ re_n ∧ (rem_n > 0 ∨ d' = 0) ∧ (re_n = 0 ∨ d' + rem_n > 2 * re_n) ∧ (rem_n = 0 ∨ validBase re_n rc_n (2 * rem_n - 1)) := by
  have hb := rem_bounds rs
  dsimp [validBase, validC, condC] at h_vc h_c ⊢
  rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, h2, h3, m, hm⟩
  · split_ifs
    all_goals try omega
    all_goals try (exact ⟨by omega, by omega, by omega, Or.inr ⟨0, by omega⟩⟩)
  · have h_not : ¬(2 * remC rs + 1 ≤ remE rs) := by omega
    rw [if_neg h_not] at h_vc
    split_ifs <;> omega
  · rw [if_pos h1] at h_vc
    have h_mul : (2 * m) * (2 * (2 * remC rs + 1) + 2) = 4 * (m * (2 * remC rs + 2)) := by ring
    split_ifs
    all_goals try omega
    all_goals (exact ⟨by omega, by omega, by omega, Or.inr ⟨2 * m, by omega⟩⟩)

lemma validBase_to_validC (rs : List RItem) (c d : Nat)
    (h_vc : validC (remE rs) (remC rs) (c + 1))
    (h_c : remE rs = 0 ∨ c > 2 * remE rs)
    (h : validBase (remE rs) (remC rs) d) :
    let rem_n := 2 * remE rs + 1
    let re_n := if c + 1 > 2 * remE rs + 1 then 2 * remC rs + 1 else remC rs
    let rc_n := if c + 1 > 2 * remE rs + 1 ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs) then 2 * remCC rs + 1 else remCC rs
    validC re_n rc_n ((d + 2) + rem_n + 1) ∧
    ((remE rs = 0 ∧ c = 0 ∧ d + 2 = 1) ∨ (d + 2 ≥ 4 * remC rs + 3 ∧ d + 2 ≥ 2 * remE rs + 1)) := by
  have hb := rem_bounds rs
  dsimp [validBase, validC, condC] at h_vc h_c h ⊢
  rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, h2, h3, m, hm⟩
  · have h_not : ¬(2 * remC rs + 1 ≤ remE rs) := by omega
    rw [if_neg h_not] at h_vc h
    rcases h with ⟨k, hk⟩
    rw [h1] at hk
    rw [h1, h2, h3]
    split_ifs
    all_goals try omega
    all_goals try (exact ⟨⟨k + 1, by omega⟩, by omega⟩)
  · have h_not : ¬(2 * remC rs + 1 ≤ remE rs) := by omega
    rw [if_neg h_not] at h_vc h
    rcases h with ⟨k, hk⟩
    have h_mul1 : ((k + 1) * (m + 1)) * (2 * (2 * remCC rs + 1) + 2) =
        k * (2 * (2 * remCC rs + 1 + m * (2 * remCC rs + 2)) + 2) + (2 * (2 * remCC rs + 1 + m * (2 * remCC rs + 2)) + 2) := by ring
    have h_mul2 : ((k + 1) * (2 * m + 2)) * (2 * remCC rs + 2) =
        k * (2 * (2 * remCC rs + 1 + m * (2 * remCC rs + 2)) + 2) + (2 * (2 * remCC rs + 1 + m * (2 * remCC rs + 2)) + 2) := by ring
    rw [← hm] at h_mul1 h_mul2
    have hk_b := mul_bound k (2 * remE rs + 2)
    split_ifs
    all_goals try omega
    all_goals try (exact ⟨⟨(k + 1) * (m + 1), by omega⟩, by omega⟩)
    all_goals try (exact ⟨⟨(k + 1) * (2 * m + 2), by omega⟩, by omega⟩)
  · rw [if_pos h1] at h_vc h
    rcases h_vc with ⟨kc, hkc⟩
    have hm_b := mul_bound m (2 * remC rs + 2)
    have hkc_b := mul_bound kc (2 * remC rs + 2)
    split_ifs <;> refine ⟨by omega, by omega⟩

lemma validD_zero_to_step (rs : List RItem) (c₂ d : Nat)
    (h_vd : validD 0 (remE rs) (remC rs) c₂ (d + 2))
    (h_vc2 : validC (remE rs) (remC rs) (c₂ + 1)) :
    let rem_n := 2 * remE rs + 1
    let re_n := if c₂ + 1 > 2 * remE rs + 1 then 2 * remC rs + 1 else remC rs
    let rc_n := if c₂ + 1 > 2 * remE rs + 1 ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs) then 2 * remCC rs + 1 else remCC rs
    above00 (remE rs) (remC rs) (remCC rs) d ∧
    validC re_n rc_n (d + rem_n + 1) := by
  have hb := rem_bounds rs
  dsimp [validD, validC, above00, condC] at h_vd h_vc2 ⊢
  rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, h2, h3, m, hm⟩
  · have h_not : ¬(2 * remC rs + 1 ≤ remE rs) := by omega
    rw [if_neg h_not] at h_vd h_vc2
    rcases h_vd with h_d1 | ⟨_, _, h_c0, h_ge3⟩ | ⟨h_cond, k, hk⟩
    · omega
    · split_ifs <;> refine ⟨by omega, by omega⟩
    · rw [h1] at hk
      rw [h1, h2, h3]
      split_ifs
      all_goals try (exact ⟨by omega, k, by omega⟩)
      all_goals (refine ⟨by omega, by omega⟩)
  · have h_not : ¬(2 * remC rs + 1 ≤ remE rs) := by omega
    rw [if_neg h_not] at h_vd h_vc2
    rcases h_vd with h_d1 | ⟨_, h_re0, _, _⟩ | ⟨h_cond, k, hk⟩
    · omega
    · omega
    · have h_mul1 : (k * (m + 1)) * (2 * (2 * remCC rs + 1) + 2) =
          k * (2 * (2 * remCC rs + 1 + m * (2 * remCC rs + 2)) + 2) := by ring
      have h_mul2 : (k * (2 * m + 2)) * (2 * remCC rs + 2) =
          k * (2 * (2 * remCC rs + 1 + m * (2 * remCC rs + 2)) + 2) := by ring
      rw [← hm] at h_mul1 h_mul2
      have hk_b := mul_bound k (2 * remE rs + 2)
      split_ifs
      all_goals try omega
      all_goals try (exact ⟨by omega, k * (m + 1), by omega⟩)
      all_goals try (exact ⟨by omega, k * (2 * m + 2), by omega⟩)
  · rw [if_pos h1] at h_vd h_vc2
    rcases h_vc2 with ⟨kc, hkc⟩
    have hm_b := mul_bound m (2 * remC rs + 2)
    have hkc_b := mul_bound kc (2 * remC rs + 2)
    split_ifs <;> refine ⟨by omega, by omega⟩

lemma topAbove_mono {c₁ c₂ : Nat} (rs : List RItem) (h_le : c₁ ≤ c₂) (h : topAbove c₁ rs) :
    topAbove c₂ rs := by
  cases rs with
  | nil => trivial
  | cons item rs' =>
    cases item <;> {
      dsimp [topAbove, above00, above01] at h ⊢
      omega
    }

theorem inv_init : InvD [] 0 [] := by
  dsimp [InvD, GoodRS, topAbove, validC, GoodCSD, remSweeps, remE, remC, condC]
  refine ⟨trivial, trivial, by omega, by omega⟩

theorem invD_nil (c : Nat) (rs : List RItem) (h : InvD [] c rs) : InvE [1] c rs := by
  rcases h with ⟨h_rs, h_top, h_vc, h_csd⟩
  have hb := rem_bounds rs
  refine ⟨h_rs, h_top, by simp, ?_⟩
  split_ifs with h_rem0
  · rw [h_rem0] at h_vc h_csd
    have h_vd := validC_to_validD rs (c + 1) h_vc
    have h_re0 : remE rs = 0 ∧ c = 0 := by dsimp [GoodCSD] at h_csd; omega
    have h_next := validBase_next rs c 1 h_vc (Or.inl h_re0.1) (Or.inl ⟨h_re0.1, h_re0.2, rfl⟩)
    dsimp [GoodCSD] at h_csd ⊢
    refine ⟨h_vd, ?_, ?_, h_next⟩
    · dsimp [above00]; omega
    · have h_rc0 : remC rs = 0 ∧ remCC rs = 0 ∧ lastD rs = 0 := by
        rcases hb with ⟨_, h2, h3, h4⟩ | ⟨h1, h2, _⟩ | ⟨h1, _, _, _⟩ <;> omega
      rw [h_re0.1, h_re0.2, h_rc0.1, h_rc0.2.1, h_rc0.2.2]
      dsimp [validC, condC]
      omega
  · dsimp [GoodCSD] at h_csd ⊢
    rcases h_csd with ⟨_, _, h_cond, h_base⟩
    rcases h_base with h_z | h_vb
    · omega
    · refine ⟨?_, ?_, ?_⟩
      · have h_eq : (c + 1) + (remSweeps rs - 1) + 1 = c + remSweeps rs + 1 := by omega
        rw [h_eq]; exact h_vc
      · omega
      · have h_eq : 1 + 2 * (remSweeps rs - 1) = 2 * remSweeps rs - 1 := by omega
        rw [h_eq]; exact h_vb

theorem invD_single (d c : Nat) (rs : List RItem) (h : InvD [d] c rs) : InvE [d + 2] c rs := by
  rcases h with ⟨h_rs, h_top, h_vc, h_csd⟩
  have hb := rem_bounds rs
  refine ⟨h_rs, h_top, by simp, ?_⟩
  split_ifs with h_rem0
  · rw [h_rem0] at h_vc h_csd
    rcases h_csd with ⟨h_c_cond, h_vb⟩
    have h_c_gt : remE rs = 0 ∨ c > 2 * remE rs := by omega
    have h_vd := validC_to_validD rs (c + 1) h_vc
    have ⟨h_vc_next, h_d2_ge⟩ := validBase_to_validC rs c d h_vc h_c_gt h_vb
    have h_next := validBase_next rs c (d + 2) h_vc h_c_gt h_d2_ge
    dsimp [GoodCSD]
    refine ⟨h_vd, ?_, h_vc_next, h_next⟩
    dsimp [above00]
    rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, h2, h3, m, hm⟩ <;> omega
  · dsimp [GoodCSD] at h_csd ⊢
    rcases h_csd with ⟨h_c_cond, h_vb⟩
    refine ⟨?_, ?_, ?_⟩
    · have h_eq : (c + 1) + (remSweeps rs - 1) + 1 = c + remSweeps rs + 1 := by omega
      rw [h_eq]; exact h_vc
    · omega
    · have h_eq : (d + 2) + 2 * (remSweeps rs - 1) = d + 2 * remSweeps rs := by omega
      rw [h_eq]; exact h_vb

theorem invD_cons2 (d cp : Nat) (cs : List Nat) (c : Nat) (rs : List RItem)
    (h : InvD (d :: cp :: cs) c rs) : InvD cs cp (.item00 d c :: rs) := by
  rcases h with ⟨h_rs, h_top, h_vc, h_d_val, h_cp_above, h_cp_val, h_csd⟩
  have hd_ge1 : d ≥ 1 := by
    dsimp [validD] at h_d_val
    split_ifs at h_d_val
    · omega
    · rcases h_d_val with h1 | h2 | ⟨_, k, hk⟩ <;> omega
  have hd_eq : d - 1 + 1 = d := by omega
  refine ⟨⟨hd_ge1, ⟨?_, h_vc, h_top⟩, h_rs⟩, h_cp_above, h_cp_val, h_csd⟩
  rw [hd_eq]; exact h_d_val

theorem invE_nil (cs : List Nat) (c : Nat) (h : InvE cs c []) : InvD ((c + 1) :: cs) 0 [] := by
  rcases h with ⟨_, _, _, h_e⟩
  dsimp [remSweeps, remE, remC, remCC, lastD] at h_e
  refine ⟨trivial, trivial, ?_, h_e⟩
  dsimp [validC, remE, remC, remSweeps]; omega

theorem invE_item00 (cs : List Nat) (c d c₂ : Nat) (rs : List RItem)
    (h : InvE cs c (.item00 d c₂ :: rs)) :
    ∃ d', d = d' + 1 ∧ InvD cs (c + 1) (.item01 d' c₂ :: rs) := by
  rcases h with ⟨⟨hd_ge1, hp, hrs⟩, h_top, h_ne, h_e⟩
  refine ⟨d - 1, by omega, ?_⟩
  have h_rem_ne : remSweeps (.item00 d c₂ :: rs) ≠ 0 := by dsimp [remSweeps]; omega
  rw [if_neg h_rem_ne] at h_e
  rcases h_e with ⟨h_vc, h_csd⟩
  have h_rem_eq : remSweeps (.item00 d c₂ :: rs) - 1 = remSweeps (.item01 (d - 1) c₂ :: rs) := by
    dsimp [remSweeps]
  have h_re_eq : remE (.item00 d c₂ :: rs) = remE (.item01 (d - 1) c₂ :: rs) := by
    dsimp [remE]; split_ifs <;> omega
  have h_rc_eq : remC (.item00 d c₂ :: rs) = remC (.item01 (d - 1) c₂ :: rs) := by
    dsimp [remC, condC]; split_ifs <;> omega
  rw [h_rem_eq, h_re_eq, h_rc_eq] at h_vc h_csd
  refine ⟨⟨hp, hrs⟩, ?_, h_vc, h_csd⟩
  dsimp [topAbove, above00, above01] at h_top ⊢
  omega

theorem invE_item01_zero (cs : List Nat) (c c₂ : Nat) (rs : List RItem)
    (h : InvE cs c (.item01 0 c₂ :: rs)) : InvE cs (c + c₂ + 1) rs := by
  rcases h with ⟨⟨⟨h_vd0, h_vc2, h_top2⟩, hrs⟩, h_top, h_ne, h_e⟩
  have hb := rem_bounds rs
  have h_rem0_and_not : remSweeps rs = 0 ∧ ¬(2 * remC rs + 1 ≤ remE rs) := by
    dsimp [validD] at h_vd0
    split_ifs at h_vd0 with h_gt
    · omega
    · rcases h_vd0 with h1 | h2 | ⟨_, k, hk⟩ <;> omega
  have h_rem0 : remSweeps rs = 0 := h_rem0_and_not.1
  have h_not_gt : ¬(2 * remC rs + 1 ≤ remE rs) := h_rem0_and_not.2
  have h_rem0_cons : remSweeps (.item01 0 c₂ :: rs) = 0 := by dsimp [remSweeps]; omega
  rw [if_pos h_rem0_cons] at h_e
  have h_re_eq : remE (.item01 0 c₂ :: rs) = remE rs := by rw [remE, h_rem0]; split_ifs <;> omega
  have h_rc_eq : remC (.item01 0 c₂ :: rs) = remC rs := by rw [remC, h_rem0]; split_ifs <;> omega
  have h_rcc_eq : remCC (.item01 0 c₂ :: rs) = remCC rs := by rw [remCC, h_rem0]; split_ifs <;> omega
  have h_ld_eq : lastD (.item01 0 c₂ :: rs) = lastD rs := by rw [lastD, h_rem0]; split_ifs <;> omega
  rw [h_re_eq, h_rc_eq, h_rcc_eq, h_ld_eq] at h_e
  have h_c_gt : c + 1 > 2 * remE rs + 1 := by
    dsimp [topAbove, above01] at h_top; omega
  have h_cc2_gt : c + c₂ + 2 > 2 * remE rs + 1 := by omega
  refine ⟨hrs, topAbove_mono rs (by omega) h_top2, h_ne, ?_⟩
  rw [if_pos h_rem0]
  rcases List.exists_cons_of_ne_nil h_ne with ⟨cp, cs', rfl⟩
  dsimp [GoodCSD] at h_e ⊢
  rcases h_e with ⟨h_vd_c, h_above_cp, h_vc_cp, h_csd_tail⟩
  have h_re_n_eq : (if c + c₂ + 1 + 1 > 2 * remE rs + 1 then 2 * remC rs + 1 else remC rs) =
      (if c + 1 > 2 * remE rs + 1 then 2 * remC rs + 1 else remC rs) := by
    split_ifs <;> omega
  have h_rc_n_eq : (if c + c₂ + 1 + 1 > 2 * remE rs + 1 ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs) then 2 * remCC rs + 1 else remCC rs) =
      (if c + 1 > 2 * remE rs + 1 ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs) then 2 * remCC rs + 1 else remCC rs) := by
    dsimp [condC]; split_ifs <;> omega
  rw [h_re_n_eq, h_rc_n_eq]
  refine ⟨?_, Or.inl h_cc2_gt, h_vc_cp, h_csd_tail⟩
  dsimp [topAbove, above01] at h_top
  dsimp [validD, validC, condC] at h_vd_c h_vc2 ⊢
  rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, m, hm⟩ | ⟨h1, _, _, _⟩
  · split_ifs at h_vd_c h_vc2 ⊢ <;> omega
  · split_ifs at h_vd_c h_vc2 ⊢ <;> omega
  · exact False.elim (h_not_gt h1)

theorem invE_item01_succ (cs : List Nat) (c d c₂ : Nat) (rs : List RItem)
    (h : InvE cs c (.item01 (d + 1) c₂ :: rs)) : InvE (d :: (c + 1) :: cs) c₂ rs := by
  rcases h with ⟨⟨⟨h_vd, h_vc2, h_top2⟩, hrs⟩, h_top, h_ne, h_e⟩
  have hb := rem_bounds rs
  refine ⟨hrs, h_top2, by simp, ?_⟩
  split_ifs with h_rem0
  · have h_rem0_cons : remSweeps (.item01 (d + 1) c₂ :: rs) = 0 := by dsimp [remSweeps]; omega
    rw [if_pos h_rem0_cons] at h_e
    rw [h_rem0] at h_vd h_vc2
    have h_vd_c2 := validC_to_validD rs (c₂ + 1) h_vc2
    have h_step := validD_zero_to_step rs c₂ d h_vd h_vc2
    have h_d_ge : d ≥ 2 * remE rs + 1 := by
      dsimp [validD] at h_vd
      split_ifs at h_vd
      · omega
      · rcases h_vd with h1 | h2 | ⟨_, k, hk⟩ <;> omega
    have h_c2_cond : condC 0 (remE rs) (remC rs) c₂ ↔ c₂ + 1 > 2 * remE rs + 1 := by
      dsimp [condC, validC] at h_vc2 ⊢
      split_ifs at h_vc2 <;> omega
    have h_re_eq : remE (.item01 (d + 1) c₂ :: rs) = 2 * remE rs + 1 := by
      rw [remE, h_rem0]; split_ifs <;> omega
    have h_rc_eq : remC (.item01 (d + 1) c₂ :: rs) =
        (if c₂ + 1 > 2 * remE rs + 1 then 2 * remC rs + 1 else remC rs) := by
      rw [remC, h_rem0]; dsimp [condC] at h_c2_cond ⊢; split_ifs <;> omega
    have h_rcc_eq : remCC (.item01 (d + 1) c₂ :: rs) =
        (if c₂ + 1 > 2 * remE rs + 1 ∧ condC (remE rs) (remC rs) (remCC rs) (lastD rs) then 2 * remCC rs + 1 else remCC rs) := by
      rw [remCC, h_rem0]; dsimp [condC] at h_c2_cond ⊢; split_ifs <;> omega
    have h_ld_eq : lastD (.item01 (d + 1) c₂ :: rs) = d := by
      rw [lastD, h_rem0]; split_ifs <;> omega
    rw [h_re_eq, h_rc_eq, h_rcc_eq, h_ld_eq] at h_e
    dsimp [GoodCSD]
    exact ⟨h_vd_c2, Or.inr h_step.1, h_step.2, h_e⟩
  · have h_rem_ne_cons : remSweeps (.item01 (d + 1) c₂ :: rs) ≠ 0 := by dsimp [remSweeps]; omega
    rw [if_neg h_rem_ne_cons] at h_e
    rcases h_e with ⟨h_vc, h_csd⟩
    have h_rem_eq : remSweeps (.item01 (d + 1) c₂ :: rs) - 1 = 2 * (remSweeps rs - 1) + 1 := by
      dsimp [remSweeps]; omega
    have h_re_eq : remE (.item01 (d + 1) c₂ :: rs) =
        (if d > 2 * (remSweeps rs - 1) + 1 then 2 * remE rs + 1 else remE rs) := by
      dsimp [remE]; split_ifs <;> omega
    have h_rc_eq : remC (.item01 (d + 1) c₂ :: rs) =
        (if d > 2 * (remSweeps rs - 1) + 1 ∧ condC (remSweeps rs - 1) (remE rs) (remC rs) (c₂ + 1) then 2 * remC rs + 1 else remC rs) := by
      dsimp [remC, condC]; split_ifs <;> omega
    rw [h_rem_eq, h_re_eq, h_rc_eq] at h_vc h_csd
    refine ⟨?_, ?_⟩
    · have h_eq : (c₂ + 1) + (remSweeps rs - 1) + 1 = c₂ + remSweeps rs + 1 := by omega
      rw [h_eq]; exact h_vc2
    · dsimp [GoodCSD]
      refine ⟨?_, ?_, h_vc, h_csd⟩
      · dsimp [validD, condC] at h_vd ⊢
        split_ifs at h_vd ⊢
        · omega
        · rcases h_vd with h1 | h2 | ⟨h_cond, k, hk⟩
          · left; omega
          · omega
          · right; right; refine ⟨by omega, k, by omega⟩
      · dsimp [topAbove, above01, above00] at h_top ⊢; omega

def Inv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  (∃ cs c rs, cfg = cfgD cs c rs ∧ InvD cs c rs) ∨
  (∃ cs c rs, cfg = cfgE cs c rs ∧ InvE cs c rs)

theorem inv_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : Inv cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧ Inv cfg' := by
  rcases h with ⟨cs, c, rs, rfl, hD⟩ | ⟨cs, c, rs, rfl, hE⟩
  · rcases cs with _ | ⟨d, _ | ⟨cp, cs⟩⟩
    · exact ⟨cfgE [1] c rs, step_D0 c rs, Or.inr ⟨[1], c, rs, rfl, invD_nil c rs hD⟩⟩
    · exact ⟨cfgE [d + 2] c rs, step_D1 d c rs, Or.inr ⟨[d + 2], c, rs, rfl, invD_single d c rs hD⟩⟩
    · exact ⟨cfgD cs cp (.item00 d c :: rs), step_D2 d cp cs c rs,
        Or.inl ⟨cs, cp, .item00 d c :: rs, rfl, invD_cons2 d cp cs c rs hD⟩⟩
  · rcases rs with _ | ⟨⟨d, c₂⟩ | ⟨_ | d, c₂⟩, rs⟩
    · exact ⟨cfgD ((c + 1) :: cs) 0 [], step_E0 cs c, Or.inl ⟨(c + 1) :: cs, 0, [], rfl, invE_nil cs c hE⟩⟩
    · obtain ⟨d', rfl, hD'⟩ := invE_item00 cs c d c₂ rs hE
      exact ⟨cfgD cs (c + 1) (.item01 d' c₂ :: rs), step_E1 cs c d' c₂ rs,
        Or.inl ⟨cs, c + 1, .item01 d' c₂ :: rs, rfl, hD'⟩⟩
    · exact ⟨cfgE cs (c + c₂ + 1) rs, step_E2 cs c c₂ rs,
        Or.inr ⟨cs, c + c₂ + 1, rs, rfl, invE_item01_zero cs c c₂ rs hE⟩⟩
    · exact ⟨cfgE (d :: (c + 1) :: cs) c₂ rs, step_E3 cs c d c₂ rs,
        Or.inr ⟨d :: (c + 1) :: cs, c₂, rs, rfl, invE_item01_succ cs c d c₂ rs hE⟩⟩







-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  apply closed_inv_does_not_halt target_tm Inv
  · exact ⟨cfgD [] 0 [], init_to_cfgD, Or.inl ⟨[], 0, [], rfl, inv_init⟩⟩
  · exact inv_closed

end BusyBeaver.M_1RB0RE_1LC0RE_1LD0LD_1RA0LC_1RA1RF_1RAHHH
