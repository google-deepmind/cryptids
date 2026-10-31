/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace State270System
open BusyBeaver.Simp BusyBeaver.Counter
abbrev holdout_270_tm : Machine (Fin 2) (Fin 6) := target_tm

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

omit [Inhabited Γ] in
lemma list_pow_add (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, ← add_assoc, add_comm 1 m, list_pow_add]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [← List.append_assoc, ← List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa

omit [Inhabited Γ] in
lemma list_pow_add_comm (l : List Γ) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [← list_pow_add, add_comm, list_pow_add]

lemma listblank_append_append (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s

lemma list_pow_append_one (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := list_pow_add_comm u k 1
  dsimp [HPow.hPow, list_nat_repeat] at h ⊢
  rw [List.append_nil] at h
  exact h

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) {r : ListBlank (Fin 2)} :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

lemma pow_succ_append_right (u : List (Fin 2)) (n : Nat) {r : ListBlank (Fin 2)} :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

lemma pow_succ_append_right' (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [listblank_append_append, list_pow_append_one]

lemma pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

lemma step_multiStep {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

lemma step_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, step_multiStep tm c₁ c₂ h⟩

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

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | gstep)) <;> (any_goals (first | finish | gstep)) <;> (any_goals (first | finish | gstep)) <;> (any_goals (first | finish | gstep)) <;> (any_goals (first | finish | gstep)))
local macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
local macro "execute60" : tactic =>
  `(tactic| execute <;> execute)

abbrev O : List (Fin 2) := [1]
abbrev Z : List (Fin 2) := [0]

-- ============================================================================
-- Section 5b: Shift & Macro Lemmas for holdout_270
-- ============================================================================

lemma shift_A_right_1_270 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (O ^ k +> r)) [holdout_270_tm]⊢*
    ((l <+ Z ^ k) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{A}}> ([1] +> (O ^ k +> r)))
        [holdout_270_tm]⊢*
        ((l <+ [0]) {{A}}> (O ^ k +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih (l <+ [0]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

lemma shift_E_left_1_270 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ O ^ k) <{{E}} r) [holdout_270_tm]⊢*
    (l <{{E}} (O ^ k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ O ^ k) <+ [1]) <{{E}} r)
        [holdout_270_tm]⊢*
        ((l <+ O ^ k) <{{E}} ([1] +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([1] +> r)
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

lemma shift_D_right_1_270 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> (O ^ k +> r)) [holdout_270_tm]⊢*
    ((l <+ O ^ k) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{D}}> ([1] +> (O ^ k +> r)))
        [holdout_270_tm]⊢*
        ((l <+ [1]) {{D}}> (O ^ k +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih (l <+ [1]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

lemma sweep_R (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0] +> (O ^ (k + 5) +> ([0, 1] +> r)))) [holdout_270_tm]⊢⁺
    (((l <+ [1, 1, 0]) <+ Z ^ k) {{B}}> ([0, 1, 1, 1, 0] +> r)) := by
  have hk : k + 5 = (k + 3) + 1 + 1 := by omega
  rw [hk, pow_succ_append_right O (k + 3 + 1), pow_succ_append_right O (k + 3)]
  have h1 : (l {{B}}> ([0] +> (O +> (O +> (O ^ (k + 3) +> ([0, 1] +> r))))))
      [holdout_270_tm]⊢⁺
      ((l <+ [1, 1, 0]) {{A}}> (O ^ (k + 3) +> ([0, 1] +> r))) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_A_right_1_270 (k + 3) (l <+ [1, 1, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have hk3 : k + 3 = k + 1 + 1 + 1 := by omega
  rw [hk3, pow_add_append_left _ Z (k + 1 + 1) 1, pow_add_append_left _ Z (k + 1) 1,
      pow_add_append_left _ Z k 1, pow_succ_list Z 0, pow_zero_list Z, append_nil_list] at h12
  have h3 : ((((((l <+ [1, 1, 0]) <+ Z ^ k) <+ Z) <+ Z) <+ Z) {{A}}> ([0, 1] +> r))
      [holdout_270_tm]⊢⁺
      (((l <+ [1, 1, 0]) <+ Z ^ k) {{B}}> ([0, 1, 1, 1, 0] +> r)) := by
    dsimp [Z, ListBlank.append]; execute
  exact stepPlus_trans h12 h3

lemma sweep_blank_R (k : Nat) (l : ListBlank (Fin 2)) :
    (l {{B}}> ([0] +> (O ^ (k + 4) +> default))) [holdout_270_tm]⊢⁺
    (((l <+ [1, 1, 0]) <+ Z ^ k) {{D}}> ([0, 1, 0, 1, 1] +> default)) := by
  have hk : k + 4 = (k + 2) + 1 + 1 := by omega
  rw [hk, pow_succ_append_right O (k + 2 + 1), pow_succ_append_right O (k + 2)]
  have h1 : (l {{B}}> ([0] +> (O +> (O +> (O ^ (k + 2) +> default)))))
      [holdout_270_tm]⊢⁺
      ((l <+ [1, 1, 0]) {{A}}> (O ^ (k + 2) +> default)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_A_right_1_270 (k + 2) (l <+ [1, 1, 0]) default
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have hk2 : k + 2 = k + 1 + 1 := by omega
  rw [hk2, pow_add_append_left _ Z (k + 1) 1, pow_add_append_left _ Z k 1,
      pow_succ_list Z 0, pow_zero_list Z, append_nil_list] at h12
  have h3 : (((((l <+ [1, 1, 0]) <+ Z ^ k) <+ Z) <+ Z) {{A}}> default)
      [holdout_270_tm]⊢⁺
      (((l <+ [1, 1, 0]) <+ Z ^ k) {{D}}> ([0, 1, 0, 1, 1] +> default)) := by
    dsimp [Z, ListBlank.append]; execute
  exact stepPlus_trans h12 h3

lemma left_sweep_to_hub (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [holdout_270_tm]⊢⁺
    (l {{D}}> ([0] +> (O ^ (k + 1) +> ([0, 1] +> r)))) := by
  rw [pow_add_append_left (l <+ [0, 0]) O k 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
  have h1 : ((((l <+ [0, 0]) <+ O ^ k) <+ O) {{D}}> ([0] +> r))
      [holdout_270_tm]⊢⁺
      (((l <+ [0, 0]) <+ O ^ k) <{{E}} ([0, 1] +> r)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_E_left_1_270 k (l <+ [0, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((l <+ [0, 0]) <{{E}} (O ^ k +> ([0, 1] +> r)))
      [holdout_270_tm]⊢⁺
      (l {{D}}> ([0] +> ([1] +> (O ^ k +> ([0, 1] +> r))))) := by
    dsimp [ListBlank.append]; execute
  have h123 := stepPlus_trans h12 h3
  rw [← pow_succ_append_right O k] at h123
  exact h123

lemma left_sweep_to_B (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 0, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [holdout_270_tm]⊢⁺
    (l {{B}}> ([0] +> (O ^ (k + 2) +> ([0, 1] +> r)))) := by
  have heq : l <+ [0, 0, 0] = (l <+ [0]) <+ [0, 0] := rfl
  rw [heq]
  have h1 := left_sweep_to_hub k (l <+ [0]) r
  have h2 : ((l <+ [0]) {{D}}> ([0] +> (O ^ (k + 1) +> ([0, 1] +> r))))
      [holdout_270_tm]⊢⁺
      (l {{B}}> ([0] +> ([1] +> (O ^ (k + 1) +> ([0, 1] +> r))))) := by
    dsimp [ListBlank.append]; execute
  have h12 := stepPlus_trans h1 h2
  rw [← pow_succ_append_right O (k + 1)] at h12
  exact h12

lemma merge_011 (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 1, 1, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ (k + 3)) {{D}}> ([0, 1] +> r)) := by
  rw [pow_add_append_left (l <+ [0, 1, 1, 0]) O k 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
  have h1 : ((((l <+ [0, 1, 1, 0]) <+ O ^ k) <+ O) {{D}}> ([0] +> r))
      [holdout_270_tm]⊢⁺
      (((l <+ [0, 1, 1, 0]) <+ O ^ k) <{{E}} ([0, 1] +> r)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_E_left_1_270 k (l <+ [0, 1, 1, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((l <+ [0, 1, 1, 0]) <{{E}} (O ^ k +> ([0, 1] +> r)))
      [holdout_270_tm]⊢⁺
      ((((((l <+ [0]) <+ O) <+ O) <+ O)) {{D}}> (O ^ k +> ([0, 1] +> r))) := by
    dsimp [O, ListBlank.append]; execute
  have h123 := stepPlus_trans h12 h3
  have ho3 : (((((l <+ [0]) <+ O) <+ O) <+ O)) = ((l <+ [0]) <+ O ^ 3) := by
    rw [pow_succ_list O 2, pow_succ_list O 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
    simp only [listblank_append_append]; rfl
  rw [ho3] at h123
  have h4 := shift_D_right_1_270 k ((l <+ [0]) <+ O ^ 3) ([0, 1] +> r)
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  rw [← pow_add_append_left (l <+ [0]) O 3 k] at h1234
  have hk : 3 + k = k + 3 := by omega
  rw [hk] at h1234
  exact h1234

lemma merge_p5 (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 1, 0, 1, 1, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ (k + 4)) {{D}}> ([0, 1, 1] +> r)) := by
  rw [pow_add_append_left (l <+ [0, 1, 0, 1, 1, 0]) O k 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
  have h1 : ((((l <+ [0, 1, 0, 1, 1, 0]) <+ O ^ k) <+ O) {{D}}> ([0] +> r))
      [holdout_270_tm]⊢⁺
      (((l <+ [0, 1, 0, 1, 1, 0]) <+ O ^ k) <{{E}} ([0, 1] +> r)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_E_left_1_270 k (l <+ [0, 1, 0, 1, 1, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((l <+ [0, 1, 0, 1, 1, 0]) <{{E}} (O ^ k +> ([0, 1] +> r)))
      [holdout_270_tm]⊢⁺
      ((((l <+ [0, 1, 1, 0]) <+ O) <+ O) {{D}}> (O ^ k +> ([0, 1] +> r))) := by
    dsimp [O, ListBlank.append]; execute
  have h123 := stepPlus_trans h12 h3
  have ho2 : (((l <+ [0, 1, 1, 0]) <+ O) <+ O) = ((l <+ [0, 1, 1, 0]) <+ O ^ 2) := by
    rw [pow_succ_list O 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
    simp only [listblank_append_append]; rfl
  rw [ho2] at h123
  have h4 := shift_D_right_1_270 k ((l <+ [0, 1, 1, 0]) <+ O ^ 2) ([0, 1] +> r)
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  rw [← pow_add_append_left (l <+ [0, 1, 1, 0]) O 2 k] at h1234
  have hk : 2 + k = (k + 1) + 1 := by omega
  rw [hk] at h1234
  have h5 := merge_011 (k + 1) l ([1] +> r)
  exact stepPlus_trans h1234 h5

-- ============================================================================
-- Section 5c: Concrete Finite Bridges for holdout_270
-- ============================================================================

lemma thm_A_0 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 0, 1] +> r)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 4) {{D}}> ([0] +> r)) := by
  dsimp [O, ListBlank.append]; execute

lemma step_D_0011 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 0, 0, 0]) {{D}}> ([0, 1] +> r)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 4) {{D}}> ([0, 1] +> r)) := by
  dsimp [O, ListBlank.append]; execute

lemma step_D_p3z1_pop (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 0, 0]) {{D}}> ([0, 1] +> r)) [holdout_270_tm]⊢⁺
    (l {{D}}> ([0, 1, 1, 0, 1, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma bridge_b2_m0 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1, 1] +> r)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 6) {{D}}> ([0, 1] +> r)) := by
  dsimp [O, ListBlank.append]; execute

lemma bridge_b2_tail (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 0]) {{B}}> ([0, 1, 1, 1, 0, 1] +> r)) [holdout_270_tm]⊢⁺
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma bridge_b5a (l : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1] +> default)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 5) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute60

lemma bridge_b5b_pre (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1, 0] +> r)) [holdout_270_tm]⊢⁺
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma bridge_b5b_d0_blank (l : ListBlank (Fin 2)) :
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0, 1, 1] +> default)) [holdout_270_tm]⊢⁺
    ((((l <+ [1, 1, 0]) <+ [0]) <+ O ^ 6) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute

lemma bridge_b5b_d1_blank (l : ListBlank (Fin 2)) :
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0, 1, 1, 1] +> default)) [holdout_270_tm]⊢⁺
    (((((l <+ [1, 1, 0]) <+ [1, 1, 0]) <+ [0]) <+ O ^ 4) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute

lemma bridge_b5b_d2_blank (l : ListBlank (Fin 2)) :
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0, 1, 1, 1, 1] +> default)) [holdout_270_tm]⊢⁺
    ((((l <+ [1, 1, 0]) <+ [0]) <+ O ^ 5) {{D}}> ([0, 1, 1, 1, 0, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute

lemma bridge_blank_apos_tail (l : ListBlank (Fin 2)) :
    ((l <+ [0, 0, 0]) {{D}}> ([0, 1, 0, 1, 1] +> default)) [holdout_270_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 5) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute60

-- ============================================================================
-- Section 5d: Closed State Space & Step Function for holdout_270
-- ============================================================================

inductive LTok where
  | p3z (m : Nat)
  | p5
  deriving DecidableEq

def evalL : List LTok → ListBlank (Fin 2)
  | [] => default
  | .p3z m :: ls => ((evalL ls <+ [1, 1, 0]) <+ Z ^ m)
  | .p5 :: ls => (evalL ls <+ [1, 0, 1, 1, 0])

def evalR : List Nat → ListBlank (Fin 2)
  | [] => default
  | d :: ds => [0] +> (O ^ (d + 2) +> evalR ds)

inductive State270 where
  | ModeE_c1 (ls : List LTok) (k : Nat) (ds : List Nat)
  | ModeE_ge2 (ls : List LTok) (k : Nat) (c : Nat) (ds : List Nat)
  | ModeB_ge3 (ls : List LTok) (a : Nat) (c : Nat) (ds : List Nat)
  | ModeB_b2 (ls : List LTok) (m : Nat) (ds : List Nat)
  | ModeB_blank (ls : List LTok) (a : Nat)

def k0Of (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => k' + 2

def m0Of (m : Nat) : Nat :=
  match m with
  | 0 => 0
  | m' + 1 => m' + 2

def toCfg : State270 → Cfg (Fin 2) (Fin 6)
  | .ModeE_c1 ls k ds =>
      (((evalL ls <+ [0]) <+ O ^ (k0Of k + 4)) {{D}}> ([0, 1] +> evalR ds))
  | .ModeE_ge2 ls k c ds =>
      (((evalL ls <+ [0]) <+ O ^ (k + 4)) {{D}}> ([0] +> (O ^ (c + 2) +> evalR ds)))
  | .ModeB_ge3 ls a c ds =>
      ((evalL ls) {{B}}> ([0] +> (O ^ (a + 5) +> ([0] +> (O ^ (c + 3) +> evalR ds)))))
  | .ModeB_b2 ls m ds =>
      ((evalL ls) {{B}}> ([0] +> (O ^ (m0Of m + 5) +> ([0, 1, 1] +> evalR ds))))
  | .ModeB_blank ls a =>
      ((evalL ls) {{B}}> ([0] +> (O ^ (a + 5) +> default)))

def nextModeE_p3z1 : List LTok → Nat → List Nat → State270
  | [], b, ds => .ModeE_ge2 [] 0 b ds
  | .p3z 0 :: ls'', b, ds => .ModeE_ge2 ls'' 0 (b + 1) ds
  | .p3z 1 :: ls'', b, ds => nextModeE_p3z1 ls'' 0 ((b + 1) :: ds)
  | .p3z (m2 + 2) :: ls'', b, ds => .ModeE_ge2 (.p3z m2 :: ls'') 0 b ds
  | .p5 :: ls'', b, ds => .ModeE_ge2 ls'' 1 (b + 2) ds

def nextState : State270 → State270
  | .ModeE_c1 [] k ds => .ModeB_b2 [] k ds
  | .ModeE_c1 (.p3z 0 :: ls') k ds => .ModeE_ge2 ls' (k0Of k + 2) 0 ds
  | .ModeE_c1 (.p3z 1 :: ls') k ds => nextModeE_p3z1 ls' (k0Of k + 2) (0 :: ds)
  | .ModeE_c1 (.p3z (m2 + 2) :: ls') k ds => .ModeB_b2 (.p3z m2 :: ls') k ds
  | .ModeE_c1 (.p5 :: ls') k ds => .ModeE_ge2 ls' (k0Of k + 3) 1 ds
  | .ModeE_ge2 [] k c ds => .ModeB_ge3 [] k c ds
  | .ModeE_ge2 (.p3z 0 :: ls') k c ds => .ModeE_ge2 ls' (k + 2) (c + 1) ds
  | .ModeE_ge2 (.p3z 1 :: ls') k c ds => nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)
  | .ModeE_ge2 (.p3z (m2 + 2) :: ls') k c ds => .ModeB_ge3 (.p3z m2 :: ls') k c ds
  | .ModeE_ge2 (.p5 :: ls') k c ds => .ModeE_ge2 ls' (k + 3) (c + 2) ds
  | .ModeB_ge3 ls a 0 ds => .ModeE_c1 (.p3z a :: ls) 0 ds
  | .ModeB_ge3 ls a (c' + 1) ds => .ModeE_ge2 (.p3z a :: ls) 0 c' ds
  | .ModeB_b2 ls 0 ds => .ModeE_c1 ls 1 ds
  | .ModeB_b2 ls (m' + 1) [] => .ModeE_ge2 (.p3z m' :: ls) 1 1 []
  | .ModeB_b2 ls (m' + 1) [0] => .ModeE_ge2 (.p3z 0 :: .p3z m' :: ls) 2 1 []
  | .ModeB_b2 ls (m' + 1) [1] => .ModeE_ge2 (.p3z 0 :: .p3z 0 :: .p3z m' :: ls) 0 1 []
  | .ModeB_b2 ls (m' + 1) [2] => .ModeE_ge2 (.p3z 0 :: .p3z m' :: ls) 1 1 [0]
  | .ModeB_b2 ls (m' + 1) [m'' + 3] => .ModeB_blank (.p5 :: .p3z 0 :: .p3z m' :: ls) m''
  | .ModeB_b2 ls (m' + 1) ((m4 + 5) :: 0 :: ds'') =>
      .ModeB_b2 (.p5 :: .p3z 0 :: .p3z m' :: ls) (m4 + 1) ds''
  | .ModeB_b2 ls (m' + 1) ((m'' + 3) :: (c' + 1) :: ds'') =>
      .ModeB_ge3 (.p5 :: .p3z 0 :: .p3z m' :: ls) m'' c' ds''
  | .ModeB_b2 ls (m' + 1) ds => .ModeB_b2 ls (m' + 1) ds
  | .ModeB_blank ls (a'' + 2) => .ModeE_ge2 (.p3z a'' :: ls) 1 1 []
  | .ModeB_blank ls a => .ModeB_blank ls a

-- ============================================================================
-- Section 5e: Inductive Invariant on State270
-- ============================================================================

def z0 : List LTok → Nat
  | .p3z 0 :: ls => 1 + z0 ls
  | _ => 0

def dropZ0 : List LTok → List LTok
  | .p3z 0 :: ls => dropZ0 ls
  | ls => ls

def z0Rep : Nat → List LTok → List LTok
  | 0, rest => rest
  | n + 1, rest => .p3z 0 :: z0Rep n rest

def ep : List LTok → Nat
  | .p3z m :: ls => if m % 2 = 1 then 0 else 1 + ep ls
  | _ => 0

def epW : List LTok → Nat
  | .p3z m :: ls =>
    if m % 2 = 1 then 0
    else match ls with
      | .p5 :: _ => 0
      | _ => 1 + epW ls
  | _ => 0

def prefSumW : List LTok → Nat
  | .p3z m :: ls =>
    if m % 2 = 1 then 0
    else match ls with
      | .p5 :: _ => 0
      | _ => m + prefSumW ls
  | _ => 0

def epSum : List LTok → Nat
  | .p3z m :: ls => if m % 2 = 1 then m - 1 else m + epSum ls
  | _ => 0

def hasOdd : List LTok → Bool
  | .p3z m :: ls => if m % 2 = 1 then true else hasOdd ls
  | _ => false

def hasP5 : List LTok → Bool
  | [] => false
  | .p5 :: _ => true
  | .p3z _ :: ls => hasP5 ls

def preP5Val : List LTok → Nat
  | .p3z m :: ls =>
    match ls with
    | .p5 :: _ => m
    | _ => preP5Val ls
  | _ => 0

def MustDrain : List LTok → Bool
  | .p3z m :: ls =>
    if m % 2 = 1 then
      match ls with
      | .p5 :: _ => false
      | _ => true
    else MustDrain ls
  | _ => false

def p5Suf : List LTok → List LTok
  | [] => []
  | .p5 :: ls => ls
  | .p3z _ :: ls => p5Suf ls

def isHeadP5 : List LTok → Bool
  | .p5 :: _ => true
  | _ => false

def isHeadP3z1 : List LTok → Bool
  | .p3z 1 :: _ => true
  | _ => false

def headP3zVal : List LTok → Nat
  | .p3z m :: _ => m
  | _ => 0

def isP3zGe1P5 : List LTok → Bool
  | .p3z (_ + 1) :: .p5 :: _ => true
  | _ => false

def isP3zP5 : List LTok → Bool
  | .p3z _ :: .p5 :: _ => true
  | _ => false

def drop1L : List LTok → List LTok
  | [] => []
  | _ :: xs => xs

def drop2L : List LTok → List LTok
  | _ :: _ :: xs => xs
  | _ => []

def headNat : List Nat → Nat
  | [] => 0
  | d :: _ => d

def ValidP5Chain : List LTok → Bool
  | [] => true
  | .p3z 0 :: ls => ValidP5Chain ls
  | .p5 :: suf => decide (z0 suf ≥ 18) && ValidP5Chain suf
  | .p3z (_ + 1) :: .p5 :: suf => decide (z0 suf ≥ 18) && ValidP5Chain suf
  | _ => false

def ValidAfterOdd : List LTok → Bool
  | [] => true
  | .p5 :: suf => decide (z0 suf ≥ 18) && ValidP5Chain suf
  | .p3z _ :: .p5 :: suf => decide (z0 suf ≥ 18) && ValidP5Chain suf
  | _ => false

def ValidEvenLs : List LTok → Bool
  | [] => true
  | .p5 :: suf => decide (z0 suf ≥ 18) && ValidP5Chain suf
  | .p3z m :: rest =>
    if m % 2 = 0 then ValidEvenLs rest
    else ValidAfterOdd rest

def isOddDrain1 (d : Nat) : Bool :=
  decide (d = 9 ∨ d = 11 ∨ d = 13 ∨ d = 15 ∨ d = 17)

def isOddDrainDs : List Nat → Bool
  | [d] => isOddDrain1 d
  | [d, 0] => isOddDrain1 d
  | _ => false

def GoodDs1 (d : Nat) : Bool :=
  decide (d ≤ 2 ∨ d ≥ 8)

def GoodDs2 (d d2 : Nat) : Bool :=
  if d2 = 0 then decide (d ≥ 8)
  else if d2 = 1 then decide (d = 3 ∨ d ≥ 25)
  else if d2 < 3 then false
  else if isOddDrain1 d2 && decide (d < 19) then false
  else if decide (d < 17) || !GoodDs1 d2 then false
  else if decide (d % 2 = 0 ∧ d ≤ 2 * d2 + 4) && !GoodDs1 (d2 - 1) then false
  else if decide (d % 2 = 0 ∧ d + 14 ≤ 2 * d2) && !GoodDs1 (d2 - 2) then false
  else true

def GoodDsAux : Nat → List Nat → Bool
  | d, [] => GoodDs1 d
  | d, [d2] => GoodDs2 d d2
  | d, d2 :: d3 :: ds3 =>
    if d2 < 3 then false
    else if decide (d2 = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ d < 19) then false
    else if isOddDrainDs (d2 :: d3 :: ds3) && decide (d < 19) then false
    else if decide (d2 ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ d < 39) then false
    else if decide (d < 17) || !GoodDsAux d2 (d3 :: ds3) then false
    else if decide (d % 2 = 0 ∧ d ≤ 2 * d2 + 4) && !GoodDsAux (d2 - 1) (d3 :: ds3) then false
    else if decide (d % 2 = 0 ∧ d + 14 ≤ 2 * d2) && !GoodDsAux (d2 - 2) (d3 :: ds3) then false
    else true

def GoodDs : List Nat → Bool
  | [] => true
  | d :: ds => GoodDsAux d ds

def GoodPhiW (phiW : Nat) (ds : List Nat) (is_start : Bool) : Bool :=
  if ds = [2] then decide (phiW = 4)
  else if ds = [0] then decide (phiW ≥ 6)
  else if ds = [1] then decide (phiW ≥ 1)
  else if ds = [] then is_start || decide (phiW ≥ 6)
  else if match ds with | [d, 1] => decide (d ≥ 25) | _ => false then decide (phiW ≥ 35)
  else if isOddDrainDs ds then decide (phiW ≥ 17)
  else decide (phiW ≥ 15)

def GoodPsi (psi : Nat) (ds : List Nat) : Bool :=
  GoodDs ((psi + 1) :: ds)

def checkChainAux : Nat → Bool → List LTok → Nat → Nat → Nat → List Nat → Bool
  | 0, _, _, _, _, _, _ => true
  | fuel + 1, false, ls, c, k, _, ds =>
    let cz := c + z0 ls
    let kz := k + 2 * z0 ls
    let rem := dropZ0 ls
    if !isHeadP5 rem && !GoodPhiW (cz - 1) ds false then false
    else match rem with
      | [] => GoodPsi (cz - 1) ds && checkChainAux fuel true [] (kz + 2) 0 (2 * (kz + 1) + 4) (cz :: ds)
      | .p5 :: suf => checkChainAux fuel true suf (cz + 3) (kz + 3) (2 * (cz + 2) + 4) ds
      | .p3z m :: rest =>
        let suf := drop1L rest
        if m = 1 then
          GoodPsi cz ds && checkChainAux fuel false suf (kz + 4) 1 0 ((cz + 1) :: ds)
        else if !GoodPsi (cz - 1) ds then false
        else if m % 2 = 0 ∧ m ≤ 2 * kz + 10 then
          checkChainAux fuel false suf (kz + 4) (m + 1) 0 (cz :: ds)
        else if m % 2 = 1 ∧ m ≤ 2 * kz + 11 then
          GoodDs ((kz + 2) :: cz :: ds) && checkChainAux fuel false suf (m - 1) 1 0 ((kz + 2) :: cz :: ds)
        else
          checkChainAux fuel true (.p3z (m - 4) :: .p5 :: suf) (kz + 2) 0 (2 * (kz + 1) + 4) (cz :: ds)
  | fuel + 1, true, ls, cp1, kb, margin, ds =>
    if hasOdd ls && decide (margin ≥ kb + epSum ls) then
      let psip1 := cp1 + ep ls
      let xi := kb + epSum ls + 2 * ep ls
      let suf := p5Suf ls
      if !MustDrain ls then
        if !hasP5 ls then
          checkChainAux fuel true [] (xi + 3) 0 (2 * (xi + 2) + 4) (psip1 :: ds)
        else
          GoodDs (psip1 :: ds) && checkChainAux fuel false suf (xi + 4) 1 0 (psip1 :: ds)
      else if hasP5 ls then
        let m2 := preP5Val ls
        if m2 % 2 = 0 ∧ m2 ≤ 2 * xi + 10 then
          checkChainAux fuel false suf (xi + 5) (m2 + 3) 0 (psip1 :: ds)
        else if m2 % 2 = 1 ∧ m2 ≤ 2 * xi + 11 then
          GoodDs ((xi + 3) :: psip1 :: ds) && checkChainAux fuel false suf (m2 + 1) 1 0 ((xi + 3) :: psip1 :: ds)
        else
          checkChainAux fuel true (.p3z (m2 - 2) :: .p5 :: suf) (xi + 3) 0 (2 * (xi + 2) + 4) (psip1 :: ds)
      else
        checkChainAux fuel true [] (xi + 3) 0 (2 * (xi + 2) + 4) (psip1 :: ds)
    else if !hasOdd ls && hasP5 ls && (isHeadP5 ls || decide (margin ≥ kb + epSum ls)) then
      checkChainAux fuel false (p5Suf ls) (cp1 + ep ls + 1) (kb + epSum ls + 2 * ep ls + 3) 0 ds
    else if match ds with | [d] => decide (d ≥ 8) | [d, 0] => decide (d ≥ 8) | _ => false then
      let phiWp1 := cp1 + epW ls
      let reqp1 := if isOddDrainDs ds then 18 else 16
      if phiWp1 < reqp1 then false
      else
        let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (margin + 2)
        let tail_b2 := if hasP5 ls then .p3z m_rem :: .p5 :: p5Suf ls else []
        let suf_b2 := z0Rep (phiWp1 + 2) tail_b2
        let m_rst := headNat ds - 7
        if m_rst = 1 then
          checkChainAux fuel false suf_b2 2 1 0 [3, 1]
        else
          checkChainAux fuel true (.p3z (m_rst - 2) :: .p5 :: suf_b2) 3 0 8 [1]
    else if ds = [] ∨ ds = [0] ∨ ds = [1] ∨ ds = [2] then
      let phiWp1 := cp1 + epW ls
      if phiWp1 < 2 then true
      else
        let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (margin + 2)
        let tail_b2 := if hasP5 ls then .p3z m_rem :: .p5 :: p5Suf ls else []
        if ds = [] then
          checkChainAux fuel false (z0Rep (phiWp1 + 1) tail_b2) 1 1 0 []
        else if ds = [0] then
          checkChainAux fuel true (z0Rep (phiWp1 + 2) tail_b2) 2 2 6 []
        else if ds = [1] then
          checkChainAux fuel true (z0Rep (phiWp1 + 3) tail_b2) 2 0 6 []
        else
          checkChainAux fuel false (z0Rep (phiWp1 + 2) tail_b2) 1 1 0 [0]
    else match ds with
      | d :: d2 :: ds2 =>
        if d ≥ 3 ∧ d2 ≥ 1 then
          if d % 2 = 0 ∧ d ≤ 2 * d2 + 4 ∧ GoodDs ((d2 - 1) :: ds2) = false then false
          else if d % 2 = 0 ∧ d + 14 ≤ 2 * d2 ∧ GoodDs ((d2 - 2) :: ds2) = false then false
          else if cp1 + epW ls < 16 then false
          else
            let phiWp1 := cp1 + epW ls
            let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (margin + 2)
            let tail_b2 := if hasP5 ls then .p3z m_rem :: .p5 :: p5Suf ls else []
            let ls_b2 := z0Rep phiWp1 tail_b2
            if d2 = 1 ∧ ds2 = [] ∧ d ≥ 25 then
              checkChainAux fuel true (.p3z (d - 11) :: .p5 :: .p3z 0 :: .p3z 0 :: ls_b2) 5 0 12 [2]
            else
              let nls_pop := .p3z (d - 3) :: .p5 :: .p3z 0 :: .p3z 0 :: ls_b2
              checkChainAux fuel true nls_pop (d2 - 1) 0 (2 * d2) ds2
        else true
      | _ => true

def checkResetSufAux (fuel : Nat) (m : Nat) (suf : List LTok) : Bool :=
  if m = 1 then
    checkChainAux fuel false suf 2 1 0 [3, 1]
  else
    checkChainAux fuel true (.p3z (m - 2) :: .p5 :: suf) 3 0 8 [1]

def checkDs2 (s : State270) : Bool :=
  match s with
  | .ModeB_blank _ _ => true
  | .ModeE_ge2 ls k c ds =>
    if ds ≠ [2] then true
    else hasP5 ls && !MustDrain ls && decide (z0 (p5Suf ls) ≥ 38) &&
      decide (k % 2 = 0) && !isHeadP5 ls && decide (k + epSum ls ≥ 2 * c + 6)
  | .ModeB_ge3 ls a c ds =>
    if ds ≠ [2] then true
    else hasP5 ls && !MustDrain ls && decide (z0 (p5Suf ls) ≥ 38) &&
      decide (a % 2 = 0) && !isHeadP5 ls && decide (a + epSum ls ≥ 2 * c + 4)
  | .ModeE_c1 ls k ds =>
    if ds ≠ [2] then true
    else hasP5 ls && !MustDrain ls && decide (z0 (p5Suf ls) ≥ 38) &&
      !isHeadP5 ls && decide (2 * k + epSum ls ≥ 4)
  | .ModeB_b2 ls m ds =>
    if ds ≠ [2] then true
    else hasP5 ls && !MustDrain ls && decide (z0 (p5Suf ls) ≥ 38) &&
      !isHeadP5 ls && decide (2 * m + epSum ls ≥ 2)

def checkDs1Phi1 (s : State270) : Bool :=
  match s with
  | .ModeB_blank _ _ => true
  | .ModeE_ge2 ls k c ds =>
    if ds ≠ [1] then true
    else
      let phi1_case :=
        if k % 2 = 0 then
          let pw := if isHeadP5 ls then c - 1 else c + epW ls
          decide (pw = 1)
        else false
      if !phi1_case then true
      else hasP5 ls && !MustDrain ls && !isHeadP5 ls && decide (k + epSum ls ≥ 2 * c + 14)
  | .ModeB_ge3 ls a c ds =>
    if ds ≠ [1] then true
    else
      let phi1_case :=
        if a % 2 = 0 then
          let pw := if isHeadP5 ls then c - 1 else c + epW ls
          decide (pw = 1)
        else decide (c = 2)
      if !phi1_case then true
      else
        let nls := .p3z a :: ls
        hasP5 nls && !MustDrain nls && !isHeadP5 nls &&
          (if a % 2 = 0 then decide (a + epSum ls ≥ 2 * c + 12) else decide (a ≥ 2 * c + 13))
  | .ModeE_c1 ls k ds =>
    if ds ≠ [1] then true
    else if epW ls ≠ 2 then true
    else hasP5 ls && !MustDrain ls && !isHeadP5 ls && decide (2 * k + epSum ls ≥ 12)
  | .ModeB_b2 ls m ds =>
    if ds ≠ [1] then true
    else if epW ls ≠ 2 then true
    else hasP5 ls && !MustDrain ls && !isHeadP5 ls && decide (2 * m + epSum ls ≥ 10)

def invCore (s : State270) : Bool :=
  match s with
  | .ModeB_blank ls a =>
    decide (a ≥ 5) && isHeadP5 ls &&
      (let suf := drop1L ls; decide (z0 suf ≥ 18) && ValidP5Chain suf)
  | .ModeE_ge2 ls k c ds =>
    if !GoodDs ds || !checkDs2 s || !checkDs1Phi1 s then false
    else if k % 2 = 0 then
      if !ValidEvenLs ls then false
      else if !(k ≤ 2 * c + 4 ∧ k + prefSumW ls ≤ 2 * c + 6) then false
      else
        let ok_phi :=
          if !isHeadP5 ls then
            let is_start := isHeadP3z1 ls && decide (k = 0 ∧ c = 0 ∧ ds = [])
            let is_phi1 := decide (ds = [] ∧ c + epW ls = 1) && MustDrain ls &&
              decide (c + ep ls = 1 ∧ k + epSum ls + 2 * ep ls = 2) &&
              hasP5 ls && decide (preP5Val ls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38)
            is_phi1 || GoodPhiW (c + epW ls) ds is_start
          else
            decide (c = 0 ∧ ds = [] ∧ k = 2) || (decide (c ≥ 1) && GoodPhiW (c - 1) ds false)
        if !ok_phi then false
        else if MustDrain ls && decide (2 * c + 4 < k + epSum ls) then false
        else
          let is_reset := decide (k = 0 ∧ c = 0 ∧ ds = []) && isHeadP3z1 ls
          let ok_rst :=
            if is_reset then
              match drop1L ls with
              | [] => true
              | rest => isP3zGe1P5 rest
            else true
          if !ok_rst then false
          else if hasOdd ls && decide (2 * c + 4 ≥ k + epSum ls) then
            let psi := c + ep ls
            let xi := k + epSum ls + 2 * ep ls
            if is_reset then true
            else
              GoodPsi psi ds &&
              (!decide (ds = [1] ∧ psi ≥ 24) || decide (xi ≥ 36)) &&
              (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧ (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
              (!MustDrain ls || decide (xi ≥ 14 ∧ psi ≥ 7) ||
                decide (ds = [] ∧ psi = 1 ∧ xi = 2 ∧ preP5Val ls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38))
          else true
    else
      if !ValidP5Chain ls then false
      else if !(c ≥ 1 ∧ k ≤ 2 * c + 3) then false
      else
        let cz := c + z0 ls
        let kz := k + 2 * z0 ls
        if ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 ls = true ∧ headP3zVal ls ≥ 3 then true
        else if ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 ls = 1) ∨ (k = 3 ∧ c = 2 ∧ z0 ls = 0)) ∧
            isP3zP5 (dropZ0 ls) = true ∧ headP3zVal (dropZ0 ls) ≥ 18 ∧ z0 (p5Suf ls) ≥ 38 then true
        else
          let ok_base :=
            if match ds with | d :: _ => decide (d ≥ 3) | [] => false then decide (cz ≥ 20 ∧ kz ≥ 15)
            else decide (cz ≥ 8 ∧ kz ≥ 15)
          ok_base &&
          (!decide (((ds = [] ∨ ds = [0]) ∧ cz ≥ 9) ∨ isOddDrainDs ds = true) || decide (kz ≥ 17)) &&
          (!decide (ds = [1]) || decide (kz ≥ 37)) &&
          (!(match ds with | [d, 1] => decide (d ≥ 25) | _ => false) || decide (cz ≥ 36))
  | .ModeB_ge3 ls a c ds =>
    if !GoodDs ds || !checkDs2 s || !checkDs1Phi1 s then false
    else if a % 2 = 0 then
      if !ValidEvenLs ls then false
      else
        let ok_phi :=
          if !isHeadP5 ls then
            let is_phi1 := decide (ds = [] ∧ c + epW ls = 1) && MustDrain ls &&
              decide (c + ep ls = 1 ∧ a + epSum ls + 2 * ep ls + 2 = 2) &&
              hasP5 ls && decide (preP5Val ls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38)
            decide (a + prefSumW ls ≤ 2 * c + 4) &&
              (is_phi1 || GoodPhiW (c + epW ls) ds false) &&
              (!decide (c = 0) || decide (epW (.p3z a :: ls) ≥ 1))
          else
            if c = 0 then decide (ds = [] ∧ (a = 0 ∨ (a ≥ 22 ∧ z0 (p5Suf ls) ≥ 38)))
            else GoodPhiW (c - 1) ds false
        if !ok_phi then false
        else if MustDrain ls && decide (2 * c + 2 < a + epSum ls) then false
        else if hasOdd ls && decide (2 * c + 2 ≥ a + epSum ls) then
          let psi := c + ep ls
          let xi := a + epSum ls + 2 * ep ls + 2
          GoodPsi psi ds &&
          (!decide (ds = [1] ∧ psi ≥ 24) || decide (xi ≥ 36)) &&
          (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧ (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
          (!MustDrain ls || decide (xi ≥ 14 ∧ psi ≥ 7) ||
            decide (ds = [] ∧ psi = 1 ∧ xi = 2 ∧ preP5Val ls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38))
        else true
    else
      if c = 0 ∧ !(ds = [] ∧ a ≥ 23 ∧ isHeadP5 ls = true ∧ z0 (p5Suf ls) ≥ 38) then false
      else
        let nls := .p3z a :: ls
        if !ValidEvenLs nls then false
        else
          let is_reset := decide (a = 1 ∧ c = 1 ∧ ds = [])
          let ok_c1 :=
            if c ≥ 1 then
              let is_phi1 := decide (ds = [] ∧ c = 2 ∧ a = 3) && MustDrain nls &&
                hasP5 ls && decide (preP5Val nls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38)
              if !is_reset then is_phi1 || GoodPhiW (c - 1) ds false
              else match ls with | [] => true | _ => isP3zGe1P5 ls
            else true
          if !ok_c1 then false
          else if MustDrain nls && decide (a > 2 * c + 3) then false
          else if a ≤ 2 * c + 3 then
            let psi := c - 1
            if is_reset then true
            else
              GoodPsi psi ds &&
              (!decide (ds = [1] ∧ psi ≥ 24) || decide (a ≥ 37)) &&
              (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧ (!hasP5 ls ∨ MustDrain nls)) || decide (a ≥ 17)) &&
              (!MustDrain nls || decide (a ≥ 15 ∧ psi ≥ 7) ||
                decide (ds = [] ∧ psi = 1 ∧ a = 3 ∧ preP5Val nls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38))
          else true
  | .ModeE_c1 ls k ds =>
    if !GoodDs ds || !checkDs2 s || !checkDs1Phi1 s || !ValidEvenLs ls then false
    else
      let ok_phi :=
        if ds = [] ∧ epW ls = 0 then
          decide (k ≤ 1) && isP3zP5 ls &&
            (let m0 := headP3zVal ls
             decide ((k = 0 ∧ m0 = 0) ∨ (m0 ≥ 22 - 2 * k ∧ z0 (p5Suf ls) ≥ 38)))
        else
          decide (k ≤ 1 ∧ epW ls ≥ 1 ∧ 2 * k + prefSumW ls ≤ 4) && GoodPhiW (epW ls - 1) ds false
      if !ok_phi then false
      else if MustDrain ls && decide (2 < 2 * k + epSum ls) then false
      else if hasOdd ls && decide (2 ≥ 2 * k + epSum ls) then
        let psi := ep ls - 1
        let xi := 2 * k + epSum ls + 2 * ep ls
        GoodPsi psi ds &&
        (!decide (ds = [1] ∧ psi ≥ 24) || decide (xi ≥ 36)) &&
        (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧ (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
        (!MustDrain ls || decide (xi ≥ 14 ∧ psi ≥ 7))
      else true
  | .ModeB_b2 ls m ds =>
    if !GoodDs ds || !checkDs2 s || !checkDs1Phi1 s || !ValidEvenLs ls then false
    else if m ≥ 2 then decide (ds = [] ∧ m ≥ 4) && isHeadP5 ls
    else
      let ok_phi :=
        if ds = [] ∧ epW ls = 0 then
          decide (m ≤ 1) && isP3zP5 ls &&
            (let m0 := headP3zVal ls; decide (m0 ≥ 20 - 2 * m ∧ z0 (p5Suf ls) ≥ 38))
        else
          decide (m ≤ 1 ∧ epW ls ≥ 1 ∧ 2 * m + prefSumW ls ≤ 2) && GoodPhiW (epW ls - 1) ds false
      if !ok_phi then false
      else if MustDrain ls && decide (0 < 2 * m + epSum ls) then false
      else if hasOdd ls && decide (0 ≥ 2 * m + epSum ls) then
        let psi := ep ls - 1
        let xi := 2 * m + epSum ls + 2 * ep ls + 2
        GoodPsi psi ds &&
        (!decide (ds = [1] ∧ psi ≥ 24) || decide (xi ≥ 36)) &&
        (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧ (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
        (!MustDrain ls || decide (xi ≥ 14 ∧ psi ≥ 7))
      else true

def invChain (fuel : Nat) (s : State270) : Bool :=
  match s with
  | .ModeB_blank ls a =>
    checkResetSufAux fuel (a - 4) (drop1L ls)
  | .ModeE_ge2 ls k c ds =>
    if k % 2 = 0 then
      if k = 0 ∧ c = 0 ∧ ds = [] ∧ isHeadP3z1 ls = true then
        match drop1L ls with
        | [] => checkChainAux fuel true [] 3 0 8 [1]
        | rest => checkResetSufAux fuel (headP3zVal rest) (drop2L rest)
      else
        checkChainAux fuel true ls (c + 1) k (2 * c + 4) ds
    else
      if ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 ls = true ∧ headP3zVal ls ≥ 3 then
        checkResetSufAux fuel (headP3zVal ls - 2) (drop2L ls)
      else if ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 ls = 1) ∨ (k = 3 ∧ c = 2 ∧ z0 ls = 0)) ∧
          isP3zP5 (dropZ0 ls) = true ∧ headP3zVal (dropZ0 ls) ≥ 18 ∧ z0 (p5Suf ls) ≥ 38 then
        let rem := dropZ0 ls
        checkChainAux fuel true (.p3z (headP3zVal rem - 4) :: .p5 :: drop2L rem) 5 0 12 [2]
      else
        checkChainAux fuel false ls c k 0 ds
  | .ModeB_ge3 ls a c ds =>
    if a % 2 = 0 then
      let ok := checkChainAux fuel true (.p3z a :: ls) c 0 (2 * c + 2) ds
      if isHeadP5 ls = true ∧ c = 0 ∧ a ≥ 22 then
        ok && checkChainAux fuel true (.p3z (a - 8) :: .p5 :: drop1L ls) 5 0 12 [2]
      else ok
    else
      if a = 1 ∧ c = 1 ∧ ds = [] then
        match ls with
        | [] => checkChainAux fuel true [] 3 0 8 [1]
        | _ => checkResetSufAux fuel (headP3zVal ls) (drop2L ls)
      else
        let ok := checkChainAux fuel true (.p3z a :: ls) c 0 (2 * c + 2) ds
        if c = 0 then
          ok && checkChainAux fuel true (.p3z (a - 8) :: .p5 :: drop1L ls) 5 0 12 [2]
        else ok
  | .ModeE_c1 ls k ds =>
    let ok := checkChainAux fuel true ls 0 (2 * k) 2 ds
    if ds = [] ∧ epW ls = 0 then
      let m0 := headP3zVal ls
      if !(k = 0 ∧ m0 = 0) then
        ok && checkChainAux fuel true (.p3z (m0 - 6 - 2 * (1 - k)) :: .p5 :: drop2L ls) 5 0 12 [2]
      else ok
    else ok
  | .ModeB_b2 ls m ds =>
    if m ≥ 2 then
      checkResetSufAux fuel (m - 3) (drop1L ls)
    else
      let ok := checkChainAux fuel true ls 0 2 (2 - 2 * m) ds
      if ds = [] ∧ epW ls = 0 then
        let m0 := headP3zVal ls
        ok && checkChainAux fuel true (.p3z (m0 - 4 - 2 * (1 - m)) :: .p5 :: drop2L ls) 5 0 12 [2]
      else ok

def Inv (s : State270) : Prop :=
  invCore s = true ∧ ∀ fuel : Nat, invChain fuel s = true

-- ============================================================================
-- Section 5f: TM Step Simulation & Invariant Preservation
-- ============================================================================

lemma GoodDs_pair_ge3 {d d2 : Nat} {ds2 : List Nat} (h : GoodDs (d :: d2 :: ds2) = true) : d ≥ 3 := by
  cases ds2 with
  | nil =>
    dsimp [GoodDs, GoodDsAux, GoodDs2] at h
    by_cases h1 : d2 = 0
    · simp [h1] at h; omega
    · by_cases h2 : d2 = 1
      · simp [h1, h2] at h; omega
      · by_cases h3 : d2 ≥ 3
        · simp [h1, h2, h3] at h; omega
        · simp [h1, h2, h3] at h
  | cons d3 ds3 =>
    by_contra hd
    have hd17 : decide (d < 17) = true := decide_eq_true (by omega)
    dsimp [GoodDs, GoodDsAux] at h
    rw [hd17, Bool.true_or] at h
    split_ifs at h; simp_all

lemma GoodDs_second_zero_ge8 {d : Nat} {ds2 : List Nat} (h : GoodDs (d :: 0 :: ds2) = true) : d ≥ 8 := by
  cases ds2 with
  | nil =>
    dsimp [GoodDs, GoodDsAux, GoodDs2] at h
    simp_all
  | cons d3 ds3 =>
    dsimp [GoodDs, GoodDsAux] at h
    cases h

lemma step_ModeE_p3z1_after_sweep (ls' : List LTok) (b : Nat) (ds : List Nat) :
    (((evalL ls' <+ [1, 1, 0]) {{D}}> ([0] +> (O ^ (b + 2) +> evalR ds)))) [holdout_270_tm]⊢⁺
    toCfg (nextModeE_p3z1 ls' b ds) := by
  induction ls' generalizing b ds with
  | nil =>
    dsimp only [nextModeE_p3z1, toCfg, evalL]
    have hl : (default : ListBlank (Fin 2)) <+ [1, 1, 0] = default <+ [1, 1, 0, 0, 0] := by
      have h0 : (default : ListBlank (Fin 2)) = default <+ [0, 0] := by
        calc (default : ListBlank (Fin 2)) = default <+ [0] := zero_cons_default.symm
        _ = (default <+ [0]) <+ [0] := congrArg (· <+ [0]) zero_cons_default.symm
        _ = default <+ [0, 0] := rfl
      exact congrArg (· <+ [1, 1, 0]) h0
    rw [hl]
    have hr' : [0] +> (O ^ (b + 2) +> evalR ds) = [0, 1] +> (O ^ (b + 1) +> evalR ds) := by
      have hb : b + 2 = 1 + (b + 1) := by omega
      rw [hb, pow_add_append_right O 1 (b + 1)]; rfl
    rw [hr']
    exact step_D_0011 default (O ^ (b + 1) +> evalR ds)
  | cons tok ls'' ih =>
    cases tok with
    | p3z m' =>
      cases m' with
      | zero =>
        dsimp only [nextModeE_p3z1, toCfg, evalL]
        have hl : ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ 0) <+ [1, 1, 0] = (evalL ls'' <+ [0, 1, 1, 0]) <+ O ^ 2 := rfl
        rw [hl]
        have h1 := merge_011 1 (evalL ls'') (O ^ (b + 2) +> evalR ds)
        have hr' : [0, 1] +> (O ^ (b + 2) +> evalR ds) = [0] +> (O ^ (b + 3) +> evalR ds) := by
          rw [pow_succ_append_right O (b + 2)]; rfl
        rw [hr'] at h1
        exact h1
      | succ m1 =>
        cases m1 with
        | zero =>
          dsimp only [nextModeE_p3z1, evalL]
          have hl : ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ 1) <+ [1, 1, 0] = (evalL ls'' <+ [1, 1, 0]) <+ [1, 1, 0, 0] := rfl
          rw [hl]
          have hr' : [0] +> (O ^ (b + 2) +> evalR ds) = [0, 1] +> (O ^ (b + 1) +> evalR ds) := by
            have hb : b + 2 = 1 + (b + 1) := by omega
            rw [hb, pow_add_append_right O 1 (b + 1)]; rfl
          rw [hr']
          have h1 := step_D_p3z1_pop (evalL ls'' <+ [1, 1, 0]) (O ^ (b + 1) +> evalR ds)
          have hr2 : [0, 1, 1, 0, 1, 1] +> (O ^ (b + 1) +> evalR ds) = [0] +> (O ^ (0 + 2) +> evalR ((b + 1) :: ds)) := by
            dsimp only [evalR]
            have hb : b + 1 + 2 = 2 + (b + 1) := by omega
            rw [hb, pow_add_append_right O 2 (b + 1)]; rfl
          rw [hr2] at h1
          exact stepPlus_trans h1 (ih 0 ((b + 1) :: ds))
        | succ m2 =>
          dsimp only [nextModeE_p3z1, toCfg, evalL]
          have hl : ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ (m2 + 2)) <+ [1, 1, 0] =
              ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ m2) <+ [1, 1, 0, 0, 0] := by
            rw [pow_add_append_left (evalL ls'' <+ [1, 1, 0]) Z m2 2]; rfl
          rw [hl]
          have hr' : [0] +> (O ^ (b + 2) +> evalR ds) = [0, 1] +> (O ^ (b + 1) +> evalR ds) := by
            have hb : b + 2 = 1 + (b + 1) := by omega
            rw [hb, pow_add_append_right O 1 (b + 1)]; rfl
          rw [hr']
          exact step_D_0011 ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ m2) (O ^ (b + 1) +> evalR ds)
    | p5 =>
      dsimp only [nextModeE_p3z1, toCfg, evalL]
      have hl : (evalL ls'' <+ [1, 0, 1, 1, 0]) <+ [1, 1, 0] = (evalL ls'' <+ [0, 1, 0, 1, 1, 0]) <+ O ^ 2 := rfl
      rw [hl]
      have h1 := merge_p5 1 (evalL ls'') (O ^ (b + 2) +> evalR ds)
      have hr' : [0, 1, 1] +> (O ^ (b + 2) +> evalR ds) = [0] +> (O ^ (b + 4) +> evalR ds) := by
        have hb : b + 4 = 2 + (b + 2) := by omega
        rw [hb, pow_add_append_right O 2 (b + 2)]; rfl
      rw [hr'] at h1
      exact h1

lemma step_toCfg (s : State270) (hinv : Inv s) :
    (toCfg s) [holdout_270_tm]⊢⁺ toCfg (nextState s) := by
  cases s with
  | ModeE_c1 ls k ds =>
    cases ls with
    | nil =>
      dsimp only [nextState, toCfg, evalL]
      have hl : (default : ListBlank (Fin 2)) <+ [0] = default <+ [0, 0, 0] := by
        calc (default : ListBlank (Fin 2)) <+ [0] = default := zero_cons_default
        _ = default <+ [0] := zero_cons_default.symm
        _ = (default <+ [0]) <+ [0] := congrArg (· <+ [0]) zero_cons_default.symm
        _ = ((default <+ [0]) <+ [0]) <+ [0] := congrArg (fun x => (x <+ [0]) <+ [0]) zero_cons_default.symm
        _ = default <+ [0, 0, 0] := rfl
      rw [hl]
      have h1 := left_sweep_to_B (k0Of k + 3) default ([1] +> evalR ds)
      have hm : m0Of k + 5 = k0Of k + 5 := by cases k <;> rfl
      rw [hm]
      exact h1
    | cons tok ls' =>
      cases tok with
      | p3z m =>
        cases m with
        | zero =>
          dsimp only [nextState, toCfg, evalL]
          exact merge_011 (k0Of k + 3) (evalL ls') ([1] +> evalR ds)
        | succ m1 =>
          cases m1 with
          | zero =>
            dsimp only [nextState, toCfg, evalL]
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ 1) <+ [0]) = (evalL ls' <+ [1, 1, 0]) <+ [0, 0] := rfl
            rw [hl]
            have h1 := left_sweep_to_hub (k0Of k + 3) (evalL ls' <+ [1, 1, 0]) ([1] +> evalR ds)
            exact stepPlus_trans h1 (step_ModeE_p3z1_after_sweep ls' (k0Of k + 2) (0 :: ds))
          | succ m2 =>
            dsimp only [nextState, toCfg, evalL]
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ (m2 + 2)) <+ [0]) =
                ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) <+ [0, 0, 0] := by
              rw [pow_add_append_left (evalL ls' <+ [1, 1, 0]) Z m2 2]; rfl
            rw [hl]
            have h1 := left_sweep_to_B (k0Of k + 3) ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) ([1] +> evalR ds)
            have hm : m0Of k + 5 = k0Of k + 5 := by cases k <;> rfl
            rw [hm]
            exact h1
      | p5 =>
        dsimp only [nextState, toCfg, evalL]
        exact merge_p5 (k0Of k + 3) (evalL ls') ([1] +> evalR ds)
  | ModeE_ge2 ls k c ds =>
    cases ls with
    | nil =>
      dsimp only [nextState, toCfg, evalL]
      have hl : (default : ListBlank (Fin 2)) <+ [0] = default <+ [0, 0, 0] := by
        calc (default : ListBlank (Fin 2)) <+ [0] = default := zero_cons_default
        _ = default <+ [0] := zero_cons_default.symm
        _ = (default <+ [0]) <+ [0] := congrArg (· <+ [0]) zero_cons_default.symm
        _ = ((default <+ [0]) <+ [0]) <+ [0] := congrArg (fun x => (x <+ [0]) <+ [0]) zero_cons_default.symm
        _ = default <+ [0, 0, 0] := rfl
      rw [hl]
      have h1 := left_sweep_to_B (k + 3) default (O ^ (c + 2) +> evalR ds)
      have hr : [0, 1] +> (O ^ (c + 2) +> evalR ds) = [0] +> (O ^ (c + 3) +> evalR ds) := by
        rw [pow_succ_append_right O (c + 2)]; rfl
      rw [hr] at h1
      exact h1
    | cons tok ls' =>
      cases tok with
      | p3z m =>
        cases m with
        | zero =>
          dsimp only [nextState, toCfg, evalL]
          have h1 := merge_011 (k + 3) (evalL ls') (O ^ (c + 2) +> evalR ds)
          have hr : [0, 1] +> (O ^ (c + 2) +> evalR ds) = [0] +> (O ^ (c + 3) +> evalR ds) := by
            rw [pow_succ_append_right O (c + 2)]; rfl
          rw [hr] at h1
          exact h1
        | succ m1 =>
          cases m1 with
          | zero =>
            dsimp only [nextState, toCfg, evalL]
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ 1) <+ [0]) = (evalL ls' <+ [1, 1, 0]) <+ [0, 0] := rfl
            rw [hl]
            have h1 := left_sweep_to_hub (k + 3) (evalL ls' <+ [1, 1, 0]) (O ^ (c + 2) +> evalR ds)
            have hr : [0, 1] +> (O ^ (c + 2) +> evalR ds) = evalR ((c + 1) :: ds) := by
              dsimp only [evalR]; rw [pow_succ_append_right O (c + 2)]; rfl
            rw [hr] at h1
            exact stepPlus_trans h1 (step_ModeE_p3z1_after_sweep ls' (k + 2) ((c + 1) :: ds))
          | succ m2 =>
            dsimp only [nextState, toCfg, evalL]
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ (m2 + 2)) <+ [0]) =
                ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) <+ [0, 0, 0] := by
              rw [pow_add_append_left (evalL ls' <+ [1, 1, 0]) Z m2 2]; rfl
            rw [hl]
            have h1 := left_sweep_to_B (k + 3) ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) (O ^ (c + 2) +> evalR ds)
            have hr : [0, 1] +> (O ^ (c + 2) +> evalR ds) = [0] +> (O ^ (c + 3) +> evalR ds) := by
              rw [pow_succ_append_right O (c + 2)]; rfl
            rw [hr] at h1
            exact h1
      | p5 =>
        dsimp only [nextState, toCfg, evalL]
        have h1 := merge_p5 (k + 3) (evalL ls') (O ^ (c + 2) +> evalR ds)
        have hr : [0, 1, 1] +> (O ^ (c + 2) +> evalR ds) = [0] +> (O ^ (c + 4) +> evalR ds) := by
          have hc : c + 4 = 2 + (c + 2) := by omega
          rw [hc, pow_add_append_right O 2 (c + 2)]; rfl
        rw [hr] at h1
        exact h1
  | ModeB_ge3 ls a c ds =>
    dsimp only [toCfg]
    have hr : [0] +> (O ^ (c + 3) +> evalR ds) = [0, 1] +> ([1] +> (O ^ (c + 1) +> evalR ds)) := by
      have hc : c + 3 = 2 + (c + 1) := by omega
      rw [hc, pow_add_append_right O 2 (c + 1)]; rfl
    rw [hr]
    have h1 := sweep_R a (evalL ls) ([1] +> (O ^ (c + 1) +> evalR ds))
    have h2 := thm_A_0 ((evalL ls <+ [1, 1, 0]) <+ Z ^ a) (O ^ (c + 1) +> evalR ds)
    have h12 := stepPlus_trans h1 h2
    cases c with
    | zero =>
      dsimp only [nextState, toCfg, evalL, k0Of]
      exact h12
    | succ c' =>
      dsimp only [nextState, toCfg, evalL]
      exact h12
  | ModeB_b2 ls m ds =>
    have hgd : GoodDs ds = true := by
      have hc := hinv.1
      dsimp [invCore] at hc
      cases h : GoodDs ds
      · simp [h] at hc
      · rfl
    cases m with
    | zero =>
      dsimp only [nextState, toCfg, m0Of, k0Of]
      exact bridge_b2_m0 (evalL ls) (evalR ds)
    | succ m' =>
      dsimp only [toCfg, m0Of]
      have h1 := sweep_R (m' + 2) (evalL ls) ([1] +> evalR ds)
      have hl : (evalL ls <+ [1, 1, 0]) <+ Z ^ (m' + 2) = ((evalL ls <+ [1, 1, 0]) <+ Z ^ m') <+ [0, 0] := by
        rw [pow_add_append_left (evalL ls <+ [1, 1, 0]) Z m' 2]; rfl
      rw [hl] at h1
      have h2 := bridge_b2_tail ((evalL ls <+ [1, 1, 0]) <+ Z ^ m') (evalR ds)
      have h12 := stepPlus_trans h1 h2
      let l_base := (evalL ls <+ [1, 1, 0]) <+ Z ^ m'
      cases ds with
      | nil =>
        dsimp only [nextState, toCfg, evalL, evalR] at h12 ⊢
        exact stepPlus_trans h12 (bridge_b5a l_base)
      | cons d' ds' =>
        dsimp only [evalR] at h12
        have h3 := bridge_b5b_pre l_base (O ^ (d' + 2) +> evalR ds')
        have h123 := stepPlus_trans h12 h3
        cases d' with
        | zero =>
          cases ds' with
          | nil =>
            dsimp only [nextState, toCfg, evalL, evalR] at h123 ⊢
            exact stepPlus_trans h123 (bridge_b5b_d0_blank l_base)
          | cons d2 ds'' =>
            have := GoodDs_pair_ge3 hgd; omega
        | succ d1 =>
          cases d1 with
          | zero =>
            cases ds' with
            | nil =>
              dsimp only [nextState, toCfg, evalL, evalR] at h123 ⊢
              exact stepPlus_trans h123 (bridge_b5b_d1_blank l_base)
            | cons d2 ds'' =>
              have := GoodDs_pair_ge3 hgd; omega
          | succ d2_idx =>
            cases d2_idx with
            | zero =>
              cases ds' with
              | nil =>
                dsimp only [nextState, toCfg, evalL, evalR] at h123 ⊢
                exact stepPlus_trans h123 (bridge_b5b_d2_blank l_base)
              | cons d2 ds'' =>
                have := GoodDs_pair_ge3 hgd; omega
            | succ m'' =>
              cases ds' with
              | nil =>
                dsimp only [nextState, toCfg, evalL, evalR] at h123 ⊢
                exact h123
              | cons d_next ds'' =>
                cases d_next with
                | zero =>
                  cases m'' with
                  | zero =>
                    have := GoodDs_second_zero_ge8 hgd; omega
                  | succ m3 =>
                    cases m3 with
                    | zero =>
                      have := GoodDs_second_zero_ge8 hgd; omega
                    | succ m4 =>
                      dsimp only [nextState, toCfg, evalL, evalR, m0Of] at h123 ⊢
                      exact h123
                | succ c' =>
                  dsimp only [nextState, toCfg, evalL, evalR] at h123 ⊢
                  exact h123
  | ModeB_blank ls a =>
    have ha5 : a ≥ 5 := by
      have hc := hinv.1
      dsimp [invCore] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.1
    dsimp only [toCfg]
    have h1 := sweep_blank_R (a + 1) (evalL ls)
    cases a with
    | zero => omega
    | succ a1 =>
      cases a1 with
      | zero => omega
      | succ a'' =>
        dsimp only [nextState, toCfg, evalL, evalR]
        have hl : (evalL ls <+ [1, 1, 0]) <+ Z ^ (a'' + 3) = ((evalL ls <+ [1, 1, 0]) <+ Z ^ a'') <+ [0, 0, 0] := by
          rw [pow_add_append_left (evalL ls <+ [1, 1, 0]) Z a'' 3]; rfl
        rw [hl] at h1
        exact stepPlus_trans h1 (bridge_blank_apos_tail ((evalL ls <+ [1, 1, 0]) <+ Z ^ a''))

lemma z0_z0Rep (n : Nat) (rest : List LTok) : z0 (z0Rep n rest) = n + z0 rest := by
  induction n with
  | zero => simp [z0Rep]
  | succ n ih => change 1 + z0 (z0Rep n rest) = n + 1 + z0 rest; omega

lemma ep_z0Rep (n : Nat) (rest : List LTok) : ep (z0Rep n rest) = n + ep rest := by
  induction n with
  | zero => simp [z0Rep]
  | succ n ih => dsimp [z0Rep, ep]; omega

lemma hasOdd_p3z_add2 (m : Nat) (ls : List LTok) :
    hasOdd (.p3z (m + 2) :: ls) = hasOdd (.p3z m :: ls) := by
  dsimp [hasOdd]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

lemma ep_p3z_add2 (m : Nat) (ls : List LTok) :
    ep (.p3z (m + 2) :: ls) = ep (.p3z m :: ls) := by
  dsimp [ep]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

lemma epW_p3z_add2 (m : Nat) (ls : List LTok) :
    epW (.p3z (m + 2) :: ls) = epW (.p3z m :: ls) := by
  dsimp [epW]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

lemma decide_eq_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

lemma GoodPhiW_mono (phiW : Nat) (ds : List Nat) (b : Bool) (h : GoodPhiW phiW ds false = true) :
    GoodPhiW phiW ds b = true := by
  dsimp [GoodPhiW] at h ⊢
  split_ifs at h ⊢ <;> simp_all

lemma prefSumW_p3z_add2 (m : Nat) (ls : List LTok) (hm : m % 2 = 0) (hnp5 : isHeadP5 ls = false) :
    prefSumW (.p3z (m + 2) :: ls) = prefSumW (.p3z m :: ls) + 2 := by
  have hm1 : ¬((m + 2) % 2 = 1) := by omega
  have hm2 : ¬(m % 2 = 1) := by omega
  cases ls with
  | nil => dsimp [prefSumW]; rw [if_neg hm1, if_neg hm2]
  | cons t s =>
    cases t with
    | p5 => cases hnp5
    | p3z _ => dsimp [prefSumW]; rw [if_neg hm1, if_neg hm2]; omega

lemma epSum_p3z_add2 (m : Nat) (ls : List LTok) :
    epSum (.p3z (m + 2) :: ls) = epSum (.p3z m :: ls) + 2 := by
  dsimp [epSum]
  by_cases hm : m % 2 = 1
  · have hm' : (m + 2) % 2 = 1 := by omega
    rw [if_pos hm', if_pos hm]; omega
  · have hm' : ¬((m + 2) % 2 = 1) := by omega
    rw [if_neg hm', if_neg hm]; omega

lemma MustDrain_p3z_add2 (m : Nat) (ls : List LTok) :
    MustDrain (.p3z (m + 2) :: ls) = MustDrain (.p3z m :: ls) := by
  dsimp [MustDrain]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

lemma ValidEvenLs_p3z_add2 (m : Nat) (ls : List LTok) :
    ValidEvenLs (.p3z (m + 2) :: ls) = ValidEvenLs (.p3z m :: ls) := by
  dsimp [ValidEvenLs]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

lemma preP5Val_p3z_add2_of_not_headP5 (m : Nat) (ls : List LTok) (h : isHeadP5 ls = false) :
    preP5Val (.p3z (m + 2) :: ls) = preP5Val (.p3z m :: ls) := by
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases h | p3z _ => rfl

lemma not_isHeadP5_of_MustDrain_p3z (m : Nat) (ls : List LTok) (h : MustDrain (.p3z m :: ls) = true) :
    isHeadP5 ls = false := by
  cases ls with
  | nil => rfl
  | cons t s =>
    cases t with
    | p3z _ => rfl
    | p5 =>
      dsimp [MustDrain] at h
      split_ifs at h

lemma hasOdd_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    hasOdd (.p3z k :: ls) = hasOdd ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [hasOdd]; rw [if_neg hk1]

lemma ep_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    ep (.p3z k :: ls) = 1 + ep ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [ep]; rw [if_neg hk1]

lemma epW_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) (hnp5 : isHeadP5 ls = false) :
    epW (.p3z k :: ls) = 1 + epW ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [epW]; rw [if_neg hk1]
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases hnp5 | p3z _ => rfl

lemma prefSumW_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) (hnp5 : isHeadP5 ls = false) :
    prefSumW (.p3z k :: ls) = k + prefSumW ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [prefSumW]; rw [if_neg hk1]
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases hnp5 | p3z _ => rfl

lemma epSum_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    epSum (.p3z k :: ls) = k + epSum ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [epSum]; rw [if_neg hk1]

lemma MustDrain_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    MustDrain (.p3z k :: ls) = MustDrain ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [MustDrain]; rw [if_neg hk1]

lemma ValidEvenLs_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    ValidEvenLs (.p3z k :: ls) = ValidEvenLs ls := by
  dsimp [ValidEvenLs]; rw [if_pos hk]

lemma preP5Val_p3z_cons_of_not_headP5 (k : Nat) (ls : List LTok) (h : isHeadP5 ls = false) :
    preP5Val (.p3z k :: ls) = preP5Val ls := by
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases h | p3z _ => rfl

lemma epSum_z0Rep (n : Nat) (rest : List LTok) : epSum (z0Rep n rest) = epSum rest := by
  induction n with
  | zero => rfl
  | succ n ih => dsimp [z0Rep, epSum]; omega

lemma hasOdd_z0Rep (n : Nat) (rest : List LTok) : hasOdd (z0Rep n rest) = hasOdd rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma hasP5_z0Rep (n : Nat) (rest : List LTok) : hasP5 (z0Rep n rest) = hasP5 rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma MustDrain_z0Rep (n : Nat) (rest : List LTok) : MustDrain (z0Rep n rest) = MustDrain rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma p5Suf_z0Rep (n : Nat) (rest : List LTok) : p5Suf (z0Rep n rest) = p5Suf rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma ValidP5Chain_z0Rep (n : Nat) (rest : List LTok) :
    ValidP5Chain (z0Rep n rest) = ValidP5Chain rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma z0Rep_succ_right (n : Nat) (rest : List LTok) :
    z0Rep n (.p3z 0 :: rest) = z0Rep (n + 1) rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc z0Rep (n + 1) (.p3z 0 :: rest) = .p3z 0 :: z0Rep n (.p3z 0 :: rest) := rfl
    _ = .p3z 0 :: z0Rep (n + 1) rest := by rw [ih]
    _ = z0Rep (n + 2) rest := rfl

lemma epSum_even (ls : List LTok) : epSum ls % 2 = 0 := by
  induction ls with
  | nil => rfl
  | cons tok rest ih =>
    cases tok with
    | p5 => rfl
    | p3z m =>
      dsimp [epSum]
      split_ifs with h <;> omega

lemma ValidP5Chain_imp_ValidEvenLs (ls : List LTok) (h : ValidP5Chain ls = true) :
    ValidEvenLs ls = true := by
  induction ls with
  | nil => rfl
  | cons tok rest ih =>
    cases tok with
    | p5 => exact h
    | p3z m =>
      cases m with
      | zero =>
        dsimp [ValidP5Chain] at h
        dsimp [ValidEvenLs]
        exact ih h
      | succ m' =>
        cases rest with
        | nil => cases h
        | cons tok2 suf =>
          cases tok2 with
          | p3z _ => cases h
          | p5 =>
            dsimp [ValidP5Chain] at h
            dsimp [ValidEvenLs]
            split_ifs with hm
            · exact h
            · exact h

lemma ls_eq_z0Rep_of_prefSumW_zero (ls : List LTok)
    (heven : ValidEvenLs ls = true)
    (hpref : prefSumW ls = 0)
    (hmd : MustDrain ls = false)
    (hnp5 : isHeadP5 ls = false) :
    ls = (if hasP5 ls then
            z0Rep (epW ls) (.p3z (epSum ls + (if hasOdd ls then 1 else 0)) :: .p5 :: p5Suf ls)
          else
            z0Rep (epW ls) []) ∧
    (hasP5 ls = false → hasOdd ls = false) := by
  induction ls with
  | nil => simp [z0Rep, epW, hasP5, hasOdd]
  | cons tok rest ih =>
    cases tok with
    | p5 => cases hnp5
    | p3z m =>
      by_cases hm : m % 2 = 1
      · have hrest : ∃ suf, rest = .p5 :: suf := by
          dsimp [MustDrain] at hmd
          rw [if_pos hm] at hmd
          cases rest with
          | nil => cases hmd
          | cons t2 s2 =>
            cases t2 with
            | p3z _ => cases hmd
            | p5 => exact ⟨s2, rfl⟩
        obtain ⟨suf, rfl⟩ := hrest
        refine ⟨?_, ?_⟩
        · dsimp [hasP5, epW, epSum, hasOdd, p5Suf, z0Rep]
          simp only [hm, ↓reduceIte]
          congr 2; omega
        · intro h_abs; cases h_abs
      · have hm0 : m % 2 = 0 := by omega
        cases h_rest : rest with
        | nil =>
          subst h_rest
          dsimp [prefSumW] at hpref
          rw [if_neg hm] at hpref
          have hm_z : m = 0 := by omega
          subst hm_z
          simp [hasP5, epW, hasOdd, z0Rep]
        | cons t2 s2 =>
          cases t2 with
          | p5 =>
            subst h_rest
            refine ⟨?_, ?_⟩
            · dsimp [hasP5, epW, epSum, hasOdd, p5Suf, z0Rep]
              simp [hm, z0Rep]
            · intro h_abs; cases h_abs
          | p3z m2 =>
            subst h_rest
            have hpref_unfold : prefSumW (.p3z m :: .p3z m2 :: s2) = m + prefSumW (.p3z m2 :: s2) := by
              dsimp only [prefSumW]
              rw [if_neg hm]
            rw [hpref_unfold] at hpref
            have hm_zero : m = 0 := by omega
            have hpref' : prefSumW (.p3z m2 :: s2) = 0 := by omega
            subst hm_zero
            dsimp [ValidEvenLs] at heven
            dsimp [MustDrain] at hmd
            obtain ⟨ih1, ih2⟩ := ih heven hpref' hmd rfl
            refine ⟨?_, ?_⟩
            · have hepw : epW (.p3z 0 :: .p3z m2 :: s2) = epW (.p3z m2 :: s2) + 1 := by
                rw [epW_p3z_even_cons 0 _ rfl rfl]; omega
              have hepsum : epSum (.p3z 0 :: .p3z m2 :: s2) = epSum (.p3z m2 :: s2) := by
                rw [epSum_p3z_even_cons 0 _ rfl, Nat.zero_add]
              have hodd : hasOdd (.p3z 0 :: .p3z m2 :: s2) = hasOdd (.p3z m2 :: s2) :=
                hasOdd_p3z_even_cons 0 _ rfl
              have hp5_eq : hasP5 (.p3z 0 :: .p3z m2 :: s2) = hasP5 (.p3z m2 :: s2) := rfl
              have hsuf_eq : p5Suf (.p3z 0 :: .p3z m2 :: s2) = p5Suf (.p3z m2 :: s2) := rfl
              rw [hepw, hepsum, hodd, hp5_eq, hsuf_eq]
              have h_cons := congrArg (LTok.p3z 0 :: ·) ih1
              exact h_cons.trans (by cases hasP5 (.p3z m2 :: s2) <;> rfl)
            · exact ih2

lemma checkChainAux_false_p3z0 (fuel : Nat) (ls : List LTok) (c k m_dummy : Nat) (ds : List Nat) :
    checkChainAux fuel false (.p3z 0 :: ls) c k m_dummy ds =
    checkChainAux fuel false ls (c + 1) (k + 2) m_dummy ds := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hz : c + z0 (.p3z 0 :: ls) = c + 1 + z0 ls := by change c + (1 + z0 ls) = c + 1 + z0 ls; omega
    have hk : k + 2 * z0 (.p3z 0 :: ls) = k + 2 + 2 * z0 ls := by change k + 2 * (1 + z0 ls) = k + 2 + 2 * z0 ls; omega
    have hd : dropZ0 (.p3z 0 :: ls) = dropZ0 ls := rfl
    dsimp only [checkChainAux]
    rw [hz, hk, hd]

lemma checkChainAux_true_congr (fuel : Nat) (ls1 ls2 : List LTok)
    (cp1_1 kb_1 margin_1 cp1_2 kb_2 margin_2 : Nat) (ds : List Nat)
    (hnp1 : isHeadP5 ls1 = false)
    (hnp2 : isHeadP5 ls2 = false)
    (hodd : hasOdd ls1 = hasOdd ls2)
    (hdec : decide (margin_1 ≥ kb_1 + epSum ls1) = decide (margin_2 ≥ kb_2 + epSum ls2))
    (hep : cp1_1 + ep ls1 = cp1_2 + ep ls2)
    (hxi : margin_1 ≥ kb_1 + epSum ls1 → kb_1 + epSum ls1 + 2 * ep ls1 = kb_2 + epSum ls2 + 2 * ep ls2)
    (hsuf : p5Suf ls1 = p5Suf ls2)
    (hmd : MustDrain ls1 = MustDrain ls2)
    (hp5 : hasP5 ls1 = hasP5 ls2)
    (hm2 : MustDrain ls1 = true → preP5Val ls1 = preP5Val ls2)
    (hepw : cp1_1 + epW ls1 = cp1_2 + epW ls2)
    (hrem : ¬(margin_1 ≥ kb_1 + epSum ls1) →
      kb_1 + epSum ls1 + (if hasOdd ls1 then 1 else 0) - (margin_1 + 2) =
      kb_2 + epSum ls2 + (if hasOdd ls2 then 1 else 0) - (margin_2 + 2)) :
    checkChainAux fuel true ls1 cp1_1 kb_1 margin_1 ds =
    checkChainAux fuel true ls2 cp1_2 kb_2 margin_2 ds := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    dsimp only [checkChainAux]
    rw [hnp1, hnp2, Bool.false_or, Bool.false_or]
    by_cases hge1 : margin_1 ≥ kb_1 + epSum ls1
    · have hdec1 : decide (margin_1 ≥ kb_1 + epSum ls1) = true := decide_eq_true hge1
      have hdec2 : decide (margin_2 ≥ kb_2 + epSum ls2) = true := hdec.symm.trans hdec1
      have hxi' := hxi hge1
      cases ho : hasOdd ls1
      · have ho2 : hasOdd ls2 = false := hodd.symm.trans ho
        cases hp : hasP5 ls1
        · have hp2 : hasP5 ls2 = false := hp5.symm.trans hp
          simp only [hdec1, hdec2, ho, ho2, hp, hp2, hepw, Bool.and_true, Bool.and_false, Bool.true_and,
            Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, and_false]
        · have hp2 : hasP5 ls2 = true := hp5.symm.trans hp
          simp only [hdec1, hdec2, ho2, hp2, hsuf, hep, hxi', Bool.and_true, Bool.and_false,
            Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      · have ho2 : hasOdd ls2 = true := hodd.symm.trans ho
        cases hm : MustDrain ls1
        · have hm2_eq : MustDrain ls2 = false := hmd.symm.trans hm
          simp only [hdec1, hdec2, ho2, hm2_eq, hp5, hsuf, hep, hxi', Bool.and_true, Bool.and_false,
            Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        · have hm2_eq : MustDrain ls2 = true := hmd.symm.trans hm
          have hpre := hm2 hm
          simp only [hdec1, hdec2, ho2, hm2_eq, hp5, hpre, hsuf, hep, hxi', Bool.and_true, Bool.and_false,
            Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · have hdec1 : decide (margin_1 ≥ kb_1 + epSum ls1) = false := decide_eq_false hge1
      have hdec2 : decide (margin_2 ≥ kb_2 + epSum ls2) = false := hdec.symm.trans hdec1
      have hrem' := hrem hge1
      rw [hrem']
      simp only [hdec1, hdec2, hodd, hepw, hp5, hsuf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

lemma checkChainAux_true_no_odd_no_p5 (fuel : Nat) (ls1 ls2 : List LTok)
    (cp1_1 kb_1 margin_1 cp1_2 kb_2 margin_2 : Nat) (ds : List Nat)
    (ho1 : hasOdd ls1 = false) (ho2 : hasOdd ls2 = false)
    (hp1 : hasP5 ls1 = false) (hp2 : hasP5 ls2 = false)
    (hepw : cp1_1 + epW ls1 = cp1_2 + epW ls2) :
    checkChainAux fuel true ls1 cp1_1 kb_1 margin_1 ds =
    checkChainAux fuel true ls2 cp1_2 kb_2 margin_2 ds := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    dsimp only [checkChainAux]
    simp only [ho1, ho2, hp1, hp2, hepw, Bool.false_and, Bool.and_false, Bool.not_false,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte, and_false]

lemma checkChainAux_true_p3z0 (fuel : Nat) (ls : List LTok) (cp1 kb margin : Nat) (ds : List Nat)
    (h : isHeadP5 ls = false ∨ margin ≥ kb + epSum ls) :
    checkChainAux fuel true (.p3z 0 :: ls) cp1 kb margin ds =
    checkChainAux fuel true ls (cp1 + 1) (kb + 2) (margin + 2) ds := by
  cases hp5 : isHeadP5 ls with
  | false =>
    apply checkChainAux_true_congr fuel (.p3z 0 :: ls) ls cp1 kb margin (cp1 + 1) (kb + 2) (margin + 2) ds
      rfl hp5
    · exact hasOdd_p3z_even_cons 0 ls rfl
    · rw [epSum_p3z_even_cons 0 ls rfl, Nat.zero_add]; exact decide_eq_of_iff (by omega)
    · rw [ep_p3z_even_cons 0 ls rfl]; omega
    · intro _; rw [epSum_p3z_even_cons 0 ls rfl, ep_p3z_even_cons 0 ls rfl]; omega
    · rfl
    · exact MustDrain_p3z_even_cons 0 ls rfl
    · rfl
    · intro _; exact preP5Val_p3z_cons_of_not_headP5 0 ls hp5
    · rw [epW_p3z_even_cons 0 ls rfl hp5]; omega
    · intro _; rw [epSum_p3z_even_cons 0 ls rfl, hasOdd_p3z_even_cons 0 ls rfl]; omega
  | true =>
    have hge : margin ≥ kb + epSum ls := by
      cases h with
      | inl h1 => rw [hp5] at h1; cases h1
      | inr h2 => exact h2
    cases ls with
    | nil => cases hp5
    | cons tok suf =>
      cases tok with
      | p3z _ => cases hp5
      | p5 =>
        dsimp [epSum] at hge
        cases fuel with
        | zero => rfl
        | succ fuel =>
          have hl : checkChainAux (fuel + 1) true (.p3z 0 :: .p5 :: suf) cp1 kb margin ds =
              checkChainAux fuel false suf (cp1 + 2) (kb + 5) 0 ds := by
            have hdec : decide (margin ≥ kb + 0) = true := decide_eq_true (by omega)
            dsimp only [checkChainAux]
            have ho : hasOdd (.p3z 0 :: .p5 :: suf) = false := rfl
            have hs : epSum (.p3z 0 :: .p5 :: suf) = 0 := rfl
            have hp : hasP5 (.p3z 0 :: .p5 :: suf) = true := rfl
            have hnp : isHeadP5 (.p3z 0 :: .p5 :: suf) = false := rfl
            have hep : ep (.p3z 0 :: .p5 :: suf) = 1 := rfl
            have hsuf : p5Suf (.p3z 0 :: .p5 :: suf) = suf := rfl
            rw [ho, hs, hp, hnp, hep, hsuf, hdec]
            rfl
          have hr : checkChainAux (fuel + 1) true (.p5 :: suf) (cp1 + 1) (kb + 2) (margin + 2) ds =
              checkChainAux fuel false suf (cp1 + 2) (kb + 5) 0 ds := by
            dsimp only [checkChainAux]
            have ho : hasOdd (.p5 :: suf) = false := rfl
            have hp : hasP5 (.p5 :: suf) = true := rfl
            have hip : isHeadP5 (.p5 :: suf) = true := rfl
            have hep : ep (.p5 :: suf) = 0 := rfl
            have hs : epSum (.p5 :: suf) = 0 := rfl
            have hsuf : p5Suf (.p5 :: suf) = suf := rfl
            rw [ho, hp, hip, hep, hs, hsuf]
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, Bool.true_or]
          rw [hl, hr]

lemma checkChainAux_true_E_ge2_to_B_ge3_nil (fuel : Nat) (k c : Nat) (ds : List Nat) (hk : k % 2 = 0) :
    checkChainAux fuel true [] (c + 1) k (2 * c + 4) ds =
    checkChainAux fuel true [.p3z k] c 0 (2 * c + 2) ds := by
  apply checkChainAux_true_no_odd_no_p5 fuel [] [.p3z k] (c + 1) k (2 * c + 4) c 0 (2 * c + 2) ds
    rfl (hasOdd_p3z_even_cons k [] hk) rfl rfl
  rw [epW_p3z_even_cons k [] hk rfl]; omega

lemma checkChainAux_true_E_ge2_to_B_ge3_even (fuel : Nat) (m : Nat) (ls' : List LTok) (k c : Nat)
    (ds : List Nat) (hk : k % 2 = 0) :
    checkChainAux fuel true (.p3z (m + 2) :: ls') (c + 1) k (2 * c + 4) ds =
    checkChainAux fuel true (.p3z k :: .p3z m :: ls') c 0 (2 * c + 2) ds := by
  apply checkChainAux_true_congr fuel (.p3z (m + 2) :: ls') (.p3z k :: .p3z m :: ls')
    (c + 1) k (2 * c + 4) c 0 (2 * c + 2) ds rfl rfl
  · rw [hasOdd_p3z_add2, hasOdd_p3z_even_cons k _ hk]
  · rw [epSum_p3z_add2, epSum_p3z_even_cons k _ hk]; exact decide_eq_of_iff (by omega)
  · rw [ep_p3z_add2, ep_p3z_even_cons k _ hk]; omega
  · intro _; rw [epSum_p3z_add2, epSum_p3z_even_cons k _ hk, ep_p3z_add2, ep_p3z_even_cons k _ hk]; omega
  · rfl
  · rw [MustDrain_p3z_add2, MustDrain_p3z_even_cons k _ hk]
  · rfl
  · intro hmd1
    rw [MustDrain_p3z_add2] at hmd1
    have hnp5 := not_isHeadP5_of_MustDrain_p3z m ls' hmd1
    rw [preP5Val_p3z_add2_of_not_headP5 m ls' hnp5, preP5Val_p3z_cons_of_not_headP5 k _ rfl]
  · rw [epW_p3z_add2, epW_p3z_even_cons k _ hk rfl]; omega
  · intro _
    rw [epSum_p3z_add2, epSum_p3z_even_cons k _ hk, hasOdd_p3z_add2, hasOdd_p3z_even_cons k _ hk]
    omega

lemma checkChainAux_true_E_c1_to_B_b2 (fuel : Nat) (m : Nat) (ls' : List LTok) (k : Nat)
    (ds : List Nat) (hk : k ≤ 1) :
    checkChainAux fuel true (.p3z (m + 2) :: ls') 0 (2 * k) 2 ds =
    checkChainAux fuel true (.p3z m :: ls') 0 2 (2 - 2 * k) ds := by
  have heven_sum := epSum_even (.p3z m :: ls')
  apply checkChainAux_true_congr fuel (.p3z (m + 2) :: ls') (.p3z m :: ls')
    0 (2 * k) 2 0 2 (2 - 2 * k) ds rfl rfl
  · exact hasOdd_p3z_add2 m ls'
  · rw [epSum_p3z_add2]; exact decide_eq_of_iff (by omega)
  · rw [ep_p3z_add2]
  · intro hge
    rw [epSum_p3z_add2] at hge ⊢
    rw [ep_p3z_add2]
    omega
  · rfl
  · exact MustDrain_p3z_add2 m ls'
  · rfl
  · intro hmd1
    rw [MustDrain_p3z_add2] at hmd1
    exact preP5Val_p3z_add2_of_not_headP5 m ls' (not_isHeadP5_of_MustDrain_p3z m ls' hmd1)
  · rw [epW_p3z_add2]
  · intro hlt
    rw [epSum_p3z_add2] at hlt ⊢
    rw [hasOdd_p3z_add2]
    omega

lemma step_Inv_ModeB_blank (ls : List LTok) (a : Nat) (hinv : Inv (.ModeB_blank ls a)) :
    Inv (nextState (.ModeB_blank ls a)) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp [invCore] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨ha5, hp5⟩, hz0, hvp5⟩ := hc
  cases ls with
  | nil => cases hp5
  | cons tok suf =>
    cases tok with
    | p3z _ => cases hp5
    | p5 =>
      dsimp [drop1L] at hz0 hvp5
      obtain ⟨a'', rfl⟩ : ∃ a'', a = a'' + 2 := ⟨a - 2, by omega⟩
      have ha''3 : a'' ≥ 3 := by omega
      obtain ⟨a3, rfl⟩ : ∃ a3, a'' = a3 + 1 := ⟨a'' - 1, by omega⟩
      dsimp only [nextState]
      have hvp5' : ValidP5Chain (.p3z (a3 + 1) :: .p5 :: suf) = true := by
        dsimp [ValidP5Chain]; simp [hz0, hvp5]
      have hcond : ([] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
          isP3zP5 (.p3z (a3 + 1) :: .p5 :: suf) = true ∧ headP3zVal (.p3z (a3 + 1) :: .p5 :: suf) ≥ 3 :=
        ⟨rfl, rfl, rfl, rfl, ha''3⟩
      refine ⟨?_, ?_⟩
      · dsimp [invCore, GoodDs, checkDs2, checkDs1Phi1]
        rw [hvp5']
        simp [hcond]
      · intro fuel
        have hf := hch fuel
        dsimp [invChain, drop1L] at hf ⊢
        rw [if_pos hcond]
        dsimp [headP3zVal, drop2L]
        have heq : a3 + 1 - 2 = a3 + 1 + 2 - 4 := by omega
        rw [heq]; exact hf

lemma not_bool_eq_false {b : Bool} : (!b) = false ↔ b = true := by
  cases b <;> simp

lemma bool_if_false_eq_true {c e : Bool} :
    (if c = true then false else e) = true ↔ (c = false ∧ e = true) := by
  cases c <;> simp

lemma prop_if_false_eq_true {P : Prop} [Decidable P] {e : Bool} :
    (if P then false else e) = true ↔ (¬P ∧ e = true) := by
  by_cases h : P <;> simp [h]

lemma bool_if_false_eq_self {b e : Bool} (hb : b = false) :
    (if b = true then false else e) = e := by
  simp [hb]

lemma not_bool_if_false_eq_true {b e : Bool} (hb : b = true) :
    (if (!b) = true then false else e) = e := by
  simp [hb]

lemma not_decide_if_false_eq_true {P : Prop} [Decidable P] {e : Bool} (hP : P) :
    (if (!decide P) = true then false else e) = e := by
  simp [hP]

lemma drop2L_cons (t1 t2 : LTok) (ls : List LTok) :
    drop2L (t1 :: ls) = drop2L (t2 :: ls) := by
  cases ls <;> rfl

lemma k0Of_eq_two_mul {k : Nat} (hk : k ≤ 1) : k0Of k = 2 * k := by
  cases k with
  | zero => rfl
  | succ k' =>
    cases k' with
    | zero => rfl
    | succ _ => omega

lemma step_Inv_ModeB_b2_m0 (ls : List LTok) (ds : List Nat) (hinv : Inv (.ModeB_b2 ls 0 ds)) :
    Inv (.ModeE_c1 ls 1 ds) := by
  have hc := hinv.1
  have hch := hinv.2
  have hds2 : checkDs2 (.ModeE_c1 ls 1 ds) = checkDs2 (.ModeB_b2 ls 0 ds) := by
    dsimp [checkDs2]
    by_cases h : ds = [2]
    · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [show decide (2 * 1 + epSum ls ≥ 4) = decide (2 * 0 + epSum ls ≥ 2) from
        decide_eq_of_iff (by omega)]
    · simp [h]
  have hds1 : checkDs1Phi1 (.ModeE_c1 ls 1 ds) = checkDs1Phi1 (.ModeB_b2 ls 0 ds) := by
    dsimp [checkDs1Phi1]
    by_cases h : ds = [1]
    · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
      by_cases he : epW ls = 2
      · simp only [he, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [show decide (2 * 1 + epSum ls ≥ 12) = decide (2 * 0 + epSum ls ≥ 10) from
          decide_eq_of_iff (by omega)]
      · simp [he]
    · simp [h]
  refine ⟨?_, ?_⟩
  · have hcore_eq : invCore (.ModeE_c1 ls 1 ds) = invCore (.ModeB_b2 ls 0 ds) := by
      dsimp only [invCore]
      rw [hds2, hds1, if_neg (show ¬((0 : Nat) ≥ 2) by omega)]
      have hd1 : decide ((1 : Nat) ≤ 1) = decide ((0 : Nat) ≤ 1) := rfl
      have hd2 : decide ((1 = 0 ∧ headP3zVal ls = 0) ∨ (headP3zVal ls ≥ 22 - 2 * 1 ∧ z0 (p5Suf ls) ≥ 38)) =
          decide (headP3zVal ls ≥ 20 - 2 * 0 ∧ z0 (p5Suf ls) ≥ 38) :=
        decide_eq_of_iff (by omega)
      have hd3 : decide (1 ≤ 1 ∧ epW ls ≥ 1 ∧ 2 * 1 + prefSumW ls ≤ 4) =
          decide (0 ≤ 1 ∧ epW ls ≥ 1 ∧ 2 * 0 + prefSumW ls ≤ 2) :=
        decide_eq_of_iff (by omega)
      have hd4 : decide (2 < 2 * 1 + epSum ls) = decide (0 < 2 * 0 + epSum ls) :=
        decide_eq_of_iff (by omega)
      have hd5 : decide (2 ≥ 2 * 1 + epSum ls) = decide (0 ≥ 2 * 0 + epSum ls) :=
        decide_eq_of_iff (by omega)
      have hxi : 2 * 1 + epSum ls + 2 * ep ls = 2 * 0 + epSum ls + 2 * ep ls + 2 := by omega
      rw [hd1, hd2, hd3, hd4, hd5, hxi]
    rw [hcore_eq]
    exact hc
  · intro fuel
    have hf := hch fuel
    have hch_eq : invChain fuel (.ModeE_c1 ls 1 ds) = invChain fuel (.ModeB_b2 ls 0 ds) := by
      dsimp only [invChain]
      rw [if_neg (show ¬((0 : Nat) ≥ 2) by omega)]
      by_cases hemp : ds = [] ∧ epW ls = 0
      · rw [if_pos hemp, if_pos hemp]
        have hnot : (!(1 = 0 ∧ headP3zVal ls = 0)) = true := rfl
        rw [if_pos hnot]
        have hm0 : headP3zVal ls - 6 - 2 * (1 - 1) = headP3zVal ls - 4 - 2 * (1 - 0) := by omega
        rw [hm0]
      · rw [if_neg hemp, if_neg hemp]
    rw [hch_eq]
    exact hf

lemma step_Inv_ModeE_c1 (ls : List LTok) (k : Nat) (ds : List Nat) (hinv : Inv (.ModeE_c1 ls k ds)) :
    Inv (nextState (.ModeE_c1 ls k ds)) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨⟨hgd, hds2⟩, hds1⟩, heven⟩
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hok_phi, hc⟩
  rw [not_bool_eq_false] at hok_phi
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hmd_bound, hodd_branch⟩
  have hk : k ≤ 1 := by
    by_cases h_emp : ds = [] ∧ epW ls = 0
    · rw [if_pos h_emp] at hok_phi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
      exact hok_phi.1.1
    · rw [if_neg h_emp] at hok_phi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
      exact hok_phi.1.1
  cases ls with
  | nil =>
    exfalso
    by_cases h_emp : ds = [] ∧ epW [] = 0
    · rw [if_pos h_emp] at hok_phi
      simp [isP3zP5] at hok_phi
    · rw [if_neg h_emp] at hok_phi
      simp [epW] at hok_phi
  | cons tok ls' =>
    cases tok with
    | p5 =>
      exfalso
      by_cases h_emp : ds = [] ∧ epW (.p5 :: ls') = 0
      · rw [if_pos h_emp] at hok_phi
        simp [isP3zP5] at hok_phi
      · rw [if_neg h_emp] at hok_phi
        simp [epW] at hok_phi
    | p3z m =>
      cases m with
      | zero =>
        dsimp only [nextState]
        rw [k0Of_eq_two_mul hk]
        by_cases h_emp : ds = [] ∧ epW (.p3z 0 :: ls') = 0
        · rcases h_emp with ⟨rfl, hepw0⟩
          have h_p5 : ∃ suf, ls' = .p5 :: suf := by
            cases ls' with
            | nil => simp [epW] at hepw0
            | cons t2 s2 =>
              cases t2 with
              | p3z _ => simp [epW] at hepw0
              | p5 => exact ⟨s2, rfl⟩
          obtain ⟨suf, rfl⟩ := h_p5
          rw [if_pos ⟨rfl, hepw0⟩] at hok_phi
          simp only [Bool.and_eq_true, decide_eq_true_eq, headP3zVal] at hok_phi
          have hk0 : k = 0 := by omega
          subst hk0
          have heven' : ValidEvenLs (.p5 :: suf) = true := heven
          refine ⟨?_, ?_⟩
          · dsimp only [invCore, GoodDs, checkDs2, checkDs1Phi1, isHeadP5, MustDrain, hasOdd, prefSumW]
            rw [if_pos rfl, not_bool_if_false_eq_true heven']
            rfl
          · intro fuel
            have hf := hch fuel
            dsimp [invChain] at hf ⊢
            rw [if_pos ⟨rfl, rfl⟩] at hf
            simp only [headP3zVal] at hf
            simp only [and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hf
            have h_shift := checkChainAux_true_p3z0 fuel (.p5 :: suf) 0 0 2 [] (Or.inr (by dsimp [epSum]; omega))
            rw [← h_shift]
            exact hf
        · rw [if_neg h_emp] at hok_phi
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
          rcases hok_phi with ⟨⟨_, hepw_pos, hpref_le⟩, hphiw⟩
          have hnp5 : isHeadP5 ls' = false := by
            cases ls' with
            | nil => rfl
            | cons t2 s2 =>
              cases t2 with
              | p3z _ => rfl
              | p5 => simp [epW] at hepw_pos
          have hepw_eq := epW_p3z_even_cons 0 ls' rfl hnp5
          have hpref_eq := prefSumW_p3z_even_cons 0 ls' rfl hnp5
          have hepsum_eq := epSum_p3z_even_cons 0 ls' rfl
          have hep_eq := ep_p3z_even_cons 0 ls' rfl
          have hodd_eq := hasOdd_p3z_even_cons 0 ls' rfl
          have hmd_eq := MustDrain_p3z_even_cons 0 ls' rfl
          have heven' : ValidEvenLs ls' = true := by
            rw [ValidEvenLs_p3z_even_cons 0 ls' rfl] at heven; exact heven
          have hds2' : checkDs2 (.ModeE_ge2 ls' (2 * k + 2) 0 ds) = true := by
            dsimp [checkDs2] at hds2 ⊢
            by_cases h2 : ds = [2]
            · simp only [h2, ne_eq, not_true_eq_false, ↓reduceIte] at hds2 ⊢
              rw [hepsum_eq] at hds2
              have hm0 : (2 * k + 2) % 2 = 0 := by omega
              simp only [hasP5, hmd_eq, p5Suf, isHeadP5, Bool.not_false, Bool.and_true, Bool.true_and] at hds2
              simp only [hm0, decide_true, hnp5, Bool.not_false, Bool.and_true, Bool.true_and]
              rw [show decide (2 * k + 2 + epSum ls' ≥ 2 * 0 + 6) = decide (2 * k + (0 + epSum ls') ≥ 4) from
                decide_eq_of_iff (by omega)]
              exact hds2
            · simp [h2]
          have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (2 * k + 2) 0 ds) = true := by
            dsimp [checkDs1Phi1] at hds1 ⊢
            by_cases h1 : ds = [1]
            · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
              have hm0 : (2 * k + 2) % 2 = 0 := by omega
              rw [if_pos hm0, hnp5]
              simp only [Bool.false_eq_true, ↓reduceIte]
              by_cases he1 : 0 + epW ls' = 1
              · have he2 : epW (.p3z 0 :: ls') = 2 := by omega
                simp only [he1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                simp only [he2, ne_eq, not_true_eq_false, ↓reduceIte, hasP5, hmd_eq, isHeadP5,
                  Bool.not_false, Bool.true_and, Bool.and_true, hepsum_eq] at hds1
                simp only [hnp5, Bool.not_false, Bool.true_and, Bool.and_true]
                rw [show decide (2 * k + 2 + epSum ls' ≥ 2 * 0 + 14) = decide (2 * k + (0 + epSum ls') ≥ 12) from
                  decide_eq_of_iff (by omega)]
                exact hds1
              · rw [decide_eq_false he1]; rfl
            · simp [h1]
          refine ⟨?_, ?_⟩
          · dsimp only [invCore]
            have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 ls' (2 * k + 2) 0 ds) ||
                !checkDs1Phi1 (.ModeE_ge2 ls' (2 * k + 2) 0 ds)) = false := by
              simp [hgd, hds2', hds1']
            rw [bool_if_false_eq_self h_g]
            have hm0 : (2 * k + 2) % 2 = 0 := by omega
            rw [if_pos hm0]
            rw [not_bool_if_false_eq_true heven']
            rw [hpref_eq] at hpref_le
            rw [not_decide_if_false_eq_true (by omega)]
            have hphi_eq : 0 + epW ls' = epW (.p3z 0 :: ls') - 1 := by omega
            have hphiw' : GoodPhiW (0 + epW ls') ds
                (isHeadP3z1 ls' && decide (2 * k + 2 = 0 ∧ 0 = 0 ∧ ds = [])) = true := by
              rw [hphi_eq]
              exact GoodPhiW_mono _ _ _ hphiw
            have hok_phi' : (if (!isHeadP5 ls') = true then
                (decide (ds = [] ∧ 0 + epW ls' = 1) && MustDrain ls' &&
                  decide (0 + ep ls' = 1 ∧ 2 * k + 2 + epSum ls' + 2 * ep ls' = 2) &&
                  hasP5 ls' && decide (preP5Val ls' ≥ 16 ∧ z0 (p5Suf ls') ≥ 38)) ||
                  GoodPhiW (0 + epW ls') ds (isHeadP3z1 ls' && decide (2 * k + 2 = 0 ∧ 0 = 0 ∧ ds = []))
              else
                decide (0 = 0 ∧ ds = [] ∧ 2 * k + 2 = 2) || (decide (0 ≥ 1) && GoodPhiW (0 - 1) ds false)) = true := by
              rw [if_pos (by rw [hnp5]; rfl), hphiw', Bool.or_true]
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd_eq, hepsum_eq] at hmd_bound
            have hmd_bound' : (MustDrain ls' && decide (2 * 0 + 4 < 2 * k + 2 + epSum ls')) = false := by
              rw [show decide (2 * 0 + 4 < 2 * k + 2 + epSum ls') = decide (2 < 2 * k + (0 + epSum ls')) from
                decide_eq_of_iff (by omega)]
              exact hmd_bound
            rw [bool_if_false_eq_self hmd_bound']
            have h_rst_false : (decide (2 * k + 2 = 0 ∧ 0 = 0 ∧ ds = []) && isHeadP3z1 ls') = false := by
              have hne : ¬(2 * k + 2 = 0 ∧ 0 = 0 ∧ ds = []) := by omega
              simp [hne]
            rw [h_rst_false]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            rw [hodd_eq, hepsum_eq] at hodd_branch
            have hd_odd : decide (2 * 0 + 4 ≥ 2 * k + 2 + epSum ls') = decide (2 ≥ 2 * k + (0 + epSum ls')) :=
              decide_eq_of_iff (by omega)
            rw [hd_odd]
            by_cases h_cond : (hasOdd ls' && decide (2 ≥ 2 * k + (0 + epSum ls'))) = true
            · rw [if_pos h_cond] at hodd_branch ⊢
              have hpsi_eq : ep (.p3z 0 :: ls') - 1 = 0 + ep ls' := by omega
              have hxi_eq : 2 * k + (0 + epSum ls') + 2 * ep (.p3z 0 :: ls') =
                  2 * k + 2 + epSum ls' + 2 * ep ls' := by omega
              rw [hpsi_eq, hxi_eq, hmd_eq] at hodd_branch
              have hp5_eq : hasP5 (.p3z 0 :: ls') = hasP5 ls' := rfl
              rw [hp5_eq] at hodd_branch
              simp only [Bool.and_eq_true] at hodd_branch ⊢
              rcases hodd_branch with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
              refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
              rw [h4, Bool.true_or]
            · rw [if_neg h_cond]
          · intro fuel
            have hf := hch fuel
            dsimp only [invChain] at hf ⊢
            have hm0 : (2 * k + 2) % 2 = 0 := by omega
            rw [if_pos hm0, if_neg (show ¬(2 * k + 2 = 0 ∧ 0 = 0 ∧ ds = [] ∧ isHeadP3z1 ls' = true) by omega)]
            rw [if_neg h_emp] at hf
            have h_shift := checkChainAux_true_p3z0 fuel ls' 0 (2 * k) 2 ds (Or.inl hnp5)
            rw [← h_shift]
            exact hf
      | succ m1 =>
        cases m1 with
        | zero =>
          exfalso
          by_cases h_emp : ds = [] ∧ epW (.p3z 1 :: ls') = 0
          · rw [if_pos h_emp] at hok_phi
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
            dsimp only [headP3zVal] at hok_phi
            omega
          · rw [if_neg h_emp] at hok_phi
            simp [epW] at hok_phi
        | succ m2 =>
          have hm_eq : m2 + 1 + 1 = m2 + 2 := rfl
          rw [hm_eq] at *
          dsimp only [nextState]
          have hepw_eq := epW_p3z_add2 m2 ls'
          have hep_eq := ep_p3z_add2 m2 ls'
          have hepsum_eq := epSum_p3z_add2 m2 ls'
          have hodd_eq := hasOdd_p3z_add2 m2 ls'
          have hmd_eq := MustDrain_p3z_add2 m2 ls'
          have heven_eq := ValidEvenLs_p3z_add2 m2 ls'
          have hds2' : checkDs2 (.ModeB_b2 (.p3z m2 :: ls') k ds) = true := by
            dsimp [checkDs2] at hds2 ⊢
            by_cases h2 : ds = [2]
            · simp only [h2, ne_eq, not_true_eq_false, ↓reduceIte] at hds2 ⊢
              rw [hmd_eq, hepsum_eq] at hds2
              rw [show decide (2 * k + epSum (.p3z m2 :: ls') ≥ 2) =
                  decide (2 * k + (epSum (.p3z m2 :: ls') + 2) ≥ 4) from decide_eq_of_iff (by omega)]
              exact hds2
            · simp [h2]
          have hds1' : checkDs1Phi1 (.ModeB_b2 (.p3z m2 :: ls') k ds) = true := by
            dsimp [checkDs1Phi1] at hds1 ⊢
            by_cases h1 : ds = [1]
            · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
              rw [hepw_eq, hmd_eq, hepsum_eq] at hds1
              by_cases he2 : epW (.p3z m2 :: ls') = 2
              · simp only [he2, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
                rw [show decide (2 * k + epSum (.p3z m2 :: ls') ≥ 10) =
                    decide (2 * k + (epSum (.p3z m2 :: ls') + 2) ≥ 12) from decide_eq_of_iff (by omega)]
                exact hds1
              · simp [he2]
            · simp [h1]
          refine ⟨?_, ?_⟩
          · dsimp only [invCore]
            rw [heven_eq] at heven
            have h_g : (!GoodDs ds || !checkDs2 (.ModeB_b2 (.p3z m2 :: ls') k ds) ||
                !checkDs1Phi1 (.ModeB_b2 (.p3z m2 :: ls') k ds) || !ValidEvenLs (.p3z m2 :: ls')) = false := by
              simp [hgd, hds2', hds1', heven]
            rw [bool_if_false_eq_self h_g]
            rw [if_neg (show ¬(k ≥ 2) by omega)]
            have hok_phi' : (if ds = [] ∧ epW (.p3z m2 :: ls') = 0 then
                decide (k ≤ 1) && isP3zP5 (.p3z m2 :: ls') &&
                  decide (headP3zVal (.p3z m2 :: ls') ≥ 20 - 2 * k ∧ z0 (p5Suf (.p3z m2 :: ls')) ≥ 38)
              else
                decide (k ≤ 1 ∧ epW (.p3z m2 :: ls') ≥ 1 ∧ 2 * k + prefSumW (.p3z m2 :: ls') ≤ 2) &&
                  GoodPhiW (epW (.p3z m2 :: ls') - 1) ds false) = true := by
              rw [hepw_eq] at hok_phi
              by_cases h_emp : ds = [] ∧ epW (.p3z m2 :: ls') = 0
              · rw [if_pos h_emp] at hok_phi ⊢
                have hp3zp5 : isP3zP5 (.p3z (m2 + 2) :: ls') = isP3zP5 (.p3z m2 :: ls') := by
                  cases ls' with
                  | nil => rfl
                  | cons t2 _ => cases t2 <;> rfl
                rw [hp3zp5] at hok_phi
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi ⊢
                dsimp only [headP3zVal, p5Suf] at hok_phi ⊢
                exact ⟨hok_phi.1, by omega⟩
              · rw [if_neg h_emp] at hok_phi ⊢
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
                have h_epw_ge1 : epW (.p3z m2 :: ls') ≥ 1 := hok_phi.1.2.1
                have hm2_even : m2 % 2 = 0 := by
                  dsimp [epW] at h_epw_ge1
                  by_cases hm2 : m2 % 2 = 1
                  · rw [if_pos hm2] at h_epw_ge1; omega
                  · omega
                have hnp5 : isHeadP5 ls' = false := by
                  cases ls' with
                  | nil => rfl
                  | cons t2 _ =>
                    cases t2 with
                    | p3z _ => rfl
                    | p5 => dsimp [epW] at h_epw_ge1; rw [if_neg (by omega)] at h_epw_ge1; omega
                have hpref_add2 := prefSumW_p3z_add2 m2 ls' hm2_even hnp5
                rw [hpref_add2] at hok_phi
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨hk, h_epw_ge1, by omega⟩, hok_phi.2⟩
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd_eq, hepsum_eq] at hmd_bound
            have hmd_bound' : (MustDrain (.p3z m2 :: ls') &&
                decide (0 < 2 * k + epSum (.p3z m2 :: ls'))) = false := by
              rw [show decide (0 < 2 * k + epSum (.p3z m2 :: ls')) =
                  decide (2 < 2 * k + (epSum (.p3z m2 :: ls') + 2)) from decide_eq_of_iff (by omega)]
              exact hmd_bound
            rw [bool_if_false_eq_self hmd_bound']
            rw [hodd_eq, hepsum_eq, hep_eq, hmd_eq] at hodd_branch
            have hd_odd : decide (0 ≥ 2 * k + epSum (.p3z m2 :: ls')) =
                decide (2 ≥ 2 * k + (epSum (.p3z m2 :: ls') + 2)) :=
              decide_eq_of_iff (by omega)
            have hxi_eq : 2 * k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 =
                2 * k + (epSum (.p3z m2 :: ls') + 2) + 2 * ep (.p3z m2 :: ls') := by omega
            rw [hd_odd, hxi_eq]
            have hp5_eq : hasP5 (.p3z (m2 + 2) :: ls') = hasP5 (.p3z m2 :: ls') := rfl
            rw [hp5_eq] at hodd_branch
            exact hodd_branch
          · intro fuel
            have hf := hch fuel
            dsimp only [invChain] at hf ⊢
            rw [if_neg (show ¬(k ≥ 2) by omega)]
            rw [hepw_eq] at hf
            have h_shift := checkChainAux_true_E_c1_to_B_b2 fuel m2 ls' k ds hk
            rw [h_shift] at hf
            by_cases h_emp : ds = [] ∧ epW (.p3z m2 :: ls') = 0
            · rw [if_pos h_emp] at hf ⊢
              have hnot : (!(k = 0 ∧ headP3zVal (.p3z (m2 + 2) :: ls') = 0)) = true := by
                dsimp [headP3zVal]; simp
              rw [if_pos hnot] at hf
              simp only [headP3zVal] at hf ⊢
              rw [drop2L_cons (.p3z (m2 + 2)) (.p3z m2) ls'] at hf
              have hm_sub : m2 + 2 - 6 - 2 * (1 - k) = m2 - 4 - 2 * (1 - k) := by omega
              rw [hm_sub] at hf
              exact hf
            · rw [if_neg h_emp] at hf ⊢
              exact hf

lemma step_Inv_ModeB_ge3_c0 (ls : List LTok) (a : Nat) (ds : List Nat)
    (hinv : Inv (.ModeB_ge3 ls a 0 ds)) :
    Inv (.ModeE_c1 (.p3z a :: ls) 0 ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  by_cases ha : a % 2 = 0
  · rw [if_pos ha] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, hc⟩
    rw [not_bool_eq_false] at heven
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_phi, hc⟩
    rw [not_bool_eq_false] at hok_phi
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hmd_bound, hodd_branch⟩
    have heven' : ValidEvenLs (.p3z a :: ls) = true := by
      rw [ValidEvenLs_p3z_even_cons a ls ha]; exact heven
    have hmd_eq := MustDrain_p3z_even_cons a ls ha
    have hepsum_eq := epSum_p3z_even_cons a ls ha
    have hep_eq := ep_p3z_even_cons a ls ha
    have hodd_eq := hasOdd_p3z_even_cons a ls ha
    have hds2' : checkDs2 (.ModeE_c1 (.p3z a :: ls) 0 ds) = true := by
      dsimp [checkDs2] at hds2 ⊢
      by_cases h2 : ds = [2]
      · simp only [h2, ne_eq, not_true_eq_false, ↓reduceIte] at hds2 ⊢
        simp only [ha, decide_true, hasP5, hmd_eq, p5Suf, isHeadP5, Bool.not_false,
          Bool.and_true, Bool.true_and, hepsum_eq, Nat.zero_add] at hds2 ⊢
        simp only [Bool.and_eq_true] at hds2 ⊢
        exact ⟨hds2.1.1, hds2.2⟩
      · simp [h2]
    have hds1' : checkDs1Phi1 (.ModeE_c1 (.p3z a :: ls) 0 ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
        rw [if_pos ha, if_pos ha] at hds1
        by_cases he2 : epW (.p3z a :: ls) = 2
        · simp only [he2, ne_eq, not_true_eq_false, ↓reduceIte]
          have hnp5 : isHeadP5 ls = false := by
            cases ls with
            | nil => rfl
            | cons t2 _ =>
              cases t2 with
              | p3z _ => rfl
              | p5 => dsimp [epW] at he2; rw [if_neg (by omega)] at he2; omega
          have hepw_eq := epW_p3z_even_cons a ls ha hnp5
          have he1 : 0 + epW ls = 1 := by omega
          rw [hnp5] at hds1
          simp only [Bool.false_eq_true, ↓reduceIte] at hds1
          simp only [he1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hds1
          simp only [hasP5, hmd_eq, isHeadP5, Bool.not_false, Bool.true_and, Bool.and_true, hepsum_eq, Nat.zero_add] at hds1 ⊢
          exact hds1
        · simp [he2]
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_c1 (.p3z a :: ls) 0 ds) ||
          !checkDs1Phi1 (.ModeE_c1 (.p3z a :: ls) 0 ds) || !ValidEvenLs (.p3z a :: ls)) = false := by
        simp [hgd, hds2', hds1', heven']
      rw [bool_if_false_eq_self h_g]
      by_cases hp5 : isHeadP5 ls = true
      · have h_ls : ∃ suf, ls = .p5 :: suf := by
          cases ls with
          | nil => cases hp5
          | cons t2 s2 => cases t2 with | p3z _ => cases hp5 | p5 => exact ⟨s2, rfl⟩
        obtain ⟨suf, rfl⟩ := h_ls
        have hip5 : (!isHeadP5 (.p5 :: suf)) = false := rfl
        rw [hip5, if_neg Bool.false_ne_true, if_pos rfl] at hok_phi
        simp only [decide_eq_true_eq] at hok_phi
        dsimp only [p5Suf] at hok_phi
        rcases hok_phi with ⟨rfl, ha_or⟩
        have hepw0 : epW (.p3z a :: .p5 :: suf) = 0 := by
          dsimp [epW]; rw [if_neg (by omega)]
        have hok_phi' : (if ([] : List Nat) = [] ∧ epW (.p3z a :: .p5 :: suf) = 0 then
            decide ((0 : Nat) ≤ 1) && isP3zP5 (.p3z a :: .p5 :: suf) &&
              decide ((0 = 0 ∧ headP3zVal (.p3z a :: .p5 :: suf) = 0) ∨
                (headP3zVal (.p3z a :: .p5 :: suf) ≥ 22 - 2 * 0 ∧ z0 (p5Suf (.p3z a :: .p5 :: suf)) ≥ 38))
          else
            decide (0 ≤ 1 ∧ epW (.p3z a :: .p5 :: suf) ≥ 1 ∧ 2 * 0 + prefSumW (.p3z a :: .p5 :: suf) ≤ 4) &&
              GoodPhiW (epW (.p3z a :: .p5 :: suf) - 1) [] false) = true := by
          rw [if_pos ⟨rfl, hepw0⟩]
          simp only [isP3zP5, headP3zVal, p5Suf, Bool.and_eq_true, true_and, and_true, decide_eq_true_eq]
          omega
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd0 : MustDrain (.p3z a :: .p5 :: suf) = false := by
          rw [MustDrain_p3z_even_cons a (.p5 :: suf) ha]; rfl
        have hodd0 : hasOdd (.p3z a :: .p5 :: suf) = false := by
          rw [hasOdd_p3z_even_cons a (.p5 :: suf) ha]; rfl
        rw [bool_if_false_eq_self (by simp [hmd0]), if_neg (by simp [hodd0])]
      · have hp5_f : isHeadP5 ls = false := Bool.eq_false_iff.mpr hp5
        rw [if_pos (by rw [hp5_f]; rfl)] at hok_phi
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
        rcases hok_phi with ⟨⟨hpref_le, hphi_or⟩, _⟩
        have h_imp : decide (0 + ep ls = 1 ∧ a + epSum ls + 2 * ep ls + 2 = 2) = false := by
          rw [decide_eq_false_iff_not]; omega
        have hphi1_false : (decide (ds = [] ∧ 0 + epW ls = 1) && MustDrain ls &&
            decide (0 + ep ls = 1 ∧ a + epSum ls + 2 * ep ls + 2 = 2) &&
            hasP5 ls && decide (preP5Val ls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38)) = false := by
          rw [h_imp]; simp
        rw [hphi1_false, Bool.false_or] at hphi_or
        have hepw_eq := epW_p3z_even_cons a ls ha hp5_f
        have hpref_eq := prefSumW_p3z_even_cons a ls ha hp5_f
        have h_not_emp : ¬(ds = [] ∧ epW (.p3z a :: ls) = 0) := by omega
        have hok_phi' : (if ds = [] ∧ epW (.p3z a :: ls) = 0 then
            decide ((0 : Nat) ≤ 1) && isP3zP5 (.p3z a :: ls) &&
              decide ((0 = 0 ∧ headP3zVal (.p3z a :: ls) = 0) ∨
                (headP3zVal (.p3z a :: ls) ≥ 22 - 2 * 0 ∧ z0 (p5Suf (.p3z a :: ls)) ≥ 38))
          else
            decide (0 ≤ 1 ∧ epW (.p3z a :: ls) ≥ 1 ∧ 2 * 0 + prefSumW (.p3z a :: ls) ≤ 4) &&
              GoodPhiW (epW (.p3z a :: ls) - 1) ds false) = true := by
          rw [if_neg h_not_emp]
          have hsub : epW (.p3z a :: ls) - 1 = 0 + epW ls := by omega
          rw [hsub, hphi_or, Bool.and_true, decide_eq_true_eq, hpref_eq, hepw_eq]
          omega
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_bound' : (MustDrain (.p3z a :: ls) &&
            decide (2 < 2 * 0 + epSum (.p3z a :: ls))) = false := by
          rw [hmd_eq, hepsum_eq]
          rw [show decide (2 < 2 * 0 + (a + epSum ls)) = decide (2 * 0 + 2 < a + epSum ls) from
            decide_eq_of_iff (by omega)]
          exact hmd_bound
        rw [bool_if_false_eq_self hmd_bound']
        rw [hodd_eq, hepsum_eq]
        have hd_odd : decide (2 ≥ 2 * 0 + (a + epSum ls)) = decide (2 * 0 + 2 ≥ a + epSum ls) :=
          decide_eq_of_iff (by omega)
        rw [hd_odd]
        by_cases h_cond : (hasOdd ls && decide (2 * 0 + 2 ≥ a + epSum ls)) = true
        · rw [if_pos h_cond] at hodd_branch ⊢
          have hpsi_eq : ep (.p3z a :: ls) - 1 = 0 + ep ls := by omega
          have hxi_eq : 2 * 0 + (a + epSum ls) + 2 * ep (.p3z a :: ls) =
              a + epSum ls + 2 * ep ls + 2 := by omega
          rw [hpsi_eq, hxi_eq, hmd_eq]
          have hp5_eq : hasP5 (.p3z a :: ls) = hasP5 ls := rfl
          rw [hp5_eq]
          have h_false_disj : decide (ds = [] ∧ 0 + ep ls = 1 ∧ a + epSum ls + 2 * ep ls + 2 = 2 ∧
              preP5Val ls ≥ 16 ∧ z0 (p5Suf ls) ≥ 38) = false := by
            rw [decide_eq_false_iff_not]
            intro ⟨_, h1, h2, _⟩; omega
          rw [h_false_disj, Bool.or_false] at hodd_branch
          exact hodd_branch
        · rw [if_neg h_cond]
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_pos ha] at hf
      by_cases hp5 : isHeadP5 ls = true
      · have h_ls : ∃ suf, ls = .p5 :: suf := by
          cases ls with
          | nil => cases hp5
          | cons t2 s2 => cases t2 with | p3z _ => cases hp5 | p5 => exact ⟨s2, rfl⟩
        obtain ⟨suf, rfl⟩ := h_ls
        have hip5 : (!isHeadP5 (.p5 :: suf)) = false := rfl
        rw [hip5, if_neg Bool.false_ne_true, if_pos rfl] at hok_phi
        simp only [decide_eq_true_eq] at hok_phi
        dsimp only [p5Suf] at hok_phi
        rcases hok_phi with ⟨rfl, ha_or⟩
        have hepw0 : epW (.p3z a :: .p5 :: suf) = 0 := by
          dsimp [epW]; rw [if_neg (by omega)]
        rw [if_pos ⟨rfl, hepw0⟩]
        rcases ha_or with rfl | ⟨ha22, _⟩
        · simp only [isHeadP5, headP3zVal] at hf ⊢
          rw [if_neg (by omega)] at hf
          simp only [and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact hf
        · rw [if_pos ⟨rfl, rfl, ha22⟩] at hf
          have hnot : (!((0 : Nat) = 0 ∧ headP3zVal (.p3z a :: .p5 :: suf) = 0)) = true := by
            dsimp [headP3zVal]; simp [show a ≠ 0 by omega]
          rw [if_pos hnot]
          dsimp only [headP3zVal, drop2L, drop1L] at hf ⊢
          exact hf
      · have hp5_f : isHeadP5 ls = false := Bool.eq_false_iff.mpr hp5
        have hepw_eq := epW_p3z_even_cons a ls ha hp5_f
        have h_not_emp : ¬(ds = [] ∧ epW (.p3z a :: ls) = 0) := by omega
        have h_not_p5 : ¬(isHeadP5 ls = true ∧ (0 : Nat) = 0 ∧ a ≥ 22) := by simp [hp5_f]
        rw [if_neg h_not_p5] at hf
        rw [if_neg h_not_emp]
        exact hf
  · rw [if_neg ha] at hc
    rw [prop_if_false_eq_true] at hc
    rcases hc with ⟨h_c0_cond, hc⟩
    have h_c0 : ds = [] ∧ a ≥ 23 ∧ isHeadP5 ls = true ∧ z0 (p5Suf ls) ≥ 38 := by
      by_cases h_inner : ds = [] ∧ a ≥ 23 ∧ isHeadP5 ls = true ∧ z0 (p5Suf ls) ≥ 38
      · exact h_inner
      · exfalso; apply h_c0_cond; exact ⟨rfl, by simp [h_inner]⟩
    rcases h_c0 with ⟨rfl, ha23, hp5, hz38⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, _⟩
    rw [not_bool_eq_false] at heven
    have h_ls : ∃ suf, ls = .p5 :: suf := by
      cases ls with
      | nil => cases hp5
      | cons t2 s2 => cases t2 with | p3z _ => cases hp5 | p5 => exact ⟨s2, rfl⟩
    obtain ⟨suf, rfl⟩ := h_ls
    have hm1 : a % 2 = 1 := by omega
    have hepw0 : epW (.p3z a :: .p5 :: suf) = 0 := by
      dsimp [epW]; rw [if_pos hm1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs [] || !checkDs2 (.ModeE_c1 (.p3z a :: .p5 :: suf) 0 []) ||
          !checkDs1Phi1 (.ModeE_c1 (.p3z a :: .p5 :: suf) 0 []) ||
          !ValidEvenLs (.p3z a :: .p5 :: suf)) = false := by
        dsimp [GoodDs, checkDs2, checkDs1Phi1]
        simp [heven]
      rw [bool_if_false_eq_self h_g]
      have hok_phi' : (if ([] : List Nat) = [] ∧ epW (.p3z a :: .p5 :: suf) = 0 then
          decide ((0 : Nat) ≤ 1) && isP3zP5 (.p3z a :: .p5 :: suf) &&
            decide ((0 = 0 ∧ headP3zVal (.p3z a :: .p5 :: suf) = 0) ∨
              (headP3zVal (.p3z a :: .p5 :: suf) ≥ 22 - 2 * 0 ∧ z0 (p5Suf (.p3z a :: .p5 :: suf)) ≥ 38))
        else
          decide (0 ≤ 1 ∧ epW (.p3z a :: .p5 :: suf) ≥ 1 ∧ 2 * 0 + prefSumW (.p3z a :: .p5 :: suf) ≤ 4) &&
            GoodPhiW (epW (.p3z a :: .p5 :: suf) - 1) [] false) = true := by
        rw [if_pos ⟨rfl, hepw0⟩]
        dsimp [p5Suf] at hz38
        simp only [isP3zP5, headP3zVal, p5Suf, Bool.and_eq_true, true_and, and_true, decide_eq_true_eq]
        omega
      rw [not_bool_if_false_eq_true hok_phi']
      have hmd0 : MustDrain (.p3z a :: .p5 :: suf) = false := by
        dsimp [MustDrain]; rw [if_pos hm1]
      have h_not_le : decide (2 ≥ 2 * 0 + epSum (.p3z a :: .p5 :: suf)) = false := by
        rw [decide_eq_false_iff_not]; dsimp [epSum]; rw [if_pos hm1]; omega
      have h_odd_f : (hasOdd (.p3z a :: .p5 :: suf) && decide (2 ≥ 2 * 0 + epSum (.p3z a :: .p5 :: suf))) = false := by
        rw [h_not_le, Bool.and_false]
      rw [bool_if_false_eq_self (by simp [hmd0]), h_odd_f]; rfl
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_neg ha, if_neg (show ¬(a = 1 ∧ 0 = 1 ∧ ([] : List Nat) = []) by omega), if_pos rfl] at hf
      rw [if_pos ⟨rfl, hepw0⟩]
      have hnot : (!((0 : Nat) = 0 ∧ headP3zVal (.p3z a :: .p5 :: suf) = 0)) = true := by
        dsimp [headP3zVal]; simp [show a ≠ 0 by omega]
      rw [if_pos hnot]
      dsimp only [headP3zVal, drop2L, drop1L] at hf ⊢
      exact hf

lemma step_Inv_ModeB_ge3_cpos (ls : List LTok) (a c' : Nat) (ds : List Nat)
    (hinv : Inv (.ModeB_ge3 ls a (c' + 1) ds)) :
    Inv (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  by_cases ha : a % 2 = 0
  · rw [if_pos ha] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, hc⟩
    rw [not_bool_eq_false] at heven
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_phi, hc⟩
    rw [not_bool_eq_false] at hok_phi
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hmd_bound, hodd_branch⟩
    have heven' : ValidEvenLs (.p3z a :: ls) = true := by
      rw [ValidEvenLs_p3z_even_cons a ls ha]; exact heven
    have hmd_eq := MustDrain_p3z_even_cons a ls ha
    have hepsum_eq := epSum_p3z_even_cons a ls ha
    have hep_eq := ep_p3z_even_cons a ls ha
    have hodd_eq := hasOdd_p3z_even_cons a ls ha
    have hds2' : checkDs2 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) = true := by
      dsimp [checkDs2] at hds2 ⊢
      by_cases h2 : ds = [2]
      · simp only [h2, ne_eq, not_true_eq_false, ↓reduceIte] at hds2 ⊢
        simp only [ha, decide_true, hasP5, hmd_eq, p5Suf, isHeadP5, Bool.not_false,
          Bool.and_true, Bool.true_and, hepsum_eq, Nat.zero_add] at hds2 ⊢
        rw [show decide (a + epSum ls ≥ 2 * c' + 6) = decide (a + epSum ls ≥ 2 * (c' + 1) + 4) from
          decide_eq_of_iff (by omega)]
        simp only [Bool.and_eq_true] at hds2 ⊢
        exact ⟨hds2.1.1, hds2.2⟩
      · simp [h2]
    have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
        rw [if_pos ha, if_pos ha] at hds1
        have hnp5_a : isHeadP5 (.p3z a :: ls) = false := rfl
        rw [hnp5_a] at hds1 ⊢
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hp5 : isHeadP5 ls = true
        · have h_ls : ∃ suf, ls = .p5 :: suf := by
            cases ls with
            | nil => cases hp5
            | cons t2 s2 => cases t2 with | p3z _ => cases hp5 | p5 => exact ⟨s2, rfl⟩
          obtain ⟨suf, rfl⟩ := h_ls
          have hepw0 : epW (.p3z a :: .p5 :: suf) = 0 := by
            dsimp [epW]; rw [if_neg (by omega)]
          rw [hepw0, Nat.add_zero]
          by_cases hc1 : c' = 1
          · subst hc1
            rw [hmd_eq] at hds1 ⊢
            rw [hepsum_eq]
            simp only [isHeadP5, hasP5, MustDrain, ↓reduceIte, decide_true, Bool.not_true, Bool.false_eq_true,
              Bool.not_false, Bool.true_and, decide_eq_true_eq] at hds1 ⊢
            dsimp only [epSum] at hds1 ⊢
            omega
          · rw [decide_eq_false hc1]; rfl
        · have hp5_f : isHeadP5 ls = false := Bool.eq_false_iff.mpr hp5
          have hepw_eq := epW_p3z_even_cons a ls ha hp5_f
          rw [hp5_f] at hds1
          simp only [Bool.false_eq_true, ↓reduceIte] at hds1
          have hpw_eq : c' + epW (.p3z a :: ls) = c' + 1 + epW ls := by omega
          rw [hpw_eq]
          by_cases he1 : c' + 1 + epW ls = 1
          · simp only [he1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hds1 ⊢
            simp only [hasP5, hmd_eq, Bool.not_false, Bool.true_and, Bool.and_true, hepsum_eq, Nat.zero_add] at hds1 ⊢
            rw [show decide (a + epSum ls ≥ 2 * c' + 14) = decide (a + epSum ls ≥ 2 * (c' + 1) + 12) from
              decide_eq_of_iff (by omega)]
            exact hds1
          · rw [decide_eq_false he1]; rfl
      · simp [h1]
    have h_not_p3z1 : isHeadP3z1 (.p3z a :: ls) = false := by
      dsimp [isHeadP3z1]
      by_cases h1 : a = 1
      · omega
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) ||
          !checkDs1Phi1 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven']
      by_cases hp5 : isHeadP5 ls = true
      · have h_ls : ∃ suf, ls = .p5 :: suf := by
          cases ls with
          | nil => cases hp5
          | cons t2 s2 => cases t2 with | p3z _ => cases hp5 | p5 => exact ⟨s2, rfl⟩
        obtain ⟨suf, rfl⟩ := h_ls
        dsimp [isHeadP5] at hok_phi
        have hpref0 : prefSumW (.p3z a :: .p5 :: suf) = 0 := by
          dsimp [prefSumW]; rw [if_neg (by omega)]
        have hepw0 : epW (.p3z a :: .p5 :: suf) = 0 := by
          dsimp [epW]; rw [if_neg (by omega)]
        rw [hpref0, not_decide_if_false_eq_true (by omega)]
        have hphiw' : GoodPhiW (c' + epW (.p3z a :: .p5 :: suf)) ds
            (isHeadP3z1 (.p3z a :: .p5 :: suf) && decide (0 = 0 ∧ c' = 0 ∧ ds = [])) = true := by
          rw [hepw0, Nat.add_zero]
          exact GoodPhiW_mono _ _ _ hok_phi
        have hok_phi' : (if (!isHeadP5 (.p3z a :: .p5 :: suf)) = true then
            (decide (ds = [] ∧ c' + epW (.p3z a :: .p5 :: suf) = 1) && MustDrain (.p3z a :: .p5 :: suf) &&
              decide (c' + ep (.p3z a :: .p5 :: suf) = 1 ∧ 0 + epSum (.p3z a :: .p5 :: suf) + 2 * ep (.p3z a :: .p5 :: suf) = 2) &&
              hasP5 (.p3z a :: .p5 :: suf) && decide (preP5Val (.p3z a :: .p5 :: suf) ≥ 16 ∧ z0 (p5Suf (.p3z a :: .p5 :: suf)) ≥ 38)) ||
              GoodPhiW (c' + epW (.p3z a :: .p5 :: suf)) ds (isHeadP3z1 (.p3z a :: .p5 :: suf) && decide (0 = 0 ∧ c' = 0 ∧ ds = []))
          else
            decide (c' = 0 ∧ ds = [] ∧ (0 : Nat) = 2) || (decide (c' ≥ 1) && GoodPhiW (c' - 1) ds false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z a :: .p5 :: suf)) = true := rfl
          rw [if_pos hnp5_t, hphiw', Bool.or_true]
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd0 : MustDrain (.p3z a :: .p5 :: suf) = false := by
          rw [MustDrain_p3z_even_cons a (.p5 :: suf) ha]; rfl
        have hodd0 : hasOdd (.p3z a :: .p5 :: suf) = false := by
          rw [hasOdd_p3z_even_cons a (.p5 :: suf) ha]; rfl
        have h_rst_false : (decide ((0 : Nat) = 0 ∧ c' = 0 ∧ ds = []) && isHeadP3z1 (.p3z a :: .p5 :: suf)) = false := by
          rw [h_not_p3z1, Bool.and_false]
        rw [bool_if_false_eq_self (by simp [hmd0]), h_rst_false]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        rw [if_neg (by simp [hodd0])]
      · have hp5_f : isHeadP5 ls = false := Bool.eq_false_iff.mpr hp5
        rw [if_pos (by rw [hp5_f]; rfl)] at hok_phi
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
        rcases hok_phi with ⟨⟨hpref_le, hphi_or⟩, _⟩
        have hepw_eq := epW_p3z_even_cons a ls ha hp5_f
        have hpref_eq := prefSumW_p3z_even_cons a ls ha hp5_f
        have hpre_eq := preP5Val_p3z_cons_of_not_headP5 a ls hp5_f
        have h_b_pref : 0 ≤ 2 * c' + 4 ∧ 0 + prefSumW (.p3z a :: ls) ≤ 2 * c' + 6 := by omega
        rw [not_decide_if_false_eq_true h_b_pref]
        have hok_phi' : (if (!isHeadP5 (.p3z a :: ls)) = true then
            (decide (ds = [] ∧ c' + epW (.p3z a :: ls) = 1) && MustDrain (.p3z a :: ls) &&
              decide (c' + ep (.p3z a :: ls) = 1 ∧ 0 + epSum (.p3z a :: ls) + 2 * ep (.p3z a :: ls) = 2) &&
              hasP5 (.p3z a :: ls) && decide (preP5Val (.p3z a :: ls) ≥ 16 ∧ z0 (p5Suf (.p3z a :: ls)) ≥ 38)) ||
              GoodPhiW (c' + epW (.p3z a :: ls)) ds (isHeadP3z1 (.p3z a :: ls) && decide (0 = 0 ∧ c' = 0 ∧ ds = []))
          else
            decide (c' = 0 ∧ ds = [] ∧ (0 : Nat) = 2) || (decide (c' ≥ 1) && GoodPhiW (c' - 1) ds false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z a :: ls)) = true := rfl
          rw [if_pos hnp5_t]
          cases Bool.or_eq_true_iff.mp hphi_or with
          | inl hphi1 =>
            apply Bool.or_inl
            rw [hmd_eq, hpre_eq]
            simp only [hasP5, p5Suf]
            rw [show decide (ds = [] ∧ c' + epW (.p3z a :: ls) = 1) = decide (ds = [] ∧ c' + 1 + epW ls = 1) from
              decide_eq_of_iff ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩]
            rw [show decide (c' + ep (.p3z a :: ls) = 1 ∧ 0 + epSum (.p3z a :: ls) + 2 * ep (.p3z a :: ls) = 2) =
              decide (c' + 1 + ep ls = 1 ∧ a + epSum ls + 2 * ep ls + 2 = 2) from
              decide_eq_of_iff (by omega)]
            exact hphi1
          | inr hphiw =>
            apply Bool.or_inr
            have hpw_eq : c' + epW (.p3z a :: ls) = c' + 1 + epW ls := by omega
            rw [hpw_eq]
            exact GoodPhiW_mono _ _ _ hphiw
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_bound' : (MustDrain (.p3z a :: ls) &&
            decide (2 * c' + 4 < 0 + epSum (.p3z a :: ls))) = false := by
          rw [hmd_eq, hepsum_eq]
          rw [show decide (2 * c' + 4 < 0 + (a + epSum ls)) = decide (2 * (c' + 1) + 2 < a + epSum ls) from
            decide_eq_of_iff (by omega)]
          exact hmd_bound
        rw [bool_if_false_eq_self hmd_bound']
        have h_rst_false : (decide ((0 : Nat) = 0 ∧ c' = 0 ∧ ds = []) && isHeadP3z1 (.p3z a :: ls)) = false := by
          rw [h_not_p3z1, Bool.and_false]
        rw [h_rst_false]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        rw [hodd_eq, hepsum_eq]
        have hd_odd : decide (2 * c' + 4 ≥ 0 + (a + epSum ls)) = decide (2 * (c' + 1) + 2 ≥ a + epSum ls) :=
          decide_eq_of_iff (by omega)
        rw [hd_odd]
        by_cases h_cond : (hasOdd ls && decide (2 * (c' + 1) + 2 ≥ a + epSum ls)) = true
        · rw [if_pos h_cond] at hodd_branch ⊢
          have hpsi_eq : c' + ep (.p3z a :: ls) = c' + 1 + ep ls := by omega
          have hxi_eq : 0 + (a + epSum ls) + 2 * ep (.p3z a :: ls) =
              a + epSum ls + 2 * ep ls + 2 := by omega
          rw [hpsi_eq, hxi_eq, hmd_eq, hpre_eq]
          simp only [hasP5, p5Suf]
          exact hodd_branch
        · rw [if_neg h_cond]
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_pos ha, if_neg (show ¬(isHeadP5 ls = true ∧ c' + 1 = 0 ∧ a ≥ 22) by omega)] at hf
      rw [if_pos rfl, if_neg (by simp [h_not_p3z1])]
      have hm_eq : 2 * c' + 4 = 2 * (c' + 1) + 2 := by omega
      rw [hm_eq]
      exact hf
  · have hm1 : a % 2 = 1 := by omega
    rw [if_neg ha] at hc
    rw [prop_if_false_eq_true] at hc
    rcases hc with ⟨_, hc⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, hc⟩
    rw [not_bool_eq_false] at heven
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_c1, hc⟩
    rw [not_bool_eq_false] at hok_c1
    rw [ if_pos (show c' + 1 ≥ 1 by omega) ] at hok_c1
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hmd_bound, hodd_branch⟩
    have hepw0 : epW (.p3z a :: ls) = 0 := by dsimp [epW]; rw [if_pos hm1]
    have hpref0 : prefSumW (.p3z a :: ls) = 0 := by dsimp [prefSumW]; rw [if_pos hm1]
    have hep0 : ep (.p3z a :: ls) = 0 := by dsimp [ep]; rw [if_pos hm1]
    have hepsum_odd : epSum (.p3z a :: ls) = a - 1 := by dsimp [epSum]; rw [if_pos hm1]
    have hodd_true : hasOdd (.p3z a :: ls) = true := by dsimp [hasOdd]; rw [if_pos hm1]
    have hds2' : checkDs2 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) = true := by
      dsimp [checkDs2] at hds2 ⊢
      by_cases h2 : ds = [2]
      · simp [h2, ha] at hds2
      · simp [h2]
    have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
        rw [if_neg ha, if_neg ha] at hds1
        have hnp5_a : isHeadP5 (.p3z a :: ls) = false := rfl
        rw [hnp5_a] at hds1 ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true] at hds1 ⊢
        rw [hepw0, Nat.add_zero]
        by_cases hc1 : c' = 1
        · subst hc1
          simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hds1 ⊢
          rw [hepsum_odd, Nat.zero_add]
          rw [show decide (a - 1 ≥ 2 * 1 + 14) = decide (a ≥ 2 * (1 + 1) + 13) from
            decide_eq_of_iff (by omega)]
          exact hds1
        · rw [decide_eq_false hc1]; rfl
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) ||
          !checkDs1Phi1 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven]
      rw [hpref0, not_decide_if_false_eq_true (by omega)]
      by_cases hrst : a = 1 ∧ c' = 0 ∧ ds = []
      · rcases hrst with ⟨rfl, rfl, rfl⟩
        have hok_phi' : (if (!isHeadP5 (.p3z 1 :: ls)) = true then
            (decide (([] : List Nat) = [] ∧ 0 + epW (.p3z 1 :: ls) = 1) && MustDrain (.p3z 1 :: ls) &&
              decide (0 + ep (.p3z 1 :: ls) = 1 ∧ 0 + epSum (.p3z 1 :: ls) + 2 * ep (.p3z 1 :: ls) = 2) &&
              hasP5 (.p3z 1 :: ls) && decide (preP5Val (.p3z 1 :: ls) ≥ 16 ∧ z0 (p5Suf (.p3z 1 :: ls)) ≥ 38)) ||
              GoodPhiW (0 + epW (.p3z 1 :: ls)) [] (isHeadP3z1 (.p3z 1 :: ls) && decide (0 = 0 ∧ 0 = 0 ∧ ([] : List Nat) = []))
          else
            decide ((0 : Nat) = 0 ∧ ([] : List Nat) = [] ∧ (0 : Nat) = 2) || (decide (0 ≥ 1) && GoodPhiW (0 - 1) [] false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z 1 :: ls)) = true := rfl
          rw [if_pos hnp5_t, hepw0]
          dsimp [isHeadP3z1, GoodPhiW]
          simp
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_false : (MustDrain (.p3z 1 :: ls) && decide (2 * 0 + 4 < 0 + epSum (.p3z 1 :: ls))) = false := by
          rw [hepsum_odd]; simp
        rw [bool_if_false_eq_self hmd_false]
        have hrst_true : (decide ((0 : Nat) = 0 ∧ (0 : Nat) = 0 ∧ ([] : List Nat) = []) && isHeadP3z1 (.p3z 1 :: ls)) = true := rfl
        rw [hrst_true]
        rw [if_neg (by decide)] at hok_c1
        dsimp only [drop1L]
        cases ls <;> simp [hok_c1]
      · have hrst_b : decide (a = 1 ∧ c' + 1 = 1 ∧ ds = []) = false := by
          rw [decide_eq_false_iff_not]
          intro ⟨h1, h2, h3⟩
          exact hrst ⟨h1, by omega, h3⟩
        have hrst_e : (decide ((0 : Nat) = 0 ∧ c' = 0 ∧ ds = []) && isHeadP3z1 (.p3z a :: ls)) = false := by
          dsimp [isHeadP3z1]
          by_cases ha1 : a = 1
          · subst ha1
            have hnot : decide ((0 : Nat) = 0 ∧ c' = 0 ∧ ds = []) = false :=
              decide_eq_false (fun ⟨_, hc0, hds⟩ => hrst ⟨rfl, hc0, hds⟩)
            rw [hnot]; rfl
          · simp [ha1]
        have hstart_e : (isHeadP3z1 (.p3z a :: ls) && decide ((0 : Nat) = 0 ∧ c' = 0 ∧ ds = [])) = false := by
          rw [Bool.and_comm]; exact hrst_e
        rw [hrst_b] at hok_c1
        simp only [Bool.not_false, ↓reduceIte] at hok_c1
        have hok_phi' : (if (!isHeadP5 (.p3z a :: ls)) = true then
            (decide (ds = [] ∧ c' + epW (.p3z a :: ls) = 1) && MustDrain (.p3z a :: ls) &&
              decide (c' + ep (.p3z a :: ls) = 1 ∧ 0 + epSum (.p3z a :: ls) + 2 * ep (.p3z a :: ls) = 2) &&
              hasP5 (.p3z a :: ls) && decide (preP5Val (.p3z a :: ls) ≥ 16 ∧ z0 (p5Suf (.p3z a :: ls)) ≥ 38)) ||
              GoodPhiW (c' + epW (.p3z a :: ls)) ds (isHeadP3z1 (.p3z a :: ls) && decide (0 = 0 ∧ c' = 0 ∧ ds = []))
          else
            decide (c' = 0 ∧ ds = [] ∧ (0 : Nat) = 2) || (decide (c' ≥ 1) && GoodPhiW (c' - 1) ds false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z a :: ls)) = true := rfl
          rw [if_pos hnp5_t, hepw0, hep0, hepsum_odd, hstart_e]
          cases Bool.or_eq_true_iff.mp hok_c1 with
          | inl hphi1 =>
            apply Bool.or_inl
            simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hphi1 ⊢
            simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, hasP5, p5Suf] at hphi1 ⊢
            rcases hphi1 with ⟨rfl, hc2, rfl, hmd, hp5, hpre, hz⟩
            have hc1 : c' = 1 := by omega
            subst hc1
            exact ⟨rfl, rfl, hmd, rfl, rfl, hp5, hpre, hz⟩
          | inr hphiw =>
            rw [Nat.add_sub_cancel] at hphiw
            rw [Nat.add_zero]
            exact Bool.or_inr hphiw
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_bound' : (MustDrain (.p3z a :: ls) &&
            decide (2 * c' + 4 < 0 + epSum (.p3z a :: ls))) = false := by
          rw [hepsum_odd]
          rw [show decide (2 * c' + 4 < 0 + (a - 1)) = decide (a > 2 * (c' + 1) + 3) from
            decide_eq_of_iff (by omega)]
          exact hmd_bound
        rw [bool_if_false_eq_self hmd_bound']
        rw [hrst_e]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        simp only [hodd_true, hepsum_odd, hep0, Nat.add_zero, Nat.zero_add, Nat.mul_zero, Bool.true_and]
        rw [show decide (2 * c' + 4 ≥ a - 1) = decide (a ≤ 2 * (c' + 1) + 3) from
          decide_eq_of_iff (by omega)]
        by_cases h_le : a ≤ 2 * (c' + 1) + 3
        · rw [if_pos h_le, hrst_b] at hodd_branch
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel] at hodd_branch
          rw [if_pos (decide_eq_true h_le)]
          have hp5_eq : hasP5 (.p3z a :: ls) = hasP5 ls := rfl
          have hpsuf_eq : p5Suf (.p3z a :: ls) = p5Suf ls := rfl
          rw [hp5_eq, hpsuf_eq]
          rw [show decide (a - 1 ≥ 36) = decide (a ≥ 37) from decide_eq_of_iff (by omega)]
          rw [show decide (a - 1 ≥ 16) = decide (a ≥ 17) from decide_eq_of_iff (by omega)]
          rw [show decide (a - 1 ≥ 14 ∧ c' ≥ 7) = decide (a ≥ 15 ∧ c' ≥ 7) from
            decide_eq_of_iff (by omega)]
          rw [show decide (ds = [] ∧ c' = 1 ∧ a - 1 = 2 ∧ preP5Val (.p3z a :: ls) ≥ 16 ∧ z0 (p5Suf ls) ≥ 38) =
              decide (ds = [] ∧ c' = 1 ∧ a = 3 ∧ preP5Val (.p3z a :: ls) ≥ 16 ∧ z0 (p5Suf ls) ≥ 38) from
            decide_eq_of_iff ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, by omega, h4, h5⟩,
              fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, by omega, h4, h5⟩⟩]
          exact hodd_branch
        · rw [decide_eq_false h_le]; rfl
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_neg ha] at hf
      rw [if_pos rfl]
      by_cases hrst : a = 1 ∧ c' = 0 ∧ ds = []
      · rcases hrst with ⟨rfl, rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl, rfl⟩] at hf
        rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]
        dsimp only [drop1L]
        cases ls <;> exact hf
      · rw [if_neg (fun ⟨h1, h2, h3⟩ => hrst ⟨h1, by omega, h3⟩), if_neg (Nat.succ_ne_zero c')] at hf
        have hnot_e : ¬((0 : Nat) = 0 ∧ c' = 0 ∧ ds = [] ∧ isHeadP3z1 (.p3z a :: ls) = true) := by
          dsimp [isHeadP3z1]
          by_cases ha1 : a = 1
          · subst ha1
            exact fun ⟨_, hc0, hds, _⟩ => hrst ⟨rfl, hc0, hds⟩
          · simp [ha1]
        rw [if_neg hnot_e]
        have hm_eq : 2 * c' + 4 = 2 * (c' + 1) + 2 := by omega
        rw [hm_eq]
        exact hf

lemma ValidEvenLs_p5Suf (ls : List LTok) (heven : ValidEvenLs ls = true) (hp5 : hasP5 ls = true) :
    z0 (p5Suf ls) ≥ 18 ∧ ValidP5Chain (p5Suf ls) = true := by
  induction ls with
  | nil => cases hp5
  | cons tok rest ih =>
    cases tok with
    | p5 =>
      dsimp [ValidEvenLs, p5Suf] at heven ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at heven
      exact heven
    | p3z m =>
      dsimp [ValidEvenLs] at heven
      dsimp [hasP5, p5Suf] at hp5 ⊢
      split_ifs at heven with hm
      · exact ih heven hp5
      · cases rest with
        | nil => cases hp5
        | cons t2 s2 =>
          cases t2 with
          | p5 =>
            dsimp [ValidAfterOdd] at heven
            simp only [Bool.and_eq_true, decide_eq_true_eq] at heven
            exact heven
          | p3z m2 =>
            cases s2 with
            | nil => cases heven
            | cons t3 s3 =>
              cases t3 with
              | p3z _ => cases heven
              | p5 =>
                dsimp [ValidAfterOdd] at heven
                simp only [Bool.and_eq_true, decide_eq_true_eq] at heven
                exact heven

lemma ValidP5Chain_p3z_p5 (m : Nat) (suf : List LTok) (hz : z0 suf ≥ 18) (hv : ValidP5Chain suf = true) :
    ValidP5Chain (.p3z m :: .p5 :: suf) = true := by
  cases m with
  | zero => dsimp [ValidP5Chain]; simp [hz, hv]
  | succ m' => dsimp [ValidP5Chain]; simp [hz, hv]

lemma ValidP5Chain_of_ValidEvenLs_z0Rep (ls : List LTok)
    (heven : ValidEvenLs ls = true) (hpref : prefSumW ls = 0)
    (hmd : MustDrain ls = false) (hnp5 : isHeadP5 ls = false) :
    ValidP5Chain ls = true ∧ z0 ls ≥ epW ls := by
  obtain ⟨hls, _⟩ := ls_eq_z0Rep_of_prefSumW_zero ls heven hpref hmd hnp5
  cases hp5 : hasP5 ls with
  | false =>
    rw [hp5, if_neg Bool.false_ne_true] at hls
    refine ⟨?_, ?_⟩
    · rw [hls, ValidP5Chain_z0Rep]; rfl
    · have hz := congrArg z0 hls
      rw [z0_z0Rep] at hz; dsimp [z0] at hz; omega
  | true =>
    rw [hp5, if_pos rfl] at hls
    obtain ⟨hz18, hv⟩ := ValidEvenLs_p5Suf ls heven hp5
    refine ⟨?_, ?_⟩
    · rw [hls, ValidP5Chain_z0Rep]
      exact ValidP5Chain_p3z_p5 _ _ hz18 hv
    · have hz := congrArg z0 hls
      rw [z0_z0Rep] at hz; omega

lemma GoodDs_d1_valid {d : Nat} (hd : d ≥ 3) (h : GoodDs [d] = true) : d ≥ 8 := by
  dsimp [GoodDs, GoodDsAux, GoodDs1] at h
  simp only [decide_eq_true_eq] at h
  omega

lemma GoodDs_pair_d2_cases {d d2 : Nat} {ds2 : List Nat} (h : GoodDs (d :: d2 :: ds2) = true) :
    (d2 = 0 ∧ ds2 = [] ∧ d ≥ 8) ∨
    (d2 = 1 ∧ ds2 = [] ∧ (d = 3 ∨ d ≥ 25)) ∨
    (d2 ≥ 3 ∧ d ≥ 17 ∧ GoodDs (d2 :: ds2) = true ∧
      (d % 2 = 0 ∧ d ≤ 2 * d2 + 4 → GoodDs ((d2 - 1) :: ds2) = true) ∧
      (d % 2 = 0 ∧ d + 14 ≤ 2 * d2 → GoodDs ((d2 - 2) :: ds2) = true)) := by
  cases ds2 with
  | nil =>
    dsimp [GoodDs, GoodDsAux, GoodDs2] at h
    by_cases h0 : d2 = 0
    · subst h0; simp only [↓reduceIte, decide_eq_true_eq] at h; exact Or.inl ⟨rfl, rfl, h⟩
    · by_cases h1 : d2 = 1
      · subst h1; simp only [Nat.one_ne_zero, ↓reduceIte, decide_eq_true_eq] at h; exact Or.inr (Or.inl ⟨rfl, rfl, h⟩)
      · by_cases h3 : d2 < 3
        · simp [h0, h1, h3] at h
        · rw [if_neg h0, if_neg h1, if_neg h3] at h
          rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
          rw [bool_if_false_eq_true] at h; rcases h with ⟨hd17_gd, h⟩
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_bool_eq_false] at hd17_gd
          rw [bool_if_false_eq_true] at h; rcases h with ⟨hsub1, hsub2⟩
          rw [bool_if_false_eq_true] at hsub2; rcases hsub2 with ⟨hsub2, _⟩
          refine Or.inr (Or.inr ⟨by omega, by omega, hd17_gd.2, ?_, ?_⟩)
          · intro hc1
            rw [decide_eq_true hc1, Bool.true_and, not_bool_eq_false] at hsub1
            exact hsub1
          · intro hc2
            rw [decide_eq_true hc2, Bool.true_and, not_bool_eq_false] at hsub2
            exact hsub2
  | cons d3 ds3 =>
    dsimp [GoodDs, GoodDsAux] at h
    by_cases h3 : d2 < 3
    · rw [if_pos h3] at h; cases h
    · rw [if_neg h3] at h
      rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
      rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
      rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
      rw [bool_if_false_eq_true] at h; rcases h with ⟨hd17_gd, h⟩
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_bool_eq_false] at hd17_gd
      rw [bool_if_false_eq_true] at h; rcases h with ⟨hsub1, hsub2⟩
      rw [bool_if_false_eq_true] at hsub2; rcases hsub2 with ⟨hsub2, _⟩
      refine Or.inr (Or.inr ⟨by omega, by omega, hd17_gd.2, ?_, ?_⟩)
      · intro hc1
        rw [decide_eq_true hc1, Bool.true_and, not_bool_eq_false] at hsub1
        exact hsub1
      · intro hc2
        rw [decide_eq_true hc2, Bool.true_and, not_bool_eq_false] at hsub2
        exact hsub2

lemma GoodDs_d31 {d : Nat} (h : GoodDs [d, 3, 1] = true) : d ≥ 19 := by
  dsimp [GoodDs, GoodDsAux] at h
  by_contra hlt
  have hdec : decide (3 = 3 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ d < 19) = true := decide_eq_true ⟨rfl, rfl, rfl, by omega⟩
  rw [if_pos hdec] at h
  cases h

lemma GoodDs_d_ge25_1 {d d2 : Nat} (hd2 : d2 ≥ 25) (h : GoodDs [d, d2, 1] = true) : d ≥ 39 := by
  dsimp [GoodDs, GoodDsAux] at h
  by_contra hlt
  have hdec : decide (d2 ≥ 25 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ d < 39) = true := decide_eq_true ⟨hd2, rfl, rfl, by omega⟩
  rw [if_neg (by omega)] at h
  rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
  rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
  rw [if_pos hdec] at h
  cases h

lemma GoodDs_isOddDrainDs_ge19 {d2 : Nat} {ds2 : List Nat} (hd2 : d2 ≥ 3)
    (hod : isOddDrainDs ds2 = true) (h : GoodDs (d2 :: ds2) = true) : d2 ≥ 19 := by
  cases ds2 with
  | nil => cases hod
  | cons d3 ds3 =>
    cases ds3 with
    | nil =>
      dsimp [isOddDrainDs] at hod
      dsimp [GoodDs, GoodDsAux, GoodDs2] at h
      have hd3 : d3 ≥ 3 := by
        dsimp [isOddDrain1] at hod; simp only [decide_eq_true_eq] at hod; omega
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
      by_contra hlt
      have hdec : (isOddDrain1 d3 && decide (d2 < 19)) = true := by simp [hod, show d2 < 19 by omega]
      rw [if_pos hdec] at h; cases h
    | cons d4 ds4 =>
      dsimp [GoodDs, GoodDsAux] at h
      have hd3 : d3 ≥ 3 := by
        cases ds4 with
        | nil =>
          cases d4 with
          | zero => dsimp [isOddDrainDs, isOddDrain1] at hod; simp only [decide_eq_true_eq] at hod; omega
          | succ _ => cases hod
        | cons _ _ =>
          cases d4 <;> cases hod
      rw [if_neg (by omega)] at h
      rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
      by_contra hlt
      have hdec : (isOddDrainDs (d3 :: d4 :: ds4) && decide (d2 < 19)) = true := by simp [hod, show d2 < 19 by omega]
      rw [if_pos hdec] at h; cases h

lemma GoodPhiW_of_GoodDs_sub2 {d2 : Nat} {ds2 : List Nat} (hd2 : d2 ≥ 3) (h : GoodDs (d2 :: ds2) = true) :
    GoodPhiW (d2 - 2) ds2 false = true := by
  cases ds2 with
  | nil =>
    have hd8 := GoodDs_d1_valid hd2 h
    dsimp [GoodPhiW]; simp; omega
  | cons d3 ds3 =>
    rcases GoodDs_pair_d2_cases h with ⟨rfl, rfl, hd8⟩ | ⟨rfl, rfl, hd_or⟩ | ⟨hd3_ge3, hd2_17, _, _, _⟩
    · dsimp [GoodPhiW]; simp; omega
    · dsimp [GoodPhiW]; simp; omega
    · dsimp [GoodPhiW]
      rw [if_neg (by intro heq; injection heq with h1 _; omega)]
      rw [if_neg (by intro heq; injection heq with h1 _; omega)]
      rw [if_neg (by intro heq; injection heq with h1 _; omega)]
      by_cases h_25 : (match d3 :: ds3 with | [d, 1] => decide (d ≥ 25) | _ => false) = true
      · rw [if_pos h_25]
        cases ds3 with
        | nil => cases h_25
        | cons d4 ds4 =>
          cases ds4 with
          | nil =>
            cases d4 with
            | zero => cases h_25
            | succ d4' =>
              cases d4' with
              | zero =>
                have hd3_25 : d3 ≥ 25 := of_decide_eq_true h_25
                have hd39 := GoodDs_d_ge25_1 hd3_25 h
                simp; omega
              | succ _ => cases h_25
          | cons _ _ =>
            cases d4 with
            | zero => cases h_25
            | succ d4' => cases d4' <;> cases h_25
      · rw [if_neg h_25]
        by_cases hod : isOddDrainDs (d3 :: ds3) = true
        · rw [if_pos hod]
          have hd19 := GoodDs_isOddDrainDs_ge19 hd2 hod h
          simp; omega
        · rw [if_neg hod]
          simp; omega

lemma checkChainAux_B_ge3_c0_ok_ge22 (fuel a : Nat) (suf : List LTok) (ha : a ≥ 22) :
    checkChainAux fuel true (.p3z a :: .p5 :: suf) 0 0 2 [] = true := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hdec : decide (2 ≥ 0 + epSum (.p3z a :: .p5 :: suf)) = false := by
      dsimp [epSum]; split_ifs <;> (rw [decide_eq_false_iff_not]; omega)
    have hnp5 : isHeadP5 (.p3z a :: .p5 :: suf) = false := rfl
    have hepw0 : epW (.p3z a :: .p5 :: suf) = 0 := by
      dsimp [epW]; split_ifs <;> rfl
    dsimp only [checkChainAux]
    rw [hdec, hnp5, hepw0]
    simp

lemma GoodDs_tail_any {d : Nat} {ds : List Nat} (h : GoodDs (d :: ds) = true) :
    GoodDs ds = true ∧ ds ≠ [2] := by
  cases ds with
  | nil => exact ⟨rfl, by decide⟩
  | cons d2 ds2 =>
    rcases GoodDs_pair_d2_cases h with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨hd2_3, _, hgd2, _, _⟩
    · exact ⟨rfl, by decide⟩
    · exact ⟨rfl, by decide⟩
    · exact ⟨hgd2, by intro heq; injection heq with h1 _; omega⟩

lemma step_Inv_ModeB_b2_mge2 (ls : List LTok) (m'' : Nat) (ds : List Nat)
    (hinv : Inv (.ModeB_b2 ls (m'' + 2) ds)) :
    Inv (nextState (.ModeB_b2 ls (m'' + 2) ds)) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨_, heven⟩
  rw [if_pos (show m'' + 2 ≥ 2 by omega)] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨rfl, hm4⟩, hp5⟩
  cases ls with
  | nil => cases hp5
  | cons tok suf =>
    cases tok with
    | p3z _ => cases hp5
    | p5 =>
      dsimp [ValidEvenLs] at heven
      simp only [Bool.and_eq_true, decide_eq_true_eq] at heven
      rcases heven with ⟨hz18, hvp5⟩
      have hm'3 : m'' + 1 ≥ 3 := by omega
      have h_eq_m : m'' + 2 = (m'' + 1) + 1 := rfl
      rw [h_eq_m]
      dsimp only [nextState]
      have hvp5' : ValidP5Chain (.p3z (m'' + 1) :: .p5 :: suf) = true :=
        ValidP5Chain_p3z_p5 (m'' + 1) suf hz18 hvp5
      have hcond : ([] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
          isP3zP5 (.p3z (m'' + 1) :: .p5 :: suf) = true ∧
          headP3zVal (.p3z (m'' + 1) :: .p5 :: suf) ≥ 3 :=
        ⟨rfl, rfl, rfl, rfl, hm'3⟩
      refine ⟨?_, ?_⟩
      · dsimp [invCore, GoodDs, checkDs2, checkDs1Phi1]
        rw [hvp5']
        simp [hcond]
      · intro fuel
        have hf := hch fuel
        dsimp [invChain] at hf ⊢
        rw [if_pos hcond]
        dsimp [headP3zVal, drop2L, drop1L] at hf ⊢
        have hm_sub : m'' + 1 - 2 = m'' + 2 - 3 := by omega
        rw [hm_sub]
        exact hf

lemma step_Inv_ModeB_b2_m1 (ls : List LTok) (ds : List Nat)
    (hinv : Inv (.ModeB_b2 ls 1 ds)) :
    Inv (nextState (.ModeB_b2 ls 1 ds)) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨⟨hgd, hds2⟩, hds1⟩, heven⟩
  rw [if_neg (show ¬((1 : Nat) ≥ 2) by omega)] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hok_phi, hc⟩
  rw [not_bool_eq_false] at hok_phi
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hmd_bound, _⟩
  by_cases h_emp : ds = [] ∧ epW ls = 0
  · rcases h_emp with ⟨rfl, hepw0⟩
    rw [if_pos ⟨rfl, hepw0⟩] at hok_phi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
    rcases hok_phi with ⟨⟨_, hp3zp5⟩, hm0_18, hz38⟩
    have h_ls : ∃ m0 suf, ls = .p3z m0 :: .p5 :: suf := by
      cases ls with
      | nil => cases hp3zp5
      | cons t1 r1 =>
        cases t1 with
        | p5 => cases hp3zp5
        | p3z m0 =>
          cases r1 with
          | nil => cases hp3zp5
          | cons t2 suf =>
            cases t2 with
            | p3z _ => cases hp3zp5
            | p5 => exact ⟨m0, suf, rfl⟩
    obtain ⟨m0, suf, rfl⟩ := h_ls
    dsimp [headP3zVal, p5Suf] at hm0_18 hz38
    obtain ⟨hz18, hvp5⟩ := ValidEvenLs_p5Suf (.p3z m0 :: .p5 :: suf) heven rfl
    dsimp [p5Suf] at hz18 hvp5
    dsimp only [nextState]
    have hvp5' : ValidP5Chain (.p3z 0 :: .p3z m0 :: .p5 :: suf) = true := by
      dsimp [ValidP5Chain]; exact ValidP5Chain_p3z_p5 m0 suf hz18 hvp5
    have hz0_eq : z0 (.p3z 0 :: .p3z m0 :: .p5 :: suf) = 1 := by
      obtain ⟨m0', rfl⟩ : ∃ m0', m0 = m0' + 1 := ⟨m0 - 1, by omega⟩
      rfl
    have hdrop_eq : dropZ0 (.p3z 0 :: .p3z m0 :: .p5 :: suf) = .p3z m0 :: .p5 :: suf := by
      obtain ⟨m0', rfl⟩ : ∃ m0', m0 = m0' + 1 := ⟨m0 - 1, by omega⟩
      rfl
    have hcond1_f : ¬(([] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
        isP3zP5 (.p3z 0 :: .p3z m0 :: .p5 :: suf) = true ∧
        headP3zVal (.p3z 0 :: .p3z m0 :: .p5 :: suf) ≥ 3) := by
      dsimp [headP3zVal]; omega
    have hcond2 : ([] : List Nat) = [] ∧
        ((1 = 1 ∧ 1 = 1 ∧ z0 (.p3z 0 :: .p3z m0 :: .p5 :: suf) = 1) ∨
          (1 = 3 ∧ 1 = 2 ∧ z0 (.p3z 0 :: .p3z m0 :: .p5 :: suf) = 0)) ∧
        isP3zP5 (dropZ0 (.p3z 0 :: .p3z m0 :: .p5 :: suf)) = true ∧
        headP3zVal (dropZ0 (.p3z 0 :: .p3z m0 :: .p5 :: suf)) ≥ 18 ∧
        z0 (p5Suf (.p3z 0 :: .p3z m0 :: .p5 :: suf)) ≥ 38 := by
      rw [hz0_eq, hdrop_eq]
      exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩, rfl, hm0_18, hz38⟩
    refine ⟨?_, ?_⟩
    · have h_g : (!GoodDs [] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: .p3z m0 :: .p5 :: suf) 1 1 []) ||
          !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: .p3z m0 :: .p5 :: suf) 1 1 [])) = false := by
        dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
      dsimp only [invCore]
      rw [bool_if_false_eq_self h_g, if_neg (show ¬((1 : Nat) % 2 = 0) by decide)]
      rw [not_bool_if_false_eq_true hvp5']
      rw [not_decide_if_false_eq_true (by omega)]
      rw [if_neg hcond1_f, if_pos hcond2]
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_neg (show ¬((1 : Nat) ≥ 2) by omega), if_pos ⟨rfl, hepw0⟩] at hf
      simp only [Bool.and_eq_true] at hf
      rw [if_neg (by omega), if_neg hcond1_f, if_pos hcond2]
      rw [hdrop_eq]
      dsimp only [headP3zVal, drop2L] at hf ⊢
      have hm_sub : m0 - 4 = m0 - 4 - 2 * (1 - 1) := by omega
      rw [hm_sub]
      exact hf.2
  · rw [if_neg h_emp] at hok_phi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_phi
    rcases hok_phi with ⟨⟨_, hepw_pos, hpref_le⟩, hphiw⟩
    have hpref0 : prefSumW ls = 0 := by omega
    have hmd0 : MustDrain ls = false := by
      have hdec : decide (0 < 2 * 1 + epSum ls) = true := decide_eq_true (by omega)
      rw [hdec, Bool.and_true] at hmd_bound
      exact hmd_bound
    have hnp5 : isHeadP5 ls = false := by
      cases ls with
      | nil => rfl
      | cons t _ => cases t with | p3z _ => rfl | p5 => simp [epW] at hepw_pos
    obtain ⟨hvp5, hz0_ge⟩ := ValidP5Chain_of_ValidEvenLs_z0Rep ls heven hpref0 hmd0 hnp5
    obtain ⟨hls_z0_eq, hodd_imp_p5⟩ := ls_eq_z0Rep_of_prefSumW_zero ls heven hpref0 hmd0 hnp5
    have hep_ge_epw : ep ls ≥ epW ls := by
      have h_eq := congrArg ep hls_z0_eq
      cases hp : hasP5 ls with
      | false => rw [hp, if_neg Bool.false_ne_true, ep_z0Rep] at h_eq; omega
      | true => rw [hp, if_pos rfl, ep_z0Rep] at h_eq; omega
    have h_mrem_eq : 2 + epSum ls + (if hasOdd ls then 1 else 0) - (0 + 2) =
        epSum ls + (if hasOdd ls then 1 else 0) := by omega
    have hls_z0_symm : (if hasP5 ls = true then
          z0Rep (epW ls) (.p3z (epSum ls + (if hasOdd ls = true then 1 else 0)) :: .p5 :: p5Suf ls)
        else z0Rep (epW ls) []) = ls := hls_z0_eq.symm
    have h_tail_z0Rep : ∀ n, z0Rep n (if hasP5 ls = true then
          .p3z (epSum ls + (if hasOdd ls = true then 1 else 0)) :: .p5 :: p5Suf ls
        else []) =
        (if hasP5 ls = true then
          z0Rep n (.p3z (epSum ls + (if hasOdd ls = true then 1 else 0)) :: .p5 :: p5Suf ls)
        else z0Rep n []) := by
      intro n; cases hasP5 ls <;> rfl
    have hz_ls0 : z0Rep (0 + epW ls) (if hasP5 ls = true then
        .p3z (2 + epSum ls + (if hasOdd ls = true then 1 else 0) - (0 + 2)) :: .p5 :: p5Suf ls
      else []) = ls := by
      rw [Nat.zero_add, h_mrem_eq, h_tail_z0Rep, hls_z0_symm]
    have hz_ls1 : z0Rep (0 + epW ls + 1) (if hasP5 ls = true then
        .p3z (2 + epSum ls + (if hasOdd ls = true then 1 else 0) - (0 + 2)) :: .p5 :: p5Suf ls
      else []) = .p3z 0 :: ls := congrArg (LTok.p3z 0 :: ·) hz_ls0
    have hz_ls2 : z0Rep (0 + epW ls + 2) (if hasP5 ls = true then
        .p3z (2 + epSum ls + (if hasOdd ls = true then 1 else 0) - (0 + 2)) :: .p5 :: p5Suf ls
      else []) = .p3z 0 :: .p3z 0 :: ls := congrArg (LTok.p3z 0 :: ·) hz_ls1
    have hz_ls3 : z0Rep (0 + epW ls + 3) (if hasP5 ls = true then
        .p3z (2 + epSum ls + (if hasOdd ls = true then 1 else 0) - (0 + 2)) :: .p5 :: p5Suf ls
      else []) = .p3z 0 :: .p3z 0 :: .p3z 0 :: ls := congrArg (LTok.p3z 0 :: ·) hz_ls2
    have hdec_0_2 : decide (0 ≥ 2 + epSum ls) = false := decide_eq_false (by omega)
    have hch_step : ∀ fuel, invChain (fuel + 1) (.ModeB_b2 ls 1 ds) =
        checkChainAux (fuel + 1) true ls 0 2 0 ds := by
      intro fuel
      dsimp only [invChain]
      rw [if_neg (show ¬((1 : Nat) ≥ 2) by omega), if_neg h_emp]
    cases ds with
    | nil =>
      dsimp only [nextState]
      dsimp [GoodPhiW] at hphiw
      simp only [Bool.false_or, decide_eq_true_eq] at hphiw
      have hepw7 : epW ls ≥ 7 := by omega
      have hvp5' : ValidP5Chain (.p3z 0 :: ls) = true := hvp5
      have hz0' : z0 (.p3z 0 :: ls) = 1 + z0 ls := rfl
      have hcond1_f : ¬(([] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
          isP3zP5 (.p3z 0 :: ls) = true ∧ headP3zVal (.p3z 0 :: ls) ≥ 3) := by
        dsimp [headP3zVal]; omega
      have hcond2_f : ¬(([] : List Nat) = [] ∧
          ((1 = 1 ∧ 1 = 1 ∧ z0 (.p3z 0 :: ls) = 1) ∨ (1 = 3 ∧ 1 = 2 ∧ z0 (.p3z 0 :: ls) = 0)) ∧
          isP3zP5 (dropZ0 (.p3z 0 :: ls)) = true ∧
          headP3zVal (dropZ0 (.p3z 0 :: ls)) ≥ 18 ∧ z0 (p5Suf (.p3z 0 :: ls)) ≥ 38) := by
        rw [hz0']; omega
      refine ⟨?_, ?_⟩
      · have h_g : (!GoodDs [] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: ls) 1 1 []) ||
            !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: ls) 1 1 [])) = false := by
          dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
        dsimp only [invCore]
        rw [bool_if_false_eq_self h_g, if_neg (show ¬((1 : Nat) % 2 = 0) by decide)]
        rw [not_bool_if_false_eq_true hvp5']
        rw [not_decide_if_false_eq_true (by omega)]
        rw [if_neg hcond1_f, if_neg hcond2_f, hz0']
        have hkz17 : decide (1 + 2 * (1 + z0 ls) ≥ 17) = true := decide_eq_true (by omega)
        have hbase : decide (1 + (1 + z0 ls) ≥ 8 ∧ 1 + 2 * (1 + z0 ls) ≥ 15) = true := decide_eq_true ⟨by omega, by omega⟩
        rw [hbase, hkz17]
        simp
      · intro fuel
        have hf := hch (fuel + 1)
        rw [hch_step fuel] at hf
        dsimp only [checkChainAux] at hf
        rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
          if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
          if_pos (Or.inl rfl), if_neg (show ¬(0 + epW ls < 2) by omega), if_pos rfl, hz_ls1] at hf
        dsimp only [invChain]
        rw [if_neg (by omega), if_neg hcond1_f, if_neg hcond2_f]
        exact hf
    | cons d ds' =>
      cases d with
      | zero =>
        cases ds' with
        | cons d2 ds'' => have := GoodDs_pair_ge3 hgd; omega
        | nil =>
          dsimp only [nextState]
          dsimp [GoodPhiW] at hphiw
          simp only [decide_eq_true_eq] at hphiw
          have hepw7 : epW ls ≥ 7 := by omega
          have heven2 : ValidEvenLs (.p3z 0 :: .p3z 0 :: ls) = true := heven
          have hnp5_2 : isHeadP5 (.p3z 0 :: .p3z 0 :: ls) = false := rfl
          have hepw2 : epW (.p3z 0 :: .p3z 0 :: ls) = 2 + epW ls := by
            rw [epW_p3z_even_cons 0 _ rfl rfl, epW_p3z_even_cons 0 ls rfl hnp5]; omega
          have hpref2 : prefSumW (.p3z 0 :: .p3z 0 :: ls) = 0 := by
            rw [prefSumW_p3z_even_cons 0 _ rfl rfl, prefSumW_p3z_even_cons 0 ls rfl hnp5, hpref0]
          have hmd2 : MustDrain (.p3z 0 :: .p3z 0 :: ls) = false := hmd0
          have hep2 : ep (.p3z 0 :: .p3z 0 :: ls) = 2 + ep ls := by
            rw [ep_p3z_even_cons 0 _ rfl, ep_p3z_even_cons 0 ls rfl]; omega
          have hepsum2 : epSum (.p3z 0 :: .p3z 0 :: ls) = epSum ls := by dsimp [epSum]; omega
          have hodd2 : hasOdd (.p3z 0 :: .p3z 0 :: ls) = hasOdd ls := rfl
          have hp5_2 : hasP5 (.p3z 0 :: .p3z 0 :: ls) = hasP5 ls := rfl
          refine ⟨?_, ?_⟩
          · have h_g : (!GoodDs [] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: ls) 2 1 []) ||
                !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: ls) 2 1 [])) = false := by
              dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
            dsimp only [invCore]
            rw [bool_if_false_eq_self h_g, if_pos (show (2 : Nat) % 2 = 0 by decide)]
            rw [not_bool_if_false_eq_true heven2]
            rw [hpref2, not_decide_if_false_eq_true (by omega)]
            have hphiw2 : GoodPhiW (1 + epW (.p3z 0 :: .p3z 0 :: ls)) []
                (isHeadP3z1 (.p3z 0 :: .p3z 0 :: ls) && decide (2 = 0 ∧ 1 = 0 ∧ ([] : List Nat) = [])) = true := by
              rw [hepw2]; dsimp [GoodPhiW]; simp; omega
            have hok_phi2 : (if (!isHeadP5 (.p3z 0 :: .p3z 0 :: ls)) = true then
                (decide (([] : List Nat) = [] ∧ 1 + epW (.p3z 0 :: .p3z 0 :: ls) = 1) && MustDrain (.p3z 0 :: .p3z 0 :: ls) &&
                  decide (1 + ep (.p3z 0 :: .p3z 0 :: ls) = 1 ∧ 2 + epSum (.p3z 0 :: .p3z 0 :: ls) + 2 * ep (.p3z 0 :: .p3z 0 :: ls) = 2) &&
                  hasP5 (.p3z 0 :: .p3z 0 :: ls) && decide (preP5Val (.p3z 0 :: .p3z 0 :: ls) ≥ 16 ∧ z0 (p5Suf (.p3z 0 :: .p3z 0 :: ls)) ≥ 38)) ||
                  GoodPhiW (1 + epW (.p3z 0 :: .p3z 0 :: ls)) [] (isHeadP3z1 (.p3z 0 :: .p3z 0 :: ls) && decide (2 = 0 ∧ 1 = 0 ∧ ([] : List Nat) = []))
              else
                decide (1 = 0 ∧ ([] : List Nat) = [] ∧ 2 = 2) || (decide (1 ≥ 1) && GoodPhiW (1 - 1) [] false)) = true := by
              rw [if_pos (by rfl), hphiw2, Bool.or_true]
            rw [not_bool_if_false_eq_true hok_phi2]
            rw [hmd2, Bool.false_and, if_neg Bool.false_ne_true]
            have hrst_f : (decide ((2 : Nat) = 0 ∧ (1 : Nat) = 0 ∧ ([] : List Nat) = []) && isHeadP3z1 (.p3z 0 :: .p3z 0 :: ls)) = false := rfl
            rw [hrst_f]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            by_cases h_odd_c : (hasOdd (.p3z 0 :: .p3z 0 :: ls) && decide (2 * 1 + 4 ≥ 2 + epSum (.p3z 0 :: .p3z 0 :: ls))) = true
            · rw [if_pos h_odd_c]
              simp only [Bool.and_eq_true] at h_odd_c
              have hp5_t : hasP5 ls = true := by
                cases hp : hasP5 ls with
                | true => rfl
                | false => have := hodd_imp_p5 hp; rw [hodd2, this] at h_odd_c; cases h_odd_c.1
              have hgp : GoodPsi (1 + ep (.p3z 0 :: .p3z 0 :: ls)) [] = true := by
                dsimp [GoodPsi, GoodDs, GoodDsAux, GoodDs1]; simp; omega
              rw [hgp, hp5_2, hp5_t]
              simp
            · rw [if_neg h_odd_c]
          · intro fuel
            have hf := hch (fuel + 1)
            rw [hch_step fuel] at hf
            dsimp only [checkChainAux] at hf
            rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
              if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by decide),
              if_pos (Or.inr (Or.inl rfl)), if_neg (show ¬(0 + epW ls < 2) by omega),
              if_neg (by decide), if_pos rfl, hz_ls2] at hf
            dsimp only [invChain]
            rw [if_pos rfl, if_neg (by intro ⟨h1, _⟩; cases h1)]
            exact hf
      | succ d1 =>
        cases d1 with
        | zero =>
          cases ds' with
          | cons d2 ds'' => have := GoodDs_pair_ge3 hgd; omega
          | nil =>
            dsimp only [nextState]
            dsimp [GoodPhiW] at hphiw
            simp only [decide_eq_true_eq] at hphiw
            have hepw2_ge : epW ls ≥ 2 := by omega
            have heven3 : ValidEvenLs (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = true := heven
            have hepw3 : epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 3 + epW ls := by
              rw [epW_p3z_even_cons 0 _ rfl rfl, epW_p3z_even_cons 0 _ rfl rfl, epW_p3z_even_cons 0 ls rfl hnp5]; omega
            have hpref3 : prefSumW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 0 := by
              rw [prefSumW_p3z_even_cons 0 _ rfl rfl, prefSumW_p3z_even_cons 0 _ rfl rfl, prefSumW_p3z_even_cons 0 ls rfl hnp5, hpref0]
            have hmd3 : MustDrain (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = false := hmd0
            have hep3 : ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 3 + ep ls := by
              rw [ep_p3z_even_cons 0 _ rfl, ep_p3z_even_cons 0 _ rfl, ep_p3z_even_cons 0 ls rfl]; omega
            have hepsum3 : epSum (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = epSum ls := by dsimp [epSum]; omega
            have hodd3 : hasOdd (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = hasOdd ls := rfl
            have hp5_3 : hasP5 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = hasP5 ls := rfl
            refine ⟨?_, ?_⟩
            · have h_g : (!GoodDs [] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) 0 1 []) ||
                  !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) 0 1 [])) = false := by
                dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
              dsimp only [invCore]
              rw [bool_if_false_eq_self h_g, if_pos (show (0 : Nat) % 2 = 0 by decide)]
              rw [not_bool_if_false_eq_true heven3]
              rw [hpref3, not_decide_if_false_eq_true (by omega)]
              have hphiw3 : GoodPhiW (1 + epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) []
                  (isHeadP3z1 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (0 = 0 ∧ 1 = 0 ∧ ([] : List Nat) = [])) = true := by
                rw [hepw3]; dsimp [GoodPhiW]; simp; omega
              have hok_phi3 : (if (!isHeadP5 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) = true then
                  (decide (([] : List Nat) = [] ∧ 1 + epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 1) && MustDrain (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) &&
                    decide (1 + ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 1 ∧ 0 + epSum (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) + 2 * ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 2) &&
                    hasP5 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (preP5Val (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) ≥ 16 ∧ z0 (p5Suf (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) ≥ 38)) ||
                    GoodPhiW (1 + epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) [] (isHeadP3z1 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (0 = 0 ∧ 1 = 0 ∧ ([] : List Nat) = []))
                else
                  decide (1 = 0 ∧ ([] : List Nat) = [] ∧ 0 = 2) || (decide (1 ≥ 1) && GoodPhiW (1 - 1) [] false)) = true := by
                rw [if_pos (by rfl), hphiw3, Bool.or_true]
              rw [not_bool_if_false_eq_true hok_phi3]
              rw [hmd3, Bool.false_and, if_neg Bool.false_ne_true]
              have hrst_f : (decide ((0 : Nat) = 0 ∧ (1 : Nat) = 0 ∧ ([] : List Nat) = []) && isHeadP3z1 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) = false := rfl
              rw [hrst_f]
              simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
              by_cases h_odd_c : (hasOdd (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (2 * 1 + 4 ≥ 0 + epSum (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls))) = true
              · rw [if_pos h_odd_c]
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h_odd_c
                have hepw_ge3 : epW ls ≥ 3 := by
                  by_cases he2 : epW ls = 2
                  · dsimp [checkDs1Phi1] at hds1
                    simp only [he2, ne_eq, not_true_eq_false, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hds1
                    rw [hepsum3] at h_odd_c; omega
                  · omega
                have hp5_t : hasP5 ls = true := by
                  cases hp : hasP5 ls with
                  | true => rfl
                  | false => have := hodd_imp_p5 hp; rw [hodd3, this] at h_odd_c; cases h_odd_c.1
                have hgp : GoodPsi (1 + ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) [] = true := by
                  dsimp [GoodPsi, GoodDs, GoodDsAux, GoodDs1]; simp; omega
                rw [hgp, hp5_3, hp5_t]
                simp
              · rw [if_neg h_odd_c]
            · intro fuel
              have hf := hch (fuel + 1)
              rw [hch_step fuel] at hf
              dsimp only [checkChainAux] at hf
              rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by decide),
                if_pos (Or.inr (Or.inr (Or.inl rfl))), if_neg (show ¬(0 + epW ls < 2) by omega),
                if_neg (by decide), if_neg (by decide), if_pos rfl, hz_ls3] at hf
              dsimp only [invChain]
              rw [if_pos rfl, if_neg (by intro ⟨_, h1, _⟩; cases h1)]
              exact hf
        | succ d2_idx =>
          cases d2_idx with
          | zero =>
            have hd_eq : 0 + 1 + 1 = 2 := rfl
            rw [hd_eq] at *
            cases ds' with
            | cons d2 ds'' => have := GoodDs_pair_ge3 hgd; omega
            | nil =>
              dsimp only [nextState]
              dsimp [GoodPhiW] at hphiw
              simp only [decide_eq_true_eq] at hphiw
              have hepw5 : epW ls = 5 := by omega
              have hvp5' : ValidP5Chain (.p3z 0 :: .p3z 0 :: ls) = true := hvp5
              have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by change 1 + (1 + z0 ls) = 2 + z0 ls; omega
              have hcond1_f : ¬(([0] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
                  isP3zP5 (.p3z 0 :: .p3z 0 :: ls) = true ∧ headP3zVal (.p3z 0 :: .p3z 0 :: ls) ≥ 3) := by
                intro ⟨h1, _⟩; cases h1
              have hcond2_f : ¬(([0] : List Nat) = [] ∧
                  ((1 = 1 ∧ 1 = 1 ∧ z0 (.p3z 0 :: .p3z 0 :: ls) = 1) ∨ (1 = 3 ∧ 1 = 2 ∧ z0 (.p3z 0 :: .p3z 0 :: ls) = 0)) ∧
                  isP3zP5 (dropZ0 (.p3z 0 :: .p3z 0 :: ls)) = true ∧
                  headP3zVal (dropZ0 (.p3z 0 :: .p3z 0 :: ls)) ≥ 18 ∧ z0 (p5Suf (.p3z 0 :: .p3z 0 :: ls)) ≥ 38) := by
                intro ⟨h1, _⟩; cases h1
              refine ⟨?_, ?_⟩
              · have h_g : (!GoodDs [0] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: ls) 1 1 [0]) ||
                    !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: ls) 1 1 [0])) = false := by
                  dsimp [GoodDs, GoodDsAux, GoodDs1, checkDs2, checkDs1Phi1]; simp
                dsimp only [invCore]
                rw [bool_if_false_eq_self h_g, if_neg (show ¬((1 : Nat) % 2 = 0) by decide)]
                rw [not_bool_if_false_eq_true hvp5']
                rw [not_decide_if_false_eq_true (by omega)]
                rw [if_neg hcond1_f, if_neg hcond2_f, hz0_2]
                have hbase : decide (1 + (2 + z0 ls) ≥ 8 ∧ 1 + 2 * (2 + z0 ls) ≥ 15) = true := decide_eq_true ⟨by omega, by omega⟩
                have hod_f : isOddDrainDs [0] = false := rfl
                rw [hbase, hod_f]
                by_cases hz6 : z0 ls ≥ 6
                · have hkz17 : decide (1 + 2 * (2 + z0 ls) ≥ 17) = true := decide_eq_true (by omega)
                  rw [hkz17]; simp
                · have hcz_lt9 : decide (([0] = [] ∨ [0] = [0]) ∧ 1 + (2 + z0 ls) ≥ 9 ∨ false = true) = false :=
                    decide_eq_false (by intro h_or; rcases h_or with ⟨_, h9⟩ | h_f; omega; cases h_f)
                  rw [hcz_lt9]; simp
              · intro fuel
                have hf := hch (fuel + 1)
                rw [hch_step fuel] at hf
                dsimp only [checkChainAux] at hf
                rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                  if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by decide),
                  if_pos (Or.inr (Or.inr (Or.inr rfl))), if_neg (show ¬(0 + epW ls < 2) by omega),
                  if_neg (by decide), if_neg (by decide), if_neg (by decide), hz_ls2] at hf
                dsimp only [invChain]
                rw [if_neg (show ¬((1 : Nat) % 2 = 0) by decide), if_neg hcond1_f, if_neg hcond2_f]
                exact hf
          | succ m'' =>
            have hd_eq : m'' + 1 + 1 + 1 = m'' + 3 := rfl
            rw [hd_eq] at *
            cases ds' with
            | nil =>
              dsimp only [nextState]
              have hd8 := GoodDs_d1_valid (by omega) hgd
              dsimp [GoodPhiW] at hphiw
              have hepw_req : epW ls ≥ if isOddDrainDs [m'' + 3] then 18 else 16 := by
                by_cases hod : isOddDrainDs [m'' + 3] = true
                · rw [if_pos hod] at hphiw ⊢; simp only [decide_eq_true_eq] at hphiw; omega
                · rw [if_neg hod] at hphiw ⊢; simp only [decide_eq_true_eq] at hphiw; omega
              have hepw16 : epW ls ≥ 16 := by split_ifs at hepw_req <;> omega
              refine ⟨?_, ?_⟩
              · dsimp [invCore, isHeadP5, drop1L]
                have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by change 1 + (1 + z0 ls) = 2 + z0 ls; omega
                have hvp5' : ValidP5Chain (.p3z 0 :: .p3z 0 :: ls) = true := hvp5
                rw [hz0_2, hvp5']
                simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨by omega, by omega⟩
              · intro fuel
                have hf := hch (fuel + 1)
                rw [hch_step fuel] at hf
                dsimp only [checkChainAux] at hf
                rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                  if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos (decide_eq_true hd8),
                  if_neg (show ¬(0 + epW ls < if isOddDrainDs [m'' + 3] = true then 18 else 16) by omega),
                  hz_ls2] at hf
                have h_hnat : headNat [m'' + 3] = m'' + 3 := rfl
                have hm_sub : m'' + 3 - 7 = m'' - 4 := by omega
                rw [h_hnat, hm_sub] at hf
                dsimp only [invChain, drop1L, checkResetSufAux]
                exact hf
            | cons d2 ds'' =>
              cases d2 with
              | zero =>
                rcases GoodDs_pair_d2_cases hgd with ⟨_, rfl, hd8⟩ | ⟨h_abs, _⟩ | ⟨h_abs, _⟩
                · obtain ⟨m4, rfl⟩ : ∃ m4, m'' = m4 + 2 := ⟨m'' - 2, by omega⟩
                  have hd_eq2 : m4 + 2 + 3 = m4 + 5 := rfl
                  rw [hd_eq2] at *
                  dsimp only [nextState]
                  dsimp [GoodPhiW] at hphiw
                  have hepw_req : epW ls ≥ if isOddDrainDs [m4 + 5, 0] then 18 else 16 := by
                    by_cases hod : isOddDrainDs [m4 + 5, 0] = true
                    · rw [if_pos hod] at hphiw ⊢; simp only [decide_eq_true_eq] at hphiw; omega
                    · rw [if_neg hod] at hphiw ⊢; simp only [decide_eq_true_eq] at hphiw; omega
                  have hepw16 : epW ls ≥ 16 := by split_ifs at hepw_req <;> omega
                  have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by change 1 + (1 + z0 ls) = 2 + z0 ls; omega
                  have heven_new : ValidEvenLs (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true := by
                    dsimp [ValidEvenLs, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                  refine ⟨?_, ?_⟩
                  · have h_g : (!GoodDs [] || !checkDs2 (.ModeB_b2 (.p5 :: .p3z 0 :: .p3z 0 :: ls) (m4 + 1) []) ||
                        !checkDs1Phi1 (.ModeB_b2 (.p5 :: .p3z 0 :: .p3z 0 :: ls) (m4 + 1) []) ||
                        !ValidEvenLs (.p5 :: .p3z 0 :: .p3z 0 :: ls)) = false := by
                      dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp [heven_new]
                    dsimp only [invCore]
                    rw [bool_if_false_eq_self h_g, if_pos (show m4 + 1 ≥ 2 by omega)]
                    dsimp [isHeadP5]; simp; omega
                  · intro fuel
                    have hf := hch (fuel + 1)
                    rw [hch_step fuel] at hf
                    dsimp only [checkChainAux] at hf
                    have h_m_t : (match [m4 + 5, 0] with | [d] => decide (d ≥ 8) | [d, 0] => decide (d ≥ 8) | _ => false) = decide (m4 + 5 ≥ 8) := rfl
                    rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false, h_m_t,
                      if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos (decide_eq_true hd8),
                      if_neg (show ¬(0 + epW ls < if isOddDrainDs [m4 + 5, 0] = true then 18 else 16) by omega),
                      hz_ls2] at hf
                    have h_hnat : headNat [m4 + 5, 0] = m4 + 5 := rfl
                    have hm_sub : m4 + 5 - 7 = m4 + 1 - 3 := by omega
                    rw [h_hnat, hm_sub] at hf
                    dsimp only [invChain, drop1L, checkResetSufAux]
                    rw [if_pos (show m4 + 1 ≥ 2 by omega)]
                    exact hf
                · cases h_abs
                · omega
              | succ c' =>
                dsimp only [nextState]
                have h_m_f : (match ((m'' + 3) :: (c' + 1) :: ds'') with | [d] => decide (d ≥ 8) | [d, 0] => decide (d ≥ 8) | _ => false) = false := by
                  cases ds'' <;> rfl
                have h_or_f : ¬((m'' + 3) :: (c' + 1) :: ds'' = [] ∨
                    (m'' + 3) :: (c' + 1) :: ds'' = [0] ∨
                    (m'' + 3) :: (c' + 1) :: ds'' = [1] ∨
                    (m'' + 3) :: (c' + 1) :: ds'' = [2]) := by simp
                dsimp [GoodPhiW] at hphiw
                have hepw16 : epW ls ≥ 16 := by
                  split_ifs at hphiw <;> (simp only [decide_eq_true_eq] at hphiw; omega)
                have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by change 1 + (1 + z0 ls) = 2 + z0 ls; omega
                have heven_new : ValidEvenLs (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true := by
                  dsimp [ValidEvenLs, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                rcases GoodDs_pair_d2_cases hgd with ⟨h_abs, _⟩ | ⟨hc'0, rfl, hd_or⟩ | ⟨hc'2, hd17, hgd_tail, hsub1, hsub2⟩
                · cases h_abs
                · have hc'_z : c' = 0 := by omega
                  subst hc'_z
                  have h_d_cond1 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 ≤ 2 * 1 + 4 ∧ GoodDs [1 - 1] = false) := by
                    intro ⟨_, _, h_f⟩; cases h_f
                  have h_d_cond2 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 + 14 ≤ 2 * 1 ∧ GoodDs [1 - 2] = false) := by omega
                  rcases hd_or with hm''0 | hd25
                  · have hm''_z : m'' = 0 := by omega
                    subst hm''_z
                    refine ⟨?_, ?_⟩
                    · have h_g : (!GoodDs [] || !checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) 0 0 []) ||
                          !checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) 0 0 [])) = false := by
                        dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
                      dsimp only [invCore]
                      rw [bool_if_false_eq_self h_g, if_pos (by decide), not_bool_if_false_eq_true heven_new]
                      dsimp [isHeadP5, MustDrain, hasOdd]
                    · intro fuel
                      have hf := hch (fuel + 1)
                      rw [hch_step fuel] at hf
                      dsimp only [checkChainAux] at hf
                      rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false, h_m_f,
                        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                        if_neg h_or_f, if_pos ⟨by omega, by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                        if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                        if_neg (show ¬((1 : Nat) = 1 ∧ ([] : List Nat) = [] ∧ 0 + 3 ≥ 25) by omega)] at hf
                      dsimp only [invChain]
                      rw [if_pos (by decide), if_neg (by intro ⟨_, _, h22⟩; omega)]
                      exact hf
                  · have hm''22 : m'' ≥ 22 := by omega
                    have hepw36 : epW ls ≥ 36 := by
                      have h_m25_t : (match ([m'' + 3, 1] : List Nat) with | [d, 1] => decide (d ≥ 25) | _ => false) = true :=
                        decide_eq_true hd25
                      rw [h_m25_t, if_pos (by rfl)] at hphiw
                      simp only [decide_eq_true_eq] at hphiw; omega
                    have hz38 : z0 (.p3z 0 :: .p3z 0 :: ls) ≥ 38 := by omega
                    refine ⟨?_, ?_⟩
                    · have h_g : (!GoodDs [] || !checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' 0 []) ||
                          !checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' 0 [])) = false := by
                        dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
                      dsimp only [invCore]
                      rw [bool_if_false_eq_self h_g]
                      by_cases hm_ev : m'' % 2 = 0
                      · rw [if_pos hm_ev, not_bool_if_false_eq_true heven_new]
                        dsimp [isHeadP5, p5Suf, MustDrain, hasOdd]
                        simp [hm''22, hz38]
                      · have hm''23 : m'' ≥ 23 := by omega
                        have heven_odd : ValidEvenLs (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) = true := by
                          dsimp [ValidEvenLs]; rw [if_neg hm_ev]
                          dsimp [ValidAfterOdd, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                        rw [if_neg hm_ev]
                        have h_c0_ok : ¬((0 : Nat) = 0 ∧ (!decide (([] : List Nat) = [] ∧ m'' ≥ 23 ∧
                            isHeadP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true ∧
                            z0 (p5Suf (.p5 :: .p3z 0 :: .p3z 0 :: ls)) ≥ 38)) = true) := by
                          dsimp [isHeadP5, p5Suf]; simp [hm''23, hz38]
                        rw [if_neg h_c0_ok, not_bool_if_false_eq_true heven_odd]
                        have hmd_f : MustDrain (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) = false := by
                          dsimp [MustDrain]; split_ifs <;> rfl
                        rw [hmd_f, Bool.false_and, if_neg Bool.false_ne_true,
                          if_neg (show ¬(m'' ≤ 2 * 0 + 3) by omega)]; simp
                    · intro fuel
                      have hf := hch (fuel + 1)
                      rw [hch_step fuel] at hf
                      dsimp only [checkChainAux] at hf
                      rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false, h_m_f,
                        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                        if_neg h_or_f, if_pos ⟨by omega, by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                        if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                        if_pos ⟨rfl, rfl, hd25⟩] at hf
                      have h_ok_t := checkChainAux_B_ge3_c0_ok_ge22 fuel m'' (.p3z 0 :: .p3z 0 :: ls) hm''22
                      have hm_sub : m'' - 8 = m'' + 3 - 11 := by omega
                      dsimp only [invChain]
                      by_cases hm_ev : m'' % 2 = 0
                      · rw [if_pos hm_ev, if_pos ⟨rfl, rfl, hm''22⟩, h_ok_t, Bool.true_and]
                        dsimp only [drop1L]; rw [hm_sub]; exact hf
                      · rw [if_neg hm_ev, if_neg (show ¬(m'' = 1 ∧ (0 : Nat) = 1 ∧ ([] : List Nat) = []) by omega),
                          if_pos rfl, h_ok_t, Bool.true_and]
                        dsimp only [drop1L]; rw [hm_sub]; exact hf
                · obtain ⟨hgd_ds'', hds''_ne2⟩ := GoodDs_tail_any hgd_tail
                  have h_d_cond1 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 ≤ 2 * (c' + 1) + 4 ∧ GoodDs ((c' + 1 - 1) :: ds'') = false) := by
                    intro ⟨h1, h2, h3⟩; rw [hsub1 ⟨h1, h2⟩] at h3; cases h3
                  have h_d_cond2 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 + 14 ≤ 2 * (c' + 1) ∧ GoodDs ((c' + 1 - 2) :: ds'') = false) := by
                    intro ⟨h1, h2, h3⟩; rw [hsub2 ⟨h1, h2⟩] at h3; cases h3
                  have h_not_25_1 : ¬(c' + 1 = 1 ∧ ds'' = [] ∧ m'' + 3 ≥ 25) := by omega
                  have hds2' : checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'') = true := by
                    dsimp [checkDs2]; rw [if_pos hds''_ne2]
                  have hds1' : checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'') = true := by
                    dsimp [checkDs1Phi1]
                    by_cases h1 : ds'' = [1]
                    · subst h1
                      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
                      rcases GoodDs_pair_d2_cases hgd_tail with ⟨h_abs, _⟩ | ⟨_, _, hd_c_or⟩ | ⟨h_abs, _⟩
                      · cases h_abs
                      · rcases hd_c_or with hc'2_eq | hc'24
                        · have hc'_eq2 : c' = 2 := by omega
                          subst hc'_eq2
                          have hd19 := GoodDs_d31 hgd
                          by_cases hm_ev : m'' % 2 = 0
                          · rw [if_pos hm_ev, if_pos hm_ev]
                            dsimp [isHeadP5, hasP5, MustDrain, epSum]
                            rw [if_neg (by omega)]
                            simp; omega
                          · rw [if_neg hm_ev, if_neg hm_ev]
                            dsimp [isHeadP5, hasP5, MustDrain]
                            rw [if_pos (by omega)]
                            simp; omega
                        · by_cases hm_ev : m'' % 2 = 0
                          · rw [if_pos hm_ev]
                            have hip5 : isHeadP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true := rfl
                            rw [if_pos hip5]
                            have hne : decide (c' - 1 = 1) = false := decide_eq_false (by omega)
                            rw [hne]; rfl
                          · rw [if_neg hm_ev]
                            have hne : decide (c' = 2) = false := decide_eq_false (by omega)
                            rw [hne]; rfl
                      · omega
                    · simp [h1]
                  have hphiw_c' : GoodPhiW (c' - 1) ds'' false = true := by
                    have h_sub : c' - 1 = (c' + 1) - 2 := by omega
                    rw [h_sub]
                    exact GoodPhiW_of_GoodDs_sub2 hc'2 hgd_tail
                  refine ⟨?_, ?_⟩
                  · dsimp only [invCore]
                    have h_g : (!GoodDs ds'' || !checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'') ||
                        !checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'')) = false := by
                      simp [hgd_ds'', hds2', hds1']
                    rw [bool_if_false_eq_self h_g]
                    by_cases hm_ev : m'' % 2 = 0
                    · rw [if_pos hm_ev, not_bool_if_false_eq_true heven_new]
                      have hip5_f : (!isHeadP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls)) = false := rfl
                      rw [hip5_f, if_neg Bool.false_ne_true, if_neg (show c' ≠ 0 by omega), not_bool_if_false_eq_true hphiw_c']
                      rfl
                    · have heven_odd : ValidEvenLs (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) = true := by
                        dsimp [ValidEvenLs]; rw [if_neg hm_ev]
                        dsimp [ValidAfterOdd, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                      rw [if_neg hm_ev, if_neg (by intro ⟨hc0, _⟩; omega), not_bool_if_false_eq_true heven_odd]
                      have hrst_f : decide (m'' = 1 ∧ c' = 1 ∧ ds'' = []) = false :=
                        decide_eq_false (by intro ⟨_, hc1, _⟩; omega)
                      have hmd_f : MustDrain (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) = false := by
                        dsimp [MustDrain]; split_ifs <;> rfl
                      have hok_c1' : (if c' ≥ 1 then
                          if (!decide (m'' = 1 ∧ c' = 1 ∧ ds'' = [])) = true then
                            (decide (ds'' = [] ∧ c' = 2 ∧ m'' = 3) && MustDrain (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) &&
                              hasP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls) &&
                              decide (preP5Val (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) ≥ 16 ∧ z0 (p5Suf (.p5 :: .p3z 0 :: .p3z 0 :: ls)) ≥ 38)) ||
                              GoodPhiW (c' - 1) ds'' false
                          else isP3zGe1P5 (.p5 :: .p3z 0 :: .p3z 0 :: ls)
                        else true) = true := by
                        rw [if_pos (by omega), hrst_f, if_pos (by rfl), hphiw_c', Bool.or_true]
                      rw [not_bool_if_false_eq_true hok_c1', hmd_f, Bool.false_and, if_neg Bool.false_ne_true]
                      by_cases h_le : m'' ≤ 2 * c' + 3
                      · rw [if_pos h_le, hrst_f, if_neg Bool.false_ne_true]
                        have hgp : GoodPsi (c' - 1) ds'' = true := by
                          dsimp [GoodPsi]
                          have h_eq_c : c' - 1 + 1 = c' + 1 - 1 := by omega
                          rw [h_eq_c]
                          exact hsub1 ⟨by omega, by omega⟩
                        have h_not_8 : decide ((ds'' = [] ∨ ds'' = [0]) ∧ c' - 1 ≥ 8 ∧
                            ((!hasP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls)) = true ∨ false = true)) = false := by
                          dsimp [hasP5]; simp
                        rw [hgp, h_not_8]
                        simp only [Bool.true_and, Bool.not_false, Bool.true_or, Bool.and_true]
                        by_cases h_ds1 : (ds'' = [1] ∧ c' - 1 ≥ 24)
                        · rcases h_ds1 with ⟨rfl, hc'24⟩
                          have hd39 := GoodDs_d_ge25_1 (by omega) hgd
                          have hm37 : decide (m'' ≥ 37) = true := decide_eq_true (by omega)
                          rw [hm37, Bool.or_true]
                        · rw [decide_eq_false h_ds1]; rfl
                      · rw [if_neg h_le]
                  · intro fuel
                    have hf := hch (fuel + 1)
                    rw [hch_step fuel] at hf
                    dsimp only [checkChainAux] at hf
                    rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                      if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, h_m_f, if_neg Bool.false_ne_true,
                      if_neg h_or_f, if_pos ⟨by omega, by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                      if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                      if_neg h_not_25_1] at hf
                    have hm_sub : m'' + 3 - 3 = m'' := by omega
                    have hc_sub : c' + 1 - 1 = c' := by omega
                    have hm_mul : 2 * (c' + 1) = 2 * c' + 2 := by omega
                    rw [hm_sub, hc_sub, hm_mul] at hf
                    dsimp only [invChain]
                    by_cases hm_ev : m'' % 2 = 0
                    · rw [if_pos hm_ev, if_neg (by intro ⟨_, hc0, _⟩; omega)]; exact hf
                    · rw [if_neg hm_ev, if_neg (by intro ⟨_, hc1, _⟩; omega), if_neg (by omega)]; exact hf

lemma step_Inv_ModeB_b2 (ls : List LTok) (m : Nat) (ds : List Nat)
    (hinv : Inv (.ModeB_b2 ls m ds)) :
    Inv (nextState (.ModeB_b2 ls m ds)) := by
  cases m with
  | zero => exact step_Inv_ModeB_b2_m0 ls ds hinv
  | succ m' =>
    cases m' with
    | zero => exact step_Inv_ModeB_b2_m1 ls ds hinv
    | succ m'' => exact step_Inv_ModeB_b2_mge2 ls m'' ds hinv

lemma prefSumW_of_ValidP5Chain (ls : List LTok) (h : ValidP5Chain ls = true) :
    prefSumW ls = 0 := by
  induction ls with
  | nil => rfl
  | cons tok rest ih =>
    cases tok with
    | p5 => rfl
    | p3z m =>
      cases m with
      | zero =>
        dsimp [ValidP5Chain] at h
        dsimp [prefSumW]
        cases rest with
        | nil => rfl
        | cons t2 s2 =>
          cases t2 with
          | p5 => rfl
          | p3z _ => rw [Nat.zero_add]; exact ih h
      | succ m' =>
        cases rest with
        | nil => cases h
        | cons t2 s2 =>
          cases t2 with
          | p3z _ => cases h
          | p5 => dsimp [prefSumW]; split_ifs <;> rfl

lemma MustDrain_of_ValidP5Chain (ls : List LTok) (h : ValidP5Chain ls = true) :
    MustDrain ls = false := by
  induction ls with
  | nil => rfl
  | cons tok rest ih =>
    cases tok with
    | p5 => rfl
    | p3z m =>
      cases m with
      | zero => dsimp [ValidP5Chain] at h; dsimp [MustDrain]; exact ih h
      | succ m' =>
        cases rest with
        | nil => cases h
        | cons t2 s2 =>
          cases t2 with
          | p3z _ => cases h
          | p5 => dsimp [MustDrain]; split_ifs <;> rfl

lemma ep_ge_z0 (ls : List LTok) : ep ls ≥ z0 ls := by
  induction ls with
  | nil => simp [z0, ep]
  | cons tok rest ih =>
    cases tok with
    | p5 => simp [z0, ep]
    | p3z m =>
      cases m with
      | zero => change 1 + z0 rest ≤ 1 + ep rest; omega
      | succ _ => simp [z0]

lemma epW_add1_ge_z0 (ls : List LTok) : epW ls + 1 ≥ z0 ls := by
  induction ls with
  | nil => simp [z0, epW]
  | cons tok rest ih =>
    cases tok with
    | p5 => simp [z0, epW]
    | p3z m =>
      cases m with
      | zero =>
        cases rest with
        | nil => simp [z0, epW]
        | cons t2 s2 =>
          cases t2 with
          | p5 => simp [z0, epW]
          | p3z m2 =>
            have h1 : epW (.p3z 0 :: .p3z m2 :: s2) = 1 + epW (.p3z m2 :: s2) := rfl
            have h2 : z0 (.p3z 0 :: .p3z m2 :: s2) = 1 + z0 (.p3z m2 :: s2) := rfl
            omega
      | succ _ => simp [z0]

lemma isHeadP5_false_of_z0_pos {ls : List LTok} (h : z0 ls ≥ 1) : isHeadP5 ls = false := by
  cases ls with
  | nil => simp [z0] at h
  | cons tok _ =>
    cases tok with
    | p5 => simp [z0] at h
    | p3z _ => rfl

lemma isHeadP3z1_false_of_z0_pos {ls : List LTok} (h : z0 ls ≥ 1) : isHeadP3z1 ls = false := by
  cases ls with
  | nil => simp [z0] at h
  | cons tok _ =>
    cases tok with
    | p5 => simp [z0] at h
    | p3z m => cases m with | zero => rfl | succ _ => simp [z0] at h

lemma hasP5_of_ValidP5Chain_hasOdd (ls : List LTok) (hv : ValidP5Chain ls = true) (ho : hasOdd ls = true) :
    hasP5 ls = true := by
  induction ls with
  | nil => cases ho
  | cons tok rest ih =>
    cases tok with
    | p5 => rfl
    | p3z m =>
      cases m with
      | zero => dsimp [ValidP5Chain] at hv; dsimp [hasOdd] at ho; dsimp [hasP5]; exact ih hv ho
      | succ m' =>
        cases rest with
        | nil => cases hv
        | cons t2 s2 =>
          cases t2 with
          | p3z _ => cases hv
          | p5 => rfl

lemma ds_ne_two_of_checkDs2_ModeE_ge2 {ls : List LTok} {k c : Nat} {ds : List Nat}
    (h : checkDs2 (.ModeE_ge2 ls k c ds) = true)
    (h_imp : hasP5 ls = false ∨ MustDrain ls = true ∨ k % 2 = 1 ∨ isHeadP5 ls = true ∨ k + epSum ls < 2 * c + 6) :
    ds ≠ [2] := by
  intro rfl
  dsimp [checkDs2] at h
  rcases h_imp with hp | hm | hk | hip | hlt
  · simp [hp] at h
  · simp [hm] at h
  · have hk0 : decide (k % 2 = 0) = false := decide_eq_false (by omega)
    simp [hk0] at h
  · simp [hip] at h
  · have hge : decide (k + epSum ls ≥ 2 * c + 6) = false := decide_eq_false (by omega)
    simp [hge] at h

lemma d25_check_of_ge36 (cz : Nat) (ds : List Nat) :
    (∀ d, ds = [d, 1] → d ≥ 25 → cz ≥ 36) →
    (!(match ds with | [d, 1] => decide (d ≥ 25) | _ => false) || decide (cz ≥ 36)) = true := by
  cases ds with
  | nil => intro _; rfl
  | cons d ds' =>
    cases ds' with
    | nil => intro _; rfl
    | cons d2 ds'' =>
      cases ds'' with
      | nil =>
        cases d2 with
        | zero => intro _; rfl
        | succ d2' =>
          cases d2' with
          | zero =>
            intro h
            have hm : (match [d, 0 + 1] with | [d, 1] => decide (d ≥ 25) | _ => false) = decide (d ≥ 25) := rfl
            rw [hm]
            by_cases hd : d ≥ 25
            · rw [decide_eq_true hd, Bool.not_true, Bool.false_or]
              exact decide_eq_true (h d rfl hd)
            · rw [decide_eq_false hd]; rfl
          | succ _ => intro _; rfl
      | cons _ _ =>
        cases d2 with
        | zero => intro _; rfl
        | succ d2' =>
          cases d2' with
          | zero => intro _; rfl
          | succ _ => intro _; rfl

lemma d25_ge36_of_check {c : Nat} {ds : List Nat}
    (h : (!(match ds with | [d, 1] => decide (d ≥ 25) | _ => false) || decide (c ≥ 36)) = true) :
    ∀ d, ds = [d, 1] → d ≥ 25 → c ≥ 36 := by
  intro d rfl hd
  have hm : (match [d, 1] with | [d, 1] => decide (d ≥ 25) | _ => false) = decide (d ≥ 25) := rfl
  rw [hm, decide_eq_true hd, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact h

lemma GoodPhiW_d25_ge35 {phiW : Nat} {d : Nat} (hd : d ≥ 25)
    (h : GoodPhiW phiW [d, 1] false = true) : phiW ≥ 35 := by
  have h1 : [d, 1] ≠ [2] := by intro hc; injection hc with _ hc2; cases hc2
  have h2 : [d, 1] ≠ [0] := by intro hc; injection hc with _ hc2; cases hc2
  have h3 : [d, 1] ≠ [1] := by intro hc; injection hc with _ hc2; cases hc2
  have h4 : [d, 1] ≠ [] := by intro hc; cases hc
  have h_m25 : (match [d, 1] with | [d, 1] => decide (d ≥ 25) | _ => false) = decide (d ≥ 25) := rfl
  dsimp only [GoodPhiW] at h
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, h_m25, if_pos (decide_eq_true hd)] at h
  exact of_decide_eq_true h

lemma prefSumW_p3z_m2_bound (m2 : Nat) (ls' : List LTok) (k c : Nat)
    (hk1 : k ≤ 2 * c + 4) (hk2 : k + prefSumW (.p3z (m2 + 2) :: ls') ≤ 2 * c + 6) :
    k + prefSumW (.p3z m2 :: ls') ≤ 2 * c + 4 := by
  by_cases hm : m2 % 2 = 1
  · have h0 : prefSumW (.p3z m2 :: ls') = 0 := by dsimp [prefSumW]; rw [if_pos hm]
    omega
  · by_cases hp5 : isHeadP5 ls' = true
    · have h0 : prefSumW (.p3z m2 :: ls') = 0 := by
        dsimp [prefSumW]; rw [if_neg hm]
        cases ls' with | nil => cases hp5 | cons t s => cases t with | p3z _ => cases hp5 | p5 => rfl
      omega
    · have hp5_f : isHeadP5 ls' = false := Bool.eq_false_iff.mpr hp5
      have := prefSumW_p3z_add2 m2 ls' (by omega) hp5_f
      omega

lemma ValidP5Chain_p3z_succ {m : Nat} {ls' : List LTok}
    (h : ValidP5Chain (.p3z (m + 1) :: ls') = true) :
    ∃ suf, ls' = .p5 :: suf ∧ z0 suf ≥ 18 ∧ ValidP5Chain suf = true := by
  cases ls' with
  | nil => cases h
  | cons t suf =>
    cases t with
    | p3z _ => cases h
    | p5 =>
      dsimp [ValidP5Chain] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨suf, rfl, h.1, h.2⟩

lemma GoodPhiW_of_ge17_and_d25 (phiW : Nat) (ds : List Nat) (hne2 : ds ≠ [2])
    (h17 : phiW ≥ 17)
    (hd25 : ∀ d, ds = [d, 1] → d ≥ 25 → phiW ≥ 35) :
    GoodPhiW phiW ds false = true := by
  dsimp [GoodPhiW]
  simp only [Bool.false_or]
  rw [if_neg hne2]
  split_ifs with h0 h1 h2 h3 h4
  · exact decide_eq_true (by omega)
  · exact decide_eq_true (by omega)
  · exact decide_eq_true (by omega)
  · cases ds with
    | nil => cases h2 rfl
    | cons d ds' =>
      cases ds' with
      | nil => cases h3
      | cons d2 ds'' =>
        cases ds'' with
        | nil =>
          cases d2 with
          | zero => cases h3
          | succ d2' =>
            cases d2' with
            | zero =>
              have hd : d ≥ 25 := of_decide_eq_true h3
              have := hd25 d rfl hd
              exact decide_eq_true (by omega)
            | succ _ => cases h3
        | cons _ _ =>
          cases d2 with
          | zero => cases h3
          | succ d2' => cases d2' <;> cases h3
  · exact decide_eq_true (by omega)
  · exact decide_eq_true (by omega)

lemma step_Inv_ModeE_ge2_nil (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 [] k c ds)) :
    Inv (.ModeB_ge3 [] k c ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  have hne2 : ds ≠ [2] := ds_ne_two_of_checkDs2_ModeE_ge2 hds2 (Or.inl rfl)
  have hds2' : checkDs2 (.ModeB_ge3 [] k c ds) = true := by
    dsimp [checkDs2]; rw [if_pos hne2]
  by_cases hk : k % 2 = 0
  · rw [if_pos hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨_, hc⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hk_le, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hk_le
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_phi, _⟩
    rw [not_bool_eq_false] at hok_phi
    have hphiw_c : GoodPhiW c ds false = true := by
      dsimp [isHeadP5, isHeadP3z1, epW, MustDrain, hasP5] at hok_phi
      simpa using hok_phi
    have hds1' : checkDs1Phi1 (.ModeB_ge3 [] k c ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp [h1, hk, isHeadP5, epW, hasP5] at hds1 ⊢
        by_cases hc1 : c = 1
        · subst hc1; simp at hds1
        · simp [hc1]
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 [] k c ds) || !checkDs1Phi1 (.ModeB_ge3 [] k c ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_pos hk]
      have h_even_nil : (!ValidEvenLs []) = false := rfl
      rw [bool_if_false_eq_self h_even_nil]
      have hok_all : (if (!isHeadP5 []) = true then
          decide (k + prefSumW [] ≤ 2 * c + 4) &&
            ((decide (ds = [] ∧ c + epW [] = 1) && MustDrain [] &&
              decide (c + ep [] = 1 ∧ k + epSum [] + 2 * ep [] + 2 = 2) &&
              hasP5 [] && decide (preP5Val [] ≥ 16 ∧ z0 (p5Suf []) ≥ 38)) ||
              GoodPhiW (c + epW []) ds false) &&
            (!decide (c = 0) || decide (epW [.p3z k] ≥ 1))
        else if c = 0 then decide (ds = [] ∧ (k = 0 ∨ k ≥ 22 ∧ z0 (p5Suf []) ≥ 38))
        else GoodPhiW (c - 1) ds false) = true := by
        have hepw1 : epW [.p3z k] = 1 := by dsimp [epW]; rw [if_neg (by omega)]
        have hpref_nil : prefSumW [] = 0 := rfl
        have hd1 : decide ((1 : Nat) ≥ 1) = true := rfl
        rw [hepw1, hpref_nil, hd1]
        simp only [isHeadP5, epW, hasP5, hphiw_c, Bool.or_true, Bool.and_true, Bool.true_and,
          decide_eq_true_eq, ↓reduceIte, Bool.not_false, Nat.add_zero]
        exact hk_le.1
      rw [not_bool_if_false_eq_true hok_all]
      dsimp [MustDrain, hasOdd]
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_pos hk, if_neg (by simp [isHeadP3z1])] at hf
      rw [if_pos hk, if_neg (by simp [isHeadP5])]
      rw [← checkChainAux_true_E_ge2_to_B_ge3_nil fuel k c ds hk]
      exact hf
  · have hm1 : k % 2 = 1 := by omega
    rw [if_neg hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨_, hc⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hck, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hck
    have h_not_b1 : ¬(ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 [] = true ∧ headP3zVal [] ≥ 3) := by
      simp [isP3zP5]
    have h_not_b2 : ¬(ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 [] = 1) ∨ (k = 3 ∧ c = 2 ∧ z0 [] = 0)) ∧
        isP3zP5 (dropZ0 []) = true ∧ headP3zVal (dropZ0 []) ≥ 18 ∧ z0 (p5Suf []) ≥ 38) := by
      simp [dropZ0, isP3zP5]
    rw [if_neg h_not_b1, if_neg h_not_b2] at hc
    have hz0_nil : z0 [] = 0 := rfl
    rw [hz0_nil] at hc
    simp only [Nat.add_zero, Nat.mul_zero, Bool.and_eq_true] at hc
    rcases hc with ⟨⟨⟨hok_base, hc_9⟩, hc_1⟩, _⟩
    have hck_8_15 : c ≥ 8 ∧ k ≥ 15 := by
      split_ifs at hok_base <;> (simp_all; try omega)
    have hf1 := hch 1
    dsimp only [invChain] at hf1
    rw [if_neg hk, if_neg h_not_b1, if_neg h_not_b2] at hf1
    dsimp only [checkChainAux, z0, dropZ0, isHeadP5] at hf1
    simp only [Nat.add_zero, Nat.mul_zero, Bool.not_false, Bool.true_and] at hf1
    rw [bool_if_false_eq_true] at hf1
    rcases hf1 with ⟨hphiw_f, hf1⟩
    rw [not_bool_eq_false] at hphiw_f
    simp only [Bool.and_eq_true] at hf1
    have hgp : GoodPsi (c - 1) ds = true := hf1.1
    have hds1' : checkDs1Phi1 (.ModeB_ge3 [] k c ds) = true := by
      dsimp [checkDs1Phi1]
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [if_neg hk]
        have hc2 : decide (c = 2) = false := decide_eq_false (by omega)
        rw [hc2]; rfl
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 [] k c ds) || !checkDs1Phi1 (.ModeB_ge3 [] k c ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega)]
      have heven_k : ValidEvenLs [.p3z k] = true := by
        dsimp [ValidEvenLs]; rw [if_neg hk]; rfl
      rw [not_bool_if_false_eq_true heven_k]
      have hrst_f : decide (k = 1 ∧ c = 1 ∧ ds = []) = false := decide_eq_false (by omega)
      have hok_c1 : (if c ≥ 1 then
          if (!decide (k = 1 ∧ c = 1 ∧ ds = [])) = true then
            (decide (ds = [] ∧ c = 2 ∧ k = 3) && MustDrain [.p3z k] &&
              hasP5 [] && decide (preP5Val [.p3z k] ≥ 16 ∧ z0 (p5Suf []) ≥ 38)) ||
              GoodPhiW (c - 1) ds false
          else true
        else true) = true := by
        rw [if_pos (by omega), hrst_f, if_pos (by decide), hphiw_f, Bool.or_true]
      rw [not_bool_if_false_eq_true hok_c1]
      have hmd_t : MustDrain [.p3z k] = true := by dsimp [MustDrain]; rw [if_pos hm1]
      have hdec_gt : decide (k > 2 * c + 3) = false := decide_eq_false (by omega)
      rw [hmd_t, hdec_gt, Bool.and_false, if_neg Bool.false_ne_true, if_pos hck.2, hrst_f, if_neg Bool.false_ne_true]
      rw [hgp, Bool.true_and]
      have h_ds1_ok : ((!decide (ds = [1] ∧ c - 1 ≥ 24)) || decide (k ≥ 37)) = true := by
        by_cases h1 : ds = [1]
        · simp [h1] at hc_1; simp [hc_1]
        · simp [h1]
      have h_ds0_ok : ((!decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧ ((!hasP5 []) = true ∨ true = true))) ||
          decide (k ≥ 17)) = true := by
        by_cases h0 : (ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8
        · have hc9 : ((ds = [] ∨ ds = [0]) ∧ c ≥ 9) ∨ isOddDrainDs ds = true := Or.inl ⟨h0.1, by omega⟩
          have hc9_d : decide (((ds = [] ∨ ds = [0]) ∧ c ≥ 9) ∨ isOddDrainDs ds = true) = true := decide_eq_true hc9
          rw [hc9_d] at hc_9
          simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_9
          simp [hc_9]
        · have h_f : decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧ ((!hasP5 []) = true ∨ true = true)) = false :=
            decide_eq_false (fun ⟨h_a, h_b, _⟩ => h0 ⟨h_a, h_b⟩)
          rw [h_f]; rfl
      have h15_7 : decide (k ≥ 15 ∧ c - 1 ≥ 7) = true := decide_eq_true (by omega)
      rw [h_ds1_ok, h_ds0_ok, h15_7]
      simp
    · intro fuel
      cases fuel with
      | zero =>
        dsimp [invChain]
        rw [if_neg hk, if_neg (by omega), if_neg (by omega)]
        rfl
      | succ fuel' =>
        have hf := hch (fuel' + 1)
        dsimp only [invChain] at hf ⊢
        rw [if_neg hk, if_neg h_not_b1, if_neg h_not_b2] at hf
        rw [if_neg hk, if_neg (show ¬(k = 1 ∧ c = 1 ∧ ds = []) by omega), if_neg (show c ≠ 0 by omega)]
        dsimp only [checkChainAux, z0, dropZ0, isHeadP5] at hf
        simp only [Nat.add_zero, Nat.mul_zero, Bool.not_false, Bool.true_and, hphiw_f,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, hgp] at hf
        have hodd_k : hasOdd [.p3z k] = true := by dsimp [hasOdd]; rw [if_pos hm1]
        have hepsum_k : epSum [.p3z k] = k - 1 := by dsimp [epSum]; rw [if_pos hm1]
        have hep_k : ep [.p3z k] = 0 := by dsimp [ep]; rw [if_pos hm1]
        have hmd_k : MustDrain [.p3z k] = true := by dsimp [MustDrain]; rw [if_pos hm1]
        have hp5_k : hasP5 [.p3z k] = false := rfl
        have hdec_m : decide (2 * c + 2 ≥ 0 + (k - 1)) = true := decide_eq_true (by omega)
        dsimp only [checkChainAux]
        rw [hodd_k, hepsum_k, hep_k, hmd_k, hp5_k, hdec_m]
        simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
        have hk3 : k - 1 + 3 = k + 2 := by omega
        have hk2 : k - 1 + 2 = k + 1 := by omega
        rw [hk3, hk2]
        exact hf

lemma step_Inv_ModeE_ge2_p3z0 (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 (.p3z 0 :: ls') k c ds)) :
    Inv (.ModeE_ge2 ls' (k + 2) (c + 1) ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  by_cases hk : k % 2 = 0
  · have hk2_ev : (k + 2) % 2 = 0 := by omega
    rw [if_pos hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, hc⟩
    rw [not_bool_eq_false, ValidEvenLs_p3z_even_cons 0 ls' rfl] at heven
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hk_le, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hk_le
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_phi, hc⟩
    rw [not_bool_eq_false] at hok_phi
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hmd_bound, hc⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨_, hodd_branch⟩
    have hepsum_eq := epSum_p3z_even_cons 0 ls' rfl
    have hep_eq := ep_p3z_even_cons 0 ls' rfl
    have hodd_eq := hasOdd_p3z_even_cons 0 ls' rfl
    have hmd_eq := MustDrain_p3z_even_cons 0 ls' rfl
    by_cases hp5 : isHeadP5 ls' = true
    · have h_ls : ∃ suf, ls' = .p5 :: suf := by
        cases ls' with
        | nil => cases hp5
        | cons t2 s2 => cases t2 with | p3z _ => cases hp5 | p5 => exact ⟨s2, rfl⟩
      obtain ⟨suf, rfl⟩ := h_ls
      have hne2 : ds ≠ [2] := by
        apply ds_ne_two_of_checkDs2_ModeE_ge2 hds2
        refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        dsimp [epSum]; omega
      have hds2' : checkDs2 (.ModeE_ge2 (.p5 :: suf) (k + 2) (c + 1) ds) = true := by
        dsimp [checkDs2]; rw [if_pos hne2]
      have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p5 :: suf) (k + 2) (c + 1) ds) = true := by
        dsimp [checkDs1Phi1] at hds1 ⊢
        by_cases h1 : ds = [1]
        · simp [h1, hk, hk2_ev, isHeadP5, epW] at hds1 ⊢
          by_cases hc1 : c = 1
          · subst hc1
            simp [hasP5, MustDrain, epSum] at hds1
            omega
          · simp [hc1]
        · simp [h1]
      have hphiw_c : GoodPhiW c ds false = true := by
        dsimp [isHeadP5, isHeadP3z1, epW, MustDrain] at hok_phi
        simpa using hok_phi
      refine ⟨?_, ?_⟩
      · dsimp only [invCore]
        have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 (.p5 :: suf) (k + 2) (c + 1) ds) ||
            !checkDs1Phi1 (.ModeE_ge2 (.p5 :: suf) (k + 2) (c + 1) ds)) = false := by
          simp [hgd, hds2', hds1']
        rw [bool_if_false_eq_self h_g, if_pos hk2_ev, not_bool_if_false_eq_true heven]
        have hpref0 : prefSumW (.p5 :: suf) = 0 := rfl
        rw [hpref0, Nat.add_zero, not_decide_if_false_eq_true (by omega)]
        have hok_phi' : (if (!isHeadP5 (.p5 :: suf)) = true then
            (decide (ds = [] ∧ c + 1 + epW (.p5 :: suf) = 1) && MustDrain (.p5 :: suf) &&
              decide (c + 1 + ep (.p5 :: suf) = 1 ∧ k + 2 + epSum (.p5 :: suf) + 2 * ep (.p5 :: suf) = 2) &&
              hasP5 (.p5 :: suf) && decide (preP5Val (.p5 :: suf) ≥ 16 ∧ z0 (p5Suf (.p5 :: suf)) ≥ 38)) ||
              GoodPhiW (c + 1 + epW (.p5 :: suf)) ds (isHeadP3z1 (.p5 :: suf) && decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = []))
          else
            decide (c + 1 = 0 ∧ ds = [] ∧ k + 2 = 2) ||
              (decide (c + 1 ≥ 1) && GoodPhiW (c + 1 - 1) ds false)) = true := by
          dsimp [isHeadP5]
          simp [hphiw_c]
        rw [not_bool_if_false_eq_true hok_phi']
        dsimp [MustDrain, isHeadP3z1, hasOdd]
      · intro fuel
        have hf := hch fuel
        dsimp only [invChain] at hf ⊢
        rw [if_pos hk, if_neg (by simp [isHeadP3z1])] at hf
        rw [if_pos hk2_ev, if_neg (by simp [isHeadP3z1])]
        have h_shift := checkChainAux_true_p3z0 fuel (.p5 :: suf) (c + 1) k (2 * c + 4) ds
          (Or.inr (by dsimp [epSum]; omega))
        have hm_eq : 2 * (c + 1) + 4 = 2 * c + 4 + 2 := by omega
        rw [hm_eq, ← h_shift]
        exact hf
    · have hp5_f : isHeadP5 ls' = false := Bool.eq_false_iff.mpr hp5
      have hepw_eq := epW_p3z_even_cons 0 ls' rfl hp5_f
      have hpref_eq := prefSumW_p3z_even_cons 0 ls' rfl hp5_f
      have hpre_eq := preP5Val_p3z_cons_of_not_headP5 0 ls' hp5_f
      have hip5_0 : isHeadP5 (.p3z 0 :: ls') = false := rfl
      have hds2' : checkDs2 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) = true := by
        dsimp [checkDs2] at hds2 ⊢
        by_cases h2 : ds = [2]
        · rw [if_neg (not_not.mpr h2)] at hds2 ⊢
          have hd_k : decide (k % 2 = 0) = true := decide_eq_true hk
          have hd_k2 : decide ((k + 2) % 2 = 0) = true := decide_eq_true hk2_ev
          rw [hip5_0, hmd_eq, hepsum_eq, Nat.zero_add, hd_k] at hds2
          rw [hp5_f, hd_k2]
          dsimp [hasP5, p5Suf] at hds2
          rw [show decide (k + 2 + epSum ls' ≥ 2 * (c + 1) + 6) = decide (k + epSum ls' ≥ 2 * c + 6) from
            decide_eq_of_iff (by omega)]
          exact hds2
        · rw [if_pos h2]
      have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) = true := by
        dsimp [checkDs1Phi1] at hds1 ⊢
        by_cases h1 : ds = [1]
        · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
          rw [if_pos hk, hip5_0] at hds1
          rw [if_pos hk2_ev, hp5_f]
          simp only [Bool.false_eq_true, ↓reduceIte] at hds1 ⊢
          have hpw_eq : c + 1 + epW ls' = c + epW (.p3z 0 :: ls') := by omega
          rw [hpw_eq]
          by_cases he1 : c + epW (.p3z 0 :: ls') = 1
          · rw [decide_eq_true he1] at hds1 ⊢
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hds1 ⊢
            rw [hmd_eq, hepsum_eq, Nat.zero_add] at hds1
            dsimp [hasP5] at hds1
            rw [show decide (k + 2 + epSum ls' ≥ 2 * (c + 1) + 14) = decide (k + epSum ls' ≥ 2 * c + 14) from
              decide_eq_of_iff (by omega)]
            exact hds1
          · simp [decide_eq_false he1]
        · simp [h1]
      refine ⟨?_, ?_⟩
      · dsimp only [invCore]
        have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) ||
            !checkDs1Phi1 (.ModeE_ge2 ls' (k + 2) (c + 1) ds)) = false := by
          simp [hgd, hds2', hds1']
        rw [bool_if_false_eq_self h_g, if_pos hk2_ev, not_bool_if_false_eq_true heven]
        rw [hpref_eq, Nat.zero_add] at hk_le
        rw [not_decide_if_false_eq_true (by omega)]
        have h_np5 : (!isHeadP5 ls') = true := by rw [hp5_f]; rfl
        have h_np5_0 : (!isHeadP5 (.p3z 0 :: ls')) = true := rfl
        rw [if_pos h_np5_0] at hok_phi
        have hstart_0 : (isHeadP3z1 (.p3z 0 :: ls') && decide (k = 0 ∧ c = 0 ∧ ds = [])) = false := rfl
        have hstart_1 : (isHeadP3z1 ls' && decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = [])) = false := by
          have hne : decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = []) = false := decide_eq_false (by omega)
          rw [hne, Bool.and_false]
        rw [hstart_0] at hok_phi
        have hok_phi' : (if (!isHeadP5 ls') = true then
            (decide (ds = [] ∧ c + 1 + epW ls' = 1) && MustDrain ls' &&
              decide (c + 1 + ep ls' = 1 ∧ k + 2 + epSum ls' + 2 * ep ls' = 2) &&
              hasP5 ls' && decide (preP5Val ls' ≥ 16 ∧ z0 (p5Suf ls') ≥ 38)) ||
              GoodPhiW (c + 1 + epW ls') ds (isHeadP3z1 ls' && decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = []))
          else
            decide (c + 1 = 0 ∧ ds = [] ∧ k + 2 = 2) || (decide (c + 1 ≥ 1) && GoodPhiW (c + 1 - 1) ds false)) = true := by
          rw [if_pos h_np5, hstart_1]
          have hpw_eq : c + 1 + epW ls' = c + epW (.p3z 0 :: ls') := by omega
          have hp_eq : c + 1 + ep ls' = c + ep (.p3z 0 :: ls') := by omega
          have hx_eq : k + 2 + epSum ls' + 2 * ep ls' = k + epSum (.p3z 0 :: ls') + 2 * ep (.p3z 0 :: ls') := by omega
          rw [hpw_eq, hp_eq, hx_eq, ← hmd_eq, ← hpre_eq]
          exact hok_phi
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_bound' : (MustDrain ls' && decide (2 * (c + 1) + 4 < k + 2 + epSum ls')) = false := by
          rw [hmd_eq, hepsum_eq, Nat.zero_add] at hmd_bound
          rw [show decide (2 * (c + 1) + 4 < k + 2 + epSum ls') = decide (2 * c + 4 < k + epSum ls') from
            decide_eq_of_iff (by omega)]
          exact hmd_bound
        rw [bool_if_false_eq_self hmd_bound']
        have hrst_f : (decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = []) && isHeadP3z1 ls') = false := by
          have hne : decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = []) = false := decide_eq_false (by omega)
          rw [hne, Bool.false_and]
        rw [hrst_f]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        have hrst_0 : (decide (k = 0 ∧ c = 0 ∧ ds = []) && isHeadP3z1 (.p3z 0 :: ls')) = false := by
          simp [isHeadP3z1]
        have hepsum_0 : epSum (.p3z 0 :: ls') = epSum ls' := by rw [hepsum_eq, Nat.zero_add]
        have hp5_0 : hasP5 (.p3z 0 :: ls') = hasP5 ls' := rfl
        have hpsuf_0 : p5Suf (.p3z 0 :: ls') = p5Suf ls' := rfl
        rw [hodd_eq, hepsum_0, hp5_0, hpsuf_0] at hodd_branch
        have hd_odd : decide (2 * (c + 1) + 4 ≥ k + 2 + epSum ls') = decide (2 * c + 4 ≥ k + epSum ls') :=
          decide_eq_of_iff (by omega)
        rw [hd_odd]
        by_cases h_cond : (hasOdd ls' && decide (2 * c + 4 ≥ k + epSum ls')) = true
        · rw [if_pos h_cond, hrst_0, if_neg Bool.false_ne_true] at hodd_branch
          rw [if_pos h_cond]
          have hp_eq : c + 1 + ep ls' = c + ep (.p3z 0 :: ls') := by omega
          have hx_eq : k + 2 + epSum ls' + 2 * ep ls' = k + epSum ls' + 2 * ep (.p3z 0 :: ls') := by omega
          rw [hp_eq, hx_eq, ← hmd_eq, ← hpre_eq]
          exact hodd_branch
        · rw [if_neg h_cond]
      · intro fuel
        have hf := hch fuel
        dsimp only [invChain] at hf ⊢
        rw [if_pos hk, if_neg (by simp [isHeadP3z1])] at hf
        rw [if_pos hk2_ev, if_neg (show ¬(k + 2 = 0 ∧ c + 1 = 0 ∧ ds = [] ∧ isHeadP3z1 ls' = true) by omega)]
        have h_shift := checkChainAux_true_p3z0 fuel ls' (c + 1) k (2 * c + 4) ds (Or.inl hp5_f)
        have hm_eq : 2 * (c + 1) + 4 = 2 * c + 4 + 2 := by omega
        rw [hm_eq, ← h_shift]
        exact hf
  · have hm1 : k % 2 = 1 := by omega
    have hk2_odd : ¬((k + 2) % 2 = 0) := by omega
    have hne2 : ds ≠ [2] := ds_ne_two_of_checkDs2_ModeE_ge2 hds2 (Or.inr (Or.inr (Or.inl hm1)))
    have hds2' : checkDs2 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) = true := by
      dsimp [checkDs2]; rw [if_pos hne2]
    have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) = true := by
      dsimp [checkDs1Phi1]
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte]; rw [if_neg hk2_odd]; rfl
      · simp [h1]
    rw [if_neg hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hvp5, hc⟩
    rw [not_bool_eq_false] at hvp5
    dsimp [ValidP5Chain] at hvp5
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hck, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hck
    have h_not_b1_0 : ¬(ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 (.p3z 0 :: ls') = true ∧ headP3zVal (.p3z 0 :: ls') ≥ 3) := by
      dsimp [headP3zVal]; omega
    have h_not_b1_1 : ¬(ds = [] ∧ k + 2 = 1 ∧ c + 1 = 1 ∧ isP3zP5 ls' = true ∧ headP3zVal ls' ≥ 3) := by
      omega
    rw [if_neg h_not_b1_0] at hc
    have hz_eq : c + 1 + z0 ls' = c + z0 (.p3z 0 :: ls') := by change c + 1 + z0 ls' = c + (1 + z0 ls'); omega
    have hk_eq : k + 2 + 2 * z0 ls' = k + 2 * z0 (.p3z 0 :: ls') := by change k + 2 + 2 * z0 ls' = k + 2 * (1 + z0 ls'); omega
    have hb2_iff : (ds = [] ∧ ((k + 2 = 1 ∧ c + 1 = 1 ∧ z0 ls' = 1) ∨ (k + 2 = 3 ∧ c + 1 = 2 ∧ z0 ls' = 0)) ∧
        isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38) ↔
        (ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 (.p3z 0 :: ls') = 1) ∨ (k = 3 ∧ c = 2 ∧ z0 (.p3z 0 :: ls') = 0)) ∧
        isP3zP5 (dropZ0 (.p3z 0 :: ls')) = true ∧ headP3zVal (dropZ0 (.p3z 0 :: ls')) ≥ 18 ∧ z0 (p5Suf (.p3z 0 :: ls')) ≥ 38) := by
      dsimp [z0, dropZ0, p5Suf]
      constructor
      · rintro ⟨rfl, h_or, hp3, hh, hz⟩
        refine ⟨rfl, ?_, hp3, hh, hz⟩
        rcases h_or with ⟨hk1, _, _⟩ | ⟨hk3, hc2, hz0⟩
        · omega
        · exact Or.inl ⟨by omega, by omega, by omega⟩
      · rintro ⟨rfl, h_or, hp3, hh, hz⟩
        refine ⟨rfl, ?_, hp3, hh, hz⟩
        rcases h_or with ⟨rfl, rfl, hz1⟩ | ⟨_, _, hz0⟩
        · exact Or.inr ⟨rfl, rfl, by omega⟩
        · omega
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) ||
          !checkDs1Phi1 (.ModeE_ge2 ls' (k + 2) (c + 1) ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_neg hk2_odd, not_bool_if_false_eq_true hvp5]
      rw [not_decide_if_false_eq_true (by omega)]
      rw [if_neg h_not_b1_1]
      by_cases hb2 : ds = [] ∧ ((k + 2 = 1 ∧ c + 1 = 1 ∧ z0 ls' = 1) ∨ (k + 2 = 3 ∧ c + 1 = 2 ∧ z0 ls' = 0)) ∧
          isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38
      · rw [if_pos hb2]
      · rw [if_neg hb2]
        rw [if_neg (fun h => hb2 (hb2_iff.mpr h))] at hc
        rw [hz_eq, hk_eq]
        exact hc
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_neg hk, if_neg h_not_b1_0] at hf
      rw [if_neg hk2_odd, if_neg h_not_b1_1]
      by_cases hb2 : ds = [] ∧ ((k + 2 = 1 ∧ c + 1 = 1 ∧ z0 ls' = 1) ∨ (k + 2 = 3 ∧ c + 1 = 2 ∧ z0 ls' = 0)) ∧
          isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38
      · rw [if_pos hb2]
        rw [if_pos (hb2_iff.mp hb2)] at hf
        exact hf
      · rw [if_neg hb2]
        rw [if_neg (fun h => hb2 (hb2_iff.mpr h))] at hf
        rw [← checkChainAux_false_p3z0 fuel ls' c k 0 ds]
        exact hf

lemma step_Inv_ModeE_ge2_p5 (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 (.p5 :: ls') k c ds)) :
    Inv (.ModeE_ge2 ls' (k + 3) (c + 2) ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  have hne2 : ds ≠ [2] := ds_ne_two_of_checkDs2_ModeE_ge2 hds2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hds2' : checkDs2 (.ModeE_ge2 ls' (k + 3) (c + 2) ds) = true := by
    dsimp [checkDs2]; rw [if_pos hne2]
  by_cases hk : k % 2 = 0
  · have hk3_odd : ¬((k + 3) % 2 = 0) := by omega
    have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (k + 3) (c + 2) ds) = true := by
      dsimp [checkDs1Phi1]
      by_cases h1 : ds = [1]
      · simp [h1, hk3_odd]
      · simp [h1]
    rw [if_pos hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, hc⟩
    rw [not_bool_eq_false] at heven
    dsimp [ValidEvenLs] at heven
    simp only [Bool.and_eq_true, decide_eq_true_eq] at heven
    rcases heven with ⟨hz18, hvp5⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hk_le, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hk_le
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_phi, _⟩
    rw [not_bool_eq_false] at hok_phi
    dsimp [isHeadP5] at hok_phi
    have h_not_b1 : ¬(ds = [] ∧ k + 3 = 1 ∧ c + 2 = 1 ∧ isP3zP5 ls' = true ∧ headP3zVal ls' ≥ 3) := by omega
    have h_not_b2 : ¬(ds = [] ∧ ((k + 3 = 1 ∧ c + 2 = 1 ∧ z0 ls' = 1) ∨ (k + 3 = 3 ∧ c + 2 = 2 ∧ z0 ls' = 0)) ∧
        isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38) := by omega
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 ls' (k + 3) (c + 2) ds) ||
          !checkDs1Phi1 (.ModeE_ge2 ls' (k + 3) (c + 2) ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_neg hk3_odd, not_bool_if_false_eq_true hvp5]
      rw [not_decide_if_false_eq_true (by omega)]
      rw [if_neg h_not_b1, if_neg h_not_b2]
      have h20 : decide (c + 2 + z0 ls' ≥ 20 ∧ k + 3 + 2 * z0 ls' ≥ 15) = true := decide_eq_true (by omega)
      have h8 : decide (c + 2 + z0 ls' ≥ 8 ∧ k + 3 + 2 * z0 ls' ≥ 15) = true := decide_eq_true (by omega)
      rw [h20, h8, ite_self]
      have h17 : decide (k + 3 + 2 * z0 ls' ≥ 17) = true := decide_eq_true (by omega)
      have h37 : decide (k + 3 + 2 * z0 ls' ≥ 37) = true := decide_eq_true (by omega)
      rw [h17, h37]
      simp only [Bool.true_and, Bool.or_true]
      apply d25_check_of_ge36
      intro d hd_eq hd25
      cases Bool.or_eq_true_iff.mp hok_phi with
      | inl h0 =>
        simp only [decide_eq_true_eq] at h0
        rcases h0 with ⟨_, rfl, _⟩
        cases hd_eq
      | inr hc1 =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
        rcases hc1 with ⟨_, hphiw⟩
        subst hd_eq
        have := GoodPhiW_d25_ge35 hd25 hphiw
        omega
    · intro fuel
      have hf := hch (fuel + 1)
      dsimp only [invChain] at hf ⊢
      rw [if_pos hk, if_neg (by simp [isHeadP3z1])] at hf
      rw [if_neg hk3_odd, if_neg h_not_b1, if_neg h_not_b2]
      dsimp only [checkChainAux, hasOdd, hasP5, isHeadP5, p5Suf, ep, epSum] at hf
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
        Bool.true_or, Nat.add_zero] at hf
      exact hf
  · have hm1 : k % 2 = 1 := by omega
    have hk3_ev : (k + 3) % 2 = 0 := by omega
    rw [if_neg hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hvp5_p5, hc⟩
    rw [not_bool_eq_false] at hvp5_p5
    dsimp [ValidP5Chain] at hvp5_p5
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvp5_p5
    rcases hvp5_p5 with ⟨hz18, hvp5⟩
    have heven' := ValidP5Chain_imp_ValidEvenLs ls' hvp5
    have hpref0 := prefSumW_of_ValidP5Chain ls' hvp5
    have hmd0 := MustDrain_of_ValidP5Chain ls' hvp5
    have hnp5 : isHeadP5 ls' = false := isHeadP5_false_of_z0_pos (by omega)
    have hnp3z1 : isHeadP3z1 ls' = false := isHeadP3z1_false_of_z0_pos (by omega)
    have hepw17 : epW ls' ≥ 17 := by have := epW_add1_ge_z0 ls'; omega
    have hep18 : ep ls' ≥ 18 := by have := ep_ge_z0 ls'; omega
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hck, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hck
    have h_not_b1 : ¬(ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 (.p5 :: ls') = true ∧ headP3zVal (.p5 :: ls') ≥ 3) := by
      simp [isP3zP5]
    have h_not_b2 : ¬(ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 (.p5 :: ls') = 1) ∨ (k = 3 ∧ c = 2 ∧ z0 (.p5 :: ls') = 0)) ∧
        isP3zP5 (dropZ0 (.p5 :: ls')) = true ∧ headP3zVal (dropZ0 (.p5 :: ls')) ≥ 18 ∧ z0 (p5Suf (.p5 :: ls')) ≥ 38) := by
      simp [dropZ0, isP3zP5]
    rw [if_neg h_not_b1, if_neg h_not_b2] at hc
    have hz0_p5 : z0 (.p5 :: ls') = 0 := rfl
    rw [hz0_p5] at hc
    simp only [Nat.add_zero, Bool.and_eq_true] at hc
    rcases hc with ⟨⟨⟨hok_base, _⟩, _⟩, hc_25⟩
    have hck_8_15 : c ≥ 8 ∧ k ≥ 15 := by
      split_ifs at hok_base <;> (simp_all; try omega)
    have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (k + 3) (c + 2) ds) = true := by
      dsimp [checkDs1Phi1]
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [if_pos hk3_ev, hnp5]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hne1 : decide (c + 2 + epW ls' = 1) = false := decide_eq_false (by omega)
        simp [hne1]
      · simp [h1]
    have hphiw' : GoodPhiW (c + 2 + epW ls') ds false = true := by
      apply GoodPhiW_of_ge17_and_d25 _ _ hne2 (by omega)
      intro d hd_eq hd25
      have hc36 := d25_ge36_of_check hc_25 d hd_eq hd25
      omega
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 ls' (k + 3) (c + 2) ds) ||
          !checkDs1Phi1 (.ModeE_ge2 ls' (k + 3) (c + 2) ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_pos hk3_ev, not_bool_if_false_eq_true heven']
      rw [hpref0, Nat.add_zero]
      rw [not_decide_if_false_eq_true (by omega)]
      have hok_phi' : (if (!isHeadP5 ls') = true then
          (decide (ds = [] ∧ c + 2 + epW ls' = 1) && MustDrain ls' &&
            decide (c + 2 + ep ls' = 1 ∧ k + 3 + epSum ls' + 2 * ep ls' = 2) &&
            hasP5 ls' && decide (preP5Val ls' ≥ 16 ∧ z0 (p5Suf ls') ≥ 38)) ||
            GoodPhiW (c + 2 + epW ls') ds (isHeadP3z1 ls' && decide (k + 3 = 0 ∧ c + 2 = 0 ∧ ds = []))
        else
          decide (c + 2 = 0 ∧ ds = [] ∧ k + 3 = 2) || (decide (c + 2 ≥ 1) && GoodPhiW (c + 2 - 1) ds false)) = true := by
        have hnp5_t : (!isHeadP5 ls') = true := by rw [hnp5]; rfl
        rw [if_pos hnp5_t, GoodPhiW_mono _ _ _ hphiw', Bool.or_true]
      rw [not_bool_if_false_eq_true hok_phi']
      rw [hmd0, Bool.false_and, if_neg Bool.false_ne_true]
      rw [hnp3z1, Bool.and_false]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      by_cases h_cond : (hasOdd ls' && decide (2 * (c + 2) + 4 ≥ k + 3 + epSum ls')) = true
      · rw [if_pos h_cond]
        simp only [Bool.and_eq_true] at h_cond
        rcases h_cond with ⟨hodd_t, hdec_m⟩
        have hp5_t := hasP5_of_ValidP5Chain_hasOdd ls' hvp5 hodd_t
        have hf2 := hch 2
        dsimp only [invChain] at hf2
        rw [if_neg hk, if_neg h_not_b1, if_neg h_not_b2] at hf2
        dsimp only [checkChainAux, z0, dropZ0, isHeadP5] at hf2
        simp only [Nat.add_zero, Nat.mul_zero, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hf2
        rw [hodd_t, hdec_m, hmd0, hp5_t] at hf2
        simp only [Bool.and_true, ↓reduceIte, Bool.not_false, Bool.not_true, Bool.false_eq_true] at hf2
        have hgp : GoodPsi (c + 2 + ep ls') ds = true := by
          unfold GoodPsi
          have h_eq : c + 2 + ep ls' + 1 = c + 3 + ep ls' := by omega
          rw [h_eq]; exact hf2
        rw [hgp]
        have h36 : decide (k + 3 + epSum ls' + 2 * ep ls' ≥ 36) = true := decide_eq_true (by omega)
        have h16 : decide (k + 3 + epSum ls' + 2 * ep ls' ≥ 16) = true := decide_eq_true (by omega)
        rw [h36, h16]
        simp
      · rw [if_neg h_cond]
    · intro fuel
      have hf := hch (fuel + 1)
      dsimp only [invChain] at hf ⊢
      rw [if_neg hk, if_neg h_not_b1, if_neg h_not_b2] at hf
      rw [if_pos hk3_ev, if_neg (by simp [hnp3z1])]
      dsimp only [checkChainAux, z0, dropZ0, isHeadP5] at hf
      simp only [Nat.add_zero, Nat.mul_zero, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hf
      exact hf

lemma step_Inv_ModeE_ge2_p3z_ge2 (m2 : Nat) (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 (.p3z (m2 + 2) :: ls') k c ds)) :
    Inv (.ModeB_ge3 (.p3z m2 :: ls') k c ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  by_cases hk : k % 2 = 0
  · rw [if_pos hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨heven, hc⟩
    rw [not_bool_eq_false, ValidEvenLs_p3z_add2] at heven
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hk_le, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hk_le
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hok_phi, hc⟩
    rw [not_bool_eq_false] at hok_phi
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hmd_bound, hc⟩
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨_, hodd_branch⟩
    have hmd_eq := MustDrain_p3z_add2 m2 ls'
    have hepsum_eq := epSum_p3z_add2 m2 ls'
    have hep_eq := ep_p3z_add2 m2 ls'
    have hepw_eq := epW_p3z_add2 m2 ls'
    have hodd_eq := hasOdd_p3z_add2 m2 ls'
    have hip5_0 : isHeadP5 (.p3z (m2 + 2) :: ls') = false := rfl
    have hip5_1 : isHeadP5 (.p3z m2 :: ls') = false := rfl
    have hds2' : checkDs2 (.ModeB_ge3 (.p3z m2 :: ls') k c ds) = true := by
      dsimp [checkDs2] at hds2 ⊢
      by_cases h2 : ds = [2]
      · rw [if_neg (not_not.mpr h2)] at hds2 ⊢
        have hd_k : decide (k % 2 = 0) = true := decide_eq_true hk
        rw [hip5_0, hmd_eq, hepsum_eq, hd_k] at hds2
        rw [hip5_1, hd_k]
        dsimp [hasP5, p5Suf] at hds2 ⊢
        rw [show decide (k + epSum (.p3z m2 :: ls') ≥ 2 * c + 4) =
          decide (k + (epSum (.p3z m2 :: ls') + 2) ≥ 2 * c + 6) from decide_eq_of_iff (by omega)]
        exact hds2
      · rw [if_pos h2]
    have hds1' : checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: ls') k c ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hds1 ⊢
        rw [if_pos hk, hip5_0, hepw_eq] at hds1
        rw [if_pos hk, hip5_1]
        simp only [Bool.false_eq_true, ↓reduceIte] at hds1 ⊢
        by_cases he1 : c + epW (.p3z m2 :: ls') = 1
        · rw [decide_eq_true he1] at hds1 ⊢
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hds1 ⊢
          rw [hmd_eq, hepsum_eq] at hds1
          have hmd_k := MustDrain_p3z_even_cons k (.p3z m2 :: ls') hk
          rw [hmd_k, if_pos hk]
          dsimp [hasP5, isHeadP5] at hds1 ⊢
          rw [show decide (k + epSum (.p3z m2 :: ls') ≥ 2 * c + 12) =
            decide (k + (epSum (.p3z m2 :: ls') + 2) ≥ 2 * c + 14) from decide_eq_of_iff (by omega)]
          exact hds1
        · simp [decide_eq_false he1]
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 (.p3z m2 :: ls') k c ds) ||
          !checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: ls') k c ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_pos hk, not_bool_if_false_eq_true heven]
      have h_np5_0 : (!isHeadP5 (.p3z (m2 + 2) :: ls')) = true := rfl
      have h_np5_1 : (!isHeadP5 (.p3z m2 :: ls')) = true := rfl
      have hstart_0 : (isHeadP3z1 (.p3z (m2 + 2) :: ls') && decide (k = 0 ∧ c = 0 ∧ ds = [])) = false := rfl
      rw [if_pos h_np5_0, hstart_0] at hok_phi
      have hpref_m2 := prefSumW_p3z_m2_bound m2 ls' k c hk_le.1 hk_le.2
      have hepw_ge1 : epW (.p3z k :: .p3z m2 :: ls') ≥ 1 := by
        rw [epW_p3z_even_cons k (.p3z m2 :: ls') hk rfl]; omega
      have hok_all : (if (!isHeadP5 (.p3z m2 :: ls')) = true then
          decide (k + prefSumW (.p3z m2 :: ls') ≤ 2 * c + 4) &&
            ((decide (ds = [] ∧ c + epW (.p3z m2 :: ls') = 1) && MustDrain (.p3z m2 :: ls') &&
              decide (c + ep (.p3z m2 :: ls') = 1 ∧ k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 = 2) &&
              hasP5 (.p3z m2 :: ls') && decide (preP5Val (.p3z m2 :: ls') ≥ 16 ∧ z0 (p5Suf (.p3z m2 :: ls')) ≥ 38)) ||
              GoodPhiW (c + epW (.p3z m2 :: ls')) ds false) &&
            (!decide (c = 0) || decide (epW (.p3z k :: .p3z m2 :: ls') ≥ 1))
        else if c = 0 then decide (ds = [] ∧ (k = 0 ∨ k ≥ 22 ∧ z0 (p5Suf (.p3z m2 :: ls')) ≥ 38))
        else GoodPhiW (c - 1) ds false) = true := by
        rw [if_pos h_np5_1, decide_eq_true hpref_m2, decide_eq_true hepw_ge1, Bool.or_true, Bool.and_true, Bool.true_and]
        rw [hepw_eq, hmd_eq, hep_eq, hepsum_eq] at hok_phi
        have h_xi_eq : k + (epSum (.p3z m2 :: ls') + 2) + 2 * ep (.p3z m2 :: ls') =
            k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 := by omega
        rw [h_xi_eq] at hok_phi
        dsimp [hasP5, p5Suf] at hok_phi ⊢
        by_cases hmd : MustDrain (.p3z m2 :: ls') = true
        · have hpre := preP5Val_p3z_add2_of_not_headP5 m2 ls' (not_isHeadP5_of_MustDrain_p3z m2 ls' hmd)
          rw [hpre] at hok_phi
          exact hok_phi
        · have hmd_f : MustDrain (.p3z m2 :: ls') = false := Bool.eq_false_iff.mpr hmd
          rw [hmd_f] at hok_phi ⊢
          simpa using hok_phi
      rw [not_bool_if_false_eq_true hok_all]
      have hmd_bound' : (MustDrain (.p3z m2 :: ls') && decide (2 * c + 2 < k + epSum (.p3z m2 :: ls'))) = false := by
        rw [hmd_eq, hepsum_eq] at hmd_bound
        rw [show decide (2 * c + 2 < k + epSum (.p3z m2 :: ls')) =
          decide (2 * c + 4 < k + (epSum (.p3z m2 :: ls') + 2)) from decide_eq_of_iff (by omega)]
        exact hmd_bound
      rw [bool_if_false_eq_self hmd_bound']
      have hrst_0 : (decide (k = 0 ∧ c = 0 ∧ ds = []) && isHeadP3z1 (.p3z (m2 + 2) :: ls')) = false := by
        rw [show isHeadP3z1 (.p3z (m2 + 2) :: ls') = false from rfl, Bool.and_false]
      rw [hodd_eq, hepsum_eq] at hodd_branch
      have hd_odd : decide (2 * c + 2 ≥ k + epSum (.p3z m2 :: ls')) =
          decide (2 * c + 4 ≥ k + (epSum (.p3z m2 :: ls') + 2)) := decide_eq_of_iff (by omega)
      rw [hd_odd]
      by_cases h_cond : (hasOdd (.p3z m2 :: ls') && decide (2 * c + 4 ≥ k + (epSum (.p3z m2 :: ls') + 2))) = true
      · rw [if_pos h_cond, hrst_0, if_neg Bool.false_ne_true] at hodd_branch
        rw [if_pos h_cond]
        rw [hep_eq, hmd_eq] at hodd_branch
        have h_xi_eq : k + (epSum (.p3z m2 :: ls') + 2) + 2 * ep (.p3z m2 :: ls') =
            k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 := by omega
        rw [h_xi_eq] at hodd_branch
        dsimp [hasP5, p5Suf] at hodd_branch ⊢
        by_cases hmd : MustDrain (.p3z m2 :: ls') = true
        · have hpre := preP5Val_p3z_add2_of_not_headP5 m2 ls' (not_isHeadP5_of_MustDrain_p3z m2 ls' hmd)
          rw [hpre] at hodd_branch
          exact hodd_branch
        · have hmd_f : MustDrain (.p3z m2 :: ls') = false := Bool.eq_false_iff.mpr hmd
          rw [hmd_f] at hodd_branch ⊢
          simpa using hodd_branch
      · rw [if_neg h_cond]
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_pos hk, if_neg (by simp [isHeadP3z1])] at hf
      rw [if_pos hk, if_neg (by simp [isHeadP5])]
      rw [← checkChainAux_true_E_ge2_to_B_ge3_even fuel m2 ls' k c ds hk]
      exact hf
  · have hm1 : k % 2 = 1 := by omega
    have hne2 : ds ≠ [2] := ds_ne_two_of_checkDs2_ModeE_ge2 hds2 (Or.inr (Or.inr (Or.inl hm1)))
    have hds2' : checkDs2 (.ModeB_ge3 (.p3z m2 :: ls') k c ds) = true := by
      dsimp [checkDs2]; rw [if_pos hne2]
    rw [if_neg hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hvp5_0, hc⟩
    rw [not_bool_eq_false] at hvp5_0
    obtain ⟨suf, rfl, hz18, hvp5⟩ := ValidP5Chain_p3z_succ hvp5_0
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hck, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hck
    let nls := LTok.p3z k :: .p3z m2 :: .p5 :: suf
    have heven_nls : ValidEvenLs nls = true := by
      dsimp [nls, ValidEvenLs, ValidAfterOdd]
      rw [if_neg hk, decide_eq_true hz18, hvp5, Bool.true_and]
    have hmd_nls : MustDrain nls = true := by
      dsimp [nls, MustDrain]; rw [if_pos hm1]
    have h_gt_f : decide (k > 2 * c + 3) = false := decide_eq_false (by omega)
    have hz0_eq : z0 (.p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
    have hdz0_eq : dropZ0 (.p3z (m2 + 2) :: .p5 :: suf) = .p3z (m2 + 2) :: .p5 :: suf := rfl
    by_cases hb1 : ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 (.p3z (m2 + 2) :: .p5 :: suf) = true ∧
        headP3zVal (.p3z (m2 + 2) :: .p5 :: suf) ≥ 3
    · rcases hb1 with ⟨rfl, rfl, rfl, _, hm2_ge⟩
      dsimp [headP3zVal] at hm2_ge
      have hds1' : checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) 1 1 []) = true := rfl
      refine ⟨?_, ?_⟩
      · dsimp only [invCore]
        have h_g : (!GoodDs [] || !checkDs2 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) 1 1 []) ||
            !checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) 1 1 [])) = false := rfl
        rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega), not_bool_if_false_eq_true heven_nls]
        have hm2_pos : ∃ m2', m2 = m2' + 1 := ⟨m2 - 1, by omega⟩
        obtain ⟨m2', rfl⟩ := hm2_pos
        dsimp [isP3zGe1P5, MustDrain]
      · intro fuel
        have hf := hch fuel
        dsimp only [invChain] at hf ⊢
        have hb1_t : ([] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
            isP3zP5 (.p3z (m2 + 2) :: .p5 :: suf) = true ∧ headP3zVal (.p3z (m2 + 2) :: .p5 :: suf) ≥ 3 :=
          ⟨rfl, rfl, rfl, rfl, hm2_ge⟩
        rw [if_neg hk, if_pos hb1_t] at hf
        rw [if_neg hk, if_pos ⟨rfl, rfl, rfl⟩]
        exact hf
    · rw [if_neg hb1] at hc
      by_cases hb2 : ds = [] ∧
          ((k = 1 ∧ c = 1 ∧ z0 (.p3z (m2 + 2) :: .p5 :: suf) = 1) ∨
            (k = 3 ∧ c = 2 ∧ z0 (.p3z (m2 + 2) :: .p5 :: suf) = 0)) ∧
          isP3zP5 (dropZ0 (.p3z (m2 + 2) :: .p5 :: suf)) = true ∧
          headP3zVal (dropZ0 (.p3z (m2 + 2) :: .p5 :: suf)) ≥ 18 ∧
          z0 (p5Suf (.p3z (m2 + 2) :: .p5 :: suf)) ≥ 38
      · have hb2_orig := hb2
        rw [hz0_eq, hdz0_eq] at hb2
        dsimp [headP3zVal, p5Suf] at hb2
        rcases hb2 with ⟨rfl, h_or, _, hm2_ge, hz38⟩
        have hk3_c2 : k = 3 ∧ c = 2 := by omega
        rcases hk3_c2 with ⟨rfl, rfl⟩
        have hds1' : checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) 3 2 []) = true := rfl
        refine ⟨?_, ?_⟩
        · dsimp only [invCore]
          have h_g : (!GoodDs [] || !checkDs2 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) 3 2 []) ||
              !checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) 3 2 [])) = false := rfl
          rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega), not_bool_if_false_eq_true heven_nls]
          have hok_c1 : (if 2 ≥ 1 then
              if (!decide (3 = 1 ∧ 2 = 1 ∧ ([] : List Nat) = [])) = true then
                (decide (([] : List Nat) = [] ∧ 2 = 2 ∧ 3 = 3) && MustDrain nls &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val nls ≥ 16 ∧ z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (2 - 1) [] false
              else isP3zGe1P5 (.p3z m2 :: .p5 :: suf)
            else true) = true := by
            have h16_38 : decide (m2 ≥ 16 ∧ z0 suf ≥ 38) = true := decide_eq_true ⟨by omega, hz38⟩
            dsimp [nls, MustDrain, hasP5, preP5Val, p5Suf]
            simp [h16_38]
          rw [not_bool_if_false_eq_true hok_c1]
          have h16_38' : decide (([] : List Nat) = [] ∧ 2 - 1 = 1 ∧ 3 = 3 ∧ m2 ≥ 16 ∧ z0 suf ≥ 38) = true :=
            decide_eq_true ⟨rfl, rfl, rfl, by omega, hz38⟩
          have hpre_eq : preP5Val nls = m2 := rfl
          have hsuf_eq : p5Suf (.p3z m2 :: .p5 :: suf) = suf := rfl
          have hp5_eq : hasP5 (.p3z m2 :: .p5 :: suf) = true := rfl
          have hgp_t : GoodPsi (2 - 1) [] = true := rfl
          rw [hmd_nls, h_gt_f, hp5_eq, hpre_eq, hsuf_eq, hgp_t, h16_38']
          rfl
        · intro fuel
          cases fuel with
          | zero =>
            dsimp [invChain]; rfl
          | succ fuel' =>
            have hf := hch fuel'
            dsimp only [invChain] at hf ⊢
            rw [if_neg hk, if_neg hb1, if_pos hb2_orig] at hf
            rw [hdz0_eq] at hf
            dsimp only [headP3zVal, drop2L] at hf
            rw [if_neg hk, if_neg (by omega), if_neg (by omega)]
            dsimp only [checkChainAux]
            have hodd3 : hasOdd nls = true := rfl
            have hepsum3 : epSum nls = 2 := rfl
            have hep3 : ep nls = 0 := rfl
            have hp5_3 : hasP5 nls = true := rfl
            have hpre3 : preP5Val nls = m2 := rfl
            have hsuf3 : p5Suf nls = suf := rfl
            have hdec3 : decide (2 * 2 + 2 ≥ 0 + 2) = true := rfl
            rw [hodd3, hepsum3, hep3, hmd_nls, hp5_3, hpre3, hsuf3, hdec3]
            simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero]
            rw [if_neg (by omega), if_neg (by omega)]
            have hm_sub : m2 + 2 - 4 = m2 - 2 := by omega
            rw [hm_sub] at hf
            exact hf
      · rw [if_neg hb2] at hc
        rw [hz0_eq] at hc
        simp only [Nat.add_zero, Nat.mul_zero, Bool.and_eq_true] at hc
        rcases hc with ⟨⟨⟨hok_base, hc_9⟩, hc_1⟩, _⟩
        have hck_8_15 : c ≥ 8 ∧ k ≥ 15 := by
          split_ifs at hok_base <;> (simp only [decide_eq_true_eq] at hok_base; omega)
        have hf1 := hch 1
        dsimp only [invChain] at hf1
        rw [if_neg hk, if_neg hb1, if_neg hb2] at hf1
        dsimp only [checkChainAux] at hf1
        rw [hz0_eq, hdz0_eq] at hf1
        dsimp only [isHeadP5, drop1L] at hf1
        simp only [Nat.add_zero, Nat.mul_zero, Bool.not_false, Bool.true_and] at hf1
        rw [bool_if_false_eq_true] at hf1
        rcases hf1 with ⟨hphiw_f, hf1⟩
        rw [not_bool_eq_false] at hphiw_f
        rw [if_neg (by omega), bool_if_false_eq_true] at hf1
        rcases hf1 with ⟨hgp, _⟩
        rw [not_bool_eq_false] at hgp
        have hds1' : checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) k c ds) = true := by
          dsimp [checkDs1Phi1]
          by_cases h1 : ds = [1]
          · simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte]; rw [if_neg hk, decide_eq_false (by omega)]; rfl
          · simp [h1]
        refine ⟨?_, ?_⟩
        · dsimp only [invCore]
          have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) k c ds) ||
              !checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) k c ds)) = false := by
            simp [hgd, hds2', hds1']
          rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega), not_bool_if_false_eq_true heven_nls]
          have hrst_f : decide (k = 1 ∧ c = 1 ∧ ds = []) = false := decide_eq_false (by omega)
          have hok_c1 : (if c ≥ 1 then
              if (!decide (k = 1 ∧ c = 1 ∧ ds = [])) = true then
                (decide (ds = [] ∧ c = 2 ∧ k = 3) && MustDrain nls &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val nls ≥ 16 ∧ z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (c - 1) ds false
              else isP3zGe1P5 (.p3z m2 :: .p5 :: suf)
            else true) = true := by
            rw [if_pos (by omega), hrst_f, if_pos (by decide), hphiw_f, Bool.or_true]
          rw [not_bool_if_false_eq_true hok_c1]
          rw [hmd_nls, h_gt_f, Bool.and_false, if_neg Bool.false_ne_true, if_pos hck.2, hrst_f, if_neg Bool.false_ne_true]
          rw [hgp, Bool.true_and]
          have h_ds1_ok : ((!decide (ds = [1] ∧ c - 1 ≥ 24)) || decide (k ≥ 37)) = true := by
            by_cases h1 : ds = [1]
            · simp [h1] at hc_1; simp [hc_1]
            · simp [h1]
          have h_ds0_ok : ((!decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧ ((!hasP5 (.p3z m2 :: .p5 :: suf)) = true ∨ true = true))) ||
              decide (k ≥ 17)) = true := by
            by_cases h0 : (ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8
            · have hc9 : ((ds = [] ∨ ds = [0]) ∧ c ≥ 9) ∨ isOddDrainDs ds = true := Or.inl ⟨h0.1, by omega⟩
              rw [decide_eq_true hc9] at hc_9
              simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_9
              simp [hc_9]
            · have h_f : decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧ ((!hasP5 (.p3z m2 :: .p5 :: suf)) = true ∨ true = true)) = false :=
                decide_eq_false (fun ⟨h_a, h_b, _⟩ => h0 ⟨h_a, h_b⟩)
              rw [h_f]; rfl
          have h15_7 : decide (k ≥ 15 ∧ c - 1 ≥ 7) = true := decide_eq_true (by omega)
          rw [h_ds1_ok, h_ds0_ok, h15_7]
          simp
        · intro fuel
          cases fuel with
          | zero =>
            dsimp [invChain]
            rw [if_neg hk, if_neg (by omega), if_neg (by omega)]
            rfl
          | succ fuel' =>
            have hf := hch (fuel' + 1)
            dsimp only [invChain] at hf ⊢
            rw [if_neg hk, if_neg hb1, if_neg hb2] at hf
            rw [if_neg hk, if_neg (show ¬(k = 1 ∧ c = 1 ∧ ds = []) by omega), if_neg (show c ≠ 0 by omega)]
            dsimp only [checkChainAux] at hf
            rw [hz0_eq, hdz0_eq] at hf
            dsimp only [isHeadP5, drop1L] at hf
            simp only [Nat.add_zero, Nat.mul_zero, Bool.not_false, Bool.true_and, hphiw_f,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte, hgp] at hf
            rw [if_neg (by omega)] at hf
            have hodd_k : hasOdd nls = true := by dsimp [nls, hasOdd]; rw [if_pos hm1]
            have hepsum_k : epSum nls = k - 1 := by dsimp [nls, epSum]; rw [if_pos hm1]
            have hep_k : ep nls = 0 := by dsimp [nls, ep]; rw [if_pos hm1]
            have hp5_k : hasP5 nls = true := rfl
            have hpre_k : preP5Val nls = m2 := rfl
            have hsuf_k : p5Suf nls = suf := rfl
            have hdec_m : decide (2 * c + 2 ≥ 0 + (k - 1)) = true := decide_eq_true (by omega)
            dsimp only [checkChainAux]
            rw [hodd_k, hepsum_k, hep_k, hmd_nls, hp5_k, hpre_k, hsuf_k, hdec_m]
            simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
            have hk5 : k - 1 + 5 = k + 4 := by omega
            have hk3 : k - 1 + 3 = k + 2 := by omega
            have hk2 : k - 1 + 2 = k + 1 := by omega
            have hm_sub : m2 + 2 - 4 = m2 - 2 := by omega
            have hm_add : m2 + 2 + 1 = m2 + 3 := by omega
            have hm_m1 : m2 + 2 - 1 = m2 + 1 := by omega
            rw [hk5, hk3, hk2]
            rw [hm_sub, hm_add, hm_m1] at hf
            by_cases h_c1 : m2 % 2 = 0 ∧ m2 ≤ 2 * (k - 1) + 10
            · have h_c1' : (m2 + 2) % 2 = 0 ∧ m2 + 2 ≤ 2 * k + 10 := by omega
              rw [if_pos h_c1]
              rw [if_pos h_c1'] at hf
              exact hf
            · have h_c1' : ¬((m2 + 2) % 2 = 0 ∧ m2 + 2 ≤ 2 * k + 10) := by omega
              rw [if_neg h_c1]
              rw [if_neg h_c1'] at hf
              by_cases h_c2 : m2 % 2 = 1 ∧ m2 ≤ 2 * (k - 1) + 11
              · have h_c2' : (m2 + 2) % 2 = 1 ∧ m2 + 2 ≤ 2 * k + 11 := by omega
                rw [if_pos h_c2]
                rw [if_pos h_c2'] at hf
                exact hf
              · have h_c2' : ¬((m2 + 2) % 2 = 1 ∧ m2 + 2 ≤ 2 * k + 11) := by omega
                rw [if_neg h_c2]
                rw [if_neg h_c2'] at hf
                exact hf

lemma isOddDrainDs_cons_imp {d : Nat} {ds : List Nat} (h : isOddDrainDs (d :: ds) = true) :
    (ds = [] ∨ ds = [0]) ∧ d ≥ 9 := by
  cases ds with
  | nil =>
    dsimp [isOddDrainDs, isOddDrain1] at h
    rw [decide_eq_true_eq] at h
    exact ⟨Or.inl rfl, by omega⟩
  | cons d2 ds' =>
    cases d2 with
    | zero =>
      cases ds' with
      | nil =>
        simp only [isOddDrainDs, isOddDrain1, decide_eq_true_eq] at h
        exact ⟨Or.inr rfl, by omega⟩
      | cons _ _ => cases h
    | succ _ => cases h

lemma GoodPhiW_push_ge8 (phiW c : Nat) (ds : List Nat) (hc : c ≥ 7) (h15 : phiW ≥ 15)
    (hd25 : ds = [1] → c ≥ 24 → phiW ≥ 35)
    (hod : (ds = [] ∨ ds = [0]) → c ≥ 8 → phiW ≥ 17) :
    GoodPhiW phiW ((c + 1) :: ds) false = true := by
  have hne2 : (c + 1) :: ds ≠ [2] := by intro h; injection h with h1 _; omega
  have hne0 : (c + 1) :: ds ≠ [0] := by intro h; injection h with h1 _; omega
  have hne1 : (c + 1) :: ds ≠ [1] := by intro h; injection h with h1 _; omega
  have hnen : (c + 1) :: ds ≠ [] := by intro h; cases h
  dsimp only [GoodPhiW]
  rw [if_neg hne2, if_neg hne0, if_neg hne1, if_neg hnen]
  split_ifs with h_d25 h_od
  · cases ds with
    | nil => cases h_d25
    | cons d2 ds' =>
      cases ds' with
      | nil =>
        cases d2 with
        | zero => cases h_d25
        | succ d2' =>
          cases d2' with
          | zero =>
            have hc25 : c + 1 ≥ 25 := of_decide_eq_true h_d25
            exact decide_eq_true (hd25 rfl (by omega))
          | succ _ => cases h_d25
      | cons _ _ =>
        cases d2 with
        | zero => cases h_d25
        | succ d2' => cases d2' <;> cases h_d25
  · obtain ⟨h_ds, hc9⟩ := isOddDrainDs_cons_imp h_od
    exact decide_eq_true (hod h_ds (by omega))
  · exact decide_eq_true h15

lemma GoodPhiW_c_pos {c : Nat} {ds : List Nat} (hne2 : ds ≠ [2]) (h : GoodPhiW c ds false = true) :
    c ≥ 1 := by
  by_contra hc0
  have rfl_c : c = 0 := by omega
  subst rfl_c
  dsimp [GoodPhiW] at h
  rw [if_neg hne2] at h
  split_ifs at h <;> cases h

lemma GoodPhiW_nil_ge6 {c : Nat} (h : GoodPhiW c [] false = true) : c ≥ 6 := by
  dsimp [GoodPhiW] at h
  exact of_decide_eq_true h

lemma ValidAfterOdd_cases {ls' : List LTok} (h : ValidAfterOdd ls' = true) :
    ls' = [] ∨
    (∃ suf, ls' = .p5 :: suf ∧ z0 suf ≥ 18 ∧ ValidP5Chain suf = true) ∨
    (∃ m suf, ls' = .p3z m :: .p5 :: suf ∧ z0 suf ≥ 18 ∧ ValidP5Chain suf = true) := by
  cases ls' with
  | nil => exact Or.inl rfl
  | cons t rest =>
    cases t with
    | p5 =>
      dsimp [ValidAfterOdd] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inr (Or.inl ⟨rest, rfl, h.1, h.2⟩)
    | p3z m =>
      cases rest with
      | nil => cases h
      | cons t2 suf =>
        cases t2 with
        | p3z _ => cases h
        | p5 =>
          dsimp [ValidAfterOdd] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact Or.inr (Or.inr ⟨m, suf, rfl, h.1, h.2⟩)

lemma epSum_p3z_p5_ge14 {m2 : Nat} {suf : List LTok} (hm : m2 ≥ 14) :
    epSum (.p3z m2 :: .p5 :: suf) ≥ 14 := by
  dsimp [epSum]; split_ifs <;> omega

lemma step_Inv_ModeE_ge2_p3z1_odd (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hk : ¬(k % 2 = 0))
    (hinv : Inv (.ModeE_ge2 (.p3z 1 :: ls') k c ds)) :
    Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hc⟩
  rw [if_neg hk] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hvp5_0, hc⟩
  rw [not_bool_eq_false] at hvp5_0
  obtain ⟨suf, rfl, hz18, hvp5⟩ := ValidP5Chain_p3z_succ hvp5_0
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hck, hc⟩
  rw [not_bool_eq_false, decide_eq_true_eq] at hck
  have hb1 : ¬(ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 (.p3z 1 :: .p5 :: suf) = true ∧
      headP3zVal (.p3z 1 :: .p5 :: suf) ≥ 3) := by dsimp [headP3zVal]; omega
  have hb2 : ¬(ds = [] ∧
      ((k = 1 ∧ c = 1 ∧ z0 (.p3z 1 :: .p5 :: suf) = 1) ∨
        (k = 3 ∧ c = 2 ∧ z0 (.p3z 1 :: .p5 :: suf) = 0)) ∧
      isP3zP5 (dropZ0 (.p3z 1 :: .p5 :: suf)) = true ∧
      headP3zVal (dropZ0 (.p3z 1 :: .p5 :: suf)) ≥ 18 ∧
      z0 (p5Suf (.p3z 1 :: .p5 :: suf)) ≥ 38) := by
    have hdz : dropZ0 (.p3z 1 :: .p5 :: suf) = .p3z 1 :: .p5 :: suf := rfl
    rw [hdz]; dsimp [headP3zVal]; omega
  rw [if_neg hb1, if_neg hb2] at hc
  have hz0_eq : z0 (.p3z 1 :: .p5 :: suf) = 0 := rfl
  rw [hz0_eq] at hc
  simp only [Nat.add_zero, Nat.mul_zero, Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨hok_base, _⟩, _⟩, _⟩
  have hck_8_15 : c ≥ 8 ∧ k ≥ 15 := by
    split_ifs at hok_base <;> (simp only [decide_eq_true_eq] at hok_base; omega)
  have hf1 := hch 1
  dsimp only [invChain] at hf1
  rw [if_neg hk, if_neg hb1, if_neg hb2] at hf1
  have hdz : dropZ0 (.p3z 1 :: .p5 :: suf) = .p3z 1 :: .p5 :: suf := rfl
  dsimp only [checkChainAux] at hf1
  rw [hz0_eq, hdz] at hf1
  dsimp only [isHeadP5, drop1L] at hf1
  simp only [Nat.add_zero, Nat.mul_zero, Bool.not_false, Bool.true_and] at hf1
  rw [bool_if_false_eq_true] at hf1
  rcases hf1 with ⟨_, hf1⟩
  simp only [↓reduceIte, Bool.and_eq_true] at hf1
  have hgd' : GoodDs ((c + 1) :: ds) = true := hf1.1
  have hne2' : (c + 1) :: ds ≠ [2] := by intro h; injection h with h1 _; omega
  have hne1' : (c + 1) :: ds ≠ [1] := by intro h; injection h with h1 _; omega
  have hds2' : checkDs2 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true := by
    dsimp [checkDs2]; rw [if_pos hne2']
  have hds1' : checkDs1Phi1 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true := by
    dsimp [checkDs1Phi1]; rw [if_pos hne1']
  dsimp only [nextModeE_p3z1]
  have h1_odd : ¬(1 % 2 = 0) := by omega
  have hb1' : ¬((c + 1) :: ds = [] ∧ 1 = 1 ∧ k + 4 = 1 ∧ isP3zP5 suf = true ∧ headP3zVal suf ≥ 3) := by
    intro ⟨h, _⟩; cases h
  have hb2' : ¬((c + 1) :: ds = [] ∧
      ((1 = 1 ∧ k + 4 = 1 ∧ z0 suf = 1) ∨ (1 = 3 ∧ k + 4 = 2 ∧ z0 suf = 0)) ∧
      isP3zP5 (dropZ0 suf) = true ∧ headP3zVal (dropZ0 suf) ≥ 18 ∧ z0 (p5Suf suf) ≥ 38) := by
    intro ⟨h, _⟩; cases h
  refine ⟨?_, ?_⟩
  · dsimp only [invCore]
    have h_g : (!GoodDs ((c + 1) :: ds) || !checkDs2 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) ||
        !checkDs1Phi1 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds))) = false := by
      simp [hgd', hds2', hds1']
    rw [bool_if_false_eq_self h_g, if_neg h1_odd, not_bool_if_false_eq_true hvp5]
    rw [not_decide_if_false_eq_true (by omega)]
    rw [if_neg hb1', if_neg hb2']
    have h20 : decide (k + 4 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
    have h8 : decide (k + 4 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
    have h17 : decide (1 + 2 * z0 suf ≥ 17) = true := decide_eq_true (by omega)
    have h37 : decide (1 + 2 * z0 suf ≥ 37) = true := decide_eq_true (by omega)
    rw [h20, h8, ite_self, h17, h37]
    simp only [Bool.true_and, Bool.or_true]
    apply d25_check_of_ge36
    intro _ _ _; omega
  · intro fuel
    have hf := hch (fuel + 1)
    dsimp only [invChain] at hf ⊢
    rw [if_neg hk, if_neg hb1, if_neg hb2] at hf
    rw [if_neg h1_odd, if_neg hb1', if_neg hb2']
    dsimp only [checkChainAux] at hf
    rw [hz0_eq, hdz] at hf
    dsimp only [isHeadP5, drop1L] at hf
    simp only [Nat.add_zero, Nat.mul_zero, Bool.not_false, Bool.true_and] at hf
    rw [bool_if_false_eq_true] at hf
    rcases hf with ⟨_, hf⟩
    simp only [↓reduceIte, Bool.and_eq_true] at hf
    exact hf.2

lemma step_Inv_ModeE_ge2_p3z1_reset (ls' : List LTok)
    (hinv : Inv (.ModeE_ge2 (.p3z 1 :: ls') 0 0 [])) :
    Inv (nextModeE_p3z1 ls' 2 [1]) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hc⟩
  rw [if_pos rfl] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨heven, hc⟩
  rw [not_bool_eq_false] at heven
  dsimp [ValidEvenLs] at heven
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hc⟩
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hc⟩
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hc⟩
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hok_rst, _⟩
  rw [not_bool_eq_false] at hok_rst
  dsimp [isHeadP3z1, drop1L] at hok_rst
  rcases ValidAfterOdd_cases heven with rfl | ⟨suf, rfl, _, _⟩ | ⟨m, suf, rfl, hz18, hvp5⟩
  · refine ⟨by decide, ?_⟩
    intro fuel
    have hf := hch fuel
    dsimp only [invChain, drop1L, nextModeE_p3z1] at hf ⊢
    rw [if_pos rfl, if_pos ⟨rfl, rfl, rfl, rfl⟩] at hf
    rw [if_pos rfl, if_neg (by simp [isHeadP3z1])]
    exact hf
  · cases hok_rst
  · cases m with
    | zero => cases hok_rst
    | succ m' =>
      cases m' with
      | zero =>
        dsimp only [nextModeE_p3z1]
        have h1_odd : ¬(1 % 2 = 0) := by omega
        have hb1' : ¬([3, 1] = [] ∧ 1 = 1 ∧ 2 = 1 ∧ isP3zP5 suf = true ∧ headP3zVal suf ≥ 3) := by
          intro ⟨h, _⟩; cases h
        have hb2' : ¬([3, 1] = [] ∧
            ((1 = 1 ∧ 2 = 1 ∧ z0 suf = 1) ∨ (1 = 3 ∧ 2 = 2 ∧ z0 suf = 0)) ∧
            isP3zP5 (dropZ0 suf) = true ∧ headP3zVal (dropZ0 suf) ≥ 18 ∧ z0 (p5Suf suf) ≥ 38) := by
          intro ⟨h, _⟩; cases h
        refine ⟨?_, ?_⟩
        · dsimp only [invCore]
          have h_g : (!GoodDs [3, 1] || !checkDs2 (.ModeE_ge2 suf 1 2 [3, 1]) ||
              !checkDs1Phi1 (.ModeE_ge2 suf 1 2 [3, 1])) = false := rfl
          rw [bool_if_false_eq_self h_g, if_neg h1_odd, not_bool_if_false_eq_true hvp5]
          rw [not_decide_if_false_eq_true (by omega)]
          rw [if_neg hb1', if_neg hb2']
          have h20 : decide (2 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
          have h8 : decide (2 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
          have h17 : decide (1 + 2 * z0 suf ≥ 17) = true := decide_eq_true (by omega)
          have h37 : decide (1 + 2 * z0 suf ≥ 37) = true := decide_eq_true (by omega)
          rw [h20, h8, ite_self, h17, h37]
          simp only [Bool.true_and, Bool.or_true]
          rfl
        · intro fuel
          have hf := hch fuel
          dsimp only [invChain] at hf ⊢
          rw [if_pos rfl, if_pos ⟨rfl, rfl, rfl, rfl⟩] at hf
          dsimp only [drop1L, headP3zVal, drop2L, checkResetSufAux] at hf
          rw [if_neg h1_odd, if_neg hb1', if_neg hb2']
          exact hf
      | succ m2 =>
        dsimp only [nextModeE_p3z1]
        have heven_m2 : ValidEvenLs (.p3z m2 :: .p5 :: suf) = true := by
          dsimp [ValidEvenLs, ValidAfterOdd]
          split_ifs <;> simp [hz18, hvp5]
        have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 2 [1]) = true := by
          dsimp [checkDs1Phi1, isHeadP5, epW]
          by_cases hm2 : m2 % 2 = 1 <;> simp [hm2]
        refine ⟨?_, ?_⟩
        · dsimp only [invCore]
          have h_g : (!GoodDs [1] || !checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 2 [1]) ||
              !checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 2 [1])) = false := by
            simp [GoodDs, GoodDsAux, GoodDs1, checkDs2, hds1']
          rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven_m2]
          have hpref0 : prefSumW (.p3z m2 :: .p5 :: suf) = 0 := by
            dsimp [prefSumW]; split_ifs <;> rfl
          rw [hpref0, not_decide_if_false_eq_true (by omega)]
          have hepw0 : epW (.p3z m2 :: .p5 :: suf) = 0 := by
            dsimp [epW]; split_ifs <;> rfl
          have hmd0 : MustDrain (.p3z m2 :: .p5 :: suf) = false := by
            dsimp [MustDrain]; split_ifs <;> rfl
          have hok_phi' : (if (!isHeadP5 (.p3z m2 :: .p5 :: suf)) = true then
              (decide ([1] = [] ∧ 2 + epW (.p3z m2 :: .p5 :: suf) = 1) && MustDrain (.p3z m2 :: .p5 :: suf) &&
                decide (2 + ep (.p3z m2 :: .p5 :: suf) = 1 ∧ 0 + epSum (.p3z m2 :: .p5 :: suf) + 2 * ep (.p3z m2 :: .p5 :: suf) = 2) &&
                hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val (.p3z m2 :: .p5 :: suf) ≥ 16 ∧ z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                GoodPhiW (2 + epW (.p3z m2 :: .p5 :: suf)) [1] (isHeadP3z1 (.p3z m2 :: .p5 :: suf) && decide (0 = 0 ∧ 2 = 0 ∧ [1] = []))
            else
              decide (2 = 0 ∧ [1] = [] ∧ 0 = 2) || (decide (2 ≥ 1) && GoodPhiW (2 - 1) [1] false)) = true := by
            dsimp [isHeadP5]; rw [hepw0]; simp [GoodPhiW]
          rw [not_bool_if_false_eq_true hok_phi']
          rw [hmd0, Bool.false_and, if_neg Bool.false_ne_true]
          have hrst_f : (decide (0 = 0 ∧ 2 = 0 ∧ [1] = []) && isHeadP3z1 (.p3z m2 :: .p5 :: suf)) = false := rfl
          rw [hrst_f]
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
          by_cases h_cond : (hasOdd (.p3z m2 :: .p5 :: suf) && decide (2 * 2 + 4 ≥ 0 + epSum (.p3z m2 :: .p5 :: suf))) = true
          · rw [if_pos h_cond]
            have hm2_odd : m2 % 2 = 1 := by
              by_contra hm2_ev
              have : hasOdd (.p3z m2 :: .p5 :: suf) = false := by dsimp [hasOdd]; rw [if_neg hm2_ev]
              rw [this] at h_cond; cases h_cond
            have hep0 : ep (.p3z m2 :: .p5 :: suf) = 0 := by dsimp [ep]; rw [if_pos hm2_odd]
            simp [hep0, GoodPsi, GoodDs, GoodDsAux, GoodDs2]
          · rw [if_neg h_cond]
        · intro fuel
          have hf := hch fuel
          dsimp only [invChain] at hf ⊢
          rw [if_pos rfl, if_pos ⟨rfl, rfl, rfl, rfl⟩] at hf
          dsimp only [drop1L, headP3zVal, drop2L, checkResetSufAux] at hf
          rw [if_neg (show m2 + 2 ≠ 1 by omega)] at hf
          rw [if_pos rfl, if_neg (by omega)]
          exact hf

lemma step_Inv_ModeE_ge2_p3z1_even_nonreset (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hk : k % 2 = 0) (hrst : ¬(k = 0 ∧ c = 0 ∧ ds = []))
    (hinv : Inv (.ModeE_ge2 (.p3z 1 :: ls') k c ds)) :
    Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, _⟩
  rw [if_pos hk] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨heven, hc⟩
  rw [not_bool_eq_false] at heven
  dsimp [ValidEvenLs] at heven
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hk_le, hc⟩
  rw [not_bool_eq_false, decide_eq_true_eq] at hk_le
  dsimp [prefSumW] at hk_le
  have hne2 : ds ≠ [2] := by
    apply ds_ne_two_of_checkDs2_ModeE_ge2 hds2
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    dsimp [epSum]; omega
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨hok_phi, hc⟩
  rw [not_bool_eq_false] at hok_phi
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hc⟩
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨_, hodd_branch⟩
  have h_odd_t : (hasOdd (.p3z 1 :: ls') && decide (2 * c + 4 ≥ k + epSum (.p3z 1 :: ls'))) = true := by
    dsimp [hasOdd, epSum]; simp [hk_le.1]
  have hrst_f : (decide (k = 0 ∧ c = 0 ∧ ds = []) && isHeadP3z1 (.p3z 1 :: ls')) = false := by
    rw [decide_eq_false hrst, Bool.false_and]
  rw [if_pos h_odd_t, hrst_f, if_neg Bool.false_ne_true] at hodd_branch
  have hep0 : ep (.p3z 1 :: ls') = 0 := rfl
  have hepw0 : epW (.p3z 1 :: ls') = 0 := rfl
  have hepsum0 : epSum (.p3z 1 :: ls') = 0 := rfl
  rw [hep0, hepsum0, Nat.add_zero, Nat.mul_zero, Nat.add_zero] at hodd_branch
  simp only [Bool.and_eq_true] at hodd_branch
  rcases hodd_branch with ⟨⟨⟨hgp, hc_ds1⟩, hc_ds0⟩, hc_md⟩
  have hgd' : GoodDs ((c + 1) :: ds) = true := hgp
  have hd25_imp : ds = [1] → c ≥ 24 → k ≥ 36 := by
    intro h1 hc24
    rw [decide_eq_true ⟨h1, hc24⟩, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_ds1
    exact hc_ds1
  have hrst_ch : ¬(k = 0 ∧ c = 0 ∧ ds = [] ∧ isHeadP3z1 (.p3z 1 :: ls') = true) :=
    fun ⟨hk0, hc0, hds0, _⟩ => hrst ⟨hk0, hc0, hds0⟩
  rcases ValidAfterOdd_cases heven with rfl | ⟨suf, rfl, hz18, hvp5⟩ | ⟨m, suf, rfl, hz18, hvp5⟩
  · dsimp only [nextModeE_p3z1]
    have hmd_t : MustDrain [.p3z 1] = true := rfl
    have hp5_f : hasP5 [.p3z 1] = false := rfl
    have hpre0 : preP5Val [.p3z 1] = 0 := rfl
    rw [hmd_t, hpre0] at hc_md
    have h_f3 : decide (ds = [] ∧ c = 1 ∧ k = 2 ∧ 0 ≥ 16 ∧ z0 (p5Suf [.p3z 1]) ≥ 38) = false :=
      decide_eq_false (by omega)
    rw [h_f3, Bool.or_false, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_md
    have hod_imp : (ds = [] ∨ ds = [0]) → c ≥ 8 → k ≥ 16 := by
      intro h0 hc8
      have h_t : (ds = [] ∨ ds = [0]) ∧ c ≥ 8 ∧ ((!hasP5 [.p3z 1]) = true ∨ MustDrain [.p3z 1] = true) :=
        ⟨h0, hc8, Or.inl rfl⟩
      rw [decide_eq_true h_t, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_ds0
      exact hc_ds0
    have hphiw' : GoodPhiW (k + 2) ((c + 1) :: ds) false = true :=
      GoodPhiW_push_ge8 (k + 2) c ds hc_md.2 (by omega)
        (fun h1 hc24 => by have := hd25_imp h1 hc24; omega)
        (fun h0 hc8 => by have := hod_imp h0 hc8; omega)
    have hne2' : (c + 1) :: ds ≠ [2] := by intro h; injection h with h1 _; omega
    have hne1' : (c + 1) :: ds ≠ [1] := by intro h; injection h with h1 _; omega
    have hds2' : checkDs2 (.ModeE_ge2 [] 0 (k + 2) ((c + 1) :: ds)) = true := by
      dsimp [checkDs2]; rw [if_pos hne2']
    have hds1' : checkDs1Phi1 (.ModeE_ge2 [] 0 (k + 2) ((c + 1) :: ds)) = true := by
      dsimp [checkDs1Phi1]; rw [if_pos hne1']
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ((c + 1) :: ds) || !checkDs2 (.ModeE_ge2 [] 0 (k + 2) ((c + 1) :: ds)) ||
          !checkDs1Phi1 (.ModeE_ge2 [] 0 (k + 2) ((c + 1) :: ds))) = false := by
        simp [hgd', hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_pos rfl]
      dsimp [ValidEvenLs, prefSumW]
      have hok_phi' : (if (!isHeadP5 []) = true then
          (decide ((c + 1) :: ds = [] ∧ k + 2 + epW [] = 1) && MustDrain [] &&
            decide (k + 2 + ep [] = 1 ∧ 0 + epSum [] + 2 * ep [] = 2) &&
            hasP5 [] && decide (preP5Val [] ≥ 16 ∧ z0 (p5Suf []) ≥ 38)) ||
            GoodPhiW (k + 2 + epW []) ((c + 1) :: ds) (isHeadP3z1 [] && decide (0 = 0 ∧ k + 2 = 0 ∧ (c + 1) :: ds = []))
        else
          decide (k + 2 = 0 ∧ (c + 1) :: ds = [] ∧ 0 = 2) || (decide (k + 2 ≥ 1) && GoodPhiW (k + 1) ((c + 1) :: ds) false)) = true := by
        dsimp [isHeadP5, epW, isHeadP3z1]
        simp [hphiw']
      rw [not_bool_if_false_eq_true hok_phi']
      dsimp [MustDrain, isHeadP3z1, hasOdd]
    · intro fuel
      have hf := hch (fuel + 1)
      dsimp only [invChain] at hf ⊢
      rw [if_pos hk, if_neg hrst_ch] at hf
      rw [if_pos rfl, if_neg (by simp [isHeadP3z1])]
      dsimp only [checkChainAux] at hf
      have hodd1 : hasOdd [.p3z 1] = true := rfl
      have hepsum1 : epSum [.p3z 1] = 0 := rfl
      have hep1 : ep [.p3z 1] = 0 := rfl
      have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
      rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_f] at hf
      simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero, Nat.mul_zero] at hf
      exact hf
  · dsimp only [nextModeE_p3z1]
    have hmd_f : MustDrain (.p3z 1 :: .p5 :: suf) = false := rfl
    have hip5_f : (!isHeadP5 (.p3z 1 :: .p5 :: suf)) = true := rfl
    rw [if_pos hip5_f, hmd_f, hepw0, Nat.add_zero, Bool.and_comm (isHeadP3z1 _), hrst_f] at hok_phi
    simp only [Bool.and_false, Bool.false_and, Bool.false_or] at hok_phi
    have hc_pos : c ≥ 1 := GoodPhiW_c_pos hne2 hok_phi
    have hne2' : (c + 1) :: ds ≠ [2] := by
      intro h; injection h with h1 h2; subst h2
      have hc6 := GoodPhiW_nil_ge6 hok_phi; omega
    have hne1' : (c + 1) :: ds ≠ [1] := by intro h; injection h with h1 _; omega
    have hds2' : checkDs2 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true := by
      dsimp [checkDs2]; rw [if_pos hne2']
    have hds1' : checkDs1Phi1 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true := by
      dsimp [checkDs1Phi1]; rw [if_pos hne1']
    have h1_odd : ¬(1 % 2 = 0) := by omega
    have hb1' : ¬((c + 1) :: ds = [] ∧ 1 = 1 ∧ k + 4 = 1 ∧ isP3zP5 suf = true ∧ headP3zVal suf ≥ 3) := by
      intro ⟨h, _⟩; cases h
    have hb2' : ¬((c + 1) :: ds = [] ∧
        ((1 = 1 ∧ k + 4 = 1 ∧ z0 suf = 1) ∨ (1 = 3 ∧ k + 4 = 2 ∧ z0 suf = 0)) ∧
        isP3zP5 (dropZ0 suf) = true ∧ headP3zVal (dropZ0 suf) ≥ 18 ∧ z0 (p5Suf suf) ≥ 38) := by
      intro ⟨h, _⟩; cases h
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ((c + 1) :: ds) || !checkDs2 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) ||
          !checkDs1Phi1 (.ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds))) = false := by
        simp [hgd', hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_neg h1_odd, not_bool_if_false_eq_true hvp5]
      rw [not_decide_if_false_eq_true (by omega)]
      rw [if_neg hb1', if_neg hb2']
      have h20 : decide (k + 4 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
      have h8 : decide (k + 4 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
      have h17 : decide (1 + 2 * z0 suf ≥ 17) = true := decide_eq_true (by omega)
      have h37 : decide (1 + 2 * z0 suf ≥ 37) = true := decide_eq_true (by omega)
      rw [h20, h8, ite_self, h17, h37]
      simp only [Bool.true_and, Bool.or_true]
      apply d25_check_of_ge36
      intro d hd_eq hd25
      injection hd_eq with hd1 hds_eq
      have := hd25_imp hds_eq (by omega)
      omega
    · intro fuel
      have hf := hch (fuel + 1)
      dsimp only [invChain] at hf ⊢
      rw [if_pos hk, if_neg hrst_ch] at hf
      rw [if_neg h1_odd, if_neg hb1', if_neg hb2']
      dsimp only [checkChainAux] at hf
      have hodd1 : hasOdd (.p3z 1 :: .p5 :: suf) = true := rfl
      have hepsum1 : epSum (.p3z 1 :: .p5 :: suf) = 0 := rfl
      have hep1 : ep (.p3z 1 :: .p5 :: suf) = 0 := rfl
      have hp5_1 : hasP5 (.p3z 1 :: .p5 :: suf) = true := rfl
      have hsuf1 : p5Suf (.p3z 1 :: .p5 :: suf) = suf := rfl
      have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
      rw [hodd1, hepsum1, hep1, hdec1, hmd_f, hp5_1, hsuf1] at hf
      simp only [Bool.and_true, ↓reduceIte, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        Nat.add_zero, Nat.mul_zero, Bool.and_eq_true] at hf
      exact hf.2
  · have hmd_t : MustDrain (.p3z 1 :: .p3z m :: .p5 :: suf) = true := rfl
    have hp5_t : hasP5 (.p3z 1 :: .p3z m :: .p5 :: suf) = true := rfl
    have hpre_m : preP5Val (.p3z 1 :: .p3z m :: .p5 :: suf) = m := rfl
    have hsuf_m : p5Suf (.p3z 1 :: .p3z m :: .p5 :: suf) = suf := rfl
    rw [hmd_t, hpre_m, hsuf_m] at hc_md
    have hod_imp : (ds = [] ∨ ds = [0]) → c ≥ 8 → k ≥ 16 := by
      intro h0 hc8
      have h_t : (ds = [] ∨ ds = [0]) ∧ c ≥ 8 ∧
          ((!hasP5 (.p3z 1 :: .p3z m :: .p5 :: suf)) = true ∨ MustDrain (.p3z 1 :: .p3z m :: .p5 :: suf) = true) :=
        ⟨h0, hc8, Or.inr rfl⟩
      rw [decide_eq_true h_t, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_ds0
      exact hc_ds0
    cases m with
    | zero =>
      dsimp only [nextModeE_p3z1]
      have h_f3 : decide (ds = [] ∧ c = 1 ∧ k = 2 ∧ 0 ≥ 16 ∧ z0 suf ≥ 38) = false :=
        decide_eq_false (by omega)
      rw [h_f3, Bool.or_false, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_md
      have hphiw' : GoodPhiW (k + 2) ((c + 1) :: ds) false = true :=
        GoodPhiW_push_ge8 (k + 2) c ds hc_md.2 (by omega)
          (fun h1 hc24 => by have := hd25_imp h1 hc24; omega)
          (fun h0 hc8 => by have := hod_imp h0 hc8; omega)
      have hne2' : (c + 1) :: ds ≠ [2] := by intro h; injection h with h1 _; omega
      have hne1' : (c + 1) :: ds ≠ [1] := by intro h; injection h with h1 _; omega
      have hds2' : checkDs2 (.ModeE_ge2 (.p5 :: suf) 0 (k + 3) ((c + 1) :: ds)) = true := by
        dsimp [checkDs2]; rw [if_pos hne2']
      have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p5 :: suf) 0 (k + 3) ((c + 1) :: ds)) = true := by
        dsimp [checkDs1Phi1]; rw [if_pos hne1']
      have heven_p5 : ValidEvenLs (.p5 :: suf) = true := by
        dsimp [ValidEvenLs]; simp [hz18, hvp5]
      refine ⟨?_, ?_⟩
      · dsimp only [invCore]
        have h_g : (!GoodDs ((c + 1) :: ds) || !checkDs2 (.ModeE_ge2 (.p5 :: suf) 0 (k + 3) ((c + 1) :: ds)) ||
            !checkDs1Phi1 (.ModeE_ge2 (.p5 :: suf) 0 (k + 3) ((c + 1) :: ds))) = false := by
          simp [hgd', hds2', hds1']
        rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven_p5]
        dsimp [prefSumW]
        have hok_phi' : (if (!isHeadP5 (.p5 :: suf)) = true then
            (decide ((c + 1) :: ds = [] ∧ k + 2 + 1 + epW (.p5 :: suf) = 1) && MustDrain (.p5 :: suf) &&
              decide (k + 2 + 1 + ep (.p5 :: suf) = 1 ∧ 0 + epSum (.p5 :: suf) + 2 * ep (.p5 :: suf) = 2) &&
              hasP5 (.p5 :: suf) && decide (preP5Val (.p5 :: suf) ≥ 16 ∧ z0 (p5Suf (.p5 :: suf)) ≥ 38)) ||
              GoodPhiW (k + 2 + 1 + epW (.p5 :: suf)) ((c + 1) :: ds) (isHeadP3z1 (.p5 :: suf) && decide (0 = 0 ∧ k + 2 + 1 = 0 ∧ (c + 1) :: ds = []))
          else
            decide (k + 2 + 1 = 0 ∧ (c + 1) :: ds = [] ∧ 0 = 2) || (decide (k + 2 + 1 ≥ 1) && GoodPhiW (k + 2) ((c + 1) :: ds) false)) = true := by
          dsimp [isHeadP5]
          simp [hphiw']
        rw [not_bool_if_false_eq_true hok_phi']
        dsimp [MustDrain, isHeadP3z1, hasOdd]
      · intro fuel
        cases fuel with
        | zero =>
          dsimp [invChain]; rfl
        | succ fuel' =>
          have hf := hch (fuel' + 1)
          dsimp only [invChain] at hf ⊢
          rw [if_pos hk, if_neg hrst_ch] at hf
          rw [if_pos rfl, if_neg (by simp [isHeadP3z1])]
          dsimp only [checkChainAux] at hf ⊢
          have hodd1 : hasOdd (.p3z 1 :: .p3z 0 :: .p5 :: suf) = true := rfl
          have hepsum1 : epSum (.p3z 1 :: .p3z 0 :: .p5 :: suf) = 0 := rfl
          have hep1 : ep (.p3z 1 :: .p3z 0 :: .p5 :: suf) = 0 := rfl
          have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
          rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m, hsuf_m] at hf
          simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
            Nat.add_zero, Nat.mul_zero] at hf
          have h_c0 : True ∧ 0 ≤ 2 * k + 10 := ⟨trivial, by omega⟩
          rw [if_pos h_c0] at hf
          dsimp [hasOdd, hasP5, isHeadP5, p5Suf, ep, epSum]
          exact hf
    | succ m' =>
      cases m' with
      | zero =>
        dsimp only [nextModeE_p3z1]
        have h_f3 : decide (ds = [] ∧ c = 1 ∧ k = 2 ∧ 1 ≥ 16 ∧ z0 suf ≥ 38) = false :=
          decide_eq_false (by omega)
        rw [h_f3, Bool.or_false, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_md
        have hf1 := hch 1
        dsimp only [invChain] at hf1
        rw [if_pos hk, if_neg hrst_ch] at hf1
        dsimp only [checkChainAux] at hf1
        have hodd1 : hasOdd (.p3z 1 :: .p3z 1 :: .p5 :: suf) = true := rfl
        have hepsum1 : epSum (.p3z 1 :: .p3z 1 :: .p5 :: suf) = 0 := rfl
        have hep1 : ep (.p3z 1 :: .p3z 1 :: .p5 :: suf) = 0 := rfl
        have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
        rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m] at hf1
        simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
          Nat.add_zero, Nat.mul_zero] at hf1
        have h_c2 : True ∧ 0 + 1 ≤ 2 * k + 11 := ⟨trivial, by omega⟩
        rw [if_pos h_c2] at hf1
        have hgd'' : GoodDs ((k + 3) :: (c + 1) :: ds) = true := hf1
        have hds2' : checkDs2 (.ModeE_ge2 suf 1 2 ((k + 3) :: (c + 1) :: ds)) = true := by
          dsimp [checkDs2]
        have hds1' : checkDs1Phi1 (.ModeE_ge2 suf 1 2 ((k + 3) :: (c + 1) :: ds)) = true := by
          dsimp [checkDs1Phi1]
        have h1_odd : ¬(1 % 2 = 0) := by omega
        have hb1' : ¬((k + 3) :: (c + 1) :: ds = [] ∧ 1 = 1 ∧ 2 = 1 ∧ isP3zP5 suf = true ∧ headP3zVal suf ≥ 3) := by
          intro ⟨h, _⟩; cases h
        have hb2' : ¬((k + 3) :: (c + 1) :: ds = [] ∧
            ((1 = 1 ∧ 2 = 1 ∧ z0 suf = 1) ∨ (1 = 3 ∧ 2 = 2 ∧ z0 suf = 0)) ∧
            isP3zP5 (dropZ0 suf) = true ∧ headP3zVal (dropZ0 suf) ≥ 18 ∧ z0 (p5Suf suf) ≥ 38) := by
          intro ⟨h, _⟩; cases h
        refine ⟨?_, ?_⟩
        · dsimp only [invCore]
          have h_g : (!GoodDs ((k + 3) :: (c + 1) :: ds) ||
              !checkDs2 (.ModeE_ge2 suf 1 2 ((k + 3) :: (c + 1) :: ds)) ||
              !checkDs1Phi1 (.ModeE_ge2 suf 1 2 ((k + 3) :: (c + 1) :: ds))) = false := by
            simp [hgd'', hds2', hds1']
          rw [bool_if_false_eq_self h_g, if_neg h1_odd, not_bool_if_false_eq_true hvp5]
          rw [not_decide_if_false_eq_true (by omega)]
          rw [if_neg hb1', if_neg hb2']
          have h20 : decide (2 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
          have h8 : decide (2 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true := decide_eq_true (by omega)
          have h17 : decide (1 + 2 * z0 suf ≥ 17) = true := decide_eq_true (by omega)
          have h37 : decide (1 + 2 * z0 suf ≥ 37) = true := decide_eq_true (by omega)
          rw [h20, h8, ite_self, h17, h37]
          simp only [Bool.true_and, Bool.or_true]
          apply d25_check_of_ge36
          intro d hd_eq _
          injection hd_eq with _ hd2
          injection hd2 with hc1 _
          omega
        · intro fuel
          have hf := hch (fuel + 1)
          dsimp only [invChain] at hf ⊢
          rw [if_pos hk, if_neg hrst_ch] at hf
          rw [if_neg h1_odd, if_neg hb1', if_neg hb2']
          dsimp only [checkChainAux] at hf
          rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m, hsuf_m] at hf
          simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
            Nat.add_zero, Nat.mul_zero] at hf
          rw [if_pos h_c2] at hf
          exact (Bool.and_eq_true _ _).mp hf |>.2
      | succ m2 =>
        dsimp only [nextModeE_p3z1]
        have heven_m2 : ValidEvenLs (.p3z m2 :: .p5 :: suf) = true := by
          dsimp [ValidEvenLs, ValidAfterOdd]
          split_ifs <;> simp [hz18, hvp5]
        have hpref0 : prefSumW (.p3z m2 :: .p5 :: suf) = 0 := by
          dsimp [prefSumW]; split_ifs <;> rfl
        have hepw0_m2 : epW (.p3z m2 :: .p5 :: suf) = 0 := by
          dsimp [epW]; split_ifs <;> rfl
        have hmd0_m2 : MustDrain (.p3z m2 :: .p5 :: suf) = false := by
          dsimp [MustDrain]; split_ifs <;> rfl
        rw [Bool.not_true, Bool.false_or] at hc_md
        rcases Bool.or_eq_true_iff.mp hc_md with h14_7 | hphi1
        · rw [decide_eq_true_eq] at h14_7
          have hphiw' : GoodPhiW (k + 2) ((c + 1) :: ds) false = true :=
            GoodPhiW_push_ge8 (k + 2) c ds h14_7.2 (by omega)
              (fun h1 hc24 => by have := hd25_imp h1 hc24; omega)
              (fun h0 hc8 => by have := hod_imp h0 hc8; omega)
          have hne2' : (c + 1) :: ds ≠ [2] := by intro h; injection h with h1 _; omega
          have hne1' : (c + 1) :: ds ≠ [1] := by intro h; injection h with h1 _; omega
          have hds2' : checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) = true := by
            dsimp [checkDs2]; rw [if_pos hne2']
          have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) = true := by
            dsimp [checkDs1Phi1]; rw [if_pos hne1']
          refine ⟨?_, ?_⟩
          · dsimp only [invCore]
            have h_g : (!GoodDs ((c + 1) :: ds) ||
                !checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) ||
                !checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds))) = false := by
              simp [hgd', hds2', hds1']
            rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven_m2]
            rw [hpref0, not_decide_if_false_eq_true (by omega)]
            have hok_phi' : (if (!isHeadP5 (.p3z m2 :: .p5 :: suf)) = true then
                (decide ((c + 1) :: ds = [] ∧ k + 2 + epW (.p3z m2 :: .p5 :: suf) = 1) && MustDrain (.p3z m2 :: .p5 :: suf) &&
                  decide (k + 2 + ep (.p3z m2 :: .p5 :: suf) = 1 ∧ 0 + epSum (.p3z m2 :: .p5 :: suf) + 2 * ep (.p3z m2 :: .p5 :: suf) = 2) &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val (.p3z m2 :: .p5 :: suf) ≥ 16 ∧ z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (k + 2 + epW (.p3z m2 :: .p5 :: suf)) ((c + 1) :: ds)
                    (isHeadP3z1 (.p3z m2 :: .p5 :: suf) && decide (0 = 0 ∧ k + 2 = 0 ∧ (c + 1) :: ds = []))
              else
                decide (k + 2 = 0 ∧ (c + 1) :: ds = [] ∧ 0 = 2) || (decide (k + 2 ≥ 1) && GoodPhiW (k + 2 - 1) ((c + 1) :: ds) false)) = true := by
              dsimp [isHeadP5]; rw [hepw0_m2, Nat.add_zero, GoodPhiW_mono _ _ _ hphiw', Bool.or_true]
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd0_m2, Bool.false_and, if_neg Bool.false_ne_true]
            have hrst_f' : (decide (0 = 0 ∧ k + 2 = 0 ∧ (c + 1) :: ds = []) && isHeadP3z1 (.p3z m2 :: .p5 :: suf)) = false := by
              rw [decide_eq_false (by omega), Bool.false_and]
            rw [hrst_f']
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            by_cases h_cond : (hasOdd (.p3z m2 :: .p5 :: suf) && decide (2 * (k + 2) + 4 ≥ 0 + epSum (.p3z m2 :: .p5 :: suf))) = true
            · rw [if_pos h_cond]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cond
              have hm2_odd : m2 % 2 = 1 := by
                by_contra hm2_ev
                have : hasOdd (.p3z m2 :: .p5 :: suf) = false := by dsimp [hasOdd]; rw [if_neg hm2_ev]
                rw [this] at h_cond; cases h_cond.1
              have hep0_m2 : ep (.p3z m2 :: .p5 :: suf) = 0 := by dsimp [ep]; rw [if_pos hm2_odd]
              have hepsum_m2 : epSum (.p3z m2 :: .p5 :: suf) = m2 - 1 := by dsimp [epSum]; rw [if_pos hm2_odd]
              rw [hepsum_m2] at h_cond
              have hf1 := hch 1
              dsimp only [invChain] at hf1
              rw [if_pos hk, if_neg hrst_ch] at hf1
              dsimp only [checkChainAux] at hf1
              have hodd1 : hasOdd (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = true := rfl
              have hepsum1 : epSum (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
              have hep1 : ep (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
              have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
              rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m] at hf1
              simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
                Nat.add_zero, Nat.mul_zero] at hf1
              have hm2_le : 2 * (k + 2) + 4 ≥ m2 - 1 := by have := h_cond.2; omega
              have h_c1_m2 : ¬((m2 + 1 + 1) % 2 = 0 ∧ m2 + 1 + 1 ≤ 2 * k + 10) := by omega
              have h_c2_m2 : (m2 + 1 + 1) % 2 = 1 ∧ m2 + 1 + 1 ≤ 2 * k + 11 := by omega
              rw [if_neg h_c1_m2, if_pos h_c2_m2] at hf1
              have hgp' : GoodPsi (k + 2 + ep (.p3z m2 :: .p5 :: suf)) ((c + 1) :: ds) = true := by
                rw [hep0_m2, Nat.add_zero]; exact hf1
              rw [hgp']
              have hf_ds1 : decide ((c + 1) :: ds = [1] ∧ k + 2 + ep (.p3z m2 :: .p5 :: suf) ≥ 24) = false :=
                decide_eq_false (fun ⟨h, _⟩ => hne1' h)
              have hf_ds0 : decide (((c + 1) :: ds = [] ∨ (c + 1) :: ds = [0]) ∧ k + 2 + ep (.p3z m2 :: .p5 :: suf) ≥ 8 ∧
                  ((!hasP5 (.p3z m2 :: .p5 :: suf)) = true ∨ False)) = false := by
                apply decide_eq_false
                rintro ⟨h_or, _⟩
                rcases h_or with h | h
                · cases h
                · injection h with h1 _; omega
              rw [hf_ds1, hf_ds0]
              simp
            · rw [if_neg h_cond]
          · intro fuel
            have hrst_ch' : ¬(0 = 0 ∧ k + 2 = 0 ∧ (c + 1) :: ds = [] ∧ isHeadP3z1 (.p3z m2 :: .p5 :: suf) = true) := by
              omega
            by_cases h_c1 : (m2 + 2) % 2 = 0 ∧ m2 + 2 ≤ 2 * k + 10
            · cases fuel with
              | zero =>
                dsimp [invChain]; rfl
              | succ fuel' =>
                have hf := hch (fuel' + 1)
                dsimp only [invChain] at hf ⊢
                rw [if_pos hk, if_neg hrst_ch] at hf
                rw [if_pos rfl, if_neg hrst_ch']
                dsimp only [checkChainAux] at hf ⊢
                have hodd1 : hasOdd (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = true := rfl
                have hepsum1 : epSum (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
                have hep1 : ep (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
                have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
                rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m, hsuf_m] at hf
                simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
                  Nat.add_zero, Nat.mul_zero] at hf
                rw [if_pos h_c1] at hf
                have hm2_ev : ¬(m2 % 2 = 1) := by omega
                have hodd_m2 : hasOdd (.p3z m2 :: .p5 :: suf) = false := by dsimp [hasOdd]; rw [if_neg hm2_ev]
                have hp5_m2 : hasP5 (.p3z m2 :: .p5 :: suf) = true := rfl
                have hip5_m2 : isHeadP5 (.p3z m2 :: .p5 :: suf) = false := rfl
                have hepsum_m2 : epSum (.p3z m2 :: .p5 :: suf) = m2 := by dsimp [epSum]; rw [if_neg hm2_ev]
                have hep_m2 : ep (.p3z m2 :: .p5 :: suf) = 1 := by dsimp [ep]; rw [if_neg hm2_ev]
                have hsuf_m2 : p5Suf (.p3z m2 :: .p5 :: suf) = suf := rfl
                have hdec_m2 : decide (2 * (k + 2) + 4 ≥ 0 + m2) = true := decide_eq_true (by omega)
                rw [hodd_m2, hepsum_m2, hep_m2, hp5_m2, hip5_m2, hsuf_m2, hdec_m2]
                simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
                  Bool.true_and, Bool.false_or, Nat.zero_add]
                have hk5 : k + 3 + 1 + 1 = k + 5 := by omega
                have hm5 : m2 + 2 * 1 + 3 = m2 + 2 + 3 := by omega
                rw [hk5, hm5]
                exact hf
            · by_cases h_c2 : (m2 + 2) % 2 = 1 ∧ m2 + 2 ≤ 2 * k + 11
              · cases fuel with
                | zero =>
                  dsimp [invChain]; rfl
                | succ fuel' =>
                  have hf := hch (fuel' + 1)
                  dsimp only [invChain] at hf ⊢
                  rw [if_pos hk, if_neg hrst_ch] at hf
                  rw [if_pos rfl, if_neg hrst_ch']
                  dsimp only [checkChainAux] at hf ⊢
                  have hodd1 : hasOdd (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = true := rfl
                  have hepsum1 : epSum (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
                  have hep1 : ep (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
                  have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
                  rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m, hsuf_m] at hf
                  simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
                    Nat.add_zero, Nat.mul_zero] at hf
                  rw [if_neg h_c1, if_pos h_c2] at hf
                  have hm2_odd : m2 % 2 = 1 := by omega
                  have hodd_m2 : hasOdd (.p3z m2 :: .p5 :: suf) = true := by dsimp [hasOdd]; rw [if_pos hm2_odd]
                  have hp5_m2 : hasP5 (.p3z m2 :: .p5 :: suf) = true := rfl
                  have hepsum_m2 : epSum (.p3z m2 :: .p5 :: suf) = m2 - 1 := by dsimp [epSum]; rw [if_pos hm2_odd]
                  have hep_m2 : ep (.p3z m2 :: .p5 :: suf) = 0 := by dsimp [ep]; rw [if_pos hm2_odd]
                  have hsuf_m2 : p5Suf (.p3z m2 :: .p5 :: suf) = suf := rfl
                  have hdec_m2 : decide (2 * (k + 2) + 4 ≥ 0 + (m2 - 1)) = true := decide_eq_true (by omega)
                  rw [hodd_m2, hepsum_m2, hep_m2, hmd0_m2, hp5_m2, hsuf_m2, hdec_m2]
                  simp only [Bool.and_true, ↓reduceIte, Bool.not_false, Bool.not_true,
                    Bool.false_eq_true, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
                  have hm3 : m2 - 1 + 4 = m2 + 2 + 1 := by omega
                  rw [hm3]
                  exact hf
              · have hf := hch (fuel + 1)
                dsimp only [invChain] at hf ⊢
                rw [if_pos hk, if_neg hrst_ch] at hf
                rw [if_pos rfl, if_neg hrst_ch']
                dsimp only [checkChainAux] at hf
                have hodd1 : hasOdd (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = true := rfl
                have hepsum1 : epSum (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
                have hep1 : ep (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
                have hdec1 : decide (2 * c + 4 ≥ k + 0) = true := decide_eq_true (by omega)
                rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m, hsuf_m] at hf
                simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
                  Nat.add_zero, Nat.mul_zero] at hf
                rw [if_neg h_c1, if_neg h_c2] at hf
                exact hf
        · rw [decide_eq_true_eq] at hphi1
          rcases hphi1 with ⟨rfl, rfl, rfl, hm2_ge, hz38⟩
          have hm2_14 : m2 ≥ 14 := by omega
          have hepsum_14 : epSum (.p3z m2 :: .p5 :: suf) ≥ 14 := epSum_p3z_p5_ge14 hm2_14
          have hds2' : checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 4 [2]) = true := by
            dsimp only [checkDs2]
            have hp5_t : hasP5 (.p3z m2 :: .p5 :: suf) = true := rfl
            have hsuf_eq : p5Suf (.p3z m2 :: .p5 :: suf) = suf := rfl
            have hip5_f : isHeadP5 (.p3z m2 :: .p5 :: suf) = false := rfl
            rw [if_neg (by decide), hp5_t, hmd0_m2, hsuf_eq, hip5_f,
              decide_eq_true hz38, decide_eq_true (show 0 + epSum (.p3z m2 :: .p5 :: suf) ≥ 2 * 4 + 6 by omega)]
            rfl
          have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 4 [2]) = true := rfl
          refine ⟨?_, ?_⟩
          · dsimp only [invCore]
            have h_g : (!GoodDs [2] || !checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 4 [2]) ||
                !checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 4 [2])) = false := by
              simp [GoodDs, GoodDsAux, GoodDs1, hds2', hds1']
            rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven_m2]
            rw [hpref0, not_decide_if_false_eq_true (by omega)]
            have hok_phi' : (if (!isHeadP5 (.p3z m2 :: .p5 :: suf)) = true then
                (decide ([2] = [] ∧ 4 + epW (.p3z m2 :: .p5 :: suf) = 1) && MustDrain (.p3z m2 :: .p5 :: suf) &&
                  decide (4 + ep (.p3z m2 :: .p5 :: suf) = 1 ∧ 0 + epSum (.p3z m2 :: .p5 :: suf) + 2 * ep (.p3z m2 :: .p5 :: suf) = 2) &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val (.p3z m2 :: .p5 :: suf) ≥ 16 ∧ z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (4 + epW (.p3z m2 :: .p5 :: suf)) [2]
                    (isHeadP3z1 (.p3z m2 :: .p5 :: suf) && decide (0 = 0 ∧ 4 = 0 ∧ [2] = []))
              else
                decide (4 = 0 ∧ [2] = [] ∧ 0 = 2) || (decide (4 ≥ 1) && GoodPhiW (4 - 1) [2] false)) = true := by
              dsimp [isHeadP5]; rw [hepw0_m2]; simp [GoodPhiW]
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd0_m2, Bool.false_and, if_neg Bool.false_ne_true]
            have hrst_f' : (decide (0 = 0 ∧ 4 = 0 ∧ [2] = []) && isHeadP3z1 (.p3z m2 :: .p5 :: suf)) = false := rfl
            rw [hrst_f']
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            have hdec_f : decide (2 * 4 + 4 ≥ 0 + epSum (.p3z m2 :: .p5 :: suf)) = false :=
              decide_eq_false (by omega)
            rw [hdec_f, Bool.and_false, if_neg Bool.false_ne_true]
          · intro fuel
            have hf := hch (fuel + 1)
            dsimp only [invChain] at hf ⊢
            rw [if_pos hk, if_neg hrst_ch] at hf
            rw [if_pos rfl, if_neg (by omega)]
            dsimp only [checkChainAux] at hf
            have hodd1 : hasOdd (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = true := rfl
            have hepsum1 : epSum (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
            have hep1 : ep (.p3z 1 :: .p3z (m2 + 2) :: .p5 :: suf) = 0 := rfl
            have hdec1 : decide (2 * 1 + 4 ≥ 2 + 0) = true := rfl
            rw [hodd1, hepsum1, hep1, hdec1, hmd_t, hp5_t, hpre_m, hsuf_m] at hf
            simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
              Nat.add_zero, Nat.mul_zero] at hf
            have h_n1 : ¬((m2 + 1 + 1) % 2 = 0 ∧ m2 + 1 + 1 ≤ 2 * 2 + 10) := by omega
            have h_n2 : ¬((m2 + 1 + 1) % 2 = 1 ∧ m2 + 1 + 1 ≤ 2 * 2 + 11) := by omega
            rw [if_neg h_n1, if_neg h_n2] at hf
            exact hf

lemma step_Inv_ModeE_ge2_p3z1 (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 (.p3z 1 :: ls') k c ds)) :
    Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)) := by
  by_cases hk : k % 2 = 0
  · by_cases hrst : k = 0 ∧ c = 0 ∧ ds = []
    · rcases hrst with ⟨rfl, rfl, rfl⟩
      exact step_Inv_ModeE_ge2_p3z1_reset ls' hinv
    · exact step_Inv_ModeE_ge2_p3z1_even_nonreset ls' k c ds hk hrst hinv
  · exact step_Inv_ModeE_ge2_p3z1_odd ls' k c ds hk hinv

lemma step_Inv_ModeE_ge2 (ls : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 ls k c ds)) :
    Inv (nextState (.ModeE_ge2 ls k c ds)) := by
  cases ls with
  | nil => exact step_Inv_ModeE_ge2_nil k c ds hinv
  | cons tok ls' =>
    cases tok with
    | p5 => exact step_Inv_ModeE_ge2_p5 ls' k c ds hinv
    | p3z m =>
      cases m with
      | zero => exact step_Inv_ModeE_ge2_p3z0 ls' k c ds hinv
      | succ m' =>
        cases m' with
        | zero => exact step_Inv_ModeE_ge2_p3z1 ls' k c ds hinv
        | succ m2 => exact step_Inv_ModeE_ge2_p3z_ge2 m2 ls' k c ds hinv

lemma step_Inv (s : State270) (hinv : Inv s) : Inv (nextState s) := by
  cases s with
  | ModeE_c1 ls k ds => exact step_Inv_ModeE_c1 ls k ds hinv
  | ModeE_ge2 ls k c ds => exact step_Inv_ModeE_ge2 ls k c ds hinv
  | ModeB_ge3 ls a c ds =>
    cases c with
    | zero => exact step_Inv_ModeB_ge3_c0 ls a ds hinv
    | succ c' => exact step_Inv_ModeB_ge3_cpos ls a c' ds hinv
  | ModeB_b2 ls m ds => exact step_Inv_ModeB_b2 ls m ds hinv
  | ModeB_blank ls a => exact step_Inv_ModeB_blank ls a hinv


namespace ChainClosure

lemma dec_or (P : Prop) [h : Decidable P] : P ∨ ¬ P :=
  match h with
  | isTrue hp => Or.inl hp
  | isFalse hnp => Or.inr hnp

-- ============================================================================
-- Section 5g.1: Normalized Segment Representation & 1-Step Chain Equivalence
-- ============================================================================

structure SegState where
  b : Bool
  segs : List (Nat × Nat)
  zl : Nat
  cp1 : Nat
  kb : Nat
  mrg : Nat
  ds : List Nat

def normSeg (z m : Nat) : Nat × Nat :=
  if m = 0 then (z + 1, 0) else (z, m)

def pushSeg (has_p5 : Bool) (z_new m_rem : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    List (Nat × Nat) × Nat :=
  if has_p5 then (normSeg z_new m_rem :: rest, zl) else ([], z_new)

def encSegs : List (Nat × Nat) → Nat → List LTok
  | [], zl => z0Rep zl []
  | (z, 0) :: rest, zl => z0Rep z (.p5 :: encSegs rest zl)
  | (z, m + 1) :: rest, zl => z0Rep z (.p3z (m + 1) :: .p5 :: encSegs rest zl)

lemma z0Rep_succ_right (n : Nat) (rest : List LTok) :
    z0Rep (n + 1) rest = z0Rep n (.p3z 0 :: rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change LTok.p3z 0 :: z0Rep (n + 1) rest = LTok.p3z 0 :: z0Rep n (.p3z 0 :: rest)
    rw [ih]

lemma encSegs_normSeg (z m : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    encSegs (normSeg z m :: rest) zl = z0Rep z (.p3z m :: .p5 :: encSegs rest zl) := by
  cases m with
  | zero =>
    dsimp only [normSeg, ite_true, encSegs]
    exact z0Rep_succ_right z (.p5 :: encSegs rest zl)
  | succ m' => rfl

lemma encSegs_pushSeg (hp : Bool) (z_new m_rem : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    encSegs (pushSeg hp z_new m_rem rest zl).1 (pushSeg hp z_new m_rem rest zl).2 =
      z0Rep z_new (if hp then .p3z m_rem :: .p5 :: encSegs rest zl else []) := by
  cases hp with
  | false => rfl
  | true => exact encSegs_normSeg z_new m_rem rest zl

lemma z0_z0Rep_of_zero {rest : List LTok} (h : z0 rest = 0) (n : Nat) :
    z0 (z0Rep n rest) = n := by
  induction n with
  | zero => exact h
  | succ n ih => simp only [z0Rep, z0, ih]; omega

lemma dropZ0_z0Rep_of_nonz0 {rest : List LTok} (h : dropZ0 rest = rest) (n : Nat) :
    dropZ0 (z0Rep n rest) = rest := by
  induction n with
  | zero => exact h
  | succ n ih => simp only [z0Rep, dropZ0, ih]

lemma hasOdd_z0Rep (n : Nat) (rest : List LTok) :
    hasOdd (z0Rep n rest) = hasOdd rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, hasOdd, ih]; rfl

lemma hasP5_z0Rep (n : Nat) (rest : List LTok) :
    hasP5 (z0Rep n rest) = hasP5 rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, hasP5, ih]

lemma p5Suf_z0Rep (n : Nat) (rest : List LTok) :
    p5Suf (z0Rep n rest) = p5Suf rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, p5Suf, ih]

lemma MustDrain_z0Rep (n : Nat) (rest : List LTok) :
    MustDrain (z0Rep n rest) = MustDrain rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, MustDrain, ih]; rfl

lemma ep_z0Rep (n : Nat) (rest : List LTok) :
    ep (z0Rep n rest) = n + ep rest := by
  induction n with
  | zero => simp only [z0Rep, Nat.zero_add]
  | succ n ih =>
    have h0 : (0 : Nat) % 2 = 1 ↔ False := by decide
    simp only [z0Rep, ep, h0, ite_false, ih]
    omega

lemma epSum_z0Rep (n : Nat) (rest : List LTok) :
    epSum (z0Rep n rest) = epSum rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h0 : (0 : Nat) % 2 = 1 ↔ False := by decide
    simp only [z0Rep, epSum, h0, ite_false, Nat.zero_add, ih]

lemma epW_z0Rep_nil (n : Nat) : epW (z0Rep n []) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      change (if 0 % 2 = 1 then 0 else 1 + epW (z0Rep (n' + 1) [])) = n' + 2
      rw [ih, if_neg (by decide)]; omega

lemma epW_z0Rep_p3z (n m : Nat) (suf : List LTok) :
    epW (z0Rep n (.p3z m :: .p5 :: suf)) = n := by
  induction n with
  | zero =>
    dsimp [z0Rep, epW]
    rcases dec_or (m % 2 = 1) with hm | hm
    · rw [if_pos hm]
    · rw [if_neg hm]
  | succ n ih =>
    cases n with
    | zero =>
      change (if 0 % 2 = 1 then 0 else 1 + epW (.p3z m :: .p5 :: suf)) = 1
      have h0 : epW (.p3z m :: .p5 :: suf) = 0 := ih
      rw [h0]; rfl
    | succ n' =>
      change (if 0 % 2 = 1 then 0 else 1 + epW (z0Rep (n' + 1) (.p3z m :: .p5 :: suf))) = n' + 2
      rw [ih, if_neg (by decide)]; omega

lemma isHeadP5_z0Rep_p3z (n m : Nat) (suf : List LTok) :
    isHeadP5 (z0Rep n (.p3z m :: suf)) = false := by
  cases n <;> rfl

def isDrainRstDs : List Nat → Bool
  | [d] => decide (d ≥ 8)
  | [d, 0] => decide (d ≥ 8)
  | _ => false

def isRank0 : List Nat → Bool
  | [] => true
  | [0] => true
  | [1] => true
  | [2] => true
  | _ => false

lemma isRank0_iff (ds : List Nat) :
    isRank0 ds = true ↔ (ds = [] ∨ ds = [0] ∨ ds = [1] ∨ ds = [2]) := by
  rcases ds with _ | ⟨d, _ | ⟨d2, ds2⟩⟩
  · simp [isRank0]
  · rcases d with _ | _ | _ | d3 <;> simp [isRank0]
  · simp [isRank0]

def drainPopGuards (phiWp1 : Nat) (ds : List Nat) : Bool :=
  if isDrainRstDs ds then
    decide (phiWp1 ≥ if isOddDrainDs ds then 18 else 16)
  else if isRank0 ds then
    decide (phiWp1 ≥ 2)
  else
    match ds with
    | d :: d2 :: ds2 =>
      decide (d ≥ 3 ∧ d2 ≥ 1) &&
      (!decide (d % 2 = 0 ∧ d ≤ 2 * d2 + 4) || GoodDs ((d2 - 1) :: ds2)) &&
      (!decide (d % 2 = 0 ∧ d + 14 ≤ 2 * d2) || GoodDs ((d2 - 2) :: ds2)) &&
      decide (phiWp1 ≥ 16)
    | _ => false

def drainPopStep (has_p5 : Bool) (phiWp1 m_rem : Nat) (rest : List (Nat × Nat)) (zl : Nat)
    (ds : List Nat) : SegState :=
  if isDrainRstDs ds then
    let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
    let m_rst := headNat ds - 7
    if m_rst = 1 then
      ⟨false, p.1, p.2, 2, 1, 0, [3, 1]⟩
    else
      ⟨true, normSeg 0 (m_rst - 2) :: p.1, p.2, 3, 0, 8, [1]⟩
  else if isRank0 ds then
    if ds = [] then
      let p := pushSeg has_p5 (phiWp1 + 1) m_rem rest zl
      ⟨false, p.1, p.2, 1, 1, 0, []⟩
    else if ds = [0] then
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
      ⟨true, p.1, p.2, 2, 2, 6, []⟩
    else if ds = [1] then
      let p := pushSeg has_p5 (phiWp1 + 3) m_rem rest zl
      ⟨true, p.1, p.2, 2, 0, 6, []⟩
    else
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
      ⟨false, p.1, p.2, 1, 1, 0, [0]⟩
  else
    match ds with
    | d :: d2 :: ds2 =>
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
      if d2 = 1 ∧ ds2 = [] ∧ d ≥ 25 then
        ⟨true, normSeg 0 (d - 11) :: p.1, p.2, 5, 0, 12, [2]⟩
      else
        ⟨true, normSeg 0 (d - 3) :: p.1, p.2, d2 - 1, 0, 2 * d2, ds2⟩
    | _ => ⟨true, [], 0, 0, 0, 0, []⟩

def stepGuards (s : SegState) : Bool :=
  match s.b with
  | false =>
    let c := s.cp1
    let k := s.kb
    match s.segs with
    | [] =>
      let cz := c + s.zl
      GoodPhiW (cz - 1) s.ds false && GoodPsi (cz - 1) s.ds
    | (_, 0) :: _ => true
    | (z0, m + 1) :: _ =>
      let m0 := m + 1
      let cz := c + z0
      let kz := k + 2 * z0
      GoodPhiW (cz - 1) s.ds false &&
      if m0 = 1 then GoodPsi cz s.ds
      else
        GoodPsi (cz - 1) s.ds &&
        if m0 % 2 = 0 ∧ m0 ≤ 2 * kz + 10 then true
        else if m0 % 2 = 1 ∧ m0 ≤ 2 * kz + 11 then GoodDs ((kz + 2) :: cz :: s.ds)
        else true
  | true =>
    match s.segs with
    | [] => drainPopGuards (s.cp1 + s.zl) s.ds
    | (_, 0) :: _ => decide (s.mrg ≥ s.kb)
    | (z0, m + 1) :: _ =>
      let m0 := m + 1
      if m0 % 2 = 1 then
        if decide (s.mrg ≥ s.kb + m) then GoodDs ((s.cp1 + z0) :: s.ds)
        else drainPopGuards (s.cp1 + z0) s.ds
      else
        if decide (s.mrg ≥ s.kb + m0) then true
        else drainPopGuards (s.cp1 + z0) s.ds

def stepSegs (s : SegState) : SegState :=
  match s.b with
  | false =>
    let c := s.cp1
    let k := s.kb
    match s.segs with
    | [] =>
      let cz := c + s.zl
      let kz := k + 2 * s.zl
      ⟨true, [], 0, kz + 2, 0, 2 * kz + 6, cz :: s.ds⟩
    | (z0, 0) :: rest =>
      let cz := c + z0
      let kz := k + 2 * z0
      ⟨true, rest, s.zl, cz + 3, kz + 3, 2 * cz + 8, s.ds⟩
    | (z0, m + 1) :: rest =>
      let m0 := m + 1
      let cz := c + z0
      let kz := k + 2 * z0
      if m0 = 1 then
        ⟨false, rest, s.zl, kz + 4, 1, 0, (cz + 1) :: s.ds⟩
      else if m0 % 2 = 0 ∧ m0 ≤ 2 * kz + 10 then
        ⟨false, rest, s.zl, kz + 4, m0 + 1, 0, cz :: s.ds⟩
      else if m0 % 2 = 1 ∧ m0 ≤ 2 * kz + 11 then
        ⟨false, rest, s.zl, m0 - 1, 1, 0, (kz + 2) :: cz :: s.ds⟩
      else
        ⟨true, normSeg 0 (m0 - 4) :: rest, s.zl, kz + 2, 0, 2 * kz + 6, cz :: s.ds⟩
  | true =>
    match s.segs with
    | [] => drainPopStep false (s.cp1 + s.zl) 0 [] s.zl s.ds
    | (z0, 0) :: rest => ⟨false, rest, s.zl, s.cp1 + z0 + 1, s.kb + 2 * z0 + 3, 0, s.ds⟩
    | (z0, m + 1) :: rest =>
      let m0 := m + 1
      if m0 % 2 = 1 then
        if decide (s.mrg ≥ s.kb + m) then
          ⟨false, rest, s.zl, s.kb + m + 2 * z0 + 4, 1, 0, (s.cp1 + z0) :: s.ds⟩
        else
          drainPopStep true (s.cp1 + z0) (s.kb + m0 - (s.mrg + 2)) rest s.zl s.ds
      else
        if decide (s.mrg ≥ s.kb + m0) then
          ⟨false, rest, s.zl, s.cp1 + z0 + 2, s.kb + m0 + 2 * z0 + 5, 0, s.ds⟩
        else
          drainPopStep true (s.cp1 + z0) (s.kb + m0 - (s.mrg + 2)) rest s.zl s.ds

lemma drainPop_eq_checkChain (fuel : Nat) (ls : List LTok) (cp1 kb mrg : Nat) (ds : List Nat)
    (has_p5 : Bool) (m_rem_arg : Nat) (rest : List (Nat × Nat)) (zl : Nat)
    (h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false)
    (h2 : (!hasOdd ls && hasP5 ls && (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = false)
    (hp5 : hasP5 ls = has_p5)
    (hsuf : has_p5 = true → p5Suf ls = encSegs rest zl)
    (hmrem : has_p5 = true → kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2) = m_rem_arg)
    (hg : drainPopGuards (cp1 + epW ls) ds = true) :
    checkChainAux (fuel + 1) true ls cp1 kb mrg ds =
      let s' := drainPopStep has_p5 (cp1 + epW ls) m_rem_arg rest zl ds
      checkChainAux fuel s'.b (encSegs s'.segs s'.zl) s'.cp1 s'.kb s'.mrg s'.ds := by
  conv_lhs => unfold checkChainAux
  rw [if_neg (by rw [h1]; decide), if_neg (by rw [h2]; decide)]
  have htail :
      (if hasP5 ls = true then
        LTok.p3z (kb + epSum ls + (if hasOdd ls = true then 1 else 0) - (mrg + 2)) :: .p5 :: p5Suf ls
      else []) =
      (if has_p5 then LTok.p3z m_rem_arg :: .p5 :: encSegs rest zl else []) := by
    cases has_p5 with
    | false => simp [hp5]
    | true => simp only [hp5, ite_true, hsuf rfl, hmrem rfl]
  unfold drainPopGuards drainPopStep at *
  rcases ds with _ | ⟨d, _ | ⟨_ | d2, ds2⟩⟩
  · -- ds = []
    simp only [isDrainRstDs, isRank0, Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq] at hg ⊢
    have hlt2 : ¬ (cp1 + epW ls < 2) := by omega
    rw [if_pos (Or.inl trivial), if_neg hlt2, encSegs_pushSeg, htail]
  · -- ds = [d]
    rcases dec_or (d ≥ 8) with hd8 | hd8
    · have hd8b : decide (d ≥ 8) = true := decide_eq_true hd8
      simp only [isDrainRstDs, hd8b, ite_true] at hg ⊢
      have hlt : ¬ (cp1 + epW ls < if isOddDrainDs [d] = true then 18 else 16) := by
        simp only [decide_eq_true_eq] at hg; omega
      rw [if_neg hlt]
      rcases dec_or (headNat [d] - 7 = 1) with hm1 | hm1
      · rw [if_pos hm1, if_pos hm1]; dsimp only; rw [encSegs_pushSeg, htail]
      · rw [if_neg hm1, if_neg hm1]; dsimp only; rw [encSegs_normSeg, z0Rep, encSegs_pushSeg, htail]
    · have hd8b : decide (d ≥ 8) = false := decide_eq_false hd8
      simp only [isDrainRstDs, hd8b, Bool.false_eq_true, ite_false] at hg ⊢
      cases h_r0 : isRank0 [d] with
      | false => simp [h_r0] at hg
      | true =>
        have hr0_prop : ([d] : List Nat) = [] ∨ [d] = [0] ∨ [d] = [1] ∨ [d] = [2] := (isRank0_iff [d]).mp h_r0
        rw [if_pos hr0_prop]
        simp only [h_r0, ite_true, decide_eq_true_eq] at hg ⊢
        have hlt2 : ¬ (cp1 + epW ls < 2) := by omega
        rw [if_neg hlt2]
        rcases hr0_prop with hnil | h0 | h1' | h2'
        · cases hnil
        · injection h0 with hd0; subst hd0
          simp only [List.cons_ne_self, imp_false, ite_false, ite_true, List.cons.injEq,
            OfNat.ofNat_ne_zero, false_and]; rw [encSegs_pushSeg, htail]
        · injection h1' with hd1; subst hd1
          have h10 : ([1] : List Nat) ≠ [0] := by decide
          have h1nil : ([1] : List Nat) ≠ [] := by decide
          simp only [h1nil, h10, ite_false, ite_true]; rw [encSegs_pushSeg, htail]
        · injection h2' with hd2; subst hd2
          have h2nil : ([2] : List Nat) ≠ [] := by decide
          have h20 : ([2] : List Nat) ≠ [0] := by decide
          have h21 : ([2] : List Nat) ≠ [1] := by decide
          simp only [h2nil, h20, h21, ite_false]; rw [encSegs_pushSeg, htail]
  · -- ds = d :: 0 :: ds2
    rcases ds2 with _ | ⟨d3, ds3⟩
    · -- ds = [d, 0]
      rcases dec_or (d ≥ 8) with hd8 | hd8
      · have hd8b : decide (d ≥ 8) = true := decide_eq_true hd8
        simp only [isDrainRstDs, hd8b, ite_true] at hg ⊢
        have hlt : ¬ (cp1 + epW ls < if isOddDrainDs [d, 0] = true then 18 else 16) := by
          simp only [decide_eq_true_eq] at hg; omega
        rw [if_neg hlt]
        rcases dec_or (headNat [d, 0] - 7 = 1) with hm1 | hm1
        · rw [if_pos hm1, if_pos hm1]; dsimp only; rw [encSegs_pushSeg, htail]
        · rw [if_neg hm1, if_neg hm1]; dsimp only; rw [encSegs_normSeg, z0Rep, encSegs_pushSeg, htail]
      · have hd8b : decide (d ≥ 8) = false := decide_eq_false hd8
        simp [isDrainRstDs, isRank0, hd8b] at hg
    · -- ds = d :: 0 :: d3 :: ds3
      simp [isDrainRstDs, isRank0] at hg
  · -- ds = d :: (d2 + 1) :: ds2
    have h_ge2_step : ∀ ts : List Nat,
        isDrainRstDs (d :: (d2 + 1) :: ts) = false →
        ((decide (d ≥ 3 ∧ d2 + 1 ≥ 1) &&
          (!decide (d % 2 = 0 ∧ d ≤ 2 * (d2 + 1) + 4) || GoodDs (((d2 + 1) - 1) :: ts)) &&
          (!decide (d % 2 = 0 ∧ d + 14 ≤ 2 * (d2 + 1)) || GoodDs (((d2 + 1) - 2) :: ts)) &&
          decide (cp1 + epW ls ≥ 16)) = true) →
        (if d :: (d2 + 1) :: ts = [] ∨ d :: (d2 + 1) :: ts = [0] ∨
            d :: (d2 + 1) :: ts = [1] ∨ d :: (d2 + 1) :: ts = [2] then
          let phiWp1 := cp1 + epW ls
          if phiWp1 < 2 then true
          else
            let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2)
            let tail_b2 := if hasP5 ls then LTok.p3z m_rem :: LTok.p5 :: p5Suf ls else []
            if d :: (d2 + 1) :: ts = [] then checkChainAux fuel false (z0Rep (phiWp1 + 1) tail_b2) 1 1 0 []
            else if d :: (d2 + 1) :: ts = [0] then checkChainAux fuel true (z0Rep (phiWp1 + 2) tail_b2) 2 2 6 []
            else if d :: (d2 + 1) :: ts = [1] then checkChainAux fuel true (z0Rep (phiWp1 + 3) tail_b2) 2 0 6 []
            else checkChainAux fuel false (z0Rep (phiWp1 + 2) tail_b2) 1 1 0 [0]
        else
          if d ≥ 3 ∧ d2 + 1 ≥ 1 then
            if d % 2 = 0 ∧ d ≤ 2 * (d2 + 1) + 4 ∧ GoodDs (((d2 + 1) - 1) :: ts) = false then false
            else if d % 2 = 0 ∧ d + 14 ≤ 2 * (d2 + 1) ∧ GoodDs (((d2 + 1) - 2) :: ts) = false then false
            else if cp1 + epW ls < 16 then false
            else
              let phiWp1 := cp1 + epW ls
              let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2)
              let tail_b2 := if hasP5 ls then LTok.p3z m_rem :: LTok.p5 :: p5Suf ls else []
              let ls_b2 := z0Rep phiWp1 tail_b2
              if d2 + 1 = 1 ∧ ts = [] ∧ d ≥ 25 then
                checkChainAux fuel true (LTok.p3z (d - 11) :: LTok.p5 :: LTok.p3z 0 :: LTok.p3z 0 :: ls_b2) 5 0 12 [2]
              else
                checkChainAux fuel true (LTok.p3z (d - 3) :: LTok.p5 :: LTok.p3z 0 :: LTok.p3z 0 :: ls_b2)
                  ((d2 + 1) - 1) 0 (2 * (d2 + 1)) ts
          else true) =
        (let p := pushSeg has_p5 (cp1 + epW ls + 2) m_rem_arg rest zl
         let s' : SegState :=
           if d2 + 1 = 1 ∧ ts = [] ∧ d ≥ 25 then
             ⟨true, normSeg 0 (d - 11) :: p.1, p.2, 5, 0, 12, [2]⟩
           else
             ⟨true, normSeg 0 (d - 3) :: p.1, p.2, (d2 + 1) - 1, 0, 2 * (d2 + 1), ts⟩
         checkChainAux fuel s'.b (encSegs s'.segs s'.zl) s'.cp1 s'.kb s'.mrg s'.ds) := by
      intro ts _ hg_ts
      dsimp only
      rw [if_neg (by simp)]
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at hg_ts
      rcases hg_ts with ⟨⟨⟨hd32, hg1⟩, hg2⟩, hphi16⟩
      rw [if_pos hd32]
      have hc1 : ¬ (d % 2 = 0 ∧ d ≤ 2 * (d2 + 1) + 4 ∧ GoodDs (((d2 + 1) - 1) :: ts) = false) := by
        intro ⟨he, hle, hgf⟩
        rcases hg1 with hnot | hgt
        · exact hnot ⟨he, hle⟩
        · rw [hgf] at hgt; cases hgt
      have hc2 : ¬ (d % 2 = 0 ∧ d + 14 ≤ 2 * (d2 + 1) ∧ GoodDs (((d2 + 1) - 2) :: ts) = false) := by
        intro ⟨he, hle, hgf⟩
        rcases hg2 with hnot | hgt
        · exact hnot ⟨he, hle⟩
        · rw [hgf] at hgt; cases hgt
      have hc3 : ¬ (cp1 + epW ls < 16) := by omega
      rw [if_neg hc1, if_neg hc2, if_neg hc3]
      rcases dec_or (d2 + 1 = 1 ∧ ts = [] ∧ d ≥ 25) with hrst2 | hrst2
      · rw [if_pos hrst2]; rw [if_pos hrst2]; dsimp only; rw [encSegs_normSeg, z0Rep, encSegs_pushSeg, htail]; rfl
      · rw [if_neg hrst2]; rw [if_neg hrst2]; dsimp only; rw [encSegs_normSeg, z0Rep, encSegs_pushSeg, htail]; rfl
    rcases ds2 with _ | ⟨d3, ds3⟩
    · change (if false = true then _ else _) = _
      rw [if_neg Bool.false_ne_true]
      have hf1 : isDrainRstDs [d, d2 + 1] = false := rfl
      have hf2 : isRank0 [d, d2 + 1] = false := by rcases d with _ | _ | _ | _ <;> rfl
      rw [hf1, hf2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true] at hg ⊢
      dsimp only
      exact h_ge2_step [] hf1 hg
    · change (if false = true then _ else _) = _
      rw [if_neg Bool.false_ne_true]
      have hf1 : isDrainRstDs (d :: (d2 + 1) :: d3 :: ds3) = false := rfl
      have hf2 : isRank0 (d :: (d2 + 1) :: d3 :: ds3) = false := by rcases d with _ | _ | _ | _ <;> rfl
      rw [hf1, hf2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true] at hg ⊢
      dsimp only
      exact h_ge2_step (d3 :: ds3) hf1 hg

lemma checkChainAux_eq_of_guards (fuel : Nat) (s : SegState) (hg : stepGuards s = true) :
    checkChainAux (fuel + 1) s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds =
      let s' := stepSegs s
      checkChainAux fuel s'.b (encSegs s'.segs s'.zl) s'.cp1 s'.kb s'.mrg s'.ds := by
  rcases s with ⟨b, segs, zl, cp1, kb, mrg, ds⟩
  cases b with
  | false =>
    rcases segs with _ | ⟨⟨z, m⟩, rest⟩
    · dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
      simp only [Bool.and_eq_true] at hg
      rcases hg with ⟨hphi, hpsi⟩
      conv_lhs => unfold checkChainAux
      rw [z0_z0Rep_of_zero rfl zl, dropZ0_z0Rep_of_nonz0 rfl zl]
      have hhd : (!isHeadP5 [] && !GoodPhiW (cp1 + zl - 1) ds false) = false := by
        simp [isHeadP5, hphi]
      rw [if_neg (by rw [hhd]; decide)]
      dsimp only
      rw [hpsi, Bool.true_and]
      have h6 : 2 * (kb + 2 * zl + 1) + 4 = 2 * (kb + 2 * zl) + 6 := by omega
      rw [h6]; rfl
    · cases m with
      | zero =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        conv_lhs => unfold checkChainAux
        rw [z0_z0Rep_of_zero rfl z, dropZ0_z0Rep_of_nonz0 rfl z]
        have hhd : (!isHeadP5 (.p5 :: encSegs rest zl) && !GoodPhiW (cp1 + z - 1) ds false) = false := by
          simp [isHeadP5]
        rw [if_neg (by rw [hhd]; decide)]
        dsimp only
        have h8 : 2 * (cp1 + z + 2) + 4 = 2 * (cp1 + z) + 8 := by omega
        rw [h8]
      | succ m' =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        simp only [Bool.and_eq_true] at hg
        rcases hg with ⟨hphi, hg_rest⟩
        conv_lhs => unfold checkChainAux
        rw [z0_z0Rep_of_zero rfl z, dropZ0_z0Rep_of_nonz0 rfl z]
        have hhd : (!isHeadP5 (.p3z (m' + 1) :: .p5 :: encSegs rest zl) &&
            !GoodPhiW (cp1 + z - 1) ds false) = false := by
          simp [isHeadP5, hphi]
        rw [if_neg (by rw [hhd]; decide)]
        dsimp only [drop1L]
        rcases dec_or (m' + 1 = 1) with hm1 | hm1
        · rw [if_pos hm1] at hg_rest
          rw [if_pos hm1, if_pos hm1]
          dsimp only
          rw [hg_rest, Bool.true_and]
        · rw [if_neg hm1] at hg_rest
          rw [if_neg hm1, if_neg hm1]
          simp only [Bool.and_eq_true] at hg_rest
          rcases hg_rest with ⟨hpsi, hg_sub⟩
          have hnpsi : (!GoodPsi (cp1 + z - 1) ds) = false := by simp [hpsi]
          rw [if_neg (by rw [hnpsi]; decide)]
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (kb + 2 * z) + 10) with hev | hev
          · rw [if_pos hev, if_pos hev]
          · rw [if_neg hev] at hg_sub
            rw [if_neg hev, if_neg hev]
            rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (kb + 2 * z) + 11) with hod | hod
            · rw [if_pos hod] at hg_sub
              rw [if_pos hod, if_pos hod]
              dsimp only
              rw [hg_sub, Bool.true_and]
              rfl
            · rw [if_neg hod, if_neg hod]
              dsimp only
              rw [encSegs_normSeg, z0Rep]
              have h6 : 2 * (kb + 2 * z + 1) + 4 = 2 * (kb + 2 * z) + 6 := by omega
              rw [h6]
  | true =>
    rcases segs with _ | ⟨⟨z, m⟩, rest⟩
    · dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
      have hepw : epW (z0Rep zl []) = zl := epW_z0Rep_nil zl
      have h1 : (hasOdd (z0Rep zl []) && decide (mrg ≥ kb + epSum (z0Rep zl []))) = false := by
        rw [hasOdd_z0Rep]; rfl
      have h2 : (!hasOdd (z0Rep zl []) && hasP5 (z0Rep zl []) &&
          (isHeadP5 (z0Rep zl []) || decide (mrg ≥ kb + epSum (z0Rep zl [])))) = false := by
        rw [hasP5_z0Rep]; simp [hasP5]
      have h_eq := drainPop_eq_checkChain fuel (z0Rep zl []) cp1 kb mrg ds false 0 [] zl
        h1 h2 (by rw [hasP5_z0Rep]; rfl) (by intro h; cases h) (by intro h; cases h)
        (by rw [hepw]; exact hg)
      rw [hepw] at h_eq
      exact h_eq
    · cases m with
      | zero =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        simp only [decide_eq_true_eq] at hg
        conv_lhs => unfold checkChainAux
        have hodd : hasOdd (z0Rep z (.p5 :: encSegs rest zl)) = false := by
          rw [hasOdd_z0Rep]; rfl
        have hp5 : hasP5 (z0Rep z (.p5 :: encSegs rest zl)) = true := by
          rw [hasP5_z0Rep]; rfl
        have heps : epSum (z0Rep z (.p5 :: encSegs rest zl)) = 0 := by
          rw [epSum_z0Rep]; rfl
        have hep : ep (z0Rep z (.p5 :: encSegs rest zl)) = z := by
          rw [ep_z0Rep]; simp [ep]
        have hsuf : p5Suf (z0Rep z (.p5 :: encSegs rest zl)) = encSegs rest zl := by
          rw [p5Suf_z0Rep]; rfl
        have h1 : (hasOdd (z0Rep z (.p5 :: encSegs rest zl)) &&
            decide (mrg ≥ kb + epSum (z0Rep z (.p5 :: encSegs rest zl)))) = false := by
          rw [hodd]; rfl
        have h2 : (!hasOdd (z0Rep z (.p5 :: encSegs rest zl)) &&
            hasP5 (z0Rep z (.p5 :: encSegs rest zl)) &&
            (isHeadP5 (z0Rep z (.p5 :: encSegs rest zl)) ||
              decide (mrg ≥ kb + epSum (z0Rep z (.p5 :: encSegs rest zl))))) = true := by
          rw [hodd, hp5, heps]
          have hdec : decide (mrg ≥ kb + 0) = true := decide_eq_true (by omega)
          rw [hdec, Bool.or_true]; rfl
        rw [if_neg (by rw [h1]; decide), if_pos h2, hsuf, hep, heps]
        have hk3 : kb + 0 + 2 * z + 3 = kb + 2 * z + 3 := by omega
        rw [hk3]
      | succ m' =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        set ls := z0Rep z (.p3z (m' + 1) :: .p5 :: encSegs rest zl)
        have hp5 : hasP5 ls = true := by rw [hasP5_z0Rep]; rfl
        have hsuf : p5Suf ls = encSegs rest zl := by rw [p5Suf_z0Rep]; rfl
        have hhd : isHeadP5 ls = false := isHeadP5_z0Rep_p3z z (m' + 1) (.p5 :: encSegs rest zl)
        have hepw : epW ls = z := epW_z0Rep_p3z z (m' + 1) (encSegs rest zl)
        rcases dec_or ((m' + 1) % 2 = 1) with hm_odd | hm_even
        · rw [if_pos hm_odd] at hg ⊢
          have hodd : hasOdd ls = true := by
            rw [hasOdd_z0Rep]; dsimp [hasOdd]; rw [if_pos hm_odd]
          have hmd : MustDrain ls = false := by
            rw [MustDrain_z0Rep]; dsimp [MustDrain]; rw [if_pos hm_odd]
          have hep : ep ls = z := by
            rw [ep_z0Rep]; dsimp [ep]; rw [if_pos hm_odd]; omega
          have heps : epSum ls = m' := by
            rw [epSum_z0Rep]; dsimp [epSum]; rw [if_pos hm_odd]
          cases hd_mrg : decide (mrg ≥ kb + m') with
          | true =>
            simp only [hd_mrg, ite_true] at hg ⊢
            conv_lhs => unfold checkChainAux
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = true := by
              rw [hodd, heps, hd_mrg]; rfl
            rw [if_pos h1]
            dsimp only
            rw [hmd, hp5, hsuf, hep, heps]
            change (GoodDs ((cp1 + z) :: ds) &&
              checkChainAux fuel false (encSegs rest zl) (kb + m' + 2 * z + 4) 1 0 ((cp1 + z) :: ds)) = _
            rw [hg, Bool.true_and]
          | false =>
            simp only [hd_mrg, Bool.false_eq_true, ite_false] at hg ⊢
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false := by
              rw [hodd, heps, hd_mrg]; rfl
            have h2 : (!hasOdd ls && hasP5 ls &&
                (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = false := by
              rw [hodd]; rfl
            have h_eq := drainPop_eq_checkChain fuel ls cp1 kb mrg ds true
              (kb + (m' + 1) - (mrg + 2)) rest zl h1 h2 hp5 (fun _ => hsuf)
              (fun _ => by rw [heps, hodd]; simp only [ite_true, Nat.add_assoc])
              (by rw [hepw]; exact hg)
            rw [hepw] at h_eq
            exact h_eq
        · rw [if_neg hm_even] at hg ⊢
          have hodd : hasOdd ls = false := by
            rw [hasOdd_z0Rep]; dsimp [hasOdd]; rw [if_neg hm_even]
          have hep : ep ls = z + 1 := by
            rw [ep_z0Rep]; dsimp [ep]; rw [if_neg hm_even]
          have heps : epSum ls = m' + 1 := by
            rw [epSum_z0Rep]; dsimp [epSum]; rw [if_neg hm_even]
          cases hd_mrg : decide (mrg ≥ kb + (m' + 1)) with
          | true =>
            simp only [hd_mrg, ite_true] at hg ⊢
            conv_lhs => unfold checkChainAux
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false := by
              rw [hodd]; rfl
            have h2 : (!hasOdd ls && hasP5 ls &&
                (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = true := by
              rw [hodd, hp5, hhd, heps, hd_mrg]; rfl
            rw [if_neg (by rw [h1]; decide), if_pos h2, hsuf, hep, heps]
            have hc2 : cp1 + (z + 1) + 1 = cp1 + z + 2 := by omega
            have hk5 : kb + (m' + 1) + 2 * (z + 1) + 3 = kb + (m' + 1) + 2 * z + 5 := by omega
            rw [hc2, hk5]
          | false =>
            simp only [hd_mrg, Bool.false_eq_true, ite_false] at hg ⊢
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false := by
              rw [hodd]; rfl
            have h2 : (!hasOdd ls && hasP5 ls &&
                (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = false := by
              rw [hodd, hp5, hhd, heps, hd_mrg]; rfl
            have h_eq := drainPop_eq_checkChain fuel ls cp1 kb mrg ds true
              (kb + (m' + 1) - (mrg + 2)) rest zl h1 h2 hp5 (fun _ => hsuf)
              (fun _ => by rw [heps, hodd]; simp only [Bool.false_eq_true, ite_false, Nat.add_zero])
              (by rw [hepw]; exact hg)
            rw [hepw] at h_eq
            exact h_eq


-- ============================================================================
-- Section 5g.2: Fuel-Bounded LeadsUpTo Framework & Stack-Polymorphic Excursion
-- ============================================================================

def FailsIn (s : SegState) (n : Nat) : Prop :=
  checkChainAux n s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds = false

def ChainLeadsUpTo (N : Nat) (s : SegState) (P : SegState → Prop) : Prop :=
  ∀ n, n ≤ N → FailsIn s n → ∃ m s', m ≤ n ∧ P s' ∧ FailsIn s' m

def ChainLeads (s : SegState) (P : SegState → Prop) : Prop :=
  ∀ N, ChainLeadsUpTo N s P

def ChainAdvances (s : SegState) (P : SegState → Prop) : Prop :=
  stepGuards s = true ∧ ChainLeads (stepSegs s) P

lemma not_failsIn_zero (s : SegState) : ¬FailsIn s 0 := by
  intro h; cases h

lemma chainLeadsUpTo_here {N : Nat} {s : SegState} {P : SegState → Prop} (hp : P s) :
    ChainLeadsUpTo N s P := by
  intro n _ hf
  exact ⟨n, s, Nat.le_refl n, hp, hf⟩

lemma chainLeadsUpTo_mono {M N : Nat} (hle : M ≤ N) {s : SegState} {P : SegState → Prop}
    (h : ChainLeadsUpTo N s P) : ChainLeadsUpTo M s P := by
  intro n hn hf
  exact h n (Nat.le_trans hn hle) hf

lemma chainLeadsUpTo_imp {N : Nat} {s : SegState} {P Q : SegState → Prop}
    (h : ChainLeadsUpTo N s P) (himp : ∀ s', P s' → Q s') : ChainLeadsUpTo N s Q := by
  intro n hn hf
  obtain ⟨m, s', hm, hp, hfm⟩ := h n hn hf
  exact ⟨m, s', hm, himp s' hp, hfm⟩

lemma chainLeadsUpTo_trans {N : Nat} {s : SegState} {P Q : SegState → Prop}
    (h1 : ChainLeadsUpTo N s P)
    (h2 : ∀ m s', m ≤ N → P s' → ChainLeadsUpTo m s' Q) :
    ChainLeadsUpTo N s Q := by
  intro n hn hf
  obtain ⟨m, s', hm, hp, hfm⟩ := h1 n hn hf
  obtain ⟨k, s'', hk, hq, hfk⟩ := h2 m s' (Nat.le_trans hm hn) hp m (Nat.le_refl m) hfm
  exact ⟨k, s'', Nat.le_trans hk hm, hq, hfk⟩

lemma chainLeadsUpTo_step {N : Nat} {s : SegState} {P : SegState → Prop}
    (hg : stepGuards s = true)
    (hnext : ∀ m, m < N → ChainLeadsUpTo m (stepSegs s) P) :
    ChainLeadsUpTo N s P := by
  intro n hn hf
  cases n with
  | zero => exact False.elim (not_failsIn_zero s hf)
  | succ m =>
    have h_eq := checkChainAux_eq_of_guards m s hg
    dsimp only [FailsIn] at hf
    rw [h_eq] at hf
    obtain ⟨k, s', hk, hp, hfk⟩ := hnext m (by omega) m (Nat.le_refl m) hf
    exact ⟨k, s', by omega, hp, hfk⟩

lemma chainLeadsUpTo_step1 {N : Nat} {s : SegState} {P : SegState → Prop}
    (hg : stepGuards s = true)
    (hnext : ChainLeadsUpTo N (stepSegs s) P) :
    ChainLeadsUpTo N s P :=
  chainLeadsUpTo_step hg (fun m hm => chainLeadsUpTo_mono (by omega) hnext)

lemma checkChainAux_true_of_advances {P : SegState → Prop}
    (hadv : ∀ s, P s → ChainAdvances s P) :
    ∀ fuel s, P s → checkChainAux fuel s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds = true := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h n ih =>
    intro s hp
    cases n with
    | zero => rfl
    | succ m =>
      obtain ⟨hg, hleads⟩ := hadv s hp
      cases hval : checkChainAux (m + 1) s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds with
      | true => rfl
      | false =>
        have h_eq := checkChainAux_eq_of_guards m s hg
        rw [h_eq] at hval
        obtain ⟨k, s', hk, hps', hfk⟩ := hleads m m (Nat.le_refl m) hval
        have htr := ih k (by omega) s' hps'
        dsimp only [FailsIn] at hfk
        rw [htr] at hfk
        cases hfk

-- ============================================================================
-- Segment Validity, SafeStack, and Standalone Arithmetic Lemmas
-- ============================================================================

def ValidSegs40 (segs : List (Nat × Nat)) (zl : Nat) : Prop :=
  (∀ p ∈ segs, 40 ≤ p.1) ∧ 230 ≤ zl

def ValidTail40 (segs : List (Nat × Nat)) (zl : Nat) : Prop :=
  match segs with
  | [] => 230 ≤ zl
  | _ :: rest => ValidSegs40 rest zl

def fzOf (segs : List (Nat × Nat)) (zl : Nat) : Nat :=
  match segs with
  | [] => zl
  | (z, _) :: _ => z

lemma fzOf_ge_40 {segs : List (Nat × Nat)} {zl : Nat} (hv : ValidSegs40 segs zl) :
    40 ≤ fzOf segs zl := by
  rcases segs with _ | ⟨⟨z, m⟩, rest⟩
  · exact Nat.le_trans (by decide) hv.2
  · exact hv.1 (z, m) List.mem_cons_self

lemma validTail40_of_validSegs40 {segs : List (Nat × Nat)} {zl : Nat}
    (hv : ValidSegs40 segs zl) : ValidTail40 segs zl := by
  rcases segs with _ | ⟨p, rest⟩
  · exact hv.2
  · exact ⟨fun q hq => hv.1 q (List.mem_cons_of_mem _ hq), hv.2⟩

lemma validSegs40_tail {p : Nat × Nat} {rest : List (Nat × Nat)} {zl : Nat}
    (hv : ValidSegs40 (p :: rest) zl) : ValidSegs40 rest zl :=
  ⟨fun q hq => hv.1 q (List.mem_cons_of_mem _ hq), hv.2⟩

lemma normSeg_fst_ge (z m : Nat) : z ≤ (normSeg z m).1 := by
  dsimp [normSeg]
  rcases dec_or (m = 0) with hm | hm
  · rw [if_pos hm]; omega
  · rw [if_neg hm]

lemma validSegs40_pushSeg (hp : Bool) {z m : Nat} {rest : List (Nat × Nat)} {zl : Nat}
    (hz : 40 ≤ z) (hv : hp = true → ValidSegs40 rest zl) (hzl : hp = false → 230 ≤ z) :
    ValidSegs40 (pushSeg hp z m rest zl).1 (pushSeg hp z m rest zl).2 := by
  cases hp with
  | false =>
    exact ⟨(by intro _ h; cases h), hzl rfl⟩
  | true =>
    have hvr := hv rfl
    refine ⟨?_, hvr.2⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact Nat.le_trans hz (normSeg_fst_ge z m)
    · exact hvr.1 q hq'

lemma validTail40_pushSeg (hp : Bool) {z m : Nat} {rest : List (Nat × Nat)} {zl : Nat}
    (hv : hp = true → ValidSegs40 rest zl) (hzl : hp = false → 230 ≤ z) :
    ValidTail40 (pushSeg hp z m rest zl).1 (pushSeg hp z m rest zl).2 := by
  cases hp with
  | false => exact hzl rfl
  | true => exact hv rfl

lemma fzOf_pushSeg_ge (hp : Bool) (z m : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    z ≤ fzOf (pushSeg hp z m rest zl).1 (pushSeg hp z m rest zl).2 := by
  cases hp with
  | false => exact Nat.le_refl z
  | true => exact normSeg_fst_ge z m

lemma goodPhiW_of_ge35 {phiW : Nat} {ds : List Nat} (hne2 : ds ≠ [2]) (h35 : 35 ≤ phiW) :
    GoodPhiW phiW ds false = true := by
  dsimp only [GoodPhiW]
  rw [if_neg hne2]
  rcases dec_or (ds = [0]) with h0 | h0
  · rw [if_pos h0]; exact decide_eq_true (by omega)
  · rw [if_neg h0]
    rcases dec_or (ds = [1]) with h1 | h1
    · rw [if_pos h1]; exact decide_eq_true (by omega)
    · rw [if_neg h1]
      rcases dec_or (ds = []) with hn | hn
      · rw [if_pos hn, Bool.false_or]; exact decide_eq_true (by omega)
      · rw [if_neg hn]
        have hd35 : decide (phiW ≥ 35) = true := decide_eq_true (by omega)
        have hd17 : decide (phiW ≥ 17) = true := decide_eq_true (by omega)
        have hd15 : decide (phiW ≥ 15) = true := decide_eq_true (by omega)
        rcases ds with _ | ⟨d, _ | ⟨d2, _ | ⟨d3, ds3⟩⟩⟩
        · exact False.elim (hn rfl)
        · dsimp only; rw [if_neg Bool.false_ne_true]
          cases hod : isOddDrainDs [d] <;> simp only [hod, ite_true, Bool.false_eq_true, ite_false, hd17, hd15]
        · cases d2 with
          | zero =>
            cases hod : isOddDrainDs [d, 0] <;> simp only [hod, ite_true, Bool.false_eq_true, ite_false, hd17, hd15]
          | succ d2' =>
            cases d2' with
            | zero =>
              cases hd25 : decide (d ≥ 25) <;>
                simp only [hd25, ite_true, Bool.false_eq_true, ite_false, isOddDrainDs, hd35, hd15]
            | succ _ =>
              simp only [Bool.false_eq_true, ite_false, isOddDrainDs, hd15]
        · simp only [Bool.false_eq_true, ite_false, isOddDrainDs, hd15]

def SafeStack (m : Nat) (S : List Nat) : Prop :=
  S ≠ [2] ∧ GoodDs S = true ∧ ∀ u, m ≤ u → GoodDs (u :: S) = true

lemma safeStack_mono {m1 m2 : Nat} {S : List Nat} (hle : m1 ≤ m2) (hs : SafeStack m1 S) :
    SafeStack m2 S :=
  ⟨hs.1, hs.2.1, fun u hu => hs.2.2 u (Nat.le_trans hle hu)⟩

lemma isOddDrain1_eq_false_of_ge18 {x : Nat} (hx : 18 ≤ x) : isOddDrain1 x = false := by
  dsimp only [isOddDrain1]
  exact decide_eq_false (by omega)

lemma safeStack_cons {m x : Nat} {S : List Nat}
    (hs : SafeStack m S) (hx18 : 18 ≤ x) (hxm : m + 2 ≤ x) :
    SafeStack 39 (x :: S) := by
  refine ⟨(by intro h; injection h with h1; omega), hs.2.2 x (by omega), ?_⟩
  intro u hu
  rcases S with _ | ⟨d3, ds3⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hod : isOddDrain1 x = false := isOddDrain1_eq_false_of_ge18 hx18
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDs1 x = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg1 : GoodDs1 (x - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg2 : GoodDs1 (x - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    rw [hod, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]
  · dsimp only [GoodDs, GoodDsAux]
    rw [if_neg (by omega)]
    have h31 : decide (x = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 19) = false := decide_eq_false (by omega)
    have hod : isOddDrainDs (x :: d3 :: ds3) = false := by
      cases d3 with
      | zero =>
        rcases ds3 with _ | ⟨d4, ds4⟩
        · dsimp only [isOddDrainDs]; exact isOddDrain1_eq_false_of_ge18 hx18
        · rfl
      | succ _ => rfl
    have hd25 : decide (x ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 39) = false :=
      decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDsAux x (d3 :: ds3) = true := hs.2.2 x (by omega)
    have hg1 : GoodDsAux (x - 1) (d3 :: ds3) = true := hs.2.2 (x - 1) (by omega)
    have hg2 : GoodDsAux (x - 2) (d3 :: ds3) = true := hs.2.2 (x - 2) (by omega)
    rw [h31, hod, hd25, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]

lemma safeStack_cons_ne1 {m x : Nat} {S : List Nat}
    (hne1 : S ≠ [1]) (hs : SafeStack m S) (hx18 : 18 ≤ x) (hxm : m + 2 ≤ x) :
    SafeStack 19 (x :: S) := by
  refine ⟨(by intro h; injection h with h1; omega), hs.2.2 x (by omega), ?_⟩
  intro u hu
  rcases S with _ | ⟨d3, ds3⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hod : isOddDrain1 x = false := isOddDrain1_eq_false_of_ge18 hx18
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDs1 x = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg1 : GoodDs1 (x - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg2 : GoodDs1 (x - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    rw [hod, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]
  · dsimp only [GoodDs, GoodDsAux]
    rw [if_neg (by omega)]
    have h31 : decide (x = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 19) = false := decide_eq_false (by omega)
    have hod : isOddDrainDs (x :: d3 :: ds3) = false := by
      cases d3 with
      | zero =>
        rcases ds3 with _ | ⟨d4, ds4⟩
        · dsimp only [isOddDrainDs]; exact isOddDrain1_eq_false_of_ge18 hx18
        · rfl
      | succ _ => rfl
    have hd25 : decide (x ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 39) = false := by
      apply decide_eq_false
      rintro ⟨_, rfl, rfl, _⟩
      exact hne1 rfl
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDsAux x (d3 :: ds3) = true := hs.2.2 x (by omega)
    have hg1 : GoodDsAux (x - 1) (d3 :: ds3) = true := hs.2.2 (x - 1) (by omega)
    have hg2 : GoodDsAux (x - 2) (d3 :: ds3) = true := hs.2.2 (x - 2) (by omega)
    rw [h31, hod, hd25, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]

def ox (kz cz : Nat) : Nat := cz - (3 * cz - kz) / 30 - 2
def odw (kz cz : Nat) : Nat := ox kz cz - 1
def oxw (kz cz : Nat) : Nat := cz + kz / 20 + 36

lemma ox_spec_lt {kz cz : Nat} (hlt : kz < 3 * cz) :
    ∃ q r, r < 30 ∧ 3 * cz = kz + 30 * q + r ∧ ox kz cz = cz - q - 2 := by
  set d := 3 * cz - kz
  refine ⟨d / 30, d % 30, Nat.mod_lt d (by decide), ?_, rfl⟩
  have hdiv := Nat.div_add_mod d 30
  omega

lemma div20_spec (kz : Nat) : ∃ q r, r < 20 ∧ kz = 20 * q + r ∧ kz / 20 = q :=
  ⟨kz / 20, kz % 20, Nat.mod_lt kz (by decide), (Nat.div_add_mod kz 20).symm, rfl⟩

lemma div10_spec (kz : Nat) : ∃ q r, r < 10 ∧ kz = 10 * q + r ∧ kz / 10 = q :=
  ⟨kz / 10, kz % 10, Nat.mod_lt kz (by decide), (Nat.div_add_mod kz 10).symm, rfl⟩

lemma ox_bounds_relaxed {c k fz : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz : 35 ≤ fz) (hcz : 42 ≤ c + fz) (hkz : 73 ≤ k + 2 * fz) :
    39 ≤ ox (k + 2 * fz) (c + fz) ∧ ox (k + 2 * fz) (c + fz) + 3 ≤ c + fz := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  omega

lemma ox_ge41_of_c5 {c k fz : Nat}
    (_hc : 5 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    41 ≤ ox (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  omega

lemma arith_fb_t0 {c k z0 z1 fz2 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hz1 : 40 ≤ z1) (_hfz2 : 40 ≤ fz2) :
    ox (k + 2 * z0) (c + z0) ≤ ox (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (c + z0 + 3 + z1 + 1 + fz2) ∧
    odw (k + 2 * z0) (c + z0) ≤ odw (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (c + z0 + 3 + z1 + 1 + fz2) ∧
    oxw (k + 2 * z0) (c + z0) ≤ oxw (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (c + z0 + 3 + z1 + 1 + fz2) := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ :=
    ox_spec_lt (kz := k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (cz := c + z0 + 3 + z1 + 1 + fz2) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2)
  dsimp only [odw, oxw]
  rw [hdw1, hdw2, hox1, hox2]
  omega

lemma arith_fb_to {c k z0 z1 m1' fz2 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hz1 : 40 ≤ z1) (_hfz2 : 40 ≤ fz2) :
    ox (k + 2 * z0) (c + z0) ≤ c + z0 + 3 + z1 ∧
    30 * ox (k + 2 * z0) (c + z0) ≤ (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 27 * (c + z0 + 3 + z1) + 900 ∧
    60 * ox (k + 2 * z0) (c + z0) + 120 ≤ 2 * (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 55 * (c + z0 + 3 + z1) ∧
    10 * oxw (k + 2 * z0) (c + z0) + 40 ≤ 9 * (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 10 * (c + z0 + 3 + z1) ∧
    20 * oxw (k + 2 * z0) (c + z0) ≤ (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 20 * (c + z0 + 3 + z1) + 800 := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  dsimp only [oxw]
  rw [hdw1, hox1]
  omega

lemma arith_fb_te {c k z0 z1 m1' fz2 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hz1 : 40 ≤ z1) (_hfz2 : 40 ≤ fz2)
    (_hmrg : 2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) :
    ox (k + 2 * z0) (c + z0) ≤ ox ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (c + z0 + 3 + z1 + 2 + fz2) ∧
    odw (k + 2 * z0) (c + z0) ≤ odw ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (c + z0 + 3 + z1 + 2 + fz2) ∧
    oxw (k + 2 * z0) (c + z0) ≤ oxw ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (c + z0 + 3 + z1 + 2 + fz2) := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ :=
    ox_spec_lt (kz := (k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (cz := c + z0 + 3 + z1 + 2 + fz2) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2)
  dsimp only [odw, oxw]
  rw [hdw1, hdw2, hox1, hox2]
  omega

lemma arith_fb_m1_ev {c k z0 fz1 dx : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hfz1 : 40 ≤ fz1) (_hdx : dx ≤ 1) :
    ox (k + 2 * z0) (c + z0) ≤ c + z0 + dx ∧
    30 * ox (k + 2 * z0) (c + z0) ≤ (k + 2 * z0 + 4 + fz1) + 27 * (c + z0 + dx) + 900 ∧
    60 * ox (k + 2 * z0) (c + z0) + 120 ≤ 2 * (k + 2 * z0 + 4 + fz1) + 55 * (c + z0 + dx) ∧
    10 * oxw (k + 2 * z0) (c + z0) + 40 ≤ 9 * (k + 2 * z0 + 4 + fz1) + 10 * (c + z0 + dx) ∧
    20 * oxw (k + 2 * z0) (c + z0) ≤ (k + 2 * z0 + 4 + fz1) + 20 * (c + z0 + dx) + 800 := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  dsimp only [oxw]
  rw [hdw1, hox1]
  omega

lemma arith_fb_os_r10 {c k z0 y1 phi1 fz4 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hy1_lo : 9 * ((k + 2 * z0) / 10) - 2 ≤ y1)
    (_hy1_hi : y1 ≤ 2 * (c + z0) + 3)
    (_hphi1 : 38 ≤ phi1)
    (_hyw : k + 2 * z0 + 35 ≤ y1 + phi1)
    (_hfz4 : phi1 + 2 ≤ fz4) :
    ox (k + 2 * z0) (c + z0) ≤ ox (y1 + 2 + 2 * fz4) (c + z0 + 1 + fz4) ∧
    odw (k + 2 * z0) (c + z0) ≤ odw (y1 + 2 + 2 * fz4) (c + z0 + 1 + fz4) ∧
    oxw (k + 2 * z0) (c + z0) ≤ oxw (y1 + 2 + 2 * fz4) (c + z0 + 1 + fz4) := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨q4, r4, hr4, heq4, hox4⟩ := ox_spec_lt (kz := y1 + 2 + 2 * fz4) (cz := c + z0 + 1 + fz4) (by omega)
  obtain ⟨q10, r10, hr10, hkz10, hdw10⟩ := div10_spec (k + 2 * z0)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  obtain ⟨qw4, rw4, hrw4, hkw4, hdw4⟩ := div20_spec (y1 + 2 + 2 * fz4)
  rw [hdw10] at _hy1_lo
  dsimp only [odw, oxw]
  rw [hdw1, hdw4, hox1, hox4]
  omega

lemma arith_fb_os_r11 {c k z0 y1 phi1 fz4 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hyw : k + 2 * z0 + 35 ≤ y1 + phi1)
    (_hfz4 : phi1 + 2 ≤ fz4) :
    ox (k + 2 * z0) (c + z0) ≤ c + z0 - 1 ∧
    30 * ox (k + 2 * z0) (c + z0) ≤ (y1 + fz4) + 27 * (c + z0 - 1) + 900 ∧
    60 * ox (k + 2 * z0) (c + z0) + 120 ≤ 2 * (y1 + fz4) + 55 * (c + z0 - 1) ∧
    10 * oxw (k + 2 * z0) (c + z0) + 40 ≤ 9 * (y1 + fz4) + 10 * (c + z0 - 1) ∧
    20 * oxw (k + 2 * z0) (c + z0) ≤ (y1 + fz4) + 20 * (c + z0 - 1) + 800 := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  dsimp only [oxw]
  rw [hdw1, hox1]
  omega

lemma arith_lb_r10 {c k fz x tx txw y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_htx21 : 21 ≤ tx) (_htx_x : tx ≤ x)
    (_hi1 : 30 * tx ≤ (c + fz) + 27 * x + 900)
    (_hi2 : 60 * tx + 120 ≤ 2 * (c + fz) + 55 * x)
    (_hi3 : 10 * txw + 40 ≤ 9 * (c + fz) + 10 * x)
    (_hi4 : 20 * txw ≤ (c + fz) + 20 * x + 800)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y)
    (_hy_hi : y ≤ 2 * x + 3)
    (_hphi38 : 38 ≤ phi)
    (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    tx ≤ ox (y + 2 + 2 * fz3) (x + 1 + fz3) ∧
    tx - 1 ≤ odw (y + 2 + 2 * fz3) (x + 1 + fz3) ∧
    txw ≤ oxw (y + 2 + 2 * fz3) (x + 1 + fz3) := by
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨q3, r3, hr3, heq3, hox3⟩ := ox_spec_lt (kz := y + 2 + 2 * fz3) (cz := x + 1 + fz3) (by omega)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec (k + 2 * fz)
  obtain ⟨qw3, rw3, hrw3, hkw3, hdw3⟩ := div20_spec (y + 2 + 2 * fz3)
  dsimp only [oxw] at _hyw
  rw [hdw2] at _hyw
  rw [hox2] at _hy_lo
  dsimp only [odw, oxw]
  rw [hdw3, hox3]
  omega

lemma arith_lb_r11 {c k fz x tx txw y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_htx21 : 21 ≤ tx) (_htx_x : tx ≤ x)
    (_hi1 : 30 * tx ≤ (c + fz) + 27 * x + 900)
    (_hi2 : 60 * tx + 120 ≤ 2 * (c + fz) + 55 * x)
    (_hi3 : 10 * txw + 40 ≤ 9 * (c + fz) + 10 * x)
    (_hi4 : 20 * txw ≤ (c + fz) + 20 * x + 800)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y)
    (_hy_hi : y ≤ 2 * x + 4)
    (_hphi38 : 38 ≤ phi)
    (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    5 ≤ y ∧
    tx ≤ x - 1 ∧
    30 * tx ≤ (y + fz3) + 27 * (x - 1) + 900 ∧
    60 * tx + 120 ≤ 2 * (y + fz3) + 55 * (x - 1) ∧
    10 * txw + 40 ≤ 9 * (y + fz3) + 10 * (x - 1) ∧
    20 * txw ≤ (y + fz3) + 20 * (x - 1) + 800 := by
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec (k + 2 * fz)
  dsimp only [oxw] at _hyw
  rw [hdw2] at _hyw
  rw [hox2] at _hy_lo
  omega

-- ============================================================================
-- Pre-Pop Bounce Predicate & R9/R10/R11 Pop Dispatcher
-- ============================================================================

inductive IsBounce : Nat → List Nat → SegState → Prop where
  | nil {zl cp1 kb mrg : Nat} {ds : List Nat}
      (hphi : 230 ≤ cp1 + zl) :
      IsBounce (cp1 + zl) ds ⟨true, [], zl, cp1, kb, mrg, ds⟩
  | cons {z0 m zl cp1 kb mrg : Nat} {rest : List (Nat × Nat)} {ds : List Nat}
      (hv : ValidSegs40 rest zl)
      (hphi : 16 ≤ cp1 + z0)
      (hnm : if (m + 1) % 2 = 1 then mrg < kb + m else mrg < kb + (m + 1)) :
      IsBounce (cp1 + z0) ds ⟨true, (z0, m + 1) :: rest, zl, cp1, kb, mrg, ds⟩

lemma isBounce_step {phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi ds s) (hg_pop : drainPopGuards phi ds = true) :
    stepGuards s = true ∧ 16 ≤ phi ∧
      ∃ hp m_rem rest zl,
        (hp = true → ValidSegs40 rest zl) ∧
        (hp = false → 230 ≤ phi) ∧
        stepSegs s = drainPopStep hp phi m_rem rest zl ds := by
  cases hb with
  | @nil zl cp1 kb mrg ds hphi =>
    refine ⟨hg_pop, by omega, false, 0, [], zl, ?_, ?_, rfl⟩
    · intro h; cases h
    · intro _; exact hphi
  | @cons z0 m zl cp1 kb mrg rest ds hv hphi hnm =>
    refine ⟨?_, hphi, true, kb + (m + 1) - (mrg + 2), rest, zl, ?_, ?_, ?_⟩
    · dsimp only [stepGuards]
      rcases dec_or ((m + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod] at hnm ⊢
        rw [decide_eq_false (by omega)]; exact hg_pop
      · rw [if_neg hev] at hnm ⊢
        rw [decide_eq_false (by omega)]; exact hg_pop
    · intro _; exact hv
    · intro h; cases h
    · dsimp only [stepSegs]
      rcases dec_or ((m + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod] at hnm ⊢
        rw [decide_eq_false (by omega)]; rfl
      · rw [if_neg hev] at hnm ⊢
        rw [decide_eq_false (by omega)]; rfl

def Exit270 (tx tdw txw : Nat) (S : List Nat) (s : SegState) : Prop :=
  (∃ phi, tdw ≤ phi ∧ IsBounce phi S s) ∨
  (∃ y phi, tx ≤ y ∧ 38 ≤ phi ∧ txw ≤ y + phi ∧ IsBounce phi (y :: S) s)

lemma exit270_mono {tx1 tdw1 txw1 tx2 tdw2 txw2 : Nat} {S : List Nat} {s : SegState}
    (he : Exit270 tx2 tdw2 txw2 S s)
    (h1 : tx1 ≤ tx2) (h2 : tdw1 ≤ tdw2) (h3 : txw1 ≤ txw2) :
    Exit270 tx1 tdw1 txw1 S s := by
  rcases he with ⟨phi, hp, hb⟩ | ⟨y, phi, hy, hp38, hyw, hb⟩
  · exact Or.inl ⟨phi, Nat.le_trans h2 hp, hb⟩
  · exact Or.inr ⟨y, phi, Nat.le_trans h1 hy, hp38, Nat.le_trans h3 hyw, hb⟩

lemma drainPop_two (hp : Bool) (phi m_rem zl y x : Nat) (rest : List (Nat × Nat)) (S : List Nat)
    (hy : 19 ≤ y) (hx : 19 ≤ x) (hphi : 16 ≤ phi)
    (hg1 : GoodDs ((x - 1) :: S) = true)
    (hg2 : y % 2 = 0 ∧ y + 14 ≤ 2 * x → GoodDs ((x - 2) :: S) = true) :
    drainPopGuards phi (y :: x :: S) = true ∧
      drainPopStep hp phi m_rem rest zl (y :: x :: S) =
        let p := pushSeg hp (phi + 2) m_rem rest zl
        ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ := by
  have hnrst : isDrainRstDs (y :: x :: S) = false := by
    cases x with
    | zero => omega
    | succ _ => rfl
  have hnr0 : isRank0 (y :: x :: S) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  refine ⟨?_, ?_⟩
  · dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ x ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : (!decide (y % 2 = 0 ∧ y ≤ 2 * x + 4) || GoodDs ((x - 1) :: S)) = true := by
      rw [hg1, Bool.or_true]
    have hc3 : (!decide (y % 2 = 0 ∧ y + 14 ≤ 2 * x) || GoodDs ((x - 2) :: S)) = true := by
      rcases dec_or (y % 2 = 0 ∧ y + 14 ≤ 2 * x) with h | h
      · rw [hg2 h, Bool.or_true]
      · rw [decide_eq_false h]; rfl
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  · dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    rw [if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]

lemma amega_pop_step {N x y phi : Nat} {S : List Nat} {sb : SegState} {P : SegState → Prop}
    (hb : IsBounce phi (y :: x :: S) sb)
    (hphi38 : 38 ≤ phi) (hy : 19 ≤ y) (hx : 19 ≤ x)
    (hg1 : GoodDs ((x - 1) :: S) = true)
    (hg2 : y % 2 = 0 ∧ y + 14 ≤ 2 * x → GoodDs ((x - 2) :: S) = true)
    (hr9 : 2 * x + 5 ≤ y → ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 → phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨true, (0, y - 3) :: p1, p2, x - 1, 0, 2 * x, S⟩ P)
    (hr10 : y ≤ 2 * x + 3 → y % 2 = 1 → ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 → phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨false, p1, p2, x + 1, y + 2, 0, S⟩ P)
    (hr11 : y ≤ 2 * x + 4 → y % 2 = 0 → ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 → phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨false, p1, p2, y, 1, 0, (x - 1) :: S⟩ P) :
    ChainLeadsUpTo N sb P := by
  have hg_pop : drainPopGuards phi (y :: x :: S) = true :=
    (drainPop_two false phi 0 0 y x [] S hy hx (by omega) hg1 hg2).1
  obtain ⟨hg_sb, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep_sb⟩ := isBounce_step hb hg_pop
  have hdp_eq := (drainPop_two hp phi m_rem zl y x rest S hy hx (by omega) hg1 hg2).2
  rw [hdp_eq] at hstep_sb
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_sb
  intro m hm
  rw [hstep_sb]
  rcases dec_or (2 * x + 5 ≤ y) with hbig | hsmall
  · exact hr9 hbig m hm p.1 p.2 hvp hfzp
  · have hy_sub : y - 3 = (y - 4) + 1 := by omega
    rcases dec_or (y % 2 = 1) with hy_odd | hy_even
    · have hm_ev : ¬(((y - 4) + 1) % 2 = 1) := by omega
      have hmrg : decide (2 * x ≥ 0 + ((y - 4) + 1)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ = true := by
        rw [hy_sub]
        dsimp only [stepGuards]
        rw [if_neg hm_ev, hmrg, if_pos rfl]
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ =
          ⟨false, p.1, p.2, x + 1, y + 2, 0, S⟩ := by
        rw [hy_sub]
        dsimp only [stepSegs]
        rw [if_neg hm_ev, hmrg, if_pos rfl]
        have hc : x - 1 + 0 + 2 = x + 1 := by omega
        have hk : 0 + (y - 4 + 1) + 2 * 0 + 5 = y + 2 := by omega
        rw [hc, hk]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      exact hr10 (by omega) hy_odd m hm p.1 p.2 hvp hfzp
    · have hm_od : ((y - 4) + 1) % 2 = 1 := by omega
      have hmrg : decide (2 * x ≥ 0 + (y - 4)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ = true := by
        rw [hy_sub]
        dsimp only [stepGuards]
        rw [if_pos hm_od, hmrg, if_pos rfl]
        simpa only [Nat.add_zero] using hg1
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ =
          ⟨false, p.1, p.2, y, 1, 0, (x - 1) :: S⟩ := by
        rw [hy_sub]
        dsimp only [stepSegs]
        rw [if_pos hm_od, hmrg, if_pos rfl]
        have hc : 0 + (y - 4) + 2 * 0 + 4 = y := by omega
        have hx0 : x - 1 + 0 = x - 1 := by omega
        rw [hc, hx0]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      exact hr11 (by omega) (by omega) m hm p.1 p.2 hvp hfzp

lemma isBounce_r9 {x y : Nat} {p1 : List (Nat × Nat)} {p2 : Nat} {S : List Nat}
    (hx : 19 ≤ x) (hbig : 2 * x + 5 ≤ y) (hvp : ValidSegs40 p1 p2) :
    IsBounce (x - 1) S ⟨true, (0, y - 3) :: p1, p2, x - 1, 0, 2 * x, S⟩ := by
  have hy_sub : y - 3 = (y - 4) + 1 := by omega
  rw [hy_sub]
  have h := IsBounce.cons (z0 := 0) (m := y - 4) (zl := p2) (cp1 := x - 1) (kb := 0)
    (mrg := 2 * x) (rest := p1) (ds := S) hvp (by omega) (by
      rcases dec_or (((y - 4) + 1) % 2 = 1) with h1 | h1
      · rw [if_pos h1]; omega
      · rw [if_neg h1]; omega)
  simpa only [Nat.add_zero] using h

-- ============================================================================
-- Main Fuel-Indexed Excursion Bundle (`FBound N ∧ LoopBound N`)
-- ============================================================================

def FBound (N : Nat) : Prop :=
  ∀ ms S segs zl c k,
    19 ≤ ms → SafeStack ms S →
    ValidTail40 segs zl →
    1 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    35 ≤ fzOf segs zl →
    42 ≤ c + fzOf segs zl →
    73 ≤ k + 2 * fzOf segs zl →
    ms + 2 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, S⟩
      (Exit270 (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) S)

def LoopBound (N : Nat) : Prop :=
  ∀ ms S segs zl c k x tx txw,
    19 ≤ ms → SafeStack ms S →
    (S ≠ [1] ∨ 5 ≤ c) →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    ms + 2 ≤ tx → tx ≤ x →
    30 * tx ≤ (c + fzOf segs zl) + 27 * x + 900 →
    60 * tx + 120 ≤ 2 * (c + fzOf segs zl) + 55 * x →
    10 * txw + 40 ≤ 9 * (c + fzOf segs zl) + 10 * x →
    20 * txw ≤ (c + fzOf segs zl) + 20 * x + 800 →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: S⟩
      (Exit270 tx (tx - 1) txw S)

lemma excursion270_bundle (N : Nat) : FBound N ∧ LoopBound N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hFB : FBound N := by
      intro ms S segs zl c k hms19 hS hvt hc hk1 hkc hfz35 hcz42 hkz73 hms_ox
      obtain ⟨hox39, hox_cz3⟩ := ox_bounds_relaxed hc hk1 hkc hfz35 hcz42 hkz73
      rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
      · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
        have hg : stepGuards ⟨false, [], zl, c, k, 0, S⟩ = true := by
          dsimp only [stepGuards]
          rw [goodPhiW_of_ge35 hS.1 (by omega), Bool.true_and]
          dsimp only [GoodPsi]
          have hcz : c + zl - 1 + 1 = c + zl := by omega
          rw [hcz]; exact hS.2.2 (c + zl) (by omega)
        apply chainLeadsUpTo_step1 hg
        dsimp only [stepSegs]
        apply chainLeadsUpTo_here
        obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * zl)
        refine Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, by omega, ?_, ?_⟩
        · dsimp only [oxw]; rw [hdw]; omega
        · simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
            (mrg := 2 * (k + 2 * zl) + 6) (ds := (c + zl) :: S) (by omega)
      · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
        have hv_rest : ValidSegs40 rest zl := hvt
        cases m0 with
        | zero =>
          have hg1 : stepGuards ⟨false, (z0, 0) :: rest, zl, c, k, 0, S⟩ = true := rfl
          apply chainLeadsUpTo_step hg1
          intro m1 hm1
          dsimp only [stepSegs]
          rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
          · have hzl230 : 230 ≤ zl := hv_rest.2
            exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + zl, by dsimp only [odw]; omega,
              IsBounce.nil (by omega)⟩)
          · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
            have hv_rest2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
            have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_rest2
            cases m1_seg with
            | zero =>
              have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; exact decide_eq_true (by omega)
              apply chainLeadsUpTo_step hg2
              intro m2 hm2
              dsimp only [stepSegs]
              have hmono := arith_fb_t0 hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
              exact chainLeadsUpTo_imp
                ((ih m2 (by omega)).1 ms S rest2 zl (c + z0 + 3 + z1 + 1) (k + 2 * z0 + 3 + 2 * z1 + 3)
                  hms19 hS (validTail40_of_validSegs40 hv_rest2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  (Nat.le_trans hms_ox hmono.1))
                (fun s' he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2)
            | succ m1' =>
              rcases dec_or ((m1' + 1) % 2 = 1) with hm1_odd | hm1_even
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
                | true =>
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                    exact hS.2.2 (c + z0 + 3 + z1) (by omega)
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                  have hi := arith_fb_to (m1' := m1') hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
                  exact (ih m2 (by omega)).2 ms S rest2 zl
                    ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1 (c + z0 + 3 + z1)
                    (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                    hms19 hS (Or.inr (by omega)) hv_rest2
                    (by omega) (by omega) (by omega) hms_ox hi.1
                    hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') := of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_pos hm1_odd]; omega)⟩)
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
                | true =>
                  have h_mrg : 2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1) := of_decide_eq_true hd_mrg
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  have hmono := arith_fb_te hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40 h_mrg
                  exact chainLeadsUpTo_imp
                    ((ih m2 (by omega)).1 ms S rest2 zl (c + z0 + 3 + z1 + 2) ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                      hms19 hS (validTail40_of_validSegs40 hv_rest2)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      (Nat.le_trans hms_ox hmono.1))
                    (fun s' he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2)
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) := of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_neg hm1_even]; omega)⟩)
        | succ m' =>
          have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
          have hphiw : GoodPhiW (c + z0 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
          rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
          · have hm0_eq : m' = 0 := by omega
            subst hm0_eq
            have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false && if 1 = 1 then GoodPsi (c + z0) S else _) = true
              rw [hphiw, Bool.true_and, if_pos rfl]
              exact hS.2.2 (c + z0 + 1) (by omega)
            apply chainLeadsUpTo_step hg
            intro m1 hm1
            dsimp only [stepSegs]
            change ChainLeadsUpTo m1 (if 1 = 1 then _ else _) _
            rw [if_pos rfl]
            have hi := arith_fb_m1_ev (dx := 1) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
            exact (ih m1 hm1).2 ms S rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1)
              (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
              hms19 hS (Or.inr (by omega)) hv_rest
              (by omega) (by omega) (by omega) hms_ox hi.1
              hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
          · have hpsi_cz : GoodPsi (c + z0 - 1) S = true := by
              dsimp only [GoodPsi]
              have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
              rw [hcz_eq]; exact hS.2.2 (c + z0) (by omega)
            rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
              apply chainLeadsUpTo_step hg
              intro m1 hm1
              dsimp only [stepSegs]
              change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
              rw [if_neg hm_gt1, if_pos hev_sm]
              have hi := arith_fb_m1_ev (dx := 0) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
              have hcz0 : c + z0 + 0 = c + z0 := by omega
              rw [hcz0] at hi
              exact (ih m1 hm1).2 ms S rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0)
                (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                hms19 hS (Or.inr (by omega)) hv_rest
                (by omega) (by omega) (by omega) hms_ox hi.1
                hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
            · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
              · have hS_cz : SafeStack 39 ((c + z0) :: S) := safeStack_cons hS (by omega) (by omega)
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                        GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: S) else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_pos hod_sm]
                  exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
                apply chainLeadsUpTo_step hg
                intro m1 hm1
                dsimp only [stepSegs]
                change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                obtain ⟨q10, r10, hr10, hkz10, hdw10⟩ := div10_spec (k + 2 * z0)
                have hos_in : 39 + 2 ≤ 9 * q10 - 2 ∧ 9 * q10 - 2 ≤ k + 2 * z0 + 2 ∧
                    30 * (9 * q10 - 2) ≤ (m' + fzOf rest zl) + 27 * (k + 2 * z0 + 2) + 900 ∧
                    60 * (9 * q10 - 2) + 120 ≤ 2 * (m' + fzOf rest zl) + 55 * (k + 2 * z0 + 2) ∧
                    10 * (k + 2 * z0 + 35) + 40 ≤ 9 * (m' + fzOf rest zl) + 10 * (k + 2 * z0 + 2) ∧
                    20 * (k + 2 * z0 + 35) ≤ (m' + fzOf rest zl) + 20 * (k + 2 * z0 + 2) + 800 := by omega
                have hm_sub : m' + 1 - 1 = m' := by omega
                rw [hm_sub]
                have hne1_cz : ((c + z0) :: S) ≠ [1] := by intro h; injection h with h1; omega
                have h_loop1 := (ih m1 hm1).2 39 ((c + z0) :: S) rest zl m' 1
                  (k + 2 * z0 + 2) (9 * q10 - 2) (k + 2 * z0 + 35)
                  (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                  (by omega) (by omega) (by omega) hos_in.1 hos_in.2.1
                  hos_in.2.2.1 hos_in.2.2.2.1 hos_in.2.2.2.2.1 hos_in.2.2.2.2.2
                refine chainLeadsUpTo_trans h_loop1 ?_
                intro m2 s_mid hm2 hexit1
                rcases hexit1 with ⟨phi1, hphi1, hb1⟩ | ⟨y1, phi1, hy1_tx1, hphi1_38, hyw1, hb1⟩
                · apply chainLeadsUpTo_here
                  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
                  refine Or.inr ⟨c + z0, phi1, by omega, by omega, ?_, hb1⟩
                  dsimp only [oxw]; rw [hdw]; omega
                · exact amega_pop_step hb1 hphi1_38 (by omega) (by omega)
                    (hS.2.2 (c + z0 - 1) (by omega))
                    (fun _ => hS.2.2 (c + z0 - 2) (by omega))
                    (fun hbig _ _ p1 p2 hvp _ =>
                      chainLeadsUpTo_here (Or.inl ⟨c + z0 - 1, by dsimp only [odw]; omega,
                        isBounce_r9 (by omega) hbig hvp⟩))
                    (fun hy1_le _ m3 hm3 p1 p2 hvp hfzp => by
                      have hy1_lo : 9 * ((k + 2 * z0) / 10) - 2 ≤ y1 := by rw [hdw10]; exact hy1_tx1
                      have hmono := arith_fb_os_r10 hc hk1 hkc hfz35 hcz42 hkz73 hy1_lo hy1_le hphi1_38 hyw1 hfzp
                      exact chainLeadsUpTo_imp
                        ((ih m3 (by omega)).1 ms S p1 p2 (c + z0 + 1) (y1 + 2) hms19 hS
                          (validTail40_of_validSegs40 hvp)
                          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                          (Nat.le_trans hms_ox hmono.1))
                        (fun s' he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2))
                    (fun hy1_le _ m3 hm3 p1 p2 hvp hfzp => by
                      have hi := arith_fb_os_r11 hc hk1 hkc hfz35 hcz42 hkz73 hyw1 hfzp
                      exact (ih m3 (by omega)).2 ms S p1 p2 y1 1 (c + z0 - 1)
                        (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                        hms19 hS (Or.inr (by omega)) hvp
                        (by omega) (by omega) (by omega) hms_ox hi.1
                        hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2)
              · have hm0_big : 2 * (k + 2 * z0) + 12 ≤ m' + 1 := by omega
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_neg hbig_m]
                apply chainLeadsUpTo_step1 hg
                dsimp only [stepSegs]
                change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
                have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                  dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
                rw [hnorm]
                apply chainLeadsUpTo_here
                obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
                refine Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, by omega, ?_, ?_⟩
                · dsimp only [oxw]; rw [hdw]; omega
                · have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                    (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                    (rest := rest) (ds := (c + z0) :: S) hv_rest (by omega) (by
                      rcases dec_or (((m' - 4) + 1) % 2 = 1) with h | h
                      · rw [if_pos h]; omega
                      · rw [if_neg h]; omega)
                  simpa only [Nat.add_zero] using hbc
    have hLB : LoopBound N := by
      intro ms S segs zl c k x tx txw hms19 hS hSc5 hv hc hk1 hkc hms_tx htx_x hi1 hi2 hi3 hi4
      have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
      have hox39 : 39 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) :=
        (ox_bounds_relaxed (by omega) hk1 hkc (by omega) (by omega) (by omega)).1
      have hfb : ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: S⟩
          (Exit270 (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
            (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
            (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) (x :: S)) := by
        rcases hSc5 with hne1 | hc5
        · exact hFB 19 (x :: S) segs zl c k (by decide)
            (safeStack_cons_ne1 hne1 hS (by omega) (by omega))
            (validTail40_of_validSegs40 hv)
            (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
        · have hox41 := ox_ge41_of_c5 hc5 hk1 hkc hfz40
          exact hFB 39 (x :: S) segs zl c k (by decide)
            (safeStack_cons hS (by omega) (by omega))
            (validTail40_of_validSegs40 hv)
            (by omega) hk1 hkc (by omega) (by omega) (by omega) hox41
      refine chainLeadsUpTo_trans hfb ?_
      intro m1 s_mid hm1 hexit
      rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
      · apply chainLeadsUpTo_here
        obtain ⟨q, r, hr, heq, hox⟩ :=
          ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
        dsimp only [odw] at hphi_odw
        rw [hox] at hphi_odw hox39
        exact Or.inr ⟨x, phi, htx_x, by omega, by omega, hb⟩
      · exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS.2.2 (x - 1) (by omega)) (fun _ => hS.2.2 (x - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inl ⟨x - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
          (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
            have hmono := arith_lb_r10 hc hk1 hkc hfz40 (by omega) htx_x
              hi1 hi2 hi3 hi4 hy_ox hy_le hphi38 hyw hfzp
            exact chainLeadsUpTo_imp
              ((ih m2 (by omega)).1 ms S p1 p2 (x + 1) (y + 2) hms19 hS
                (validTail40_of_validSegs40 hvp)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (Nat.le_trans hms_tx hmono.1))
              (fun s' he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2))
          (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
            have hr11 := arith_lb_r11 hc hk1 hkc hfz40 (by omega) htx_x
              hi1 hi2 hi3 hi4 hy_ox hy_le hphi38 hyw hfzp
            exact (ih m2 (by omega)).2 ms S p1 p2 y 1 (x - 1) tx txw
              hms19 hS (Or.inr hr11.1) hvp
              (by omega) (by omega) (by omega) hms_tx hr11.2.1
              hr11.2.2.1 hr11.2.2.2.1 hr11.2.2.2.2.1 hr11.2.2.2.2.2)
    exact ⟨hFB, hLB⟩


-- ============================================================================
-- Section 5g.3a: SafeStack Bases & High-Excursion Bundle (`FHigh`, `LoopHigh`, `LoopOS`)
-- ============================================================================

lemma safeStack_nil : SafeStack 19 [] := by
  refine ⟨(by intro h; cases h), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs, GoodDsAux, GoodDs1]
  exact decide_eq_true (by omega)

lemma safeStack_zero : SafeStack 19 [0] := by
  refine ⟨(by intro h; injection h with h1; omega), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs, GoodDsAux, GoodDs2]
  rw [if_pos rfl]
  exact decide_eq_true (by omega)

lemma safeStack_one : SafeStack 25 [1] := by
  refine ⟨(by intro h; injection h with h1; omega), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs, GoodDsAux, GoodDs2]
  rw [if_neg (by decide), if_pos rfl]
  exact decide_eq_true (by omega)

lemma safeStack_31 : SafeStack 19 [3, 1] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by decide)]
  have h1 : decide (3 = 3 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
    decide_eq_false (by omega)
  have h2 : isOddDrainDs [3, 1] = false := rfl
  have h3 : decide (3 ≥ 25 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false := rfl
  have h4 : decide (u < 17) = false := decide_eq_false (by omega)
  have h5 : GoodDsAux 3 [1] = true := rfl
  have h6 : decide (u % 2 = 0 ∧ u ≤ 2 * 3 + 4) = false := decide_eq_false (by omega)
  have h7 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * 3) = false := decide_eq_false (by omega)
  rw [h1, h2, h3, h4, h5, h6, h7]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

lemma safeStack_x_31 {x : Nat} (hx20 : 20 ≤ x) (hx22 : x ≤ 22) :
    SafeStack 39 [x, 3, 1] := by
  have hgx : GoodDs [x, 3, 1] = true := safeStack_31.2.2 x (by omega)
  have hgx1 : GoodDs [x - 1, 3, 1] = true := safeStack_31.2.2 (x - 1) (by omega)
  refine ⟨(by intro h; injection h with _ h2; cases h2), hgx, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by omega)]
  have h1 : decide (x = 3 ∧ 3 = 1 ∧ [1] = [] ∧ u < 19) = false := decide_eq_false (by omega)
  have h2 : isOddDrainDs [x, 3, 1] = false := rfl
  have h3 : decide (x ≥ 25 ∧ 3 = 1 ∧ [1] = [] ∧ u < 39) = false := decide_eq_false (by omega)
  have h4 : decide (u < 17) = false := decide_eq_false (by omega)
  have h7 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * x) = false := decide_eq_false (by omega)
  have hgx' : GoodDsAux x [3, 1] = true := hgx
  have hgx1' : GoodDsAux (x - 1) [3, 1] = true := hgx1
  rw [h1, h2, h3, h4, hgx', hgx1', h7]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

lemma safeStack_d {d : Nat} (hd8 : 8 ≤ d) : SafeStack 21 [d] := by
  refine ⟨(by intro h; injection h with h1; omega), ?_, ?_⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs1]; exact decide_eq_true (by omega)
  · intro u hu
    dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDs1 d = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hc1 : (decide (u % 2 = 0 ∧ u ≤ 2 * d + 4) && !GoodDs1 (d - 1)) = false := by
      rcases dec_or (d = 8) with rfl | hd9
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg1 : GoodDs1 (d - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
        rw [hg1, Bool.not_true, Bool.and_false]
    have hc2 : (decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d) && !GoodDs1 (d - 2)) = false := by
      rcases dec_or (d ≤ 9) with hd9 | hd10
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg2 : GoodDs1 (d - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
        rw [hg2, Bool.not_true, Bool.and_false]
    rw [hu19, hu17, hgd, hc1, hc2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

lemma safeStack_d0 {d : Nat} (hd8 : 8 ≤ d) : SafeStack 21 [d, 0] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), ?_, ?_⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
  · intro u hu
    dsimp only [GoodDs]
    rw [GoodDsAux.eq_3, if_neg (by omega)]
    have h1 : decide (d = 3 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
      decide_eq_false (by omega)
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have h3 : decide (d ≥ 25 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false :=
      decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDsAux d [0] = true := by
      dsimp only [GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
    have hc1 : (decide (u % 2 = 0 ∧ u ≤ 2 * d + 4) && !GoodDsAux (d - 1) [0]) = false := by
      rcases dec_or (d = 8) with rfl | hd9
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg1 : GoodDsAux (d - 1) [0] = true := by
          dsimp only [GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
        rw [hg1, Bool.not_true, Bool.and_false]
    have hc2 : (decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d) && !GoodDsAux (d - 2) [0]) = false := by
      rcases dec_or (d ≤ 9) with hd9 | hd10
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg2 : GoodDsAux (d - 2) [0] = true := by
          dsimp only [GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
        rw [hg2, Bool.not_true, Bool.and_false]
    rw [h1, hu19, h3, hu17, hgd, hc1, hc2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

lemma safeStack_d1 {d : Nat} (hd26 : 26 ≤ d) : SafeStack 39 [d, 1] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), safeStack_one.2.2 d (by omega), ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by omega)]
  have h1 : decide (d = 3 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
    decide_eq_false (by omega)
  have h2 : isOddDrainDs [d, 1] = false := rfl
  have h3 : decide (d ≥ 25 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false :=
    decide_eq_false (by omega)
  have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
  have hgd : GoodDsAux d [1] = true := safeStack_one.2.2 d (by omega)
  have hg1 : GoodDsAux (d - 1) [1] = true := safeStack_one.2.2 (d - 1) (by omega)
  have hc2 : (decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d) && !GoodDsAux (d - 2) [1]) = false := by
    rcases dec_or (d = 26) with rfl | hd27
    · rw [decide_eq_false (by omega), Bool.false_and]
    · have hg2 : GoodDsAux (d - 2) [1] = true := safeStack_one.2.2 (d - 2) (by omega)
      rw [hg2, Bool.not_true, Bool.and_false]
  rw [h1, h2, h3, hu17, hgd, hg1, hc2]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

lemma safeStack_of_gt2d2 {m d2 d3 : Nat} {ds3 : List Nat}
    (_hm39 : 39 ≤ m) (hm_gt : 2 * d2 + 5 ≤ m) (hd2 : 17 ≤ d2)
    (hg : GoodDs (d2 :: d3 :: ds3) = true) :
    SafeStack m (d2 :: d3 :: ds3) := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), hg, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by omega)]
  have h1 : decide (d2 = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 19) = false := decide_eq_false (by omega)
  have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
  have h3 : decide (d2 ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 39) = false := decide_eq_false (by omega)
  have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
  have hg0 : GoodDsAux d2 (d3 :: ds3) = true := hg
  have hc1 : decide (u % 2 = 0 ∧ u ≤ 2 * d2 + 4) = false := decide_eq_false (by omega)
  have hc2 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d2) = false := decide_eq_false (by omega)
  rw [h1, hu19, h3, hu17, hg0, hc1, hc2]
  simp only [Bool.and_false, Bool.false_and, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ite_false]

lemma safeStack_25_1 : SafeStack 55 [25, 1] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

lemma safeStack_17_8_0 : SafeStack 39 [17, 8, 0] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

lemma safeStack_20_3_1 : SafeStack 27 [20, 3, 1] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by decide)]
  have h1 : decide (20 = 3 ∧ 3 = 1 ∧ [1] = [] ∧ u < 19) = false := rfl
  have h2 : isOddDrainDs [20, 3, 1] = false := rfl
  have h3 : decide (20 ≥ 25 ∧ 3 = 1 ∧ [1] = [] ∧ u < 39) = false := rfl
  have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
  have hg0 : GoodDsAux 20 [3, 1] = true := rfl
  have hg1 : GoodDsAux 19 [3, 1] = true := rfl
  have hc2 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * 20) = false := decide_eq_false (by omega)
  rw [h1, h2, h3, hu17, hg0, hg1, hc2]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

lemma safeStack_19_9 : SafeStack 43 [19, 9] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

lemma safeStack_19_9_0 : SafeStack 43 [19, 9, 0] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

lemma safeStack_47_25_1 : SafeStack 99 [47, 25, 1] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

-- ============================================================================
-- High-Excursion Arithmetic Lemmas & Bundle (`FHigh`, `LoopHigh`, `LoopOS`)
-- ============================================================================

def ExitHigh (S : List Nat) (s : SegState) : Prop :=
  (∃ phi, 48 ≤ phi ∧ IsBounce phi S s) ∨
  (∃ y phi, 49 ≤ y ∧ ((53 ≤ y ∧ 90 ≤ phi) ∨ 100 ≤ phi) ∧ IsBounce phi (y :: S) s)

lemma arith_lh_bounds {c k fz : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) (_hcz : 131 ≤ c + fz) :
    119 ≤ ox (k + 2 * fz) (c + fz) ∧ 118 ≤ odw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  dsimp only [odw]
  omega

lemma arith_los_r11 {c k fz x y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_hx : 91 ≤ x) (_hpot : 2220 ≤ (c + fz) + 22 * x)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y) (_hy_hi : y ≤ 2 * x + 4)
    (_hphi38 : 38 ≤ phi) (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    39 ≤ y ∧ 91 ≤ x - 1 ∧ 2220 ≤ (y + fz3) + 22 * (x - 1) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [oxw] at _hyw
  rw [hdw] at _hyw
  rw [hox] at _hy_lo
  omega

def FHigh (N : Nat) : Prop :=
  ∀ S segs zl c k,
    S ≠ [1] → SafeStack 43 S →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    53 ≤ c + fzOf segs zl →
    97 ≤ k + 2 * fzOf segs zl →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, S⟩ (ExitHigh S)

def LoopHigh (N : Nat) : Prop :=
  ∀ S segs zl c k x,
    S ≠ [1] → SafeStack 43 S →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    49 ≤ x →
    131 ≤ c + fzOf segs zl →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: S⟩ (ExitHigh S)

def LoopOS (N : Nat) : Prop :=
  ∀ S segs zl c k x cz_out,
    S ≠ [1] → SafeStack 43 S →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    53 ≤ cz_out →
    91 ≤ x →
    2220 ≤ (c + fzOf segs zl) + 22 * x →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: cz_out :: S⟩ (ExitHigh S)

lemma fhigh_bundle (N : Nat) : FHigh N ∧ LoopHigh N ∧ LoopOS N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hFH : FHigh N := by
      intro S segs zl c k hne1 hS hv hc hk1 hkc hcz53 hkz99
      rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
      · dsimp only [fzOf] at hcz53 hkz99
        have hzl230 : 230 ≤ zl := hv.2
        have hg : stepGuards ⟨false, [], zl, c, k, 0, S⟩ = true := by
          dsimp only [stepGuards]
          rw [goodPhiW_of_ge35 hS.1 (by omega), Bool.true_and]
          dsimp only [GoodPsi]
          have hcz : c + zl - 1 + 1 = c + zl := by omega
          rw [hcz]; exact hS.2.2 (c + zl) (by omega)
        apply chainLeadsUpTo_step1 hg
        dsimp only [stepSegs]
        apply chainLeadsUpTo_here
        refine Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, Or.inr (by omega), ?_⟩
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := (c + zl) :: S) (by omega)
      · have hz0_40 : 40 ≤ z0 := fzOf_ge_40 hv
        have hv_rest : ValidSegs40 rest zl := validSegs40_tail hv
        dsimp only [fzOf] at hcz53 hkz99
        cases m0 with
        | zero =>
          have hg1 : stepGuards ⟨false, (z0, 0) :: rest, zl, c, k, 0, S⟩ = true := rfl
          apply chainLeadsUpTo_step hg1
          intro m1 hm1
          dsimp only [stepSegs]
          rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
          · have hzl230 : 230 ≤ zl := hv_rest.2
            exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + zl, by omega, IsBounce.nil (by omega)⟩)
          · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
            have hv_rest2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
            have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_rest2
            cases m1_seg with
            | zero =>
              have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; exact decide_eq_true (by omega)
              apply chainLeadsUpTo_step hg2
              intro m2 hm2
              dsimp only [stepSegs]
              exact (ih m2 (by omega)).1 S rest2 zl (c + z0 + 3 + z1 + 1) (k + 2 * z0 + 3 + 2 * z1 + 3)
                hne1 hS hv_rest2 (by omega) (by omega) (by omega) (by omega) (by omega)
            | succ m1' =>
              rcases dec_or ((m1' + 1) % 2 = 1) with hm1_odd | hm1_even
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
                | true =>
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                    exact hS.2.2 (c + z0 + 3 + z1) (by omega)
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                  exact (ih m2 (by omega)).2.1 S rest2 zl ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1
                    (c + z0 + 3 + z1) hne1 hS hv_rest2
                    (by omega) (by omega) (by omega) (by omega) (by omega)
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') := of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_pos hm1_odd]; omega)⟩)
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
                | true =>
                  have h_mrg : 2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1) := of_decide_eq_true hd_mrg
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  exact (ih m2 (by omega)).1 S rest2 zl (c + z0 + 3 + z1 + 2)
                    ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                    hne1 hS hv_rest2 (by omega) (by omega) (by omega) (by omega) (by omega)
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) := of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_neg hm1_even]; omega)⟩)
        | succ m' =>
          have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
          have hphiw : GoodPhiW (c + z0 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
          rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
          · have hm0_eq : m' = 0 := by omega
            subst hm0_eq
            have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false && if 1 = 1 then GoodPsi (c + z0) S else _) = true
              rw [hphiw, Bool.true_and, if_pos rfl]
              exact hS.2.2 (c + z0 + 1) (by omega)
            apply chainLeadsUpTo_step hg
            intro m1 hm1
            dsimp only [stepSegs]
            change ChainLeadsUpTo m1 (if 1 = 1 then _ else _) _
            rw [if_pos rfl]
            exact (ih m1 hm1).2.1 S rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1)
              hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega)
          · have hpsi_cz : GoodPsi (c + z0 - 1) S = true := by
              dsimp only [GoodPsi]
              have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
              rw [hcz_eq]; exact hS.2.2 (c + z0) (by omega)
            rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
              apply chainLeadsUpTo_step hg
              intro m1 hm1
              dsimp only [stepSegs]
              change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
              rw [if_neg hm_gt1, if_pos hev_sm]
              exact (ih m1 hm1).2.1 S rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0)
                hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega)
            · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
              · have hS_cz : SafeStack 19 ((c + z0) :: S) :=
                  safeStack_cons_ne1 hne1 hS (by omega) (by omega)
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                        GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: S) else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_pos hod_sm]
                  exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
                apply chainLeadsUpTo_step hg
                intro m1 hm1
                dsimp only [stepSegs]
                change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                have hm_sub : m' + 1 - 1 = m' := by omega
                rw [hm_sub]
                exact (ih m1 hm1).2.2 S rest zl m' 1 (k + 2 * z0 + 2) (c + z0)
                  hne1 hS hv_rest (by omega) (by omega) (by omega) hcz53 (by omega) (by omega)
              · have hm0_big : 2 * (k + 2 * z0) + 12 ≤ m' + 1 := by omega
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_neg hbig_m]
                apply chainLeadsUpTo_step1 hg
                dsimp only [stepSegs]
                change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
                have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                  dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
                rw [hnorm]
                apply chainLeadsUpTo_here
                refine Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, Or.inl ⟨hcz53, by omega⟩, ?_⟩
                have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := (c + z0) :: S) hv_rest (by omega) (by
                    rcases dec_or (((m' - 4) + 1) % 2 = 1) with h | h
                    · rw [if_pos h]; omega
                    · rw [if_neg h]; omega)
                simpa only [Nat.add_zero] using hbc
    have hLH : LoopHigh N := by
      intro S segs zl c k x hne1 hS hv hc hk1 hkc hx49 hcz135
      have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
      obtain ⟨hox101, hodw100⟩ := arith_lh_bounds hc hk1 hkc hfz40 hcz135
      have hSx : SafeStack 19 (x :: S) := safeStack_cons_ne1 hne1 hS (by omega) (by omega)
      have hfb := (excursion270_bundle N).1 19 (x :: S) segs zl c k (by decide) hSx
        (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
      refine chainLeadsUpTo_trans hfb ?_
      intro m1 s_mid hm1 hexit
      rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, _, hb⟩
      · exact chainLeadsUpTo_here (Or.inr ⟨x, phi, hx49, Or.inr (by omega), hb⟩)
      · exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS.2.2 (x - 1) (by omega)) (fun _ => hS.2.2 (x - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inl ⟨x - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).1 S p1 p2 (x + 1) (y + 2) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
          (fun hy_le _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).2.1 S p1 p2 y 1 (x - 1) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
    have hLOS : LoopOS N := by
      intro S segs zl c k x cz_out hne1 hS hv hc hk1 hkc hcz_out hx96 hpot
      have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
      have hox39 : 39 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) :=
        (ox_bounds_relaxed (by omega) hk1 hkc (by omega) (by omega) (by omega)).1
      have hS_cz : SafeStack 19 (cz_out :: S) := safeStack_cons_ne1 hne1 hS (by omega) (by omega)
      have hne1_cz : (cz_out :: S) ≠ [1] := by intro h; injection h with h1; omega
      have hS_xcz : SafeStack 19 (x :: cz_out :: S) :=
        safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
      have hfb := (excursion270_bundle N).1 19 (x :: cz_out :: S) segs zl c k (by decide) hS_xcz
        (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
      refine chainLeadsUpTo_trans hfb ?_
      intro m1 s_mid hm1 hexit
      rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
      · have hphi38 : 38 ≤ phi := by
          obtain ⟨q, r, hr, heq, hox⟩ :=
            ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
          dsimp only [odw] at hphi_odw; rw [hox] at hphi_odw hox39; omega
        exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS.2.2 (cz_out - 1) (by omega)) (fun _ => hS.2.2 (cz_out - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inl ⟨cz_out - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).1 S p1 p2 (cz_out + 1) (x + 2) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).2.1 S p1 p2 x 1 (cz_out - 1) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
      · exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS_cz.2.2 (x - 1) (by omega)) (fun _ => hS_cz.2.2 (x - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inr ⟨cz_out, x - 1, by omega,
              Or.inl ⟨hcz_out, by omega⟩, isBounce_r9 (by omega) hbig hvp⟩))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).2.1 S p1 p2 (x + 1) (y + 2) cz_out hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
          (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
            have hlos := arith_los_r11 hc hk1 hkc hfz40 hx96 hpot hy_ox hy_le hphi38 hyw hfzp
            exact (ih m2 (by omega)).2.2 S p1 p2 y 1 (x - 1) cz_out hne1 hS hvp
              (by omega) (by omega) (by omega) hcz_out hlos.2.1 hlos.2.2)
    exact ⟨hFH, hLH, hLOS⟩


-- ============================================================================
-- Section 5g.3b: Excursion Helpers, Root Invariant, and Drain-Pop Closures
-- ============================================================================

lemma chainLeads_trans {s : SegState} {P Q : SegState → Prop}
    (h1 : ChainLeads s P) (h2 : ∀ s', P s' → ChainLeads s' Q) :
    ChainLeads s Q :=
  fun N => chainLeadsUpTo_trans (h1 N) (fun m s' _ hp => h2 s' hp m)

-- ============================================================================
-- Generic Forced-R9 & k=1 Boost Helpers (`fbound_force_r9`, `fbound_k1_boost`)
-- ============================================================================

lemma fbound_force_r9 {N x d3 : Nat} {ds3 : List Nat} {segs : List (Nat × Nat)} {zl c k : Nat}
    {P : SegState → Prop}
    (hx19 : 19 ≤ x)
    (hgx : GoodDs (x :: d3 :: ds3) = true)
    (hg_pop1 : GoodDs ((x - 1) :: d3 :: ds3) = true)
    (hv : ValidSegs40 segs zl)
    (hc : 1 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hcz42 : 42 ≤ c + fzOf segs zl)
    (hox : 2 * x + 7 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
    (hcont1 : ∀ m phi, m ≤ N → 2 * x + 6 ≤ phi → ∀ s',
      IsBounce phi (x :: d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (hcont2 : ∀ m, m < N → ∀ s',
      IsBounce (x - 1) (d3 :: ds3) s' → ChainLeadsUpTo m s' P) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: d3 :: ds3⟩ P := by
  have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
  have hS : SafeStack (2 * x + 5) (x :: d3 :: ds3) :=
    safeStack_of_gt2d2 (by omega) (Nat.le_refl _) (by omega) hgx
  have hfb := (excursion270_bundle N).1 (2 * x + 5) (x :: d3 :: ds3) segs zl c k
    (by omega) hS (validTail40_of_validSegs40 hv) hc hk1 hkc
    (by omega) hcz42 (by omega) hox
  refine chainLeadsUpTo_trans hfb ?_
  intro m1 s_mid hm1 hexit
  rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, _, hb⟩
  · have hphi_ge : 2 * x + 6 ≤ phi := by dsimp only [odw] at hphi_odw; omega
    exact hcont1 m1 phi hm1 hphi_ge s_mid hb
  · exact amega_pop_step hb hphi38 (by omega) hx19 hg_pop1
      (by rintro ⟨_, h⟩; omega)
      (fun hbig m2 hm2 p1 p2 hvp _ =>
        hcont2 m2 (Nat.lt_of_lt_of_le hm2 hm1) _ (isBounce_r9 hx19 hbig hvp))
      (fun hle => False.elim (by omega))
      (fun hle => False.elim (by omega))

lemma arith_boost_c85 {c k fz : Nat}
    (_hc : 85 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    114 ≤ ox (k + 2 * fz) (c + fz) ∧ 113 ≤ odw (k + 2 * fz) (c + fz) ∧
    165 ≤ oxw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [odw, oxw]; rw [hdw, hox]; omega

lemma arith_boost_r10 {c k fz : Nat}
    (_hc : 43 ≤ c) (_hk : 72 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    73 ≤ ox (k + 2 * fz) (c + fz) ∧ 72 ≤ odw (k + 2 * fz) (c + fz) ∧
    126 ≤ oxw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [odw, oxw]; rw [hdw, hox]; omega

lemma arith_boost_cz {c fz cz_lo ox_lo : Nat}
    (_hc : 2 ≤ c) (_hfz : 40 ≤ fz) (_hcz : cz_lo ≤ c + fz)
    (_h : (cz_lo = 109 ∧ ox_lo = 99) ∨ (cz_lo = 118 ∧ ox_lo = 107) ∨
          (cz_lo = 148 ∧ ox_lo = 134) ∨ (cz_lo = 154 ∧ ox_lo = 140)) :
    ox_lo ≤ ox (1 + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := 1 + 2 * fz) (cz := c + fz) (by omega)
  omega

lemma fbound_k1_boost {N d2 : Nat} {ds2 : List Nat} {segs : List (Nat × Nat)} {zl c1 : Nat}
    (hne1 : (d2 :: ds2) ≠ [1]) (hS1 : SafeStack 19 (d2 :: ds2))
    (hv : ValidSegs40 segs zl) (hc1 : 2 ≤ c1) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, d2 :: ds2⟩ (Exit270 39 38 107 (d2 :: ds2)) := by
  rcases segs with _ | ⟨⟨z1, m1⟩, rest1⟩
  · have hzl230 : 230 ≤ zl := hv.2
    have hg : stepGuards ⟨false, [], zl, c1, 1, 0, d2 :: ds2⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_of_ge35 hS1.1 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c1 + zl - 1 + 1 = c1 + zl := by omega
      rw [hcz]; exact hS1.2.2 (c1 + zl) (by omega)
    apply chainLeadsUpTo_step1 hg
    dsimp only [stepSegs]
    apply chainLeadsUpTo_here
    refine Or.inr ⟨c1 + zl, 1 + 2 * zl + 2, by omega, by omega, by omega, ?_⟩
    simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := 1 + 2 * zl + 2) (kb := 0)
      (mrg := 2 * (1 + 2 * zl) + 6) (ds := (c1 + zl) :: d2 :: ds2) (by omega)
  · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv
    have hv_r1 : ValidSegs40 rest1 zl := validSegs40_tail hv
    cases m1 with
    | zero =>
      have hg1 : stepGuards ⟨false, (z1, 0) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := rfl
      apply chainLeadsUpTo_step hg1
      intro m_a hm_a
      dsimp only [stepSegs]
      rcases rest1 with _ | ⟨⟨z2, m2⟩, rest2⟩
      · have hzl230 : 230 ≤ zl := hv_r1.2
        exact chainLeadsUpTo_here (Or.inl ⟨c1 + z1 + 3 + zl, by omega, IsBounce.nil (by omega)⟩)
      · have hz2_40 : 40 ≤ z2 := fzOf_ge_40 hv_r1
        have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_r1
        have hfz3_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
        cases m2 with
        | zero =>
          have hg2 : stepGuards ⟨true, (z2, 0) :: rest2, zl, c1 + z1 + 3, 1 + 2 * z1 + 3,
              2 * (c1 + z1) + 8, d2 :: ds2⟩ = true := by
            dsimp only [stepGuards]; exact decide_eq_true (by omega)
          apply chainLeadsUpTo_step hg2
          intro m_b hm_b
          dsimp only [stepSegs]
          have hb := arith_boost_c85 (c := c1 + z1 + 3 + z2 + 1) (k := 1 + 2 * z1 + 3 + 2 * z2 + 3)
            (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz3_40
          exact chainLeadsUpTo_imp
            ((excursion270_bundle m_b).1 19 (d2 :: ds2) rest2 zl
              (c1 + z1 + 3 + z2 + 1) (1 + 2 * z1 + 3 + 2 * z2 + 3) (by decide) hS1
              (validTail40_of_validSegs40 hv_r2) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega))
            (fun _ he => exit270_mono he (by omega) (by omega) (by omega))
        | succ m2' =>
          rcases dec_or ((m2' + 1) % 2 = 1) with hm2_od | hm2_ev
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + m2') with
            | true =>
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, d2 :: ds2⟩ = true := by
                dsimp only [stepGuards]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
                exact hS1.2.2 (c1 + z1 + 3 + z2) (by omega)
              apply chainLeadsUpTo_step hg2
              intro m_b hm_b
              dsimp only [stepSegs]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
              exact (excursion270_bundle m_b).2 19 (d2 :: ds2) rest2 zl
                ((1 + 2 * z1 + 3) + m2' + 2 * z2 + 4) 1 (c1 + z1 + 3 + z2) 39 107
                (by decide) hS1 (Or.inl hne1) hv_r2
                (by omega) (by omega) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c1 + z1 + 3 + z2, by omega,
                IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm2_od]; omega)⟩)
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + (m2' + 1)) with
            | true =>
              have h_mrg := of_decide_eq_true hd_mrg
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, d2 :: ds2⟩ = true := by
                dsimp only [stepGuards]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              apply chainLeadsUpTo_step hg2
              intro m_b hm_b
              dsimp only [stepSegs]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              have hb := arith_boost_c85 (c := c1 + z1 + 3 + z2 + 2)
                (k := (1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz3_40
              exact chainLeadsUpTo_imp
                ((excursion270_bundle m_b).1 19 (d2 :: ds2) rest2 zl
                  (c1 + z1 + 3 + z2 + 2) ((1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                  (by decide) hS1 (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                (fun _ he => exit270_mono he (by omega) (by omega) (by omega))
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c1 + z1 + 3 + z2, by omega,
                IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm2_ev]; omega)⟩)
    | succ m' =>
      have hfz2_40 : 40 ≤ fzOf rest1 zl := fzOf_ge_40 hv_r1
      have hphiw : GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false = true :=
        goodPhiW_of_ge35 hS1.1 (by omega)
      -- Helper for x0 >= 42 pushed onto (d2 :: ds2) with c' >= 85:
      have h_push85 : ∀ m_b x0 k', 42 ≤ x0 → 1 ≤ k' → k' ≤ 2 * (1 + 2 * z1 + 4) + 3 →
          ChainLeadsUpTo m_b ⟨false, rest1, zl, 1 + 2 * z1 + 4, k', 0, x0 :: d2 :: ds2⟩
            (Exit270 39 38 107 (d2 :: ds2)) := by
        intro m_b x0 k' hx0 hk'1 hk'c
        rcases dec_or (67 ≤ x0) with hx67 | hx66
        · exact (excursion270_bundle m_b).2 19 (d2 :: ds2) rest1 zl (1 + 2 * z1 + 4) k' x0 39 107
            (by decide) hS1 (Or.inl hne1) hv_r1 (by omega) hk'1 hk'c (by decide) (by omega)
            (by omega) (by omega) (by omega) (by omega)
        · have hb85 := arith_boost_c85 (c := 1 + 2 * z1 + 4) (k := k') (fz := fzOf rest1 zl)
            (by omega) hk'1 hk'c hfz2_40
          have hSx0 : SafeStack 19 (x0 :: d2 :: ds2) :=
            safeStack_cons_ne1 hne1 hS1 (by omega) (by omega)
          have hfb1 := (excursion270_bundle m_b).1 19 (x0 :: d2 :: ds2) rest1 zl
            (1 + 2 * z1 + 4) k' (by decide) hSx0 (validTail40_of_validSegs40 hv_r1)
            (by omega) hk'1 hk'c (by omega) (by omega) (by omega) (by omega)
          refine chainLeadsUpTo_trans hfb1 ?_
          intro m_c s_mid hm_c hex1
          rcases hex1 with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
          · exact chainLeadsUpTo_here (Or.inr ⟨x0, phi, by omega, by omega, by omega, hb⟩)
          · exact amega_pop_step hb hphi38 (by omega) (by omega)
              (hS1.2.2 (x0 - 1) (by omega)) (fun _ => hS1.2.2 (x0 - 2) (by omega))
              (fun hbig _ _ p1 p2 hvp _ =>
                chainLeadsUpTo_here (Or.inl ⟨x0 - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
              (fun _ _ m_d hm_d p1 p2 hvp _ => by
                have hfp := fzOf_ge_40 hvp
                have hr10 := arith_boost_r10 (c := x0 + 1) (k := y + 2) (fz := fzOf p1 p2)
                  (by omega) (by omega) (by omega) hfp
                exact chainLeadsUpTo_imp
                  ((excursion270_bundle m_d).1 19 (d2 :: ds2) p1 p2 (x0 + 1) (y + 2)
                    (by decide) hS1 (validTail40_of_validSegs40 hvp)
                    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ he => exit270_mono he (by omega) (by omega) (by omega)))
              (fun hy_le _ m_d hm_d p1 p2 hvp _ => by
                have hfp := fzOf_ge_40 hvp
                have hox140 := arith_boost_cz (c := y) (fz := fzOf p1 p2) (cz_lo := 154) (ox_lo := 140)
                  (by omega) hfp (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                exact fbound_force_r9 (x := x0 - 1) (d3 := d2) (ds3 := ds2) (by omega)
                  (hS1.2.2 (x0 - 1) (by omega)) (hS1.2.2 (x0 - 2) (by omega)) hvp
                  (by omega) (by omega) (by omega) (by omega) (by omega)
                  (fun _ phi2 _ hphi2 _ hb2 =>
                    chainLeadsUpTo_here (Or.inr ⟨x0 - 1, phi2, by omega, by omega, by omega, hb2⟩))
                  (fun _ _ _ hb2 => chainLeadsUpTo_here (Or.inl ⟨x0 - 2, by omega, hb2⟩)))
      rcases dec_or (m' + 1 = 1) with hm_eq1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z1, 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
            if 1 = 1 then GoodPsi (c1 + z1) (d2 :: ds2) else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact hS1.2.2 (c1 + z1 + 1) (by omega)
        apply chainLeadsUpTo_step hg
        intro m_b hm_b
        dsimp only [stepSegs]
        change ChainLeadsUpTo m_b (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        exact h_push85 m_b (c1 + z1 + 1) 1 (by omega) (by omega) (by omega)
      · have hpsi_cz : GoodPsi (c1 + z1 - 1) (d2 :: ds2) = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c1 + z1 - 1 + 1 = c1 + z1 := by omega
          rw [hcz_eq]; exact hS1.2.2 (c1 + z1) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z1, m' + 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
              if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) (d2 :: ds2) &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          apply chainLeadsUpTo_step hg
          intro m_b hm_b
          dsimp only [stepSegs]
          change ChainLeadsUpTo m_b (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          exact h_push85 m_b (c1 + z1) (m' + 2) (by omega) (by omega) (by omega)
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 19 ((c1 + z1) :: d2 :: ds2) :=
              safeStack_cons_ne1 hne1 hS1 (by omega) (by omega)
            have hg : stepGuards ⟨false, (z1, m' + 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) (d2 :: ds2) &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then
                    GoodDs ((1 + 2 * z1 + 2) :: (c1 + z1) :: d2 :: ds2) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (1 + 2 * z1 + 2) (by omega)
            apply chainLeadsUpTo_step hg
            intro m_b hm_b
            dsimp only [stepSegs]
            change ChainLeadsUpTo m_b (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            obtain ⟨q10, r10, hr10, hkz10, _⟩ := div10_spec (1 + 2 * z1)
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            have hne1_cz : ((c1 + z1) :: d2 :: ds2) ≠ [1] := by intro h; injection h with h1; omega
            have hl1 := (excursion270_bundle m_b).2 19 ((c1 + z1) :: d2 :: ds2) rest1 zl
              m' 1 (1 + 2 * z1 + 2) (9 * q10 - 2) (1 + 2 * z1 + 35)
              (by decide) hS_cz (Or.inl hne1_cz) hv_r1
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega)
            refine chainLeadsUpTo_trans hl1 ?_
            intro m_c s_mid hm_c hex1
            rcases hex1 with ⟨phi0, hphi0, hb0⟩ | ⟨y0, phi0, hy0, hphi0_38, hyw0, hb0⟩
            · exact chainLeadsUpTo_here (Or.inr ⟨c1 + z1, phi0, by omega, by omega, by omega, hb0⟩)
            · exact amega_pop_step hb0 hphi0_38 (by omega) (by omega)
                (hS1.2.2 (c1 + z1 - 1) (by omega)) (fun _ => hS1.2.2 (c1 + z1 - 2) (by omega))
                (fun hbig _ _ p1 p2 hvp _ =>
                  chainLeadsUpTo_here (Or.inl ⟨c1 + z1 - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
                (fun _ _ m_d hm_d p1 p2 hvp _ => by
                  have hfp := fzOf_ge_40 hvp
                  have hr10 := arith_boost_r10 (c := c1 + z1 + 1) (k := y0 + 2) (fz := fzOf p1 p2)
                    (by omega) (by omega) (by omega) hfp
                  exact chainLeadsUpTo_imp
                    ((excursion270_bundle m_d).1 19 (d2 :: ds2) p1 p2 (c1 + z1 + 1) (y0 + 2)
                      (by decide) hS1 (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                    (fun _ he => exit270_mono he (by omega) (by omega) (by omega)))
                (fun hy0_le _ m_d hm_d p1 p2 hvp hfzp => by
                  have hfp := fzOf_ge_40 hvp
                  rcases dec_or (62 ≤ c1 + z1 - 1) with hx62 | hx61
                  · exact (excursion270_bundle m_d).2 19 (d2 :: ds2) p1 p2 y0 1 (c1 + z1 - 1) 39 107
                      (by decide) hS1 (Or.inl hne1) hvp (by omega) (by omega) (by omega)
                      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                  · obtain ⟨x0, hx0⟩ : ∃ x0, c1 + z1 - 1 = x0 + 2 := ⟨c1 + z1 - 3, by omega⟩
                    rw [hx0] at hx61 ⊢
                    have hx0_lo : 39 ≤ x0 := by omega
                    have hx0_hi : x0 ≤ 59 := by omega
                    have hox107 := arith_boost_cz (c := y0) (fz := fzOf p1 p2)
                      (cz_lo := 118) (ox_lo := 107) (by omega) hfp (by omega)
                      (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    have hSx' : SafeStack 19 ((x0 + 2) :: d2 :: ds2) :=
                      safeStack_cons_ne1 hne1 hS1 (by omega) (by omega)
                    have hfb2 := (excursion270_bundle m_d).1 19 ((x0 + 2) :: d2 :: ds2)
                      p1 p2 y0 1 (by decide) hSx' (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    refine chainLeadsUpTo_trans hfb2 ?_
                    intro m_e s_m2 hm_e hex2
                    rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2_ox, hphi2_38, _, hb2⟩
                    · have hphi2_106 : 106 ≤ phi2 := by dsimp only [odw] at hphi2; omega
                      exact chainLeadsUpTo_here (Or.inr ⟨x0 + 2, phi2, by omega, by omega, by omega, hb2⟩)
                    · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
                        (hS1.2.2 (x0 + 1) (by omega)) (fun _ => hS1.2.2 x0 (by omega))
                        (fun hbig _ _ q1 q2 hvq _ =>
                          chainLeadsUpTo_here (Or.inl ⟨x0 + 1, by omega, isBounce_r9 (by omega) hbig hvq⟩))
                        (fun _ _ m_f hm_f q1 q2 hvq _ => by
                          have hfq := fzOf_ge_40 hvq
                          have hr10 := arith_boost_r10 (c := x0 + 3) (k := y2 + 2) (fz := fzOf q1 q2)
                            (by omega) (by omega) (by omega) hfq
                          exact chainLeadsUpTo_imp
                            ((excursion270_bundle m_f).1 19 (d2 :: ds2) q1 q2 (x0 + 3) (y2 + 2)
                              (by decide) hS1 (validTail40_of_validSegs40 hvq)
                              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                            (fun _ he => exit270_mono he (by omega) (by omega) (by omega)))
                        (fun hy2_le _ m_f hm_f q1 q2 hvq _ => by
                          have hfq := fzOf_ge_40 hvq
                          have hox134 := arith_boost_cz (c := y2) (fz := fzOf q1 q2)
                            (cz_lo := 148) (ox_lo := 134) (by omega) hfq (by omega)
                            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                          exact fbound_force_r9 (x := x0 + 1) (d3 := d2) (ds3 := ds2) (by omega)
                            (hS1.2.2 (x0 + 1) (by omega)) (hS1.2.2 x0 (by omega)) hvq
                            (by omega) (by omega) (by omega) (by omega) (by omega)
                            (fun _ phi3 _ hphi3 _ hb3 =>
                              chainLeadsUpTo_here (Or.inr ⟨x0 + 1, phi3, by omega, by omega, by omega, hb3⟩))
                            (fun _ _ _ hb3 => chainLeadsUpTo_here (Or.inl ⟨x0, by omega, hb3⟩))))
          · have hm1_big : 2 * (1 + 2 * z1) + 12 ≤ m' + 1 := by omega
            have hg : stepGuards ⟨false, (z1, m' + 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) (d2 :: ds2) &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            apply chainLeadsUpTo_step1 hg
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            apply chainLeadsUpTo_here
            refine Or.inr ⟨c1 + z1, 1 + 2 * z1 + 2, by omega, by omega, by omega, ?_⟩
            have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
              (cp1 := 1 + 2 * z1 + 2) (kb := 0) (mrg := 2 * (1 + 2 * z1) + 6)
              (rest := rest1) (ds := (c1 + z1) :: d2 :: ds2) hv_r1 (by omega) (by
                rcases dec_or (((m' - 4) + 1) % 2 = 1) with h | h
                · rw [if_pos h]; omega
                · rw [if_neg h]; omega)
            simpa only [Nat.add_zero] using hbc

lemma loop_k1_le47 {N x1 d3 : Nat} {ds3 : List Nat} {segs : List (Nat × Nat)} {zl c1 : Nat}
    {P : SegState → Prop}
    (hne1_0 : (d3 :: ds3) ≠ [1])
    (hS0 : SafeStack 21 (d3 :: ds3))
    (hx_lo : 23 ≤ x1 ∨ (x1 = 21 ∧ SafeStack 19 (d3 :: ds3)))
    (hx_hi : x1 ≤ 47)
    (hv : ValidSegs40 segs zl) (hc1 : 2 ≤ c1)
    (h_top : ∀ m z phi, m ≤ N → (z = x1 ∨ z = x1 - 1) → 38 ≤ phi → ∀ s',
      IsBounce phi (z :: d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b1 : ∀ m, m < N → ∀ s', IsBounce (x1 - 1) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b2 : ∀ m, m < N → ∀ s', IsBounce (x1 - 2) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_r10 : ∀ m c' k' p1 p2, m < N → c' = x1 + 1 → 41 ≤ k' → k' ≤ 2 * c' + 3 →
      ValidSegs40 p1 p2 → ChainLeadsUpTo m ⟨false, p1, p2, c', k', 0, d3 :: ds3⟩ P) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, x1 :: d3 :: ds3⟩ P := by
  have hx21 : 21 ≤ x1 := by rcases hx_lo with h | ⟨rfl, _⟩ <;> omega
  have hS1 : SafeStack 19 (x1 :: d3 :: ds3) := by
    rcases hx_lo with h23 | ⟨rfl, h19⟩
    · exact safeStack_cons_ne1 hne1_0 hS0 (by omega) (by omega)
    · exact safeStack_cons_ne1 hne1_0 h19 (by omega) (by omega)
  have hg_x1_1 : GoodDs ((x1 - 1) :: d3 :: ds3) = true := by
    rcases hx_lo with h23 | ⟨rfl, h19⟩
    · exact hS0.2.2 (x1 - 1) (by omega)
    · exact h19.2.2 20 (by decide)
  have hg_x1_2 : GoodDs ((x1 - 2) :: d3 :: ds3) = true := by
    rcases hx_lo with h23 | ⟨rfl, h19⟩
    · exact hS0.2.2 (x1 - 2) (by omega)
    · exact h19.2.2 19 (by decide)
  have hne1_1 : (x1 :: d3 :: ds3) ≠ [1] := by intro h; injection h with _ h2; cases h2
  have hb := fbound_k1_boost hne1_1 hS1 hv hc1 (N := N)
  refine chainLeadsUpTo_trans hb ?_
  intro m1 s_mid hm1 hex
  rcases hex with ⟨phi, hphi38, hsb⟩ | ⟨y1, phi1, hy1_39, hphi1_38, hyw1, hsb⟩
  · exact h_top m1 x1 phi hm1 (Or.inl rfl) hphi38 s_mid hsb
  · exact amega_pop_step hsb hphi1_38 (by omega) (by omega) hg_x1_1 (fun _ => hg_x1_2)
      (fun hbig m2 hm2 p1 p2 hvp _ =>
        h_b1 m2 (Nat.lt_of_lt_of_le hm2 hm1) _ (isBounce_r9 (by omega) hbig hvp))
      (fun _ _ m2 hm2 p1 p2 hvp _ =>
        h_r10 m2 (x1 + 1) (y1 + 2) p1 p2 (Nat.lt_of_lt_of_le hm2 hm1)
          rfl (by omega) (by omega) hvp)
      (fun hy1_le _ m2 hm2 p1 p2 hvp hfzp => by
        have hfp := fzOf_ge_40 hvp
        have hox99 := arith_boost_cz (c := y1) (fz := fzOf p1 p2) (cz_lo := 109) (ox_lo := 99)
          (by omega) hfp (by omega) (Or.inl ⟨rfl, rfl⟩)
        exact fbound_force_r9 (x := x1 - 1) (d3 := d3) (ds3 := ds3) (by omega)
          hg_x1_1 hg_x1_2 hvp (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun m3 phi2 hm3 hphi2 s' hb2 =>
            h_top m3 (x1 - 1) phi2 (Nat.le_trans hm3 (Nat.le_of_lt (Nat.lt_of_lt_of_le hm2 hm1)))
              (Or.inr rfl) (by omega) s' hb2)
          (fun m3 hm3 s' hb2 =>
            h_b2 m3 (Nat.lt_trans hm3 (Nat.lt_of_lt_of_le hm2 hm1)) s' hb2))

-- ============================================================================
-- Odd-cz53 High Excursion Extension (`ExitHighOdd`, `loopOS_odd`, `fhigh_ext`)
-- ============================================================================

def ExitHighExt (S : List Nat) (s : SegState) : Prop :=
  ExitHigh S s ∨ (∃ y phi, 53 ≤ y ∧ y % 2 = 1 ∧ 88 ≤ phi ∧ IsBounce phi (y :: S) s)

lemma arith_los_odd_r11 {c k fz x y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_hx : 89 ≤ x) (_hpot : 2079 ≤ (c + fz) + 21 * x)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y) (_hy_hi : y ≤ 2 * x + 4)
    (_hphi38 : 38 ≤ phi) (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    39 ≤ y ∧ 89 ≤ x - 1 ∧ 2079 ≤ (y + fz3) + 21 * (x - 1) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [oxw] at _hyw
  rw [hdw] at _hyw
  rw [hox] at _hy_lo
  omega

lemma loopOS_odd (N : Nat) :
    ∀ S segs zl c k x cz_out,
      S ≠ [1] → SafeStack 43 S → ValidSegs40 segs zl →
      2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
      53 ≤ cz_out → cz_out % 2 = 1 →
      89 ≤ x → 2079 ≤ (c + fzOf segs zl) + 21 * x →
      ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: cz_out :: S⟩ (ExitHighExt S) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro S segs zl c k x cz_out hne1 hS hv hc hk1 hkc hcz_out hcz_odd hx89 hpot
    have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    have hox39 : 39 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) :=
      (ox_bounds_relaxed (by omega) hk1 hkc (by omega) (by omega) (by omega)).1
    have hS_cz : SafeStack 19 (cz_out :: S) := safeStack_cons_ne1 hne1 hS (by omega) (by omega)
    have hne1_cz : (cz_out :: S) ≠ [1] := by intro h; injection h with h1; omega
    have hS_xcz : SafeStack 19 (x :: cz_out :: S) :=
      safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
    have hfb := (excursion270_bundle N).1 19 (x :: cz_out :: S) segs zl c k (by decide) hS_xcz
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hexit
    rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
    · obtain ⟨q0, r0, hr0, heq0, hox0⟩ :=
        ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
      dsimp only [odw] at hphi_odw
      rw [hox0] at hphi_odw hox39
      have hphi38 : 38 ≤ phi := by omega
      exact amega_pop_step hb hphi38 (by omega) (by omega)
        (hS.2.2 (cz_out - 1) (by omega)) (fun _ => hS.2.2 (cz_out - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          chainLeadsUpTo_here (Or.inl (Or.inl ⟨cz_out - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩)))
        (fun _ _ m2 hm2 p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m2).1 S p1 p2 (cz_out + 1) (x + 2) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he))
        (fun _ _ m2 hm2 p1 p2 hvp hfzp => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m2).2.1 S p1 p2 x 1 (cz_out - 1) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he))
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (hS_cz.2.2 (x - 1) (by omega)) (fun _ => hS_cz.2.2 (x - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          chainLeadsUpTo_here (Or.inr ⟨cz_out, x - 1, hcz_out, hcz_odd, by omega,
            isBounce_r9 (by omega) hbig hvp⟩))
        (fun hy_hi _ m2 hm2 p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          obtain ⟨q0, r0, hr0, heq0, hox0⟩ :=
            ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
          rw [hox0] at hy_ox
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m2).2.1 S p1 p2 (x + 1) (y + 2) cz_out hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he))
        (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
          have hlos := arith_los_odd_r11 hc hk1 hkc hfz40 hx89 hpot hy_ox hy_le hphi38 hyw hfzp
          exact ih m2 (by omega) S p1 p2 y 1 (x - 1) cz_out hne1 hS hvp
            (by omega) (by omega) (by omega) hcz_out hcz_odd hlos.2.1 hlos.2.2)

lemma fhigh_ext {N : Nat} {S : List Nat} {segs : List (Nat × Nat)} {zl c : Nat}
    (hne1 : S ≠ [1]) (hS : SafeStack 43 S) (hv : ValidSegs40 segs zl)
    (hc : 2 ≤ c) (hcz53 : 53 ≤ c + fzOf segs zl)
    (hkz95 : 95 ≤ 1 + 2 * fzOf segs zl)
    (hodd : 1 + 2 * fzOf segs zl < 97 → (c + fzOf segs zl) % 2 = 1) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, 1, 0, S⟩ (ExitHighExt S) := by
  rcases dec_or (97 ≤ 1 + 2 * fzOf segs zl) with h97 | hlt97
  · exact chainLeadsUpTo_imp
      ((fhigh_bundle N).1 S segs zl c 1 hne1 hS hv hc (by decide) (by omega) hcz53 h97)
      (fun _ he => Or.inl he)
  · have hcz_odd : (c + fzOf segs zl) % 2 = 1 := hodd (by omega)
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf] at hlt97; have := hv.2; omega
    · dsimp only [fzOf] at hcz53 hkz95 hlt97 hcz_odd
      have hz0_eq : z0 = 47 := by omega
      subst hz0_eq
      have hv_rest : ValidSegs40 rest zl := validSegs40_tail hv
      cases m0 with
      | zero =>
        have hg1 : stepGuards ⟨false, (47, 0) :: rest, zl, c, 1, 0, S⟩ = true := rfl
        apply chainLeadsUpTo_step hg1
        intro m1 hm1
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact chainLeadsUpTo_here (Or.inl (Or.inl ⟨c + 47 + 3 + zl, by omega, IsBounce.nil (by omega)⟩))
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + 50, 98, 2 * (c + 47) + 8, S⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step hg2
            intro m2 _
            dsimp only [stepSegs]
            exact chainLeadsUpTo_imp
              ((fhigh_bundle m2).1 S rest2 zl (c + 50 + z1 + 1) (98 + 2 * z1 + 3)
                hne1 hS hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ he => Or.inl he)
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + 47) + 8 ≥ 98 + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + 50, 98,
                    2 * (c + 47) + 8, S⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS.2.2 (c + 50 + z1) (by omega)
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_imp
                  ((fhigh_bundle m2).2.1 S rest2 zl (98 + m1' + 2 * z1 + 4) 1 (c + 50 + z1)
                    hne1 hS hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ he => Or.inl he)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact chainLeadsUpTo_here (Or.inl (Or.inl ⟨c + 50 + z1, by omega,
                  IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)⟩))
            · cases hd_mrg : decide (2 * (c + 47) + 8 ≥ 98 + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + 50, 98,
                    2 * (c + 47) + 8, S⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_imp
                  ((fhigh_bundle m2).1 S rest2 zl (c + 50 + z1 + 2) (98 + (m1' + 1) + 2 * z1 + 5)
                    hne1 hS hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ he => Or.inl he)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact chainLeadsUpTo_here (Or.inl (Or.inl ⟨c + 50 + z1, by omega,
                  IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)⟩))
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + 47 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (47, 1) :: rest, zl, c, 1, 0, S⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + 47 - 1) S false && if 1 = 1 then GoodPsi (c + 47) S else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS.2.2 (c + 48) (by omega)
          apply chainLeadsUpTo_step hg
          intro m1 _
          dsimp only [stepSegs]
          change ChainLeadsUpTo m1 (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m1).2.1 S rest zl 99 1 (c + 48)
              hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he)
        · have hpsi_cz : GoodPsi (c + 47 - 1) S = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + 47 - 1 + 1 = c + 47 := by omega
            rw [hcz_eq]; exact hS.2.2 (c + 47) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (47, m' + 1) :: rest, zl, c, 1, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + 47 - 1) S false &&
                if m' + 1 = 1 then _ else GoodPsi (c + 47 - 1) S &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            apply chainLeadsUpTo_step hg
            intro m1 _
            dsimp only [stepSegs]
            change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_imp
              ((fhigh_bundle m1).2.1 S rest zl 99 (m' + 2) (c + 47)
                hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ he => Or.inl he)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201) with hod_sm | hbig_m
            · have hS_cz : SafeStack 19 ((c + 47) :: S) :=
                safeStack_cons_ne1 hne1 hS (by omega) (by omega)
              have hg : stepGuards ⟨false, (47, m' + 1) :: rest, zl, c, 1, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + 47 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + 47 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then
                      GoodDs (97 :: (c + 47) :: S) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 97 (by decide)
              apply chainLeadsUpTo_step hg
              intro m1 _
              dsimp only [stepSegs]
              change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              exact loopOS_odd m1 S rest zl m' 1 97 (c + 47) hne1 hS hv_rest
                (by omega) (by decide) (by omega) hcz53 hcz_odd (by decide) (by omega)
            · have hg : stepGuards ⟨false, (47, m' + 1) :: rest, zl, c, 1, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + 47 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + 47 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              apply chainLeadsUpTo_step1 hg
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              apply chainLeadsUpTo_here
              refine Or.inl (Or.inr ⟨c + 47, 97, by omega, Or.inl ⟨hcz53, by decide⟩, ?_⟩)
              have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := 97) (kb := 0) (mrg := 196)
                (rest := rest) (ds := (c + 47) :: S) hv_rest (by omega) (by
                  rcases dec_or (((m' - 4) + 1) % 2 = 1) with h | h
                  · rw [if_pos h]; omega
                  · rw [if_neg h]; omega)
              simpa only [Nat.add_zero] using hbc

-- ============================================================================
-- Root Invariant (`Root0`, `Root1`, `Root31`, `RootD`, `RootD1`, `RootInv270`)
-- ============================================================================

def Root0A (s : SegState) : Prop :=
  s.ds = [] ∧ s.cp1 = 1 ∧ s.kb = 1 ∧
  ∃ z1 m0 m1 rest,
    s.segs = (8, m0) :: (z1, m1) :: rest ∧
    (m0 = 1 ∨ m0 = 2) ∧ 36 ≤ z1 ∧ ValidSegs40 rest s.zl

def Root0B (s : SegState) : Prop :=
  (s.ds = [] ∨ s.ds = [0]) ∧
  ValidTail40 s.segs s.zl ∧
  1 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  7 ≤ fzOf s.segs s.zl ∧ 8 ≤ s.cp1 + fzOf s.segs s.zl ∧
  (s.cp1 + fzOf s.segs s.zl = 8 → ∃ m0 rest,
    s.segs = (7, m0) :: rest ∧ s.cp1 = 1 ∧ s.kb = 1 ∧ s.ds = [0] ∧ 44 ≤ fzOf rest s.zl) ∧
  (fzOf s.segs s.zl < 39 →
    (s.cp1 = 1 ∧ s.kb = 1) ∨ (s.cp1 = 2 ∧ s.kb = 5 ∧ 20 ≤ fzOf s.segs s.zl)) ∧
  (∀ z0 m0 rest, s.segs = (z0, m0) :: rest → s.cp1 + fzOf s.segs s.zl = 9 →
    3 ≤ m0 → m0 % 2 = 1 →
      53 ≤ (m0 - 1) + fzOf rest s.zl ∧ 95 ≤ 1 + 2 * fzOf rest s.zl ∧
      (1 + 2 * fzOf rest s.zl < 97 → ((m0 - 1) + fzOf rest s.zl) % 2 = 1))

def Root0 (s : SegState) : Prop :=
  Root0A s ∨ Root0B s

def Root1 (s : SegState) : Prop :=
  s.ds = [1] ∧
  ValidTail40 s.segs s.zl ∧
  5 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  20 ≤ fzOf s.segs s.zl ∧ 45 ≤ s.kb + 2 * fzOf s.segs s.zl ∧
  (s.cp1 + fzOf s.segs s.zl = 25 → ∃ m0 rest,
    s.segs = (20, m0) :: rest ∧ s.cp1 = 5 ∧ s.kb = 5 ∧ 6 ≤ m0 ∧
    (m0 % 2 = 1 → 102 ≤ (m0 - 1) + fzOf rest s.zl ∧ 185 ≤ 1 + 2 * fzOf rest s.zl)) ∧
  (26 ≤ s.cp1 + fzOf s.segs s.zl → 47 ≤ s.kb + 2 * fzOf s.segs s.zl)

def Root31A (s : SegState) : Prop :=
  s.ds = [3, 1] ∧ ValidTail40 s.segs s.zl ∧
  s.cp1 = 2 ∧ s.kb = 1 ∧
  (fzOf s.segs s.zl = 18 ∨ fzOf s.segs s.zl = 19 ∨ ∃ rest, s.segs = (20, 0) :: rest)

def Root31B (s : SegState) : Prop :=
  s.ds = [3, 1] ∧
  ValidTail40 s.segs s.zl ∧
  2 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  21 ≤ fzOf s.segs s.zl ∧ 25 ≤ s.cp1 + fzOf s.segs s.zl ∧ 43 ≤ s.kb + 2 * fzOf s.segs s.zl ∧
  (∀ z0 m0 rest, s.segs = (z0, m0) :: rest → (s.cp1 + z0) % 2 = 0 → 3 ≤ m0 → m0 % 2 = 1 →
    (s.cp1 = 4 ∧ s.kb = 1 ∧ z0 = 22) ∨ 47 ≤ s.kb + 2 * z0)

def Root31 (s : SegState) : Prop :=
  Root31A s ∨ Root31B s

def RootD (s : SegState) : Prop :=
  (∃ d, 8 ≤ d ∧ (s.ds = [d] ∨ s.ds = [d, 0])) ∧
  ValidTail40 s.segs s.zl ∧
  1 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  35 ≤ fzOf s.segs s.zl ∧ 42 ≤ s.cp1 + fzOf s.segs s.zl ∧ 73 ≤ s.kb + 2 * fzOf s.segs s.zl

def RootD1 (s : SegState) : Prop :=
  (∃ d, 25 ≤ d ∧ s.ds = [d, 1]) ∧
  ValidTail40 s.segs s.zl ∧
  2 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  40 ≤ fzOf s.segs s.zl ∧ 62 ≤ s.cp1 + fzOf s.segs s.zl ∧ 81 ≤ s.kb + 2 * fzOf s.segs s.zl

def RootInv270 (s : SegState) : Prop :=
  s.b = false ∧ s.mrg = 0 ∧ (Root0 s ∨ Root1 s ∨ Root31 s ∨ RootD s ∨ RootD1 s)

lemma rootInv_of_0A {z1 m0 m1 zl : Nat} {rest : List (Nat × Nat)}
    (hm0 : m0 = 1 ∨ m0 = 2) (hz1 : 36 ≤ z1) (hv : ValidSegs40 rest zl) :
    RootInv270 ⟨false, (8, m0) :: (z1, m1) :: rest, zl, 1, 1, 0, []⟩ :=
  ⟨rfl, rfl, Or.inl (Or.inl ⟨rfl, rfl, rfl, z1, m0, m1, rest, rfl, hm0, hz1, hv⟩)⟩

lemma rootInv_of_0B {segs : List (Nat × Nat)} {zl c k : Nat} {ds : List Nat}
    (hds : ds = [] ∨ ds = [0]) (hvt : ValidTail40 segs zl)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 7 ≤ fzOf segs zl) (hcz : 8 ≤ c + fzOf segs zl)
    (h8 : c + fzOf segs zl = 8 → ∃ m0 rest,
      segs = (7, m0) :: rest ∧ c = 1 ∧ k = 1 ∧ ds = [0] ∧ 44 ≤ fzOf rest zl)
    (h39 : fzOf segs zl < 39 → (c = 1 ∧ k = 1) ∨ (c = 2 ∧ k = 5 ∧ 20 ≤ fzOf segs zl))
    (h9 : ∀ z0 m0 rest, segs = (z0, m0) :: rest → c + fzOf segs zl = 9 →
      3 ≤ m0 → m0 % 2 = 1 →
        53 ≤ (m0 - 1) + fzOf rest zl ∧ 95 ≤ 1 + 2 * fzOf rest zl ∧
        (1 + 2 * fzOf rest zl < 97 → ((m0 - 1) + fzOf rest zl) % 2 = 1)) :
    RootInv270 ⟨false, segs, zl, c, k, 0, ds⟩ :=
  ⟨rfl, rfl, Or.inl (Or.inr ⟨hds, hvt, hc, hk, hkc, hfz, hcz, h8, h39, h9⟩)⟩

lemma rootInv_of_1 {segs : List (Nat × Nat)} {zl c k : Nat}
    (hvt : ValidTail40 segs zl)
    (hc : 5 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 20 ≤ fzOf segs zl) (hkz : 45 ≤ k + 2 * fzOf segs zl)
    (h25 : c + fzOf segs zl = 25 → ∃ m0 rest,
      segs = (20, m0) :: rest ∧ c = 5 ∧ k = 5 ∧ 6 ≤ m0 ∧
      (m0 % 2 = 1 → 102 ≤ (m0 - 1) + fzOf rest zl ∧ 185 ≤ 1 + 2 * fzOf rest zl))
    (h26 : 26 ≤ c + fzOf segs zl → 47 ≤ k + 2 * fzOf segs zl) :
    RootInv270 ⟨false, segs, zl, c, k, 0, [1]⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, hvt, hc, hk, hkc, hfz, hkz, h25, h26⟩)⟩

lemma rootInv_of_31A {segs : List (Nat × Nat)} {zl : Nat}
    (hvt : ValidTail40 segs zl)
    (hfz : fzOf segs zl = 18 ∨ fzOf segs zl = 19 ∨ ∃ rest, segs = (20, 0) :: rest) :
    RootInv270 ⟨false, segs, zl, 2, 1, 0, [3, 1]⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, hvt, rfl, rfl, hfz⟩)))⟩

lemma rootInv_of_31B {segs : List (Nat × Nat)} {zl c k : Nat} {ds : List Nat}
    (hds : ds = [3, 1]) (hvt : ValidTail40 segs zl)
    (hc : 2 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 21 ≤ fzOf segs zl) (hcz : 25 ≤ c + fzOf segs zl) (hkz : 43 ≤ k + 2 * fzOf segs zl)
    (hod : ∀ z0 m0 rest, segs = (z0, m0) :: rest → (c + z0) % 2 = 0 → 3 ≤ m0 → m0 % 2 = 1 →
      (c = 4 ∧ k = 1 ∧ z0 = 22) ∨ 47 ≤ k + 2 * z0) :
    RootInv270 ⟨false, segs, zl, c, k, 0, ds⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inl (Or.inr ⟨hds, hvt, hc, hk, hkc, hfz, hcz, hkz, hod⟩)))⟩

lemma rootInv_of_D {segs : List (Nat × Nat)} {zl c k d : Nat} {ds : List Nat}
    (hd : 8 ≤ d) (hds : ds = [d] ∨ ds = [d, 0]) (hvt : ValidTail40 segs zl)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 35 ≤ fzOf segs zl) (hcz : 42 ≤ c + fzOf segs zl) (hkz : 73 ≤ k + 2 * fzOf segs zl) :
    RootInv270 ⟨false, segs, zl, c, k, 0, ds⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨d, hd, hds⟩, hvt, hc, hk, hkc, hfz, hcz, hkz⟩)))⟩

lemma rootInv_of_D1 {segs : List (Nat × Nat)} {zl c k d : Nat}
    (hd : 25 ≤ d) (hvt : ValidTail40 segs zl)
    (hc : 2 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 40 ≤ fzOf segs zl) (hcz : 62 ≤ c + fzOf segs zl) (hkz : 81 ≤ k + 2 * fzOf segs zl) :
    RootInv270 ⟨false, segs, zl, c, k, 0, [d, 1]⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨d, hd, rfl⟩, hvt, hc, hk, hkc, hfz, hcz, hkz⟩)))⟩

-- ============================================================================
-- Drain-Pop Closure Lemmas (`IsBounce phi ds s -> ChainLeadsUpTo N s RootInv270`)
-- ============================================================================

lemma bounce_nil_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [] s) (hphi : 9 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [] = true := by
    change decide (phi ≥ 2) = true
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step1 hg_s
  rw [hstep]
  set p := pushSeg hp (phi + 1) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [] = ⟨false, p.1, p.2, 1, 1, 0, []⟩ := rfl
  rw [hdp]
  have hvt : ValidTail40 p.1 p.2 :=
    validTail40_pushSeg hp hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 1 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 1) m_rem rest zl
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvt (by decide) (by decide) (by decide)
    (by omega) (by omega) (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩)
    (by intro _ _ _ _ hcz9; omega))

lemma bounce_zero_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [0] s) (hphi : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [0] = true := by
    change decide (phi ≥ 2) = true
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [0] = ⟨true, p.1, p.2, 2, 2, 6, []⟩ := rfl
  rw [hdp]
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  rcases h_p1 : p.1 with _ | ⟨⟨z1, m1_seg⟩, r2⟩
  · have hzl230 : 230 ≤ p.2 := by rw [h_p1] at hvp; exact hvp.2
    exact bounce_nil_leads (IsBounce.nil (by omega)) (by omega)
  · rw [h_p1] at hvp
    have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hvp
    have hv_r2 : ValidSegs40 r2 p.2 := validSegs40_tail hvp
    have hfz2_40 : 40 ≤ fzOf r2 p.2 := fzOf_ge_40 hv_r2
    cases m1_seg with
    | zero =>
      have hg2 : stepGuards ⟨true, (z1, 0) :: r2, p.2, 2, 2, 6, []⟩ = true := rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r2)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    | succ m1' =>
      rcases dec_or ((m1' + 1) % 2 = 1) with hod | hev
      · cases hd_mrg : decide (6 ≥ 2 + m1') with
        | true =>
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, p.2, 2, 2, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_pos rfl]
            exact safeStack_nil.2.2 (2 + z1) (by omega)
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := 2 + z1) (by omega) (Or.inl rfl)
            (validTail40_of_validSegs40 hv_r2) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hod]; omega)) (by omega)
      · cases hd_mrg : decide (6 ≥ 2 + (m1' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, p.2, 2, 2, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hev]; omega)) (by omega)

lemma bounce_one_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [1] s) (hphi : 24 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [1] = true := by
    change decide (phi ≥ 2) = true
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hdp : drainPopStep hp phi m_rem rest zl [1] =
      ⟨true, (pushSeg hp (phi + 3) m_rem rest zl).1, (pushSeg hp (phi + 3) m_rem rest zl).2,
        2, 0, 6, []⟩ := rfl
  rw [hdp]
  cases hp with
  | false =>
    have hzl230 : 230 ≤ phi := hzl_false rfl
    change ChainLeadsUpTo m1 ⟨true, [], phi + 3, 2, 0, 6, []⟩ RootInv270
    exact bounce_nil_leads (IsBounce.nil (by omega)) (by omega)
  | true =>
    have hv_r : ValidSegs40 rest zl := hv_rest rfl
    have hfz_r : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_r
    dsimp only [pushSeg, ite_true]
    cases m_rem with
    | zero =>
      dsimp only [normSeg, ite_true]
      have hg2 : stepGuards ⟨true, (phi + 3 + 1, 0) :: rest, zl, 2, 0, 6, []⟩ = true := rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    | succ mr' =>
      have hnorm : normSeg (phi + 3) (mr' + 1) = (phi + 3, mr' + 1) := rfl
      rw [hnorm]
      rcases dec_or ((mr' + 1) % 2 = 1) with hod | hev
      · cases hd_mrg : decide (6 ≥ 0 + mr') with
        | true =>
          have hg2 : stepGuards ⟨true, (phi + 3, mr' + 1) :: rest, zl, 2, 0, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_pos rfl]
            exact safeStack_nil.2.2 (2 + (phi + 3)) (by omega)
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := 2 + (phi + 3)) (by omega) (Or.inl rfl)
            (validTail40_of_validSegs40 hv_r) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r (by omega) (by rw [if_pos hod]; omega)) (by omega)
      · cases hd_mrg : decide (6 ≥ 0 + (mr' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (phi + 3, mr' + 1) :: rest, zl, 2, 0, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r (by omega) (by rw [if_neg hev]; omega)) (by omega)

lemma bounce_31_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [3, 1] s) (hphi : 18 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [3, 1] = true := by
    change (true && true && true && decide (phi ≥ 16)) = true
    rw [Bool.true_and, Bool.true_and, Bool.true_and]
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [3, 1] = ⟨true, (1, 0) :: p.1, p.2, 0, 0, 2, []⟩ := rfl
  rw [hdp]
  have hvt : ValidTail40 p.1 p.2 :=
    validTail40_pushSeg hp hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  have hg2 : stepGuards ⟨true, (1, 0) :: p.1, p.2, 0, 0, 2, []⟩ = true := rfl
  apply chainLeadsUpTo_step1 hg2
  dsimp only [stepSegs]
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvt
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (fun _ => Or.inr ⟨rfl, rfl, by omega⟩)
    (by intro _ _ _ _ hcz9; omega))

lemma bounce_cz_31_leads {N cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [cz, 3, 1] s)
    (hcases : ((cz = 20 ∨ cz = 21) ∧ 34 ≤ phi) ∨
              (22 ≤ cz ∧ cz % 2 = 1 ∧ 38 ≤ phi) ∨
              (26 ≤ cz ∧ cz % 2 = 0 ∧ (46 ≤ phi ∨ (cz = 26 ∧ phi = 45)))) :
    ChainLeadsUpTo N s RootInv270 := by
  have hcz20 : 20 ≤ cz := by rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hphi34 : 34 ≤ phi := by
    rcases hcases with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h | ⟨_, rfl⟩⟩ <;> omega
  have hnrst : isDrainRstDs [cz, 3, 1] = false := rfl
  have hnr0 : isRank0 [cz, 3, 1] = false := by
    rcases cz with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop' : drainPopGuards phi [cz, 3, 1] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (cz ≥ 3 ∧ 3 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (cz % 2 = 0 ∧ cz ≤ 2 * 3 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (cz % 2 = 0 ∧ cz + 14 ≤ 2 * 3) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop'
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [cz, 3, 1] =
      ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h31, _, _⟩; cases h31)]
    have hnorm : normSeg 0 (cz - 3) = (0, cz - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  -- Step 1: <true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]> bounces on [1] with phi' = 2, m_rem' = cz - 11
  have hg_b1 : stepGuards ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ = true := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b1 : stepSegs ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ =
      ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    have hm_eq : 0 + ((cz - 4) + 1) - (6 + 2) = (cz - 12) + 1 := by omega
    have h11 : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub, h11]; dsimp only [stepSegs]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step hg_b1
  intro m2 _
  rw [hs_b1]
  -- Step 2: <true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []> bounces on [] with phi'' = 7, m_rem'' = cz - 19
  have hg_b2 : stepGuards ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b2 : stepSegs ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ =
      ⟨false, (8, cz - 19) :: p.1, p.2, 1, 1, 0, []⟩ := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    have hm_eq : 0 + ((cz - 12) + 1) - (6 + 2) = (cz - 20) + 1 := by omega
    have h19 : cz - 19 = (cz - 20) + 1 := by omega
    rw [hsub, h19]; dsimp only [stepSegs]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step1 hg_b2
  rw [hs_b2]
  apply chainLeadsUpTo_here
  rcases hcases with ⟨hcz2021, _⟩ | ⟨hcz22, hcz_od, hphi38⟩ | ⟨hcz26, hcz_ev, hphi_ev⟩
  · -- Root0A (`cz = 20` or `cz = 21`, `34 <= phi => 36 <= fzOf p.1 p.2`):
    cases hp with
    | false =>
      have := hzl_false rfl
      have hvp : ValidSegs40 p.1 p.2 :=
        validSegs40_pushSeg false (by omega) hv_rest (fun _ => by omega)
      exact rootInv_of_0B (Or.inl rfl) hvp
        (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
        (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩)
        (by intro z0 m0 r hseg _; injection hseg with hhd _; injection hhd with _ hm0; omega)
    | true =>
      have hvr := hv_rest rfl
      dsimp only [p, pushSeg, ite_true] at hfzp ⊢
      exact rootInv_of_0A (by omega) (Nat.le_trans (by omega) (normSeg_fst_ge (phi + 2) m_rem)) hvr
  · -- `cz >= 22` odd => `cz - 19` is EVEN (`m0 % 2 = 1` vacuous!):
    have hvp : ValidSegs40 p.1 p.2 :=
      validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
    exact rootInv_of_0B (Or.inl rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
      (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩)
      (by intro z0 m0 r hseg _ _ hm0_od; injection hseg with hhd _; injection hhd with _ hm0; omega)
  · -- `cz >= 26` even => `cz - 19 >= 7` odd:
    have hphi45 : 45 ≤ phi := by rcases hphi_ev with h | ⟨_, rfl⟩ <;> omega
    have hvp : ValidSegs40 p.1 p.2 :=
      validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
    refine rootInv_of_0B (Or.inl rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
      (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
    intro z0 m0 r hseg _ _ _
    injection hseg with hhd htl
    injection hhd with hz0 hm0
    subst hz0 hm0 htl
    rcases hphi_ev with hphi46 | ⟨rfl, rfl⟩
    · exact ⟨by omega, by omega, fun hlt => False.elim (by omega)⟩
    · exact ⟨by omega, by omega, fun _ => by omega⟩

lemma bounce_d1_leads {N d phi : Nat} {s : SegState}
    (hb : IsBounce phi [d, 1] s) (hd25 : 25 ≤ d) (hphi42 : 42 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hnrst : isDrainRstDs [d, 1] = false := rfl
  have hnr0 : isRank0 [d, 1] = false := by
    rcases d with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [d, 1] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (d ≥ 3 ∧ 1 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (d % 2 = 0 ∧ d ≤ 2 * 1 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (d % 2 = 0 ∧ d + 14 ≤ 2 * 1) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [d, 1] =
      ⟨true, normSeg 0 (d - 11) :: p.1, p.2, 5, 0, 12, [2]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos ⟨rfl, rfl, hd25⟩]
  rw [hdp]
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  have hnorm0 : normSeg 0 (d - 11) = (0, (d - 12) + 1) := by
    dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
  rw [hnorm0]
  -- <true, (0, d - 11) :: p.1, p.2, 5, 0, 12, [2]> bounces on [2] with phi' = 5, m_rem' = d - 25
  have hg2 : stepGuards ⟨true, (0, (d - 12) + 1) :: p.1, p.2, 5, 0, 12, [2]⟩ = true := by
    dsimp only [stepGuards]
    rcases dec_or (((d - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs2 : stepSegs ⟨true, (0, (d - 12) + 1) :: p.1, p.2, 5, 0, 12, [2]⟩ =
      ⟨false, normSeg 7 (d - 25) :: p.1, p.2, 1, 1, 0, [0]⟩ := by
    have hm_eq : 0 + ((d - 12) + 1) - (12 + 2) = d - 25 := by omega
    dsimp only [stepSegs]
    rcases dec_or (((d - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  apply chainLeadsUpTo_here
  rcases dec_or (d = 25) with rfl | hd26
  · have hnorm8 : normSeg 7 (25 - 25) = (8, 0) := rfl
    rw [hnorm8]
    exact rootInv_of_0B (Or.inr rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
      (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩)
      (by intro z0 m0 r hseg _ h3; injection hseg with hhd _; injection hhd with _ hm0; omega)
  · have hnorm7 : normSeg 7 (d - 25) = (7, d - 25) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm7]
    exact rootInv_of_0B (Or.inr rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
      (fun _ => ⟨d - 25, p.1, rfl, rfl, rfl, rfl, by omega⟩)
      (fun _ => Or.inl ⟨rfl, rfl⟩)
      (by intro _ _ _ _ hcz9; cases hcz9)

lemma bounce_d_leads {N d phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi ds s)
    (hds : ds = [d] ∨ ds = [d, 0])
    (hcases : (d = 8 ∧ (phi = 16 ∨ phi = 17 ∨ 38 ≤ phi)) ∨
              (d = 9 ∧ 19 ≤ phi) ∨
              (10 ≤ d ∧ d ≤ 18 ∧ 19 ≤ phi ∧ (12 ≤ d → d % 2 = 0 → 23 ≤ phi)) ∨
              (d = 19 ∧ 37 ≤ phi) ∨
              (20 ≤ d ∧ 38 ≤ phi)) :
    ChainLeadsUpTo N s RootInv270 := by
  have hd8 : 8 ≤ d := by
    rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨h, _⟩ | ⟨rfl, _⟩ | ⟨h, _⟩ <;> omega
  have hrst : isDrainRstDs ds = true := by
    rcases hds with rfl | rfl <;> (dsimp only [isDrainRstDs]; exact decide_eq_true hd8)
  have hhd_ds : headNat ds = d := by rcases hds with rfl | rfl <;> rfl
  have hg_pop : drainPopGuards phi ds = true := by
    dsimp only [drainPopGuards]; rw [hrst, if_pos rfl]
    apply decide_eq_true
    rcases hcases with ⟨rfl, h16⟩ | ⟨_, h19⟩ | ⟨_, _, h19, _⟩ | ⟨_, h19⟩ | ⟨_, h19⟩
    · rcases hds with rfl | rfl <;> (change 16 ≤ phi; omega)
    all_goals (cases isOddDrainDs ds <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  dsimp only [drainPopStep]
  rw [hrst, if_pos rfl, hhd_ds]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hvt : ValidTail40 p.1 p.2 :=
    validTail40_pushSeg hp hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  rcases hcases with ⟨rfl, hphi_d8⟩ | ⟨rfl, hphi19⟩ | ⟨hd10, hd18, hphi19, hd_ev23⟩ |
      ⟨rfl, hphi37⟩ | ⟨hd20, hphi38⟩
  · -- d = 8 (`d - 7 = 1` -> `[3, 1]` with `c = 2, k = 1`):
    rw [if_pos rfl]
    apply chainLeadsUpTo_here
    rcases hphi_d8 with rfl | rfl | hphi38
    · refine rootInv_of_31A hvt ?_
      cases hp with
      | false => have := hzl_false rfl; omega
      | true =>
        cases m_rem with
        | zero => exact Or.inr (Or.inl rfl)
        | succ _ => exact Or.inl rfl
    · refine rootInv_of_31A hvt ?_
      cases hp with
      | false => have := hzl_false rfl; omega
      | true =>
        cases m_rem with
        | zero => exact Or.inr (Or.inr ⟨rest, rfl⟩)
        | succ _ => exact Or.inr (Or.inl rfl)
    · refine rootInv_of_31B rfl hvt (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega) ?_
      intro z0 m0 r hseg _ _ _
      have hz0 : fzOf p.1 p.2 = z0 := by rw [hseg]; rfl
      exact Or.inr (by omega)
  · -- d = 9 (`9 - 7 = 2`, `normSeg 0 0 = (1, 0)` on `[1]`, steps to `c = 5, k = 5, fz >= 21`):
    rw [if_neg (by decide)]
    dsimp only [Nat.reduceSub, normSeg, ite_true]
    have hg2 : stepGuards ⟨true, (1, 0) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := rfl
    apply chainLeadsUpTo_step1 hg2
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_1 hvt
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (by intro h; omega) (fun _ => by omega))
  · -- 10 <= d <= 18 (`1 <= d - 9 <= 9`):
    rw [if_neg (by omega)]
    have hnorm : normSeg 0 (d - 7 - 2) = (0, (d - 10) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
    rcases dec_or (((d - 10) + 1) % 2 = 1) with hod | hev
    · -- d even in {10, 12, 14, 16, 18} -> `[3, 1]` with `c = d - 6, k = 1`:
      have hmrg : decide (8 ≥ 0 + (d - 10)) = true := decide_eq_true (by omega)
      have hg2 : stepGuards ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := by
        dsimp only [stepGuards]; rw [if_pos hod, hmrg, if_pos rfl]; rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]; rw [if_pos hod, hmrg, if_pos rfl]
      apply chainLeadsUpTo_here
      refine rootInv_of_31B rfl hvt (by omega) (by decide) (by omega)
        (by omega) (by omega) (by omega) ?_
      intro z0 m0 r hseg hpar _ _
      have hz0 : fzOf p.1 p.2 = z0 := by rw [hseg]; rfl
      rcases dec_or (d = 10) with rfl | hd12
      · omega
      · have h23 := hd_ev23 (by omega) (by omega)
        exact Or.inr (by omega)
    · -- d odd in {11, 13, 15, 17} -> `[1]` with `c = 5, k = d - 4 >= 7, fz >= 21`:
      have hmrg : decide (8 ≥ 0 + ((d - 10) + 1)) = true := decide_eq_true (by omega)
      have hg2 : stepGuards ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := by
        dsimp only [stepGuards]; rw [if_neg hev, hmrg, if_pos rfl]
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]; rw [if_neg hev, hmrg, if_pos rfl]
      exact chainLeadsUpTo_here (rootInv_of_1 hvt
        (by decide) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (fun _ => by omega))
  · -- d = 19 (`19 - 9 = 10`, bounces on `[1]` with `m_rem' = 0` -> `(7, 0) :: p.1` -> `c = 10, k = 17, fz >= 39`):
    rw [if_neg (by decide)]
    have hnorm : normSeg 0 (19 - 7 - 2) = (0, 10) := rfl
    rw [hnorm]
    have hg2 : stepGuards ⟨true, (0, 10) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := rfl
    have hs2 : stepSegs ⟨true, (0, 10) :: p.1, p.2, 3, 0, 8, [1]⟩ =
        ⟨true, (7, 0) :: p.1, p.2, 2, 0, 6, []⟩ := rfl
    apply chainLeadsUpTo_step hg2
    intro m2 _
    rw [hs2]
    have hg3 : stepGuards ⟨true, (7, 0) :: p.1, p.2, 2, 0, 6, []⟩ = true := rfl
    apply chainLeadsUpTo_step1 hg3
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvt
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
  · -- d >= 20 (`38 <= phi` => `ValidSegs40 p.1 p.2`, bounces on `[1]` with `m_rem' = d - 19 >= 1`):
    rw [if_neg (by omega)]
    have hvp : ValidSegs40 p.1 p.2 :=
      validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
    have hfzp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
    have hnorm : normSeg 0 (d - 7 - 2) = (0, (d - 10) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
    have hg2 : stepGuards ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := by
      dsimp only [stepGuards]
      rcases dec_or (((d - 10) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega)]; rfl
      · rw [if_neg hev, decide_eq_false (by omega)]; rfl
    have hs2 : stepSegs ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ =
        ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ := by
      have hm_eq : 0 + ((d - 10) + 1) - (8 + 2) = (d - 20) + 1 := by omega
      dsimp only [stepSegs]
      rcases dec_or (((d - 10) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
      · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
    apply chainLeadsUpTo_step hg2
    intro m2 _
    rw [hs2]
    rcases dec_or (((d - 20) + 1) % 2 = 1) with hod2 | hev2
    · cases hd_mrg2 : decide (6 ≥ 0 + (d - 20)) with
      | true =>
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod2, hd_mrg2, if_pos rfl]; rfl
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_pos hod2, hd_mrg2, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
          (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
          (by omega) (by omega) (by omega))
      | false =>
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod2, hd_mrg2, if_neg Bool.false_ne_true]; rfl
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_pos hod2, hd_mrg2, if_neg Bool.false_ne_true]
        set q := pushSeg true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        have hdp3 : drainPopStep true (2 + 6) (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp3]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 9 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · cases hd_mrg2 : decide (6 ≥ 0 + ((d - 20) + 1)) with
      | true =>
        have h_mrg2 := of_decide_eq_true hd_mrg2
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev2, hd_mrg2, if_pos rfl]
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_neg hev2, hd_mrg2, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hvp)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
      | false =>
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev2, hd_mrg2, if_neg Bool.false_ne_true]; rfl
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_neg hev2, hd_mrg2, if_neg Bool.false_ne_true]
        set q := pushSeg true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        have hdp3 : drainPopStep true (2 + 6) (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp3]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 9 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))


-- ============================================================================
-- Section 5g.3c: RootD, RootD1, and Root1 Advancement Closures
-- ============================================================================

lemma chainAdvances_trans {s : SegState} {P Q : SegState → Prop}
    (h1 : ChainAdvances s P) (h2 : ∀ s', P s' → ChainLeads s' Q) :
    ChainAdvances s Q :=
  ⟨h1.1, chainLeads_trans h1.2 h2⟩

lemma fbound_advances {ms : Nat} {S : List Nat} {segs : List (Nat × Nat)} {zl c k : Nat}
    (hms19 : 19 ≤ ms) (hS : SafeStack ms S)
    (hvt : ValidTail40 segs zl)
    (hc : 1 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz35 : 35 ≤ fzOf segs zl) (hcz42 : 42 ≤ c + fzOf segs zl)
    (hkz73 : 73 ≤ k + 2 * fzOf segs zl)
    (hms_ox : ms + 2 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl)) :
    ChainAdvances ⟨false, segs, zl, c, k, 0, S⟩
      (Exit270 (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) S) := by
  obtain ⟨hox39, hox_cz3⟩ := ox_bounds_relaxed hc hk1 hkc hfz35 hcz42 hkz73
  rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
  · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
    have hg : stepGuards ⟨false, [], zl, c, k, 0, S⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_of_ge35 hS.1 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c + zl - 1 + 1 = c + zl := by omega
      rw [hcz]; exact hS.2.2 (c + zl) (by omega)
    refine ⟨hg, fun N => ?_⟩
    dsimp only [stepSegs]
    apply chainLeadsUpTo_here
    obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * zl)
    refine Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, by omega, ?_, ?_⟩
    · dsimp only [oxw]; rw [hdw]; omega
    · simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
        (mrg := 2 * (k + 2 * zl) + 6) (ds := (c + zl) :: S) (by omega)
  · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
    have hv_rest : ValidSegs40 rest zl := hvt
    cases m0 with
    | zero =>
      refine ⟨rfl, fun N => ?_⟩
      dsimp only [stepSegs]
      rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
      · have hzl230 : 230 ≤ zl := hv_rest.2
        exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + zl, by dsimp only [odw]; omega,
          IsBounce.nil (by omega)⟩)
      · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
        have hv_rest2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
        have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_rest2
        cases m1_seg with
        | zero =>
          have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, S⟩ = true := by
            dsimp only [stepGuards]; exact decide_eq_true (by omega)
          apply chainLeadsUpTo_step hg2
          intro m2 _
          dsimp only [stepSegs]
          have hmono := arith_fb_t0 hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
          exact chainLeadsUpTo_imp
            ((excursion270_bundle m2).1 ms S rest2 zl (c + z0 + 3 + z1 + 1)
              (k + 2 * z0 + 3 + 2 * z1 + 3) hms19 hS (validTail40_of_validSegs40 hv_rest2)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (Nat.le_trans hms_ox hmono.1))
            (fun _ he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2)
        | succ m1' =>
          rcases dec_or ((m1' + 1) % 2 = 1) with hm1_odd | hm1_even
          · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
            | true =>
              have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                  k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                exact hS.2.2 (c + z0 + 3 + z1) (by omega)
              apply chainLeadsUpTo_step hg2
              intro m2 _
              dsimp only [stepSegs]; rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
              have hi := arith_fb_to (m1' := m1') hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
              exact (excursion270_bundle m2).2 ms S rest2 zl
                ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1 (c + z0 + 3 + z1)
                (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                hms19 hS (Or.inr (by omega)) hv_rest2
                (by omega) (by omega) (by omega) hms_ox hi.1
                hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                IsBounce.cons hv_rest2 (by omega) (by rw [if_pos hm1_odd]; omega)⟩)
          · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
            | true =>
              have h_mrg := of_decide_eq_true hd_mrg
              have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                  k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; rw [if_neg hm1_even, hd_mrg, if_pos rfl]
              apply chainLeadsUpTo_step hg2
              intro m2 _
              dsimp only [stepSegs]; rw [if_neg hm1_even, hd_mrg, if_pos rfl]
              have hmono := arith_fb_te hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40 h_mrg
              exact chainLeadsUpTo_imp
                ((excursion270_bundle m2).1 ms S rest2 zl (c + z0 + 3 + z1 + 2)
                  ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                  hms19 hS (validTail40_of_validSegs40 hv_rest2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  (Nat.le_trans hms_ox hmono.1))
                (fun _ he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                IsBounce.cons hv_rest2 (by omega) (by rw [if_neg hm1_even]; omega)⟩)
    | succ m' =>
      have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
      have hphiw : GoodPhiW (c + z0 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
      rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, S⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c + z0 - 1) S false && if 1 = 1 then GoodPsi (c + z0) S else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact hS.2.2 (c + z0 + 1) (by omega)
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        have hi := arith_fb_m1_ev (dx := 1) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
        exact (excursion270_bundle N).2 ms S rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1)
          (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
          hms19 hS (Or.inr (by omega)) hv_rest
          (by omega) (by omega) (by omega) hms_ox hi.1
          hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
      · have hpsi_cz : GoodPsi (c + z0 - 1) S = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
          rw [hcz_eq]; exact hS.2.2 (c + z0) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) S false &&
              if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          have hi := arith_fb_m1_ev (dx := 0) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
          have hcz0 : c + z0 + 0 = c + z0 := by omega
          rw [hcz0] at hi
          exact (excursion270_bundle N).2 ms S rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0)
            (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
            hms19 hS (Or.inr (by omega)) hv_rest
            (by omega) (by omega) (by omega) hms_ox hi.1
            hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 39 ((c + z0) :: S) := safeStack_cons hS (by omega) (by omega)
            have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                    GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: S) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            obtain ⟨q10, r10, hr10, hkz10, hdw10⟩ := div10_spec (k + 2 * z0)
            have hos_in : 39 + 2 ≤ 9 * q10 - 2 ∧ 9 * q10 - 2 ≤ k + 2 * z0 + 2 ∧
                30 * (9 * q10 - 2) ≤ (m' + fzOf rest zl) + 27 * (k + 2 * z0 + 2) + 900 ∧
                60 * (9 * q10 - 2) + 120 ≤ 2 * (m' + fzOf rest zl) + 55 * (k + 2 * z0 + 2) ∧
                10 * (k + 2 * z0 + 35) + 40 ≤ 9 * (m' + fzOf rest zl) + 10 * (k + 2 * z0 + 2) ∧
                20 * (k + 2 * z0 + 35) ≤ (m' + fzOf rest zl) + 20 * (k + 2 * z0 + 2) + 800 := by omega
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            have hne1_cz : ((c + z0) :: S) ≠ [1] := by intro h; injection h with h1; omega
            have h_loop1 := (excursion270_bundle N).2 39 ((c + z0) :: S) rest zl m' 1
              (k + 2 * z0 + 2) (9 * q10 - 2) (k + 2 * z0 + 35)
              (by decide) hS_cz (Or.inl hne1_cz) hv_rest
              (by omega) (by omega) (by omega) hos_in.1 hos_in.2.1
              hos_in.2.2.1 hos_in.2.2.2.1 hos_in.2.2.2.2.1 hos_in.2.2.2.2.2
            refine chainLeadsUpTo_trans h_loop1 ?_
            intro m2 s_mid hm2 hexit1
            rcases hexit1 with ⟨phi1, hphi1, hb1⟩ | ⟨y1, phi1, hy1_tx1, hphi1_38, hyw1, hb1⟩
            · apply chainLeadsUpTo_here
              obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
              refine Or.inr ⟨c + z0, phi1, by omega, by omega, ?_, hb1⟩
              dsimp only [oxw]; rw [hdw]; omega
            · exact amega_pop_step hb1 hphi1_38 (by omega) (by omega)
                (hS.2.2 (c + z0 - 1) (by omega))
                (fun _ => hS.2.2 (c + z0 - 2) (by omega))
                (fun hbig _ _ p1 p2 hvp _ =>
                  chainLeadsUpTo_here (Or.inl ⟨c + z0 - 1, by dsimp only [odw]; omega,
                    isBounce_r9 (by omega) hbig hvp⟩))
                (fun hy1_le _ m3 _ p1 p2 hvp hfzp => by
                  have hy1_lo : 9 * ((k + 2 * z0) / 10) - 2 ≤ y1 := by rw [hdw10]; exact hy1_tx1
                  have hmono := arith_fb_os_r10 hc hk1 hkc hfz35 hcz42 hkz73 hy1_lo hy1_le hphi1_38 hyw1 hfzp
                  exact chainLeadsUpTo_imp
                    ((excursion270_bundle m3).1 ms S p1 p2 (c + z0 + 1) (y1 + 2) hms19 hS
                      (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      (Nat.le_trans hms_ox hmono.1))
                    (fun _ he => exit270_mono he hmono.1 hmono.2.1 hmono.2.2))
                (fun _ _ m3 _ p1 p2 hvp hfzp => by
                  have hi := arith_fb_os_r11 hc hk1 hkc hfz35 hcz42 hkz73 hyw1 hfzp
                  exact (excursion270_bundle m3).2 ms S p1 p2 y1 1 (c + z0 - 1)
                    (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                    hms19 hS (Or.inr (by omega)) hvp
                    (by omega) (by omega) (by omega) hms_ox hi.1
                    hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2)
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            apply chainLeadsUpTo_here
            obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
            refine Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, by omega, ?_, ?_⟩
            · dsimp only [oxw]; rw [hdw]; omega
            · have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                (rest := rest) (ds := (c + z0) :: S) hv_rest (by omega) (by
                  rcases dec_or (((m' - 4) + 1) % 2 = 1) with h | h
                  · rw [if_pos h]; omega
                  · rw [if_neg h]; omega)
              simpa only [Nat.add_zero] using hbc

lemma ox_ge_of_c {c k fz : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (_hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    c + 38 - (c + 13) / 10 ≤ ox (k + 2 * fz) (c + fz) ∧
    c + 37 - (c + 13) / 10 ≤ odw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  dsimp only [odw]; omega

lemma ox_ge57_of_cz62 {c k fz : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (_hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_hcz : 62 ≤ c + fz) (_hkz : 81 ≤ k + 2 * fz) :
    57 ≤ ox (k + 2 * fz) (c + fz) ∧ 56 ≤ odw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  dsimp only [odw]; omega

lemma r9_pop_step {N x y phi : Nat} {S : List Nat} {sb : SegState} {P : SegState → Prop}
    (hb : IsBounce phi (y :: x :: S) sb)
    (hphi38 : 38 ≤ phi) (hx19 : 19 ≤ x) (hbig : 2 * x + 5 ≤ y)
    (hcont : ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 → phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨true, (0, y - 3) :: p1, p2, x - 1, 0, 2 * x, S⟩ P) :
    ChainLeadsUpTo N sb P := by
  have hnrst : isDrainRstDs (y :: x :: S) = false := by
    cases x with | zero => omega | succ _ => rfl
  have hnr0 : isRank0 (y :: x :: S) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi (y :: x :: S) = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ x ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (y % 2 = 0 ∧ y ≤ 2 * x + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * x) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_sb, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (y :: x :: S) =
      ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_sb
  intro m hm
  rw [hstep, hdp]
  exact hcont m hm p.1 p.2 hvp hfzp

-- ============================================================================
-- Auxiliary Bounce & Drain-Pop Lemmas for RootD / RootD1 / Root1
-- ============================================================================

lemma bounce_r9_zero_leads {N d y : Nat} {p1 : List (Nat × Nat)} {p2 : Nat}
    (hd8 : 8 ≤ d) (hbig : 2 * d + 5 ≤ y) (hvp : ValidSegs40 p1 p2) :
    ChainLeadsUpTo N ⟨true, (0, y - 3) :: p1, p2, d - 1, 0, 2 * d, [0]⟩ RootInv270 := by
  have hy_sub : y - 3 = (y - 4) + 1 := by omega
  have hpop0 : drainPopGuards (d - 1 + 0) [0] = true := by
    change decide (d - 1 + 0 ≥ 2) = true; exact decide_eq_true (by omega)
  have hg1 : stepGuards ⟨true, (0, y - 3) :: p1, p2, d - 1, 0, 2 * d, [0]⟩ = true := by
    rw [hy_sub]; dsimp only [stepGuards]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; exact hpop0
    · rw [if_neg hev, decide_eq_false (by omega)]; exact hpop0
  have hs1 : stepSegs ⟨true, (0, y - 3) :: p1, p2, d - 1, 0, 2 * d, [0]⟩ =
      ⟨true, normSeg (d + 1) (y - 2 * d - 5) :: p1, p2, 2, 2, 6, []⟩ := by
    have hm_eq : 0 + ((y - 4) + 1) - (2 * d + 2) = y - 2 * d - 5 := by omega
    have hd_eq : d - 1 + 0 + 2 = d + 1 := by omega
    rw [hy_sub]; dsimp only [stepSegs]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]
      dsimp only [drainPopStep, isDrainRstDs, isRank0, pushSeg, ite_true, ite_false]
      rw [hd_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]
      dsimp only [drainPopStep, isDrainRstDs, isRank0, pushSeg, ite_true, ite_false]
      rw [hd_eq]; rfl
  apply chainLeadsUpTo_step hg1
  intro m1 _
  rw [hs1]
  have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
  rcases hmr : y - 2 * d - 5 with _ | mr'
  · dsimp only [normSeg, ite_true]
    have hg2 : stepGuards ⟨true, (d + 1 + 1, 0) :: p1, p2, 2, 2, 6, []⟩ = true := rfl
    apply chainLeadsUpTo_step1 hg2
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hvp)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
  · have hn : normSeg (d + 1) (mr' + 1) = (d + 1, mr' + 1) := rfl
    rw [hn]
    rcases dec_or ((mr' + 1) % 2 = 1) with hod | hev
    · cases hd_mrg : decide (6 ≥ 2 + mr') with
      | true =>
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_pos rfl]
          exact (safeStack_d (by omega)).2.1
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_D (d := 2 + (d + 1)) (by omega) (Or.inl rfl)
          (validTail40_of_validSegs40 hvp) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))
      | false =>
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_neg Bool.false_ne_true]
          change decide (2 + (d + 1) ≥ 2) = true; exact decide_eq_true (by omega)
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_neg Bool.false_ne_true]
        set q := pushSeg true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        have hdp : drainPopStep true (2 + (d + 1)) (2 + (mr' + 1) - (6 + 2)) p1 p2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 2 + (d + 1) + 1 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · cases hd_mrg : decide (6 ≥ 2 + (mr' + 1)) with
      | true =>
        have h_mrg := of_decide_eq_true hd_mrg
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_pos rfl]
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hvp)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
      | false =>
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_neg Bool.false_ne_true]
          change decide (2 + (d + 1) ≥ 2) = true; exact decide_eq_true (by omega)
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_neg Bool.false_ne_true]
        set q := pushSeg true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        have hdp : drainPopStep true (2 + (d + 1)) (2 + (mr' + 1) - (6 + 2)) p1 p2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 2 + (d + 1) + 1 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))

lemma bounce_y_8_ge46_leads {N y phi : Nat} {s : SegState}
    (hb : IsBounce phi [y, 8] s) (hy28 : 28 ≤ y) (hphi46 : 46 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hnrst : isDrainRstDs [y, 8] = false := rfl
  have hnr0 : isRank0 [y, 8] = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [y, 8] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ 8 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (y % 2 = 0 ∧ y ≤ 2 * 8 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * 8) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [y, 8] =
      ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 7, 0, 16, []⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h81, _, _⟩; cases h81)]
    have hnorm : normSeg 0 (y - 3) = (0, (y - 4) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg2 : stepGuards ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 7, 0, 16, []⟩ = true := by
    dsimp only [stepGuards]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs2 : stepSegs ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 7, 0, 16, []⟩ =
      ⟨false, (8, y - 21) :: p.1, p.2, 1, 1, 0, []⟩ := by
    have hm_eq : 0 + ((y - 4) + 1) - (16 + 2) = y - 21 := by omega
    have hn8 : normSeg 8 (y - 21) = (8, y - 21) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    have hdp2 : drainPopStep true (7 + 0) (y - 21) p.1 p.2 [] =
        ⟨false, normSeg 8 (y - 21) :: p.1, p.2, 1, 1, 0, []⟩ := rfl
    dsimp only [stepSegs]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp2, hn8]
    · rw [if_neg hev, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp2, hn8]
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  apply chainLeadsUpTo_here
  refine rootInv_of_0B (Or.inl rfl) hvp
    (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
  intro z0 m0 r hseg _ _ _
  injection hseg with hhd htl
  injection hhd with hz0 hm0
  subst hz0 hm0 htl
  exact ⟨by omega, by omega, fun hlt => False.elim (by omega)⟩

lemma bounce_y_d_small_leads {N d y phi : Nat} {tl : List Nat} {s : SegState}
    (hb : IsBounce phi (y :: d :: tl) s)
    (hd_lo : 8 ≤ d) (hd_hi : d ≤ 18)
    (htl : tl = [] ∨ tl = [0])
    (h8_tl : d = 8 → tl = [0])
    (hy39 : 39 ≤ y) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg1 : 9 ≤ d → GoodDs ((d - 1) :: tl) = true := by
    intro hd9
    rcases htl with rfl | rfl
    · exact (safeStack_d (by omega)).2.1
    · exact (safeStack_d0 (by omega)).2.1
  have hnrst : isDrainRstDs (y :: d :: tl) = false := by
    cases d with | zero => omega | succ _ => rfl
  have hnr0 : isRank0 (y :: d :: tl) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi (y :: d :: tl) = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ d ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : (!decide (y % 2 = 0 ∧ y ≤ 2 * d + 4) || GoodDs ((d - 1) :: tl)) = true := by
      rcases dec_or (d = 8) with rfl | hd9
      · rw [decide_eq_false (by omega)]; rfl
      · rw [hg1 (by omega), Bool.or_true]
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * d) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (y :: d :: tl) =
      ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, tl⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  rcases dec_or (2 * d + 5 ≤ y) with hbig | hsm
  · rcases htl with rfl | rfl
    · have hd9 : 9 ≤ d := by
        rcases dec_or (d = 8) with rfl | h9
        · cases h8_tl rfl
        · omega
      have hy_sub : y - 3 = (y - 4) + 1 := by omega
      have hpop_nil : drainPopGuards (d - 1 + 0) [] = true := by
        change decide (d - 1 + 0 ≥ 2) = true; exact decide_eq_true (by omega)
      have hg2 : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, []⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]
        rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
        · rw [if_pos hod, decide_eq_false (by omega)]; exact hpop_nil
        · rw [if_neg hev, decide_eq_false (by omega)]; exact hpop_nil
      apply chainLeadsUpTo_step1 hg2
      rw [hy_sub]; dsimp only [stepSegs]
      set q := pushSeg true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      have hvtq : ValidTail40 q.1 q.2 :=
        validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
      have hfzq : d - 1 + 0 + 1 ≤ fzOf q.1 q.2 :=
        fzOf_pushSeg_ge true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv270
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
      · rw [if_neg hev, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv270
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · exact bounce_r9_zero_leads hd_lo hbig hvp
  · -- Only possible when `d = 18` and `y = 39` or `y = 40`:
    have hd18 : d = 18 := by omega
    subst hd18
    rcases dec_or (y = 39) with rfl | hy40
    · have hg2 : stepGuards ⟨true, (0, 39 - 3) :: p.1, p.2, 18 - 1, 0, 2 * 18, tl⟩ = true := rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B htl (validTail40_of_validSegs40 hvp)
        (by decide) (by decide) (by decide) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    · have hy_eq : y = 40 := by omega
      subst hy_eq
      have hg2 : stepGuards ⟨true, (0, 40 - 3) :: p.1, p.2, 18 - 1, 0, 2 * 18, tl⟩ = true := by
        change stepGuards ⟨true, (0, 36 + 1) :: p.1, p.2, 17, 0, 36, tl⟩ = true
        dsimp only [stepGuards]
        rw [if_pos (by decide), decide_eq_true (by decide), if_pos rfl]
        exact hg1 (by decide)
      apply chainLeadsUpTo_step1 hg2
      change ChainLeadsUpTo m1 (stepSegs ⟨true, (0, 36 + 1) :: p.1, p.2, 17, 0, 36, tl⟩) RootInv270
      dsimp only [stepSegs]
      rw [if_pos (by decide), decide_eq_true (by decide), if_pos rfl]
      have hds17 : (17 :: tl) = [17] ∨ (17 :: tl) = [17, 0] := by
        rcases htl with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact chainLeadsUpTo_here (rootInv_of_D (d := 17) (by decide) hds17
        (validTail40_of_validSegs40 hvp) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega))

-- ============================================================================
-- 1. `rootD_advances` (`RootD s -> ChainAdvances s RootInv270`)
-- ============================================================================

lemma x_8_high_leads {N x zl c k : Nat} {segs : List (Nat × Nat)}
    (hx41 : 41 ≤ x) (hv : ValidSegs40 segs zl)
    (hc : (66 ≤ c ∧ k = 1) ∨ (77 ≤ c ∧ 1 ≤ k ∧ k ≤ 2 * c + 3)) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 8]⟩ RootInv270 := by
  have hc2 : 2 ≤ c := by rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hk1 : 1 ≤ k := by rcases hc with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  have hkc : k ≤ 2 * c + 3 := by rcases hc with ⟨_, rfl⟩ | ⟨_, _, h⟩ <;> omega
  have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
  have hox97 : 97 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) ∧
      96 ≤ odw (k + 2 * fzOf segs zl) (c + fzOf segs zl) := by
    have h := ox_ge_of_c hc2 hk1 hkc hfz40
    have hc66 : 66 ≤ c := by rcases hc with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    omega
  have hS8_21 : SafeStack 21 [8] := safeStack_d (by decide)
  have hS8 : SafeStack 43 [8] := safeStack_mono (by decide) hS8_21
  have hSx8 : SafeStack 19 [x, 8] :=
    safeStack_cons_ne1 (by decide) hS8_21 (by omega) (by omega)
  have hfb := (excursion270_bundle N).1 19 [x, 8] segs zl c k (by decide) hSx8
    (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
  refine chainLeadsUpTo_trans hfb ?_
  intro m1 s_mid hm1 hex
  rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
  · exact bounce_y_8_ge46_leads hb (by omega) (by omega)
  · exact amega_pop_step hb hphi38 (by omega) (by omega)
      (hS8_21.2.2 (x - 1) (by omega))
      (fun _ => hS8_21.2.2 (x - 2) (by omega))
      (fun hbig _ _ p1 p2 hvp _ =>
        bounce_d_leads (isBounce_r9 (by omega) hbig hvp) (Or.inl rfl)
          (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩))
      (fun _ _ _ _ p1 p2 hvp _ => by
        have hfp := fzOf_ge_40 hvp
        exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
          (validTail40_of_validSegs40 hvp) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)))
      (fun hy_le _ m2 _ p1 p2 hvp _ => by
        have hfp := fzOf_ge_40 hvp
        have hox124 : 124 ≤ ox (1 + 2 * fzOf p1 p2) (y + fzOf p1 p2) ∧
            123 ≤ odw (1 + 2 * fzOf p1 p2) (y + fzOf p1 p2) := by
          have h := ox_ge_of_c (c := y) (k := 1) (fz := fzOf p1 p2)
            (by omega) (by decide) (by omega) hfp
          omega
        have hSx1 : SafeStack 19 [x - 1, 8] :=
          safeStack_cons_ne1 (by decide) hS8_21 (by omega) (by omega)
        have hfb2 := (excursion270_bundle m2).1 19 [x - 1, 8] p1 p2 y 1 (by decide) hSx1
          (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
          (by omega) (by omega) (by omega) (by omega)
        refine chainLeadsUpTo_trans hfb2 ?_
        intro m3 s_m2 _ hex2
        rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
        · exact bounce_y_8_ge46_leads hb2 (by omega) (by omega)
        · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
            (hS8_21.2.2 (x - 1 - 1) (by omega))
            (fun _ => hS8_21.2.2 (x - 1 - 2) (by omega))
            (fun hbig _ _ q1 q2 hvq _ =>
              bounce_d_leads (isBounce_r9 (by omega) hbig hvq) (Or.inl rfl)
                (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩))
            (fun _ _ _ _ q1 q2 hvq _ => by
              have hfq := fzOf_ge_40 hvq
              exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
                (validTail40_of_validSegs40 hvq) (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega)))
            (fun hy2_le _ m4 _ q1 q2 hvq _ => by
              have hfq := fzOf_ge_40 hvq
              have hx2_49 : 49 ≤ x - 1 - 1 := by omega
              have hlh := (fhigh_bundle m4).2.1 [8] q1 q2 y2 1 (x - 1 - 1)
                (by decide) hS8 hvq (by omega) (by decide) (by omega) hx2_49 (by omega)
              refine chainLeadsUpTo_trans hlh ?_
              intro m5 s_eh _ heh
              rcases heh with ⟨phi3, hphi3, hb3⟩ | ⟨y3, phi3, hy3, hphi3, hb3⟩
              · exact bounce_d_leads hb3 (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
              · exact bounce_y_8_ge46_leads hb3 (by omega) (by omega)))

lemma exitHigh_8_leads {N : Nat} {s : SegState} (heh : ExitHigh [8] s) :
    ChainLeadsUpTo N s RootInv270 := by
  rcases heh with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi, hb⟩
  · exact bounce_d_leads hb (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
  · exact bounce_y_8_ge46_leads hb (by omega) (by omega)

lemma rootD_advances {s : SegState} (hb0 : s.b = false) (hm0_z : s.mrg = 0) (hr : RootD s) :
    ChainAdvances s RootInv270 := by
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb0 hm0_z
  subst hb0 hm0_z
  obtain ⟨⟨d, hd8, hds⟩, hvt, hc, hk1, hkc, hfz35, hcz42, hkz73⟩ := hr
  dsimp only at hds hvt hc hk1 hkc hfz35 hcz42 hkz73
  rcases dec_or (ds = [8]) with rfl | hnot8
  · -- Dedicated 1-step unrolling for `ds = [8]` (ensures `46 <= phi` on all `[y, 8]` exits):
    have hS8_21 : SafeStack 21 [8] := safeStack_d (by decide)
    have hS8_43 : SafeStack 43 [8] := safeStack_mono (by decide) hS8_21
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73
      have hg : stepGuards ⟨false, [], zl, c, k, 0, [8]⟩ = true := by
        dsimp only [stepGuards]
        rw [goodPhiW_of_ge35 hS8_21.1 (by omega), Bool.true_and]
        dsimp only [GoodPsi]
        have hcz : c + zl - 1 + 1 = c + zl := by omega
        rw [hcz]; exact hS8_21.2.2 (c + zl) (by omega)
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 8]
          ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 8]⟩ := by
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 8]) (by omega)
      exact bounce_y_8_ge46_leads hbc (by omega) (by omega)
    · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        refine ⟨rfl, fun N => ?_⟩
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact bounce_d_leads (IsBounce.nil (by omega)) (Or.inl rfl)
            (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
                2 * (c + z0) + 8, [8]⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step hg2
            intro m2 _
            dsimp only [stepSegs]
            exact chainLeadsUpTo_trans
              ((fhigh_bundle m2).1 [8] rest2 zl (c + z0 + 3 + z1 + 1) (k + 2 * z0 + 3 + 2 * z1 + 3)
                (by decide) hS8_43 hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ _ _ heh => exitHigh_8_leads heh)
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [8]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS8_21.2.2 (c + z0 + 3 + z1) (by omega)
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_trans
                  ((fhigh_bundle m2).2.1 [8] rest2 zl ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1
                    (c + z0 + 3 + z1) (by decide) hS8_43 hv_r2
                    (by omega) (by decide) (by omega) (by omega) (by omega))
                  (fun _ _ _ heh => exitHigh_8_leads heh)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega))
                  (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [8]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_trans
                  ((fhigh_bundle m2).1 [8] rest2 zl (c + z0 + 3 + z1 + 2)
                    ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                    (by decide) hS8_43 hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ heh => exitHigh_8_leads heh)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega))
                  (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + z0 - 1) [8] false = true := goodPhiW_of_ge35 hS8_21.1 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [8] false && if 1 = 1 then GoodPsi (c + z0) [8] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS8_21.2.2 (c + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact x_8_high_leads (by omega) hv_rest (Or.inr ⟨by omega, by decide, by omega⟩)
        · have hpsi_cz : GoodPsi (c + z0 - 1) [8] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
            rw [hcz_eq]; exact hS8_21.2.2 (c + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [8] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [8] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact x_8_high_leads (by omega) hv_rest (Or.inr ⟨by omega, by omega, by omega⟩)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 19 [c + z0, 8] :=
                safeStack_cons_ne1 (by decide) hS8_21 (by omega) (by omega)
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [8] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [8] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                      GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [8]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              have hne1_cz : ([c + z0, 8] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              have hlb := (excursion270_bundle N).2 19 [c + z0, 8] rest zl m' 1
                (k + 2 * z0 + 2) 65 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                (by omega) (by decide) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega)
              refine chainLeadsUpTo_trans hlb ?_
              intro m1 s_mid _ hex
              rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
              · exact bounce_y_8_ge46_leads hb (by omega) (by omega)
              · exact amega_pop_step hb hphi38 (by omega) (by omega)
                  (hS8_21.2.2 (c + z0 - 1) (by omega))
                  (fun _ => hS8_21.2.2 (c + z0 - 2) (by omega))
                  (fun hbig _ _ p1 p2 hvp _ =>
                    bounce_d_leads (isBounce_r9 (by omega) hbig hvp) (Or.inl rfl)
                      (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩))
                  (fun _ _ _ _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
                      (validTail40_of_validSegs40 hvp) (by omega) (by omega) (by omega)
                      (by omega) (by omega) (by omega)))
                  (fun _ _ m2 _ p1 p2 hvp _ =>
                    x_8_high_leads (by omega) hvp (Or.inl ⟨by omega, rfl⟩))
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [8] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [8] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 8]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, [c + z0, 8]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := [c + z0, 8]) hv_rest (by omega) (by
                    rcases dec_or (((m' - 4) + 1) % 2 = 1) with h1 | h1
                    · rw [if_pos h1]; omega
                    · rw [if_neg h1]; omega)
                simpa only [Nat.add_zero] using h
              exact bounce_y_8_ge46_leads hbc (by omega) (by omega)
  · -- General `RootD` (`9 <= d` or `ds = [8, 0]`):
    have hS : SafeStack 21 ds := by
      rcases hds with rfl | rfl
      · exact safeStack_d hd8
      · exact safeStack_d0 hd8
    obtain ⟨hox39, _⟩ := ox_bounds_relaxed hc hk1 hkc hfz35 hcz42 hkz73
    have hadv := fbound_advances (ms := 21) (by decide) hS hvt hc hk1 hkc hfz35 hcz42 hkz73 (by omega)
    refine chainAdvances_trans hadv ?_
    intro s' hex N
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · have hphi38 : 38 ≤ phi := by dsimp only [odw] at hphi; omega
      refine bounce_d_leads hb hds ?_
      rcases dec_or (d = 8) with rfl | hd9
      · exact Or.inl ⟨rfl, Or.inr (Or.inr hphi38)⟩
      · rcases dec_or (d = 9) with rfl | hd10
        · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
        · rcases dec_or (d ≤ 18) with hd18 | hd19
          · exact Or.inr (Or.inr (Or.inl ⟨by omega, hd18, by omega, fun _ _ => by omega⟩))
          · rcases dec_or (d = 19) with rfl | hd20
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hphi38⟩)))
    · obtain ⟨tl, hds_eq, htl, h8_tl⟩ :
          ∃ tl, ds = d :: tl ∧ (tl = [] ∨ tl = [0]) ∧ (d = 8 → tl = [0]) := by
        rcases hds with rfl | rfl
        · exact ⟨[], rfl, Or.inl rfl, fun hd => False.elim (hnot8 (by rw [hd]))⟩
        · exact ⟨[0], rfl, Or.inr rfl, fun _ => rfl⟩
      rw [hds_eq] at hb
      rcases dec_or (d ≤ 18) with hd18 | hd19
      · exact bounce_y_d_small_leads hb hd8 hd18 htl h8_tl (by omega) hphi38
      · have hg1 : GoodDs ((d - 1) :: tl) = true := by
          rcases htl with rfl | rfl
          · exact (safeStack_d (by omega)).2.1
          · exact (safeStack_d0 (by omega)).2.1
        have hg2 : GoodDs ((d - 2) :: tl) = true := by
          rcases htl with rfl | rfl
          · exact (safeStack_d (by omega)).2.1
          · exact (safeStack_d0 (by omega)).2.1
        exact amega_pop_step hb hphi38 (by omega) (by omega) hg1 (fun _ => hg2)
          (fun hbig _ _ p1 p2 hvp _ => by
            rcases htl with rfl | rfl
            · exact bounce_nil_leads (isBounce_r9 (by omega) hbig hvp) (by omega)
            · exact bounce_r9_zero_leads (by omega) hbig hvp)
          (fun _ _ _ _ p1 p2 hvp _ => by
            have hfp := fzOf_ge_40 hvp
            exact chainLeadsUpTo_here (rootInv_of_0B htl (validTail40_of_validSegs40 hvp)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega)))
          (fun _ _ _ _ p1 p2 hvp _ => by
            have hfp := fzOf_ge_40 hvp
            have hds_d1 : ((d - 1) :: tl) = [d - 1] ∨ ((d - 1) :: tl) = [d - 1, 0] := by
              rcases htl with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
            exact chainLeadsUpTo_here (rootInv_of_D (d := d - 1) (by omega) hds_d1
              (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
              (by omega) (by omega) (by omega)))

-- ============================================================================
-- 2. `rootD1_advances` (`RootD1 s -> ChainAdvances s RootInv270`)
-- ============================================================================

lemma exit270_d1_leads {N d tx tdw txw : Nat} {s : SegState}
    (hd25 : 25 ≤ d) (htx : 43 ≤ tx) (htdw : 42 ≤ tdw)
    (h25_tx : d = 25 → 57 ≤ tx)
    (hex : Exit270 tx tdw txw [d, 1] s) :
    ChainLeadsUpTo N s RootInv270 := by
  rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
  · exact bounce_d1_leads hb hd25 (by omega)
  · rcases dec_or (d = 25) with rfl | hd26
    · have h57 : 57 ≤ tx := h25_tx rfl
      exact r9_pop_step hb hphi38 (by decide) (by omega)
        (fun _ _ p1 p2 hvp _ =>
          bounce_one_leads (isBounce_r9 (by decide) (by omega) hvp) (by decide))
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (safeStack_one.2.2 (d - 1) (by omega))
        (fun _ => safeStack_one.2.2 (d - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          bounce_one_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
        (fun _ _ _ _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hvp)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (fun _ => by omega)))
        (fun _ _ _ _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_here (rootInv_of_D1 (by omega) (validTail40_of_validSegs40 hvp)
            (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)))

lemma rootD1_advances {s : SegState} (hb0 : s.b = false) (hm0_z : s.mrg = 0) (hr : RootD1 s) :
    ChainAdvances s RootInv270 := by
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb0 hm0_z
  subst hb0 hm0_z
  obtain ⟨⟨d, hd25, hds⟩, hvt, hc, hk1, hkc, hfz40, hcz62, hkz81⟩ := hr
  dsimp only at hds hvt hc hk1 hkc hfz40 hcz62 hkz81
  subst hds
  rcases dec_or (d = 25) with rfl | hd26
  · -- Dedicated 1-step unrolling for `d = 25` (`SafeStack 55 [25, 1]`):
    have hS55 : SafeStack 55 [25, 1] := safeStack_25_1
    have hne1 : ([25, 1] : List Nat) ≠ [1] := by intro h; cases h
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz40 hcz62 hkz81
      have hg : stepGuards ⟨false, [], zl, c, k, 0, [25, 1]⟩ = true := by
        dsimp only [stepGuards]
        rw [goodPhiW_of_ge35 hS55.1 (by omega), Bool.true_and]
        dsimp only [GoodPsi]
        have hcz : c + zl - 1 + 1 = c + zl := by omega
        rw [hcz]; exact hS55.2.2 (c + zl) (by omega)
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 25, 1]
          ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 25, 1]⟩ := by
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 25, 1]) (by omega)
      exact exit270_d1_leads (tx := 57) (tdw := 42) (txw := 0) (by decide) (by decide) (by decide)
        (fun _ => by decide) (Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, by omega, by omega, hbc⟩)
    · dsimp only [fzOf, ValidTail40] at hvt hfz40 hcz62 hkz81
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        refine ⟨rfl, fun N => ?_⟩
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact bounce_d1_leads (IsBounce.nil (by omega)) (by decide) (by omega)
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
                2 * (c + z0) + 8, [25, 1]⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step hg2
            intro m2 _
            dsimp only [stepSegs]
            have hox := ox_ge_of_c (c := c + z0 + 3 + z1 + 1) (k := k + 2 * z0 + 3 + 2 * z1 + 3)
              (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
            exact chainLeadsUpTo_trans
              ((excursion270_bundle m2).1 55 [25, 1] rest2 zl (c + z0 + 3 + z1 + 1)
                (k + 2 * z0 + 3 + 2 * z1 + 3) (by decide) hS55 (validTail40_of_validSegs40 hv_r2)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ _ _ hex => exit270_d1_leads (by decide) (by omega) (by omega)
                (fun _ => by omega) hex)
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [25, 1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS55.2.2 (c + z0 + 3 + z1) (by omega)
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_trans
                  ((excursion270_bundle m2).2 55 [25, 1] rest2 zl
                    ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1 (c + z0 + 3 + z1) 57 0
                    (by decide) hS55 (Or.inl hne1) hv_r2
                    (by omega) (by decide) (by omega) (by decide) (by omega)
                    (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ hex => exit270_d1_leads (by decide) (by decide) (by decide)
                    (fun _ => by decide) hex)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d1_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega))
                  (by decide) (by omega)
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [25, 1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                have hox := ox_ge_of_c (c := c + z0 + 3 + z1 + 2)
                  (k := (k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                  (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
                exact chainLeadsUpTo_trans
                  ((excursion270_bundle m2).1 55 [25, 1] rest2 zl (c + z0 + 3 + z1 + 2)
                    ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                    (by decide) hS55 (validTail40_of_validSegs40 hv_r2)
                    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ hex => exit270_d1_leads (by decide) (by omega) (by omega)
                    (fun _ => by omega) hex)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d1_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega))
                  (by decide) (by omega)
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + z0 - 1) [25, 1] false = true :=
          goodPhiW_of_ge35 hS55.1 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [25, 1] false &&
              if 1 = 1 then GoodPsi (c + z0) [25, 1] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS55.2.2 (c + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_trans
            ((excursion270_bundle N).2 55 [25, 1] rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1) 57 0
              (by decide) hS55 (Or.inl hne1) hv_rest
              (by omega) (by decide) (by omega) (by decide) (by omega)
              (by omega) (by omega) (by omega) (by omega))
            (fun _ _ _ hex => exit270_d1_leads (by decide) (by decide) (by decide)
              (fun _ => by decide) hex)
        · have hpsi_cz : GoodPsi (c + z0 - 1) [25, 1] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
            rw [hcz_eq]; exact hS55.2.2 (c + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [25, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [25, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_trans
              ((excursion270_bundle N).2 55 [25, 1] rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0) 57 0
                (by decide) hS55 (Or.inl hne1) hv_rest
                (by omega) (by omega) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega))
              (fun _ _ _ hex => exit270_d1_leads (by decide) (by decide) (by decide)
                (fun _ => by decide) hex)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 19 [c + z0, 25, 1] :=
                safeStack_cons_ne1 hne1 hS55 (by omega) (by omega)
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [25, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [25, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                      GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [25, 1]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              have hne1_cz : ([c + z0, 25, 1] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              have hlb := (excursion270_bundle N).2 19 [c + z0, 25, 1] rest zl m' 1
                (k + 2 * z0 + 2) 65 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                (by omega) (by decide) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega)
              refine chainLeadsUpTo_trans hlb ?_
              intro m1 s_mid _ hex
              rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
              · exact exit270_d1_leads (tx := 57) (tdw := 42) (txw := 0)
                  (by decide) (by decide) (by decide) (fun _ => by decide)
                  (Or.inr ⟨c + z0, phi, by omega, by omega, by omega, hb⟩)
              · exact amega_pop_step hb hphi38 (by omega) (by omega)
                  (hS55.2.2 (c + z0 - 1) (by omega))
                  (fun _ => hS55.2.2 (c + z0 - 2) (by omega))
                  (fun hbig _ _ p1 p2 hvp _ =>
                    bounce_d1_leads (isBounce_r9 (by omega) hbig hvp) (by decide) (by omega))
                  (fun _ _ m2 _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    have hox := ox_ge_of_c (c := c + z0 + 1) (k := y + 2) (fz := fzOf p1 p2)
                      (by omega) (by omega) (by omega) hfp
                    exact chainLeadsUpTo_trans
                      ((excursion270_bundle m2).1 55 [25, 1] p1 p2 (c + z0 + 1) (y + 2)
                        (by decide) hS55 (validTail40_of_validSegs40 hvp)
                        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                      (fun _ _ _ hex2 => exit270_d1_leads (by decide) (by omega) (by omega)
                        (fun _ => by omega) hex2))
                  (fun _ _ m2 _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    exact chainLeadsUpTo_trans
                      ((excursion270_bundle m2).2 55 [25, 1] p1 p2 y 1 (c + z0 - 1) 57 0
                        (by decide) hS55 (Or.inl hne1) hvp
                        (by omega) (by decide) (by omega) (by decide) (by omega)
                        (by omega) (by omega) (by omega) (by omega))
                      (fun _ _ _ hex2 => exit270_d1_leads (by decide) (by decide) (by decide)
                        (fun _ => by decide) hex2))
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [25, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [25, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 25, 1]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, [c + z0, 25, 1]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := [c + z0, 25, 1]) hv_rest (by omega) (by
                    rcases dec_or (((m' - 4) + 1) % 2 = 1) with h1 | h1
                    · rw [if_pos h1]; omega
                    · rw [if_neg h1]; omega)
                simpa only [Nat.add_zero] using h
              exact exit270_d1_leads (tx := 57) (tdw := 42) (txw := 0)
                (by decide) (by decide) (by decide) (fun _ => by decide)
                (Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, by omega, by omega, hbc⟩)
  · -- General `26 <= d` (`SafeStack 39 [d, 1]`):
    have hS : SafeStack 39 [d, 1] := safeStack_d1 (by omega)
    have hox57 := ox_ge57_of_cz62 hc hk1 hkc hfz40 hcz62 hkz81
    have hadv := fbound_advances (ms := 39) (by decide) hS hvt (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    exact chainAdvances_trans hadv
      (fun _ hex _ => exit270_d1_leads hd25 (by omega) (by omega) (fun h25 => False.elim (hd26 h25)) hex)

-- ============================================================================
-- 3. `root1_advances` (`Root1 s -> ChainAdvances s RootInv270`)
-- ============================================================================

lemma pop_47_25_1_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [47, 25, 1] s) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [47, 25, 1] = true := by
    change (true && true && true && decide (phi ≥ 16)) = true
    rw [Bool.true_and, Bool.true_and, Bool.true_and]
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [47, 25, 1] =
      ⟨true, (0, 44) :: p.1, p.2, 24, 0, 50, [1]⟩ := rfl
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfp := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep, hdp]
  have hg2 : stepGuards ⟨true, (0, 44) :: p.1, p.2, 24, 0, 50, [1]⟩ = true := rfl
  apply chainLeadsUpTo_step1 hg2
  dsimp only [stepSegs]
  exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hvp)
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (fun _ => by omega))

lemma exit_47_25_1_leads {N tx tdw txw : Nat} {s : SegState}
    (htx99 : 99 ≤ tx) (htdw38 : 38 ≤ tdw)
    (hex : Exit270 tx tdw txw [47, 25, 1] s) :
    ChainLeadsUpTo N s RootInv270 := by
  rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
  · exact pop_47_25_1_leads hb (by omega)
  · exact r9_pop_step hb hphi38 (by decide) (by omega)
      (fun _ _ p1 p2 hvp _ =>
        bounce_d1_leads (isBounce_r9 (by decide) (by omega) hvp) (by decide) (by decide))

lemma x_47_25_1_high_leads {N x zl c k : Nat} {segs : List (Nat × Nat)}
    (hx101 : 101 ≤ x) (hv : ValidSegs40 segs zl)
    (hc : (170 ≤ c ∧ k = 1) ∨ (189 ≤ c ∧ 1 ≤ k ∧ k ≤ 2 * c + 3)) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 47, 25, 1]⟩ RootInv270 := by
  have hc170 : 170 ≤ c := by rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hk1 : 1 ≤ k := by rcases hc with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  have hkc : k ≤ 2 * c + 3 := by rcases hc with ⟨_, rfl⟩ | ⟨_, _, h⟩ <;> omega
  have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
  have hS47 : SafeStack 99 [47, 25, 1] := safeStack_47_25_1
  have hne1 : ([47, 25, 1] : List Nat) ≠ [1] := by intro h; cases h
  rcases dec_or (105 ≤ x) with hx105 | hx104
  · exact chainLeadsUpTo_trans
      ((excursion270_bundle N).2 99 [47, 25, 1] segs zl c k x 101 0
        (by decide) hS47 (Or.inl hne1) hv
        (by omega) hk1 hkc (by decide) (by omega)
        (by omega) (by omega) (by omega) (by omega))
      (fun _ _ _ hex => exit_47_25_1_leads (by decide) (by decide) hex)
  · have hox190 := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hSx : SafeStack 19 [x, 47, 25, 1] :=
      safeStack_cons_ne1 hne1 hS47 (by omega) (by omega)
    have hfb := (excursion270_bundle N).1 19 [x, 47, 25, 1] segs zl c k (by decide) hSx
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid _ hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
        (Or.inr ⟨x, phi, by omega, by omega, by omega, hb⟩)
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (hS47.2.2 (x - 1) (by omega)) (fun _ => hS47.2.2 (x - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          pop_47_25_1_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
        (fun _ _ m2 _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          have hox129 := ox_ge_of_c (c := x + 1) (k := y + 2) (fz := fzOf p1 p2)
            (by omega) (by omega) (by omega) hfp
          exact chainLeadsUpTo_trans
            ((excursion270_bundle m2).1 99 [47, 25, 1] p1 p2 (x + 1) (y + 2)
              (by decide) hS47 (validTail40_of_validSegs40 hvp)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ _ _ hex2 => exit_47_25_1_leads (by omega) (by omega) hex2))
        (fun _ _ m2 _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          have hox208 := ox_ge_of_c (c := y) (k := 1) (fz := fzOf p1 p2)
            (by omega) (by decide) (by omega) hfp
          rcases dec_or (x = 101) with rfl | hx102
          · exact fbound_force_r9 (x := 100) (d3 := 47) (ds3 := [25, 1]) (by decide)
              (hS47.2.2 100 (by decide)) (hS47.2.2 99 (by decide)) hvp
              (by omega) (by decide) (by omega) (by omega) (by omega)
              (fun _ phi2 _ hphi2 _ hb2 =>
                exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                  (Or.inr ⟨100, phi2, by decide, by omega, by omega, hb2⟩))
              (fun _ _ _ hb2 => pop_47_25_1_leads hb2 (by decide))
          · have hSx1 : SafeStack 19 [x - 1, 47, 25, 1] :=
              safeStack_cons_ne1 hne1 hS47 (by omega) (by omega)
            have hfb2 := (excursion270_bundle m2).1 19 [x - 1, 47, 25, 1] p1 p2 y 1
              (by decide) hSx1 (validTail40_of_validSegs40 hvp)
              (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
            refine chainLeadsUpTo_trans hfb2 ?_
            intro m3 s_m2 _ hex2
            rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
            · exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                (Or.inr ⟨x - 1, phi2, by omega, by omega, by omega, hb2⟩)
            · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
                (hS47.2.2 (x - 1 - 1) (by omega)) (fun _ => hS47.2.2 (x - 1 - 2) (by omega))
                (fun hbig _ _ q1 q2 hvq _ =>
                  pop_47_25_1_leads (isBounce_r9 (by omega) hbig hvq) (by omega))
                (fun _ _ m4 _ q1 q2 hvq _ => by
                  have hfq := fzOf_ge_40 hvq
                  have hox129 := ox_ge_of_c (c := x - 1 + 1) (k := y2 + 2) (fz := fzOf q1 q2)
                    (by omega) (by omega) (by omega) hfq
                  exact chainLeadsUpTo_trans
                    ((excursion270_bundle m4).1 99 [47, 25, 1] q1 q2 (x - 1 + 1) (y2 + 2)
                      (by decide) hS47 (validTail40_of_validSegs40 hvq)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                    (fun _ _ _ hex3 => exit_47_25_1_leads (by omega) (by omega) hex3))
                (fun _ _ _ _ q1 q2 hvq _ => by
                  have hfq := fzOf_ge_40 hvq
                  have hox224 := ox_ge_of_c (c := y2) (k := 1) (fz := fzOf q1 q2)
                    (by omega) (by decide) (by omega) hfq
                  exact fbound_force_r9 (x := x - 1 - 1) (d3 := 47) (ds3 := [25, 1]) (by omega)
                    (hS47.2.2 (x - 1 - 1) (by omega)) (hS47.2.2 (x - 1 - 1 - 1) (by omega)) hvq
                    (by omega) (by decide) (by omega) (by omega) (by omega)
                    (fun _ phi3 _ hphi3 _ hb3 =>
                      exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                        (Or.inr ⟨x - 1 - 1, phi3, by omega, by omega, by omega, hb3⟩))
                    (fun _ _ _ hb3 => pop_47_25_1_leads hb3 (by omega))))

lemma stack_47_25_1_leads {N zl c1 : Nat} {segs : List (Nat × Nat)}
    (hv : ValidSegs40 segs zl) (hc1 : 6 ≤ c1)
    (hcz102 : 102 ≤ c1 + fzOf segs zl) (hkz185 : 185 ≤ 1 + 2 * fzOf segs zl) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, [47, 25, 1]⟩ RootInv270 := by
  have hS47 : SafeStack 99 [47, 25, 1] := safeStack_47_25_1
  have hne1 : ([47, 25, 1] : List Nat) ≠ [1] := by intro h; cases h
  rcases segs with _ | ⟨⟨z1, m1⟩, rest⟩
  · have := hv.2
    have hg : stepGuards ⟨false, [], zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_of_ge35 hS47.1 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c1 + zl - 1 + 1 = c1 + zl := by omega
      rw [hcz]; exact hS47.2.2 (c1 + zl) (by omega)
    apply chainLeadsUpTo_step1 hg
    dsimp only [stepSegs]
    have hbc : IsBounce (1 + 2 * zl + 2) [c1 + zl, 47, 25, 1]
        ⟨true, [], 0, 1 + 2 * zl + 2, 0, 2 * (1 + 2 * zl) + 6, [c1 + zl, 47, 25, 1]⟩ := by
      simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := 1 + 2 * zl + 2) (kb := 0)
        (mrg := 2 * (1 + 2 * zl) + 6) (ds := [c1 + zl, 47, 25, 1]) (by omega)
    exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
      (Or.inr ⟨c1 + zl, 1 + 2 * zl + 2, by omega, by omega, by omega, hbc⟩)
  · dsimp only [fzOf] at hcz102 hkz185
    have hv_rest : ValidSegs40 rest zl := validSegs40_tail hv
    cases m1 with
    | zero =>
      have hg1 : stepGuards ⟨false, (z1, 0) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := rfl
      apply chainLeadsUpTo_step hg1
      intro m_a _
      dsimp only [stepSegs]
      rcases rest with _ | ⟨⟨z2, m2⟩, rest2⟩
      · have := hv_rest.2
        exact pop_47_25_1_leads (IsBounce.nil (by omega)) (by omega)
      · have hz2_40 : 40 ≤ z2 := fzOf_ge_40 hv_rest
        have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
        have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
        cases m2 with
        | zero =>
          have hg2 : stepGuards ⟨true, (z2, 0) :: rest2, zl, c1 + z1 + 3, 1 + 2 * z1 + 3,
              2 * (c1 + z1) + 8, [47, 25, 1]⟩ = true := by
            dsimp only [stepGuards]; exact decide_eq_true (by omega)
          apply chainLeadsUpTo_step hg2
          intro m_b _
          dsimp only [stepSegs]
          have hox := ox_ge_of_c (c := c1 + z1 + 3 + z2 + 1) (k := 1 + 2 * z1 + 3 + 2 * z2 + 3)
            (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
          exact chainLeadsUpTo_trans
            ((excursion270_bundle m_b).1 99 [47, 25, 1] rest2 zl (c1 + z1 + 3 + z2 + 1)
              (1 + 2 * z1 + 3 + 2 * z2 + 3) (by decide) hS47 (validTail40_of_validSegs40 hv_r2)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ _ _ hex => exit_47_25_1_leads (by omega) (by omega) hex)
        | succ m2' =>
          rcases dec_or ((m2' + 1) % 2 = 1) with hm2_od | hm2_ev
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + m2') with
            | true =>
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, [47, 25, 1]⟩ = true := by
                dsimp only [stepGuards]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
                exact hS47.2.2 (c1 + z1 + 3 + z2) (by omega)
              apply chainLeadsUpTo_step hg2
              intro m_b _
              dsimp only [stepSegs]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
              exact x_47_25_1_high_leads (by omega) hv_r2 (Or.inl ⟨by omega, rfl⟩)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact pop_47_25_1_leads
                (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm2_od]; omega)) (by omega)
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + (m2' + 1)) with
            | true =>
              have h_mrg := of_decide_eq_true hd_mrg
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, [47, 25, 1]⟩ = true := by
                dsimp only [stepGuards]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              apply chainLeadsUpTo_step hg2
              intro m_b _
              dsimp only [stepSegs]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              have hox := ox_ge_of_c (c := c1 + z1 + 3 + z2 + 2)
                (k := (1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
              exact chainLeadsUpTo_trans
                ((excursion270_bundle m_b).1 99 [47, 25, 1] rest2 zl (c1 + z1 + 3 + z2 + 2)
                  ((1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                  (by decide) hS47 (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                (fun _ _ _ hex => exit_47_25_1_leads (by omega) (by omega) hex)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact pop_47_25_1_leads
                (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm2_ev]; omega)) (by omega)
    | succ m' =>
      have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
      have hphiw : GoodPhiW (c1 + z1 - 1) [47, 25, 1] false = true :=
        goodPhiW_of_ge35 hS47.1 (by omega)
      rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z1, 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
            if 1 = 1 then GoodPsi (c1 + z1) [47, 25, 1] else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact hS47.2.2 (c1 + z1 + 1) (by omega)
        apply chainLeadsUpTo_step hg
        intro m_a _
        dsimp only [stepSegs]
        change ChainLeadsUpTo m_a (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        exact x_47_25_1_high_leads (by omega) hv_rest (Or.inl ⟨by omega, rfl⟩)
      · have hpsi_cz : GoodPsi (c1 + z1 - 1) [47, 25, 1] = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c1 + z1 - 1 + 1 = c1 + z1 := by omega
          rw [hcz_eq]; exact hS47.2.2 (c1 + z1) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z1, m' + 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
              if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) [47, 25, 1] &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          apply chainLeadsUpTo_step hg
          intro m_a _
          dsimp only [stepSegs]
          change ChainLeadsUpTo m_a (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          exact x_47_25_1_high_leads (by omega) hv_rest (Or.inr ⟨by omega, by omega, by omega⟩)
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 19 [c1 + z1, 47, 25, 1] :=
              safeStack_cons_ne1 hne1 hS47 (by omega) (by omega)
            have hg : stepGuards ⟨false, (z1, m' + 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) [47, 25, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then
                    GoodDs ((1 + 2 * z1 + 2) :: (c1 + z1) :: [47, 25, 1]) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (1 + 2 * z1 + 2) (by omega)
            apply chainLeadsUpTo_step hg
            intro m_a _
            dsimp only [stepSegs]
            change ChainLeadsUpTo m_a (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            have hne1_cz : ([c1 + z1, 47, 25, 1] : List Nat) ≠ [1] := by
              intro h; injection h with _ h2; cases h2
            have hlb := (excursion270_bundle m_a).2 19 [c1 + z1, 47, 25, 1] rest zl m' 1
              (1 + 2 * z1 + 2) 170 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
              (by omega) (by decide) (by omega) (by decide) (by omega)
              (by omega) (by omega) (by omega) (by omega)
            refine chainLeadsUpTo_trans hlb ?_
            intro m_b s_mid _ hex
            rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
            · exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                (Or.inr ⟨c1 + z1, phi, by omega, by omega, by omega, hb⟩)
            · exact amega_pop_step hb hphi38 (by omega) (by omega)
                (hS47.2.2 (c1 + z1 - 1) (by omega))
                (fun _ => hS47.2.2 (c1 + z1 - 2) (by omega))
                (fun hbig _ _ p1 p2 hvp _ =>
                  pop_47_25_1_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
                (fun _ _ m_c _ p1 p2 hvp _ => by
                  have hfp := fzOf_ge_40 hvp
                  have hox := ox_ge_of_c (c := c1 + z1 + 1) (k := y + 2) (fz := fzOf p1 p2)
                    (by omega) (by omega) (by omega) hfp
                  exact chainLeadsUpTo_trans
                    ((excursion270_bundle m_c).1 99 [47, 25, 1] p1 p2 (c1 + z1 + 1) (y + 2)
                      (by decide) hS47 (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                    (fun _ _ _ hex2 => exit_47_25_1_leads (by omega) (by omega) hex2))
                (fun _ _ _ _ p1 p2 hvp _ =>
                  x_47_25_1_high_leads (by omega) hvp (Or.inl ⟨by omega, rfl⟩))
          · have hg : stepGuards ⟨false, (z1, m' + 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) [47, 25, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            apply chainLeadsUpTo_step1 hg
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            have hbc : IsBounce (1 + 2 * z1 + 2) [c1 + z1, 47, 25, 1]
                ⟨true, (0, (m' - 4) + 1) :: rest, zl, 1 + 2 * z1 + 2, 0,
                  2 * (1 + 2 * z1) + 6, [c1 + z1, 47, 25, 1]⟩ := by
              have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := 1 + 2 * z1 + 2) (kb := 0) (mrg := 2 * (1 + 2 * z1) + 6)
                (rest := rest) (ds := [c1 + z1, 47, 25, 1]) hv_rest (by omega) (by
                  rcases dec_or (((m' - 4) + 1) % 2 = 1) with h1 | h1
                  · rw [if_pos h1]; omega
                  · rw [if_neg h1]; omega)
              simpa only [Nat.add_zero] using h
            exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
              (Or.inr ⟨c1 + z1, 1 + 2 * z1 + 2, by omega, by omega, by omega, hbc⟩)

lemma root1_advances {s : SegState} (hb0 : s.b = false) (hm0_z : s.mrg = 0) (hr : Root1 s) :
    ChainAdvances s RootInv270 := by
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb0 hm0_z
  subst hb0 hm0_z
  obtain ⟨hds, hvt, hc5, hk1, hkc, hfz20, hkz45, h25, h26⟩ := hr
  dsimp only at hds hvt hc5 hk1 hkc hfz20 hkz45 h25 h26
  subst hds
  have hS1 : SafeStack 25 [1] := safeStack_one
  rcases dec_or (c + fzOf segs zl = 25) with hcz25 | hcz_ne25
  · obtain ⟨m0, rest, hseg, rfl, rfl, hm0_6, hm0_odd⟩ := h25 hcz25
    subst hseg
    dsimp only [ValidTail40] at hvt
    obtain ⟨m', rfl⟩ : ∃ m', m0 = m' + 1 := ⟨m0 - 1, by omega⟩
    have hm_gt1 : ¬(m' + 1 = 1) := by omega
    have hphiw : GoodPhiW (5 + 20 - 1) [1] false = true := rfl
    have hpsi_cz : GoodPsi (5 + 20 - 1) [1] = true := rfl
    rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10) with hev_sm | hnot_ev
    · have hg : stepGuards ⟨false, (20, m' + 1) :: rest, zl, 5, 5, 0, [1]⟩ = true := by
        dsimp only [stepGuards]
        change (GoodPhiW (5 + 20 - 1) [1] false &&
          if m' + 1 = 1 then _ else GoodPsi (5 + 20 - 1) [1] &&
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then true else _) = true
        rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
        if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then _ else _) _
      rw [if_neg hm_gt1, if_pos hev_sm]
      have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hvt
      have hox := ox_ge_of_c (c := 5 + 2 * 20 + 4) (k := m' + 2) (fz := fzOf rest zl)
        (by decide) (by omega) (by omega) hfz1_40
      exact chainLeadsUpTo_trans
        ((excursion270_bundle N).1 55 [25, 1] rest zl (5 + 2 * 20 + 4) (m' + 2)
          (by decide) safeStack_25_1 (validTail40_of_validSegs40 hvt)
          (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun _ _ _ hex => exit270_d1_leads (by decide) (by omega) (by omega) (fun _ => by omega) hex)
    · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11) with hod_sm | hbig_m
      · have hg : stepGuards ⟨false, (20, m' + 1) :: rest, zl, 5, 5, 0, [1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (5 + 20 - 1) [1] false &&
            if m' + 1 = 1 then _ else GoodPsi (5 + 20 - 1) [1] &&
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then true else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then
                GoodDs [47, 25, 1] else true) = true
          rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
            if_neg hnot_ev, if_pos hod_sm]
          rfl
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
          if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then _ else
          if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then _ else _) _
        rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
        have hm_sub : m' + 1 - 1 = m' := by omega
        rw [hm_sub]
        obtain ⟨h102, h185⟩ := hm0_odd hod_sm.1
        rw [hm_sub] at h102
        exact stack_47_25_1_leads hvt (by omega) h102 h185
      · have hg : stepGuards ⟨false, (20, m' + 1) :: rest, zl, 5, 5, 0, [1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (5 + 20 - 1) [1] false &&
            if m' + 1 = 1 then _ else GoodPsi (5 + 20 - 1) [1] &&
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then true else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then _ else true) = true
          rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
            if_neg hnot_ev, if_neg hbig_m]
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
          if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then _ else
          if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then _ else _) _
        rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
        have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
          dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
        rw [hnorm]
        have hbc : IsBounce 47 [25, 1]
            ⟨true, (0, (m' - 4) + 1) :: rest, zl, 47, 0, 96, [25, 1]⟩ := by
          have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
            (cp1 := 47) (kb := 0) (mrg := 96)
            (rest := rest) (ds := [25, 1]) hvt (by decide) (by
              rcases dec_or (((m' - 4) + 1) % 2 = 1) with h1 | h1
              · rw [if_pos h1]; omega
              · rw [if_neg h1]; omega)
          simpa only [Nat.add_zero] using h
        exact bounce_d1_leads hbc (by decide) (by decide)
  · -- `26 <= c + fz`:
    have hcz26 : 26 ≤ c + fzOf segs zl := by omega
    have hkz47 : 47 ≤ k + 2 * fzOf segs zl := h26 hcz26
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz20 hcz26 hkz47
      have hg : stepGuards ⟨false, [], zl, c, k, 0, [1]⟩ = true := by
        dsimp only [stepGuards]
        have hpw : GoodPhiW (c + zl - 1) [1] false = true := by
          dsimp only [GoodPhiW]; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
          exact decide_eq_true (by omega)
        rw [hpw, Bool.true_and]
        dsimp only [GoodPsi]
        have hcz : c + zl - 1 + 1 = c + zl := by omega
        rw [hcz]; exact hS1.2.2 (c + zl) (by omega)
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 1]
          ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 1]⟩ := by
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 1]) (by omega)
      exact bounce_d1_leads hbc (by omega) (by omega)
    · dsimp only [fzOf, ValidTail40] at hvt hfz20 hcz26 hkz47
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        refine ⟨rfl, fun N => ?_⟩
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact bounce_one_leads (IsBounce.nil (by omega)) (by omega)
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
                2 * (c + z0) + 8, [1]⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step1 hg2
            dsimp only [stepSegs]
            exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hv_r2)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by intro h; omega) (fun _ => by omega))
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS1.2.2 (c + z0 + 3 + z1) (by omega)
                apply chainLeadsUpTo_step1 hg2
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_here (rootInv_of_D1 (by omega)
                  (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_one_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)) (by omega)
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step1 hg2
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by omega) (by omega) (by omega) (by omega)
                  (by intro h; omega) (fun _ => by omega))
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_one_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)) (by omega)
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + z0 - 1) [1] false = true := by
          dsimp only [GoodPhiW]; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
          exact decide_eq_true (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [1] false &&
              if 1 = 1 then GoodPsi (c + z0) [1] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS1.2.2 (c + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D1 (by omega)
            (validTail40_of_validSegs40 hv_rest)
            (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))
        · have hpsi_cz : GoodPsi (c + z0 - 1) [1] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
            rw [hcz_eq]; exact hS1.2.2 (c + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_here (rootInv_of_D1 (by omega)
              (validTail40_of_validSegs40 hv_rest)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 39 [c + z0, 1] := safeStack_d1 hcz26
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                      GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [1]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              have hne1_cz : ([c + z0, 1] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              exact chainLeadsUpTo_trans
                ((excursion270_bundle N).2 39 [c + z0, 1] rest zl m' 1
                  (k + 2 * z0 + 2) 43 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                  (by omega) (by decide) (by omega) (by decide) (by omega)
                  (by omega) (by omega) (by omega) (by omega))
                (fun _ _ _ hex => exit270_d1_leads (by omega) (by decide) (by decide)
                  (fun h25 => False.elim (by omega)) hex)
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 1]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, [c + z0, 1]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := [c + z0, 1]) hv_rest (by omega) (by
                    rcases dec_or (((m' - 4) + 1) % 2 = 1) with h1 | h1
                    · rw [if_pos h1]; omega
                    · rw [if_neg h1]; omega)
                simpa only [Nat.add_zero] using h
              exact bounce_d1_leads hbc (by omega) (by omega)


-- ============================================================================
-- Section 5g.3d: Root31, Root0, Global Root Advancement, and `inv_s0`
-- ============================================================================

lemma goodPhiW_31 {w : Nat} (hw : 15 ≤ w) : GoodPhiW w [3, 1] false = true := by
  dsimp only [GoodPhiW]
  rw [if_neg (by intro h; injection h with _ h2; cases h2),
      if_neg (by intro h; injection h with _ h2; cases h2),
      if_neg (by intro h; injection h with _ h2; cases h2),
      if_neg (by intro h; cases h)]
  change (if decide (3 ≥ 25) = true then _ else if false = true then _ else decide (w ≥ 15)) = true
  rw [if_neg (by decide), if_neg Bool.false_ne_true]
  exact decide_eq_true hw

lemma bounce_19_31_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [19, 3, 1] s) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [19, 3, 1] = true := by
    have hnrst : isDrainRstDs [19, 3, 1] = false := rfl
    have hnr0 : isRank0 [19, 3, 1] = false := rfl
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [19, 3, 1] =
      ⟨true, (0, 16) :: p.1, p.2, 2, 0, 6, [1]⟩ := rfl
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg_b1 : stepGuards ⟨true, (0, 16) :: p.1, p.2, 2, 0, 6, [1]⟩ = true := rfl
  have hs_b1 : stepSegs ⟨true, (0, 16) :: p.1, p.2, 2, 0, 6, [1]⟩ =
      ⟨true, (5, 8) :: p.1, p.2, 2, 0, 6, []⟩ := rfl
  apply chainLeadsUpTo_step hg_b1
  intro m2 _
  rw [hs_b1]
  have hg_b2 : stepGuards ⟨true, (5, 8) :: p.1, p.2, 2, 0, 6, []⟩ = true := rfl
  have hs_b2 : stepSegs ⟨true, (5, 8) :: p.1, p.2, 2, 0, 6, []⟩ =
      ⟨false, (9, 0) :: p.1, p.2, 1, 1, 0, []⟩ := rfl
  apply chainLeadsUpTo_step1 hg_b2
  rw [hs_b2]
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvp
    (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (by intro h; dsimp only [fzOf] at h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩)
    (by intro _ _ _ _ hcz9; dsimp only [fzOf] at hcz9; omega))

lemma bounce_cz_31_even_extra {N cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [cz, 3, 1] s)
    (hcases : (22 ≤ cz ∧ cz % 2 = 0 ∧ 49 ≤ phi) ∨
              (26 ≤ cz ∧ cz % 2 = 0 ∧ 45 ≤ phi)) :
    ChainLeadsUpTo N s RootInv270 := by
  have hcz22 : 22 ≤ cz := by rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hphi45 : 45 ≤ phi := by rcases hcases with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
  have hnrst : isDrainRstDs [cz, 3, 1] = false := rfl
  have hnr0 : isRank0 [cz, 3, 1] = false := by
    rcases cz with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [cz, 3, 1] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (cz ≥ 3 ∧ 3 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (cz % 2 = 0 ∧ cz ≤ 2 * 3 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (cz % 2 = 0 ∧ cz + 14 ≤ 2 * 3) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [cz, 3, 1] =
      ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h31, _, _⟩; cases h31)]
    have hnorm : normSeg 0 (cz - 3) = (0, cz - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg_b1 : stepGuards ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ = true := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b1 : stepSegs ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ =
      ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    have hm_eq : 0 + ((cz - 4) + 1) - (6 + 2) = (cz - 12) + 1 := by omega
    have h11 : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub, h11]; dsimp only [stepSegs]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step hg_b1
  intro m2 _
  rw [hs_b1]
  have hg_b2 : stepGuards ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b2 : stepSegs ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ =
      ⟨false, (8, cz - 19) :: p.1, p.2, 1, 1, 0, []⟩ := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    have hm_eq : 0 + ((cz - 12) + 1) - (6 + 2) = (cz - 20) + 1 := by omega
    have h19 : cz - 19 = (cz - 20) + 1 := by omega
    rw [hsub, h19]; dsimp only [stepSegs]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step1 hg_b2
  rw [hs_b2]
  apply chainLeadsUpTo_here
  refine rootInv_of_0B (Or.inl rfl) hvp
    (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
  intro z0 m0 r hseg _ _ _
  injection hseg with hhd htl
  injection hhd with hz0 hm0
  subst hz0 hm0 htl
  rcases hcases with ⟨_, _, hphi49⟩ | ⟨hcz26, hcz_ev, _⟩
  · exact ⟨by omega, by omega, fun hlt => False.elim (by omega)⟩
  · exact ⟨by omega, by omega, fun hlt => by omega⟩

lemma bounce_cz_31_ge25_leads {N cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [cz, 3, 1] s) (hcz25 : 25 ≤ cz) (hphi45 : 45 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  rcases dec_or (cz % 2 = 1) with hod | hev
  · exact bounce_cz_31_leads hb (Or.inr (Or.inl ⟨by omega, hod, by omega⟩))
  · exact bounce_cz_31_even_extra hb (Or.inr ⟨by omega, by omega, hphi45⟩)

lemma x_31_high_aux (d : Nat) :
    ∀ N x segs zl c k,
      23 ≤ x → x - 23 ≤ d →
      ValidSegs40 segs zl →
      40 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
      ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 3, 1]⟩ RootInv270 := by
  induction d with
  | zero =>
    intro N x segs zl c k hx23 hxd hv hc40 hk1 hkc
    have hx_eq : x = 23 := by omega
    subst hx_eq
    have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    obtain ⟨hox, hodw⟩ := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hS : SafeStack 19 [23, 3, 1] :=
      safeStack_cons_ne1 (by decide) safeStack_31 (by decide) (by decide)
    have hfb := (excursion270_bundle N).1 19 [23, 3, 1] segs zl c k (by decide) hS
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · exact bounce_cz_31_leads hb (Or.inr (Or.inl ⟨by decide, by decide, by omega⟩))
    · exact r9_pop_step hb hphi38 (by decide) (by omega)
        (fun m2 _ p1 p2 hvp _ => bounce_31_leads (isBounce_r9 (by decide) (by omega) hvp) (by decide))
  | succ d ih =>
    intro N x segs zl c k hx23 hxd hv hc40 hk1 hkc
    have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    obtain ⟨hox, hodw⟩ := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hS : SafeStack 19 [x, 3, 1] :=
      safeStack_cons_ne1 (by decide) safeStack_31 (by omega) (by omega)
    have hfb := (excursion270_bundle N).1 19 [x, 3, 1] segs zl c k (by decide) hS
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · rcases dec_or (x % 2 = 1) with hod | hev
      · exact bounce_cz_31_leads hb (Or.inr (Or.inl ⟨by omega, hod, by omega⟩))
      · exact bounce_cz_31_even_extra hb (Or.inl ⟨by omega, by omega, by omega⟩)
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (safeStack_31.2.2 (x - 1) (by omega))
        (fun _ => safeStack_31.2.2 (x - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          bounce_31_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
        (fun hy_le _ _ _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hvp)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
          intro z0 m0 r hseg _ _ _
          have hz0 : fzOf p1 p2 = z0 := by rw [hseg]; rfl
          exact Or.inr (by omega))
        (fun hy_le _ m2 _ p1 p2 hvp _ =>
          ih m2 (x - 1) p1 p2 y 1 (by omega) (by omega) hvp (by omega) (by decide) (by omega))

lemma x_31_high_leads {N x : Nat} {segs : List (Nat × Nat)} {zl c k : Nat}
    (hx20 : 20 ≤ x) (hv : ValidSegs40 segs zl)
    (hc40 : 40 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 3, 1]⟩ RootInv270 := by
  rcases dec_or (x ≤ 22) with hx22 | hx23
  · have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    obtain ⟨hox, hodw⟩ := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hS : SafeStack 39 [x, 3, 1] := safeStack_x_31 hx20 hx22
    have hfb := (excursion270_bundle N).1 39 [x, 3, 1] segs zl c k (by decide) hS
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · rcases dec_or (x = 22) with rfl | hx2021
      · exact bounce_cz_31_even_extra hb (Or.inl ⟨by decide, by decide, by omega⟩)
      · exact bounce_cz_31_leads hb (Or.inl ⟨by omega, by omega⟩)
    · exact r9_pop_step hb hphi38 (by omega) (by omega)
        (fun _ _ p1 p2 hvp _ => bounce_31_leads (isBounce_r9 (by omega) (by omega) hvp) (by omega))
  · exact x_31_high_aux (x - 23) N x segs zl c k (by omega) (Nat.le_refl _) hv hc40 hk1 hkc

lemma pop_z_cz_31_leads {N z cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [z, cz, 3, 1] s)
    (hz44 : 44 ≤ z) (hcz25 : 25 ≤ cz) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  exact amega_pop_step hb hphi38 (by omega) (by omega)
    (safeStack_31.2.2 (cz - 1) (by omega))
    (fun _ => safeStack_31.2.2 (cz - 2) (by omega))
    (fun hbig _ _ p1 p2 hvp _ =>
      bounce_31_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
    (fun _ _ _ _ p1 p2 hvp _ => by
      have hfp := fzOf_ge_40 hvp
      refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hvp)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
      intro z0 m0 r hseg _ _ _
      have hz0 : fzOf p1 p2 = z0 := by rw [hseg]; rfl
      exact Or.inr (by omega))
    (fun _ _ m2 _ p1 p2 hvp _ =>
      x_31_high_leads (by omega) hvp (by omega) (by decide) (by omega))

lemma loop_k1_gen {N x1 d3 : Nat} {ds3 : List Nat} {segs : List (Nat × Nat)} {zl c1 : Nat}
    {P : SegState → Prop}
    (hx_lo : 21 ≤ x1) (hx_hi : x1 ≤ 47)
    (hS1 : SafeStack 19 (x1 :: d3 :: ds3))
    (hg_x1_1 : GoodDs ((x1 - 1) :: d3 :: ds3) = true)
    (hg_x1_2 : GoodDs ((x1 - 2) :: d3 :: ds3) = true)
    (hv : ValidSegs40 segs zl) (hc1 : 2 ≤ c1)
    (h_top : ∀ m z phi, m ≤ N → (z = x1 ∨ z = x1 - 1) → 38 ≤ phi → ∀ s',
      IsBounce phi (z :: d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b1 : ∀ m, m < N → ∀ s', IsBounce (x1 - 1) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b2 : ∀ m, m < N → ∀ s', IsBounce (x1 - 2) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_r10 : ∀ m c' k' p1 p2, m < N → c' = x1 + 1 → 41 ≤ k' → k' ≤ 2 * c' + 3 →
      ValidSegs40 p1 p2 → ChainLeadsUpTo m ⟨false, p1, p2, c', k', 0, d3 :: ds3⟩ P) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, x1 :: d3 :: ds3⟩ P := by
  have hne1_1 : (x1 :: d3 :: ds3) ≠ [1] := by intro h; injection h with _ h2; cases h2
  have hb := fbound_k1_boost hne1_1 hS1 hv hc1 (N := N)
  refine chainLeadsUpTo_trans hb ?_
  intro m1 s_mid hm1 hex
  rcases hex with ⟨phi, hphi38, hsb⟩ | ⟨y1, phi1, hy1_39, hphi1_38, hyw1, hsb⟩
  · exact h_top m1 x1 phi hm1 (Or.inl rfl) hphi38 s_mid hsb
  · exact amega_pop_step hsb hphi1_38 (by omega) (by omega) hg_x1_1 (fun _ => hg_x1_2)
      (fun hbig m2 hm2 p1 p2 hvp _ =>
        h_b1 m2 (Nat.lt_of_lt_of_le hm2 hm1) _ (isBounce_r9 (by omega) hbig hvp))
      (fun _ _ m2 hm2 p1 p2 hvp _ =>
        h_r10 m2 (x1 + 1) (y1 + 2) p1 p2 (Nat.lt_of_lt_of_le hm2 hm1)
          rfl (by omega) (by omega) hvp)
      (fun hy1_le _ m2 hm2 p1 p2 hvp hfzp => by
        have hfp := fzOf_ge_40 hvp
        have hox99 := arith_boost_cz (c := y1) (fz := fzOf p1 p2) (cz_lo := 109) (ox_lo := 99)
          (by omega) hfp (by omega) (Or.inl ⟨rfl, rfl⟩)
        exact fbound_force_r9 (x := x1 - 1) (d3 := d3) (ds3 := ds3) (by omega)
          hg_x1_1 hg_x1_2 hvp (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun m3 phi2 hm3 hphi2 s' hb2 =>
            h_top m3 (x1 - 1) phi2 (Nat.le_trans hm3 (Nat.le_of_lt (Nat.lt_of_lt_of_le hm2 hm1)))
              (Or.inr rfl) (by omega) s' hb2)
          (fun m3 hm3 s' hb2 =>
            h_b2 m3 (Nat.lt_trans hm3 (Nat.lt_of_lt_of_le hm2 hm1)) s' hb2))

lemma step_m0_zero_31_advances {z0 zl c k : Nat} {rest : List (Nat × Nat)}
    (hv_rest : ValidSegs40 rest zl)
    (_hc : 2 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (hcz20 : 20 ≤ c + z0) :
    ChainAdvances ⟨false, (z0, 0) :: rest, zl, c, k, 0, [3, 1]⟩ RootInv270 := by
  refine ⟨rfl, fun N => ?_⟩
  dsimp only [stepSegs]
  rcases rest with _ | ⟨⟨z1, m1_seg⟩, r2⟩
  · have hzl230 : 230 ≤ zl := hv_rest.2
    exact bounce_31_leads (IsBounce.nil (by omega)) (by omega)
  · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
    have hv_r2 : ValidSegs40 r2 zl := validSegs40_tail hv_rest
    have hfz2_40 : 40 ≤ fzOf r2 zl := fzOf_ge_40 hv_r2
    cases m1_seg with
    | zero =>
      have hg2 : stepGuards ⟨true, (z1, 0) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
          2 * (c + z0) + 8, [3, 1]⟩ = true := by
        dsimp only [stepGuards]; exact decide_eq_true (by omega)
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hv_r2)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
      intro z2 m2 r3 hseg _ _ _
      have hz2 : fzOf r2 zl = z2 := by rw [hseg]; rfl
      exact Or.inr (by omega)
    | succ m1' =>
      rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
        | true =>
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, [3, 1]⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
            exact safeStack_31.2.2 (c + z0 + 3 + z1) (by omega)
          apply chainLeadsUpTo_step hg2
          intro m2 _
          dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
          exact x_31_high_leads (by omega) hv_r2 (by omega) (by decide) (by omega)
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_31_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)) (by omega)
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, [3, 1]⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hv_r2)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
          intro z2 m2 r3 hseg _ _ _
          have hz2 : fzOf r2 zl = z2 := by rw [hseg]; rfl
          exact Or.inr (by omega)
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_31_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)) (by omega)

lemma root31A_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root31A s) :
    ChainAdvances s RootInv270 := by
  obtain ⟨hds, hvt, hc, hk, hcases⟩ := hr
  rcases s with ⟨b, segs, zl, cp1, kb, mrg, ds⟩
  dsimp only at hb hmrg hds hvt hc hk hcases
  subst hb hmrg hds hc hk
  rcases hcases with hfz | hfz | ⟨rest, rfl⟩
  all_goals (try exact step_m0_zero_31_advances hvt (by decide) (by decide) (by decide) (by decide))
  all_goals
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz; omega
    · dsimp only [fzOf, ValidTail40] at hvt hfz
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        exact step_m0_zero_31_advances hv_rest (by decide) (by decide) (by decide) (by omega)
      | succ m' =>
        have hphiw : GoodPhiW (2 + z0 - 1) [3, 1] false = true := goodPhiW_31 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
              if 1 = 1 then GoodPsi (2 + z0) [3, 1] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact safeStack_31.2.2 (2 + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact x_31_high_leads (by omega) hv_rest (by omega) (by decide) (by omega)
        · have hpsi_cz : GoodPsi (2 + z0 - 1) [3, 1] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : 2 + z0 - 1 + 1 = 2 + z0 := by omega
            rw [hcz_eq]; exact safeStack_31.2.2 (2 + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (2 + z0 - 1) [3, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact x_31_high_leads (by omega) hv_rest (by omega) (by omega) (by omega)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 27 [2 + z0, 3, 1] := by
                rcases dec_or (z0 = 18) with rfl | hz19
                · exact safeStack_20_3_1
                · have hz_eq : z0 = 19 := by omega
                  subst hz_eq
                  exact safeStack_mono (by decide)
                    (safeStack_cons_ne1 (by decide) safeStack_31 (by decide) (by decide))
              have hne1_cz : ([2 + z0, 3, 1] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              have hS1 : SafeStack 19 [1 + 2 * z0 + 2, 2 + z0, 3, 1] :=
                safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (2 + z0 - 1) [3, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then
                      GoodDs ((1 + 2 * z0 + 2) :: (2 + z0) :: [3, 1]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (1 + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              refine loop_k1_gen (by omega) (by omega) hS1
                (hS_cz.2.2 (1 + 2 * z0 + 2 - 1) (by omega))
                (hS_cz.2.2 (1 + 2 * z0 + 2 - 2) (by omega))
                hv_rest (by omega) ?_ ?_ ?_ ?_
              · intro m1 z phi _ hz hphi38 s' hbz
                refine amega_pop_step hbz hphi38 (by omega) (by omega)
                  (safeStack_31.2.2 (2 + z0 - 1) (by omega))
                  (by intro hbad; omega)
                  (fun hbig => False.elim (by omega))
                  (fun _ _ _ _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
                    intro z2 m2 r3 hseg _ _ _
                    have hz2 : fzOf p1 p2 = z2 := by rw [hseg]; rfl
                    exact Or.inr (by omega))
                  (fun _ _ m2 _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    obtain ⟨hox, hodw⟩ := ox_ge_of_c (c := z) (k := 1) (fz := fzOf p1 p2)
                      (by omega) (by decide) (by omega) hfp
                    have hS45 : SafeStack 45 [2 + z0 - 1, 3, 1] :=
                      safeStack_of_gt2d2 (by decide) (by omega) (by omega)
                        (safeStack_31.2.2 (2 + z0 - 1) (by omega))
                    have hfb := (excursion270_bundle m2).1 45 [2 + z0 - 1, 3, 1] p1 p2 z 1
                      (by decide) hS45 (validTail40_of_validSegs40 hvp)
                      (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                    refine chainLeadsUpTo_trans hfb ?_
                    intro m3 s_m3 _ hex2
                    rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
                    · rcases dec_or (2 + z0 - 1 = 19) with h19 | h20
                      · rw [h19] at hb2; exact bounce_19_31_leads hb2 (by omega)
                      · exact bounce_cz_31_leads hb2 (Or.inl ⟨by omega, by omega⟩)
                    · exact r9_pop_step hb2 hphi2_38 (by omega) (by omega)
                        (fun _ _ q1 q2 hvq _ =>
                          bounce_31_leads (isBounce_r9 (by omega) (by omega) hvq) (by omega)))
              · intro m1 _ s' hb1
                exact bounce_cz_31_leads hb1 (Or.inl ⟨by omega, by omega⟩)
              · intro m1 _ s' hb2
                exact bounce_cz_31_leads hb2 (Or.inl ⟨by omega, by omega⟩)
              · intro m1 c' k' p1 p2 _ hc' hk'41 hk'c hvp
                subst hc'
                exact x_31_high_leads (by omega) hvp (by omega) (by omega) hk'c
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (2 + z0 - 1) [3, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (1 + 2 * z0 + 2) [2 + z0, 3, 1]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, 1 + 2 * z0 + 2, 0,
                    2 * (1 + 2 * z0) + 6, [2 + z0, 3, 1]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := 1 + 2 * z0 + 2) (kb := 0) (mrg := 2 * (1 + 2 * z0) + 6)
                  (rest := rest) (ds := [2 + z0, 3, 1]) hv_rest (by omega) (by
                    rcases dec_or (((m' - 4) + 1) % 2 = 1) with ho | he
                    · rw [if_pos ho]; omega
                    · rw [if_neg he]; omega)
                simpa only [Nat.add_zero] using h
              exact bounce_cz_31_leads hbc (Or.inl ⟨by omega, by omega⟩)

lemma root31B_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root31B s) :
    ChainAdvances s RootInv270 := by
  obtain ⟨hds, hvt, hc, hk1, hkc, hfz21, hcz25, hkz43, hod_inv⟩ := hr
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb hmrg hds hvt hc hk1 hkc hfz21 hcz25 hkz43 hod_inv
  subst hb hmrg hds
  rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
  · dsimp only [fzOf, ValidTail40] at hvt hfz21 hcz25 hkz43
    have hg : stepGuards ⟨false, [], zl, c, k, 0, [3, 1]⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_31 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c + zl - 1 + 1 = c + zl := by omega
      rw [hcz]; exact safeStack_31.2.2 (c + zl) (by omega)
    refine ⟨hg, fun N => ?_⟩
    dsimp only [stepSegs]
    have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 3, 1]
        ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 3, 1]⟩ := by
      simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2)
        (kb := 0) (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 3, 1]) (by omega)
    exact bounce_cz_31_ge25_leads hbc (by omega) (by omega)
  · dsimp only [fzOf, ValidTail40] at hvt hfz21 hcz25 hkz43
    have hv_rest : ValidSegs40 rest zl := hvt
    cases m0 with
    | zero =>
      exact step_m0_zero_31_advances hv_rest hc hk1 hkc (by omega)
    | succ m' =>
      have hphiw : GoodPhiW (c + z0 - 1) [3, 1] false = true := goodPhiW_31 (by omega)
      rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c + z0 - 1) [3, 1] false &&
            if 1 = 1 then GoodPsi (c + z0) [3, 1] else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact safeStack_31.2.2 (c + z0 + 1) (by omega)
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        exact x_31_high_leads (by omega) hv_rest (by omega) (by decide) (by omega)
      · have hpsi_cz : GoodPsi (c + z0 - 1) [3, 1] = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
          rw [hcz_eq]; exact safeStack_31.2.2 (c + z0) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [3, 1] false &&
              if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [3, 1] &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          exact x_31_high_leads (by omega) hv_rest (by omega) (by omega) (by omega)
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 19 [c + z0, 3, 1] :=
              safeStack_cons_ne1 (by decide) safeStack_31 (by omega) (by omega)
            have hne1_cz : ([c + z0, 3, 1] : List Nat) ≠ [1] := by
              intro h; injection h with _ h2; cases h2
            have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [3, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [3, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                    GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [3, 1]) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            set x1 := k + 2 * z0 + 2
            rcases dec_or (x1 ≤ 47) with hx47 | hx48
            · refine loop_k1_le47 hne1_cz (safeStack_mono (by decide) hS_cz)
                (Or.inl (by omega)) hx47 hv_rest (by omega)
                (fun m1 z phi _ hz hphi38 _ hbz =>
                  pop_z_cz_31_leads hbz (by omega) hcz25 hphi38)
                ?_ ?_
                (fun m1 c' k' p1 p2 _ hc' hk'41 hk'c hvp => by
                  subst hc'
                  exact x_31_high_leads (by omega) hvp (by omega) (by omega) hk'c)
              · intro m1 _ s' hb1
                rcases dec_or ((c + z0) % 2 = 1) with hcz_od | hcz_ev
                · exact bounce_cz_31_leads hb1 (Or.inr (Or.inl ⟨by omega, hcz_od, by omega⟩))
                · have h_ev := hod_inv z0 (m' + 1) rest rfl (by omega) (by omega) hod_sm.1
                  rcases h_ev with ⟨rfl, rfl, rfl⟩ | h47
                  · exact bounce_cz_31_even_extra hb1 (Or.inr ⟨by decide, by decide, by omega⟩)
                  · omega
              · intro m1 _ s' hb2
                rcases dec_or ((c + z0) % 2 = 1) with hcz_od | hcz_ev
                · exact bounce_cz_31_leads hb2 (Or.inr (Or.inl ⟨by omega, hcz_od, by omega⟩))
                · have h_ev := hod_inv z0 (m' + 1) rest rfl (by omega) (by omega) hod_sm.1
                  rcases h_ev with ⟨rfl, rfl, rfl⟩ | h47
                  · exact bounce_cz_31_even_extra hb2 (Or.inr ⟨by decide, by decide, by omega⟩)
                  · omega
            · rcases dec_or (x1 ≤ 50) with hx50 | hx51
              · have hS_x1 : SafeStack 19 [x1, c + z0, 3, 1] :=
                  safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
                have hne1_x1 : ([x1, c + z0, 3, 1] : List Nat) ≠ [1] := by
                  intro h; injection h with _ h2; cases h2
                refine chainLeadsUpTo_trans (fbound_k1_boost hne1_x1 hS_x1 hv_rest (by omega)) ?_
                intro m1 s_m1 hm1 hex1
                rcases hex1 with ⟨phi1, hphi1, hb1⟩ | ⟨y1, phi1, hy1, hphi1_38, hyw1, hb1⟩
                · exact pop_z_cz_31_leads hb1 (by omega) hcz25 hphi1
                · exact amega_pop_step hb1 hphi1_38 (by omega) (by omega)
                    (hS_cz.2.2 (x1 - 1) (by omega)) (fun _ => hS_cz.2.2 (x1 - 2) (by omega))
                    (fun hbig _ _ p1 p2 hvp _ =>
                      bounce_cz_31_ge25_leads (isBounce_r9 (by omega) hbig hvp) hcz25 (by omega))
                    (fun _ _ _ _ p1 p2 hvp _ =>
                      x_31_high_leads (by omega) hvp (by omega) (by omega) (by omega))
                    (fun hy1_le _ m2 _ p1 p2 hvp hfzp => by
                      have hfp := fzOf_ge_40 hvp
                      have hox99 := arith_boost_cz (c := y1) (fz := fzOf p1 p2)
                        (cz_lo := 109) (ox_lo := 99) (by omega) hfp (by omega) (Or.inl ⟨rfl, rfl⟩)
                      have hS_x1' : SafeStack 19 [x1 - 1, c + z0, 3, 1] :=
                        safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
                      have hfb2 := (excursion270_bundle m2).1 19 [x1 - 1, c + z0, 3, 1] p1 p2 y1 1
                        (by decide) hS_x1' (validTail40_of_validSegs40 hvp)
                        (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                      refine chainLeadsUpTo_trans hfb2 ?_
                      intro m3 s_m3 _ hex2
                      rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
                      · have hp2 : 38 ≤ phi2 := by dsimp only [odw] at hphi2; omega
                        exact pop_z_cz_31_leads hb2 (by omega) hcz25 hp2
                      · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
                          (hS_cz.2.2 (x1 - 2) (by omega)) (fun _ => hS_cz.2.2 (x1 - 3) (by omega))
                          (fun hbig _ _ q1 q2 hvq _ =>
                            bounce_cz_31_ge25_leads (isBounce_r9 (by omega) hbig hvq) hcz25 (by omega))
                          (fun _ _ _ _ q1 q2 hvq _ =>
                            x_31_high_leads (by omega) hvq (by omega) (by omega) (by omega))
                          (fun hy2_le _ m4 _ q1 q2 hvq _ => by
                            have hfq := fzOf_ge_40 hvq
                            obtain ⟨hox_q, _⟩ := ox_ge_of_c (c := y2) (k := 1) (fz := fzOf q1 q2)
                              (by omega) (by decide) (by omega) hfq
                            exact fbound_force_r9 (x := x1 - 2) (d3 := c + z0) (ds3 := [3, 1])
                              (by omega) (hS_cz.2.2 (x1 - 2) (by omega))
                              (hS_cz.2.2 (x1 - 3) (by omega)) hvq
                              (by omega) (by decide) (by omega) (by omega) (by omega)
                              (fun _ phi3 _ hphi3 _ hb3 =>
                                pop_z_cz_31_leads hb3 (by omega) hcz25 (by omega))
                              (fun _ _ _ hb3 =>
                                bounce_cz_31_ge25_leads hb3 hcz25 (by omega))))
              · have hfz_r : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
                exact chainLeadsUpTo_trans
                  ((excursion270_bundle N).2 19 [c + z0, 3, 1] rest zl m' 1 x1 46 0
                    (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                    (by omega) (by decide) (by omega) (by decide) (by omega)
                    (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ hex => by
                    rcases hex with ⟨phi, hphi, hb⟩ | ⟨z, phi, hz, hphi38, _, hb⟩
                    · exact bounce_cz_31_ge25_leads hb hcz25 hphi
                    · exact pop_z_cz_31_leads hb (by omega) hcz25 hphi38)
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [3, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [3, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 3, 1]
                ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                  2 * (k + 2 * z0) + 6, [c + z0, 3, 1]⟩ := by
              have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                (rest := rest) (ds := [c + z0, 3, 1]) hv_rest (by omega) (by
                  rcases dec_or (((m' - 4) + 1) % 2 = 1) with ho | he
                  · rw [if_pos ho]; omega
                  · rw [if_neg he]; omega)
              simpa only [Nat.add_zero] using h
            exact bounce_cz_31_ge25_leads hbc hcz25 (by omega)

lemma root31_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root31 s) :
    ChainAdvances s RootInv270 := by
  rcases hr with ha | hb31
  · exact root31A_advances hb hmrg ha
  · exact root31B_advances hb hmrg hb31

-- ============================================================================
-- Helpers & Advancement Closure for `Root0` (`Root0A` and `Root0B`)
-- ============================================================================

lemma goodPhiW_0 {w : Nat} {ds : List Nat} (hds : ds = [] ∨ ds = [0]) (hw : 6 ≤ w) :
    GoodPhiW w ds false = true := by
  rcases hds with rfl | rfl
  · dsimp only [GoodPhiW]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl, Bool.false_or]
    exact decide_eq_true hw
  · dsimp only [GoodPhiW]
    rw [if_neg (by decide), if_pos rfl]
    exact decide_eq_true hw

lemma goodPsi_0 {w : Nat} {ds : List Nat} (hds : ds = [] ∨ ds = [0]) (hw : 7 ≤ w) :
    GoodPsi w ds = true := by
  rcases hds with rfl | rfl
  · dsimp only [GoodPsi, GoodDs, GoodDsAux, GoodDs1]
    exact decide_eq_true (by omega)
  · dsimp only [GoodPsi, GoodDs, GoodDsAux, GoodDs2]
    rw [if_pos rfl]
    exact decide_eq_true (by omega)

lemma safeStack_0 {ds : List Nat} (hds : ds = [] ∨ ds = [0]) : SafeStack 19 ds := by
  rcases hds with rfl | rfl
  · exact safeStack_nil
  · exact safeStack_zero

lemma safeStack19_d_ds {d : Nat} {ds : List Nat} (hd10 : 10 ≤ d) (hds : ds = [] ∨ ds = [0]) :
    SafeStack 19 (d :: ds) := by
  rcases hds with rfl | rfl
  · refine ⟨(by intro h; injection h with h1; omega), (safeStack_d (by omega)).2.1, ?_⟩
    intro u hu
    dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDs1 d = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg1 : GoodDs1 (d - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg2 : GoodDs1 (d - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    rw [hu19, hu17, hgd, hg1, hg2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
  · refine ⟨(by intro h; injection h with _ h2; cases h2), (safeStack_d0 (by omega)).2.1, ?_⟩
    intro u hu
    dsimp only [GoodDs]
    rw [GoodDsAux.eq_3, if_neg (by omega)]
    have h1 : decide (d = 3 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
      decide_eq_false (by omega)
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have h3 : decide (d ≥ 25 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false :=
      decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDsAux d [0] = true := (safeStack_d0 (by omega)).2.1
    have hg1 : GoodDsAux (d - 1) [0] = true := (safeStack_d0 (by omega)).2.1
    have hg2 : GoodDsAux (d - 2) [0] = true := (safeStack_d0 (by omega)).2.1
    rw [h1, hu19, h3, hu17, hgd, hg1, hg2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

lemma bounce_0_leads {N phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi ds s) (hds : ds = [] ∨ ds = [0]) (hphi : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  rcases hds with rfl | rfl
  · exact bounce_nil_leads hb (by omega)
  · exact bounce_zero_leads hb hphi

lemma step_m0_zero_0_advances {z0 zl c k : Nat} {rest : List (Nat × Nat)} {ds : List Nat}
    (hds : ds = [] ∨ ds = [0]) (hv_rest : ValidSegs40 rest zl)
    (_hc : 1 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (hcz8 : 8 ≤ c + z0) :
    ChainAdvances ⟨false, (z0, 0) :: rest, zl, c, k, 0, ds⟩ RootInv270 := by
  refine ⟨rfl, fun N => ?_⟩
  dsimp only [stepSegs]
  rcases rest with _ | ⟨⟨z1, m1_seg⟩, r2⟩
  · have hzl230 : 230 ≤ zl := hv_rest.2
    exact bounce_0_leads (IsBounce.nil (by omega)) hds (by omega)
  · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
    have hv_r2 : ValidSegs40 r2 zl := validSegs40_tail hv_rest
    have hfz2_40 : 40 ≤ fzOf r2 zl := fzOf_ge_40 hv_r2
    cases m1_seg with
    | zero =>
      have hg2 : stepGuards ⟨true, (z1, 0) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
          2 * (c + z0) + 8, ds⟩ = true := by
        dsimp only [stepGuards]; exact decide_eq_true (by omega)
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hv_r2)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    | succ m1' =>
      rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
        | true =>
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, ds⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
            exact (safeStack_0 hds).2.2 (c + z0 + 3 + z1) (by omega)
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
          have hds_d : ((c + z0 + 3 + z1) :: ds) = [c + z0 + 3 + z1] ∨
              ((c + z0 + 3 + z1) :: ds) = [c + z0 + 3 + z1, 0] := by
            rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0 + 3 + z1) (by omega) hds_d
            (validTail40_of_validSegs40 hv_r2) (by omega) (by decide) (by omega)
            (by omega) (by omega) (by omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_0_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)) hds (by omega)
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, ds⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hv_r2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_0_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)) hds (by omega)

lemma pop_17_8_0_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [17, 8, 0] s) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi [17, 8, 0] = true := by
    have hnrst : isDrainRstDs [17, 8, 0] = false := rfl
    have hnr0 : isRank0 [17, 8, 0] = false := rfl
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [17, 8, 0] =
      ⟨true, (0, 14) :: p.1, p.2, 7, 0, 16, [0]⟩ := rfl
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg2 : stepGuards ⟨true, (0, 14) :: p.1, p.2, 7, 0, 16, [0]⟩ = true := rfl
  have hs2 : stepSegs ⟨true, (0, 14) :: p.1, p.2, 7, 0, 16, [0]⟩ =
      ⟨false, p.1, p.2, 9, 19, 0, [0]⟩ := rfl
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inr rfl) (validTail40_of_validSegs40 hvp)
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))

lemma pop_y_17_8_0_leads {N y phi : Nat} {s : SegState}
    (hb : IsBounce phi [y, 17, 8, 0] s) (hy43 : 43 ≤ y) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hnrst : isDrainRstDs [y, 17, 8, 0] = false := rfl
  have hnr0 : isRank0 [y, 17, 8, 0] = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [y, 17, 8, 0] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ 17 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (y % 2 = 0 ∧ y ≤ 2 * 17 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * 17) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [y, 17, 8, 0] =
      ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 16, 0, 34, [8, 0]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h17, _, _⟩; cases h17)]
    have hnorm : normSeg 0 (y - 3) = (0, (y - 4) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hbc : IsBounce 16 [8, 0] ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 16, 0, 34, [8, 0]⟩ := by
    have h := IsBounce.cons (z0 := 0) (m := y - 4) (zl := p.2) (cp1 := 16) (kb := 0) (mrg := 34)
      (rest := p.1) (ds := [8, 0]) hvp (by omega) (by
        rcases dec_or (((y - 4) + 1) % 2 = 1) with ho | he
        · rw [if_pos ho]; omega
        · rw [if_neg he]; omega)
    simpa only [Nat.add_zero] using h
  exact bounce_d_leads hbc (Or.inr rfl) (Or.inl ⟨rfl, Or.inl rfl⟩)

lemma pop_19_9_leads {N phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi (19 :: 9 :: ds) s) (hds : ds = [] ∨ ds = [0]) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hg_pop : drainPopGuards phi (19 :: 9 :: ds) = true := by
    have hnrst : isDrainRstDs (19 :: 9 :: ds) = false := rfl
    have hnr0 : isRank0 (19 :: 9 :: ds) = false := rfl
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rcases hds with rfl | rfl <;> (rw [hc4]; rfl)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (19 :: 9 :: ds) =
      ⟨true, (0, 16) :: p.1, p.2, 8, 0, 18, ds⟩ := by
    rcases hds with rfl | rfl <;> rfl
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg2 : stepGuards ⟨true, (0, 16) :: p.1, p.2, 8, 0, 18, ds⟩ = true := rfl
  have hs2 : stepSegs ⟨true, (0, 16) :: p.1, p.2, 8, 0, 18, ds⟩ =
      ⟨false, p.1, p.2, 10, 21, 0, ds⟩ := rfl
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hvp)
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))

lemma pop_y_19_9_leads {N y phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi (y :: 19 :: 9 :: ds) s)
    (hds : ds = [] ∨ ds = [0])
    (hy49 : 49 ≤ y)
    (hphi_cases : (53 ≤ y ∧ 90 ≤ phi) ∨ 100 ≤ phi ∨ (53 ≤ y ∧ y % 2 = 1 ∧ 88 ≤ phi)) :
    ChainLeadsUpTo N s RootInv270 := by
  have hphi88 : 88 ≤ phi := by
    rcases hphi_cases with ⟨_, h⟩ | h | ⟨_, _, h⟩ <;> omega
  refine r9_pop_step hb (by omega) (by decide) (by omega) ?_
  intro m1 _ p0_1 p0_2 hvp0 hfzp0
  have hy_sub : y - 3 = (y - 4) + 1 := by omega
  have hg_pop9 : drainPopGuards (18 + 0) (9 :: ds) = true := by
    rcases hds with rfl | rfl <;> rfl
  have hg2 : stepGuards ⟨true, (0, y - 3) :: p0_1, p0_2, 18, 0, 38, 9 :: ds⟩ = true := by
    rw [hy_sub]; dsimp only [stepGuards]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; exact hg_pop9
    · rw [if_neg hev, decide_eq_false (by omega)]; exact hg_pop9
  have hs2 : stepSegs ⟨true, (0, y - 3) :: p0_1, p0_2, 18, 0, 38, 9 :: ds⟩ =
      ⟨true, (1, 0) :: (20, y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ := by
    have hm_eq : 0 + ((y - 4) + 1) - (38 + 2) = y - 43 := by omega
    have hn20 : normSeg 20 (y - 43) = (20, y - 43) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    have hdp9 : drainPopStep true (18 + 0) (y - 43) p0_1 p0_2 (9 :: ds) =
        ⟨true, (1, 0) :: normSeg 20 (y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ := by
      rcases hds with rfl | rfl <;> rfl
    rw [hy_sub]; dsimp only [stepSegs]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp9, hn20]
    · rw [if_neg hev, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp9, hn20]
  apply chainLeadsUpTo_step hg2
  intro m2 _
  rw [hs2]
  have hg3 : stepGuards ⟨true, (1, 0) :: (20, y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ = true := rfl
  have hs3 : stepSegs ⟨true, (1, 0) :: (20, y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ =
      ⟨false, (20, y - 43) :: p0_1, p0_2, 5, 5, 0, [1]⟩ := rfl
  apply chainLeadsUpTo_step1 hg3
  rw [hs3]
  apply chainLeadsUpTo_here
  refine rootInv_of_1 hvp0 (by decide) (by decide) (by decide)
    (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (fun _ => ⟨y - 43, p0_1, rfl, rfl, rfl, by omega, ?_⟩)
    (by intro h; dsimp only [fzOf] at h; omega)
  intro hm0_od
  rcases hphi_cases with ⟨hy53, hphi90⟩ | hphi100 | ⟨_, hy_od, _⟩ <;> omega

lemma pop_y_d_leads {N d y phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi (y :: d :: ds) s)
    (hd10 : 10 ≤ d) (hds : ds = [] ∨ ds = [0])
    (hy20 : 20 ≤ y) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv270 := by
  have hSd : SafeStack 19 (d :: ds) := safeStack19_d_ds hd10 hds
  have hg1 : GoodDs ((d - 1) :: ds) = true := by
    rcases hds with rfl | rfl
    · exact (safeStack_d (by omega)).2.1
    · exact (safeStack_d0 (by omega)).2.1
  have hg2 : GoodDs ((d - 2) :: ds) = true := by
    rcases hds with rfl | rfl
    · exact (safeStack_d (by omega)).2.1
    · exact (safeStack_d0 (by omega)).2.1
  have hnrst : isDrainRstDs (y :: d :: ds) = false := by
    cases d with | zero => omega | succ _ => rfl
  have hnr0 : isRank0 (y :: d :: ds) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi (y :: d :: ds) = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ d ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : (!decide (y % 2 = 0 ∧ y ≤ 2 * d + 4) || GoodDs ((d - 1) :: ds)) = true := by
      rw [hg1, Bool.or_true]
    have hc3 : (!decide (y % 2 = 0 ∧ y + 14 ≤ 2 * d) || GoodDs ((d - 2) :: ds)) = true := by
      rw [hg2, Bool.or_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (y :: d :: ds) =
      ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  rcases dec_or (2 * d + 5 ≤ y) with hbig | hsm
  · rcases hds with rfl | rfl
    · have hy_sub : y - 3 = (y - 4) + 1 := by omega
      have hpop_nil : drainPopGuards (d - 1 + 0) [] = true := by
        change decide (d - 1 + 0 ≥ 2) = true; exact decide_eq_true (by omega)
      have hg_s2 : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, []⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]
        rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
        · rw [if_pos hod, decide_eq_false (by omega)]; exact hpop_nil
        · rw [if_neg hev, decide_eq_false (by omega)]; exact hpop_nil
      apply chainLeadsUpTo_step1 hg_s2
      rw [hy_sub]; dsimp only [stepSegs]
      set q := pushSeg true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      have hvtq : ValidTail40 q.1 q.2 :=
        validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
      have hfzq : d - 1 + 0 + 1 ≤ fzOf q.1 q.2 :=
        fzOf_pushSeg_ge true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv270
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
      · rw [if_neg hev, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv270
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · exact bounce_r9_zero_leads (by omega) hbig hvp
  · have hy_sub : y - 3 = (y - 4) + 1 := by omega
    rcases dec_or (y % 2 = 1) with hy_od | hy_ev
    · have hm_ev : ¬(((y - 4) + 1) % 2 = 1) := by omega
      have hmrg : decide (2 * d ≥ 0 + ((y - 4) + 1)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]; rw [if_neg hm_ev, hmrg, if_pos rfl]
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ =
          ⟨false, p.1, p.2, d + 1, y + 2, 0, ds⟩ := by
        rw [hy_sub]; dsimp only [stepSegs]; rw [if_neg hm_ev, hmrg, if_pos rfl]
        have hc_eq : d - 1 + 0 + 2 = d + 1 := by omega
        have hk_eq : 0 + (y - 4 + 1) + 2 * 0 + 5 = y + 2 := by omega
        rw [hc_eq, hk_eq]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hvp)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    · have hm_od : ((y - 4) + 1) % 2 = 1 := by omega
      have hmrg : decide (2 * d ≥ 0 + (y - 4)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]; rw [if_pos hm_od, hmrg, if_pos rfl]
        simpa only [Nat.add_zero] using hg1
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ =
          ⟨false, p.1, p.2, y, 1, 0, (d - 1) :: ds⟩ := by
        rw [hy_sub]; dsimp only [stepSegs]; rw [if_pos hm_od, hmrg, if_pos rfl]
        have hc_eq : 0 + (y - 4) + 2 * 0 + 4 = y := by omega
        have hd_eq : d - 1 + 0 = d - 1 := by omega
        rw [hc_eq, hd_eq]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      have hds_d1 : ((d - 1) :: ds) = [d - 1] ∨ ((d - 1) :: ds) = [d - 1, 0] := by
        rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact chainLeadsUpTo_here (rootInv_of_D (d := d - 1) (by omega) hds_d1
        (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
        (by omega) (by omega) (by omega))

lemma root0A_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root0A s) :
    ChainAdvances s RootInv270 := by
  obtain ⟨hds, hc, hk, z1, m0, m1, rest, hsegs, hm0, hz1, hv⟩ := hr
  rcases s with ⟨b, segs, zl, cp1, kb, mrg, ds⟩
  dsimp only at hb hmrg hds hc hk hsegs hm0 hz1 hv
  subst hb hmrg hds hc hk hsegs
  rcases hm0 with rfl | rfl
  · refine ⟨rfl, fun _ => ?_⟩
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_D (d := 10) (by decide) (Or.inl rfl) hv
      (by decide) (by decide) (by decide)
      (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega))
  · refine ⟨rfl, fun _ => ?_⟩
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_D (d := 9) (by decide) (Or.inl rfl) hv
      (by decide) (by decide) (by decide)
      (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega))

lemma root0B_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root0B s) :
    ChainAdvances s RootInv270 := by
  obtain ⟨hds, hvt, hc, hk1, hkc, hfz7, hcz8, h8, h39, h9⟩ := hr
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb hmrg hds hvt hc hk1 hkc hfz7 hcz8 h8 h39 h9
  subst hb hmrg
  rcases dec_or (39 ≤ fzOf segs zl ∧ 42 ≤ c + fzOf segs zl) with ⟨hfz39, hcz42⟩ | hlow
  · have hS0 : SafeStack 19 ds := safeStack_0 hds
    obtain ⟨hox39, _⟩ := ox_bounds_relaxed hc hk1 hkc (by omega) hcz42 (by omega)
    refine chainAdvances_trans
      (fbound_advances (by decide) hS0 hvt hc hk1 hkc (by omega) hcz42 (by omega) (by omega)) ?_
    intro s' hex N
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · exact bounce_0_leads hb hds (by dsimp only [odw] at hphi; omega)
    · have hds_y : (y :: ds) = [y] ∨ (y :: ds) = [y, 0] := by
        rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact bounce_d_leads hb hds_y (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hphi38⟩))))
  · rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hlow; omega
    · dsimp only [fzOf, ValidTail40] at hvt hfz7 hcz8 h39 hlow
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        exact step_m0_zero_0_advances hds hv_rest hc hk1 hkc hcz8
      | succ m' =>
        have hphiw : GoodPhiW (c + z0 - 1) ds false = true := goodPhiW_0 hds (by omega)
        have hds_cz : ((c + z0) :: ds) = [c + z0] ∨ ((c + z0) :: ds) = [c + z0, 0] := by
          rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
        have hds_cz1 : ((c + z0 + 1) :: ds) = [c + z0 + 1] ∨ ((c + z0 + 1) :: ds) = [c + z0 + 1, 0] := by
          rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
        have hfz_r : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, ds⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) ds false && if 1 = 1 then GoodPsi (c + z0) ds else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact goodPsi_0 hds (by omega)
          refine ⟨hg, fun _ => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo _ (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0 + 1) (by omega) hds_cz1
            (validTail40_of_validSegs40 hv_rest) (by omega) (by decide) (by omega)
            (by omega) (by omega) (by omega))
        · have hpsi_cz : GoodPsi (c + z0 - 1) ds = true := goodPsi_0 hds (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, ds⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) ds false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) ds &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun _ => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo _ (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0) (by omega) hds_cz
              (validTail40_of_validSegs40 hv_rest) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega))
          · -- Helper for `bounce_d_leads` at `phi >= k + 2 * z0` on `(c + z0) :: ds` when `10 <= c + z0`:
            have h_bounce_cz : 10 ≤ c + z0 → ∀ phi, k + 2 * z0 ≤ phi →
                (c + z0 = 8 ∧ (phi = 16 ∨ phi = 17 ∨ 38 ≤ phi)) ∨
                (c + z0 = 9 ∧ 19 ≤ phi) ∨
                (10 ≤ c + z0 ∧ c + z0 ≤ 18 ∧ 19 ≤ phi ∧ (12 ≤ c + z0 → (c + z0) % 2 = 0 → 23 ≤ phi)) ∨
                (c + z0 = 19 ∧ 37 ≤ phi) ∨
                (20 ≤ c + z0 ∧ 38 ≤ phi) := by
              intro hd10 phi hphi_kz
              rcases dec_or (39 ≤ z0) with hz39 | hz_lt39
              · rcases dec_or (c + z0 ≤ 18) with h18 | h19
                · omega
                · rcases dec_or (c + z0 = 19) with h_eq19 | h20
                  · omega
                  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
              · rcases h39 (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hz20⟩
                · rcases dec_or (1 + z0 ≤ 18) with h_le18 | h_ge19
                  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h_le18, by omega,
                      fun _ _ => by omega⟩))
                  · rcases dec_or (1 + z0 = 19) with h_eq19 | h_ge20
                    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h_eq19, by omega⟩)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
            rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · rcases dec_or (c + z0 = 8) with hcz_eq8 | hcz_ge9
              · obtain ⟨m0_, rest_, hseg_eq, rfl, rfl, rfl, hfz44⟩ := h8 hcz_eq8
                injection hseg_eq with hhd htl
                injection hhd with hz0_eq _
                subst hz0_eq htl
                clear h8 h9 h39
                have hg : stepGuards ⟨false, (7, m' + 1) :: rest, zl, 1, 1, 0, [0]⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW 7 [0] false &&
                    if m' + 1 = 1 then _ else GoodPsi 7 [0] &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 40 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 41 then
                        GoodDs [17, 8, 0] else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_pos hod_sm]
                  rfl
                refine ⟨hg, fun N => ?_⟩
                dsimp only [stepSegs]
                change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 40 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 41 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                have hm_sub : m' + 1 - 1 = m' := by omega
                rw [hm_sub]
                have hox43 : 43 ≤ ox (1 + 2 * fzOf rest zl) (m' + fzOf rest zl) ∧
                    42 ≤ odw (1 + 2 * fzOf rest zl) (m' + fzOf rest zl) := by
                  obtain ⟨q, r, hr_lt, heq, hox_eq⟩ :=
                    ox_spec_lt (kz := 1 + 2 * fzOf rest zl) (cz := m' + fzOf rest zl) (by omega)
                  dsimp only [odw]
                  rw [hox_eq]
                  omega
                have hfb := (excursion270_bundle N).1 39 [17, 8, 0] rest zl m' 1
                  (by decide) safeStack_17_8_0 (validTail40_of_validSegs40 hv_rest)
                  (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                refine chainLeadsUpTo_trans hfb ?_
                intro m1 s_mid _ hex
                rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
                · exact pop_17_8_0_leads hb (by omega)
                · exact pop_y_17_8_0_leads hb (by omega) hphi38
              · clear h8
                rcases dec_or (c + z0 = 9) with hcz_eq9 | hcz_ge10
                · have hck1 : c = 1 ∧ k = 1 := by
                    rcases h39 (by clear h9; omega) with h | ⟨_, _, hz20⟩
                    · exact h
                    · clear h9 h39; omega
                  rcases hck1 with ⟨rfl, rfl⟩
                  clear h39
                  have hz8 : z0 = 8 := by clear h9; omega
                  subst hz8
                  have hm'2 : 2 ≤ m' := by clear h9; have := hod_sm.1; omega
                  have hm'3 : 3 ≤ m' + 1 := Nat.succ_le_succ hm'2
                  have h9_props := h9 8 (m' + 1) rest rfl hcz_eq9 hm'3 hod_sm.1
                  clear h9
                  have hm_sub : m' + 1 - 1 = m' := by omega
                  rw [hm_sub] at h9_props
                  have hS_19 : SafeStack 43 (19 :: 9 :: ds) := by
                    rcases hds with rfl | rfl
                    · exact safeStack_19_9
                    · exact safeStack_19_9_0
                  have hg : stepGuards ⟨false, (8, m' + 1) :: rest, zl, 1, 1, 0, ds⟩ = true := by
                    dsimp only [stepGuards]
                    change (GoodPhiW 8 ds false &&
                      if m' + 1 = 1 then _ else GoodPsi 8 ds &&
                        if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 44 then true else
                        if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 45 then
                          GoodDs (19 :: 9 :: ds) else true) = true
                    rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                      if_neg hnot_ev, if_pos hod_sm]
                    exact hS_19.2.1
                  refine ⟨hg, fun N => ?_⟩
                  dsimp only [stepSegs]
                  change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 44 then _ else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 45 then _ else _) _
                  rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm, hm_sub]
                  have hne1_19 : (19 :: 9 :: ds) ≠ [1] := by
                    intro h; injection h with h1; omega
                  refine chainLeadsUpTo_trans
                    (fhigh_ext hne1_19 hS_19 hv_rest hm'2
                      h9_props.1 h9_props.2.1 h9_props.2.2) ?_
                  intro m1 s_mid _ hex
                  rcases hex with (⟨phi, hphi, hb⟩ | ⟨y, phi, hy49, hpc, hb⟩) |
                      ⟨y, phi, hy53, hy_od, hphi88, hb⟩
                  · exact pop_19_9_leads hb hds (by omega)
                  · exact pop_y_19_9_leads hb hds hy49
                      (by rcases hpc with h1 | h2; exact Or.inl h1; exact Or.inr (Or.inl h2))
                  · exact pop_y_19_9_leads hb hds (by omega) (Or.inr (Or.inr ⟨hy53, hy_od, hphi88⟩))
                · -- `10 <= c + z0`:
                  have hd10 : 10 ≤ c + z0 := by omega
                  have hS_d : SafeStack 19 ((c + z0) :: ds) := safeStack19_d_ds hd10 hds
                  have hne1_d : ((c + z0) :: ds) ≠ [1] := by
                    intro h; injection h with h1; omega
                  have hx1_21 : 21 ≤ k + 2 * z0 + 2 := by
                    rcases dec_or (39 ≤ z0) with hz39 | hz_lt39
                    · omega
                    · rcases h39 (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> omega
                  have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, ds⟩ = true := by
                    dsimp only [stepGuards]
                    change (GoodPhiW (c + z0 - 1) ds false &&
                      if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) ds &&
                        if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                        if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                          GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: ds) else true) = true
                    rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                      if_neg hnot_ev, if_pos hod_sm]
                    exact hS_d.2.2 (k + 2 * z0 + 2) (by omega)
                  refine ⟨hg, fun N => ?_⟩
                  dsimp only [stepSegs]
                  change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                  rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                  have hm_sub : m' + 1 - 1 = m' := by omega
                  rw [hm_sub]
                  set x1 := k + 2 * z0 + 2
                  rcases dec_or (x1 ≤ 47) with hx47 | hx48
                  · have hx_lo : 23 ≤ x1 ∨ (x1 = 21 ∧ SafeStack 19 ((c + z0) :: ds)) := by
                      rcases dec_or (x1 = 21) with h21 | hne21
                      · exact Or.inr ⟨h21, hS_d⟩
                      · rcases dec_or (39 ≤ z0) with hz39 | hz_lt39
                        · omega
                        · rcases h39 (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> omega
                    exact loop_k1_le47 hne1_d (safeStack_mono (by decide) hS_d)
                      hx_lo hx47 hv_rest (by omega)
                      (fun _ z phi _ hz hphi38 _ hbz =>
                        pop_y_d_leads hbz hd10 hds (by omega) hphi38)
                      (fun _ _ _ hb1 =>
                        bounce_d_leads hb1 hds_cz (h_bounce_cz hd10 (x1 - 1) (by omega)))
                      (fun _ _ _ hb2 =>
                        bounce_d_leads hb2 hds_cz (h_bounce_cz hd10 (x1 - 2) (by omega)))
                      (fun _ c' k' p1 p2 _ hc' hk'41 hk'c hvp => by
                        subst hc'
                        have hfp := fzOf_ge_40 hvp
                        exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0) (by omega) hds_cz
                          (validTail40_of_validSegs40 hvp) (by omega) (by omega) hk'c
                          (by omega) (by omega) (by omega)))
                  · exact chainLeadsUpTo_trans
                      ((excursion270_bundle N).2 19 ((c + z0) :: ds) rest zl m' 1 x1 39 0
                        (by decide) hS_d (Or.inl hne1_d) hv_rest
                        (by omega) (by decide) (by omega) (by decide) (by omega)
                        (by omega) (by omega) (by omega) (by omega))
                      (fun _ _ _ hex => by
                        rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
                        · have hb_cases :
                            (c + z0 = 8 ∧ (phi = 16 ∨ phi = 17 ∨ 38 ≤ phi)) ∨
                            (c + z0 = 9 ∧ 19 ≤ phi) ∨
                            (10 ≤ c + z0 ∧ c + z0 ≤ 18 ∧ 19 ≤ phi ∧
                              (12 ≤ c + z0 → (c + z0) % 2 = 0 → 23 ≤ phi)) ∨
                            (c + z0 = 19 ∧ 37 ≤ phi) ∨
                            (20 ≤ c + z0 ∧ 38 ≤ phi) := by
                            rcases dec_or (c + z0 ≤ 18) with h_le18 | h_ge19
                            · exact Or.inr (Or.inr (Or.inl ⟨hd10, h_le18, by omega,
                                fun _ _ => by omega⟩))
                            · rcases dec_or (c + z0 = 19) with h_eq19 | h_ge20
                              · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h_eq19, by omega⟩)))
                              · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hphi⟩)))
                          exact bounce_d_leads hb hds_cz hb_cases
                        · exact pop_y_d_leads hb hd10 hds (by omega) hphi38)
            · -- `m0 >= 2 * kz + 12`:
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, ds⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) ds false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) ds &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) ((c + z0) :: ds)
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, (c + z0) :: ds⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := (c + z0) :: ds) hv_rest (by omega) (by
                    rcases dec_or (((m' - 4) + 1) % 2 = 1) with ho | he
                    · rw [if_pos ho]; omega
                    · rw [if_neg he]; omega)
                simpa only [Nat.add_zero] using h
              rcases dec_or (c + z0 = 8) with h_eq8 | h_ge9
              · obtain ⟨m0_, rest_, hseg_eq, rfl, rfl, _, _⟩ := h8 h_eq8
                injection hseg_eq with hhd _
                injection hhd with hz0_eq _
                subst hz0_eq
                exact bounce_d_leads hbc hds_cz (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
              · rcases dec_or (c + z0 = 9) with h_eq9 | h_ge10
                · have hck1 : c = 1 ∧ k = 1 := by
                    rcases h39 (by omega) with h | ⟨_, _, hz20⟩
                    · exact h
                    · omega
                  rcases hck1 with ⟨rfl, rfl⟩
                  exact bounce_d_leads hbc hds_cz (Or.inr (Or.inl ⟨h_eq9, by omega⟩))
                · exact bounce_d_leads hbc hds_cz (h_bounce_cz (by omega) (k + 2 * z0 + 2) (by omega))

lemma root0_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root0 s) :
    ChainAdvances s RootInv270 := by
  rcases hr with ha | hb0
  · exact root0A_advances hb hmrg ha
  · exact root0B_advances hb hmrg hb0

-- ============================================================================
-- Master Root Advancement & Unconditional `inv_s0`
-- ============================================================================

lemma root_advances270 : ∀ s, RootInv270 s → ChainAdvances s RootInv270 := by
  intro s ⟨hb, hmrg, hroot⟩
  rcases hroot with h0 | h1 | h31 | hD | hD1
  · exact root0_advances hb hmrg h0
  · exact root1_advances hb hmrg h1
  · exact root31_advances hb hmrg h31
  · exact rootD_advances hb hmrg hD
  · exact rootD1_advances hb hmrg hD1

def iterGuards : Nat → SegState → Bool
  | 0, _ => true
  | n + 1, s => stepGuards s && iterGuards n (stepSegs s)

def iterStep : Nat → SegState → SegState
  | 0, s => s
  | n + 1, s => iterStep n (stepSegs s)

lemma checkChainAux_of_iter (k : Nat) :
    ∀ fuel s, iterGuards k s = true →
      (∀ f, checkChainAux f (iterStep k s).b (encSegs (iterStep k s).segs (iterStep k s).zl)
        (iterStep k s).cp1 (iterStep k s).kb (iterStep k s).mrg (iterStep k s).ds = true) →
      checkChainAux fuel s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds = true := by
  induction k with
  | zero =>
    intro fuel s _ h
    exact h fuel
  | succ k ih =>
    intro fuel s hg h
    cases fuel with
    | zero => rfl
    | succ f =>
      dsimp only [iterGuards] at hg
      have hg1 : stepGuards s = true := by
        cases hgs : stepGuards s <;> simp_all
      have hg2 : iterGuards k (stepSegs s) = true := by
        cases hgs : stepGuards s <;> simp_all
      rw [checkChainAux_eq_of_guards f s hg1]
      exact ih f (stepSegs s) hg2 h

theorem inv_s0 : Inv (.ModeB_ge3 [] 1 1 []) := by
  refine ⟨rfl, fun fuel => ?_⟩
  change checkChainAux fuel true (encSegs [] 0) 3 0 8 [1] = true
  have hg28 : iterGuards 28 ⟨true, [], 0, 3, 0, 8, [1]⟩ = true := rfl
  have hs28 : iterStep 28 ⟨true, [], 0, 3, 0, 8, [1]⟩ =
      ⟨false, [(56, 223)], 489, 10, 21, 0, []⟩ := rfl
  refine checkChainAux_of_iter 28 fuel ⟨true, [], 0, 3, 0, 8, [1]⟩ hg28 (fun f => ?_)
  rw [hs28]
  exact checkChainAux_true_of_advances root_advances270 f
    ⟨false, [(56, 223)], 489, 10, 21, 0, []⟩
    (rootInv_of_0B (Or.inl rfl) ⟨(fun _ h => nomatch h), by decide⟩ (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ _ _ _ hcz9 => absurd hcz9 (by decide)))


end ChainClosure

-- ============================================================================
-- Section 6: Target Theorem Statement
-- ============================================================================

lemma nonhalt_of_state_step_inv {Γ Λ S : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (toCfg : S → Cfg Γ Λ) (Inv : S → Prop) (nextState : S → S) (s₀ : S)
    (h0 : (init []) [M]⊢* toCfg s₀)
    (hinv0 : Inv s₀)
    (hstep_cfg : ∀ s, Inv s → (toCfg s) [M]⊢⁺ toCfg (nextState s))
    (hstep_inv : ∀ s, Inv s → Inv (nextState s)) :
    IsDoesNotHalt M := by
  have hreach : ∀ k, ∃ s, Inv s ∧ ∃ m ≥ k, multiStep M (init []) m = some (toCfg s) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨m, hm⟩ := h0
      exact ⟨s₀, hinv0, m, Nat.zero_le m, hm⟩
    | succ k ih =>
      obtain ⟨s, hs, m, hge, hm⟩ := ih
      obtain ⟨d, hd_pos, hd⟩ := hstep_cfg s hs
      exact ⟨nextState s, hstep_inv s hs, m + d, by omega,
        multiStep_trans M (init []) (toCfg s) (toCfg (nextState s)) m d hm hd⟩
  intro cfg ⟨n, hn⟩
  rw [Option.isSome_iff_ne_none]
  intro hnone
  obtain ⟨s, _, m, hge, hm⟩ := hreach (n + 1)
  have hm_eq : m = n + (1 + (m - n - 1)) := by omega
  rw [hm_eq, multiStep_add M (init []) n (1 + (m - n - 1)), hn] at hm
  simp only [Option.bind] at hm
  rw [multiStep_add M cfg 1 (m - n - 1), multiStep_one, hnone] at hm
  simp only [Option.bind] at hm
  cases hm

lemma init_to_s0 : (init []) [holdout_270_tm]⊢⁺ toCfg (.ModeB_ge3 [] 1 1 []) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  dsimp only [toCfg, evalL, evalR]
  dsimp [O, ListBlank.append]
  execute60

theorem holdout_270_nonhalt_of_Inv_s0 (h_s0 : Inv (.ModeB_ge3 [] 1 1 [])) :
    IsDoesNotHalt target_tm := by
  exact nonhalt_of_state_step_inv holdout_270_tm toCfg Inv nextState (.ModeB_ge3 [] 1 1 [])
    (stepPlus_stepStar init_to_s0) h_s0 step_toCfg step_Inv

end State270System

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact State270System.holdout_270_nonhalt_of_Inv_s0 State270System.ChainClosure.inv_s0

end BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA
