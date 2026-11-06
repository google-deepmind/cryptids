/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter

/-!
# Segment-Chain Symbolic Transition System (`BusyBeaver.Calculi.SegmentChain`)

Symbolic state representation (`ModeState`), multi-step macro transitions, and single-step
invariant preservation (`step_toCfg`, `step_Inv`) for `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA`.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.SegmentChain

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

open BusyBeaver BusyBeaver.Counter SixState
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4

set_option maxRecDepth 2000

private theorem if_pos {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := by
  simp [hc]

private theorem if_neg {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := by
  simp [hnc]

theorem multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config :=
  rfl
theorem multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config :=
  rfl
theorem multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

theorem pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
theorem pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
theorem cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) :=
  rfl
theorem append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
theorem listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
theorem listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +>
  b = x >> (xs +> b) := rfl
theorem zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
theorem default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
theorem default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

theorem listblank_append_append (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s

theorem pow_add_append_right (u : List (Fin 2)) (m n : Nat) {r : ListBlank (Fin 2)} :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

theorem pow_succ_append_right (u : List (Fin 2)) (n : Nat) {r : ListBlank (Fin 2)} :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

theorem pow_succ_append_right' (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [listblank_append_append, list_pow_append_one]

theorem pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

theorem step_multiStep {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

theorem step_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, step_multiStep tm c₁ c₂ h⟩

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

theorem step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [BusyBeaver.Cfg.headRight,
      BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default,
      default_head, default_tail])
local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | gstep)) <;> (any_goals (first | finish | gstep)) <;>
    (any_goals (first | finish | gstep)) <;> (any_goals (first | finish | gstep)) <;>
    (any_goals (first | finish | gstep)))
local macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
local macro "execute60" : tactic =>
  `(tactic| execute <;> execute)

abbrev O : List (Fin 2) := [1]
abbrev Z : List (Fin 2) := [0]

-- ============================================================================
-- Section 5b: Shift & Macro Lemmas for target_tm
-- ============================================================================

theorem shift_A_right_1 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (O ^ k +> r)) [target_tm]⊢*
    ((l <+ Z ^ k) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{A}}> ([1] +> (O ^ k +> r)))
        [target_tm]⊢*
        ((l <+ [0]) {{A}}> (O ^ k +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih (l <+ [0]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

theorem shift_E_left_1 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ O ^ k) <{{E}} r) [target_tm]⊢*
    (l <{{E}} (O ^ k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ O ^ k) <+ [1]) <{{E}} r)
        [target_tm]⊢*
        ((l <+ O ^ k) <{{E}} ([1] +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([1] +> r)
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

theorem shift_D_right_1 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> (O ^ k +> r)) [target_tm]⊢*
    ((l <+ O ^ k) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{D}}> ([1] +> (O ^ k +> r)))
        [target_tm]⊢*
        ((l <+ [1]) {{D}}> (O ^ k +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih (l <+ [1]) r
    rw [listblank_append_append, list_pow_append_one] at h2
    exact stepStar_trans h1 h2

theorem sweep_R (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0] +> (O ^ (k + 5) +> ([0, 1] +> r)))) [target_tm]⊢⁺
    (((l <+ [1, 1, 0]) <+ Z ^ k) {{B}}> ([0, 1, 1, 1, 0] +> r)) := by
  have hk : k + 5 = (k + 3) + 1 + 1 := by omega
  rw [hk, pow_succ_append_right O (k + 3 + 1), pow_succ_append_right O (k + 3)]
  have h1 : (l {{B}}> ([0] +> (O +> (O +> (O ^ (k + 3) +> ([0, 1] +> r))))))
      [target_tm]⊢⁺
      ((l <+ [1, 1, 0]) {{A}}> (O ^ (k + 3) +> ([0, 1] +> r))) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_A_right_1 (k + 3) (l <+ [1, 1, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have hk3 : k + 3 = k + 1 + 1 + 1 := by omega
  rw [hk3, pow_add_append_left _ Z (k + 1 + 1) 1, pow_add_append_left _ Z (k + 1) 1,
      pow_add_append_left _ Z k 1, pow_succ_list Z 0, pow_zero_list Z, append_nil_list] at h12
  have h3 : ((((((l <+ [1, 1, 0]) <+ Z ^ k) <+ Z) <+ Z) <+ Z) {{A}}> ([0, 1] +> r))
      [target_tm]⊢⁺
      (((l <+ [1, 1, 0]) <+ Z ^ k) {{B}}> ([0, 1, 1, 1, 0] +> r)) := by
    dsimp [Z, ListBlank.append]; execute
  exact stepPlus_trans h12 h3

theorem sweep_blank_R (k : Nat) (l : ListBlank (Fin 2)) :
    (l {{B}}> ([0] +> (O ^ (k + 4) +> default))) [target_tm]⊢⁺
    (((l <+ [1, 1, 0]) <+ Z ^ k) {{D}}> ([0, 1, 0, 1, 1] +> default)) := by
  have hk : k + 4 = (k + 2) + 1 + 1 := by omega
  rw [hk, pow_succ_append_right O (k + 2 + 1), pow_succ_append_right O (k + 2)]
  have h1 : (l {{B}}> ([0] +> (O +> (O +> (O ^ (k + 2) +> default)))))
      [target_tm]⊢⁺
      ((l <+ [1, 1, 0]) {{A}}> (O ^ (k + 2) +> default)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_A_right_1 (k + 2) (l <+ [1, 1, 0]) default
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have hk2 : k + 2 = k + 1 + 1 := by omega
  rw [hk2, pow_add_append_left _ Z (k + 1) 1, pow_add_append_left _ Z k 1,
      pow_succ_list Z 0, pow_zero_list Z, append_nil_list] at h12
  have h3 : (((((l <+ [1, 1, 0]) <+ Z ^ k) <+ Z) <+ Z) {{A}}> default)
      [target_tm]⊢⁺
      (((l <+ [1, 1, 0]) <+ Z ^ k) {{D}}> ([0, 1, 0, 1, 1] +> default)) := by
    dsimp [Z, ListBlank.append]; execute
  exact stepPlus_trans h12 h3

theorem left_sweep_to_hub (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [target_tm]⊢⁺
    (l {{D}}> ([0] +> (O ^ (k + 1) +> ([0, 1] +> r)))) := by
  rw [pow_add_append_left (l <+ [0, 0]) O k 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
  have h1 : ((((l <+ [0, 0]) <+ O ^ k) <+ O) {{D}}> ([0] +> r))
      [target_tm]⊢⁺
      (((l <+ [0, 0]) <+ O ^ k) <{{E}} ([0, 1] +> r)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_E_left_1 k (l <+ [0, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((l <+ [0, 0]) <{{E}} (O ^ k +> ([0, 1] +> r)))
      [target_tm]⊢⁺
      (l {{D}}> ([0] +> ([1] +> (O ^ k +> ([0, 1] +> r))))) := by
    dsimp [ListBlank.append]; execute
  have h123 := stepPlus_trans h12 h3
  rw [← pow_succ_append_right O k] at h123
  exact h123

theorem left_sweep_to_B (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 0, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([0] +> (O ^ (k + 2) +> ([0, 1] +> r)))) := by
  have heq : l <+ [0, 0, 0] = (l <+ [0]) <+ [0, 0] := rfl
  rw [heq]
  have h1 := left_sweep_to_hub k (l <+ [0]) r
  have h2 : ((l <+ [0]) {{D}}> ([0] +> (O ^ (k + 1) +> ([0, 1] +> r))))
      [target_tm]⊢⁺
      (l {{B}}> ([0] +> ([1] +> (O ^ (k + 1) +> ([0, 1] +> r))))) := by
    dsimp [ListBlank.append]; execute
  have h12 := stepPlus_trans h1 h2
  rw [← pow_succ_append_right O (k + 1)] at h12
  exact h12

theorem merge_011 (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 1, 1, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ (k + 3)) {{D}}> ([0, 1] +> r)) := by
  rw [pow_add_append_left (l <+ [0, 1, 1, 0]) O k 1, pow_succ_list O 0, pow_zero_list O,
    append_nil_list]
  have h1 : ((((l <+ [0, 1, 1, 0]) <+ O ^ k) <+ O) {{D}}> ([0] +> r))
      [target_tm]⊢⁺
      (((l <+ [0, 1, 1, 0]) <+ O ^ k) <{{E}} ([0, 1] +> r)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_E_left_1 k (l <+ [0, 1, 1, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((l <+ [0, 1, 1, 0]) <{{E}} (O ^ k +> ([0, 1] +> r)))
      [target_tm]⊢⁺
      ((((((l <+ [0]) <+ O) <+ O) <+ O)) {{D}}> (O ^ k +> ([0, 1] +> r))) := by
    dsimp [O, ListBlank.append]; execute
  have h123 := stepPlus_trans h12 h3
  have ho3 : (((((l <+ [0]) <+ O) <+ O) <+ O)) = ((l <+ [0]) <+ O ^ 3) := by
    rw [pow_succ_list O 2, pow_succ_list O 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
    simp only [listblank_append_append]; rfl
  rw [ho3] at h123
  have h4 := shift_D_right_1 k ((l <+ [0]) <+ O ^ 3) ([0, 1] +> r)
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  rw [← pow_add_append_left (l <+ [0]) O 3 k] at h1234
  have hk : 3 + k = k + 3 := by omega
  rw [hk] at h1234
  exact h1234

theorem merge_p5 (k : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ [0, 1, 0, 1, 1, 0]) <+ O ^ (k + 1)) {{D}}> ([0] +> r)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ (k + 4)) {{D}}> ([0, 1, 1] +> r)) := by
  rw [pow_add_append_left (l <+ [0, 1, 0, 1, 1, 0]) O k 1, pow_succ_list O 0, pow_zero_list O,
    append_nil_list]
  have h1 : ((((l <+ [0, 1, 0, 1, 1, 0]) <+ O ^ k) <+ O) {{D}}> ([0] +> r))
      [target_tm]⊢⁺
      (((l <+ [0, 1, 0, 1, 1, 0]) <+ O ^ k) <{{E}} ([0, 1] +> r)) := by
    dsimp [O, ListBlank.append]; execute
  have h2 := shift_E_left_1 k (l <+ [0, 1, 0, 1, 1, 0]) ([0, 1] +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((l <+ [0, 1, 0, 1, 1, 0]) <{{E}} (O ^ k +> ([0, 1] +> r)))
      [target_tm]⊢⁺
      ((((l <+ [0, 1, 1, 0]) <+ O) <+ O) {{D}}> (O ^ k +> ([0, 1] +> r))) := by
    dsimp [O, ListBlank.append]; execute
  have h123 := stepPlus_trans h12 h3
  have ho2 : (((l <+ [0, 1, 1, 0]) <+ O) <+ O) = ((l <+ [0, 1, 1, 0]) <+ O ^ 2) := by
    rw [pow_succ_list O 1, pow_succ_list O 0, pow_zero_list O, append_nil_list]
    simp only [listblank_append_append]; rfl
  rw [ho2] at h123
  have h4 := shift_D_right_1 k ((l <+ [0, 1, 1, 0]) <+ O ^ 2) ([0, 1] +> r)
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  rw [← pow_add_append_left (l <+ [0, 1, 1, 0]) O 2 k] at h1234
  have hk : 2 + k = (k + 1) + 1 := by omega
  rw [hk] at h1234
  have h5 := merge_011 (k + 1) l ([1] +> r)
  exact stepPlus_trans h1234 h5

-- ============================================================================
-- Section 5c: Concrete Finite Bridges for target_tm
-- ============================================================================

theorem thm_A_0 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 0, 1] +> r)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 4) {{D}}> ([0] +> r)) := by
  dsimp [O, ListBlank.append]; execute

theorem step_D_0011 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 0, 0, 0]) {{D}}> ([0, 1] +> r)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 4) {{D}}> ([0, 1] +> r)) := by
  dsimp [O, ListBlank.append]; execute

theorem step_D_p3z1_pop (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 0, 0]) {{D}}> ([0, 1] +> r)) [target_tm]⊢⁺
    (l {{D}}> ([0, 1, 1, 0, 1, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

theorem bridge_b2_m0 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1, 1] +> r)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 6) {{D}}> ([0, 1] +> r)) := by
  dsimp [O, ListBlank.append]; execute

theorem bridge_b2_tail (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 0]) {{B}}> ([0, 1, 1, 1, 0, 1] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

theorem bridge_b5a (l : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1] +> default)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 5) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute60

theorem bridge_b5b_pre (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 1, 1, 1, 0, 1, 0] +> r)) [target_tm]⊢⁺
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0] +> r)) := by
  dsimp [ListBlank.append]; execute

theorem bridge_b5b_d0_blank (l : ListBlank (Fin 2)) :
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0, 1, 1] +> default)) [target_tm]⊢⁺
    ((((l <+ [1, 1, 0]) <+ [0]) <+ O ^ 6) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute

theorem bridge_b5b_d1_blank (l : ListBlank (Fin 2)) :
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0, 1, 1, 1] +> default)) [target_tm]⊢⁺
    (((((l <+ [1, 1, 0]) <+ [1, 1, 0]) <+ [0]) <+ O ^ 4) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute

theorem bridge_b5b_d2_blank (l : ListBlank (Fin 2)) :
    (((l <+ [1, 1, 0]) <+ [1, 0, 1, 1, 0]) {{B}}> ([0, 1, 1, 1, 1] +> default)) [target_tm]⊢⁺
    ((((l <+ [1, 1, 0]) <+ [0]) <+ O ^ 5) {{D}}> ([0, 1, 1, 1, 0, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute

theorem bridge_blank_apos_tail (l : ListBlank (Fin 2)) :
    ((l <+ [0, 0, 0]) {{D}}> ([0, 1, 0, 1, 1] +> default)) [target_tm]⊢⁺
    (((l <+ [0]) <+ O ^ 5) {{D}}> ([0, 1, 1, 1] +> default)) := by
  dsimp [O, ListBlank.append]; execute60

-- ============================================================================
-- Section 5d: Closed State Space & Step Function for target_tm
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

inductive ModeState where
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

def toCfg : ModeState → Cfg (Fin 2) (Fin 6)
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

def nextModeE_p3z1 : List LTok → Nat → List Nat → ModeState
  | [], b, ds => .ModeE_ge2 [] 0 b ds
  | .p3z 0 :: ls'', b, ds => .ModeE_ge2 ls'' 0 (b + 1) ds
  | .p3z 1 :: ls'', b, ds => nextModeE_p3z1 ls'' 0 ((b + 1) :: ds)
  | .p3z (m2 + 2) :: ls'', b, ds => .ModeE_ge2 (.p3z m2 :: ls'') 0 b ds
  | .p5 :: ls'', b, ds => .ModeE_ge2 ls'' 1 (b + 2) ds

def nextState : ModeState → ModeState
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
-- Section 5e: Inductive Invariant on ModeState
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
      | [] => GoodPsi (cz - 1) ds && checkChainAux fuel true [] (kz + 2) 0 (2 * (kz + 1) +
        4) (cz :: ds)
      | .p5 :: suf => checkChainAux fuel true suf (cz + 3) (kz + 3) (2 * (cz + 2) + 4) ds
      | .p3z m :: rest =>
        let suf := drop1L rest
        if m = 1 then
          GoodPsi cz ds && checkChainAux fuel false suf (kz + 4) 1 0 ((cz + 1) :: ds)
        else if !GoodPsi (cz - 1) ds then false
        else if m % 2 = 0 ∧ m ≤ 2 * kz + 10 then
          checkChainAux fuel false suf (kz + 4) (m + 1) 0 (cz :: ds)
        else if m % 2 = 1 ∧ m ≤ 2 * kz + 11 then
          GoodDs ((kz + 2) :: cz :: ds) && checkChainAux fuel false suf (m - 1) 1 0 ((kz +
            2) :: cz :: ds)
        else
          checkChainAux fuel true (.p3z (m - 4) :: .p5 :: suf) (kz + 2) 0 (2 * (kz + 1) +
            4) (cz :: ds)
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
          GoodDs ((xi + 3) :: psip1 :: ds) && checkChainAux fuel false suf (m2 + 1) 1 0 ((xi +
            3) :: psip1 :: ds)
        else
          checkChainAux fuel true (.p3z (m2 - 2) :: .p5 :: suf) (xi + 3) 0 (2 * (xi + 2) +
            4) (psip1 :: ds)
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

def checkDs2 (s : ModeState) : Bool :=
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

def checkDs1Phi1 (s : ModeState) : Bool :=
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

def invCore (s : ModeState) : Bool :=
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
              (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧
                (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
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
            if match ds with | d :: _ => decide (d ≥ 3) | [] => false then decide (cz ≥ 20 ∧
              kz ≥ 15)
            else decide (cz ≥ 8 ∧ kz ≥ 15)
          ok_base &&
          (!decide (((ds = [] ∨ ds = [0]) ∧
            cz ≥ 9) ∨ isOddDrainDs ds = true) || decide (kz ≥ 17)) &&
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
          (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧
            (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
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
              (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧
                (!hasP5 ls ∨ MustDrain nls)) || decide (a ≥ 17)) &&
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
        (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧
          (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
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
        (!decide ((ds = [] ∨ ds = [0]) ∧ psi ≥ 8 ∧
          (!hasP5 ls ∨ MustDrain ls)) || decide (xi ≥ 16)) &&
        (!MustDrain ls || decide (xi ≥ 14 ∧ psi ≥ 7))
      else true

def invChain (fuel : Nat) (s : ModeState) : Bool :=
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

def Inv (s : ModeState) : Prop :=
  invCore s = true ∧ ∀ fuel : Nat, invChain fuel s = true

-- ============================================================================
-- Section 5f: TM Step Simulation & Invariant Preservation
-- ============================================================================

theorem GoodDs_pair_ge3 {d d2 : Nat} {ds2 : List Nat} (h : GoodDs (d :: d2 :: ds2) =
  true) : d ≥ 3 := by
  cases ds2 with
  | nil =>
    dsimp [GoodDs, GoodDsAux, GoodDs2] at h
    by_cases h1 : d2 = 0
    · simp [h1] at h; omega
    · by_cases h2 : d2 = 1
      · simp [h2] at h; omega
      · by_cases h3 : d2 ≥ 3
        · simp [h1, h2, h3] at h; omega
        · simp [h1, h2, h3] at h
  | cons d3 ds3 =>
    by_contra hd
    have hd17 : decide (d < 17) = true := decide_eq_true (by omega)
    dsimp [GoodDs, GoodDsAux] at h
    rw [hd17, Bool.true_or] at h
    split_ifs at h; simp_all

theorem GoodDs_second_zero_ge8 {d : Nat} {ds2 : List Nat} (h : GoodDs (d :: 0 :: ds2) =
  true) : d ≥ 8 := by
  cases ds2 with
  | nil =>
    dsimp [GoodDs, GoodDsAux, GoodDs2] at h
    simp_all
  | cons d3 ds3 =>
    dsimp [GoodDs, GoodDsAux] at h
    cases h

theorem step_ModeE_p3z1_after_sweep (ls' : List LTok) (b : Nat) (ds : List Nat) :
    (((evalL ls' <+ [1, 1, 0]) {{D}}> ([0] +> (O ^ (b + 2) +> evalR ds)))) [target_tm]⊢⁺
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
        have hl : ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ 0) <+ [1, 1, 0] =
          (evalL ls'' <+ [0, 1, 1, 0]) <+ O ^ 2 := rfl
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
          have hl : ((evalL ls'' <+ [1, 1, 0]) <+ Z ^ 1) <+ [1, 1, 0] =
            (evalL ls'' <+ [1, 1, 0]) <+ [1, 1, 0, 0] := rfl
          rw [hl]
          have hr' : [0] +> (O ^ (b + 2) +> evalR ds) = [0, 1] +> (O ^ (b + 1) +> evalR ds) := by
            have hb : b + 2 = 1 + (b + 1) := by omega
            rw [hb, pow_add_append_right O 1 (b + 1)]; rfl
          rw [hr']
          have h1 := step_D_p3z1_pop (evalL ls'' <+ [1, 1, 0]) (O ^ (b + 1) +> evalR ds)
          have hr2 : [0, 1, 1, 0, 1, 1] +> (O ^ (b + 1) +> evalR ds) =
            [0] +> (O ^ (0 + 2) +> evalR ((b + 1) :: ds)) := by
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
      have hl : (evalL ls'' <+ [1, 0, 1, 1, 0]) <+ [1, 1, 0] =
        (evalL ls'' <+ [0, 1, 0, 1, 1, 0]) <+ O ^ 2 := rfl
      rw [hl]
      have h1 := merge_p5 1 (evalL ls'') (O ^ (b + 2) +> evalR ds)
      have hr' : [0, 1, 1] +> (O ^ (b + 2) +> evalR ds) = [0] +> (O ^ (b + 4) +> evalR ds) := by
        have hb : b + 4 = 2 + (b + 2) := by omega
        rw [hb, pow_add_append_right O 2 (b + 2)]; rfl
      rw [hr'] at h1
      exact h1

theorem step_toCfg (s : ModeState) (hinv : Inv s) :
    (toCfg s) [target_tm]⊢⁺ toCfg (nextState s) := by
  cases s with
  | ModeE_c1 ls k ds =>
    cases ls with
    | nil =>
      dsimp only [nextState, toCfg, evalL]
      have hl : (default : ListBlank (Fin 2)) <+ [0] = default <+ [0, 0, 0] := by
        calc (default : ListBlank (Fin 2)) <+ [0] = default := zero_cons_default
        _ = default <+ [0] := zero_cons_default.symm
        _ = (default <+ [0]) <+ [0] := congrArg (· <+ [0]) zero_cons_default.symm
        _ = ((default <+ [0]) <+ [0]) <+ [0] :=
          congrArg (fun x => (x <+ [0]) <+ [0]) zero_cons_default.symm
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
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ 1) <+ [0]) =
              (evalL ls' <+ [1, 1, 0]) <+ [0, 0] := rfl
            rw [hl]
            have h1 := left_sweep_to_hub (k0Of k + 3) (evalL ls' <+ [1, 1, 0]) ([1] +> evalR ds)
            exact stepPlus_trans h1 (step_ModeE_p3z1_after_sweep ls' (k0Of k + 2) (0 :: ds))
          | succ m2 =>
            dsimp only [nextState, toCfg, evalL]
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ (m2 + 2)) <+ [0]) =
                ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) <+ [0, 0, 0] := by
              rw [pow_add_append_left (evalL ls' <+ [1, 1, 0]) Z m2 2]; rfl
            rw [hl]
            have h1 :=
              left_sweep_to_B (k0Of k + 3) ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) ([1] +> evalR ds)
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
        _ = ((default <+ [0]) <+ [0]) <+ [0] :=
          congrArg (fun x => (x <+ [0]) <+ [0]) zero_cons_default.symm
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
            have hl : (((evalL ls' <+ [1, 1, 0]) <+ Z ^ 1) <+ [0]) =
              (evalL ls' <+ [1, 1, 0]) <+ [0, 0] := rfl
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
            have h1 :=
              left_sweep_to_B (k + 3) ((evalL ls' <+ [1, 1, 0]) <+ Z ^ m2) (O ^ (c + 2) +> evalR ds)
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
      have hl : (evalL ls <+ [1, 1, 0]) <+ Z ^ (m' + 2) =
        ((evalL ls <+ [1, 1, 0]) <+ Z ^ m') <+ [0, 0] := by
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
        have hl : (evalL ls <+ [1, 1, 0]) <+ Z ^ (a'' + 3) =
          ((evalL ls <+ [1, 1, 0]) <+ Z ^ a'') <+ [0, 0, 0] := by
          rw [pow_add_append_left (evalL ls <+ [1, 1, 0]) Z a'' 3]; rfl
        rw [hl] at h1
        exact stepPlus_trans h1 (bridge_blank_apos_tail ((evalL ls <+ [1, 1, 0]) <+ Z ^ a''))

theorem z0_z0Rep (n : Nat) (rest : List LTok) : z0 (z0Rep n rest) = n + z0 rest := by
  induction n with
  | zero => simp [z0Rep]
  | succ n ih => change 1 + z0 (z0Rep n rest) = n + 1 + z0 rest; omega

theorem ep_z0Rep (n : Nat) (rest : List LTok) : ep (z0Rep n rest) = n + ep rest := by
  induction n with
  | zero => simp [z0Rep]
  | succ n ih => dsimp [z0Rep, ep]; omega

theorem hasOdd_p3z_add2 (m : Nat) (ls : List LTok) :
    hasOdd (.p3z (m + 2) :: ls) = hasOdd (.p3z m :: ls) := by
  dsimp [hasOdd]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

theorem ep_p3z_add2 (m : Nat) (ls : List LTok) :
    ep (.p3z (m + 2) :: ls) = ep (.p3z m :: ls) := by
  dsimp [ep]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

theorem epW_p3z_add2 (m : Nat) (ls : List LTok) :
    epW (.p3z (m + 2) :: ls) = epW (.p3z m :: ls) := by
  dsimp [epW]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

theorem decide_eq_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

theorem GoodPhiW_mono (phiW : Nat) (ds : List Nat) (b : Bool) (h : GoodPhiW phiW ds false = true) :
    GoodPhiW phiW ds b = true := by
  dsimp [GoodPhiW] at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem prefSumW_p3z_add2 (m : Nat) (ls : List LTok) (hm : m % 2 = 0) (hnp5 : isHeadP5 ls = false) :
    prefSumW (.p3z (m + 2) :: ls) = prefSumW (.p3z m :: ls) + 2 := by
  have hm1 : ¬((m + 2) % 2 = 1) := by omega
  have hm2 : ¬(m % 2 = 1) := by omega
  cases ls with
  | nil => dsimp [prefSumW]; rw [if_neg hm1, if_neg hm2]
  | cons t s =>
    cases t with
    | p5 => cases hnp5
    | p3z _ => dsimp [prefSumW]; rw [if_neg hm1, if_neg hm2]; omega

theorem epSum_p3z_add2 (m : Nat) (ls : List LTok) :
    epSum (.p3z (m + 2) :: ls) = epSum (.p3z m :: ls) + 2 := by
  dsimp [epSum]
  by_cases hm : m % 2 = 1
  · have hm' : (m + 2) % 2 = 1 := by omega
    rw [if_pos hm', if_pos hm]; omega
  · have hm' : ¬((m + 2) % 2 = 1) := by omega
    rw [if_neg hm', if_neg hm]; omega

theorem MustDrain_p3z_add2 (m : Nat) (ls : List LTok) :
    MustDrain (.p3z (m + 2) :: ls) = MustDrain (.p3z m :: ls) := by
  dsimp [MustDrain]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

theorem ValidEvenLs_p3z_add2 (m : Nat) (ls : List LTok) :
    ValidEvenLs (.p3z (m + 2) :: ls) = ValidEvenLs (.p3z m :: ls) := by
  dsimp [ValidEvenLs]
  have h : (m + 2) % 2 = m % 2 := by omega
  rw [h]

theorem preP5Val_p3z_add2_of_not_headP5 (m : Nat) (ls : List LTok) (h : isHeadP5 ls = false) :
    preP5Val (.p3z (m + 2) :: ls) = preP5Val (.p3z m :: ls) := by
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases h | p3z _ => rfl

theorem not_isHeadP5_of_MustDrain_p3z (m : Nat) (ls : List LTok) (h : MustDrain (.p3z m :: ls) =
  true) :
    isHeadP5 ls = false := by
  cases ls with
  | nil => rfl
  | cons t s =>
    cases t with
    | p3z _ => rfl
    | p5 =>
      dsimp [MustDrain] at h
      split_ifs at h

theorem hasOdd_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    hasOdd (.p3z k :: ls) = hasOdd ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [hasOdd]; rw [if_neg hk1]

theorem ep_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    ep (.p3z k :: ls) = 1 + ep ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [ep]; rw [if_neg hk1]

theorem epW_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) (hnp5 : isHeadP5 ls = false) :
    epW (.p3z k :: ls) = 1 + epW ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [epW]; rw [if_neg hk1]
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases hnp5 | p3z _ => rfl

theorem prefSumW_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) (hnp5 : isHeadP5 ls =
  false) :
    prefSumW (.p3z k :: ls) = k + prefSumW ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [prefSumW]; rw [if_neg hk1]
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases hnp5 | p3z _ => rfl

theorem epSum_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    epSum (.p3z k :: ls) = k + epSum ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [epSum]; rw [if_neg hk1]

theorem MustDrain_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    MustDrain (.p3z k :: ls) = MustDrain ls := by
  have hk1 : ¬(k % 2 = 1) := by omega
  dsimp [MustDrain]; rw [if_neg hk1]

theorem ValidEvenLs_p3z_even_cons (k : Nat) (ls : List LTok) (hk : k % 2 = 0) :
    ValidEvenLs (.p3z k :: ls) = ValidEvenLs ls := by
  dsimp [ValidEvenLs]; rw [if_pos hk]

theorem preP5Val_p3z_cons_of_not_headP5 (k : Nat) (ls : List LTok) (h : isHeadP5 ls = false) :
    preP5Val (.p3z k :: ls) = preP5Val ls := by
  cases ls with
  | nil => rfl
  | cons t s => cases t with | p5 => cases h | p3z _ => rfl

theorem epSum_z0Rep (n : Nat) (rest : List LTok) : epSum (z0Rep n rest) = epSum rest := by
  induction n with
  | zero => rfl
  | succ n ih => dsimp [z0Rep, epSum]; omega

theorem hasOdd_z0Rep (n : Nat) (rest : List LTok) : hasOdd (z0Rep n rest) = hasOdd rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem hasP5_z0Rep (n : Nat) (rest : List LTok) : hasP5 (z0Rep n rest) = hasP5 rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem MustDrain_z0Rep (n : Nat) (rest : List LTok) : MustDrain (z0Rep n rest) = MustDrain rest :=
  by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem p5Suf_z0Rep (n : Nat) (rest : List LTok) : p5Suf (z0Rep n rest) = p5Suf rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem ValidP5Chain_z0Rep (n : Nat) (rest : List LTok) :
    ValidP5Chain (z0Rep n rest) = ValidP5Chain rest := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem z0Rep_succ_right (n : Nat) (rest : List LTok) :
    z0Rep n (.p3z 0 :: rest) = z0Rep (n + 1) rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc z0Rep (n + 1) (.p3z 0 :: rest) = .p3z 0 :: z0Rep n (.p3z 0 :: rest) := rfl
    _ = .p3z 0 :: z0Rep (n + 1) rest := by rw [ih]
    _ = z0Rep (n + 2) rest := rfl

theorem epSum_even (ls : List LTok) : epSum ls % 2 = 0 := by
  induction ls with
  | nil => rfl
  | cons tok rest ih =>
    cases tok with
    | p5 => rfl
    | p3z m =>
      dsimp [epSum]
      split_ifs with h <;> omega

theorem ValidP5Chain_imp_ValidEvenLs (ls : List LTok) (h : ValidP5Chain ls = true) :
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

theorem ls_eq_z0Rep_of_prefSumW_zero (ls : List LTok)
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
            have hpref_unfold : prefSumW (.p3z m :: .p3z m2 :: s2) = m + prefSumW (.p3z m2 :: s2) :=
              by
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

theorem checkChainAux_false_p3z0 (fuel : Nat) (ls : List LTok) (c k m_dummy : Nat) (ds : List Nat) :
    checkChainAux fuel false (.p3z 0 :: ls) c k m_dummy ds =
    checkChainAux fuel false ls (c + 1) (k + 2) m_dummy ds := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hz : c + z0 (.p3z 0 :: ls) = c + 1 + z0 ls := by
      change c + (1 + z0 ls) = c + 1 + z0 ls; omega
    have hk : k + 2 * z0 (.p3z 0 :: ls) = k + 2 + 2 * z0 ls := by
      change k + 2 * (1 + z0 ls) = k + 2 + 2 * z0 ls; omega
    have hd : dropZ0 (.p3z 0 :: ls) = dropZ0 ls := rfl
    dsimp only [checkChainAux]
    rw [hz, hk, hd]

theorem checkChainAux_true_congr (fuel : Nat) (ls1 ls2 : List LTok)
    (cp1_1 kb_1 margin_1 cp1_2 kb_2 margin_2 : Nat) (ds : List Nat)
    (hnp1 : isHeadP5 ls1 = false)
    (hnp2 : isHeadP5 ls2 = false)
    (hodd : hasOdd ls1 = hasOdd ls2)
    (hdec : decide (margin_1 ≥ kb_1 + epSum ls1) = decide (margin_2 ≥ kb_2 + epSum ls2))
    (hep : cp1_1 + ep ls1 = cp1_2 + ep ls2)
    (hxi : margin_1 ≥ kb_1 + epSum ls1 →
      kb_1 + epSum ls1 + 2 * ep ls1 = kb_2 + epSum ls2 + 2 * ep ls2)
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
          simp only [hdec1, hdec2, ho2, hp2, hepw, Bool.and_true, Bool.and_false,
            Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        · have hp2 : hasP5 ls2 = true := hp5.symm.trans hp
          simp only [hdec1, hdec2, ho2, hp2, hsuf, hep, hxi', Bool.and_true,
            Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      · have ho2 : hasOdd ls2 = true := hodd.symm.trans ho
        cases hm : MustDrain ls1
        · have hm2_eq : MustDrain ls2 = false := hmd.symm.trans hm
          simp only [hdec1, hdec2, ho2, hm2_eq, hp5, hsuf, hep, hxi', Bool.and_true,
            Bool.not_false, ↓reduceIte]
        · have hm2_eq : MustDrain ls2 = true := hmd.symm.trans hm
          have hpre := hm2 hm
          simp only [hdec1, hdec2, ho2, hm2_eq, hp5, hpre, hsuf, hep, hxi', Bool.and_true,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · have hdec1 : decide (margin_1 ≥ kb_1 + epSum ls1) = false := decide_eq_false hge1
      have hdec2 : decide (margin_2 ≥ kb_2 + epSum ls2) = false := hdec.symm.trans hdec1
      have hrem' := hrem hge1
      rw [hrem']
      simp only [hdec1, hdec2, hodd, hepw, hp5, hsuf, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]

theorem checkChainAux_true_no_odd_no_p5 (fuel : Nat) (ls1 ls2 : List LTok)
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
      Bool.false_eq_true, ↓reduceIte]

theorem checkChainAux_true_p3z0 (fuel : Nat) (ls : List LTok) (cp1 kb margin : Nat) (ds : List Nat)
    (h : isHeadP5 ls = false ∨ margin ≥ kb + epSum ls) :
    checkChainAux fuel true (.p3z 0 :: ls) cp1 kb margin ds =
    checkChainAux fuel true ls (cp1 + 1) (kb + 2) (margin + 2) ds := by
  cases hp5 : isHeadP5 ls with
  | false =>
    apply checkChainAux_true_congr fuel (.p3z 0 :: ls) ls cp1 kb margin (cp1 + 1) (kb + 2) (margin +
      2) ds
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
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
              Bool.true_and, Bool.true_or]
          rw [hl, hr]

theorem checkChainAux_true_E_ge2_to_B_ge3_nil (fuel : Nat) (k c : Nat) (ds : List Nat) (hk : k % 2 =
  0) :
    checkChainAux fuel true [] (c + 1) k (2 * c + 4) ds =
    checkChainAux fuel true [.p3z k] c 0 (2 * c + 2) ds := by
  apply checkChainAux_true_no_odd_no_p5 fuel [] [.p3z k] (c + 1) k (2 * c + 4) c 0 (2 * c + 2) ds
    rfl (hasOdd_p3z_even_cons k [] hk) rfl rfl
  rw [epW_p3z_even_cons k [] hk rfl]; omega

theorem checkChainAux_true_E_ge2_to_B_ge3_even (fuel : Nat) (m : Nat) (ls' : List LTok) (k c : Nat)
    (ds : List Nat) (hk : k % 2 = 0) :
    checkChainAux fuel true (.p3z (m + 2) :: ls') (c + 1) k (2 * c + 4) ds =
    checkChainAux fuel true (.p3z k :: .p3z m :: ls') c 0 (2 * c + 2) ds := by
  apply checkChainAux_true_congr fuel (.p3z (m + 2) :: ls') (.p3z k :: .p3z m :: ls')
    (c + 1) k (2 * c + 4) c 0 (2 * c + 2) ds rfl rfl
  · rw [hasOdd_p3z_add2, hasOdd_p3z_even_cons k _ hk]
  · rw [epSum_p3z_add2, epSum_p3z_even_cons k _ hk]; exact decide_eq_of_iff (by omega)
  · rw [ep_p3z_add2, ep_p3z_even_cons k _ hk]; omega
  · intro _; rw [epSum_p3z_add2, epSum_p3z_even_cons k _ hk, ep_p3z_add2,
    ep_p3z_even_cons k _ hk]; omega
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

theorem checkChainAux_true_E_c1_to_B_b2 (fuel : Nat) (m : Nat) (ls' : List LTok) (k : Nat)
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

theorem step_Inv_ModeB_blank (ls : List LTok) (a : Nat) (hinv : Inv (.ModeB_blank ls a)) :
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
          isP3zP5 (.p3z (a3 + 1) :: .p5 :: suf) = true ∧
            headP3zVal (.p3z (a3 + 1) :: .p5 :: suf) ≥ 3 :=
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

theorem not_bool_eq_false {b : Bool} : (!b) = false ↔ b = true := by
  cases b <;> simp

theorem bool_if_false_eq_true {c e : Bool} :
    (if c = true then false else e) = true ↔ (c = false ∧ e = true) := by
  cases c <;> simp

theorem prop_if_false_eq_true {P : Prop} [Decidable P] {e : Bool} :
    (if P then false else e) = true ↔ (¬P ∧ e = true) := by
  by_cases h : P <;> simp [h]

theorem bool_if_false_eq_self {b e : Bool} (hb : b = false) :
    (if b = true then false else e) = e := by
  simp [hb]

theorem not_bool_if_false_eq_true {b e : Bool} (hb : b = true) :
    (if (!b) = true then false else e) = e := by
  simp [hb]

theorem not_decide_if_false_eq_true {P : Prop} [Decidable P] {e : Bool} (hP : P) :
    (if (!decide P) = true then false else e) = e := by
  simp [hP]

theorem drop2L_cons (t1 t2 : LTok) (ls : List LTok) :
    drop2L (t1 :: ls) = drop2L (t2 :: ls) := by
  cases ls <;> rfl

theorem k0Of_eq_two_mul {k : Nat} (hk : k ≤ 1) : k0Of k = 2 * k := by
  cases k with
  | zero => rfl
  | succ k' =>
    cases k' with
    | zero => rfl
    | succ _ => omega

theorem step_Inv_ModeB_b2_m0 (ls : List LTok) (ds : List Nat) (hinv : Inv (.ModeB_b2 ls 0 ds)) :
    Inv (.ModeE_c1 ls 1 ds) := by
  have hc := hinv.1
  have hch := hinv.2
  have hds2 : checkDs2 (.ModeE_c1 ls 1 ds) = checkDs2 (.ModeB_b2 ls 0 ds) := by
    dsimp [checkDs2]
    by_cases h : ds = [2]
    · simp only [h, not_true_eq_false, ↓reduceIte]
      rw [show decide (2 * 1 + epSum ls ≥ 4) = decide (2 * 0 + epSum ls ≥ 2) from
        decide_eq_of_iff (by omega)]
    · simp [h]
  have hds1 : checkDs1Phi1 (.ModeE_c1 ls 1 ds) = checkDs1Phi1 (.ModeB_b2 ls 0 ds) := by
    dsimp [checkDs1Phi1]
    by_cases h : ds = [1]
    · simp only [h, not_true_eq_false, ↓reduceIte]
      by_cases he : epW ls = 2
      · simp only [he, not_true_eq_false, ↓reduceIte]
        rw [show decide (2 * 1 + epSum ls ≥ 12) = decide (2 * 0 + epSum ls ≥ 10) from
          decide_eq_of_iff (by omega)]
      · simp [he]
    · simp [h]
  refine ⟨?_, ?_⟩
  · have hcore_eq : invCore (.ModeE_c1 ls 1 ds) = invCore (.ModeB_b2 ls 0 ds) := by
      dsimp only [invCore]
      rw [hds2, hds1, if_neg (show ¬((0 : Nat) ≥ 2) by omega)]
      have hd1 : decide ((1 : Nat) ≤ 1) = decide ((0 : Nat) ≤ 1) := rfl
      have hd2 : decide ((1 = 0 ∧ headP3zVal ls = 0) ∨ (headP3zVal ls ≥ 22 - 2 * 1 ∧
        z0 (p5Suf ls) ≥ 38)) =
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

theorem step_Inv_ModeE_c1 (ls : List LTok) (k : Nat) (ds : List Nat) (hinv : Inv (.ModeE_c1 ls k
  ds)) :
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
          · dsimp only [invCore, GoodDs, checkDs2, checkDs1Phi1, isHeadP5, MustDrain, hasOdd,
            prefSumW]
            rw [if_pos rfl, not_bool_if_false_eq_true heven']
            rfl
          · intro fuel
            have hf := hch fuel
            dsimp [invChain] at hf ⊢
            rw [if_pos ⟨rfl, rfl⟩] at hf
            simp only [headP3zVal] at hf
            simp only [and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hf
            have h_shift :=
              checkChainAux_true_p3z0 fuel (.p5 :: suf) 0 0 2 [] (Or.inr (by dsimp [epSum]; omega))
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
            · simp only [h2, not_true_eq_false, ↓reduceIte] at hds2 ⊢
              rw [hepsum_eq] at hds2
              have hm0 : (2 * k + 2) % 2 = 0 := by omega
              simp only [hasP5, hmd_eq, p5Suf, isHeadP5, Bool.not_false, Bool.and_true] at hds2
              simp only [hm0, decide_true, hnp5, Bool.not_false, Bool.and_true]
              rw [show decide (2 * k + 2 + epSum ls' ≥ 2 * 0 + 6) =
                decide (2 * k + (0 + epSum ls') ≥ 4) from
                decide_eq_of_iff (by omega)]
              exact hds2
            · simp [h2]
          have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (2 * k + 2) 0 ds) = true := by
            dsimp [checkDs1Phi1] at hds1 ⊢
            by_cases h1 : ds = [1]
            · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
              have hm0 : (2 * k + 2) % 2 = 0 := by omega
              rw [if_pos hm0, hnp5]
              simp only [Bool.false_eq_true, ↓reduceIte]
              by_cases he1 : 0 + epW ls' = 1
              · have he2 : epW (.p3z 0 :: ls') = 2 := by omega
                simp only [he1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                simp only [he2, not_true_eq_false, ↓reduceIte, hasP5, hmd_eq, isHeadP5,
                  Bool.not_false, Bool.and_true, hepsum_eq] at hds1
                simp only [Bool.not_false, Bool.and_true]
                rw [show decide (2 * k + 2 + epSum ls' ≥ 2 * 0 + 14) =
                  decide (2 * k + (0 + epSum ls') ≥ 12) from
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
                  GoodPhiW (0 + epW ls') ds (isHeadP3z1 ls' && decide (2 * k + 2 = 0 ∧ 0 = 0 ∧
                    ds = []))
              else
                decide (0 = 0 ∧ ds = [] ∧
                  2 * k + 2 = 2) || (decide (0 ≥ 1) && GoodPhiW (0 - 1) ds false)) = true := by
              rw [if_pos (by rw [hnp5]; rfl), hphiw', Bool.or_true]
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd_eq, hepsum_eq] at hmd_bound
            have hmd_bound' : (MustDrain ls' && decide (2 * 0 + 4 < 2 * k + 2 + epSum ls')) =
              false := by
              rw [show decide (2 * 0 + 4 < 2 * k + 2 + epSum ls') =
                decide (2 < 2 * k + (0 + epSum ls')) from
                decide_eq_of_iff (by omega)]
              exact hmd_bound
            rw [bool_if_false_eq_self hmd_bound']
            have h_rst_false : (decide (2 * k + 2 = 0 ∧ 0 = 0 ∧
              ds = []) && isHeadP3z1 ls') = false := by
              simp
            rw [h_rst_false]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            rw [hodd_eq, hepsum_eq] at hodd_branch
            have hd_odd : decide (2 * 0 + 4 ≥ 2 * k + 2 + epSum ls') =
              decide (2 ≥ 2 * k + (0 + epSum ls')) :=
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
            rw [if_pos hm0, if_neg (show ¬(2 * k + 2 = 0 ∧ 0 = 0 ∧ ds = [] ∧
              isHeadP3z1 ls' = true) by omega)]
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
            · simp only [h2, not_true_eq_false, ↓reduceIte] at hds2 ⊢
              rw [hmd_eq, hepsum_eq] at hds2
              rw [show decide (2 * k + epSum (.p3z m2 :: ls') ≥ 2) =
                  decide (2 * k + (epSum (.p3z m2 :: ls') + 2) ≥
                    4) from decide_eq_of_iff (by omega)]
              exact hds2
            · simp [h2]
          have hds1' : checkDs1Phi1 (.ModeB_b2 (.p3z m2 :: ls') k ds) = true := by
            dsimp [checkDs1Phi1] at hds1 ⊢
            by_cases h1 : ds = [1]
            · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
              rw [hepw_eq, hmd_eq, hepsum_eq] at hds1
              by_cases he2 : epW (.p3z m2 :: ls') = 2
              · simp only [he2, not_true_eq_false, ↓reduceIte] at hds1 ⊢
                rw [show decide (2 * k + epSum (.p3z m2 :: ls') ≥ 10) =
                    decide (2 * k + (epSum (.p3z m2 :: ls') + 2) ≥
                      12) from decide_eq_of_iff (by omega)]
                exact hds1
              · simp [he2]
            · simp [h1]
          refine ⟨?_, ?_⟩
          · dsimp only [invCore]
            rw [heven_eq] at heven
            have h_g : (!GoodDs ds || !checkDs2 (.ModeB_b2 (.p3z m2 :: ls') k ds) ||
                !checkDs1Phi1 (.ModeB_b2 (.p3z m2 :: ls') k ds) || !ValidEvenLs (.p3z m2 :: ls')) =
                  false := by
              simp [hgd, hds2', hds1', heven]
            rw [bool_if_false_eq_self h_g]
            rw [if_neg (show ¬(k ≥ 2) by omega)]
            have hok_phi' : (if ds = [] ∧ epW (.p3z m2 :: ls') = 0 then
                decide (k ≤ 1) && isP3zP5 (.p3z m2 :: ls') &&
                  decide (headP3zVal (.p3z m2 :: ls') ≥ 20 - 2 * k ∧
                    z0 (p5Suf (.p3z m2 :: ls')) ≥ 38)
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
                  decide (2 < 2 * k + (epSum (.p3z m2 :: ls') +
                    2)) from decide_eq_of_iff (by omega)]
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

theorem step_Inv_ModeB_ge3_c0 (ls : List LTok) (a : Nat) (ds : List Nat)
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
      · simp only [h2, not_true_eq_false, ↓reduceIte] at hds2 ⊢
        simp only [ha, decide_true, hasP5, hmd_eq, p5Suf, isHeadP5, Bool.not_false,
          Bool.and_true, hepsum_eq, Nat.zero_add] at hds2 ⊢
        simp only [Bool.and_eq_true] at hds2 ⊢
        exact ⟨hds2.1.1, hds2.2⟩
      · simp [h2]
    have hds1' : checkDs1Phi1 (.ModeE_c1 (.p3z a :: ls) 0 ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
        rw [if_pos ha, if_pos ha] at hds1
        by_cases he2 : epW (.p3z a :: ls) = 2
        · simp only [he2, not_true_eq_false, ↓reduceIte]
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
          simp only [hasP5, hmd_eq, isHeadP5, Bool.not_false, Bool.and_true, hepsum_eq,
            Nat.zero_add] at hds1 ⊢
          exact hds1
        · simp [he2]
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_c1 (.p3z a :: ls) 0 ds) ||
          !checkDs1Phi1 (.ModeE_c1 (.p3z a :: ls) 0 ds) || !ValidEvenLs (.p3z a :: ls)) = false :=
            by
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
                (headP3zVal (.p3z a :: .p5 :: suf) ≥ 22 - 2 * 0 ∧
                  z0 (p5Suf (.p3z a :: .p5 :: suf)) ≥ 38))
          else
            decide (0 ≤ 1 ∧ epW (.p3z a :: .p5 :: suf) ≥ 1 ∧
              2 * 0 + prefSumW (.p3z a :: .p5 :: suf) ≤ 4) &&
              GoodPhiW (epW (.p3z a :: .p5 :: suf) - 1) [] false) = true := by
          rw [if_pos ⟨rfl, hepw0⟩]
          simp only [isP3zP5, headP3zVal, p5Suf, Bool.and_eq_true, true_and, and_true,
            decide_eq_true_eq]
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
              (headP3zVal (.p3z a :: .p5 :: suf) ≥ 22 - 2 * 0 ∧
                z0 (p5Suf (.p3z a :: .p5 :: suf)) ≥ 38))
        else
          decide (0 ≤ 1 ∧ epW (.p3z a :: .p5 :: suf) ≥ 1 ∧
            2 * 0 + prefSumW (.p3z a :: .p5 :: suf) ≤ 4) &&
            GoodPhiW (epW (.p3z a :: .p5 :: suf) - 1) [] false) = true := by
        rw [if_pos ⟨rfl, hepw0⟩]
        dsimp [p5Suf] at hz38
        simp only [isP3zP5, headP3zVal, p5Suf, Bool.and_eq_true, true_and, and_true,
          decide_eq_true_eq]
        omega
      rw [not_bool_if_false_eq_true hok_phi']
      have hmd0 : MustDrain (.p3z a :: .p5 :: suf) = false := by
        dsimp [MustDrain]; rw [if_pos hm1]
      have h_not_le : decide (2 ≥ 2 * 0 + epSum (.p3z a :: .p5 :: suf)) = false := by
        rw [decide_eq_false_iff_not]; dsimp [epSum]; rw [if_pos hm1]; omega
      have h_odd_f : (hasOdd (.p3z a :: .p5 :: suf) && decide (2 ≥
        2 * 0 + epSum (.p3z a :: .p5 :: suf))) = false := by
        rw [h_not_le, Bool.and_false]
      rw [bool_if_false_eq_self (by simp [hmd0]), h_odd_f]; rfl
    · intro fuel
      have hf := hch fuel
      dsimp only [invChain] at hf ⊢
      rw [if_neg ha, if_neg (show ¬(a = 1 ∧ 0 = 1 ∧
        ([] : List Nat) = []) by omega), if_pos rfl] at hf
      rw [if_pos ⟨rfl, hepw0⟩]
      have hnot : (!((0 : Nat) = 0 ∧ headP3zVal (.p3z a :: .p5 :: suf) = 0)) = true := by
        dsimp [headP3zVal]; simp [show a ≠ 0 by omega]
      rw [if_pos hnot]
      dsimp only [headP3zVal, drop2L, drop1L] at hf ⊢
      exact hf

theorem step_Inv_ModeB_ge3_cpos (ls : List LTok) (a c' : Nat) (ds : List Nat)
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
      · simp only [h2, not_true_eq_false, ↓reduceIte] at hds2 ⊢
        simp only [ha, decide_true, hasP5, hmd_eq, p5Suf, isHeadP5, Bool.not_false,
          Bool.and_true, hepsum_eq, Nat.zero_add] at hds2 ⊢
        rw [show decide (a + epSum ls ≥ 2 * c' + 6) = decide (a + epSum ls ≥ 2 * (c' + 1) + 4) from
          decide_eq_of_iff (by omega)]
        simp only [Bool.and_eq_true] at hds2 ⊢
        exact ⟨hds2.1.1, hds2.2⟩
      · simp [h2]
    have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z a :: ls) 0 c' ds) = true := by
      dsimp [checkDs1Phi1] at hds1 ⊢
      by_cases h1 : ds = [1]
      · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
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
            simp only [isHeadP5, hasP5, MustDrain, ↓reduceIte, decide_true, Bool.not_true,
              Bool.false_eq_true,
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
            simp only [hasP5, hmd_eq, Bool.not_false, Bool.and_true, hepsum_eq,
              Nat.zero_add] at hds1 ⊢
            rw [show decide (a + epSum ls ≥ 2 * c' + 14) =
              decide (a + epSum ls ≥ 2 * (c' + 1) + 12) from
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
            (decide (ds = [] ∧
              c' + epW (.p3z a :: .p5 :: suf) = 1) && MustDrain (.p3z a :: .p5 :: suf) &&
              decide (c' + ep (.p3z a :: .p5 :: suf) = 1 ∧
                0 + epSum (.p3z a :: .p5 :: suf) + 2 * ep (.p3z a :: .p5 :: suf) = 2) &&
              hasP5 (.p3z a :: .p5 :: suf) && decide (preP5Val (.p3z a :: .p5 :: suf) ≥ 16 ∧
                z0 (p5Suf (.p3z a :: .p5 :: suf)) ≥ 38)) ||
              GoodPhiW (c' +
                epW (.p3z a :: .p5 :: suf)) ds (isHeadP3z1 (.p3z a :: .p5 :: suf) && decide (0 = 0 ∧
                c' = 0 ∧ ds = []))
          else
            decide (c' = 0 ∧ ds = [] ∧
              (0 : Nat) = 2) || (decide (c' ≥ 1) && GoodPhiW (c' - 1) ds false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z a :: .p5 :: suf)) = true := rfl
          rw [if_pos hnp5_t, hphiw', Bool.or_true]
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd0 : MustDrain (.p3z a :: .p5 :: suf) = false := by
          rw [MustDrain_p3z_even_cons a (.p5 :: suf) ha]; rfl
        have hodd0 : hasOdd (.p3z a :: .p5 :: suf) = false := by
          rw [hasOdd_p3z_even_cons a (.p5 :: suf) ha]; rfl
        have h_rst_false : (decide ((0 : Nat) = 0 ∧ c' = 0 ∧
          ds = []) && isHeadP3z1 (.p3z a :: .p5 :: suf)) = false := by
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
              decide (c' + ep (.p3z a :: ls) = 1 ∧
                0 + epSum (.p3z a :: ls) + 2 * ep (.p3z a :: ls) = 2) &&
              hasP5 (.p3z a :: ls) && decide (preP5Val (.p3z a :: ls) ≥ 16 ∧
                z0 (p5Suf (.p3z a :: ls)) ≥ 38)) ||
              GoodPhiW (c' + epW (.p3z a :: ls)) ds (isHeadP3z1 (.p3z a :: ls) && decide (0 = 0 ∧
                c' = 0 ∧ ds = []))
          else
            decide (c' = 0 ∧ ds = [] ∧
              (0 : Nat) = 2) || (decide (c' ≥ 1) && GoodPhiW (c' - 1) ds false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z a :: ls)) = true := rfl
          rw [if_pos hnp5_t]
          cases Bool.or_eq_true_iff.mp hphi_or with
          | inl hphi1 =>
            apply Bool.or_inl
            rw [hmd_eq, hpre_eq]
            simp only [hasP5, p5Suf]
            rw [show decide (ds = [] ∧ c' + epW (.p3z a :: ls) = 1) = decide (ds = [] ∧
              c' + 1 + epW ls = 1) from
              decide_eq_of_iff ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩]
            rw [show decide (c' + ep (.p3z a :: ls) = 1 ∧
              0 + epSum (.p3z a :: ls) + 2 * ep (.p3z a :: ls) = 2) =
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
          rw [show decide (2 * c' + 4 < 0 + (a + epSum ls)) =
            decide (2 * (c' + 1) + 2 < a + epSum ls) from
            decide_eq_of_iff (by omega)]
          exact hmd_bound
        rw [bool_if_false_eq_self hmd_bound']
        have h_rst_false : (decide ((0 : Nat) = 0 ∧ c' = 0 ∧
          ds = []) && isHeadP3z1 (.p3z a :: ls)) = false := by
          rw [h_not_p3z1, Bool.and_false]
        rw [h_rst_false]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        rw [hodd_eq, hepsum_eq]
        have hd_odd : decide (2 * c' + 4 ≥ 0 + (a + epSum ls)) =
          decide (2 * (c' + 1) + 2 ≥ a + epSum ls) :=
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
      · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
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
            (decide (([] : List Nat) = [] ∧
              0 + epW (.p3z 1 :: ls) = 1) && MustDrain (.p3z 1 :: ls) &&
              decide (0 + ep (.p3z 1 :: ls) = 1 ∧
                0 + epSum (.p3z 1 :: ls) + 2 * ep (.p3z 1 :: ls) = 2) &&
              hasP5 (.p3z 1 :: ls) && decide (preP5Val (.p3z 1 :: ls) ≥ 16 ∧
                z0 (p5Suf (.p3z 1 :: ls)) ≥ 38)) ||
              GoodPhiW (0 + epW (.p3z 1 :: ls)) [] (isHeadP3z1 (.p3z 1 :: ls) && decide (0 = 0 ∧
                0 = 0 ∧ ([] : List Nat) = []))
          else
            decide ((0 : Nat) = 0 ∧ ([] : List Nat) = [] ∧
              (0 : Nat) = 2) || (decide (0 ≥ 1) && GoodPhiW (0 - 1) [] false)) = true := by
          have hnp5_t : (!isHeadP5 (.p3z 1 :: ls)) = true := rfl
          rw [if_pos hnp5_t, hepw0]
          dsimp [isHeadP3z1, GoodPhiW]
          simp
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_false : (MustDrain (.p3z 1 :: ls) && decide (2 * 0 + 4 < 0 +
          epSum (.p3z 1 :: ls))) = false := by
          rw [hepsum_odd]; simp
        rw [bool_if_false_eq_self hmd_false]
        have hrst_true : (decide ((0 : Nat) = 0 ∧ (0 : Nat) = 0 ∧
          ([] : List Nat) = []) && isHeadP3z1 (.p3z 1 :: ls)) = true := rfl
        rw [hrst_true]
        rw [if_neg (by decide)] at hok_c1
        dsimp only [drop1L]
        cases ls <;> simp [hok_c1]
      · have hrst_b : decide (a = 1 ∧ c' + 1 = 1 ∧ ds = []) = false := by
          rw [decide_eq_false_iff_not]
          intro ⟨h1, h2, h3⟩
          exact hrst ⟨h1, by omega, h3⟩
        have hrst_e : (decide ((0 : Nat) = 0 ∧ c' = 0 ∧
          ds = []) && isHeadP3z1 (.p3z a :: ls)) = false := by
          dsimp [isHeadP3z1]
          by_cases ha1 : a = 1
          · subst ha1
            have hnot : decide ((0 : Nat) = 0 ∧ c' = 0 ∧ ds = []) = false :=
              decide_eq_false (fun ⟨_, hc0, hds⟩ => hrst ⟨rfl, hc0, hds⟩)
            rw [hnot]; rfl
          · simp [ha1]
        have hstart_e : (isHeadP3z1 (.p3z a :: ls) && decide ((0 : Nat) = 0 ∧ c' = 0 ∧
          ds = [])) = false := by
          rw [Bool.and_comm]; exact hrst_e
        rw [hrst_b] at hok_c1
        simp only [Bool.not_false, ↓reduceIte] at hok_c1
        have hok_phi' : (if (!isHeadP5 (.p3z a :: ls)) = true then
            (decide (ds = [] ∧ c' + epW (.p3z a :: ls) = 1) && MustDrain (.p3z a :: ls) &&
              decide (c' + ep (.p3z a :: ls) = 1 ∧
                0 + epSum (.p3z a :: ls) + 2 * ep (.p3z a :: ls) = 2) &&
              hasP5 (.p3z a :: ls) && decide (preP5Val (.p3z a :: ls) ≥ 16 ∧
                z0 (p5Suf (.p3z a :: ls)) ≥ 38)) ||
              GoodPhiW (c' + epW (.p3z a :: ls)) ds (isHeadP3z1 (.p3z a :: ls) && decide (0 = 0 ∧
                c' = 0 ∧ ds = []))
          else
            decide (c' = 0 ∧ ds = [] ∧
              (0 : Nat) = 2) || (decide (c' ≥ 1) && GoodPhiW (c' - 1) ds false)) = true := by
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
        simp only [hodd_true, hepsum_odd, hep0, Nat.add_zero, Nat.zero_add, Nat.mul_zero,
          Bool.true_and]
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
          rw [show decide (ds = [] ∧ c' = 1 ∧ a - 1 = 2 ∧ preP5Val (.p3z a :: ls) ≥ 16 ∧
            z0 (p5Suf ls) ≥ 38) =
              decide (ds = [] ∧ c' = 1 ∧ a = 3 ∧ preP5Val (.p3z a :: ls) ≥ 16 ∧
                z0 (p5Suf ls) ≥ 38) from
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
      · rw [if_neg (fun ⟨h1, h2, h3⟩ => hrst ⟨h1,
        by omega, h3⟩), if_neg (Nat.succ_ne_zero c')] at hf
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

theorem ValidEvenLs_p5Suf (ls : List LTok) (heven : ValidEvenLs ls = true) (hp5 : hasP5 ls = true) :
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

theorem ValidP5Chain_p3z_p5 (m : Nat) (suf : List LTok) (hz : z0 suf ≥ 18) (hv : ValidP5Chain suf =
  true) :
    ValidP5Chain (.p3z m :: .p5 :: suf) = true := by
  cases m with
  | zero => dsimp [ValidP5Chain]; simp [hz, hv]
  | succ m' => dsimp [ValidP5Chain]; simp [hz, hv]

theorem ValidP5Chain_of_ValidEvenLs_z0Rep (ls : List LTok)
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

theorem GoodDs_d1_valid {d : Nat} (hd : d ≥ 3) (h : GoodDs [d] = true) : d ≥ 8 := by
  dsimp [GoodDs, GoodDsAux, GoodDs1] at h
  simp only [decide_eq_true_eq] at h
  omega

theorem GoodDs_pair_d2_cases {d d2 : Nat} {ds2 : List Nat} (h : GoodDs (d :: d2 :: ds2) = true) :
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
      · subst h1; simp only [Nat.one_ne_zero, ↓reduceIte,
        decide_eq_true_eq] at h; exact Or.inr (Or.inl ⟨rfl, rfl, h⟩)
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

theorem GoodDs_d31 {d : Nat} (h : GoodDs [d, 3, 1] = true) : d ≥ 19 := by
  dsimp [GoodDs, GoodDsAux] at h
  by_contra hlt
  have hdec : decide (3 = 3 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ d < 19) = true :=
    decide_eq_true ⟨rfl, rfl, rfl, by omega⟩
  rw [if_pos hdec] at h
  cases h

theorem GoodDs_d_ge25_1 {d d2 : Nat} (hd2 : d2 ≥ 25) (h : GoodDs [d, d2, 1] = true) : d ≥ 39 := by
  dsimp [GoodDs, GoodDsAux] at h
  by_contra hlt
  have hdec : decide (d2 ≥ 25 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ d < 39) = true :=
    decide_eq_true ⟨hd2, rfl, rfl, by omega⟩
  rw [if_neg (by omega)] at h
  rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
  rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
  rw [if_pos hdec] at h
  cases h

theorem GoodDs_isOddDrainDs_ge19 {d2 : Nat} {ds2 : List Nat} (hd2 : d2 ≥ 3)
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
      have hdec : (isOddDrain1 d3 && decide (d2 < 19)) = true := by
        simp [hod, show d2 < 19 by omega]
      rw [if_pos hdec] at h; cases h
    | cons d4 ds4 =>
      dsimp [GoodDs, GoodDsAux] at h
      have hd3 : d3 ≥ 3 := by
        cases ds4 with
        | nil =>
          cases d4 with
          | zero => dsimp [isOddDrainDs,
            isOddDrain1] at hod; simp only [decide_eq_true_eq] at hod; omega
          | succ _ => cases hod
        | cons _ _ =>
          cases d4 <;> cases hod
      rw [if_neg (by omega)] at h
      rw [bool_if_false_eq_true] at h; rcases h with ⟨_, h⟩
      by_contra hlt
      have hdec : (isOddDrainDs (d3 :: d4 :: ds4) && decide (d2 < 19)) = true := by
        simp [hod, show d2 < 19 by omega]
      rw [if_pos hdec] at h; cases h

theorem GoodPhiW_of_GoodDs_sub2 {d2 : Nat} {ds2 : List Nat} (hd2 : d2 ≥ 3) (h : GoodDs (d2 :: ds2) =
  true) :
    GoodPhiW (d2 - 2) ds2 false = true := by
  cases ds2 with
  | nil =>
    have hd8 := GoodDs_d1_valid hd2 h
    dsimp [GoodPhiW]; simp; omega
  | cons d3 ds3 =>
    rcases GoodDs_pair_d2_cases h with ⟨rfl, rfl, hd8⟩ | ⟨rfl, rfl, hd_or⟩ | ⟨hd3_ge3, hd2_17, _, _,
      _⟩
    · dsimp [GoodPhiW]; simp; omega
    · dsimp [GoodPhiW]; simp; omega
    · dsimp [GoodPhiW]
      rw [if_neg (by intro heq; injection heq with h1 _; omega)]
      rw [if_neg (by intro heq; injection heq with h1 _; omega)]
      rw [if_neg (by intro heq; injection heq with h1 _; omega)]
      split_ifs with h_25 hod
      · cases ds3 with
        | nil =>
          change false = true at h_25; cases h_25
        | cons d4 ds4 =>
          cases ds4 with
          | nil =>
            cases d4 with
            | zero =>
              change false = true at h_25; cases h_25
            | succ d4' =>
              cases d4' with
              | zero =>
                have hd3_25 : d3 ≥ 25 := of_decide_eq_true h_25
                have hd39 := GoodDs_d_ge25_1 hd3_25 h
                simp; omega
              | succ _ =>
                change false = true at h_25; cases h_25
          | cons _ _ =>
            cases d4 with
            | zero =>
              change false = true at h_25; cases h_25
            | succ d4' =>
              cases d4' with
              | zero =>
                change false = true at h_25; cases h_25
              | succ _ =>
                change false = true at h_25; cases h_25
      · have hd19 := GoodDs_isOddDrainDs_ge19 hd2 hod h
        simp; omega
      · simp; omega

theorem checkChainAux_B_ge3_c0_ok_ge22 (fuel a : Nat) (suf : List LTok) (ha : a ≥ 22) :
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

theorem GoodDs_tail_any {d : Nat} {ds : List Nat} (h : GoodDs (d :: ds) = true) :
    GoodDs ds = true ∧ ds ≠ [2] := by
  cases ds with
  | nil => exact ⟨rfl, by decide⟩
  | cons d2 ds2 =>
    rcases GoodDs_pair_d2_cases h with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨hd2_3, _, hgd2, _, _⟩
    · exact ⟨rfl, by decide⟩
    · exact ⟨rfl, by decide⟩
    · exact ⟨hgd2, by intro heq; injection heq with h1 _; omega⟩

theorem step_Inv_ModeB_b2_mge2 (ls : List LTok) (m'' : Nat) (ds : List Nat)
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

theorem step_Inv_ModeB_b2_m1 (ls : List LTok) (ds : List Nat)
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
        have hbase : decide (1 + (1 + z0 ls) ≥ 8 ∧ 1 + 2 * (1 + z0 ls) ≥ 15) = true :=
          decide_eq_true ⟨by omega, by omega⟩
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
                (isHeadP3z1 (.p3z 0 :: .p3z 0 :: ls) && decide (2 = 0 ∧ 1 = 0 ∧
                  ([] : List Nat) = [])) = true := by
              rw [hepw2]; dsimp [GoodPhiW]; simp; omega
            have hok_phi2 : (if (!isHeadP5 (.p3z 0 :: .p3z 0 :: ls)) = true then
                (decide (([] : List Nat) = [] ∧
                  1 + epW (.p3z 0 :: .p3z 0 :: ls) = 1) && MustDrain (.p3z 0 :: .p3z 0 :: ls) &&
                  decide (1 + ep (.p3z 0 :: .p3z 0 :: ls) = 1 ∧
                    2 + epSum (.p3z 0 :: .p3z 0 :: ls) + 2 * ep (.p3z 0 :: .p3z 0 :: ls) = 2) &&
                  hasP5 (.p3z 0 :: .p3z 0 :: ls) && decide (preP5Val (.p3z 0 :: .p3z 0 :: ls) ≥ 16 ∧
                    z0 (p5Suf (.p3z 0 :: .p3z 0 :: ls)) ≥ 38)) ||
                  GoodPhiW (1 +
                    epW (.p3z 0 :: .p3z 0 :: ls)) [] (isHeadP3z1 (.p3z 0 :: .p3z 0 :: ls) && decide
                    (2 = 0 ∧ 1 = 0 ∧ ([] : List Nat) = []))
              else
                decide (1 = 0 ∧ ([] : List Nat) = [] ∧
                  2 = 2) || (decide (1 ≥ 1) && GoodPhiW (1 - 1) [] false)) = true := by
              rw [if_pos (by rfl), hphiw2, Bool.or_true]
            rw [not_bool_if_false_eq_true hok_phi2]
            rw [hmd2, Bool.false_and, if_neg Bool.false_ne_true]
            have hrst_f : (decide ((2 : Nat) = 0 ∧ (1 : Nat) = 0 ∧
              ([] : List Nat) = []) && isHeadP3z1 (.p3z 0 :: .p3z 0 :: ls)) = false := rfl
            rw [hrst_f]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            by_cases h_odd_c : (hasOdd (.p3z 0 :: .p3z 0 :: ls) && decide (2 * 1 + 4 ≥
              2 + epSum (.p3z 0 :: .p3z 0 :: ls))) = true
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
              rw [epW_p3z_even_cons 0 _ rfl rfl, epW_p3z_even_cons 0 _ rfl rfl,
                epW_p3z_even_cons 0 ls rfl hnp5]; omega
            have hpref3 : prefSumW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 0 := by
              rw [prefSumW_p3z_even_cons 0 _ rfl rfl, prefSumW_p3z_even_cons 0 _ rfl rfl,
                prefSumW_p3z_even_cons 0 ls rfl hnp5, hpref0]
            have hmd3 : MustDrain (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = false := hmd0
            have hep3 : ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 3 + ep ls := by
              rw [ep_p3z_even_cons 0 _ rfl, ep_p3z_even_cons 0 _ rfl,
                ep_p3z_even_cons 0 ls rfl]; omega
            have hepsum3 : epSum (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = epSum ls := by
              dsimp [epSum]; omega
            have hodd3 : hasOdd (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = hasOdd ls := rfl
            have hp5_3 : hasP5 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = hasP5 ls := rfl
            refine ⟨?_, ?_⟩
            · have h_g : (!GoodDs [] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) 0 1
              []) ||
                  !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) 0 1 [])) = false :=
                    by
                dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
              dsimp only [invCore]
              rw [bool_if_false_eq_self h_g, if_pos (show (0 : Nat) % 2 = 0 by decide)]
              rw [not_bool_if_false_eq_true heven3]
              rw [hpref3, not_decide_if_false_eq_true (by omega)]
              have hphiw3 : GoodPhiW (1 + epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) []
                  (isHeadP3z1 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (0 = 0 ∧ 1 = 0 ∧
                    ([] : List Nat) = [])) = true := by
                rw [hepw3]; dsimp [GoodPhiW]; simp; omega
              have hok_phi3 : (if (!isHeadP5 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) = true then
                  (decide (([] : List Nat) = [] ∧
                    1 + epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) =
                    1) && MustDrain (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) &&
                    decide (1 + ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 1 ∧
                      0 + epSum (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) +
                      2 * ep (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) = 2) &&
                    hasP5 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (preP5Val (.p3z 0 :: .p3z 0
                      :: .p3z 0 :: ls) ≥ 16 ∧
                      z0 (p5Suf (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) ≥ 38)) ||
                    GoodPhiW (1 +
                      epW (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) [] (isHeadP3z1 (.p3z 0 :: .p3z 0 ::
                      .p3z 0 :: ls) && decide (0 = 0 ∧ 1 = 0 ∧ ([] : List Nat) = []))
                else
                  decide (1 = 0 ∧ ([] : List Nat) = [] ∧
                    0 = 2) || (decide (1 ≥ 1) && GoodPhiW (1 - 1) [] false)) = true := by
                rw [if_pos (by rfl), hphiw3, Bool.or_true]
              rw [not_bool_if_false_eq_true hok_phi3]
              rw [hmd3, Bool.false_and, if_neg Bool.false_ne_true]
              have hrst_f : (decide ((0 : Nat) = 0 ∧ (1 : Nat) = 0 ∧
                ([] : List Nat) = []) && isHeadP3z1 (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls)) = false :=
                rfl
              rw [hrst_f]
              simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
              by_cases h_odd_c : (hasOdd (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls) && decide (2 * 1 + 4 ≥
                0 + epSum (.p3z 0 :: .p3z 0 :: .p3z 0 :: ls))) = true
              · rw [if_pos h_odd_c]
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h_odd_c
                have hepw_ge3 : epW ls ≥ 3 := by
                  by_cases he2 : epW ls = 2
                  · dsimp [checkDs1Phi1] at hds1
                    simp only [he2, not_true_eq_false, ↓reduceIte, Bool.and_eq_true,
                      decide_eq_true_eq] at hds1
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
              have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by
                change 1 + (1 + z0 ls) = 2 + z0 ls; omega
              have hcond1_f : ¬(([0] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
                  isP3zP5 (.p3z 0 :: .p3z 0 :: ls) = true ∧
                    headP3zVal (.p3z 0 :: .p3z 0 :: ls) ≥ 3) := by
                intro ⟨h1, _⟩; cases h1
              have hcond2_f : ¬(([0] : List Nat) = [] ∧
                  ((1 = 1 ∧ 1 = 1 ∧ z0 (.p3z 0 :: .p3z 0 :: ls) = 1) ∨ (1 = 3 ∧ 1 = 2 ∧
                    z0 (.p3z 0 :: .p3z 0 :: ls) = 0)) ∧
                  isP3zP5 (dropZ0 (.p3z 0 :: .p3z 0 :: ls)) = true ∧
                  headP3zVal (dropZ0 (.p3z 0 :: .p3z 0 :: ls)) ≥ 18 ∧
                    z0 (p5Suf (.p3z 0 :: .p3z 0 :: ls)) ≥ 38) := by
                intro ⟨h1, _⟩; cases h1
              refine ⟨?_, ?_⟩
              · have h_g : (!GoodDs [0] || !checkDs2 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: ls) 1 1 [0])
                ||
                    !checkDs1Phi1 (.ModeE_ge2 (.p3z 0 :: .p3z 0 :: ls) 1 1 [0])) = false := by
                  dsimp [GoodDs, GoodDsAux, GoodDs1, checkDs2, checkDs1Phi1]; simp
                dsimp only [invCore]
                rw [bool_if_false_eq_self h_g, if_neg (show ¬((1 : Nat) % 2 = 0) by decide)]
                rw [not_bool_if_false_eq_true hvp5']
                rw [not_decide_if_false_eq_true (by omega)]
                rw [if_neg hcond1_f, if_neg hcond2_f, hz0_2]
                have hbase : decide (1 + (2 + z0 ls) ≥ 8 ∧ 1 + 2 * (2 + z0 ls) ≥ 15) = true :=
                  decide_eq_true ⟨by omega, by omega⟩
                have hod_f : isOddDrainDs [0] = false := rfl
                rw [hbase, hod_f]
                by_cases hz6 : z0 ls ≥ 6
                · have hkz17 : decide (1 + 2 * (2 + z0 ls) ≥ 17) = true := decide_eq_true (by omega)
                  rw [hkz17]; simp
                · have hcz_lt9 : decide (([0] = [] ∨ [0] = [0]) ∧
                  1 + (2 + z0 ls) ≥ 9 ∨ false = true) = false :=
                    decide_eq_false (by intro h_or; rcases h_or with ⟨_,
                      h9⟩ | h_f <;> first | omega | cases h_f)
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
                have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by
                  change 1 + (1 + z0 ls) = 2 + z0 ls; omega
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
                  if_neg (show ¬(0 + epW ls < if isOddDrainDs [m'' + 3] =
                    true then 18 else 16) by omega),
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
                  have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by
                    change 1 + (1 + z0 ls) = 2 + z0 ls; omega
                  have heven_new : ValidEvenLs (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true := by
                    dsimp [ValidEvenLs, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                  refine ⟨?_, ?_⟩
                  · have h_g : (!GoodDs [] || !checkDs2 (.ModeB_b2 (.p5 :: .p3z 0 :: .p3z 0 :: ls)
                    (m4 + 1) []) ||
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
                    rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                      if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                        if_pos (by exact decide_eq_true hd8),
                      if_neg (show ¬(0 + epW ls < if isOddDrainDs [m4 + 5, 0] =
                        true then 18 else 16) by omega),
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
                have h_or_f : ¬((m'' + 3) :: (c' + 1) :: ds'' = [] ∨
                    (m'' + 3) :: (c' + 1) :: ds'' = [0] ∨
                    (m'' + 3) :: (c' + 1) :: ds'' = [1] ∨
                    (m'' + 3) :: (c' + 1) :: ds'' = [2]) := by simp
                dsimp [GoodPhiW] at hphiw
                have hepw16 : epW ls ≥ 16 := by
                  split_ifs at hphiw <;> (simp only [decide_eq_true_eq] at hphiw; omega)
                have hz0_2 : z0 (.p3z 0 :: .p3z 0 :: ls) = 2 + z0 ls := by
                  change 1 + (1 + z0 ls) = 2 + z0 ls; omega
                have heven_new : ValidEvenLs (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true := by
                  dsimp [ValidEvenLs, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                rcases GoodDs_pair_d2_cases hgd with ⟨h_abs, _⟩ | ⟨hc'0, rfl, hd_or⟩ | ⟨hc'2, hd17,
                  hgd_tail, hsub1, hsub2⟩
                · cases h_abs
                · have hc'_z : c' = 0 := by omega
                  subst hc'_z
                  have h_d_cond1 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 ≤ 2 * 1 + 4 ∧
                    GoodDs [1 - 1] = false) := by
                    intro ⟨_, _, h_f⟩; cases h_f
                  have h_d_cond2 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 + 14 ≤ 2 * 1 ∧
                    GoodDs [1 - 2] = false) := by omega
                  rcases hd_or with hm''0 | hd25
                  · have hm''_z : m'' = 0 := by omega
                    subst hm''_z
                    refine ⟨?_, ?_⟩
                    · have h_g : (!GoodDs [] || !checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 ::
                      ls) 0 0 []) ||
                          !checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) 0 0 [])) =
                            false := by
                        dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
                      dsimp only [invCore]
                      rw [bool_if_false_eq_self h_g, if_pos (by decide),
                        not_bool_if_false_eq_true heven_new]
                      dsimp [isHeadP5, MustDrain, hasOdd]
                    · intro fuel
                      have hf := hch (fuel + 1)
                      rw [hch_step fuel] at hf
                      dsimp only [checkChainAux] at hf
                      rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                          if_neg (by exact Bool.false_ne_true),
                        if_neg h_or_f, if_pos ⟨by omega,
                          by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                        if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                        if_neg (show ¬((1 : Nat) = 1 ∧ ([] : List Nat) = [] ∧
                          0 + 3 ≥ 25) by omega)] at hf
                      dsimp only [invChain]
                      rw [if_pos (by decide), if_neg (by intro ⟨_, _, h22⟩; omega)]
                      exact hf
                  · have hm''22 : m'' ≥ 22 := by omega
                    have hepw36 : epW ls ≥ 36 := by
                      rw [if_pos (by exact decide_eq_true hd25)] at hphiw
                      simp only [decide_eq_true_eq] at hphiw
                      omega
                    have hz38 : z0 (.p3z 0 :: .p3z 0 :: ls) ≥ 38 := by omega
                    refine ⟨?_, ?_⟩
                    · have h_g : (!GoodDs [] || !checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 ::
                      ls) m'' 0 []) ||
                          !checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' 0 [])) =
                            false := by
                        dsimp [GoodDs, checkDs2, checkDs1Phi1]; simp
                      dsimp only [invCore]
                      rw [bool_if_false_eq_self h_g]
                      by_cases hm_ev : m'' % 2 = 0
                      · rw [if_pos hm_ev, not_bool_if_false_eq_true heven_new]
                        dsimp [isHeadP5, p5Suf, MustDrain, hasOdd]
                        simp [hm''22, hz38]
                      · have hm''23 : m'' ≥ 23 := by omega
                        have heven_odd : ValidEvenLs (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) =
                          true := by
                          dsimp [ValidEvenLs]; rw [if_neg hm_ev]
                          dsimp [ValidAfterOdd, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                        rw [if_neg hm_ev]
                        have h_c0_ok : ¬((0 : Nat) = 0 ∧ (!decide (([] : List Nat) = [] ∧ m'' ≥ 23 ∧
                            isHeadP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls) = true ∧
                            z0 (p5Suf (.p5 :: .p3z 0 :: .p3z 0 :: ls)) ≥ 38)) = true) := by
                          dsimp [isHeadP5, p5Suf]; simp [hm''23, hz38]
                        rw [if_neg h_c0_ok, not_bool_if_false_eq_true heven_odd]
                        have hmd_f : MustDrain (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) =
                          false := by
                          dsimp [MustDrain]; split_ifs <;> rfl
                        rw [hmd_f, Bool.false_and, if_neg Bool.false_ne_true,
                          if_neg (show ¬(m'' ≤ 2 * 0 + 3) by omega)]; simp
                    · intro fuel
                      have hf := hch (fuel + 1)
                      rw [hch_step fuel] at hf
                      dsimp only [checkChainAux] at hf
                      rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                          if_neg (by exact Bool.false_ne_true),
                        if_neg h_or_f, if_pos ⟨by omega,
                          by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                        if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                        if_pos ⟨rfl, rfl, hd25⟩] at hf
                      have h_ok_t :=
                        checkChainAux_B_ge3_c0_ok_ge22 fuel m'' (.p3z 0 :: .p3z 0 :: ls) hm''22
                      have hm_sub : m'' - 8 = m'' + 3 - 11 := by omega
                      dsimp only [invChain]
                      by_cases hm_ev : m'' % 2 = 0
                      · rw [if_pos hm_ev, if_pos ⟨rfl, rfl, hm''22⟩, h_ok_t, Bool.true_and]
                        dsimp only [drop1L]; rw [hm_sub]; exact hf
                      · rw [if_neg hm_ev, if_neg (show ¬(m'' = 1 ∧ (0 : Nat) = 1 ∧
                        ([] : List Nat) = []) by omega),
                          if_pos rfl, h_ok_t, Bool.true_and]
                        dsimp only [drop1L]; rw [hm_sub]; exact hf
                · obtain ⟨hgd_ds'', hds''_ne2⟩ := GoodDs_tail_any hgd_tail
                  have h_d_cond1 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 ≤ 2 * (c' + 1) + 4 ∧
                    GoodDs ((c' + 1 - 1) :: ds'') = false) := by
                    intro ⟨h1, h2, h3⟩; rw [hsub1 ⟨h1, h2⟩] at h3; cases h3
                  have h_d_cond2 : ¬((m'' + 3) % 2 = 0 ∧ m'' + 3 + 14 ≤ 2 * (c' + 1) ∧
                    GoodDs ((c' + 1 - 2) :: ds'') = false) := by
                    intro ⟨h1, h2, h3⟩; rw [hsub2 ⟨h1, h2⟩] at h3; cases h3
                  have h_not_25_1 : ¬(c' + 1 = 1 ∧ ds'' = [] ∧ m'' + 3 ≥ 25) := by omega
                  have hds2' : checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'') =
                    true := by
                    dsimp [checkDs2]; rw [if_pos hds''_ne2]
                  have hds1' : checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'')
                    = true := by
                    dsimp [checkDs1Phi1]
                    by_cases h1 : ds'' = [1]
                    · subst h1
                      simp only [not_true_eq_false, ↓reduceIte]
                      rcases GoodDs_pair_d2_cases hgd_tail with ⟨h_abs, _⟩ | ⟨_, _,
                        hd_c_or⟩ | ⟨h_abs, _⟩
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
                    have h_g : (!GoodDs ds'' || !checkDs2 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 ::
                      ls) m'' c' ds'') ||
                        !checkDs1Phi1 (.ModeB_ge3 (.p5 :: .p3z 0 :: .p3z 0 :: ls) m'' c' ds'')) =
                          false := by
                      simp [hgd_ds'', hds2', hds1']
                    rw [bool_if_false_eq_self h_g]
                    by_cases hm_ev : m'' % 2 = 0
                    · rw [if_pos hm_ev, not_bool_if_false_eq_true heven_new]
                      have hip5_f : (!isHeadP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls)) = false := rfl
                      rw [hip5_f, if_neg Bool.false_ne_true,
                        if_neg (show c' ≠ 0 by omega), not_bool_if_false_eq_true hphiw_c']
                      rfl
                    · have heven_odd : ValidEvenLs (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) =
                      true := by
                        dsimp [ValidEvenLs]; rw [if_neg hm_ev]
                        dsimp [ValidAfterOdd, ValidP5Chain]; rw [hz0_2]; simp [hvp5]; omega
                      rw [if_neg hm_ev, if_neg (by intro ⟨hc0, _⟩; omega),
                        not_bool_if_false_eq_true heven_odd]
                      have hrst_f : decide (m'' = 1 ∧ c' = 1 ∧ ds'' = []) = false :=
                        decide_eq_false (by intro ⟨_, hc1, _⟩; omega)
                      have hmd_f : MustDrain (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) = false :=
                        by
                        dsimp [MustDrain]; split_ifs <;> rfl
                      have hok_c1' : (if c' ≥ 1 then
                          if (!decide (m'' = 1 ∧ c' = 1 ∧ ds'' = [])) = true then
                            (decide (ds'' = [] ∧ c' = 2 ∧
                              m'' = 3) && MustDrain (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) &&
                              hasP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls) &&
                              decide (preP5Val (.p3z m'' :: .p5 :: .p3z 0 :: .p3z 0 :: ls) ≥ 16 ∧
                                z0 (p5Suf (.p5 :: .p3z 0 :: .p3z 0 :: ls)) ≥ 38)) ||
                              GoodPhiW (c' - 1) ds'' false
                          else isP3zGe1P5 (.p5 :: .p3z 0 :: .p3z 0 :: ls)
                        else true) = true := by
                        rw [if_pos (by omega), hrst_f, if_pos (by rfl), hphiw_c', Bool.or_true]
                      rw [not_bool_if_false_eq_true hok_c1', hmd_f, Bool.false_and,
                        if_neg Bool.false_ne_true]
                      by_cases h_le : m'' ≤ 2 * c' + 3
                      · rw [if_pos h_le, hrst_f, if_neg Bool.false_ne_true]
                        have hgp : GoodPsi (c' - 1) ds'' = true := by
                          dsimp [GoodPsi]
                          have h_eq_c : c' - 1 + 1 = c' + 1 - 1 := by omega
                          rw [h_eq_c]
                          exact hsub1 ⟨by omega, by omega⟩
                        have h_not_8 : decide ((ds'' = [] ∨ ds'' = [0]) ∧ c' - 1 ≥ 8 ∧
                            ((!hasP5 (.p5 :: .p3z 0 :: .p3z 0 :: ls)) = true ∨
                              false = true)) = false := by
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
                    cases ds'' with
                    | nil =>
                      rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                          if_neg (by exact Bool.false_ne_true),
                        if_neg h_or_f, if_pos ⟨by omega,
                          by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                        if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                        if_neg h_not_25_1] at hf
                      have hm_sub : m'' + 3 - 3 = m'' := by omega
                      have hc_sub : c' + 1 - 1 = c' := by omega
                      have hm_mul : 2 * (c' + 1) = 2 * c' + 2 := by omega
                      rw [hm_sub, hc_sub, hm_mul] at hf
                      dsimp only [invChain]
                      by_cases hm_ev : m'' % 2 = 0
                      · rw [if_pos hm_ev, if_neg (by intro ⟨_, hc0, _⟩; omega)]; exact hf
                      · rw [if_neg hm_ev, if_neg (by intro ⟨_, hc1, _⟩; omega),
                        if_neg (by omega)]; exact hf
                    | cons d_ds ds_rest =>
                      rw [hdec_0_2, hnp5, Bool.and_false, Bool.or_false, Bool.and_false,
                        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
                          if_neg (by exact Bool.false_ne_true),
                        if_neg h_or_f, if_pos ⟨by omega,
                          by omega⟩, if_neg h_d_cond1, if_neg h_d_cond2,
                        if_neg (show ¬(0 + epW ls < 16) by omega), hz_ls0,
                        if_neg h_not_25_1] at hf
                      have hm_sub : m'' + 3 - 3 = m'' := by omega
                      have hc_sub : c' + 1 - 1 = c' := by omega
                      have hm_mul : 2 * (c' + 1) = 2 * c' + 2 := by omega
                      rw [hm_sub, hc_sub, hm_mul] at hf
                      dsimp only [invChain]
                      by_cases hm_ev : m'' % 2 = 0
                      · rw [if_pos hm_ev, if_neg (by intro ⟨_, hc0, _⟩; omega)]; exact hf
                      · rw [if_neg hm_ev, if_neg (by intro ⟨_, hc1, _⟩; omega),
                        if_neg (by omega)]; exact hf

theorem step_Inv_ModeB_b2 (ls : List LTok) (m : Nat) (ds : List Nat)
    (hinv : Inv (.ModeB_b2 ls m ds)) :
    Inv (nextState (.ModeB_b2 ls m ds)) := by
  cases m with
  | zero => exact step_Inv_ModeB_b2_m0 ls ds hinv
  | succ m' =>
    cases m' with
    | zero => exact step_Inv_ModeB_b2_m1 ls ds hinv
    | succ m'' => exact step_Inv_ModeB_b2_mge2 ls m'' ds hinv

theorem prefSumW_of_ValidP5Chain (ls : List LTok) (h : ValidP5Chain ls = true) :
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

theorem MustDrain_of_ValidP5Chain (ls : List LTok) (h : ValidP5Chain ls = true) :
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

theorem ep_ge_z0 (ls : List LTok) : ep ls ≥ z0 ls := by
  induction ls with
  | nil => simp [z0, ep]
  | cons tok rest ih =>
    cases tok with
    | p5 => simp [z0, ep]
    | p3z m =>
      cases m with
      | zero => change 1 + z0 rest ≤ 1 + ep rest; omega
      | succ _ => simp [z0]

theorem epW_add1_ge_z0 (ls : List LTok) : epW ls + 1 ≥ z0 ls := by
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

theorem isHeadP5_false_of_z0_pos {ls : List LTok} (h : z0 ls ≥ 1) : isHeadP5 ls = false := by
  cases ls with
  | nil => simp [z0] at h
  | cons tok _ =>
    cases tok with
    | p5 => simp [z0] at h
    | p3z _ => rfl

theorem isHeadP3z1_false_of_z0_pos {ls : List LTok} (h : z0 ls ≥ 1) : isHeadP3z1 ls = false := by
  cases ls with
  | nil => simp [z0] at h
  | cons tok _ =>
    cases tok with
    | p5 => simp [z0] at h
    | p3z m => cases m with | zero => rfl | succ _ => simp [z0] at h

theorem hasP5_of_ValidP5Chain_hasOdd (ls : List LTok) (hv : ValidP5Chain ls =
  true) (ho : hasOdd ls = true) :
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

theorem ds_ne_two_of_checkDs2_ModeE_ge2 {ls : List LTok} {k c : Nat} {ds : List Nat}
    (h : checkDs2 (.ModeE_ge2 ls k c ds) = true)
    (h_imp : hasP5 ls = false ∨ MustDrain ls = true ∨ k % 2 = 1 ∨ isHeadP5 ls = true ∨
      k + epSum ls < 2 * c + 6) :
    ds ≠ [2] := by
  intro rfl
  dsimp [checkDs2] at h
  rcases h_imp with hp | hm | hk | hip | hlt
  · simp [hp] at h
  · simp [hm] at h
  · have hk0 : decide (k % 2 = 0) = false := decide_eq_false (by omega)
    simp [hk0] at h
  · simp [hip] at h
  · simp at h; omega

theorem d25_check_of_ge36 (cz : Nat) (ds : List Nat) :
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
            by_cases hd : d ≥ 25
            · simp [hd, h d rfl hd]
            · simp [hd]
          | succ _ => intro _; rfl
      | cons _ _ =>
        cases d2 with
        | zero => intro _; rfl
        | succ d2' =>
          cases d2' with
          | zero => intro _; rfl
          | succ _ => intro _; rfl

theorem d25_ge36_of_check {c : Nat} {ds : List Nat}
    (h : (!(match ds with | [d, 1] => decide (d ≥ 25) | _ => false) || decide (c ≥ 36)) = true) :
    ∀ d, ds = [d, 1] → d ≥ 25 → c ≥ 36 := by
  intro d rfl hd
  simpa [hd] using h

theorem GoodPhiW_d25_ge35 {phiW : Nat} {d : Nat} (hd : d ≥ 25)
    (h : GoodPhiW phiW [d, 1] false = true) : phiW ≥ 35 := by
  dsimp only [GoodPhiW] at h
  split_ifs at h with h1 h2 h3 h4 h5
  · cases h1
  · cases h2
  · cases h3
  · cases h4
  · exact of_decide_eq_true h
  · exfalso; apply h5; exact decide_eq_true hd
  · exfalso; apply h5; exact decide_eq_true hd

theorem prefSumW_p3z_m2_bound (m2 : Nat) (ls' : List LTok) (k c : Nat)
    (hk1 : k ≤ 2 * c + 4) (hk2 : k + prefSumW (.p3z (m2 + 2) :: ls') ≤ 2 * c + 6) :
    k + prefSumW (.p3z m2 :: ls') ≤ 2 * c + 4 := by
  by_cases hm : m2 % 2 = 1
  · have h0 : prefSumW (.p3z m2 :: ls') = 0 := by dsimp [prefSumW]; rw [if_pos hm]
    omega
  · by_cases hp5 : isHeadP5 ls' = true
    · have h0 : prefSumW (.p3z m2 :: ls') = 0 := by
        dsimp [prefSumW]; rw [if_neg hm]
        cases ls' with | nil => cases hp5 | cons t s => cases t with | p3z _ => cases hp5 | p5 =>
          rfl
      omega
    · have hp5_f : isHeadP5 ls' = false := Bool.eq_false_iff.mpr hp5
      have := prefSumW_p3z_add2 m2 ls' (by omega) hp5_f
      omega

theorem ValidP5Chain_p3z_succ {m : Nat} {ls' : List LTok}
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

theorem GoodPhiW_of_ge17_and_d25 (phiW : Nat) (ds : List Nat) (hne2 : ds ≠ [2])
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

theorem step_Inv_ModeE_ge2_nil (k c : Nat) (ds : List Nat)
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
      have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 [] k c ds) || !checkDs1Phi1 (.ModeB_ge3 [] k c
        ds)) = false := by
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
        simp only [isHeadP5, epW, hasP5, hphiw_c, Bool.or_true, Bool.and_true,
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
    simp only [Nat.add_zero, Bool.not_false, Bool.true_and] at hf1
    rw [bool_if_false_eq_true] at hf1
    rcases hf1 with ⟨hphiw_f, hf1⟩
    rw [not_bool_eq_false] at hphiw_f
    simp only [Bool.and_eq_true] at hf1
    have hgp : GoodPsi (c - 1) ds = true := hf1.1
    have hds1' : checkDs1Phi1 (.ModeB_ge3 [] k c ds) = true := by
      dsimp [checkDs1Phi1]
      by_cases h1 : ds = [1]
      · simp only [h1, not_true_eq_false, ↓reduceIte]
        rw [if_neg hk]
        have hc2 : decide (c = 2) = false := decide_eq_false (by omega)
        rw [hc2]; rfl
      · simp [h1]
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 [] k c ds) || !checkDs1Phi1 (.ModeB_ge3 [] k c
        ds)) = false := by
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
      rw [hmd_t, hdec_gt, Bool.and_false, if_neg Bool.false_ne_true, if_pos hck.2, hrst_f,
        if_neg Bool.false_ne_true]
      rw [hgp, Bool.true_and]
      have h_ds1_ok : ((!decide (ds = [1] ∧ c - 1 ≥ 24)) || decide (k ≥ 37)) = true := by
        by_cases h1 : ds = [1]
        · simp [h1] at hc_1; simp [hc_1]
        · simp [h1]
      have h_ds0_ok : ((!decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧
        ((!hasP5 []) = true ∨ true = true))) ||
          decide (k ≥ 17)) = true := by
        by_cases h0 : (ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8
        · have hc9 : ((ds = [] ∨ ds = [0]) ∧
          c ≥ 9) ∨ isOddDrainDs ds = true := Or.inl ⟨h0.1, by omega⟩
          have hc9_d : decide (((ds = [] ∨ ds = [0]) ∧ c ≥ 9) ∨ isOddDrainDs ds = true) = true :=
            decide_eq_true hc9
          rw [hc9_d] at hc_9
          simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_9
          simp [hc_9]
        · have h_f : decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧
          ((!hasP5 []) = true ∨ true = true)) = false :=
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
        rw [if_neg hk, if_neg (show ¬(k = 1 ∧ c = 1 ∧
          ds = []) by omega), if_neg (show c ≠ 0 by omega)]
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
        simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero,
          Nat.zero_add, Nat.mul_zero]
        have hk3 : k - 1 + 3 = k + 2 := by omega
        have hk2 : k - 1 + 2 = k + 1 := by omega
        rw [hk3, hk2]
        exact hf

theorem step_Inv_ModeE_ge2_p3z0 (ls' : List LTok) (k c : Nat) (ds : List Nat)
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
              decide (c + 1 + ep (.p5 :: suf) = 1 ∧
                k + 2 + epSum (.p5 :: suf) + 2 * ep (.p5 :: suf) = 2) &&
              hasP5 (.p5 :: suf) && decide (preP5Val (.p5 :: suf) ≥ 16 ∧
                z0 (p5Suf (.p5 :: suf)) ≥ 38)) ||
              GoodPhiW (c + 1 + epW (.p5 :: suf)) ds (isHeadP3z1 (.p5 :: suf) && decide (k + 2 = 0 ∧
                c + 1 = 0 ∧ ds = []))
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
          rw [show decide (k + 2 + epSum ls' ≥ 2 * (c + 1) + 6) =
            decide (k + epSum ls' ≥ 2 * c + 6) from
            decide_eq_of_iff (by omega)]
          exact hds2
        · rw [if_pos h2]
      have hds1' : checkDs1Phi1 (.ModeE_ge2 ls' (k + 2) (c + 1) ds) = true := by
        dsimp [checkDs1Phi1] at hds1 ⊢
        by_cases h1 : ds = [1]
        · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
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
            rw [show decide (k + 2 + epSum ls' ≥ 2 * (c + 1) + 14) =
              decide (k + epSum ls' ≥ 2 * c + 14) from
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
        have hstart_0 : (isHeadP3z1 (.p3z 0 :: ls') && decide (k = 0 ∧ c = 0 ∧ ds = [])) = false :=
          rfl
        have hstart_1 : (isHeadP3z1 ls' && decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = [])) = false := by
          have hne : decide (k + 2 = 0 ∧ c + 1 = 0 ∧ ds = []) = false := decide_eq_false (by omega)
          rw [hne, Bool.and_false]
        rw [hstart_0] at hok_phi
        have hok_phi' : (if (!isHeadP5 ls') = true then
            (decide (ds = [] ∧ c + 1 + epW ls' = 1) && MustDrain ls' &&
              decide (c + 1 + ep ls' = 1 ∧ k + 2 + epSum ls' + 2 * ep ls' = 2) &&
              hasP5 ls' && decide (preP5Val ls' ≥ 16 ∧ z0 (p5Suf ls') ≥ 38)) ||
              GoodPhiW (c + 1 + epW ls') ds (isHeadP3z1 ls' && decide (k + 2 = 0 ∧ c + 1 = 0 ∧
                ds = []))
          else
            decide (c + 1 = 0 ∧ ds = [] ∧
              k + 2 = 2) || (decide (c + 1 ≥ 1) && GoodPhiW (c + 1 - 1) ds false)) = true := by
          rw [if_pos h_np5, hstart_1]
          have hpw_eq : c + 1 + epW ls' = c + epW (.p3z 0 :: ls') := by omega
          have hp_eq : c + 1 + ep ls' = c + ep (.p3z 0 :: ls') := by omega
          have hx_eq : k + 2 + epSum ls' + 2 * ep ls' =
            k + epSum (.p3z 0 :: ls') + 2 * ep (.p3z 0 :: ls') := by omega
          rw [hpw_eq, hp_eq, hx_eq, ← hmd_eq, ← hpre_eq]
          exact hok_phi
        rw [not_bool_if_false_eq_true hok_phi']
        have hmd_bound' : (MustDrain ls' && decide (2 * (c + 1) + 4 < k + 2 + epSum ls')) = false :=
          by
          rw [hmd_eq, hepsum_eq, Nat.zero_add] at hmd_bound
          rw [show decide (2 * (c + 1) + 4 < k + 2 + epSum ls') =
            decide (2 * c + 4 < k + epSum ls') from
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
        have hd_odd : decide (2 * (c + 1) + 4 ≥ k + 2 + epSum ls') =
          decide (2 * c + 4 ≥ k + epSum ls') :=
          decide_eq_of_iff (by omega)
        rw [hd_odd]
        by_cases h_cond : (hasOdd ls' && decide (2 * c + 4 ≥ k + epSum ls')) = true
        · rw [if_pos h_cond, hrst_0, if_neg Bool.false_ne_true] at hodd_branch
          rw [if_pos h_cond]
          have hp_eq : c + 1 + ep ls' = c + ep (.p3z 0 :: ls') := by omega
          have hx_eq : k + 2 + epSum ls' + 2 * ep ls' = k + epSum ls' + 2 * ep (.p3z 0 :: ls') := by
            omega
          rw [hp_eq, hx_eq, ← hmd_eq, ← hpre_eq]
          exact hodd_branch
        · rw [if_neg h_cond]
      · intro fuel
        have hf := hch fuel
        dsimp only [invChain] at hf ⊢
        rw [if_pos hk, if_neg (by simp [isHeadP3z1])] at hf
        rw [if_pos hk2_ev, if_neg (show ¬(k + 2 = 0 ∧ c + 1 = 0 ∧ ds = [] ∧
          isHeadP3z1 ls' = true) by omega)]
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
      · simp only [h1, not_true_eq_false, ↓reduceIte]; rw [if_neg hk2_odd]; rfl
      · simp [h1]
    rw [if_neg hk] at hc
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hvp5, hc⟩
    rw [not_bool_eq_false] at hvp5
    dsimp [ValidP5Chain] at hvp5
    rw [bool_if_false_eq_true] at hc
    rcases hc with ⟨hck, hc⟩
    rw [not_bool_eq_false, decide_eq_true_eq] at hck
    have h_not_b1_0 : ¬(ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 (.p3z 0 :: ls') = true ∧
      headP3zVal (.p3z 0 :: ls') ≥ 3) := by
      dsimp [headP3zVal]; omega
    have h_not_b1_1 : ¬(ds = [] ∧ k + 2 = 1 ∧ c + 1 = 1 ∧ isP3zP5 ls' = true ∧
      headP3zVal ls' ≥ 3) := by
      omega
    rw [if_neg h_not_b1_0] at hc
    have hz_eq : c + 1 + z0 ls' = c + z0 (.p3z 0 :: ls') := by
      change c + 1 + z0 ls' = c + (1 + z0 ls'); omega
    have hk_eq : k + 2 + 2 * z0 ls' = k + 2 * z0 (.p3z 0 :: ls') := by
      change k + 2 + 2 * z0 ls' = k + 2 * (1 + z0 ls'); omega
    have hb2_iff : (ds = [] ∧ ((k + 2 = 1 ∧ c + 1 = 1 ∧ z0 ls' = 1) ∨ (k + 2 = 3 ∧ c + 1 = 2 ∧
      z0 ls' = 0)) ∧
        isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38) ↔
        (ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 (.p3z 0 :: ls') = 1) ∨ (k = 3 ∧ c = 2 ∧
          z0 (.p3z 0 :: ls') = 0)) ∧
        isP3zP5 (dropZ0 (.p3z 0 :: ls')) = true ∧ headP3zVal (dropZ0 (.p3z 0 :: ls')) ≥ 18 ∧
          z0 (p5Suf (.p3z 0 :: ls')) ≥ 38) := by
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
      by_cases hb2 : ds = [] ∧ ((k + 2 = 1 ∧ c + 1 = 1 ∧ z0 ls' = 1) ∨ (k + 2 = 3 ∧ c + 1 = 2 ∧
        z0 ls' = 0)) ∧
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
      by_cases hb2 : ds = [] ∧ ((k + 2 = 1 ∧ c + 1 = 1 ∧ z0 ls' = 1) ∨ (k + 2 = 3 ∧ c + 1 = 2 ∧
        z0 ls' = 0)) ∧
          isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38
      · rw [if_pos hb2]
        rw [if_pos (hb2_iff.mp hb2)] at hf
        exact hf
      · rw [if_neg hb2]
        rw [if_neg (fun h => hb2 (hb2_iff.mpr h))] at hf
        rw [← checkChainAux_false_p3z0 fuel ls' c k 0 ds]
        exact hf

theorem step_Inv_ModeE_ge2_p5 (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 (.p5 :: ls') k c ds)) :
    Inv (.ModeE_ge2 ls' (k + 3) (c + 2) ds) := by
  have hc := hinv.1
  have hch := hinv.2
  dsimp only [invCore] at hc
  rw [bool_if_false_eq_true] at hc
  rcases hc with ⟨h_guards, hc⟩
  simp only [Bool.or_eq_false_iff, not_bool_eq_false] at h_guards
  rcases h_guards with ⟨⟨hgd, hds2⟩, hds1⟩
  have hne2 : ds ≠ [2] :=
    ds_ne_two_of_checkDs2_ModeE_ge2 hds2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
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
    have h_not_b1 : ¬(ds = [] ∧ k + 3 = 1 ∧ c + 2 = 1 ∧ isP3zP5 ls' = true ∧
      headP3zVal ls' ≥ 3) := by omega
    have h_not_b2 : ¬(ds = [] ∧ ((k + 3 = 1 ∧ c + 2 = 1 ∧ z0 ls' = 1) ∨ (k + 3 = 3 ∧ c + 2 = 2 ∧
      z0 ls' = 0)) ∧
        isP3zP5 (dropZ0 ls') = true ∧ headP3zVal (dropZ0 ls') ≥ 18 ∧ z0 (p5Suf ls') ≥ 38) := by
          omega
    refine ⟨?_, ?_⟩
    · dsimp only [invCore]
      have h_g : (!GoodDs ds || !checkDs2 (.ModeE_ge2 ls' (k + 3) (c + 2) ds) ||
          !checkDs1Phi1 (.ModeE_ge2 ls' (k + 3) (c + 2) ds)) = false := by
        simp [hgd, hds2', hds1']
      rw [bool_if_false_eq_self h_g, if_neg hk3_odd, not_bool_if_false_eq_true hvp5]
      rw [not_decide_if_false_eq_true (by omega)]
      rw [if_neg h_not_b1, if_neg h_not_b2]
      have h20 : decide (c + 2 + z0 ls' ≥ 20 ∧ k + 3 + 2 * z0 ls' ≥ 15) = true :=
        decide_eq_true (by omega)
      have h8 : decide (c + 2 + z0 ls' ≥ 8 ∧ k + 3 + 2 * z0 ls' ≥ 15) = true :=
        decide_eq_true (by omega)
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
    have h_not_b1 : ¬(ds = [] ∧ k = 1 ∧ c = 1 ∧ isP3zP5 (.p5 :: ls') = true ∧
      headP3zVal (.p5 :: ls') ≥ 3) := by
      simp [isP3zP5]
    have h_not_b2 : ¬(ds = [] ∧ ((k = 1 ∧ c = 1 ∧ z0 (.p5 :: ls') = 1) ∨ (k = 3 ∧ c = 2 ∧
      z0 (.p5 :: ls') = 0)) ∧
        isP3zP5 (dropZ0 (.p5 :: ls')) = true ∧ headP3zVal (dropZ0 (.p5 :: ls')) ≥ 18 ∧
          z0 (p5Suf (.p5 :: ls')) ≥ 38) := by
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
      · simp only [h1, not_true_eq_false, ↓reduceIte]
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
            GoodPhiW (c + 2 + epW ls') ds (isHeadP3z1 ls' && decide (k + 3 = 0 ∧ c + 2 = 0 ∧
              ds = []))
        else
          decide (c + 2 = 0 ∧ ds = [] ∧
            k + 3 = 2) || (decide (c + 2 ≥ 1) && GoodPhiW (c + 2 - 1) ds false)) = true := by
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
        simp only [Nat.add_zero, Nat.mul_zero, Bool.not_true, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte] at hf2
        rw [hodd_t, hdec_m, hmd0, hp5_t] at hf2
        simp only [Bool.and_true, ↓reduceIte, Bool.not_false, Bool.not_true,
          Bool.false_eq_true] at hf2
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
      simp only [Nat.add_zero, Nat.mul_zero, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte] at hf
      exact hf

theorem step_Inv_ModeE_ge2_p3z_ge2 (m2 : Nat) (ls' : List LTok) (k c : Nat) (ds : List Nat)
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
      · simp only [h1, not_true_eq_false, ↓reduceIte] at hds1 ⊢
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
      have hstart_0 : (isHeadP3z1 (.p3z (m2 + 2) :: ls') && decide (k = 0 ∧ c = 0 ∧
        ds = [])) = false := rfl
      rw [if_pos h_np5_0, hstart_0] at hok_phi
      have hpref_m2 := prefSumW_p3z_m2_bound m2 ls' k c hk_le.1 hk_le.2
      have hepw_ge1 : epW (.p3z k :: .p3z m2 :: ls') ≥ 1 := by
        rw [epW_p3z_even_cons k (.p3z m2 :: ls') hk rfl]; omega
      have hok_all : (if (!isHeadP5 (.p3z m2 :: ls')) = true then
          decide (k + prefSumW (.p3z m2 :: ls') ≤ 2 * c + 4) &&
            ((decide (ds = [] ∧ c + epW (.p3z m2 :: ls') = 1) && MustDrain (.p3z m2 :: ls') &&
              decide (c + ep (.p3z m2 :: ls') = 1 ∧
                k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 = 2) &&
              hasP5 (.p3z m2 :: ls') && decide (preP5Val (.p3z m2 :: ls') ≥ 16 ∧
                z0 (p5Suf (.p3z m2 :: ls')) ≥ 38)) ||
              GoodPhiW (c + epW (.p3z m2 :: ls')) ds false) &&
            (!decide (c = 0) || decide (epW (.p3z k :: .p3z m2 :: ls') ≥ 1))
        else if c = 0 then decide (ds = [] ∧ (k = 0 ∨ k ≥ 22 ∧ z0 (p5Suf (.p3z m2 :: ls')) ≥ 38))
        else GoodPhiW (c - 1) ds false) = true := by
        rw [if_pos h_np5_1, decide_eq_true hpref_m2, decide_eq_true hepw_ge1, Bool.or_true,
          Bool.and_true, Bool.true_and]
        rw [hepw_eq, hmd_eq, hep_eq, hepsum_eq] at hok_phi
        have h_xi_eq : k + (epSum (.p3z m2 :: ls') + 2) + 2 * ep (.p3z m2 :: ls') =
            k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 := by omega
        rw [h_xi_eq] at hok_phi
        dsimp [hasP5, p5Suf] at hok_phi ⊢
        by_cases hmd : MustDrain (.p3z m2 :: ls') = true
        · have hpre :=
          preP5Val_p3z_add2_of_not_headP5 m2 ls' (not_isHeadP5_of_MustDrain_p3z m2 ls' hmd)
          rw [hpre] at hok_phi
          exact hok_phi
        · have hmd_f : MustDrain (.p3z m2 :: ls') = false := Bool.eq_false_iff.mpr hmd
          rw [hmd_f] at hok_phi ⊢
          simpa using hok_phi
      rw [not_bool_if_false_eq_true hok_all]
      have hmd_bound' : (MustDrain (.p3z m2 :: ls') && decide (2 * c + 2 < k +
        epSum (.p3z m2 :: ls'))) = false := by
        rw [hmd_eq, hepsum_eq] at hmd_bound
        rw [show decide (2 * c + 2 < k + epSum (.p3z m2 :: ls')) =
          decide (2 * c + 4 < k + (epSum (.p3z m2 :: ls') + 2)) from decide_eq_of_iff (by omega)]
        exact hmd_bound
      rw [bool_if_false_eq_self hmd_bound']
      have hrst_0 : (decide (k = 0 ∧ c = 0 ∧
        ds = []) && isHeadP3z1 (.p3z (m2 + 2) :: ls')) = false := by
        rw [show isHeadP3z1 (.p3z (m2 + 2) :: ls') = false from rfl, Bool.and_false]
      rw [hodd_eq, hepsum_eq] at hodd_branch
      have hd_odd : decide (2 * c + 2 ≥ k + epSum (.p3z m2 :: ls')) =
          decide (2 * c + 4 ≥ k + (epSum (.p3z m2 :: ls') + 2)) := decide_eq_of_iff (by omega)
      rw [hd_odd]
      by_cases h_cond : (hasOdd (.p3z m2 :: ls') && decide (2 * c + 4 ≥
        k + (epSum (.p3z m2 :: ls') + 2))) = true
      · rw [if_pos h_cond, hrst_0, if_neg Bool.false_ne_true] at hodd_branch
        rw [if_pos h_cond]
        rw [hep_eq, hmd_eq] at hodd_branch
        have h_xi_eq : k + (epSum (.p3z m2 :: ls') + 2) + 2 * ep (.p3z m2 :: ls') =
            k + epSum (.p3z m2 :: ls') + 2 * ep (.p3z m2 :: ls') + 2 := by omega
        rw [h_xi_eq] at hodd_branch
        dsimp [hasP5, p5Suf] at hodd_branch ⊢
        by_cases hmd : MustDrain (.p3z m2 :: ls') = true
        · have hpre :=
          preP5Val_p3z_add2_of_not_headP5 m2 ls' (not_isHeadP5_of_MustDrain_p3z m2 ls' hmd)
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
        rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega),
          not_bool_if_false_eq_true heven_nls]
        have hm2_pos : ∃ m2', m2 = m2' + 1 := ⟨m2 - 1, by omega⟩
        obtain ⟨m2', rfl⟩ := hm2_pos
        dsimp [isP3zGe1P5, MustDrain]
      · intro fuel
        have hf := hch fuel
        dsimp only [invChain] at hf ⊢
        have hb1_t : ([] : List Nat) = [] ∧ (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧
            isP3zP5 (.p3z (m2 + 2) :: .p5 :: suf) = true ∧
              headP3zVal (.p3z (m2 + 2) :: .p5 :: suf) ≥ 3 :=
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
          rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega),
            not_bool_if_false_eq_true heven_nls]
          have hok_c1 : (if 2 ≥ 1 then
              if (!decide (3 = 1 ∧ 2 = 1 ∧ ([] : List Nat) = [])) = true then
                (decide (([] : List Nat) = [] ∧ 2 = 2 ∧ 3 = 3) && MustDrain nls &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val nls ≥ 16 ∧
                    z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (2 - 1) [] false
              else isP3zGe1P5 (.p3z m2 :: .p5 :: suf)
            else true) = true := by
            have h16_38 : decide (m2 ≥ 16 ∧ z0 suf ≥ 38) = true := decide_eq_true ⟨by omega, hz38⟩
            dsimp [nls, MustDrain, hasP5, preP5Val, p5Suf]
            simp [h16_38]
          rw [not_bool_if_false_eq_true hok_c1]
          have h16_38' : decide (([] : List Nat) = [] ∧ 2 - 1 = 1 ∧ 3 = 3 ∧ m2 ≥ 16 ∧
            z0 suf ≥ 38) = true :=
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
          · simp only [h1, not_true_eq_false, ↓reduceIte]; rw [if_neg hk,
            decide_eq_false (by omega)]; rfl
          · simp [h1]
        refine ⟨?_, ?_⟩
        · dsimp only [invCore]
          have h_g : (!GoodDs ds || !checkDs2 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) k c ds) ||
              !checkDs1Phi1 (.ModeB_ge3 (.p3z m2 :: .p5 :: suf) k c ds)) = false := by
            simp [hgd, hds2', hds1']
          rw [bool_if_false_eq_self h_g, if_neg hk, if_neg (by omega),
            not_bool_if_false_eq_true heven_nls]
          have hrst_f : decide (k = 1 ∧ c = 1 ∧ ds = []) = false := decide_eq_false (by omega)
          have hok_c1 : (if c ≥ 1 then
              if (!decide (k = 1 ∧ c = 1 ∧ ds = [])) = true then
                (decide (ds = [] ∧ c = 2 ∧ k = 3) && MustDrain nls &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val nls ≥ 16 ∧
                    z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (c - 1) ds false
              else isP3zGe1P5 (.p3z m2 :: .p5 :: suf)
            else true) = true := by
            rw [if_pos (by omega), hrst_f, if_pos (by decide), hphiw_f, Bool.or_true]
          rw [not_bool_if_false_eq_true hok_c1]
          rw [hmd_nls, h_gt_f, Bool.and_false, if_neg Bool.false_ne_true, if_pos hck.2, hrst_f,
            if_neg Bool.false_ne_true]
          rw [hgp, Bool.true_and]
          have h_ds1_ok : ((!decide (ds = [1] ∧ c - 1 ≥ 24)) || decide (k ≥ 37)) = true := by
            by_cases h1 : ds = [1]
            · simp [h1] at hc_1; simp [hc_1]
            · simp [h1]
          have h_ds0_ok : ((!decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧
            ((!hasP5 (.p3z m2 :: .p5 :: suf)) = true ∨ true = true))) ||
              decide (k ≥ 17)) = true := by
            by_cases h0 : (ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8
            · have hc9 : ((ds = [] ∨ ds = [0]) ∧
              c ≥ 9) ∨ isOddDrainDs ds = true := Or.inl ⟨h0.1, by omega⟩
              rw [decide_eq_true hc9] at hc_9
              simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc_9
              simp [hc_9]
            · have h_f : decide ((ds = [] ∨ ds = [0]) ∧ c - 1 ≥ 8 ∧
              ((!hasP5 (.p3z m2 :: .p5 :: suf)) = true ∨ true = true)) = false :=
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
            rw [if_neg hk, if_neg (show ¬(k = 1 ∧ c = 1 ∧
              ds = []) by omega), if_neg (show c ≠ 0 by omega)]
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
            simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero,
              Nat.zero_add, Nat.mul_zero]
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

theorem isOddDrainDs_cons_imp {d : Nat} {ds : List Nat} (h : isOddDrainDs (d :: ds) = true) :
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

theorem GoodPhiW_push_ge8 (phiW c : Nat) (ds : List Nat) (hc : c ≥ 7) (h15 : phiW ≥ 15)
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

theorem GoodPhiW_c_pos {c : Nat} {ds : List Nat} (hne2 : ds ≠ [2]) (h : GoodPhiW c ds false =
  true) :
    c ≥ 1 := by
  by_contra hc0
  have rfl_c : c = 0 := by omega
  subst rfl_c
  dsimp [GoodPhiW] at h
  rw [if_neg hne2] at h
  split_ifs at h
  cases h

theorem GoodPhiW_nil_ge6 {c : Nat} (h : GoodPhiW c [] false = true) : c ≥ 6 := by
  dsimp [GoodPhiW] at h
  exact of_decide_eq_true h

theorem ValidAfterOdd_cases {ls' : List LTok} (h : ValidAfterOdd ls' = true) :
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

theorem epSum_p3z_p5_ge14 {m2 : Nat} {suf : List LTok} (hm : m2 ≥ 14) :
    epSum (.p3z m2 :: .p5 :: suf) ≥ 14 := by
  dsimp [epSum]; split_ifs <;> omega

theorem step_Inv_ModeE_ge2_p3z1_odd (ls' : List LTok) (k c : Nat) (ds : List Nat)
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
  have hb1' : ¬((c + 1) :: ds = [] ∧ 1 = 1 ∧ k + 4 = 1 ∧ isP3zP5 suf = true ∧ headP3zVal suf ≥ 3) :=
    by
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
    have h20 : decide (k + 4 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
      decide_eq_true (by omega)
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

theorem step_Inv_ModeE_ge2_p3z1_reset (ls' : List LTok)
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
          have h20 : decide (2 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
            decide_eq_true (by omega)
          have h8 : decide (2 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
            decide_eq_true (by omega)
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
              (decide ([1] = [] ∧
                2 + epW (.p3z m2 :: .p5 :: suf) = 1) && MustDrain (.p3z m2 :: .p5 :: suf) &&
                decide (2 + ep (.p3z m2 :: .p5 :: suf) = 1 ∧
                  0 + epSum (.p3z m2 :: .p5 :: suf) + 2 * ep (.p3z m2 :: .p5 :: suf) = 2) &&
                hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val (.p3z m2 :: .p5 :: suf) ≥ 16 ∧
                  z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                GoodPhiW (2 +
                  epW (.p3z m2 :: .p5 :: suf)) [1] (isHeadP3z1 (.p3z m2 :: .p5 :: suf) && decide (0
                  = 0 ∧ 2 = 0 ∧ [1] = []))
            else
              decide (2 = 0 ∧ [1] = [] ∧
                0 = 2) || (decide (2 ≥ 1) && GoodPhiW (2 - 1) [1] false)) = true := by
            dsimp [isHeadP5]; rw [hepw0]; simp [GoodPhiW]
          rw [not_bool_if_false_eq_true hok_phi']
          rw [hmd0, Bool.false_and, if_neg Bool.false_ne_true]
          have hrst_f : (decide (0 = 0 ∧ 2 = 0 ∧
            [1] = []) && isHeadP3z1 (.p3z m2 :: .p5 :: suf)) = false := rfl
          rw [hrst_f]
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
          by_cases h_cond : (hasOdd (.p3z m2 :: .p5 :: suf) && decide (2 * 2 + 4 ≥
            0 + epSum (.p3z m2 :: .p5 :: suf))) = true
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

theorem step_Inv_ModeE_ge2_p3z1_even_nonreset (ls' : List LTok) (k c : Nat) (ds : List Nat)
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
  have h_odd_t : (hasOdd (.p3z 1 :: ls') && decide (2 * c + 4 ≥ k + epSum (.p3z 1 :: ls'))) =
    true := by
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
      have h_t : (ds = [] ∨ ds = [0]) ∧ c ≥ 8 ∧
        ((!hasP5 [.p3z 1]) = true ∨ MustDrain [.p3z 1] = true) :=
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
            GoodPhiW (k + 2 + epW []) ((c + 1) :: ds) (isHeadP3z1 [] && decide (0 = 0 ∧ k + 2 = 0 ∧
              (c + 1) :: ds = []))
        else
          decide (k + 2 = 0 ∧ (c + 1) :: ds = [] ∧
            0 = 2) || (decide (k + 2 ≥ 1) && GoodPhiW (k + 1) ((c + 1) :: ds) false)) = true := by
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
      simp only [Bool.and_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.add_zero,
        Nat.mul_zero] at hf
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
    have hb1' : ¬((c + 1) :: ds = [] ∧ 1 = 1 ∧ k + 4 = 1 ∧ isP3zP5 suf = true ∧
      headP3zVal suf ≥ 3) := by
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
      have h20 : decide (k + 4 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
        decide_eq_true (by omega)
      have h8 : decide (k + 4 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
        decide_eq_true (by omega)
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
          ((!hasP5 (.p3z 1 :: .p3z m :: .p5 :: suf)) = true ∨
            MustDrain (.p3z 1 :: .p3z m :: .p5 :: suf) = true) :=
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
        have h_g : (!GoodDs ((c + 1) :: ds) || !checkDs2 (.ModeE_ge2 (.p5 :: suf) 0 (k + 3) ((c +
          1) :: ds)) ||
            !checkDs1Phi1 (.ModeE_ge2 (.p5 :: suf) 0 (k + 3) ((c + 1) :: ds))) = false := by
          simp [hgd', hds2', hds1']
        rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven_p5]
        dsimp [prefSumW]
        have hok_phi' : (if (!isHeadP5 (.p5 :: suf)) = true then
            (decide ((c + 1) :: ds = [] ∧
              k + 2 + 1 + epW (.p5 :: suf) = 1) && MustDrain (.p5 :: suf) &&
              decide (k + 2 + 1 + ep (.p5 :: suf) = 1 ∧
                0 + epSum (.p5 :: suf) + 2 * ep (.p5 :: suf) = 2) &&
              hasP5 (.p5 :: suf) && decide (preP5Val (.p5 :: suf) ≥ 16 ∧
                z0 (p5Suf (.p5 :: suf)) ≥ 38)) ||
              GoodPhiW (k + 2 + 1 + epW (.p5 :: suf)) ((c +
                1) :: ds) (isHeadP3z1 (.p5 :: suf) && decide (0 = 0 ∧ k + 2 + 1 = 0 ∧
                (c + 1) :: ds = []))
          else
            decide (k + 2 + 1 = 0 ∧ (c + 1) :: ds = [] ∧
              0 = 2) || (decide (k + 2 + 1 ≥ 1) && GoodPhiW (k + 2) ((c + 1) :: ds) false)) =
              true := by
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
        have hb1' : ¬((k + 3) :: (c + 1) :: ds = [] ∧ 1 = 1 ∧ 2 = 1 ∧ isP3zP5 suf = true ∧
          headP3zVal suf ≥ 3) := by
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
          have h20 : decide (2 + z0 suf ≥ 20 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
            decide_eq_true (by omega)
          have h8 : decide (2 + z0 suf ≥ 8 ∧ 1 + 2 * z0 suf ≥ 15) = true :=
            decide_eq_true (by omega)
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
          have hds2' : checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) =
            true := by
            dsimp [checkDs2]; rw [if_pos hne2']
          have hds1' : checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) =
            true := by
            dsimp [checkDs1Phi1]; rw [if_pos hne1']
          refine ⟨?_, ?_⟩
          · dsimp only [invCore]
            have h_g : (!GoodDs ((c + 1) :: ds) ||
                !checkDs2 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) ||
                !checkDs1Phi1 (.ModeE_ge2 (.p3z m2 :: .p5 :: suf) 0 (k + 2) ((c + 1) :: ds))) =
                  false := by
              simp [hgd', hds2', hds1']
            rw [bool_if_false_eq_self h_g, if_pos rfl, not_bool_if_false_eq_true heven_m2]
            rw [hpref0, not_decide_if_false_eq_true (by omega)]
            have hok_phi' : (if (!isHeadP5 (.p3z m2 :: .p5 :: suf)) = true then
                (decide ((c + 1) :: ds = [] ∧
                  k + 2 + epW (.p3z m2 :: .p5 :: suf) = 1) && MustDrain (.p3z m2 :: .p5 :: suf) &&
                  decide (k + 2 + ep (.p3z m2 :: .p5 :: suf) = 1 ∧
                    0 + epSum (.p3z m2 :: .p5 :: suf) + 2 * ep (.p3z m2 :: .p5 :: suf) = 2) &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val (.p3z m2 :: .p5 :: suf) ≥ 16 ∧
                    z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (k + 2 + epW (.p3z m2 :: .p5 :: suf)) ((c + 1) :: ds)
                    (isHeadP3z1 (.p3z m2 :: .p5 :: suf) && decide (0 = 0 ∧ k + 2 = 0 ∧
                      (c + 1) :: ds = []))
              else
                decide (k + 2 = 0 ∧ (c + 1) :: ds = [] ∧
                  0 = 2) || (decide (k + 2 ≥ 1) && GoodPhiW (k + 2 - 1) ((c + 1) :: ds) false)) =
                  true := by
              dsimp [isHeadP5]; rw [hepw0_m2, Nat.add_zero, GoodPhiW_mono _ _ _ hphiw',
                Bool.or_true]
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd0_m2, Bool.false_and, if_neg Bool.false_ne_true]
            have hrst_f' : (decide (0 = 0 ∧ k + 2 = 0 ∧
              (c + 1) :: ds = []) && isHeadP3z1 (.p3z m2 :: .p5 :: suf)) = false := by
              rw [decide_eq_false (by omega), Bool.false_and]
            rw [hrst_f']
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            by_cases h_cond : (hasOdd (.p3z m2 :: .p5 :: suf) && decide (2 * (k + 2) + 4 ≥
              0 + epSum (.p3z m2 :: .p5 :: suf))) = true
            · rw [if_pos h_cond]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cond
              have hm2_odd : m2 % 2 = 1 := by
                by_contra hm2_ev
                have : hasOdd (.p3z m2 :: .p5 :: suf) = false := by
                  dsimp [hasOdd]; rw [if_neg hm2_ev]
                rw [this] at h_cond; cases h_cond.1
              have hep0_m2 : ep (.p3z m2 :: .p5 :: suf) = 0 := by dsimp [ep]; rw [if_pos hm2_odd]
              have hepsum_m2 : epSum (.p3z m2 :: .p5 :: suf) = m2 - 1 := by
                dsimp [epSum]; rw [if_pos hm2_odd]
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
              have hf_ds1 : decide ((c + 1) :: ds = [1] ∧
                k + 2 + ep (.p3z m2 :: .p5 :: suf) ≥ 24) = false :=
                decide_eq_false (fun ⟨h, _⟩ => hne1' h)
              have hf_ds0 : decide (((c + 1) :: ds = [] ∨ (c + 1) :: ds = [0]) ∧
                k + 2 + ep (.p3z m2 :: .p5 :: suf) ≥ 8 ∧
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
            have hrst_ch' : ¬(0 = 0 ∧ k + 2 = 0 ∧ (c + 1) :: ds = [] ∧
              isHeadP3z1 (.p3z m2 :: .p5 :: suf) = true) := by
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
                have hodd_m2 : hasOdd (.p3z m2 :: .p5 :: suf) = false := by
                  dsimp [hasOdd]; rw [if_neg hm2_ev]
                have hp5_m2 : hasP5 (.p3z m2 :: .p5 :: suf) = true := rfl
                have hip5_m2 : isHeadP5 (.p3z m2 :: .p5 :: suf) = false := rfl
                have hepsum_m2 : epSum (.p3z m2 :: .p5 :: suf) = m2 := by
                  dsimp [epSum]; rw [if_neg hm2_ev]
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
                  have hodd_m2 : hasOdd (.p3z m2 :: .p5 :: suf) = true := by
                    dsimp [hasOdd]; rw [if_pos hm2_odd]
                  have hp5_m2 : hasP5 (.p3z m2 :: .p5 :: suf) = true := rfl
                  have hepsum_m2 : epSum (.p3z m2 :: .p5 :: suf) = m2 - 1 := by
                    dsimp [epSum]; rw [if_pos hm2_odd]
                  have hep_m2 : ep (.p3z m2 :: .p5 :: suf) = 0 := by dsimp [ep]; rw [if_pos hm2_odd]
                  have hsuf_m2 : p5Suf (.p3z m2 :: .p5 :: suf) = suf := rfl
                  have hdec_m2 : decide (2 * (k + 2) + 4 ≥ 0 + (m2 - 1)) = true :=
                    decide_eq_true (by omega)
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
              decide_eq_true hz38, decide_eq_true (show 0 + epSum (.p3z m2 :: .p5 :: suf) ≥
                2 * 4 + 6 by omega)]
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
                (decide ([2] = [] ∧
                  4 + epW (.p3z m2 :: .p5 :: suf) = 1) && MustDrain (.p3z m2 :: .p5 :: suf) &&
                  decide (4 + ep (.p3z m2 :: .p5 :: suf) = 1 ∧
                    0 + epSum (.p3z m2 :: .p5 :: suf) + 2 * ep (.p3z m2 :: .p5 :: suf) = 2) &&
                  hasP5 (.p3z m2 :: .p5 :: suf) && decide (preP5Val (.p3z m2 :: .p5 :: suf) ≥ 16 ∧
                    z0 (p5Suf (.p3z m2 :: .p5 :: suf)) ≥ 38)) ||
                  GoodPhiW (4 + epW (.p3z m2 :: .p5 :: suf)) [2]
                    (isHeadP3z1 (.p3z m2 :: .p5 :: suf) && decide (0 = 0 ∧ 4 = 0 ∧ [2] = []))
              else
                decide (4 = 0 ∧ [2] = [] ∧
                  0 = 2) || (decide (4 ≥ 1) && GoodPhiW (4 - 1) [2] false)) = true := by
              dsimp [isHeadP5]; rw [hepw0_m2]; simp [GoodPhiW]
            rw [not_bool_if_false_eq_true hok_phi']
            rw [hmd0_m2, Bool.false_and, if_neg Bool.false_ne_true]
            have hrst_f' : (decide (0 = 0 ∧ 4 = 0 ∧
              [2] = []) && isHeadP3z1 (.p3z m2 :: .p5 :: suf)) = false := rfl
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

theorem step_Inv_ModeE_ge2_p3z1 (ls' : List LTok) (k c : Nat) (ds : List Nat)
    (hinv : Inv (.ModeE_ge2 (.p3z 1 :: ls') k c ds)) :
    Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)) := by
  by_cases hk : k % 2 = 0
  · by_cases hrst : k = 0 ∧ c = 0 ∧ ds = []
    · rcases hrst with ⟨rfl, rfl, rfl⟩
      exact step_Inv_ModeE_ge2_p3z1_reset ls' hinv
    · exact step_Inv_ModeE_ge2_p3z1_even_nonreset ls' k c ds hk hrst hinv
  · exact step_Inv_ModeE_ge2_p3z1_odd ls' k c ds hk hinv

theorem step_Inv_ModeE_ge2 (ls : List LTok) (k c : Nat) (ds : List Nat)
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

theorem step_Inv (s : ModeState) (hinv : Inv s) : Inv (nextState s) := by
  cases s with
  | ModeE_c1 ls k ds => exact step_Inv_ModeE_c1 ls k ds hinv
  | ModeE_ge2 ls k c ds => exact step_Inv_ModeE_ge2 ls k c ds hinv
  | ModeB_ge3 ls a c ds =>
    cases c with
    | zero => exact step_Inv_ModeB_ge3_c0 ls a ds hinv
    | succ c' => exact step_Inv_ModeB_ge3_cpos ls a c' ds hinv
  | ModeB_b2 ls m ds => exact step_Inv_ModeB_b2 ls m ds hinv
  | ModeB_blank ls a => exact step_Inv_ModeB_blank ls a hinv


theorem nonhalt_of_state_step_inv {Γ Λ S : Type*} [Inhabited Γ] [Inhabited Λ]
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

theorem init_to_s0 : (init []) [target_tm]⊢⁺ toCfg (.ModeB_ge3 [] 1 1 []) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  dsimp only [toCfg, evalL, evalR]
  dsimp [O, ListBlank.append]
  execute60

theorem nonhalt_of_Inv_s0 (h_s0 : Inv (.ModeB_ge3 [] 1 1 [])) :
    IsDoesNotHalt target_tm := by
  exact nonhalt_of_state_step_inv target_tm toCfg Inv nextState (.ModeB_ge3 [] 1 1 [])
    (stepPlus_stepStar init_to_s0) h_s0 step_toCfg step_Inv

end BusyBeaver.SegmentChain
