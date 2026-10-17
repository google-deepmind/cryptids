/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`

## Collatz-like Acceleration Rules
Canonical configurations map out to R1, R2, Q, S4, S6 parametrized by `n`.
-/


@[expose] public section

namespace BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def list_nat_repeat (a : List (Fin 2)) (n : Nat) : List (Fin 2) := a ^ n
@[simp] lemma list_nat_repeat_eq (a : List (Fin 2)) (n : Nat) : list_nat_repeat a n = a ^ n := rfl

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

notation3 c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
notation3 c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
notation3 c₁ " [" M "]⊢* " c₂ => ∃ n, multiStep M c₁ n = some c₂
notation3 c₁ " [" M "]⊢⁺ " c₂ => ∃ n > 0, multiStep M c₁ n = some c₂

notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
notation:67 s:67 " << " a:68 => ListBlank.cons a s
infixr:67 " >> " => ListBlank.cons
notation:67 s:67 " <+ " l:68 => ListBlank.append l s
infixr:67 " +> " => ListBlank.append
notation3 l " {{" q "}}> " r => (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg _ _)
notation3 l " <{{" q "}} " r => (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg _ _)

abbrev target_tm := target
abbrev suspect_153_tm := target

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs)
  ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x ::
  xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

@[simp]
theorem list_pow_add (l : List (Fin 2)) (n m : Nat) : l^(n + m) = l^n ++ l^m := by
  change (List.replicate (n + m) l).flatten = (List.replicate n l).flatten
    ++ (List.replicate m l).flatten
  rw [List.replicate_add, List.flatten_append]

theorem list_pow_add_comm (l : List (Fin 2)) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [← list_pow_add, add_comm, list_pow_add]

lemma listblank_append_append (s : ListBlank (Fin 2)) (l₁ l₂ : List (Fin 2)) :
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

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

lemma pow_succ_append_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

lemma pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

lemma step_multiStep {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

lemma step_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ := ⟨1, step_multiStep tm c₁ c₂ h⟩

lemma step_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, step_multiStep tm c₁ c₂ h⟩

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

lemma stepStar_stepPlus_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_trans' {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (stepPlus_stepStar h₂)

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

lemma step_stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ :=
  stepPlus_stepStar (step_stepStar_stepPlus h₁ h₂)

macro "finish" : tactic =>
  `(tactic| exact ⟨0, rfl⟩)
macro "step_plus" : tactic =>
  `(tactic|
    refine step_stepStar_stepPlus
        (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
      simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
        Tape.write, zero_cons_default, default_head, default_tail])
macro "step" : tactic =>
  `(tactic|
    refine step_stepStar_trans
        (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
      simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
        Tape.write, zero_cons_default, default_head, default_tail])
macro "bb_steps" : tactic =>
  `(tactic| step_plus <;> repeat (any_goals (first | finish | step)))


lemma nat_even_or_odd (k : Nat) : (∃ m : Nat, k = 2 * m) ∨ (∃ m : Nat, k = 2 * m + 1) := by
  induction k with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ k ih =>
    rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inr ⟨m, rfl⟩
    · exact Or.inl ⟨m + 1, by omega⟩

lemma ge_4_exists (n : Nat) (h : n ≥ 4) : ∃ a : Nat, n = a + 4 := ⟨n - 4, by omega⟩
lemma ge_7_exists (n : Nat) (h : n ≥ 7) : ∃ a : Nat, n = a + 7 := ⟨n - 7, by omega⟩

lemma zero1_append_default : (([0] : List (Fin 2)) +> default) = default := by
  simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]

lemma zero2_append_default : (([0, 0] : List (Fin 2)) +> default) = default := by
  simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]

abbrev B4 : List (Fin 2) := [1, 1, 1, 0]

/-- Left stack block `[0, 0, 1, 1]` (representing `1100` from left to right on the tape). -/
abbrev U4 : List (Fin 2) := [0, 0, 1, 1]

/-- Right sweep block `[0, 1, 1, 0]`. -/
abbrev V4 : List (Fin 2) := [0, 1, 1, 0]

/-- Canonical 8-bit `D`-drain block `[1, 0, 1, 1, 0, 1, 1, 0]`. -/
abbrev W8 : List (Fin 2) := [1, 0, 1, 1, 0, 1, 1, 0]

/-- Canonical left tape `LA a := default <+ ([0, 0, 1, 1])^a`. -/
def LA (a : Nat) : ListBlank (Fin 2) := default <+ (U4 ^ a)

/-- Right-boundary suffix `R_Q := [1] +> default`. -/
def R_Q : ListBlank (Fin 2) := ([1] : List (Fin 2)) +> default

/-- Right-boundary suffix `R_S6 := [1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1] +> default`. -/
def R_S6 : ListBlank (Fin 2) := ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default

/-- Canonical `State_A` configuration on Holdout #330:
    `State_A a b R_end := LA a {{A}}> ([0, 1, 1, 1, 0] +> (([1, 1, 1, 0])^b +> R_end))`. -/
def State_A (a b : Nat) (R_end : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  LA a {{A}}> (([0, 1, 1, 1, 0] : List (Fin 2)) +> ((([1, 1, 1, 0] : List (Fin 2)) ^ b) +> R_end))

lemma LA_zero : LA 0 = default := rfl

lemma LA_succ (a : Nat) : LA (a + 1) = LA a <+ U4 := by
  unfold LA
  rw [pow_add_append_left default U4 a 1]
  rfl

lemma LA_add (a k : Nat) : LA (a + k) = LA a <+ (U4 ^ k) := by
  unfold LA
  exact pow_add_append_left default U4 a k

-- ============================================================================
-- Section 2: Universal One-Bit & Multi-Bit `LA` Consumption Laws
-- ============================================================================

/-- 8-step trigger from `((l <+ U4) {{A}}> ((1 : Fin 2) >> r))` to `(l {{C}}> ([1, 1, 1, 1,
  0] +> r))`. -/
lemma step_trigger_1_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> ((1 : Fin 2) >> r)) [suspect_153_tm]⊢⁺
    (l {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- 10-step left `{{C}}>` step across one `U4 = [0, 0, 1, 1]` block. -/
lemma step_C_left_U4_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (l {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> (V4 +> r))) := by
  simp only [U4, V4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Inductive left `{{C}}>` sweep across `U4 ^ k` (`10k` steps). -/
lemma shift_C_left_U4_0349 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (U4 ^ k)) {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢*
    (l {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> ((V4 ^ k) +> r))) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_l : (l <+ (U4 ^ (k + 1))) = ((l <+ (U4 ^ k)) <+ U4) := by
      exact pow_add_append_left l U4 k 1
    rw [h_l]
    have h1 := stepPlus_stepStar (step_C_left_U4_0349 (l <+ (U4 ^ k)) r)
    have h2 := ih l (V4 +> r)
    have h_r : (V4 ^ k) +> (V4 +> r) = (V4 ^ (k + 1)) +> r := by
      rw [listblank_append_append, list_pow_append_one]
    rw [h_r] at h2
    exact stepStar_trans h1 h2

/-- 9-step left-boundary bounce from `default {{C}}> ([1, 1, 1, 1,
  0] +> r)` to `default {{A}}> (V4 +> (V4 +> r))`. -/
lemma step_C_bounce_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{C}}> (([1, 1, 1, 1,
      0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((default : ListBlank (Fin 2)) {{A}}> (V4 +> (V4 +> r))) := by
  simp only [V4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- 6-step right `{{A}}>` step across one `V4 = [0, 1, 1, 0]` block. -/
lemma step_A_right_V4_0349 (l r : ListBlank (Fin 2)) :
    (l {{A}}> (V4 +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> r) := by
  simp only [U4, V4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Inductive right `{{A}}>` sweep across `V4 ^ k` (`6k` steps). -/
lemma shift_A_right_V4_0349 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((V4 ^ k) +> r)) [suspect_153_tm]⊢*
    ((l <+ (U4 ^ k)) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [pow_succ_append_right V4 k r]
    have h1 := stepPlus_stepStar (step_A_right_V4_0349 l ((V4 ^ k) +> r))
    have h2 := ih (l <+ U4) r
    have h_l : (l <+ U4) <+ (U4 ^ k) = l <+ (U4 ^ (k + 1)) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [h_l] at h2
    exact stepStar_trans h1 h2

/-- Universal One-Bit Consumption Theorem on Holdout #330 (`16a + 29` micro-steps):
    For all `a : Nat` and `r : ListBlank (Fin 2)`,
    `LA (a + 1) {{A}}> ((1 : Fin 2) >> r) ⊢⁺ LA (a + 2) {{A}}> r`. -/
theorem consume_1_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> ((1 : Fin 2) >> r)) [suspect_153_tm]⊢⁺
    (LA (a + 2) {{A}}> r) := by
  rw [LA_succ a]
  have h1 := step_trigger_1_0349 (LA a) r
  have h2 := shift_C_left_U4_0349 a default r
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 := step_C_bounce_0349 ((V4 ^ a) +> r)
  have h4 := step_A_right_V4_0349 default (V4 +> ((V4 ^ a) +> r))
  have h5 := step_A_right_V4_0349 (LA 1) ((V4 ^ a) +> r)
  have h13 := stepPlus_trans' h12 h3
  have h14 := stepPlus_trans' h13 h4
  have h_l1 : (default <+ U4) = LA 1 := rfl
  rw [h_l1] at h14
  have h15 := stepPlus_trans' h14 h5
  have h_l2 : (LA 1 <+ U4) = LA 2 := rfl
  rw [h_l2] at h15
  have h6 := shift_A_right_V4_0349 a (LA 2) r
  have h16 := stepPlus_stepStar_stepPlus h15 h6
  have h_la : (LA 2 <+ (U4 ^ a)) = LA (a + 2) := by
    rw [← LA_add 2 a, Nat.add_comm 2 a]
  rw [h_la] at h16
  exact h16

/-- Two-bit consumption on `LA (a + 1)`:
    `LA (a + 1) {{A}}> ([1, 1] +> r) ⊢⁺ LA (a + 3) {{A}}> r`. -/
lemma consume_2_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 3) {{A}}> r) := by
  have h1 := consume_1_LA_0349 a ((1 : Fin 2) >> r)
  have h2 := consume_1_LA_0349 (a + 1) r
  exact stepPlus_trans' h1 h2

/-- Three-bit consumption on `LA (a + 1)` (`48a + 135` micro-steps):
    `LA (a + 1) {{A}}> ([1, 1, 1] +> r) ⊢⁺ LA (a + 4) {{A}}> r`. -/
lemma consume_3_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1, 1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> r) := by
  have h1 := consume_2_LA_0349 a ((1 : Fin 2) >> r)
  have h2 := consume_1_LA_0349 (a + 2) r
  exact stepPlus_trans' h1 h2

-- ============================================================================
-- Section 3: Local In-Place Rewrites & Combined `LA` Block Consumers
-- ============================================================================

/-- 10-step local rewrite `((l <+ U4) {{A}}> ([0, 1, 0, 1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1,
  0] +> r))`. -/
lemma rewrite_10_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Combined `[0, 1, 0, 1]` consumer: `LA (a + 1) {{A}}> ([0, 1, 0,
  1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0] +> r)`. -/
lemma consume_0101_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_10_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0] : List (Fin 2)) +> r)
  exact stepPlus_trans' h1 h2

/-- 12-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1,
  0] +> r))`. -/
lemma rewrite_12_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Combined `[0, 0, 1, 1]` consumer: `LA (a + 1) {{A}}> ([0, 0, 1,
  1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0] +> r)`. -/
lemma consume_0011_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_12_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0] : List (Fin 2)) +> r)
  exact stepPlus_trans' h1 h2

/-- 28-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 0, 1, 1, 0,
  1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1, 0, 0, 1, 1, 0] +> r))`. -/
lemma rewrite_28_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Combined `[0, 0, 1, 0, 1, 1, 0, 1]` consumer:
    `LA (a + 1) {{A}}> ([0, 0, 1, 0, 1, 1, 0, 1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0, 0, 1, 1,
      0] +> r)`. -/
lemma consume_00101101_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_28_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0, 0, 1, 1, 0] : List (Fin 2)) +> r)
  exact stepPlus_trans' h1 h2

/-- 22-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 0, 1, 0,
  1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1, 0, 1, 1, 0] +> r))`. -/
lemma rewrite_22_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Combined `[0, 0, 1, 0, 1, 0, 1]` consumer:
    `LA (a + 1) {{A}}> ([0, 0, 1, 0, 1, 0, 1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0, 1, 1, 0] +> r)`. -/
lemma consume_0010101_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_22_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0, 1, 1, 0] : List (Fin 2)) +> r)
  exact stepPlus_trans' h1 h2

/-- 92-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 0, 1, 1, 1, 0,
  1] +> r)) ⊢⁺ (l {{A}}> ([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] +> r))`. -/
lemma rewrite_92_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

-- ============================================================================
-- Section 4: Universal Halting Suffix Theorem (`halt_LA_S6_0349`) & `S6(2)`
-- ============================================================================

/-- 4-step prefix step to halting configuration `E(1)` (`1LF---`):
    `l {{A}}> ([0, 0, 0, 0, 1] +> r) ⊢⁺ ((l <+ [1, 1, 1, 1]) {{E}}> ((1 : Fin 2) >> r))`. -/
lemma step_halt_00001_0349 (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([0, 0, 0, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ [1, 1, 1, 1]) {{E}}> ((1 : Fin 2) >> r)) := by
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

-- ============================================================================
-- Section 5: Universal `D`-Drain Parity-Absorption Laws (`drain_LA_odd/even`)
-- ============================================================================

/-- 48-step entry from `(l <+ U4) {{A}}> ([0, 1, 1, 1, 0, 1, 1, 1, 0] +> r)` to
    `l {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] +> ([1, 0] +> r))`. -/
lemma step_drain_entry_48_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (([1,
      0] : List (Fin 2)) +> r))) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- 98-step `D`-drain step across two `U4` blocks (`U4 ^ 2 = [0, 0, 1, 1, 0, 0, 1, 1]`):
    `(((l <+ U4) <+ U4) {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] +> r)) ⊢⁺ (l {{D}}> ([1, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 1] +> (W8 +> r)))`. -/
lemma step_drain_2U4_98_0349 (l r : ListBlank (Fin 2)) :
    (((l <+ U4) <+ U4) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (W8 +> r))) := by
  simp only [U4, W8, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- Inductive `D`-drain across `2 * m` blocks of `U4` (`98m` micro-steps). -/
lemma shift_drain_2m_0349 (m : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (U4 ^ (2 * m))) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢*
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> ((W8 ^ m) +> r))) := by
  induction m generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have h_l : (l <+ (U4 ^ (2 * (m + 1)))) = (((l <+ (U4 ^ (2 * m))) <+ U4) <+ U4) := by
      have h_eq : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h_eq, pow_add_append_left l U4 (2 * m + 1) 1, pow_add_append_left l U4 (2 * m) 1]
      rfl
    rw [h_l]
    have h1 := stepPlus_stepStar (step_drain_2U4_98_0349 (l <+ (U4 ^ (2 * m))) r)
    have h2 := ih l (W8 +> r)
    have h_r : (W8 ^ m) +> (W8 +> r) = (W8 ^ (m + 1)) +> r := by
      rw [listblank_append_append, list_pow_append_one]
    rw [h_r] at h2
    exact stepStar_trans h1 h2

/-- 66-step odd left-boundary turnaround from `default {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
  1] +> r)`. -/
lemma step_drain_odd_end_66_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((default : ListBlank (Fin 2)) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0] : List (Fin 2)) +> r)) := by
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

/-- 70-step even left-boundary turnaround from `(default <+ U4) {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0,
  1, 0, 1] +> r)`. -/
lemma step_drain_even_end_70_0349 (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ U4) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((default : ListBlank (Fin 2)) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma consume_1_LA_zero_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{A}}> ((1 : Fin 2) >> r)) [suspect_153_tm]⊢⁺
    (LA 1 {{A}}> r) := by
  simp only [LA, U4, HPow.hPow, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  bb_steps

/-- 269-step universal post-drain prefix transition to `LA 7 {{A}}> r`. -/
lemma step_drain_prefix_269_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0] : List (Fin 2)) +> r))
    [suspect_153_tm]⊢⁺ (LA 7 {{A}}> r) := by
  have h1 := consume_1_LA_zero_0349 (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_2_LA_0349 0 (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h3 := step_A_right_V4_0349 (LA 3) (([1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  rw [← LA_succ 3] at h3
  have h4 := consume_2_LA_0349 3 (([0, 1, 1, 0] : List (Fin 2)) +> r)
  have h5 := step_A_right_V4_0349 (LA 6) r
  rw [← LA_succ 6] at h5
  exact stepPlus_trans' (stepPlus_trans' (stepPlus_trans' (stepPlus_trans' h1 h2) h3) h4) h5

/-- Universal Odd `D`-Drain + Prefix Law (`98m + 383` micro-steps):
    For all `m : Nat` and `r : ListBlank (Fin 2)`,
    `LA (2 * m + 1) {{A}}> ([0, 1, 1, 1, 0, 1, 1, 1, 0] +> r) ⊢⁺ LA 7 {{A}}> ((W8 ^ m) +> ([1,
      0] +> r))`. -/
theorem drain_LA_odd_to_LA7_0349 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m + 1) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))) := by
  rw [LA_succ (2 * m)]
  have h1 := step_drain_entry_48_0349 (LA (2 * m)) r
  have h2 := shift_drain_2m_0349 m default (([1, 0] : List (Fin 2)) +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 := step_drain_odd_end_66_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  exact stepPlus_trans' (stepPlus_trans' h12 h3) h4

/-- Universal Even `D`-Drain + Prefix Law (`98m + 387` micro-steps, exact +4 step parity offset):
    For all `m : Nat` and `r : ListBlank (Fin 2)`,
    `LA (2 * m + 2) {{A}}> ([0, 1, 1, 1, 0, 1, 1, 1, 0] +> r) ⊢⁺ LA 7 {{A}}> ((W8 ^ m) +> ([1,
      0] +> r))`. -/
theorem drain_LA_even_to_LA7_0349 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m + 2) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))) := by
  have h_la : LA (2 * m + 2) = ((default <+ U4) <+ (U4 ^ (2 * m))) <+ U4 := by
    rw [LA_succ (2 * m + 1)]
    have h_eq : 2 * m + 1 = 1 + 2 * m := by omega
    unfold LA
    rw [h_eq, pow_add_append_left default U4 1 (2 * m)]
    rfl
  rw [h_la]
  have h1 := step_drain_entry_48_0349 ((default <+ U4) <+ (U4 ^ (2 * m))) r
  have h2 := shift_drain_2m_0349 m (default <+ U4) (([1, 0] : List (Fin 2)) +> r)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 := step_drain_even_end_70_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  exact stepPlus_trans' (stepPlus_trans' h12 h3) h4

-- ============================================================================
-- Section 6: Shared `W8` Segment Consumers & Universal 5-Block `W8` (+31) Law
-- ============================================================================

/-- Shared 17-bit `W8^2 ++ [1]` prefix consumer (`192a + 1616` micro-steps):
    `LA (a + 1) {{A}}> ([1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
      1] +> r) ⊢⁺ LA (a + 14) {{A}}> ([0] +> r)`. -/
theorem consume_W8_prefix_13_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r))
    [suspect_153_tm]⊢⁺ (LA (a + 14) {{A}}> (([0] : List (Fin 2)) +> r)) := by
  have h1 := consume_1_LA_0349 a (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1] : List (Fin 2)) +> r)
  have h2 := step_A_right_V4_0349 (LA (a + 2)) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1] : List (Fin 2)) +> r)
  rw [← LA_succ (a + 2)] at h2
  have h3 := consume_2_LA_0349 (a + 2) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)
  have h4 := consume_0101_LA_0349 (a + 4) (([1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)
  have h5 := consume_0101_LA_0349 (a + 7) (([1, 0, 1] : List (Fin 2)) +> r)
  have h6 := consume_0101_LA_0349 (a + 10) r
  exact stepPlus_trans' (stepPlus_trans' (stepPlus_trans' (stepPlus_trans' (stepPlus_trans' h1 h2)
    h3) h4) h5) h6

/-- Shared 8-bit `[0, 0, 1, 1, 0, 1, 1, 0]` mid-segment consumer (`96a + 438` micro-steps):
    `LA (a + 1) {{A}}> ([0, 0, 1, 1, 0, 1, 1, 0] +> r) ⊢⁺ LA (a + 7) {{A}}> ([0, 0] +> r)`. -/
theorem consume_W8_mid_6_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r))
    [suspect_153_tm]⊢⁺ (LA (a + 7) {{A}}> (([0, 0] : List (Fin 2)) +> r)) := by
  have h1 := consume_0011_LA_0349 a (([0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_0011_LA_0349 (a + 3) (([0] : List (Fin 2)) +> r)
  exact stepPlus_trans' h1 h2

/-- Shared 3-block `W8^3` consumer (`288a + 3302` micro-steps):
    `LA (a + 1) {{A}}> ((W8 ^ 3) +> r) ⊢⁺ LA (a + 20) {{A}}> ([0, 0] +> r)`. -/
theorem consume_W8_3_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> ((W8 ^ 3) +> r))
    [suspect_153_tm]⊢⁺ (LA (a + 20) {{A}}> (([0, 0] : List (Fin 2)) +> r)) := by
  have h1 := consume_W8_prefix_13_0349 a (([0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_W8_mid_6_0349 (a + 13) r
  exact stepPlus_trans' h1 h2

/-- Remaining 2-block `[0, 0] +> (W8^2 +> r)` consumer (`160a + 1898` micro-steps):
    `LA (a + 1) {{A}}> ([0, 0] +> ((W8 ^ 2) +> r)) ⊢⁺ LA (a + 13) {{A}}> r`. -/
theorem consume_W8_2_tail_12_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0] : List (Fin 2)) +> ((W8 ^ 2) +> r)))
    [suspect_153_tm]⊢⁺ (LA (a + 13) {{A}}> r) := by
  have h1 := consume_00101101_LA_0349 a (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_0011_LA_0349 (a + 3) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h3 := consume_0010101_LA_0349 (a + 6) (([1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h4 := step_A_right_V4_0349 (LA (a + 10)) (([1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  rw [← LA_succ (a + 10)] at h4
  have h5 := consume_1_LA_0349 (a + 10) (([0, 1, 1, 0] : List (Fin 2)) +> r)
  have h6 := step_A_right_V4_0349 (LA (a + 12)) r
  rw [← LA_succ (a + 12)] at h6
  exact stepPlus_trans' (stepPlus_trans' (stepPlus_trans' (stepPlus_trans' (stepPlus_trans' h1 h2)
    h3) h4) h5) h6

/-- Universal 5-Block `W8` (+31) Consumption Theorem on Holdout #330 (`448a + 7442` micro-steps):
    For all `a : Nat` and `r : ListBlank (Fin 2)`,
    `LA (a + 1) {{A}}> ((W8 ^ 5) +> r) ⊢⁺ LA (a + 32) {{A}}> r`. -/
theorem consume_5_W8_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> ((W8 ^ 5) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 32) {{A}}> r) := by
  have h_w8 : (W8 ^ 5) +> r = (W8 ^ 3) +> ((W8 ^ 2) +> r) := by
    exact pow_add_append_right W8 3 2 r
  rw [h_w8]
  have h1 := consume_W8_3_0349 a ((W8 ^ 2) +> r)
  have h2 := consume_W8_2_tail_12_0349 (a + 19) r
  exact stepPlus_trans' h1 h2


lemma consume_1_LA_zero (r : ListBlank (Fin 2)) :
    (LA 0 {{A}}> (([1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 1 {{A}}> r) := by
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  bb_steps

lemma consume_V4_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA a {{A}}> (([0, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 1) {{A}}> r) := by
  have h := step_A_right_V4_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma consume_1_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 2) {{A}}> r) := consume_1_LA_0349 a r

lemma consume_0101_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := consume_0101_LA_0349 a r

lemma consume_0011_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := consume_0011_LA_0349 a r

lemma consume_00101101_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := consume_00101101_LA_0349 a r

lemma consume_0010101_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 4) {{A}}> (([0, 1, 1, 0] : List (Fin 2)) +> r)) := consume_0010101_LA_0349 a r

lemma consume_rewrite92_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA a {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_92_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma rewrite_24_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rewrite_24_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_24_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma rewrite_20_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rewrite_20_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_20_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma rewrite_38a_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rewrite_38a_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_38a_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma rewrite_38b_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rewrite_38b_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_38b_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma rewrite_26_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rewrite_26_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_26_0349 (LA a) r
  rwa [← LA_succ a] at h

lemma rewrite_56_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rewrite_56_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA a {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_56_0349 (LA a) r
  rwa [← LA_succ a] at h


lemma drain_D_even_to_LA7 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> r)) := by
  have h2 := shift_drain_2m_0349 m default r
  have h3 := step_drain_odd_end_66_0349 ((W8 ^ m) +> r)
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> r)
  exact stepPlus_trans' (stepStar_stepPlus_stepPlus h2 h3) h4

lemma drain_D_odd_to_LA7 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m + 1) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> r)) := by
  have h_la : LA (2 * m + 1) = (default <+ U4) <+ (U4 ^ (2 * m)) := by
    have h_eq : 2 * m + 1 = 1 + 2 * m := by omega
    unfold LA
    rw [h_eq, pow_add_append_left default U4 1 (2 * m)]
    rfl
  rw [h_la]
  have h2 := shift_drain_2m_0349 m (default <+ U4) r
  have h3 := step_drain_even_end_70_0349 ((W8 ^ m) +> r)
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> r)
  exact stepPlus_trans' (stepStar_stepPlus_stepPlus h2 h3) h4

lemma drain_D_any_to_LA7 (k : Nat) (r : ListBlank (Fin 2)) :
    ∃ m : Nat, (LA k {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
      (LA 7 {{A}}> ((W8 ^ m) +> r)) := by
  rcases nat_even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m, drain_D_even_to_LA7 m r⟩
  · exact ⟨m, drain_D_odd_to_LA7 m r⟩

lemma drain_A_any_to_LA7 (k : Nat) (r : ListBlank (Fin 2)) :
    ∃ m : Nat, (LA (k + 1) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1,
      0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
      (LA 7 {{A}}> ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))) := by
  rcases nat_even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m, drain_LA_odd_to_LA7_0349 m r⟩
  · exact ⟨m, drain_LA_even_to_LA7_0349 m r⟩


-- ============================================================================
-- Section 7: Pattern Families & Remainder Lemmas
-- ============================================================================

def P_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n) {{A}}> default
def R1_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1]) {{A}}> default
def R2_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1]) {{A}}> default
def R3_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1]) {{A}}> default
def T1_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 1, 0, 0,
  1]) {{A}}> default
def Q_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 1, 1, 1]) {{A}}> default
def S4_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1,
  1]) {{A}}> default
def S6_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1,
  1]) {{A}}> default

abbrev r_R2 : List (Fin 2) := [1, 0, 0, 1]
abbrev r_3 : List (Fin 2) := [1, 0, 1, 1, 0, 1, 0, 0, 1]
abbrev r_4 : List (Fin 2) := [1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
abbrev r_5 : List (Fin 2) := [1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1]

abbrev r_Q : List (Fin 2) := [1]
abbrev r_S6 : List (Fin 2) := [1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
abbrev r_S4 : List (Fin 2) := [1, 0, 1, 1, 0, 0, 1]

def HubTail (k w : Nat) (rt : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (LA k) {{A}}> ((W8 ^ w) +> (rt +> default))

def HubW8 (k w b : Nat) (rend : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (LA k) {{A}}> ((W8 ^ w) +> (([1, 0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default))))

def Scan (k b : Nat) (pfx rend : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (LA k) {{A}}> (pfx +> ((B4 ^ b) +> (rend +> default)))

-- B4 Left-Sweep Lemmas
lemma Q_entry_40 (l : ListBlank (Fin 2)) :
    ((l <+ ([0, 0, 1, 1, 1, 1] : List (Fin 2))) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (r_Q +> default))) := by
  simp only [r_Q, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma S4_entry_100 (l : ListBlank (Fin 2)) :
    ((l <+ ([0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1] : List (Fin 2))) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (r_S4 +> default))) := by
  simp only [r_S4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma S6_entry_152 (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ ([0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1,
      1] : List (Fin 2))) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (r_S6 +> default))) := by
  simp only [U4, r_S6, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma step_D_B4_50 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (B4 +> r))) := by
  simp only [U4, B4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma shift_D_B4 (n : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (U4 ^ n)) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢*
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> ((B4 ^ n) +> r))) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h_l : (l <+ (U4 ^ (n + 1))) = ((l <+ (U4 ^ n)) <+ U4) := pow_add_append_left l U4 n 1
    rw [h_l]
    have h1 := stepPlus_stepStar (step_D_B4_50 (l <+ (U4 ^ n)) r)
    have h2 := ih l (B4 +> r)
    have h_r : (B4 ^ n) +> (B4 +> r) = (B4 ^ (n + 1)) +> r := by
      rw [listblank_append_append, list_pow_append_one]
    rw [h_r] at h2
    exact stepStar_trans h1 h2

lemma step_D_B4_bounce_58 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 1 {{A}}> (([0, 0, 0, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  bb_steps

lemma step_D_B4_bounce_125 (r : ListBlank (Fin 2)) :
    (LA 1 {{A}}> (([0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1] : List (Fin 2)) +> r)) [suspect_153_tm]⊢⁺
    (LA 1 {{A}}> (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  bb_steps

lemma step_D_B4_bounce_to_LA6 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> (([1] : List (Fin 2)) +> r))) [suspect_153_tm]⊢⁺
    (LA 6 {{A}}> (([0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have h1 := step_D_B4_bounce_58 (([1] : List (Fin 2)) +> r)
  have h2 := step_D_B4_bounce_125 r
  have h3 := consume_2_LA_0349 0 (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)
  have h4 := consume_V4_LA 3 (([1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)
  have h5 := consume_2_LA_0349 3 (([0, 0, 1, 0] : List (Fin 2)) +> r)
  exact stepPlus_trans' (stepPlus_trans' (stepPlus_trans' (stepPlus_trans' h1 h2) h3) h4) h5

lemma sweep_D_B4_to_Scan (n : Nat) (rend : List (Fin 2)) :
    (LA (n + 1) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> (rend +> default))) [suspect_153_tm]⊢⁺
    (Scan 6 n [0, 0, 1, 0, 1, 1, 0] rend) := by
  have h1 := shift_D_B4 (n + 1) default (rend +> default)
  have h2 := step_D_B4_bounce_to_LA6 (([1, 1, 0] : List (Fin 2)) +> ((B4 ^ n) +> (rend +> default)))
  exact stepStar_stepPlus_stepPlus h1 h2


-- Remainder Lemmas
lemma rem_halt_1 (k : Nat) :
    ∃ cfg', ((LA k {{A}}> (([0, 0, 0, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ cfg') ∧
      (step suspect_153_tm cfg').isNone := by
  have h := step_halt_00001_0349 (LA k) default
  refine ⟨_, h, ?_⟩
  simp only [step, E, suspect_153_tm, Turing.ListBlank.head_cons]
  rfl

lemma rem_halt_2 (k : Nat) :
    ∃ cfg', ((LA k {{A}}> (([0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ cfg') ∧
      (step suspect_153_tm cfg').isNone := by
  have h := step_halt_00001_0349 (LA k) (([1, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
  refine ⟨_, h, ?_⟩
  simp only [step, E, suspect_153_tm, Turing.ListBlank.head_cons]
  rfl

lemma rem_to_Q_0001_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    ((l <+ [0, 0, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_Q_0001 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (Q_cfg k) := by
  rw [LA_succ k]; exact rem_to_Q_0001_raw (LA k)

lemma rem_to_S6_0001011001_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_S6_0001011001 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (S6_cfg k) := by
  rw [LA_succ k]; exact rem_to_S6_0001011001_raw (LA k)

lemma rem_to_S4_00011001_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_S4_00011001 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (S4_cfg k) := by
  rw [LA_succ k]; exact rem_to_S4_00011001_raw (LA k)

lemma rem_to_R1_001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R1_cfg k) := by
  unfold R1_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_R1_0010 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R1_cfg k) := by
  unfold R1_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_R1_01 (k : Nat) :
    (LA k {{A}}> (([0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R1_cfg k) := by
  unfold R1_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_R2_001001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R2_cfg k) := by
  unfold R2_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_R2_00101 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R2_cfg k) := by
  unfold R2_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_R2_01001 (k : Nat) :
    (LA k {{A}}> (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R2_cfg k) := by
  unfold R2_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_R3_00101001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (R3_cfg k) := by
  unfold R3_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_T1_001011001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (T1_cfg k) := by
  unfold T1_cfg
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_S6_011101_raw (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_to_S6_011101 (k : Nat) :
    (LA (k + 2) {{A}}> (([0, 1, 1, 1, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺ (S6_cfg k) := by
  rw [LA_succ (k + 1), LA_succ k]
  exact rem_to_S6_011101_raw (LA k)

lemma rem_ddrain_82_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (r_3 +> default))) := by
  simp only [U4, r_3, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_ddrain_82 (k : Nat) :
    ∃ m : Nat, (LA (k + 1) {{A}}> (([0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
      (HubTail 7 m r_3) := by
  rw [LA_succ k]
  have h1 := rem_ddrain_82_raw (LA k)
  rcases drain_D_any_to_LA7 k (r_3 +> default) with ⟨m, h2⟩
  exact ⟨m, stepPlus_trans' h1 h2⟩

lemma rem_ddrain_158_raw (l : ListBlank (Fin 2)) :
    ((((l <+ U4) <+ U4) <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> (W8 +> (r_4 +> default)))) := by
  simp only [U4, W8, r_4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_ddrain_158 (k : Nat) :
    ∃ m : Nat, (LA (k + 3) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
      (HubTail 7 m r_4) := by
  rw [LA_succ (k + 2), LA_succ (k + 1), LA_succ k]
  have h1 := rem_ddrain_158_raw (LA k)
  rcases drain_D_any_to_LA7 k (W8 +> (r_4 +> default)) with ⟨m, h2⟩
  have h_w8 : (W8 ^ m) +> (W8 +> (r_4 +> default)) = (W8 ^ (m + 1)) +> (r_4 +> default) := by
    rw [listblank_append_append, list_pow_append_one]
  rw [h_w8] at h2
  exact ⟨m + 1, stepPlus_trans' h1 h2⟩

lemma rem_ddrain_232_raw (l : ListBlank (Fin 2)) :
    ((((l <+ U4) <+ U4) <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> (W8 +> (r_5 +> default)))) := by
  simp only [U4, W8, r_5, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma rem_ddrain_232 (k : Nat) :
    ∃ m : Nat, (LA (k + 3) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [suspect_153_tm]⊢⁺
      (HubTail 7 m r_5) := by
  rw [LA_succ (k + 2), LA_succ (k + 1), LA_succ k]
  have h1 := rem_ddrain_232_raw (LA k)
  rcases drain_D_any_to_LA7 k (W8 +> (r_5 +> default)) with ⟨m, h2⟩
  have h_w8 : (W8 ^ m) +> (W8 +> (r_5 +> default)) = (W8 ^ (m + 1)) +> (r_5 +> default) := by
    rw [listblank_append_append, list_pow_append_one]
  rw [h_w8] at h2
  exact ⟨m + 1, stepPlus_trans' h1 h2⟩


-- ============================================================================
-- Section 8: TapePatternSet & Membership Lemmas (36 Patterns)
-- ============================================================================

abbrev p0 : List (Fin 2) := [0]
abbrev p001010 : List (Fin 2) := [0, 0, 1, 0, 1, 0]
abbrev p0010 : List (Fin 2) := [0, 0, 1, 0]
abbrev p0010110 : List (Fin 2) := [0, 0, 1, 0, 1, 1, 0]
abbrev p00 : List (Fin 2) := [0, 0]
abbrev p010 : List (Fin 2) := [0, 1, 0]
abbrev pnil : List (Fin 2) := []



def pat_Master : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [0, 0, 1] 1 (.rep [1] 2 (.rep [0, 0, 1, 1] 0 .default))
    head  := some A
    right := .default }

def cond_Master : VarCond :=
  .or (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2)) (.not (.ge_const 2 1))))
    (.or (.and (.ge_const 1 2) (.and (.not (.ge_const 1 3)) (.not (.ge_const 2 1))))
      (.or (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2)) (.and (.ge_const 2 3) (.not
        (.ge_const 2 4)))))
        (.or (.and (.ge_const 1 3) (.and (.not (.ge_const 1 4)) (.and (.ge_const 2 3) (.not
          (.ge_const 2 4)))))
             (.and (.ge_const 1 3) (.and (.not (.ge_const 1 4)) (.and (.ge_const 2 5) (.not
               (.ge_const 2 6))))))))

def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_Master, cond_Master)]

abbrev ps_153 : TapePatternSet (Fin 2) (Fin 6) := ps

lemma eval_pat_R1 (vars : Nat -> Nat) (h1 : vars 1 = 1) (h2 : vars 2 = 0) :
    evalTapePattern pat_Master vars = R1_cfg (vars 0) := by
  simp only [pat_Master, R1_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

lemma eval_pat_R2 (vars : Nat -> Nat) (h1 : vars 1 = 2) (h2 : vars 2 = 0) :
    evalTapePattern pat_Master vars = R2_cfg (vars 0) := by
  simp only [pat_Master, R2_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

lemma eval_pat_Q (vars : Nat -> Nat) (h1 : vars 1 = 1) (h2 : vars 2 = 3) :
    evalTapePattern pat_Master vars = Q_cfg (vars 0) := by
  simp only [pat_Master, Q_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

lemma eval_pat_S4 (vars : Nat -> Nat) (h1 : vars 1 = 3) (h2 : vars 2 = 3) :
    evalTapePattern pat_Master vars = S4_cfg (vars 0) := by
  simp only [pat_Master, S4_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

lemma eval_pat_S6 (vars : Nat -> Nat) (h1 : vars 1 = 3) (h2 : vars 2 = 5) :
    evalTapePattern pat_Master vars = S6_cfg (vars 0) := by
  simp only [pat_Master, S6_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

lemma in_R1 (n : Nat) : IsInPatternSet ps_153 (R1_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 1 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_R1 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
lemma in_R2 (n : Nat) : IsInPatternSet ps_153 (R2_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 2 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_R2 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
lemma in_Q (n : Nat) : IsInPatternSet ps_153 (Q_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 1 | 2 => 3 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_Q vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
lemma in_S4 (n : Nat) : IsInPatternSet ps_153 (S4_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 3 | 2 => 3 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_S4 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
lemma in_S6 (n : Nat) : IsInPatternSet ps_153 (S6_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 3 | 2 => 5 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_S6 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
abbrev ReachesCore (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg', (c [suspect_153_tm]⊢⁺ cfg') ∧
    (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone)

lemma reaches_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [suspect_153_tm]⊢⁺ c₂) (h₂ : ReachesCore c₂) : ReachesCore c₁ := by
  rcases h₂ with ⟨cfg', h_plus, h_end⟩
  exact ⟨cfg', stepPlus_trans' h₁ h_plus, h_end⟩

def ScanBundle (b : Nat) (rend : List (Fin 2)) : Prop :=
  (∀ k, k ≥ 4 → ReachesCore (Scan k b p0 rend)) ∧
  (∀ k, k ≥ 4 → ReachesCore (Scan k b p001010 rend)) ∧
  (∀ k, k ≥ 4 → ReachesCore (Scan k b p0010 rend)) ∧
  (∀ k, k ≥ 4 → ReachesCore (Scan k b p0010110 rend)) ∧
  (∀ k, k ≥ 4 → ReachesCore (Scan k b p00 rend)) ∧
  (∀ k, k ≥ 4 → ReachesCore (Scan k b p010 rend)) ∧
  (∀ k, k ≥ 4 → ReachesCore (Scan k b pnil rend))


-- Section 9: Closure Lemmas (Inductively Folded to 5 Core Patterns)

lemma step_P_0 : (P_cfg 0) [suspect_153_tm]⊢⁺ (P_cfg 3) := by
  unfold P_cfg
  simp only [LA, U4, HPow.hPow]
  bb_steps

lemma step_P_1 : (P_cfg 1) [suspect_153_tm]⊢⁺ (S4_cfg 0) := by
  unfold P_cfg S4_cfg
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil]
  bb_steps

lemma step_P_2plus_raw (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ U4) {{A}}> default) [suspect_153_tm]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, listblank_append_cons, listblank_append_nil]
  bb_steps

lemma step_P (n : Nat) :
    ∃ cfg', ((P_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | _ | n'
  · have h3 : (P_cfg 3) [suspect_153_tm]⊢⁺ (S6_cfg 1) := by
      unfold P_cfg; rw [LA_succ 2, LA_succ 1]; exact step_P_2plus_raw (LA 1)
    exact ⟨S6_cfg 1, stepPlus_trans' step_P_0 h3, Or.inl (in_S6 1)⟩
  · exact ⟨S4_cfg 0, step_P_1, Or.inl (in_S4 0)⟩
  · unfold P_cfg
    rw [LA_succ (n' + 1), LA_succ n']
    exact ⟨S6_cfg n', step_P_2plus_raw (LA n'), Or.inl (in_S6 n')⟩


lemma step_R1_0 : (R1_cfg 0) [suspect_153_tm]⊢⁺ (R1_cfg 4) := by
  unfold R1_cfg
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil]
  bb_steps

lemma R1_entry_77 (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ [0, 0, 1]) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma step_R1 (n : Nat) :
    ∃ cfg', ((R1_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | _ | n'
  · exact ⟨R1_cfg 4, step_R1_0, Or.inl (in_R1 4)⟩
  · have h1 := R1_entry_77 default
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have h12 := stepPlus_trans' h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have h_rem := rem_to_R1_001 6
    exact ⟨R1_cfg 6, stepPlus_trans' hc_4 h_rem, Or.inl (in_R1 6)⟩
  · unfold R1_cfg
    rw [LA_succ (n' + 1)]
    have h1 := R1_entry_77 (LA (n' + 1))
    have hs_0 := consume_1_LA n' (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h1 hs_0
    have hs_1 := consume_1_LA (n' + 1) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_1_LA (n' + 2) (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_V4_LA (n' + 4) (([1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA (n' + 4) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (n' + 5) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have h_rem := rem_to_R1_001 (n' + 7)
    exact ⟨R1_cfg (n' + 7), stepPlus_trans' hc_5 h_rem, Or.inl (in_R1 (n' + 7))⟩


lemma T1_entry_84 (l : ListBlank (Fin 2)) :
    ((l <+ [0, 0, 1, 0, 0, 1, 1, 0, 0, 1]) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)) := by
  simp only [listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma step_T1 (n : Nat) :
    ∃ cfg', ((T1_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | n'
  · have h1 := T1_entry_84 default
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have h12 := stepPlus_trans' h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_V4_LA 6 (([0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have h_rem := rem_to_R1_01 7
    exact ⟨R1_cfg 7, stepPlus_trans' hc_5 h_rem, Or.inl (in_R1 7)⟩
  · have h1 := T1_entry_84 (LA (n' + 1))
    have hs_0 := consume_1_LA n' (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h1 hs_0
    have hs_1 := consume_1_LA (n' + 1) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_1_LA (n' + 2) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_V4_LA (n' + 4) (([1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA (n' + 4) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (n' + 5) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_V4_LA (n' + 7) (([0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have h_rem := rem_to_R1_01 (n' + 8)
    exact ⟨R1_cfg (n' + 8), stepPlus_trans' hc_6 h_rem, Or.inl (in_R1 (n' + 8))⟩


lemma step_R3_0 : (R3_cfg 0) [suspect_153_tm]⊢⁺ (T1_cfg 4) := by
  unfold R3_cfg T1_cfg
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil]
  bb_steps

lemma R3_entry_137 (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ [0, 0, 1, 0, 0, 1, 0, 0, 1]) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) := by
  simp only [U4, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma step_R3 (n : Nat) :
    ∃ cfg', ((R3_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | _ | n'
  · exact reaches_trans (step_R3_0) (step_T1 4)
  · have h1 := R3_entry_137 default
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have h12 := stepPlus_trans' h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have h_rem := rem_to_T1_001011001 6
    exact reaches_trans (stepPlus_trans' hc_4 h_rem) (step_T1 6)
  · unfold R3_cfg
    rw [LA_succ (n' + 1)]
    have h1 := R3_entry_137 (LA (n' + 1))
    have hs_0 := consume_1_LA n' (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h1 hs_0
    have hs_1 := consume_1_LA (n' + 1) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_1_LA (n' + 2) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_V4_LA (n' + 4) (([1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA (n' + 4) (([1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (n' + 5) (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have h_rem := rem_to_T1_001011001 (n' + 7)
    exact reaches_trans (stepPlus_trans' hc_5 h_rem) (step_T1 (n' + 7))


lemma step_HubTail_r_R2 (k w : Nat) (hk : k ≥ 7) :
    ∃ cfg', ((HubTail k w r_R2) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  revert k
  refine Nat.strong_induction_on w ?_
  intro w ih k hk
  rcases ge_7_exists k hk with ⟨a, rfl⟩
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 0, 1] : List (Fin 2)) +> default)
    have h_rem := rem_to_R1_001 (a + 8)
    exact ⟨R1_cfg (a + 8), stepPlus_trans' hs_0 h_rem, Or.inl (in_R1 (a + 8))⟩
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have h_rem := rem_to_R2_01001 (a + 11)
    exact ⟨R2_cfg (a + 11), stepPlus_trans' hc_3 h_rem, Or.inl (in_R2 (a + 11))⟩
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have h_rem := rem_to_Q_0001 (a + 19)
    exact ⟨Q_cfg (a + 19), stepPlus_trans' hc_6 h_rem, Or.inl (in_Q (a + 19))⟩
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have h_rem := rem_to_R2_001001 (a + 26)
    exact ⟨R2_cfg (a + 26), stepPlus_trans' hc_8 h_rem, Or.inl (in_R2 (a + 26))⟩
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have h_rem := rem_to_R3_00101001 (a + 32)
    exact reaches_trans (stepPlus_trans' hc_10 h_rem) (step_R3 (a + 32))
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_R2 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_R2
      +> default)) := by
      rw [Nat.add_comm w' 5, pow_add_append_right W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_R2 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 38) (Nat.le_trans (by decide) (Nat.le_add_left 38
      a)))

lemma step_HubTail_r_3 (k w : Nat) (hk : k ≥ 7) :
    ∃ cfg', ((HubTail k w r_3) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  revert k
  refine Nat.strong_induction_on w ?_
  intro w ih k hk
  rcases ge_7_exists k hk with ⟨a, rfl⟩
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have h_rem := rem_to_R1_001 (a + 10)
    exact ⟨R1_cfg (a + 10), stepPlus_trans' hc_2 h_rem, Or.inl (in_R1 (a + 10))⟩
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have h_rem := rem_to_Q_0001 (a + 16)
    exact ⟨Q_cfg (a + 16), stepPlus_trans' hc_5 h_rem, Or.inl (in_Q (a + 16))⟩
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have h_rem := rem_to_R2_001001 (a + 23)
    exact ⟨R2_cfg (a + 23), stepPlus_trans' hc_7 h_rem, Or.inl (in_R2 (a + 23))⟩
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    rcases rem_halt_1 (a + 32) with ⟨cfg', h_rem, h_halt⟩
    exact ⟨cfg', stepPlus_trans' hc_10 h_rem, Or.inr h_halt⟩
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have hs_11 := consume_0010101_LA (a + 31) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := stepPlus_trans' hc_10 hs_11
    have hs_12 := consume_V4_LA (a + 35) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_12 := stepPlus_trans' hc_11 hs_12
    have hs_13 := consume_1_LA (a + 35) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_13 := stepPlus_trans' hc_12 hs_13
    have h_rem := rem_to_R2_01001 (a + 37)
    exact ⟨R2_cfg (a + 37), stepPlus_trans' hc_13 h_rem, Or.inl (in_R2 (a + 37))⟩
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_3 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_3
      +> default)) := by
      rw [Nat.add_comm w' 5, pow_add_append_right W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_3 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 38) (Nat.le_trans (by decide) (Nat.le_add_left 38
      a)))

lemma step_HubTail_r_4 (k w : Nat) (hk : k ≥ 7) :
    ∃ cfg', ((HubTail k w r_4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  revert k
  refine Nat.strong_induction_on w ?_
  intro w ih k hk
  rcases ge_7_exists k hk with ⟨a, rfl⟩
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have h_rem := rem_to_T1_001011001 (a + 9)
    exact reaches_trans (stepPlus_trans' hc_1 h_rem) (step_T1 (a + 9))
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 11) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 11) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have h_rem := rem_to_R2_01001 (a + 15)
    exact ⟨R2_cfg (a + 15), stepPlus_trans' hc_5 h_rem, Or.inl (in_R2 (a + 15))⟩
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := rewrite_20_LA (a + 19) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_1_LA (a + 19) (([1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_1_LA (a + 20) (([1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_1_LA (a + 21) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have hs_11 := consume_V4_LA (a + 23) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := stepPlus_trans' hc_10 hs_11
    have hs_12 := consume_1_LA (a + 23) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_12 := stepPlus_trans' hc_11 hs_12
    have h_rem := rem_to_R1_001 (a + 25)
    exact ⟨R1_cfg (a + 25), stepPlus_trans' hc_12 h_rem, Or.inl (in_R1 (a + 25))⟩
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_0011_LA (a + 25) (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have h_rem := rem_to_S6_0001011001 (a + 28)
    exact ⟨S6_cfg (a + 28), stepPlus_trans' hc_9 h_rem, Or.inl (in_S6 (a + 28))⟩
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1,
      0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have hs_11 := rewrite_38a_LA (a + 31) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := stepPlus_trans' hc_10 hs_11
    have hs_12 := consume_1_LA (a + 31) (([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_12 := stepPlus_trans' hc_11 hs_12
    have hs_13 := consume_1_LA (a + 32) (([1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_13 := stepPlus_trans' hc_12 hs_13
    have hs_14 := consume_1_LA (a + 33) (([0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_14 := stepPlus_trans' hc_13 hs_14
    have hs_15 := consume_0011_LA (a + 34) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_15 := stepPlus_trans' hc_14 hs_15
    have hs_16 := consume_0011_LA (a + 37) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_16 := stepPlus_trans' hc_15 hs_16
    have h_rem := rem_to_R2_001001 (a + 41)
    exact ⟨R2_cfg (a + 41), stepPlus_trans' hc_16 h_rem, Or.inl (in_R2 (a + 41))⟩
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_4 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_4
      +> default)) := by
      rw [Nat.add_comm w' 5, pow_add_append_right W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_4 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 38) (Nat.le_trans (by decide) (Nat.le_add_left 38
      a)))

lemma step_HubTail_r_5 (k w : Nat) (hk : k ≥ 7) :
    ∃ cfg', ((HubTail k w r_5) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  revert k
  refine Nat.strong_induction_on w ?_
  intro w ih k hk
  rcases ge_7_exists k hk with ⟨a, rfl⟩
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 7) (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_V4_LA (a + 9) (([1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA (a + 10) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have h_rem := rem_to_R1_001 (a + 12)
    exact ⟨R1_cfg (a + 12), stepPlus_trans' hc_4 h_rem, Or.inl (in_R1 (a + 12))⟩
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 11) (([1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 11) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 12) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_V4_LA (a + 14) (([0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have h_rem := rem_to_R1_01 (a + 15)
    exact ⟨R1_cfg (a + 15), stepPlus_trans' hc_7 h_rem, Or.inl (in_R1 (a + 15))⟩
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0101_LA (a + 19) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0101_LA (a + 22) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have h_rem := rem_to_R2_01001 (a + 26)
    exact ⟨R2_cfg (a + 26), stepPlus_trans' hc_8 h_rem, Or.inl (in_R2 (a + 26))⟩
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_0011_LA (a + 25) (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have hs_11 := consume_0011_LA (a + 31) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := stepPlus_trans' hc_10 hs_11
    have h_rem := rem_to_Q_0001 (a + 34)
    exact ⟨Q_cfg (a + 34), stepPlus_trans' hc_11 h_rem, Or.inl (in_Q (a + 34))⟩
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have hs_11 := consume_00101101_LA (a + 31) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := stepPlus_trans' hc_10 hs_11
    have hs_12 := consume_0011_LA (a + 34) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_12 := stepPlus_trans' hc_11 hs_12
    have h_rem := rem_to_T1_001011001 (a + 38)
    exact reaches_trans (stepPlus_trans' hc_12 h_rem) (step_T1 (a + 38))
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_5 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_5
      +> default)) := by
      rw [Nat.add_comm w' 5, pow_add_append_right W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_5 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 38) (Nat.le_trans (by decide) (Nat.le_add_left 38
      a)))


lemma step_R2_0 : (R2_cfg 0) [suspect_153_tm]⊢⁺ (R1_cfg 4) := by
  unfold R2_cfg R1_cfg
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil]
  bb_steps

lemma step_R2_succ_raw (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ [0, 0, 1, 0, 0, 1]) {{A}}> default) [suspect_153_tm]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (r_R2 +> default))) := by
  simp only [U4, r_R2, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma step_R2 (n : Nat) :
    ∃ cfg', ((R2_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | n'
  · exact ⟨R1_cfg 4, step_R2_0, Or.inl (in_R1 4)⟩
  · unfold R2_cfg
    rw [LA_succ n']
    have h1 := step_R2_succ_raw (LA n')
    rcases drain_D_any_to_LA7 n' (r_R2 +> default) with ⟨m, h2⟩
    exact reaches_trans (stepPlus_trans' h1 h2) (step_HubTail_r_R2 7 m (by decide))


lemma hub_w0_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 0) +> (([1, 0] : List (Fin 2)) +> r))) [suspect_153_tm]⊢⁺
    (LA (a + 8) {{A}}> (([0] : List (Fin 2)) +> r)) :=
  consume_1_LA (a + 6) (([0] : List (Fin 2)) +> r)

lemma hub_w1_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 1) +> (([1, 0] : List (Fin 2)) +> r))) [suspect_153_tm]⊢⁺
    (LA (a + 11) {{A}}> (([0, 1, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_1 := stepPlus_trans' hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_2 := stepPlus_trans' hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0] : List (Fin 2)) +> r)
  exact stepPlus_trans' hc_2 hs_3

lemma hub_w2_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 2) +> (([1, 0] : List (Fin 2)) +> r))) [suspect_153_tm]⊢⁺
    (LA (a + 20) {{A}}> (([0, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_1 := stepPlus_trans' hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_2 := stepPlus_trans' hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_3 := stepPlus_trans' hc_2 hs_3
  have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_4 := stepPlus_trans' hc_3 hs_4
  have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_5 := stepPlus_trans' hc_4 hs_5
  have hs_6 := consume_0101_LA (a + 16) (([0] : List (Fin 2)) +> r)
  exact stepPlus_trans' hc_5 hs_6

lemma hub_w3_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 3) +> (([1, 0] : List (Fin 2)) +> r))) [suspect_153_tm]⊢⁺
    (LA (a + 26) {{A}}> (([0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
    0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0] : List (Fin 2)) +> r)
  have hc_1 := stepPlus_trans' hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_2 := stepPlus_trans' hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_3 := stepPlus_trans' hc_2 hs_3
  have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_4 := stepPlus_trans' hc_3 hs_4
  have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_5 := stepPlus_trans' hc_4 hs_5
  have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_6 := stepPlus_trans' hc_5 hs_6
  have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_7 := stepPlus_trans' hc_6 hs_7
  have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0] : List (Fin 2)) +> r)
  exact stepPlus_trans' hc_7 hs_8

lemma hub_w4_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 4) +> (([1, 0] : List (Fin 2)) +> r))) [suspect_153_tm]⊢⁺
    (LA (a + 32) {{A}}> (([0, 0, 1, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
    0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_1 := stepPlus_trans' hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_2 := stepPlus_trans' hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
    1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_3 := stepPlus_trans' hc_2 hs_3
  have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_4 := stepPlus_trans' hc_3 hs_4
  have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0] : List (Fin 2)) +> r)
  have hc_5 := stepPlus_trans' hc_4 hs_5
  have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_6 := stepPlus_trans' hc_5 hs_6
  have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_7 := stepPlus_trans' hc_6 hs_7
  have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_8 := stepPlus_trans' hc_7 hs_8
  have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_9 := stepPlus_trans' hc_8 hs_9
  have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 0] : List (Fin 2)) +> r)
  exact stepPlus_trans' hc_9 hs_10

lemma step_HubW8 (rend : List (Fin 2)) (k w b : Nat) (hk : k ≥ 7) (hb : ScanBundle b rend) :
    ∃ cfg', ((HubW8 k w b rend) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  revert k
  refine Nat.strong_induction_on w ?_
  intro w ih k hk
  rcases ge_7_exists k hk with ⟨a, rfl⟩
  rcases w with _ | _ | _ | _ | _ | w'
  · exact reaches_trans (hub_w0_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.1 (a + 8) (Nat.le_trans (by decide) (Nat.le_add_left 8 a)))
  · exact reaches_trans (hub_w1_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.2.2.2.2.1 (a + 11) (Nat.le_trans (by decide) (Nat.le_add_left 11 a)))
  · exact reaches_trans (hub_w2_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.2.2.2.1 (a + 20) (Nat.le_trans (by decide) (Nat.le_add_left 20 a)))
  · exact reaches_trans (hub_w3_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.2.1 (a + 26) (Nat.le_trans (by decide) (Nat.le_add_left 26 a)))
  · exact reaches_trans (hub_w4_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.1 (a + 32) (Nat.le_trans (by decide) (Nat.le_add_left 32 a)))
  · unfold HubW8
    have h_w8 : (W8 ^ (w' + 5)) +> (([1, 0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default))) =
        (W8 ^ 5) +> ((W8 ^ w') +> (([1,
          0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default)))) := by
      rw [Nat.add_comm w' 5, pow_add_append_right W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (([1,
      0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default))))
    exact reaches_trans h1 (ih w' (by omega) (a + 38) (Nat.le_trans (by decide) (Nat.le_add_left 38
      a)))

lemma step_HubW8_r_Q (k w b : Nat) (hk : k ≥ 7) (hb : ScanBundle b r_Q) :
    ∃ cfg', ((HubW8 k w b r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) :=
  step_HubW8 r_Q k w b hk hb
lemma step_HubW8_r_S6 (k w b : Nat) (hk : k ≥ 7) (hb : ScanBundle b r_S6) :
    ∃ cfg', ((HubW8 k w b r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) :=
  step_HubW8 r_S6 k w b hk hb
lemma step_HubW8_r_S4 (k w b : Nat) (hk : k ≥ 7) (hb : ScanBundle b r_S4) :
    ∃ cfg', ((HubW8 k w b r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) :=
  step_HubW8 r_S4 k w b hk hb


lemma step_Scan_p0_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b p0 r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | _ | b'
  · unfold Scan p0 r_Q
    have h_rem := rem_to_R1_01 (a + 4)
    exact ⟨R1_cfg (a + 4), h_rem, Or.inl (in_R1 (a + 4))⟩
  · unfold Scan p0 r_Q
    have h_rem := rem_to_S6_011101 (a + 2)
    exact ⟨S6_cfg (a + 2), h_rem, Or.inl (in_S6 (a + 2))⟩
  · unfold Scan p0
    have h_b4 : (B4 ^ (b' + 2)) +> (r_Q +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_Q
      +> default)) := by
      rw [Nat.add_comm b' 2, pow_add_append_right B4 2 b']
    rw [h_b4]
    rcases drain_A_any_to_LA7 (a + 3) ((B4 ^ b') +> (r_Q +> default)) with ⟨m, h1⟩
    exact reaches_trans h1 (step_HubW8_r_Q 7 m b' (by decide) (ih b' (Nat.lt_trans
      (Nat.lt_succ_self b') (Nat.lt_succ_self (b' + 1)))))

lemma step_Scan_p0_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b p0 r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | _ | b'
  · unfold Scan p0 r_S6
    have hs_0 := rewrite_26_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 3) (([1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 4) (([1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 5) (([0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_0011_LA (a + 6) (([0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have h_rem := rem_to_S4_00011001 (a + 9)
    exact ⟨S4_cfg (a + 9), stepPlus_trans' hc_4 h_rem, Or.inl (in_S4 (a + 9))⟩
  · unfold Scan p0 r_S6
    rcases rem_ddrain_158 (a + 1) with ⟨m, h_rem⟩
    exact reaches_trans (h_rem) (step_HubTail_r_4 7 m (by decide))
  · unfold Scan p0
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S6 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S6
      +> default)) := by
      rw [Nat.add_comm b' 2, pow_add_append_right B4 2 b']
    rw [h_b4]
    rcases drain_A_any_to_LA7 (a + 3) ((B4 ^ b') +> (r_S6 +> default)) with ⟨m, h1⟩
    exact reaches_trans h1 (step_HubW8_r_S6 7 m b' (by decide) (ih b' (Nat.lt_trans
      (Nat.lt_succ_self b') (Nat.lt_succ_self (b' + 1)))))

lemma step_Scan_p0_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b p0 r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | _ | b'
  · unfold Scan p0 r_S4
    have hs_0 := consume_0101_LA (a + 3) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have h_rem := rem_to_R2_01001 (a + 7)
    exact ⟨R2_cfg (a + 7), stepPlus_trans' hs_0 h_rem, Or.inl (in_R2 (a + 7))⟩
  · unfold Scan p0 r_S4
    rcases rem_ddrain_232 (a + 1) with ⟨m, h_rem⟩
    exact reaches_trans (h_rem) (step_HubTail_r_5 7 m (by decide))
  · unfold Scan p0
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S4 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S4
      +> default)) := by
      rw [Nat.add_comm b' 2, pow_add_append_right B4 2 b']
    rw [h_b4]
    rcases drain_A_any_to_LA7 (a + 3) ((B4 ^ b') +> (r_S4 +> default)) with ⟨m, h1⟩
    exact reaches_trans h1 (step_HubW8_r_S4 7 m b' (by decide) (ih b' (Nat.lt_trans
      (Nat.lt_succ_self b') (Nat.lt_succ_self (b' + 1)))))

lemma step_Scan_p001010_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b p001010 r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p001010 r_Q
    have hs_0 := consume_0010101_LA (a + 3) default
    have hs_1 := consume_V4_LA (a + 7) default
    have hc_1 := stepPlus_trans' hs_0 hs_1
    exact reaches_trans (hc_1) (step_P (a + 8))
  · unfold Scan p001010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      pow_succ_append_right B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_0010101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_V4_LA (a + 7) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 8) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_3 := stepPlus_trans' hc_2 hs_3
    exact reaches_trans (hc_3) ((ih b' (Nat.lt_succ_self b')).1 (a + 10) (Nat.le_trans (by decide)
      (Nat.le_add_left 10 a)))

lemma step_Scan_p001010_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b p001010 r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p001010 r_S6
    have hs_0 := consume_0010101_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 7) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 7) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have h_rem := rem_to_T1_001011001 (a + 11)
    exact reaches_trans (stepPlus_trans' hc_2 h_rem) (step_T1 (a + 11))
  · unfold Scan p001010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      pow_succ_append_right B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_0010101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_V4_LA (a + 7) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 8) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_3 := stepPlus_trans' hc_2 hs_3
    exact reaches_trans (hc_3) ((ih b' (Nat.lt_succ_self b')).1 (a + 10) (Nat.le_trans (by decide)
      (Nat.le_add_left 10 a)))

lemma step_Scan_p001010_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b p001010 r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p001010 r_S4
    have hs_0 := consume_0010101_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 7) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_V4_LA (a + 8) (([0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have h_rem := rem_to_R1_01 (a + 9)
    exact ⟨R1_cfg (a + 9), stepPlus_trans' hc_2 h_rem, Or.inl (in_R1 (a + 9))⟩
  · unfold Scan p001010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      pow_succ_append_right B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_0010101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_V4_LA (a + 7) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 8) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_3 := stepPlus_trans' hc_2 hs_3
    exact reaches_trans (hc_3) ((ih b' (Nat.lt_succ_self b')).1 (a + 10) (Nat.le_trans (by decide)
      (Nat.le_add_left 10 a)))

lemma step_Scan_p0010_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b p0010 r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | _ | b'
  · unfold Scan p0010 r_Q
    have h_rem := rem_to_R2_00101 (a + 4)
    exact ⟨R2_cfg (a + 4), h_rem, Or.inl (in_R2 (a + 4))⟩
  · unfold Scan p0010 r_Q
    have hs_0 := consume_rewrite92_LA (a + 3) default
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1,
      0] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1,
      0] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have h_rem := rem_to_R1_0010 (a + 9)
    exact ⟨R1_cfg (a + 9), stepPlus_trans' hc_6 h_rem, Or.inl (in_R1 (a + 9))⟩
  · unfold Scan p0010
    have h_b4 : (B4 ^ (b' + 2)) +> (r_Q +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_Q
      +> default)) := by
      rw [Nat.add_comm b' 2, pow_add_append_right B4 2 b']
    rw [h_b4]
    have hs_0 := consume_rewrite92_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_6 := stepPlus_trans' hc_5 hs_6
    exact reaches_trans (hc_6) ((ih b' (Nat.lt_trans (Nat.lt_succ_self b') (Nat.lt_succ_self (b' +
      1)))).2.2.2.1 (a + 9) (Nat.le_trans (by decide) (Nat.le_add_left 9 a)))

lemma step_Scan_p0010_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b p0010 r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | _ | b'
  · unfold Scan p0010 r_S6
    have hs_0 := rewrite_38b_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 3) (([1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 4) (([1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 5) (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 7) (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_V4_LA (a + 8) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_V4_LA (a + 9) (([0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have h_rem := rem_to_R1_01 (a + 10)
    exact ⟨R1_cfg (a + 10), stepPlus_trans' hc_6 h_rem, Or.inl (in_R1 (a + 10))⟩
  · unfold Scan p0010 r_S6
    have hs_0 := consume_rewrite92_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    rcases rem_ddrain_82 (a + 8) with ⟨m, h_rem⟩
    exact reaches_trans (stepPlus_trans' hc_6 h_rem) (step_HubTail_r_3 7 m (by decide))
  · unfold Scan p0010
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S6 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S6
      +> default)) := by
      rw [Nat.add_comm b' 2, pow_add_append_right B4 2 b']
    rw [h_b4]
    have hs_0 := consume_rewrite92_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_6 := stepPlus_trans' hc_5 hs_6
    exact reaches_trans (hc_6) ((ih b' (Nat.lt_trans (Nat.lt_succ_self b') (Nat.lt_succ_self (b' +
      1)))).2.2.2.1 (a + 9) (Nat.le_trans (by decide) (Nat.le_add_left 9 a)))

lemma step_Scan_p0010_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b p0010 r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | _ | b'
  · unfold Scan p0010 r_S4
    have hs_0 := consume_0010101_LA (a + 3) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 7) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have h_rem := rem_to_R1_001 (a + 9)
    exact ⟨R1_cfg (a + 9), stepPlus_trans' hc_2 h_rem, Or.inl (in_R1 (a + 9))⟩
  · unfold Scan p0010 r_S4
    have hs_0 := consume_rewrite92_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := rewrite_24_LA (a + 8) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_1_LA (a + 8) (([1, 1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_1_LA (a + 9) (([1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have hs_10 := consume_1_LA (a + 10) (([0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := stepPlus_trans' hc_9 hs_10
    have hs_11 := consume_V4_LA (a + 12) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := stepPlus_trans' hc_10 hs_11
    have h_rem := rem_to_R1_001 (a + 13)
    exact ⟨R1_cfg (a + 13), stepPlus_trans' hc_11 h_rem, Or.inl (in_R1 (a + 13))⟩
  · unfold Scan p0010
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S4 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S4
      +> default)) := by
      rw [Nat.add_comm b' 2, pow_add_append_right B4 2 b']
    rw [h_b4]
    have hs_0 := consume_rewrite92_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_6 := stepPlus_trans' hc_5 hs_6
    exact reaches_trans (hc_6) ((ih b' (Nat.lt_trans (Nat.lt_succ_self b') (Nat.lt_succ_self (b' +
      1)))).2.2.2.1 (a + 9) (Nat.le_trans (by decide) (Nat.le_add_left 9 a)))

lemma step_Scan_p0010110_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b p0010110 r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p0010110 r_Q
    have hs_0 := consume_00101101_LA (a + 3) default
    have hs_1 := consume_0011_LA (a + 6) (([0] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    try rw [zero2_append_default] at hc_1
    repeat rw [zero1_append_default] at hc_1
    exact reaches_trans (hc_1) (step_P (a + 10))
  · unfold Scan p0010110
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      pow_succ_append_right B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_00101101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_0011_LA (a + 6) (([0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 9) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.1 (a + 13) (Nat.le_trans (by
      decide) (Nat.le_add_left 13 a)))

lemma step_Scan_p0010110_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b p0010110 r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p0010110 r_S6
    have hs_0 := consume_00101101_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 6) (([0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    rcases rem_halt_2 (a + 10) with ⟨cfg', h_rem, h_halt⟩
    exact ⟨cfg', stepPlus_trans' hc_1 h_rem, Or.inr h_halt⟩
  · unfold Scan p0010110
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      pow_succ_append_right B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_00101101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_0011_LA (a + 6) (([0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 9) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.1 (a + 13) (Nat.le_trans (by
      decide) (Nat.le_add_left 13 a)))

lemma step_Scan_p0010110_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b p0010110 r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p0010110 r_S4
    have hs_0 := consume_00101101_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 6) (([0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have h_rem := rem_to_S4_00011001 (a + 9)
    exact ⟨S4_cfg (a + 9), stepPlus_trans' hc_1 h_rem, Or.inl (in_S4 (a + 9))⟩
  · unfold Scan p0010110
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      pow_succ_append_right B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_00101101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_0011_LA (a + 6) (([0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 9) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.1 (a + 13) (Nat.le_trans (by
      decide) (Nat.le_add_left 13 a)))

lemma step_Scan_p00_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b p00 r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p00 r_Q
    have h_rem := rem_to_R1_001 (a + 4)
    exact ⟨R1_cfg (a + 4), h_rem, Or.inl (in_R1 (a + 4))⟩
  · unfold Scan p00
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      pow_succ_append_right B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_0011_LA (a + 3) (([1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    exact reaches_trans (hs_0) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.1 (a + 7) (Nat.le_trans (by
      decide) (Nat.le_add_left 7 a)))

lemma step_Scan_p00_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b p00 r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p00 r_S6
    have hs_0 := rewrite_24_LA (a + 3) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 3) (([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 4) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 5) (([0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 7) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 7) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have h_rem := rem_to_R2_01001 (a + 11)
    exact ⟨R2_cfg (a + 11), stepPlus_trans' hc_5 h_rem, Or.inl (in_R2 (a + 11))⟩
  · unfold Scan p00
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      pow_succ_append_right B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_0011_LA (a + 3) (([1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    exact reaches_trans (hs_0) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.1 (a + 7) (Nat.le_trans (by
      decide) (Nat.le_add_left 7 a)))

lemma step_Scan_p00_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b p00 r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p00 r_S4
    have h_rem := rem_to_T1_001011001 (a + 4)
    exact reaches_trans (h_rem) (step_T1 (a + 4))
  · unfold Scan p00
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      pow_succ_append_right B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_0011_LA (a + 3) (([1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    exact reaches_trans (hs_0) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.1 (a + 7) (Nat.le_trans (by
      decide) (Nat.le_add_left 7 a)))

lemma step_Scan_p010_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b p010 r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p010 r_Q
    have hs_0 := consume_0101_LA (a + 3) default
    rw [zero1_append_default] at hs_0
    exact reaches_trans (hs_0) (step_P (a + 7))
  · unfold Scan p010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      pow_succ_append_right B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_0101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_V4_LA (a + 7) ((B4 ^ b') +> (r_Q +> default))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    exact reaches_trans (hc_1) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.2 (a + 8) (Nat.le_trans (by
      decide) (Nat.le_add_left 8 a)))

lemma step_Scan_p010_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b p010 r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p010 r_S6
    have hs_0 := consume_0101_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := rewrite_56_LA (a + 6) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA (a + 6) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA (a + 7) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_V4_LA (a + 9) (([1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_1_LA (a + 9) (([1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_1_LA (a + 10) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have hs_8 := consume_V4_LA (a + 12) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := stepPlus_trans' hc_7 hs_8
    have hs_9 := consume_1_LA (a + 12) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := stepPlus_trans' hc_8 hs_9
    have h_rem := rem_to_R1_001 (a + 14)
    exact ⟨R1_cfg (a + 14), stepPlus_trans' hc_9 h_rem, Or.inl (in_R1 (a + 14))⟩
  · unfold Scan p010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      pow_succ_append_right B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_0101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_V4_LA (a + 7) ((B4 ^ b') +> (r_S6 +> default))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    exact reaches_trans (hc_1) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.2 (a + 8) (Nat.le_trans (by
      decide) (Nat.le_add_left 8 a)))

lemma step_Scan_p010_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b p010 r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan p010 r_S4
    have hs_0 := consume_0101_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 6) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have h_rem := rem_to_Q_0001 (a + 9)
    exact ⟨Q_cfg (a + 9), stepPlus_trans' hc_1 h_rem, Or.inl (in_Q (a + 9))⟩
  · unfold Scan p010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      pow_succ_append_right B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_0101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_V4_LA (a + 7) ((B4 ^ b') +> (r_S4 +> default))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    exact reaches_trans (hc_1) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.2 (a + 8) (Nat.le_trans (by
      decide) (Nat.le_add_left 8 a)))

lemma step_Scan_pnil_r_Q (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_Q) :
    ∃ cfg', ((Scan k b pnil r_Q) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan pnil r_Q
    have hs_0 := consume_1_LA (a + 3) default
    exact reaches_trans (hs_0) (step_P (a + 5))
  · unfold Scan pnil
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      pow_succ_append_right B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_1_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_1_LA (a + 4) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).1 (a + 7) (Nat.le_trans (by decide)
      (Nat.le_add_left 7 a)))

lemma step_Scan_pnil_r_S6 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S6) :
    ∃ cfg', ((Scan k b pnil r_S6) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan pnil r_S6
    have hs_0 := consume_1_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 4) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have h_rem := rem_to_T1_001011001 (a + 8)
    exact reaches_trans (stepPlus_trans' hc_1 h_rem) (step_T1 (a + 8))
  · unfold Scan pnil
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      pow_succ_append_right B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_1_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_1_LA (a + 4) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).1 (a + 7) (Nat.le_trans (by decide)
      (Nat.le_add_left 7 a)))

lemma step_Scan_pnil_r_S4 (k b : Nat) (hk : k ≥ 4) (ih : ∀ b' < b, ScanBundle b' r_S4) :
    ∃ cfg', ((Scan k b pnil r_S4) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases ge_4_exists k hk with ⟨a, rfl⟩
  rcases b with _ | b'
  · unfold Scan pnil r_S4
    have hs_0 := consume_1_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 5) (([0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have h_rem := rem_to_R1_01 (a + 6)
    exact ⟨R1_cfg (a + 6), stepPlus_trans' hc_1 h_rem, Or.inl (in_R1 (a + 6))⟩
  · unfold Scan pnil
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      pow_succ_append_right B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_1_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_1_LA (a + 4) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := stepPlus_trans' hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := stepPlus_trans' hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).1 (a + 7) (Nat.le_trans (by decide)
      (Nat.le_add_left 7 a)))



lemma scanBundle_all_r_Q (b : Nat) : ScanBundle b r_Q := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  exact ⟨fun k hk => step_Scan_p0_r_Q k b hk ih,
         fun k hk => step_Scan_p001010_r_Q k b hk ih,
         fun k hk => step_Scan_p0010_r_Q k b hk ih,
         fun k hk => step_Scan_p0010110_r_Q k b hk ih,
         fun k hk => step_Scan_p00_r_Q k b hk ih,
         fun k hk => step_Scan_p010_r_Q k b hk ih,
         fun k hk => step_Scan_pnil_r_Q k b hk ih⟩

lemma scanBundle_all_r_S6 (b : Nat) : ScanBundle b r_S6 := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  exact ⟨fun k hk => step_Scan_p0_r_S6 k b hk ih,
         fun k hk => step_Scan_p001010_r_S6 k b hk ih,
         fun k hk => step_Scan_p0010_r_S6 k b hk ih,
         fun k hk => step_Scan_p0010110_r_S6 k b hk ih,
         fun k hk => step_Scan_p00_r_S6 k b hk ih,
         fun k hk => step_Scan_p010_r_S6 k b hk ih,
         fun k hk => step_Scan_pnil_r_S6 k b hk ih⟩

lemma scanBundle_all_r_S4 (b : Nat) : ScanBundle b r_S4 := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  exact ⟨fun k hk => step_Scan_p0_r_S4 k b hk ih,
         fun k hk => step_Scan_p001010_r_S4 k b hk ih,
         fun k hk => step_Scan_p0010_r_S4 k b hk ih,
         fun k hk => step_Scan_p0010110_r_S4 k b hk ih,
         fun k hk => step_Scan_p00_r_S4 k b hk ih,
         fun k hk => step_Scan_p010_r_S4 k b hk ih,
         fun k hk => step_Scan_pnil_r_S4 k b hk ih⟩


lemma step_Q (n : Nat) :
    ∃ cfg', ((Q_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | n'
  · have h1 := Q_entry_40 default
    have h2 := step_D_B4_bounce_to_LA6 default
    have h3 := rem_to_R1_0010 6
    exact ⟨R1_cfg 6, stepPlus_trans' (stepPlus_trans' h1 h2) h3, Or.inl (in_R1 6)⟩
  · have h1 := Q_entry_40 (LA (n' + 1))
    have h2 := sweep_D_B4_to_Scan n' r_Q
    exact reaches_trans (stepPlus_trans' h1 h2) ((scanBundle_all_r_Q n').2.2.2.1 6 (by decide))

lemma step_S4 (n : Nat) :
    ∃ cfg', ((S4_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | n'
  · have h1 := S4_entry_100 default
    have h2 := step_D_B4_bounce_to_LA6 (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have h12 := stepPlus_trans' h1 h2
    have hs_0 := rewrite_24_LA 5 (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h12 hs_0
    have hs_1 := consume_1_LA 5 (([1, 1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_1_LA 6 (([1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA 7 (([0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_V4_LA 9 (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have h_rem := rem_to_R1_001 10
    exact ⟨R1_cfg 10, stepPlus_trans' hc_4 h_rem, Or.inl (in_R1 10)⟩
  · have h1 := S4_entry_100 (LA (n' + 1))
    have h2 := sweep_D_B4_to_Scan n' r_S4
    exact reaches_trans (stepPlus_trans' h1 h2) ((scanBundle_all_r_S4 n').2.2.2.1 6 (by decide))

lemma S6_0_entry_232 :
    (S6_cfg 0) [suspect_153_tm]⊢⁺
    (LA 0 {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) := by
  unfold S6_cfg
  simp only [LA, U4, HPow.hPow,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps

lemma step_S6 (n : Nat) :
    ∃ cfg', ((S6_cfg n) [suspect_153_tm]⊢⁺ cfg') ∧
      (IsInPatternSet ps_153 cfg' ∨ (step suspect_153_tm cfg').isNone) := by
  rcases n with _ | _ | n'
  · have h1 := S6_0_entry_232
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have h12 := stepPlus_trans' h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := stepPlus_trans' h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := stepPlus_trans' hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := stepPlus_trans' hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := stepPlus_trans' hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := stepPlus_trans' hc_3 hs_4
    have hs_5 := consume_V4_LA 6 (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := stepPlus_trans' hc_4 hs_5
    have hs_6 := consume_V4_LA 7 (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := stepPlus_trans' hc_5 hs_6
    have hs_7 := consume_V4_LA 8 (([0, 1] : List (Fin 2)) +> default)
    have hc_7 := stepPlus_trans' hc_6 hs_7
    have h_rem := rem_to_R1_01 9
    exact ⟨R1_cfg 9, stepPlus_trans' hc_7 h_rem, Or.inl (in_R1 9)⟩
  · have h1 := S6_entry_152 default
    have h2 := step_D_B4_bounce_to_LA6 (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have h12 := stepPlus_trans' h1 h2
    rcases rem_ddrain_82 5 with ⟨m, h3⟩
    exact reaches_trans (stepPlus_trans' h12 h3) (step_HubTail_r_3 7 m (by decide))
  · unfold S6_cfg
    rw [LA_succ (n' + 1)]
    have h1 := S6_entry_152 (LA (n' + 1))
    have h2 := sweep_D_B4_to_Scan n' r_S6
    exact reaches_trans (stepPlus_trans' h1 h2) ((scanBundle_all_r_S6 n').2.2.2.1 6 (by decide))



-- ============================================================================
-- Section 10: Initial Reachability & Main Cryptid Theorem (5 Core Patterns)
-- ============================================================================

theorem init_to_S6_1 : (init []) [suspect_153_tm]⊢* (S6_cfg 1) := by
  have h1 : (init []) [suspect_153_tm]⊢* (P_cfg 3) := stepPlus_stepStar step_P_0
  have h2 : (P_cfg 3) [suspect_153_tm]⊢⁺ (S6_cfg 1) := by
    unfold P_cfg; rw [LA_succ 2, LA_succ 1]; exact step_P_2plus_raw (LA 1)
  exact stepStar_trans h1 (stepPlus_stepStar h2)


theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨S6_cfg 1, init_to_S6_1, in_S6 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  cases h_mem with
  | head =>
    simp only [cond_Master, evalVarCond] at h_cond
    rcases h_cond with ⟨h1a, h1b, h2a⟩ | ⟨h1a, h1b, h2a⟩ | ⟨h1a, h1b, h2a, h2b⟩ | ⟨h1a, h1b, h2a,
      h2b⟩ | ⟨h1a, h1b, h2a, h2b⟩
    · have h1 : vars 1 = 1 := by omega
      have h2 : vars 2 = 0 := by omega
      rw [eval_pat_R1 vars h1 h2]; exact step_R1 (vars 0)
    · have h1 : vars 1 = 2 := by omega
      have h2 : vars 2 = 0 := by omega
      rw [eval_pat_R2 vars h1 h2]; exact step_R2 (vars 0)
    · have h1 : vars 1 = 1 := by omega
      have h2 : vars 2 = 3 := by omega
      rw [eval_pat_Q vars h1 h2]; exact step_Q (vars 0)
    · have h1 : vars 1 = 3 := by omega
      have h2 : vars 2 = 3 := by omega
      rw [eval_pat_S4 vars h1 h2]; exact step_S4 (vars 0)
    · have h1 : vars 1 = 3 := by omega
      have h2 : vars 2 = 5 := by omega
      rw [eval_pat_S6 vars h1 h2]; exact step_S6 (vars 0)
  | tail _ h_mem =>
    nomatch h_mem

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA
