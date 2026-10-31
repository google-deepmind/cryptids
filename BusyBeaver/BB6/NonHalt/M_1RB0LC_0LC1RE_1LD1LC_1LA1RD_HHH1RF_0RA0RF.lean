/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LC_0LC1RE_1LD1LC_1LA1RD_---1RF_0RA0RF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LC_0LC1RE_1LD1LC_1LA1RD_---1RF_0RA0RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_0LC1RE_1LD1LC_1LA1RD_HHH1RF_0RA0RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LC_0LC1RE_1LD1LC_1LA1RD_---1RF_0RA0RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

-- ============================================================================
-- Section 6: Proof of Non-Halting (IsDoesNotHalt target_tm)
-- ============================================================================

namespace Solution

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 0 = some config := rfl

@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 1 = step M config := rfl

@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma multiStep_add (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma stepStar_refl (tm : Machine Γ Λ) (c : Cfg Γ Λ) : c [tm]⊢* c :=
  ⟨0, rfl⟩

lemma step_to_stepStar {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ :=
  ⟨1, h⟩

lemma step_to_stepPlus {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ :=
  ⟨1, Nat.succ_pos 0, h⟩

lemma stepPlus_to_stepStar {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by
  rcases h with ⟨n, _, hn⟩; exact ⟨n, hn⟩

lemma stepPlus_stepStar_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn_pos, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, Nat.add_pos_left hn_pos m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm_pos, hm⟩
  exact ⟨n + m, Nat.add_pos_right n hm_pos, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma step_stepStar_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_trans (step_to_stepPlus h₁) h₂

lemma step_stepPlus_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_trans (step_to_stepPlus h₁) h₂

-- ============================================================================
-- Tape & List Algebra Lemmas
-- ============================================================================

lemma multiStep_step {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : Nat}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢^{n} c₃) : c₁ [tm]⊢^{n + 1} c₃ := by
  have := multiStep_trans tm c₁ c₂ c₃ 1 n h₁ h₂
  rwa [Nat.add_comm 1 n] at this

omit [Inhabited Γ] in
@[simp] lemma pow_zero_list (l : List Γ) : l ^ (0 : Nat) = [] := rfl

omit [Inhabited Γ] in
lemma pow_succ_list (l : List Γ) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl

omit [Inhabited Γ] in
@[simp] theorem list_pow_add (l : List Γ) (n m : Nat) : l ^ (n + m) = l ^ n ++ l ^ m := by
  induction n with
  | zero => simp [pow_zero_list]
  | succ n ih =>
    rw [Nat.succ_add, pow_succ_list, pow_succ_list, ih, List.append_assoc]

omit [Inhabited Γ] in
lemma pow_succ_right (l : List Γ) (n : Nat) : l ^ (n + 1) = l ^ n ++ l := by
  rw [list_pow_add]; simp [pow_succ_list, pow_zero_list]

@[simp] lemma listblank_append_nil (s : ListBlank Γ) : ([] : List Γ) +> s = s := rfl

@[simp] lemma listblank_append_cons (a : Γ) (l : List Γ) (s : ListBlank Γ) :
    (a :: l) +> s = a >> (l +> s) := rfl

@[simp] lemma listblank_append_assoc (l₁ l₂ : List Γ) (s : ListBlank Γ) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  exact Turing.ListBlank.append_assoc l₁ l₂ s

@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

@[simp] lemma zero_cons_default : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default := by
  change ListBlank.cons default default = default
  exact ListBlank.cons_head_tail default

@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
    ⟨some A, ⟨0, default, default⟩⟩ := rfl

macro "step1" : tactic => `(tactic| (
  try simp only [init_nil, pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  refine multiStep_step (by rfl) ?_
  simp only [Turing.Tape.move, Tape.write,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]))

macro "run_steps" n:num : tactic => `(tactic| (
  iterate $n step1
  simp only [pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail, multiStep_zero]
  rfl))

@[simp] lemma zeros_append_default (n : Nat) :
    ([0] : List (Fin 2)) ^ n +> (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, List.singleton_append, listblank_append_cons, ih, zero_cons_default]

lemma one_pow_comm_cons (k : Nat) (s : ListBlank (Fin 2)) :
    ([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> s) =
    (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> s) := by
  change ([1] : List (Fin 2)) ^ k +> (([1] : List (Fin 2)) ^ 1 +> s) = _
  rw [← listblank_append_assoc, ← list_pow_add, Nat.add_comm k 1, list_pow_add, listblank_append_assoc]
  rfl

lemma append_pow_split (l : List (Fin 2)) (a b : Nat) (s : ListBlank (Fin 2)) :
    l ^ (a + b) +> s = l ^ a +> (l ^ b +> s) := by
  rw [list_pow_add, listblank_append_assoc]

/-- Key pattern shift identity: `[1, 1, 1] ++ [0, 1, 1, 1]^b ++ [0] = [1, 1, 1, 0]^(b+1)`. -/
lemma shift_0111_to_1110 (b : Nat) (s : ListBlank (Fin 2)) :
    (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> s)) =
    ([1, 1, 1, 0] : List (Fin 2)) ^ (b + 1) +> s := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ_list]
    change (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> s)) = _
    rw [ih]
    rfl

lemma shift_00111_to_0001110 (b : Nat) (s : ListBlank (Fin 2)) :
    (0 : Fin 2) >> (0 : Fin 2) >> (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> s)) =
    (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (([1, 1, 1, 0] : List (Fin 2)) ^ b +> s) := by
  cases b with
  | zero => rfl
  | succ b =>
    have h1 : ([0, 1, 1, 1] : List (Fin 2)) ^ (b + 1) +> ((0 : Fin 2) >> s) =
        (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> s)) := by
      rw [pow_succ_list]; rfl
    rw [h1, shift_0111_to_1110 b s]

lemma shift_1110_111_0111 (b : Nat) (s : ListBlank (Fin 2)) :
    (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> s)) =
    ([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> s := by
  rw [shift_0111_to_1110 b s]
  rfl

-- ============================================================================
-- Section 6.1: Primitive Sweep Loops & Micro-Step Building Blocks
-- ============================================================================

/-- `F` sweeps right across `1^m`, turning `1`s into `0`s on the left tape. -/
lemma F_sweep (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some F, ⟨((([1] : List (Fin 2)) ^ m +> R)).head, L,
               ((([1] : List (Fin 2)) ^ m +> R)).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢*
    ⟨some F, ⟨R.head, ([0] : List (Fin 2)) ^ m +> L, R.tail⟩⟩ := by
  induction m generalizing L with
  | zero => exact stepStar_refl _ _
  | succ m ih =>
    have h1 :
        (⟨some F, ⟨((([1] : List (Fin 2)) ^ (m + 1) +> R)).head, L,
                   ((([1] : List (Fin 2)) ^ (m + 1) +> R)).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
          [target_tm]⊢^{1}
        ⟨some F, ⟨((([1] : List (Fin 2)) ^ m +> R)).head, (0 : Fin 2) >> L,
                   ((([1] : List (Fin 2)) ^ m +> R)).tail⟩⟩ := by run_steps 1
    refine stepStar_trans (step_to_stepStar h1) ?_
    have h2 := ih ((0 : Fin 2) >> L)
    have heq : ([0] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> L) =
        ([0] : List (Fin 2)) ^ (m + 1) +> L := by
      rw [pow_succ_right, listblank_append_assoc]; rfl
    rw [heq] at h2
    exact h2

/-- `D` sweeps right across `1^m` and lands on `0`. -/
lemma D_sweep (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some D, ⟨1, L, ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some D, ⟨0, ([1] : List (Fin 2)) ^ (m + 1) +> L, R⟩⟩ := by
  induction m generalizing L with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ m ih =>
    have h1 :
        (⟨some D, ⟨1, L, ([1] : List (Fin 2)) ^ (m + 1) +> ((0 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
          [target_tm]⊢^{1}
        ⟨some D, ⟨1, (1 : Fin 2) >> L, ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> R)⟩⟩ := by run_steps 1
    refine step_stepPlus_trans h1 ?_
    have h2 := ih ((1 : Fin 2) >> L)
    have heq : ([1] : List (Fin 2)) ^ (m + 1) +> ((1 : Fin 2) >> L) =
        ([1] : List (Fin 2)) ^ (m + 2) +> L := by
      rw [one_pow_comm_cons]; rfl
    rw [heq] at h2
    exact h2

/-- `C` sweeps left across `1^m` and lands on `0`. -/
lemma C_sweep (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨1, ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> L), R⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (m + 1) +> R⟩⟩ := by
  induction m generalizing R with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ m ih =>
    have h1 :
        (⟨some C, ⟨1, ([1] : List (Fin 2)) ^ (m + 1) +> ((0 : Fin 2) >> L), R⟩⟩ : Cfg (Fin 2) (Fin 6))
          [target_tm]⊢^{1}
        ⟨some C, ⟨1, ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> L), (1 : Fin 2) >> R⟩⟩ := by run_steps 1
    refine step_stepPlus_trans h1 ?_
    have h2 := ih ((1 : Fin 2) >> R)
    have heq : ([1] : List (Fin 2)) ^ (m + 1) +> ((1 : Fin 2) >> R) =
        ([1] : List (Fin 2)) ^ (m + 2) +> R := by
      rw [one_pow_comm_cons]; rfl
    rw [heq] at h2
    exact h2

/-- Forward sweep across `1^m 0 1`: turns `1^m` into `0^m` on the left tape and consumes `0 1`. -/
lemma forward_sweep (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ m +> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
               (0 : Fin 2) >> R⟩⟩ := by
  have h5 :
      (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
                 ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{5}
      ⟨some F, ⟨((([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R))).head,
                 (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L,
                 ((([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R))).tail⟩⟩ := by run_steps 5
  have hF := F_sweep m ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) ((0 : Fin 2) >> (1 : Fin 2) >> R)
  simp only [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons] at hF
  have h2 :
      (⟨some F, ⟨0, ([0] : List (Fin 2)) ^ m +> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
                 (1 : Fin 2) >> R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{2}
      ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ m +> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
                 (0 : Fin 2) >> R⟩⟩ := by run_steps 2
  exact stepPlus_trans (stepPlus_stepStar_trans ⟨5, by decide, h5⟩ hF) ⟨2, by decide, h2⟩

/-- Return sweep across `1^m 0`: consumes `1 1 1 0` on the left and produces `1^(m+3) 0 1` on the right. -/
lemma return_sweep (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (m + 3) +> ((0 : Fin 2) >> (1 : Fin 2) >> R)⟩⟩ := by
  have h1 :
      (⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
                 ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{1}
      ⟨some D, ⟨1, (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
                 ([1] : List (Fin 2)) ^ (m + 1) +> ((0 : Fin 2) >> R)⟩⟩ := by run_steps 1
  have hD := D_sweep (m + 1) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) R
  have h2 :
      (⟨some D, ⟨0, ([1] : List (Fin 2)) ^ (m + 2) +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L), R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{2}
      ⟨some C, ⟨1, ([1] : List (Fin 2)) ^ (m + 2) +> ((0 : Fin 2) >> L),
                 (0 : Fin 2) >> (1 : Fin 2) >> R⟩⟩ := by
    have heq : ([1] : List (Fin 2)) ^ (m + 2) +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) =
        (1 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ (m + 2) +> ((0 : Fin 2) >> L)) := by
      repeat rw [one_pow_comm_cons]
    rw [heq]; run_steps 2
  have hC := C_sweep (m + 2) L ((0 : Fin 2) >> (1 : Fin 2) >> R)
  exact step_stepPlus_trans h1 (stepPlus_trans hD (stepPlus_trans ⟨2, by decide, h2⟩ hC))

/-- Return sweep with 6 ones on the left: consumes `1^6 0` and produces `1^(m+6) 0 1` on the right. -/
lemma return_sweep_6 (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                  (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (m + 6) +> ((0 : Fin 2) >> (1 : Fin 2) >> R)⟩⟩ := by
  have h1 :
      (⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                    (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
                 ([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{1}
      ⟨some D, ⟨1, (1 : Fin 2) >> (1 : Fin 2) >>
                   (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
                 ([1] : List (Fin 2)) ^ (m + 1) +> ((0 : Fin 2) >> R)⟩⟩ := by run_steps 1
  have hD := D_sweep (m + 1) ((1 : Fin 2) >> (1 : Fin 2) >>
                              (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) R
  have h2 :
      (⟨some D, ⟨0, ([1] : List (Fin 2)) ^ (m + 2) +>
                    ((1 : Fin 2) >> (1 : Fin 2) >>
                     (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L), R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{2}
      ⟨some C, ⟨1, ([1] : List (Fin 2)) ^ (m + 5) +> ((0 : Fin 2) >> L),
                 (0 : Fin 2) >> (1 : Fin 2) >> R⟩⟩ := by
    have heq : ([1] : List (Fin 2)) ^ (m + 2) +>
        ((1 : Fin 2) >> (1 : Fin 2) >>
         (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) =
        (1 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ (m + 5) +> ((0 : Fin 2) >> L)) := by
      repeat rw [one_pow_comm_cons]
      rfl
    rw [heq]; run_steps 2
  have hC := C_sweep (m + 5) L ((0 : Fin 2) >> (1 : Fin 2) >> R)
  exact step_stepPlus_trans h1 (stepPlus_trans hD (stepPlus_trans ⟨2, by decide, h2⟩ hC))

/-- 5-step turnaround: consumes `0 1 1 1 0` on the left and prepends `1^2 0 1^2` on the right. -/
lemma turnaround_5step (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ m +> R⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ 2 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (m + 2) +> R))⟩⟩ := by
  have heq : (1 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> R) =
      ([1] : List (Fin 2)) ^ (m + 2) +> R := by
    rw [show m + 2 = 2 + m by omega, list_pow_add, listblank_append_assoc]; rfl
  refine ⟨5, by decide, ?_⟩
  rw [← heq]
  run_steps 5

/-- 9-step turnaround on empty right tape (`default`). -/
lemma turnaround_empty (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L, default⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ :=
  ⟨9, by decide, by run_steps 9⟩

/-- 10-step initial expansion on `[1] +> default`. -/
lemma start_10step (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ :=
  ⟨10, by decide, by run_steps 10⟩

/-- Bounce across `0 0 1^(m+2)` at the right end of the tape (`default`). -/
lemma bounce_right_F (m : Nat) (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
               (0 : Fin 2) >> (0 : Fin 2) >> (([1] : List (Fin 2)) ^ (m + 2) +> default)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ m +>
                 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                  (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
               ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ := by
  have heq : ([1] : List (Fin 2)) ^ (m + 2) +> (default : ListBlank (Fin 2)) =
      (1 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> default) := by
    rw [show m + 2 = 2 + m by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [heq]
  have h9 :
      (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
                 (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                 (([1] : List (Fin 2)) ^ m +> default)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{9}
      ⟨some F, ⟨((([1] : List (Fin 2)) ^ m +> default)).head,
                 (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                 (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L,
                 ((([1] : List (Fin 2)) ^ m +> default)).tail⟩⟩ := by run_steps 9
  have hF := F_sweep m
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) default
  have h4 :
      (⟨some F, ⟨0, ([0] : List (Fin 2)) ^ m +>
                    ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                     (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
                 default⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{4}
      ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ m +>
                    ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                     (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
                 ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ := by run_steps 4
  exact stepPlus_trans (stepPlus_stepStar_trans ⟨9, by decide, h9⟩ hF) ⟨4, by decide, h4⟩

/-- Bounce across `0 0 1^(m+2) 0 1` when another block follows on the right. -/
lemma bounce_right_F_block (m : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
               (0 : Fin 2) >> (0 : Fin 2) >>
               (([1] : List (Fin 2)) ^ (m + 2) +> ((0 : Fin 2) >> (1 : Fin 2) >> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ m +>
                 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                  (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
               (0 : Fin 2) >> R⟩⟩ := by
  have heq : ([1] : List (Fin 2)) ^ (m + 2) +> ((0 : Fin 2) >> (1 : Fin 2) >> R) =
      (1 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R)) := by
    rw [show m + 2 = 2 + m by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [heq]
  have h9 :
      (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
                 (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                 (([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{9}
      ⟨some F, ⟨((([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R))).head,
                 (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                 (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L,
                 ((([1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (1 : Fin 2) >> R))).tail⟩⟩ := by run_steps 9
  have hF := F_sweep m
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) ((0 : Fin 2) >> (1 : Fin 2) >> R)
  simp only [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons] at hF
  have h2 :
      (⟨some F, ⟨0, ([0] : List (Fin 2)) ^ m +>
                    ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                     (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
                 (1 : Fin 2) >> R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢^{2}
      ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ m +>
                    ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                     (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L),
                 (0 : Fin 2) >> R⟩⟩ := by run_steps 2
  exact stepPlus_trans (stepPlus_stepStar_trans ⟨9, by decide, h9⟩ hF) ⟨2, by decide, h2⟩

-- ============================================================================
-- Section 6.2: Higher-Order Recursive & Exponential Counter Lemmas
-- ============================================================================

/-- Exponential $O(2^k)$ Hanoi chain: turns `0^(3k)` on the left and `0 1^k` on the right
    into `1^(3k) 0 1^k` on the right. -/
lemma hanoi_chain (k : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (3 * k) +> L,
               (0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> R)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢*
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (3 * k) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> R))⟩⟩ := by
  induction k generalizing L R with
  | zero => exact stepStar_refl _ _
  | succ k ih =>
    have hL : ([0] : List (Fin 2)) ^ (3 * (k + 1)) +> L =
        ([0] : List (Fin 2)) ^ (3 * k) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L) := by
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, list_pow_add, listblank_append_assoc]; rfl
    have hR : ([1] : List (Fin 2)) ^ (k + 1) +> R =
        ([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> R) := by
      rw [pow_succ_right, listblank_append_assoc]; rfl
    rw [hL, hR]
    have s1 := ih ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L) ((1 : Fin 2) >> R)
    have hR' : (0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> R)) =
        (0 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> R) := by
      rw [← hR, pow_succ_list, List.singleton_append, listblank_append_cons]
    have s2 :
        (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L,
                   ([1] : List (Fin 2)) ^ (3 * k) +>
                   ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> R)))⟩⟩ : Cfg (Fin 2) (Fin 6))
          [target_tm]⊢⁺
        ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (3 * k) +>
                     ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L),
                   (0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> R)⟩⟩ := by
      rw [hR']
      exact forward_sweep (3 * k) ((0 : Fin 2) >> L) (([1] : List (Fin 2)) ^ k +> R)
    have s3 := ih ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) R
    have s4 := return_sweep (3 * k) L (([1] : List (Fin 2)) ^ k +> R)
    have hR'' : (0 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> R) =
        (0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> R)) := hR'.symm
    rw [hR''] at s4
    exact stepPlus_to_stepStar
      (stepStar_stepPlus_trans s1 (stepPlus_trans s2 (stepStar_stepPlus_trans s3 s4)))

/-- Single exponential increment step: `1^(3k) 0 1^(k+1) -> 1^(3k+3) 0 1^(k+1)` consuming `0^3`. -/
lemma hanoi_inc (k : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 3 +> L,
               ([1] : List (Fin 2)) ^ (3 * k) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1) +> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (3 * (k + 1)) +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1) +> R))⟩⟩ := by
  have hR : ([1] : List (Fin 2)) ^ (k + 1) +> R = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> R) := by
    rw [pow_succ_list]; rfl
  rw [hR]
  have s1 := forward_sweep (3 * k) ((0 : Fin 2) >> L) (([1] : List (Fin 2)) ^ k +> R)
  have s2 := hanoi_chain k ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) R
  have s3 := return_sweep (3 * k) L (([1] : List (Fin 2)) ^ k +> R)
  exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 s3)

/-- Iterated exponential increment: `n` rounds of `hanoi_inc`. -/
lemma hanoi_inc_iter (n k d : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (3 * n) +> L,
               ([1] : List (Fin 2)) ^ (3 * k) +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + n + d) +> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢*
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (3 * (k + n)) +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + n + d) +> R))⟩⟩ := by
  induction n generalizing k d L with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, pow_zero_list, listblank_append_nil]
    exact stepStar_refl _ _
  | succ n ih =>
    have hL : ([0] : List (Fin 2)) ^ (3 * (n + 1)) +> L =
        ([0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ (3 * n) +> L) := by
      rw [show 3 * (n + 1) = 3 + 3 * n by omega, list_pow_add, listblank_append_assoc]
    have hR : ([1] : List (Fin 2)) ^ (k + (n + 1) + d) +> R =
        ([1] : List (Fin 2)) ^ (k + 1) +> (([1] : List (Fin 2)) ^ (n + d) +> R) := by
      rw [show k + (n + 1) + d = (k + 1) + (n + d) by omega, list_pow_add, listblank_append_assoc]
    rw [hL, hR]
    have s1 := hanoi_inc k (([0] : List (Fin 2)) ^ (3 * n) +> L) (([1] : List (Fin 2)) ^ (n + d) +> R)
    have hR2 : ([1] : List (Fin 2)) ^ (k + 1) +> (([1] : List (Fin 2)) ^ (n + d) +> R) =
        ([1] : List (Fin 2)) ^ ((k + 1) + n + d) +> R := by
      rw [← hR, show k + (n + 1) + d = (k + 1) + n + d by omega]
    rw [hR2] at s1 ⊢
    have s2 := ih (k + 1) d L
    rw [show (k + 1) + n = k + (n + 1) by omega] at s1 s2 ⊢
    exact stepStar_trans (stepPlus_to_stepStar s1) s2

/-- Rule R2: `1^(3k+2) 0 1^(k+2+d) -> 1^(3k+6) 0 1^(k+1+d)` consuming `0^3`. -/
lemma rule_r2 (k d : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 3 +> L,
               ([1] : List (Fin 2)) ^ (3 * k + 2) +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 2 + d) +> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (3 * (k + 2)) +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1 + d) +> R))⟩⟩ := by
  have hR1 : ([1] : List (Fin 2)) ^ (k + 2 + d) +> R =
      (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R))) := by
    rw [show k + 2 + d = 1 + k + 1 + d by omega]
    repeat rw [list_pow_add]
    repeat rw [listblank_append_assoc]
    rfl
  rw [hR1]
  have s1 := forward_sweep (3 * k + 2) ((0 : Fin 2) >> L)
      (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R)))
  have hL1 : ([0] : List (Fin 2)) ^ (3 * k + 2) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) =
      ([0] : List (Fin 2)) ^ (3 * k) +>
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) := by
    rw [list_pow_add, listblank_append_assoc]; rfl
  rw [hL1] at s1
  have s2 := hanoi_chain k
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)
      ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R))
  have hR2 : (0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R))) =
      (0 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> (([1] : List (Fin 2)) ^ d +> R)) := by
    rw [one_pow_comm_cons]
  have s3 :
      (⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L,
                 ([1] : List (Fin 2)) ^ (3 * k) +>
                 ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R))))⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢⁺
      ⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (3 * k) +>
                   ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                    (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L),
                 (0 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> (([1] : List (Fin 2)) ^ d +> R))⟩⟩ := by
    rw [hR2]
    exact forward_sweep (3 * k)
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)
      (([1] : List (Fin 2)) ^ k +> (([1] : List (Fin 2)) ^ d +> R))
  have s4 := hanoi_chain k
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)
      (([1] : List (Fin 2)) ^ d +> R)
  have s5 := return_sweep_6 (3 * k) L (([1] : List (Fin 2)) ^ k +> (([1] : List (Fin 2)) ^ d +> R))
  have hR3 : (0 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> (([1] : List (Fin 2)) ^ d +> R)) =
      (0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1 + d) +> R) := by
    rw [show k + 1 + d = 1 + k + d by omega, list_pow_add, list_pow_add, listblank_append_assoc, listblank_append_assoc]; rfl
  rw [hR3] at s5
  exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 (stepPlus_trans s3 (stepStar_stepPlus_trans s4 s5)))

/-- Combined R2 + iterated increment: `[3*k + 2, k + 3 + d] -> [3*(k + 2 + d), k + 2 + d]` consuming `0^(3*d + 3)`. -/
lemma stage_from_r2 (k d : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (3 * d + 3) +> L,
               ([1] : List (Fin 2)) ^ (3 * k + 2) +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 3 + d) +> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (3 * (k + 2 + d)) +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 2 + d) +> R))⟩⟩ := by
  have hL : ([0] : List (Fin 2)) ^ (3 * d + 3) +> L =
      ([0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ (3 * d) +> L) := by
    rw [show 3 * d + 3 = 3 + 3 * d by omega, list_pow_add, listblank_append_assoc]
  have hR1 : k + 3 + d = k + 2 + (d + 1) := by omega
  rw [hL, hR1]
  have s1 := rule_r2 k (d + 1) (([0] : List (Fin 2)) ^ (3 * d) +> L) R
  have hR2 : k + 1 + (d + 1) = (k + 2) + d + 0 := by omega
  rw [hR2] at s1
  have s2 := hanoi_inc_iter d (k + 2) 0 L R
  have h_step := stepPlus_stepStar_trans s1 s2
  simpa only [Nat.add_zero] using h_step

/-- Descending overflow staircase configuration. -/
def Stair (d : Nat) (L R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> L,
             ([1] : List (Fin 2)) ^ (3 * d) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R))⟩⟩

/-- Single step of the descending overflow staircase: `Stair (d+1) -> Stair d`. -/
lemma stair_step (d : Nat) (L R : ListBlank (Fin 2)) :
    (Stair (d + 1) L R) [target_tm]⊢⁺ (Stair d (([0, 1, 1, 1] : List (Fin 2)) +> L) R) := by
  unfold Stair
  have hR : ([1] : List (Fin 2)) ^ (d + 1) +> R = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> R) := by
    rw [pow_succ_list]; rfl
  rw [hR]
  have s1 := forward_sweep (3 * (d + 1)) L (([1] : List (Fin 2)) ^ d +> R)
  have hL : ([0] : List (Fin 2)) ^ (3 * (d + 1)) +> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) =
      ([0] : List (Fin 2)) ^ (3 * d) +>
      ((0 : Fin 2) >> (0 : Fin 2) >> (([0, 1, 1, 1] : List (Fin 2)) +> L)) := by
    rw [show 3 * (d + 1) = 3 * d + 3 by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL] at s1
  have s2 := hanoi_chain d ((0 : Fin 2) >> (0 : Fin 2) >> (([0, 1, 1, 1] : List (Fin 2)) +> L)) R
  exact stepPlus_stepStar_trans s1 s2

/-- Iterated descending staircase: `Stair b L R ⊢* Stair 0 ([0, 1, 1, 1]^b +> L) R`. -/
lemma stair_iter (b : Nat) (L R : ListBlank (Fin 2)) :
    (Stair b L R) [target_tm]⊢* (Stair 0 (([0, 1, 1, 1] : List (Fin 2)) ^ b +> L) R) := by
  induction b generalizing L with
  | zero => exact stepStar_refl _ _
  | succ b ih =>
    have s1 := stair_step b L R
    have s2 := ih (([0, 1, 1, 1] : List (Fin 2)) +> L)
    have heq : ([0, 1, 1, 1] : List (Fin 2)) ^ b +> (([0, 1, 1, 1] : List (Fin 2)) +> L) =
        ([0, 1, 1, 1] : List (Fin 2)) ^ (b + 1) +> L := by
      rw [pow_succ_right, listblank_append_assoc]
    rw [heq] at s2
    exact stepStar_trans (stepPlus_to_stepStar s1) s2

/-- Iterated return sweep across `[1, 1, 1, 0]^n` on the left tape. -/
lemma return_sweep_iter (n a b : Nat) (L R : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([1, 1, 1, 0] : List (Fin 2)) ^ n +> L,
               ([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ b +> R))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢*
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (a + 3 * n) +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (b + n) +> R))⟩⟩ := by
  induction n generalizing a b L with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, pow_zero_list, listblank_append_nil]
    exact stepStar_refl _ _
  | succ n ih =>
    have hL : ([1, 1, 1, 0] : List (Fin 2)) ^ (n + 1) +> L =
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (([1, 1, 1, 0] : List (Fin 2)) ^ n +> L) := by
      rw [pow_succ_list]; rfl
    rw [hL]
    have s1 := return_sweep a (([1, 1, 1, 0] : List (Fin 2)) ^ n +> L) (([1] : List (Fin 2)) ^ b +> R)
    have hR : (0 : Fin 2) >> (1 : Fin 2) >> (([1] : List (Fin 2)) ^ b +> R) =
        (0 : Fin 2) >> (([1] : List (Fin 2)) ^ (b + 1) +> R) := by
      rw [pow_succ_list]; rfl
    rw [hR] at s1
    have s2 := ih (a + 3) (b + 1) L
    rw [show a + 3 + 3 * n = a + 3 * (n + 1) by omega,
        show b + 1 + n = b + (n + 1) by omega] at s2
    exact stepStar_trans (stepPlus_to_stepStar s1) s2

-- ============================================================================
-- Section 6.3: Era Hub & Multi-Stage Drain Lemmas
-- ============================================================================

/-- Canonical 3-block Hub configuration: `L <C 0 1^a 0 1^b 0 1^c 0^∞`. -/
def Hub (a b c : Nat) (L : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ a +>
                  ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ b +>
                   ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c +> default))))⟩⟩

/-- Collapse from `[3*(k+1) + 1, k + 1]` to `[2, 3*k + 6, k + 1]` consuming `0^3`. -/
lemma collapse_to_2 (k : Nat) (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 3 +> L,
               ([1] : List (Fin 2)) ^ (3 * (k + 1) + 1) +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1) +> default))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ 2 +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (3 * k + 6) +>
                     ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1) +> default))))⟩⟩ := by
  have hR1 : ([1] : List (Fin 2)) ^ (k + 1) +> (default : ListBlank (Fin 2)) =
      (1 : Fin 2) >> (([1] : List (Fin 2)) ^ k +> default) := by
    rw [pow_succ_list]; rfl
  rw [hR1]
  have s1 := forward_sweep (3 * (k + 1) + 1) ((0 : Fin 2) >> L) (([1] : List (Fin 2)) ^ k +> default)
  have hL1 : ([0] : List (Fin 2)) ^ (3 * (k + 1) + 1) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) =
      ([0] : List (Fin 2)) ^ (3 * k) +>
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) := by
    rw [show 3 * (k + 1) + 1 = 3 * k + 4 by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL1] at s1
  have s2 := hanoi_chain k
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) default
  have s3 := stair_iter k
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) default
  have hStair0 : Stair 0
      (([0, 1, 1, 1] : List (Fin 2)) ^ k +>
       ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)) default =
      ⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                   (([1, 1, 1, 0] : List (Fin 2)) ^ k +>
                    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)),
                default⟩⟩ := by
    unfold Stair
    rw [shift_00111_to_0001110 k ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)]
    simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hStair0] at s3
  have s4 := turnaround_empty
      (([1, 1, 1, 0] : List (Fin 2)) ^ k +>
       ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L))
  have hL2 : (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (([1, 1, 1, 0] : List (Fin 2)) ^ k +>
       ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L)) =
      ([1, 1, 1, 0] : List (Fin 2)) ^ (k + 1) +>
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) := by
    rw [pow_succ_list]; rfl
  have hR2 : ([1] : List (Fin 2)) ^ 1 +> (default : ListBlank (Fin 2)) =
      ([1] : List (Fin 2)) ^ 1 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 0 +> default)) := by
    simp only [pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hL2, hR2] at s4
  have s5 := return_sweep_iter (k + 1) 1 0
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L) default
  rw [show 1 + 3 * (k + 1) = 3 * k + 4 by omega, show 0 + (k + 1) = k + 1 by omega] at s5
  have s6 := turnaround_5step (3 * k + 4) L
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 1) +> default))
  rw [show 3 * k + 4 + 2 = 3 * k + 6 by omega] at s6
  rw [← hR1]
  exact stepPlus_trans s1
    (stepStar_stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4
          (stepStar_stepPlus_trans s5 s6))))

/-- Final stage of a drain: from `[3*m, m]` (for `m >= 1`) with `0^15` on the left to `Hub 12 (3*m + 5) (m + 1)`. -/
lemma stage_final (m : Nat) (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 15 +> L,
               ([1] : List (Fin 2)) ^ (3 * m) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> default))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    (Hub 12 (3 * m + 5) (m + 1) L) := by
  have hL1 : ([0] : List (Fin 2)) ^ 15 +> L =
      (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 12 +> L)) := by
    rw [show (15 : Nat) = 3 + 12 by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL1]
  have s1 := stair_iter m ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 12 +> L)) default
  have hStair0 : Stair 0 (([0, 1, 1, 1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 12 +> L))) default =
      ⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                   (([1, 1, 1, 0] : List (Fin 2)) ^ m +> (([0] : List (Fin 2)) ^ 12 +> L)),
                default⟩⟩ := by
    unfold Stair
    rw [shift_00111_to_0001110 m (([0] : List (Fin 2)) ^ 12 +> L)]
    simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hStair0] at s1
  have s2 := turnaround_empty (([1, 1, 1, 0] : List (Fin 2)) ^ m +> (([0] : List (Fin 2)) ^ 12 +> L))
  have hL2 : (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (([1, 1, 1, 0] : List (Fin 2)) ^ m +> (([0] : List (Fin 2)) ^ 12 +> L)) =
      ([1, 1, 1, 0] : List (Fin 2)) ^ (m + 1) +> (([0] : List (Fin 2)) ^ 12 +> L) := by
    rw [pow_succ_list]; rfl
  have hR2 : ([1] : List (Fin 2)) ^ 1 +> (default : ListBlank (Fin 2)) =
      ([1] : List (Fin 2)) ^ 1 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 0 +> default)) := by
    simp only [pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hL2, hR2] at s2
  have s3 := return_sweep_iter (m + 1) 1 0 (([0] : List (Fin 2)) ^ 12 +> L) default
  rw [show 1 + 3 * (m + 1) = 3 * (m + 1) + 1 by omega, show 0 + (m + 1) = m + 1 by omega] at s3
  have hL3 : ([0] : List (Fin 2)) ^ 12 +> L =
      ([0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ 9 +> L) := by
    rw [show (12 : Nat) = 3 + 9 by omega, list_pow_add, listblank_append_assoc]
  have s4 := collapse_to_2 m (([0] : List (Fin 2)) ^ 9 +> L)
  rw [← hL3] at s4
  have hL4' : ([0] : List (Fin 2)) ^ 9 +> L =
      ([0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ (3 * 2) +> L) := by
    rw [show (9 : Nat) = 3 + 6 by omega, list_pow_add, listblank_append_assoc]
  have hR4' : 3 * m + 6 = 0 + 2 + (3 * m + 4) := by omega
  rw [hL4', hR4'] at s4
  have s5a := rule_r2 0 (3 * m + 4) (([0] : List (Fin 2)) ^ (3 * 2) +> L)
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (m + 1) +> default))
  have hR5 : 0 + 1 + (3 * m + 4) = 2 + 2 + (3 * m + 1) := by omega
  rw [hR5] at s5a
  have s5b := hanoi_inc_iter 2 2 (3 * m + 1) L
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (m + 1) +> default))
  have hR6 : 2 + 2 + (3 * m + 1) = 3 * m + 5 := by omega
  rw [hR6] at s5a s5b
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4
          (stepPlus_stepStar_trans s5a s5b))))

/-- 19-step bounce on `0 0 1^3`: from `Stair 0 L (0 >> 1^3)` to `[2, 3]` with `1 1 1 >> L`. -/
lemma bounce_3 (L : ListBlank (Fin 2)) :
    (Stair 0 L ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default)))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ 2 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))⟩⟩ := by
  unfold Stair
  simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil]
  have s1 := bounce_right_F 1 L
  have s2 := turnaround_5step 1 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) default
  exact stepPlus_trans s1 s2

/-- Stage from `Hub (3*m) m 3` (consuming `0^21`) to `Hub 12 (3*m + 14) (m + 4)`. -/
lemma stage_from_3 (m : Nat) (L : ListBlank (Fin 2)) :
    (Hub (3 * m) m 3 (([0] : List (Fin 2)) ^ 21 +> L))
      [target_tm]⊢⁺
    (Hub 12 (3 * m + 14) (m + 4) L) := by
  unfold Hub
  have hL1 : ([0] : List (Fin 2)) ^ 21 +> L =
      (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 18 +> L)) := by
    rw [show (21 : Nat) = 3 + 18 by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL1]
  have s1 := stair_iter m ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 18 +> L))
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))
  have s2 := bounce_3 (([0, 1, 1, 1] : List (Fin 2)) ^ m +> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 18 +> L)))
  rw [shift_0111_to_1110 m (([0] : List (Fin 2)) ^ 18 +> L)] at s2
  have s3 := return_sweep_iter (m + 1) 2 3 (([0] : List (Fin 2)) ^ 18 +> L) default
  rw [show 2 + 3 * (m + 1) = 3 * (m + 1) + 2 by omega,
      show 3 + (m + 1) = (m + 1) + 2 + 1 by omega] at s3
  have hL2 : ([0] : List (Fin 2)) ^ 18 +> L =
      ([0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ 15 +> L) := by
    rw [show (18 : Nat) = 3 + 15 by omega, list_pow_add, listblank_append_assoc]
  have s4 := rule_r2 (m + 1) 1 (([0] : List (Fin 2)) ^ 15 +> L) default
  rw [← hL2, show (m + 1) + 1 + 1 = m + 3 by omega, show (m + 1) + 2 = m + 3 by omega] at s4
  have s5 := stage_final (m + 3) L
  unfold Hub at s5
  rw [show 3 * (m + 3) + 5 = 3 * m + 14 by omega, show m + 3 + 1 = m + 4 by omega] at s5
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4 s5)))

/-- Stage from `[3*k + 2, k + 12, 3]` (consuming `0^51`) to `Hub 12 (3*k + 47) (k + 15)`. -/
lemma stage_from_2_m_3 (k : Nat) (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 51 +> L,
               ([1] : List (Fin 2)) ^ (3 * k + 2) +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + 12) +>
                ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    (Hub 12 (3 * k + 47) (k + 15) L) := by
  have hL1 : ([0] : List (Fin 2)) ^ 51 +> L =
      ([0] : List (Fin 2)) ^ (3 * 9 + 3) +> (([0] : List (Fin 2)) ^ 21 +> L) := by
    rw [show (51 : Nat) = (3 * 9 + 3) + 21 by omega, list_pow_add, listblank_append_assoc]
  have hR1 : k + 12 = k + 3 + 9 := by omega
  rw [hL1, hR1]
  have s1 := stage_from_r2 k 9 (([0] : List (Fin 2)) ^ 21 +> L)
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))
  rw [show k + 2 + 9 = k + 11 by omega] at s1
  have s2 := stage_from_3 (k + 11) L
  unfold Hub at s2 ⊢
  rw [show 3 * (k + 11) + 14 = 3 * k + 47 by omega, show k + 11 + 4 = k + 15 by omega] at s2
  exact stepPlus_trans s1 s2

/-- 308-step macro-transition from `Start(0^12 +> L)` to `[2, 12, 3]`. -/
lemma start_12_to_2_12_3 (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 12 +> L, ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ 2 +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
                     ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))⟩⟩ := by
  have hL1 : ([0] : List (Fin 2)) ^ 12 +> L =
      (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ 9 +> L) := by
    rw [show (12 : Nat) = 3 + 9 by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL1]
  have s1 := start_10step (([0] : List (Fin 2)) ^ 9 +> L)
  have s2 := turnaround_5step 1 (([0] : List (Fin 2)) ^ 9 +> L) default
  have hL2 : ([0] : List (Fin 2)) ^ 9 +> L =
      ([0] : List (Fin 2)) ^ 3 +>
      ((0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 3 +> L))) := by
    rw [show (9 : Nat) = 3 + (3 + 3) by omega, list_pow_add, list_pow_add,
        listblank_append_assoc, listblank_append_assoc]; rfl
  rw [hL2] at s2
  have s3 := rule_r2 0 1
      ((0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 3 +> L))) default
  have s4 := stair_iter 2 ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 3 +> L)) default
  have hStair0 : Stair 0 (([0, 1, 1, 1] : List (Fin 2)) ^ 2 +> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 3 +> L))) default =
      ⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                   (([1, 1, 1, 0] : List (Fin 2)) ^ 2 +> (([0] : List (Fin 2)) ^ 3 +> L)),
                default⟩⟩ := by
    unfold Stair
    rw [shift_00111_to_0001110 2 (([0] : List (Fin 2)) ^ 3 +> L)]
    simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hStair0] at s4
  have s5 := turnaround_empty (([1, 1, 1, 0] : List (Fin 2)) ^ 2 +> (([0] : List (Fin 2)) ^ 3 +> L))
  have hL3 : (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (([1, 1, 1, 0] : List (Fin 2)) ^ 2 +> (([0] : List (Fin 2)) ^ 3 +> L)) =
      ([1, 1, 1, 0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ 3 +> L) := rfl
  have hR3 : ([1] : List (Fin 2)) ^ 1 +> (default : ListBlank (Fin 2)) =
      ([1] : List (Fin 2)) ^ 1 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 0 +> default)) := by
    simp only [pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hL3, hR3] at s5
  have s6 := return_sweep_iter 3 1 0 (([0] : List (Fin 2)) ^ 3 +> L) default
  have s7 := collapse_to_2 2 L
  exact stepPlus_trans s1
    (stepPlus_trans s2
      (stepPlus_trans s3
        (stepStar_stepPlus_trans s4
          (stepPlus_trans s5
            (stepStar_stepPlus_trans s6 s7)))))

/-- Base Era 0 reachability: `Start(0^63 +> L) ⊢⁺ Hub 12 47 15 L`. -/
lemma era_reach_0 (L : ListBlank (Fin 2)) :
    (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ 63 +> L, ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    (Hub 12 47 15 L) := by
  have hL : ([0] : List (Fin 2)) ^ 63 +> L =
      ([0] : List (Fin 2)) ^ 12 +> (([0] : List (Fin 2)) ^ 51 +> L) := by
    rw [show (63 : Nat) = 12 + 51 by omega, list_pow_add, listblank_append_assoc]
  rw [hL]
  exact stepPlus_trans (start_12_to_2_12_3 (([0] : List (Fin 2)) ^ 51 +> L)) (stage_from_2_m_3 0 L)

/-- 175-step bounce across `0 0 1^12 0 1^3`: from `Stair 0 L (0 >> 1^12 0 1^3)` to `[2, 12, 3]` with `1 1 1 >> L`. -/
lemma bounce_12_3 (L : ListBlank (Fin 2)) :
    (Stair 0 L ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default)))))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ 2 +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
                ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))⟩⟩ := by
  unfold Stair
  simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil]
  have s1 := bounce_right_F_block 10 L (([1] : List (Fin 2)) ^ 2 +> default)
  have hL1 : ([0] : List (Fin 2)) ^ 10 +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) =
      ([0] : List (Fin 2)) ^ (3 * 2) +>
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) := rfl
  rw [hL1] at s1
  have s2 := hanoi_chain 2
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) default
  have s3 := stair_iter 2
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) default
  have hStair0 : Stair 0
      (([0, 1, 1, 1] : List (Fin 2)) ^ 2 +>
       ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)) default =
      ⟨some C, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                   (([1, 1, 1, 0] : List (Fin 2)) ^ 2 +>
                    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                     (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)),
                default⟩⟩ := by
    unfold Stair
    rw [shift_00111_to_0001110 2
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)]
    simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hStair0] at s3
  have s4 := turnaround_empty
      (([1, 1, 1, 0] : List (Fin 2)) ^ 2 +>
       ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L))
  have hL2 : (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (([1, 1, 1, 0] : List (Fin 2)) ^ 2 +>
       ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)) =
      ([1, 1, 1, 0] : List (Fin 2)) ^ 3 +>
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) := rfl
  have hR2 : ([1] : List (Fin 2)) ^ 1 +> (default : ListBlank (Fin 2)) =
      ([1] : List (Fin 2)) ^ 1 +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 0 +> default)) := by
    simp only [pow_zero_list, listblank_append_nil, zero_cons_default]
  rw [hL2, hR2] at s4
  have s5 := return_sweep_iter 3 1 0
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) default
  have s6 := turnaround_5step 10 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))
  exact stepPlus_trans s1
    (stepStar_stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4
          (stepStar_stepPlus_trans s5 s6))))

/-- 339-step bounce across `0 0 1^15`: from `Stair 0 L (0 >> 1^15)` to `[2, 4, 12, 3]` with `1 1 1 >> L`. -/
lemma bounce_15 (L : ListBlank (Fin 2)) :
    (Stair 0 L ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 15 +> default)))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L,
               ([1] : List (Fin 2)) ^ 2 +>
               ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 4 +>
                ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
                 ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))))⟩⟩ := by
  unfold Stair
  simp only [Nat.mul_zero, pow_zero_list, listblank_append_nil]
  have s1 := bounce_right_F 13 L
  have hL1 : ([0] : List (Fin 2)) ^ 13 +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) =
      ([0] : List (Fin 2)) ^ 12 +>
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L) := rfl
  rw [hL1] at s1
  have s2 := start_12_to_2_12_3
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
       (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)
  have s3 := turnaround_5step 2 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> L)
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
       ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))
  exact stepPlus_trans s1 (stepPlus_trans s2 s3)

/-- First 12-zero stage of Era 0 drain (`c_0 = 15`):
    `Hub (3*b) b 15 (0^12 +> L) ⊢⁺ [3*(b+5) + 2, (b+5) + 12, 3]`. -/
lemma drain_0_first_12 (b : Nat) (L : ListBlank (Fin 2)) :
    (Hub (3 * b) b 15 (([0] : List (Fin 2)) ^ 12 +> L))
      [target_tm]⊢⁺
    ⟨some C, ⟨0, L, ([1] : List (Fin 2)) ^ (3 * (b + 5) + 2) +>
                    ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ ((b + 5) + 12) +>
                     ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))⟩⟩ := by
  unfold Hub
  have hL1 : ([0] : List (Fin 2)) ^ 12 +> L =
      (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 9 +> L)) := by
    rw [show (12 : Nat) = 3 + 9 by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL1]
  have s1 := stair_iter b ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 9 +> L))
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 15 +> default))
  have s2 := bounce_15 (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ 9 +> L)))
  rw [shift_0111_to_1110 b (([0] : List (Fin 2)) ^ 9 +> L)] at s2
  have s3 := return_sweep_iter (b + 1) 2 4 (([0] : List (Fin 2)) ^ 9 +> L)
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
       ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))
  rw [show 2 + 3 * (b + 1) = 3 * (b + 1) + 2 by omega,
      show 4 + (b + 1) = (b + 1) + 3 + 1 by omega] at s3
  have hL2 : ([0] : List (Fin 2)) ^ 9 +> L =
      ([0] : List (Fin 2)) ^ (3 * 1 + 3) +>
      ((0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> L)) := by
    rw [show (9 : Nat) = 6 + 3 by omega, list_pow_add, listblank_append_assoc]; rfl
  have s4 := stage_from_r2 (b + 1) 1
      ((0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> L))
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
       ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))
  rw [← hL2, show (b + 1) + 2 + 1 = b + 4 by omega] at s4
  have s5 := stair_iter (b + 4) ((0 : Fin 2) >> L)
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 12 +>
       ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))))
  have s6 := bounce_12_3
      (([0, 1, 1, 1] : List (Fin 2)) ^ (b + 4) +> ((0 : Fin 2) >> L))
  rw [shift_0111_to_1110 (b + 4) L] at s6
  have s7 := return_sweep_iter (b + 5) 2 12 L
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ 3 +> default))
  rw [show 2 + 3 * (b + 5) = 3 * (b + 5) + 2 by omega,
      show 12 + (b + 5) = (b + 5) + 12 by omega] at s7
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4
          (stepStar_stepPlus_trans s5
            (stepPlus_stepStar_trans s6 s7)))))

lemma stepPlus_Hub_congr {c : Cfg (Fin 2) (Fin 6)} {a b₁ b₂ c₁ c₂ : Nat} {L : ListBlank (Fin 2)}
    (h : c [target_tm]⊢⁺ (Hub a b₁ c₁ L)) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    c [target_tm]⊢⁺ (Hub a b₂ c₂ L) := by
  subst hb hc; exact h

lemma Hub_stepPlus_congr {c : Cfg (Fin 2) (Fin 6)} {a b c_m : Nat} {L₁ L₂ : ListBlank (Fin 2)}
    (h : (Hub a b c_m L₁) [target_tm]⊢⁺ c) (hL : L₂ = L₁) :
    (Hub a b c_m L₂) [target_tm]⊢⁺ c := by
  subst hL; exact h

/-- Base Era 0 drain (`c_0 = 15`): `Hub (3*b) b 15 (0^63 +> L) ⊢⁺ Hub 12 (3*b + 62) (b + 20) L`. -/
lemma drain_0 (b : Nat) (L : ListBlank (Fin 2)) :
    (Hub (3 * b) b 15 (([0] : List (Fin 2)) ^ 63 +> L))
      [target_tm]⊢⁺
    (Hub 12 (3 * b + 62) (b + 20) L) := by
  refine Hub_stepPlus_congr (stepPlus_trans
    (drain_0_first_12 b (([0] : List (Fin 2)) ^ 51 +> L))
    (stepPlus_Hub_congr (stage_from_2_m_3 (b + 5) L) (by omega) (by omega))) ?_
  exact append_pow_split ([0] : List (Fin 2)) 12 51 L

-- ============================================================================
-- Section 6.4: Era Parameter Sequences & Inductive Closure Across All Eras
-- ============================================================================

mutual
def S_seq : Nat → Nat
  | 0 => 0
  | m + 1 => S_seq m + b_seq m + 1

def b_seq : Nat → Nat
  | 0 => 47
  | m + 1 => 3 * (b_seq m + S_seq m) + 62

def c_seq : Nat → Nat
  | 0 => 15
  | m + 1 => b_seq m + S_seq m + 20
end

def a_seq : Nat → Nat
  | 0 => 4
  | 1 => 8
  | m + 2 => 2 * a_seq (m + 1) + 2

def W_seq : Nat → Nat
  | 0 => 63
  | m + 1 => W_seq m + 3 * (b_seq m - a_seq m - 1)

def E_seq : Nat → Nat
  | 0 => 63
  | m + 1 => E_seq m + 3 * (b_seq m - a_seq m) + W_seq m + 3 * (a_seq (m + 1) - 4)

lemma era_params_spec (m : Nat) :
    b_seq m = 3 * c_seq m + 2 ∧
    (m = 0 ∨ S_seq m + 19 = c_seq m) ∧
    (m = 0 ∨ W_seq m + 3 * a_seq m = 3 * c_seq m + 12) ∧
    E_seq m + 4 = c_seq (m + 1) ∧
    b_seq m ≥ a_seq m + 2 ∧
    a_seq m ≥ 4 := by
  induction m with
  | zero =>
    decide
  | succ m ih =>
    rcases m with _ | m'
    · decide
    · have hS : S_seq (m' + 1 + 1) = S_seq (m' + 1) + b_seq (m' + 1) + 1 := rfl
      have hb : b_seq (m' + 1 + 1) = 3 * (b_seq (m' + 1) + S_seq (m' + 1)) + 62 := rfl
      have hc : c_seq (m' + 1 + 1) = b_seq (m' + 1) + S_seq (m' + 1) + 20 := rfl
      have hc3 : c_seq (m' + 1 + 1 + 1) = b_seq (m' + 1 + 1) + S_seq (m' + 1 + 1) + 20 := rfl
      have ha : a_seq (m' + 1 + 1) = 2 * a_seq (m' + 1) + 2 := rfl
      have hW : W_seq (m' + 1 + 1) = W_seq (m' + 1) + 3 * (b_seq (m' + 1) - a_seq (m' + 1) - 1) := rfl
      have hE : E_seq (m' + 1 + 1) = E_seq (m' + 1) + 3 * (b_seq (m' + 1) - a_seq (m' + 1)) +
          W_seq (m' + 1) + 3 * (a_seq (m' + 1 + 1) - 4) := rfl
      omega

/-- Mid-era hub transition: from `Hub (3*a) b_m c_m (0 >> 0 >> ([1, 1, 1, 0]^(b+2) +> L))`
    to `Hub (3*(b + a + 3)) (b + b_m + 1) c_m L`. -/
lemma hub_absorb_1110 (a b b_m c_m : Nat) (hb : b_m ≥ a + 1) (L : ListBlank (Fin 2)) :
    (Hub (3 * a) b_m c_m
      ((0 : Fin 2) >> (0 : Fin 2) >> (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> L)))
      [target_tm]⊢⁺
    (Hub (3 * (b + a + 3)) (b + b_m + 1) c_m L) := by
  unfold Hub
  have hR1 : ([1] : List (Fin 2)) ^ b_m +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default)) =
      (1 : Fin 2) >>
      (([1] : List (Fin 2)) ^ a +>
       (([1] : List (Fin 2)) ^ (b_m - a - 1) +>
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default)))) := by
    have h1 : (1 : Fin 2) >>
        (([1] : List (Fin 2)) ^ a +>
         (([1] : List (Fin 2)) ^ (b_m - a - 1) +>
          ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default)))) =
        ([1] : List (Fin 2)) ^ (1 + a + (b_m - a - 1)) +>
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default)) := by
      repeat rw [list_pow_add]
      repeat rw [listblank_append_assoc]
      rfl
    rw [h1, show 1 + a + (b_m - a - 1) = b_m by omega]
  rw [hR1]
  have s1 := forward_sweep (3 * a) (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> L)
      (([1] : List (Fin 2)) ^ a +>
       (([1] : List (Fin 2)) ^ (b_m - a - 1) +>
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default))))
  have s2 := hanoi_chain a
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> L))
      (([1] : List (Fin 2)) ^ (b_m - a - 1) +>
       ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default)))
  have hL2 : (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> L) =
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 1) +> L) := by
    rw [show b + 2 = 1 + (b + 1) by omega, list_pow_add, listblank_append_assoc]; rfl
  rw [hL2] at s2
  have s3 := return_sweep_6 (3 * a) (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 1) +> L)
      (([1] : List (Fin 2)) ^ a +>
       (([1] : List (Fin 2)) ^ (b_m - a - 1) +>
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default))))
  have hR3 : (0 : Fin 2) >> (1 : Fin 2) >>
      (([1] : List (Fin 2)) ^ a +>
       (([1] : List (Fin 2)) ^ (b_m - a - 1) +>
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default)))) =
      (0 : Fin 2) >> (([1] : List (Fin 2)) ^ b_m +>
       ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default))) := by
    rw [hR1]
  rw [hR3] at s3
  have s4 := return_sweep_iter (b + 1) (3 * a + 6) b_m L
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ c_m +> default))
  rw [show 3 * a + 6 + 3 * (b + 1) = 3 * (b + a + 3) by omega,
      show b_m + (b + 1) = b + b_m + 1 by omega] at s4
  exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 (stepPlus_stepStar_trans s3 s4))

/-- Simultaneous induction proving `EraReach m` and `Drain m` for all eras `m >= 0`. -/
theorem era_and_drain (m : Nat) :
    (∀ L : ListBlank (Fin 2),
      (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (E_seq m) +> L,
                 ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢⁺
      (Hub (3 * a_seq m) (b_seq m) (c_seq m) L)) ∧
    (∀ b : Nat, ∀ L : ListBlank (Fin 2),
      (Hub (3 * b) b (c_seq m) (([0] : List (Fin 2)) ^ (W_seq m) +> L))
        [target_tm]⊢⁺
      (Hub 12 (3 * (b + S_seq m) + 62) (b + S_seq m + 20) L)) := by
  induction m with
  | zero =>
    refine ⟨era_reach_0, ?_⟩
    intro b L
    simpa [S_seq, c_seq, W_seq] using drain_0 b L
  | succ m ih =>
    rcases ih with ⟨ih_era, ih_drain⟩
    have hspec_m := era_params_spec m
    have hspec_m1 := era_params_spec (m + 1)
    have h_era_succ : ∀ L : ListBlank (Fin 2),
        (⟨some C, ⟨0, ([0] : List (Fin 2)) ^ (E_seq (m + 1)) +> L,
                   ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ : Cfg (Fin 2) (Fin 6))
          [target_tm]⊢⁺
        (Hub (3 * a_seq (m + 1)) (b_seq (m + 1)) (c_seq (m + 1)) L) := by
      intro L
      have hL1 : ([0] : List (Fin 2)) ^ (E_seq (m + 1)) +> L =
          ([0] : List (Fin 2)) ^ (E_seq m) +>
          (([0] : List (Fin 2)) ^ (3 * (b_seq m - a_seq m)) +>
           (([0] : List (Fin 2)) ^ (W_seq m) +>
            (([0] : List (Fin 2)) ^ (3 * (a_seq (m + 1) - 4)) +> L))) := by
        have hE : E_seq (m + 1) = E_seq m + (3 * (b_seq m - a_seq m) +
            (W_seq m + 3 * (a_seq (m + 1) - 4))) := by
          have : E_seq (m + 1) = E_seq m + 3 * (b_seq m - a_seq m) + W_seq m + 3 * (a_seq (m + 1) - 4) := rfl
          omega
        rw [hE]
        repeat rw [list_pow_add]
        repeat rw [listblank_append_assoc]
      rw [hL1]
      have s1 := ih_era
          (([0] : List (Fin 2)) ^ (3 * (b_seq m - a_seq m)) +>
           (([0] : List (Fin 2)) ^ (W_seq m) +>
            (([0] : List (Fin 2)) ^ (3 * (a_seq (m + 1) - 4)) +> L)))
      have s2 := hanoi_inc_iter (b_seq m - a_seq m) (a_seq m) 0
          (([0] : List (Fin 2)) ^ (W_seq m) +>
           (([0] : List (Fin 2)) ^ (3 * (a_seq (m + 1) - 4)) +> L))
          ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c_seq m) +> default))
      have hb_eq : a_seq m + (b_seq m - a_seq m) + 0 = b_seq m := by omega
      have hb_eq' : a_seq m + (b_seq m - a_seq m) = b_seq m := by omega
      rw [hb_eq, hb_eq'] at s2
      have s3 := ih_drain (b_seq m)
          (([0] : List (Fin 2)) ^ (3 * (a_seq (m + 1) - 4)) +> L)
      have hb1_def : 3 * (b_seq m + S_seq m) + 62 = b_seq (m + 1) := rfl
      have hc1_def : b_seq m + S_seq m + 20 = c_seq (m + 1) := rfl
      rw [hb1_def, hc1_def] at s3
      have s4 := hanoi_inc_iter (a_seq (m + 1) - 4) 4 (b_seq (m + 1) - a_seq (m + 1)) L
          ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c_seq (m + 1)) +> default))
      have ha_eq : 4 + (a_seq (m + 1) - 4) + (b_seq (m + 1) - a_seq (m + 1)) = b_seq (m + 1) := by omega
      have ha_eq' : 4 + (a_seq (m + 1) - 4) = a_seq (m + 1) := by omega
      rw [ha_eq, ha_eq'] at s4
      exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 (stepPlus_stepStar_trans s3 s4))
    refine ⟨h_era_succ, ?_⟩
    intro b L
    have hL1 : ([0] : List (Fin 2)) ^ (W_seq (m + 1)) +> L =
        (0 : Fin 2) >> (0 : Fin 2) >>
        ((0 : Fin 2) >>
         (([0] : List (Fin 2)) ^ (3 * (b_seq m - a_seq m - 2)) +>
          (([0] : List (Fin 2)) ^ (W_seq m) +> L))) := by
      have hW : W_seq (m + 1) = 3 + (3 * (b_seq m - a_seq m - 2) + W_seq m) := by
        have : W_seq (m + 1) = W_seq m + 3 * (b_seq m - a_seq m - 1) := rfl
        omega
      rw [hW]
      repeat rw [list_pow_add]
      repeat rw [listblank_append_assoc]
      rfl
    unfold Hub
    rw [hL1]
    set L_rem := ([0] : List (Fin 2)) ^ (3 * (b_seq m - a_seq m - 2)) +>
                 (([0] : List (Fin 2)) ^ (W_seq m) +> L)
    have s1 := stair_iter b ((0 : Fin 2) >> L_rem)
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c_seq (m + 1)) +> default))
    have hc_eq : c_seq (m + 1) = (E_seq m + 2) + 2 := by omega
    have s2 := bounce_right_F (E_seq m + 2) (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> L_rem))
    rw [← hc_eq] at s2
    have hL2 : ([0] : List (Fin 2)) ^ (E_seq m + 2) +>
        ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
         (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
         (([0, 1, 1, 1] : List (Fin 2)) ^ b +> ((0 : Fin 2) >> L_rem))) =
        ([0] : List (Fin 2)) ^ (E_seq m) +>
        ((0 : Fin 2) >> (0 : Fin 2) >> (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> L_rem)) := by
      rw [shift_1110_111_0111 b L_rem, list_pow_add, listblank_append_assoc]; rfl
    rw [hL2] at s2
    have s3 := ih_era
        ((0 : Fin 2) >> (0 : Fin 2) >> (([1, 1, 1, 0] : List (Fin 2)) ^ (b + 2) +> L_rem))
    have s4 := hub_absorb_1110 (a_seq m) b (b_seq m) (c_seq m) (by omega) L_rem
    have s5 := hanoi_inc_iter (b_seq m - a_seq m - 2) (b + a_seq m + 3) 0
        (([0] : List (Fin 2)) ^ (W_seq m) +> L)
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c_seq m) +> default))
    have hb_sum : (b + a_seq m + 3) + (b_seq m - a_seq m - 2) + 0 = b + b_seq m + 1 := by omega
    have hb_sum' : (b + a_seq m + 3) + (b_seq m - a_seq m - 2) = b + b_seq m + 1 := by omega
    rw [hb_sum, hb_sum'] at s5
    have s6 := ih_drain (b + b_seq m + 1) L
    have hS_eq : b + b_seq m + 1 + S_seq m = b + S_seq (m + 1) := by
      have : S_seq (m + 1) = S_seq m + b_seq m + 1 := rfl
      omega
    rw [hS_eq] at s6
    exact stepStar_stepPlus_trans s1
      (stepPlus_trans s2
        (stepPlus_trans s3
          (stepPlus_trans s4
            (stepStar_stepPlus_trans s5 s6))))

-- ============================================================================
-- Section 6.5: Blank-Tape Reachability & Unconditional Non-Halting Theorem
-- ============================================================================

/-- `init []` reaches `Hub 12 (b_seq 0) (c_seq 0) default` in positive steps. -/
theorem init_reaches_hub_0 :
    (init []) [target_tm]⊢* (Hub 12 (b_seq 0) (c_seq 0) default) := by
  have h3 : (init []) [target_tm]⊢^{3}
      ⟨some C, ⟨0, default, ([1] : List (Fin 2)) ^ 1 +> default⟩⟩ := by
    run_steps 3
  have h_era0 := era_reach_0 default
  rw [zeros_append_default 63] at h_era0
  exact stepStar_trans ⟨3, h3⟩ (stepPlus_to_stepStar h_era0)

/-- Every era hub transitions in `1` or more steps to the next era hub:
    `Hub 12 (b_seq m) (c_seq m) default ⊢⁺ Hub 12 (b_seq (m+1)) (c_seq (m+1)) default`. -/
theorem hub_step (m : Nat) :
    (Hub 12 (b_seq m) (c_seq m) default)
      [target_tm]⊢⁺
    (Hub 12 (b_seq (m + 1)) (c_seq (m + 1)) default) := by
  have hspec := era_params_spec m
  have s1 := hanoi_inc_iter (b_seq m - 4) 4 0 default
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c_seq m) +> default))
  rw [zeros_append_default (3 * (b_seq m - 4)),
      show 4 + (b_seq m - 4) + 0 = b_seq m by omega,
      show 4 + (b_seq m - 4) = b_seq m by omega] at s1
  have s2 := (era_and_drain m).2 (b_seq m) default
  rw [zeros_append_default (W_seq m)] at s2
  exact stepStar_stepPlus_trans s1 s2

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : Nat}
    (h : multiStep target_tm c k = none) (d : Nat) :
    multiStep target_tm c (k + d) = none := by
  rw [multiStep_add, h]; rfl

/-- For every `m : Nat`, `init []` runs for at least `m` steps and reaches `Hub 12 (b_seq m) (c_seq m) default`. -/
theorem reach_arbitrarily_long :
    ∀ m : Nat, ∃ N : Nat, m ≤ N ∧
      multiStep target_tm (init []) N = some (Hub 12 (b_seq m) (c_seq m) default)
  | 0 => by
    rcases init_reaches_hub_0 with ⟨N₀, hN₀⟩
    exact ⟨N₀, Nat.zero_le N₀, hN₀⟩
  | m + 1 => by
    rcases reach_arbitrarily_long m with ⟨N, h_le, hN⟩
    rcases hub_step m with ⟨k, hk_pos, hk⟩
    exact ⟨N + k, by omega, multiStep_trans target_tm _ _ _ N k hN hk⟩


end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨k, hk⟩
  cases h_step : step target_tm cfg with
  | some cfg' => rfl
  | none =>
    have h_none : multiStep target_tm (init []) (k + 1) = none := by
      rw [multiStep_succ, hk]; exact h_step
    rcases reach_arbitrarily_long (k + 1) with ⟨N, h_ge, hN⟩
    have h_split : N = (k + 1) + (N - (k + 1)) := by omega
    have h_none_N : multiStep target_tm (init []) N = none := by
      rw [h_split]
      exact multiStep_none_add h_none (N - (k + 1))
    rw [h_none_N] at hN
    nomatch hN

end BusyBeaver.M_1RB0LC_0LC1RE_1LD1LC_1LA1RD_HHH1RF_0RA0RF
