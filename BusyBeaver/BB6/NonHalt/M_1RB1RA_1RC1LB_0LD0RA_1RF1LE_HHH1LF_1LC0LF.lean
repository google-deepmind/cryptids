/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic
import BusyBeaver.Excursion

/-!
# Busy Beaver Machine `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`, `BusyBeaver.Excursion`
and defines `target_tm` for `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Excursion

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace M240

def tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

def qA : Fin 6 := 0
def qB : Fin 6 := 1
def qC : Fin 6 := 2
def qD : Fin 6 := 3
def qE : Fin 6 := 4
def qF : Fin 6 := 5

abbrev T := ListBlank (Fin 2)

def K (q : Fin 6) (L : T) (h : Fin 2) (R : T) : Cfg (Fin 2) (Fin 6) := ⟨some q, ⟨h, L, R⟩⟩

@[simp] lemma ms_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl
@[simp] lemma ms_one (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 1 = step M c := rfl
@[simp] lemma ms_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = Option.bind (multiStep M c n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma ms_add (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, ms_succ, ih, Option.bind_assoc]
    simp_rw [ms_succ]

lemma ms_trans (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) : c₁ [M]⊢^{n+m} c₃ := by
  rw [ms_add, h₁]; simp [h₂]

lemma ss_refl (M : Machine Γ Λ) (c : Cfg Γ Λ) : c [M]⊢* c := ⟨0, rfl⟩
lemma step_to_sp {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [M]⊢ c₂) : c₁ [M]⊢⁺ c₂ :=
  ⟨1, Nat.succ_pos 0, h⟩
lemma stepN_to_ss {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : ℕ} (h : c₁ [M]⊢^{n} c₂) :
    c₁ [M]⊢* c₂ := ⟨n, h⟩
lemma stepN_to_sp {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : ℕ} (hn : 0 < n)
    (h : c₁ [M]⊢^{n} c₂) : c₁ [M]⊢⁺ c₂ := ⟨n, hn, h⟩
lemma sp_to_ss {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [M]⊢⁺ c₂) : c₁ [M]⊢* c₂ := by
  rcases h with ⟨n, _, hn⟩; exact ⟨n, hn⟩
lemma ss_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢* c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, ms_trans M c₁ c₂ c₃ n m hn hm⟩
lemma sp_ss_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn_pos, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, Nat.add_pos_left hn_pos m, ms_trans M c₁ c₂ c₃ n m hn hm⟩
lemma ss_sp_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm_pos, hm⟩
  exact ⟨n + m, Nat.add_pos_right n hm_pos, ms_trans M c₁ c₂ c₃ n m hn hm⟩
lemma sp_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ :=
  sp_ss_trans h₁ (sp_to_ss h₂)
lemma step_sp_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ :=
  sp_trans (step_to_sp h₁) h₂
lemma ms_step {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : ℕ}
    (h₁ : c₁ [M]⊢ c₂) (h₂ : c₂ [M]⊢^{n} c₃) : c₁ [M]⊢^{n + 1} c₃ := by
  have := ms_trans M c₁ c₂ c₃ 1 n h₁ h₂
  rwa [Nat.add_comm 1 n] at this

omit [Inhabited Γ] in
@[simp] lemma p_zero_list (l : List Γ) : l ^ (0 : ℕ) = [] := rfl
omit [Inhabited Γ] in
lemma p_succ_list (l : List Γ) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := rfl
omit [Inhabited Γ] in
@[simp] theorem l_pow_add (l : List Γ) (n m : ℕ) : l ^ (n + m) = l ^ n ++ l ^ m := by
  induction n with
  | zero => simp [p_zero_list]
  | succ n ih => rw [Nat.succ_add, p_succ_list, p_succ_list, ih, List.append_assoc]
omit [Inhabited Γ] in
lemma p_succ_right (l : List Γ) (n : ℕ) : l ^ (n + 1) = l ^ n ++ l := by
  rw [l_pow_add]; simp [p_succ_list, p_zero_list]

@[simp] lemma lb_append_nil (s : ListBlank Γ) : ([] : List Γ) +> s = s := rfl
@[simp] lemma lb_append_cons (a : Γ) (l : List Γ) (s : ListBlank Γ) : (a :: l) +> s = a >> (l +> s) := rfl
@[simp] lemma lb_append_assoc (l₁ l₂ : List Γ) (s : ListBlank Γ) : (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) :=
  Turing.ListBlank.append_assoc l₁ l₂ s
@[simp] lemma def_head : (default : T).head = 0 := rfl
@[simp] lemma def_tail : (default : T).tail = default := rfl
@[simp] lemma z_cons_def : (0 : Fin 2) >> (default : T) = default := by
  change ListBlank.cons default default = default
  exact ListBlank.cons_head_tail default
@[simp] lemma m_init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = K qA default 0 default := rfl

lemma pow1_succ (x : Fin 2) (n : ℕ) (s : T) : ([x] : List (Fin 2)) ^ (n + 1) +> s = x >> (([x] : List (Fin 2)) ^ n +> s) := rfl
lemma pow1_succ' (x : Fin 2) (n : ℕ) (s : T) : ([x] : List (Fin 2)) ^ (n + 1) +> s = ([x] : List (Fin 2)) ^ n +> (x >> s) := by
  rw [p_succ_right, lb_append_assoc]; rfl
lemma pow1_add (x : Fin 2) (a b : ℕ) (s : T) : ([x] : List (Fin 2)) ^ (a + b) +> s = ([x] : List (Fin 2)) ^ a +> (([x] : List (Fin 2)) ^ b +> s) := by
  rw [l_pow_add, lb_append_assoc]
lemma pow_blk_succ (u : List (Fin 2)) (n : ℕ) (s : T) : u ^ (n + 1) +> s = u +> (u ^ n +> s) := by
  rw [p_succ_list, lb_append_assoc]
lemma pow_blk_succ' (u : List (Fin 2)) (n : ℕ) (s : T) : u ^ (n + 1) +> s = u ^ n +> (u +> s) := by
  rw [p_succ_right, lb_append_assoc]
lemma pow_blk_add (u : List (Fin 2)) (a b : ℕ) (s : T) : u ^ (a + b) +> s = u ^ a +> (u ^ b +> s) := by
  rw [l_pow_add, lb_append_assoc]
@[simp] lemma zeros_default (n : ℕ) : ([0] : List (Fin 2)) ^ n +> (default : T) = default := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow1_succ, ih, z_cons_def]

local macro "step1" : tactic => `(tactic| (
  try simp only [K, m_init_nil, p_succ_list, p_zero_list, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one,
    List.singleton_append, List.nil_append, List.cons_append,
    lb_append_cons, lb_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    z_cons_def, def_head, def_tail]
  refine ms_step (by rfl) ?_
  simp only [Turing.Tape.move, Tape.write,
    lb_append_cons, lb_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    z_cons_def, def_head, def_tail]))

local macro "run_steps" n:num : tactic => `(tactic| (
  iterate $n step1
  simp only [K, p_succ_list, p_zero_list, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one,
    List.singleton_append, List.nil_append, List.cons_append,
    lb_append_cons, lb_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    z_cons_def, def_head, def_tail, ms_zero]
  rfl))

-- ---------------------------------------------------------------------------
-- Elementary runs & bounce lemmas
-- ---------------------------------------------------------------------------

lemma a1_run (k : ℕ) (L R : T) :
    (K qA L 1 (([1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> R))) [tm]⊢⁺ K qA (([0] : List (Fin 2)) ^ (k + 1) +> L) 0 R := by
  induction k generalizing L with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ k ih =>
    have h1 : (K qA L 1 (([1] : List (Fin 2)) ^ (k + 1) +> ((0 : Fin 2) >> R))) [tm]⊢^{1}
        K qA ((0 : Fin 2) >> L) 1 (([1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> R)) := by run_steps 1
    refine step_sp_trans h1 ?_
    have h2 := ih ((0 : Fin 2) >> L)
    rwa [← pow1_succ'] at h2

lemma d1_run (k : ℕ) (L R : T) (s : Fin 2) :
    (K qD (([1] : List (Fin 2)) ^ k +> (s >> L)) 1 R) [tm]⊢⁺ K qD L s (([1] : List (Fin 2)) ^ (k + 1) +> R) := by
  induction k generalizing R with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ k ih =>
    have h1 : (K qD (([1] : List (Fin 2)) ^ (k + 1) +> (s >> L)) 1 R) [tm]⊢^{1}
        K qD (([1] : List (Fin 2)) ^ k +> (s >> L)) 1 ((1 : Fin 2) >> R) := by run_steps 1
    refine step_sp_trans h1 ?_
    have h2 := ih ((1 : Fin 2) >> R)
    rwa [← pow1_succ'] at h2

lemma e1_run (k : ℕ) (L R : T) :
    (K qE L 1 (([1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> R))) [tm]⊢⁺ K qE (([1] : List (Fin 2)) ^ (k + 1) +> L) 0 R := by
  induction k generalizing L with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ k ih =>
    have h1 : (K qE L 1 (([1] : List (Fin 2)) ^ (k + 1) +> ((0 : Fin 2) >> R))) [tm]⊢^{1}
        K qE ((1 : Fin 2) >> L) 1 (([1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> R)) := by run_steps 1
    refine step_sp_trans h1 ?_
    have h2 := ih ((1 : Fin 2) >> L)
    rwa [← pow1_succ'] at h2

lemma b1_walk (a : ℕ) (s : Fin 2) (L R : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> (s >> L)) 1 R) [tm]⊢⁺ K qD L s (([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> R)) := by
  cases a with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ a =>
    have h1 : (K qB (([1] : List (Fin 2)) ^ (a + 1) +> (s >> L)) 1 R) [tm]⊢^{1}
        K qD (([1] : List (Fin 2)) ^ a +> (s >> L)) 1 ((0 : Fin 2) >> R) := by run_steps 1
    exact step_sp_trans h1 (d1_run a L ((0 : Fin 2) >> R) s)

lemma b1_zero_one (a : ℕ) (Rest R : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> (1 : Fin 2) >> Rest)) 1 R) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (a + 1) +> Rest) 1 ((1 : Fin 2) >> R) := by
  refine sp_trans (b1_walk a 0 ((1 : Fin 2) >> Rest) R) ?_
  have h1 : (K qD ((1 : Fin 2) >> Rest) 0 (([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> R))) [tm]⊢^{1}
      K qE Rest 1 (([1] : List (Fin 2)) ^ (a + 1) +> ((0 : Fin 2) >> R)) := by run_steps 1
  refine step_sp_trans h1 ?_
  refine sp_ss_trans (e1_run (a + 1) Rest R) ?_
  refine stepN_to_ss (n := 1) ?_
  rw [pow1_succ (1 : Fin 2) (a + 1)]
  run_steps 1

lemma b1_two_zeros_one (a : ℕ) (Rest R : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Rest)) 1 R) [tm]⊢⁺
      K qB Rest 1 (([1] : List (Fin 2)) ^ (a + 2) +> ((0 : Fin 2) >> R)) := by
  refine sp_ss_trans (b1_walk a 0 ((0 : Fin 2) >> (1 : Fin 2) >> Rest) R) ?_
  refine stepN_to_ss (n := 2) ?_
  rw [pow1_succ, pow1_succ]
  run_steps 2

lemma b1_three_zeros (a : ℕ) (Rest R : T) :
    (K qB (([1] : List (Fin 2)) ^ (a + 1) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> Rest)) 1 R) [tm]⊢⁺
      K qA (([0] : List (Fin 2)) ^ (a + 1) +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> Rest)) 0 R := by
  refine sp_trans (b1_walk (a + 1) 0 ((0 : Fin 2) >> (0 : Fin 2) >> Rest) R) ?_
  have h1 : (K qD ((0 : Fin 2) >> (0 : Fin 2) >> Rest) 0 (([1] : List (Fin 2)) ^ (a + 1) +> ((0 : Fin 2) >> R))) [tm]⊢^{5}
      K qA ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> Rest) 1 (([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> R)) := by
    rw [pow1_succ]; run_steps 5
  exact ss_sp_trans (stepN_to_ss h1) (a1_run a _ R)

lemma a0_zero_R (c : ℕ) (L R : T) :
    (K qA L 0 ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c + 3) +> ((0 : Fin 2) >> R)))) [tm]⊢⁺
      K qA (([0] : List (Fin 2)) ^ (c + 1) +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> L)) 0 R := by
  have h1 : (K qA L 0 ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c + 3) +> ((0 : Fin 2) >> R)))) [tm]⊢^{4}
      K qA ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> L) 1 (([1] : List (Fin 2)) ^ c +> ((0 : Fin 2) >> R)) := by
    rw [pow1_succ, pow1_succ, pow1_succ]; run_steps 4
  exact ss_sp_trans (stepN_to_ss h1) (a1_run c _ R)

lemma a0_step (L R : T) : (K qA L 0 ((1 : Fin 2) >> R)) [tm]⊢^{1} K qB ((1 : Fin 2) >> L) 1 R := by
  run_steps 1

def EBounce (j : ℕ) (s : Fin 2) (L' R' : T) : Cfg (Fin 2) (Fin 6) :=
  K qE L' s (([1] : List (Fin 2)) ^ (2 * j + 2) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R')))

lemma ebounce_to_B1 (j : ℕ) (L' R' : T) :
    (EBounce j 1 L' R') [tm]⊢⁺ K qB (([1] : List (Fin 2)) ^ (2 * j + 2) +> L') 1 (([1] : List (Fin 2)) ^ (j + 1) +> R') := by
  unfold EBounce
  refine sp_ss_trans (e1_run (2 * j + 2) L' _) ?_
  refine stepN_to_ss (n := 1) ?_
  rw [pow1_succ (1 : Fin 2) (2 * j + 2), pow1_succ (1 : Fin 2) j]
  run_steps 1

lemma ebounce_one (j : ℕ) (s : Fin 2) (L' R' : T) :
    (EBounce j 1 ((1 : Fin 2) >> (0 : Fin 2) >> s >> L') R') [tm]⊢⁺ EBounce (j + 1) s L' R' := by
  refine sp_trans (ebounce_to_B1 j _ R') ?_
  rw [← pow1_succ']
  refine sp_ss_trans (b1_walk (2 * j + 3) 0 (s >> L') _) ?_
  refine stepN_to_ss (n := 1) ?_
  unfold EBounce
  have e1 : 2 * (j + 1) + 2 = (2 * j + 3) + 1 := by ring
  rw [e1, pow1_succ (1 : Fin 2) (2 * j + 3)]
  run_steps 1

lemma ebounce_zero (j : ℕ) (L₀ R' : T) :
    (EBounce j 0 ((0 : Fin 2) >> L₀) R') [tm]⊢⁺
      K qA (([0] : List (Fin 2)) ^ (2 * j + 1) +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L₀)) 0 (([1] : List (Fin 2)) ^ j +> R') := by
  unfold EBounce
  have h1 : (K qE ((0 : Fin 2) >> L₀) 0 (([1] : List (Fin 2)) ^ (2 * j + 2) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R')))) [tm]⊢^{4}
      K qA ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L₀) 1 (([1] : List (Fin 2)) ^ (2 * j) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R'))) := by
    rw [pow1_succ (1 : Fin 2) (2 * j + 1), pow1_succ (1 : Fin 2) (2 * j)]; run_steps 4
  exact ss_sp_trans (stepN_to_ss h1) (a1_run (2 * j) _ _)

lemma e0_to_B1 (j : ℕ) (L' R' : T) :
    (EBounce j 0 ((1 : Fin 2) >> L') R') [tm]⊢^{1} K qB L' 1 (([1] : List (Fin 2)) ^ (2 * j + 3) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R'))) := by
  unfold EBounce
  rw [pow1_succ (1 : Fin 2) (2 * j + 2)]
  run_steps 1

lemma a0_odd_zeros (j : ℕ) : ∀ (s : Fin 2) (L' R' : T),
    (K qA (([0] : List (Fin 2)) ^ (2 * j + 1) +> (s >> L')) 0 (([1] : List (Fin 2)) ^ (j + 1) +> R')) [tm]⊢⁺
      EBounce j s L' R' := by
  induction j with
  | zero =>
    intro s L' R'
    exact ⟨4, by decide, by unfold EBounce; run_steps 4⟩
  | succ j ih =>
    intro s L' R'
    have e1 : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
    rw [e1, pow1_succ' (0 : Fin 2) (2 * j + 1 + 1), pow1_succ' (0 : Fin 2) (2 * j + 1),
      pow1_succ' (1 : Fin 2) (j + 1)]
    refine sp_trans (ih 0 ((0 : Fin 2) >> s >> L') ((1 : Fin 2) >> R')) ?_
    refine sp_trans (ebounce_zero j (s >> L') ((1 : Fin 2) >> R')) ?_
    rw [← pow1_succ' (1 : Fin 2) j]
    refine sp_trans (ih 1 ((1 : Fin 2) >> (0 : Fin 2) >> s >> L') R') ?_
    exact ebounce_one j s L' R'

lemma a0_cascade (k : ℕ) : ∀ (Lrem R' : T),
    (K qA (([0] : List (Fin 2)) ^ (2 * k + 1) +> ((1 : Fin 2) >> (1 : Fin 2) >> Lrem)) 0 (([1] : List (Fin 2)) ^ k +> R')) [tm]⊢*
      K qA (([0, 1, 1] : List (Fin 2)) ^ (k + 1) +> Lrem) 0 R' := by
  induction k with
  | zero => intro Lrem R'; exact ss_refl _ _
  | succ k ih =>
    intro Lrem R'
    have e1 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
    rw [e1, pow1_succ' (0 : Fin 2) (2 * k + 1 + 1), pow1_succ' (0 : Fin 2) (2 * k + 1)]
    refine ss_trans (sp_to_ss (a0_odd_zeros k 0 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lrem) R')) ?_
    refine ss_trans (sp_to_ss (ebounce_zero k ((1 : Fin 2) >> (1 : Fin 2) >> Lrem) R')) ?_
    have h := ih ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lrem) R'
    rw [pow_blk_succ' ([0, 1, 1] : List (Fin 2)) (k + 1)]
    exact h

lemma b1_zero_one_run (w : ℕ) : ∀ (a m : ℕ) (Rest R' : T),
    (K qB (([1] : List (Fin 2)) ^ (a + 1) +> (([0, 1, 1] : List (Fin 2)) ^ w +> Rest)) 1 (([1] : List (Fin 2)) ^ m +> R')) [tm]⊢*
      K qB (([1] : List (Fin 2)) ^ (a + 2 * w + 1) +> Rest) 1 (([1] : List (Fin 2)) ^ (m + w) +> R') := by
  induction w with
  | zero => intro a m Rest R'; exact ss_refl _ _
  | succ w ih =>
    intro a m Rest R'
    rw [pow_blk_succ ([0, 1, 1] : List (Fin 2)) w]
    simp only [lb_append_cons, lb_append_nil]
    refine ss_trans (sp_to_ss (b1_zero_one (a + 1) _ _)) ?_
    rw [← pow1_succ' (1 : Fin 2) (a + 1 + 1), ← pow1_succ (1 : Fin 2) m]
    have h := ih (a + 2) (m + 1) Rest R'
    have e1 : a + 2 + 2 * w + 1 = a + 2 * (w + 1) + 1 := by ring
    have e2 : m + 1 + w = m + (w + 1) := by ring
    have e0 : a + 2 + 1 = a + 1 + 1 + 1 := rfl
    rw [e0, e1, e2] at h
    exact h

lemma m_round (j : ℕ) (L R : T) :
    (K qB (([1] : List (Fin 2)) ^ (2 * j + 1) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L)) 1 (([1] : List (Fin 2)) ^ (j + 1) +> R)) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (2 * j + 3) +> ((0 : Fin 2) >> L)) 1 (([1] : List (Fin 2)) ^ (j + 1) +> R) := by
  refine sp_trans (b1_three_zeros (2 * j) L _) ?_
  refine sp_trans (a0_odd_zeros j 1 ((1 : Fin 2) >> (0 : Fin 2) >> L) R) ?_
  have h := ebounce_to_B1 j ((1 : Fin 2) >> (0 : Fin 2) >> L) R
  rw [← pow1_succ' (1 : Fin 2) (2 * j + 2)] at h
  exact h

lemma m_rounds (n : ℕ) : ∀ (j : ℕ) (L R : T),
    (K qB (([1] : List (Fin 2)) ^ (2 * j + 1) +> (([0] : List (Fin 2)) ^ (2 * n + 2) +> L)) 1 (([1] : List (Fin 2)) ^ (j + n) +> R)) [tm]⊢*
      K qB (([1] : List (Fin 2)) ^ (2 * j + 2 * n + 1) +> ((0 : Fin 2) >> (0 : Fin 2) >> L)) 1 (([1] : List (Fin 2)) ^ (j + n) +> R) := by
  induction n with
  | zero => intro j L R; exact ss_refl _ _
  | succ n ih =>
    intro j L R
    have e1 : 2 * (n + 1) + 2 = (2 * n + 1) + 1 + 1 + 1 := by ring
    rw [e1, pow1_succ (0 : Fin 2), pow1_succ (0 : Fin 2), pow1_succ (0 : Fin 2)]
    have e2 : j + (n + 1) = (j + 1) + n := by ring
    rw [e2, pow1_add (1 : Fin 2) (j + 1) n]
    refine ss_trans (sp_to_ss (m_round j _ _)) ?_
    have h := ih (j + 1) L R
    have e3 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
    have e4 : 2 * (j + 1) + 2 * n + 1 = 2 * j + 2 * (n + 1) + 1 := by ring
    have e5 : 2 * n + 2 = (2 * n + 1) + 1 := rfl
    rw [e3, e4, e5, pow1_succ (0 : Fin 2) (2 * n + 1), pow1_add (1 : Fin 2) (j + 1) n] at h
    exact h

lemma fixed89 (Lrem : T) :
    (K qA (([0, 1, 1] : List (Fin 2)) ^ 5 +> Lrem) 0 default) [tm]⊢^{89}
      K qB (([1] : List (Fin 2)) ^ 12 +> Lrem) 1 (([1] : List (Fin 2)) ^ 5 +> default) := by
  run_steps 89

lemma fixed23 (Rest : T) :
    (K qA ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> Rest) 0 default) [tm]⊢^{23}
      K qB ((1 : Fin 2) >> (0 : Fin 2) >> Rest) 1 (([1] : List (Fin 2)) ^ 4 +> default) := by
  run_steps 23

-- ---------------------------------------------------------------------------
-- Two-stack configuration family & 17 macro rules
-- ---------------------------------------------------------------------------

def encL : List (ℕ × ℕ) → T
  | [] => default
  | (z, w) :: l => ([0] : List (Fin 2)) ^ (z + 1) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l))

def encS : List ℕ → T
  | [] => default
  | b :: s => (0 : Fin 2) >> (([1] : List (Fin 2)) ^ b +> encS s)

@[simp] lemma encL_nil : encL [] = default := rfl
@[simp] lemma encL_cons (z w : ℕ) (l : List (ℕ × ℕ)) : encL ((z, w) :: l) = ([0] : List (Fin 2)) ^ (z + 1) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l)) := rfl
@[simp] lemma encS_nil : encS [] = default := rfl
@[simp] lemma encS_cons (b : ℕ) (s : List ℕ) : encS (b :: s) = (0 : Fin 2) >> (([1] : List (Fin 2)) ^ b +> encS s) := rfl

def Beq (m : ℕ) (l : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  K qB (([1] : List (Fin 2)) ^ (2 * m + 2) +> encL l) 1 (([1] : List (Fin 2)) ^ m +> default)
def Bev (j : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qB (([1] : List (Fin 2)) ^ (2 * j + 1) +> encL l) 1 (([1] : List (Fin 2)) ^ m +> encS s)
def Bodd (k : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qB (([1] : List (Fin 2)) ^ (2 * k + 10) +> encL l) 1 (([1] : List (Fin 2)) ^ m +> encS s)
def Amega (z w : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qA (encL ((z, w) :: l)) 0 (([1] : List (Fin 2)) ^ m +> encS s)
def Bounce (w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qA (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l) 0 (encS s)

lemma default3 : (default : T) = (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default := by simp
lemma zeros3 (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 3) +> X = (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ n +> X) := rfl
lemma zeros3' (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 3) +> X = ([0] : List (Fin 2)) ^ n +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> X) := by
  rw [pow1_add]; rfl
lemma zeros2 (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 2) +> X = (0 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ n +> X) := rfl
lemma zeros1 (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 1) +> X = (0 : Fin 2) >> (([0] : List (Fin 2)) ^ n +> X) := rfl
lemma ones1 (n : ℕ) (X : T) : ([1] : List (Fin 2)) ^ (n + 1) +> X = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ n +> X) := rfl
lemma ones1' (n : ℕ) (X : T) : ([1] : List (Fin 2)) ^ (n + 1) +> X = ([1] : List (Fin 2)) ^ n +> ((1 : Fin 2) >> X) := pow1_succ' 1 n X
lemma ones_one (X : T) : ([1] : List (Fin 2)) ^ 1 +> X = (1 : Fin 2) >> X := rfl
lemma ones_add (a b : ℕ) (X : T) : ([1] : List (Fin 2)) ^ (a + b) +> X = ([1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +> X) := pow1_add 1 a b X
lemma blk_add (a b : ℕ) (X : T) : ([0, 1, 1] : List (Fin 2)) ^ (a + b) +> X = ([0, 1, 1] : List (Fin 2)) ^ a +> (([0, 1, 1] : List (Fin 2)) ^ b +> X) := pow_blk_add _ a b X

theorem R4 (j r z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev j ((z + 2, w) :: l') (j + 1 + r) s) [tm]⊢⁺ Bev (j + 1) ((z, w) :: l') (j + 1 + r) s := by
  unfold Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, ones_add (j + 1) r]
  have h := m_round j (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l')))
    (([1] : List (Fin 2)) ^ r +> encS s)
  have e : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [e]; exact h

theorem R4nil (j r : ℕ) (s : List ℕ) :
    (Bev j [] (j + 1 + r) s) [tm]⊢⁺ Bev (j + 1) [] (j + 1 + r) s := by
  unfold Bev
  rw [encL_nil, default3, ones_add (j + 1) r]
  have h := m_round j default (([1] : List (Fin 2)) ^ r +> encS s)
  have e : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [e]
  simp only [z_cons_def] at h ⊢
  exact h

theorem R5 (m z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev (m + 4) ((z + 2, w) :: l') (m + 4) s) [tm]⊢⁺ Bounce m ((z, w) :: l') s := by
  unfold Bev Bounce
  rw [encL_cons, encL_cons, zeros3, zeros1]
  refine sp_ss_trans (b1_three_zeros (2 * (m + 4)) _ _) ?_
  have h := a0_cascade (m + 4) ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (encS s)
  have e : m + 4 + 1 = m + 5 := by ring
  rw [e] at h; exact h

theorem R5nil (m : ℕ) (s : List ℕ) :
    (Bev (m + 4) [] (m + 4) s) [tm]⊢⁺ Bounce m [] s := by
  unfold Bev Bounce
  rw [encL_nil, default3]
  refine sp_ss_trans (b1_three_zeros (2 * (m + 4)) _ _) ?_
  have h := a0_cascade (m + 4) ((0 : Fin 2) >> default) (encS s)
  have e : m + 4 + 1 = m + 5 := by ring
  rw [e] at h
  simp only [z_cons_def] at h ⊢
  exact h

lemma pop_frame0 (a m w : ℕ) (l' : List (ℕ × ℕ)) (R' : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> encL ((0, w) :: l')) 1 (([1] : List (Fin 2)) ^ m +> R')) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (a + 2 * w + 13) +> encL l') 1 (([1] : List (Fin 2)) ^ (m + w + 7) +> R') := by
  rw [encL_cons, zeros1, p_zero_list, lb_append_nil]
  refine sp_trans (b1_zero_one a _ _) ?_
  rw [← ones1' (a + 1)]
  refine sp_ss_trans (b1_zero_one (a + 2) _ _) ?_
  rw [← ones1 m, ← ones1 (m + 1)]
  have h := b1_zero_one_run (w + 5) (a + 2) (m + 2) (encL l') R'
  have e1 : a + 2 + 2 * (w + 5) + 1 = a + 2 * w + 13 := by ring
  have e2 : m + 2 + (w + 5) = m + w + 7 := by ring
  have e3 : m + 2 = m + 1 + 1 := rfl
  rw [e1, e2, e3] at h
  exact h

lemma pop_frame1 (a m w : ℕ) (l' : List (ℕ × ℕ)) (R' : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> encL ((1, w) :: l')) 1 (([1] : List (Fin 2)) ^ m +> R')) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (2 * w + 12) +> encL l') 1 (([1] : List (Fin 2)) ^ (a + w + 8) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> R'))) := by
  rw [encL_cons, zeros2, p_zero_list, lb_append_nil]
  refine sp_trans (b1_two_zeros_one a _ _) ?_
  have h1 := b1_zero_one 1 (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l') (([1] : List (Fin 2)) ^ (a + 2) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> R')))
  rw [pow1_succ (1 : Fin 2) 0, p_zero_list, lb_append_nil] at h1
  refine sp_ss_trans h1 ?_
  rw [← ones1 (a + 2)]
  have h := b1_zero_one_run (w + 5) 1 (a + 2 + 1) (encL l') ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> R'))
  have e1 : 1 + 2 * (w + 5) + 1 = 2 * w + 12 := by ring
  have e2 : a + 2 + 1 + (w + 5) = a + w + 8 := by ring
  rw [e1, e2] at h
  exact h

theorem R2 (m w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq m ((0, w) :: l')) [tm]⊢⁺ Bev (m + w + 7) l' (m + w + 7) [] := by
  unfold Beq Bev
  have h := pop_frame0 (2 * m + 2) m w l' default
  have e : 2 * m + 2 + 2 * w + 13 = 2 * (m + w + 7) + 1 := by ring
  rw [e] at h; rw [encS_nil]; exact h

theorem R3 (m w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq m ((1, w) :: l')) [tm]⊢⁺ Bodd (w + 1) l' (2 * m + w + 10) [m] := by
  unfold Beq Bodd
  have h := pop_frame1 (2 * m + 2) m w l' default
  have e1 : 2 * m + 2 + w + 8 = 2 * m + w + 10 := by ring
  have e2 : 2 * w + 12 = 2 * (w + 1) + 10 := by ring
  rw [e1, e2] at h; rw [encS_cons, encS_nil]; exact h

theorem R6 (j m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev j ((0, w) :: l') m s) [tm]⊢⁺ Bodd (j + w + 2) l' (m + w + 7) s := by
  unfold Bev Bodd
  have h := pop_frame0 (2 * j + 1) m w l' (encS s)
  have e : 2 * j + 1 + 2 * w + 13 = 2 * (j + w + 2) + 10 := by ring
  rw [e] at h; exact h

theorem R7 (j m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev j ((1, w) :: l') m s) [tm]⊢⁺ Bodd (w + 1) l' (2 * j + w + 9) (m :: s) := by
  unfold Bev Bodd
  have h := pop_frame1 (2 * j + 1) m w l' (encS s)
  have e1 : 2 * j + 1 + w + 8 = 2 * j + w + 9 := by ring
  have e2 : 2 * w + 12 = 2 * (w + 1) + 10 := by ring
  rw [e1, e2] at h; rw [encS_cons]; exact h

theorem R8a (k m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bodd k ((0, w) :: l') m s) [tm]⊢⁺ Bev (k + w + 11) l' (m + w + 7) s := by
  unfold Bodd Bev
  have h := pop_frame0 (2 * k + 10) m w l' (encS s)
  have e : 2 * k + 10 + 2 * w + 13 = 2 * (k + w + 11) + 1 := by ring
  rw [e] at h; exact h

theorem R8b (k m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bodd k ((1, w) :: l') m s) [tm]⊢⁺ Bodd (w + 1) l' (2 * k + w + 18) (m :: s) := by
  unfold Bodd
  have h := pop_frame1 (2 * k + 10) m w l' (encS s)
  have e1 : 2 * k + 10 + w + 8 = 2 * k + w + 18 := by ring
  have e2 : 2 * w + 12 = 2 * (w + 1) + 10 := by ring
  rw [e1, e2] at h; rw [encS_cons]; exact h

theorem R8 (k r z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bodd k ((z + 2, w) :: l') (k + 5 + r) s) [tm]⊢⁺ Bev 0 ((z, w) :: l') (2 * k + 11) ((k + 4 + r) :: s) := by
  unfold Bodd Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_cons]
  have e0 : 2 * k + 10 = (2 * k + 9) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * k + 9) _ _) ?_
  rw [show k + 5 + r = (k + 4 + r) + 1 by ring, ones1 (k + 4 + r)]
  refine ss_sp_trans (stepN_to_ss (a0_step _ _)) ?_
  have e1 : 2 * k + 9 + 1 = 2 * (k + 4) + 2 := by ring
  rw [e1]
  have hr := m_rounds (k + 4) 0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l'))))
    (([1] : List (Fin 2)) ^ r +> encS s)
  rw [← ones_add (0 + (k + 4)) r] at hr
  simp only [Nat.zero_add, Nat.mul_zero, ones_one] at hr
  refine ss_sp_trans hr ?_
  have h := b1_two_zeros_one (2 * (k + 4) + 1) ((1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (([1] : List (Fin 2)) ^ (k + 4 + r) +> encS s)
  have e2 : 2 * (k + 4) + 1 + 2 = 2 * k + 11 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one]
  exact h

theorem R8nil (k r : ℕ) (s : List ℕ) :
    (Bodd k [] (k + 5 + r) s) [tm]⊢⁺ Bev 0 [] (2 * k + 11) ((k + 4 + r) :: s) := by
  unfold Bodd Bev
  rw [encL_nil, default3, encS_cons]
  have e0 : 2 * k + 10 = (2 * k + 9) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * k + 9) _ _) ?_
  rw [show k + 5 + r = (k + 4 + r) + 1 by ring, ones1 (k + 4 + r)]
  refine ss_sp_trans (stepN_to_ss (a0_step _ _)) ?_
  have e1 : 2 * k + 9 + 1 = 2 * (k + 4) + 2 := by ring
  rw [e1]
  have hr := m_rounds (k + 4) 0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) (([1] : List (Fin 2)) ^ r +> encS s)
  rw [← ones_add (0 + (k + 4)) r] at hr
  simp only [Nat.zero_add, Nat.mul_zero, ones_one] at hr
  refine ss_sp_trans hr ?_
  have h := b1_two_zeros_one (2 * (k + 4) + 1) ((1 : Fin 2) >> (0 : Fin 2) >> default) (([1] : List (Fin 2)) ^ (k + 4 + r) +> encS s)
  have e2 : 2 * (k + 4) + 1 + 2 = 2 * k + 11 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one, z_cons_def] at h ⊢
  exact h

theorem R1 (m z w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq (m + 5) ((z + 2, w) :: l')) [tm]⊢⁺ Bev 0 ((z, w) :: l') (2 * (m + 5) + 4) [m + 5] := by
  unfold Beq Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_cons, encS_nil]
  have e0 : 2 * (m + 5) + 2 = (2 * m + 11) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * m + 11) _ _) ?_
  have e1 : 2 * m + 11 + 1 = (2 * (m + 4) + 1) + 3 := by ring
  rw [e1, zeros3']
  rw [show m + 5 = (m + 4) + 1 by ring]
  set Y : T := (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l'))) with hY
  refine sp_trans (a0_odd_zeros (m + 4) 0 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine sp_trans (ebounce_zero (m + 4) ((0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (a0_cascade (m + 4) ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  rw [show m + 4 + 1 = 5 + m by ring, blk_add 5 m]
  refine ss_sp_trans (stepN_to_ss (fixed89 _)) ?_
  have hrun := b1_zero_one_run m 11 5 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default
  refine ss_sp_trans hrun ?_
  rw [hY]
  have h := b1_two_zeros_one (11 + 2 * m + 1) ((1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (([1] : List (Fin 2)) ^ (5 + m) +> default)
  have e2 : 11 + 2 * m + 1 + 2 = 2 * (5 + m) + 4 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one]
  exact h

theorem R1nil (m : ℕ) :
    (Beq (m + 5) []) [tm]⊢⁺ Bev 0 [] (2 * (m + 5) + 4) [m + 5] := by
  unfold Beq Bev
  rw [encL_nil, encS_cons, encS_nil]
  rw [show (([1] : List (Fin 2)) ^ (2 * (m + 5) + 2) +> (default : T)) = ([1] : List (Fin 2)) ^ (2 * (m + 5) + 2) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default) by simp]
  have e0 : 2 * (m + 5) + 2 = (2 * m + 11) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * m + 11) _ _) ?_
  have e1 : 2 * m + 11 + 1 = (2 * (m + 4) + 1) + 3 := by ring
  rw [e1, zeros3']
  rw [show m + 5 = (m + 4) + 1 by ring]
  set Y : T := (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default with hY
  refine sp_trans (a0_odd_zeros (m + 4) 0 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine sp_trans (ebounce_zero (m + 4) ((0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (a0_cascade (m + 4) ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  rw [show m + 4 + 1 = 5 + m by ring, blk_add 5 m]
  refine ss_sp_trans (stepN_to_ss (fixed89 _)) ?_
  have hrun := b1_zero_one_run m 11 5 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default
  refine ss_sp_trans hrun ?_
  rw [hY]
  have h := b1_two_zeros_one (11 + 2 * m + 1) ((1 : Fin 2) >> (0 : Fin 2) >> default) (([1] : List (Fin 2)) ^ (5 + m) +> default)
  have e2 : 11 + 2 * m + 1 + 2 = 2 * (5 + m) + 4 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one, z_cons_def] at h ⊢
  exact h

theorem R9 (m z' w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) :
    (Amega (2 * (m + 5) + z') w l (m + 5) s) [tm]⊢⁺ Bounce m ((z', w) :: l) s := by
  unfold Amega Bounce
  rw [encL_cons, encL_cons]
  have e1 : 2 * (m + 5) + z' + 1 = (2 * (m + 4) + 1) + (z' + 2) := by ring
  rw [e1, pow1_add (0 : Fin 2) _ (z' + 2), zeros2 z', zeros1 z']
  rw [show m + 5 = (m + 4) + 1 by ring]
  set Z : T := ([0] : List (Fin 2)) ^ z' +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l)) with hZ
  refine sp_trans (a0_odd_zeros (m + 4) 0 ((0 : Fin 2) >> Z) (encS s)) ?_
  refine sp_ss_trans (ebounce_zero (m + 4) Z (encS s)) ?_
  exact a0_cascade (m + 4) ((0 : Fin 2) >> Z) (encS s)

theorem R10 (k r w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) :
    (Amega (2 * k) w l (k + 1 + r) s) [tm]⊢⁺ Bodd (k + w + 2) l (k + 1 + r + w + 6) s := by
  unfold Amega Bodd
  rw [encL_cons, zeros1, ones_add (k + 1) r]
  refine sp_trans (a0_odd_zeros k 1 _ _) ?_
  refine sp_trans (ebounce_to_B1 k _ _) ?_
  rw [← ones1' (2 * k + 2)]
  refine sp_ss_trans (b1_zero_one (2 * k + 3) _ _) ?_
  rw [← ones_add (k + 1) r, ← ones1 (k + 1 + r)]
  have h := b1_zero_one_run (w + 5) (2 * k + 3) (k + 1 + r + 1) (encL l) (encS s)
  have e1 : 2 * k + 3 + 2 * (w + 5) + 1 = 2 * (k + w + 2) + 10 := by ring
  have e2 : k + 1 + r + 1 + (w + 5) = k + 1 + r + w + 6 := by ring
  rw [e1, e2] at h
  exact h

theorem R11 (k r w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) :
    (Amega (2 * k + 1) w l (k + 1 + r) s) [tm]⊢⁺ Bodd (w + 1) l (2 * k + w + 9) ((k + r) :: s) := by
  unfold Amega Bodd
  rw [encL_cons, pow1_succ' (0 : Fin 2) (2 * k + 1), ones_add (k + 1) r, encS_cons]
  refine sp_trans (a0_odd_zeros k 0 _ _) ?_
  refine ss_sp_trans (stepN_to_ss (e0_to_B1 k _ _)) ?_
  rw [← ones_add k r]
  have h1 := b1_zero_one 1 (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l) (([1] : List (Fin 2)) ^ (2 * k + 3) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + r) +> encS s)))
  rw [pow1_succ (1 : Fin 2) 0, p_zero_list, lb_append_nil] at h1
  refine sp_ss_trans h1 ?_
  rw [← ones1 (2 * k + 3)]
  have h := b1_zero_one_run (w + 5) 1 (2 * k + 4) (encL l) ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + r) +> encS s))
  have e1 : 1 + 2 * (w + 5) + 1 = 2 * (w + 1) + 10 := by ring
  have e2 : 2 * k + 4 + (w + 5) = 2 * k + w + 9 := by ring
  rw [e1, e2] at h
  exact h

theorem R12 (w : ℕ) (l : List (ℕ × ℕ)) :
    (Bounce w l []) [tm]⊢⁺ Beq (w + 5) l := by
  unfold Bounce Beq
  rw [encS_nil, show w + 5 = 5 + w by ring, blk_add 5 w]
  refine sp_ss_trans (stepN_to_sp (n := 89) (by decide) (fixed89 _)) ?_
  have h := b1_zero_one_run w 11 5 (encL l) default
  have e1 : 11 + 2 * w + 1 = 2 * (5 + w) + 2 := by ring
  rw [e1] at h
  exact h

theorem R13 (w : ℕ) (l : List (ℕ × ℕ)) :
    (Bounce w l [5]) [tm]⊢⁺ Bodd (w + 2) l (w + 11) [] := by
  unfold Bounce Bodd
  rw [encS_cons, encS_nil]
  have hz : (([1] : List (Fin 2)) ^ 5 +> default) = ([1] : List (Fin 2)) ^ (2 + 3) +> ((0 : Fin 2) >> default) := by simp
  rw [hz]
  refine sp_trans (a0_zero_R 2 _ _) ?_
  rw [zeros3 0, p_zero_list, lb_append_nil]
  refine ss_sp_trans (stepN_to_ss (fixed23 _)) ?_
  have h1 := b1_zero_one 1 ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l)) (([1] : List (Fin 2)) ^ 4 +> default)
  rw [pow1_succ (1 : Fin 2) 0, p_zero_list, lb_append_nil] at h1
  refine sp_trans h1 ?_
  rw [← ones1' 2, ← ones1 4]
  refine sp_ss_trans (b1_zero_one 3 _ _) ?_
  rw [← ones1 5]
  have h := b1_zero_one_run (w + 5) 3 (5 + 1) (encL l) default
  have e1 : 3 + 2 * (w + 5) + 1 = 2 * (w + 2) + 10 := by ring
  have e2 : 5 + 1 + (w + 5) = w + 11 := by ring
  rw [e1, e2] at h
  exact h

theorem R14 (w b' : ℕ) (l : List (ℕ × ℕ)) :
    (Bounce w l [b' + 15]) [tm]⊢⁺ Beq 5 ((b', w) :: l) := by
  unfold Bounce Beq
  rw [encS_cons, encS_nil, encL_cons]
  set X : T := (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l) with hX
  have hz : (([1] : List (Fin 2)) ^ (b' + 15) +> default) = ([1] : List (Fin 2)) ^ ((b' + 12) + 3) +> ((0 : Fin 2) >> default) := by
    rw [show b' + 12 + 3 = b' + 15 by ring, z_cons_def]
  rw [hz]
  refine sp_trans (a0_zero_R (b' + 12) _ _) ?_
  rw [show b' + 12 + 1 = (b' + 10) + 3 by ring, zeros3]
  refine ss_sp_trans (stepN_to_ss (fixed23 _)) ?_
  have hr := m_rounds 4 0 (([0] : List (Fin 2)) ^ (b' + 1) +> X) default
  rw [show (2 : ℕ) * 0 + 1 = 1 by norm_num, show (2 : ℕ) * 4 + 2 = 10 by norm_num,
    show (0 : ℕ) + 4 = 4 by norm_num, show (2 : ℕ) * 0 + 2 * 4 + 1 = 9 by norm_num, ones_one,
    ← pow1_add (0 : Fin 2) 10 (b' + 1), show 10 + (b' + 1) = (b' + 10) + 1 by ring, zeros1 (b' + 10)] at hr
  refine ss_sp_trans hr ?_
  rw [zeros1 b']
  refine sp_ss_trans (b1_three_zeros 8 _ _) ?_
  refine ss_trans (a0_cascade 4 ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ b' +> X)) default) ?_
  exact stepN_to_ss (fixed89 _)

theorem R15 (w b₁ b₂ : ℕ) (l : List (ℕ × ℕ)) (s' : List ℕ) :
    (Bounce w l ((b₁ + 3) :: b₂ :: s')) [tm]⊢⁺ Amega b₁ w l b₂ s' := by
  unfold Bounce Amega
  rw [encS_cons, encS_cons, encL_cons]
  exact a0_zero_R b₁ _ _

-- Iterated R4 / R4nil helpers
lemma R4_iter (d : ℕ) : ∀ (j r z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ),
    (Bev j ((z + 2 * d, w) :: l') (j + d + r) s) [tm]⊢* Bev (j + d) ((z, w) :: l') (j + d + r) s := by
  induction d with
  | zero =>
    intro j r z w l' s
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ss_refl _ _
  | succ d ih =>
    intro j r z w l' s
    have h_step := sp_to_ss (R4 j (d + r) (z + 2 * d) w l' s)
    have e_z : (z + 2 * d) + 2 = z + 2 * (d + 1) := by omega
    have e_m : j + 1 + (d + r) = j + (d + 1) + r := by omega
    rw [e_z, e_m] at h_step
    refine ss_trans h_step ?_
    have h2 := ih (j + 1) r z w l' s
    have e1 : j + 1 + d = j + (d + 1) := by omega
    rw [e1] at h2
    exact h2

lemma R4nil_iter (d : ℕ) : ∀ (j r : ℕ) (s : List ℕ),
    (Bev j [] (j + d + r) s) [tm]⊢* Bev (j + d) [] (j + d + r) s := by
  induction d with
  | zero =>
    intro j r s
    simp only [Nat.add_zero]
    exact ss_refl _ _
  | succ d ih =>
    intro j r s
    have h_step := sp_to_ss (R4nil j (d + r) s)
    have e_m : j + 1 + (d + r) = j + (d + 1) + r := by omega
    rw [e_m] at h_step
    refine ss_trans h_step ?_
    have h2 := ih (j + 1) r s
    have e1 : j + 1 + d = j + (d + 1) := by omega
    rw [e1] at h2
    exact h2

lemma bev0_nil_bounce (m' : ℕ) (s : List ℕ) :
    (Bev 0 [] (m' + 4) s) [tm]⊢⁺ Bounce m' [] s := by
  have h1 := R4nil_iter (m' + 4) 0 0 s
  simp only [Nat.zero_add, Nat.add_zero] at h1
  exact ss_sp_trans h1 (R5nil m' s)

-- ---------------------------------------------------------------------------
-- Stack-polymorphic linear excursion calculus & root invariant
-- ---------------------------------------------------------------------------

def ValidL (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, 27 ≤ p.2

lemma validL_nil : ValidL [] := by
  intro p hp; cases hp

lemma validL_cons {z w : ℕ} {l : List (ℕ × ℕ)} (hw : 27 ≤ w) (hl : ValidL l) :
    ValidL ((z, w) :: l) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hmem
  · exact hw
  · exact hl p hmem

lemma validL_head {z w : ℕ} {l : List (ℕ × ℕ)} (hl : ValidL ((z, w) :: l)) : 27 ≤ w :=
  hl (z, w) (List.mem_cons_self ..)

lemma validL_tail {z w : ℕ} {l : List (ℕ × ℕ)} (hl : ValidL ((z, w) :: l)) : ValidL l :=
  fun p hp => hl p (List.mem_cons_of_mem _ hp)

@[reducible] def bx (j m : ℕ) : ℕ := m - (5 * m - (4 * j + 165)) / 60 - 1
@[reducible] def bdw (j m : ℕ) : ℕ := bx j m - 5
@[reducible] def bxw (j m : ℕ) : ℕ := m + j / 15 + 27
@[reducible] def ox (k M : ℕ) : ℕ := M - (5 * M - (4 * k + 30)) / 60 - 2
@[reducible] def odw (k M : ℕ) : ℕ := ox k M - 5
@[reducible] def oxw (k M : ℕ) : ℕ := M + k / 15 + 55

local macro "lin_omega" : tactic =>
  `(tactic| (dsimp only [bx, bdw, bxw, ox, odw, oxw] at *; omega))

lemma div15_spec (n : ℕ) : ∃ q r : ℕ, r < 15 ∧ n = 15 * q + r ∧ n / 15 = q :=
  ⟨n / 15, n % 15, Nat.mod_lt n (by decide), (Nat.div_add_mod n 15).symm, rfl⟩

lemma bx_spec (j m : ℕ) :
    ∃ bxv : ℕ, bx j m = bxv ∧ bdw j m = bxv - 5 ∧
      ((5 * m ≤ 4 * j + 165 ∧ bxv = m - 1) ∨
       (∃ q r : ℕ, r < 60 ∧ 5 * m = 4 * j + 165 + 60 * q + r ∧ bxv = m - q - 1)) := by
  refine ⟨bx j m, rfl, rfl, ?_⟩
  dsimp only [bx]
  rcases Nat.lt_or_ge (4 * j + 165) (5 * m) with hgt | hle
  · right
    refine ⟨(5 * m - (4 * j + 165)) / 60, (5 * m - (4 * j + 165)) % 60,
      Nat.mod_lt _ (by decide), ?_, rfl⟩
    have hdm := Nat.div_add_mod (5 * m - (4 * j + 165)) 60
    omega
  · left
    exact ⟨hle, by rw [Nat.sub_eq_zero_of_le hle]; omega⟩

lemma ox_spec (k M : ℕ) :
    ∃ oxv : ℕ, ox k M = oxv ∧ odw k M = oxv - 5 ∧
      ((5 * M ≤ 4 * k + 30 ∧ oxv = M - 2) ∨
       (∃ q r : ℕ, r < 60 ∧ 5 * M = 4 * k + 30 + 60 * q + r ∧ oxv = M - q - 2)) := by
  refine ⟨ox k M, rfl, rfl, ?_⟩
  dsimp only [ox]
  rcases Nat.lt_or_ge (4 * k + 30) (5 * M) with hgt | hle
  · right
    refine ⟨(5 * M - (4 * k + 30)) / 60, (5 * M - (4 * k + 30)) % 60,
      Nat.mod_lt _ (by decide), ?_, rfl⟩
    have hdm := Nat.div_add_mod (5 * M - (4 * k + 30)) 60
    omega
  · left
    exact ⟨hle, by rw [Nat.sub_eq_zero_of_le hle]; omega⟩

def Exit (tx tdw txw : ℕ) (S : List ℕ) (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  (∃ w l, ValidL l ∧ 27 ≤ w ∧ tdw ≤ w ∧ c = Bounce w l S) ∨
  (∃ x w l, ValidL l ∧ 27 ≤ w ∧ tx ≤ x ∧ txw ≤ x + w ∧ c = Bounce w l (x :: S))

lemma exit_mono {tx₁ tdw₁ txw₁ tx₂ tdw₂ txw₂ : ℕ} {S : List ℕ} {c : Cfg (Fin 2) (Fin 6)}
    (h : Exit tx₂ tdw₂ txw₂ S c) (h1 : tx₁ ≤ tx₂) (h2 : tdw₁ ≤ tdw₂) (h3 : txw₁ ≤ txw₂) :
    Exit tx₁ tdw₁ txw₁ S c := by
  rcases h with ⟨w, l, hl, hw, htdw, rfl⟩ | ⟨x, w, l, hl, hw, htx, htxw, rfl⟩
  · exact Or.inl ⟨w, l, hl, hw, by omega, rfl⟩
  · exact Or.inr ⟨x, w, l, hl, hw, by omega, by omega, rfl⟩

def LeadsUpTo (N : ℕ) (c : Cfg (Fin 2) (Fin 6)) (P : Cfg (Fin 2) (Fin 6) → Prop) : Prop :=
  ∀ n, n ≤ N → HaltsIn tm c n → ∃ m d, m ≤ n ∧ P d ∧ HaltsIn tm d m

lemma leadsUpTo_here {N : ℕ} {c : Cfg (Fin 2) (Fin 6)} {P : Cfg (Fin 2) (Fin 6) → Prop}
    (hc : P c) : LeadsUpTo N c P :=
  fun n _ hn => ⟨n, c, Nat.le_refl n, hc, hn⟩

lemma leadsUpTo_mono {N : ℕ} {c : Cfg (Fin 2) (Fin 6)} {P Q : Cfg (Fin 2) (Fin 6) → Prop}
    (h₁ : LeadsUpTo N c P) (h₂ : ∀ d, P d → Q d) : LeadsUpTo N c Q := by
  intro n hnN hn
  rcases h₁ n hnN hn with ⟨m, d, hmn, hPd, hm⟩
  exact ⟨m, d, hmn, h₂ d hPd, hm⟩

lemma leadsUpTo_trans {N : ℕ} {c : Cfg (Fin 2) (Fin 6)} {P Q : Cfg (Fin 2) (Fin 6) → Prop}
    (h₁ : LeadsUpTo N c P) (h₂ : ∀ d, P d → LeadsUpTo N d Q) : LeadsUpTo N c Q := by
  intro n hnN hn
  rcases h₁ n hnN hn with ⟨m, d, hmn, hPd, hm⟩
  rcases h₂ d hPd m (Nat.le_trans hmn hnN) hm with ⟨k, e, hkm, hQe, hk⟩
  exact ⟨k, e, Nat.le_trans hkm hmn, hQe, hk⟩

lemma leadsUpTo_stepPlus {N : ℕ} {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {P : Cfg (Fin 2) (Fin 6) → Prop}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : ∀ m, m < N → LeadsUpTo m c₂ P) : LeadsUpTo N c₁ P := by
  intro n hnN hn
  rcases haltsIn_reduce_stepPlus h₁ hn with ⟨m, hmn, hm⟩
  rcases h₂ m (Nat.lt_of_lt_of_le hmn hnN) m (Nat.le_refl m) hm with ⟨k, d, hkm, hPd, hk⟩
  exact ⟨k, d, Nat.le_trans hkm (Nat.le_of_lt hmn), hPd, hk⟩

def BevBound (N : ℕ) : Prop :=
  ∀ j l m S, ValidL l → j ≤ m → 35 ≤ m →
    LeadsUpTo N (Bev j l m S) (Exit (bx j m) (bdw j m) (bxw j m) S)

def BoddBound (N : ℕ) : Prop :=
  ∀ k l M S, ValidL l → 28 ≤ k → k + 5 ≤ M → 36 ≤ M →
    LeadsUpTo N (Bodd k l M S) (Exit (ox k M) (odw k M) (oxw k M) S)

def LoopBound (N : ℕ) : Prop :=
  ∀ kc lc Mc x tx tdw txw S,
    ValidL lc → 28 ≤ kc → kc + 5 ≤ Mc → 36 ≤ Mc →
    34 ≤ tx → tdw = tx - 5 → tx ≤ x →
    695 * tx + 27 ≤ 11 * (Mc + 61 * x) →
    60 * tx ≤ 2 * Mc + 55 * x + 200 →
    12 * txw + 72 ≤ 11 * Mc + 12 * x →
    30 * txw ≤ Mc + 30 * x + 1700 →
    LeadsUpTo N (Bodd kc lc Mc (x :: S)) (Exit tx tdw txw S)

lemma amega_bounce_step {N : ℕ}
    (ih : ∀ m, m < N → BevBound m ∧ BoddBound m ∧ LoopBound m)
    {z0 w1 x tx tdw txw : ℕ} {l1 : List (ℕ × ℕ)} {S : List ℕ}
    (hl1 : ValidL l1) (hw1 : 27 ≤ w1) (hz0_ge3 : 3 ≤ z0)
    (htx34 : 34 ≤ tx) (htdw : tdw = tx - 5) (htxx : tx ≤ x)
    (h_r10_tx : ∀ kp, z0 = 3 + kp * 2 → kp + 1 ≤ x → tx ≤ ox (kp + w1 + 2) (x + w1 + 6))
    (h_r10_txw : ∀ kp, z0 = 3 + kp * 2 → kp + 1 ≤ x → txw ≤ oxw (kp + w1 + 2) (x + w1 + 6))
    (h_r11_x : ∀ kp, z0 = 4 + kp * 2 → kp + 1 ≤ x → tx ≤ x - 1)
    (h_r11_i1 : ∀ kp, z0 = 4 + kp * 2 → kp + 1 ≤ x → 695 * tx + 27 ≤ 11 * ((2 * kp + w1 + 9) + 61 * (x - 1)))
    (h_r11_i2 : ∀ kp, z0 = 4 + kp * 2 → kp + 1 ≤ x → 60 * tx ≤ 2 * (2 * kp + w1 + 9) + 55 * (x - 1) + 200)
    (h_r11_i3 : ∀ kp, z0 = 4 + kp * 2 → kp + 1 ≤ x → 12 * txw + 72 ≤ 11 * (2 * kp + w1 + 9) + 12 * (x - 1))
    (h_r11_i4 : ∀ kp, z0 = 4 + kp * 2 → kp + 1 ≤ x → 30 * txw ≤ (2 * kp + w1 + 9) + 30 * (x - 1) + 1700) :
    LeadsUpTo N (Bounce w1 l1 (z0 :: x :: S)) (Exit tx tdw txw S) := by
  rcases Nat.lt_or_ge (z0 - 3) (2 * x) with hlt | hge
  · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
    · have hz_eq : z0 = 3 + kp * 2 := by omega
      have hkpx : kp + 1 ≤ x := by omega
      have h_step : (Bounce w1 l1 (z0 :: x :: S)) [tm]⊢⁺ Bodd (kp + w1 + 2) l1 (x + w1 + 6) S := by
        have h1 : Bounce w1 l1 (z0 :: x :: S) = Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (x - (kp + 1))) :: S) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h2 := sp_trans (R15 w1 (2 * kp) (kp + 1 + (x - (kp + 1))) l1 S)
          (R10 kp (x - (kp + 1)) w1 l1 S)
        have e1 : kp + 1 + (x - (kp + 1)) + w1 + 6 = x + w1 + 6 := by omega
        rwa [e1] at h2
      refine leadsUpTo_stepPlus h_step (fun m hm => ?_)
      have hb := (ih m hm).2.1 (kp + w1 + 2) l1 (x + w1 + 6) S hl1 (by omega) (by omega) (by omega)
      refine leadsUpTo_mono hb (fun d hd => ?_)
      have htx' := h_r10_tx kp hz_eq hkpx
      have htxw' := h_r10_txw kp hz_eq hkpx
      exact exit_mono hd htx' (by dsimp only [odw]; omega) htxw'
    · have hz_eq : z0 = 4 + kp * 2 := by omega
      have hkpx : kp + 1 ≤ x := by omega
      have h_step : (Bounce w1 l1 (z0 :: x :: S)) [tm]⊢⁺ Bodd (w1 + 1) l1 (2 * kp + w1 + 9) ((x - 1) :: S) := by
        have h1 : Bounce w1 l1 (z0 :: x :: S) = Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (x - (kp + 1))) :: S) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h2 := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (x - (kp + 1))) l1 S)
          (R11 kp (x - (kp + 1)) w1 l1 S)
        have e1 : kp + (x - (kp + 1)) = x - 1 := by omega
        rwa [e1] at h2
      refine leadsUpTo_stepPlus h_step (fun m hm => ?_)
      exact (ih m hm).2.2 (w1 + 1) l1 (2 * kp + w1 + 9) (x - 1) tx tdw txw S
        hl1 (by omega) (by omega) (by omega) htx34 htdw
        (h_r11_x kp hz_eq hkpx) (h_r11_i1 kp hz_eq hkpx)
        (h_r11_i2 kp hz_eq hkpx) (h_r11_i3 kp hz_eq hkpx) (h_r11_i4 kp hz_eq hkpx)
  · have h_step : (Bounce w1 l1 (z0 :: x :: S)) [tm]⊢⁺ Bounce (x - 5) ((z0 - 3 - 2 * x, w1) :: l1) S := by
      have h1 : Bounce w1 l1 (z0 :: x :: S) =
          Bounce w1 l1 (((2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) + 3) :: ((x - 5) + 5) :: S) := by
        congr 1; congr 1
        · omega
        · congr 1; omega
      rw [h1]
      exact sp_trans (R15 w1 (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) ((x - 5) + 5) l1 S)
        (R9 (x - 5) (z0 - 3 - 2 * x) w1 l1 S)
    refine leadsUpTo_stepPlus h_step (fun m _ => ?_)
    exact leadsUpTo_here (Or.inl ⟨x - 5, (z0 - 3 - 2 * x, w1) :: l1,
      validL_cons hw1 hl1, by omega, by omega, rfl⟩)

theorem excursion_bundle (N : ℕ) : BevBound N ∧ BoddBound N ∧ LoopBound N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have h_bev : BevBound N := by
      intro j l m S hl hjm hm35
      rcases l with _ | ⟨⟨z, w⟩, l'⟩
      · rcases Nat.lt_or_ge j m with hlt | hge
        · have h_eq : Bev j [] m S = Bev j [] (j + 1 + (m - (j + 1))) S := by congr 1; omega
          rw [h_eq]
          refine leadsUpTo_stepPlus (R4nil j (m - (j + 1)) S) (fun n' hn' => ?_)
          have h_sub : j + 1 + (m - (j + 1)) = m := by omega
          rw [h_sub]
          refine leadsUpTo_mono ((ih n' hn').1 (j + 1) [] m S validL_nil (by omega) hm35) (fun d hd => ?_)
          exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
        · have hjm_eq : j = m := by omega
          subst hjm_eq
          have h_eq : Bev j [] j S = Bev ((j - 4) + 4) [] ((j - 4) + 4) S := by congr 1 <;> omega
          rw [h_eq]
          refine leadsUpTo_stepPlus (R5nil (j - 4) S) (fun _ _ => ?_)
          exact leadsUpTo_here (Or.inl ⟨j - 4, [], validL_nil, by omega, by lin_omega, rfl⟩)
      · have hw : 27 ≤ w := validL_head hl
        have hl' : ValidL l' := validL_tail hl
        rcases z with _ | _ | z'
        · refine leadsUpTo_stepPlus (R6 j m w l' S) (fun n' hm' => ?_)
          refine leadsUpTo_mono ((ih n' hm').2.1 (j + w + 2) l' (m + w + 7) S hl'
            (by omega) (by omega) (by omega)) (fun d hd => ?_)
          exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
        · refine leadsUpTo_stepPlus (R7 j m w l' S) (fun n' hn' => ?_)
          have hb_all : 34 ≤ bx j m ∧ bx j m ≤ m ∧
              695 * bx j m + 27 ≤ 11 * ((2 * j + w + 9) + 61 * m) ∧
              60 * bx j m ≤ 2 * (2 * j + w + 9) + 55 * m + 200 ∧
              12 * bxw j m + 72 ≤ 11 * (2 * j + w + 9) + 12 * m ∧
              30 * bxw j m ≤ (2 * j + w + 9) + 30 * m + 1700 := by
            rcases bx_spec j m with ⟨bxv, hbxv, _, hbx_cases⟩
            rcases div15_spec j with ⟨qj, rj, hrj, hjeq, hjdiv⟩
            dsimp only [bxw]
            rw [hbxv, hjdiv]
            rcases hbx_cases with ⟨hle, rfl⟩ | ⟨q, r, hr, heq, rfl⟩
            · omega
            · refine ⟨by omega, by omega, ?_, by omega, by omega, by omega⟩
              rcases j with _ | _ | _ | _ | j' <;> omega
          exact (ih n' hn').2.2 (w + 1) l' (2 * j + w + 9) m (bx j m) (bdw j m) (bxw j m) S
            hl' (by omega) (by omega) (by omega) hb_all.1 rfl hb_all.2.1
            hb_all.2.2.1 hb_all.2.2.2.1 hb_all.2.2.2.2.1 hb_all.2.2.2.2.2
        · rcases Nat.lt_or_ge j m with hlt | hge
          · have h_eq : Bev j ((z' + 2, w) :: l') m S =
                Bev j ((z' + 2, w) :: l') (j + 1 + (m - (j + 1))) S := by congr 1; omega
            rw [h_eq]
            refine leadsUpTo_stepPlus (R4 j (m - (j + 1)) z' w l' S) (fun n' hn' => ?_)
            have h_sub : j + 1 + (m - (j + 1)) = m := by omega
            rw [h_sub]
            refine leadsUpTo_mono ((ih n' hn').1 (j + 1) ((z', w) :: l') m S
              (validL_cons hw hl') (by omega) hm35) (fun d hd => ?_)
            exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
          · have hjm_eq : j = m := by omega
            subst hjm_eq
            have h_eq : Bev j ((z' + 2, w) :: l') j S =
                Bev ((j - 4) + 4) ((z' + 2, w) :: l') ((j - 4) + 4) S := by congr 1 <;> omega
            rw [h_eq]
            refine leadsUpTo_stepPlus (R5 (j - 4) z' w l' S) (fun _ _ => ?_)
            exact leadsUpTo_here (Or.inl ⟨j - 4, (z', w) :: l', validL_cons hw hl',
              by omega, by lin_omega, rfl⟩)
    have h_bodd : BoddBound N := by
      intro k l M S hl hk28 hkM hM36
      have h_r8_post : ∀ (l'' : List (ℕ × ℕ)), ValidL l'' →
          ∀ m', m' < N → LeadsUpTo m' (Bev 0 l'' (2 * k + 11) ((M - 1) :: S))
            (Exit (ox k M) (odw k M) (oxw k M) S) := by
        intro l'' hl'' m' hm'
        refine leadsUpTo_trans ((ih m' hm').1 0 l'' (2 * k + 11) ((M - 1) :: S) hl'' (by omega) (by omega)) ?_
        rintro d (⟨w1, l1, hl1, hw1, hbdw, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hbx, hbxw, rfl⟩)
        · rcases bx_spec 0 (2 * k + 11) with ⟨bxv, _, hbdwv, hbx_c⟩
          rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
          rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
          rw [hbdwv] at hbdw
          refine leadsUpTo_here (Or.inr ⟨M - 1, w1, l1, hl1, hw1, ?_, ?_, rfl⟩)
          · rw [hoxv]
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
          · dsimp only [oxw]; rw [hkdiv]
            rcases hbx_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
        · have hz3 : 3 ≤ z0 := by lin_omega
          have hox34 : 34 ≤ ox k M := by lin_omega
          have hoxM : ox k M ≤ M - 1 := by lin_omega
          exact amega_bounce_step (fun m'' hm'' => ih m'' (Nat.lt_trans hm'' hm'))
            hl1 hw1 hz3 hox34 rfl hoxM
            (fun kp hz hkpx => by
              rcases bx_spec 0 (2 * k + 11) with ⟨bxv, hbxv, _, hbx_c⟩
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              rcases ox_spec (kp + w1 + 2) ((M - 1) + w1 + 6) with ⟨ox2, hox2, _, hox2_c⟩
              dsimp only [bxw] at hbxw
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hbxv] at hbx; rw [hoxv, hox2]
              rcases hbx_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
                rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
                rcases hox2_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
              rcases div15_spec (kp + w1 + 2) with ⟨qo, ro, hro, hoeq, hodiv⟩
              dsimp only [bxw, oxw] at hbxw ⊢
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hkdiv, hodiv]; omega)
            (fun kp hz hkpx => by
              rcases bx_spec 0 (2 * k + 11) with ⟨bxv, hbxv, _, hbx_c⟩
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              rw [hbxv] at hbx; rw [hoxv]
              rcases hbx_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
                rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              dsimp only [bxw] at hbxw
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hoxv]
              rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              dsimp only [bxw] at hbxw
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hoxv]
              rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
              dsimp only [bxw, oxw] at hbxw ⊢
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hkdiv]; omega)
            (fun kp hz hkpx => by
              rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
              dsimp only [bxw, oxw] at hbxw ⊢
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hkdiv]; omega)
      rcases l with _ | ⟨⟨z, w⟩, l'⟩
      · have h_eq : Bodd k [] M S = Bodd k [] (k + 5 + (M - (k + 5))) S := by congr 1; omega
        rw [h_eq]
        refine leadsUpTo_stepPlus (R8nil k (M - (k + 5)) S) (fun m' hm' => ?_)
        have e1 : k + 4 + (M - (k + 5)) = M - 1 := by omega
        rw [e1]
        exact h_r8_post [] validL_nil m' hm'
      · have hw : 27 ≤ w := validL_head hl
        have hl' : ValidL l' := validL_tail hl
        rcases z with _ | _ | z'
        · refine leadsUpTo_stepPlus (R8a k M w l' S) (fun m' hm' => ?_)
          refine leadsUpTo_mono ((ih m' hm').1 (k + w + 11) l' (M + w + 7) S hl'
            (by omega) (by omega)) (fun d hd => ?_)
          exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
        · refine leadsUpTo_stepPlus (R8b k M w l' S) (fun m' hm' => ?_)
          have ho_all : 34 ≤ ox k M ∧ ox k M ≤ M ∧
              695 * ox k M + 27 ≤ 11 * ((2 * k + w + 18) + 61 * M) ∧
              60 * ox k M ≤ 2 * (2 * k + w + 18) + 55 * M + 200 ∧
              12 * oxw k M + 72 ≤ 11 * (2 * k + w + 18) + 12 * M ∧
              30 * oxw k M ≤ (2 * k + w + 18) + 30 * M + 1700 := by
            rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
            rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
            dsimp only [oxw]
            rw [hoxv, hkdiv]
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
          exact (ih m' hm').2.2 (w + 1) l' (2 * k + w + 18) M (ox k M) (odw k M) (oxw k M) S
            hl' (by omega) (by omega) (by omega) ho_all.1 rfl ho_all.2.1
            ho_all.2.2.1 ho_all.2.2.2.1 ho_all.2.2.2.2.1 ho_all.2.2.2.2.2
        · have h_eq : Bodd k ((z' + 2, w) :: l') M S =
              Bodd k ((z' + 2, w) :: l') (k + 5 + (M - (k + 5))) S := by congr 1; omega
          rw [h_eq]
          refine leadsUpTo_stepPlus (R8 k (M - (k + 5)) z' w l' S) (fun m' hm' => ?_)
          have e1 : k + 4 + (M - (k + 5)) = M - 1 := by omega
          rw [e1]
          exact h_r8_post ((z', w) :: l') (validL_cons hw hl') m' hm'
    have h_loop : LoopBound N := by
      intro kc lc Mc x tx tdw txw S hlc hkc28 hkcMc hMc36 htx34 htdw htxx hi1 hi2 hi3 hi4
      refine leadsUpTo_trans (h_bodd kc lc Mc (x :: S) hlc hkc28 hkcMc hMc36) ?_
      rintro d (⟨w1, l1, hl1, hw1, hodw, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hox, hoxw, rfl⟩)
      · rcases ox_spec kc Mc with ⟨oxv, _, hodwv, hox_c⟩
        rw [hodwv] at hodw
        refine leadsUpTo_here (Or.inr ⟨x, w1, l1, hl1, hw1, htxx, ?_, rfl⟩)
        rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
      · have hz3 : 3 ≤ z0 := by lin_omega
        exact amega_bounce_step ih hl1 hw1 hz3 htx34 htdw htxx
          (fun kp hz hkpx => by
            rcases ox_spec kc Mc with ⟨oxv, hoxv, _, hox_c⟩
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            rcases ox_spec (kp + w1 + 2) (x + w1 + 6) with ⟨ox2, hox2, _, hox2_c⟩
            dsimp only [oxw] at hoxw
            rw [hoxv] at hox; rw [hkcdiv] at hoxw; rw [hox2]
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
              rcases hox2_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            rcases div15_spec (kp + w1 + 2) with ⟨qo, ro, hro, hoeq, hodiv⟩
            dsimp only [oxw] at hoxw ⊢
            rw [hkcdiv] at hoxw; rw [hodiv]; omega)
          (fun kp hz hkpx => by
            rcases ox_spec kc Mc with ⟨oxv, hoxv, _, hox_c⟩
            rw [hoxv] at hox
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
    exact ⟨h_bev, h_bodd, h_loop⟩

lemma bev_leads {j m : ℕ} {l : List (ℕ × ℕ)} {S : List ℕ}
    (hl : ValidL l) (hjm : j ≤ m) (hm35 : 35 ≤ m) :
    Leads tm (Bev j l m S) (Exit (bx j m) (bdw j m) (bxw j m) S) :=
  fun n hn => (excursion_bundle n).1 j l m S hl hjm hm35 n (Nat.le_refl n) hn

lemma bodd_leads {k M : ℕ} {l : List (ℕ × ℕ)} {S : List ℕ}
    (hl : ValidL l) (hk28 : 28 ≤ k) (hkM : k + 5 ≤ M) (hM36 : 36 ≤ M) :
    Leads tm (Bodd k l M S) (Exit (ox k M) (odw k M) (oxw k M) S) :=
  fun n hn => (excursion_bundle n).2.1 k l M S hl hk28 hkM hM36 n (Nat.le_refl n) hn

lemma loop_leads {kc Mc x tx tdw txw : ℕ} {lc : List (ℕ × ℕ)} {S : List ℕ}
    (hlc : ValidL lc) (hkc28 : 28 ≤ kc) (hkcMc : kc + 5 ≤ Mc) (hMc36 : 36 ≤ Mc)
    (htx34 : 34 ≤ tx) (htdw : tdw = tx - 5) (htxx : tx ≤ x)
    (hi1 : 695 * tx + 27 ≤ 11 * (Mc + 61 * x))
    (hi2 : 60 * tx ≤ 2 * Mc + 55 * x + 200)
    (hi3 : 12 * txw + 72 ≤ 11 * Mc + 12 * x)
    (hi4 : 30 * txw ≤ Mc + 30 * x + 1700) :
    Leads tm (Bodd kc lc Mc (x :: S)) (Exit tx tdw txw S) :=
  fun n hn => (excursion_bundle n).2.2 kc lc Mc x tx tdw txw S
    hlc hkc28 hkcMc hMc36 htx34 htdw htxx hi1 hi2 hi3 hi4 n (Nat.le_refl n) hn

-- ---------------------------------------------------------------------------
-- Root invariant closure (`RootInv`)
-- ---------------------------------------------------------------------------

def RootInv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ M l, (M = 5 ∨ 18 ≤ M) ∧ ValidL l ∧ c = Beq M l

lemma root_of_5 {l : List (ℕ × ℕ)} (hl : ValidL l) : RootInv (Beq 5 l) :=
  ⟨5, l, Or.inl rfl, hl, rfl⟩

lemma root_of_ge18 {M : ℕ} {l : List (ℕ × ℕ)} (hM : 18 ≤ M) (hl : ValidL l) : RootInv (Beq M l) :=
  ⟨M, l, Or.inr hM, hl, rfl⟩

lemma exit_nil_leads_root {tx tdw txw : ℕ} (htx : 15 ≤ tx) {c : Cfg (Fin 2) (Fin 6)}
    (hc : Exit tx tdw txw [] c) : Leads tm c RootInv := by
  rcases hc with ⟨w, l, hl, hw, _, rfl⟩ | ⟨x, w, l, hl, hw, hxx, _, rfl⟩
  · exact (Advances.of_stepPlus (R12 w l) (root_of_ge18 (by omega) hl)).to_leads
  · have h_eq : Bounce w l [x] = Bounce w l [(x - 15) + 15] := by
      congr 1; congr 1; omega
    rw [h_eq]
    exact (Advances.of_stepPlus (R14 w (x - 15) l) (root_of_5 (validL_cons hw hl))).to_leads

lemma bev_nil_leads_root {j m : ℕ} {l : List (ℕ × ℕ)}
    (hl : ValidL l) (hjm : j ≤ m) (hm35 : 35 ≤ m) :
    Leads tm (Bev j l m []) RootInv :=
  (bev_leads hl hjm hm35).trans (fun _ hd => exit_nil_leads_root (by lin_omega) hd)

lemma bodd_nil_leads_root {k M : ℕ} {l : List (ℕ × ℕ)}
    (hl : ValidL l) (hk28 : 28 ≤ k) (hkM : k + 5 ≤ M) (hM36 : 36 ≤ M) :
    Leads tm (Bodd k l M []) RootInv :=
  (bodd_leads hl hk28 hkM hM36).trans (fun _ hd => exit_nil_leads_root (by lin_omega) hd)

lemma exit_single_forced_r9 {tx tdw txw x : ℕ} (hx18 : 18 ≤ x) (htx_r9 : 2 * x + 3 ≤ tx)
    {c : Cfg (Fin 2) (Fin 6)} (hc : Exit tx tdw txw [x] c) : Leads tm c RootInv := by
  rcases hc with ⟨w, l, hl, hw, _, rfl⟩ | ⟨z0, w, l, hl, hw, hz0, _, rfl⟩
  · have h_eq : Bounce w l [x] = Bounce w l [(x - 15) + 15] := by
      congr 1; congr 1; omega
    rw [h_eq]
    exact (Advances.of_stepPlus (R14 w (x - 15) l) (root_of_5 (validL_cons hw hl))).to_leads
  · have h_step := sp_trans
      (sp_trans (R15 w (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) ((x - 5) + 5) l [])
        (R9 (x - 5) (z0 - 3 - 2 * x) w l []))
      (R12 (x - 5) ((z0 - 3 - 2 * x, w) :: l))
    have e1 : 2 * ((x - 5) + 5) + (z0 - 3 - 2 * x) + 3 = z0 := by omega
    have e2 : (x - 5) + 5 = x := by omega
    rw [e1, e2] at h_step
    exact (Advances.of_stepPlus h_step (root_of_ge18 hx18 (validL_cons hw hl))).to_leads

lemma exit_5_leads_root {tx tdw txw : ℕ} (htx : 13 ≤ tx) {c : Cfg (Fin 2) (Fin 6)}
    (hc : Exit tx tdw txw [5] c) : Leads tm c RootInv := by
  rcases hc with ⟨w, l, hl, hw, _, rfl⟩ | ⟨z0, w, l, hl, hw, hz0, _, rfl⟩
  · exact Leads.of_stepPlus_leads (R13 w l)
      (bodd_nil_leads_root hl (by omega) (by omega) (by omega))
  · have h1 : Bounce w l [z0, 5] = Bounce w l (((2 * (0 + 5) + (z0 - 13)) + 3) :: (0 + 5) :: []) := by
      congr 1; congr 1; omega
    rw [h1]
    have h_step := sp_trans
      (sp_trans (R15 w (2 * (0 + 5) + (z0 - 13)) (0 + 5) l [])
        (R9 0 (z0 - 13) w l []))
      (R12 0 ((z0 - 13, w) :: l))
    exact (Advances.of_stepPlus h_step (root_of_5 (validL_cons hw hl))).to_leads
lemma bev0_35_20_leads_root {l : List (ℕ × ℕ)} (hl : ValidL l) :
    Leads tm (Bev 0 l 35 [20]) RootInv := by
  refine (bev_leads hl (by omega) (by omega)).trans ?_
  rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
  · exact (Advances.of_stepPlus (R14 w1 5 l1) (root_of_5 (validL_cons hw1 hl1))).to_leads
  · have hz34 : 34 ≤ z0 := by lin_omega
    have hzw62 : 62 ≤ z0 + w1 := by lin_omega
    rcases Nat.lt_or_ge (z0 - 3) 40 with hlt | hge
    · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
      · have h1 : Bounce w1 l1 [z0, 20] =
            Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (20 - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (20 - (kp + 1))) l1 [])
          (R10 kp (20 - (kp + 1)) w1 l1 [])
        have e1 : kp + 1 + (20 - (kp + 1)) + w1 + 6 = w1 + 26 := by omega
        rw [e1] at h_step
        exact Leads.of_stepPlus_leads h_step
          (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
      · have h1 : Bounce w1 l1 [z0, 20] =
            Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (20 - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (20 - (kp + 1))) l1 [])
          (R11 kp (20 - (kp + 1)) w1 l1 [])
        have e1 : kp + (20 - (kp + 1)) = 19 := by omega
        rw [e1] at h_step
        refine Leads.of_stepPlus_leads h_step ?_
        exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
    · have h1 : Bounce w1 l1 [z0, 20] =
          Bounce w1 l1 (((2 * (15 + 5) + (z0 - 43)) + 3) :: (15 + 5) :: []) := by
        congr 1; congr 1; omega
      rw [h1]
      have h_step := sp_trans
        (sp_trans (R15 w1 (2 * (15 + 5) + (z0 - 43)) (15 + 5) l1 [])
          (R9 15 (z0 - 43) w1 l1 []))
        (R12 15 ((z0 - 43, w1) :: l1))
      exact (Advances.of_stepPlus h_step (root_of_ge18 (by omega) (validL_cons hw1 hl1))).to_leads

lemma bodd12_21_leads_root {l : List (ℕ × ℕ)} (hl : ValidL l) :
    Leads tm (Bodd 12 l 21 []) RootInv := by
  rcases l with _ | ⟨⟨z, w⟩, l'⟩
  · exact Leads.of_stepPlus_leads (R8nil 12 4 []) (bev0_35_20_leads_root validL_nil)
  · have hw : 27 ≤ w := validL_head hl
    have hl' : ValidL l' := validL_tail hl
    rcases z with _ | _ | z'
    · exact Leads.of_stepPlus_leads (R8a 12 21 w l' [])
        (bev_nil_leads_root hl' (by omega) (by omega))
    · refine Leads.of_stepPlus_leads (R8b 12 21 w l' []) ?_
      exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
        (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
    · exact Leads.of_stepPlus_leads (R8 12 4 z' w l' [])
        (bev0_35_20_leads_root (validL_cons hw hl'))

lemma bev_33_19_walk (rem : ℕ) : ∀ {j : ℕ} {l : List (ℕ × ℕ)},
    rem = 33 - j → j ≤ 33 → ValidL l → Leads tm (Bev j l 33 [19]) RootInv := by
  induction rem with
  | zero =>
    intro j l hrem hj hl
    have hj33 : j = 33 := by omega
    subst hj33
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · exact (Advances.of_stepPlus (sp_trans (R5nil 29 [19]) (R14 29 4 []))
        (root_of_5 (validL_cons (by omega) validL_nil))).to_leads
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 33 33 w l' [19]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
      · refine Leads.of_stepPlus_leads (R7 33 33 w l' [19]) ?_
        refine (bodd_leads hl' (by omega) (by omega) (by omega)).trans ?_
        rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
        · have h_step := sp_trans (R15 w1 30 19 l1 []) (R10 15 3 w1 l1 [])
          exact Leads.of_stepPlus_leads h_step
            (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
        · have hz34 : 34 ≤ z0 := by lin_omega
          have hzw92 : 92 ≤ z0 + w1 := by lin_omega
          rcases Nat.lt_or_ge (z0 - 3) 66 with hlt | hge
          · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R10 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + 1 + (33 - (kp + 1)) + w1 + 6 = w1 + 39 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
                (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R11 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + (33 - (kp + 1)) = 32 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              refine (bodd_leads hl1 (by omega) (by omega) (by omega)).trans ?_
              rintro d2 (⟨w2, l2, hl2, hw2, hodw2, rfl⟩ | ⟨z2, w2, l2, hl2, hw2, hz2, _, rfl⟩)
              · have hw85 : 85 ≤ w2 := by lin_omega
                have h_s2 := sp_trans (R15 w2 29 19 l2 []) (R11 14 4 w2 l2 [])
                refine Leads.of_stepPlus_leads h_s2 ?_
                exact (bodd_leads hl2 (by omega) (by omega) (by omega)).trans
                  (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
              · have hz90 : 90 ≤ z2 := by lin_omega
                have h2 : Bounce w2 l2 [z2, 32, 19] =
                    Bounce w2 l2 (((2 * (27 + 5) + (z2 - 67)) + 3) :: (27 + 5) :: [19]) := by
                  congr 1; congr 1; omega
                rw [h2]
                have h_s2 := sp_trans
                  (sp_trans (R15 w2 (2 * (27 + 5) + (z2 - 67)) (27 + 5) l2 [19])
                    (R9 27 (z2 - 67) w2 l2 [19]))
                  (R14 27 4 ((z2 - 67, w2) :: l2))
                exact (Advances.of_stepPlus h_s2
                  (root_of_5 (validL_cons (by omega) (validL_cons hw2 hl2)))).to_leads
          · have h1 : Bounce w1 l1 [z0, 33, 19] =
                Bounce w1 l1 (((2 * (28 + 5) + (z0 - 69)) + 3) :: (28 + 5) :: [19]) := by
              congr 1; congr 1; omega
            rw [h1]
            have h_step := sp_trans
              (sp_trans (R15 w1 (2 * (28 + 5) + (z0 - 69)) (28 + 5) l1 [19])
                (R9 28 (z0 - 69) w1 l1 [19]))
              (R14 28 4 ((z0 - 69, w1) :: l1))
            exact (Advances.of_stepPlus h_step
              (root_of_5 (validL_cons (by omega) (validL_cons hw1 hl1)))).to_leads
      · exact (Advances.of_stepPlus (sp_trans (R5 29 z' w l' [19]) (R14 29 4 ((z', w) :: l')))
          (root_of_5 (validL_cons (by omega) (validL_cons hw hl')))).to_leads
  | succ rem ih =>
    intro j l hrem hj hl
    have hj_lt : j < 33 := by omega
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_eq : Bev j [] 33 [19] = Bev j [] (j + 1 + (32 - j)) [19] := by congr 1; omega
      rw [h_eq]
      refine Leads.of_stepPlus_leads (R4nil j (32 - j) [19]) ?_
      have e1 : j + 1 + (32 - j) = 33 := by omega
      rw [e1]
      exact ih (by omega) (by omega) validL_nil
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 j 33 w l' [19]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
      · refine Leads.of_stepPlus_leads (R7 j 33 w l' [19]) ?_
        refine (bodd_leads hl' (by omega) (by omega) (by omega)).trans ?_
        rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
        · have h_step := sp_trans (R15 w1 30 19 l1 []) (R10 15 3 w1 l1 [])
          exact Leads.of_stepPlus_leads h_step
            (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
        · have hz34 : 34 ≤ z0 := by lin_omega
          have hzw92 : 92 ≤ z0 + w1 := by lin_omega
          rcases Nat.lt_or_ge (z0 - 3) 66 with hlt | hge
          · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R10 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + 1 + (33 - (kp + 1)) + w1 + 6 = w1 + 39 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
                (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R11 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + (33 - (kp + 1)) = 32 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              refine (bodd_leads hl1 (by omega) (by omega) (by omega)).trans ?_
              rintro d2 (⟨w2, l2, hl2, hw2, hodw2, rfl⟩ | ⟨z2, w2, l2, hl2, hw2, hz2, _, rfl⟩)
              · have hw85 : 85 ≤ w2 := by lin_omega
                have h_s2 := sp_trans (R15 w2 29 19 l2 []) (R11 14 4 w2 l2 [])
                refine Leads.of_stepPlus_leads h_s2 ?_
                exact (bodd_leads hl2 (by omega) (by omega) (by omega)).trans
                  (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
              · have hz90 : 90 ≤ z2 := by lin_omega
                have h2 : Bounce w2 l2 [z2, 32, 19] =
                    Bounce w2 l2 (((2 * (27 + 5) + (z2 - 67)) + 3) :: (27 + 5) :: [19]) := by
                  congr 1; congr 1; omega
                rw [h2]
                have h_s2 := sp_trans
                  (sp_trans (R15 w2 (2 * (27 + 5) + (z2 - 67)) (27 + 5) l2 [19])
                    (R9 27 (z2 - 67) w2 l2 [19]))
                  (R14 27 4 ((z2 - 67, w2) :: l2))
                exact (Advances.of_stepPlus h_s2
                  (root_of_5 (validL_cons (by omega) (validL_cons hw2 hl2)))).to_leads
          · have h1 : Bounce w1 l1 [z0, 33, 19] =
                Bounce w1 l1 (((2 * (28 + 5) + (z0 - 69)) + 3) :: (28 + 5) :: [19]) := by
              congr 1; congr 1; omega
            rw [h1]
            have h_step := sp_trans
              (sp_trans (R15 w1 (2 * (28 + 5) + (z0 - 69)) (28 + 5) l1 [19])
                (R9 28 (z0 - 69) w1 l1 [19]))
              (R14 28 4 ((z0 - 69, w1) :: l1))
            exact (Advances.of_stepPlus h_step
              (root_of_5 (validL_cons (by omega) (validL_cons hw1 hl1)))).to_leads
      · have h_eq : Bev j ((z' + 2, w) :: l') 33 [19] =
            Bev j ((z' + 2, w) :: l') (j + 1 + (32 - j)) [19] := by congr 1; omega
        rw [h_eq]
        refine Leads.of_stepPlus_leads (R4 j (32 - j) z' w l' [19]) ?_
        have e1 : j + 1 + (32 - j) = 33 := by omega
        rw [e1]
        exact ih (by omega) (by omega) (validL_cons hw hl')

lemma bodd11_20_leads_root {l : List (ℕ × ℕ)} (hl : ValidL l) :
    Leads tm (Bodd 11 l 20 []) RootInv := by
  rcases l with _ | ⟨⟨z, w⟩, l'⟩
  · exact Leads.of_stepPlus_leads (R8nil 11 4 []) (bev_33_19_walk 33 rfl (by omega) validL_nil)
  · have hw : 27 ≤ w := validL_head hl
    have hl' : ValidL l' := validL_tail hl
    rcases z with _ | _ | z'
    · exact Leads.of_stepPlus_leads (R8a 11 20 w l' [])
        (bev_nil_leads_root hl' (by omega) (by omega))
    · refine Leads.of_stepPlus_leads (R8b 11 20 w l' []) ?_
      exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
        (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
    · exact Leads.of_stepPlus_leads (R8 11 4 z' w l' [])
        (bev_33_19_walk 33 rfl (by omega) (validL_cons hw hl'))

lemma r7_14_5_leads_root {j w : ℕ} {l' : List (ℕ × ℕ)} (hj : j ≤ 14) (hw : 27 ≤ w) (hl' : ValidL l') :
    Leads tm (Bev j ((1, w) :: l') 14 [5]) RootInv := by
  refine Leads.of_stepPlus_leads (R7 j 14 w l' [5]) ?_
  refine (bodd_leads hl' (by omega) (by omega) (by omega)).trans ?_
  rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, _, rfl⟩)
  · have h_step := sp_trans (sp_trans (R15 w1 11 5 l1 []) (R9 0 1 w1 l1 [])) (R12 0 ((1, w1) :: l1))
    exact (Advances.of_stepPlus h_step (root_of_5 (validL_cons hw1 hl1))).to_leads
  · have hz34 : 34 ≤ z0 := by lin_omega
    have h1 : Bounce w1 l1 [z0, 14, 5] =
        Bounce w1 l1 (((2 * (9 + 5) + (z0 - 31)) + 3) :: (9 + 5) :: [5]) := by
      congr 1; congr 1; omega
    rw [h1]
    have h_step := sp_trans
      (sp_trans (R15 w1 (2 * (9 + 5) + (z0 - 31)) (9 + 5) l1 [5])
        (R9 9 (z0 - 31) w1 l1 [5]))
      (R13 9 ((z0 - 31, w1) :: l1))
    exact Leads.of_stepPlus_leads h_step (bodd11_20_leads_root (validL_cons hw1 hl1))

lemma bev_14_5_walk (rem : ℕ) : ∀ {j : ℕ} {l : List (ℕ × ℕ)},
    rem = 14 - j → j ≤ 14 → ValidL l → Leads tm (Bev j l 14 [5]) RootInv := by
  induction rem with
  | zero =>
    intro j l hrem hj hl
    have hj14 : j = 14 := by omega
    subst hj14
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · exact Leads.of_stepPlus_leads (sp_trans (R5nil 10 [5]) (R13 10 []))
        (bodd12_21_leads_root validL_nil)
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 14 14 w l' [5]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_5_leads_root (by lin_omega) hd)
      · exact r7_14_5_leads_root (by omega) hw hl'
      · exact Leads.of_stepPlus_leads (sp_trans (R5 10 z' w l' [5]) (R13 10 ((z', w) :: l')))
          (bodd12_21_leads_root (validL_cons hw hl'))
  | succ rem ih =>
    intro j l hrem hj hl
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_eq : Bev j [] 14 [5] = Bev j [] (j + 1 + (13 - j)) [5] := by congr 1; omega
      rw [h_eq]
      refine Leads.of_stepPlus_leads (R4nil j (13 - j) [5]) ?_
      have e1 : j + 1 + (13 - j) = 14 := by omega
      rw [e1]
      exact ih (by omega) (by omega) validL_nil
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 j 14 w l' [5]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_5_leads_root (by lin_omega) hd)
      · exact r7_14_5_leads_root hj hw hl'
      · have h_eq : Bev j ((z' + 2, w) :: l') 14 [5] =
            Bev j ((z' + 2, w) :: l') (j + 1 + (13 - j)) [5] := by congr 1; omega
        rw [h_eq]
        refine Leads.of_stepPlus_leads (R4 j (13 - j) z' w l' [5]) ?_
        have e1 : j + 1 + (13 - j) = 14 := by omega
        rw [e1]
        exact ih (by omega) (by omega) (validL_cons hw hl')

lemma bev0_ge18_leads_root {M : ℕ} {l : List (ℕ × ℕ)} (hM18 : 18 ≤ M) (hl : ValidL l) :
    Leads tm (Bev 0 l (2 * M + 4) [M]) RootInv := by
  refine (bev_leads hl (by omega) (by omega)).trans ?_
  rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
  · have h_eq : Bounce w1 l1 [M] = Bounce w1 l1 [(M - 15) + 15] := by
      congr 1; congr 1; omega
    rw [h_eq]
    exact (Advances.of_stepPlus (R14 w1 (M - 15) l1) (root_of_5 (validL_cons hw1 hl1))).to_leads
  · have hz34 : 34 ≤ z0 := by lin_omega
    rcases Nat.lt_or_ge (z0 - 3) (2 * M) with hlt | hge
    · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
      · have h1 : Bounce w1 l1 [z0, M] =
            Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (M - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (M - (kp + 1))) l1 [])
          (R10 kp (M - (kp + 1)) w1 l1 [])
        have e1 : kp + 1 + (M - (kp + 1)) + w1 + 6 = M + w1 + 6 := by omega
        rw [e1] at h_step
        exact Leads.of_stepPlus_leads h_step
          (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
      · have hM21 : 21 ≤ M := by lin_omega
        have h1 : Bounce w1 l1 [z0, M] =
            Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (M - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (M - (kp + 1))) l1 [])
          (R11 kp (M - (kp + 1)) w1 l1 [])
        have e1 : kp + (M - (kp + 1)) = M - 1 := by omega
        rw [e1] at h_step
        refine Leads.of_stepPlus_leads h_step ?_
        rcases Nat.lt_or_ge M 35 with hsmall | hbig
        · exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
            (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
        · exact (loop_leads hl1 (by omega) (by omega) (by omega)
            (tx := 34) (tdw := 29) (txw := 63) (by omega) rfl (by omega)
            (by lin_omega) (by lin_omega) (by lin_omega) (by lin_omega)).trans
            (fun _ hd => exit_nil_leads_root (by omega) hd)
    · have h_step := sp_trans
        (sp_trans (R15 w1 (2 * ((M - 5) + 5) + (z0 - 3 - 2 * M)) ((M - 5) + 5) l1 [])
          (R9 (M - 5) (z0 - 3 - 2 * M) w1 l1 []))
        (R12 (M - 5) ((z0 - 3 - 2 * M, w1) :: l1))
      have e1 : 2 * ((M - 5) + 5) + (z0 - 3 - 2 * M) + 3 = z0 := by omega
      have e2 : (M - 5) + 5 = M := by omega
      rw [e1, e2] at h_step
      exact (Advances.of_stepPlus h_step (root_of_ge18 hM18 (validL_cons hw1 hl1))).to_leads

theorem root_advances : ∀ c, RootInv c → Advances tm c RootInv := by
  rintro _ ⟨M, l, hM_or, hl, rfl⟩
  rcases hM_or with rfl | hM18
  · rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_step : (Beq 5 []) [tm]⊢⁺ Beq 5 [(5, 31)] := by
        refine sp_trans (R1nil 0) ?_
        refine sp_trans (bev0_nil_bounce 10 [5]) ?_
        refine sp_trans (R13 10 []) ?_
        refine sp_trans (R8nil 12 4 []) ?_
        refine sp_trans (bev0_nil_bounce 31 [20]) ?_
        exact R14 31 5 []
      exact Advances.of_stepPlus h_step (root_of_5 (validL_cons (by omega) validL_nil))
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · exact Advances.of_stepPlus_leads (R2 5 w l')
          (bev_nil_leads_root hl' (Nat.le_refl _) (by omega))
      · refine Advances.of_stepPlus_leads (R3 5 w l') ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_5_leads_root (by lin_omega) hd)
      · exact Advances.of_stepPlus_leads (R1 0 z' w l')
          (bev_14_5_walk 14 rfl (by omega) (validL_cons hw hl'))
  · rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_eq : Beq M [] = Beq ((M - 5) + 5) [] := by congr 1; omega
      rw [h_eq]
      refine Advances.of_stepPlus_leads (R1nil (M - 5)) ?_
      have e1 : (M - 5) + 5 = M := by omega
      rw [e1]
      exact bev0_ge18_leads_root hM18 validL_nil
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · exact Advances.of_stepPlus_leads (R2 M w l')
          (bev_nil_leads_root hl' (Nat.le_refl _) (by omega))
      · refine Advances.of_stepPlus_leads (R3 M w l') ?_
        rcases Nat.lt_or_ge M 35 with hsmall | hbig
        · exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
            (fun _ hd => exit_single_forced_r9 hM18 (by lin_omega) hd)
        · exact (loop_leads hl' (by omega) (by omega) (by omega)
            (tx := 34) (tdw := 29) (txw := 63) (by omega) rfl (by omega)
            (by omega) (by omega) (by omega) (by omega)).trans
            (fun _ hd => exit_nil_leads_root (by omega) hd)
      · have h_eq : Beq M ((z' + 2, w) :: l') = Beq ((M - 5) + 5) ((z' + 2, w) :: l') := by
          congr 1; omega
        rw [h_eq]
        refine Advances.of_stepPlus_leads (R1 (M - 5) z' w l') ?_
        have e1 : (M - 5) + 5 = M := by omega
        rw [e1]
        exact bev0_ge18_leads_root hM18 (validL_cons hw hl')

lemma fixed64 (Lrem : T) :
    (K qA (([0, 1, 1] : List (Fin 2)) ^ 4 +> Lrem) 0 default) [tm]⊢^{64}
      K qB (([1] : List (Fin 2)) ^ 10 +> Lrem) 1 (([1] : List (Fin 2)) ^ 4 +> default) := by
  run_steps 64

lemma bev3_nil_to_bodd0 :
    (Bev 3 [] 3 [4]) [tm]⊢⁺ Bodd 0 [] 9 [] := by
  unfold Bev Bodd
  rw [encL_nil, show (([1] : List (Fin 2)) ^ (2 * 3 + 1) +> (default : T)) =
    ([1] : List (Fin 2)) ^ (2 * 3 + 1) +> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default) by simp]
  refine sp_trans (b1_three_zeros 6 default (([1] : List (Fin 2)) ^ 3 +> encS [4])) ?_
  refine ss_sp_trans (a0_cascade 3 ((0 : Fin 2) >> default) (encS [4])) ?_
  simp only [z_cons_def, encS_cons, encS_nil]
  exact stepN_to_sp (n := 82) (by decide) (by run_steps 82)

lemma bounce7_to_beq0 :
    (Bounce 7 [] [8]) [tm]⊢⁺ Beq 0 [(5, 7)] := by
  unfold Bounce Beq
  rw [encL_nil, encL_cons, encL_nil, encS_cons, encS_nil]
  exact stepN_to_sp (n := 14) (by decide) (by run_steps 14)

lemma beq0_to_bev0 :
    (Beq 0 [(5, 7)]) [tm]⊢⁺ Bev 0 [(3, 7)] 4 [] := by
  unfold Beq Bev
  rw [encL_cons, encL_cons, encL_nil, encS_nil]
  exact stepN_to_sp (n := 19) (by decide) (by run_steps 19)

lemma amega_to_bev0 (z w : ℕ) (l : List (ℕ × ℕ)) :
    (Amega z w l 4 []) [tm]⊢⁺ Bev 0 ((z, w) :: l) 3 [] := by
  unfold Amega Bev
  rw [encL_cons, zeros1, ones1 3, encS_nil]
  exact stepN_to_sp (n := 1) (by decide) (by run_steps 1)

lemma bev3_to_beq4 (z w : ℕ) (l' : List (ℕ × ℕ)) :
    (Bev 3 ((z + 2, w) :: l') 3 []) [tm]⊢⁺ Beq 4 ((z, w) :: l') := by
  unfold Bev Beq
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_nil]
  refine sp_trans (b1_three_zeros 6 _ _) ?_
  refine ss_sp_trans (a0_cascade 3 _ default) ?_
  exact stepN_to_sp (n := 64) (by decide) (fixed64 _)

lemma beq4_to_bev0 (z w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq 4 ((z + 2, w) :: l')) [tm]⊢⁺ Bev 0 ((z, w) :: l') 12 [4] := by
  unfold Beq Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_cons, encS_nil]
  have e0 : 2 * 4 + 2 = 9 + 1 := rfl
  rw [e0]
  refine sp_trans (b1_three_zeros 9 _ _) ?_
  have e1 : 9 + 1 = (2 * 3 + 1) + 3 := rfl
  rw [e1, zeros3']
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  set Y : T := (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l'))) with hY
  refine sp_trans (a0_odd_zeros 3 0 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine sp_trans (ebounce_zero 3 ((0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (a0_cascade 3 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (stepN_to_ss (fixed64 _)) ?_
  rw [hY]
  have h := b1_two_zeros_one 10 ((1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (([1] : List (Fin 2)) ^ 4 +> default)
  simp only [Nat.mul_zero, Nat.zero_add, ones_one]
  exact h

lemma bounce8_to_beq0 (l : List (ℕ × ℕ)) :
    (Bounce 8 l [4]) [tm]⊢⁺ Beq 0 ((1, 8) :: l) := by
  unfold Bounce Beq
  rw [encL_cons, encS_cons, encS_nil]
  exact stepN_to_sp (n := 10) (by decide) (by run_steps 10)

lemma bodd_s0_eq_nil (k : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) :
    Bodd k l m [0] = Bodd k l m [] := by
  unfold Bodd
  rw [encS_cons, encS_nil, p_zero_list, lb_append_nil, z_cons_def]

def c0_756 : Cfg (Fin 2) (Fin 6) := K qD default 0 default

theorem entry_756_part1 : c0_756 [tm]⊢⁺ Bodd 8 [] 18 [4] := by
  have h50 : c0_756 [tm]⊢^{50} Bev 0 [] 3 [4] := by
    unfold c0_756 Bev; rw [encL_nil, encS_cons, encS_nil]; run_steps 50
  refine sp_trans (stepN_to_sp (by decide) h50) ?_
  refine ss_sp_trans (R4nil_iter 3 0 0 [4]) ?_
  refine sp_trans bev3_nil_to_bodd0 ?_
  refine sp_trans (R8nil 0 4 []) ?_
  refine sp_trans (bev0_nil_bounce 7 [8]) ?_
  refine sp_trans bounce7_to_beq0 ?_
  refine sp_trans beq0_to_bev0 ?_
  refine sp_trans (R4 0 3 1 7 [] []) ?_
  exact R7 1 4 7 [] []

theorem entry_756_part2 : (Bodd 8 [] 18 [4]) [tm]⊢⁺ Bodd 27 [] 42 [4] := by
  refine sp_trans (R8nil 8 5 [4]) ?_
  refine sp_trans (bev0_nil_bounce 23 [17, 4]) ?_
  refine sp_trans (R15 23 14 4 [] []) ?_
  refine sp_trans (amega_to_bev0 14 23 []) ?_
  refine ss_sp_trans (R4_iter 3 0 0 8 23 [] []) ?_
  refine sp_trans (bev3_to_beq4 6 23 []) ?_
  refine sp_trans (beq4_to_bev0 4 23 []) ?_
  refine ss_sp_trans (R4_iter 2 0 10 0 23 [] [4]) ?_
  exact R6 2 12 23 [] [4]

theorem entry_756_part3 : (Bodd 27 [] 42 [4]) [tm]⊢⁺ Bodd 9 [(2, 61)] 18 [] := by
  refine sp_trans (R8nil 27 10 [4]) ?_
  refine sp_trans (bev0_nil_bounce 61 [41, 4]) ?_
  refine sp_trans (R15 61 38 4 [] []) ?_
  refine sp_trans (amega_to_bev0 38 61 []) ?_
  refine ss_sp_trans (R4_iter 3 0 0 32 61 [] []) ?_
  refine sp_trans (bev3_to_beq4 30 61 []) ?_
  refine sp_trans (beq4_to_bev0 28 61 []) ?_
  refine ss_sp_trans (R4_iter 12 0 0 4 61 [] [4]) ?_
  refine sp_trans (R5 8 2 61 [] [4]) ?_
  refine sp_trans (bounce8_to_beq0 [(2, 61)]) ?_
  rw [← bodd_s0_eq_nil 9 [(2, 61)] 18]
  exact R3 0 8 [(2, 61)]

theorem entry_756_part4 : (Bodd 9 [(2, 61)] 18 []) [tm]⊢⁺ Beq 5 [(2, 33), (118, 275)] := by
  refine sp_trans (R8 9 4 0 61 [] []) ?_
  refine sp_trans (R6 0 29 61 [] [17]) ?_
  refine sp_trans (R8nil 63 29 [17]) ?_
  refine sp_trans (bev0_nil_bounce 133 [96, 17]) ?_
  refine sp_trans (R15 133 93 17 [] []) ?_
  refine sp_trans (R9 12 59 133 [] []) ?_
  refine sp_trans (R12 12 [(59, 133)]) ?_
  refine sp_trans (R1 12 57 133 []) ?_
  refine ss_sp_trans (R4_iter 28 0 10 1 133 [] [17]) ?_
  refine sp_trans (R7 28 38 133 [] [17]) ?_
  refine sp_trans (R8nil 134 59 [38, 17]) ?_
  refine sp_trans (bev0_nil_bounce 275 [197, 38, 17]) ?_
  refine sp_trans (R15 275 194 38 [] [17]) ?_
  refine sp_trans (R9 33 118 275 [] [17]) ?_
  exact R14 33 2 [(118, 275)]

theorem entry_756 : c0_756 [tm]⊢⁺ Beq 5 [(2, 33), (118, 275)] :=
  sp_trans entry_756_part1 (sp_trans entry_756_part2 (sp_trans entry_756_part3 entry_756_part4))

-- E1 Table Isomorphism Bridge from `target_tm` (#756) to `tm` (#240)
def sigma756 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | 5 => 0

def flipTape (t : Tape (Fin 2)) : Tape (Fin 2) :=
  ⟨t.1, t.3, t.2⟩

def mapCfg756 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map sigma756, flipTape c.tape⟩

lemma mapCfg756_init : mapCfg756 (init ([] : List (Fin 2))) = c0_756 := rfl

lemma fin6_cases (P : Fin 6 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ q : Fin 6, P q
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4
  | ⟨5, _⟩ => h5
  | ⟨n + 6, h⟩ => by omega

lemma fin2_cases (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : ∀ a : Fin 2, P a
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨n + 2, h⟩ => by omega

lemma step_mapCfg756 (c c' : Cfg (Fin 2) (Fin 6)) (h : c [target_tm]⊢ c') :
    (mapCfg756 c) [tm]⊢ (mapCfg756 c') := by
  rcases c with ⟨_ | q, ⟨hd, l, r⟩⟩
  · cases h
  · revert h
    refine fin6_cases (fun q =>
      (⟨some q, ⟨hd, l, r⟩⟩ [target_tm]⊢ c') →
      ((mapCfg756 ⟨some q, ⟨hd, l, r⟩⟩) [tm]⊢ (mapCfg756 c'))) ?_ ?_ ?_ ?_ ?_ ?_ q
    all_goals
      refine fin2_cases (fun hd =>
        (⟨some _, ⟨hd, l, r⟩⟩ [target_tm]⊢ c') →
        ((mapCfg756 ⟨some _, ⟨hd, l, r⟩⟩) [tm]⊢ (mapCfg756 c'))) ?_ ?_ hd
      all_goals
        intro h; cases h <;> rfl

lemma multiStep_mapCfg756 (n : ℕ) : ∀ (c c' : Cfg (Fin 2) (Fin 6)),
    (c [target_tm]⊢^{n} c') → ((mapCfg756 c) [tm]⊢^{n} (mapCfg756 c')) := by
  induction n with
  | zero =>
    intro c c' h
    rw [ms_zero] at h ⊢
    cases h; rfl
  | succ n ih =>
    intro c c' h
    rw [ms_succ, Option.bind_eq_some_iff] at h
    rcases h with ⟨c_mid, h1, h2⟩
    exact ms_trans tm _ _ _ n 1 (ih c c_mid h1) (step_mapCfg756 c_mid c' h2)

lemma stepStar_mapCfg756 {c c' : Cfg (Fin 2) (Fin 6)} (h : c [target_tm]⊢* c') :
    (mapCfg756 c) [tm]⊢* (mapCfg756 c') := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, multiStep_mapCfg756 n c c' hn⟩

lemma step_isNone_mapCfg756 (c : Cfg (Fin 2) (Fin 6))
    (h : (step target_tm c).isNone) : (step tm (mapCfg756 c)).isNone := by
  rcases c with ⟨_ | q, ⟨hd, l, r⟩⟩
  · rfl
  · revert h
    refine fin6_cases (fun q =>
      (step target_tm ⟨some q, ⟨hd, l, r⟩⟩).isNone →
      (step tm (mapCfg756 ⟨some q, ⟨hd, l, r⟩⟩)).isNone) ?_ ?_ ?_ ?_ ?_ ?_ q
    all_goals
      refine fin2_cases (fun hd =>
        (step target_tm ⟨some _, ⟨hd, l, r⟩⟩).isNone →
        (step tm (mapCfg756 ⟨some _, ⟨hd, l, r⟩⟩)).isNone) ?_ ?_ hd
      all_goals
        intro h; first | rfl | cases h

end M240

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  have h_inv0 : M240.RootInv (M240.Beq 5 [(2, 33), (118, 275)]) :=
    M240.root_of_5 (M240.validL_cons (by omega) (M240.validL_cons (by omega) M240.validL_nil))
  intro cfg ⟨n, hn⟩
  cases h_step : step target_tm cfg with
  | some _ => rfl
  | none =>
    have h_ms : M240.c0_756 [M240.tm]⊢^{n} M240.mapCfg756 cfg := by
      rw [← M240.mapCfg756_init]
      exact M240.multiStep_mapCfg756 n (init []) cfg hn
    have h_halt_c0 : BusyBeaver.Excursion.HaltsIn M240.tm M240.c0_756 n :=
      ⟨M240.mapCfg756 cfg, h_ms, M240.step_isNone_mapCfg756 cfg (by simp [h_step])⟩
    rcases BusyBeaver.Excursion.haltsIn_reduce_stepStar
      (M240.sp_to_ss M240.entry_756) h_halt_c0 with ⟨m, _, h_halt_m⟩
    exact False.elim (BusyBeaver.Excursion.not_haltsIn_of_advances
      M240.root_advances m _ h_inv0 h_halt_m)

end BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF
