/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LE_1LC1RD_1LA0LC_1RA1RE_0RF0RB_1LC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LE_1LC1RD_1LA0LC_1RA1RE_0RF0RB_1LC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1LC1RD_1LA0LC_1RA1RE_0RF0RB_1LCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LE_1LC1RD_1LA0LC_1RA1RE_0RF0RB_1LC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4

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
    c₁ [tm]⊢^{n + m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma multiStep_step {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : Nat}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢^{n} c₃) : c₁ [tm]⊢^{n + 1} c₃ := by
  have := multiStep_trans tm c₁ c₂ c₃ 1 n h₁ h₂
  rwa [Nat.add_comm 1 n] at this

lemma stepStar_refl (c : Cfg (Fin 2) (Fin 6)) : c [target_tm]⊢* c := ⟨0, rfl⟩

lemma stepPlus_to_stepStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [target_tm]⊢⁺ c₂) :
    c₁ [target_tm]⊢* c₂ := by
  rcases h with ⟨n, _, hn⟩; exact ⟨n, hn⟩

lemma stepPlus_stepStar_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢⁺ c₂) (h₂ : c₂ [target_tm]⊢* c₃) : c₁ [target_tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn_pos, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, Nat.add_pos_left hn_pos m, multiStep_trans target_tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢* c₂) (h₂ : c₂ [target_tm]⊢⁺ c₃) : c₁ [target_tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm_pos, hm⟩
  exact ⟨n + m, Nat.add_pos_right n hm_pos, multiStep_trans target_tm c₁ c₂ c₃ n m hn hm⟩

omit [Inhabited Γ] in
@[simp] lemma pow_zero_list (l : List Γ) : l ^ (0 : Nat) = [] := rfl

omit [Inhabited Γ] in
lemma pow_succ_list (l : List Γ) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl

omit [Inhabited Γ] in
@[simp] lemma list_pow_add (l : List Γ) (n m : Nat) : l ^ (n + m) = l ^ n ++ l ^ m := by
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
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) :=
  Turing.ListBlank.append_assoc l₁ l₂ s

lemma left_pow_add (l : ListBlank (Fin 2)) (u : List (Fin 2)) (n m : Nat) :
    l <+ u ^ (n + m) = l <+ u ^ m <+ u ^ n := by
  rw [list_pow_add, listblank_append_assoc]

lemma left_pow_succ (l : ListBlank (Fin 2)) (u : List (Fin 2)) (n : Nat) :
    l <+ u ^ (n + 1) = l <+ u ^ n <+ u := by
  rw [pow_succ_list, listblank_append_assoc]

lemma left_pow_succ_right (l : ListBlank (Fin 2)) (u : List (Fin 2)) (n : Nat) :
    l <+ u ^ (n + 1) = l <+ u <+ u ^ n := by
  rw [pow_succ_right, listblank_append_assoc]

lemma right_pow_add (u : List (Fin 2)) (n m : Nat) (r : ListBlank (Fin 2)) :
    u ^ (n + m) +> r = u ^ n +> (u ^ m +> r) := by
  rw [list_pow_add, listblank_append_assoc]

lemma right_pow_succ (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    u ^ (n + 1) +> r = u +> (u ^ n +> r) := by
  rw [pow_succ_list, listblank_append_assoc]

lemma right_pow_succ_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    u ^ (n + 1) +> r = u ^ n +> (u +> r) := by
  rw [pow_succ_right, listblank_append_assoc]

@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

@[simp] lemma zero_cons_default : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default := by
  change ListBlank.cons default default = default
  exact ListBlank.cons_head_tail default

@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
    ⟨some A, ⟨0, default, default⟩⟩ := rfl

def ones : List (Fin 2) := [1]
def ld0 : List (Fin 2) := [0, 1, 1, 0, 1, 1]
def ld1 : List (Fin 2) := [0, 1, 1, 1, 1, 1]
def ldh : ListBlank (Fin 2) := default <+ [1]
def rd0 : List (Fin 2) := [0, 0, 0]
def rd1 : List (Fin 2) := [1, 0, 0]
def Half (b : Fin 2) : List (Fin 2) := [b, 1, 1]
def Opp (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0
def Marked : List (Fin 2) → List (Fin 2)
  | [] => []
  | b :: bs => Half b ++ Half 1 ++ Marked bs
def s_tag : List (Fin 2) := [1, 0, 1, 1]
def t_tag : List (Fin 2) := [1, 1, 1, 1]
def cut_tag : List (Fin 2) := [0, 1, 1, 1]

lemma fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  rcases b with ⟨_ | ⟨_ | n⟩, hlt⟩
  · left; rfl
  · right; rfl
  · omega

macro "step1" : tactic => `(tactic| (
  try simp only [init_nil, ones, ld0, ld1, ldh, rd0, rd1, Half, Opp, s_tag, t_tag, cut_tag,
    pow_succ_list, pow_zero_list,
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
  simp only [ones, ld0, ld1, ldh, rd0, rd1, Half, Opp, s_tag, t_tag, cut_tag,
    pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail, multiStep_zero]
  rfl))

-- ============================================================================
-- Section 1: Word & Power Commutation Identities
-- ============================================================================

lemma left_ld0_eq (l : ListBlank (Fin 2)) : l <+ ld0 = l <+ Half 0 <+ Half 0 := rfl
lemma left_ld1_eq (l : ListBlank (Fin 2)) : l <+ ld1 = l <+ Half 1 <+ Half 0 := rfl

lemma half0_pairs (n : Nat) : (Half 0) ^ (n * 2) = ld0 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show (n + 1) * 2 = 2 + n * 2 by omega, list_pow_add, ih]
    rfl

lemma half0_pairs_two_mul (n : Nat) : (Half 0) ^ (2 * n) = ld0 ^ n := by
  rw [Nat.mul_comm 2 n, half0_pairs]

lemma half0_comm_ld0_pow (n : Nat) (l : ListBlank (Fin 2)) :
    l <+ ld0 ^ n <+ Half 0 = l <+ Half 0 <+ ld0 ^ n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [left_pow_succ_right l ld0 n, ih (l <+ ld0), left_pow_succ_right (l <+ Half 0) ld0 n]
    rfl

lemma one_comm_half1_pow (n : Nat) (l : ListBlank (Fin 2)) :
    l <+ (Half 1) ^ n <+ [1] = l <+ [1] <+ (Half 1) ^ n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [left_pow_succ_right l (Half 1) n, ih (l <+ Half 1), left_pow_succ_right (l <+ [1]) (Half 1) n]
    rfl

lemma one_comm_ones_pow (n : Nat) (r : ListBlank (Fin 2)) :
    ones ^ n +> ([1] +> r) = [1] +> (ones ^ n +> r) := by
  change ones ^ n +> (ones +> r) = ones +> (ones ^ n +> r)
  rw [← right_pow_succ_right, ← right_pow_succ]

-- ============================================================================
-- Section 2: Constant-Step & Inductive Machine Rules (TM4)
-- ============================================================================

lemma LInc_zero (l r : ListBlank (Fin 2)) :
    ((l <+ ld0) <{{C}} r) [target_tm]⊢⁺ ((l <+ ld1) {{B}}> r) :=
  ⟨9, by omega, by run_steps 9⟩

lemma RInc_zero (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0] +> r)) [target_tm]⊢⁺ (l <{{C}} ([1] +> r)) :=
  ⟨1, by omega, by run_steps 1⟩

lemma ECarry (l r : ListBlank (Fin 2)) (b : Fin 2) :
    ((l <+ Half 1 <+ Half b) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    (l <{{E}} ([0] +> (ones ^ 6 +> r))) := by
  rcases fin2_cases b with rfl | rfl
  · exact ⟨12, by omega, by run_steps 12⟩
  · exact ⟨12, by omega, by run_steps 12⟩

lemma EStop (l r : ListBlank (Fin 2)) (b : Fin 2) :
    ((l <+ Half 0 <+ Half b) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 1 <+ s_tag) {{D}}> r) := by
  rcases fin2_cases b with rfl | rfl
  · exact ⟨12, by omega, by run_steps 12⟩
  · exact ⟨12, by omega, by run_steps 12⟩

lemma SOnes_step (l r : ListBlank (Fin 2)) :
    ((l <+ s_tag) {{D}}> (ones ^ 6 +> r)) [target_tm]⊢⁺
    ((l <+ ld0 <+ s_tag) {{D}}> r) :=
  ⟨6, by omega, by run_steps 6⟩

lemma SOnes (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ s_tag) {{D}}> (ones ^ (n * 6) +> r)) [target_tm]⊢*
    ((l <+ ld0 ^ n <+ s_tag) {{D}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [show (n + 1) * 6 = 6 + n * 6 by omega, right_pow_add ones 6 (n * 6) r,
        left_pow_succ_right l ld0 n]
    exact stepStar_trans (stepPlus_to_stepStar (SOnes_step l (ones ^ (n * 6) +> r))) (ih (l <+ ld0))

lemma S100 (l r : ListBlank (Fin 2)) :
    ((l <+ s_tag) {{D}}> ([1, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 1 <+ s_tag) {{D}}> r) :=
  ⟨13, by omega, by run_steps 13⟩

lemma T100 (l r : ListBlank (Fin 2)) :
    ((l <+ t_tag) {{D}}> ([1, 0, 0] +> r)) [target_tm]⊢⁺
    (l <{{E}} ([0] +> (ones ^ 6 +> r))) :=
  ⟨13, by omega, by run_steps 13⟩

lemma S000 (l r : ListBlank (Fin 2)) (b : Fin 2) :
    ((l <+ Half b <+ s_tag) {{D}}> ([0, 0, 0] +> r)) [target_tm]⊢⁺
    (l <{{E}} ([0] +> (ones ^ 5 +> ([Opp b, 0, 0, 1] +> r)))) := by
  rcases fin2_cases b with rfl | rfl
  · exact ⟨26, by omega, by run_steps 26⟩
  · exact ⟨16, by omega, by run_steps 16⟩

lemma S000_end (l r : ListBlank (Fin 2)) (b : Fin 2) :
    ((l <+ s_tag) {{D}}> (ones ^ 5 +> ([Opp b, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((l <+ Half 0 <+ Half b <+ Half 0 <+ t_tag) {{D}}> r) := by
  rcases fin2_cases b with rfl | rfl
  · exact ⟨9, by omega, by run_steps 9⟩
  · exact ⟨19, by omega, by run_steps 19⟩

lemma MarkedCarry (l r : ListBlank (Fin 2)) (bs : List (Fin 2)) :
    ((l <+ Marked bs) <{{E}} ([0] +> r)) [target_tm]⊢*
    (l <{{E}} ([0] +> (ones ^ (bs.length * 6) +> r))) := by
  induction bs generalizing l r with
  | nil => exact stepStar_refl _
  | cons b bs ih =>
    have hM : l <+ Marked (b :: bs) = l <+ Marked bs <+ Half 1 <+ Half b := by
      simp [Marked, List.append_assoc]
    rw [hM, List.length_cons, show (bs.length + 1) * 6 = bs.length * 6 + 6 by omega,
        right_pow_add ones (bs.length * 6) 6 r]
    exact stepStar_trans (stepPlus_to_stepStar (ECarry (l <+ Marked bs) r b)) (ih l (ones ^ 6 +> r))

lemma ECarry_ld1 (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ ld1 ^ n) <{{E}} ([0] +> r)) [target_tm]⊢*
    (l <{{E}} ([0] +> (ones ^ (n * 6) +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [left_pow_succ l ld1 n, left_ld1_eq, show (n + 1) * 6 = n * 6 + 6 by omega,
        right_pow_add ones (n * 6) 6 r]
    exact stepStar_trans (stepPlus_to_stepStar (ECarry (l <+ ld1 ^ n) r 0)) (ih (ones ^ 6 +> r))

lemma ECarry_half1_pair (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ (Half 1) ^ (n * 2)) <{{E}} ([0] +> r)) [target_tm]⊢*
    (l <{{E}} ([0] +> (ones ^ (n * 6) +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [show (n + 1) * 2 = 2 + n * 2 by omega, left_pow_add l (Half 1) 2 (n * 2),
        show (Half 1) ^ 2 = Half 1 ++ Half 1 by rfl, listblank_append_assoc,
        show (n + 1) * 6 = n * 6 + 6 by omega, right_pow_add ones (n * 6) 6 r]
    exact stepStar_trans (stepPlus_to_stepStar (ECarry (l <+ (Half 1) ^ (n * 2)) r 1)) (ih (ones ^ 6 +> r))

lemma TStart (l r : ListBlank (Fin 2)) :
    ((l <+ t_tag) {{D}}> ([0, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 1 <+ Half 1) <{{C}} ([1] +> r)) :=
  ⟨3, by omega, by run_steps 3⟩

lemma LOnes_step (l r : ListBlank (Fin 2)) :
    ((l <+ Half 1) <{{C}} r) [target_tm]⊢⁺
    (l <{{C}} (rd0 +> r)) :=
  ⟨3, by omega, by run_steps 3⟩

lemma LOnes (l r : ListBlank (Fin 2)) (h : Nat) :
    ((l <+ (Half 1) ^ h) <{{C}} r) [target_tm]⊢*
    (l <{{C}} (rd0 ^ h +> r)) := by
  induction h generalizing r with
  | zero => exact stepStar_refl _
  | succ h ih =>
    rw [left_pow_succ l (Half 1) h, right_pow_succ_right rd0 h r]
    exact stepStar_trans (stepPlus_to_stepStar (LOnes_step (l <+ (Half 1) ^ h) r)) (ih (rd0 +> r))

lemma TZeroEntry (l r : ListBlank (Fin 2)) (h : Nat) :
    ((l <+ Half 0 <+ (Half 1) ^ h <+ t_tag) {{D}}> ([0, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 0) <{{C}} (rd0 ^ (h + 2) +> ([1] +> r))) := by
  have s1 := TStart (l <+ Half 0 <+ (Half 1) ^ h) r
  have s2 := LOnes (l <+ Half 0) ([1] +> r) (h + 2)
  have heq : l <+ Half 0 <+ (Half 1) ^ (h + 2) =
      l <+ Half 0 <+ (Half 1) ^ h <+ Half 1 <+ Half 1 := by
    rw [show h + 2 = 2 + h by omega, left_pow_add (l <+ Half 0) (Half 1) 2 h,
        show (Half 1) ^ 2 = Half 1 ++ Half 1 by rfl, listblank_append_assoc]
  rw [heq] at s2
  exact stepPlus_stepStar_trans s1 s2

lemma LBAtoE (l r : ListBlank (Fin 2)) :
    ((l <+ Half 1 <+ Half 0) <{{C}} r) [target_tm]⊢⁺
    (l <{{E}} ([0] +> (ones ^ 5 +> r))) :=
  ⟨10, by omega, by run_steps 10⟩

lemma SFive (l r : ListBlank (Fin 2)) :
    ((l <+ s_tag) {{D}}> (ones ^ 5 +> r)) [target_tm]⊢⁺
    ((l <+ Half 0 <+ Half 0 <+ Half 0) {{B}}> r) :=
  ⟨5, by omega, by run_steps 5⟩

lemma R100Scan_step (l r : ListBlank (Fin 2)) :
    (l {{B}}> (rd1 +> r)) [target_tm]⊢⁺
    ((l <+ Half 1) {{B}}> r) :=
  ⟨3, by omega, by run_steps 3⟩

lemma R100Scan (l r : ListBlank (Fin 2)) (n : Nat) :
    (l {{B}}> (rd1 ^ n +> r)) [target_tm]⊢*
    ((l <+ (Half 1) ^ n) {{B}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [right_pow_succ rd1 n r, left_pow_succ_right l (Half 1) n]
    exact stepStar_trans (stepPlus_to_stepStar (R100Scan_step l (rd1 ^ n +> r))) (ih (l <+ Half 1))

lemma RExit_step (l r : ListBlank (Fin 2)) :
    ((l <+ Half 1) {{B}}> ([1] +> r)) [target_tm]⊢⁺
    ((l <+ t_tag) {{D}}> r) :=
  ⟨1, by omega, by run_steps 1⟩

lemma RExit (l r : ListBlank (Fin 2)) (h : Nat) :
    (l {{B}}> (rd1 ^ (h + 2) +> ([1] +> r))) [target_tm]⊢⁺
    ((l <+ (Half 1) ^ (h + 1) <+ t_tag) {{D}}> r) := by
  have s1 := R100Scan l ([1] +> r) (h + 2)
  rw [left_pow_succ l (Half 1) (h + 1)] at s1
  exact stepStar_stepPlus_trans s1 (RExit_step (l <+ (Half 1) ^ (h + 1)) r)

lemma R111Scan_step (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 1, 1] +> r)) [target_tm]⊢⁺
    ((l <+ Half 0) {{B}}> r) :=
  ⟨3, by omega, by run_steps 3⟩

lemma R111Scan (l r : ListBlank (Fin 2)) (n : Nat) :
    (l {{B}}> (ones ^ (n * 3) +> r)) [target_tm]⊢*
    ((l <+ (Half 0) ^ n) {{B}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [show (n + 1) * 3 = 3 + n * 3 by omega, right_pow_add ones 3 (n * 3) r,
        show ones ^ 3 = [1, 1, 1] by rfl, left_pow_succ_right l (Half 0) n]
    exact stepStar_trans (stepPlus_to_stepStar (R111Scan_step l (ones ^ (n * 3) +> r))) (ih (l <+ Half 0))

lemma RInc_rule (l r : ListBlank (Fin 2)) (n : Nat) :
    (l {{B}}> (rd1 ^ n +> ([0] +> r))) [target_tm]⊢⁺
    (l <{{C}} (rd0 ^ n +> ([1] +> r))) := by
  have s1 := R100Scan l ([0] +> r) n
  have s2 := RInc_zero (l <+ (Half 1) ^ n) r
  have s3 := LOnes l ([1] +> r) n
  exact stepStar_stepPlus_trans s1 (stepPlus_stepStar_trans s2 s3)

lemma EEven_entry (r : ListBlank (Fin 2)) :
    (ldh <{{E}} ([0] +> r)) [target_tm]⊢⁺
    (ldh {{B}}> ([1, 1] +> r)) :=
  ⟨4, by omega, by run_steps 4⟩

lemma EEven (r : ListBlank (Fin 2)) (n : Nat) :
    (ldh <{{E}} ([0] +> (ones ^ (n * 6 + 5) +> r))) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (n + 1)) {{B}}> ([1] +> r)) := by
  have s1 := EEven_entry (ones ^ (n * 6 + 5) +> r)
  have h1 : ([1, 1] : List (Fin 2)) +> (ones ^ (n * 6 + 5) +> r) =
      ones ^ (((n + 1) * 2) * 3) +> ([1] +> r) := by
    change ones ^ 2 +> (ones ^ (n * 6 + 5) +> r) =
      ones ^ (((n + 1) * 2) * 3) +> (ones +> r)
    rw [← right_pow_add, ← right_pow_succ_right]
    have : 2 + (n * 6 + 5) = (n + 1) * 2 * 3 + 1 := by omega
    rw [this]
  rw [h1] at s1
  have s2 := R111Scan ldh ([1] +> r) ((n + 1) * 2)
  rw [half0_pairs (n + 1)] at s2
  exact stepPlus_stepStar_trans s1 s2

lemma LOv (r : ListBlank (Fin 2)) (n : Nat) :
    ((ldh <+ ld1 ^ (1 + n)) <{{C}} r) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (1 + n)) {{B}}> ([1] +> r)) := by
  rw [Nat.add_comm 1 n, left_pow_succ ldh ld1 n, left_ld1_eq]
  have s1 := LBAtoE (ldh <+ ld1 ^ n) r
  have s2 := ECarry_ld1 ldh (ones ^ 5 +> r) n
  rw [← right_pow_add] at s2
  exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 (EEven r n))

lemma R1100Turn (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 1, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 0) <{{C}} ([1] +> r)) :=
  ⟨4, by omega, by run_steps 4⟩

lemma ROvOddRecover (l r : ListBlank (Fin 2)) (a m : Nat) :
    ((l <+ ld0 <+ ld1 ^ a) {{B}}> (rd1 ^ (m * 2 + 1) +> ([1, 1, 0, 0] +> r))) [target_tm]⊢⁺
    ((l <+ ld1 <+ ld0 ^ (m + a + 1)) {{B}}> ([1] +> r)) := by
  have s1 := R100Scan (l <+ ld0 <+ ld1 ^ a) ([1, 1, 0, 0] +> r) (m * 2 + 1)
  have s2 := R1100Turn (l <+ ld0 <+ ld1 ^ a <+ (Half 1) ^ (m * 2 + 1)) r
  rw [left_pow_succ (l <+ ld0 <+ ld1 ^ a) (Half 1) (m * 2)] at s2
  have s3 := LBAtoE (l <+ ld0 <+ ld1 ^ a <+ (Half 1) ^ (m * 2)) ([1] +> r)
  have s4 := ECarry_half1_pair (l <+ ld0 <+ ld1 ^ a) (ones ^ 5 +> ([1] +> r)) m
  have s5 := ECarry_ld1 (l <+ ld0) (ones ^ (m * 6) +> (ones ^ 5 +> ([1] +> r))) a
  have h_ones : ones ^ (a * 6) +> (ones ^ (m * 6) +> (ones ^ 5 +> ([1] +> r))) =
      ones ^ ((m + a) * 6) +> (ones ^ 5 +> ([1] +> r)) := by
    rw [← right_pow_add, show a * 6 + m * 6 = (m + a) * 6 by omega]
  rw [h_ones] at s5
  have s6 := EStop l (ones ^ ((m + a) * 6) +> (ones ^ 5 +> ([1] +> r))) 0
  rw [← left_ld0_eq] at s6
  have s7 := SOnes (l <+ Half 1) (ones ^ 5 +> ([1] +> r)) (m + a)
  have s8 := SFive (l <+ Half 1 <+ ld0 ^ (m + a)) ([1] +> r)
  have heq : l <+ Half 1 <+ ld0 ^ (m + a) <+ Half 0 <+ Half 0 <+ Half 0 =
      l <+ ld1 <+ ld0 ^ (m + a + 1) := by
    rw [half0_comm_ld0_pow (m + a) (l <+ Half 1), ← left_ld1_eq, ← left_ld0_eq, ← left_pow_succ (l <+ ld1) ld0 (m + a)]
  rw [heq] at s8
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepPlus_trans s3
        (stepStar_stepPlus_trans s4
          (stepStar_stepPlus_trans s5
            (stepPlus_trans s6
              (stepStar_stepPlus_trans s7 s8))))))

lemma ROvEven_entry (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 1, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ [1]) <{{E}} ([0] +> ([1, 1] +> r))) :=
  ⟨6, by omega, by run_steps 6⟩

lemma E01_exit (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 0]) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    ((l <+ [1]) {{B}}> ([1, 1] +> r)) :=
  ⟨4, by omega, by run_steps 4⟩

lemma B_four_ones_to_s (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 1, 1, 1] +> r)) [target_tm]⊢⁺
    ((l <+ s_tag) {{D}}> r) :=
  ⟨4, by omega, by run_steps 4⟩

lemma ROvEvenAux (l r : ListBlank (Fin 2)) (m : Nat) :
    ((l <+ [0]) {{B}}> (rd1 ^ (m * 2) +> ([1, 1, 0, 0] +> r))) [target_tm]⊢⁺
    ((l <+ [1] <+ ld0 ^ m <+ s_tag) {{D}}> r) := by
  have s1 := R100Scan (l <+ [0]) ([1, 1, 0, 0] +> r) (m * 2)
  have s2 := ROvEven_entry (l <+ [0] <+ (Half 1) ^ (m * 2)) r
  have h1 : l <+ [0] <+ (Half 1) ^ (m * 2) <+ [1] =
      l <+ [1, 0] <+ (Half 1) ^ (m * 2) := by
    rw [one_comm_half1_pow (m * 2) (l <+ [0])]
    rfl
  rw [h1] at s2
  have s3 := ECarry_half1_pair (l <+ [1, 0]) ([1, 1] +> r) m
  have s4 := E01_exit l (ones ^ (m * 6) +> ([1, 1] +> r))
  have h2 : ([1, 1] : List (Fin 2)) +> (ones ^ (m * 6) +> ([1, 1] +> r)) =
      ones ^ ((m * 2) * 3) +> ([1, 1, 1, 1] +> r) := by
    change ones ^ 2 +> (ones ^ (m * 6) +> (ones ^ 2 +> r)) =
      ones ^ ((m * 2) * 3) +> (ones ^ 4 +> r)
    rw [← right_pow_add, ← right_pow_add, ← right_pow_add]
    have : 2 + m * 6 + 2 = m * 2 * 3 + 4 := by omega
    rw [this]
  rw [h2] at s4
  have s5 := R111Scan (l <+ [1]) ([1, 1, 1, 1] +> r) (m * 2)
  rw [half0_pairs m] at s5
  have s6 := B_four_ones_to_s (l <+ [1] <+ ld0 ^ m) r
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4
          (stepStar_stepPlus_trans s5 s6))))

lemma ROv101Odd_entry (l r : ListBlank (Fin 2)) :
    ((l <+ Half 1) {{B}}> ([1, 0, 1] +> r)) [target_tm]⊢⁺
    ((l <+ [1]) <{{E}} ([0] +> ([1, 1, 1, 1] +> r))) :=
  ⟨11, by omega, by run_steps 11⟩

lemma ROv101Odd (l r : ListBlank (Fin 2)) (m : Nat) :
    ((l <+ [0]) {{B}}> (rd1 ^ (m * 2 + 1) +> ([1, 0, 1] +> r))) [target_tm]⊢⁺
    ((l <+ [1] <+ ld0 ^ (m + 1)) {{B}}> r) := by
  have s1 := R100Scan (l <+ [0]) ([1, 0, 1] +> r) (m * 2 + 1)
  rw [left_pow_succ (l <+ [0]) (Half 1) (m * 2)] at s1
  have s2 := ROv101Odd_entry (l <+ [0] <+ (Half 1) ^ (m * 2)) r
  have h1 : l <+ [0] <+ (Half 1) ^ (m * 2) <+ [1] =
      l <+ [1, 0] <+ (Half 1) ^ (m * 2) := by
    rw [one_comm_half1_pow (m * 2) (l <+ [0])]
    rfl
  rw [h1] at s2
  have s3 := ECarry_half1_pair (l <+ [1, 0]) ([1, 1, 1, 1] +> r) m
  have s4 := E01_exit l (ones ^ (m * 6) +> ([1, 1, 1, 1] +> r))
  have h2 : ([1, 1] : List (Fin 2)) +> (ones ^ (m * 6) +> ([1, 1, 1, 1] +> r)) =
      ones ^ (((m + 1) * 2) * 3) +> r := by
    change ones ^ 2 +> (ones ^ (m * 6) +> (ones ^ 4 +> r)) = _
    rw [← right_pow_add, ← right_pow_add]
    have : 2 + m * 6 + 4 = (m + 1) * 2 * 3 := by omega
    rw [this]
  rw [h2] at s4
  have s5 := R111Scan (l <+ [1]) r ((m + 1) * 2)
  rw [half0_pairs (m + 1)] at s5
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_stepStar_trans s4 s5)))

lemma saturated_one (r : ListBlank (Fin 2)) :
    ((ldh <+ ld0) {{B}}> ([1] +> (rd0 +> (rd1 +> r)))) [target_tm]⊢⁺
    ((default <+ cut_tag <+ ld1) {{B}}> ([1, 1, 1, 0, 0] +> r)) :=
  ⟨50, by omega, by run_steps 50⟩

lemma Cap_entry (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 1, 1, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ [1]) <{{E}} ([0] +> ([1, 1, 0] +> r))) :=
  ⟨6, by omega, by run_steps 6⟩

lemma OddCap_exit (l r : ListBlank (Fin 2)) :
    ((l <+ ld1 <+ [1]) <{{E}} ([0, 1] +> r)) [target_tm]⊢⁺
    ((l <+ [1, 1, 1] <+ ld1) {{B}}> r) :=
  ⟨7, by omega, by run_steps 7⟩

lemma odd_capacity_entry (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ ld1) {{B}}> (rd1 ^ (n * 2) +> ([1, 1, 1, 0, 0] +> r))) [target_tm]⊢⁺
    ((l <+ [1, 1, 1] <+ ld1 <+ ld0 ^ n) {{B}}> ([1, 0] +> r)) := by
  have s1 := R100Scan (l <+ ld1) ([1, 1, 1, 0, 0] +> r) (n * 2)
  have s2 := Cap_entry (l <+ ld1 <+ (Half 1) ^ (n * 2)) r
  rw [one_comm_half1_pow (n * 2) (l <+ ld1)] at s2
  have s3 := ECarry_half1_pair (l <+ ld1 <+ [1]) ([1, 1, 0] +> r) n
  have h1 : ([0] : List (Fin 2)) +> (ones ^ (n * 6) +> ([1, 1, 0] +> r)) =
      [0, 1] +> (ones ^ ((n * 2) * 3) +> ([1, 0] +> r)) := by
    have : ones ^ (n * 6) +> ([1] +> ([1, 0] +> r)) =
        [1] +> (ones ^ ((n * 2) * 3) +> ([1, 0] +> r)) := by
      rw [one_comm_ones_pow (n * 6) ([1, 0] +> r), show n * 6 = n * 2 * 3 by omega]
    simpa using! congrArg ((0 : Fin 2) >> ·) this
  rw [h1] at s3
  have s4 := OddCap_exit l (ones ^ ((n * 2) * 3) +> ([1, 0] +> r))
  have s5 := R111Scan (l <+ [1, 1, 1] <+ ld1) ([1, 0] +> r) (n * 2)
  rw [half0_pairs n] at s5
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_stepStar_trans s4 s5)))

lemma EvenCap_mid (l r : ListBlank (Fin 2)) :
    ((l <+ Half 1 <+ [1]) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    (l <{{E}} ([0] +> ([1, 1, 1, 1] +> r))) :=
  ⟨8, by omega, by run_steps 8⟩

lemma EvenCap_exit (r : ListBlank (Fin 2)) :
    ((default <+ cut_tag) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    (ldh {{B}}> (ones ^ 6 +> r)) :=
  ⟨12, by omega, by run_steps 12⟩

lemma even_capacity_cleanup (n : Nat) (r : ListBlank (Fin 2)) :
    ((default <+ cut_tag <+ ld1 ^ (2 + n * 2)) {{B}}>
      (rd1 ^ (1 + n * 2) +> ([1, 1, 1, 0, 0] +> r))) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (4 + n * 3)) {{B}}> ([0] +> r)) := by
  have s1 := R100Scan (default <+ cut_tag <+ ld1 ^ (2 + n * 2)) ([1, 1, 1, 0, 0] +> r) (1 + n * 2)
  have s2 := Cap_entry (default <+ cut_tag <+ ld1 ^ (2 + n * 2) <+ (Half 1) ^ (1 + n * 2)) r
  have h1 : default <+ cut_tag <+ ld1 ^ (2 + n * 2) <+ (Half 1) ^ (1 + n * 2) <+ [1] =
      default <+ cut_tag <+ ld1 ^ (2 + n * 2) <+ Half 1 <+ [1] <+ (Half 1) ^ (n * 2) := by
    rw [show 1 + n * 2 = n * 2 + 1 by omega, left_pow_succ_right,
        one_comm_half1_pow (n * 2) (default <+ cut_tag <+ ld1 ^ (2 + n * 2) <+ Half 1)]
  rw [h1] at s2
  have s3 := ECarry_half1_pair (default <+ cut_tag <+ ld1 ^ (2 + n * 2) <+ Half 1 <+ [1]) ([1, 1, 0] +> r) n
  have s4 := EvenCap_mid (default <+ cut_tag <+ ld1 ^ (2 + n * 2)) (ones ^ (n * 6) +> ([1, 1, 0] +> r))
  have s5 := ECarry_ld1 (default <+ cut_tag) ([1, 1, 1, 1] +> (ones ^ (n * 6) +> ([1, 1, 0] +> r))) (2 + n * 2)
  have s6 := EvenCap_exit (ones ^ ((2 + n * 2) * 6) +> ([1, 1, 1, 1] +> (ones ^ (n * 6) +> ([1, 1, 0] +> r))))
  have h2 : ones ^ 6 +>
      (ones ^ ((2 + n * 2) * 6) +> ([1, 1, 1, 1] +> (ones ^ (n * 6) +> ([1, 1, 0] +> r)))) =
      ones ^ (((4 + n * 3) * 2) * 3) +> ([0] +> r) := by
    have h110 : ([1, 1, 0] : List (Fin 2)) +> r = ones ^ 2 +> ([0] +> r) := rfl
    have h1111 : ([1, 1, 1, 1] : List (Fin 2)) = ones ^ 4 := rfl
    rw [h110, h1111, ← right_pow_add, ← right_pow_add, ← right_pow_add, ← right_pow_add]
    have : 6 + (2 + n * 2) * 6 + 4 + n * 6 + 2 = (4 + n * 3) * 2 * 3 := by omega
    rw [this]
  rw [h2] at s6
  have s7 := R111Scan ldh ([0] +> r) ((4 + n * 3) * 2)
  rw [half0_pairs (4 + n * 3)] at s7
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3
        (stepPlus_trans s4
          (stepStar_stepPlus_trans s5
            (stepPlus_stepStar_trans s6 s7)))))

lemma SZeroEntry (l r : ListBlank (Fin 2)) :
    ((l <+ s_tag) {{D}}> ([0, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 0) <{{C}} ([0, 0, 0, 1] +> r)) :=
  ⟨6, by omega, by run_steps 6⟩

lemma R11Bit (l r : ListBlank (Fin 2)) (b : Fin 2) :
    (l {{B}}> ([1, 1, b, 0, 0] +> r)) [target_tm]⊢⁺
    ((l <+ Half 0) <{{C}} ([1, 0] +> r)) := by
  rcases fin2_cases b with rfl | rfl
  · exact ⟨4, by omega, by run_steps 4⟩
  · exact ⟨4, by omega, by run_steps 4⟩

lemma EHalfBoundary (r : ListBlank (Fin 2)) (b : Fin 2) :
    ((ldh <+ Half b) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    (ldh {{B}}> (ones ^ 6 +> r)) := by
  rcases fin2_cases b with rfl | rfl
  · exact ⟨12, by omega, by run_steps 12⟩
  · exact ⟨12, by omega, by run_steps 12⟩

lemma EOdd (r : ListBlank (Fin 2)) (n : Nat) (b : Fin 2) :
    ((ldh <+ Half b) <{{E}} ([0] +> (ones ^ (n * 6 + 5) +> r))) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (n + 1) <+ Half 0) {{B}}> ([1, 1] +> r)) := by
  have s1 := EHalfBoundary (ones ^ (n * 6 + 5) +> r) b
  have h1 : ones ^ 6 +> (ones ^ (n * 6 + 5) +> r) =
      ones ^ (((n + 1) * 2 + 1) * 3) +> ([1, 1] +> r) := by
    have h11 : ([1, 1] : List (Fin 2)) +> r = ones ^ 2 +> r := rfl
    rw [h11, ← right_pow_add, ← right_pow_add]
    have : 6 + (n * 6 + 5) = ((n + 1) * 2 + 1) * 3 + 2 := by omega
    rw [this]
  rw [h1] at s1
  have s2 := R111Scan ldh ([1, 1] +> r) ((n + 1) * 2 + 1)
  rw [left_pow_succ, half0_pairs (n + 1)] at s2
  exact stepPlus_stepStar_trans s1 s2

lemma LSingle (r : ListBlank (Fin 2)) :
    ((ldh <+ Half 0) <{{C}} r) [target_tm]⊢⁺
    ((ldh <+ Half 0) {{B}}> ([1, 1] +> r)) :=
  ⟨13, by omega, by run_steps 13⟩

lemma LZeroEven (r : ListBlank (Fin 2)) (bs : List (Fin 2)) :
    ((ldh <+ Marked bs <+ Half 1 <+ Half 0) <{{C}} r) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (bs.length + 1)) {{B}}> ([1] +> r)) := by
  have s1 := LBAtoE (ldh <+ Marked bs) r
  have s2 := MarkedCarry ldh (ones ^ 5 +> r) bs
  rw [← right_pow_add] at s2
  exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 (EEven r bs.length))

lemma LZeroOdd (r : ListBlank (Fin 2)) (bs : List (Fin 2)) (b : Fin 2) :
    ((ldh <+ Half b <+ Marked bs <+ Half 1 <+ Half 0) <{{C}} r) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (bs.length + 1) <+ Half 0) {{B}}> ([1, 1] +> r)) := by
  have s1 := LBAtoE (ldh <+ Half b <+ Marked bs) r
  have s2 := MarkedCarry (ldh <+ Half b) (ones ^ 5 +> r) bs
  rw [← right_pow_add] at s2
  exact stepPlus_trans s1 (stepStar_stepPlus_trans s2 (EOdd r bs.length b))

lemma R101Even_entry (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 0, 1, 0, 0] +> r)) [target_tm]⊢⁺
    (l <{{E}} ([0] +> ([1, 1, 0, 0] +> r))) :=
  ⟨7, by omega, by run_steps 7⟩

lemma E0_to_C (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    ((l <+ [0]) <{{C}} ([1] +> r)) :=
  ⟨2, by omega, by run_steps 2⟩

lemma R101EvenEntry (l r : ListBlank (Fin 2)) (m : Nat) :
    ((l <+ [0]) {{B}}> (rd1 ^ (m * 2) +> ([1, 0, 1, 0, 0] +> r))) [target_tm]⊢⁺
    ((l <+ [0]) <{{C}} (ones ^ (m * 6 + 3) +> ([0, 0] +> r))) := by
  have s1 := R100Scan (l <+ [0]) ([1, 0, 1, 0, 0] +> r) (m * 2)
  have s2 := R101Even_entry (l <+ [0] <+ (Half 1) ^ (m * 2)) r
  have s3 := ECarry_half1_pair (l <+ [0]) ([1, 1, 0, 0] +> r) m
  have s4 := E0_to_C l (ones ^ (m * 6) +> ([1, 1, 0, 0] +> r))
  have h1 : ([1] : List (Fin 2)) +> (ones ^ (m * 6) +> ([1, 1, 0, 0] +> r)) =
      ones ^ (m * 6 + 3) +> ([0, 0] +> r) := by
    have h1100 : ([1, 1, 0, 0] : List (Fin 2)) +> r = ones ^ 2 +> ([0, 0] +> r) := rfl
    have h1_pow : ([1] : List (Fin 2)) +> (ones ^ (m * 6) +> (ones ^ 2 +> ([0, 0] +> r))) =
        ones ^ 1 +> (ones ^ (m * 6) +> (ones ^ 2 +> ([0, 0] +> r))) := rfl
    rw [h1100, h1_pow, ← right_pow_add, ← right_pow_add]
    have : 1 + m * 6 + 2 = m * 6 + 3 := by omega
    rw [this]
  rw [h1] at s4
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepStar_stepPlus_trans s3 s4))

lemma init_to_J2 :
    (init []) [target_tm]⊢*
    ((ldh <+ ld0 ^ 2) <{{C}} ([1, 0] +> (rd1 +> default))) :=
  ⟨136, by run_steps 136⟩


-- ============================================================================
-- Section 3: Right Counter (Pair45Right)
-- ============================================================================

@[simp] lemma rd0_append_default : rd0 +> (default : ListBlank (Fin 2)) = default := by
  simp [rd0]

inductive RC : Nat → ListBlank (Fin 2) → Prop
  | zero : RC 0 default
  | d0 (n : Nat) (r : ListBlank (Fin 2)) : RC n r → RC (n * 2) (rd0 +> r)
  | d1 (n : Nat) (r : ListBlank (Fin 2)) : RC n r → RC (1 + n * 2) (rd1 +> r)

inductive FC (tail : ListBlank (Fin 2)) : Nat → Nat → ListBlank (Fin 2) → Prop
  | nil : FC tail 0 0 tail
  | d0 (k n : Nat) (r : ListBlank (Fin 2)) : FC tail k n r → FC tail (k + 1) (n * 2) (rd0 +> r)
  | d1 (k n : Nat) (r : ListBlank (Fin 2)) : FC tail k n r → FC tail (k + 1) (1 + n * 2) (rd1 +> r)

lemma RC_eq {n m : Nat} {r s : ListBlank (Fin 2)} (h : RC n r) (hn : n = m) (hr : r = s) :
    RC m s := by
  subst hn; subst hr; exact h

lemma FC_eq {tail : ListBlank (Fin 2)} {k k' n n' : Nat} {r r' : ListBlank (Fin 2)}
    (h : FC tail k n r) (hk : k = k') (hn : n = n') (hr : r = r') :
    FC tail k' n' r' := by
  subst hk; subst hn; subst hr; exact h

lemma RC_zero_unique {r : ListBlank (Fin 2)} (h : RC 0 r) : r = default := by
  generalize hn : (0 : Nat) = n at h
  induction h with
  | zero => rfl
  | d0 n r _ ih =>
    have hn0 : n = 0 := by omega
    rw [ih hn0.symm, rd0_append_default]
  | d1 _ _ _ _ => omega

lemma RC_inv_d0 {n : Nat} {s : ListBlank (Fin 2)} (hs : RC (n * 2) s) :
    (n = 0 ∧ s = default) ∨ ∃ s0, s = rd0 +> s0 ∧ RC n s0 := by
  generalize hm : n * 2 = m at hs
  cases hs with
  | zero => exact Or.inl ⟨by omega, rfl⟩
  | d0 n0 s0 hs0 =>
    have hn : n0 = n := by omega
    subst hn
    exact Or.inr ⟨s0, rfl, hs0⟩
  | d1 _ _ _ => omega

lemma RC_inv_d1 {n : Nat} {s : ListBlank (Fin 2)} (hs : RC (1 + n * 2) s) :
    ∃ s0, s = rd1 +> s0 ∧ RC n s0 := by
  generalize hm : 1 + n * 2 = m at hs
  cases hs with
  | zero => omega
  | d0 _ _ _ => omega
  | d1 n0 s0 hs0 =>
    have hn : n0 = n := by omega
    subst hn
    exact ⟨s0, rfl, hs0⟩

lemma FC_inv_nil {tail : ListBlank (Fin 2)} {n : Nat} {s : ListBlank (Fin 2)}
    (hs : FC tail 0 n s) : s = tail := by
  generalize hk : (0 : Nat) = k at hs
  cases hs with
  | nil => rfl
  | d0 _ _ _ _ => omega
  | d1 _ _ _ _ => omega

lemma FC_inv_d0 {tail : ListBlank (Fin 2)} {k n : Nat} {s : ListBlank (Fin 2)}
    (hs : FC tail (k + 1) (n * 2) s) : ∃ s0, s = rd0 +> s0 ∧ FC tail k n s0 := by
  generalize hk : k + 1 = K, hm : n * 2 = m at hs
  cases hs with
  | nil => omega
  | d0 k0 n0 s0 hs0 =>
    have hk0 : k0 = k := by omega
    have hn0 : n0 = n := by omega
    subst hk0; subst hn0
    exact ⟨s0, rfl, hs0⟩
  | d1 _ _ _ _ => omega

lemma FC_inv_d1 {tail : ListBlank (Fin 2)} {k n : Nat} {s : ListBlank (Fin 2)}
    (hs : FC tail (k + 1) (1 + n * 2) s) : ∃ s0, s = rd1 +> s0 ∧ FC tail k n s0 := by
  generalize hk : k + 1 = K, hm : 1 + n * 2 = m at hs
  cases hs with
  | nil => omega
  | d0 _ _ _ _ => omega
  | d1 k0 n0 s0 hs0 =>
    have hk0 : k0 = k := by omega
    have hn0 : n0 = n := by omega
    subst hk0; subst hn0
    exact ⟨s0, rfl, hs0⟩

lemma RC_unique {n : Nat} {r s : ListBlank (Fin 2)} (hr : RC n r) (hs : RC n s) : r = s := by
  induction hr generalizing s with
  | zero => exact (RC_zero_unique hs).symm
  | d0 n r hr ih =>
    rcases RC_inv_d0 hs with ⟨rfl, rfl⟩ | ⟨s0, rfl, hs0⟩
    · rw [RC_zero_unique hr, rd0_append_default]
    · rw [ih hs0]
  | d1 n r _ ih =>
    rcases RC_inv_d1 hs with ⟨s0, rfl, hs0⟩
    rw [ih hs0]

lemma FC_unique {tail : ListBlank (Fin 2)} {k n : Nat} {r s : ListBlank (Fin 2)}
    (hr : FC tail k n r) (hs : FC tail k n s) : r = s := by
  induction hr generalizing s with
  | nil => exact (FC_inv_nil hs).symm
  | d0 k n r _ ih =>
    rcases FC_inv_d0 hs with ⟨s0, rfl, hs0⟩
    rw [ih hs0]
  | d1 k n r _ ih =>
    rcases FC_inv_d1 hs with ⟨s0, rfl, hs0⟩
    rw [ih hs0]

lemma pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

lemma nat_even_or_odd (n : Nat) : (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inr ⟨m, rfl⟩
    · exact Or.inl ⟨m + 1, by omega⟩

lemma FC_zero (tail : ListBlank (Fin 2)) (k : Nat) : FC tail k 0 (rd0 ^ k +> tail) := by
  induction k with
  | zero => exact FC.nil
  | succ k ih =>
    rw [right_pow_succ rd0 k tail]
    exact FC_eq (FC.d0 k 0 (rd0 ^ k +> tail) ih) rfl (by omega) rfl

lemma FC_full (tail : ListBlank (Fin 2)) (k : Nat) : FC tail k (2 ^ k - 1) (rd1 ^ k +> tail) := by
  induction k with
  | zero => exact FC.nil
  | succ k ih =>
    have hp := pow2_pos k
    rw [right_pow_succ rd1 k tail]
    exact FC_eq (FC.d1 k (2 ^ k - 1) (rd1 ^ k +> tail) ih) rfl (by rw [Nat.pow_succ]; omega) rfl

lemma FC_full_unique {tail : ListBlank (Fin 2)} {k : Nat} {r : ListBlank (Fin 2)}
    (h : FC tail k (2 ^ k - 1) r) : r = rd1 ^ k +> tail :=
  FC_unique h (FC_full tail k)

lemma FC_RC {tail : ListBlank (Fin 2)} {k n : Nat} {r : ListBlank (Fin 2)} {m : Nat}
    (hf : FC tail k n r) (hr : RC m tail) : RC (n + 2 ^ k * m) r := by
  induction hf with
  | nil =>
    exact RC_eq hr (by omega) rfl
  | d0 k n r _ ih =>
    exact RC_eq (RC.d0 (n + 2 ^ k * m) r ih) (by rw [Nat.pow_succ]; ring) rfl
  | d1 k n r _ ih =>
    exact RC_eq (RC.d1 (n + 2 ^ k * m) r ih) (by rw [Nat.pow_succ]; ring) rfl

lemma RC_zeros {n : Nat} {r : ListBlank (Fin 2)} (k : Nat) (hr : RC n r) :
    RC (2 ^ k * n) (rd0 ^ k +> r) := by
  simpa using! FC_RC (FC_zero r k) hr

lemma RC_carry {n : Nat} {r : ListBlank (Fin 2)} (h : RC n r) :
    ∃ (k : Nat) (s : ListBlank (Fin 2)), r = rd1 ^ k +> (rd0 +> s) ∧ RC (n + 1) (rd0 ^ k +> (rd1 +> s)) := by
  induction h with
  | zero =>
    refine ⟨(0 : Nat), default, ?_, ?_⟩
    · simp
    · exact RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  | d0 n r hr _ =>
    exact ⟨(0 : Nat), r, rfl, RC_eq (RC.d1 n r hr) (by omega) rfl⟩
  | d1 n r _ ih =>
    rcases ih with ⟨k, s, rfl, hs⟩
    refine ⟨k + 1, s, ?_, ?_⟩
    · rw [right_pow_succ rd1 k (rd0 +> s)]
    · rw [right_pow_succ rd0 k (rd1 +> s)]
      exact RC_eq (RC.d0 (n + 1) (rd0 ^ k +> (rd1 +> s)) hs) (by omega) rfl

lemma RC_positive_split {n : Nat} {r : ListBlank (Fin 2)} (h : RC n r) (hn : 0 < n) :
    ∃ t q s, r = rd0 ^ t +> (rd1 +> s) ∧ RC q s ∧ n = 2 ^ t * (1 + q * 2) ∧ q < n := by
  induction h with
  | zero => omega
  | d0 n r _ ih =>
    rcases ih (by omega) with ⟨t, q, s, rfl, hs, heq, hlt⟩
    refine ⟨t + 1, q, s, ?_, hs, ?_, by omega⟩
    · rw [right_pow_succ rd0 t (rd1 +> s)]
    · rw [Nat.pow_succ, heq]; ring
  | d1 n r hr _ =>
    exact ⟨0, n, r, rfl, hr, by omega, by omega⟩

lemma FC_carry {tail : ListBlank (Fin 2)} {k n : Nat} {r : ListBlank (Fin 2)}
    (h : FC tail k n r) (hb : n + 1 < 2 ^ k) :
    ∃ j s, j < k ∧ r = rd1 ^ j +> (rd0 +> s) ∧ FC tail k (n + 1) (rd0 ^ j +> (rd1 +> s)) := by
  induction h with
  | nil => simp at hb
  | d0 k n r hr _ =>
    exact ⟨0, r, by omega, rfl, FC_eq (FC.d1 k n r hr) rfl (by omega) rfl⟩
  | d1 k n r _ ih =>
    have hb' : n + 1 < 2 ^ k := by rw [Nat.pow_succ] at hb; omega
    rcases ih hb' with ⟨j, s, hj, rfl, hs⟩
    refine ⟨j + 1, s, by omega, ?_, ?_⟩
    · rw [right_pow_succ rd1 j (rd0 +> s)]
    · rw [right_pow_succ rd0 j (rd1 +> s)]
      exact FC_eq (FC.d0 k (n + 1) (rd0 ^ j +> (rd1 +> s)) hs) rfl (by omega) rfl

lemma RC_tail {n : Nat} {r : ListBlank (Fin 2)} (h : RC n r) :
    ∃ (b : Fin 2) (s : ListBlank (Fin 2)), RC (n / 2) s ∧ r = [b, 0, 0] +> s := by
  cases h with
  | zero => exact ⟨0, default, RC.zero, rd0_append_default.symm⟩
  | d0 n s hs => exact ⟨0, s, RC_eq hs (by omega) rfl, rfl⟩
  | d1 n s hs => exact ⟨1, s, RC_eq hs (by omega) rfl, rfl⟩

lemma RScan (l r : ListBlank (Fin 2)) (k : Nat) :
    (l {{B}}> (rd1 ^ k +> (rd0 +> r))) [target_tm]⊢⁺
    (l <{{C}} (rd0 ^ k +> (rd1 +> r))) := by
  simpa [rd0, rd1] using! RInc_rule l ([0, 0] +> r) k

lemma RInc_ex {n : Nat} {r : ListBlank (Fin 2)} (h : RC n r) :
    ∃ s, RC (n + 1) s ∧ ∀ l, (l {{B}}> r) [target_tm]⊢⁺ (l <{{C}} s) := by
  rcases RC_carry h with ⟨k, s, rfl, hs⟩
  exact ⟨rd0 ^ k +> (rd1 +> s), hs, fun l => RScan l s k⟩

lemma FiniteRInc_ex {tail : ListBlank (Fin 2)} {k n : Nat} {r : ListBlank (Fin 2)}
    (h : FC tail k n r) (hb : n + 1 < 2 ^ k) :
    ∃ s, FC tail k (n + 1) s ∧ ∀ l, (l {{B}}> r) [target_tm]⊢⁺ (l <{{C}} s) := by
  rcases FC_carry h hb with ⟨j, s, _, rfl, hs⟩
  exact ⟨rd0 ^ j +> (rd1 +> s), hs, fun l => RScan l s j⟩

-- ============================================================================
-- Section 4: HalfCounter Model (Num, Borrow, LInc, Pairs, TZero)
-- ============================================================================

def digit (b : Bool) : List (Fin 2) := Half (if b then 0 else 1)

def l_tape : List Bool → List (Fin 2)
  | [] => []
  | b :: w => digit b ++ l_tape w

@[simp] lemma l_tape_nil : l_tape [] = [] := rfl
@[simp] lemma l_tape_cons (b : Bool) (w : List Bool) :
    l_tape (b :: w) = digit b ++ l_tape w := rfl

inductive Num : Nat → Nat → Nat → List Bool → Prop
  | nil : Num 0 0 0 []
  | A (n e o : Nat) (w : List Bool) : Num n e o w → Num (1 + n) (1 + o * 2) e (true :: w)
  | B (n e o : Nat) (w : List Bool) : Num n e o w → Num (1 + n) (o * 2) e (false :: w)

lemma Num_eq {n n' e e' o o' : Nat} {w w' : List Bool}
    (h : Num n e o w) (hn : n = n') (he : e = e') (ho : o = o') (hw : w = w') :
    Num n' e' o' w' := by
  subst hn; subst he; subst ho; subst hw; exact h

lemma Num_length {n e o : Nat} {w : List Bool} (h : Num n e o w) : w.length = n := by
  induction h with
  | nil => rfl
  | A _ _ _ _ _ ih => simp [ih]; omega
  | B _ _ _ _ _ ih => simp [ih]; omega

lemma Num_bounds {n e o : Nat} {w : List Bool} (h : Num n e o w) :
    e < 2 ^ ((n + 1) / 2) ∧ o < 2 ^ (n / 2) := by
  induction h with
  | nil => simp
  | A n e o w _ ih =>
    rcases ih with ⟨he, ho⟩
    have h1 : (1 + n + 1) / 2 = (n / 2) + 1 := by omega
    have h2 : (1 + n) / 2 = (n + 1) / 2 := by omega
    rw [h1, h2, Nat.pow_succ]
    omega
  | B n e o w _ ih =>
    rcases ih with ⟨he, ho⟩
    have h1 : (1 + n + 1) / 2 = (n / 2) + 1 := by omega
    have h2 : (1 + n) / 2 = (n + 1) / 2 := by omega
    rw [h1, h2, Nat.pow_succ]
    omega

lemma Num_inv_nil {n e o : Nat} (h : Num n e o []) : n = 0 ∧ e = 0 ∧ o = 0 := by
  generalize hw : ([] : List Bool) = w at h
  cases h with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | A _ _ _ _ _ => cases hw
  | B _ _ _ _ _ => cases hw

lemma Num_inv_true {n e o : Nat} {w : List Bool} (h : Num n e o (true :: w)) :
    ∃ n0 o0, n = 1 + n0 ∧ e = 1 + o0 * 2 ∧ Num n0 o o0 w := by
  generalize hw : true :: w = u at h
  cases h with
  | nil => cases hw
  | A n0 e0 o0 w0 h0 =>
    injection hw with _ hw0; subst hw0
    exact ⟨n0, o0, rfl, rfl, h0⟩
  | B _ _ _ _ _ => cases hw

lemma Num_inv_false {n e o : Nat} {w : List Bool} (h : Num n e o (false :: w)) :
    ∃ n0 o0, n = 1 + n0 ∧ e = o0 * 2 ∧ Num n0 o o0 w := by
  generalize hw : false :: w = u at h
  cases h with
  | nil => cases hw
  | A _ _ _ _ _ => cases hw
  | B n0 e0 o0 w0 h0 =>
    injection hw with _ hw0; subst hw0
    exact ⟨n0, o0, rfl, rfl, h0⟩

lemma Num_inv_cons {n e o : Nat} {b : Bool} {w : List Bool} (h : Num n e o (b :: w)) :
    ∃ n0 o0, n = 1 + n0 ∧ e = (if b then 1 + o0 * 2 else o0 * 2) ∧ Num n0 o o0 w := by
  cases b
  · rcases Num_inv_false h with ⟨n0, o0, hn, he, h0⟩
    exact ⟨n0, o0, hn, he, h0⟩
  · rcases Num_inv_true h with ⟨n0, o0, hn, he, h0⟩
    exact ⟨n0, o0, hn, he, h0⟩

inductive Borrow : List Bool → List Bool → Prop
  | stop (b : Bool) (w : List Bool) : Borrow (b :: true :: w) (false :: w)
  | carry (b : Bool) (w w' : List Bool) : Borrow w w' → Borrow (b :: false :: w) (true :: true :: w')

lemma Borrow_num {w w' : List Bool} (hb : Borrow w w') :
    ∀ {n e o : Nat}, Num n e (1 + o) w → ∃ e', Num n e' o (true :: w') ∧ e ≤ e' := by
  induction hb with
  | stop b w =>
    intro n e o h
    rcases Num_inv_cons h with ⟨n0, o0, rfl, rfl, h0⟩
    rcases Num_inv_true h0 with ⟨n1, o1, rfl, ho, h1⟩
    refine ⟨1 + o0 * 2, ⟨Num_eq (Num.A _ _ _ _ (Num.B _ _ _ _ h1)) rfl rfl (by omega) rfl, ?_⟩⟩
    cases b <;> (simp; try omega)
  | carry b w w' _ ih =>
    intro n e o h
    rcases Num_inv_cons h with ⟨n0, o0, rfl, rfl, h0⟩
    rcases Num_inv_false h0 with ⟨n1, o1, rfl, ho, h1⟩
    have h1' : Num n1 o0 (1 + (o1 - 1)) w := Num_eq h1 rfl rfl (by omega) rfl
    rcases ih h1' with ⟨e', hn', hle⟩
    refine ⟨1 + e' * 2, ⟨Num_eq (Num.A _ _ _ _ (Num.A _ _ _ _ hn')) rfl rfl (by omega) rfl, ?_⟩⟩
    cases b <;> (simp; try omega)

lemma Borrow_ex : ∀ (n : Nat) {e o : Nat} {w : List Bool},
    Num n e (1 + o) w → ∃ w', Borrow w w' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro e o w hn
    rcases w with _ | ⟨b, _ | ⟨c, w1⟩⟩
    · rcases Num_inv_nil hn with ⟨_, _, _⟩; omega
    · rcases Num_inv_cons hn with ⟨n0, o0, rfl, rfl, h0⟩
      rcases Num_inv_nil h0 with ⟨_, _, _⟩; omega
    · rcases Num_inv_cons hn with ⟨n0, o0, rfl, rfl, h0⟩
      cases c
      · rcases Num_inv_false h0 with ⟨n1, o1, rfl, ho, h1⟩
        have h1' : Num n1 o0 (1 + (o1 - 1)) w1 := Num_eq h1 rfl rfl (by omega) rfl
        rcases ih n1 (by omega) h1' with ⟨w', hw'⟩
        exact ⟨true :: true :: w', Borrow.carry b w1 w' hw'⟩
      · exact ⟨false :: w1, Borrow.stop b w1⟩

lemma Borrow_spec {w w' : List Bool} (hb : Borrow w w') (l r : ListBlank (Fin 2)) :
    ((l <+ l_tape w) <{{E}} ([0] +> r)) [target_tm]⊢⁺
    ((l <+ l_tape w' <+ s_tag) {{D}}> r) := by
  induction hb generalizing l r with
  | stop b w =>
    have ht : l <+ l_tape (b :: true :: w) = l <+ l_tape w <+ Half 0 <+ Half (if b then 0 else 1) := by
      simp [l_tape, digit]
    have ht' : l <+ l_tape (false :: w) = l <+ l_tape w <+ Half 1 := by
      simp [l_tape, digit]
    rw [ht, ht']
    exact EStop (l <+ l_tape w) r (if b then 0 else 1)
  | carry b w w' _ ih =>
    have ht : l <+ l_tape (b :: false :: w) = l <+ l_tape w <+ Half 1 <+ Half (if b then 0 else 1) := by
      simp [l_tape, digit]
    have ht' : l <+ l_tape (true :: true :: w') = l <+ l_tape w' <+ ld0 ^ 1 := by
      simp [l_tape, digit, ld0, Half, pow_succ_list, pow_zero_list]
    rw [ht, ht']
    have s1 := ECarry (l <+ l_tape w) r (if b then 0 else 1)
    have s2 := ih l (ones ^ 6 +> r)
    have s3 := SOnes (l <+ l_tape w') r 1
    exact stepPlus_trans s1 (stepPlus_stepStar_trans s2 s3)

lemma L_borrow_spec {w w' : List Bool} (hb : Borrow (true :: w) w') (l r : ListBlank (Fin 2)) :
    ((l <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢⁺
    ((l <+ l_tape (true :: w')) {{B}}> r) := by
  cases hb with
  | stop _ v =>
    have ht : l <+ l_tape (true :: true :: v) = l <+ l_tape v <+ ld0 := by
      simp [l_tape, digit, ld0, Half]
    have ht' : l <+ l_tape (true :: false :: v) = l <+ l_tape v <+ ld1 := by
      simp [l_tape, digit, ld1, Half]
    rw [ht, ht']
    exact LInc_zero (l <+ l_tape v) r
  | carry _ v u hv =>
    have ht : l <+ l_tape (true :: false :: v) = l <+ l_tape v <+ Half 1 <+ Half 0 := by
      simp [l_tape, digit]
    have ht' : l <+ l_tape (true :: true :: true :: u) =
        l <+ l_tape u <+ Half 0 <+ Half 0 <+ Half 0 := by
      simp [l_tape, digit]
    rw [ht, ht']
    exact stepPlus_trans (LBAtoE (l <+ l_tape v) r)
      (stepPlus_trans (Borrow_spec hv l (ones ^ 5 +> r)) (SFive (l <+ l_tape u) r))

lemma LInc_num {n e o : Nat} {w : List Bool} (hn : Num n e (1 + o) (true :: w)) :
    ∃ e' w', Num n e' o (true :: w') ∧ e ≤ e' ∧ ∀ l r,
      ((l <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢⁺
      ((l <+ l_tape (true :: w')) {{B}}> r) := by
  rcases Borrow_ex n hn with ⟨w', hb⟩
  rcases Borrow_num hb hn with ⟨e', hn', hle⟩
  exact ⟨e', w', hn', hle, L_borrow_spec hb⟩

lemma RC_pairs (q : Nat) {n e o : Nat} {w : List Bool} {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Num n e (q + o) (true :: w)) (hr : RC z r) :
    ∃ e' w' r', Num n e' o (true :: w') ∧ e ≤ e' ∧ RC (z + q) r' ∧ ∀ l,
      ((l <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢*
      ((l <+ l_tape (true :: w')) <{{C}} r') := by
  induction q generalizing e w z r with
  | zero =>
    exact ⟨e, w, r, Num_eq hn rfl rfl (by omega) rfl, Nat.le_refl e,
      RC_eq hr (by omega) rfl, fun l => stepStar_refl _⟩
  | succ q ih =>
    have hn1 : Num n e (1 + (q + o)) (true :: w) := Num_eq hn rfl rfl (by omega) rfl
    rcases LInc_num hn1 with ⟨e1, w1, hn_w1, hle1, hL⟩
    rcases RInc_ex hr with ⟨r1, hr1, hR⟩
    rcases ih hn_w1 hr1 with ⟨e2, w2, r2, hn_w2, hle2, hr2, hS⟩
    refine ⟨e2, w2, r2, hn_w2, by omega, RC_eq hr2 (by omega) rfl, fun l => ?_⟩
    exact stepStar_trans (stepPlus_to_stepStar (hL l r))
      (stepStar_trans (stepPlus_to_stepStar (hR (l <+ l_tape (true :: w1)))) (hS l))

lemma FC_pairs (tail : ListBlank (Fin 2)) (k q : Nat) {n e o : Nat} {w : List Bool}
    {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Num n e (q + o) (true :: w)) (hr : FC tail k z r) (hb : z + q < 2 ^ k) :
    ∃ e' w' r', Num n e' o (true :: w') ∧ e ≤ e' ∧ FC tail k (z + q) r' ∧ ∀ l,
      ((l <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢*
      ((l <+ l_tape (true :: w')) <{{C}} r') := by
  induction q generalizing e w z r with
  | zero =>
    exact ⟨e, w, r, Num_eq hn rfl rfl (by omega) rfl, Nat.le_refl e,
      FC_eq hr rfl (by omega) rfl, fun l => stepStar_refl _⟩
  | succ q ih =>
    have hn1 : Num n e (1 + (q + o)) (true :: w) := Num_eq hn rfl rfl (by omega) rfl
    rcases LInc_num hn1 with ⟨e1, w1, hn_w1, hle1, hL⟩
    rcases FiniteRInc_ex hr (by omega) with ⟨r1, hr1, hR⟩
    rcases ih hn_w1 hr1 (by omega) with ⟨e2, w2, r2, hn_w2, hle2, hr2, hS⟩
    refine ⟨e2, w2, r2, hn_w2, by omega, FC_eq hr2 rfl (by omega) rfl, fun l => ?_⟩
    exact stepStar_trans (stepPlus_to_stepStar (hL l r))
      (stepStar_trans (stepPlus_to_stepStar (hR (l <+ l_tape (true :: w1)))) (hS l))

lemma TZero {n e o : Nat} {w : List Bool} (h : Nat) (l r : ListBlank (Fin 2))
    (hn : Num n e (2 ^ (h + 2) + o) (true :: w)) :
    ∃ e' w', Num n e' o (true :: w') ∧ e ≤ e' ∧
      ((l <+ l_tape (true :: w) <+ (Half 1) ^ h <+ t_tag) {{D}}> (rd0 +> r)) [target_tm]⊢⁺
      ((l <+ l_tape (true :: w') <+ (Half 1) ^ (h + 1) <+ t_tag) {{D}}> r) := by
  have hp := pow2_pos (h + 2)
  have hn' : Num n e ((2 ^ (h + 2) - 1) + (1 + o)) (true :: w) :=
    Num_eq hn rfl rfl (by omega) rfl
  rcases FC_pairs ([1] +> r) (h + 2) (2 ^ (h + 2) - 1) hn' (FC_zero ([1] +> r) (h + 2)) (by omega)
    with ⟨e1, w1, r1, h1, hle1, hr1, hS⟩
  rcases LInc_num h1 with ⟨e2, w2, h2, hle2, hL⟩
  have hr1_eq : r1 = rd1 ^ (h + 2) +> ([1] +> r) :=
    FC_full_unique (FC_eq hr1 rfl (by omega) rfl)
  subst hr1_eq
  refine ⟨e2, w2, h2, by omega, ?_⟩
  have ht : l <+ l_tape (true :: w) = l <+ l_tape w <+ Half 0 := by simp [l_tape, digit]
  have s1 := TZeroEntry (l <+ l_tape w) r h
  rw [← ht] at s1
  have s2 := hS l
  have s3 := hL l (rd1 ^ (h + 2) +> ([1] +> r))
  have s4 := RExit (l <+ l_tape (true :: w2)) r h
  exact stepPlus_trans s1
    (stepStar_stepPlus_trans s2
      (stepPlus_trans s3 s4))

-- ============================================================================
-- Section 5: HalfNormal
-- ============================================================================

inductive Normal : Nat → Nat → List Bool → Prop
  | nil : Normal 0 0 []
  | one (n k : Nat) (w : List Bool) : Normal n k w → Normal (n + 1) (1 + 2 * k) (true :: true :: w)
  | zero (n k : Nat) (w : List Bool) : Normal n k w → Normal (n + 1) (2 * k) (true :: false :: w)

lemma Normal_eq {n n' k k' : Nat} {w w' : List Bool}
    (h : Normal n k w) (hn : n = n') (hk : k = k') (hw : w = w') :
    Normal n' k' w' := by
  subst hn; subst hk; subst hw; exact h

lemma normal_num {n k : Nat} {w : List Bool} (h : Normal n k w) :
    Num (2 * n) (2 ^ n - 1) k w := by
  induction h with
  | nil => exact Num.nil
  | one n k w _ ih =>
    have hp := pow2_pos n
    exact Num_eq (Num.A _ _ _ _ (Num.A _ _ _ _ ih)) (by omega) (by rw [Nat.pow_succ]; omega) (by omega) rfl
  | zero n k w _ ih =>
    have hp := pow2_pos n
    exact Num_eq (Num.A _ _ _ _ (Num.B _ _ _ _ ih)) (by omega) (by rw [Nat.pow_succ]; omega) (by omega) rfl

lemma normal_bound {n k : Nat} {w : List Bool} (h : Normal n k w) : k < 2 ^ n := by
  induction h with
  | nil => simp
  | one n k w _ ih => rw [Nat.pow_succ]; omega
  | zero n k w _ ih => rw [Nat.pow_succ]; omega

lemma normal_length {n k : Nat} {w : List Bool} (h : Normal n k w) : w.length = 2 * n :=
  Num_length (normal_num h)

lemma normal_head {n k : Nat} {w : List Bool} (h : Normal n k w) (hn : 0 < n) :
    ∃ v, w = true :: v := by
  cases h with
  | nil => omega
  | one _ _ w _ => exact ⟨true :: w, rfl⟩
  | zero _ _ w _ => exact ⟨false :: w, rfl⟩

lemma num_normal : ∀ (n : Nat) {k : Nat} {w : List Bool},
    Num (2 * n) (2 ^ n - 1) k w → Normal n k w := by
  intro n
  induction n with
  | zero =>
    intro k w h
    have hl := Num_length h
    rcases w with _ | ⟨b, w⟩
    · rcases Num_inv_nil h with ⟨_, _, rfl⟩
      exact Normal.nil
    · simp at hl
  | succ n ih =>
    intro k w h
    have hp := pow2_pos n
    have hp1 : 2 ^ (n + 1) - 1 = 1 + (2 ^ n - 1) * 2 := by rw [Nat.pow_succ]; omega
    have hl := Num_length h
    rcases w with _ | ⟨b, _ | ⟨c, w1⟩⟩
    · simp at hl
    · simp at hl; omega
    · rcases Num_inv_cons h with ⟨n0, o0, hn0, he0, h0⟩
      cases b
      · simp at he0; omega
      · simp at he0
        rcases Num_inv_cons h0 with ⟨n1, o1, hn1, he1, h1⟩
        have h1' : Num (2 * n) (2 ^ n - 1) o1 w1 :=
          Num_eq h1 (by omega) (by omega) rfl rfl
        cases c
        · simp at he1
          exact Normal_eq (Normal.zero n o1 w1 (ih h1')) rfl (by omega) rfl
        · simp at he1
          exact Normal_eq (Normal.one n o1 w1 (ih h1')) rfl (by omega) rfl

lemma normal_full_tape {n k : Nat} {w : List Bool} (h : Normal n k w) (hk : k = 2 ^ n - 1) :
    l_tape w = ld0 ^ n := by
  induction h with
  | nil => rfl
  | one n k w _ ih =>
    have hp := pow2_pos n
    have hk' : k = 2 ^ n - 1 := by rw [Nat.pow_succ] at hk; omega
    simp [l_tape, digit, Half, ld0, pow_succ_list, ih hk']
  | zero n k w _ _ =>
    have hp := pow2_pos n
    rw [Nat.pow_succ] at hk
    omega

lemma normal_zero_tape {n k : Nat} {w : List Bool} (h : Normal n k w) (hk : k = 0) :
    l_tape w = ld1 ^ n := by
  induction h with
  | nil => rfl
  | one _ _ _ _ _ => omega
  | zero n k w _ ih =>
    have hk' : k = 0 := by omega
    simp [l_tape, digit, Half, ld1, pow_succ_list, ih hk']

lemma normal_full (n : Nat) : Normal n (2 ^ n - 1) (List.replicate (2 * n) true) := by
  induction n with
  | zero => exact Normal.nil
  | succ n ih =>
    have hp := pow2_pos n
    have hrep : List.replicate (2 * (n + 1)) true = true :: true :: List.replicate (2 * n) true := by
      rw [show 2 * (n + 1) = (2 * n) + 2 by omega]
      rfl
    rw [hrep]
    exact Normal_eq (Normal.one n (2 ^ n - 1) (List.replicate (2 * n) true) ih)
      rfl (by rw [Nat.pow_succ]; omega) rfl

lemma normal_zero (n : Nat) : ∃ w, Normal n 0 w := by
  induction n with
  | zero => exact ⟨[], Normal.nil⟩
  | succ n ih =>
    rcases ih with ⟨w, hw⟩
    exact ⟨true :: false :: w, Normal_eq (Normal.zero n 0 w hw) rfl (by omega) rfl⟩

lemma l_tape_append (u v : List Bool) : l_tape (u ++ v) = l_tape u ++ l_tape v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [l_tape, ih, List.append_assoc]

lemma l_tape_replicate_true (m : Nat) (w : List Bool) :
    l_tape (List.replicate m true ++ w) = (Half 0) ^ m ++ l_tape w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, l_tape_cons, ih, pow_succ_list]
    simp [digit, List.append_assoc]

lemma l_tape_replicate_false (m : Nat) (w : List Bool) :
    l_tape (List.replicate m false ++ w) = (Half 1) ^ m ++ l_tape w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, l_tape_cons, ih, pow_succ_list]
    simp [digit, List.append_assoc]

lemma Num_AA {n e o : Nat} {w : List Bool} (m : Nat) (h : Num n e o w) :
    Num (n + 2 * m) ((e + 1) * 2 ^ m - 1) ((o + 1) * 2 ^ m - 1) (List.replicate (2 * m) true ++ w) := by
  induction m with
  | zero =>
    exact Num_eq h (by omega) (by omega) (by omega) rfl
  | succ m ih =>
    have hp := pow2_pos m
    have hrep : List.replicate (2 * (m + 1)) true ++ w =
        true :: true :: (List.replicate (2 * m) true ++ w) := by
      rw [show 2 * (m + 1) = 2 + 2 * m by omega, List.replicate_add]
      rfl
    rw [hrep]
    have h1 : 1 + ((e + 1) * 2 ^ m - 1) * 2 = (e + 1) * 2 ^ (m + 1) - 1 := by
      have hmul : (e + 1) * 2 ^ (m + 1) = ((e + 1) * 2 ^ m) * 2 := by rw [Nat.pow_succ]; ring
      have hpos : 1 ≤ (e + 1) * 2 ^ m := Nat.mul_pos (by omega) hp
      rw [hmul]; omega
    have h2 : 1 + ((o + 1) * 2 ^ m - 1) * 2 = (o + 1) * 2 ^ (m + 1) - 1 := by
      have hmul : (o + 1) * 2 ^ (m + 1) = ((o + 1) * 2 ^ m) * 2 := by rw [Nat.pow_succ]; ring
      have hpos : 1 ≤ (o + 1) * 2 ^ m := Nat.mul_pos (by omega) hp
      rw [hmul]; omega
    exact Num_eq (Num.A _ _ _ _ (Num.A _ _ _ _ ih)) (by omega) h1 h2 rfl

lemma Num_Aodd {n e o : Nat} {w : List Bool} (m : Nat) (h : Num n e o w) :
    Num (n + 2 * m + 1) ((o + 1) * 2 ^ (m + 1) - 1) ((e + 1) * 2 ^ m - 1)
      (List.replicate (2 * m + 1) true ++ w) := by
  have hp := pow2_pos m
  have hAA := Num_AA m h
  have hrep : List.replicate (2 * m + 1) true ++ w =
      true :: (List.replicate (2 * m) true ++ w) := by
    rw [show 2 * m + 1 = 1 + 2 * m by omega, List.replicate_add]
    rfl
  rw [hrep]
  have h1 : 1 + ((o + 1) * 2 ^ m - 1) * 2 = (o + 1) * 2 ^ (m + 1) - 1 := by
    have hmul : (o + 1) * 2 ^ (m + 1) = ((o + 1) * 2 ^ m) * 2 := by rw [Nat.pow_succ]; ring
    have hpos : 1 ≤ (o + 1) * 2 ^ m := Nat.mul_pos (by omega) hp
    rw [hmul]; omega
  exact Num_eq (Num.A _ _ _ _ hAA) (by omega) h1 rfl rfl

lemma normal_LInc {n k : Nat} {w : List Bool} (h : Normal n (1 + k) w) :
    ∃ w', Normal n k w' ∧ ∀ l r,
      ((l <+ l_tape w) <{{C}} r) [target_tm]⊢⁺
      ((l <+ l_tape w') {{B}}> r) := by
  have hb := normal_bound h
  have hn : 0 < n := by
    cases n with
    | zero => simp at hb
    | succ n => omega
  rcases normal_head h hn with ⟨v, rfl⟩
  rcases LInc_num (normal_num h) with ⟨e', v', hN, hle, hS⟩
  rcases Num_bounds hN with ⟨hmax, _⟩
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hdiv] at hmax
  have he' : e' = 2 ^ n - 1 := by omega
  subst he'
  exact ⟨true :: v', num_normal n hN, hS⟩

-- ============================================================================
-- Section 6: HalfZero & HalfDrain
-- ============================================================================

lemma zero_pair {n e : Nat} {b c : Bool} {w : List Bool} (h : Num (2 + n) e 0 (b :: c :: w)) :
    c = false ∧ ∃ e', Num n e' 0 w := by
  rcases Num_inv_cons h with ⟨n0, o0, hn0, _, h0⟩
  rcases Num_inv_cons h0 with ⟨n1, o1, hn1, he1, h1⟩
  cases c
  · simp at he1
    exact ⟨rfl, o0, Num_eq h1 (by omega) rfl (by omega) rfl⟩
  · simp at he1; omega

lemma zero_even : ∀ (m : Nat) {e : Nat} {w : List Bool},
    Num (2 * m) e 0 w → ∃ bs : List (Fin 2), bs.length = m ∧ l_tape w = Marked bs := by
  intro m
  induction m with
  | zero =>
    intro e w h
    have hl := Num_length h
    rcases w with _ | ⟨b, w⟩
    · exact ⟨[], rfl, rfl⟩
    · simp at hl
  | succ m ih =>
    intro e w h
    have hl := Num_length h
    rcases w with _ | ⟨b, _ | ⟨c, w⟩⟩
    · simp at hl
    · simp at hl; omega
    · have h' : Num (2 + 2 * m) e 0 (b :: c :: w) := Num_eq h (by omega) rfl rfl rfl
      rcases zero_pair h' with ⟨rfl, e', hw⟩
      rcases ih hw with ⟨bs, hbs, ht⟩
      refine ⟨(if b then 0 else 1) :: bs, by simp [hbs], ?_⟩
      simp [l_tape, digit, Marked, ht, List.append_assoc]

lemma zero_odd : ∀ (m : Nat) {e : Nat} {w : List Bool},
    Num (2 * m + 1) e 0 w →
    ∃ (bs : List (Fin 2)) (b : Fin 2), bs.length = m ∧ l_tape w = Marked bs ++ Half b := by
  intro m
  induction m with
  | zero =>
    intro e w h
    have hl := Num_length h
    rcases w with _ | ⟨b, _ | ⟨c, w⟩⟩
    · simp at hl
    · refine ⟨[], if b then 0 else 1, rfl, ?_⟩
      simp [l_tape, digit, Marked]
    · simp at hl
  | succ m ih =>
    intro e w h
    have hl := Num_length h
    rcases w with _ | ⟨b, _ | ⟨c, w⟩⟩
    · simp at hl
    · simp at hl
    · have h' : Num (2 + (2 * m + 1)) e 0 (b :: c :: w) := Num_eq h (by omega) rfl rfl rfl
      rcases zero_pair h' with ⟨rfl, e', hw⟩
      rcases ih hw with ⟨bs, d, hbs, ht⟩
      refine ⟨(if b then 0 else 1) :: bs, d, by simp [hbs], ?_⟩
      simp [l_tape, digit, Marked, ht, List.append_assoc]

lemma zero_even_A {m e : Nat} {w : List Bool} (h : Num (2 * m) e 0 (true :: w)) :
    ∃ bs : List (Fin 2), bs.length + 1 = m ∧ l_tape (true :: w) = Half 0 ++ Half 1 ++ Marked bs := by
  cases m with
  | zero =>
    have hl := Num_length h
    simp at hl
  | succ m =>
    have hl := Num_length h
    rcases w with _ | ⟨c, w⟩
    · simp at hl; omega
    · have h' : Num (2 + 2 * m) e 0 (true :: c :: w) := Num_eq h (by omega) rfl rfl rfl
      rcases zero_pair h' with ⟨rfl, e', hw⟩
      rcases zero_even m hw with ⟨bs, hbs, ht⟩
      refine ⟨bs, by omega, ?_⟩
      simp [l_tape, digit, ht, List.append_assoc]

lemma zero_odd_A {m e : Nat} {w : List Bool} (h : Num (2 * m + 1) e 0 (true :: w)) :
    (m = 0 ∧ w = []) ∨
    ∃ (bs : List (Fin 2)) (b : Fin 2), bs.length + 1 = m ∧
      l_tape (true :: w) = Half 0 ++ Half 1 ++ Marked bs ++ Half b := by
  cases m with
  | zero =>
    have hl := Num_length h
    rcases w with _ | ⟨c, w⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · simp at hl
  | succ m =>
    have hl := Num_length h
    rcases w with _ | ⟨c, w⟩
    · simp at hl
    · have h' : Num (2 + (2 * m + 1)) e 0 (true :: c :: w) := Num_eq h (by omega) rfl rfl rfl
      rcases zero_pair h' with ⟨rfl, e', hw⟩
      rcases zero_odd m hw with ⟨bs, b, hbs, ht⟩
      refine Or.inr ⟨bs, b, by omega, ?_⟩
      simp [l_tape, digit, ht, List.append_assoc]

lemma LZeroEven_num {m e : Nat} {w : List Bool} (r : ListBlank (Fin 2))
    (h : Num (2 * m) e 0 (true :: w)) :
    ((ldh <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ m) {{B}}> ([1] +> r)) := by
  rcases zero_even_A h with ⟨bs, rfl, ht⟩
  have heq : ldh <+ l_tape (true :: w) = ldh <+ Marked bs <+ Half 1 <+ Half 0 := by
    rw [ht]; simp [listblank_append_assoc]
  rw [heq]
  exact LZeroEven r bs

lemma LZeroOdd_num {m e : Nat} {w : List Bool} (r : ListBlank (Fin 2))
    (h : Num (2 * m + 1) e 0 (true :: w)) :
    ((ldh <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ m <+ Half 0) {{B}}> ([1, 1] +> r)) := by
  rcases zero_odd_A h with ⟨rfl, rfl⟩ | ⟨bs, b, rfl, ht⟩
  · simpa [l_tape, digit] using! LSingle r
  · have heq : ldh <+ l_tape (true :: w) = ldh <+ Half b <+ Marked bs <+ Half 1 <+ Half 0 := by
      rw [ht]; simp [listblank_append_assoc]
    rw [heq]
    exact LZeroOdd r bs b

lemma S_even_bound (m e o : Nat) (w : List Bool) (h : Num (2 * (1 + m)) e o w) :
    2 * ((2 + e) / 2) + 1 ≤ 2 ^ (2 + m) - 1 := by
  rcases Num_bounds h with ⟨he, _⟩
  have hdiv : (2 * (1 + m) + 1) / 2 = 1 + m := by omega
  rw [hdiv] at he
  have hp0 := pow2_pos m
  have hp1 : 2 ≤ 2 ^ (1 + m) := by rw [Nat.add_comm 1 m, Nat.pow_succ]; omega
  have hp : 2 ^ (2 + m) = 2 * 2 ^ (1 + m) := by
    rw [show 2 + m = (1 + m) + 1 by omega, Nat.pow_succ]
    omega
  rw [hp]
  omega

lemma S_odd_bound (m e o : Nat) (w : List Bool) (h : Num (2 * m + 1) e o w) :
    2 + e ≤ 2 ^ (1 + m) + 1 := by
  rcases Num_bounds h with ⟨he, _⟩
  have hdiv : (2 * m + 1 + 1) / 2 = 1 + m := by omega
  rw [hdiv] at he
  omega

lemma Drain_even {m e o : Nat} {w : List Bool} {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Num (2 * m) e o (true :: w)) (hr : RC z r) :
    ∃ r', RC (z + o) r' ∧
      ((ldh <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢⁺
      ((ldh <+ ld0 ^ m) {{B}}> ([1] +> r')) := by
  have hn' : Num (2 * m) e (o + 0) (true :: w) := Num_eq hn rfl rfl (by omega) rfl
  rcases RC_pairs o hn' hr with ⟨e', w', r', hn1, _, hr1, hS⟩
  exact ⟨r', hr1, stepStar_stepPlus_trans (hS ldh) (LZeroEven_num r' hn1)⟩

lemma Drain_odd {m e o : Nat} {w : List Bool} {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Num (2 * m + 1) e o (true :: w)) (hr : RC z r) :
    ∃ r', RC ((z + o) / 2) r' ∧
      ((ldh <+ l_tape (true :: w)) <{{C}} r) [target_tm]⊢⁺
      ((ldh <+ ld0 ^ (1 + m)) <{{C}} ([1, 0] +> r')) := by
  have hn' : Num (2 * m + 1) e (o + 0) (true :: w) := Num_eq hn rfl rfl (by omega) rfl
  rcases RC_pairs o hn' hr with ⟨e', w', s, hn1, _, hs, hS⟩
  rcases RC_tail hs with ⟨b, r', hr', rfl⟩
  refine ⟨r', hr', ?_⟩
  have s1 := hS ldh
  have s2 := LZeroOdd_num ([b, 0, 0] +> r') hn1
  have s3 := R11Bit (ldh <+ ld0 ^ m <+ Half 0) r' b
  have heq : ldh <+ ld0 ^ m <+ Half 0 <+ Half 0 = ldh <+ ld0 ^ (1 + m) := by
    rw [← left_ld0_eq, Nat.add_comm 1 m, left_pow_succ ldh ld0 m]
  rw [heq] at s3
  exact stepStar_stepPlus_trans s1 (stepPlus_trans s2 s3)

lemma Drain_S_even {m e o : Nat} {w : List Bool} (hn : Num (2 * m) e o w) :
    ∃ r', RC ((2 + e) / 2) r' ∧
      ((ldh <+ l_tape w <+ s_tag) {{D}}> default) [target_tm]⊢⁺
      ((ldh <+ ld0 ^ (1 + m)) <{{C}} ([1, 0] +> r')) := by
  have hn' : Num (2 * m + 1) (1 + o * 2) e (true :: w) :=
    Num_eq (Num.A _ _ _ _ hn) (by omega) rfl rfl rfl
  have hr2 : RC 2 ([0, 0, 0, 1] +> default) := by
    have h0 : RC 2 (rd0 +> (rd1 +> default)) :=
      RC_eq (RC.d0 1 (rd1 +> default) (RC_eq (RC.d1 0 default RC.zero) (by omega) rfl)) (by omega) rfl
    have heq : rd0 +> (rd1 +> (default : ListBlank (Fin 2))) = [0, 0, 0, 1] +> default := by
      simp [rd0, rd1]
    rwa [heq] at h0
  rcases Drain_odd hn' hr2 with ⟨r', hr', hS⟩
  refine ⟨r', hr', ?_⟩
  have s1 := SZeroEntry (ldh <+ l_tape w) default
  have h000 : ([0, 0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
    rd0_append_default
  rw [h000] at s1
  have ht : ldh <+ l_tape (true :: w) = ldh <+ l_tape w <+ Half 0 := by simp [l_tape, digit]
  rw [ht] at hS
  exact stepPlus_trans s1 hS

lemma Drain_S_odd {m e o : Nat} {w : List Bool} (hn : Num (2 * m + 1) e o w) :
    ∃ r', RC (2 + e) r' ∧
      ((ldh <+ l_tape w <+ s_tag) {{D}}> default) [target_tm]⊢⁺
      ((ldh <+ ld0 ^ (1 + m)) {{B}}> ([1] +> r')) := by
  have hn' : Num (2 * (1 + m)) (1 + o * 2) e (true :: w) :=
    Num_eq (Num.A _ _ _ _ hn) (by omega) rfl rfl rfl
  have hr2 : RC 2 ([0, 0, 0, 1] +> default) := by
    have h0 : RC 2 (rd0 +> (rd1 +> default)) :=
      RC_eq (RC.d0 1 (rd1 +> default) (RC_eq (RC.d1 0 default RC.zero) (by omega) rfl)) (by omega) rfl
    have heq : rd0 +> (rd1 +> (default : ListBlank (Fin 2))) = [0, 0, 0, 1] +> default := by
      simp [rd0, rd1]
    rwa [heq] at h0
  rcases Drain_even hn' hr2 with ⟨r', hr', hS⟩
  refine ⟨r', hr', ?_⟩
  have s1 := SZeroEntry (ldh <+ l_tape w) default
  have h000 : ([0, 0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
    rd0_append_default
  rw [h000] at s1
  have ht : ldh <+ l_tape (true :: w) = ldh <+ l_tape w <+ Half 0 := by simp [l_tape, digit]
  rw [ht] at hS
  exact stepPlus_trans s1 hS

-- ============================================================================
-- Section 7: HalfST & STClosure
-- ============================================================================

lemma S000_borrow {n e o : Nat} {b : Bool} {v : List Bool} (h : Num n (2 + e) o (b :: v)) :
    ∃ e' u, Borrow v u ∧ Num (n + 1) e' e (true :: b :: true :: u) ∧ 2 * o + 1 ≤ e' := by
  rcases Num_inv_cons h with ⟨n0, o0, rfl, he0, h0⟩
  have h0' : Num n0 o (1 + (o0 - 1)) v := by
    refine Num_eq h0 rfl rfl ?_ rfl
    cases b <;> simp at he0 <;> omega
  rcases Borrow_ex n0 h0' with ⟨u, hb⟩
  rcases Borrow_num hb h0' with ⟨e', hN, hle⟩
  refine ⟨1 + e' * 2, u, hb, ?_, by omega⟩
  cases b
  · simp at he0
    exact Num_eq (Num.A _ _ _ _ (Num.B _ _ _ _ hN)) (by omega) rfl (by omega) rfl
  · simp at he0
    exact Num_eq (Num.A _ _ _ _ (Num.A _ _ _ _ hN)) (by omega) rfl (by omega) rfl

lemma ST_S100 {n e o : Nat} {w : List Bool} (h : Num n e o w) :
    Num (n + 1) (2 * o) e (false :: w) ∧ ∀ l r,
      ((l <+ l_tape w <+ s_tag) {{D}}> (rd1 +> r)) [target_tm]⊢⁺
      ((l <+ l_tape (false :: w) <+ s_tag) {{D}}> r) := by
  refine ⟨Num_eq (Num.B _ _ _ _ h) (by omega) (by omega) rfl rfl, fun l r => ?_⟩
  simpa [l_tape, digit, rd1] using! S100 (l <+ l_tape w) r

lemma ST_T100 {n e o : Nat} {w : List Bool} (h : Num n e (1 + o) w) :
    ∃ e' w', Num (n + 1) (1 + 2 * o) e' (true :: w') ∧ e ≤ e' ∧ ∀ l r,
      ((l <+ l_tape w <+ t_tag) {{D}}> (rd1 +> r)) [target_tm]⊢⁺
      ((l <+ l_tape (true :: w') <+ s_tag) {{D}}> r) := by
  rcases Borrow_ex n h with ⟨u, hb⟩
  rcases Borrow_num hb h with ⟨e', hN, hle⟩
  refine ⟨e', true :: u, Num_eq (Num.A _ _ _ _ hN) (by omega) (by omega) rfl rfl, hle, fun l r => ?_⟩
  have s1 := T100 (l <+ l_tape w) r
  have s2 := Borrow_spec hb l (ones ^ 6 +> r)
  have s3 := SOnes (l <+ l_tape u) r 1
  have ht : l <+ l_tape (true :: true :: u) = l <+ l_tape u <+ ld0 ^ 1 := by
    simp [l_tape, digit, ld0, Half, pow_succ_list, pow_zero_list]
  rw [ht]
  exact stepPlus_trans s1 (stepPlus_stepStar_trans s2 s3)

lemma ST_S000 {n e o : Nat} {w : List Bool} (h : Num n (2 + e) o w) :
    ∃ e' w', Num (n + 1) e' e (true :: w') ∧ 2 * o + 1 ≤ e' ∧ ∀ l r,
      ((l <+ l_tape w <+ s_tag) {{D}}> (rd0 +> r)) [target_tm]⊢⁺
      ((l <+ l_tape (true :: w') <+ t_tag) {{D}}> r) := by
  rcases w with _ | ⟨b, v⟩
  · rcases Num_inv_nil h with ⟨_, _, _⟩; omega
  · rcases S000_borrow h with ⟨e', u, hb, hN, hle⟩
    refine ⟨e', b :: true :: u, hN, hle, fun l r => ?_⟩
    have ht1 : l <+ l_tape (b :: v) = l <+ l_tape v <+ Half (if b then 0 else 1) := by
      simp [l_tape, digit]
    have ht2 : l <+ l_tape (true :: b :: true :: u) =
        l <+ l_tape u <+ Half 0 <+ Half (if b then 0 else 1) <+ Half 0 := by
      simp [l_tape, digit]
    rw [ht1, ht2]
    have s1 := S000 (l <+ l_tape v) r (if b then 0 else 1)
    have s2 := Borrow_spec hb l (ones ^ 5 +> ([Opp (if b then 0 else 1), 0, 0, 1] +> r))
    have s3 := S000_end (l <+ l_tape u) r (if b then 0 else 1)
    exact stepPlus_trans s1 (stepPlus_trans s2 s3)

def SC (w : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((ldh <+ l_tape w <+ s_tag) {{D}}> r)

def TC (w : List Bool) (h : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((ldh <+ l_tape (true :: w) <+ (Half 1) ^ h <+ t_tag) {{D}}> r)

lemma TC_word (w : List Bool) (h : Nat) (r : ListBlank (Fin 2)) :
    TC w h r = ((ldh <+ l_tape (List.replicate h false ++ true :: w) <+ t_tag) {{D}}> r) := by
  simp [TC, l_tape_replicate_false, listblank_append_assoc]

lemma Num_B_lower (h : Nat) {n e o : Nat} {w : List Bool} (k : Nat)
    (hn : Num n e o w) (he : k ≤ e) (ho : k ≤ o) :
    ∃ E O, Num (n + h) E O (List.replicate h false ++ w) ∧ k ≤ E ∧ k ≤ O := by
  induction h with
  | zero => exact ⟨e, o, Num_eq hn (by omega) rfl rfl rfl, he, ho⟩
  | succ h ih =>
    rcases ih with ⟨E, O, hN, hE, hO⟩
    refine ⟨O * 2, E, ?_, by omega, hE⟩
    rw [List.replicate_succ, List.cons_append]
    exact Num_eq (Num.B _ _ _ _ hN) (by omega) rfl rfl rfl

inductive STAllowed : Nat → Cfg (Fin 2) (Fin 6) → Prop
  | S (n e o : Nat) (w : List Bool) (z : Nat) (r : ListBlank (Fin 2)) :
      Num n e o w → 2 ≤ n → 2 * z ≤ e → z ≤ o → RC z r →
      STAllowed z (SC w r)
  | T (n e o : Nat) (w : List Bool) (h z : Nat) (r : ListBlank (Fin 2)) :
      Num n e o (true :: w) → 2 ≤ n → 0 < z →
      2 ^ (h + 2) * z + 1 ≤ e → 2 ^ (h + 2) * (z - 1) + 2 ≤ o → RC z r →
      STAllowed z (TC w h r)

lemma ST_zero_shape {c : Cfg (Fin 2) (Fin 6)} (h : STAllowed 0 c) :
    ∃ n e o w, Num n e o w ∧ 2 ≤ n ∧ c = SC w default := by
  generalize hz : (0 : Nat) = z at h
  cases h with
  | S n e o w _ r hn hl _ _ hr =>
    subst hz
    rw [RC_zero_unique hr]
    exact ⟨n, e, o, w, hn, hl, rfl⟩
  | T _ _ _ _ _ _ _ _ _ hpos _ _ _ => omega

lemma ST_positive_step {z : Nat} {c : Cfg (Fin 2) (Fin 6)} (h : STAllowed z c) (hz : 0 < z) :
    ∃ c', STAllowed (z / 2) c' ∧ c [target_tm]⊢⁺ c' := by
  cases h with
  | S n e o w z r hn hl he ho hr =>
    cases hr with
    | zero => omega
    | d0 q s hrc =>
      have hdiv : q * 2 / 2 = q := by omega
      rw [hdiv]
      have hn' : Num n (2 + (e - 2)) o w := Num_eq hn rfl (by omega) rfl rfl
      rcases ST_S000 hn' with ⟨e', w', hN, hle, hS⟩
      refine ⟨TC w' 0 s, ?_, hS ldh s⟩
      exact STAllowed.T (n + 1) e' (e - 2) w' 0 q s hN (by omega) (by omega) (by omega) (by omega) hrc
    | d1 q s hrc =>
      have hdiv : (1 + q * 2) / 2 = q := by omega
      rw [hdiv]
      rcases ST_S100 hn with ⟨hN, hS⟩
      refine ⟨SC (false :: w) s, ?_, hS ldh s⟩
      exact STAllowed.S (n + 1) (2 * o) e (false :: w) q s hN (by omega) (by omega) (by omega) hrc
  | T n e o w h z r hn hl hpos he ho hr =>
    have hp := pow2_pos (h + 2)
    cases hr with
    | zero => omega
    | d0 q s hrc =>
      have hdiv : q * 2 / 2 = q := by omega
      rw [hdiv]
      have hq : 0 < q := by omega
      have hb : 2 ^ (h + 2) ≤ o := by
        have : 2 ^ (h + 2) * 1 ≤ 2 ^ (h + 2) * (q * 2 - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hn' : Num n e (2 ^ (h + 2) + (o - 2 ^ (h + 2))) (true :: w) :=
        Num_eq hn rfl rfl (by omega) rfl
      rcases TZero h ldh s hn' with ⟨e', w', hN, hle, hS⟩
      refine ⟨TC w' (h + 1) s, ?_, hS⟩
      have hcap : 2 ^ (h + 1 + 2) = 2 ^ (h + 2) * 2 := by
        rw [show h + 1 + 2 = (h + 2) + 1 by omega, Nat.pow_succ]
      have he' : 2 ^ (h + 1 + 2) * q + 1 ≤ e' := by
        rw [hcap]
        have : 2 ^ (h + 2) * 2 * q = 2 ^ (h + 2) * (q * 2) := by ring
        omega
      have ho' : 2 ^ (h + 1 + 2) * (q - 1) + 2 ≤ o - 2 ^ (h + 2) := by
        rw [hcap]
        have : 2 ^ (h + 2) * (q * 2 - 1) = 2 ^ (h + 2) * 2 * (q - 1) + 2 ^ (h + 2) := by
          have hq1 : q * 2 - 1 = 2 * (q - 1) + 1 := by omega
          rw [hq1]; ring
        omega
      exact STAllowed.T n e' (o - 2 ^ (h + 2)) w' (h + 1) q s hN hl hq he' ho' hrc
    | d1 q s hrc =>
      have hdiv : (1 + q * 2) / 2 = q := by omega
      rw [hdiv]
      have hke : q + 1 ≤ e := by
        have : 1 * (1 + q * 2) ≤ 2 ^ (h + 2) * (1 + q * 2) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hko : q + 1 ≤ o := by
        have : 1 * (q * 2) ≤ 2 ^ (h + 2) * (1 + q * 2 - 1) := by
          rw [show 1 + q * 2 - 1 = q * 2 by omega]
          exact Nat.mul_le_mul_right _ (by omega)
        omega
      rcases Num_B_lower h (q + 1) hn hke hko with ⟨E, O, hN, hE, hO⟩
      have hN' : Num (n + h) E (1 + (O - 1)) (List.replicate h false ++ true :: w) :=
        Num_eq hN rfl rfl (by omega) rfl
      rcases ST_T100 hN' with ⟨e', w', hN2, hle, hS⟩
      refine ⟨SC (true :: w') s, ?_, ?_⟩
      · exact STAllowed.S (n + h + 1) (1 + 2 * (O - 1)) e' (true :: w') q s
          hN2 (by omega) (by omega) (by omega) hrc
      · rw [TC_word]
        exact hS ldh s

lemma ST_to_zero : ∀ (z : Nat) {c : Cfg (Fin 2) (Fin 6)},
    STAllowed z c → ∃ c', STAllowed 0 c' ∧ c [target_tm]⊢* c' := by
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro c hA
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · exact ⟨c, hA, stepStar_refl _⟩
    · rcases ST_positive_step hA hz with ⟨c1, hA1, hS1⟩
      rcases ih (z / 2) (by omega) hA1 with ⟨c2, hA2, hS2⟩
      exact ⟨c2, hA2, stepStar_trans (stepPlus_to_stepStar hS1) hS2⟩

-- ============================================================================
-- Section 8: HalfTen & TenClosure
-- ============================================================================

lemma two_zeros_comm_rd0_pow (t : Nat) (s : ListBlank (Fin 2)) :
    ([0, 0] : List (Fin 2)) +> (rd0 ^ t +> s) = rd0 ^ t +> ([0, 0] +> s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [right_pow_succ rd0 t s, right_pow_succ rd0 t ([0, 0] +> s), ← ih]
    rfl

lemma ten_prefix (t : Nat) (r : ListBlank (Fin 2)) :
    ([1, 0] : List (Fin 2)) +> (rd0 ^ (1 + t) +> (rd1 +> r)) =
    rd1 +> (rd0 ^ t +> ([0, 0, 1, 0, 0] +> r)) := by
  rw [Nat.add_comm 1 t, right_pow_succ rd0 t (rd1 +> r)]
  change rd1 +> (([0, 0] : List (Fin 2)) +> (rd0 ^ t +> (rd1 +> r))) =
    rd1 +> (rd0 ^ t +> (([0, 0] : List (Fin 2)) +> (rd1 +> r)))
  rw [two_zeros_comm_rd0_pow t (rd1 +> r)]

lemma A_head {k : Nat} (w : List Bool) (hk : 0 < k) :
    ∃ v, List.replicate k true ++ w = true :: v := by
  cases k with
  | zero => omega
  | succ k => exact ⟨List.replicate k true ++ w, rfl⟩

lemma flip_A {n e o : Nat} {w : List Bool} (h : Num n e o (true :: w)) :
    Num n (e - 1) o (false :: w) ∧ 1 ≤ e := by
  rcases Num_inv_true h with ⟨n0, o0, rfl, rfl, h0⟩
  exact ⟨Num_eq (Num.B _ _ _ _ h0) rfl (by omega) rfl rfl, by omega⟩

lemma Ten_pre {n e o : Nat} {w : List Bool} (t : Nat) (l r : ListBlank (Fin 2))
    (hn : Num n e (2 ^ (1 + t) - 1 + o) (true :: w)) :
    ∃ e' w', Num n e' o (true :: w') ∧ e ≤ e' ∧
      ((l <+ l_tape (true :: w)) <{{C}} ([1, 0] +> (rd0 ^ t +> (rd1 +> r)))) [target_tm]⊢⁺
      ((l <+ l_tape (true :: w')) {{B}}> (rd1 ^ t +> ([1, 0, 1, 0, 0] +> r))) := by
  cases t with
  | zero =>
    have hn' : Num n e (1 + o) (true :: w) := Num_eq hn rfl rfl (by simp) rfl
    rcases LInc_num hn' with ⟨e', w', h', hle, hS⟩
    exact ⟨e', w', h', hle, hS l ([1, 0, 1, 0, 0] +> r)⟩
  | succ t =>
    have hp := pow2_pos t
    have hp1 : 2 ≤ 2 ^ (1 + t) := by rw [Nat.add_comm 1 t, Nat.pow_succ]; omega
    have hn' : Num n e ((2 ^ (1 + t) - 2) + (2 ^ (1 + t) + o + 1)) (true :: w) :=
      Num_eq hn rfl rfl (by rw [show 1 + (t + 1) = (1 + t) + 1 by omega, Nat.pow_succ]; omega) rfl
    have hr : FC ([0, 0, 1, 0, 0] +> r) (1 + t) 1 (rd1 +> (rd0 ^ t +> ([0, 0, 1, 0, 0] +> r))) :=
      FC_eq (FC.d1 t 0 (rd0 ^ t +> ([0, 0, 1, 0, 0] +> r)) (FC_zero ([0, 0, 1, 0, 0] +> r) t))
        (by omega) (by omega) rfl
    rcases FC_pairs ([0, 0, 1, 0, 0] +> r) (1 + t) (2 ^ (1 + t) - 2) hn' hr (by omega)
      with ⟨e1, w1, r1, h1, hle1, hr1, hS1⟩
    have h1' : Num n e1 (1 + (2 ^ (1 + t) + o)) (true :: w1) :=
      Num_eq h1 rfl rfl (by omega) rfl
    rcases LInc_num h1' with ⟨e2, w2, h2, hle2, hL2⟩
    have hr1_eq : r1 = rd1 ^ (1 + t) +> ([0, 0, 1, 0, 0] +> r) :=
      FC_full_unique (FC_eq hr1 rfl (by omega) rfl)
    subst hr1_eq
    have h2' : Num n e2 ((2 ^ (1 + t) - 1) + (1 + o)) (true :: w2) :=
      Num_eq h2 rfl rfl (by omega) rfl
    rcases FC_pairs ([1, 0, 1, 0, 0] +> r) (1 + t) (2 ^ (1 + t) - 1) h2'
      (FC_zero ([1, 0, 1, 0, 0] +> r) (1 + t)) (by omega)
      with ⟨e3, w3, r3, h3, hle3, hr3, hS3⟩
    rcases LInc_num h3 with ⟨e4, w4, h4, hle4, hL4⟩
    have hr3_eq : r3 = rd1 ^ (1 + t) +> ([1, 0, 1, 0, 0] +> r) :=
      FC_full_unique (FC_eq hr3 rfl (by omega) rfl)
    subst hr3_eq
    refine ⟨e4, w4, h4, by omega, ?_⟩
    rw [show t + 1 = 1 + t by omega, ten_prefix t r]
    have s1 := hS1 l
    have s2 := hL2 l (rd1 ^ (1 + t) +> ([0, 0, 1, 0, 0] +> r))
    have s3 := RInc_rule (l <+ l_tape (true :: w2)) ([0, 1, 0, 0] +> r) (1 + t)
    have heq3 : ([0] : List (Fin 2)) +> ([0, 1, 0, 0] +> r) = [0, 0, 1, 0, 0] +> r := rfl
    have heq3' : ([1] : List (Fin 2)) +> ([0, 1, 0, 0] +> r) = [1, 0, 1, 0, 0] +> r := rfl
    rw [heq3, heq3'] at s3
    have s4 := hS3 l
    have s5 := hL4 l (rd1 ^ (1 + t) +> ([1, 0, 1, 0, 0] +> r))
    exact stepStar_stepPlus_trans s1
      (stepPlus_trans s2
        (stepPlus_trans s3
          (stepStar_stepPlus_trans s4 s5)))

lemma Ten_even_exit {n e o : Nat} {w : List Bool} (m : Nat) (l r : ListBlank (Fin 2))
    (h : Num n e (1 + o) (true :: w)) :
    ∃ n' e' o' v, Num n' e' o' (true :: v) ∧ n ≤ n' ∧
      2 * o + 1 ≤ e' ∧ e ≤ o' ∧
      ((l <+ l_tape (true :: w)) {{B}}> (rd1 ^ (m * 2) +> ([1, 0, 1, 0, 0] +> r))) [target_tm]⊢⁺
      ((l <+ l_tape (true :: v)) <{{C}} ([1, 0] +> r)) := by
  rcases LInc_num h with ⟨e1, w1, h1, hle, hL⟩
  have hN := Num_Aodd m h1
  rcases A_head (true :: w1) (show 0 < 2 * m + 1 by omega) with ⟨v, hv⟩
  have ht := l_tape_replicate_true (2 * m + 1) (true :: w1)
  rw [hv] at hN ht
  have hp := pow2_pos m
  have hp2 : 2 ≤ 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
  refine ⟨n + 2 * m + 1, (o + 1) * 2 ^ (m + 1) - 1, (e1 + 1) * 2 ^ m - 1, v,
    hN, by omega, ?_, ?_, ?_⟩
  · have : 2 * o + 2 ≤ (o + 1) * 2 ^ (m + 1) := by
      have : (o + 1) * 2 ≤ (o + 1) * 2 ^ (m + 1) := Nat.mul_le_mul_left _ hp2
      omega
    omega
  · have : e + 1 ≤ (e1 + 1) * 2 ^ m := by
      have : (e1 + 1) * 1 ≤ (e1 + 1) * 2 ^ m := Nat.mul_le_mul_left _ hp
      omega
    omega
  · have ht0 : l <+ l_tape (true :: w) = l <+ l_tape w <+ [1, 1] <+ [0] := by
      simp [l_tape, digit, Half]
    have s1 := R101EvenEntry (l <+ l_tape w <+ [1, 1]) r m
    rw [← ht0] at s1
    have s2 := hL l (ones ^ (m * 6 + 3) +> ([0, 0] +> r))
    have hmul : m * 6 + 3 = (2 * m + 1) * 3 := by omega
    rw [hmul] at s1 s2
    have s3 := R111Scan (l <+ l_tape (true :: w1)) ([0, 0] +> r) (2 * m + 1)
    have ht_v : l <+ l_tape (true :: v) = l <+ l_tape (true :: w1) <+ (Half 0) ^ (2 * m + 1) := by
      rw [ht, listblank_append_assoc]
    rw [← ht_v] at s3
    have s4 := RInc_rule (l <+ l_tape (true :: v)) ([0] +> r) 0
    have heq4 : rd1 ^ 0 +> ([0] +> ([0] +> r)) = [0, 0] +> r := rfl
    have heq4' : rd0 ^ 0 +> ([1] +> ([0] +> r)) = [1, 0] +> r := rfl
    rw [heq4, heq4'] at s4
    exact stepPlus_trans s1
      (stepPlus_trans s2
        (stepStar_stepPlus_trans s3 s4))

lemma Ten_odd_exit {n e o : Nat} {w : List Bool} (m : Nat) (l r : ListBlank (Fin 2))
    (h : Num n e o (true :: w)) :
    ∃ n' e' o' v, Num n' e' o' (true :: v) ∧ n ≤ n' ∧
      2 * e - 1 ≤ e' ∧ 2 * o + 1 ≤ o' ∧
      ((l <+ l_tape (true :: w)) {{B}}> (rd1 ^ (m * 2 + 1) +> ([1, 0, 1, 0, 0] +> r))) [target_tm]⊢⁺
      ((l <+ l_tape (true :: v)) <{{C}} ([1, 0] +> r)) := by
  rcases flip_A h with ⟨hF, he⟩
  have hN := Num_AA (m + 1) hF
  rcases A_head (false :: w) (show 0 < 2 * (m + 1) by omega) with ⟨v, hv⟩
  have ht := l_tape_replicate_true (2 * (m + 1)) (false :: w)
  rw [hv, half0_pairs_two_mul (m + 1)] at ht
  rw [hv] at hN
  have hp := pow2_pos m
  have hp2 : 2 ≤ 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
  refine ⟨n + 2 * (m + 1), (e - 1 + 1) * 2 ^ (m + 1) - 1, (o + 1) * 2 ^ (m + 1) - 1, v,
    hN, by omega, ?_, ?_, ?_⟩
  · have : e * 2 ≤ (e - 1 + 1) * 2 ^ (m + 1) := by
      rw [show e - 1 + 1 = e by omega]
      exact Nat.mul_le_mul_left e hp2
    omega
  · have : 2 * o + 2 ≤ (o + 1) * 2 ^ (m + 1) := by
      have : (o + 1) * 2 ≤ (o + 1) * 2 ^ (m + 1) := Nat.mul_le_mul_left _ hp2
      omega
    omega
  · have ht0 : l <+ l_tape (true :: w) = l <+ l_tape w <+ [1, 1] <+ [0] := by
      simp [l_tape, digit, Half]
    have s1 := ROv101Odd (l <+ l_tape w <+ [1, 1]) ([0, 0] +> r) m
    have heq1 : ([1, 0, 1] : List (Fin 2)) +> ([0, 0] +> r) = [1, 0, 1, 0, 0] +> r := rfl
    rw [← ht0, heq1] at s1
    have ht_v : l <+ l_tape (true :: v) = l <+ l_tape w <+ [1, 1] <+ [1] <+ ld0 ^ (m + 1) := by
      rw [ht]; simp [l_tape, digit, Half, listblank_append_assoc]
    rw [← ht_v] at s1
    have s2 := RInc_rule (l <+ l_tape (true :: v)) ([0] +> r) 0
    have heq2 : rd1 ^ 0 +> ([0] +> ([0] +> r)) = [0, 0] +> r := rfl
    have heq2' : rd0 ^ 0 +> ([1] +> ([0] +> r)) = [1, 0] +> r := rfl
    rw [heq2, heq2'] at s2
    exact stepPlus_trans s1 s2

def JC (w : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((ldh <+ l_tape (true :: w)) <{{C}} ([1, 0] +> r))

inductive TenAllowed : Nat → Cfg (Fin 2) (Fin 6) → Prop
  | J (n e o : Nat) (w : List Bool) (z : Nat) (r : ListBlank (Fin 2)) :
      Num n e o (true :: w) → 4 ≤ n → RC z r →
      (z = 0 ∨ (2 * z + 1 ≤ e ∧ 2 * z + 1 ≤ o)) →
      TenAllowed z (JC w r)

lemma Ten_zero_shape {c : Cfg (Fin 2) (Fin 6)} (h : TenAllowed 0 c) :
    ∃ n e o w, Num n e o (true :: w) ∧ 4 ≤ n ∧ c = JC w default := by
  cases h with
  | J n e o w _ r hn hl hr _ =>
    rw [RC_zero_unique hr]
    exact ⟨n, e, o, w, hn, hl, rfl⟩

lemma Ten_reserve (t q e o : Nat)
    (he : 2 * (2 ^ t * (1 + q * 2)) + 1 ≤ e)
    (ho : 2 * (2 ^ t * (1 + q * 2)) + 1 ≤ o) :
    2 ^ (1 + t) - 1 ≤ o ∧ 2 * q + 2 ≤ o - (2 ^ (1 + t) - 1) ∧ 2 * q + 1 ≤ e := by
  have hp := pow2_pos t
  have hp1 : 2 ^ (1 + t) = 2 * 2 ^ t := by rw [Nat.add_comm 1 t, Nat.pow_succ]; ring
  have h1 : 2 * (2 ^ t * (1 + q * 2)) = 2 ^ (1 + t) + 2 ^ (1 + t) * q * 2 := by
    rw [hp1]; ring
  have h2 : 1 * q * 2 ≤ 2 ^ (1 + t) * q * 2 := by
    have : 1 ≤ 2 ^ (1 + t) := pow2_pos (1 + t)
    exact Nat.mul_le_mul_right 2 (Nat.mul_le_mul_right q this)
  omega

lemma Ten_positive_step {z : Nat} {c : Cfg (Fin 2) (Fin 6)} (hA : TenAllowed z c) (hz : 0 < z) :
    ∃ q c', q < z ∧ TenAllowed q c' ∧ c [target_tm]⊢⁺ c' := by
  cases hA with
  | J n e o w z r hn hl hr hg =>
    rcases hg with rfl | ⟨he, ho⟩
    · omega
    · rcases RC_positive_split hr hz with ⟨t, q, s, rfl, hs, hez, hqz⟩
      have he' : 2 * (2 ^ t * (1 + q * 2)) + 1 ≤ e := by rw [← hez]; exact he
      have ho' : 2 * (2 ^ t * (1 + q * 2)) + 1 ≤ o := by rw [← hez]; exact ho
      rcases Ten_reserve t q e o he' ho' with ⟨hb, hbq, heq⟩
      set b := o - (2 ^ (1 + t) - 1)
      have hn' : Num n e (2 ^ (1 + t) - 1 + b) (true :: w) :=
        Num_eq hn rfl rfl (by omega) rfl
      rcases Ten_pre t ldh s hn' with ⟨e1, w1, h1, hle1, hS1⟩
      rcases nat_even_or_odd t with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have h1' : Num n e1 (1 + (b - 1)) (true :: w1) :=
          Num_eq h1 rfl rfl (by omega) rfl
        rcases Ten_even_exit m ldh s h1' with ⟨n2, e2, o2, w2, h2, hlen, hE, hO, hS2⟩
        refine ⟨q, JC w2 s, hqz, ?_, ?_⟩
        · exact TenAllowed.J n2 e2 o2 w2 q s h2 (by omega) hs (Or.inr ⟨by omega, by omega⟩)
        · rw [Nat.mul_comm 2 m] at hS1 ⊢
          exact stepPlus_trans hS1 hS2
      · rcases Ten_odd_exit m ldh s h1 with ⟨n2, e2, o2, w2, h2, hlen, hE, hO, hS2⟩
        refine ⟨q, JC w2 s, hqz, ?_, ?_⟩
        · exact TenAllowed.J n2 e2 o2 w2 q s h2 (by omega) hs (Or.inr ⟨by omega, by omega⟩)
        · rw [show 2 * m + 1 = m * 2 + 1 by omega] at hS1 ⊢
          exact stepPlus_trans hS1 hS2

lemma Ten_to_zero : ∀ (z : Nat) {c : Cfg (Fin 2) (Fin 6)},
    TenAllowed z c → ∃ c', TenAllowed 0 c' ∧ c [target_tm]⊢* c' := by
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro c hA
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · exact ⟨c, hA, stepStar_refl _⟩
    · rcases Ten_positive_step hA hz with ⟨q, c1, hq, hA1, hS1⟩
      rcases ih q hq hA1 with ⟨c2, hA2, hS2⟩
      exact ⟨c2, hA2, stepStar_trans (stepPlus_to_stepStar hS1) hS2⟩

-- ============================================================================
-- Section 9: HalfI, HalfTBoundary, PairUnion, NormalReturn, IClosure,
--            PairSpecial, Saturated, PairClosure
-- ============================================================================

lemma one_zero_comm_rd0_pow (t : Nat) (s : ListBlank (Fin 2)) :
    ([0] : List (Fin 2)) +> (rd0 ^ t +> s) = rd0 ^ t +> ([0] +> s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [right_pow_succ rd0 t s, right_pow_succ rd0 t ([0] +> s), ← ih]
    rfl

lemma FC_insert_one (r : ListBlank (Fin 2)) (t : Nat) :
    FC ([0, 1, 0, 0] +> r) (t + 1) 1 ([1] +> (rd0 ^ (t + 1) +> (rd1 +> r))) := by
  have h0 := FC.d1 t 0 (rd0 ^ t +> ([0, 1, 0, 0] +> r)) (FC_zero ([0, 1, 0, 0] +> r) t)
  have heq : rd1 +> (rd0 ^ t +> ([0, 1, 0, 0] +> r)) =
      [1] +> (rd0 ^ (t + 1) +> (rd1 +> r)) := by
    rw [right_pow_succ rd0 t (rd1 +> r)]
    change rd1 +> (rd0 ^ t +> (([0] : List (Fin 2)) +> (rd1 +> r))) =
      rd1 +> (([0] : List (Fin 2)) +> (rd0 ^ t +> (rd1 +> r)))
    rw [one_zero_comm_rd0_pow t (rd1 +> r)]
  exact FC_eq h0 rfl (by omega) heq

lemma normal_split {n k : Nat} {w : List Bool} (h : Normal n k w) (hk : 0 < k) :
    ∃ (v : List Bool) (a : Nat) (u : List Bool), Normal n (k - 1) v ∧
      l_tape w = ld1 ^ a ++ ld0 ++ l_tape u ∧
      l_tape v = ld0 ^ a ++ ld1 ++ l_tape u := by
  induction h with
  | nil => omega
  | one n k w h ih =>
    refine ⟨true :: false :: w, (0 : Nat), w, ?_, ?_, ?_⟩
    · exact Normal_eq (Normal.zero n k w h) rfl (by omega) rfl
    · simp [l_tape, digit, ld0, Half]
    · simp [l_tape, digit, ld1, Half]
  | zero n k w h ih =>
    rcases ih (by omega) with ⟨v, a, u, hv, hw_eq, hv_eq⟩
    refine ⟨true :: true :: v, a + 1, u, ?_, ?_, ?_⟩
    · exact Normal_eq (Normal.one n (k - 1) v hv) rfl (by omega) rfl
    · simp [l_tape, digit, ld1, Half, pow_succ_list, hw_eq, List.append_assoc]
    · simp [l_tape, digit, ld0, Half, pow_succ_list, hv_eq, List.append_assoc]

lemma normal_AA {n k : Nat} {w : List Bool} (m : Nat) (h : Normal n k w) :
    Normal (n + m) ((k + 1) * 2 ^ m - 1) (List.replicate (2 * m) true ++ w) := by
  have hp := pow2_pos n
  have hpm := pow2_pos m
  have hN := Num_AA m (normal_num h)
  have h1 : (2 ^ n - 1 + 1) * 2 ^ m - 1 = 2 ^ (n + m) - 1 := by
    rw [Nat.sub_add_cancel hp, Nat.pow_add]
  exact num_normal (n + m) (Num_eq hN (by omega) h1 rfl rfl)

lemma Num_flip {n e o : Nat} {w : List Bool} (h : Num n e o (true :: w)) :
    Num n (e - 1) o (false :: w) :=
  (flip_A h).1

lemma normal_FC_Rpairs (tail : ListBlank (Fin 2)) (h q : Nat) {n b : Nat} {w : List Bool}
    {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Normal n (q + b) w) (hr : FC tail h z r) (hb : z + q < 2 ^ h) :
    ∃ w' r', Normal n b w' ∧ FC tail h (z + q) r' ∧ ∀ l,
      ((l <+ l_tape w) {{B}}> r) [target_tm]⊢*
      ((l <+ l_tape w') {{B}}> r') := by
  induction q generalizing b w z r with
  | zero =>
    exact ⟨w, r, Normal_eq hn rfl (by omega) rfl, FC_eq hr rfl (by omega) rfl,
      fun l => stepStar_refl _⟩
  | succ q ih =>
    rcases FiniteRInc_ex hr (by omega) with ⟨r1, hr1, hR⟩
    have hn' : Normal n (1 + (q + b)) w := Normal_eq hn rfl (by omega) rfl
    rcases normal_LInc hn' with ⟨w1, h1, hL⟩
    rcases ih h1 hr1 (by omega) with ⟨w2, r2, h2, hr2, hS⟩
    refine ⟨w2, r2, h2, FC_eq hr2 rfl (by omega) rfl, fun l => ?_⟩
    exact stepStar_trans (stepPlus_to_stepStar (hR (l <+ l_tape w)))
      (stepStar_trans (stepPlus_to_stepStar (hL l r1)) (hS l))

lemma I_pre {n b : Nat} {w : List Bool} (t : Nat) (l r : ListBlank (Fin 2))
    (hn : Normal n (2 ^ (1 + t) - 2 + b) w) (_hb : 1 ≤ b) :
    ∃ w', Normal n b w' ∧
      ((l <+ l_tape w) {{B}}> ([1] +> (rd0 ^ t +> (rd1 +> r)))) [target_tm]⊢*
      ((l <+ l_tape w') {{B}}> (rd1 ^ t +> ([1, 1, 0, 0] +> r))) := by
  cases t with
  | zero =>
    refine ⟨w, Normal_eq hn rfl (by simp) rfl, ?_⟩
    exact stepStar_refl _
  | succ t =>
    have hp := pow2_pos t
    have hp1 : 2 ≤ 2 ^ (t + 1) := by rw [Nat.pow_succ]; omega
    have hn' : Normal n ((2 ^ (t + 1) - 2) + (2 ^ (t + 1) + b)) w :=
      Normal_eq hn rfl (by rw [show 1 + (t + 1) = (t + 1) + 1 by omega, Nat.pow_succ]; omega) rfl
    rcases normal_FC_Rpairs ([0, 1, 0, 0] +> r) (t + 1) (2 ^ (t + 1) - 2) hn' (FC_insert_one r t) (by omega)
      with ⟨w1, r1, h1, hr1, hS1⟩
    have hr1_eq : r1 = rd1 ^ (t + 1) +> ([0, 1, 0, 0] +> r) :=
      FC_full_unique (FC_eq hr1 rfl (by omega) rfl)
    subst hr1_eq
    have h1' : Normal n (1 + ((2 ^ (t + 1) - 1) + b)) w1 :=
      Normal_eq h1 rfl (by omega) rfl
    rcases normal_LInc h1' with ⟨w2, h2, hL⟩
    rcases normal_FC_Rpairs ([1, 1, 0, 0] +> r) (t + 1) (2 ^ (t + 1) - 1) h2
      (FC_zero ([1, 1, 0, 0] +> r) (t + 1)) (by omega)
      with ⟨w3, r3, h3, hr3, hS3⟩
    have hr3_eq : r3 = rd1 ^ (t + 1) +> ([1, 1, 0, 0] +> r) :=
      FC_full_unique (FC_eq hr3 rfl (by omega) rfl)
    subst hr3_eq
    refine ⟨w3, h3, ?_⟩
    have s1 := hS1 l
    have s2 := RInc_rule (l <+ l_tape w1) ([1, 0, 0] +> r) (t + 1)
    have heq2 : ([0] : List (Fin 2)) +> ([1, 0, 0] +> r) = [0, 1, 0, 0] +> r := rfl
    have heq2' : ([1] : List (Fin 2)) +> ([1, 0, 0] +> r) = [1, 1, 0, 0] +> r := rfl
    rw [heq2, heq2'] at s2
    have s3 := hL l (rd0 ^ (t + 1) +> ([1, 1, 0, 0] +> r))
    have s4 := hS3 l
    exact stepStar_trans s1
      (stepStar_trans (stepPlus_to_stepStar s2)
        (stepStar_trans (stepPlus_to_stepStar s3) s4))

lemma I_odd_exit {n b : Nat} {w : List Bool} (m : Nat) (l r : ListBlank (Fin 2))
    (hn : Normal n b w) (hb : 0 < b) :
    ∃ w', Normal (n + m + 1) (b * 2 ^ (m + 1) - 1) w' ∧
      ((l <+ l_tape w) {{B}}> (rd1 ^ (m * 2 + 1) +> ([1, 1, 0, 0] +> r))) [target_tm]⊢⁺
      ((l <+ l_tape w') {{B}}> ([1] +> r)) := by
  rcases normal_split hn hb with ⟨v, a, u, hv, hw_eq, hv_eq⟩
  refine ⟨List.replicate (2 * (m + 1)) true ++ v, ?_, ?_⟩
  · exact Normal_eq (normal_AA (m + 1) hv) (by omega) (by rw [Nat.sub_add_cancel hb]) rfl
  · have ht1 : l <+ l_tape w = l <+ l_tape u <+ ld0 <+ ld1 ^ a := by
      rw [hw_eq]; simp [listblank_append_assoc]
    have ht2 : l <+ l_tape (List.replicate (2 * (m + 1)) true ++ v) =
        l <+ l_tape u <+ ld1 <+ ld0 ^ (m + a + 1) := by
      rw [l_tape_append, normal_full_tape (normal_full (m + 1)) rfl, hv_eq,
          show m + a + 1 = (m + 1) + a by omega, list_pow_add]
      simp [listblank_append_assoc]
    rw [ht1, ht2]
    exact ROvOddRecover (l <+ l_tape u) r a m

lemma I_odd {n b : Nat} {w : List Bool} (m : Nat) (l r : ListBlank (Fin 2))
    (hn : Normal n (2 ^ (1 + (m * 2 + 1)) - 2 + b) w) (hb : 1 ≤ b) :
    ∃ w', Normal (n + m + 1) (b * 2 ^ (m + 1) - 1) w' ∧
      ((l <+ l_tape w) {{B}}> ([1] +> (rd0 ^ (m * 2 + 1) +> (rd1 +> r)))) [target_tm]⊢⁺
      ((l <+ l_tape w') {{B}}> ([1] +> r)) := by
  rcases I_pre (m * 2 + 1) l r hn hb with ⟨v, hv, hP⟩
  rcases I_odd_exit m l r hv (by omega) with ⟨u, hu, hU⟩
  exact ⟨u, hu, stepStar_stepPlus_trans hP hU⟩

lemma I_even_exit {n b : Nat} {w : List Bool} (m : Nat) (l r : ListBlank (Fin 2))
    (hn : Normal n b w) (hb : 0 < b) :
    ∃ w', Num (2 * (n + m)) ((2 ^ n - 1) * 2 ^ m - 1) ((b + 1) * 2 ^ m - 1) w' ∧
      ((l <+ l_tape w) {{B}}> (rd1 ^ (m * 2) +> ([1, 1, 0, 0] +> r))) [target_tm]⊢⁺
      ((l <+ l_tape w' <+ s_tag) {{D}}> r) := by
  have hbound := normal_bound hn
  have hpos : 0 < n := by
    cases n with
    | zero => simp at hbound; omega
    | succ n => omega
  have hpow : 2 ≤ 2 ^ n := by
    cases n with
    | zero => omega
    | succ n =>
      have := pow2_pos n
      rw [Nat.pow_succ]; omega
  rcases normal_head hn hpos with ⟨v, rfl⟩
  refine ⟨List.replicate (2 * m) true ++ false :: v, ?_, ?_⟩
  · have hAA := Num_AA m (Num_flip (normal_num hn))
    have h1 : (2 ^ n - 1 - 1 + 1) * 2 ^ m - 1 = (2 ^ n - 1) * 2 ^ m - 1 := by
      rw [show 2 ^ n - 1 - 1 + 1 = 2 ^ n - 1 by omega]
    exact Num_eq hAA (by omega) h1 rfl rfl
  · have ht1 : l <+ l_tape (true :: v) = l <+ l_tape v <+ [1, 1] <+ [0] := by
      simp [l_tape, digit, Half]
    have ht2 : l <+ l_tape (List.replicate (2 * m) true ++ false :: v) =
        l <+ l_tape v <+ [1, 1] <+ [1] <+ ld0 ^ m := by
      rw [l_tape_append, normal_full_tape (normal_full m) rfl]
      simp [l_tape, digit, Half, listblank_append_assoc]
    rw [ht1, ht2]
    exact ROvEvenAux (l <+ l_tape v <+ [1, 1]) r m

lemma I_even {n b : Nat} {w : List Bool} (m : Nat) (l r : ListBlank (Fin 2))
    (hn : Normal n (2 ^ (1 + m * 2) - 2 + b) w) (hb : 1 ≤ b) :
    ∃ w', Num (2 * (n + m)) ((2 ^ n - 1) * 2 ^ m - 1) ((b + 1) * 2 ^ m - 1) w' ∧
      ((l <+ l_tape w) {{B}}> ([1] +> (rd0 ^ (m * 2) +> (rd1 +> r)))) [target_tm]⊢⁺
      ((l <+ l_tape w' <+ s_tag) {{D}}> r) := by
  rcases I_pre (m * 2) l r hn hb with ⟨v, hv, hP⟩
  rcases I_even_exit m l r hv (by omega) with ⟨u, hu, hU⟩
  exact ⟨u, hu, stepStar_stepPlus_trans hP hU⟩

lemma geometric_step (h k o : Nat) :
    2 ^ (h + 2) * (2 ^ (k + 1) - 1) + o =
    2 ^ (h + 2) + (2 ^ (h + 1 + 2) * (2 ^ k - 1) + o) := by
  have hp := pow2_pos k
  have h1 : 2 ^ (h + 1 + 2) = 2 ^ (h + 2) * 2 := by
    rw [show h + 1 + 2 = (h + 2) + 1 by omega, Nat.pow_succ]
  have h2 : 2 ^ (k + 1) - 1 = 1 + 2 * (2 ^ k - 1) := by
    rw [Nat.pow_succ]; omega
  rw [h1, h2]
  ring

lemma TZeros (k : Nat) {n e o : Nat} {w : List Bool} (h : Nat) (l r : ListBlank (Fin 2))
    (hn : Num n e (2 ^ (h + 2) * (2 ^ k - 1) + o) (true :: w)) :
    ∃ e' w', Num n e' o (true :: w') ∧ e ≤ e' ∧
      ((l <+ l_tape (true :: w) <+ (Half 1) ^ h <+ t_tag) {{D}}> (rd0 ^ k +> r)) [target_tm]⊢*
      ((l <+ l_tape (true :: w') <+ (Half 1) ^ (h + k) <+ t_tag) {{D}}> r) := by
  induction k generalizing e w h r with
  | zero =>
    have hn' : Num n e o (true :: w) := Num_eq hn rfl rfl (by simp) rfl
    exact ⟨e, w, hn', Nat.le_refl e, stepStar_refl _⟩
  | succ k ih =>
    rw [geometric_step h k o] at hn
    rcases TZero h l (rd0 ^ k +> r) hn with ⟨e1, w1, h1, hle1, hS1⟩
    rcases ih (h + 1) r h1 with ⟨e2, w2, h2, hle2, hS2⟩
    refine ⟨e2, w2, h2, by omega, ?_⟩
    rw [right_pow_succ rd0 k r, show h + (k + 1) = h + 1 + k by omega]
    exact stepStar_trans (stepPlus_to_stepStar hS1) hS2

lemma RPairs (l r : ListBlank (Fin 2)) (k : Nat) :
    (l {{B}}> (ones ^ (k * 6) +> r)) [target_tm]⊢*
    ((l <+ ld0 ^ k) {{B}}> r) := by
  rw [show k * 6 = (k * 2) * 3 by omega, ← half0_pairs k]
  exact R111Scan l r (k * 2)

lemma T100_zero_odd {m e : Nat} {w : List Bool} (r : ListBlank (Fin 2))
    (hn : Num (2 * m + 1) e 0 w) :
    ((ldh <+ l_tape w <+ t_tag) {{D}}> (rd1 +> r)) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (m + 2)) {{B}}> r) := by
  rcases zero_odd m hn with ⟨bs, b, rfl, ht⟩
  have heq : ldh <+ l_tape w = ldh <+ Half b <+ Marked bs := by
    rw [ht, listblank_append_assoc]
  rw [heq]
  have s1 := T100 (ldh <+ Half b <+ Marked bs) r
  have s2 := MarkedCarry (ldh <+ Half b) (ones ^ 6 +> r) bs
  have s3 := EHalfBoundary (ones ^ (bs.length * 6) +> (ones ^ 6 +> r)) b
  have h_ones : ones ^ 6 +> (ones ^ (bs.length * 6) +> (ones ^ 6 +> r)) =
      ones ^ ((bs.length + 2) * 6) +> r := by
    rw [← right_pow_add, ← right_pow_add, show 6 + bs.length * 6 + 6 = (bs.length + 2) * 6 by omega]
  rw [h_ones] at s3
  have s4 := RPairs ldh r (bs.length + 2)
  exact stepPlus_trans s1
    (stepStar_stepPlus_trans s2
      (stepPlus_stepStar_trans s3 s4))

def IC (w : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((ldh <+ l_tape w) {{B}}> ([1] +> r))

def IGuard (n k z : Nat) : Prop :=
  z = 0 ∨ (∃ d, z < 2 ^ d ∧ d ≤ n ∧ 2 ^ d - 1 ≤ k) ∨ (k = 2 ^ n - 1 ∧ z ≤ 2 ^ n + 1)

inductive IAllowed : Cfg (Fin 2) (Fin 6) → Prop
  | intro (n k : Nat) (w : List Bool) (z : Nat) (r : ListBlank (Fin 2)) :
      Normal n k w → 1 ≤ n → RC z r → IGuard n k z →
      IAllowed (IC w r)

inductive Allowed : Cfg (Fin 2) (Fin 6) → Prop
  | Ordinary (c : Cfg (Fin 2) (Fin 6)) : IAllowed c → Allowed c
  | Ten (z : Nat) (c : Cfg (Fin 2) (Fin 6)) : TenAllowed z c → Allowed c
  | Signal (z : Nat) (c : Cfg (Fin 2) (Fin 6)) : STAllowed z c → Allowed c

lemma I_full (n z : Nat) (r : ListBlank (Fin 2))
    (hn : 1 ≤ n) (hz : z ≤ 2 ^ n + 1) (hr : RC z r) :
    IAllowed ((ldh <+ ld0 ^ n) {{B}}> ([1] +> r)) := by
  rw [← normal_full_tape (normal_full n) rfl]
  exact IAllowed.intro n (2 ^ n - 1) (List.replicate (2 * n) true) z r
    (normal_full n) hn hr (Or.inr (Or.inr ⟨rfl, hz⟩))

lemma J_full (n z : Nat) (r : ListBlank (Fin 2))
    (hn : 2 ≤ n) (hr : RC z r) (hg : z = 0 ∨ 2 * z + 1 ≤ 2 ^ n - 1) :
    TenAllowed z ((ldh <+ ld0 ^ n) <{{C}} ([1, 0] +> r)) := by
  rcases normal_head (normal_full n) (by omega) with ⟨w, hw⟩
  have hN := normal_num (normal_full n)
  have ht := normal_full_tape (normal_full n) rfl
  rw [hw] at hN ht
  rw [← ht]
  exact TenAllowed.J (2 * n) (2 ^ n - 1) (2 ^ n - 1) w z r hN (by omega) hr
    (hg.elim Or.inl (fun h => Or.inr ⟨h, h⟩))

lemma J_odd_bound (m e o : Nat) (w : List Bool) (h : Num (2 * (1 + m) + 1) e o w) :
    2 * ((1 + o) / 2) + 1 ≤ 2 ^ (2 + m) - 1 := by
  rcases Num_bounds h with ⟨_, ho⟩
  have hdiv : (2 * (1 + m) + 1) / 2 = 1 + m := by omega
  rw [hdiv] at ho
  have hp : 2 ^ (2 + m) = 2 * 2 ^ (1 + m) := by
    rw [show 2 + m = (1 + m) + 1 by omega, Nat.pow_succ]
    omega
  rw [hp]
  omega

lemma S_zero {c : Cfg (Fin 2) (Fin 6)} (h : STAllowed 0 c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  rcases ST_zero_shape h with ⟨n, e, o, w, hN, hl, rfl⟩
  rcases nat_even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases Drain_S_even hN with ⟨r', hr', hS⟩
    refine ⟨((ldh <+ ld0 ^ (1 + m)) <{{C}} ([1, 0] +> r')), ?_, hS⟩
    refine Allowed.Ten ((2 + e) / 2) _ (J_full (1 + m) ((2 + e) / 2) r' (by omega) hr' (Or.inr ?_))
    have hN' : Num (2 * (1 + (m - 1))) e o w := Num_eq hN (by omega) rfl rfl rfl
    have hb := S_even_bound (m - 1) e o w hN'
    rw [show 2 + (m - 1) = 1 + m by omega] at hb
    exact hb
  · rcases Drain_S_odd hN with ⟨r', hr', hS⟩
    refine ⟨((ldh <+ ld0 ^ (1 + m)) {{B}}> ([1] +> r')), ?_, hS⟩
    exact Allowed.Ordinary _ (I_full (1 + m) (2 + e) r' (by omega) (S_odd_bound m e o w hN) hr')

lemma J_zero {c : Cfg (Fin 2) (Fin 6)} (h : TenAllowed 0 c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  rcases Ten_zero_shape h with ⟨n, e, o, w, hN, hl, rfl⟩
  have hr1 : RC 1 ([1, 0] +> default) := by
    have h0 : RC 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
    have heq : rd1 +> (default : ListBlank (Fin 2)) = [1, 0] +> default := by simp [rd1]
    rwa [heq] at h0
  rcases nat_even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases Drain_even hN hr1 with ⟨r', hr', hS⟩
    refine ⟨((ldh <+ ld0 ^ m) {{B}}> ([1] +> r')), ?_, hS⟩
    rcases Num_bounds hN with ⟨_, ho⟩
    have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv] at ho
    exact Allowed.Ordinary _ (I_full m (1 + o) r' (by omega) (by omega) hr')
  · rcases Drain_odd hN hr1 with ⟨r', hr', hS⟩
    refine ⟨((ldh <+ ld0 ^ (1 + m)) <{{C}} ([1, 0] +> r')), ?_, hS⟩
    refine Allowed.Ten ((1 + o) / 2) _ (J_full (1 + m) ((1 + o) / 2) r' (by omega) hr' (Or.inr ?_))
    have hN' : Num (2 * (1 + (m - 1)) + 1) e o (true :: w) := Num_eq hN (by omega) rfl rfl rfl
    have hb := J_odd_bound (m - 1) e o (true :: w) hN'
    rw [show 2 + (m - 1) = 1 + m by omega] at hb
    exact hb

lemma even_R_return {n e o : Nat} {w : List Bool} {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Num (2 * n) e o (true :: w)) (hlen : 1 ≤ n) (hr : RC z r) (hz : z ≤ 1) :
    ∃ c', Allowed c' ∧ ((ldh <+ l_tape (true :: w)) {{B}}> r) [target_tm]⊢⁺ c' := by
  rcases Num_bounds hn with ⟨_, hb⟩
  have hdiv : 2 * n / 2 = n := by omega
  rw [hdiv] at hb
  rcases RInc_ex hr with ⟨s, hs, hR⟩
  rcases Drain_even hn hs with ⟨s', hs', hL⟩
  refine ⟨((ldh <+ ld0 ^ n) {{B}}> ([1] +> s')), ?_, stepPlus_trans (hR (ldh <+ l_tape (true :: w))) hL⟩
  exact Allowed.Ordinary _ (I_full n (z + 1 + o) s' hlen (by omega) hs')

lemma R_return {n k : Nat} {w : List Bool} {z : Nat} {r : ListBlank (Fin 2)}
    (hn : Normal n k w) (hlen : 1 ≤ n) (hr : RC z r) (hz : z ≤ 1) :
    ∃ c', Allowed c' ∧ ((ldh <+ l_tape w) {{B}}> r) [target_tm]⊢⁺ c' := by
  rcases normal_head hn (by omega) with ⟨v, rfl⟩
  exact even_R_return (normal_num hn) hlen hr hz

lemma R_zero_full (n : Nat) (hn : 1 ≤ n) :
    ∃ c', Allowed c' ∧ ((ldh <+ ld0 ^ n) {{B}}> default) [target_tm]⊢⁺ c' := by
  rcases R_return (normal_full n) hn RC.zero (by omega) with ⟨c', hA, hS⟩
  rw [normal_full_tape (normal_full n) rfl] at hS
  exact ⟨c', hA, hS⟩

lemma I_zero {n k : Nat} {w : List Bool} {r : ListBlank (Fin 2)}
    (hn : Normal n k w) (hl : 1 ≤ n) (hr : RC 0 r) :
    ∃ c', Allowed c' ∧ (IC w r) [target_tm]⊢⁺ c' := by
  rw [RC_zero_unique hr]
  have hr1 : RC 1 ([1] +> default) := by
    have h0 : RC 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
    have heq : rd1 +> (default : ListBlank (Fin 2)) = [1] +> default := by simp [rd1]
    rwa [heq] at h0
  exact R_return hn hl hr1 (by omega)

lemma small_bounds (n k d t q : Nat)
    (hz : 2 ^ t * (1 + q * 2) < 2 ^ d) (hd : d ≤ n) (hk : 2 ^ d - 1 ≤ k) :
    ∃ b s, k = 2 ^ (1 + t) - 2 + b ∧ 1 ≤ b ∧ q < 2 ^ s ∧ s ≤ n ∧ 2 ^ s ≤ b ∧ 2 * q + 2 ≤ 2 ^ n := by
  have hpt := pow2_pos t
  have htd : t < d := by
    rcases Nat.lt_or_ge t d with hlt | hge
    · exact hlt
    · have hle : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) hge
      have : 2 ^ t * 1 ≤ 2 ^ t * (1 + q * 2) := Nat.mul_le_mul_left _ (by omega)
      omega
  set s := d - (1 + t)
  have hds : d = (1 + t) + s := by omega
  have hP : 2 ^ d = 2 ^ (1 + t) * 2 ^ s := by rw [hds, Nat.pow_add]
  have hP2 : 2 ^ (1 + t) = 2 ^ t * 2 := by rw [Nat.add_comm 1 t, Nat.pow_succ]
  have hps := pow2_pos s
  have hdn : 2 ^ d ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hd
  have hqs : q < 2 ^ s := by
    rcases Nat.lt_or_ge q (2 ^ s) with hlt | hge
    · exact hlt
    · have hmul : 2 ^ t * (2 * 2 ^ s) ≤ 2 ^ t * (1 + q * 2) :=
        Nat.mul_le_mul_left _ (by omega)
      have : 2 ^ d = 2 ^ t * (2 * 2 ^ s) := by rw [hP, hP2]; ring
      omega
  have hcost : 2 ^ (1 + t) - 2 ≤ k := by
    have : 2 ^ (1 + t) * 1 ≤ 2 ^ (1 + t) * 2 ^ s := Nat.mul_le_mul_left _ hps
    omega
  set b := k - (2 ^ (1 + t) - 2)
  have hbnd : 2 ^ s ≤ b := by
    have h3 : 2 ^ (1 + t) * (2 ^ s - 1) ≥ 2 * (2 ^ s - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : 2 ^ (1 + t) * 2 ^ s = 2 ^ (1 + t) + 2 ^ (1 + t) * (2 ^ s - 1) := by
      have hs1 : 2 ^ s = 1 + (2 ^ s - 1) := by omega
      conv_lhs => rw [hs1]
      ring
    omega
  have h2q : 2 * q + 2 ≤ 2 ^ n := by
    have : 2 * q + 1 ≤ 2 ^ t * (1 + q * 2) := by
      have : 1 * (1 + q * 2) ≤ 2 ^ t * (1 + q * 2) := Nat.mul_le_mul_right _ hpt
      omega
    omega
  exact ⟨b, s, by omega, by omega, hqs, by omega, hbnd, h2q⟩

lemma IClosure_small {n k : Nat} {w : List Bool} {z : Nat} {r : ListBlank (Fin 2)} (d : Nat)
    (hn : Normal n k w) (hlen : 1 ≤ n) (hr : RC z r)
    (hz : 0 < z) (hcap : z < 2 ^ d) (hd : d ≤ n) (hbudget : 2 ^ d - 1 ≤ k) :
    ∃ c', Allowed c' ∧ (IC w r) [target_tm]⊢⁺ c' := by
  rcases RC_positive_split hr hz with ⟨t, q, s, rfl, hs, hez, hqz⟩
  have hcap' : 2 ^ t * (1 + q * 2) < 2 ^ d := by rw [← hez]; exact hcap
  rcases small_bounds n k d t q hcap' hd hbudget with ⟨b, d', hk, hb, hq, hwidth, hbb, h2q⟩
  rcases nat_even_or_odd t with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [Nat.mul_comm 2 m] at hk ⊢
    have hn' : Normal n (2 ^ (1 + m * 2) - 2 + b) w := Normal_eq hn rfl hk rfl
    rcases I_even m ldh s hn' hb with ⟨w', hN, hS⟩
    refine ⟨SC w' s, ?_, hS⟩
    have hpm := pow2_pos m
    have he' : 2 * q ≤ (2 ^ n - 1) * 2 ^ m - 1 := by
      have : (2 ^ n - 1) * 1 ≤ (2 ^ n - 1) * 2 ^ m := Nat.mul_le_mul_left _ hpm
      omega
    have ho' : q ≤ (b + 1) * 2 ^ m - 1 := by
      have : (b + 1) * 1 ≤ (b + 1) * 2 ^ m := Nat.mul_le_mul_left _ hpm
      omega
    exact Allowed.Signal q _ (STAllowed.S (2 * (n + m)) _ _ w' q s hN (by omega) he' ho' hs)
  · rw [show 2 * m + 1 = m * 2 + 1 by omega] at hk ⊢
    have hn' : Normal n (2 ^ (1 + (m * 2 + 1)) - 2 + b) w := Normal_eq hn rfl hk rfl
    rcases I_odd m ldh s hn' hb with ⟨w', hN, hS⟩
    refine ⟨IC w' s, ?_, hS⟩
    have hpm1 := pow2_pos (m + 1)
    have hbud' : 2 ^ d' - 1 ≤ b * 2 ^ (m + 1) - 1 := by
      have : b * 1 ≤ b * 2 ^ (m + 1) := Nat.mul_le_mul_left _ hpm1
      omega
    exact Allowed.Ordinary _ (IAllowed.intro (n + m + 1) _ w' q s hN (by omega) hs
      (Or.inr (Or.inl ⟨d', hq, by omega, hbud'⟩)))

lemma Num_BB {n e o : Nat} {w : List Bool} (m : Nat) (h : Num n e o w) :
    Num (n + 2 * m) (e * 2 ^ m) (o * 2 ^ m) (List.replicate (2 * m) false ++ w) := by
  induction m with
  | zero => exact Num_eq h (by omega) (by omega) (by omega) rfl
  | succ m ih =>
    have hrep : List.replicate (2 * (m + 1)) false ++ w =
        false :: false :: (List.replicate (2 * m) false ++ w) := by
      rw [show 2 * (m + 1) = 2 + 2 * m by omega, List.replicate_add]
      rfl
    rw [hrep]
    exact Num_eq (Num.B _ _ _ _ (Num.B _ _ _ _ ih))
      (by omega) (by rw [Nat.pow_succ]; ring) (by rw [Nat.pow_succ]; ring) rfl

lemma Num_Bodd {n e o : Nat} {w : List Bool} (m : Nat) (h : Num n e o w) :
    Num (n + 2 * m + 1) (o * 2 ^ (m + 1)) (e * 2 ^ m) (List.replicate (2 * m + 1) false ++ w) := by
  have hBB := Num_BB m h
  have hrep : List.replicate (2 * m + 1) false ++ w =
      false :: (List.replicate (2 * m) false ++ w) := by
    rw [show 2 * m + 1 = 1 + 2 * m by omega, List.replicate_add]
    rfl
  rw [hrep]
  exact Num_eq (Num.B _ _ _ _ hBB) (by omega) (by rw [Nat.pow_succ]; ring) rfl rfl

lemma Num_A_positive {n e o : Nat} {w : List Bool} (h : Num n e o (true :: w)) : 0 < e := by
  rcases Num_inv_true h with ⟨_, _, _, rfl, _⟩; omega

lemma plus_one_tape (k : Nat) {r : ListBlank (Fin 2)} (h : RC (2 ^ (k + 1) + 1) r) :
    r = rd1 +> (rd0 ^ k +> (rd1 +> default)) := by
  have h0 : RC (2 ^ (k + 1) + 1) (rd1 +> (rd0 ^ k +> (rd1 +> default))) := by
    have h1 := RC.d1 (2 ^ k * 1) (rd0 ^ k +> (rd1 +> default))
      (RC_zeros k (RC_eq (RC.d1 0 default RC.zero) (by omega) rfl))
    exact RC_eq h1 (by rw [Nat.pow_succ]; omega) rfl
  exact RC_unique h h0

lemma Special_entry (n : Nat) (r : ListBlank (Fin 2)) (hn : 1 ≤ n) :
    ∃ w, Num (2 * n) (2 ^ n - 2) (2 ^ n - 1) w ∧
      ((ldh <+ ld0 ^ n) {{B}}> ([1] +> (rd1 +> r))) [target_tm]⊢⁺ SC w r := by
  have hpow : 2 ≤ 2 ^ n := by
    cases n with
    | zero => omega
    | succ n => have := pow2_pos n; rw [Nat.pow_succ]; omega
  rcases I_even_exit 0 ldh r (normal_full n) (by omega) with ⟨w, hN, hS⟩
  rw [normal_full_tape (normal_full n) rfl] at hS
  have hN' : Num (2 * n) (2 ^ n - 2) (2 ^ n - 1) w :=
    Num_eq hN (by omega) (by simp; omega) (by simp) rfl
  have heq : rd1 ^ (0 * 2) +> ([1, 1, 0, 0] +> r) = [1] +> (rd1 +> r) := rfl
  rw [heq] at hS
  exact ⟨w, hN', hS⟩

lemma Special_one {r : ListBlank (Fin 2)} (hr : RC (2 ^ 1 + 1) r) :
    ∃ c', Allowed c' ∧ ((ldh <+ ld0 ^ 1) {{B}}> ([1] +> r)) [target_tm]⊢⁺ c' := by
  rw [plus_one_tape 0 hr]
  rcases Special_entry 1 (rd1 +> default) (by omega) with ⟨w, hN, hS⟩
  rcases ST_S100 hN with ⟨hN', hS'⟩
  refine ⟨SC (false :: w) default, ?_, stepPlus_trans hS (hS' ldh default)⟩
  exact Allowed.Signal 0 _ (STAllowed.S (2 * 1 + 1) _ _ (false :: w) 0 default
    hN' (by omega) (by omega) (by omega) RC.zero)

lemma Special_to_T_one (k : Nat) {r : ListBlank (Fin 2)} (hr : RC (2 ^ (k + 2) + 1) r) :
    ∃ e w, Num (2 * (k + 2) + 1) e 0 (true :: w) ∧
      ((ldh <+ ld0 ^ (k + 2)) {{B}}> ([1] +> r)) [target_tm]⊢⁺
      TC w k (rd1 +> default) := by
  have hr' : RC (2 ^ ((k + 1) + 1) + 1) r := hr
  rw [plus_one_tape (k + 1) hr', right_pow_succ rd0 k (rd1 +> default)]
  rcases Special_entry (k + 2) (rd0 +> (rd0 ^ k +> (rd1 +> default))) (by omega) with ⟨v, hN, hS⟩
  have hp := pow2_pos k
  have hP : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_add]; ring
  have hN' : Num (2 * (k + 2)) (2 + (2 ^ (k + 2) - 4)) (2 ^ (k + 2) - 1) v :=
    Num_eq hN rfl (by omega) rfl rfl
  rcases ST_S000 hN' with ⟨e1, w1, h1, hle1, hS1⟩
  have h1' : Num (2 * (k + 2) + 1) e1 (2 ^ (0 + 2) * (2 ^ k - 1) + 0) (true :: w1) :=
    Num_eq h1 rfl rfl (by omega) rfl
  rcases TZeros k 0 ldh (rd1 +> default) h1' with ⟨e2, w2, h2, hle2, hS2⟩
  refine ⟨e2, w2, h2, ?_⟩
  rw [Nat.zero_add k] at hS2
  exact stepPlus_trans hS (stepPlus_stepStar_trans (hS1 ldh (rd0 ^ k +> (rd1 +> default))) hS2)

lemma Special_odd (k : Nat) {r : ListBlank (Fin 2)} (hr : RC (2 ^ (2 * k + 3) + 1) r) :
    ∃ c', Allowed c' ∧ ((ldh <+ ld0 ^ (2 * k + 3)) {{B}}> ([1] +> r)) [target_tm]⊢⁺ c' := by
  have hr' : RC (2 ^ ((2 * k + 1) + 2) + 1) r := hr
  rcases Special_to_T_one (2 * k + 1) hr' with ⟨e, w, hN, hS⟩
  have hpos := Num_A_positive hN
  have hp := pow2_pos k
  have hB := Num_Bodd k hN
  have hB' : Num (2 * (2 * k + 1 + 2) + 1 + 2 * k + 1) (0 * 2 ^ (k + 1)) (1 + (e * 2 ^ k - 1))
      (List.replicate (2 * k + 1) false ++ true :: w) :=
    Num_eq hB rfl rfl (by have : 1 ≤ e * 2 ^ k := Nat.mul_pos hpos hp; omega) rfl
  rcases ST_T100 hB' with ⟨e', w', hN', hle, hT⟩
  refine ⟨SC (true :: w') default, ?_, ?_⟩
  · exact Allowed.Signal 0 _ (STAllowed.S _ _ _ (true :: w') 0 default
      hN' (by omega) (by omega) (by omega) RC.zero)
  · rw [TC_word] at hS
    exact stepPlus_trans hS (hT ldh default)

lemma Special_even_R_zero (k : Nat) {r : ListBlank (Fin 2)} (hr : RC (2 ^ (2 * k + 2) + 1) r) :
    ((ldh <+ ld0 ^ (2 * k + 2)) {{B}}> ([1] +> r)) [target_tm]⊢⁺
    ((ldh <+ ld0 ^ (3 * k + 4)) {{B}}> default) := by
  rcases Special_to_T_one (2 * k) hr with ⟨e, w, hN, hS⟩
  have hB := Num_BB k hN
  have hB' : Num (2 * (3 * k + 2) + 1) (e * 2 ^ k) 0 (List.replicate (2 * k) false ++ true :: w) :=
    Num_eq hB (by omega) rfl (by omega) rfl
  have hT := T100_zero_odd default hB'
  rw [show 3 * k + 2 + 2 = 3 * k + 4 by omega] at hT
  rw [TC_word] at hS
  exact stepPlus_trans hS hT

lemma cap_plus_one (n : Nat) {r : ListBlank (Fin 2)} (hn : 1 ≤ n) (hr : RC (2 ^ n + 1) r) :
    ∃ c', Allowed c' ∧ ((ldh <+ ld0 ^ n) {{B}}> ([1] +> r)) [target_tm]⊢⁺ c' := by
  rcases n with _ | _ | k
  · omega
  · exact Special_one hr
  · rcases nat_even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rcases R_zero_full (3 * m + 4) (by omega) with ⟨c', hA, hS⟩
      exact ⟨c', hA, stepPlus_trans (Special_even_R_zero m hr) hS⟩
    · exact Special_odd m hr

def cut (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((default <+ cut_tag <+ ld1 ^ n) {{B}}> (rd1 ^ (n - 1) +> ([1, 1, 1, 0, 0] +> default)))

lemma Num_total (w : List Bool) : ∃ e o, Num w.length e o w := by
  induction w with
  | nil => exact ⟨0, 0, Num.nil⟩
  | cons b w ih =>
    rcases ih with ⟨e, o, h⟩
    cases b
    · exact ⟨o * 2, e, Num_eq (Num.B _ _ _ _ h) (by simp; omega) rfl rfl rfl⟩
    · exact ⟨1 + o * 2, e, Num_eq (Num.A _ _ _ _ h) (by simp; omega) rfl rfl rfl⟩

lemma odd_word (m : Nat) :
    ∃ w e o, Num (2 * (3 * m + 2)) e o (true :: w) ∧
      ldh <+ l_tape (true :: w) =
      default <+ cut_tag <+ ld1 ^ (m * 2) <+ [1, 1, 1] <+ ld1 <+ ld0 ^ m := by
  rcases normal_zero (m * 2) with ⟨z, hz⟩
  have hl := normal_length hz
  have ht := normal_zero_tape hz rfl
  set u := List.replicate (2 * m) true ++ true :: false :: false :: (z ++ [true])
  have hu : u.length = 2 * (3 * m + 2) := by
    simp [u, hl]; omega
  have hhead : ∃ w, u = true :: w := by
    cases m with
    | zero => exact ⟨false :: false :: (z ++ [true]), rfl⟩
    | succ m =>
      have : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [show u = (List.replicate (2 * (m + 1)) true) ++ true :: false :: false :: (z ++ [true]) by rfl,
          this, List.replicate_succ, List.cons_append]
      exact ⟨_, rfl⟩
  rcases hhead with ⟨w, hw⟩
  rcases Num_total u with ⟨e, o, hN⟩
  refine ⟨w, e, o, ?_, ?_⟩
  · rw [← hu]
    exact Num_eq hN rfl rfl rfl hw
  · rw [← hw]
    simp only [u, l_tape_append, l_tape_cons, l_tape_nil,
      normal_full_tape (normal_full m) rfl, ht]
    simp [ldh, cut_tag, digit, Half, ld1, listblank_append_assoc]

lemma FC_head_one (r : ListBlank (Fin 2)) (t : Nat) :
    FC ([0] +> r) (t + 1) 1 ([1] +> (rd0 ^ (t + 1) +> r)) := by
  have h0 := FC.d1 t 0 (rd0 ^ t +> ([0] +> r)) (FC_zero ([0] +> r) t)
  have heq : rd1 +> (rd0 ^ t +> ([0] +> r)) = [1] +> (rd0 ^ (t + 1) +> r) := by
    rw [right_pow_succ rd0 t r]
    change rd1 +> (rd0 ^ t +> (([0] : List (Fin 2)) +> r)) =
      rd1 +> (([0] : List (Fin 2)) +> (rd0 ^ t +> r))
    rw [one_zero_comm_rd0_pow t r]
  exact FC_eq h0 rfl (by omega) heq

lemma cut_even (m : Nat) : ∃ c', Allowed c' ∧ (cut (2 + m * 2)) [target_tm]⊢⁺ c' := by
  rcases R_zero_full (4 + m * 3) (by omega) with ⟨c', hA, hS⟩
  refine ⟨c', hA, ?_⟩
  have s1 := even_capacity_cleanup m default
  have heq0 : ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default := zero_cons_default
  rw [heq0] at s1
  have hcut : cut (2 + m * 2) =
      ((default <+ cut_tag <+ ld1 ^ (2 + m * 2)) {{B}}> (rd1 ^ (1 + m * 2) +> ([1, 1, 1, 0, 0] +> default))) := by
    simp [cut, show 2 + m * 2 - 1 = 1 + m * 2 by omega]
  rw [hcut]
  exact stepPlus_trans s1 hS

lemma cut_odd (m : Nat) : ∃ c', Allowed c' ∧ (cut (1 + m * 2)) [target_tm]⊢⁺ c' := by
  rcases odd_word m with ⟨w, e, o, hN, ht⟩
  have hr1 : RC 1 ([1, 0] +> default) := by
    have h0 : RC 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
    have heq : rd1 +> (default : ListBlank (Fin 2)) = [1, 0] +> default := by simp [rd1]
    rwa [heq] at h0
  rcases even_R_return hN (by omega) hr1 (by omega) with ⟨c', hA, hS⟩
  refine ⟨c', hA, ?_⟩
  have s1 := odd_capacity_entry (default <+ cut_tag <+ ld1 ^ (m * 2)) default m
  have hcut : cut (1 + m * 2) =
      ((default <+ cut_tag <+ ld1 ^ (m * 2) <+ ld1) {{B}}> (rd1 ^ (m * 2) +> ([1, 1, 1, 0, 0] +> default))) := by
    dsimp [cut]
    rw [show 1 + m * 2 - 1 = m * 2 by omega,
        show 1 + m * 2 = m * 2 + 1 by omega,
        left_pow_succ (default <+ cut_tag) ld1 (m * 2)]
  rw [hcut]
  rw [ht] at hS
  exact stepPlus_trans s1 hS

lemma cut_return (n : Nat) (hn : 1 ≤ n) : ∃ c', Allowed c' ∧ (cut n) [target_tm]⊢⁺ c' := by
  rcases nat_even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · cases m with
    | zero => omega
    | succ m =>
      rw [show 2 * (m + 1) = 2 + m * 2 by omega]
      exact cut_even m
  · rw [show 2 * m + 1 = 1 + m * 2 by omega]
    exact cut_odd m

lemma two_batches {n b : Nat} {w : List Bool} (t : Nat) (l r : ListBlank (Fin 2))
    (hn : Normal n (2 ^ (1 + (t + 1)) - 2 + b) w) :
    ∃ w', Normal n b w' ∧
      ((l <+ l_tape w) {{B}}> ([1] +> (rd0 ^ (t + 1) +> ([1] +> r)))) [target_tm]⊢*
      ((l <+ l_tape w') {{B}}> (rd1 ^ (t + 1) +> ([1, 1] +> r))) := by
  have hp := pow2_pos t
  have hp1 : 2 ≤ 2 ^ (t + 1) := by rw [Nat.pow_succ]; omega
  have hn' : Normal n ((2 ^ (t + 1) - 2) + (2 ^ (t + 1) + b)) w :=
    Normal_eq hn rfl (by rw [show 1 + (t + 1) = (t + 1) + 1 by omega, Nat.pow_succ]; omega) rfl
  rcases normal_FC_Rpairs ([0, 1] +> r) (t + 1) (2 ^ (t + 1) - 2) hn' (FC_head_one ([1] +> r) t) (by omega)
    with ⟨w1, r1, h1, hr1, hS1⟩
  have hr1_eq : r1 = rd1 ^ (t + 1) +> ([0, 1] +> r) :=
    FC_full_unique (FC_eq hr1 rfl (by omega) rfl)
  subst hr1_eq
  have h1' : Normal n (1 + ((2 ^ (t + 1) - 1) + b)) w1 :=
    Normal_eq h1 rfl (by omega) rfl
  rcases normal_LInc h1' with ⟨w2, h2, hL⟩
  rcases normal_FC_Rpairs ([1, 1] +> r) (t + 1) (2 ^ (t + 1) - 1) h2
    (FC_zero ([1, 1] +> r) (t + 1)) (by omega)
    with ⟨w3, r3, h3, hr3, hS3⟩
  have hr3_eq : r3 = rd1 ^ (t + 1) +> ([1, 1] +> r) :=
    FC_full_unique (FC_eq hr3 rfl (by omega) rfl)
  subst hr3_eq
  refine ⟨w3, h3, ?_⟩
  have s1 := hS1 l
  have s2 := RInc_rule (l <+ l_tape w1) ([1] +> r) (t + 1)
  have heq2 : ([0] : List (Fin 2)) +> ([1] +> r) = [0, 1] +> r := rfl
  have heq2' : ([1] : List (Fin 2)) +> ([1] +> r) = [1, 1] +> r := rfl
  rw [heq2, heq2'] at s2
  have s3 := hL l (rd0 ^ (t + 1) +> ([1, 1] +> r))
  have s4 := hS3 l
  exact stepStar_trans s1
    (stepStar_trans (stepPlus_to_stepStar s2)
      (stepStar_trans (stepPlus_to_stepStar s3) s4))

lemma ldh_ld0_pow_half0 (k : Nat) :
    ldh <+ ld0 ^ k <+ Half 0 = default <+ cut_tag <+ ld0 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [left_pow_succ ldh ld0 k, left_pow_succ (default <+ cut_tag) ld0 k, ← ih]
    rfl

lemma Saturated_front (n : Nat) :
    ((ldh <+ ld0 ^ (n + 1)) {{B}}> ([1] +> (rd0 ^ (n + 1) +> (rd1 +> default)))) [target_tm]⊢⁺
    ((default <+ cut_tag <+ ld0 ^ (n + 1)) <{{C}} ([1] +> (rd0 ^ n +> ([1, 1, 0, 0] +> default)))) := by
  have hp := pow2_pos n
  have hp1 : 2 ≤ 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
  have hn : Normal (n + 1) ((2 ^ (n + 1) - 2) + 1) (List.replicate (2 * (n + 1)) true) :=
    Normal_eq (normal_full (n + 1)) rfl (by omega) rfl
  rcases normal_FC_Rpairs ([0, 1, 0, 0] +> default) (n + 1) (2 ^ (n + 1) - 2) hn
    (FC_insert_one default n) (by omega) with ⟨w1, r1, h1, hr1, hS1⟩
  have hr1_eq : r1 = rd1 ^ (n + 1) +> ([0, 1, 0, 0] +> default) :=
    FC_full_unique (FC_eq hr1 rfl (by omega) rfl)
  subst hr1_eq
  have h1' : Normal (n + 1) (1 + 0) w1 := Normal_eq h1 rfl (by omega) rfl
  rcases normal_LInc h1' with ⟨w2, h2, hL⟩
  have s1 := hS1 ldh
  rw [normal_full_tape (normal_full (n + 1)) rfl] at s1
  have s2 := RInc_rule (ldh <+ l_tape w1) ([1, 0, 0] +> default) (n + 1)
  have heq2 : ([0] : List (Fin 2)) +> ([1, 0, 0] +> (default : ListBlank (Fin 2))) = [0, 1, 0, 0] +> default := rfl
  have heq2' : ([1] : List (Fin 2)) +> ([1, 0, 0] +> (default : ListBlank (Fin 2))) = [1, 1, 0, 0] +> default := rfl
  rw [heq2, heq2'] at s2
  have s3 := hL ldh (rd0 ^ (n + 1) +> ([1, 1, 0, 0] +> default))
  rw [normal_zero_tape h2 rfl] at s3
  have s4 := RInc_rule (ldh <+ ld1 ^ (n + 1)) ([0, 0] +> (rd0 ^ n +> ([1, 1, 0, 0] +> default))) 0
  have heq4 : rd1 ^ 0 +> ([0] +> ([0, 0] +> (rd0 ^ n +> ([1, 1, 0, 0] +> default)))) =
      rd0 ^ (n + 1) +> ([1, 1, 0, 0] +> default) := by
    rw [right_pow_succ rd0 n ([1, 1, 0, 0] +> default)]
    rfl
  have heq4' : rd0 ^ 0 +> ([1] +> ([0, 0] +> (rd0 ^ n +> ([1, 1, 0, 0] +> default)))) =
      rd1 +> (rd0 ^ n +> ([1, 1, 0, 0] +> default)) := rfl
  rw [heq4, heq4'] at s4
  have s5 := LOv (rd1 +> (rd0 ^ n +> ([1, 1, 0, 0] +> default))) n
  rw [Nat.add_comm 1 n] at s5
  have s6 := R1100Turn (ldh <+ ld0 ^ (n + 1)) (rd0 ^ n +> ([1, 1, 0, 0] +> default))
  have heq6 : ([1] : List (Fin 2)) +> (rd1 +> (rd0 ^ n +> ([1, 1, 0, 0] +> default))) =
      [1, 1, 0, 0] +> (rd0 ^ n +> ([1, 1, 0, 0] +> default)) := rfl
  have heq6' := ldh_ld0_pow_half0 (n + 1)
  rw [← heq6, heq6'] at s6
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans s2
      (stepPlus_trans s3
        (stepPlus_trans s4
          (stepPlus_trans s5 s6))))

lemma to_cut (n : Nat) (hlen : 1 ≤ n) :
    ((ldh <+ ld0 ^ n) {{B}}> ([1] +> (rd0 ^ n +> (rd1 +> default)))) [target_tm]⊢⁺ cut n := by
  rcases n with _ | _ | n
  · omega
  · simpa [cut, rd0, rd1] using! saturated_one default
  · have hp := pow2_pos n
    have hp1 : 2 ≤ 2 ^ (n + 1 + 1) := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hn : Normal (n + 1 + 1) (1 + (2 ^ (n + 1 + 1) - 2)) (List.replicate (2 * (n + 1 + 1)) true) :=
      Normal_eq (normal_full (n + 1 + 1)) rfl (by omega) rfl
    rcases normal_LInc hn with ⟨w1, h1, hL⟩
    have h1' : Normal (n + 1 + 1) (2 ^ (1 + (n + 1)) - 2 + 0) w1 :=
      Normal_eq h1 rfl (by rw [show 1 + (n + 1) = n + 1 + 1 by omega]; omega) rfl
    rcases two_batches n (default <+ cut_tag) ([1, 0, 0] +> default) h1' with ⟨w2, h2, hS⟩
    rw [normal_zero_tape h2 rfl] at hS
    rw [normal_full_tape (normal_full (n + 1 + 1)) rfl] at hL
    have s1 := Saturated_front (n + 1)
    have s2 := hL (default <+ cut_tag) ([1] +> (rd0 ^ (n + 1) +> ([1, 1, 0, 0] +> default)))
    have heq2 : ([1, 1, 0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) =
        [1] +> ([1, 0, 0] +> default) := rfl
    have heq3 : ([1, 1] : List (Fin 2)) +> ([1, 0, 0] +> (default : ListBlank (Fin 2))) =
        [1, 1, 1, 0, 0] +> default := rfl
    rw [heq2] at s2
    rw [heq3] at hS
    exact stepPlus_trans s1 (stepPlus_stepStar_trans s2 hS)

lemma Saturated_full {n : Nat} {w : List Bool} {r : ListBlank (Fin 2)}
    (hn : Normal n (2 ^ n - 1) w) (hlen : 1 ≤ n) (hr : RC (2 ^ n) r) :
    ∃ c', Allowed c' ∧ (IC w r) [target_tm]⊢⁺ c' := by
  rcases cut_return n hlen with ⟨c', hA, hS⟩
  have hr1 : RC 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  have hr0 : RC (2 ^ n) (rd0 ^ n +> (rd1 +> default)) :=
    RC_eq (RC_zeros n hr1) (by omega) rfl
  have hr_eq : r = rd0 ^ n +> (rd1 +> default) := RC_unique hr hr0
  subst hr_eq
  refine ⟨c', hA, ?_⟩
  simp only [IC, normal_full_tape hn rfl]
  exact stepPlus_trans (to_cut n hlen) hS

lemma I_step {c : Cfg (Fin 2) (Fin 6)} (hI : IAllowed c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  cases hI with
  | intro n k w z r hN hlen hr hg =>
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · exact I_zero hN hlen hr
    · rcases hg with rfl | ⟨d, hd, hdn, hk⟩ | ⟨hk, hb⟩
      · omega
      · exact IClosure_small d hN hlen hr hz hd hdn hk
      · rcases Nat.lt_or_ge z (2 ^ n) with hlt | hge
        · exact IClosure_small n hN hlen hr hz hlt (Nat.le_refl n) (by omega)
        · rcases Nat.lt_or_ge (2 ^ n) z with hgt | hle
          · have hz1 : z = 2 ^ n + 1 := by omega
            subst hz1
            simp only [IC, normal_full_tape hN hk]
            exact cap_plus_one n hlen hr
          · have heq : z = 2 ^ n := by omega
            subst heq; subst hk; exact Saturated_full hN hlen hr

lemma Allowed_step {c : Cfg (Fin 2) (Fin 6)} (hA : Allowed c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  cases hA with
  | Ordinary c hI => exact I_step hI
  | Ten z c hJ =>
    rcases Ten_to_zero z hJ with ⟨c1, hJ0, hS1⟩
    rcases J_zero hJ0 with ⟨c2, hA2, hS2⟩
    exact ⟨c2, hA2, stepStar_stepPlus_trans hS1 hS2⟩
  | Signal z c hS =>
    rcases ST_to_zero z hS with ⟨c1, hS0, hS1⟩
    rcases S_zero hS0 with ⟨c2, hA2, hS2⟩
    exact ⟨c2, hA2, stepStar_stepPlus_trans hS1 hS2⟩

lemma seed_allowed : Allowed ((ldh <+ ld0 ^ 2) <{{C}} ([1, 0] +> (rd1 +> default))) := by
  have hr1 : RC 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  exact Allowed.Ten 1 _ (J_full 2 1 (rd1 +> default) (by omega) hr1 (Or.inr (by omega)))

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : Nat}
    (h : multiStep target_tm c k = none) (d : Nat) :
    multiStep target_tm c (k + d) = none := by
  rw [multiStep_add, h]; rfl

theorem reach_arbitrarily_long :
    ∀ m : Nat, ∃ N c, m ≤ N ∧ Allowed c ∧ multiStep target_tm (init []) N = some c
  | 0 => by
    rcases init_to_J2 with ⟨N₀, hN₀⟩
    exact ⟨N₀, _, Nat.zero_le N₀, seed_allowed, hN₀⟩
  | m + 1 => by
    rcases reach_arbitrarily_long m with ⟨N, c, h_le, hc, hN⟩
    rcases Allowed_step hc with ⟨c', hc', k, hk_pos, hk⟩
    exact ⟨N + k, c', by omega, hc', multiStep_trans target_tm _ _ _ N k hN hk⟩

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
    rcases reach_arbitrarily_long (k + 1) with ⟨N, _, h_ge, _, hN⟩
    have h_split : N = (k + 1) + (N - (k + 1)) := by omega
    have h_none_N : multiStep target_tm (init []) N = none := by
      rw [h_split]
      exact multiStep_none_add h_none (N - (k + 1))
    rw [h_none_N] at hN
    nomatch hN

end BusyBeaver.M_1RB0LE_1LC1RD_1LA0LC_1RA1RE_0RF0RB_1LCHHH
