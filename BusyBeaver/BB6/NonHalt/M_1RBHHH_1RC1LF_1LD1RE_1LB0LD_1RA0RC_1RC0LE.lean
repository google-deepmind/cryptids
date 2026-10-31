/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

open Counter

set_option linter.unusedSimpArgs false

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

-- ============================================================================
-- Section 1: Basic Utilities & PairWord
-- ============================================================================

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3

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

def rd1 : List (Fin 2) := [1, 0, 0, 0]
def rds : List (Fin 2) := [0, 0, 0, 1]

def bit (b : Bool) : Fin 2 := if b then 1 else 0

@[simp] lemma bit_false : bit false = 0 := rfl
@[simp] lemma bit_true : bit true = 1 := rfl

def pairs : List Bool → List (Fin 2)
  | [] => []
  | b :: u => bit b :: 1 :: pairs u

@[simp] lemma pairs_nil : pairs [] = [] := rfl
@[simp] lemma pairs_cons (b : Bool) (u : List Bool) :
    pairs (b :: u) = bit b :: 1 :: pairs u := rfl

def data (w : List Bool) : ListBlank (Fin 2) :=
  default <+ [1] <+ pairs w

@[simp] lemma data_cons (b : Bool) (u : List Bool) :
    data (b :: u) = data u <+ [bit b, 1] := rfl

def insert (b : Bool) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  if b then [1] +> r else r

@[simp] lemma insert_false (r : ListBlank (Fin 2)) : insert false r = r := rfl
@[simp] lemma insert_true (r : ListBlank (Fin 2)) : insert true r = [1] +> r := rfl

def Conf (w : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((data w <+ [0, 1]) {{C}}> r)

def inc : List Bool → List Bool × Bool
  | [] => ([false], false)
  | false :: u => (true :: u, false)
  | [true] => ([false], true)
  | true :: false :: u => (false :: true :: u, false)
  | [true, true] => ([false, false], true)
  | true :: true :: _ :: u =>
    let (v, e) := inc u
    (false :: false :: false :: v, e)

def push0 (n : Nat) (w : List Bool) : List Bool :=
  List.replicate n false ++ w

lemma push0_cons (n : Nat) (v : List Bool) :
    push0 n (false :: v) = push0 (n + 1) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [push0] at ih ⊢
    rw [List.replicate_succ, List.cons_append, ih]
    rfl

lemma pairs_push0 (n : Nat) (w : List Bool) :
    pairs (push0 n w) = ([0, 1] : List (Fin 2)) ^ n ++ pairs w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [push0] at ih ⊢
    rw [List.replicate_succ, List.cons_append, pairs_cons, bit_false, ih, pow_succ_list]
    rfl

lemma data_push0 (n : Nat) (w : List Bool) :
    data (push0 n w) = data w <+ ([0, 1] : List (Fin 2)) ^ n := by
  simp [data, pairs_push0]

lemma pow_comm_01 (n : Nat) (s : ListBlank (Fin 2)) :
    ([0, 1] : List (Fin 2)) ^ n +> ([0, 1] +> s) =
    [0, 1] +> (([0, 1] : List (Fin 2)) ^ n +> s) := by
  rw [← right_pow_succ_right [0, 1] n s, ← right_pow_succ [0, 1] n s]

lemma Conf_push0 (m : Nat) (w : List Bool) (r : ListBlank (Fin 2)) :
    Conf (push0 m w) r = ((data w <+ ([0, 1] : List (Fin 2)) ^ (m + 1)) {{C}}> r) := by
  dsimp [Conf]
  rw [data_push0, pow_succ_list]
  simp

lemma pairs_ones (n : Nat) (w : List Bool) :
    pairs (List.replicate n true ++ w) = ([1, 1] : List (Fin 2)) ^ n ++ pairs w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, pairs_cons, bit_true, ih, pow_succ_list]
    rfl

lemma data_ones (n : Nat) (w : List Bool) :
    data (List.replicate n true ++ w) = data w <+ ([1, 1] : List (Fin 2)) ^ n := by
  simp [data, pairs_ones]

lemma one_comm_11_pow (n : Nat) (r : ListBlank (Fin 2)) :
    ([1] : List (Fin 2)) +> (([1, 1] : List (Fin 2)) ^ n +> r) =
    ([1, 1] : List (Fin 2)) ^ n +> ([1] +> r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [right_pow_succ [1, 1] n r, right_pow_succ [1, 1] n ([1] +> r), ← ih]
    rfl

lemma insert_scan (b : Bool) (n : Nat) (r : ListBlank (Fin 2)) :
    insert b (([1, 1] : List (Fin 2)) ^ n +> r) =
    ([1, 1] : List (Fin 2)) ^ n +> insert b r := by
  cases b
  · rfl
  · exact one_comm_11_pow n r

macro "step1" : tactic => `(tactic| (
  try simp only [init_nil, rd0, rd1, rds, bit_false, bit_true,
    pairs_nil, pairs_cons, data, insert_false, insert_true,
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
  simp only [rd0, rd1, rds, bit_false, bit_true,
    pairs_nil, pairs_cons, data, insert_false, insert_true,
    pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail, multiStep_zero]
  rfl))

-- ============================================================================
-- Section 2: Machine-Specific Rules (A2Words)
-- ============================================================================

lemma CScan_step (l r : ListBlank (Fin 2)) :
    (l {{C}}> (rd1 +> r)) [target_tm]⊢⁺
    ((l <+ ([1, 1] : List (Fin 2)) ^ 2) {{C}}> r) :=
  ⟨4, by omega, by run_steps 4⟩

lemma CScan (l r : ListBlank (Fin 2)) (n : Nat) :
    (l {{C}}> (rd1 ^ n +> r)) [target_tm]⊢*
    ((l <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) {{C}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [right_pow_succ rd1 n r, show (n + 1) * 2 = n * 2 + 2 by omega,
        left_pow_add l [1, 1] (n * 2) 2]
    exact stepStar_trans (stepPlus_to_stepStar (CScan_step l (rd1 ^ n +> r)))
      (ih (l <+ ([1, 1] : List (Fin 2)) ^ 2))

lemma CZero (l r : ListBlank (Fin 2)) :
    (l {{C}}> ([0] +> r)) [target_tm]⊢⁺
    (l <{{D}} ([1] +> r)) :=
  ⟨1, by omega, by run_steps 1⟩

lemma DScan_step (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1] : List (Fin 2)) ^ 2) <{{D}} r) [target_tm]⊢⁺
    (l <{{D}} (rd0 +> r)) :=
  ⟨4, by omega, by run_steps 4⟩

lemma DScan (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) <{{D}} r) [target_tm]⊢*
    (l <{{D}} (rd0 ^ n +> r)) := by
  induction n generalizing r with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [show (n + 1) * 2 = 2 + n * 2 by omega, left_pow_add l [1, 1] 2 (n * 2),
        right_pow_succ_right rd0 n r]
    exact stepStar_trans (stepPlus_to_stepStar (DScan_step (l <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) r))
      (ih (rd0 +> r))

lemma RInc4 (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ n +> ([0] +> r))) [target_tm]⊢⁺
    ((l <+ [0, 1]) <{{D}} (rd0 ^ n +> ([1] +> r))) := by
  have s1 := CScan (l <+ [0, 1]) ([0] +> r) n
  have s2 := CZero (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) r
  have s3 := DScan (l <+ [0, 1]) ([1] +> r) n
  exact stepStar_stepPlus_trans s1 (stepPlus_stepStar_trans s2 s3)

lemma LStart (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1]) <{{D}} r) [target_tm]⊢⁺
    (l {{B}}> ([1, 1] +> r)) :=
  ⟨1, by omega, by run_steps 1⟩

lemma ZCarryMarked (b : Bool) (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 1, 1, bit b, 1]) {{B}}> ([1] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([1, 1, 1, 1, 1, 1, 1] +> r)) := by
  cases b
  · exact ⟨14, by omega, by run_steps 14⟩
  · exact ⟨10, by omega, by run_steps 10⟩

lemma BScan6_step (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1] : List (Fin 2)) ^ 3) {{B}}> ([1] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([1] +> (([1, 1] : List (Fin 2)) ^ 3 +> r))) :=
  ⟨10, by omega, by run_steps 10⟩

lemma BScan6 (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ ([1, 1] : List (Fin 2)) ^ (n * 3)) {{B}}> ([1] +> r)) [target_tm]⊢*
    (l {{B}}> ([1] +> (([1, 1] : List (Fin 2)) ^ (n * 3) +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [show (n + 1) * 3 = 3 + n * 3 by omega, left_pow_add l [1, 1] 3 (n * 3),
        show 3 + n * 3 = n * 3 + 3 by omega, list_pow_add [1, 1] (n * 3) 3,
        listblank_append_assoc]
    exact stepStar_trans
      (stepPlus_to_stepStar (BScan6_step (l <+ ([1, 1] : List (Fin 2)) ^ (n * 3)) r))
      (ih (([1, 1] : List (Fin 2)) ^ 3 +> r))

lemma C11_step (l r : ListBlank (Fin 2)) :
    (l {{C}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((l <+ [0, 1]) {{C}}> r) :=
  ⟨2, by omega, by run_steps 2⟩

lemma CScan11 (l r : ListBlank (Fin 2)) (n : Nat) :
    (l {{C}}> (([1, 1] : List (Fin 2)) ^ n +> r)) [target_tm]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ n) {{C}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl _
  | succ n ih =>
    rw [right_pow_succ [1, 1] n r, show n + 1 = n + 1 by rfl,
        left_pow_add l [0, 1] n 1]
    exact stepStar_trans (stepPlus_to_stepStar (C11_step l (([1, 1] : List (Fin 2)) ^ n +> r)))
      (ih (l <+ [0, 1]))

lemma REleven (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ n +> ([1, 1] +> r))) [target_tm]⊢⁺
    ((l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2) <+ [0, 1]) {{C}}> r) :=
  stepStar_stepPlus_trans (CScan (l <+ [0, 1]) ([1, 1] +> r) n)
    (C11_step (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) r)

lemma ZInc_nil (r : ListBlank (Fin 2)) :
    (data [] {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data [false] <+ [0, 1]) {{C}}> insert false r) :=
  ⟨14, by omega, by run_steps 14⟩

lemma ZInc_false (u : List Bool) (r : ListBlank (Fin 2)) :
    (data (false :: u) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data (true :: u) <+ [0, 1]) {{C}}> insert false r) :=
  ⟨4, by omega, by run_steps 4⟩

lemma ZInc_one_true (r : ListBlank (Fin 2)) :
    (data [true] {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data [false] <+ [0, 1]) {{C}}> insert true r) :=
  ⟨11, by omega, by run_steps 11⟩

lemma ZInc_true_false (u : List Bool) (r : ListBlank (Fin 2)) :
    (data (true :: false :: u) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data (false :: true :: u) <+ [0, 1]) {{C}}> insert false r) :=
  ⟨10, by omega, by run_steps 10⟩

lemma ZInc_two_true (r : ListBlank (Fin 2)) :
    (data [true, true] {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data [false, false] <+ [0, 1]) {{C}}> insert true r) :=
  ⟨17, by omega, by run_steps 17⟩

lemma ZInc_rec_exit (v : List Bool) (e : Bool) (r : ListBlank (Fin 2)) :
    ((data v <+ [0, 1]) {{C}}> insert e ([1, 1, 1, 1, 1, 1] +> r)) [target_tm]⊢⁺
    ((data (false :: false :: false :: v) <+ [0, 1]) {{C}}> insert e r) := by
  cases e <;> exact ⟨6, by omega, by run_steps 6⟩

lemma ZInc (w : List Bool) (r : ListBlank (Fin 2)) :
    (data w {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data (inc w).1 <+ [0, 1]) {{C}}> insert (inc w).2 r) := by
  match w with
  | [] => exact ZInc_nil r
  | false :: u => exact ZInc_false u r
  | [true] => exact ZInc_one_true r
  | true :: false :: u => exact ZInc_true_false u r
  | [true, true] => exact ZInc_two_true r
  | true :: true :: b :: u =>
    have s1 : (data (true :: true :: b :: u) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
        (data u {{B}}> ([1, 1] +> ([1, 1, 1, 1, 1, 1] +> r))) := by
      simpa [data, pairs] using ZCarryMarked b (data u) ([1] +> r)
    have s2 := ZInc u ([1, 1, 1, 1, 1, 1] +> r)
    have s3 := ZInc_rec_exit (inc u).1 (inc u).2 r
    have hinc : inc (true :: true :: b :: u) = (false :: false :: false :: (inc u).1, (inc u).2) := by
      simp [inc]
    rw [hinc]
    exact stepPlus_trans s1 (stepPlus_trans s2 s3)

lemma LIncWord (w : List Bool) (r : ListBlank (Fin 2)) :
    ((data w <+ [0, 1]) <{{D}} r) [target_tm]⊢⁺
    ((data (inc w).1 <+ [0, 1]) {{C}}> insert (inc w).2 r) :=
  stepPlus_trans (LStart (data w) r) (ZInc w r)

lemma RZero (w : List Bool) (r : ListBlank (Fin 2)) (n : Nat) :
    ((data w <+ [0, 1]) {{C}}> (rd1 ^ n +> ([0] +> r))) [target_tm]⊢⁺
    ((data (inc w).1 <+ [0, 1]) {{C}}> insert (inc w).2 (rd0 ^ n +> ([1] +> r))) :=
  stepPlus_trans (RInc4 (data w) r n) (LIncWord w (rd0 ^ n +> ([1] +> r)))

lemma C1001_exit (l r : ListBlank (Fin 2)) :
    (l {{C}}> ([1, 0, 0, 1] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([1, 1, 1, 1] +> r)) :=
  ⟨8, by omega, by run_steps 8⟩

lemma B_mod0_turn (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1]) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((l <+ [1, 1] <+ [0, 1]) {{C}}> r) :=
  ⟨4, by omega, by run_steps 4⟩

lemma B_mod2_turn (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1] <+ [1, 1]) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ 2) {{C}}> r) :=
  ⟨10, by omega, by run_steps 10⟩

lemma R1001_mod0 (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ (n * 3) +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 2)) {{C}}> r) := by
  have s1 := CScan (l <+ [0, 1]) ([1, 0, 0, 1] +> r) (n * 3)
  have s2 := C1001_exit (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 3 * 2)) r
  have hmul : n * 3 * 2 = (n * 2) * 3 := by omega
  have hr1 : ([1, 1, 1, 1] : List (Fin 2)) +> r = [1] +> ([1, 1, 1] +> r) := rfl
  rw [hmul] at s1 s2
  rw [hr1] at s2
  have s3 := BScan6 (l <+ [0, 1]) ([1, 1, 1] +> r) (n * 2)
  have hr2 : ([1] : List (Fin 2)) +> (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1, 1, 1] +> r)) =
      [1, 1] +> (([1, 1] : List (Fin 2)) ^ (n * 6 + 1) +> r) := by
    rw [show n * 6 + 1 = n * 2 * 3 + 1 by omega, right_pow_succ_right [1, 1] (n * 2 * 3) r]
    change ([1] : List (Fin 2)) +> (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1] +> ([1, 1] +> r))) =
      [1] +> ([1] +> (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1, 1] +> r)))
    rw [one_comm_11_pow (n * 2 * 3) ([1, 1] +> r)]
  rw [hr2] at s3
  have s4 := B_mod0_turn l (([1, 1] : List (Fin 2)) ^ (n * 6 + 1) +> r)
  have s5 := CScan11 (l <+ [1, 1] <+ [0, 1]) r (n * 6 + 1)
  have hl : l <+ [1, 1] <+ [0, 1] <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 1) =
      l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 2) := by
    rw [show n * 6 + 2 = (n * 6 + 1) + 1 by omega, left_pow_add (l <+ [1, 1]) [0, 1] (n * 6 + 1) 1]
    rfl
  rw [hl] at s5
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans (stepPlus_stepStar_trans s2 s3) (stepPlus_stepStar_trans s4 s5))

lemma R1001_mod2 (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ (n * 3 + 2) +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 6)) {{C}}> r) := by
  have s1 := CScan (l <+ [0, 1]) ([1, 0, 0, 1] +> r) (n * 3 + 2)
  have s2 := C1001_exit (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ ((n * 3 + 2) * 2)) r
  have hmul : l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ ((n * 3 + 2) * 2) =
      l <+ [0, 1] <+ [1, 1] <+ ([1, 1] : List (Fin 2)) ^ ((n * 2 + 1) * 3) := by
    rw [show (n * 3 + 2) * 2 = (n * 2 + 1) * 3 + 1 by omega,
        left_pow_add (l <+ [0, 1]) [1, 1] ((n * 2 + 1) * 3) 1]
    rfl
  have hr1 : ([1, 1, 1, 1] : List (Fin 2)) +> r = [1] +> ([1, 1, 1] +> r) := rfl
  rw [hmul] at s1 s2
  rw [hr1] at s2
  have s3 := BScan6 (l <+ [0, 1] <+ [1, 1]) ([1, 1, 1] +> r) (n * 2 + 1)
  have hr2 : ([1] : List (Fin 2)) +> (([1, 1] : List (Fin 2)) ^ ((n * 2 + 1) * 3) +> ([1, 1, 1] +> r)) =
      [1, 1] +> (([1, 1] : List (Fin 2)) ^ (n * 6 + 4) +> r) := by
    rw [show n * 6 + 4 = (n * 2 + 1) * 3 + 1 by omega,
        right_pow_succ_right [1, 1] ((n * 2 + 1) * 3) r]
    change ([1] : List (Fin 2)) +> (([1, 1] : List (Fin 2)) ^ ((n * 2 + 1) * 3) +> ([1] +> ([1, 1] +> r))) =
      [1] +> ([1] +> (([1, 1] : List (Fin 2)) ^ ((n * 2 + 1) * 3) +> ([1, 1] +> r)))
    rw [one_comm_11_pow ((n * 2 + 1) * 3) ([1, 1] +> r)]
  rw [hr2] at s3
  have s4 := B_mod2_turn l (([1, 1] : List (Fin 2)) ^ (n * 6 + 4) +> r)
  have s5 := CScan11 (l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ 2) r (n * 6 + 4)
  have hl : l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ 2 <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 4) =
      l <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 6) := by
    rw [show n * 6 + 6 = (n * 6 + 4) + 2 by omega, left_pow_add (l <+ [1, 1]) [0, 1] (n * 6 + 4) 2]
  rw [hl] at s5
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans (stepPlus_stepStar_trans s2 s3) (stepPlus_stepStar_trans s4 s5))

lemma R1001_call (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ (n * 3 + 1) +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    (l {{B}}> ([1, 1] +> (([1, 1] : List (Fin 2)) ^ (n * 6 + 4) +> r))) := by
  have s1 := CScan (l <+ [0, 1]) ([1, 0, 0, 1] +> r) (n * 3 + 1)
  have s2 := C1001_exit (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ ((n * 3 + 1) * 2)) r
  have hmul : l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ ((n * 3 + 1) * 2) =
      l <+ [1, 1, 1, 1, bit false, 1] <+ ([1, 1] : List (Fin 2)) ^ ((n * 2) * 3) := by
    rw [show (n * 3 + 1) * 2 = (n * 2) * 3 + 2 by omega,
        left_pow_add (l <+ [0, 1]) [1, 1] ((n * 2) * 3) 2]
    rfl
  have hr1 : ([1, 1, 1, 1] : List (Fin 2)) +> r = [1] +> ([1, 1, 1] +> r) := rfl
  rw [hmul] at s1 s2
  rw [hr1] at s2
  have s3 := BScan6 (l <+ [1, 1, 1, 1, bit false, 1]) ([1, 1, 1] +> r) (n * 2)
  have s4 := ZCarryMarked false l (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1, 1, 1] +> r))
  have hr2 : ([1, 1, 1, 1, 1, 1, 1] : List (Fin 2)) +>
      (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1, 1, 1] +> r)) =
      [1, 1] +> (([1, 1] : List (Fin 2)) ^ (n * 6 + 4) +> r) := by
    rw [show n * 6 + 4 = 2 + (n * 2 * 3 + 2) by omega,
        list_pow_add [1, 1] 2 (n * 2 * 3 + 2), listblank_append_assoc,
        right_pow_succ_right [1, 1] (n * 2 * 3 + 1) r,
        right_pow_succ_right [1, 1] (n * 2 * 3) ([1, 1] +> r)]
    change [1, 1] +> (([1, 1] : List (Fin 2)) ^ 2 +> ([1] +>
      (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1] +> ([1, 1] +> r))))) =
      [1, 1] +> (([1, 1] : List (Fin 2)) ^ 2 +>
      (([1, 1] : List (Fin 2)) ^ (n * 2 * 3) +> ([1, 1] +> ([1, 1] +> r))))
    rw [one_comm_11_pow (n * 2 * 3) ([1] +> ([1, 1] +> r))]
    rfl
  rw [hr2] at s4
  exact stepStar_stepPlus_trans s1
    (stepPlus_trans (stepPlus_stepStar_trans s2 s3) s4)

lemma R1001_return (w : List Bool) (r : ListBlank (Fin 2)) (n : Nat) :
    (Conf w (rd1 ^ (n * 3 + 1) +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    (Conf (push0 (n * 6 + 4) (inc w).1) (insert (inc w).2 r)) := by
  have s1 := R1001_call (data w) r n
  have s2 := ZInc w (([1, 1] : List (Fin 2)) ^ (n * 6 + 4) +> r)
  rw [insert_scan (inc w).2 (n * 6 + 4) r] at s2
  have s3 := CScan11 (data (inc w).1 <+ [0, 1]) (insert (inc w).2 r) (n * 6 + 4)
  have hl : data (inc w).1 <+ [0, 1] <+ ([0, 1] : List (Fin 2)) ^ (n * 6 + 4) =
      data (push0 (n * 6 + 4) (inc w).1) <+ [0, 1] := by
    rw [data_push0]
    exact pow_comm_01 (n * 6 + 4) (data (inc w).1)
  rw [hl] at s3
  exact stepPlus_trans s1 (stepPlus_stepStar_trans s2 s3)

lemma init31 :
    (init []) [target_tm]⊢* Conf [false, false] default :=
  ⟨31, by run_steps 31⟩

-- ============================================================================
-- Section 3: Right Counter (Pair12Right & PairOrdinary)
-- ============================================================================

lemma pow_two_four (t : Nat) : 2 ^ (2 * t) = 4 ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, Nat.pow_add, ih, Nat.pow_succ]
    ring

lemma pow4_pos (k : Nat) : 0 < 4 ^ k := by
  rw [← pow_two_four]
  exact pow2_pos (2 * k)

lemma FC_leading_one (t : Nat) (r : ListBlank (Fin 2)) :
    FC rd1 ([0] +> (rd1 +> r)) (t + 1) 1 ([1] +> (rd0 ^ (t + 1) +> (rd1 +> r))) := by
  have h0 := FC.d1 t 0 (rd0 ^ t +> ([0] +> (rd1 +> r))) (FC_zero rd1 ([0] +> (rd1 +> r)) t)
  have heq : rd1 +> (rd0 ^ t +> ([0] +> (rd1 +> r))) =
      [1] +> (rd0 ^ (t + 1) +> (rd1 +> r)) := by
    rw [right_pow_succ rd0 t (rd1 +> r)]
    change rd1 +> (rd0 ^ t +> (([0] : List (Fin 2)) +> (rd1 +> r))) =
      rd1 +> (([0] : List (Fin 2)) +> (rd0 ^ t +> (rd1 +> r)))
    rw [one_zero_comm_rd0_pow t (rd1 +> r)]
  exact FC_eq h0 rfl (by omega) heq

lemma RC_shift3 {n : Nat} {r : ListBlank (Fin 2)} (h : RC rd1 n r) :
    RC rds n ([0, 0, 0] +> r) := by
  induction h with
  | zero =>
    rw [three_zeros_append_default]
    exact RC.zero
  | d0 n r _ ih =>
    have heq : ([0, 0, 0] : List (Fin 2)) +> (rd0 +> r) = rd0 +> ([0, 0, 0] +> r) := rfl
    rw [heq]
    exact RC.d0 n ([0, 0, 0] +> r) ih
  | d1 n r _ ih =>
    have heq : ([0, 0, 0] : List (Fin 2)) +> (rd1 +> r) = rds +> ([0, 0, 0] +> r) := rfl
    rw [heq]
    exact RC.d1 n ([0, 0, 0] +> r) ih

-- ============================================================================
-- Section 4: PairGuard, PairCarry, PairPrefix, PairOverflow,
--            PairShiftGuard & PairEntryGuard
-- ============================================================================

def bit_value (b : Bool) : Nat := if b then 1 else 0
def zero_bit (b : Bool) : Nat := if b then 0 else 1

def digit_plane (f : Bool → Nat) : Nat → List Bool → Nat
  | _, [] => 0
  | 0, b :: u => f b + 4 * digit_plane f 2 u
  | j + 1, _ :: u => digit_plane f j u

def width : List Bool → Nat
  | [] => 0
  | [_] => 1
  | [_, _] => 2
  | _ :: _ :: _ :: u => 2 + width u

def value (w : List Bool) : Nat :=
  digit_plane bit_value 0 w + 2 * digit_plane bit_value 1 w
def gap0 (w : List Bool) : Nat :=
  1 + digit_plane zero_bit 0 w + 2 * digit_plane zero_bit 1 w
def gap1 (w : List Bool) : Nat :=
  2 + 2 * digit_plane zero_bit 0 w + 4 * digit_plane zero_bit 2 w
def gap2 (w : List Bool) : Nat :=
  4 + 4 * digit_plane zero_bit 1 w + 8 * digit_plane zero_bit 2 w

def guard (n : Nat) (w : List Bool) : Prop :=
  2 * n ≤ gap0 w ∧ 2 * n ≤ gap1 w ∧ 2 * n ≤ gap2 w

lemma gap_bounds (w : List Bool) : 1 ≤ gap0 w ∧ 2 ≤ gap1 w ∧ 4 ≤ gap2 w := by
  dsimp [gap0, gap1, gap2]; omega

lemma gap2_four (w : List Bool) :
    gap2 w = 4 * (1 + digit_plane zero_bit 1 w + 2 * digit_plane zero_bit 2 w) := by
  dsimp [gap2]; omega

lemma value_gap0 (w : List Bool) : value w + gap0 w = 2 ^ width w := by
  match w with
  | [] => rfl
  | [a] => cases a <;> rfl
  | [a, b] => cases a <;> cases b <;> rfl
  | a :: b :: c :: u =>
    have ih := value_gap0 u
    dsimp [value, gap0, digit_plane, width] at ih ⊢
    rw [Nat.add_comm 2 (width u), Nat.pow_add]
    cases a <;> cases b <;> dsimp [bit_value, zero_bit] <;> omega

lemma inc_half (w : List Bool) :
    gap1 w ≤ 2 * gap1 (inc w).1 ∧ gap2 w ≤ 2 * gap2 (inc w).1 := by
  match w with
  | [] => dsimp [inc, gap1, gap2, digit_plane, zero_bit]; omega
  | false :: u => dsimp [inc, gap1, gap2, digit_plane, zero_bit]; omega
  | [true] => dsimp [inc, gap1, gap2, digit_plane, zero_bit]; omega
  | true :: false :: u => dsimp [inc, gap1, gap2, digit_plane, zero_bit]; omega
  | [true, true] => dsimp [inc, gap1, gap2, digit_plane, zero_bit]; omega
  | true :: true :: b :: u =>
    have ih := inc_half u
    cases b <;> dsimp [inc, gap1, gap2, digit_plane, zero_bit] at ih ⊢ <;> omega

lemma inc_interior (w : List Bool) (h : 1 < gap0 w) :
    (inc w).2 = false ∧ (inc w).1.length = w.length ∧ gap0 (inc w).1 + 1 = gap0 w := by
  match w with
  | [] => dsimp [gap0, digit_plane] at h; omega
  | false :: u =>
    dsimp [inc, gap0, digit_plane, zero_bit] at h ⊢
    exact ⟨rfl, rfl, by omega⟩
  | [true] => dsimp [gap0, digit_plane, zero_bit] at h; omega
  | true :: false :: u =>
    dsimp [inc, gap0, digit_plane, zero_bit] at h ⊢
    exact ⟨rfl, rfl, by omega⟩
  | [true, true] => dsimp [gap0, digit_plane, zero_bit] at h; omega
  | true :: true :: b :: u =>
    have hu : 1 < gap0 u := by
      dsimp [gap0, digit_plane, zero_bit] at h ⊢
      omega
    rcases inc_interior u hu with ⟨he, hl, hg⟩
    dsimp [inc, gap0, digit_plane, zero_bit] at hg ⊢
    refine ⟨he, by simp [hl], by omega⟩

inductive inc_steps : Nat → List Bool → List Bool → Prop
  | zero (w : List Bool) : inc_steps 0 w w
  | succ (q : Nat) (w u v : List Bool) :
      inc w = (u, false) → inc_steps q u v → inc_steps (q + 1) w v

lemma inc_steps_interior (q : Nat) (w : List Bool) (h : q < gap0 w) :
    ∃ v, inc_steps q w v ∧ v.length = w.length ∧ gap0 v + q = gap0 w := by
  induction q generalizing w with
  | zero => exact ⟨w, inc_steps.zero w, rfl, by omega⟩
  | succ q ih =>
    rcases inc_interior w (by omega) with ⟨he, hl, hg⟩
    have hinc : inc w = ((inc w).1, false) := Prod.ext rfl he
    rcases ih (inc w).1 (by omega) with ⟨v, hs, hvl, hvg⟩
    exact ⟨v, inc_steps.succ q w (inc w).1 v hinc hs, by omega, by omega⟩

lemma inc_steps_trans {p q : Nat} {w u v : List Bool}
    (h1 : inc_steps p w u) (h2 : inc_steps q u v) : inc_steps (p + q) w v := by
  induction h1 with
  | zero => rw [Nat.zero_add]; exact h2
  | succ p w mid _ hinc _ ih =>
    rw [Nat.succ_add]
    exact inc_steps.succ (p + q) w mid v hinc (ih h2)

lemma inc_steps_add_inv {p q : Nat} {w v : List Bool} (h : inc_steps (p + q) w v) :
    ∃ u, inc_steps p w u ∧ inc_steps q u v := by
  induction p generalizing w with
  | zero =>
    rw [Nat.zero_add] at h
    exact ⟨w, inc_steps.zero w, h⟩
  | succ p ih =>
    rw [Nat.succ_add] at h
    cases h with
    | succ _ _ u _ hinc hs =>
      rcases ih hs with ⟨mid, hp, hq⟩
      exact ⟨mid, inc_steps.succ p w u mid hinc hp, hq⟩

lemma value_triple (a b marker : Bool) (w : List Bool) :
    value (a :: b :: marker :: w) = bit_value a + 2 * bit_value b + 4 * value w := by
  dsimp [value, digit_plane]; omega

lemma prefix_value_bound (t : Nat) (rho : List Bool) (hlen : rho.length = 3 * t) :
    value rho < 4 ^ t := by
  induction t generalizing rho with
  | zero =>
    cases rho with
    | nil => decide
    | cons _ _ => simp at hlen
  | succ t ih =>
    rcases rho with _ | ⟨a, _ | ⟨b, _ | ⟨marker, rho⟩⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · simp at hlen; omega
    · have htail : rho.length = 3 * t := by simp at hlen; omega
      have h := ih rho htail
      rw [value_triple, Nat.pow_succ]
      cases a <;> cases b <;> dsimp [bit_value] <;> omega

lemma inc_split (t : Nat) (rho u v : List Bool) (hlen : rho.length = 3 * t)
    (he : inc (rho ++ u) = (v, false)) :
    ∃ rho' u' c, v = rho' ++ u' ∧ rho'.length = 3 * t ∧
      inc_steps c u u' ∧ c ≤ 1 ∧ c * 4 ^ t + value rho' = value rho + 1 := by
  induction t generalizing rho v with
  | zero =>
    cases rho with
    | nil =>
      refine ⟨[], v, 1, rfl, rfl, ?_, by omega, ?_⟩
      · exact inc_steps.succ 0 u v v he (inc_steps.zero v)
      · dsimp [value, digit_plane]
    | cons _ _ => simp at hlen
  | succ t ih =>
    rcases rho with _ | ⟨a, _ | ⟨b, _ | ⟨marker, rho⟩⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · simp at hlen; omega
    · have htail : rho.length = 3 * t := by simp at hlen; omega
      cases a with
      | false =>
        dsimp [inc] at he
        injection he with hv _
        subst hv
        refine ⟨true :: b :: marker :: rho, u, 0, rfl, by simp [htail]; omega,
          inc_steps.zero u, by omega, ?_⟩
        rw [value_triple, value_triple]
        dsimp [bit_value]
        omega
      | true =>
        cases b with
        | false =>
          dsimp [inc] at he
          injection he with hv _
          subst hv
          refine ⟨false :: true :: marker :: rho, u, 0, rfl, by simp [htail]; omega,
            inc_steps.zero u, by omega, ?_⟩
          rw [value_triple, value_triple]
          dsimp [bit_value]
          omega
        | true =>
          dsimp [inc] at he
          have he2 : (inc (rho ++ u)).2 = false := congrArg Prod.snd he
          have he0 : inc (rho ++ u) = ((inc (rho ++ u)).1, false) :=
            Prod.ext rfl he2
          have hv : v = false :: false :: false :: (inc (rho ++ u)).1 :=
            (congrArg Prod.fst he).symm
          subst hv
          rcases ih rho (inc (rho ++ u)).1 htail he0 with
            ⟨rho', u', c, hrho, hl', hs, hc, hval⟩
          refine ⟨false :: false :: false :: rho', u', c, by simp [hrho],
            by simp [hl']; omega, hs, hc, ?_⟩
          rw [value_triple, value_triple, Nat.pow_succ]
          dsimp [bit_value]
          nlinarith

lemma inc_steps_split (t q : Nat) (rho u v : List Bool) (hlen : rho.length = 3 * t)
    (hs : inc_steps q (rho ++ u) v) :
    ∃ rho' u' c, v = rho' ++ u' ∧ rho'.length = 3 * t ∧
      inc_steps c u u' ∧ c * 4 ^ t + value rho' = value rho + q := by
  induction q generalizing rho u v with
  | zero =>
    cases hs
    exact ⟨rho, u, 0, rfl, hlen, inc_steps.zero u, by omega⟩
  | succ q ih =>
    cases hs with
    | succ _ _ mid _ hinc hrest =>
      rcases inc_split t rho u mid hlen hinc with
        ⟨rho1, u1, c1, hmid, hl1, hs1, _, hv1⟩
      subst hmid
      rcases ih rho1 u1 v hl1 hrest with ⟨rho2, u2, c2, hv, hl2, hs2, hv2⟩
      refine ⟨rho2, u2, c1 + c2, hv, hl2, inc_steps_trans hs1 hs2, ?_⟩
      nlinarith

lemma carry_bound (t : Nat) (rho rho' : List Bool) (c q h : Nat)
    (hlen : rho.length = 3 * t) (hval : c * 4 ^ t + value rho' = value rho + q)
    (hq : q ≤ h * 4 ^ t) : c ≤ h := by
  have hb := prefix_value_bound t rho hlen
  have hp := pow4_pos t
  nlinarith

lemma inc_steps_split_bounded (t q h : Nat) (rho u v : List Bool)
    (hlen : rho.length = 3 * t) (hs : inc_steps q (rho ++ u) v) (hq : q ≤ h * 4 ^ t) :
    ∃ rho' u' c, v = rho' ++ u' ∧ rho'.length = 3 * t ∧ inc_steps c u u' ∧
      c ≤ h ∧ c * 4 ^ t + value rho' = value rho + q := by
  rcases inc_steps_split t q rho u v hlen hs with ⟨rho', u', c, hv, hl, hsc, he⟩
  exact ⟨rho', u', c, hv, hl, hsc, carry_bound t rho rho' c q h hlen he hq, he⟩

lemma zero_bit_bound (b : Bool) : zero_bit b ≤ 1 := by
  cases b <;> decide

lemma gap_cons (b : Bool) (w : List Bool) :
    gap0 (b :: w) + 1 = gap1 w + zero_bit b ∧
    gap1 (b :: w) + 2 = gap2 w + 2 * zero_bit b ∧
    gap2 (b :: w) = 4 * gap0 w := by
  dsimp [gap0, gap1, gap2, digit_plane]; omega

lemma gap_triple (a b c : Bool) (w : List Bool) :
    gap0 (a :: b :: c :: w) + 3 = 4 * gap0 w + zero_bit a + 2 * zero_bit b ∧
    gap1 (a :: b :: c :: w) + 6 = 4 * gap1 w + 2 * zero_bit a + 4 * zero_bit c ∧
    gap2 (a :: b :: c :: w) + 12 = 4 * gap2 w + 4 * zero_bit b + 8 * zero_bit c := by
  dsimp [gap0, gap1, gap2, digit_plane]; omega

lemma gap_triple_upper (a b c : Bool) (w : List Bool) :
    gap0 (a :: b :: c :: w) ≤ 4 * gap0 w ∧
    gap1 (a :: b :: c :: w) ≤ 4 * gap1 w ∧
    gap2 (a :: b :: c :: w) ≤ 4 * gap2 w := by
  have ht := gap_triple a b c w
  have ha := zero_bit_bound a
  have hb := zero_bit_bound b
  have hc := zero_bit_bound c
  omega

lemma prefix_triples_upper (t : Nat) (z w : List Bool) (hl : z.length = 3 * t) :
    gap0 (z ++ w) ≤ 4 ^ t * gap0 w ∧
    gap1 (z ++ w) ≤ 4 ^ t * gap1 w ∧
    gap2 (z ++ w) ≤ 4 ^ t * gap2 w := by
  induction t generalizing z with
  | zero =>
    cases z with
    | nil => simp
    | cons _ _ => simp at hl
  | succ t ih =>
    rcases z with _ | ⟨a, _ | ⟨b, _ | ⟨c, z⟩⟩⟩
    · simp at hl
    · simp at hl; omega
    · simp at hl; omega
    · have htail : z.length = 3 * t := by simp at hl; omega
      rcases ih z htail with ⟨h0, h1, h2⟩
      rcases gap_triple_upper a b c (z ++ w) with ⟨u0, u1, u2⟩
      simp only [List.cons_append]
      rw [Nat.pow_succ]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma triple_preserve (H : Nat) (a b c : Bool) (w : List Bool)
    (hH : 4 ≤ H) (h0 : H ≤ gap0 w) (h1 : H ≤ gap1 w) (h2 : H ≤ gap2 w) :
    H ≤ gap0 (a :: b :: c :: w) ∧ H ≤ gap1 (a :: b :: c :: w) ∧ H ≤ gap2 (a :: b :: c :: w) := by
  have ht := gap_triple a b c w
  omega

lemma gap_01 (w : List Bool) :
    gap0 (false :: true :: w) + 2 = gap2 w ∧
    gap1 (false :: true :: w) = 4 * gap0 w ∧
    gap2 (false :: true :: w) + 4 = 4 * gap1 w := by
  dsimp [gap0, gap1, gap2, digit_plane, zero_bit]; omega

lemma gap_zero4 (w : List Bool) :
    gap0 (false :: false :: false :: false :: w) = 4 * gap1 w ∧
    gap1 (false :: false :: false :: false :: w) = 4 * gap2 w ∧
    gap2 (false :: false :: false :: false :: w) = 16 * gap0 w := by
  dsimp [gap0, gap1, gap2, digit_plane, zero_bit]; omega

lemma zero4_eight (w : List Bool) :
    8 ≤ gap0 (false :: false :: false :: false :: w) ∧
    8 ≤ gap1 (false :: false :: false :: false :: w) ∧
    8 ≤ gap2 (false :: false :: false :: false :: w) := by
  have hz := gap_zero4 w
  have hb := gap_bounds w
  omega

lemma long_prefix (H : Nat) (z w : List Bool) (hH : 4 ≤ H) (hl : 7 ≤ z.length)
    (h0 : H + 1 ≤ gap0 w) (h1 : H + 1 ≤ gap1 w) (h2 : H + 1 ≤ gap2 w) :
    2 * H ≤ gap0 (z ++ w) ∧ 2 * H ≤ gap1 (z ++ w) ∧ 2 * H ≤ gap2 (z ++ w) := by
  match z with
  | [] => simp at hl
  | [_] => simp at hl
  | [_, _] => simp at hl
  | a :: b :: c :: z' =>
    rcases Nat.lt_or_ge z'.length 7 with hlt | hge
    · rcases z' with _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, q⟩⟩⟩⟩⟩⟩⟩
      · simp at hl
      · simp at hl
      · simp at hl
      · simp at hl
      · dsimp [gap0, gap1, gap2, digit_plane] at h0 h1 h2 ⊢; omega
      · dsimp [gap0, gap1, gap2, digit_plane] at h0 h1 h2 ⊢; omega
      · dsimp [gap0, gap1, gap2, digit_plane] at h0 h1 h2 ⊢; omega
      · simp at hlt; omega
    · rcases long_prefix H z' w hH hge h0 h1 h2 with ⟨ih0, ih1, ih2⟩
      exact triple_preserve (2 * H) a b c (z' ++ w) (by omega) ih0 ih1 ih2

lemma short_01_guard (H : Nat) (w v : List Bool) (e : Bool) (he : inc w = (v, e))
    (h0 : 4 * H + 2 ≤ gap0 w) (h1 : 4 * H + 2 ≤ gap1 w) (h2 : 4 * H + 2 ≤ gap2 w) :
    2 * H ≤ gap0 (false :: true :: v) ∧
    2 * H ≤ gap1 (false :: true :: v) ∧
    2 * H ≤ gap2 (false :: true :: v) := by
  have hh := inc_half w
  have hi := inc_interior w (by omega)
  have hv : (inc w).1 = v := congrArg Prod.fst he
  rw [hv] at hh hi
  have hf := gap2_four w
  have hp := gap_01 v
  omega

lemma zero_marker_bounds (k : Nat) (w : List Bool) (hl : 3 * k ≤ w.length)
    (hz : digit_plane bit_value 2 w = 0) :
    4 ^ k + 1 ≤ gap1 w ∧ 2 * 4 ^ k + 2 ≤ gap2 w := by
  induction k generalizing w with
  | zero =>
    have hb := gap_bounds w
    simp; omega
  | succ k ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl
    · simp at hl; omega
    · simp at hl; omega
    · have hc : c = false ∧ digit_plane bit_value 2 w = 0 := by
        cases c <;> dsimp [digit_plane, bit_value] at hz
        · exact ⟨rfl, by omega⟩
        · omega
      rcases hc with ⟨rfl, hzw⟩
      have hl' : 3 * k ≤ w.length := by simp at hl; omega
      rcases ih w hl' hzw with ⟨ih1, ih2⟩
      have ht := gap_triple a b false w
      dsimp [zero_bit] at ht
      rw [Nat.pow_succ]
      omega

lemma width_length (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p) :
    width w = 2 * k + p := by
  induction k generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩ <;> dsimp [width] <;> simp at hl <;> omega
  | succ k ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl; omega
    · simp at hl; omega
    · simp at hl; omega
    · dsimp [width]
      have hl' : w.length = 3 * k + p := by simp at hl; omega
      rw [ih w hl']
      omega

lemma digit_plane_zeros (n i : Nat) : digit_plane bit_value i (List.replicate n false) = 0 := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    cases i with
    | zero => dsimp [List.replicate_succ, digit_plane, bit_value]; rw [ih 2]
    | succ j => dsimp [List.replicate_succ, digit_plane]; exact ih j

lemma value_zeros (n : Nat) : value (List.replicate n false) = 0 := by
  dsimp [value]; rw [digit_plane_zeros, digit_plane_zeros]

lemma width_zeros (k p : Nat) (hp : p ≤ 2) :
    width (List.replicate (3 * k + p) false) = 2 * k + p :=
  width_length k p _ hp List.length_replicate

lemma gap0_zeros (k p : Nat) (hp : p ≤ 2) :
    gap0 (List.replicate (3 * k + p) false) = 2 ^ (2 * k + p) := by
  have h := value_gap0 (List.replicate (3 * k + p) false)
  rw [value_zeros, width_zeros k p hp, Nat.zero_add] at h
  exact h

lemma inc_marker_monotone (w : List Bool) :
    digit_plane bit_value 2 (inc w).1 ≤ digit_plane bit_value 2 w := by
  match w with
  | [] => dsimp [inc, digit_plane, bit_value]; omega
  | false :: u => dsimp [inc, digit_plane, bit_value]; omega
  | [true] => dsimp [inc, digit_plane, bit_value]; omega
  | true :: false :: u => dsimp [inc, digit_plane, bit_value]; omega
  | [true, true] => dsimp [inc, digit_plane, bit_value]; omega
  | true :: true :: c :: u =>
    have ih := inc_marker_monotone u
    cases c <;> dsimp [inc, digit_plane, bit_value] at ih ⊢ <;> omega

lemma inc_steps_marker_zero {q : Nat} {w v : List Bool} (hs : inc_steps q w v)
    (h2 : digit_plane bit_value 2 w = 0) :
    digit_plane bit_value 2 v = 0 := by
  induction hs with
  | zero => exact h2
  | succ _ w u _ hinc _ ih =>
    have hm := inc_marker_monotone w
    have hu : (inc w).1 = u := congrArg Prod.fst hinc
    rw [hu] at hm
    exact ih (by omega)

lemma inc_at_capacity (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p)
    (hg : gap0 w = 1) :
    inc w = if p = 0 then (List.replicate (3 * k + 1) false, false)
            else (List.replicate (3 * k + p) false, true) := by
  induction k generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · have hp0 : p = 0 := by simp at hl; omega
      subst hp0; rfl
    · have hp1 : p = 1 := by simp at hl; omega
      subst hp1
      cases a
      · dsimp [gap0, digit_plane, zero_bit] at hg; omega
      · rfl
    · have hp2 : p = 2 := by simp at hl; omega
      subst hp2
      cases a <;> cases b <;> dsimp [gap0, digit_plane, zero_bit] at hg
      · omega
      · omega
      · omega
      · rfl
    · simp at hl; omega
  | succ k ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl; omega
    · simp at hl; omega
    · simp at hl; omega
    · have hab : a = true ∧ b = true ∧ gap0 w = 1 := by
        cases a <;> cases b <;> dsimp [gap0, digit_plane, zero_bit] at hg ⊢
        · omega
        · omega
        · omega
        · exact ⟨rfl, rfl, by omega⟩
      rcases hab with ⟨rfl, rfl, hg'⟩
      have hl' : w.length = 3 * k + p := by simp at hl; omega
      have ihw := ih w hl' hg'
      dsimp [inc]
      rw [ihw]
      split_ifs with hp0
      · have hrep : List.replicate (3 * (k + 1) + 1) false =
            false :: false :: false :: List.replicate (3 * k + 1) false := by
          rw [show 3 * (k + 1) + 1 = 3 + (3 * k + 1) by omega, List.replicate_add]; rfl
        rw [hrep]
      · have hrep : List.replicate (3 * (k + 1) + p) false =
            false :: false :: false :: List.replicate (3 * k + p) false := by
          rw [show 3 * (k + 1) + p = 3 + (3 * k + p) by omega, List.replicate_add]; rfl
        rw [hrep]

lemma first_capacity (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p) :
    ∃ u, inc_steps (gap0 w - 1) w u ∧ u.length = w.length ∧ gap0 u = 1 ∧
      inc u = (if p = 0 then (List.replicate (3 * k + 1) false, false)
               else (List.replicate (3 * k + p) false, true)) := by
  have hb := (gap_bounds w).1
  rcases inc_steps_interior (gap0 w - 1) w (by omega) with ⟨u, hs, hlen, hgap⟩
  have hu : gap0 u = 1 := by omega
  exact ⟨u, hs, hlen, hu, inc_at_capacity k p u hp (by omega) hu⟩

lemma inc_steps_gaps (q : Nat) (w v : List Bool) (hs : inc_steps q w v) (hc : q < gap0 w) :
    gap0 v + q = gap0 w ∧ gap1 w ≤ 2 ^ q * gap1 v ∧ gap2 w ≤ 2 ^ q * gap2 v := by
  induction hs with
  | zero w => simp
  | succ q w u v hinc _ ih =>
    have hi := inc_interior w (by omega)
    have hh := inc_half w
    have hu : (inc w).1 = u := congrArg Prod.fst hinc
    rw [hu] at hi hh
    rcases ih (by omega) with ⟨g0, g1, g2⟩
    rw [Nat.pow_succ]
    refine ⟨by omega, by nlinarith, by nlinarith⟩

lemma small_carry_guard (H e c : Nat) (u v : List Bool)
    (hH : 1 ≤ H) (he : e ≤ 1) (hc : c ≤ 2 ^ e) (hs : inc_steps c u v)
    (h0 : (2 * H + 1) * 2 ^ e ≤ gap0 u)
    (h1 : (2 * H + 1) * 2 ^ e ≤ gap1 u)
    (h2 : (2 * H + 1) * 2 ^ e ≤ gap2 u) :
    H + 1 ≤ gap0 v ∧ H + 1 ≤ gap1 v ∧ H + 1 ≤ gap2 v := by
  have hp := pow2_pos e
  have hlt : c < gap0 u := by nlinarith
  rcases inc_steps_gaps c u v hs hlt with ⟨g0, g1, g2⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · simp at hc h0 h1 h2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp at g0 g1 g2 <;> omega
  · simp at hc h0 h1 h2
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl <;>
      simp at g0 g1 g2 <;> omega

lemma gap0_short (t : Nat) (w : List Bool) (hl : w.length ≤ 3 * t) : gap0 w ≤ 4 ^ t := by
  induction t generalizing w with
  | zero =>
    cases w with
    | nil => decide
    | cons _ _ => simp at hl
  | succ t ih =>
    have hp := pow4_pos t
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨marker, w⟩⟩⟩
    · change 1 ≤ 4 ^ (t + 1); rw [Nat.pow_succ]; omega
    · dsimp [gap0, digit_plane]; rw [Nat.pow_succ]; cases a <;> dsimp [zero_bit] <;> omega
    · dsimp [gap0, digit_plane]; rw [Nat.pow_succ]
      cases a <;> cases b <;> dsimp [zero_bit] <;> omega
    · have hl' : w.length ≤ 3 * t := by simp at hl; omega
      have ihw := ih w hl'
      have hu := (gap_triple_upper a b marker w).1
      rw [Nat.pow_succ]
      nlinarith

lemma preserve_bits (a : Nat) (b : Bool) (H : Nat) (w v : List Bool)
    (ha : 1 ≤ a) (hH : 1 ≤ H) (hb1 : a = 1 → b = true) (hb2 : a = 2 → b = false)
    (h0 : (2 * H + 1) * 2 ^ a ≤ gap0 w)
    (h1 : (2 * H + 1) * 2 ^ a ≤ gap1 w)
    (h2 : (2 * H + 1) * 2 ^ a ≤ gap2 w)
    (hs : inc_steps (2 ^ a - bit_value b) w v) :
    2 * H ≤ gap0 (List.replicate (2 * a - 1) false ++ b :: v) ∧
    2 * H ≤ gap1 (List.replicate (2 * a - 1) false ++ b :: v) ∧
    2 * H ≤ gap2 (List.replicate (2 * a - 1) false ++ b :: v) := by
  rcases Nat.eq_or_lt_of_le ha with rfl | ha2
  · have hb := hb1 rfl
    subst hb
    dsimp [bit_value] at hs
    cases hs with
    | succ _ _ mid _ hinc hlast =>
      cases hlast
      exact short_01_guard H w v false hinc (by omega) (by omega) (by omega)
  · set t := a / 2
    set e := a % 2
    have he : e ≤ 1 := by omega
    have hat : a = 2 * t + e := by omega
    have ht : 1 ≤ t := by omega
    have hp : 2 ^ a = 2 ^ e * 4 ^ t := by
      rw [hat, Nat.pow_add, pow_two_four, Nat.mul_comm]
    have hf := pow4_pos t
    have hep := pow2_pos e
    have hl : 3 * t ≤ w.length := by
      rcases Nat.lt_or_ge w.length (3 * t) with hlt | hge
      · have hshort := gap0_short t w (by omega)
        rw [hp, ← Nat.mul_assoc] at h0
        have hge2 : 3 ≤ (2 * H + 1) * 2 ^ e := by nlinarith
        nlinarith
      · exact hge
    set rho := w.take (3 * t)
    set u := w.drop (3 * t)
    have hw : w = rho ++ u := (List.take_append_drop (3 * t) w).symm
    have hlr : rho.length = 3 * t := by simp [rho, hl]
    rw [hw] at h0 h1 h2 hs
    rcases prefix_triples_upper t rho u hlr with ⟨hu0, hu1, hu2⟩
    have hg0 : (2 * H + 1) * 2 ^ e ≤ gap0 u := by rw [hp] at h0; nlinarith
    have hg1 : (2 * H + 1) * 2 ^ e ≤ gap1 u := by rw [hp] at h1; nlinarith
    have hg2 : (2 * H + 1) * 2 ^ e ≤ gap2 u := by rw [hp] at h2; nlinarith
    have hq : 2 ^ a - bit_value b ≤ 2 ^ e * 4 ^ t := by rw [hp]; omega
    rcases inc_steps_split_bounded t (2 ^ a - bit_value b) (2 ^ e) rho u v hlr hs hq with
      ⟨rho', u', c, hv, hlr', hc, hcb, _⟩
    rcases small_carry_guard H e c u u' hH he hcb hc hg0 hg1 hg2 with ⟨hg0', hg1', hg2'⟩
    rcases Nat.lt_or_ge H 4 with hh3 | hh4
    · rcases Nat.eq_or_lt_of_le (show 2 ≤ a by omega) with rfl | ha3
      · have hb := hb2 rfl
        subst hb
        have hz8 := zero4_eight v
        change 2 * H ≤ gap0 (false :: false :: false :: false :: v) ∧
          2 * H ≤ gap1 (false :: false :: false :: false :: v) ∧
          2 * H ≤ gap2 (false :: false :: false :: false :: v)
        omega
      · have hrep : List.replicate (2 * a - 1) false ++ b :: v =
            false :: false :: false :: false :: (List.replicate (2 * a - 5) false ++ b :: v) := by
          rw [show 2 * a - 1 = 4 + (2 * a - 5) by omega, List.replicate_add]
          rfl
        rw [hrep]
        have hz8 := zero4_eight (List.replicate (2 * a - 5) false ++ b :: v)
        omega
    · subst hv
      have hassoc : List.replicate (2 * a - 1) false ++ b :: (rho' ++ u') =
          (List.replicate (2 * a - 1) false ++ b :: rho') ++ u' := by
        simp [List.append_assoc]
      rw [hassoc]
      refine long_prefix H (List.replicate (2 * a - 1) false ++ b :: rho') u' hh4 ?_ hg0' hg1' hg2'
      simp [hlr']
      omega

def last_bit (n : Nat) : Bool := !((1 + n) % 3 == 2)

lemma preserve (a : Nat) (b : Bool) (H : Nat) (w v : List Bool)
    (ha : 1 ≤ a) (hH : 1 ≤ H) (hb : b = !((a % 3) == 2))
    (h0 : (2 * H + 1) * 2 ^ a ≤ gap0 w)
    (h1 : (2 * H + 1) * 2 ^ a ≤ gap1 w)
    (h2 : (2 * H + 1) * 2 ^ a ≤ gap2 w)
    (hs : inc_steps (2 ^ a - bit_value b) w v) :
    2 * H ≤ gap0 (List.replicate (2 * a - 1) false ++ b :: v) ∧
    2 * H ≤ gap1 (List.replicate (2 * a - 1) false ++ b :: v) ∧
    2 * H ≤ gap2 (List.replicate (2 * a - 1) false ++ b :: v) := by
  refine preserve_bits a b H w v ha hH ?_ ?_ h0 h1 h2 hs
  · rintro rfl; exact hb
  · rintro rfl; exact hb

lemma ones_triples (t : Nat) (w : List Bool) :
    gap0 (List.replicate (3 * t) true ++ w) + 4 ^ t = 4 ^ t * gap0 w + 1 ∧
    gap1 (List.replicate (3 * t) true ++ w) + 2 * 4 ^ t = 4 ^ t * gap1 w + 2 ∧
    gap2 (List.replicate (3 * t) true ++ w) + 4 * 4 ^ t = 4 ^ t * gap2 w + 4 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hrep : List.replicate (3 * (t + 1)) true ++ w =
        true :: true :: true :: (List.replicate (3 * t) true ++ w) := by
      rw [show 3 * (t + 1) = 3 + 3 * t by omega, List.replicate_add]
      rfl
    rw [hrep]
    have hg := gap_triple true true true (List.replicate (3 * t) true ++ w)
    dsimp [zero_bit] at hg
    rw [Nat.pow_succ]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma zero_word (w : List Bool) (hv : value w = 0) (hm : digit_plane bit_value 2 w = 0) :
    w = List.replicate w.length false := by
  match w with
  | [] => rfl
  | [a] =>
    cases a
    · rfl
    · dsimp [value, digit_plane, bit_value] at hv; omega
  | [a, b] =>
    cases a <;> cases b <;> dsimp [value, digit_plane, bit_value] at hv <;> try omega
    rfl
  | a :: b :: c :: u =>
    have habc : a = false ∧ b = false ∧ c = false ∧ value u = 0 ∧ digit_plane bit_value 2 u = 0 := by
      cases a <;> cases b <;> cases c <;> dsimp [value, digit_plane, bit_value] at hv hm ⊢ <;> try omega
      exact ⟨rfl, rfl, rfl, by omega, by omega⟩
    rcases habc with ⟨rfl, rfl, rfl, hvu, hmu⟩
    have ih := zero_word u hvu hmu
    dsimp [List.length]
    rw [show u.length + 1 + 1 + 1 = 3 + u.length by omega, List.replicate_add, ← ih]
    rfl

lemma zero_entry (k p : Nat) (hp : p = 1 ∨ p = 2) :
    4 * 4 ^ k ≤ gap0 (false :: List.replicate (3 * k + p) false) ∧
    4 * 4 ^ k ≤ gap1 (false :: List.replicate (3 * k + p) false) ∧
    4 * 4 ^ k ≤ gap2 (false :: List.replicate (3 * k + p) false) := by
  induction k with
  | zero =>
    rcases hp with rfl | rfl <;> decide
  | succ k ih =>
    have hrep : false :: List.replicate (3 * (k + 1) + p) false =
        false :: false :: false :: (false :: List.replicate (3 * k + p) false) := by
      rw [show 3 * (k + 1) + p = 3 + (3 * k + p) by omega, List.replicate_add]
      rfl
    rw [hrep]
    have hg := gap_triple false false false (false :: List.replicate (3 * k + p) false)
    dsimp [zero_bit] at hg
    rw [Nat.pow_succ]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma prefix_residue_0 (t : Nat) (E : List Bool) :
    let W := List.replicate (3 * t) true ++ false :: E
    gap0 W + 4 ^ t = 4 ^ t * gap1 E + 1 ∧
    gap1 W + 2 * 4 ^ t = 4 ^ t * gap2 E + 2 ∧
    gap2 W + 4 * 4 ^ t = 4 * 4 ^ t * gap0 E + 4 := by
  dsimp only
  rcases ones_triples t (false :: E) with ⟨ht0, ht1, ht2⟩
  rcases gap_cons false E with ⟨h0a, h0b, h0c⟩
  dsimp [zero_bit] at h0a h0b h0c
  have e0 : gap0 (false :: E) = gap1 E := by omega
  have e1 : gap1 (false :: E) = gap2 E := by omega
  have e2 : gap2 (false :: E) = 4 * gap0 E := by omega
  rw [e0] at ht0
  rw [e1] at ht1
  rw [e2] at ht2
  refine ⟨ht0, ht1, by linarith⟩

lemma prefix_residue_1 (t : Nat) (E : List Bool) :
    let W := List.replicate (3 * t + 1) true ++ false :: E
    gap0 W + 2 * 4 ^ t = 4 ^ t * gap2 E + 1 ∧
    gap1 W + 4 * 4 ^ t = 4 * 4 ^ t * gap0 E + 2 ∧
    gap2 W + 4 * 4 ^ t = 4 * 4 ^ t * gap1 E + 4 := by
  dsimp only
  have hrep : List.replicate (3 * t + 1) true ++ false :: E =
      List.replicate (3 * t) true ++ (true :: false :: E) := by
    rw [List.replicate_add, List.append_assoc]; rfl
  rw [hrep]
  rcases ones_triples t (true :: false :: E) with ⟨ht0, ht1, ht2⟩
  rcases gap_cons false E with ⟨h0a, h0b, h0c⟩
  rcases gap_cons true (false :: E) with ⟨h1a, h1b, h1c⟩
  dsimp [zero_bit] at h0a h0b h0c h1a h1b h1c
  have e0 : gap2 E = gap0 (true :: false :: E) + 1 := by omega
  have e1 : 4 * gap0 E = gap1 (true :: false :: E) + 2 := by omega
  have e2 : gap2 (true :: false :: E) = 4 * gap1 E := by omega
  refine ⟨by rw [e0]; linarith,
    by rw [show 4 * 4 ^ t * gap0 E = 4 ^ t * (4 * gap0 E) by ring, e1]; linarith,
    by rw [e2] at ht2; linarith⟩

lemma prefix_residue_2 (t : Nat) (E : List Bool) :
    let W := List.replicate (3 * t + 2) true ++ false :: E
    gap0 W + 4 * 4 ^ t = 4 * 4 ^ t * gap0 E + 1 ∧
    gap1 W + 4 * 4 ^ t = 4 * 4 ^ t * gap1 E + 2 ∧
    gap2 W + 8 * 4 ^ t = 4 * 4 ^ t * gap2 E + 4 := by
  dsimp only
  have hrep : List.replicate (3 * t + 2) true ++ false :: E =
      List.replicate (3 * t) true ++ (true :: true :: false :: E) := by
    rw [List.replicate_add, List.append_assoc]; rfl
  rw [hrep]
  rcases ones_triples t (true :: true :: false :: E) with ⟨ht0, ht1, ht2⟩
  rcases gap_cons false E with ⟨h0a, h0b, h0c⟩
  rcases gap_cons true (false :: E) with ⟨h1a, h1b, h1c⟩
  rcases gap_cons true (true :: false :: E) with ⟨h2a, h2b, h2c⟩
  dsimp [zero_bit] at h0a h0b h0c h1a h1b h1c h2a h2b h2c
  have e0 : 4 * gap0 E = gap0 (true :: true :: false :: E) + 3 := by omega
  have e1 : 4 * gap1 E = gap1 (true :: true :: false :: E) + 2 := by omega
  have e2 : 4 * gap2 E = gap2 (true :: true :: false :: E) + 4 := by omega
  refine ⟨by rw [show 4 * 4 ^ t * gap0 E = 4 ^ t * (4 * gap0 E) by ring, e0]; linarith,
    by rw [show 4 * 4 ^ t * gap1 E = 4 ^ t * (4 * gap1 E) by ring, e1]; linarith,
    by rw [show 4 * 4 ^ t * gap2 E = 4 ^ t * (4 * gap2 E) by ring, e2]; linarith⟩

lemma strong (k p z : Nat) (E : List Bool)
    (hp : p = 1 ∨ p = 2) (hl : E.length = 3 * k + p)
    (hm : digit_plane bit_value 2 E = 0) (hv : value E = 2 ^ (z + 1) - 2) (hz : z < 2 * k + p) :
    2 ^ (2 * k + 2 - z) ≤ gap0 (List.replicate (2 * z) true ++ false :: E) ∧
    2 ^ (2 * k + 2 - z) ≤ gap1 (List.replicate (2 * z) true ++ false :: E) ∧
    2 ^ (2 * k + 2 - z) ≤ gap2 (List.replicate (2 * z) true ++ false :: E) := by
  rcases Nat.eq_zero_or_pos z with rfl | hzp
  · have ev : value E = 0 := by rw [hv]; rfl
    have hew := zero_word E ev hm
    rw [hl] at hew
    rw [hew]
    simp only [Nat.mul_zero, List.replicate_zero, List.nil_append, Nat.sub_zero]
    have hpow : 2 ^ (2 * k + 2) = 4 * 4 ^ k := by
      rw [Nat.pow_add, pow_two_four]; ring
    rw [hpow]
    exact zero_entry k p hp
  · have cpos := pow4_pos k
    have pz0 := pow2_pos z
    have pz : 2 ≤ 2 ^ (z + 1) := by rw [Nat.pow_succ]; omega
    have pc : 2 ^ (2 * k + p) = 2 ^ p * 4 ^ k := by
      rw [Nat.pow_add, pow_two_four, Nat.mul_comm]
    have hg := value_gap0 E
    rw [width_length k p E (by omega) hl, hv] at hg
    have hgexact : gap0 E + 2 ^ (z + 1) = 2 ^ p * 4 ^ k + 2 := by rw [pc] at hg; omega
    rcases zero_marker_bounds k E (by omega) hm with ⟨hg1, hg2⟩
    have hb : 2 ^ (2 * k + 2 - z) ≤ 2 * 4 ^ k := by
      have h1 : 2 * 4 ^ k = 2 ^ (2 * k + 1) := by
        rw [Nat.pow_succ, pow_two_four]; ring
      rw [h1]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hg0 : 4 ^ k + 2 ≤ gap0 E ∨ (2 ≤ gap0 E ∧ 2 ^ (2 * k + 2 - z) ≤ 4) := by
      rcases Nat.eq_or_lt_of_le (show z + 1 ≤ 2 * k + p by omega) with he | hlt
      · right
        refine ⟨?_, ?_⟩
        · rw [he, pc] at hgexact; omega
        · rw [show 2 * k + 2 - z = 3 - p by omega]
          rcases hp with rfl | rfl <;> decide
      · left
        have hpower : 2 * 2 ^ (z + 1) ≤ 2 ^ (2 * k + p) := by
          have h2 : 2 * 2 ^ (z + 1) = 2 ^ (z + 2) := by rw [Nat.pow_succ (2 : Nat) (z + 1)]; ring
          rw [h2]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        rw [pc] at hpower
        rcases hp with rfl | rfl <;> simp at hgexact hpower <;> omega
    obtain ⟨t, r, hr, hzr, kbig⟩ :
        ∃ t r, (r = 0 ∨ r = 1 ∨ r = 2) ∧ 2 * z = 3 * t + r ∧ (r ≤ 1 → 4 ≤ 4 ^ t) := by
      refine ⟨(2 * z) / 3, (2 * z) % 3, by omega, by omega, ?_⟩
      intro hrl
      have ht1 : 1 ≤ (2 * z) / 3 := by omega
      have h41 : (4 : Nat) = 4 ^ 1 := rfl
      rw [h41]
      exact Nat.pow_le_pow_right (by omega) ht1
    have kpos : 1 ≤ 4 ^ t := pow4_pos t
    have pk1 : 4 ^ k ≤ 4 ^ t * 4 ^ k := by
      have := Nat.mul_le_mul_right (4 ^ k) kpos; linarith
    have p1 : 4 ^ t * 4 ^ k + 4 ^ t ≤ 4 ^ t * gap1 E := by
      have := Nat.mul_le_mul_left (4 ^ t) hg1; linarith
    have p2 : 2 * (4 ^ t * 4 ^ k) + 2 * 4 ^ t ≤ 4 ^ t * gap2 E := by
      have := Nat.mul_le_mul_left (4 ^ t) hg2; linarith
    rcases hr with rfl | rfl | rfl
    · have hzr0 : 2 * z = 3 * t := by omega
      rw [hzr0]
      rcases prefix_residue_0 t E with ⟨hf0, hf1, hf2⟩
      have kb := kbig (by omega)
      have pk4 : 4 * 4 ^ k ≤ 4 ^ t * 4 ^ k := Nat.mul_le_mul_right (4 ^ k) kb
      rcases hg0 with hg0 | ⟨hg0, hb4⟩
      · have p0 : 4 ^ t * 4 ^ k + 2 * 4 ^ t ≤ 4 ^ t * gap0 E := by
          have := Nat.mul_le_mul_left (4 ^ t) hg0; linarith
        refine ⟨by linarith, by linarith, by linarith⟩
      · have p0 : 2 * 4 ^ t ≤ 4 ^ t * gap0 E := by
          have := Nat.mul_le_mul_left (4 ^ t) hg0; linarith
        refine ⟨by linarith, by linarith, by linarith⟩
    · rw [hzr]
      rcases prefix_residue_1 t E with ⟨hf0, hf1, hf2⟩
      have kb := kbig (by omega)
      have pk4 : 4 * 4 ^ k ≤ 4 ^ t * 4 ^ k := Nat.mul_le_mul_right (4 ^ k) kb
      rcases hg0 with hg0 | ⟨hg0, hb4⟩
      · have p0 : 4 ^ t * 4 ^ k + 2 * 4 ^ t ≤ 4 ^ t * gap0 E := by
          have := Nat.mul_le_mul_left (4 ^ t) hg0; linarith
        refine ⟨by linarith, by linarith, by linarith⟩
      · have p0 : 2 * 4 ^ t ≤ 4 ^ t * gap0 E := by
          have := Nat.mul_le_mul_left (4 ^ t) hg0; linarith
        refine ⟨by linarith, by linarith, by linarith⟩
    · rw [hzr]
      rcases prefix_residue_2 t E with ⟨hf0, hf1, hf2⟩
      rcases hg0 with hg0 | ⟨hg0, hb4⟩
      · have p0 : 4 ^ t * 4 ^ k + 2 * 4 ^ t ≤ 4 ^ t * gap0 E := by
          have := Nat.mul_le_mul_left (4 ^ t) hg0; linarith
        refine ⟨by linarith, by linarith, by linarith⟩
      · have p0 : 2 * 4 ^ t ≤ 4 ^ t * gap0 E := by
          have := Nat.mul_le_mul_left (4 ^ t) hg0; linarith
        refine ⟨by linarith, by linarith, by linarith⟩

lemma actual (k p z : Nat) (E : List Bool) (H : Nat)
    (hp : p = 1 ∨ p = 2) (hl : E.length = 3 * k + p)
    (hm : digit_plane bit_value 2 E = 0) (hv : value E = 2 ^ (z + 1) - 2) (hz : z < 2 * k + p)
    (ht : 2 ^ z * (1 + 2 * H) ≤ (if p = 1 then 3 else 4) * 4 ^ k) :
    2 * H < gap0 (List.replicate (2 * z) true ++ false :: E) ∧
    2 * H < gap1 (List.replicate (2 * z) true ++ false :: E) ∧
    2 * H < gap2 (List.replicate (2 * z) true ++ false :: E) := by
  rcases strong k p z E hp hl hm hv hz with ⟨hg0, hg1, hg2⟩
  have hb : 2 ^ (2 * k + 2 - z) * 2 ^ z = 4 * 4 ^ k := by
    rw [← Nat.pow_add, show 2 * k + 2 - z + z = 2 * k + 2 by omega, Nat.pow_add, pow_two_four]
    ring
  have pz := pow2_pos z
  rcases hp with rfl | rfl <;> simp at ht <;> refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

-- ============================================================================
-- Section 5: Pair12Right, PairShift, PairRegion, Pair12Entry, PairOrdinary,
--            PairExceptional, PairPostEntry, Pair12Closure & Non-Halting
-- ============================================================================

lemma right_step {w v : List Bool} {e : Bool} {n : Nat} {r : ListBlank (Fin 2)}
    (he : inc w = (v, e)) (hr : RC rd1 n r) :
    ∃ s, RC rd1 (n + 1) s ∧ (Conf w r) [target_tm]⊢⁺ (Conf v (insert e s)) := by
  rcases RC_carry hr with ⟨k, s, rfl, hs⟩
  refine ⟨rd0 ^ k +> (rd1 +> s), hs, ?_⟩
  have h := RZero w ([0, 0, 0] +> s) k
  rw [he] at h
  exact h

lemma finite_step {w v : List Bool} {n : Nat} {r tail : ListBlank (Fin 2)} {k : Nat}
    (he : inc w = (v, false)) (hr : FC rd1 tail k n r) (hb : n + 1 < 2 ^ k) :
    ∃ s, FC rd1 tail k (n + 1) s ∧ (Conf w r) [target_tm]⊢⁺ (Conf v s) := by
  rcases FC_carry hr hb with ⟨j, s, _, rfl, hs⟩
  refine ⟨rd0 ^ j +> (rd1 +> s), hs, ?_⟩
  have h := RZero w ([0, 0, 0] +> s) j
  rw [he] at h
  exact h

lemma right_steps {q : Nat} {w v : List Bool} {n : Nat} {r : ListBlank (Fin 2)}
    (hs : inc_steps q w v) (hr : RC rd1 n r) :
    ∃ s, RC rd1 (n + q) s ∧ (Conf w r) [target_tm]⊢* (Conf v s) := by
  induction hs generalizing n r with
  | zero w =>
    exact ⟨r, RC_eq hr (by omega) rfl, stepStar_refl _⟩
  | succ q w u v hinc _ ih =>
    rcases right_step hinc hr with ⟨s, hs1, hS1⟩
    rcases ih hs1 with ⟨s', hs2, hS2⟩
    exact ⟨s', RC_eq hs2 (by omega) rfl, stepStar_trans (stepPlus_to_stepStar hS1) hS2⟩

lemma finite_steps {q : Nat} {w v : List Bool} {n : Nat} {r tail : ListBlank (Fin 2)} {k : Nat}
    (hs : inc_steps q w v) (hr : FC rd1 tail k n r) (hb : n + q < 2 ^ k) :
    ∃ s, FC rd1 tail k (n + q) s ∧ (Conf w r) [target_tm]⊢* (Conf v s) := by
  induction hs generalizing n r with
  | zero w =>
    exact ⟨r, FC_eq hr rfl (by omega) rfl, stepStar_refl _⟩
  | succ q w u v hinc _ ih =>
    rcases finite_step hinc hr (by omega) with ⟨s, hs1, hS1⟩
    rcases ih hs1 (by omega) with ⟨s', hs2, hS2⟩
    exact ⟨s', FC_eq hs2 rfl (by omega) rfl, stepStar_trans (stepPlus_to_stepStar hS1) hS2⟩

def output (n : Nat) (b : Bool) (v : List Bool) : List Bool :=
  push0 (2 * n + 1) (b :: v)

lemma shifted_prefix (n : Nat) {w v : List Bool} (r : ListBlank (Fin 2))
    (h : inc_steps (2 ^ (1 + n) - 1) w v) :
    (Conf w (rd0 ^ n +> (rds +> r))) [target_tm]⊢⁺
    (Conf v (rd1 ^ n +> ([1, 0, 0, 1] +> r))) := by
  have hp := pow2_pos n
  have hsplit : 2 ^ (1 + n) - 1 = (2 ^ n - 1) + (1 + (2 ^ n - 1)) := by
    rw [Nat.add_comm 1 n, Nat.pow_succ]; omega
  rw [hsplit] at h
  rcases inc_steps_add_inv h with ⟨u, hwu, huv⟩
  rw [Nat.add_comm 1 (2 ^ n - 1)] at huv
  cases huv with
  | succ _ _ u1 _ hinc hu1v =>
    rcases finite_steps hwu (FC_zero rd1 (rds +> r) n) (by omega) with ⟨s1, hs1, hS1⟩
    have hs1_eq : s1 = rd1 ^ n +> (rds +> r) := FC_full_unique (FC_eq hs1 rfl (by omega) rfl)
    subst hs1_eq
    rcases finite_steps hu1v (FC_zero rd1 ([1, 0, 0, 1] +> r) n) (by omega) with ⟨s2, hs2, hS2⟩
    have hs2_eq : s2 = rd1 ^ n +> ([1, 0, 0, 1] +> r) := FC_full_unique (FC_eq hs2 rfl (by omega) rfl)
    subst hs2_eq
    have hm := RZero u ([0, 0, 1] +> r) n
    rw [hinc] at hm
    have heq1 : rd1 ^ n +> (rds +> r) = rd1 ^ n +> ([0] +> ([0, 0, 1] +> r)) := rfl
    have heq2 : insert false (rd0 ^ n +> ([1] +> ([0, 0, 1] +> r))) =
        rd0 ^ n +> ([1, 0, 0, 1] +> r) := rfl
    rw [heq1] at hS1
    rw [heq2] at hm
    exact stepStar_stepPlus_trans hS1 (stepPlus_stepStar_trans hm hS2)

lemma finish_signal (n : Nat) (w v : List Bool) (r : ListBlank (Fin 2))
    (h : if last_bit n then w = v else inc w = (v, false)) :
    (Conf w (rd1 ^ n +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    (Conf (output n (last_bit n) v) r) := by
  set q := n / 3
  set rem := n % 3
  have hdiv : n = q * 3 + rem := by omega
  have hrem : rem = 0 ∨ rem = 1 ∨ rem = 2 := by omega
  rcases hrem with hrem0 | hrem1 | hrem2
  · have hlb : last_bit n = true := by
      dsimp [last_bit]
      have : (1 + n) % 3 = 1 := by omega
      rw [this]; rfl
    rw [hlb] at h ⊢
    simp at h
    subst h
    have hs := R1001_mod0 (data w) r q
    have hn_eq : n = q * 3 := by omega
    rw [hn_eq]
    have hconf : Conf (output (q * 3) true w) r =
        ((data w <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ (q * 6 + 2)) {{C}}> r) := by
      dsimp [output]
      rw [Conf_push0, show 2 * (q * 3) + 1 + 1 = q * 6 + 2 by omega]
      rfl
    rw [hconf]
    exact hs
  · have hlb : last_bit n = false := by
      dsimp [last_bit]
      have : (1 + n) % 3 = 2 := by omega
      rw [this]; rfl
    rw [hlb] at h ⊢
    simp at h
    have hs := R1001_return w r q
    have hn_eq : n = q * 3 + 1 := by omega
    rw [h] at hs
    rw [hn_eq]
    dsimp [output, insert] at hs ⊢
    rw [push0_cons, show 2 * (q * 3 + 1) + 1 + 1 = q * 6 + 4 by omega]
    exact hs
  · have hlb : last_bit n = true := by
      dsimp [last_bit]
      have : (1 + n) % 3 = 0 := by omega
      rw [this]; rfl
    rw [hlb] at h ⊢
    simp at h
    subst h
    have hs := R1001_mod2 (data w) r q
    have hn_eq : n = q * 3 + 2 := by omega
    rw [hn_eq]
    have hconf : Conf (output (q * 3 + 2) true w) r =
        ((data w <+ [1, 1] <+ ([0, 1] : List (Fin 2)) ^ (q * 6 + 6)) {{C}}> r) := by
      dsimp [output]
      rw [Conf_push0, show 2 * (q * 3 + 2) + 1 + 1 = q * 6 + 6 by omega]
      rfl
    rw [hconf]
    exact hs

lemma shifted (n : Nat) {w v : List Bool} (r : ListBlank (Fin 2))
    (h : inc_steps (2 ^ (1 + n) - bit_value (last_bit n)) w v) :
    (Conf w (rd0 ^ n +> (rds +> r))) [target_tm]⊢⁺
    (Conf (output n (last_bit n) v) r) := by
  cases hlb : last_bit n with
  | true =>
    rw [hlb] at h
    dsimp [bit_value] at h
    refine stepPlus_trans (shifted_prefix n r h) ?_
    have hf := finish_signal n v v r
    rw [hlb] at hf
    exact hf (by simp)
  | false =>
    rw [hlb] at h
    dsimp [bit_value] at h
    have hp := pow2_pos (1 + n)
    have hsplit : 2 ^ (1 + n) = (2 ^ (1 + n) - 1) + 1 := by omega
    rw [hsplit] at h
    rcases inc_steps_add_inv h with ⟨u, hwu, huv⟩
    cases huv with
    | succ _ _ mid _ hinc hlast =>
      cases hlast
      refine stepPlus_trans (shifted_prefix n r hwu) ?_
      have hf := finish_signal n u v r
      rw [hlb] at hf
      exact hf (by simp [hinc])

inductive Allowed : Cfg (Fin 2) (Fin 6) → Prop
  | Blank (w : List Bool) : Allowed (Conf w default)
  | One (w : List Bool) : w ≠ [] → value w % 2 = 0 → Allowed (Conf w ([1] +> default))
  | Shifted (w : List Bool) (n : Nat) (r : ListBlank (Fin 2)) :
      0 < n → RC rds n r → guard n w → Allowed (Conf w r)

lemma zero_prefix_even (n : Nat) (w : List Bool) (hn : 1 ≤ n) :
    value (push0 n w) % 2 = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    dsimp [push0, List.replicate_succ, value, digit_plane, bit_value]
    omega

lemma push0_ne_nil (n : Nat) (w : List Bool) (hn : 1 ≤ n) :
    push0 n w ≠ [] := by
  cases n with
  | zero => omega
  | succ m => simp [push0, List.replicate_succ]

lemma one_allowed (n : Nat) (w : List Bool) (hn : 1 ≤ n) :
    Allowed (Conf (push0 n w) ([1] +> default)) :=
  Allowed.One (push0 n w) (push0_ne_nil n w hn) (zero_prefix_even n w hn)

lemma last_bit_false (n : Nat) (h : last_bit n = false) : n % 3 = 1 := by
  dsimp [last_bit] at h
  have hmod : (1 + n) % 3 = 0 ∨ (1 + n) % 3 = 1 ∨ (1 + n) % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · rw [h0] at h; contradiction
  · rw [h1] at h; contradiction
  · omega

lemma last_signal (n : Nat) (w : List Bool) :
    ∃ c', Allowed c' ∧ (Conf w (rd1 ^ n +> ([1, 0, 0, 1] +> default))) [target_tm]⊢⁺ c' := by
  cases hlb : last_bit n with
  | true =>
    refine ⟨Conf (output n (last_bit n) w) default, Allowed.Blank _, ?_⟩
    exact finish_signal n w w default (by simp [hlb])
  | false =>
    have hn3 := last_bit_false n hlb
    have hn_eq : n = (n / 3) * 3 + 1 := by omega
    have hs := R1001_return w default (n / 3)
    rw [← hn_eq] at hs
    cases h2 : (inc w).2 with
    | false =>
      rw [h2, insert_false] at hs
      exact ⟨Conf (push0 (n / 3 * 6 + 4) (inc w).1) default, Allowed.Blank _, hs⟩
    | true =>
      rw [h2, insert_true] at hs
      exact ⟨Conf (push0 (n / 3 * 6 + 4) (inc w).1) ([1] +> default),
        one_allowed (n / 3 * 6 + 4) (inc w).1 (by omega), hs⟩

lemma last_shift (n : Nat) (w : List Bool) (hg : 2 ^ (1 + n) ≤ gap0 w) :
    ∃ c', Allowed c' ∧ (Conf w (rd0 ^ n +> (rds +> default))) [target_tm]⊢⁺ c' := by
  have hp := pow2_pos (1 + n)
  rcases inc_steps_interior (2 ^ (1 + n) - 1) w (by omega) with ⟨v, hv, _⟩
  rcases last_signal n v with ⟨c', hA, hS⟩
  exact ⟨c', hA, stepPlus_trans (shifted_prefix n default hv) hS⟩

lemma bit_value_le_one (b : Bool) : bit_value b ≤ 1 := by
  cases b <;> decide

lemma shifted_step (n : Nat) (w : List Bool) (r : ListBlank (Fin 2))
    (hn : 0 < n) (hr : RC rds n r) (hg : guard n w) :
    ∃ c', Allowed c' ∧ (Conf w r) [target_tm]⊢⁺ c' := by
  rcases hg with ⟨h0, h1, h2⟩
  rcases RC_positive_split hr hn with ⟨t, q, s, rfl, hs, hen, _⟩
  cases q with
  | zero =>
    rw [RC_zero_unique hs]
    refine last_shift t w ?_
    rw [Nat.add_comm 1 t, Nat.pow_succ]
    omega
  | succ q =>
    set b := last_bit t
    have hb := bit_value_le_one b
    have hp := pow2_pos (1 + t)
    have hpow : 2 ^ (1 + t) = 2 * 2 ^ t := by rw [Nat.add_comm 1 t, Nat.pow_succ]; ring
    have hmul : 2 * n = (2 * (q + 1) + 1) * 2 ^ (1 + t) := by
      rw [hen, hpow]; ring
    rw [hmul] at h0 h1 h2
    have h3 : 3 * 2 ^ (1 + t) ≤ (2 * (q + 1) + 1) * 2 ^ (1 + t) :=
      Nat.mul_le_mul_right (2 ^ (1 + t)) (by omega)
    have hq : 2 ^ (1 + t) - bit_value b < gap0 w := by
      omega
    rcases inc_steps_interior (2 ^ (1 + t) - bit_value b) w hq with ⟨v, hv, _⟩
    have hg_next : guard (q + 1) (output t b v) := by
      dsimp [guard, output, push0]
      rw [show 2 * t + 1 = 2 * (1 + t) - 1 by omega]
      exact preserve (1 + t) b (q + 1) w v (by omega) (by omega) rfl h0 h1 h2 hv
    exact ⟨Conf (output t b v) s, Allowed.Shifted _ (q + 1) s (by omega) hs hg_next,
      shifted t s hv⟩

lemma one_cross (z : Nat) {w v : List Bool} (r : ListBlank (Fin 2))
    (hz : 1 ≤ z) (h : inc_steps (2 ^ z - 1) w v) :
    (Conf w ([1] +> (rd0 ^ z +> (rd1 +> r)))) [target_tm]⊢⁺
    (Conf v (rd0 ^ z +> ([1, 1, 0, 0, 0] +> r))) := by
  cases z with
  | zero => omega
  | succ t =>
    have hp0 := pow2_pos t
    have hp : 2 ≤ 2 ^ (t + 1) := by rw [Nat.pow_succ]; omega
    have hsplit : 2 ^ (t + 1) - 1 = (2 ^ (t + 1) - 2) + 1 := by omega
    rw [hsplit] at h
    rcases inc_steps_add_inv h with ⟨u, hw, hu⟩
    cases hu with
    | succ _ _ mid _ hinc hlast =>
      cases hlast
      rcases finite_steps hw (FC_leading_one t r) (by omega) with ⟨s, hs, hS⟩
      have hs_eq : s = rd1 ^ (t + 1) +> ([0] +> (rd1 +> r)) :=
        FC_full_unique (FC_eq hs rfl (by omega) rfl)
      subst hs_eq
      have hc := RZero u (rd1 +> r) (t + 1)
      rw [hinc] at hc
      exact stepStar_stepPlus_trans hS hc

lemma prefix_steps (z : Nat) {w v : List Bool} (r : ListBlank (Fin 2))
    (h : inc_steps (2 ^ (z + 1) - 2) w v) :
    (Conf w ([1] +> (rd0 ^ z +> (rd1 +> r)))) [target_tm]⊢*
    (Conf v (rd1 ^ z +> ([1, 1, 0, 0, 0] +> r))) := by
  cases z with
  | zero =>
    cases h
    exact stepStar_refl _
  | succ t =>
    have hp0 := pow2_pos (t + 1)
    have hsplit : 2 ^ (t + 1 + 1) - 2 = (2 ^ (t + 1) - 1) + (2 ^ (t + 1) - 1) := by
      rw [Nat.pow_succ]; omega
    rw [hsplit] at h
    rcases inc_steps_add_inv h with ⟨u, hw, hv⟩
    rcases finite_steps hv (FC_zero rd1 ([1, 1, 0, 0, 0] +> r) (t + 1)) (by omega) with ⟨s, hs, hS⟩
    have hs_eq : s = rd1 ^ (t + 1) +> ([1, 1, 0, 0, 0] +> r) :=
      FC_full_unique (FC_eq hs rfl (by omega) rfl)
    subst hs_eq
    exact stepStar_trans (stepPlus_to_stepStar (one_cross (t + 1) r (by omega) hw)) hS

lemma eleven_word (z : Nat) (w : List Bool) (r : ListBlank (Fin 2)) :
    (Conf w (rd1 ^ z +> ([1, 1] +> r))) [target_tm]⊢⁺
    (Conf (List.replicate (2 * z) true ++ false :: w) r) := by
  have h := REleven (data w) r z
  have hdata : data (List.replicate (2 * z) true ++ false :: w) =
      data w <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (z * 2) := by
    rw [data_ones, Nat.mul_comm 2 z]; rfl
  simpa [Conf, hdata] using h

lemma ordinary (z : Nat) {w v : List Bool} (r : ListBlank (Fin 2))
    (h : inc_steps (2 ^ (z + 1) - 2) w v) :
    (Conf w ([1] +> (rd0 ^ z +> (rd1 +> r)))) [target_tm]⊢⁺
    (Conf (List.replicate (2 * z) true ++ false :: v) ([0, 0, 0] +> r)) :=
  stepStar_stepPlus_trans (prefix_steps z r h) (eleven_word z v ([0, 0, 0] +> r))

lemma eleven0 (w : List Bool) (r : ListBlank (Fin 2)) :
    (Conf w ([1, 1] +> r)) [target_tm]⊢⁺ (Conf (push0 1 w) r) :=
  eleven_word 0 w r

lemma last_signal_one (n : Nat) (w : List Bool) :
    ∃ c', Allowed c' ∧ (Conf w (rd1 ^ n +> ([1, 0, 0, 1] +> ([1] +> default)))) [target_tm]⊢⁺ c' := by
  cases hlb : last_bit n with
  | true =>
    refine ⟨Conf (output n (last_bit n) w) ([1] +> default), ?_, ?_⟩
    · dsimp [output]
      exact one_allowed (2 * n + 1) (last_bit n :: w) (by omega)
    · exact finish_signal n w w ([1] +> default) (by simp [hlb])
  | false =>
    have hn3 := last_bit_false n hlb
    have hn_eq : n = (n / 3) * 3 + 1 := by omega
    have hs := R1001_return w ([1] +> default) (n / 3)
    rw [← hn_eq] at hs
    cases h2 : (inc w).2 with
    | false =>
      rw [h2, insert_false] at hs
      exact ⟨Conf (push0 (n / 3 * 6 + 4) (inc w).1) ([1] +> default),
        one_allowed (n / 3 * 6 + 4) (inc w).1 (by omega), hs⟩
    | true =>
      rw [h2, insert_true] at hs
      exact ⟨Conf (push0 1 (push0 (n / 3 * 6 + 4) (inc w).1)) default,
        Allowed.Blank _, stepPlus_trans hs (eleven0 (push0 (n / 3 * 6 + 4) (inc w).1) default)⟩

lemma last_shift_one (n : Nat) (w : List Bool) (hg : 2 ^ (1 + n) ≤ gap0 w) :
    ∃ c', Allowed c' ∧ (Conf w (rd0 ^ n +> (rds +> ([1] +> default)))) [target_tm]⊢⁺ c' := by
  have hp := pow2_pos (1 + n)
  rcases inc_steps_interior (2 ^ (1 + n) - 1) w (by omega) with ⟨v, hv, _⟩
  rcases last_signal_one n v with ⟨c', hA, hS⟩
  exact ⟨c', hA, stepPlus_trans (shifted_prefix n ([1] +> default) hv) hS⟩

lemma RC_power (a : Nat) : RC rd1 (2 ^ a) (rd0 ^ a +> (rd1 +> default)) := by
  have h1 : RC rd1 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  exact RC_eq (RC_zeros a h1) (by omega) rfl

lemma exceptional (k p : Nat) {r : ListBlank (Fin 2)} (hp : p = 1 ∨ p = 2)
    (hr : RC rd1 (2 ^ (2 * k + p)) r) :
    ∃ c', Allowed c' ∧ (Conf (List.replicate (3 * k + p) false) ([1] +> r)) [target_tm]⊢⁺ c' := by
  have ha : 1 ≤ 2 * k + p := by omega
  have hr_eq : r = rd0 ^ (2 * k + p) +> (rd1 +> default) := RC_unique hr (RC_power (2 * k + p))
  subst hr_eq
  have hg := gap0_zeros k p (by omega)
  have hc := pow2_pos (2 * k + p)
  rcases inc_steps_interior (2 ^ (2 * k + p) - 1) (List.replicate (3 * k + p) false) (by omega)
    with ⟨v, hv, hl, hg_v⟩
  rw [List.length_replicate] at hl
  have hgv1 : gap0 v = 1 := by omega
  have hei : inc v = (List.replicate (3 * k + p) false, true) := by
    have hcap := inc_at_capacity k p v (by omega) hl hgv1
    have hp0 : p ≠ 0 := by omega
    simpa [hp0] using hcap
  have hnew : 2 ^ (1 + (2 * k + p - 1)) ≤ gap0 (push0 1 (List.replicate (3 * k + p) false)) := by
    rw [show 1 + (2 * k + p - 1) = 2 * k + p by omega]
    have hz0 := (zero_entry k p hp).1
    change 2 ^ (2 * k + p) ≤ gap0 (false :: List.replicate (3 * k + p) false)
    rw [Nat.pow_add, pow_two_four]
    rcases hp with rfl | rfl <;> omega
  rcases last_shift_one (2 * k + p - 1) (push0 1 (List.replicate (3 * k + p) false)) hnew
    with ⟨c', hA, hS⟩
  refine ⟨c', hA, ?_⟩
  have s1 := one_cross (2 * k + p) default ha hv
  have s2 := RZero v ([0, 0, 0] +> (rd0 ^ (2 * k + p - 1) +> ([1, 1] +> default))) 0
  rw [hei] at s2
  dsimp only at s2
  have heq2 : rd0 ^ (2 * k + p) +> ([1, 1, 0, 0, 0] +> (default : ListBlank (Fin 2))) =
      rd1 ^ 0 +> ([0] +> ([0, 0, 0] +> (rd0 ^ (2 * k + p - 1) +> ([1, 1] +> default)))) := by
    rw [show 2 * k + p = (2 * k + p - 1) + 1 by omega,
        right_pow_succ rd0 (2 * k + p - 1) ([1, 1, 0, 0, 0] +> default)]
    simp [rd0]
  rw [heq2] at s1
  have heq3 : insert true (rd0 ^ 0 +> ([1] +> ([0, 0, 0] +> (rd0 ^ (2 * k + p - 1) +> ([1, 1] +> default))))) =
      [1, 1] +> (rd0 ^ (2 * k + p - 1) +> (rds +> ([1] +> default))) := by
    change [1, 1] +> (([0, 0, 0] : List (Fin 2)) +> (rd0 ^ (2 * k + p - 1) +> ([1, 1] +> default))) =
      [1, 1] +> (rd0 ^ (2 * k + p - 1) +> (rds +> ([1] +> default)))
    rw [zero3_rd0 (2 * k + p - 1) ([1, 1] +> default)]
    rfl
  rw [heq3] at s2
  have s3 := eleven0 (List.replicate (3 * k + p) false)
    (rd0 ^ (2 * k + p - 1) +> (rds +> ([1] +> default)))
  exact stepPlus_trans s1 (stepPlus_trans s2 (stepPlus_trans s3 hS))

def limit (k p : Nat) : Nat := (if p = 1 then 3 else 4) * 4 ^ k

lemma capacity_limit (k p : Nat) (hp : p = 1 ∨ p = 2) :
    limit k p < 2 * 2 ^ (2 * k + p) := by
  have hc := pow4_pos k
  rw [Nat.pow_add, pow_two_four]
  rcases hp with rfl | rfl <;> dsimp [limit] <;> omega

lemma valuation_bound (k p t q : Nat) (hp : p = 1 ∨ p = 2)
    (hlim : 2 ^ t * (1 + q * 2) ≤ limit k p) (hne : 2 ^ t * (1 + q * 2) ≠ 2 ^ (2 * k + p)) :
    t < 2 * k + p := by
  have hcap := capacity_limit k p hp
  have ht := pow2_pos t
  rcases Nat.lt_or_ge t (2 * k + p) with hlt | hge
  · exact hlt
  · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
    · have hq0 : q = 0 := by nlinarith
      subst hq0
      simp at hne
    · have hpow : 2 ^ (2 * k + p + 1) ≤ 2 ^ t :=
        Nat.pow_le_pow_right (by omega) hgt
      rw [Nat.pow_succ] at hpow
      nlinarith

lemma zero_gap_order (m : Nat) :
    gap0 (List.replicate m false) ≤ gap1 (List.replicate m false) ∧
    gap1 (List.replicate m false) ≤ gap2 (List.replicate m false) ∧
    gap2 (List.replicate m false) ≤ 4 * gap0 (List.replicate m false) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [List.replicate_succ]
    have hc := gap_cons false (List.replicate m false)
    dsimp [zero_bit] at hc
    omega

lemma even_gap (w : List Bool) (hw : w ≠ []) (hv : value w % 2 = 0) :
    gap0 w % 2 = 0 := by
  have hg := value_gap0 w
  have hpos : 0 < width w := by
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, u⟩⟩⟩
    · contradiction
    · dsimp [width]; omega
    · dsimp [width]; omega
    · dsimp [width]; omega
  cases hk : width w with
  | zero => omega
  | succ k =>
    rw [hk, Nat.pow_succ] at hg
    omega

lemma RC_odd_inv {n : Nat} {r : ListBlank (Fin 2)} (hr : RC rd1 (1 + n * 2) r) :
    ∃ s, RC rd1 n s ∧ r = rd1 +> s := by
  rcases RC_inv_d1 hr with ⟨s, rfl, hs⟩
  exact ⟨s, hs, rfl⟩

lemma post_first (k p T : Nat) {r : ListBlank (Fin 2)} (hp : p = 1 ∨ p = 2)
    (hr : RC rd1 T r) (ht : 0 < T) (hlim : T ≤ limit k p) :
    ∃ c', Allowed c' ∧ (Conf (List.replicate (3 * k + p) false) ([1] +> r)) [target_tm]⊢⁺ c' := by
  by_cases hne : T = 2 ^ (2 * k + p)
  · subst hne
    exact exceptional k p hp hr
  · rcases RC_positive_split hr ht with ⟨z, q, s, rfl, hs, het, _⟩
    have hz : z < 2 * k + p := by
      refine valuation_bound k p z q hp ?_ ?_
      · rw [← het]; exact hlim
      · rw [← het]; exact hne
    have hg := gap0_zeros k p (by omega)
    have hq : 2 ^ (z + 1) - 2 < gap0 (List.replicate (3 * k + p) false) := by
      rw [hg]
      have hle : 2 ^ (z + 1) ≤ 2 ^ (2 * k + p) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpz := pow2_pos (z + 1)
      omega
    rcases inc_steps_interior (2 ^ (z + 1) - 2) (List.replicate (3 * k + p) false) hq
      with ⟨v, hv, hl, hgap⟩
    have hm : digit_plane bit_value 2 v = 0 :=
      inc_steps_marker_zero hv (digit_plane_zeros _ _)
    rw [List.length_replicate] at hl
    have hval : value v = 2 ^ (z + 1) - 2 := by
      have hx := value_gap0 v
      rw [width_length k p v (by omega) hl] at hx
      rw [hg] at hgap
      omega
    have hact := actual k p z v q hp hl hm hval hz (by
      dsimp [limit] at hlim
      rw [het] at hlim
      nlinarith)
    have hs_ord := ordinary z s hv
    have hr_shift := RC_shift3 hs
    cases q with
    | zero =>
      rw [RC_zero_unique hr_shift] at hs_ord
      exact ⟨Conf (List.replicate (2 * z) true ++ false :: v) default, Allowed.Blank _, hs_ord⟩
    | succ q =>
      refine ⟨Conf (List.replicate (2 * z) true ++ false :: v) ([0, 0, 0] +> s), ?_, hs_ord⟩
      refine Allowed.Shifted _ (q + 1) ([0, 0, 0] +> s) (by omega) hr_shift ?_
      dsimp [guard]
      omega

lemma odd_entry (m n : Nat) {r : ListBlank (Fin 2)}
    (hr : RC rd1 (1 + n * 2) r) (hb : 2 * n ≤ gap0 (List.replicate (1 + m) false)) :
    ∃ c', Allowed c' ∧ (Conf (List.replicate m false) ([1] +> r)) [target_tm]⊢⁺ c' := by
  rcases RC_odd_inv hr with ⟨s, hs, rfl⟩
  have h11 : ([1] : List (Fin 2)) +> (rd1 +> s) = rd1 ^ 0 +> ([1, 1] +> ([0, 0, 0] +> s)) := rfl
  rw [h11]
  have hs_el := eleven_word 0 (List.replicate m false) ([0, 0, 0] +> s)
  have hrep : List.replicate (2 * 0) true ++ false :: List.replicate m false =
      List.replicate (1 + m) false := by
    rw [Nat.add_comm 1 m, List.replicate_succ]
    rfl
  rw [hrep] at hs_el
  have hr_shift := RC_shift3 hs
  cases n with
  | zero =>
    rw [RC_zero_unique hr_shift] at hs_el ⊢
    exact ⟨Conf (List.replicate (1 + m) false) default, Allowed.Blank _, hs_el⟩
  | succ n =>
    refine ⟨Conf (List.replicate (1 + m) false) ([0, 0, 0] +> s), ?_, hs_el⟩
    refine Allowed.Shifted _ (n + 1) ([0, 0, 0] +> s) (by omega) hr_shift ?_
    have hgo := zero_gap_order (1 + m)
    dsimp [guard]
    omega

lemma phase1_zero_gap (k : Nat) : gap0 (List.replicate (3 * k + 1) false) = 2 * 4 ^ k := by
  rw [gap0_zeros k 1 (by omega), Nat.pow_add, pow_two_four]
  ring

lemma phase12 (k p : Nat) (w : List Bool) (x : Nat) (r : ListBlank (Fin 2))
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hl : w.length = 3 * k + p) (hr : RC rd1 x r) :
    ∃ s, RC rd1 (x + gap0 w) s ∧
      (Conf w r) [target_tm]⊢⁺ (Conf (List.replicate (3 * k + p) false) ([1] +> s)) := by
  rcases first_capacity k p w hp2 hl with ⟨u, hs, _, _, he⟩
  have hp0 : p ≠ 0 := by omega
  simp [hp0] at he
  rcases right_steps hs hr with ⟨s1, hr1, hR1⟩
  rcases right_step he hr1 with ⟨s2, hr2, hR2⟩
  have hb := (gap_bounds w).1
  exact ⟨s2, RC_eq hr2 (by omega) rfl, stepStar_stepPlus_trans hR1 hR2⟩

lemma phase0_extend (k : Nat) (w : List Bool) (x : Nat) (r : ListBlank (Fin 2))
    (hl : w.length = 3 * k) (hr : RC rd1 x r) :
    ∃ s, RC rd1 (x + gap0 w) s ∧
      (Conf w r) [target_tm]⊢⁺ (Conf (List.replicate (3 * k + 1) false) s) := by
  rcases first_capacity k 0 w (by omega) (by omega) with ⟨u, hs, _, _, he⟩
  simp at he
  rcases right_steps hs hr with ⟨s1, hr1, hR1⟩
  rcases right_step he hr1 with ⟨s2, hr2, hR2⟩
  have hb := (gap_bounds w).1
  exact ⟨s2, RC_eq hr2 (by omega) rfl, stepStar_stepPlus_trans hR1 hR2⟩

lemma phase0 (k : Nat) (w : List Bool) (x : Nat) (r : ListBlank (Fin 2))
    (hl : w.length = 3 * k) (hr : RC rd1 x r) :
    ∃ s, RC rd1 (x + gap0 w + 2 * 4 ^ k) s ∧
      (Conf w r) [target_tm]⊢⁺ (Conf (List.replicate (3 * k + 1) false) ([1] +> s)) := by
  rcases phase0_extend k w x r hl hr with ⟨s1, hr1, hS1⟩
  rcases phase12 k 1 (List.replicate (3 * k + 1) false) (x + gap0 w) s1
    (by omega) (by omega) List.length_replicate hr1 with ⟨s2, hr2, hS2⟩
  rw [phase1_zero_gap] at hr2
  exact ⟨s2, hr2, stepPlus_trans hS1 hS2⟩

lemma length_split (w : List Bool) : ∃ k p, p ≤ 2 ∧ w.length = 3 * k + p :=
  ⟨w.length / 3, w.length % 3, by omega, by omega⟩

lemma capacity_bound (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p) :
    gap0 w ≤ 2 ^ p * 4 ^ k := by
  have h := value_gap0 w
  rw [width_length k p w hp hl, Nat.pow_add, pow_two_four] at h
  nlinarith

lemma right_one : RC rd1 1 ([1] +> default) := by
  have h0 : RC rd1 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  have heq : rd1 +> (default : ListBlank (Fin 2)) = [1] +> default := by simp [rd1]
  rwa [heq] at h0

lemma blank_step (w : List Bool) :
    ∃ c', Allowed c' ∧ (Conf w default) [target_tm]⊢⁺ c' := by
  rcases length_split w with ⟨k, p, hp, hl⟩
  have hb := capacity_bound k p w hp hl
  have hg := (gap_bounds w).1
  rcases Nat.eq_zero_or_pos p with rfl | hp_pos
  · simp at hl hb
    rcases phase0 k w 0 default hl RC.zero with ⟨s, hr, hS⟩
    have hle : 0 + gap0 w + 2 * 4 ^ k ≤ limit k 1 := by dsimp [limit]; omega
    rcases post_first k 1 (0 + gap0 w + 2 * 4 ^ k) (Or.inl rfl) hr (by omega) hle
      with ⟨c', hA, hT⟩
    exact ⟨c', hA, stepPlus_trans hS hT⟩
  · have hf : p = 1 ∨ p = 2 := by omega
    have hb' : 0 + gap0 w ≤ limit k p := by
      dsimp [limit]
      rcases hf with rfl | rfl <;> simp at hb ⊢ <;> omega
    rcases phase12 k p w 0 default hp_pos hp hl RC.zero with ⟨s, hr, hS⟩
    rcases post_first k p (0 + gap0 w) hf hr (by omega) hb' with ⟨c', hA, hT⟩
    exact ⟨c', hA, stepPlus_trans hS hT⟩

lemma one_step (w : List Bool) (hw : w ≠ []) (hv : value w % 2 = 0) :
    ∃ c', Allowed c' ∧ (Conf w ([1] +> default)) [target_tm]⊢⁺ c' := by
  have heg := even_gap w hw hv
  set a := gap0 w / 2
  have hga : gap0 w = 2 * a := by omega
  rcases length_split w with ⟨k, p, hp, hl⟩
  have hb := capacity_bound k p w hp hl
  rcases Nat.eq_zero_or_pos p with rfl | hp_pos
  · simp at hl hb
    rcases phase0 k w 1 ([1] +> default) hl right_one with ⟨s, hr, hS⟩
    have hr' : RC rd1 (1 + (a + 4 ^ k) * 2) s := RC_eq hr (by omega) rfl
    have hg_bound : 2 * (a + 4 ^ k) ≤ gap0 (List.replicate (1 + (3 * k + 1)) false) := by
      have hz := (zero_entry k 1 (Or.inl rfl)).1
      have hrep : List.replicate (1 + (3 * k + 1)) false = false :: List.replicate (3 * k + 1) false := by
        rw [Nat.add_comm 1 (3 * k + 1), List.replicate_succ]
      rw [hrep]
      omega
    rcases odd_entry (3 * k + 1) (a + 4 ^ k) hr' hg_bound with ⟨c', hC, hT⟩
    exact ⟨c', hC, stepPlus_trans hS hT⟩
  · have hf : p = 1 ∨ p = 2 := by omega
    have hb' : gap0 w ≤ 4 * 4 ^ k := by
      rcases hf with rfl | rfl <;> simp at hb <;> omega
    rcases phase12 k p w 1 ([1] +> default) hp_pos hp hl right_one with ⟨s, hr, hS⟩
    have hr' : RC rd1 (1 + a * 2) s := RC_eq hr (by omega) rfl
    have hg_bound : 2 * a ≤ gap0 (List.replicate (1 + (3 * k + p)) false) := by
      have hz := (zero_entry k p hf).1
      have hrep : List.replicate (1 + (3 * k + p)) false = false :: List.replicate (3 * k + p) false := by
        rw [Nat.add_comm 1 (3 * k + p), List.replicate_succ]
      rw [hrep]
      omega
    rcases odd_entry (3 * k + p) a hr' hg_bound with ⟨c', hC, hT⟩
    exact ⟨c', hC, stepPlus_trans hS hT⟩

lemma Allowed_step {c : Cfg (Fin 2) (Fin 6)} (hA : Allowed c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  cases hA with
  | Blank w => exact blank_step w
  | One w hw hv => exact one_step w hw hv
  | Shifted w n r hn hr hg => exact shifted_step n w r hn hr hg

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : Nat}
    (h : multiStep target_tm c k = none) (d : Nat) :
    multiStep target_tm c (k + d) = none := by
  rw [multiStep_add, h]; rfl

theorem reach_arbitrarily_long :
    ∀ m : Nat, ∃ N c, m ≤ N ∧ Allowed c ∧ multiStep target_tm (init []) N = some c
  | 0 => by
    rcases init31 with ⟨N₀, hN₀⟩
    exact ⟨N₀, _, Nat.zero_le N₀, Allowed.Blank [false, false], hN₀⟩
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

end BusyBeaver.M_1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE
