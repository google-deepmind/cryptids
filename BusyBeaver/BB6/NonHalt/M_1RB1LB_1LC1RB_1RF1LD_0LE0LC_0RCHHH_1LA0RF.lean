/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LB_1LC1RB_1RF1LD_0LE0LC_0RC---_1LA0RF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LB_1LC1RB_1RF1LD_0LE0LC_0RC---_1LA0RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LB_1LC1RB_1RF1LD_0LE0LC_0RCHHH_1LA0RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LB_1LC1RB_1RF1LD_0LE0LC_0RC---_1LA0RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 4, 1 => none
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def F : Fin 6 := 5

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

def U0 : List (Fin 2) := [1, 1, 0, 0, 0]
def U1 : List (Fin 2) := [1, 1, 1, 0, 0]
def d0 : List (Fin 2) := [0, 0, 0, 0]
def d1 : List (Fin 2) := [1, 0, 0, 0]
def d2 : List (Fin 2) := [0, 1, 0, 0]
def d3 : List (Fin 2) := [1, 1, 0, 0]
def p11 : List (Fin 2) := [1, 1]
def p10 : List (Fin 2) := [1, 0]
def p01 : List (Fin 2) := [0, 1]
def one_tok : List (Fin 2) := [1]

macro "step1" : tactic => `(tactic| (
  try simp only [init_nil, U0, U1, d0, d1, d2, d3, p11, p10, p01, one_tok,
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
  simp only [U0, U1, d0, d1, d2, d3, p11, p10, p01, one_tok,
    pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail, multiStep_zero]
  rfl))

-- ============================================================================
-- Section 1: Tape Rotation & Power Shift Identities
-- ============================================================================

lemma one_zero_pow_shift (m : Nat) (r : ListBlank (Fin 2)) :
    p10 ^ m +> ([1] +> r) = [1] +> (p01 ^ m +> r) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [right_pow_succ p10 m, ih, right_pow_succ p01 m]
    rfl

lemma one_one_pow_shift (m : Nat) (l : ListBlank (Fin 2)) :
    l <+ p11 ^ m <+ [1] = l <+ [1] <+ p11 ^ m := by
  induction m generalizing l with
  | zero => rfl
  | succ m ih =>
    rw [left_pow_succ_right l p11 m, ih (l <+ p11), left_pow_succ_right (l <+ [1]) p11 m]
    rfl

-- ============================================================================
-- Section 2: Side Call Relations & Primitive Machine Rules
-- ============================================================================

def sideH (l l' : ListBlank (Fin 2)) : Prop :=
  ∀ r, (l <{{C}} r) [target_tm]⊢⁺ (l' {{F}}> r)

def sideP (l l' : ListBlank (Fin 2)) : Prop :=
  ∀ r, (l <{{D}} r) [target_tm]⊢⁺ (l' {{B}}> r)

def sidePs : Nat → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | 0, l, l' => l = l'
  | q + 1, l, l' => ∃ lm, sideP l lm ∧ sidePs q lm l'

lemma sidePs_snoc {q : Nat} {l l' : ListBlank (Fin 2)}
    (h : sidePs (q + 1) l l') : ∃ lm, sidePs q l lm ∧ sideP lm l' := by
  induction q generalizing l with
  | zero =>
    rcases h with ⟨lm, hp, rfl⟩
    exact ⟨l, rfl, hp⟩
  | succ q ih =>
    rcases h with ⟨lm₁, hp₁, hps⟩
    rcases ih hps with ⟨lm₂, hps₂, hp₂⟩
    exact ⟨lm₂, ⟨lm₁, hp₁, hps₂⟩, hp₂⟩

lemma P0 (l : ListBlank (Fin 2)) : sideP (l <+ U0) (l <+ U1) :=
  fun _ => ⟨9, by omega, by run_steps 9⟩

lemma P1_enter (l r : ListBlank (Fin 2)) :
    ((l <+ U1) <{{D}} r) [target_tm]⊢⁺ (l <{{C}} (p11 ^ 2 +> ([0] +> r))) :=
  ⟨7, by omega, by run_steps 7⟩

lemma P1_exit (l' r : ListBlank (Fin 2)) :
    (l' {{F}}> (p11 ^ 2 +> ([0] +> r))) [target_tm]⊢⁺ ((l' <+ U0) {{B}}> r) :=
  ⟨7, by omega, by run_steps 7⟩

lemma P1 {l l' : ListBlank (Fin 2)} (h : sideH l l') : sideP (l <+ U1) (l' <+ U0) :=
  fun r => stepPlus_trans (P1_enter l r) (stepPlus_trans (h (p11 ^ 2 +> ([0] +> r))) (P1_exit l' r))

lemma H0 (l : ListBlank (Fin 2)) : sideH (l <+ d0) (l <+ d1) :=
  fun _ => ⟨1, by omega, by run_steps 1⟩

lemma H1 (l : ListBlank (Fin 2)) : sideH (l <+ d1) (l <+ d2) :=
  fun _ => ⟨5, by omega, by run_steps 5⟩

lemma H2 (l : ListBlank (Fin 2)) : sideH (l <+ d2) (l <+ d3) :=
  fun _ => ⟨1, by omega, by run_steps 1⟩

lemma H3_enter (l r : ListBlank (Fin 2)) :
    ((l <+ d3) <{{C}} r) [target_tm]⊢⁺ (l <{{C}} (p11 ^ 2 +> r)) :=
  ⟨6, by omega, by run_steps 6⟩

lemma H3_exit (l' r : ListBlank (Fin 2)) :
    (l' {{F}}> (p11 ^ 2 +> r)) [target_tm]⊢⁺ ((l' <+ d0) {{F}}> r) :=
  ⟨4, by omega, by run_steps 4⟩

lemma H3 {l l' : ListBlank (Fin 2)} (h : sideH l l') : sideH (l <+ d3) (l' <+ d0) :=
  fun r => stepPlus_trans (H3_enter l r) (stepPlus_trans (h (p11 ^ 2 +> r)) (H3_exit l' r))

lemma HT0 (l : ListBlank (Fin 2)) : sideH (l <+ [0, 0, 0]) (l <+ [1, 0, 0]) :=
  fun _ => ⟨1, by omega, by run_steps 1⟩

lemma HT1 (l : ListBlank (Fin 2)) : sideH (l <+ [1, 0, 0]) (l <+ [0, 1, 0]) :=
  fun _ => ⟨5, by omega, by run_steps 5⟩

lemma HT2 (l : ListBlank (Fin 2)) : sideH (l <+ [0, 1, 0]) (l <+ [1, 1, 0]) :=
  fun _ => ⟨1, by omega, by run_steps 1⟩

lemma StackEnter (l r : ListBlank (Fin 2)) :
    ((l <+ p11) <{{D}} r) [target_tm]⊢⁺ (l <{{D}} (p10 +> r)) :=
  ⟨2, by omega, by run_steps 2⟩

lemma StackFirst (l r : ListBlank (Fin 2)) :
    (l {{B}}> (p10 +> r)) [target_tm]⊢⁺ (l <{{D}} (p11 +> r)) :=
  ⟨3, by omega, by run_steps 3⟩

lemma StackLast (l r : ListBlank (Fin 2)) :
    (l {{B}}> (p11 +> r)) [target_tm]⊢⁺ ((l <+ p11) {{B}}> r) :=
  ⟨2, by omega, by run_steps 2⟩

lemma LastReturn (m : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> (p11 ^ m +> r)) [target_tm]⊢* ((l <+ p11 ^ m) {{B}}> r) := by
  induction m generalizing l with
  | zero => exact stepStar_refl _
  | succ m ih =>
    rw [right_pow_succ p11 m r, left_pow_succ_right l p11 m]
    exact stepStar_trans (stepPlus_to_stepStar (StackLast l _)) (ih (l <+ p11))

lemma H3_enter_pow (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ d3 ^ k) <{{C}} r) [target_tm]⊢* (l <{{C}} (p11 ^ (k * 2) +> r)) := by
  induction k generalizing r with
  | zero => exact stepStar_refl _
  | succ k ih =>
    rw [left_pow_succ l d3 k]
    refine stepStar_trans (stepPlus_to_stepStar (H3_enter (l <+ d3 ^ k) r)) ?_
    refine stepStar_trans (ih (p11 ^ 2 +> r)) ?_
    rw [← right_pow_add p11 (k * 2) 2 r, show k * 2 + 2 = (k + 1) * 2 by omega]
    exact stepStar_refl _

lemma overflow_turn (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1, 0, 1]) <{{C}} r) [target_tm]⊢⁺ (l {{B}}> (p11 ^ 2 +> r)) :=
  ⟨5, by omega, by run_steps 5⟩

lemma overflow_b0 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0] +> r)) [target_tm]⊢⁺ (l <{{C}} ([1] +> r)) :=
  ⟨1, by omega, by run_steps 1⟩

lemma overflow_c_step (l r : ListBlank (Fin 2)) :
    ((l <+ p11) <{{C}} r) [target_tm]⊢⁺ (l <{{C}} (p01 +> r)) :=
  ⟨2, by omega, by run_steps 2⟩

lemma overflow_c_scan (m : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ p11 ^ m) <{{C}} r) [target_tm]⊢* (l <{{C}} (p01 ^ m +> r)) := by
  induction m generalizing r with
  | zero => exact stepStar_refl _
  | succ m ih =>
    rw [left_pow_succ l p11 m]
    refine stepStar_trans (stepPlus_to_stepStar (overflow_c_step (l <+ p11 ^ m) r)) ?_
    refine stepStar_trans (ih (p01 +> r)) ?_
    rw [← right_pow_succ_right p01 m r]
    exact stepStar_refl _

lemma TerminalOverflow (l r : ListBlank (Fin 2)) (k : Nat) :
    ((l <+ [1, 1, 0, 1] <+ d3 ^ k <+ U1) <{{D}} r) [target_tm]⊢⁺
    (l <{{C}} (p01 ^ (k * 2 + 4) +> ([1] +> r))) := by
  have h1 : ((l <+ [1, 1, 0, 1] <+ d3 ^ k <+ U1) <{{D}} r) [target_tm]⊢⁺
      ((l <+ [1, 1, 0, 1] <+ d3 ^ k) <{{C}} (p11 ^ 2 +> ([0] +> r))) :=
    P1_enter (l <+ [1, 1, 0, 1] <+ d3 ^ k) r
  have h2 : ((l <+ [1, 1, 0, 1] <+ d3 ^ k) <{{C}} (p11 ^ 2 +> ([0] +> r))) [target_tm]⊢*
      ((l <+ [1, 1, 0, 1]) <{{C}} (p11 ^ (k * 2 + 2) +> ([0] +> r))) := by
    have h2' := H3_enter_pow k (l <+ [1, 1, 0, 1]) (p11 ^ 2 +> ([0] +> r))
    rwa [← right_pow_add p11 (k * 2) 2 ([0] +> r)] at h2'
  have h3 : ((l <+ [1, 1, 0, 1]) <{{C}} (p11 ^ (k * 2 + 2) +> ([0] +> r))) [target_tm]⊢⁺
      (l {{B}}> (p11 ^ (k * 2 + 4) +> ([0] +> r))) := by
    have h3' := overflow_turn l (p11 ^ (k * 2 + 2) +> ([0] +> r))
    rwa [← right_pow_add p11 2 (k * 2 + 2) ([0] +> r), show 2 + (k * 2 + 2) = k * 2 + 4 by omega] at h3'
  have h4 := LastReturn (k * 2 + 4) l ([0] +> r)
  have h5 := overflow_b0 (l <+ p11 ^ (k * 2 + 4)) r
  have h6 := overflow_c_scan (k * 2 + 4) l ([1] +> r)
  exact stepPlus_stepStar_trans
    (stepPlus_trans (stepPlus_stepStar_trans h1 h2) (stepPlus_trans (stepPlus_stepStar_trans h3 h4) h5)) h6

lemma Reentry0 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 0, 0, 0, 0, 0]) <{{C}} (p01 ^ 3 +> r)) [target_tm]⊢⁺
    ((l <+ [1, 1, 0, 0, 0, 1, 0, 0, 0]) <{{D}} ([1, 1, 1] +> r)) :=
  ⟨15, by omega, by run_steps 15⟩

lemma Reentry1 (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 0, 0, 0]) <{{C}} (p01 ^ 2 +> r)) [target_tm]⊢⁺
    ((l <+ U1) <{{D}} ([1, 1, 1] +> r)) :=
  ⟨11, by omega, by run_steps 11⟩

lemma Restart0 (l r : ListBlank (Fin 2)) :
    ((l <+ [1]) {{B}}> ([0] +> r)) [target_tm]⊢⁺ (l <{{D}} (p11 +> r)) :=
  ⟨2, by omega, by run_steps 2⟩

lemma Restart11 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [1]) <{{D}} (p11 +> r)) :=
  ⟨4, by omega, by run_steps 4⟩

-- ============================================================================
-- Section 3: Base-4 and Normal Counters (TM6Counter)
-- ============================================================================

inductive RC : Nat → ListBlank (Fin 2) → Prop where
  | zero : RC 0 default
  | d0 (n : Nat) (l : ListBlank (Fin 2)) : RC n l → RC (4 * n) (l <+ d0)
  | d1 (n : Nat) (l : ListBlank (Fin 2)) : RC n l → RC (1 + 4 * n) (l <+ d1)
  | d2 (n : Nat) (l : ListBlank (Fin 2)) : RC n l → RC (2 + 4 * n) (l <+ d2)
  | d3 (n : Nat) (l : ListBlank (Fin 2)) : RC n l → RC (3 + 4 * n) (l <+ d3)

lemma d0_default : (default : ListBlank (Fin 2)) <+ d0 = default := by
  simp [d0]

lemma RC_zero_unique {l : ListBlank (Fin 2)} (h : RC 0 l) : l = default := by
  generalize hn : (0 : Nat) = n at h
  induction h with
  | zero => rfl
  | d0 n l _ ih =>
    have hn0 : n = 0 := by omega
    rw [ih hn0.symm, d0_default]
  | d1 => omega
  | d2 => omega
  | d3 => omega

lemma RC_unique {n : Nat} {l l' : ListBlank (Fin 2)} (h : RC n l) (h' : RC n l') : l = l' := by
  induction h generalizing l' with
  | zero => exact (RC_zero_unique h').symm
  | d0 n l h ih =>
    generalize hm : 4 * n = m at h'
    cases h' with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      rw [RC_zero_unique h, d0_default]
    | d0 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [ih h']
    | d1 => omega
    | d2 => omega
    | d3 => omega
  | d1 n l h ih =>
    generalize hm : 1 + 4 * n = m at h'
    cases h' with
    | zero => omega
    | d0 => omega
    | d1 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [ih h']
    | d2 => omega
    | d3 => omega
  | d2 n l h ih =>
    generalize hm : 2 + 4 * n = m at h'
    cases h' with
    | zero => omega
    | d0 => omega
    | d1 => omega
    | d2 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [ih h']
    | d3 => omega
  | d3 n l h ih =>
    generalize hm : 3 + 4 * n = m at h'
    cases h' with
    | zero => omega
    | d0 => omega
    | d1 => omega
    | d2 => omega
    | d3 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [ih h']

lemma RInc {n : Nat} {l : ListBlank (Fin 2)} (h : RC n l) :
    ∃ l', RC (n + 1) l' ∧ sideH l l' := by
  induction h with
  | zero =>
    refine ⟨default <+ d1, ?_, ?_⟩
    · exact RC.d1 0 default RC.zero
    · have h0 := H0 default
      rwa [d0_default] at h0
  | d0 n l h _ =>
    refine ⟨l <+ d1, ?_, H0 l⟩
    rw [show 4 * n + 1 = 1 + 4 * n by omega]
    exact RC.d1 n l h
  | d1 n l h _ =>
    refine ⟨l <+ d2, ?_, H1 l⟩
    rw [show (1 + 4 * n) + 1 = 2 + 4 * n by omega]
    exact RC.d2 n l h
  | d2 n l h _ =>
    refine ⟨l <+ d3, ?_, H2 l⟩
    rw [show (2 + 4 * n) + 1 = 3 + 4 * n by omega]
    exact RC.d3 n l h
  | d3 n l _ ih =>
    rcases ih with ⟨l', hl', hstep⟩
    refine ⟨l' <+ d0, ?_, H3 hstep⟩
    rw [show (3 + 4 * n) + 1 = 4 * (n + 1) by omega]
    exact RC.d0 (n + 1) l' hl'

inductive NC : Nat → ListBlank (Fin 2) → Prop where
  | u0 (n : Nat) (l : ListBlank (Fin 2)) : RC n l → NC (2 * n) (l <+ U0)
  | u1 (n : Nat) (l : ListBlank (Fin 2)) : RC n l → NC (1 + 2 * n) (l <+ U1)

lemma NC_unique {n : Nat} {l l' : ListBlank (Fin 2)} (h : NC n l) (h' : NC n l') : l = l' := by
  cases h with
  | u0 n l h =>
    generalize hm : 2 * n = m at h'
    cases h' with
    | u0 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [RC_unique h h']
    | u1 => omega
  | u1 n l h =>
    generalize hm : 1 + 2 * n = m at h'
    cases h' with
    | u0 => omega
    | u1 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [RC_unique h h']

lemma NormalInc {n : Nat} {l : ListBlank (Fin 2)} (h : NC n l) :
    ∃ l', NC (n + 1) l' ∧ sideP l l' := by
  cases h with
  | u0 n l h =>
    refine ⟨l <+ U1, ?_, P0 l⟩
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    exact NC.u1 n l h
  | u1 n l h =>
    rcases RInc h with ⟨l', hl', hstep⟩
    refine ⟨l' <+ U0, ?_, P1 hstep⟩
    rw [show (1 + 2 * n) + 1 = 2 * (n + 1) by omega]
    exact NC.u0 (n + 1) l' hl'

lemma NormalAdds_ex (q : Nat) {n : Nat} {l : ListBlank (Fin 2)} (h : NC n l) :
    ∃ l', NC (n + q) l' ∧ sidePs q l l' := by
  induction q generalizing n l with
  | zero => exact ⟨l, h, rfl⟩
  | succ q ih =>
    rcases NormalInc h with ⟨l₁, hl₁, hp⟩
    rcases ih hl₁ with ⟨l₂, hl₂, hps⟩
    rw [show n + (q + 1) = (n + 1) + q by omega]
    exact ⟨l₂, hl₂, ⟨l₁, hp, hps⟩⟩

lemma NormalAdds (q : Nat) {n : Nat} {l l' : ListBlank (Fin 2)}
    (h : NC n l) (h' : NC (n + q) l') : sidePs q l l' := by
  rcases NormalAdds_ex q h with ⟨l₂, hl₂, hps⟩
  rw [NC_unique h' hl₂]
  exact hps

inductive FC (tail : ListBlank (Fin 2)) : Nat → Nat → ListBlank (Fin 2) → Prop where
  | t0 : FC tail 0 0 (tail <+ [0, 0, 0])
  | t1 : FC tail 0 1 (tail <+ [1, 0, 0])
  | t2 : FC tail 0 2 (tail <+ [0, 1, 0])
  | t3 : FC tail 0 3 (tail <+ [1, 1, 0])
  | d0 (k n : Nat) (l : ListBlank (Fin 2)) : FC tail k n l → FC tail (k + 1) (4 * n) (l <+ d0)
  | d1 (k n : Nat) (l : ListBlank (Fin 2)) : FC tail k n l → FC tail (k + 1) (1 + 4 * n) (l <+ d1)
  | d2 (k n : Nat) (l : ListBlank (Fin 2)) : FC tail k n l → FC tail (k + 1) (2 + 4 * n) (l <+ d2)
  | d3 (k n : Nat) (l : ListBlank (Fin 2)) : FC tail k n l → FC tail (k + 1) (3 + 4 * n) (l <+ d3)

lemma FC_zero_inv {tail : ListBlank (Fin 2)} {K m : Nat} {l' : ListBlank (Fin 2)}
    (h : FC tail K m l') (hK : K = 0) :
    (m = 0 ∧ l' = tail <+ [0, 0, 0]) ∨
    (m = 1 ∧ l' = tail <+ [1, 0, 0]) ∨
    (m = 2 ∧ l' = tail <+ [0, 1, 0]) ∨
    (m = 3 ∧ l' = tail <+ [1, 1, 0]) := by
  cases h with
  | t0 => exact Or.inl ⟨rfl, rfl⟩
  | t1 => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | t2 => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | t3 => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  | _ => omega

lemma FC_unique {tail : ListBlank (Fin 2)} {k n : Nat} {l l' : ListBlank (Fin 2)}
    (h : FC tail k n l) (h' : FC tail k n l') : l = l' := by
  induction h generalizing l' with
  | t0 =>
    rcases FC_zero_inv h' rfl with ⟨_, rfl⟩ | ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨h3, _⟩ <;> first | rfl | omega
  | t1 =>
    rcases FC_zero_inv h' rfl with ⟨h0, _⟩ | ⟨_, rfl⟩ | ⟨h2, _⟩ | ⟨h3, _⟩ <;> first | rfl | omega
  | t2 =>
    rcases FC_zero_inv h' rfl with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨_, rfl⟩ | ⟨h3, _⟩ <;> first | rfl | omega
  | t3 =>
    rcases FC_zero_inv h' rfl with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, rfl⟩ <;> first | rfl | omega
  | d0 k n l _ ih =>
    generalize hk : k + 1 = K, hm : 4 * n = m at h'
    cases h' with
    | d0 k' n' l' h' =>
      have hk' : k = k' := by omega
      have hn' : n = n' := by omega
      subst hk'; subst hn'; rw [ih h']
    | _ => omega
  | d1 k n l _ ih =>
    generalize hk : k + 1 = K, hm : 1 + 4 * n = m at h'
    cases h' with
    | d1 k' n' l' h' =>
      have hk' : k = k' := by omega
      have hn' : n = n' := by omega
      subst hk'; subst hn'; rw [ih h']
    | _ => omega
  | d2 k n l _ ih =>
    generalize hk : k + 1 = K, hm : 2 + 4 * n = m at h'
    cases h' with
    | d2 k' n' l' h' =>
      have hk' : k = k' := by omega
      have hn' : n = n' := by omega
      subst hk'; subst hn'; rw [ih h']
    | _ => omega
  | d3 k n l _ ih =>
    generalize hk : k + 1 = K, hm : 3 + 4 * n = m at h'
    cases h' with
    | d3 k' n' l' h' =>
      have hk' : k = k' := by omega
      have hn' : n = n' := by omega
      subst hk'; subst hn'; rw [ih h']
    | _ => omega

lemma FiniteRInc {tail : ListBlank (Fin 2)} {k n : Nat} {l : ListBlank (Fin 2)}
    (h : FC tail k n l) (hbound : n + 1 < 4 ^ (k + 1)) :
    ∃ l', FC tail k (n + 1) l' ∧ sideH l l' := by
  induction h with
  | t0 => exact ⟨tail <+ [1, 0, 0], FC.t1, HT0 tail⟩
  | t1 => exact ⟨tail <+ [0, 1, 0], FC.t2, HT1 tail⟩
  | t2 => exact ⟨tail <+ [1, 1, 0], FC.t3, HT2 tail⟩
  | t3 => simp at hbound
  | d0 k n l h _ =>
    refine ⟨l <+ d1, ?_, H0 l⟩
    rw [show 4 * n + 1 = 1 + 4 * n by omega]
    exact FC.d1 k n l h
  | d1 k n l h _ =>
    refine ⟨l <+ d2, ?_, H1 l⟩
    rw [show (1 + 4 * n) + 1 = 2 + 4 * n by omega]
    exact FC.d2 k n l h
  | d2 k n l h _ =>
    refine ⟨l <+ d3, ?_, H2 l⟩
    rw [show (2 + 4 * n) + 1 = 3 + 4 * n by omega]
    exact FC.d3 k n l h
  | d3 k n l _ ih =>
    have hsmall : n + 1 < 4 ^ (k + 1) := by
      rw [Nat.pow_succ] at hbound; omega
    rcases ih hsmall with ⟨l', hl', hstep⟩
    refine ⟨l' <+ d0, ?_, H3 hstep⟩
    rw [show (3 + 4 * n) + 1 = 4 * (n + 1) by omega]
    exact FC.d0 k (n + 1) l' hl'

inductive FNC (tail : ListBlank (Fin 2)) (k : Nat) : Nat → ListBlank (Fin 2) → Prop where
  | u0 (n : Nat) (l : ListBlank (Fin 2)) : FC tail k n l → FNC tail k (2 * n) (l <+ U0)
  | u1 (n : Nat) (l : ListBlank (Fin 2)) : FC tail k n l → FNC tail k (1 + 2 * n) (l <+ U1)

lemma FNC_unique {tail : ListBlank (Fin 2)} {k n : Nat} {l l' : ListBlank (Fin 2)}
    (h : FNC tail k n l) (h' : FNC tail k n l') : l = l' := by
  cases h with
  | u0 n l h =>
    generalize hm : 2 * n = m at h'
    cases h' with
    | u0 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [FC_unique h h']
    | u1 => omega
  | u1 n l h =>
    generalize hm : 1 + 2 * n = m at h'
    cases h' with
    | u0 => omega
    | u1 n' l' h' =>
      have : n = n' := by omega
      subst this; rw [FC_unique h h']

lemma FiniteInc {tail : ListBlank (Fin 2)} {k n : Nat} {l : ListBlank (Fin 2)}
    (h : FNC tail k n l) (hbound : n + 1 < 2 * 4 ^ (k + 1)) :
    ∃ l', FNC tail k (n + 1) l' ∧ sideP l l' := by
  cases h with
  | u0 n l h =>
    refine ⟨l <+ U1, ?_, P0 l⟩
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    exact FNC.u1 n l h
  | u1 n l h =>
    have hsmall : n + 1 < 4 ^ (k + 1) := by omega
    rcases FiniteRInc h hsmall with ⟨l', hl', hstep⟩
    refine ⟨l' <+ U0, ?_, P1 hstep⟩
    rw [show (1 + 2 * n) + 1 = 2 * (n + 1) by omega]
    exact FNC.u0 (n + 1) l' hl'

lemma FiniteAdds_ex {tail : ListBlank (Fin 2)} {k : Nat} (q : Nat) {n : Nat} {l : ListBlank (Fin 2)}
    (h : FNC tail k n l) (hbound : n + q < 2 * 4 ^ (k + 1)) :
    ∃ l', FNC tail k (n + q) l' ∧ sidePs q l l' := by
  induction q generalizing n l with
  | zero => exact ⟨l, h, rfl⟩
  | succ q ih =>
    have hfirst : n + 1 < 2 * 4 ^ (k + 1) := by omega
    rcases FiniteInc h hfirst with ⟨l₁, hl₁, hp⟩
    have hrest : (n + 1) + q < 2 * 4 ^ (k + 1) := by omega
    rcases ih hl₁ hrest with ⟨l₂, hl₂, hps⟩
    rw [show n + (q + 1) = (n + 1) + q by omega]
    exact ⟨l₂, hl₂, ⟨l₁, hp, hps⟩⟩

lemma FiniteAdds {tail : ListBlank (Fin 2)} {k : Nat} (q : Nat) {n : Nat} {l l' : ListBlank (Fin 2)}
    (h : FNC tail k n l) (h' : FNC tail k (n + q) l') (hbound : n + q < 2 * 4 ^ (k + 1)) :
    sidePs q l l' := by
  rcases FiniteAdds_ex q h hbound with ⟨l₂, hl₂, hps⟩
  rw [FNC_unique h' hl₂]
  exact hps

-- ============================================================================
-- Section 4: Binary Call Stack Frames (TM6Frames)
-- ============================================================================

def bval (b : Bool) : Nat := if b then 1 else 0
def bit (b : Bool) : Fin 2 := if b then 1 else 0

def fvalue : List Bool → Nat
  | [] => 0
  | b :: bs => bval b + 2 * fvalue bs

def Frame : List Bool → List (Fin 2)
  | [] => []
  | b :: bs => [1, bit b] ++ Frame bs

def finc : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: finc bs

lemma Frame_app (xs ys : List Bool) : Frame (xs ++ ys) = Frame xs ++ Frame ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [Frame, ih]

lemma fvalue_app (xs ys : List Bool) :
    fvalue (xs ++ ys) = fvalue xs + 2 ^ xs.length * fvalue ys := by
  induction xs with
  | nil => simp [fvalue]
  | cons b xs ih =>
    simp only [List.cons_append, fvalue, List.length_cons, ih, Nat.pow_succ]
    ring

lemma fvalue_zeros (m : Nat) : fvalue (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, fvalue, bval, ih]

lemma fvalue_bound (bs : List Bool) : fvalue bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [fvalue]
  | cons b bs ih =>
    cases b
    · change 0 + 2 * fvalue bs < 2 ^ bs.length * 2; omega
    · change 1 + 2 * fvalue bs < 2 ^ bs.length * 2; omega

lemma finc_length (bs : List Bool) : (finc bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [finc, ih]

lemma fvalue_finc (bs : List Bool) (h : fvalue bs + 1 < 2 ^ bs.length) :
    fvalue (finc bs) = fvalue bs + 1 := by
  induction bs with
  | nil => simp [fvalue] at h
  | cons b bs ih =>
    cases b
    · change 1 + 2 * fvalue bs = (0 + 2 * fvalue bs) + 1
      omega
    · change 1 + 2 * fvalue bs + 1 < 2 ^ bs.length * 2 at h
      have hbs : fvalue bs + 1 < 2 ^ bs.length := by omega
      change 0 + 2 * fvalue (finc bs) = (1 + 2 * fvalue bs) + 1
      rw [ih hbs]
      omega

lemma fvalue_injective {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hval : fvalue xs = fvalue ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c ys =>
      simp only [List.length_cons] at hlen
      cases b <;> cases c
      · change 0 + 2 * fvalue xs = 0 + 2 * fvalue ys at hval
        congr 1; exact ih (by omega) (by omega)
      · change 0 + 2 * fvalue xs = 1 + 2 * fvalue ys at hval; omega
      · change 1 + 2 * fvalue xs = 0 + 2 * fvalue ys at hval; omega
      · change 1 + 2 * fvalue xs = 1 + 2 * fvalue ys at hval
        congr 1; exact ih (by omega) (by omega)

lemma fvalue_ones (m : Nat) : fvalue (List.replicate m true) + 1 = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (1 + 2 * fvalue (List.replicate m true)) + 1 = 2 ^ m * 2
    omega

lemma Frame_ones (m : Nat) : Frame (List.replicate m true) = p11 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, Frame, ih, pow_succ_list]
    rfl

lemma Frame_zeros (m : Nat) : Frame (List.replicate m false) = p10 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, Frame, ih, pow_succ_list]
    rfl

lemma FrameInc (bs : List Bool) (h : fvalue bs + 1 < 2 ^ bs.length)
    (l r : ListBlank (Fin 2)) :
    (l {{B}}> (Frame bs +> r)) [target_tm]⊢⁺ (l <{{D}} (Frame (finc bs) +> r)) := by
  induction bs generalizing l with
  | nil => simp [fvalue] at h
  | cons b bs ih =>
    cases b
    · change (l {{B}}> (p10 +> (Frame bs +> r))) [target_tm]⊢⁺ (l <{{D}} (p11 +> (Frame bs +> r)))
      exact StackFirst l (Frame bs +> r)
    · change 1 + 2 * fvalue bs + 1 < 2 ^ bs.length * 2 at h
      have hbs : fvalue bs + 1 < 2 ^ bs.length := by omega
      change (l {{B}}> (p11 +> (Frame bs +> r))) [target_tm]⊢⁺ (l <{{D}} (p10 +> (Frame (finc bs) +> r)))
      exact stepPlus_trans (StackLast l (Frame bs +> r))
        (stepPlus_trans (ih hbs (l <+ p11)) (StackEnter l (Frame (finc bs) +> r)))

lemma FrameWalkCalls (q : Nat) {xs ys : List Bool} {l l' : ListBlank (Fin 2)}
    (hlen : xs.length = ys.length) (hval : fvalue xs + q = fvalue ys)
    (hps : sidePs q l l') (r : ListBlank (Fin 2)) :
    (l <{{D}} (Frame xs +> r)) [target_tm]⊢* (l' <{{D}} (Frame ys +> r)) := by
  induction q generalizing xs l with
  | zero =>
    have hxy : xs = ys := fvalue_injective hlen (by omega)
    subst hxy; subst hps
    exact stepStar_refl _
  | succ q ih =>
    rcases hps with ⟨lm, hp, hps'⟩
    have hys_bound := fvalue_bound ys
    rw [← hlen] at hys_bound
    have hxs_inc : fvalue xs + 1 < 2 ^ xs.length := by omega
    have hlen' : (finc xs).length = ys.length := by rw [finc_length, hlen]
    have hval' : fvalue (finc xs) + q = fvalue ys := by rw [fvalue_finc xs hxs_inc]; omega
    exact stepStar_trans (stepPlus_to_stepStar (hp (Frame xs +> r)))
      (stepStar_trans (stepPlus_to_stepStar (FrameInc xs hxs_inc lm r))
        (ih hlen' hval' hps'))

lemma Descend (m : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ p11 ^ m) <{{D}} r) [target_tm]⊢*
    (l <{{D}} (Frame (List.replicate m false) +> r)) := by
  rw [Frame_zeros]
  induction m generalizing r with
  | zero => exact stepStar_refl _
  | succ m ih =>
    rw [left_pow_succ l p11 m]
    refine stepStar_trans (stepPlus_to_stepStar (StackEnter (l <+ p11 ^ m) r)) ?_
    refine stepStar_trans (ih (p10 +> r)) ?_
    rw [← right_pow_succ_right p10 m r]
    exact stepStar_refl _

lemma Drain (q : Nat) (bs : List Bool) (l l' r : ListBlank (Fin 2))
    (hval : fvalue bs + q + 1 = 2 ^ bs.length) (hps : sidePs (q + 1) l l') :
    (l <{{D}} (Frame bs +> r)) [target_tm]⊢⁺
    ((l' <+ p11 ^ bs.length) {{B}}> r) := by
  rcases sidePs_snoc hps with ⟨lm, hps_q, hp_last⟩
  have hlen : bs.length = (List.replicate bs.length true).length := by simp
  have hval_ones : fvalue bs + q = fvalue (List.replicate bs.length true) := by
    have := fvalue_ones bs.length; omega
  have hwalk := FrameWalkCalls q hlen hval_ones hps_q r
  rw [Frame_ones] at hwalk
  have hcall := hp_last (p11 ^ bs.length +> r)
  have hret := LastReturn bs.length l' r
  exact stepStar_stepPlus_trans hwalk (stepPlus_stepStar_trans hcall hret)

lemma Double {l lm l' : ListBlank (Fin 2)} (h₁ : sideP l lm) (h₂ : sideP lm l') :
    sideP (l <+ p11) (l' <+ p11) := by
  intro r
  exact stepPlus_trans (StackEnter l r)
    (stepPlus_trans (h₁ (p10 +> r))
      (stepPlus_trans (StackFirst lm r)
        (stepPlus_trans (h₂ (p11 +> r)) (StackLast l' r))))

lemma Double_ps (q : Nat) {l l' : ListBlank (Fin 2)} (h : sidePs (q * 2) l l') :
    sidePs q (l <+ p11) (l' <+ p11) := by
  induction q generalizing l with
  | zero =>
    change l = l' at h
    subst h; rfl
  | succ q ih =>
    rw [show (q + 1) * 2 = q * 2 + 1 + 1 by omega] at h
    rcases h with ⟨lm₁, hp₁, lm₂, hp₂, hps⟩
    exact ⟨lm₂ <+ p11, Double hp₁ hp₂, ih hps⟩

lemma Multiplier (n q : Nat) {l l' : ListBlank (Fin 2)} (h : sidePs (q * 2 ^ n) l l') :
    sidePs q (l <+ p11 ^ n) (l' <+ p11 ^ n) := by
  induction n generalizing q with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one] at h
    simpa using h
  | succ n ih =>
    rw [left_pow_succ l p11 n, left_pow_succ l' p11 n]
    apply Double_ps
    apply ih (q * 2)
    rwa [show q * 2 * 2 ^ n = q * 2 ^ (n + 1) by rw [Nat.pow_succ]; ring]

-- ============================================================================
-- Section 5: Entry Family, Bit Budgets & Reentry Bridges (Entry / TM6Bits / TM6Reentry)
-- ============================================================================

def bnat (b : Bool) : Nat := if b then 1 else 0

def sparse : List Bool → List (Fin 2)
  | [] => []
  | b :: w => (if b then d1 else d0) ++ sparse w

def doubled : List Bool → List (Fin 2)
  | [] => []
  | b :: w => (if b then d2 else d0) ++ doubled w

def E_cfg (b : Bool) (w : List Bool) : Cfg (Fin 2) (Fin 6) :=
  ((default <+ one_tok ^ (1 + bnat b) <+ [0, 0, 0] <+ sparse w <+ U0 <+
    p11 ^ (w.length * 2 + 3 + bnat b)) <{{D}} (p11 +> default))

def next_word (b : Bool) (w : List Bool) : List Bool :=
  List.replicate (w.length + bnat b) false ++ [true] ++ w ++ [false]

def evalue : List Bool → Nat
  | [] => 0
  | b :: w => bnat b + evalue w * 4

lemma evalue_app (u v : List Bool) :
    evalue (u ++ v) = evalue u + evalue v * 4 ^ u.length := by
  induction u with
  | nil => simp [evalue]
  | cons b u ih =>
    simp only [List.cons_append, evalue, List.length_cons, ih, Nat.pow_succ]
    ring

lemma evalue_zeroes (n : Nat) : evalue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, evalue, bnat, ih]

lemma sparse_app (u v : List Bool) : sparse (u ++ v) = sparse u ++ sparse v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [sparse, ih]

lemma doubled_app (u v : List Bool) : doubled (u ++ v) = doubled u ++ doubled v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [doubled, ih]

lemma sparse_shift (w : List Bool) : ([0] : List (Fin 2)) ++ sparse w = doubled w ++ [0] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp only [sparse, doubled, d0, d1, d2, List.cons_append, List.nil_append]
    · exact congrArg (fun xs => (0 : Fin 2) :: 0 :: 0 :: 0 :: xs) ih
    · exact congrArg (fun xs => (0 : Fin 2) :: 1 :: 0 :: 0 :: xs) ih

lemma init_step_1 :
    (init ([] : List (Fin 2))) [target_tm]⊢*
    ((default <+ [1, 1, 0, 0, 0, 1, 1]) <{{D}} ([1, 1, 1, 1] +> default)) :=
  ⟨79, by run_steps 79⟩

lemma init_step_2 :
    ((default <+ [1, 1, 0, 0, 0, 1, 1]) <{{D}} ([1, 1, 1, 1] +> default)) [target_tm]⊢*
    ((default <+ [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1]) <{{D}} ([1, 1, 1, 1] +> default)) :=
  ⟨81, by run_steps 81⟩

lemma init_step_3 :
    ((default <+ [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1]) <{{D}} ([1, 1, 1, 1] +> default)) [target_tm]⊢*
    ((default <+ [1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1]) <{{D}} ([1, 1, 1, 1, 1, 1] +> default)) :=
  ⟨78, by run_steps 78⟩

lemma init_step_4 :
    ((default <+ [1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1]) <{{D}} ([1, 1, 1, 1, 1, 1] +> default)) [target_tm]⊢*
    ((default <+ [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1]) <{{D}} ([1, 1] +> default)) :=
  ⟨87, by run_steps 87⟩

lemma init_step_5 :
    ((default <+ [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1]) <{{D}} ([1, 1] +> default)) [target_tm]⊢*
    ((default <+ [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1]) <{{D}} ([1, 1, 1, 1] +> default)) :=
  ⟨164, by run_steps 164⟩

lemma init_step_6 :
    ((default <+ [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1]) <{{D}} ([1, 1, 1, 1] +> default)) [target_tm]⊢*
    E_cfg false [true] := by
  unfold E_cfg bnat sparse
  exact ⟨175, by run_steps 175⟩

lemma Entry_init : (init ([] : List (Fin 2))) [target_tm]⊢* E_cfg false [true] :=
  stepStar_trans init_step_1
    (stepStar_trans init_step_2
      (stepStar_trans init_step_3
        (stepStar_trans init_step_4
          (stepStar_trans init_step_5 init_step_6))))

def exit_bits (b : Bool) (w : List Bool) : List Bool :=
  (w.flatMap fun d => [true, !d]) ++ [true, true, true] ++ List.replicate (bnat b) false

lemma exit_bits_length (b : Bool) (w : List Bool) :
    (exit_bits b w).length = w.length * 2 + 3 + bnat b := by
  induction w with
  | nil =>
    simp only [exit_bits, List.flatMap_nil, List.nil_append, List.cons_append,
      List.length_cons, List.length_replicate, List.length_nil]
    omega
  | cons d w ih =>
    simp only [exit_bits] at ih ⊢
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons]
    omega

lemma exit_bits_value (b : Bool) (w : List Bool) :
    2 * evalue w + fvalue (exit_bits b w) + 1 = 2 * 4 ^ (w.length + 1) := by
  induction w with
  | nil => cases b <;> rfl
  | cons d w ih =>
    simp only [exit_bits] at ih ⊢
    cases d
    · change 2 * (0 + evalue w * 4) + (1 + 2 * (1 + 2 * fvalue
        (List.flatMap (fun d => [true, !d]) w ++ [true, true, true] ++ List.replicate (bnat b) false))) + 1 =
        2 * (4 ^ (w.length + 1) * 4)
      omega
    · change 2 * (1 + evalue w * 4) + (1 + 2 * (0 + 2 * fvalue
        (List.flatMap (fun d => [true, !d]) w ++ [true, true, true] ++ List.replicate (bnat b) false))) + 1 =
        2 * (4 ^ (w.length + 1) * 4)
      omega

def reentry_radius (b : Bool) (w : List Bool) : Nat := w.length * 2 + 1 + bnat b

def reentry_bits (b : Bool) (w : List Bool) : List Bool :=
  [true] ++ List.replicate (reentry_radius b w) false ++ [true] ++ exit_bits b w ++ [true]

lemma reentry_bits_length (b : Bool) (w : List Bool) :
    (reentry_bits b w).length = w.length * 4 + 7 + bnat b * 2 := by
  simp only [reentry_bits, List.length_append, List.length_replicate,
    exit_bits_length, reentry_radius, List.length_cons, List.length_nil]
  omega

lemma reentry_bits_length_parts (b : Bool) (w : List Bool) :
    (reentry_bits b w).length = reentry_radius b w + (exit_bits b w).length + 3 := by
  simp only [reentry_bits, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

lemma reentry_bits_value (b : Bool) (w : List Bool) :
    fvalue (reentry_bits b w) = 1 + 2 ^ (reentry_radius b w + 1) *
      (1 + 2 * fvalue (exit_bits b w) + 2 ^ ((exit_bits b w).length + 1)) := by
  have hb1 : bval true = 1 := rfl
  simp only [reentry_bits, List.append_assoc, fvalue_app, fvalue_zeros,
    List.length_replicate, fvalue, hb1, List.length_cons, List.length_nil, Nat.pow_succ, Nat.pow_zero]
  ring

lemma pow2_twice (k : Nat) : 2 ^ (k * 2) = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show (k + 1) * 2 = k * 2 + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ, ih, Nat.pow_succ]
    ring

lemma pow2_exit_length (b : Bool) (k : Nat) :
    2 ^ (k * 2 + 3 + bnat b + 1) = (1 + bnat b) * 4 ^ (k + 2) := by
  cases b
  · change 2 ^ (k * 2 + 3 + 0 + 1) = (1 + 0) * 4 ^ (k + 2)
    rw [show k * 2 + 3 + 0 + 1 = (k + 2) * 2 by omega, pow2_twice]; ring
  · change 2 ^ (k * 2 + 3 + 1 + 1) = (1 + 1) * 4 ^ (k + 2)
    rw [show k * 2 + 3 + 1 + 1 = (k + 2) * 2 + 1 by omega, Nat.pow_succ, pow2_twice]; ring

def drain_A (b : Bool) (w : List Bool) : Nat := 4 * evalue w + 1 + bnat b * 4 ^ (w.length + 2)
def drain_q (b : Bool) (w : List Bool) : Nat := drain_A b w * 2 ^ (reentry_radius b w + 1) - 2

lemma exit_budget_identity (b : Bool) (w : List Bool) :
    drain_A b w + 2 * fvalue (exit_bits b w) + 1 = 2 ^ ((exit_bits b w).length + 1) := by
  have he := exit_bits_value b w
  rw [exit_bits_length, pow2_exit_length]
  unfold drain_A
  rw [show w.length + 2 = (w.length + 1) + 1 by omega, Nat.pow_succ]
  cases b
  · change 4 * evalue w + 1 + 0 * (4 ^ (w.length + 1) * 4) + 2 * fvalue (exit_bits false w) + 1 =
      (1 + 0) * (4 ^ (w.length + 1) * 4)
    omega
  · change 4 * evalue w + 1 + 1 * (4 ^ (w.length + 1) * 4) + 2 * fvalue (exit_bits true w) + 1 =
      (1 + 1) * (4 ^ (w.length + 1) * 4)
    omega

lemma drain_budget (b : Bool) (w : List Bool) :
    fvalue (reentry_bits b w) + drain_q b w + 1 = 2 ^ (reentry_bits b w).length := by
  have ha := exit_budget_identity b w
  have hv := reentry_bits_value b w
  rw [reentry_bits_length_parts]
  set R := 2 ^ (reentry_radius b w + 1)
  set N := 2 ^ ((exit_bits b w).length + 1)
  set j := fvalue (exit_bits b w)
  set a := drain_A b w
  have ha_pos : 1 ≤ a := by unfold a drain_A; omega
  have hR_ge : 2 ≤ R := by
    unfold R; rw [Nat.pow_succ]
    have := Nat.one_le_pow (reentry_radius b w) 2 (by omega)
    omega
  have hprod : 2 ≤ a * R := by nlinarith
  have hpow_end : 2 ^ (reentry_radius b w + (exit_bits b w).length + 3) = R * N * 2 := by
    rw [show reentry_radius b w + (exit_bits b w).length + 3 =
      (reentry_radius b w + 1) + ((exit_bits b w).length + 1) + 1 by omega,
      Nat.pow_succ, Nat.pow_add]
  rw [hpow_end, hv]
  have h_lin : R * (1 + 2 * j + N) + a * R = R * N * 2 := by nlinarith
  change (1 + R * (1 + 2 * j + N)) + (a * R - 2) + 1 = R * N * 2
  omega

lemma Reentry0Frames (k : Nat) (bs : List Bool) :
    ((default : ListBlank (Fin 2)) <{{C}}
      (p01 ^ (k * 2 + 4) +> ([1] +> (Frame bs +> (p11 +> default))))) [target_tm]⊢⁺
    ((default <+ d1 <+ U0) <{{D}}
      (Frame ([true] ++ List.replicate (k * 2 + 1) false ++ [true] ++ bs ++ [true]) +> default)) := by
  have h_lhs : ((default : ListBlank (Fin 2)) <{{C}}
      (p01 ^ (k * 2 + 4) +> ([1] +> (Frame bs +> (p11 +> default))))) =
      ((default <+ [0, 0, 0, 0, 0, 0]) <{{C}}
        (p01 ^ 3 +> (p01 ^ (k * 2 + 1) +> ([1] +> (Frame bs +> (p11 +> default)))))) := by
    rw [show (default : ListBlank (Fin 2)) <+ [0, 0, 0, 0, 0, 0] = default by simp]
    rw [show k * 2 + 4 = 3 + (k * 2 + 1) by omega, right_pow_add p01 3 (k * 2 + 1)]
  have h_rhs : ((default <+ [1, 1, 0, 0, 0, 1, 0, 0, 0]) <{{D}}
      ([1, 1, 1] +> (p01 ^ (k * 2 + 1) +> ([1] +> (Frame bs +> (p11 +> default)))))) =
      ((default <+ d1 <+ U0) <{{D}}
        (Frame ([true] ++ List.replicate (k * 2 + 1) false ++ [true] ++ bs ++ [true]) +> default)) := by
    have h_l : (default : ListBlank (Fin 2)) <+ [1, 1, 0, 0, 0, 1, 0, 0, 0] = default <+ d1 <+ U0 := rfl
    have h_r : ([1, 1, 1] : List (Fin 2)) +> (p01 ^ (k * 2 + 1) +> ([1] +> (Frame bs +> (p11 +> default)))) =
        Frame ([true] ++ List.replicate (k * 2 + 1) false ++ [true] ++ bs ++ [true]) +> default := by
      simp only [List.append_assoc, Frame_app, Frame_zeros, listblank_append_assoc]
      have h_f1 : Frame [true] = [1, 1] := rfl
      rw [h_f1]
      change ([1, 1] : List (Fin 2)) +> ([1] +> (p01 ^ (k * 2 + 1) +> ([1] +> (Frame bs +> (p11 +> default))))) =
        ([1, 1] : List (Fin 2)) +> (p10 ^ (k * 2 + 1) +> ([1] +> ([1] +> (Frame bs +> (p11 +> default)))))
      rw [one_zero_pow_shift]
    rw [h_l, h_r]
  rw [h_lhs, ← h_rhs]
  exact Reentry0 default _

lemma Reentry1Frames (k : Nat) (bs : List Bool) :
    ((default <+ [1]) <{{C}}
      (p01 ^ (k * 2 + 4) +> ([1] +> (Frame bs +> (p11 +> default))))) [target_tm]⊢⁺
    ((default <+ U1) <{{D}}
      (Frame ([true] ++ List.replicate (k * 2 + 2) false ++ [true] ++ bs ++ [true]) +> default)) := by
  have h_lhs : ((default <+ [1]) <{{C}}
      (p01 ^ (k * 2 + 4) +> ([1] +> (Frame bs +> (p11 +> default))))) =
      ((default <+ [1, 0, 0, 0]) <{{C}}
        (p01 ^ 2 +> (p01 ^ (k * 2 + 2) +> ([1] +> (Frame bs +> (p11 +> default)))))) := by
    rw [show (default : ListBlank (Fin 2)) <+ [1, 0, 0, 0] = default <+ [1] by simp]
    rw [show k * 2 + 4 = 2 + (k * 2 + 2) by omega, right_pow_add p01 2 (k * 2 + 2)]
  have h_rhs : ((default <+ U1) <{{D}}
      ([1, 1, 1] +> (p01 ^ (k * 2 + 2) +> ([1] +> (Frame bs +> (p11 +> default)))))) =
      ((default <+ U1) <{{D}}
        (Frame ([true] ++ List.replicate (k * 2 + 2) false ++ [true] ++ bs ++ [true]) +> default)) := by
    have h_r : ([1, 1, 1] : List (Fin 2)) +> (p01 ^ (k * 2 + 2) +> ([1] +> (Frame bs +> (p11 +> default)))) =
        Frame ([true] ++ List.replicate (k * 2 + 2) false ++ [true] ++ bs ++ [true]) +> default := by
      simp only [List.append_assoc, Frame_app, Frame_zeros, listblank_append_assoc]
      have h_f1 : Frame [true] = [1, 1] := rfl
      rw [h_f1]
      change ([1, 1] : List (Fin 2)) +> ([1] +> (p01 ^ (k * 2 + 2) +> ([1] +> (Frame bs +> (p11 +> default))))) =
        ([1, 1] : List (Fin 2)) +> (p10 ^ (k * 2 + 2) +> ([1] +> ([1] +> (Frame bs +> (p11 +> default)))))
      rw [one_zero_pow_shift]
    rw [h_r]
  rw [h_lhs, ← h_rhs]
  exact Reentry1 default _

-- ============================================================================
-- Section 6: Cycle Closure & Non-Halting (TM6Cycle / TM6Target / TM6Outer)
-- ============================================================================

lemma sparse_RC (w : List Bool) : RC (evalue w) (default <+ sparse w) := by
  induction w with
  | nil => exact RC.zero
  | cons b w ih =>
    cases b
    · change RC (0 + evalue w * 4) (default <+ sparse w <+ d0)
      rw [show 0 + evalue w * 4 = 4 * evalue w by omega]
      exact RC.d0 (evalue w) (default <+ sparse w) ih
    · change RC (1 + evalue w * 4) (default <+ sparse w <+ d1)
      rw [show 1 + evalue w * 4 = 1 + 4 * evalue w by omega]
      exact RC.d1 (evalue w) (default <+ sparse w) ih

lemma doubled_RC (w : List Bool) : RC (evalue w * 2) (default <+ doubled w) := by
  induction w with
  | nil => exact RC.zero
  | cons b w ih =>
    cases b
    · change RC ((0 + evalue w * 4) * 2) (default <+ doubled w <+ d0)
      rw [show (0 + evalue w * 4) * 2 = 4 * (evalue w * 2) by omega]
      exact RC.d0 (evalue w * 2) (default <+ doubled w) ih
    · change RC ((1 + evalue w * 4) * 2) (default <+ doubled w <+ d2)
      rw [show (1 + evalue w * 4) * 2 = 2 + 4 * (evalue w * 2) by omega]
      exact RC.d2 (evalue w * 2) (default <+ doubled w) ih

lemma sparse_FC (w : List Bool) (tail : ListBlank (Fin 2)) :
    FC tail w.length (evalue w) (tail <+ [0, 0, 0] <+ sparse w) := by
  induction w with
  | nil => exact FC.t0
  | cons b w ih =>
    cases b
    · change FC tail (w.length + 1) (0 + evalue w * 4) (tail <+ [0, 0, 0] <+ sparse w <+ d0)
      rw [show 0 + evalue w * 4 = 4 * evalue w by omega]
      exact FC.d0 w.length (evalue w) (tail <+ [0, 0, 0] <+ sparse w) ih
    · change FC tail (w.length + 1) (1 + evalue w * 4) (tail <+ [0, 0, 0] <+ sparse w <+ d1)
      rw [show 1 + evalue w * 4 = 1 + 4 * evalue w by omega]
      exact FC.d1 w.length (evalue w) (tail <+ [0, 0, 0] <+ sparse w) ih

lemma FC_last (k : Nat) (tail : ListBlank (Fin 2)) :
    FC tail k (4 ^ (k + 1) - 1) (tail <+ [1, 1, 0] <+ d3 ^ k) := by
  induction k with
  | zero => exact FC.t3
  | succ k ih =>
    rw [left_pow_succ (tail <+ [1, 1, 0]) d3 k]
    have hpow : 4 ^ (k + 1 + 1) - 1 = 3 + 4 * (4 ^ (k + 1) - 1) := by
      rw [Nat.pow_succ (4 : Nat) (k + 1)]
      have := Nat.one_le_pow (k + 1) 4 (by omega)
      omega
    rw [hpow]
    exact FC.d3 k (4 ^ (k + 1) - 1) (tail <+ [1, 1, 0] <+ d3 ^ k) ih

lemma FNC_last (k : Nat) (tail : ListBlank (Fin 2)) :
    FNC tail k (2 * 4 ^ (k + 1) - 1) (tail <+ [1, 1, 0] <+ d3 ^ k <+ U1) := by
  have hpow : 2 * 4 ^ (k + 1) - 1 = 1 + 2 * (4 ^ (k + 1) - 1) := by
    have := Nat.one_le_pow (k + 1) 4 (by omega)
    omega
  rw [hpow]
  exact FNC.u1 (4 ^ (k + 1) - 1) (tail <+ [1, 1, 0] <+ d3 ^ k) (FC_last k tail)

lemma FirstExit {n k v : Nat} {bs : List Bool} {l x r : ListBlank (Fin 2)}
    (hx : FNC (l <+ [1]) k v x) (hlen : bs.length = n)
    (hval : v + fvalue bs + 1 = 2 * 4 ^ (k + 1)) :
    ((x <+ p11 ^ n) <{{D}} r) [target_tm]⊢⁺
    (l <{{C}} (p01 ^ (k * 2 + 4) +> ([1] +> (Frame bs +> r)))) := by
  have hdesc := Descend n x r
  have hlen_z : (List.replicate n false).length = bs.length := by simp [hlen]
  have hval_z : fvalue (List.replicate n false) + fvalue bs = fvalue bs := by
    rw [fvalue_zeros, Nat.zero_add]
  have htarget : FNC (l <+ [1]) k (v + fvalue bs) (l <+ [1] <+ [1, 1, 0] <+ d3 ^ k <+ U1) := by
    rw [show v + fvalue bs = 2 * 4 ^ (k + 1) - 1 by omega]
    exact FNC_last k (l <+ [1])
  have hadds := FiniteAdds (fvalue bs) hx htarget (by omega)
  have hwalk := FrameWalkCalls (fvalue bs) hlen_z hval_z hadds r
  have hovf := TerminalOverflow l (Frame bs +> r) k
  have h_eq : l <+ [1] <+ [1, 1, 0] = l <+ [1, 1, 0, 1] := rfl
  rw [h_eq] at hwalk
  exact stepStar_stepPlus_trans (stepStar_trans hdesc hwalk) hovf

lemma E_exit (b : Bool) (w : List Bool) :
    (E_cfg b w) [target_tm]⊢⁺
    ((default <+ one_tok ^ (bnat b)) <{{C}}
      (p01 ^ (w.length * 2 + 4) +>
        ([1] +> (Frame (exit_bits b w) +> (p11 +> default))))) := by
  unfold E_cfg
  rw [show 1 + bnat b = bnat b + 1 by omega, left_pow_succ default one_tok (bnat b)]
  refine FirstExit ?_ (exit_bits_length b w) (exit_bits_value b w)
  exact FNC.u0 (evalue w) _ (sparse_FC w (default <+ one_tok ^ (bnat b) <+ one_tok))

def reentry_left (b : Bool) : ListBlank (Fin 2) :=
  if b then default <+ U1 else default <+ d1 <+ U0

lemma reentry_normal (b : Bool) : NC (2 - bnat b) (reentry_left b) := by
  cases b <;> unfold reentry_left bnat
  · change NC (2 * (1 + 4 * 0)) (default <+ d1 <+ U0)
    exact NC.u0 1 (default <+ d1) (RC.d1 0 default RC.zero)
  · change NC (1 + 2 * 0) (default <+ U1)
    exact NC.u1 0 default RC.zero

lemma E_reentry (b : Bool) (w : List Bool) :
    (E_cfg b w) [target_tm]⊢⁺
    ((reentry_left b) <{{D}} (Frame (reentry_bits b w) +> default)) := by
  refine stepPlus_trans (E_exit b w) ?_
  cases b <;> unfold reentry_left reentry_bits reentry_radius bnat
  · exact Reentry0Frames w.length (exit_bits false w)
  · exact Reentry1Frames w.length (exit_bits true w)

lemma E_drain (b : Bool) (w : List Bool) :
    ∃ l, NC ((2 - bnat b) + (drain_q b w + 1)) l ∧
      (E_cfg b w) [target_tm]⊢⁺
      ((l <+ p11 ^ (w.length * 4 + 7 + bnat b * 2)) {{B}}> default) := by
  rcases NormalAdds_ex (drain_q b w + 1) (reentry_normal b) with ⟨l, hnc, hps⟩
  refine ⟨l, hnc, stepPlus_trans (E_reentry b w) ?_⟩
  rw [← reentry_bits_length b w]
  exact Drain (drain_q b w) (reentry_bits b w) (reentry_left b) l default (drain_budget b w) hps

lemma sparse_with_tail_RC (t : List Bool) {n : Nat} {l : ListBlank (Fin 2)} (hl : RC n l) :
    RC (evalue t + n * 4 ^ t.length) (l <+ sparse t) := by
  induction t with
  | nil =>
    simp only [evalue, sparse, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.zero_add,
      listblank_append_nil]
    exact hl
  | cons b t ih =>
    cases b
    · change RC ((0 + evalue t * 4) + n * (4 ^ t.length * 4)) (l <+ sparse t <+ d0)
      rw [show (0 + evalue t * 4) + n * (4 ^ t.length * 4) = 4 * (evalue t + n * 4 ^ t.length) by ring]
      exact RC.d0 _ _ ih
    · change RC ((1 + evalue t * 4) + n * (4 ^ t.length * 4)) (l <+ sparse t <+ d1)
      rw [show (1 + evalue t * 4) + n * (4 ^ t.length * 4) = 1 + 4 * (evalue t + n * 4 ^ t.length) by ring]
      exact RC.d1 _ _ ih

lemma doubled_with_tail_RC (t : List Bool) {n : Nat} {l : ListBlank (Fin 2)} (hl : RC n l) :
    RC (2 * evalue t + n * 4 ^ t.length) (l <+ doubled t) := by
  induction t with
  | nil =>
    change RC (2 * 0 + n * 1) l
    rw [show 2 * 0 + n * 1 = n by omega]
    exact hl
  | cons b t ih =>
    cases b
    · change RC (2 * (0 + evalue t * 4) + n * (4 ^ t.length * 4)) (l <+ doubled t <+ d0)
      rw [show 2 * (0 + evalue t * 4) + n * (4 ^ t.length * 4) = 4 * (2 * evalue t + n * 4 ^ t.length) by ring]
      exact RC.d0 _ _ ih
    · change RC (2 * (1 + evalue t * 4) + n * (4 ^ t.length * 4)) (l <+ doubled t <+ d2)
      rw [show 2 * (1 + evalue t * 4) + n * (4 ^ t.length * 4) = 2 + 4 * (2 * evalue t + n * 4 ^ t.length) by ring]
      exact RC.d2 _ _ ih

def core (b : Bool) (w : List Bool) : List Bool :=
  List.replicate (w.length + bnat b) false ++ [true] ++ w

lemma core_length (b : Bool) (w : List Bool) :
    (core b w).length = w.length * 2 + 1 + bnat b := by
  simp only [core, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

lemma next_word_core (b : Bool) (w : List Bool) :
    next_word b w = core b w ++ [false] := by
  simp [next_word, core, List.append_assoc]

lemma core_value (b : Bool) (w : List Bool) :
    evalue (core b w) = (4 * evalue w + 1) * 4 ^ (w.length + bnat b) := by
  have hb1 : bnat true = 1 := rfl
  simp only [core, List.append_assoc, evalue_app, evalue_zeroes, List.length_replicate,
    evalue, hb1, List.length_cons, List.length_nil, Nat.pow_succ, Nat.pow_zero]
  ring

lemma drain_joint_value (b : Bool) (w : List Bool) :
    (2 - bnat b) + (drain_q b w + 1) =
    drain_A b w * 2 ^ (reentry_radius b w + 1) + 1 - bnat b := by
  have ha : 1 ≤ drain_A b w := by unfold drain_A; omega
  have hr : 2 ≤ 2 ^ (reentry_radius b w + 1) := by
    rw [Nat.pow_succ]; have := Nat.one_le_pow (reentry_radius b w) 2 (by omega); omega
  have hprod : 2 ≤ drain_A b w * 2 ^ (reentry_radius b w + 1) := by nlinarith
  unfold drain_q
  cases b
  · change (2 - 0) + (drain_A false w * 2 ^ (reentry_radius false w + 1) - 2 + 1) =
      drain_A false w * 2 ^ (reentry_radius false w + 1) + 1 - 0
    omega
  · change (2 - 1) + (drain_A true w * 2 ^ (reentry_radius true w + 1) - 2 + 1) =
      drain_A true w * 2 ^ (reentry_radius true w + 1) + 1 - 1
    omega

lemma drain_core_value (b : Bool) (w : List Bool) :
    (2 - bnat b) + (drain_q b w + 1) =
    if b then 2 * (evalue (core b w) + 4 ^ ((core b w).length + 1))
         else 1 + 4 * evalue (core b w) := by
  rw [drain_joint_value]
  cases b
  · rw [core_value, drain_A, reentry_radius]
    change (4 * evalue w + 1 + 0 * 4 ^ (w.length + 2)) * 2 ^ (w.length * 2 + 1 + 0 + 1) + 1 =
      1 + 4 * ((4 * evalue w + 1) * 4 ^ (w.length + 0))
    rw [show w.length * 2 + 1 + 0 + 1 = (w.length + 1) * 2 by omega, pow2_twice,
      Nat.add_zero, Nat.pow_succ]
    ring
  · rw [core_value, core_length, drain_A, reentry_radius]
    change (4 * evalue w + 1 + 1 * 4 ^ (w.length + 2)) * 2 ^ (w.length * 2 + 1 + 1 + 1) =
      2 * ((4 * evalue w + 1) * 4 ^ (w.length + 1) + 4 ^ (w.length * 2 + 1 + 1 + 1))
    have hp2 : 2 ^ (w.length * 2 + 1 + 1 + 1) = 2 * 4 ^ (w.length + 1) := by
      rw [show w.length * 2 + 1 + 1 + 1 = (w.length + 1) * 2 + 1 by omega, Nat.pow_succ, pow2_twice]
      ring
    have hp4 : 4 ^ (w.length * 2 + 1 + 1 + 1) = 4 ^ (w.length + 2) * 4 ^ (w.length + 1) := by
      rw [show w.length * 2 + 1 + 1 + 1 = (w.length + 2) + (w.length + 1) by omega, Nat.pow_add]
    rw [hp2, hp4]
    ring

def outer_left (b : Bool) (t : List Bool) : ListBlank (Fin 2) :=
  if b then default <+ d1 <+ d0 <+ sparse t <+ U0
       else default <+ doubled t <+ U1

lemma outer_left_false_NC (t : List Bool) :
    NC (1 + 4 * evalue t) (outer_left false t) := by
  unfold outer_left
  rw [show 1 + 4 * evalue t = 1 + 2 * (evalue t * 2) by ring]
  exact NC.u1 (evalue t * 2) (default <+ doubled t) (doubled_RC t)

lemma outer_left_true_NC (t : List Bool) :
    NC (2 * (evalue t + 4 ^ (t.length + 1))) (outer_left true t) := by
  unfold outer_left
  have hr4 : RC 4 (default <+ d1 <+ d0) := RC.d0 1 (default <+ d1) (RC.d1 0 default RC.zero)
  have hst := sparse_with_tail_RC t hr4
  rw [show 2 * (evalue t + 4 ^ (t.length + 1)) = 2 * (evalue t + 4 * 4 ^ t.length) by
    rw [Nat.pow_succ]; ring]
  exact NC.u0 (evalue t + 4 * 4 ^ t.length) _ hst

lemma drain_target_NC (b : Bool) (w : List Bool) :
    NC ((2 - bnat b) + (drain_q b w + 1)) (outer_left b (core b w)) := by
  rw [drain_core_value]
  cases b
  · exact outer_left_false_NC (core false w)
  · exact outer_left_true_NC (core true w)

lemma Batch (n v : Nat) (l l' r : ListBlank (Fin 2))
    (hl : NC v l) (hl' : NC (v + 2 ^ n) l') :
    ((l <+ p11 ^ n) <{{D}} r) [target_tm]⊢⁺
    ((l' <+ p11 ^ n) {{B}}> r) := by
  have hadds : sidePs (1 * 2 ^ n) l l' := by
    rw [Nat.one_mul]
    exact NormalAdds (2 ^ n) hl hl'
  have hmul := Multiplier n 1 hadds
  rcases hmul with ⟨lm, hp, rfl⟩
  exact hp r

lemma Shift (t : List Bool) (l : ListBlank (Fin 2)) :
    l <+ [0] <+ doubled t = l <+ sparse t <+ [0] := by
  rw [← listblank_append_assoc, ← sparse_shift, listblank_append_assoc]

lemma Blank0 (n : Nat) (t : List Bool) (l : ListBlank (Fin 2)) :
    ((l <+ sparse t <+ U0 <+ p11 ^ (n + 1)) {{B}}> default) [target_tm]⊢⁺
    ((l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n) <{{D}} (p11 +> default)) := by
  have h_eq : l <+ sparse t <+ U0 <+ p11 ^ (n + 1) =
      l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n <+ [1] := by
    rw [Shift, left_pow_succ_right _ p11 n]
    have h_u : l <+ sparse t <+ U0 <+ p11 = l <+ sparse t <+ [0] <+ U1 <+ [1] := rfl
    rw [h_u, one_one_pow_shift]
  have h_step := Restart0 (l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n) default
  rw [show ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default by simp] at h_step
  rwa [h_eq]

lemma Blank1 (n : Nat) (t : List Bool) (l : ListBlank (Fin 2)) :
    ((l <+ [0] <+ doubled t <+ U1 <+ p11 ^ (n + 1)) {{B}}> default) [target_tm]⊢⁺
    ((l <+ sparse t <+ U0 <+ p11 ^ (n + 1)) <{{D}} (p11 +> default)) := by
  have h_eq : l <+ [0] <+ doubled t <+ U1 <+ p11 ^ (n + 1) =
      l <+ sparse t <+ U0 <+ p11 ^ (n + 1) <+ [1] := by
    rw [Shift]
    have h_u : l <+ sparse t <+ [0] <+ U1 = l <+ sparse t <+ U0 <+ [1] := rfl
    rw [h_u, one_one_pow_shift]
  have h_step := Restart0 (l <+ sparse t <+ U0 <+ p11 ^ (n + 1)) default
  rw [show ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default by simp] at h_step
  rwa [h_eq]

lemma Boundary0 (n : Nat) (t : List Bool) (l : ListBlank (Fin 2)) :
    ((l <+ sparse t <+ U0 <+ p11 ^ n) {{B}}> (p11 +> default)) [target_tm]⊢⁺
    ((l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n) <{{D}} (p11 +> default)) := by
  have h_eq : l <+ sparse t <+ U0 <+ p11 ^ n <+ [1] =
      l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n := by
    rw [Shift, one_one_pow_shift]
    rfl
  have h_r : p11 +> (default : ListBlank (Fin 2)) = [1, 1, 0] +> default := by simp [p11]
  rw [← h_eq]
  have h_step := Restart11 (l <+ sparse t <+ U0 <+ p11 ^ n) default
  rwa [← h_r] at h_step

lemma Boundary1 (n : Nat) (t : List Bool) (l : ListBlank (Fin 2)) :
    ((l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n) {{B}}> (p11 +> default)) [target_tm]⊢⁺
    ((l <+ sparse t <+ U0 <+ p11 ^ (n + 1)) <{{D}} (p11 +> default)) := by
  have h_eq : l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n <+ [1] =
      l <+ sparse t <+ U0 <+ p11 ^ (n + 1) := by
    rw [Shift, one_one_pow_shift, left_pow_succ_right _ p11 n]
    rfl
  have h_r : p11 +> (default : ListBlank (Fin 2)) = [1, 1, 0] +> default := by simp [p11]
  rw [← h_eq]
  have h_step := Restart11 (l <+ [0] <+ doubled t <+ U1 <+ p11 ^ n) default
  rwa [← h_r] at h_step

lemma pow_batch4 (n : Nat) : 2 ^ (n * 2 + 4) = 16 * 4 ^ n := by
  rw [Nat.pow_add, pow2_twice]; ring

lemma pow_batch5 (n : Nat) : 2 ^ (n * 2 + 5) = 32 * 4 ^ n := by
  rw [Nat.pow_add, pow2_twice]; ring

lemma Outer0 (t : List Bool) :
    ((default <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 5)) {{B}}> default) [target_tm]⊢⁺
    E_cfg true (t ++ [false]) := by
  have h1 : ((default <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 5)) {{B}}> default) [target_tm]⊢⁺
      ((default <+ sparse t <+ U0 <+ p11 ^ (t.length * 2 + 5)) <{{D}} (p11 +> default)) := by
    have h1' := Blank1 (t.length * 2 + 4) t default
    rwa [show (default : ListBlank (Fin 2)) <+ [0] = default by simp,
      show t.length * 2 + 4 + 1 = t.length * 2 + 5 by omega] at h1'
  have h2 : ((default <+ sparse t <+ U0 <+ p11 ^ (t.length * 2 + 5)) <{{D}} (p11 +> default)) [target_tm]⊢⁺
      ((default <+ d1 <+ d0 <+ d0 <+ sparse t <+ U0 <+ p11 ^ (t.length * 2 + 5)) {{B}}> (p11 +> default)) := by
    refine Batch (t.length * 2 + 5) (2 * evalue t) _ _ (p11 +> default)
      (NC.u0 (evalue t) (default <+ sparse t) (sparse_RC t)) ?_
    have hrc16 : RC 16 (default <+ d1 <+ d0 <+ d0) :=
      RC.d0 4 (default <+ d1 <+ d0) (RC.d0 1 (default <+ d1) (RC.d1 0 default RC.zero))
    have hst := sparse_with_tail_RC t hrc16
    rw [pow_batch5, show 2 * evalue t + 32 * 4 ^ t.length = 2 * (evalue t + 16 * 4 ^ t.length) by ring]
    exact NC.u0 _ _ hst
  have h3 : ((default <+ d1 <+ d0 <+ d0 <+ sparse t <+ U0 <+ p11 ^ (t.length * 2 + 5)) {{B}}> (p11 +> default)) [target_tm]⊢⁺
      ((default <+ d2 <+ d0 <+ d0 <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 5)) <{{D}} (p11 +> default)) := by
    have h3' := Boundary0 (t.length * 2 + 5) (t ++ [false, false, true]) default
    have h_sp : sparse (t ++ [false, false, true]) = sparse t ++ (d0 ++ d0 ++ d1) := by
      rw [sparse_app]; rfl
    have h_db : doubled (t ++ [false, false, true]) = doubled t ++ (d0 ++ d0 ++ d2) := by
      rw [doubled_app]; rfl
    rw [h_sp, h_db] at h3'
    simp only [listblank_append_assoc] at h3'
    have h_l1 : (default : ListBlank (Fin 2)) <+ d1 <+ d0 <+ d0 = default <+ d1 <+ d0 <+ d0 := rfl
    have h_l2 : (default : ListBlank (Fin 2)) <+ [0] <+ d2 <+ d0 <+ d0 = default <+ d2 <+ d0 <+ d0 := by
      simp [d0, d2]
    rwa [h_l2] at h3'
  have h4 : ((default <+ d2 <+ d0 <+ d0 <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 5)) <{{D}} (p11 +> default)) [target_tm]⊢⁺
      ((default <+ d3 <+ d0 <+ d0 <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 5)) {{B}}> (p11 +> default)) := by
    have hrc32 : RC 32 (default <+ d2 <+ d0 <+ d0) :=
      RC.d0 8 (default <+ d2 <+ d0) (RC.d0 2 (default <+ d2) (RC.d2 0 default RC.zero))
    have hrc48 : RC 48 (default <+ d3 <+ d0 <+ d0) :=
      RC.d0 12 (default <+ d3 <+ d0) (RC.d0 3 (default <+ d3) (RC.d3 0 default RC.zero))
    refine Batch (t.length * 2 + 5) (1 + 2 * (2 * evalue t + 32 * 4 ^ t.length)) _ _ (p11 +> default)
      (NC.u1 _ _ (doubled_with_tail_RC t hrc32)) ?_
    rw [pow_batch5, show 1 + 2 * (2 * evalue t + 32 * 4 ^ t.length) + 32 * 4 ^ t.length =
      1 + 2 * (2 * evalue t + 48 * 4 ^ t.length) by ring]
    exact NC.u1 _ _ (doubled_with_tail_RC t hrc48)
  have h5 : ((default <+ d3 <+ d0 <+ d0 <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 5)) {{B}}> (p11 +> default)) [target_tm]⊢⁺
      E_cfg true (t ++ [false]) := by
    have h5' := Boundary1 (t.length * 2 + 5) (t ++ [false]) (default <+ [1, 1] <+ [0, 0, 0])
    have h_db : doubled (t ++ [false]) = doubled t ++ d0 := by rw [doubled_app]; rfl
    rw [h_db] at h5'
    simp only [listblank_append_assoc] at h5'
    have h_l1 : (default : ListBlank (Fin 2)) <+ [1, 1] <+ [0, 0, 0] <+ [0] <+ d0 =
        default <+ d3 <+ d0 <+ d0 := by simp [d0, d3]
    have h_rhs : ((default <+ [1, 1] <+ [0, 0, 0] <+ sparse (t ++ [false]) <+ U0 <+
        p11 ^ (t.length * 2 + 5 + 1)) <{{D}} (p11 +> default)) =
        E_cfg true (t ++ [false]) := by
      unfold E_cfg
      have h_b : bnat true = 1 := rfl
      have h_len : (t ++ [false]).length = t.length + 1 := by simp
      rw [h_b, h_len, show (t.length + 1) * 2 + 3 + 1 = t.length * 2 + 5 + 1 by omega]
      rfl
    rwa [h_l1, h_rhs] at h5'
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 (stepPlus_trans h4 h5)))

lemma Outer1 (t : List Bool) :
    ((default <+ d1 <+ d0 <+ sparse t <+ U0 <+ p11 ^ (t.length * 2 + 5)) {{B}}> default) [target_tm]⊢⁺
    E_cfg false (t ++ [false]) := by
  have h1 : ((default <+ d1 <+ d0 <+ sparse t <+ U0 <+ p11 ^ (t.length * 2 + 5)) {{B}}> default) [target_tm]⊢⁺
      ((default <+ d1 <+ d0 <+ [0] <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 4)) <{{D}} (p11 +> default)) := by
    have h1' := Blank0 (t.length * 2 + 4) t (default <+ d1 <+ d0)
    rwa [show t.length * 2 + 4 + 1 = t.length * 2 + 5 by omega] at h1'
  have h2 : ((default <+ d1 <+ d0 <+ [0] <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 4)) <{{D}} (p11 +> default)) [target_tm]⊢⁺
      ((default <+ d1 <+ d0 <+ d0 <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 4)) {{B}}> (p11 +> default)) := by
    have h_l1 : (default : ListBlank (Fin 2)) <+ d1 <+ d0 <+ [0] = default <+ d2 <+ d0 := by
      simp [d0, d1, d2]
    rw [h_l1]
    have hrc8 : RC 8 (default <+ d2 <+ d0) :=
      RC.d0 2 (default <+ d2) (RC.d2 0 default RC.zero)
    have hrc16 : RC 16 (default <+ d1 <+ d0 <+ d0) :=
      RC.d0 4 (default <+ d1 <+ d0) (RC.d0 1 (default <+ d1) (RC.d1 0 default RC.zero))
    refine Batch (t.length * 2 + 4) (1 + 2 * (2 * evalue t + 8 * 4 ^ t.length)) _ _ (p11 +> default)
      (NC.u1 _ _ (doubled_with_tail_RC t hrc8)) ?_
    rw [pow_batch4, show 1 + 2 * (2 * evalue t + 8 * 4 ^ t.length) + 16 * 4 ^ t.length =
      1 + 2 * (2 * evalue t + 16 * 4 ^ t.length) by ring]
    exact NC.u1 _ _ (doubled_with_tail_RC t hrc16)
  have h3 : ((default <+ d1 <+ d0 <+ d0 <+ doubled t <+ U1 <+ p11 ^ (t.length * 2 + 4)) {{B}}> (p11 +> default)) [target_tm]⊢⁺
      E_cfg false (t ++ [false]) := by
    have h3' := Boundary1 (t.length * 2 + 4) (t ++ [false]) (default <+ [1] <+ [0, 0, 0])
    have h_db : doubled (t ++ [false]) = doubled t ++ d0 := by rw [doubled_app]; rfl
    rw [h_db] at h3'
    simp only [listblank_append_assoc] at h3'
    have h_l1 : (default : ListBlank (Fin 2)) <+ [1] <+ [0, 0, 0] <+ [0] <+ d0 =
        default <+ d1 <+ d0 <+ d0 := by simp [d0, d1]
    have h_rhs : ((default <+ [1] <+ [0, 0, 0] <+ sparse (t ++ [false]) <+ U0 <+
        p11 ^ (t.length * 2 + 4 + 1)) <{{D}} (p11 +> default)) =
        E_cfg false (t ++ [false]) := by
      unfold E_cfg
      have h_b : bnat false = 0 := rfl
      have h_len : (t ++ [false]).length = t.length + 1 := by simp
      rw [h_b, h_len, show (t.length + 1) * 2 + 3 + 0 = t.length * 2 + 4 + 1 by omega]
      rfl
    rwa [h_l1, h_rhs] at h3'
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

lemma E_outer (b : Bool) (w : List Bool) :
    (E_cfg b w) [target_tm]⊢⁺
    ((outer_left b (core b w) <+ p11 ^ ((core b w).length * 2 + 5)) {{B}}> default) := by
  rcases E_drain b w with ⟨l, hnc, hstep⟩
  have hl_eq : l = outer_left b (core b w) := NC_unique hnc (drain_target_NC b w)
  subst hl_eq
  have hexp : w.length * 4 + 7 + bnat b * 2 = (core b w).length * 2 + 5 := by
    rw [core_length]; omega
  rwa [hexp] at hstep

lemma E_step (b : Bool) (w : List Bool) :
    (E_cfg b w) [target_tm]⊢⁺ E_cfg (!b) (next_word b w) := by
  refine stepPlus_trans (E_outer b w) ?_
  rw [next_word_core]
  cases b <;> unfold outer_left
  · exact Outer0 (core false w)
  · exact Outer1 (core true w)

def Allowed (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ b w, c = E_cfg b w

lemma Allowed_step {c : Cfg (Fin 2) (Fin 6)} (h : Allowed c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  rcases h with ⟨b, w, rfl⟩
  exact ⟨E_cfg (!b) (next_word b w), ⟨!b, next_word b w, rfl⟩, E_step b w⟩

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : Nat}
    (h : multiStep target_tm c k = none) (d : Nat) :
    multiStep target_tm c (k + d) = none := by
  rw [multiStep_add, h]; rfl

theorem reach_arbitrarily_long :
    ∀ m : Nat, ∃ N c, m ≤ N ∧ Allowed c ∧ multiStep target_tm (init []) N = some c
  | 0 => by
    rcases Entry_init with ⟨N₀, hN₀⟩
    exact ⟨N₀, _, Nat.zero_le N₀, ⟨false, [true], rfl⟩, hN₀⟩
  | m + 1 => by
    rcases reach_arbitrarily_long m with ⟨N, c, _, hc, hN⟩
    rcases Allowed_step hc with ⟨c', hc', k, _, hk⟩
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

end BusyBeaver.M_1RB1LB_1LC1RB_1RF1LD_0LE0LC_0RCHHH_1LA0RF
