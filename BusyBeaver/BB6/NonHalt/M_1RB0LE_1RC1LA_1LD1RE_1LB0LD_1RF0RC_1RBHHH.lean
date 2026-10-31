/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

open Counter

set_option linter.unusedSimpArgs false

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

-- ============================================================================
-- Section 1: Basic Utilities, PairWord & Pair3Word
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
  | [_] => ([false, false], true)
  | _ :: false :: u => (false :: true :: u, false)
  | [_, true] => ([false, false], true)
  | _ :: true :: _ :: u =>
    let (v, e) := inc u
    (false :: false :: false :: v, e)

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
-- Section 2: Machine-Specific Rules (A3Words)
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

lemma C1001_exit (l r : ListBlank (Fin 2)) :
    (l {{C}}> ([1, 0, 0, 1] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([1, 1, 1, 1] +> r)) :=
  ⟨8, by omega, by run_steps 8⟩

lemma R1001_bridge (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ n +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) {{B}}> ([1, 1, 1, 1] +> r)) :=
  stepStar_stepPlus_trans (CScan (l <+ [0, 1]) ([1, 0, 0, 1] +> r) n)
    (C1001_exit (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) r)

lemma ZCarryMarked (a b : Bool) (l r : ListBlank (Fin 2)) :
    ((l <+ [bit a, 1, 1, 1, bit b, 1]) {{B}}> ([1] +> r)) [target_tm]⊢⁺
    (l {{B}}> ([1, 1, 1, 1, 1, 1, 1] +> r)) := by
  cases a <;> cases b
  · exact ⟨16, by omega, by run_steps 16⟩
  · exact ⟨12, by omega, by run_steps 12⟩
  · exact ⟨14, by omega, by run_steps 14⟩
  · exact ⟨10, by omega, by run_steps 10⟩

lemma C11_step (l r : ListBlank (Fin 2)) :
    (l {{C}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((l <+ [0, 1]) {{C}}> r) :=
  ⟨2, by omega, by run_steps 2⟩

lemma REleven (l r : ListBlank (Fin 2)) (n : Nat) :
    ((l <+ [0, 1]) {{C}}> (rd1 ^ n +> ([1, 1] +> r))) [target_tm]⊢⁺
    ((l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2) <+ [0, 1]) {{C}}> r) :=
  stepStar_stepPlus_trans (CScan (l <+ [0, 1]) ([1, 1] +> r) n)
    (C11_step (l <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2)) r)

lemma ZInc_nil (r : ListBlank (Fin 2)) :
    (data [] {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data [false] <+ [0, 1]) {{C}}> insert false r) :=
  ⟨14, by omega, by run_steps 14⟩

lemma ZInc_one (a : Bool) (r : ListBlank (Fin 2)) :
    (data [a] {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data [false, false] <+ [0, 1]) {{C}}> insert true r) := by
  cases a
  · exact ⟨25, by omega, by run_steps 25⟩
  · exact ⟨23, by omega, by run_steps 23⟩

lemma ZInc_two_true (a : Bool) (r : ListBlank (Fin 2)) :
    (data [a, true] {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data [false, false] <+ [0, 1]) {{C}}> insert true r) := by
  cases a
  · exact ⟨19, by omega, by run_steps 19⟩
  · exact ⟨17, by omega, by run_steps 17⟩

lemma ZInc_false (a : Bool) (u : List Bool) (r : ListBlank (Fin 2)) :
    (data (a :: false :: u) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data (false :: true :: u) <+ [0, 1]) {{C}}> insert false r) := by
  cases a
  · exact ⟨12, by omega, by run_steps 12⟩
  · exact ⟨10, by omega, by run_steps 10⟩

lemma ZInc_rec_exit (v : List Bool) (e : Bool) (r : ListBlank (Fin 2)) :
    ((data v <+ [0, 1]) {{C}}> insert e ([1, 1, 1, 1, 1, 1] +> r)) [target_tm]⊢⁺
    ((data (false :: false :: false :: v) <+ [0, 1]) {{C}}> insert e r) := by
  cases e <;> exact ⟨6, by omega, by run_steps 6⟩

lemma ZInc (w : List Bool) (r : ListBlank (Fin 2)) :
    (data w {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
    ((data (inc w).1 <+ [0, 1]) {{C}}> insert (inc w).2 r) := by
  match w with
  | [] => exact ZInc_nil r
  | [a] => exact ZInc_one a r
  | a :: false :: u => exact ZInc_false a u r
  | [a, true] => exact ZInc_two_true a r
  | a :: true :: b :: u =>
    have s1 : (data (a :: true :: b :: u) {{B}}> ([1, 1] +> r)) [target_tm]⊢⁺
        (data u {{B}}> ([1, 1] +> ([1, 1, 1, 1, 1, 1] +> r))) := by
      simpa [data, pairs] using ZCarryMarked a b (data u) ([1] +> r)
    have s2 := ZInc u ([1, 1, 1, 1, 1, 1] +> r)
    have s3 := ZInc_rec_exit (inc u).1 (inc u).2 r
    have hinc : inc (a :: true :: b :: u) = (false :: false :: false :: (inc u).1, (inc u).2) := by
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

lemma R1001_exit (v : List Bool) (e : Bool) (r : ListBlank (Fin 2)) :
    ((data v <+ [0, 1]) {{C}}> insert e ([1, 1] +> r)) [target_tm]⊢⁺
    ((data (false :: v) <+ [0, 1]) {{C}}> insert e r) := by
  cases e <;> exact ⟨2, by omega, by run_steps 2⟩

lemma R1001 (w : List Bool) (r : ListBlank (Fin 2)) (n : Nat) :
    let p := inc (List.replicate (2 * n) true ++ false :: w)
    ((data w <+ [0, 1]) {{C}}> (rd1 ^ n +> ([1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((data (false :: p.1) <+ [0, 1]) {{C}}> insert p.2 r) := by
  dsimp only
  have s1 := R1001_bridge (data w) r n
  have hdata : data (List.replicate (2 * n) true ++ false :: w) =
      data w <+ [0, 1] <+ ([1, 1] : List (Fin 2)) ^ (n * 2) := by
    rw [data_ones, Nat.mul_comm 2 n]; rfl
  have s2 := ZInc (List.replicate (2 * n) true ++ false :: w) ([1, 1] +> r)
  rw [hdata] at s2
  have h1111 : ([1, 1, 1, 1] : List (Fin 2)) +> r = [1, 1] +> ([1, 1] +> r) := rfl
  rw [h1111] at s1
  have s3 := R1001_exit (inc (List.replicate (2 * n) true ++ false :: w)).1
    (inc (List.replicate (2 * n) true ++ false :: w)).2 r
  exact stepPlus_trans s1 (stepPlus_trans s2 s3)

lemma init31 :
    (init []) [target_tm]⊢* Conf [false, false] default :=
  ⟨31, by run_steps 31⟩

-- ============================================================================
-- Section 3: Right Counter (Pair12Right & PairOrdinary)
-- ============================================================================

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
-- Section 4: Pair3Guard & Pair3EntryGuard
-- ============================================================================

def bit_value (b : Bool) : Nat := if b then 1 else 0
def zero_bit (b : Bool) : Nat := if b then 0 else 1

def plane (f : Bool → Nat) : Nat → List Bool → Nat
  | _, [] => 0
  | 0, b :: u => f b + 2 * plane f 2 u
  | j + 1, _ :: u => plane f j u

def width : List Bool → Nat
  | [] => 0
  | [_] => 0
  | [_, _] => 1
  | _ :: _ :: _ :: u => 1 + width u

def value (w : List Bool) : Nat := plane bit_value 1 w
def gap0 (w : List Bool) : Nat := 1 + plane zero_bit 1 w
def gap1 (w : List Bool) : Nat := 1 + plane zero_bit 0 w
def gap2 (w : List Bool) : Nat := 2 + 2 * plane zero_bit 2 w

def guard (n : Nat) (w : List Bool) : Prop :=
  n ≤ gap0 w ∧ n ≤ gap1 w ∧ n ≤ gap2 w

lemma gap_bounds (w : List Bool) : guard 1 w := by
  dsimp [guard, gap0, gap1, gap2]; omega

lemma value_gap0 (w : List Bool) : value w + gap0 w = 2 ^ width w := by
  match w with
  | [] => rfl
  | [_] => rfl
  | [a, b] => cases b <;> rfl
  | a :: b :: c :: u =>
    have ih := value_gap0 u
    dsimp [value, gap0, plane, width] at ih ⊢
    rw [Nat.add_comm 1 (width u), Nat.pow_succ]
    cases b <;> dsimp [bit_value, zero_bit] <;> omega

lemma gap_cons (b : Bool) (w : List Bool) :
    gap0 (b :: w) = gap1 w ∧ gap1 (b :: w) + bit_value b = gap2 w ∧ gap2 (b :: w) = 2 * gap0 w := by
  cases b <;> dsimp [gap0, gap1, gap2, plane, zero_bit, bit_value] <;> omega

lemma guard_zero {n : Nat} {w : List Bool} (h : guard n w) : guard n (false :: w) := by
  have hc := gap_cons false w
  dsimp [guard, bit_value] at hc h ⊢
  omega

lemma guard_one {n : Nat} {w : List Bool} (h : guard (n + 1) w) : guard n (true :: w) := by
  have hc := gap_cons true w
  dsimp [guard, bit_value] at hc h ⊢
  omega

lemma inc_head (w : List Bool) : ∃ u, (inc w).1 = false :: u := by
  match w with
  | [] => exact ⟨[], rfl⟩
  | [_] => exact ⟨[false], rfl⟩
  | _ :: false :: u => exact ⟨true :: u, rfl⟩
  | [_, true] => exact ⟨[false], rfl⟩
  | _ :: true :: _ :: u => exact ⟨false :: false :: (inc u).1, rfl⟩

lemma inc_mono (w : List Bool) :
    gap1 w ≤ gap1 (inc w).1 ∧ gap2 w ≤ gap2 (inc w).1 := by
  match w with
  | [] => dsimp [inc, gap1, gap2, plane, zero_bit]; omega
  | [a] => cases a <;> dsimp [inc, gap1, gap2, plane, zero_bit] <;> omega
  | a :: false :: u => cases a <;> dsimp [inc, gap1, gap2, plane, zero_bit] <;> omega
  | [a, true] => cases a <;> dsimp [inc, gap1, gap2, plane, zero_bit] <;> omega
  | a :: true :: c :: u =>
    have ih := inc_mono u
    cases a <;> cases c <;> dsimp [inc, gap1, gap2, plane, zero_bit] at ih ⊢ <;> omega

lemma inc_interior (w : List Bool) (h : 1 < gap0 w) :
    (inc w).2 = false ∧ (inc w).1.length = w.length ∧ gap0 (inc w).1 + 1 = gap0 w := by
  match w with
  | [] => dsimp [gap0, plane] at h; omega
  | [_] => dsimp [gap0, plane] at h; omega
  | a :: false :: u =>
    dsimp [inc, gap0, plane, zero_bit] at h ⊢
    exact ⟨rfl, rfl, by omega⟩
  | [a, true] =>
    dsimp [gap0, plane, zero_bit] at h
    omega
  | a :: true :: c :: u =>
    have hu : 1 < gap0 u := by
      dsimp [gap0, plane, zero_bit] at h ⊢
      omega
    rcases inc_interior u hu with ⟨he, hl, hg⟩
    dsimp [inc, gap0, plane, zero_bit] at hg ⊢
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

lemma inc_steps_mono {q : Nat} {w v : List Bool} (h : inc_steps q w v) :
    gap1 w ≤ gap1 v ∧ gap2 w ≤ gap2 v := by
  induction h with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ _ w u _ hinc _ ih =>
    have hm := inc_mono w
    have hu : (inc w).1 = u := congrArg Prod.fst hinc
    rw [hu] at hm
    omega

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

lemma guard_mono {m n : Nat} {w : List Bool} (hm : guard m w) (h : n ≤ m) : guard n w := by
  dsimp [guard] at hm ⊢; omega

lemma guard_two_ones {n : Nat} {w : List Bool} (h : guard (n + 1) w) :
    guard n (true :: true :: w) := by
  dsimp [guard, gap0, gap1, gap2, plane, zero_bit] at h ⊢; omega

lemma guard_three_ones {n : Nat} {w : List Bool} (h : guard n w) :
    guard n (true :: true :: true :: w) := by
  dsimp [guard, gap0, gap1, gap2, plane, zero_bit] at h ⊢; omega

lemma guard_ones_aux (n k : Nat) (w : List Bool) (h : guard (n + 1) w) :
    guard n (List.replicate k true ++ w) := by
  match k with
  | 0 => exact guard_mono h (by omega)
  | 1 => exact guard_one h
  | 2 => exact guard_two_ones h
  | k + 3 =>
    have hrep : List.replicate (k + 3) true ++ w =
        true :: true :: true :: (List.replicate k true ++ w) := rfl
    rw [hrep]
    exact guard_three_ones (guard_ones_aux n k w h)

lemma guard_ones {n : Nat} (k : Nat) {w : List Bool} (hn : 1 ≤ n) (h : guard (n + 1) w) :
    guard n (List.replicate k true ++ w) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | _
  · exact gap_bounds _
  · exact guard_ones_aux n k w h

lemma inc_guard (n : Nat) (w : List Bool) (hn : 1 ≤ n) (hg : guard (n + 1) w) :
    (inc w).2 = false ∧ guard n (inc w).1 := by
  have hm := inc_mono w
  have hi : 1 < gap0 w := by dsimp [guard] at hg; omega
  rcases inc_interior w hi with ⟨he, _, hg0⟩
  refine ⟨he, ?_⟩
  dsimp [guard] at hg ⊢
  omega

lemma width_length (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p) :
    width w = k + (if p = 2 then 1 else 0) := by
  induction k generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩ <;> dsimp [width] <;> simp at hl <;> split_ifs <;> omega
  | succ k ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl; omega
    · simp at hl; omega
    · simp at hl; omega
    · dsimp [width]
      have hl' : w.length = 3 * k + p := by simp at hl; omega
      rw [ih w hl']
      omega

lemma plane_zeros (n i : Nat) : plane bit_value i (List.replicate n false) = 0 := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    cases i with
    | zero => dsimp [List.replicate_succ, plane, bit_value]; rw [ih 2]
    | succ j => dsimp [List.replicate_succ, plane]; exact ih j

lemma value_zeros (n : Nat) : value (List.replicate n false) = 0 :=
  plane_zeros n 1

lemma width_zeros (k p : Nat) (hp : p ≤ 2) :
    width (List.replicate (3 * k + p) false) = k + (if p = 2 then 1 else 0) :=
  width_length k p _ hp List.length_replicate

lemma gap0_zeros (k p : Nat) (hp : p ≤ 2) :
    gap0 (List.replicate (3 * k + p) false) = 2 ^ (k + (if p = 2 then 1 else 0)) := by
  have h := value_gap0 (List.replicate (3 * k + p) false)
  rw [value_zeros, width_zeros k p hp, Nat.zero_add] at h
  exact h

lemma inc_at_capacity (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p)
    (hg : gap0 w = 1) :
    inc w = if p = 0 then (List.replicate (3 * k + 1) false, false)
            else (List.replicate (3 * k + 2) false, true) := by
  induction k generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · have hp0 : p = 0 := by simp at hl; omega
      subst hp0; rfl
    · have hp1 : p = 1 := by simp at hl; omega
      subst hp1; rfl
    · have hp2 : p = 2 := by simp at hl; omega
      subst hp2
      cases b
      · dsimp [gap0, plane, zero_bit] at hg; omega
      · rfl
    · simp at hl; omega
  | succ k ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl; omega
    · simp at hl; omega
    · simp at hl; omega
    · have hb : b = true ∧ gap0 w = 1 := by
        cases b <;> dsimp [gap0, plane, zero_bit] at hg ⊢
        · omega
        · exact ⟨rfl, by omega⟩
      rcases hb with ⟨rfl, hg'⟩
      have hl' : w.length = 3 * k + p := by simp at hl; omega
      have ihw := ih w hl' hg'
      dsimp [inc]
      rw [ihw]
      split_ifs with hp0
      · have hrep : List.replicate (3 * (k + 1) + 1) false =
            false :: false :: false :: List.replicate (3 * k + 1) false := by
          rw [show 3 * (k + 1) + 1 = 3 + (3 * k + 1) by omega, List.replicate_add]; rfl
        rw [hrep]
      · have hrep : List.replicate (3 * (k + 1) + 2) false =
            false :: false :: false :: List.replicate (3 * k + 2) false := by
          rw [show 3 * (k + 1) + 2 = 3 + (3 * k + 2) by omega, List.replicate_add]; rfl
        rw [hrep]

lemma overflow12 (k p : Nat) (w : List Bool) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hl : w.length = 3 * k + p) (hg : gap0 w = 1) :
    inc w = (List.replicate (3 * k + 2) false, true) := by
  have h := inc_at_capacity k p w hp2 hl hg
  have hp0 : p ≠ 0 := by omega
  simpa [hp0] using h

lemma first_capacity (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p) :
    ∃ u, inc_steps (gap0 w - 1) w u ∧ u.length = w.length ∧ gap0 u = 1 ∧
      inc u = (if p = 0 then (List.replicate (3 * k + 1) false, false)
               else (List.replicate (3 * k + 2) false, true)) := by
  have hb := (gap_bounds w).1
  rcases inc_steps_interior (gap0 w - 1) w (by omega) with ⟨u, hs, hlen, hgap⟩
  have hu : gap0 u = 1 := by omega
  exact ⟨u, hs, hlen, hu, inc_at_capacity k p u hp (by omega) hu⟩

lemma inc_markers_mono (w : List Bool) :
    plane bit_value 0 (inc w).1 ≤ plane bit_value 0 w ∧
    plane bit_value 2 (inc w).1 ≤ plane bit_value 2 w := by
  match w with
  | [] => dsimp [inc, plane, bit_value]; omega
  | [a] => cases a <;> dsimp [inc, plane, bit_value] <;> omega
  | a :: false :: u => cases a <;> dsimp [inc, plane, bit_value] <;> omega
  | [a, true] => cases a <;> dsimp [inc, plane, bit_value] <;> omega
  | a :: true :: c :: u =>
    have ih := inc_markers_mono u
    cases a <;> cases c <;> dsimp [inc, plane, bit_value] at ih ⊢ <;> omega

lemma inc_steps_markers_zero {q : Nat} {w v : List Bool} (hs : inc_steps q w v)
    (h0 : plane bit_value 0 w = 0) (h2 : plane bit_value 2 w = 0) :
    plane bit_value 0 v = 0 ∧ plane bit_value 2 v = 0 := by
  induction hs with
  | zero => exact ⟨h0, h2⟩
  | succ _ w u _ hinc _ ih =>
    have hm := inc_markers_mono w
    have hu : (inc w).1 = u := congrArg Prod.fst hinc
    rw [hu] at hm
    exact ih (by omega) (by omega)

lemma marker_gaps (k : Nat) (w : List Bool) (hl : w.length = 3 * k + 2)
    (h0 : plane bit_value 0 w = 0) (h2 : plane bit_value 2 w = 0) :
    gap1 w = 2 ^ (k + 1) ∧ gap2 w = 2 ^ (k + 1) := by
  induction k generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl
    · simp at hl
    · cases a
      · exact ⟨rfl, rfl⟩
      · dsimp [plane, bit_value] at h0; omega
    · simp at hl
  | succ k ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
    · simp at hl
    · simp at hl
    · simp at hl
    · have ha : a = false ∧ c = false ∧ plane bit_value 0 w = 0 ∧ plane bit_value 2 w = 0 := by
        cases a <;> cases c <;> dsimp [plane, bit_value] at h0 h2
        · exact ⟨rfl, rfl, by omega, by omega⟩
        · omega
        · omega
        · omega
      rcases ha with ⟨rfl, rfl, hw0, hw2⟩
      have hl' : w.length = 3 * k + 2 := by simp at hl; omega
      rcases ih w hl' hw0 hw2 with ⟨hg1, hg2⟩
      dsimp [gap1, gap2, plane, zero_bit] at hg1 hg2 ⊢
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, Nat.pow_succ]
      omega

lemma zero2_gaps (k : Nat) :
    gap0 (List.replicate (3 * k + 2) false) = 2 ^ (k + 1) ∧
    gap1 (List.replicate (3 * k + 2) false) = 2 ^ (k + 1) ∧
    gap2 (List.replicate (3 * k + 2) false) = 2 ^ (k + 1) := by
  refine ⟨?_, marker_gaps k _ List.length_replicate (plane_zeros _ _) (plane_zeros _ _)⟩
  simpa using gap0_zeros k 2 (by omega)

lemma zero3_gaps (k : Nat) :
    gap0 (List.replicate (3 * k + 3) false) = 2 ^ (k + 1) ∧
    gap1 (List.replicate (3 * k + 3) false) = 2 ^ (k + 1) ∧
    gap2 (List.replicate (3 * k + 3) false) = 2 ^ (k + 2) := by
  have hrep : List.replicate (3 * k + 3) false = false :: List.replicate (3 * k + 2) false := by
    rw [show 3 * k + 3 = (3 * k + 2) + 1 by omega, List.replicate_succ]
  rw [hrep]
  have hz2 := zero2_gaps k
  have hc := gap_cons false (List.replicate (3 * k + 2) false)
  dsimp [bit_value] at hc
  rw [show k + 2 = (k + 1) + 1 by omega, Nat.pow_succ]
  omega

lemma strong (k z : Nat) (w : List Bool) (hl : w.length = 3 * k + 2)
    (h0 : plane bit_value 0 w = 0) (h2 : plane bit_value 2 w = 0)
    (hv : value w = 2 ^ (z + 1) - 2) (hz : z ≤ k) :
    guard (2 ^ (k + 1 - z)) (List.replicate (2 * z) true ++ false :: w) := by
  rcases marker_gaps k w hl h0 h2 with ⟨hg1, hg2⟩
  have hsum := value_gap0 w
  have hw := width_length k 2 w (by omega) hl
  simp at hw
  rw [hw, hv] at hsum
  have hpz0 := pow2_pos z
  have hpz : 2 ≤ 2 ^ (z + 1) := by rw [Nat.pow_succ]; omega
  have hg : gap0 w + 2 ^ (z + 1) = 2 ^ (k + 1) + 2 := by omega
  have hc := gap_cons false w
  dsimp [bit_value] at hc
  rcases Nat.eq_zero_or_pos z with rfl | hz0
  · simp only [Nat.mul_zero, List.replicate_zero, List.nil_append, Nat.sub_zero]
    dsimp [guard]
    have hpow1 : 2 ^ (0 + 1) = 2 := rfl
    rw [hpow1] at hg
    omega
  · refine guard_ones (2 * z) (pow2_pos (k + 1 - z)) ?_
    have hb : 2 * 2 ^ (k + 1 - z) ≤ 2 ^ (k + 1) := by
      have h1 : 2 * 2 ^ (k + 1 - z) = 2 ^ (k + 1 - z + 1) := by rw [Nat.pow_succ]; ring
      rw [h1]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hp := pow2_pos (k + 1 - z)
    have hg0 : 2 ^ (k + 1 - z) + 1 ≤ 2 * gap0 w := by
      rcases Nat.eq_or_lt_of_le hz with rfl | hlt
      · rw [show z + 1 - z = 1 by omega]
        omega
      · have ht : 2 * 2 ^ (z + 1) ≤ 2 ^ (k + 1) := by
          have h1 : 2 * 2 ^ (z + 1) = 2 ^ (z + 1 + 1) := by rw [Nat.pow_succ]; ring
          rw [h1]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        omega
    dsimp [guard]
    omega

lemma entry (k z : Nat) (hz : z ≤ k) :
    ∃ w, inc_steps (2 ^ (z + 1) - 2) (List.replicate (3 * k + 2) false) w ∧
      guard (2 ^ (k + 1 - z)) (List.replicate (2 * z) true ++ false :: w) := by
  have hg := (zero2_gaps k).1
  have hpz0 := pow2_pos z
  have hp : 2 ≤ 2 ^ (z + 1) := by rw [Nat.pow_succ]; omega
  have hc : 2 ^ (z + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rcases inc_steps_interior (2 ^ (z + 1) - 2) (List.replicate (3 * k + 2) false) (by omega)
    with ⟨w, hs, hl, hw⟩
  rw [List.length_replicate] at hl
  rcases inc_steps_markers_zero hs (plane_zeros _ _) (plane_zeros _ _) with ⟨h0, h2⟩
  refine ⟨w, hs, strong k z w hl h0 h2 ?_ hz⟩
  have hv := value_gap0 w
  have hwidth := width_length k 2 w (by omega) hl
  simp at hwidth
  rw [hwidth] at hv
  omega

lemma entry_actual (k z h : Nat) (hz : z ≤ k) (ht : 2 ^ z * (1 + 2 * h) ≤ 2 ^ (k + 1)) :
    ∃ w, inc_steps (2 ^ (z + 1) - 2) (List.replicate (3 * k + 2) false) w ∧
      guard (2 * h) (List.replicate (2 * z) true ++ false :: w) := by
  rcases entry k z hz with ⟨w, hs, hg⟩
  have he : 2 ^ (k + 1 - z) * 2 ^ z = 2 ^ (k + 1) := by
    rw [← Nat.pow_add, show k + 1 - z + z = k + 1 by omega]
  have hp := pow2_pos z
  have hle : 2 * h ≤ 2 ^ (k + 1 - z) := by
    rcases Nat.lt_or_ge (2 ^ (k + 1 - z)) (2 * h) with hlt | hge
    · have : 2 ^ z * (2 ^ (k + 1 - z) + 1) ≤ 2 ^ z * (1 + 2 * h) :=
        Nat.mul_le_mul_left _ (by omega)
      have : 2 ^ z * (2 ^ (k + 1 - z) + 1) = 2 ^ (k + 1) + 2 ^ z := by
        rw [ ← he ]; ring
      omega
    · exact hge
  exact ⟨w, hs, guard_mono hg hle⟩

-- ============================================================================
-- Section 5: A3Right, A3Entry, A3Region, A3Closure & Full Non-Halting Closure
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

lemma phase1_zero_gap (k : Nat) : gap0 (List.replicate (3 * k + 1) false) = 2 ^ k := by
  simpa using gap0_zeros k 1 (by omega)

lemma phase12 (k p : Nat) (w : List Bool) (x : Nat) (r : ListBlank (Fin 2))
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hl : w.length = 3 * k + p) (hr : RC rd1 x r) :
    ∃ s, RC rd1 (x + gap0 w) s ∧
      (Conf w r) [target_tm]⊢⁺ (Conf (List.replicate (3 * k + 2) false) ([1] +> s)) := by
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
    ∃ s, RC rd1 (x + gap0 w + 2 ^ k) s ∧
      (Conf w r) [target_tm]⊢⁺ (Conf (List.replicate (3 * k + 2) false) ([1] +> s)) := by
  rcases phase0_extend k w x r hl hr with ⟨s1, hr1, hS1⟩
  rcases phase12 k 1 (List.replicate (3 * k + 1) false) (x + gap0 w) s1
    (by omega) (by omega) List.length_replicate hr1 with ⟨s2, hr2, hS2⟩
  rw [phase1_zero_gap] at hr2
  exact ⟨s2, hr2, stepPlus_trans hS1 hS2⟩

inductive Allowed : Cfg (Fin 2) (Fin 6) → Prop
  | Blank (w : List Bool) : Allowed (Conf w default)
  | One (w : List Bool) : Allowed (Conf (false :: false :: w) ([1] +> default))
  | Shifted (w : List Bool) (n : Nat) (r : ListBlank (Fin 2)) :
      0 < n → RC rds n r → guard (2 * n) w → Allowed (Conf w r)

lemma last_signal (n : Nat) (w : List Bool) (b : Bool) :
    ∃ c', Allowed c' ∧ (Conf w (rd1 ^ n +> ([1, 0, 0, 1] +> insert b default))) [target_tm]⊢⁺ c' := by
  have hs := R1001 w (insert b default) n
  dsimp only at hs
  rcases inc_head (List.replicate (2 * n) true ++ false :: w) with ⟨u, hu⟩
  rw [hu] at hs
  cases b <;> cases h2 : (inc (List.replicate (2 * n) true ++ false :: w)).2 <;>
    rw [h2] at hs <;> simp only [insert_false, insert_true] at hs
  · exact ⟨Conf (false :: false :: u) default, Allowed.Blank _, hs⟩
  · exact ⟨Conf (false :: false :: u) ([1] +> default), Allowed.One u, hs⟩
  · exact ⟨Conf (false :: false :: u) ([1] +> default), Allowed.One u, hs⟩
  · exact ⟨Conf (false :: false :: false :: u) default, Allowed.Blank _,
      stepPlus_trans hs (eleven_word 0 (false :: false :: u) default)⟩

lemma last_shift (n : Nat) (w : List Bool) (b : Bool) (hg : 2 ^ (1 + n) ≤ gap0 w) :
    ∃ c', Allowed c' ∧ (Conf w (rd0 ^ n +> (rds +> insert b default))) [target_tm]⊢⁺ c' := by
  have hp := pow2_pos (1 + n)
  rcases inc_steps_interior (2 ^ (1 + n) - 1) w (by omega) with ⟨v, hv, _⟩
  rcases last_signal n v b with ⟨c', hA, hS⟩
  exact ⟨c', hA, stepPlus_trans (shifted_prefix n (insert b default) hv) hS⟩

lemma shifted_step (n : Nat) (w : List Bool) (r : ListBlank (Fin 2))
    (hn : 0 < n) (hr : RC rds n r) (hg : guard (2 * n) w) :
    ∃ c', Allowed c' ∧ (Conf w r) [target_tm]⊢⁺ c' := by
  rcases RC_positive_split hr hn with ⟨t, q, s, rfl, hs, hen, _⟩
  rw [hen] at hg
  cases q with
  | zero =>
    rw [RC_zero_unique hs]
    refine last_shift t w false ?_
    dsimp [guard] at hg
    rw [Nat.add_comm 1 t, Nat.pow_succ]
    omega
  | succ q =>
    have hp := pow2_pos t
    have hpow : 2 ^ (1 + t) = 2 * 2 ^ t := by rw [Nat.add_comm 1 t, Nat.pow_succ]; ring
    have hp1 : 2 ≤ 2 ^ (1 + t) := by rw [hpow]; omega
    have hmul : 2 * (2 ^ t * (1 + (q + 1) * 2)) = 2 ^ (1 + t) + 2 ^ (1 + t) * (2 * (q + 1)) := by
      rw [hpow]; ring
    have hge2 : 2 * (2 * (q + 1)) ≤ 2 ^ (1 + t) * (2 * (q + 1)) :=
      Nat.mul_le_mul_right (2 * (q + 1)) hp1
    have hq : 2 ^ (1 + t) - 1 < gap0 w := by
      dsimp [guard] at hg; omega
    rcases inc_steps_interior (2 ^ (1 + t) - 1) w hq with ⟨v, hv, _, hd⟩
    have hm := inc_steps_mono hv
    have hvg : guard (2 * (q + 1) + 2) v := by
      dsimp [guard] at hg hm ⊢
      have hg0 : 2 * (2 ^ t * (1 + (q + 1) * 2)) ≤ gap0 w := hg.1
      have hg1 : 2 * (2 ^ t * (1 + (q + 1) * 2)) ≤ gap1 w := hg.2.1
      have hg2 : 2 * (2 ^ t * (1 + (q + 1) * 2)) ≤ gap2 w := hg.2.2
      rw [hmul] at hg0 hg1 hg2
      omega
    have hu : guard (2 * (q + 1) + 1) (List.replicate (2 * t) true ++ false :: v) :=
      guard_ones (2 * t) (by omega) (guard_zero (guard_mono hvg (by omega)))
    rcases inc_guard (2 * (q + 1)) (List.replicate (2 * t) true ++ false :: v) (by omega) hu
      with ⟨he, hu'⟩
    refine ⟨Conf (false :: (inc (List.replicate (2 * t) true ++ false :: v)).1) s,
      Allowed.Shifted _ (q + 1) s (by omega) hs (guard_zero hu'), ?_⟩
    have hs1 := shifted_prefix t s hv
    have hs2 := R1001 v s t
    dsimp only at hs2
    rw [he, insert_false] at hs2
    exact stepPlus_trans hs1 hs2

lemma RC_power (a : Nat) : RC rd1 (2 ^ a) (rd0 ^ a +> (rd1 +> default)) := by
  have h1 : RC rd1 1 (rd1 +> default) := RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  exact RC_eq (RC_zeros a h1) (by omega) rfl

lemma exceptional (k : Nat) {r : ListBlank (Fin 2)} (hr : RC rd1 (2 ^ (k + 1)) r) :
    ∃ c', Allowed c' ∧ (Conf (List.replicate (3 * k + 2) false) ([1] +> r)) [target_tm]⊢⁺ c' := by
  have hr_eq : r = rd0 ^ (k + 1) +> (rd1 +> default) := RC_unique hr (RC_power (k + 1))
  subst hr_eq
  have hg := (zero2_gaps k).1
  have hp := pow2_pos (k + 1)
  rcases inc_steps_interior (2 ^ (k + 1) - 1) (List.replicate (3 * k + 2) false) (by omega)
    with ⟨v, hv, hl, hd⟩
  rw [List.length_replicate] at hl
  have hei : inc v = (List.replicate (3 * k + 2) false, true) :=
    overflow12 k 2 v (by omega) (by omega) hl (by omega)
  have hb : 2 ^ (1 + k) ≤ gap0 (List.replicate (3 * k + 3) false) := by
    rw [(zero3_gaps k).1, Nat.add_comm 1 k]
  rcases last_shift k (List.replicate (3 * k + 3) false) true hb with ⟨c', hA, hS⟩
  refine ⟨c', hA, ?_⟩
  have s1 := one_cross (k + 1) default (by omega) hv
  have s2 := RZero v ([0, 0, 0] +> (rd0 ^ k +> ([1, 1] +> default))) 0
  rw [hei] at s2
  dsimp only at s2
  have heq2 : rd0 ^ (k + 1) +> ([1, 1, 0, 0, 0] +> (default : ListBlank (Fin 2))) =
      rd1 ^ 0 +> ([0] +> ([0, 0, 0] +> (rd0 ^ k +> ([1, 1] +> default)))) := by
    rw [right_pow_succ rd0 k ([1, 1, 0, 0, 0] +> default)]
    simp [rd0]
  rw [heq2] at s1
  have heq3 : insert true (rd0 ^ 0 +> ([1] +> ([0, 0, 0] +> (rd0 ^ k +> ([1, 1] +> default))))) =
      rd1 ^ 0 +> ([1, 1] +> (rd0 ^ k +> (rds +> insert true default))) := by
    change [1, 1] +> (([0, 0, 0] : List (Fin 2)) +> (rd0 ^ k +> ([1, 1] +> default))) =
      [1, 1] +> (rd0 ^ k +> (rds +> insert true default))
    rw [zero3_rd0 k ([1, 1] +> default)]
    rfl
  rw [heq3] at s2
  have s3 := eleven_word 0 (List.replicate (3 * k + 2) false)
    (rd0 ^ k +> (rds +> insert true default))
  have hrep : List.replicate (2 * 0) true ++ false :: List.replicate (3 * k + 2) false =
      List.replicate (3 * k + 3) false := by
    rw [show 3 * k + 3 = (3 * k + 2) + 1 by omega, List.replicate_succ]
    rfl
  rw [hrep] at s3
  exact stepPlus_trans s1 (stepPlus_trans s2 (stepPlus_trans s3 hS))

lemma post_first (k T : Nat) {r : ListBlank (Fin 2)}
    (hr : RC rd1 T r) (ht : 0 < T) (hb : T ≤ 2 ^ (k + 1)) :
    ∃ c', Allowed c' ∧ (Conf (List.replicate (3 * k + 2) false) ([1] +> r)) [target_tm]⊢⁺ c' := by
  rcases Nat.eq_or_lt_of_le hb with rfl | hlt
  · exact exceptional k hr
  · rcases RC_positive_split hr ht with ⟨z, h, s, rfl, hs, het, _⟩
    have hz : z ≤ k := by
      rcases Nat.lt_or_ge k z with hgt | hle
      · have hp : 2 ^ (k + 1) ≤ 2 ^ z := Nat.pow_le_pow_right (by omega) hgt
        have : 2 ^ z * 1 ≤ 2 ^ z * (1 + h * 2) := Nat.mul_le_mul_left _ (by omega)
        omega
      · exact hle
    have hmul : 2 ^ z * (1 + 2 * h) ≤ 2 ^ (k + 1) := by
      rw [Nat.mul_comm 2 h]; omega
    rcases entry_actual k z h hz hmul with ⟨w, hw, hg⟩
    refine ⟨Conf (List.replicate (2 * z) true ++ false :: w) ([0, 0, 0] +> s), ?_,
      ordinary z s hw⟩
    cases h with
    | zero =>
      rw [RC_zero_unique hs, three_zeros_append_default]
      exact Allowed.Blank _
    | succ h =>
      exact Allowed.Shifted _ (h + 1) ([0, 0, 0] +> s) (by omega) (RC_shift3 hs) hg

lemma RC_odd_inv {h : Nat} {r : ListBlank (Fin 2)} (hr : RC rd1 (1 + 2 * h) r) :
    ∃ s, RC rd1 h s ∧ r = rd1 +> s := by
  have hr' : RC rd1 (1 + h * 2) r := RC_eq hr (by omega) rfl
  rcases RC_inv_d1 hr' with ⟨s, rfl, hs⟩
  exact ⟨s, hs, rfl⟩

lemma odd_entry (k h : Nat) {r : ListBlank (Fin 2)}
    (hr : RC rd1 (1 + 2 * h) r) (hb : 2 * h ≤ 2 ^ (k + 1)) :
    ∃ c', Allowed c' ∧ (Conf (List.replicate (3 * k + 2) false) ([1] +> r)) [target_tm]⊢⁺ c' := by
  rcases RC_odd_inv hr with ⟨s, hs, rfl⟩
  have h11 : ([1] : List (Fin 2)) +> (rd1 +> s) = rd1 ^ 0 +> ([1, 1] +> ([0, 0, 0] +> s)) := rfl
  rw [h11]
  refine ⟨Conf (false :: List.replicate (3 * k + 2) false) ([0, 0, 0] +> s), ?_,
    eleven_word 0 (List.replicate (3 * k + 2) false) ([0, 0, 0] +> s)⟩
  cases h with
  | zero =>
    rw [RC_zero_unique hs, three_zeros_append_default]
    exact Allowed.Blank _
  | succ h =>
    refine Allowed.Shifted _ (h + 1) ([0, 0, 0] +> s) (by omega) (RC_shift3 hs) ?_
    have hg := zero3_gaps k
    have hrep : List.replicate (3 * k + 3) false = false :: List.replicate (3 * k + 2) false := by
      rw [show 3 * k + 3 = (3 * k + 2) + 1 by omega, List.replicate_succ]
    rw [hrep, show k + 2 = (k + 1) + 1 by omega, Nat.pow_succ] at hg
    dsimp [guard]
    omega

lemma length_split (w : List Bool) : ∃ k p, p ≤ 2 ∧ w.length = 3 * k + p :=
  ⟨w.length / 3, w.length % 3, by omega, by omega⟩

lemma capacity_bound (k p : Nat) (w : List Bool) (hp : p ≤ 2) (hl : w.length = 3 * k + p) :
    gap0 w ≤ 2 ^ (k + (if p = 2 then 1 else 0)) := by
  have h := value_gap0 w
  rw [width_length k p w hp hl] at h
  omega

lemma pow_twice (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ]; ring

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
    have hle : 0 + gap0 w + 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_twice]; omega
    rcases post_first k (0 + gap0 w + 2 ^ k) hr (by omega) hle with ⟨c', hA, hT⟩
    exact ⟨c', hA, stepPlus_trans hS hT⟩
  · have hu : gap0 w ≤ 2 ^ (k + 1) := by
      refine Nat.le_trans hb (Nat.pow_le_pow_right (by omega) ?_)
      split_ifs <;> omega
    rcases phase12 k p w 0 default hp_pos hp hl RC.zero with ⟨s, hr, hS⟩
    rcases post_first k (0 + gap0 w) hr (by omega) (by omega) with ⟨c', hA, hT⟩
    exact ⟨c', hA, stepPlus_trans hS hT⟩

lemma one_step (u : List Bool) :
    ∃ c', Allowed c' ∧ (Conf (false :: false :: u) ([1] +> default)) [target_tm]⊢⁺ c' := by
  set w := false :: false :: u
  set a := 1 + plane zero_bit 2 u
  have heg : gap0 w = 2 * a := by
    dsimp [w, a, gap0, plane, zero_bit]; omega
  rcases length_split w with ⟨k, p, hp, hl⟩
  have hb := capacity_bound k p w hp hl
  rcases Nat.eq_zero_or_pos p with rfl | hp_pos
  · simp at hl hb
    have hk : 1 ≤ k := by
      have : 2 ≤ w.length := by simp [w]
      omega
    cases k with
    | zero => omega
    | succ k =>
      rcases phase0 (k + 1) w 1 ([1] +> default) hl right_one with ⟨s, hr, hS⟩
      rw [heg] at hr
      have hr' : RC rd1 (1 + 2 * (a + 2 ^ k)) s :=
        RC_eq hr (by rw [pow_twice]; omega) rfl
      have hu : 2 * (a + 2 ^ k) ≤ 2 ^ (k + 1 + 1) := by
        rw [pow_twice (k + 1)]; omega
      rcases odd_entry (k + 1) (a + 2 ^ k) hr' hu with ⟨c', hA, hT⟩
      exact ⟨c', hA, stepPlus_trans hS hT⟩
  · have hu : 2 * a ≤ 2 ^ (k + 1) := by
      rw [← heg]
      refine Nat.le_trans hb (Nat.pow_le_pow_right (by omega) ?_)
      split_ifs <;> omega
    rcases phase12 k p w 1 ([1] +> default) hp_pos hp hl right_one with ⟨s, hr, hS⟩
    rw [heg] at hr
    rcases odd_entry k a hr hu with ⟨c', hA, hT⟩
    exact ⟨c', hA, stepPlus_trans hS hT⟩

lemma Allowed_step {c : Cfg (Fin 2) (Fin 6)} (hA : Allowed c) :
    ∃ c', Allowed c' ∧ c [target_tm]⊢⁺ c' := by
  cases hA with
  | Blank w => exact blank_step w
  | One w => exact one_step w
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

end BusyBeaver.M_1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RBHHH
