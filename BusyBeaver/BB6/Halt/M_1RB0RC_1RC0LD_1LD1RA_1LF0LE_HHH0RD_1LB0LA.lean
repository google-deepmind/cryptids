/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1RC0LD_1LD1RA_1LF0LE_HHH0RD_1LB0LA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 1 = step M c := rfl

lemma multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  simp only [multiStep, Function.iterate_succ_apply']

lemma multiStep_add (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) :
    c₁ [M]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

@[simp] lemma pow_zero_list (u : List (Fin 2)) : u ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
@[simp] lemma nil_append_list (l : List (Fin 2)) : ([] : List (Fin 2)) ++ l = l := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
@[simp] lemma init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

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

lemma listblank_append_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (s <+ (([1] : List (Fin 2)) ^ n)) <+ (([1] : List (Fin 2)) ^ m) =
    s <+ (([1] : List (Fin 2)) ^ (n + m)) := by
  rw [listblank_append_append, list_pow_add_comm, ← list_pow_add]

lemma listblank_right_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (([1] : List (Fin 2)) ^ n) +> ((([1] : List (Fin 2)) ^ m) +> s) =
    (([1] : List (Fin 2)) ^ (n + m)) +> s := by
  rw [← listblank_append_right_assoc, ← list_pow_add]

-- ============================================================================
-- Section 1: 2nd-Order Digit-Stack Encodings & 16 Local Separator Rules
-- ============================================================================

def encLeft1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))

def encRight1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | d :: R => (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0)

@[simp] lemma encLeft_nil : encLeft1 [] = default := rfl
@[simp] lemma encLeft_cons (a : ℕ) (L : List ℕ) :
    encLeft1 (a :: L) = ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) := rfl
@[simp] lemma encRight_nil : encRight1 [] = default := rfl
@[simp] lemma encRight_cons (d : ℕ) (R : List ℕ) :
    encRight1 (d :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0) := rfl

def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | b :: L => (b + 1) :: L

@[simp] lemma encLeft_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encLeft1 L = encLeft1 (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encLeft1]
  | cons b L' => rfl

@[simp] lemma encRight_cons_one (R : List ℕ) :
    (1 : Fin 2) >> encRight1 R = encRight1 (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encRight1]
  | cons d R' => rfl

macro "finish" : tactic => `(tactic| (refine ⟨0, ?_⟩; simp only [zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one, encRight_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail, multiStep_zero]; try rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

def cfg_F (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨0, encLeft1 L, encRight1 R⟩⟩

def cfg_AR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encLeft1 L) {{A}}> (encRight1 R)

inductive StackMode
  | F
  | AR
  deriving DecidableEq, Repr

def evalStackCfg : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .F, L, R => cfg_F L R
  | .AR, L, R => cfg_AR L R

@[simp] lemma evalStackCfg_F (L R : List ℕ) : evalStackCfg .F L R = cfg_F L R := rfl
@[simp] lemma evalStackCfg_AR (L R : List ℕ) : evalStackCfg .AR L R = cfg_AR L R := rfl

-- Mode F Rules (8 Rules)

theorem rule_F_nil (R : List ℕ) :
    (cfg_F [] R) [target_tm]⊢⁺ (cfg_AR [1] R) := by
  unfold cfg_F cfg_AR
  rw [encLeft_nil, encLeft_cons 1 [], encLeft_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_F_zero_nil (R : List ℕ) :
    (cfg_F [0] R) [target_tm]⊢⁺ (cfg_F [] (0 :: bumpHead R)) := by
  unfold cfg_F
  rw [encLeft_cons 0 [], encLeft_nil, encRight_cons 0 (bumpHead R)]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_F_zero_zero (L R : List ℕ) :
    (cfg_F (0 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_F (bumpHead (bumpHead L)) (0 :: R)) := by
  unfold cfg_F
  rw [encLeft_cons 0 (0 :: L), encLeft_cons 0 L, encRight_cons 0 R]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 12

theorem rule_F_zero_one (L R : List ℕ) :
    (cfg_F (0 :: 1 :: L) R) [target_tm]⊢⁺ (cfg_F L (2 :: bumpHead R)) := by
  unfold cfg_F
  rw [encLeft_cons 0 (1 :: L), encLeft_cons 1 L, encRight_cons 2 (bumpHead R)]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 7

theorem rule_F_zero_add_two (L R : List ℕ) (b : ℕ) :
    (cfg_F (0 :: (b + 2) :: L) R) [target_tm]⊢⁺ (cfg_AR (b :: L) (0 :: 0 :: bumpHead R)) := by
  unfold cfg_F cfg_AR
  rw [encLeft_cons 0 ((b + 2) :: L), encLeft_cons (b + 2) L, encLeft_cons b L,
      encRight_cons 0 (0 :: bumpHead R), encRight_cons 0 (bumpHead R)]
  have hb : b + 2 + 1 = (b + 1) + 2 := by omega
  rw [hb, ← listblank_append_pow_add ((encLeft1 L).cons 0) (b + 1) 2]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 4

def cfg_Halt_F (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encLeft1 L, (0 : Fin 2) >> (0 : Fin 2) >> encRight1 (bumpHead R)⟩⟩

theorem rule_F_one (L R : List ℕ) :
    ((cfg_F (1 :: L) R) [target_tm]⊢⁺ (cfg_Halt_F L R)) ∧
    (step target_tm (cfg_Halt_F L R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_F cfg_Halt_F
  rw [encLeft_cons 1 L]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_F_one_halt (L R : List ℕ) :
    ∃ cfg, ((cfg_F (1 :: L) R) [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone :=
  ⟨cfg_Halt_F L R, stepPlus_stepStar (rule_F_one L R).1, (rule_F_one L R).2⟩

theorem rule_F_two (L R : List ℕ) :
    (cfg_F (2 :: L) R) [target_tm]⊢⁺ (cfg_AR (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_F cfg_AR
  rw [encLeft_cons 2 L, encRight_cons 0 (bumpHead R)]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 8

theorem rule_F_add_three (L R : List ℕ) (a : ℕ) :
    (cfg_F ((a + 3) :: L) R) [target_tm]⊢⁺ (cfg_F (a :: L) (0 :: bumpHead R)) := by
  unfold cfg_F
  rw [encLeft_cons (a + 3) L, encLeft_cons a L, encRight_cons 0 (bumpHead R)]
  have ha : a + 3 + 1 = (a + 1) + 3 := by omega
  rw [ha, ← listblank_append_pow_add ((encLeft1 L).cons 0) (a + 1) 3]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 5

-- Mode AR Rules (8 Rules)

theorem rule_AR_nil (L : List ℕ) :
    (cfg_AR L []) [target_tm]⊢⁺ (cfg_F L [1]) := by
  unfold cfg_AR cfg_F
  rw [encRight_nil, encRight_cons 1 [], encRight_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 6

theorem rule_AR_nil_zero (R : List ℕ) :
    (cfg_AR [] (0 :: R)) [target_tm]⊢⁺ (cfg_F [] (bumpHead (bumpHead R))) := by
  unfold cfg_AR cfg_F
  rw [encLeft_nil, encRight_cons 0 R]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_AR_zero_zero (L R : List ℕ) :
    (cfg_AR (0 :: L) (0 :: R)) [target_tm]⊢⁺
    (cfg_AR (bumpHead (bumpHead (bumpHead L))) (bumpHead R)) := by
  unfold cfg_AR
  rw [encLeft_cons 0 L, encRight_cons 0 R]
  cases R with
  | nil =>
    rw [show bumpHead ([] : List ℕ) = [0] from rfl, encRight_cons 0 [], encRight_nil]
    dsimp [HPow.hPow, list_nat_repeat]
    execute 7
  | cons d R' =>
    rw [show bumpHead (d :: R') = (d + 1) :: R' from rfl,
        encRight_cons (d + 1) R', encRight_cons d R']
    have hd : d + 1 + 1 = 1 + (d + 1) := by omega
    rw [hd, ← listblank_right_pow_add ((encRight1 R').cons 0) 1 (d + 1)]
    dsimp [HPow.hPow, list_nat_repeat]
    execute 7

theorem rule_AR_one_zero (L R : List ℕ) :
    (cfg_AR (1 :: L) (0 :: R)) [target_tm]⊢⁺
    (cfg_F L (bumpHead (bumpHead (bumpHead (bumpHead R))))) := by
  unfold cfg_AR cfg_F
  rw [encLeft_cons 1 L, encRight_cons 0 R]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 7

theorem rule_AR_add_two_zero (L R : List ℕ) (a : ℕ) :
    (cfg_AR ((a + 2) :: L) (0 :: R)) [target_tm]⊢⁺
    (cfg_AR (a :: L) (0 :: bumpHead (bumpHead R))) := by
  unfold cfg_AR
  rw [encLeft_cons (a + 2) L, encLeft_cons a L,
      encRight_cons 0 R, encRight_cons 0 (bumpHead (bumpHead R))]
  have ha : a + 2 + 1 = (a + 1) + 2 := by omega
  rw [ha, ← listblank_append_pow_add ((encLeft1 L).cons 0) (a + 1) 2]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 4

theorem rule_AR_one_nil (L : List ℕ) :
    (cfg_AR L [1]) [target_tm]⊢⁺ (cfg_AR (0 :: L) []) := by
  unfold cfg_AR
  rw [encLeft_cons 0 L, encRight_cons 1 [], encRight_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 2

theorem rule_AR_one_cons (L R : List ℕ) (e : ℕ) :
    (cfg_AR L (1 :: e :: R)) [target_tm]⊢⁺ (cfg_AR L (0 :: (e + 1) :: R)) := by
  unfold cfg_AR
  rw [encRight_cons 1 (e :: R), encRight_cons e R,
      encRight_cons 0 ((e + 1) :: R), encRight_cons (e + 1) R]
  have he1 : e + 1 = 1 + e := by omega
  have he2 : e + 1 + 1 = 2 + e := by omega
  rw [he2, ← listblank_right_pow_add ((encRight1 R).cons 0) 2 e]
  rw [he1, ← listblank_right_pow_add ((encRight1 R).cons 0) 1 e]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 14

theorem rule_AR_add_two (L R : List ℕ) (d : ℕ) :
    (cfg_AR L ((d + 2) :: R)) [target_tm]⊢⁺ (cfg_AR (0 :: L) (d :: R)) := by
  unfold cfg_AR
  rw [encLeft_cons 0 L, encRight_cons (d + 2) R, encRight_cons d R]
  have hd : d + 2 + 1 = 3 + d := by omega
  rw [hd, ← listblank_right_pow_add ((encRight1 R).cons 0) 3 d]
  have hd2 : d + 1 = 1 + d := by omega
  rw [hd2, ← listblank_right_pow_add ((encRight1 R).cons 0) 1 d]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 2

-- ============================================================================
-- Section 2: Multi-Step Bulk Contractions on `List ℕ`
-- ============================================================================

lemma bumpHead_iterate_cons (k v : ℕ) (L : List ℕ) :
    bumpHead^[k] (v :: L) = (v + k) :: L := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, bumpHead, ih (v + 1)]
    have h : v + 1 + k = v + (k + 1) := by omega
    rw [h]

lemma bumpHead_iterate_nil (k : ℕ) :
    bumpHead^[k + 1] [] = [k] := by
  rw [Function.iterate_succ_apply, bumpHead, bumpHead_iterate_cons, Nat.zero_add]

lemma bumpHead2_iterate_eq (k : ℕ) (R : List ℕ) :
    (fun R => bumpHead (bumpHead R))^[k] R = bumpHead^[2 * k] R := by
  induction k generalizing R with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [Function.iterate_succ_apply', ih, h2, Function.iterate_add_apply]
    rfl

def stepF3Right : ℕ → List ℕ → List ℕ
  | 0, R => R
  | k + 1, R => stepF3Right k (0 :: bumpHead R)

lemma stepF3Right_succ (k : ℕ) (R : List ℕ) :
    stepF3Right (k + 1) R = 0 :: (List.replicate k 1 ++ bumpHead R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [stepF3Right, ih (0 :: bumpHead R)]
    have h : List.replicate (k + 1) 1 ++ bumpHead R = List.replicate k 1 ++ (1 :: bumpHead R) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [h]
    rfl

theorem rule_F_step3_all (L R : List ℕ) (a k : ℕ) :
    (cfg_F ((3 * k + a) :: L) R) [target_tm]⊢*
    (cfg_F (a :: L) (stepF3Right k R)) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, stepF3Right]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : 3 * (k + 1) + a = (3 * k + a) + 3 := by omega
    rw [h1, stepF3Right]
    exact stepStar_trans (stepPlus_stepStar (rule_F_add_three L R (3 * k + a))) (ih (0 :: bumpHead R))

theorem rule_AR_step2_all (L R : List ℕ) (d k : ℕ) :
    (cfg_AR L ((2 * k + d) :: R)) [target_tm]⊢*
    (cfg_AR (List.replicate k 0 ++ L) (d :: R)) := by
  induction k generalizing L with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, List.replicate, List.nil_append]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : 2 * (k + 1) + d = (2 * k + d) + 2 := by omega
    have h2 : List.replicate (k + 1) 0 ++ L = List.replicate k 0 ++ (0 :: L) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [h1, h2]
    exact stepStar_trans (stepPlus_stepStar (rule_AR_add_two L R (2 * k + d))) (ih (0 :: L))

theorem rule_AR_add_two_zero_all (L R : List ℕ) (a k : ℕ) :
    (cfg_AR ((2 * k + a) :: L) (0 :: R)) [target_tm]⊢*
    (cfg_AR (a :: L) (0 :: (fun R => bumpHead (bumpHead R))^[k] R)) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_zero, id_eq]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_eq : 2 * (k + 1) + a = 2 * k + a + 2 := by omega
    rw [h_eq, Function.iterate_succ_apply]
    exact stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero L R (2 * k + a)))
      (ih (bumpHead (bumpHead R)))

theorem rule_F_zero4_one (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfg_F (0 :: 0 :: 0 :: 0 :: 0 :: L) (0 :: d :: R)) [target_tm]⊢*
    (cfg_F (0 :: L) (0 :: (d + 8) :: R)) := by
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_zero (0 :: 0 :: 0 :: L) (0 :: d :: R))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_two (0 :: 0 :: L) (0 :: 0 :: d :: R))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: L) (1 :: 0 :: d :: R) 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: L) (3 :: 0 :: d :: R))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two (3 :: L) (0 :: d :: R) 2)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two (0 :: 3 :: L) (0 :: d :: R) 0)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 3 :: L) (0 :: d :: R))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (3 :: 3 :: L) R d)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (3 :: L) ((d + 1) :: R) 1)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_zero (3 :: L) ((d + 1 + 1 + 1) :: R))) ?_
  dsimp [bumpHead]
  have hd : d + 1 + 1 + 1 + 1 + 1 + 1 + 1 = d + 7 := by omega
  rw [hd]
  refine stepStar_trans (stepPlus_stepStar (rule_F_add_three L ((d + 7) :: R) 0)) ?_
  dsimp [bumpHead]
  exact ⟨0, rfl⟩

theorem rule_F_zero4_all (k r : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfg_F (List.replicate (4 * k + r + 1) 0 ++ L) (0 :: d :: R)) [target_tm]⊢*
    (cfg_F (List.replicate (r + 1) 0 ++ L) (0 :: (d + 8 * k) :: R)) := by
  induction k generalizing d with
  | zero =>
    simp
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_rep : List.replicate (4 * (k + 1) + r + 1) 0 ++ L =
        0 :: 0 :: 0 :: 0 :: 0 :: (List.replicate (4 * k + r) 0 ++ L) := by
      have h_eq : 4 * (k + 1) + r + 1 = 5 + (4 * k + r) := by omega
      rw [h_eq, List.replicate_add]
      rfl
    rw [h_rep]
    refine stepStar_trans (rule_F_zero4_one (List.replicate (4 * k + r) 0 ++ L) d R) ?_
    have h_rep2 : 0 :: (List.replicate (4 * k + r) 0 ++ L) = List.replicate (4 * k + r + 1) 0 ++ L := by
      rw [← List.cons_append, ← List.replicate_succ]
    rw [h_rep2]
    have hd : d + 8 * (k + 1) = (d + 8) + 8 * k := by omega
    rw [hd]
    exact ih (d + 8)

theorem rule_AR_zero_ones_all (m b : ℕ) (L R : List ℕ) :
    (cfg_AR (0 :: b :: L) (0 :: (List.replicate m 1 ++ R))) [target_tm]⊢*
    (cfg_AR (0 :: (b + 3 * m) :: L) (0 :: R)) := by
  induction m generalizing b with
  | zero =>
    simp
    exact ⟨0, rfl⟩
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (b :: L) (1 :: (List.replicate m 1 ++ R)))) ?_
    dsimp [bumpHead]
    refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two ((b + 3) :: L) (List.replicate m 1 ++ R) 0)) ?_
    have hb : b + 3 * (m + 1) = (b + 3) + 3 * m := by omega
    rw [hb]
    exact ih (b + 3)

theorem rule_AR_ones_all (m b : ℕ) (L R : List ℕ) :
    (cfg_AR (0 :: b :: L) (List.replicate (m + 1) 1 ++ R)) [target_tm]⊢*
    (cfg_AR (0 :: (b + 3 * m) :: L) (1 :: R)) := by
  induction m generalizing b with
  | zero =>
    simp
    exact ⟨0, rfl⟩
  | succ m ih =>
    have h_rep : List.replicate (m + 2) 1 ++ R = 1 :: 1 :: (List.replicate m 1 ++ R) := rfl
    rw [h_rep]
    refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (0 :: b :: L) (List.replicate m 1 ++ R) 1)) ?_
    refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (b :: L) (2 :: (List.replicate m 1 ++ R)))) ?_
    dsimp [bumpHead]
    refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two ((b + 3) :: L) (List.replicate m 1 ++ R) 1)) ?_
    have h_rep2 : 1 :: (List.replicate m 1 ++ R) = List.replicate (m + 1) 1 ++ R := rfl
    rw [h_rep2]
    have hb : b + 3 * (m + 1) = (b + 3) + 3 * m := by omega
    rw [hb]
    exact ih (b + 3)

-- ============================================================================
-- Section 3: 6-Rule Inductive Tower Algebra
-- ============================================================================

def A3 (k : ℕ) (tail : List ℕ) : List ℕ :=
  6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: tail

def A0 (k : ℕ) (tail : List ℕ) : List ℕ :=
  6 :: 0 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: tail

def B3 (k : ℕ) (tail : List ℕ) : List ℕ :=
  0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 3 :: 0 :: tail

def B0 (k : ℕ) (tail : List ℕ) : List ℕ :=
  0 :: 3 :: 3 :: 0 :: 0 :: (3 * k + 3) :: 0 :: 0 :: 0 :: tail

def SubStep (S S' : List ℕ) : Prop :=
  ∀ R_bot : List ℕ,
    (cfg_F (0 :: S) (9 :: R_bot)) [target_tm]⊢*
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: S') (0 :: R_bot))

def TopStep (S S' : List ℕ) : Prop :=
  (cfg_F (0 :: S) [5]) [target_tm]⊢* (cfg_F (0 :: S') [5])

def SubHalt (S : List ℕ) : Prop :=
  ∀ R_bot : List ℕ,
    ∃ cfg, ((cfg_F (0 :: S) (9 :: R_bot)) [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone

lemma topStep_refl (S : List ℕ) : TopStep S S := ⟨0, rfl⟩

lemma topStep_trans {S₁ S₂ S₃ : List ℕ} (h₁ : TopStep S₁ S₂) (h₂ : TopStep S₂ S₃) :
    TopStep S₁ S₃ := stepStar_trans h₁ h₂

lemma exit_sub (W : List ℕ) (R_bot : List ℕ) :
    (cfg_AR W (10 :: R_bot)) [target_tm]⊢* (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: W) (0 :: R_bot)) := by
  simpa using rule_AR_step2_all W R_bot 0 5

lemma exit_top (W : List ℕ) :
    (cfg_AR W [6]) [target_tm]⊢* (cfg_F (0 :: W) [5]) := by
  refine stepStar_trans (rule_AR_step2_all W [] 0 3) ?_
  dsimp [List.replicate]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 0 :: W) [])) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: W) [] 1)) ?_
  dsimp [bumpHead]
  exact stepPlus_stepStar (rule_AR_one_zero (0 :: W) [1])

theorem subStep_A_any (U : List ℕ) :
    SubStep (6 :: 0 :: 0 :: 0 :: U) (0 :: 3 :: 3 :: 0 :: 0 :: U) := by
  intro R_bot
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_add_two (0 :: 0 :: 0 :: U) (9 :: R_bot) 4)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) (0 :: 10 :: R_bot) 2)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) (2 :: 10 :: R_bot) 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 0 :: 0 :: U) (4 :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two (3 :: 0 :: 0 :: U) (10 :: R_bot) 3)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two (0 :: 3 :: 0 :: 0 :: U) (10 :: R_bot) 1)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (0 :: 0 :: 3 :: 0 :: 0 :: U) R_bot 10)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 3 :: 0 :: 0 :: U) (11 :: R_bot))) ?_
  dsimp [bumpHead]
  simpa using rule_AR_step2_all (3 :: 3 :: 0 :: 0 :: U) R_bot 0 6

theorem subStep_A3 (k : ℕ) (tail : List ℕ) : SubStep (A3 k tail) (B3 k tail) :=
  subStep_A_any ((3 * k + 3) :: 3 :: 0 :: tail)

theorem subStep_A0 (k : ℕ) (tail : List ℕ) : SubStep (A0 k tail) (B0 k tail) :=
  subStep_A_any ((3 * k + 3) :: 0 :: 0 :: 0 :: tail)

theorem top_A_to_B (U : List ℕ) :
    (cfg_F (0 :: 6 :: 0 :: 0 :: 0 :: U) [5]) [target_tm]⊢*
    (cfg_F (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [5]) := by
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_add_two (0 :: 0 :: 0 :: U) [5] 4)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) [0, 6] 2)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: 0 :: U) [2, 6] 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 0 :: 0 :: U) [4, 6])) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two (3 :: 0 :: 0 :: U) [6] 3)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two (0 :: 3 :: 0 :: 0 :: U) [6] 1)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (0 :: 0 :: 3 :: 0 :: 0 :: U) [] 6)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 3 :: 0 :: 0 :: U) [7])) ?_
  dsimp [bumpHead]
  refine stepStar_trans (rule_AR_step2_all (3 :: 3 :: 0 :: 0 :: U) [] 0 4) ?_
  dsimp [List.replicate]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [])) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [] 1)) ?_
  dsimp [bumpHead]
  exact stepPlus_stepStar (rule_AR_one_zero (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: U) [1])

theorem step_B_prefix (V : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_F (0 :: 0 :: 3 :: 3 :: 0 :: 0 :: V) (d₀ :: R_rest)) [target_tm]⊢*
    (cfg_F (0 :: 0 :: V) (9 :: 1 :: d₀ :: R_rest)) := by
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_zero (3 :: 3 :: 0 :: 0 :: V) (d₀ :: R_rest))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_add_three (3 :: 0 :: 0 :: V) (0 :: d₀ :: R_rest) 2)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_two (3 :: 0 :: 0 :: V) (0 :: 1 :: d₀ :: R_rest))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: V) (1 :: 1 :: d₀ :: R_rest) 3)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: V) (3 :: 1 :: d₀ :: R_rest) 1)) ?_
  dsimp [bumpHead]
  exact stepPlus_stepStar (rule_AR_one_zero (0 :: 0 :: V) (5 :: 1 :: d₀ :: R_rest))

theorem step_B0_core (k : ℕ) (tail : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_F (0 :: B0 k tail) (d₀ :: R_rest)) [target_tm]⊢*
    (cfg_AR (A3 (k + 1) tail) ((d₀ + 1) :: R_rest)) := by
  unfold B0
  refine stepStar_trans (step_B_prefix ((3 * k + 3) :: 0 :: 0 :: 0 :: tail) d₀ R_rest) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_zero ((3 * k + 3) :: 0 :: 0 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest))) ?_
  dsimp [bumpHead]
  have hk1 : 3 * k + 3 + 1 + 1 = 3 * (k + 1) + 2 := by omega
  rw [hk1]
  refine stepStar_trans (rule_F_step3_all (0 :: 0 :: 0 :: tail) (0 :: 9 :: 1 :: d₀ :: R_rest) 2 (k + 1)) ?_
  rw [stepF3Right_succ k (0 :: 9 :: 1 :: d₀ :: R_rest)]
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_two (0 :: 0 :: 0 :: tail)
    (0 :: (List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest))))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: 0 :: tail)
    (1 :: (List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest))) 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 0 :: tail)
    (3 :: (List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest))))) ?_
  dsimp [bumpHead]
  have h_rep : List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest) =
      List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest) := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  rw [h_rep]
  refine stepStar_trans (rule_AR_step2_all (3 :: 0 :: tail)
    (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest)) 0 2) ?_
  dsimp [List.replicate]
  refine stepStar_trans (rule_AR_zero_ones_all (k + 1) 0 (3 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest)) ?_
  rw [Nat.zero_add]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero ((3 * (k + 1)) :: 3 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (rule_AR_step2_all ((3 * (k + 1) + 3) :: 3 :: 0 :: tail) (1 :: d₀ :: R_rest) 0 5) ?_
  dsimp [List.replicate]
  refine stepStar_trans (rule_AR_zero_ones_all 1 0 (0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail) (d₀ :: R_rest)) ?_
  dsimp
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero
    (3 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 3 :: 0 :: tail) (d₀ :: R_rest))) ?_
  dsimp [bumpHead, A3]
  exact ⟨0, rfl⟩

theorem step_B3_pre (k : ℕ) (tail : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_F (0 :: B3 k tail) (d₀ :: R_rest)) [target_tm]⊢*
    (cfg_F (0 :: tail) (9 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest)))) := by
  unfold B3
  refine stepStar_trans (step_B_prefix ((3 * k + 3) :: 3 :: 0 :: tail) d₀ R_rest) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_zero ((3 * k + 3) :: 3 :: 0 :: tail) (9 :: 1 :: d₀ :: R_rest))) ?_
  dsimp [bumpHead]
  have hk1 : 3 * k + 3 + 1 + 1 = 3 * (k + 1) + 2 := by omega
  rw [hk1]
  refine stepStar_trans (rule_F_step3_all (3 :: 0 :: tail) (0 :: 9 :: 1 :: d₀ :: R_rest) 2 (k + 1)) ?_
  rw [stepF3Right_succ k (0 :: 9 :: 1 :: d₀ :: R_rest)]
  dsimp [bumpHead]
  have h_rep : List.replicate k 1 ++ (1 :: 9 :: 1 :: d₀ :: R_rest) =
      List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest) := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  rw [h_rep]
  refine stepStar_trans (stepPlus_stepStar (rule_F_two (3 :: 0 :: tail)
    (0 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: tail)
    (1 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))) 3)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (0 :: tail)
    (3 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))) 1)) ?_
  dsimp [bumpHead]
  exact stepPlus_stepStar (rule_AR_one_zero (0 :: tail)
    (5 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))))

theorem step_B3_post (k : ℕ) (tail' : List ℕ) (d₀ : ℕ) (R_rest : List ℕ) :
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: tail') (0 :: (List.replicate (k + 1) 1 ++ (9 :: 1 :: d₀ :: R_rest))))
      [target_tm]⊢*
    (cfg_AR (A0 (k + 1) tail') ((d₀ + 1) :: R_rest)) := by
  refine stepStar_trans (rule_AR_zero_ones_all (k + 1) 0 (0 :: 0 :: 0 :: tail') (9 :: 1 :: d₀ :: R_rest)) ?_
  rw [Nat.zero_add]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero ((3 * (k + 1)) :: 0 :: 0 :: 0 :: tail') (9 :: 1 :: d₀ :: R_rest))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (rule_AR_step2_all ((3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (1 :: d₀ :: R_rest) 0 5) ?_
  dsimp [List.replicate]
  refine stepStar_trans (rule_AR_zero_ones_all 1 0 (0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (d₀ :: R_rest)) ?_
  dsimp
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero
    (3 :: 0 :: 0 :: 0 :: (3 * (k + 1) + 3) :: 0 :: 0 :: 0 :: tail') (d₀ :: R_rest))) ?_
  dsimp [bumpHead, A0]
  exact ⟨0, rfl⟩

theorem subStep_B0 (k : ℕ) (tail : List ℕ) : SubStep (B0 k tail) (A3 (k + 1) tail) := by
  intro R_bot
  exact stepStar_trans (step_B0_core k tail 9 R_bot) (exit_sub (A3 (k + 1) tail) R_bot)

theorem topStep_A0 (k : ℕ) (tail : List ℕ) : TopStep (A0 k tail) (A3 (k + 1) tail) := by
  refine stepStar_trans (top_A_to_B ((3 * k + 3) :: 0 :: 0 :: 0 :: tail)) ?_
  exact stepStar_trans (step_B0_core k tail 5 []) (exit_top (A3 (k + 1) tail))

theorem subStep_B3 (k : ℕ) {tail tail' : List ℕ} (h : SubStep tail tail') :
    SubStep (B3 k tail) (A0 (k + 1) tail') := by
  intro R_bot
  refine stepStar_trans (step_B3_pre k tail 9 R_bot) ?_
  refine stepStar_trans (h (List.replicate (k + 1) 1 ++ (9 :: 1 :: 9 :: R_bot))) ?_
  exact stepStar_trans (step_B3_post k tail' 9 R_bot) (exit_sub (A0 (k + 1) tail') R_bot)

theorem topStep_A3 (k : ℕ) {tail tail' : List ℕ} (h : SubStep tail tail') :
    TopStep (A3 k tail) (A0 (k + 1) tail') := by
  refine stepStar_trans (top_A_to_B ((3 * k + 3) :: 3 :: 0 :: tail)) ?_
  refine stepStar_trans (step_B3_pre k tail 5 []) ?_
  refine stepStar_trans (h (List.replicate (k + 1) 1 ++ [9, 1, 5])) ?_
  exact stepStar_trans (step_B3_post k tail' 5 []) (exit_top (A0 (k + 1) tail'))

theorem subHalt_B3 (k : ℕ) {tail : List ℕ} (h : SubHalt tail) :
    SubHalt (B3 k tail) := by
  intro R_bot
  obtain ⟨cfg, h_steps, h_none⟩ := h (List.replicate (k + 1) 1 ++ (9 :: 1 :: 9 :: R_bot))
  exact ⟨cfg, stepStar_trans (step_B3_pre k tail 9 R_bot) h_steps, h_none⟩

theorem topHalt_A3 (k : ℕ) {tail : List ℕ} (h : SubHalt tail) :
    ∃ cfg, ((cfg_F (0 :: A3 k tail) [5]) [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone := by
  obtain ⟨cfg, h_steps, h_none⟩ := h (List.replicate (k + 1) 1 ++ [9, 1, 5])
  refine ⟨cfg, ?_, h_none⟩
  refine stepStar_trans (top_A_to_B ((3 * k + 3) :: 3 :: 0 :: tail)) ?_
  exact stepStar_trans (step_B3_pre k tail 5 []) h_steps

def TowerA3 : List ℕ → List ℕ → List ℕ
  | [], S => S
  | k :: ks, S => TowerA3 ks (A3 k S)

def TowerA0Out : List ℕ → List ℕ → List ℕ
  | [], S => S
  | k :: ks, S => A0 k (TowerA0Out ks S)

def forceNat {α : Type} (e : ℕ) (f : ℕ → α) : α :=
  Nat.rec (f 0) (fun v _ => f v) (Nat.add e 1)

@[simp]
lemma forceNat_eq {α : Type} (e : ℕ) (f : ℕ → α) : forceNat e f = f e := rfl

def stepTowerAt (c : ℕ) : List ℕ → List ℕ
  | [] => []
  | k :: ks => forceNat (k + c) (fun kc => forceNat (4 * c) (fun c4 => kc :: stepTowerAt c4 ks))

lemma stepTowerAt_ne_nil (c : ℕ) {ks : List ℕ} (hks : ks ≠ []) :
    stepTowerAt c ks ≠ [] := by
  cases ks with
  | nil => contradiction
  | cons _ _ => simp [stepTowerAt]

lemma stepTowerAt_length (c : ℕ) (ks : List ℕ) :
    (stepTowerAt c ks).length = ks.length := by
  induction ks generalizing c with
  | nil => rfl
  | cons k ks ih => simp [stepTowerAt, ih (4 * c)]

lemma stepTowerAt_four (ks : List ℕ) (c : ℕ) :
    (stepTowerAt c)^[4] ks = stepTowerAt (4 * c) ks := by
  induction ks generalizing c with
  | nil => rfl
  | cons k ks ih =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, stepTowerAt, forceNat_eq]
    have hk : k + c + c + c + c = k + 4 * c := by omega
    rw [hk]
    congr 1
    exact ih (4 * c)

theorem towerA3_topStep_len : ∀ (n : ℕ) (ks : List ℕ), ks.length = n + 1 →
    ∀ {S S' : List ℕ}, SubStep S S' →
    TopStep (TowerA3 ks S) (TowerA3 (stepTowerAt 2 ks) S')
  | 0, ks, hlen, S, S', h => by
    rcases ks with _ | ⟨k, _ | _⟩ <;> try simp at hlen
    simp only [TowerA3, stepTowerAt, forceNat_eq]
    exact topStep_trans (topStep_A3 k h) (topStep_A0 (k + 1) S')
  | n + 1, ks, hlen, S, S', h => by
    rcases ks with _ | ⟨k, ks_rest⟩
    · simp at hlen
    · simp only [TowerA3]
      have hlen0 : ks_rest.length = n + 1 := by simpa using hlen
      have hlen1 : (stepTowerAt 2 ks_rest).length = n + 1 := by
        rw [stepTowerAt_length]; exact hlen0
      have hlen2 : (stepTowerAt 2 (stepTowerAt 2 ks_rest)).length = n + 1 := by
        rw [stepTowerAt_length]; exact hlen1
      have hlen3 : (stepTowerAt 2 (stepTowerAt 2 (stepTowerAt 2 ks_rest))).length = n + 1 := by
        rw [stepTowerAt_length]; exact hlen2
      have h1 := towerA3_topStep_len n ks_rest hlen0 (subStep_A3 k S)
      have h2 := towerA3_topStep_len n _ hlen1 (subStep_B3 k h)
      have h3 := towerA3_topStep_len n _ hlen2 (subStep_A0 (k + 1) S')
      have h4 := towerA3_topStep_len n _ hlen3 (subStep_B0 (k + 1) S')
      have h_all := topStep_trans h1 (topStep_trans h2 (topStep_trans h3 h4))
      have h_iter : stepTowerAt 2 (stepTowerAt 2 (stepTowerAt 2 (stepTowerAt 2 ks_rest))) =
          (stepTowerAt 2)^[4] ks_rest := rfl
      rw [h_iter, stepTowerAt_four ks_rest 2] at h_all
      exact h_all

theorem towerA3_topStep (ks : List ℕ) (hks : ks ≠ []) {S S' : List ℕ} (h : SubStep S S') :
    TopStep (TowerA3 ks S) (TowerA3 (stepTowerAt 2 ks) S') := by
  cases hlen : ks.length with
  | zero => exact absurd (List.eq_nil_of_length_eq_zero hlen) hks
  | succ n => exact towerA3_topStep_len n ks hlen h

def absorbA0 (k : ℕ) (ks : List ℕ) : List ℕ :=
  match ks with
  | [] => [k + 1]
  | _ :: _ => (k + 1) :: stepTowerAt 2 (stepTowerAt 2 ks)

lemma absorbA0_ne_nil (k : ℕ) (ks : List ℕ) : absorbA0 k ks ≠ [] := by
  cases ks <;> simp [absorbA0]

theorem towerA3_absorb_A0 (k : ℕ) (ks : List ℕ) (U : List ℕ) :
    TopStep (TowerA3 ks (A0 k U)) (TowerA3 (absorbA0 k ks) U) := by
  cases ks with
  | nil =>
    simp only [TowerA3, absorbA0]
    exact topStep_A0 k U
  | cons k₀ ks₀ =>
    have hne : k₀ :: ks₀ ≠ [] := List.cons_ne_nil k₀ ks₀
    have h1 := towerA3_topStep (k₀ :: ks₀) hne (subStep_A0 k U)
    have h2 := towerA3_topStep (stepTowerAt 2 (k₀ :: ks₀)) (stepTowerAt_ne_nil 2 hne) (subStep_B0 k U)
    exact topStep_trans h1 h2

def absorbTowerA0Out : List ℕ → List ℕ → List ℕ
  | [], ks_top => ks_top
  | k :: ks_bot, ks_top => absorbTowerA0Out ks_bot (absorbA0 k ks_top)

lemma absorbTowerA0Out_ne_nil : ∀ (ks_bot ks_top : List ℕ),
    (ks_bot ≠ [] ∨ ks_top ≠ []) → absorbTowerA0Out ks_bot ks_top ≠ []
  | [], ks_top, h => by
    rcases h with h | h
    · contradiction
    · exact h
  | k :: ks_bot, ks_top, _ =>
    absorbTowerA0Out_ne_nil ks_bot (absorbA0 k ks_top) (Or.inr (absorbA0_ne_nil k ks_top))

theorem towerA3_absorb_towerA0Out : ∀ (ks_bot ks_top : List ℕ) (S : List ℕ),
    TopStep (TowerA3 ks_top (TowerA0Out ks_bot S))
            (TowerA3 (absorbTowerA0Out ks_bot ks_top) S)
  | [], ks_top, S => topStep_refl _
  | k :: ks_bot, ks_top, S => by
    simp only [TowerA0Out, absorbTowerA0Out]
    exact topStep_trans (towerA3_absorb_A0 k ks_top (TowerA0Out ks_bot S))
      (towerA3_absorb_towerA0Out ks_bot (absorbA0 k ks_top) S)

theorem towerA3_halt_len : ∀ (n : ℕ) (ks : List ℕ), ks.length = n + 1 →
    ∀ {S : List ℕ}, SubHalt S →
    ∃ cfg, ((cfg_F (0 :: TowerA3 ks S) [5]) [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone
  | 0, ks, hlen, S, h => by
    cases ks with
    | nil => contradiction
    | cons k ks' =>
      cases ks' with
      | nil => exact topHalt_A3 k h
      | cons _ _ => simp at hlen
  | n + 1, ks, hlen, S, h => by
    cases ks with
    | nil => contradiction
    | cons k ks_rest =>
      have hlen_rest : ks_rest.length = n + 1 := by simpa using hlen
      have hne_rest : ks_rest ≠ [] := by
        intro hnil; rw [hnil] at hlen_rest; contradiction
      have h_top := towerA3_topStep ks_rest hne_rest (subStep_A3 k S)
      have hlen_step : (stepTowerAt 2 ks_rest).length = n + 1 := by
        rw [stepTowerAt_length]; exact hlen_rest
      obtain ⟨cfg, h_halt, h_none⟩ := towerA3_halt_len n (stepTowerAt 2 ks_rest) hlen_step (subHalt_B3 k h)
      exact ⟨cfg, stepStar_trans h_top h_halt, h_none⟩

theorem towerA3_halt (ks : List ℕ) (hks : ks ≠ []) {S : List ℕ} (h : SubHalt S) :
    ∃ cfg, ((cfg_F (0 :: TowerA3 ks S) [5]) [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone := by
  cases hlen : ks.length with
  | zero => exact absurd (List.eq_nil_of_length_eq_zero hlen) hks
  | succ n => exact towerA3_halt_len n ks hlen h

lemma TowerA3_append : ∀ (ks₁ ks₂ : List ℕ) (S : List ℕ),
    TowerA3 (ks₁ ++ ks₂) S = TowerA3 ks₂ (TowerA3 ks₁ S)
  | [], _, _ => rfl
  | k :: ks₁, ks₂, S => by
    simp only [List.cons_append, TowerA3]
    exact TowerA3_append ks₁ ks₂ (A3 k S)

-- ============================================================================
-- Section 4: Computable RLE Stack Simulator (`stepGenRLE` & `runSubSim`)
-- ============================================================================

abbrev RLEStack := List (ℕ × ℕ)

def evalRLE : RLEStack → List ℕ
  | [] => []
  | (v, c) :: s => List.replicate c v ++ evalRLE s

def tailFor (isOpen : Bool) (bot : List ℕ) : List ℕ :=
  if isOpen then bot else []

def evalRLEWith (isOpen : Bool) (s : RLEStack) (bot : List ℕ) : List ℕ :=
  evalRLE s ++ tailFor isOpen bot

@[simp]
lemma evalRLEWith_false (s : RLEStack) (bot : List ℕ) :
    evalRLEWith false s bot = evalRLE s := by
  simp [evalRLEWith, tailFor]

@[simp]
lemma evalRLEWith_true (s : RLEStack) (bot : List ℕ) :
    evalRLEWith true s bot = evalRLE s ++ bot := by
  simp [evalRLEWith, tailFor]

def pushRun (v c : ℕ) (s : RLEStack) : RLEStack :=
  if c = 0 then s
  else match s with
    | [] => forceNat v (fun v0 => forceNat c (fun c0 => [(v0, c0)]))
    | (v', c') :: rest =>
      if v = v' then forceNat (c + c') (fun cc => (v', cc) :: rest)
      else forceNat v (fun v0 => forceNat c (fun c0 => (v0, c0) :: (v', c') :: rest))

lemma evalRLE_pushRun (v c : ℕ) (s : RLEStack) :
    evalRLE (pushRun v c s) = List.replicate c v ++ evalRLE s := by
  unfold pushRun
  split_ifs with hc
  · subst hc; rfl
  · cases s with
    | nil => simp [evalRLE]
    | cons hd rest =>
      rcases hd with ⟨v', c'⟩
      dsimp
      split_ifs with hv
      · subst hv
        rw [evalRLE, evalRLE, List.replicate_add, List.append_assoc]
      · simp [evalRLE]

lemma evalRLEWith_pushRun (isOpen : Bool) (v c : ℕ) (s : RLEStack) (bot : List ℕ) :
    evalRLEWith isOpen (pushRun v c s) bot = List.replicate c v ++ evalRLEWith isOpen s bot := by
  simp [evalRLEWith, evalRLE_pushRun, List.append_assoc]

lemma evalRLEWith_pushOne (isOpen : Bool) (v : ℕ) (s : RLEStack) (bot : List ℕ) :
    evalRLEWith isOpen (pushRun v 1 s) bot = v :: evalRLEWith isOpen s bot := by
  simpa using evalRLEWith_pushRun isOpen v 1 s bot

def popOne : RLEStack → Option (ℕ × RLEStack)
  | [] => none
  | (_, 0) :: s => popOne s
  | (v, c + 1) :: s => some (v, if c = 0 then s else (v, c) :: s)

lemma evalRLE_popOne_some : ∀ {s s' : RLEStack} {v : ℕ},
    popOne s = some (v, s') → evalRLE s = v :: evalRLE s'
  | [], _, _, h => by simp [popOne] at h
  | (_, 0) :: s, s', v, h => by
    simp only [popOne, evalRLE, List.replicate_zero, List.nil_append] at h ⊢
    exact evalRLE_popOne_some h
  | (w, c + 1) :: s, s', v, h => by
    simp only [popOne, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    split_ifs with hc
    · subst hc; simp [evalRLE]
    · simp [evalRLE, List.replicate_succ]

lemma evalRLE_popOne_none : ∀ {s : RLEStack},
    popOne s = none → evalRLE s = []
  | [], _ => rfl
  | (_, 0) :: s, h => by
    simp only [popOne, evalRLE, List.replicate_zero, List.nil_append] at h ⊢
    exact evalRLE_popOne_none h
  | (_, _ + 1) :: _, h => by simp [popOne] at h

lemma evalRLEWith_popOne_some {isOpen : Bool} {s s' : RLEStack} {v : ℕ} (bot : List ℕ)
    (h : popOne s = some (v, s')) :
    evalRLEWith isOpen s bot = v :: evalRLEWith isOpen s' bot := by
  simp [evalRLEWith, evalRLE_popOne_some h]

lemma evalRLEWith_popOne_none_closed {s : RLEStack} (bot : List ℕ)
    (h : popOne s = none) :
    evalRLEWith false s bot = [] := by
  simp [evalRLEWith, tailFor, evalRLE_popOne_none h]

def bumpTopOpt (isOpen : Bool) (k : ℕ) (s : RLEStack) : Option RLEStack :=
  match k with
  | 0 => some s
  | m + 1 =>
    match popOne s with
    | some (v, s') => some (pushRun (v + (m + 1)) 1 s')
    | none => if isOpen then none else some (pushRun m 1 [])

lemma evalRLEWith_bumpTopOpt {isOpen : Bool} {k : ℕ} {s s' : RLEStack} (bot : List ℕ)
    (h : bumpTopOpt isOpen k s = some s') :
    evalRLEWith isOpen s' bot = bumpHead^[k] (evalRLEWith isOpen s bot) := by
  cases k with
  | zero =>
    simp only [bumpTopOpt, Option.some.injEq] at h
    subst h
    rfl
  | succ m =>
    simp only [bumpTopOpt] at h
    cases hpop : popOne s with
    | some vp =>
      rcases vp with ⟨v, s₁⟩
      rw [hpop] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [evalRLEWith_pushOne, evalRLEWith_popOne_some bot hpop, bumpHead_iterate_cons]
    | none =>
      rw [hpop] at h
      cases isOpen with
      | true => simp at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        rw [evalRLEWith_pushOne, evalRLEWith_popOne_none_closed bot hpop,
            evalRLEWith, tailFor, evalRLE, bumpHead_iterate_nil]
        rfl

inductive GenStepResult where
  | stepped (mode : StackMode) (L R : RLEStack)
  | halted
  | abort
  deriving DecidableEq, Repr

def tryFastF (L R : RLEStack) : Option (RLEStack × RLEStack) :=
  match L with
  | [] => none
  | (v, c) :: L_rest =>
    match v with
    | 0 =>
      if 5 ≤ c then
        match popOne R with
        | none => none
        | some (r0, R₁) =>
          match r0 with
          | 0 =>
            match popOne R₁ with
            | none => none
            | some (d, R₂) =>
              let k := (c - 1) / 4
              let rem := (c - 1) % 4
              forceNat (rem + 1) (fun r1 =>
                some ((0, r1) :: L_rest, pushRun 0 1 (pushRun (d + 8 * k) 1 R₂)))
          | _ + 1 => none
      else none
    | _ + 1 => none

lemma tryFastF_sound {openL openR : Bool} {L R L' R' : RLEStack} (L_bot R_bot : List ℕ)
    (h : tryFastF L R = some (L', R')) :
    (cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (cfg_F (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold tryFastF at h
  rcases L with _ | ⟨⟨_ | v, c⟩, L_rest⟩
  · simp at h
  · dsimp at h
    split_ifs at h with hc
    cases hR1 : popOne R with
    | none => rw [hR1] at h; simp at h
    | some vp1 =>
      rcases vp1 with ⟨r0, R₁⟩
      rw [hR1] at h
      cases r0 with
      | succ _ => simp at h
      | zero =>
        dsimp at h
        cases hR2 : popOne R₁ with
        | none => rw [hR2] at h; simp at h
        | some vp2 =>
          rcases vp2 with ⟨d, R₂⟩
          rw [hR2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hL : evalRLEWith openL ((0, c) :: L_rest) L_bot =
              List.replicate (4 * ((c - 1) / 4) + ((c - 1) % 4) + 1) 0 ++
              evalRLEWith openL L_rest L_bot := by
            have h_eq : c = 4 * ((c - 1) / 4) + ((c - 1) % 4) + 1 := by omega
            simp [evalRLEWith, evalRLE, List.append_assoc, ← h_eq]
          have hL' : evalRLEWith openL ((0, (c - 1) % 4 + 1) :: L_rest) L_bot =
              List.replicate ((c - 1) % 4 + 1) 0 ++ evalRLEWith openL L_rest L_bot := by
            simp [evalRLEWith, evalRLE, List.append_assoc]
          have hR : evalRLEWith openR R R_bot = 0 :: d :: evalRLEWith openR R₂ R_bot := by
            rw [evalRLEWith_popOne_some R_bot hR1, evalRLEWith_popOne_some R_bot hR2]
          have hR' : evalRLEWith openR (pushRun 0 1 (pushRun (d + 8 * ((c - 1) / 4)) 1 R₂)) R_bot =
              0 :: (d + 8 * ((c - 1) / 4)) :: evalRLEWith openR R₂ R_bot := by
            rw [evalRLEWith_pushOne, evalRLEWith_pushOne]
          rw [hL, hL', hR, hR']
          exact rule_F_zero4_all ((c - 1) / 4) ((c - 1) % 4) (evalRLEWith openL L_rest L_bot)
            d (evalRLEWith openR R₂ R_bot)
  · simp at h

def tryFastAR_ones (fast1 : Bool) (L R : RLEStack) : Option (RLEStack × RLEStack) :=
  if !fast1 then none
  else match R with
    | [] => none
    | (v, c) :: R_rest =>
      match v with
      | 0 => none
      | 1 =>
        if 2 ≤ c then
          match popOne L with
          | none => none
          | some (l0, L₁) =>
            match l0 with
            | 0 =>
              match popOne L₁ with
              | none => none
              | some (b, L₂) =>
                let m := c - 1
                some (pushRun 0 1 (pushRun (b + 3 * m) 1 L₂), (1, 1) :: R_rest)
            | _ + 1 => none
        else none
      | _ + 2 => none

lemma tryFastAR_ones_sound {openL openR fast1 : Bool} {L R L' R' : RLEStack}
    (L_bot R_bot : List ℕ) (h : tryFastAR_ones fast1 L R = some (L', R')) :
    (cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (cfg_AR (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold tryFastAR_ones at h
  cases fast1
  · simp at h
  · rcases R with _ | ⟨⟨_ | _ | v, c⟩, R_rest⟩
    · simp at h
    · simp at h
    · dsimp at h
      split_ifs at h with hc
      cases hL1 : popOne L with
      | none => rw [hL1] at h; simp at h
      | some vp1 =>
        rcases vp1 with ⟨l0, L₁⟩
        rw [hL1] at h
        cases l0 with
        | succ _ => simp at h
        | zero =>
          dsimp at h
          cases hL2 : popOne L₁ with
          | none => rw [hL2] at h; simp at h
          | some vp2 =>
            rcases vp2 with ⟨b, L₂⟩
            rw [hL2] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hL : evalRLEWith openL L L_bot = 0 :: b :: evalRLEWith openL L₂ L_bot := by
              rw [evalRLEWith_popOne_some L_bot hL1, evalRLEWith_popOne_some L_bot hL2]
            have hL' : evalRLEWith openL (pushRun 0 1 (pushRun (b + 3 * (c - 1)) 1 L₂)) L_bot =
                0 :: (b + 3 * (c - 1)) :: evalRLEWith openL L₂ L_bot := by
              rw [evalRLEWith_pushOne, evalRLEWith_pushOne]
            have hR : evalRLEWith openR ((1, c) :: R_rest) R_bot =
                List.replicate ((c - 1) + 1) 1 ++ evalRLEWith openR R_rest R_bot := by
              have hc_eq : c = (c - 1) + 1 := by omega
              simp [evalRLEWith, evalRLE, List.append_assoc, ← hc_eq]
            have hR' : evalRLEWith openR ((1, 1) :: R_rest) R_bot =
                1 :: evalRLEWith openR R_rest R_bot := by
              simp [evalRLEWith, evalRLE]
            rw [hL, hL', hR, hR']
            exact rule_AR_ones_all (c - 1) b (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R_rest R_bot)
    · simp at h

def tryFastAR_zeroOnes (L R : RLEStack) : Option (RLEStack × RLEStack) :=
  match R with
  | [] => none
  | (v1, c1) :: R_tail =>
    match R_tail with
    | [] => none
    | (v2, m) :: R_rest =>
      if v1 == 0 && c1 == 1 && v2 == 1 && 1 ≤ m then
        match popOne L with
        | none => none
        | some (l0, L₁) =>
          match l0 with
          | 0 =>
            match popOne L₁ with
            | none => none
            | some (b, L₂) =>
              some (pushRun 0 1 (pushRun (b + 3 * m) 1 L₂), pushRun 0 1 R_rest)
          | _ + 1 => none
      else none

lemma tryFastAR_zeroOnes_sound {openL openR : Bool} {L R L' R' : RLEStack}
    (L_bot R_bot : List ℕ) (h : tryFastAR_zeroOnes L R = some (L', R')) :
    (cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (cfg_AR (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold tryFastAR_zeroOnes at h
  rcases R with _ | ⟨⟨v1, c1⟩, _ | ⟨⟨v2, m⟩, R_rest⟩⟩
  · simp at h
  · simp at h
  · dsimp at h
    split_ifs at h with hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hm⟩
    cases hL1 : popOne L with
    | none => rw [hL1] at h; simp at h
    | some vp1 =>
      rcases vp1 with ⟨l0, L₁⟩
      rw [hL1] at h
      cases l0 with
      | succ _ => simp at h
      | zero =>
        dsimp at h
        cases hL2 : popOne L₁ with
        | none => rw [hL2] at h; simp at h
        | some vp2 =>
          rcases vp2 with ⟨b, L₂⟩
          rw [hL2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hL : evalRLEWith openL L L_bot = 0 :: b :: evalRLEWith openL L₂ L_bot := by
            rw [evalRLEWith_popOne_some L_bot hL1, evalRLEWith_popOne_some L_bot hL2]
          have hL' : evalRLEWith openL (pushRun 0 1 (pushRun (b + 3 * m) 1 L₂)) L_bot =
              0 :: (b + 3 * m) :: evalRLEWith openL L₂ L_bot := by
            rw [evalRLEWith_pushOne, evalRLEWith_pushOne]
          have hR : evalRLEWith openR ((0, 1) :: (1, m) :: R_rest) R_bot =
              0 :: (List.replicate m 1 ++ evalRLEWith openR R_rest R_bot) := by
            simp [evalRLEWith, evalRLE, List.append_assoc]
          have hR' : evalRLEWith openR (pushRun 0 1 R_rest) R_bot =
              0 :: evalRLEWith openR R_rest R_bot := by
            rw [evalRLEWith_pushOne]
          rw [hL, hL', hR, hR']
          exact rule_AR_zero_ones_all m b (evalRLEWith openL L₂ L_bot)
            (evalRLEWith openR R_rest R_bot)

def stepGenF_slow (openL openR : Bool) (L R : RLEStack) : GenStepResult :=
  match popOne L with
  | none =>
    if openL then .abort
    else .stepped .AR (pushRun 1 1 []) R
  | some (a, L₁) =>
    match a with
    | 0 =>
      match popOne L₁ with
      | none =>
        if openL then .abort
        else match bumpTopOpt openR 1 R with
          | none => .abort
          | some R₁ => .stepped .F [] (pushRun 0 1 R₁)
      | some (b, L₂) =>
        match b with
        | 0 =>
          match bumpTopOpt openL 2 L₂ with
          | none => .abort
          | some L₃ => .stepped .F L₃ (pushRun 0 1 R)
        | 1 =>
          match bumpTopOpt openR 1 R with
          | none => .abort
          | some R₁ => .stepped .F L₂ (pushRun 2 1 R₁)
        | b' + 2 =>
          match bumpTopOpt openR 1 R with
          | none => .abort
          | some R₁ => .stepped .AR (pushRun b' 1 L₂) (pushRun 0 2 R₁)
    | 1 => .halted
    | 2 =>
      match bumpTopOpt openL 2 L₁ with
      | none => .abort
      | some L₂ =>
        match bumpTopOpt openR 1 R with
        | none => .abort
        | some R₁ => .stepped .AR L₂ (pushRun 0 1 R₁)
    | a' + 3 =>
      match bumpTopOpt openR 1 R with
      | none => .abort
      | some R₁ =>
        .stepped .F (pushRun (a' % 3) 1 L₁)
          (pushRun 0 1 (pushRun 1 (a' / 3) R₁))

lemma stepGenF_slow_sound_step {openL openR : Bool} {L R L' R' : RLEStack} {mode' : StackMode}
    (L_bot R_bot : List ℕ) (h : stepGenF_slow openL openR L R = .stepped mode' L' R') :
    (cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold stepGenF_slow at h
  cases hpopL : popOne L with
  | none =>
    rw [hpopL] at h
    cases openL with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rw [evalStackCfg_AR, evalRLEWith_popOne_none_closed L_bot hpopL]
      have h1 : evalRLEWith false (pushRun 1 1 []) L_bot = [1] := by
        simp [evalRLEWith, tailFor, pushRun, evalRLE]
      rw [h1]
      exact stepPlus_stepStar (rule_F_nil (evalRLEWith openR R R_bot))
  | some vp =>
    rcases vp with ⟨a, L₁⟩
    rw [hpopL] at h
    have hL : evalRLEWith openL L L_bot = a :: evalRLEWith openL L₁ L_bot :=
      evalRLEWith_popOne_some L_bot hpopL
    rcases a with _ | _ | _ | a'
    · dsimp at h
      cases hpopL1 : popOne L₁ with
      | none =>
        rw [hpopL1] at h
        cases openL with
        | true => simp at h
        | false =>
          dsimp at h
          cases hR1 : bumpTopOpt openR 1 R with
          | none => rw [hR1] at h; simp at h
          | some R₁ =>
            rw [hR1] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, evalRLEWith_popOne_none_closed L_bot hpopL1,
                evalRLEWith_pushOne, evalRLEWith_bumpTopOpt R_bot hR1]
            simpa [evalRLEWith, tailFor, evalRLE] using
              stepPlus_stepStar (rule_F_zero_nil (evalRLEWith openR R R_bot))
      | some vp2 =>
        rcases vp2 with ⟨b, L₂⟩
        rw [hpopL1] at h
        have hL1 : evalRLEWith openL L₁ L_bot = b :: evalRLEWith openL L₂ L_bot :=
          evalRLEWith_popOne_some L_bot hpopL1
        rcases b with _ | _ | b'
        · dsimp at h
          cases hL2 : bumpTopOpt openL 2 L₂ with
          | none => rw [hL2] at h; simp at h
          | some L₃ =>
            rw [hL2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, hL1, evalRLEWith_bumpTopOpt L_bot hL2, evalRLEWith_pushOne]
            exact stepPlus_stepStar (rule_F_zero_zero (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R R_bot))
        · dsimp at h
          cases hR1 : bumpTopOpt openR 1 R with
          | none => rw [hR1] at h; simp at h
          | some R₁ =>
            rw [hR1] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, hL1, evalRLEWith_pushOne, evalRLEWith_bumpTopOpt R_bot hR1]
            exact stepPlus_stepStar (rule_F_zero_one (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R R_bot))
        · dsimp at h
          cases hR1 : bumpTopOpt openR 1 R with
          | none => rw [hR1] at h; simp at h
          | some R₁ =>
            rw [hR1] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            rw [evalStackCfg_AR, hL, hL1, evalRLEWith_pushOne, evalRLEWith_pushRun,
                evalRLEWith_bumpTopOpt R_bot hR1]
            exact stepPlus_stepStar (rule_F_zero_add_two (evalRLEWith openL L₂ L_bot)
              (evalRLEWith openR R R_bot) b')
    · simp at h
    · dsimp at h
      cases hL2 : bumpTopOpt openL 2 L₁ with
      | none => rw [hL2] at h; simp at h
      | some L₂ =>
        rw [hL2] at h
        dsimp at h
        cases hR1 : bumpTopOpt openR 1 R with
        | none => rw [hR1] at h; simp at h
        | some R₁ =>
          rw [hR1] at h
          simp only [GenStepResult.stepped.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [evalStackCfg_AR, hL, evalRLEWith_bumpTopOpt L_bot hL2, evalRLEWith_pushOne,
              evalRLEWith_bumpTopOpt R_bot hR1]
          exact stepPlus_stepStar (rule_F_two (evalRLEWith openL L₁ L_bot)
            (evalRLEWith openR R R_bot))
    · dsimp at h
      cases hR1 : bumpTopOpt openR 1 R with
      | none => rw [hR1] at h; simp at h
      | some R₁ =>
        rw [hR1] at h
        simp only [GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have hL_eq : evalRLEWith openL L L_bot =
            (3 * (a' / 3 + 1) + (a' % 3)) :: evalRLEWith openL L₁ L_bot := by
          rw [hL]; congr 1; omega
        rw [evalStackCfg_F, hL_eq, evalRLEWith_pushOne, evalRLEWith_pushOne,
            evalRLEWith_pushRun, evalRLEWith_bumpTopOpt R_bot hR1]
        have h_step := rule_F_step3_all (evalRLEWith openL L₁ L_bot) (evalRLEWith openR R R_bot)
          (a' % 3) (a' / 3 + 1)
        rw [stepF3Right_succ] at h_step
        exact h_step

lemma stepGenF_slow_sound_halt {openL openR : Bool} {L R : RLEStack}
    (L_bot R_bot : List ℕ) (h : stepGenF_slow openL openR L R = .halted) :
    ∃ cfg, ((cfg_F (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢* cfg) ∧
      (step target_tm cfg).isNone := by
  unfold stepGenF_slow at h
  cases hpopL : popOne L with
  | none =>
    rw [hpopL] at h
    cases openL <;> simp at h
  | some vp =>
    rcases vp with ⟨a, L₁⟩
    rw [hpopL] at h
    rcases a with _ | _ | _ | a'
    · dsimp at h
      cases hpopL1 : popOne L₁ with
      | none =>
        rw [hpopL1] at h
        cases openL with
        | true => simp at h
        | false =>
          dsimp at h
          cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
      | some vp2 =>
        rcases vp2 with ⟨b, L₂⟩
        rw [hpopL1] at h
        rcases b with _ | _ | b'
        · dsimp at h; cases hL2 : bumpTopOpt openL 2 L₂ <;> simp [hL2] at h
        · dsimp at h; cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
        · dsimp at h; cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
    · rw [evalRLEWith_popOne_some L_bot hpopL]
      exact rule_F_one_halt (evalRLEWith openL L₁ L_bot) (evalRLEWith openR R R_bot)
    · dsimp at h
      cases hL2 : bumpTopOpt openL 2 L₁ with
      | none => rw [hL2] at h; simp at h
      | some L₂ =>
        rw [hL2] at h
        dsimp at h
        cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h
    · dsimp at h
      cases hR1 : bumpTopOpt openR 1 R <;> simp [hR1] at h

def stepGenAR_slow (openL openR : Bool) (L R : RLEStack) : GenStepResult :=
  match popOne R with
  | none =>
    if openR then .abort
    else .stepped .F L (pushRun 1 1 [])
  | some (d, R₁) =>
    match d with
    | 0 =>
      match popOne L with
      | none =>
        if openL then .abort
        else match bumpTopOpt openR 2 R₁ with
          | none => .abort
          | some R₂ => .stepped .F [] R₂
      | some (a, L₁) =>
        match a with
        | 0 =>
          match bumpTopOpt openL 3 L₁ with
          | none => .abort
          | some L₂ =>
            match bumpTopOpt openR 1 R₁ with
            | none => .abort
            | some R₂ => .stepped .AR L₂ R₂
        | 1 =>
          match bumpTopOpt openR 4 R₁ with
          | none => .abort
          | some R₂ => .stepped .F L₁ R₂
        | a' + 2 =>
          let k := (a' + 2) / 2
          match bumpTopOpt openR (2 * k) R₁ with
          | none => .abort
          | some R₂ => .stepped .AR (pushRun ((a' + 2) % 2) 1 L₁) (pushRun 0 1 R₂)
    | 1 =>
      match popOne R₁ with
      | none =>
        if openR then .abort
        else .stepped .AR (pushRun 0 1 L) []
      | some (e, R₂) =>
        .stepped .AR L (pushRun 0 1 (pushRun (e + 1) 1 R₂))
    | d' + 2 =>
      let k := (d' + 2) / 2
      .stepped .AR (pushRun 0 k L) (pushRun ((d' + 2) % 2) 1 R₁)

lemma stepGenAR_slow_sound_step {openL openR : Bool} {L R L' R' : RLEStack} {mode' : StackMode}
    (L_bot R_bot : List ℕ) (h : stepGenAR_slow openL openR L R = .stepped mode' L' R') :
    (cfg_AR (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold stepGenAR_slow at h
  cases hpopR : popOne R with
  | none =>
    rw [hpopR] at h
    cases openR with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rw [evalStackCfg_F, evalRLEWith_popOne_none_closed R_bot hpopR]
      have h1 : evalRLEWith false (pushRun 1 1 []) R_bot = [1] := by
        simp [evalRLEWith, tailFor, pushRun, evalRLE]
      rw [h1]
      exact stepPlus_stepStar (rule_AR_nil (evalRLEWith openL L L_bot))
  | some vp =>
    rcases vp with ⟨d, R₁⟩
    rw [hpopR] at h
    have hR : evalRLEWith openR R R_bot = d :: evalRLEWith openR R₁ R_bot :=
      evalRLEWith_popOne_some R_bot hpopR
    rcases d with _ | _ | d'
    · dsimp at h
      cases hpopL : popOne L with
      | none =>
        rw [hpopL] at h
        cases openL with
        | true => simp at h
        | false =>
          dsimp at h
          cases hR2 : bumpTopOpt openR 2 R₁ with
          | none => rw [hR2] at h; simp at h
          | some R₂ =>
            rw [hR2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hR, evalRLEWith_popOne_none_closed L_bot hpopL,
                evalRLEWith_bumpTopOpt R_bot hR2]
            simpa [evalRLEWith, tailFor, evalRLE] using
              stepPlus_stepStar (rule_AR_nil_zero (evalRLEWith openR R₁ R_bot))
      | some vpL =>
        rcases vpL with ⟨a, L₁⟩
        rw [hpopL] at h
        have hL : evalRLEWith openL L L_bot = a :: evalRLEWith openL L₁ L_bot :=
          evalRLEWith_popOne_some L_bot hpopL
        rcases a with _ | _ | a'
        · dsimp at h
          cases hL2 : bumpTopOpt openL 3 L₁ with
          | none => rw [hL2] at h; simp at h
          | some L₂ =>
            rw [hL2] at h
            dsimp at h
            cases hR2 : bumpTopOpt openR 1 R₁ with
            | none => rw [hR2] at h; simp at h
            | some R₂ =>
              rw [hR2] at h
              simp only [GenStepResult.stepped.injEq] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              rw [evalStackCfg_AR, hL, hR, evalRLEWith_bumpTopOpt L_bot hL2,
                  evalRLEWith_bumpTopOpt R_bot hR2]
              exact stepPlus_stepStar (rule_AR_zero_zero (evalRLEWith openL L₁ L_bot)
                (evalRLEWith openR R₁ R_bot))
        · dsimp at h
          cases hR2 : bumpTopOpt openR 4 R₁ with
          | none => rw [hR2] at h; simp at h
          | some R₂ =>
            rw [hR2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            rw [evalStackCfg_F, hL, hR, evalRLEWith_bumpTopOpt R_bot hR2]
            exact stepPlus_stepStar (rule_AR_one_zero (evalRLEWith openL L₁ L_bot)
              (evalRLEWith openR R₁ R_bot))
        · dsimp at h
          cases hR2 : bumpTopOpt openR (2 * ((a' + 2) / 2)) R₁ with
          | none => rw [hR2] at h; simp at h
          | some R₂ =>
            rw [hR2] at h
            simp only [GenStepResult.stepped.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            have hL_eq : evalRLEWith openL L L_bot =
                (2 * ((a' + 2) / 2) + ((a' + 2) % 2)) :: evalRLEWith openL L₁ L_bot := by
              rw [hL]; congr 1; omega
            rw [evalStackCfg_AR, hL_eq, hR, evalRLEWith_pushOne, evalRLEWith_pushOne,
                evalRLEWith_bumpTopOpt R_bot hR2, ← bumpHead2_iterate_eq]
            exact rule_AR_add_two_zero_all (evalRLEWith openL L₁ L_bot)
              (evalRLEWith openR R₁ R_bot) ((a' + 2) % 2) ((a' + 2) / 2)
    · dsimp at h
      cases hpopR1 : popOne R₁ with
      | none =>
        rw [hpopR1] at h
        cases openR with
        | true => simp at h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, GenStepResult.stepped.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [evalStackCfg_AR, hR, evalRLEWith_popOne_none_closed R_bot hpopR1,
              evalRLEWith_pushOne]
          simpa [evalRLEWith, tailFor, evalRLE] using
            stepPlus_stepStar (rule_AR_one_nil (evalRLEWith openL L L_bot))
      | some vpR2 =>
        rcases vpR2 with ⟨e, R₂⟩
        rw [hpopR1] at h
        dsimp at h
        simp only [GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        rw [evalStackCfg_AR, hR, evalRLEWith_popOne_some R_bot hpopR1,
            evalRLEWith_pushOne, evalRLEWith_pushOne]
        exact stepPlus_stepStar (rule_AR_one_cons (evalRLEWith openL L L_bot)
          (evalRLEWith openR R₂ R_bot) e)
    · dsimp at h
      simp only [GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hR_eq : evalRLEWith openR R R_bot =
          (2 * ((d' + 2) / 2) + ((d' + 2) % 2)) :: evalRLEWith openR R₁ R_bot := by
        rw [hR]; congr 1; omega
      rw [evalStackCfg_AR, hR_eq, evalRLEWith_pushRun, evalRLEWith_pushOne]
      exact rule_AR_step2_all (evalRLEWith openL L L_bot) (evalRLEWith openR R₁ R_bot)
        ((d' + 2) % 2) ((d' + 2) / 2)

lemma stepGenAR_slow_not_halt (openL openR : Bool) (L R : RLEStack) :
    stepGenAR_slow openL openR L R ≠ .halted := by
  unfold stepGenAR_slow
  cases popOne R with
  | none => cases openR <;> simp
  | some vp =>
    rcases vp with ⟨d, R₁⟩
    rcases d with _ | _ | d'
    · dsimp
      cases popOne L with
      | none =>
        cases openL with
        | true => simp
        | false => dsimp; cases bumpTopOpt openR 2 R₁ <;> simp
      | some vpL =>
        rcases vpL with ⟨a, L₁⟩
        rcases a with _ | _ | a'
        · dsimp
          cases bumpTopOpt openL 3 L₁ with
          | none => simp
          | some _ => dsimp; cases bumpTopOpt openR 1 R₁ <;> simp
        · dsimp; cases bumpTopOpt openR 4 R₁ <;> simp
        · dsimp; cases bumpTopOpt openR (2 * ((a' + 2) / 2)) R₁ <;> simp
    · dsimp
      cases popOne R₁ with
      | none => cases openR <;> simp
      | some vp2 => rcases vp2 with ⟨_, _⟩; simp
    · simp

def stepGenRLE (openL openR fast1 : Bool) (mode : StackMode) (L R : RLEStack) : GenStepResult :=
  match mode with
  | .F =>
    match tryFastF L R with
    | some (L', R') => .stepped .F L' R'
    | none => stepGenF_slow openL openR L R
  | .AR =>
    match tryFastAR_ones fast1 L R with
    | some (L', R') => .stepped .AR L' R'
    | none =>
      match tryFastAR_zeroOnes L R with
      | some (L', R') => .stepped .AR L' R'
      | none => stepGenAR_slow openL openR L R

lemma stepGenRLE_sound_step {openL openR fast1 : Bool} {mode mode' : StackMode}
    {L R L' R' : RLEStack} (L_bot R_bot : List ℕ)
    (h : stepGenRLE openL openR fast1 mode L R = .stepped mode' L' R') :
    (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot)) := by
  unfold stepGenRLE at h
  cases mode with
  | F =>
    cases hfast : tryFastF L R with
    | some vp =>
      rcases vp with ⟨Lf, Rf⟩
      rw [hfast] at h
      simp only [GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact tryFastF_sound L_bot R_bot hfast
    | none =>
      rw [hfast] at h
      exact stepGenF_slow_sound_step L_bot R_bot h
  | AR =>
    cases hfast1 : tryFastAR_ones fast1 L R with
    | some vp =>
      rcases vp with ⟨Lf, Rf⟩
      rw [hfast1] at h
      simp only [GenStepResult.stepped.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact tryFastAR_ones_sound L_bot R_bot hfast1
    | none =>
      rw [hfast1] at h
      cases hfast2 : tryFastAR_zeroOnes L R with
      | some vp =>
        rcases vp with ⟨Lf, Rf⟩
        rw [hfast2] at h
        simp only [GenStepResult.stepped.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact tryFastAR_zeroOnes_sound L_bot R_bot hfast2
      | none =>
        rw [hfast2] at h
        exact stepGenAR_slow_sound_step L_bot R_bot h

lemma stepGenRLE_sound_halt {openL openR fast1 : Bool} {mode : StackMode} {L R : RLEStack}
    (L_bot R_bot : List ℕ) (h : stepGenRLE openL openR fast1 mode L R = .halted) :
    ∃ cfg, ((evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢* cfg) ∧
      (step target_tm cfg).isNone := by
  unfold stepGenRLE at h
  cases mode with
  | F =>
    cases hfast : tryFastF L R with
    | some vp =>
      rcases vp with ⟨_, _⟩
      rw [hfast] at h
      simp at h
    | none =>
      rw [hfast] at h
      exact stepGenF_slow_sound_halt L_bot R_bot h
  | AR =>
    cases hfast1 : tryFastAR_ones fast1 L R with
    | some vp =>
      rcases vp with ⟨_, _⟩
      rw [hfast1] at h
      simp at h
    | none =>
      rw [hfast1] at h
      cases hfast2 : tryFastAR_zeroOnes L R with
      | some vp =>
        rcases vp with ⟨_, _⟩
        rw [hfast2] at h
        simp at h
      | none =>
        rw [hfast2] at h
        exact absurd h (stepGenAR_slow_not_halt openL openR L R)

def runStepsRLE : ℕ → Bool → Bool → Bool → StackMode → RLEStack → RLEStack → GenStepResult
  | 0, _, _, _, mode, L, R => .stepped mode L R
  | n + 1, openL, openR, fast1, mode, L, R =>
    match stepGenRLE openL openR fast1 mode L R with
    | .stepped mode₁ L₁ R₁ => runStepsRLE n openL openR fast1 mode₁ L₁ R₁
    | .halted => .halted
    | .abort => .abort

lemma runStepsRLE_sound_step : ∀ {n : ℕ} {openL openR fast1 : Bool} {mode mode' : StackMode}
    {L R L' R' : RLEStack} (L_bot R_bot : List ℕ),
    runStepsRLE n openL openR fast1 mode L R = .stepped mode' L' R' →
    (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith openR R R_bot)) [target_tm]⊢*
    (evalStackCfg mode' (evalRLEWith openL L' L_bot) (evalRLEWith openR R' R_bot))
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by
    simp only [runStepsRLE, GenStepResult.stepped.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, rfl⟩
  | n + 1, openL, openR, fast1, mode, mode', L, R, L', R', L_bot, R_bot, h => by
    unfold runStepsRLE at h
    cases hstep : stepGenRLE openL openR fast1 mode L R with
    | stepped mode₁ L₁ R₁ =>
      rw [hstep] at h
      exact stepStar_trans (stepGenRLE_sound_step L_bot R_bot hstep)
        (runStepsRLE_sound_step L_bot R_bot h)
    | halted => rw [hstep] at h; simp at h
    | abort => rw [hstep] at h; simp at h

def peelZeros : ℕ → RLEStack → Option RLEStack
  | 0, s => some s
  | n + 1, s =>
    match popOne s with
    | none => none
    | some (v, s') =>
      match v with
      | 0 => peelZeros n s'
      | _ + 1 => none

lemma evalRLE_peelZeros : ∀ {n : ℕ} {s s' : RLEStack},
    peelZeros n s = some s' → evalRLE s = List.replicate n 0 ++ evalRLE s'
  | 0, _, _, h => by
    simp only [peelZeros, Option.some.injEq] at h
    subst h
    rfl
  | n + 1, s, s', h => by
    unfold peelZeros at h
    cases hpop : popOne s with
    | none => rw [hpop] at h; simp at h
    | some vp =>
      rcases vp with ⟨v, s₁⟩
      rw [hpop] at h
      cases v with
      | succ _ => simp at h
      | zero =>
        dsimp at h
        rw [evalRLE_popOne_some hpop, evalRLE_peelZeros h]
        rfl

lemma evalRLEWith_peelZeros {isOpen : Bool} {n : ℕ} {s s' : RLEStack} (bot : List ℕ)
    (h : peelZeros n s = some s') :
    evalRLEWith isOpen s bot = List.replicate n 0 ++ evalRLEWith isOpen s' bot := by
  simp [evalRLEWith, evalRLE_peelZeros h, List.append_assoc]

def isSingleVal (v : ℕ) (s : RLEStack) : Bool :=
  match popOne s with
  | some (w, s') => (w == v) && (popOne s').isNone
  | none => false

lemma evalRLEWith_isSingleVal {v : ℕ} {s : RLEStack} (bot : List ℕ)
    (h : isSingleVal v s = true) :
    evalRLEWith true s bot = v :: bot := by
  unfold isSingleVal at h
  cases hpop1 : popOne s with
  | none => rw [hpop1] at h; simp at h
  | some vp =>
    rcases vp with ⟨w, s'⟩
    rw [hpop1] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
    rcases h with ⟨rfl, hpop2⟩
    simp [evalRLEWith, tailFor, evalRLE_popOne_some hpop1, evalRLE_popOne_none hpop2]

lemma evalRLE_isSingleVal {v : ℕ} {s : RLEStack} (h : isSingleVal v s = true) :
    evalRLE s = [v] := by
  have h1 := evalRLEWith_isSingleVal [] h
  simpa [evalRLEWith, tailFor] using h1

inductive SubSimResult where
  | stepped (S' : RLEStack)
  | halted
  | abort
  deriving DecidableEq, Repr

def runSubLoop : ℕ → Bool → Bool → StackMode → RLEStack → RLEStack → SubSimResult
  | 0, _, _, _, _, _ => .abort
  | fuel + 1, openL, fast1, mode, L, R =>
    if mode == .AR && isSingleVal 0 R then
      match peelZeros 5 L with
      | some S' => .stepped S'
      | none => .abort
    else
      match stepGenRLE openL true fast1 mode L R with
      | .stepped mode' L' R' => runSubLoop fuel openL fast1 mode' L' R'
      | .halted => .halted
      | .abort => .abort

def runSubSim (fuel : ℕ) (openL fast1 : Bool) (S : RLEStack) : SubSimResult :=
  runSubLoop fuel openL fast1 .F (pushRun 0 1 S) [(9, 1)]

lemma runSubLoop_sound_step : ∀ {fuel : ℕ} {openL fast1 : Bool} {mode : StackMode}
    {L R S' : RLEStack} (L_bot R_bot : List ℕ),
    runSubLoop fuel openL fast1 mode L R = .stepped S' →
    (evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith true R R_bot)) [target_tm]⊢*
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: evalRLEWith openL S' L_bot) (0 :: R_bot))
  | 0, _, _, _, _, _, _, _, _, h => by simp [runSubLoop] at h
  | fuel + 1, openL, fast1, mode, L, R, S', L_bot, R_bot, h => by
    unfold runSubLoop at h
    split_ifs at h with hexit
    · simp only [Bool.and_eq_true, beq_iff_eq] at hexit
      rcases hexit with ⟨rfl, hR0⟩
      cases hpeel : peelZeros 5 L with
      | none => rw [hpeel] at h; simp at h
      | some S_out =>
        rw [hpeel] at h
        simp only [SubSimResult.stepped.injEq] at h
        subst h
        rw [evalRLEWith_isSingleVal R_bot hR0, evalRLEWith_peelZeros L_bot hpeel]
        exact ⟨0, rfl⟩
    · cases hstep : stepGenRLE openL true fast1 mode L R with
      | stepped mode' L' R' =>
        rw [hstep] at h
        exact stepStar_trans (stepGenRLE_sound_step L_bot R_bot hstep)
          (runSubLoop_sound_step L_bot R_bot h)
      | halted => rw [hstep] at h; simp at h
      | abort => rw [hstep] at h; simp at h

lemma runSubLoop_sound_halt : ∀ {fuel : ℕ} {openL fast1 : Bool} {mode : StackMode}
    {L R : RLEStack} (L_bot R_bot : List ℕ),
    runSubLoop fuel openL fast1 mode L R = .halted →
    ∃ cfg, ((evalStackCfg mode (evalRLEWith openL L L_bot) (evalRLEWith true R R_bot)) [target_tm]⊢* cfg) ∧
      (step target_tm cfg).isNone
  | 0, _, _, _, _, _, _, _, h => by simp [runSubLoop] at h
  | fuel + 1, openL, fast1, mode, L, R, L_bot, R_bot, h => by
    unfold runSubLoop at h
    split_ifs at h with hexit
    · cases hpeel : peelZeros 5 L <;> simp [hpeel] at h
    · cases hstep : stepGenRLE openL true fast1 mode L R with
      | stepped mode' L' R' =>
        rw [hstep] at h
        obtain ⟨cfg, h_rest, h_none⟩ := runSubLoop_sound_halt L_bot R_bot h
        exact ⟨cfg, stepStar_trans (stepGenRLE_sound_step L_bot R_bot hstep) h_rest, h_none⟩
      | halted =>
        exact stepGenRLE_sound_halt L_bot R_bot hstep
      | abort => rw [hstep] at h; simp at h

lemma runSubSim_sound_closed {fuel : ℕ} {fast1 : Bool} {S S' : RLEStack}
    (h : runSubSim fuel false fast1 S = .stepped S') :
    SubStep (evalRLE S) (evalRLE S') := by
  intro R_bot
  have h1 := runSubLoop_sound_step [] R_bot h
  simpa [evalRLEWith, tailFor, evalRLE_pushRun, evalRLE] using h1

lemma runSubSim_sound_open {fuel : ℕ} {fast1 : Bool} {S S' : RLEStack} (U : List ℕ)
    (h : runSubSim fuel true fast1 S = .stepped S') :
    SubStep (evalRLE S ++ U) (evalRLE S' ++ U) := by
  intro R_bot
  have h1 := runSubLoop_sound_step U R_bot h
  simpa [evalRLEWith, tailFor, evalRLE_pushRun, evalRLE] using h1

lemma runSubSim_sound_halt {fuel : ℕ} {fast1 : Bool} {S : RLEStack}
    (h : runSubSim fuel false fast1 S = .halted) :
    SubHalt (evalRLE S) := by
  intro R_bot
  have h1 := runSubLoop_sound_halt [] R_bot h
  simpa [evalRLEWith, tailFor, evalRLE_pushRun, evalRLE] using h1

def peelOneA3 (s : RLEStack) : Option (ℕ × RLEStack) :=
  match popOne s with
  | none => none
  | some (v6, s₁) =>
    if v6 == 6 then
      match peelZeros 3 s₁ with
      | none => none
      | some s₂ =>
        match popOne s₂ with
        | none => none
        | some (x, s₃) =>
          if 3 ≤ x && x % 3 == 0 then
            match popOne s₃ with
            | none => none
            | some (v3, s₄) =>
              if v3 == 3 then
                match popOne s₄ with
                | none => none
                | some (v0, s₅) =>
                  if v0 == 0 then forceNat (x / 3 - 1) (fun k' => some (k', s₅))
                  else none
              else none
          else none
    else none

lemma evalRLE_peelOneA3 {s s' : RLEStack} {k : ℕ} (h : peelOneA3 s = some (k, s')) :
    evalRLE s = A3 k (evalRLE s') := by
  unfold peelOneA3 at h
  cases hp1 : popOne s with
  | none => rw [hp1] at h; simp at h
  | some vp1 =>
    rcases vp1 with ⟨v6, s₁⟩
    rw [hp1] at h
    dsimp at h
    split_ifs at h with hv6
    rw [beq_iff_eq] at hv6
    subst hv6
    cases hpz : peelZeros 3 s₁ with
    | none => rw [hpz] at h; simp at h
    | some s₂ =>
      rw [hpz] at h
      dsimp at h
      cases hp2 : popOne s₂ with
      | none => rw [hp2] at h; simp at h
      | some vp2 =>
        rcases vp2 with ⟨x, s₃⟩
        rw [hp2] at h
        dsimp at h
        split_ifs at h with hx
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
        cases hp3 : popOne s₃ with
        | none => rw [hp3] at h; simp at h
        | some vp3 =>
          rcases vp3 with ⟨v3, s₄⟩
          rw [hp3] at h
          dsimp at h
          split_ifs at h with hv3
          rw [beq_iff_eq] at hv3
          subst hv3
          cases hp4 : popOne s₄ with
          | none => rw [hp4] at h; simp at h
          | some vp4 =>
            rcases vp4 with ⟨v0, s₅⟩
            rw [hp4] at h
            dsimp at h
            split_ifs at h with hv0
            rw [beq_iff_eq] at hv0
            subst hv0
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hx_eq : x = 3 * (x / 3 - 1) + 3 := by omega
            rw [evalRLE_popOne_some hp1, evalRLE_peelZeros hpz, evalRLE_popOne_some hp2,
                evalRLE_popOne_some hp3, evalRLE_popOne_some hp4]
            simp [A3, ← hx_eq]

def peelA3Loop : ℕ → List ℕ → RLEStack → List ℕ × RLEStack
  | 0, acc, s => (acc, s)
  | fuel + 1, acc, s =>
    match peelOneA3 s with
    | some (k, s') => peelA3Loop fuel (k :: acc) s'
    | none => (acc, s)

lemma evalRLE_peelA3Loop : ∀ (fuel : ℕ) (acc : List ℕ) (s : RLEStack),
    TowerA3 (peelA3Loop fuel acc s).1 (evalRLE (peelA3Loop fuel acc s).2) =
    TowerA3 acc (evalRLE s)
  | 0, _, _ => rfl
  | fuel + 1, acc, s => by
    unfold peelA3Loop
    cases h : peelOneA3 s with
    | none => rfl
    | some vp =>
      rcases vp with ⟨k, s'⟩
      rw [evalRLE_peelA3Loop fuel (k :: acc) s', TowerA3, evalRLE_peelOneA3 h]

def wrapOneA3RLE (k : ℕ) (s : RLEStack) : RLEStack :=
  pushRun 6 1 (pushRun 0 3 (pushRun (3 * k + 3) 1 (pushRun 3 1 (pushRun 0 1 s))))

def wrapTowerA3RLE : List ℕ → RLEStack → RLEStack
  | [], s => s
  | k :: ks, s => wrapTowerA3RLE ks (wrapOneA3RLE k s)

lemma evalRLE_wrapOneA3RLE (k : ℕ) (s : RLEStack) :
    evalRLE (wrapOneA3RLE k s) = A3 k (evalRLE s) := by
  simp [wrapOneA3RLE, evalRLE_pushRun, A3]

lemma evalRLE_wrapTowerA3RLE : ∀ (ks : List ℕ) (s : RLEStack),
    evalRLE (wrapTowerA3RLE ks s) = TowerA3 ks (evalRLE s)
  | [], _ => rfl
  | k :: ks, s => by
    simp only [wrapTowerA3RLE, TowerA3, evalRLE_wrapTowerA3RLE ks, evalRLE_wrapOneA3RLE]

def wrapOneA0RLE (k : ℕ) (s : RLEStack) : RLEStack :=
  pushRun 6 1 (pushRun 0 3 (pushRun (3 * k + 3) 1 (pushRun 0 3 s)))

def wrapTowerA0OutRLE : List ℕ → RLEStack → RLEStack
  | [], s => s
  | k :: ks, s => wrapOneA0RLE k (wrapTowerA0OutRLE ks s)

lemma evalRLE_wrapOneA0RLE (k : ℕ) (s : RLEStack) :
    evalRLE (wrapOneA0RLE k s) = A0 k (evalRLE s) := by
  simp [wrapOneA0RLE, evalRLE_pushRun, A0]

lemma evalRLE_wrapTowerA0OutRLE : ∀ (ks : List ℕ) (s : RLEStack),
    evalRLE (wrapTowerA0OutRLE ks s) = TowerA0Out ks (evalRLE s)
  | [], _ => rfl
  | k :: ks, s => by
    simp only [wrapTowerA0OutRLE, TowerA0Out, evalRLE_wrapOneA0RLE, evalRLE_wrapTowerA0OutRLE ks]

-- ============================================================================
-- Section 5: Three-Phase Halting Trajectory (`init [] -> HALT`)
-- ============================================================================

lemma evalRLE_append : ∀ (s₁ s₂ : RLEStack),
    evalRLE (s₁ ++ s₂) = evalRLE s₁ ++ evalRLE s₂
  | [], _ => rfl
  | (v, c) :: s₁, s₂ => by simp [evalRLE, evalRLE_append s₁ s₂, List.append_assoc]

def midPrefixRLE : RLEStack :=
  [ (0, 2819), (12, 1), (0, 2), (3, 1), (0, 4), (1398, 1), (0, 3), (6, 1),
    (0, 3), (345, 1), (0, 3), (6, 1), (0, 3), (81, 1), (0, 3), (6, 1),
    (0, 3), (15, 1), (0, 3), (3, 1), (0, 59107), (6, 1), (0, 883), (6, 1),
    (0, 47), (12, 1), (0, 2), (3, 1), (0, 4), (12, 1), (0, 3), (3, 1),
    (0, 203), (6, 1), (0, 54), (3, 1), (0, 3), (3, 2), (0, 7) ]

def midPrefix : List ℕ := evalRLE midPrefixRLE

def bodyStack (Z b1 : ℕ) : List ℕ :=
  0 :: 3 :: (List.replicate Z 0 ++ (6 :: (midPrefix ++ [b1, 2])))

def bodyStackRLE (Z b1 : ℕ) : RLEStack :=
  pushRun 0 1 (pushRun 3 1 (pushRun 0 Z (pushRun 6 1
    (midPrefixRLE ++ [(b1, 1), (2, 1)]))))

lemma evalRLE_bodyStackRLE (Z b1 : ℕ) :
    evalRLE (bodyStackRLE Z b1) = bodyStack Z b1 := by
  simp [bodyStackRLE, bodyStack, midPrefix, evalRLE_pushRun, evalRLE_append, evalRLE]

def ksInitOut : List ℕ :=
  [30758225, 7689554, 1922386, 480594, 120146, 30034, 7506, 1874, 466, 114, 26, 4]

def expectedPhase1L : RLEStack :=
  pushRun 0 1 (wrapTowerA0OutRLE ksInitOut (bodyStackRLE 56233 3))

lemma evalRLE_expectedPhase1L :
    evalRLE expectedPhase1L = 0 :: TowerA0Out ksInitOut (bodyStack 56233 3) := by
  simp [expectedPhase1L, evalRLE_pushRun, evalRLE_wrapTowerA0OutRLE, evalRLE_bodyStackRLE]

-- Phase 1: 11,728 steps (with 1,062 TowerA3 jumps) from `cfg_F [] [1]` to `SNAP 1 + R=[5]`

def tryJumpPhase1 (mode : StackMode) (L R : RLEStack) : Option RLEStack :=
  if mode == .F && isSingleVal 5 R then
    match popOne L with
    | none => none
    | some (v0, S_rle) =>
      match v0 with
      | 0 =>
        let p := peelA3Loop 35 [] S_rle
        match p.1 with
        | [] => none
        | k₀ :: ks₀ =>
          match runSubSim 100 false false p.2 with
          | .stepped S'_inner =>
            some (pushRun 0 1 (wrapTowerA3RLE (stepTowerAt 2 (k₀ :: ks₀)) S'_inner))
          | .halted => none
          | .abort => none
      | _ + 1 => none
  else none

lemma tryJumpPhase1_sound {mode : StackMode} {L R L' : RLEStack}
    (h : tryJumpPhase1 mode L R = some L') :
    (evalStackCfg mode (evalRLE L) (evalRLE R)) [target_tm]⊢*
    (cfg_F (evalRLE L') [5]) := by
  unfold tryJumpPhase1 at h
  split_ifs at h with hmode
  simp only [Bool.and_eq_true, beq_iff_eq] at hmode
  rcases hmode with ⟨rfl, hR5⟩
  cases hpop : popOne L with
  | none => rw [hpop] at h; simp at h
  | some vp =>
    rcases vp with ⟨v0, S_rle⟩
    rw [hpop] at h
    cases v0 with
    | succ _ => simp at h
    | zero =>
      dsimp at h
      have hpeel : TowerA3 (peelA3Loop 35 [] S_rle).1 (evalRLE (peelA3Loop 35 [] S_rle).2) =
          evalRLE S_rle := evalRLE_peelA3Loop 35 [] S_rle
      cases hks : (peelA3Loop 35 [] S_rle).1 with
      | nil => rw [hks] at h; simp at h
      | cons k₀ ks₀ =>
        rw [hks] at h hpeel
        dsimp at h
        cases hsim : runSubSim 100 false false (peelA3Loop 35 [] S_rle).2 with
        | stepped S'_inner =>
          rw [hsim] at h
          simp only [Option.some.injEq] at h
          subst h
          rw [evalStackCfg_F, evalRLE_popOne_some hpop, evalRLE_isSingleVal hR5, ← hpeel]
          simpa [TopStep, evalRLE_pushRun, evalRLE_wrapTowerA3RLE] using
            towerA3_topStep (k₀ :: ks₀) (List.cons_ne_nil k₀ ks₀)
              (runSubSim_sound_closed hsim)
        | halted => rw [hsim] at h; simp at h
        | abort => rw [hsim] at h; simp at h

def stepPhase1 (mode : StackMode) (L R : RLEStack) : Option (StackMode × RLEStack × RLEStack) :=
  match tryJumpPhase1 mode L R with
  | some L' => some (.F, L', [(5, 1)])
  | none =>
    match stepGenRLE false false true mode L R with
    | .stepped mode' L' R' => some (mode', L', R')
    | .halted => none
    | .abort => none

lemma stepPhase1_sound {mode mode' : StackMode} {L R L' R' : RLEStack}
    (h : stepPhase1 mode L R = some (mode', L', R')) :
    (evalStackCfg mode (evalRLE L) (evalRLE R)) [target_tm]⊢*
    (evalStackCfg mode' (evalRLE L') (evalRLE R')) := by
  unfold stepPhase1 at h
  cases hj : tryJumpPhase1 mode L R with
  | some Lj =>
    rw [hj] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact tryJumpPhase1_sound hj
  | none =>
    rw [hj] at h
    cases hstep : stepGenRLE false false true mode L R with
    | stepped m₁ L₁ R₁ =>
      rw [hstep] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hs := stepGenRLE_sound_step [] [] hstep
      simpa [evalRLEWith, tailFor] using hs
    | halted => rw [hstep] at h; simp at h
    | abort => rw [hstep] at h; simp at h

def runPhase1Steps : ℕ → StackMode → RLEStack → RLEStack → Option (StackMode × RLEStack × RLEStack)
  | 0, mode, L, R => some (mode, L, R)
  | n + 1, mode, L, R =>
    match stepPhase1 mode L R with
    | some (mode₁, L₁, R₁) => runPhase1Steps n mode₁ L₁ R₁
    | none => none

lemma runPhase1Steps_sound : ∀ {n : ℕ} {mode mode' : StackMode} {L R L' R' : RLEStack},
    runPhase1Steps n mode L R = some (mode', L', R') →
    (evalStackCfg mode (evalRLE L) (evalRLE R)) [target_tm]⊢*
    (evalStackCfg mode' (evalRLE L') (evalRLE R'))
  | 0, _, _, _, _, _, _, h => by
    simp only [runPhase1Steps, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, rfl⟩
  | n + 1, mode, mode', L, R, L', R', h => by
    unfold runPhase1Steps at h
    cases hstep : stepPhase1 mode L R with
    | none => rw [hstep] at h; simp at h
    | some vp =>
      rcases vp with ⟨m₁, L₁, R₁⟩
      rw [hstep] at h
      exact stepStar_trans (stepPhase1_sound hstep) (runPhase1Steps_sound h)

set_option maxRecDepth 200000 in
lemma runPhase1All_eq :
    runPhase1Steps 11728 .F [] [(1, 1)] = some (.F, expectedPhase1L, [(5, 1)]) := by
  decide +kernel

theorem phase1_reach :
    ∃ ks₀ : List ℕ, ks₀ ≠ [] ∧
      (init []) [target_tm]⊢* (cfg_F (0 :: TowerA3 ks₀ (bodyStack 56233 3)) [5]) := by
  have h_entry : (init []) [target_tm]⊢* (cfg_F [] [1]) := by
    have h0 : init ([] : List (Fin 2)) = cfg_AR [] [] := rfl
    rw [h0]
    exact stepPlus_stepStar (rule_AR_nil [])
  have h_p1 : (cfg_F [] [1]) [target_tm]⊢*
      (cfg_F (0 :: TowerA0Out ksInitOut (bodyStack 56233 3)) [5]) := by
    have h_all := runPhase1Steps_sound runPhase1All_eq
    simpa [evalStackCfg, evalRLE_expectedPhase1L, evalRLE] using h_all
  have h_abs := towerA3_absorb_towerA0Out ksInitOut [] (bodyStack 56233 3)
  have h_ne : absorbTowerA0Out ksInitOut [] ≠ [] :=
    absorbTowerA0Out_ne_nil ksInitOut [] (Or.inl (by decide))
  exact ⟨absorbTowerA0Out ksInitOut [], h_ne, stepStar_trans h_entry (stepStar_trans h_p1 h_abs)⟩

-- Phase 2: 7,029 parametric body cycles from `Z = 56,233` down to `Z = 1`

def runOpenSubCalls : ℕ → ℕ → RLEStack → Option RLEStack
  | 0, _, s => some s
  | n + 1, fuel, s =>
    match runSubSim fuel true true s with
    | .stepped s' => runOpenSubCalls n fuel s'
    | .halted => none
    | .abort => none

lemma runOpenSubCalls_sound : ∀ {n fuel : ℕ} {s s' : RLEStack} {ks : List ℕ},
    ks ≠ [] → runOpenSubCalls n fuel s = some s' →
    ∀ (U : List ℕ),
    ∃ ks' : List ℕ, ks' ≠ [] ∧
      TopStep (TowerA3 ks (evalRLE s ++ U)) (TowerA3 ks' (evalRLE s' ++ U))
  | 0, _, _, _, ks, hks, h, U => by
    simp only [runOpenSubCalls, Option.some.injEq] at h
    subst h
    exact ⟨ks, hks, topStep_refl _⟩
  | n + 1, fuel, s, s', ks, hks, h, U => by
    unfold runOpenSubCalls at h
    cases hsim : runSubSim fuel true true s with
    | stepped s₁ =>
      rw [hsim] at h
      have h_sub := runSubSim_sound_open U hsim
      have h_top := towerA3_topStep ks hks h_sub
      have hne1 := stepTowerAt_ne_nil 2 hks
      obtain ⟨ks', hne', h_rest⟩ := runOpenSubCalls_sound hne1 h U
      exact ⟨ks', hne', topStep_trans h_top h_rest⟩
    | halted => rw [hsim] at h; simp at h
    | abort => rw [hsim] at h; simp at h

def headForA (m : ℕ) (U : List ℕ) : List ℕ :=
  match m with
  | 0 => 3 :: 9 :: U
  | m' + 1 => 3 :: 3 :: (List.replicate (8 * m' + 7) 0 ++ (6 :: U))

lemma calls1to10_m0_rle :
    runOpenSubCalls 10 50 [(0, 1), (3, 1), (0, 9), (6, 1)] =
    some [(0, 1), (3, 2), (0, 2), (12, 1), (3, 1), (0, 1), (3, 1), (9, 1)] := by decide +kernel

lemma calls1to10_mpos_rle :
    runOpenSubCalls 10 50 [(0, 1), (3, 1), (0, 10)] =
    some [(0, 1), (3, 2), (0, 2), (12, 1), (3, 1), (0, 1), (3, 2)] := by decide +kernel

theorem calls1to10_topStep (m : ℕ) (U : List ℕ) {ks : List ℕ} (hks : ks ≠ []) :
    ∃ ks₁ : List ℕ, ks₁ ≠ [] ∧
      TopStep (TowerA3 ks (0 :: 3 :: (List.replicate (8 * m + 9) 0 ++ (6 :: U))))
              (TowerA3 ks₁ (B3 3 (headForA m U))) := by
  cases m with
  | zero =>
    obtain ⟨ks₁, hne₁, htop⟩ := runOpenSubCalls_sound hks calls1to10_m0_rle U
    refine ⟨ks₁, hne₁, ?_⟩
    simpa [evalRLE, B3, headForA] using htop
  | succ m' =>
    set V := List.replicate (8 * m' + 7) 0 ++ (6 :: U)
    obtain ⟨ks₁, hne₁, htop⟩ := runOpenSubCalls_sound hks calls1to10_mpos_rle V
    refine ⟨ks₁, hne₁, ?_⟩
    have h_rep : List.replicate (8 * (m' + 1) + 9) 0 ++ (6 :: U) =
        List.replicate 10 0 ++ V := by
      have heq : 8 * (m' + 1) + 9 = 10 + (8 * m' + 7) := by omega
      rw [heq, List.replicate_add, List.append_assoc]
    rw [h_rep]
    simpa [evalRLE, B3, headForA] using htop

theorem partA_m0 (U R_bot : List ℕ) :
    (cfg_F (0 :: 3 :: 9 :: U) (9 :: R_bot)) [target_tm]⊢*
    (cfg_F (0 :: U) (0 :: 1 :: 1 :: 5 :: 10 :: R_bot)) := by
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_add_two (9 :: U) (9 :: R_bot) 1)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_zero (9 :: U) (0 :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  have h3 := rule_F_step3_all U (4 :: 10 :: R_bot) 0 3
  simpa [stepF3Right, bumpHead] using h3

theorem partA_mpos (m' : ℕ) (U R_bot : List ℕ) :
    (cfg_F (0 :: 3 :: 3 :: (List.replicate (8 * m' + 7) 0 ++ (6 :: U))) (9 :: R_bot)) [target_tm]⊢*
    (cfg_F (0 :: U) (0 :: 1 :: 1 :: (16 * (m' + 1) + 5) :: 10 :: R_bot)) := by
  set V := List.replicate (8 * m' + 7) 0 ++ (6 :: U)
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_add_two (3 :: V) (9 :: R_bot) 1)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_zero (3 :: V) (0 :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_add_three V (4 :: 10 :: R_bot) 0)) ?_
  dsimp [bumpHead]
  have hV : 0 :: V = List.replicate (4 * (2 * m' + 1) + 3 + 1) 0 ++ (6 :: U) := by
    have hlen : 4 * (2 * m' + 1) + 3 + 1 = 1 + (8 * m' + 7) := by omega
    rw [hlen, List.replicate_add]
    rfl
  rw [hV]
  refine stepStar_trans (rule_F_zero4_all (2 * m' + 1) 3 (6 :: U) 5 (10 :: R_bot)) ?_
  set d₁ := 5 + 8 * (2 * m' + 1)
  change (cfg_F (0 :: 0 :: 0 :: 0 :: 6 :: U) (0 :: d₁ :: 10 :: R_bot)) [target_tm]⊢* _
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_zero (0 :: 0 :: 6 :: U) (0 :: d₁ :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_two (0 :: 6 :: U) (0 :: 0 :: d₁ :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (6 :: U) (1 :: 0 :: d₁ :: 10 :: R_bot) 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (6 :: U) (3 :: 0 :: d₁ :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (rule_AR_step2_all (9 :: U) (0 :: d₁ :: 10 :: R_bot) 0 2) ?_
  dsimp [List.replicate]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: 9 :: U) (0 :: d₁ :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (3 :: 9 :: U) (10 :: R_bot) d₁)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero (9 :: U) ((d₁ + 1) :: 10 :: R_bot) 1)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_zero (9 :: U) ((d₁ + 1 + 1 + 1) :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  have hd : d₁ + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 16 * (m' + 1) + 4 := by
    dsimp [d₁]; omega
  rw [hd]
  have h14 := rule_F_step3_all U ((16 * (m' + 1) + 4) :: 10 :: R_bot) 0 3
  have hd2 : 16 * (m' + 1) + 4 + 1 = 16 * (m' + 1) + 5 := by omega
  simpa [stepF3Right, bumpHead, hd2] using h14

theorem partA_all (m : ℕ) (U R_bot : List ℕ) :
    (cfg_F (0 :: headForA m U) (9 :: R_bot)) [target_tm]⊢*
    (cfg_F (0 :: U) (0 :: 1 :: 1 :: (16 * m + 5) :: 10 :: R_bot)) := by
  cases m with
  | zero => exact partA_m0 U R_bot
  | succ m' => exact partA_mpos m' U R_bot

def midRightTailRLE : RLEStack :=
  [ (9, 1), (0, 1), (105, 1), (1, 1), (409, 1), (9, 1), (1, 3), (10, 1),
    (8, 1), (1, 3), (97, 1), (1, 1), (1769, 1), (1, 1), (118217, 1), (9, 1),
    (1, 4), (9, 1), (1, 1), (9, 1), (1, 26), (9, 1), (1, 1), (9, 1),
    (1, 114), (9, 1), (1, 1), (9, 1), (1, 465), (10, 1), (8, 1), (1, 3),
    (5641, 1), (1, 1) ]

lemma partB_rle :
    runStepsRLE 189 true true true .F (pushRun 0 1 midPrefixRLE) [(0, 1), (1, 2)] =
    .stepped .AR [(0, 1)] ((0, 1) :: (3, 1) :: (0, 1) :: (18, 1) :: midRightTailRLE) := by decide +kernel

theorem partB_step (L_bot R_bot' : List ℕ) :
    (cfg_F (0 :: (midPrefix ++ L_bot)) (0 :: 1 :: 1 :: R_bot')) [target_tm]⊢*
    (cfg_AR (0 :: L_bot) (0 :: 3 :: 0 :: 18 :: (evalRLE midRightTailRLE ++ R_bot'))) := by
  have h := runStepsRLE_sound_step L_bot R_bot' partB_rle
  simpa [evalStackCfg, evalRLEWith, tailFor, evalRLE_pushRun, midPrefix, evalRLE,
    List.append_assoc] using h

theorem partC_step (k : ℕ) (R_tail : List ℕ) :
    (cfg_AR [0, 3 * (k + 1), 2] (0 :: 3 :: 0 :: 18 :: R_tail)) [target_tm]⊢*
    (cfg_AR [3 * (k + 2), 2] (28 :: R_tail)) := by
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero [3 * (k + 1), 2] (3 :: 0 :: 18 :: R_tail))) ?_
  dsimp [bumpHead]
  have hk1 : 3 * (k + 1) + 1 + 1 + 1 = 3 * (k + 2) := by omega
  rw [hk1]
  refine stepStar_trans (rule_AR_step2_all [3 * (k + 2), 2] (0 :: 18 :: R_tail) 0 2) ?_
  dsimp [List.replicate]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero [0, 3 * (k + 2), 2] (0 :: 18 :: R_tail))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons [3, 3 * (k + 2), 2] R_tail 18)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero [3 * (k + 2), 2] (19 :: R_tail) 1)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_zero [3 * (k + 2), 2] (21 :: R_tail))) ?_
  dsimp [bumpHead]
  have hk2 : 3 * (k + 2) = 3 * (k + 2) + 0 := by omega
  rw [hk2]
  refine stepStar_trans (rule_F_step3_all [2] (25 :: R_tail) 0 (k + 2)) ?_
  rw [stepF3Right_succ (k + 1) (25 :: R_tail)]
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_F_zero_add_two []
    (0 :: (List.replicate (k + 1) 1 ++ (26 :: R_tail))) 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero []
    (0 :: 1 :: (List.replicate (k + 1) 1 ++ (26 :: R_tail))))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons [2]
    (List.replicate (k + 1) 1 ++ (26 :: R_tail)) 1)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_add_two_zero []
    (2 :: (List.replicate (k + 1) 1 ++ (26 :: R_tail))) 0)) ?_
  dsimp [bumpHead]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero []
    (4 :: (List.replicate (k + 1) 1 ++ (26 :: R_tail))))) ?_
  dsimp [bumpHead]
  refine stepStar_trans (rule_AR_step2_all [2]
    (List.replicate (k + 1) 1 ++ (26 :: R_tail)) 1 2) ?_
  dsimp [List.replicate]
  have h_rep : 1 :: 1 :: (List.replicate k 1 ++ (26 :: R_tail)) =
      List.replicate ((k + 1) + 1) 1 ++ (26 :: R_tail) := rfl
  rw [h_rep]
  refine stepStar_trans (rule_AR_ones_all (k + 1) 0 [2] (26 :: R_tail)) ?_
  rw [Nat.zero_add]
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons [0, 3 * (k + 1), 2] R_tail 26)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero [3 * (k + 1), 2] (27 :: R_tail))) ?_
  dsimp [bumpHead]
  rw [hk1]
  exact ⟨0, rfl⟩

lemma partD_rle :
    runStepsRLE 83 true true true .AR [] (pushRun 28 1 midRightTailRLE) =
    .stepped .AR ((0, 1) :: (3, 1) :: midPrefixRLE) [(1, 1)] := by decide +kernel

theorem partD_step (L_bot R_bot' : List ℕ) :
    (cfg_AR L_bot (28 :: (evalRLE midRightTailRLE ++ R_bot'))) [target_tm]⊢*
    (cfg_AR (0 :: 3 :: (midPrefix ++ L_bot)) (1 :: R_bot')) := by
  have h := runStepsRLE_sound_step L_bot R_bot' partD_rle
  simpa [evalStackCfg, evalRLEWith, tailFor, evalRLE_pushRun, midPrefix, evalRLE,
    List.append_assoc] using h

theorem partE_step (m : ℕ) (W R_bot : List ℕ) :
    (cfg_AR (0 :: 3 :: W) (1 :: (16 * m + 5) :: 10 :: R_bot)) [target_tm]⊢*
    (cfg_AR (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 3 :: (List.replicate (8 * m + 1) 0 ++ (6 :: W)))
      (0 :: R_bot)) := by
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (0 :: 3 :: W) (10 :: R_bot) (16 * m + 5))) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (3 :: W) ((16 * m + 5 + 1) :: 10 :: R_bot))) ?_
  dsimp [bumpHead]
  have hm1 : 16 * m + 5 + 1 + 1 = 2 * (8 * m + 3) + 1 := by omega
  rw [hm1]
  refine stepStar_trans (rule_AR_step2_all (6 :: W) (10 :: R_bot) 1 (8 * m + 3)) ?_
  have hrep1 : List.replicate (8 * m + 3) 0 ++ (6 :: W) =
      0 :: 0 :: (List.replicate (8 * m + 1) 0 ++ (6 :: W)) := by
    have heq : 8 * m + 3 = 2 + (8 * m + 1) := by omega
    rw [heq, List.replicate_add]
    rfl
  rw [hrep1]
  set V := List.replicate (8 * m + 1) 0 ++ (6 :: W)
  refine stepStar_trans (stepPlus_stepStar (rule_AR_one_cons (0 :: 0 :: V) R_bot 10)) ?_
  refine stepStar_trans (stepPlus_stepStar (rule_AR_zero_zero (0 :: V) (11 :: R_bot))) ?_
  dsimp [bumpHead]
  have h6 := rule_AR_step2_all (3 :: V) R_bot 0 6
  simpa [List.replicate] using h6

theorem call11_core_subStep (m k : ℕ) :
    SubStep (headForA m (midPrefix ++ [3 * (k + 1), 2]))
            (bodyStack (8 * m + 1) (3 * (k + 2))) := by
  intro R_bot
  set U := midPrefix ++ [3 * (k + 1), 2]
  set R_bot' := (16 * m + 5) :: 10 :: R_bot
  refine stepStar_trans (partA_all m U R_bot) ?_
  refine stepStar_trans (partB_step [3 * (k + 1), 2] R_bot') ?_
  refine stepStar_trans (partC_step k (evalRLE midRightTailRLE ++ R_bot')) ?_
  refine stepStar_trans (partD_step [3 * (k + 2), 2] R_bot') ?_
  exact partE_step m (midPrefix ++ [3 * (k + 2), 2]) R_bot

theorem call11_subStep (m k : ℕ) :
    SubStep (B3 3 (headForA m (midPrefix ++ [3 * (k + 1), 2])))
            (A0 4 (bodyStack (8 * m + 1) (3 * (k + 2)))) :=
  subStep_B3 3 (call11_core_subStep m k)

theorem body_cycle_step (m k : ℕ) {ks : List ℕ} (hks : ks ≠ []) :
    ∃ ks' : List ℕ, ks' ≠ [] ∧
      TopStep (TowerA3 ks (bodyStack (8 * m + 9) (3 * (k + 1))))
              (TowerA3 ks' (bodyStack (8 * m + 1) (3 * (k + 2)))) := by
  obtain ⟨ks₁, hne₁, h10⟩ := calls1to10_topStep m (midPrefix ++ [3 * (k + 1), 2]) hks
  have h11 := towerA3_topStep ks₁ hne₁ (call11_subStep m k)
  have h12 := towerA3_absorb_A0 4 (stepTowerAt 2 ks₁) (bodyStack (8 * m + 1) (3 * (k + 2)))
  exact ⟨absorbA0 4 (stepTowerAt 2 ks₁), absorbA0_ne_nil 4 _,
    topStep_trans h10 (topStep_trans h11 h12)⟩

theorem body_cycles_all : ∀ (n m₀ k₀ : ℕ) {ks : List ℕ}, ks ≠ [] →
    ∃ ks' : List ℕ, ks' ≠ [] ∧
      TopStep (TowerA3 ks (bodyStack (8 * (m₀ + n) + 1) (3 * (k₀ + 1))))
              (TowerA3 ks' (bodyStack (8 * m₀ + 1) (3 * (k₀ + n + 1))))
  | 0, m₀, k₀, ks, hks => by
    simp only [Nat.add_zero]
    exact ⟨ks, hks, topStep_refl _⟩
  | n + 1, m₀, k₀, ks, hks => by
    have h_eq1 : 8 * (m₀ + (n + 1)) + 1 = 8 * (m₀ + n) + 9 := by omega
    rw [h_eq1]
    obtain ⟨ks₁, hne₁, hstep⟩ := body_cycle_step (m₀ + n) k₀ hks
    have h_eq2 : 3 * (k₀ + 2) = 3 * ((k₀ + 1) + 1) := by omega
    rw [h_eq2] at hstep
    obtain ⟨ks', hne', hrest⟩ := body_cycles_all n m₀ (k₀ + 1) hne₁
    have h_eq3 : (k₀ + 1) + n + 1 = k₀ + (n + 1) + 1 := by omega
    rw [h_eq3] at hrest
    exact ⟨ks', hne', topStep_trans hstep hrest⟩

-- Phase 3: 186 SubStep calls from `bodyStack 1 21090` to `SubHalt`

def runPhase3 : ℕ → RLEStack → Bool
  | 0, _ => false
  | fuel + 1, s =>
    let p := peelA3Loop 35 [] s
    match runSubSim 400 false true p.2 with
    | .stepped s' => runPhase3 fuel s'
    | .halted => true
    | .abort => false

set_option maxRecDepth 200000 in
lemma runPhase3_eq : runPhase3 186 (bodyStackRLE 1 21090) = true := by decide +kernel

theorem runPhase3_sound : ∀ (fuel : ℕ) (s : RLEStack),
    runPhase3 fuel s = true →
    ∀ (ks : List ℕ), ks ≠ [] →
    ∃ cfg, ((cfg_F (0 :: TowerA3 ks (evalRLE s)) [5]) [target_tm]⊢* cfg) ∧
      (step target_tm cfg).isNone
  | 0, _, h, _, _ => by simp [runPhase3] at h
  | fuel + 1, s, h, ks, hks => by
    unfold runPhase3 at h
    dsimp at h
    have hpeel : TowerA3 (peelA3Loop 35 [] s).1 (evalRLE (peelA3Loop 35 [] s).2) = evalRLE s :=
      evalRLE_peelA3Loop 35 [] s
    set ks_p := (peelA3Loop 35 [] s).1
    set s_in := (peelA3Loop 35 [] s).2
    have h_tower : TowerA3 ks (evalRLE s) = TowerA3 (ks_p ++ ks) (evalRLE s_in) := by
      rw [← hpeel, ← TowerA3_append]
    have hne_all : ks_p ++ ks ≠ [] := by
      intro hnil
      exact hks (List.append_eq_nil_iff.mp hnil).2
    rw [h_tower]
    cases hsim : runSubSim 400 false true s_in with
    | stepped s' =>
      rw [hsim] at h
      have h_top := towerA3_topStep (ks_p ++ ks) hne_all (runSubSim_sound_closed hsim)
      obtain ⟨cfg, h_rest, h_none⟩ :=
        runPhase3_sound fuel s' h (stepTowerAt 2 (ks_p ++ ks)) (stepTowerAt_ne_nil 2 hne_all)
      exact ⟨cfg, stepStar_trans h_top h_rest, h_none⟩
    | halted =>
      exact towerA3_halt (ks_p ++ ks) hne_all (runSubSim_sound_halt hsim)
    | abort =>
      rw [hsim] at h
      simp at h

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  obtain ⟨ks₀, hks₀, h_p1⟩ := phase1_reach
  obtain ⟨ks₁, hks₁, h_p2⟩ := body_cycles_all 7029 0 0 hks₀
  dsimp at h_p2
  rw [← evalRLE_bodyStackRLE 1 21090] at h_p2
  obtain ⟨cfg, h_p3, h_none⟩ := runPhase3_sound 186 (bodyStackRLE 1 21090) runPhase3_eq ks₁ hks₁
  exact ⟨cfg, stepStar_trans h_p1 (stepStar_trans h_p2 h_p3), h_none⟩

end BusyBeaver.M_1RB0RC_1RC0LD_1LD1RA_1LF0LE_HHH0RD_1LB0LA
