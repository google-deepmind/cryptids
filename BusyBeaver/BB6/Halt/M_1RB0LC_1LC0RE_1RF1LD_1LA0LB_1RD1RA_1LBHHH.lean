/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def A : Fin 6 := 4
def B : Fin 6 := 3
def C : Fin 6 := 0
def D : Fin 6 := 2
def E : Fin 6 := 5
def F : Fin 6 := 1

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
@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = ⟨some C, ⟨0, default, default⟩⟩ := rfl

omit [Inhabited Γ] in
theorem list_pow_add (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, ← add_assoc, add_comm 1 m, list_pow_add]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [← List.append_assoc, ← List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa

def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L => (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 1))) <+ (([1] : List (Fin 2)) ^ (1 * a + 1))

def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R => (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 1)) +> encRight R)

def enc1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: R => (([1] : List (Fin 2)) ^ (a + 1)) +> ((0 : Fin 2) >> enc1 R)

@[simp] lemma encLeft_nil : encLeft [] = default := rfl
@[simp] lemma encRight_nil : encRight [] = default := rfl
@[simp] lemma enc1_nil : enc1 [] = default := rfl
@[simp] lemma enc1_cons (a : ℕ) (R : List ℕ) :
    enc1 (a :: R) = (([1] : List (Fin 2)) ^ (a + 1)) +> ((0 : Fin 2) >> enc1 R) := rfl

lemma encLeft_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = (([1] : List (Fin 2)) ^ (a + 1)) +> ((0 : Fin 2) >> encLeft L) := by
  simp only [encLeft, Nat.mod_one, Nat.add_zero, Nat.one_mul]
  rfl

lemma encRight_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d, b) :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encRight R) := by
  simp only [encRight, Nat.mod_one, Nat.add_zero, Nat.one_mul]
  rfl

@[simp] lemma encLeft_cons_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: L)).head = (1 : Fin 2) := by
  rw [encLeft_cons]; simp

@[simp] lemma cons_one_encLeft_tail (a b : ℕ) (L : List (ℕ × ℕ)) :
    (1 : Fin 2) >> (encLeft ((a, b) :: L)).tail = encLeft ((a, b) :: L) := by
  rw [encLeft_cons]; simp

@[simp] lemma encRight_cons_head (d b : ℕ) (R : List (ℕ × ℕ)) :
    (encRight ((d, b) :: R)).head = (1 : Fin 2) := by
  rw [encRight_cons]; simp

@[simp] lemma cons_one_encRight_tail (d b : ℕ) (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> (encRight ((d, b) :: R)).tail = encRight ((d, b) :: R) := by
  rw [encRight_cons]; simp

inductive MItem where
  | zero : MItem
  | run (d : ℕ) : MItem
  deriving DecidableEq

def encM : List MItem → ListBlank (Fin 2)
  | [] => default
  | .zero :: M => (0 : Fin 2) >> encM M
  | .run d :: M => (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encM M)

@[simp] lemma encM_nil : encM [] = default := rfl
@[simp] lemma encM_cons_zero (M : List MItem) :
    encM (.zero :: M) = (0 : Fin 2) >> encM M := rfl
@[simp] lemma encM_cons_run (d : ℕ) (M : List MItem) :
    encM (.run d :: M) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encM M) := rfl

@[simp] lemma encM_cons_run_head (d : ℕ) (M : List MItem) :
    (encM (.run d :: M)).head = (1 : Fin 2) := by
  rw [encM_cons_run]; simp

@[simp] lemma cons_one_encM_cons_run_tail (d : ℕ) (M : List MItem) :
    (1 : Fin 2) >> (encM (.run d :: M)).tail = encM (.run d :: M) := by
  rw [encM_cons_run]; simp

def strictNat {α : Type*} (n : ℕ) (f : ℕ → α) : α :=
  @Nat.rec (fun _ => α) (f 0) (fun k _ => f k) (Nat.add n 1)

@[simp] lemma strictNat_eq {α : Type*} (n : ℕ) (f : ℕ → α) : strictNat n f = f n := rfl

def bumpM : List MItem → List MItem
  | [] => [.run 0]
  | .zero :: M => .run 0 :: M
  | .run d :: M => strictNat (d + 1) (fun d' => .run d' :: M)

lemma encM_bumpM (M : List MItem) : (1 : Fin 2) >> encM M = encM (bumpM M) := by
  cases M with
  | nil => simp [bumpM]
  | cons x M' =>
    cases x with
    | zero => simp [bumpM]
    | run d => simp [bumpM]

macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, zero_cons_default, default_head, default_tail,
    encLeft_nil, encRight_nil, enc1_nil, encM_nil, encM_cons_zero, encM_cons_run,
    encLeft_cons_head, cons_one_encLeft_tail,
    encRight_cons_head, cons_one_encRight_tail,
    encM_cons_run_head, cons_one_encM_cons_run_tail, multiStep_zero]
  try rfl))

macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run,
    encLeft_cons_head, cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
    encM_cons_run_head, cons_one_encM_cons_run_tail]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run,
    encLeft_cons_head, cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
    encM_cons_run_head, cons_one_encM_cons_run_tail]))

macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

def cfgBB (L R : List MItem) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encM L, encM R⟩⟩

def cfgCB (L R : List MItem) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encM L, encM R⟩⟩

def cfgDL (L R : List MItem) : Cfg (Fin 2) (Fin 6) :=
  (encM L) <{{D}} (encM R)

lemma step_BB_nil (R : List MItem) :
    (cfgBB [] R) [target_tm]⊢⁺ cfgCB [] (bumpM R) := by
  unfold cfgBB cfgCB
  rw [← encM_bumpM]
  execute 1

lemma step_BB_zero (L1 R : List MItem) :
    (cfgBB (.zero :: L1) R) [target_tm]⊢⁺ cfgCB L1 (bumpM R) := by
  unfold cfgBB cfgCB
  rw [← encM_bumpM]
  execute 1

lemma step_BB_run0 (L1 R : List MItem) :
    (cfgBB (.run 0 :: L1) R) [target_tm]⊢⁺ cfgBB L1 (.run 0 :: R) := by
  unfold cfgBB
  execute 8

lemma step_BB_run1 (L1 R : List MItem) :
    (cfgBB (.run 1 :: L1) R) [target_tm]⊢⁺ cfgBB L1 (.run 0 :: bumpM R) := by
  unfold cfgBB
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

lemma step_BB_run2 (L1 R : List MItem) :
    (cfgBB (.run 2 :: L1) R) [target_tm]⊢⁺ cfgDL L1 (.run 0 :: .run 0 :: bumpM R) := by
  unfold cfgBB cfgDL
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 5

lemma step_BB_run3 (L1 R : List MItem) :
    (cfgBB (.run 3 :: L1) R) [target_tm]⊢⁺ cfgBB (.run 0 :: .zero :: .zero :: L1) (bumpM R) := by
  unfold cfgBB
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  execute 9

lemma step_BB_run_ge4 (d : ℕ) (L1 R : List MItem) :
    (cfgBB (.run (d + 4) :: L1) R) [target_tm]⊢⁺ cfgBB (.run 0 :: .zero :: .run d :: L1) (bumpM R) := by
  unfold cfgBB
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  execute 9

lemma cyc_R_A (k : ℕ) (V s : ListBlank (Fin 2)) :
    (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢*
    ⟨some A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V), s⟩⟩ := by
  induction k generalizing V with
  | zero => finish
  | succ k ih =>
    have h1 :
        (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ (k + 1)) +> s⟩⟩ : Cfg (Fin 2) (Fin 6))
          [target_tm]⊢⁺
        ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ := by
      execute 3
    have h2 := ih ((0 : Fin 2) >> V)
    have h12 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_eq :
        (([0] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> V) =
        (([0] : List (Fin 2)) ^ (k + 1)) +> V := by
      rw [zeros_append_cons_zero k V]
      simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]
    rwa [h_eq] at h12

lemma exit_R_A (W R1 : List MItem) :
    (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM W, (0 : Fin 2) >> encM R1⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    cfgCB (.run 0 :: .run 0 :: W) R1 := by
  unfold cfgCB
  execute 13

lemma encM_replicate_zero (k : ℕ) (L : List MItem) :
    ((([0] : List (Fin 2)) ^ k) +> encM L) = encM (List.replicate k .zero ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_list, nil_append_list, listblank_append_cons, ih,
      List.replicate_succ, List.cons_append, encM_cons_zero]

lemma step_DL_run0 (L1 R : List MItem) :
    (cfgDL (.run 0 :: L1) R) [target_tm]⊢⁺ cfgBB L1 (bumpM R) := by
  unfold cfgDL cfgBB
  rw [← encM_bumpM]
  execute 1

lemma step_DL_run1 (L1 R : List MItem) :
    (cfgDL (.run 1 :: L1) R) [target_tm]⊢⁺ cfgDL L1 (.run 0 :: bumpM R) := by
  unfold cfgDL
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

lemma step_DL_run2 (d0 : ℕ) (L1 R1 : List MItem) :
    (cfgDL (.run 2 :: L1) (.run d0 :: R1)) [target_tm]⊢⁺
      cfgCB (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1 := by
  unfold cfgDL
  have h1 :
      ((encM (.run 2 :: L1)) <{{D}} (encM (.run d0 :: R1)))
        [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM L1,
        (([1] : List (Fin 2)) ^ (d0 + 1)) +> ((0 : Fin 2) >> encM R1)⟩⟩ := by
    execute 6
  have h2 := cyc_R_A (d0 + 1) ((0 : Fin 2) >> (0 : Fin 2) >> encM L1) ((0 : Fin 2) >> encM R1)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h_z1 := zeros_append_cons_zero (d0 + 1) ((0 : Fin 2) >> encM L1)
  have h_z2 := zeros_append_cons_zero (d0 + 1) (encM L1)
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  exact stepPlus_trans h12 (exit_R_A (List.replicate (d0 + 1) .zero ++ L1) R1)

lemma step_CB_nil (L : List MItem) :
    (cfgCB L []) [target_tm]⊢⁺ cfgDL (bumpM L) [.run 0] := by
  unfold cfgCB cfgDL
  rw [← encM_bumpM]
  execute 2

lemma step_CB_zero (L R1 : List MItem) :
    (cfgCB L (.zero :: R1)) [target_tm]⊢⁺ cfgDL (bumpM L) (bumpM R1) := by
  unfold cfgCB cfgDL
  rw [← encM_bumpM L, ← encM_bumpM R1]
  execute 2

lemma step_CB_run0_nil (L : List MItem) :
    (cfgCB L [.run 0]) [target_tm]⊢⁺ cfgBB (.run 0 :: bumpM L) [] := by
  unfold cfgCB cfgBB
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

lemma step_CB_run0_zero (L R2 : List MItem) :
    (cfgCB L (.run 0 :: .zero :: R2)) [target_tm]⊢⁺ cfgBB (.run 0 :: bumpM L) R2 := by
  unfold cfgCB cfgBB
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

lemma step_CB_run0_run0 (L R2 : List MItem) :
    (cfgCB L (.run 0 :: .run 0 :: R2)) [target_tm]⊢⁺ cfgBB (.run 0 :: .zero :: bumpM L) R2 := by
  unfold cfgCB cfgBB
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  execute 6

lemma step_CB_run0_run_pos (d2 : ℕ) (L R2 : List MItem) :
    (cfgCB L (.run 0 :: .run (d2 + 1) :: R2)) [target_tm]⊢⁺
      cfgCB (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2 := by
  unfold cfgCB
  have h1 :
      (⟨some C, ⟨0, encM L, encM (.run 0 :: .run (d2 + 1) :: R2)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> encM (bumpM L),
        (([1] : List (Fin 2)) ^ (d2 + 1)) +> ((0 : Fin 2) >> encM R2)⟩⟩ := by
    rw [← encM_bumpM L]
    execute 5
  have h2 := cyc_R_A (d2 + 1) ((0 : Fin 2) >> encM (bumpM L)) ((0 : Fin 2) >> encM R2)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h_z1 := zeros_append_cons_zero (d2 + 1) (encM (bumpM L))
  have h_z2 :
      ((([0] : List (Fin 2)) ^ (d2 + 1)) +> encM (bumpM L)) =
      (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ d2) +> encM (bumpM L)) := by
    simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  exact stepPlus_trans h12 (exit_R_A (List.replicate d2 .zero ++ bumpM L) R2)

lemma step_CB_run1 (L R1 : List MItem) :
    (cfgCB L (.run 1 :: R1)) [target_tm]⊢⁺ cfgCB (.run 0 :: bumpM L) R1 := by
  unfold cfgCB
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

lemma step_CB_run2 (L R1 : List MItem) :
    (cfgCB L (.run 2 :: R1)) [target_tm]⊢⁺ cfgBB (bumpM L) (.run 0 :: .zero :: R1) := by
  unfold cfgCB cfgBB
  rw [← encM_bumpM]
  execute 5

lemma step_CB_run_ge3 (d : ℕ) (L R1 : List MItem) :
    (cfgCB L (.run (d + 3) :: R1)) [target_tm]⊢⁺ cfgBB (bumpM L) (.run 0 :: .run d :: R1) := by
  unfold cfgCB cfgBB
  rw [← encM_bumpM]
  execute 5

set_option maxRecDepth 200000

lemma init_to_CB : (init []) [target_tm]⊢⁺ cfgCB [] [.run 1, .run 0] := by
  rw [init_nil]
  unfold cfgCB
  execute 18

lemma step_DL_zero_halt (L1 R1 : List MItem) :
    (cfgDL (.zero :: L1) (.run 0 :: R1)) [target_tm]⊢⁺
    ⟨some E, ⟨1, (1 : Fin 2) >> encM L1, (0 : Fin 2) >> encM R1⟩⟩ := by
  unfold cfgDL
  execute 1

inductive SymMode where
  | BB : SymMode
  | DL : SymMode
  | CB : SymMode
  | HALT : SymMode
  deriving DecidableEq, Repr

def strictMList {α : Type*} (xs : List MItem) (f : List MItem → α) : α :=
  match xs with
  | [] => f []
  | h :: t => f (h :: t)

lemma strictMList_eq {α : Type*} (xs : List MItem) (f : List MItem → α) : strictMList xs f = f xs := by
  cases xs <;> rfl

def prependZeroM : ℕ → List MItem → List MItem
  | 0, acc => acc
  | n + 1, acc => prependZeroM n (.zero :: acc)

def stepElemM : SymMode × List MItem × List MItem → SymMode × List MItem × List MItem
  | (.BB, [], R) => strictMList (bumpM R) (fun R' => (.CB, [], R'))
  | (.BB, .zero :: L1, R) => strictMList (bumpM R) (fun R' => (.CB, L1, R'))
  | (.BB, .run 0 :: L1, R) => (.BB, L1, .run 0 :: R)
  | (.BB, .run 1 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, L1, .run 0 :: R'))
  | (.BB, .run 2 :: L1, R) => strictMList (bumpM R) (fun R' => (.DL, L1, .run 0 :: .run 0 :: R'))
  | (.BB, .run 3 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, .run 0 :: .zero :: .zero :: L1, R'))
  | (.BB, .run (d + 4) :: L1, R) =>
    strictNat d (fun d' => strictMList (bumpM R) (fun R' => (.BB, .run 0 :: .zero :: .run d' :: L1, R')))
  | (.DL, .zero :: L1, R) => (.HALT, .zero :: L1, R)
  | (.DL, .run 0 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, L1, R'))
  | (.DL, .run 1 :: L1, R) => strictMList (bumpM R) (fun R' => (.DL, L1, .run 0 :: R'))
  | (.DL, .run 2 :: L1, .run d0 :: R1) =>
    strictMList (prependZeroM (d0 + 1) L1) (fun L' => (.CB, .run 0 :: .run 0 :: L', R1))
  | (.CB, L, []) => strictMList (bumpM L) (fun L' => (.DL, L', [.run 0]))
  | (.CB, L, .zero :: R1) =>
    strictMList (bumpM L) (fun L' => strictMList (bumpM R1) (fun R' => (.DL, L', R')))
  | (.CB, L, .run 0 :: []) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: L', []))
  | (.CB, L, .run 0 :: .zero :: R2) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: L', R2))
  | (.CB, L, .run 0 :: .run 0 :: R2) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: .zero :: L', R2))
  | (.CB, L, .run 0 :: .run (d2 + 1) :: R2) =>
    strictMList (bumpM L) (fun L1 => strictMList (prependZeroM d2 L1) (fun L2 => (.CB, .run 0 :: .run 0 :: L2, R2)))
  | (.CB, L, .run 1 :: R1) => strictMList (bumpM L) (fun L' => (.CB, .run 0 :: L', R1))
  | (.CB, L, .run 2 :: R1) => strictMList (bumpM L) (fun L' => (.BB, L', .run 0 :: .zero :: R1))
  | (.CB, L, .run (d + 3) :: R1) =>
    strictNat d (fun d' => strictMList (bumpM L) (fun L' => (.BB, L', .run 0 :: .run d' :: R1)))
  | s => s

def iterStep {α : Type*} (f : α → α) : ℕ → α → α
  | 0, s => s
  | n + 1, s => iterStep f n (f s)

def stepElem16 := iterStep stepElemM 16
def stepElem256 := iterStep stepElem16 16
def stepElem4096 := iterStep stepElem256 16

def runElemFast (s : SymMode × List MItem × List MItem) : SymMode × List MItem × List MItem :=
  -- 19217 = 4 * 4096 + 11 * 256 + 1 * 16 + 1
  iterStep stepElemM 1 (iterStep stepElem16 1 (iterStep stepElem256 11 (iterStep stepElem4096 4 s)))

inductive SymTok where
  | item : MItem → SymTok
  | repB1 : ℕ → SymTok
  | rep2 : ℕ → SymTok
  | rep12 : ℕ → SymTok
  deriving DecidableEq

def strictList {α : Type*} (xs : List SymTok) (f : List SymTok → α) : α :=
  match xs with
  | [] => f []
  | h :: t => f (h :: t)

lemma strictList_eq {α : Type*} (xs : List SymTok) (f : List SymTok → α) : strictList xs f = f xs := by
  cases xs <;> rfl

def stripPrefixSym : List SymTok → List SymTok → Option (List SymTok)
  | [], xs => some xs
  | p :: ps, x :: xs => if p = x then stripPrefixSym ps xs else none
  | _ :: _, [] => none

lemma stripPrefixSym_some (pre xs rest : List SymTok)
    (h : stripPrefixSym pre xs = some rest) : xs = pre ++ rest := by
  induction pre generalizing xs with
  | nil => simp [stripPrefixSym] at h; exact h
  | cons p ps ih =>
    cases xs with
    | nil => simp [stripPrefixSym] at h
    | cons x xs1 =>
      simp only [stripPrefixSym] at h
      split at h
      · rename_i heq; subst heq; rw [List.cons_append, ih xs1 h]
      · contradiction

def getRepB1 : SymTok → Option ℕ
  | .repB1 k => some k
  | _ => none

def getRep2 : SymTok → Option ℕ
  | .rep2 p => some p
  | _ => none

def getRep12 : SymTok → Option ℕ
  | .rep12 m => some m
  | _ => none

def eatStep (blk : List SymTok) (getRep : SymTok → Option ℕ) (k : ℕ) (xs : List SymTok) : Option (ℕ × List SymTok) :=
  match xs with
  | [] => none
  | x :: rest =>
    match getRep x with
    | some k2 => some (k + k2, rest)
    | none =>
      match stripPrefixSym blk (x :: rest) with
      | some rest2 => some (k + 1, rest2)
      | none => none

def eatFuel (blk : List SymTok) (mkRep : ℕ → SymTok) (getRep : SymTok → Option ℕ) :
    ℕ → ℕ → List SymTok → List SymTok
  | 0, k, xs => mkRep k :: xs
  | fuel + 1, k, xs =>
    match eatStep blk getRep k xs with
    | some (k', rest) => strictNat k' (fun k'' => eatFuel blk mkRep getRep fuel k'' rest)
    | none => mkRep k :: xs

def eatB1 (k : ℕ) (xs : List SymTok) : List SymTok :=
  eatFuel [.item (.run 0), .item (.run 1)] .repB1 getRepB1 4 k xs

def eatC2 (p : ℕ) (xs : List SymTok) : List SymTok :=
  eatFuel [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2 4 p xs

def eatB2 (p : ℕ) (xs : List SymTok) : List SymTok :=
  eatFuel [.item (.run 0), .item (.run 1), .item (.run 1)] .rep2 getRep2 4 p xs

def eatC12 (m : ℕ) (xs : List SymTok) : List SymTok :=
  eatFuel [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12 4 m xs

def eatB12R (m : ℕ) (xs : List SymTok) : List SymTok :=
  eatFuel [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)] .rep12 getRep12 4 m xs

def peelTok : SymTok → List SymTok → List SymTok
  | .repB1 0, xs => .repB1 0 :: xs
  | .repB1 1, xs => .item (.run 0) :: .item (.run 1) :: xs
  | .repB1 (k + 2), xs => strictNat (k + 1) (fun k' => .item (.run 0) :: .item (.run 1) :: .repB1 k' :: xs)
  | .rep2 0, xs => .rep2 0 :: xs
  | .rep2 1, xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: xs
  | .rep2 (p + 2), xs => strictNat (p + 1) (fun p' => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep2 p' :: xs)
  | .rep12 0, xs => .rep12 0 :: xs
  | .rep12 1, xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: xs
  | .rep12 (m + 2), xs => strictNat (m + 1) (fun m' => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep12 m' :: xs)
  | .item x, xs => .item x :: xs

def peelL : List SymTok → List SymTok
  | [] => []
  | t :: xs => peelTok t xs

def splitB2Aux : ℕ → ℕ → List SymTok → ℕ × List SymTok
  | 0, p, xs => (p, xs)
  | fuel + 1, p, xs =>
    match stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1)] xs with
    | some rest => strictNat (p + 1) (fun p' => splitB2Aux fuel p' rest)
    | none => (p, xs)

def splitB2 (p : ℕ) (xs : List SymTok) : ℕ × List SymTok := splitB2Aux 32 p xs

def sep3A : List SymTok := [.item (.run 0), .item (.run 1), .item (.run 2)]
def sep3B : List SymTok := [.item (.run 0), .item .zero, .item (.run 1)]

def popSep3 (xs : List SymTok) : Option (List SymTok × List SymTok) :=
  match stripPrefixSym sep3A xs with
  | some rest => some (sep3A, rest)
  | none =>
    match stripPrefixSym sep3B xs with
    | some rest => some (sep3B, rest)
    | none => none

def popRep2 : List SymTok → Option (ℕ × List SymTok)
  | .rep2 p :: rest => some (p, rest)
  | _ => none

def popRep12 : List SymTok → Option (ℕ × List SymTok)
  | .rep12 m :: rest => some (m, rest)
  | _ => none

def popRepB1 : List SymTok → Option (ℕ × List SymTok)
  | .repB1 k :: rest => some (k, rest)
  | _ => none

def matchEndB1 (xs : List SymTok) : Option ℕ :=
  match popRepB1 xs with
  | some (k, rest) =>
    match stripPrefixSym [.item (.run 0)] rest with
    | some rest2 =>
      match rest2 with
      | [] => some k
      | _ :: _ => none
    | none => none
  | none => none

def bumpSymL : List SymTok → List SymTok
  | [] => [.item (.run 0)]
  | .item .zero :: M => .item (.run 0) :: M
  | .item (.run d) :: M => strictNat (d + 1) (fun d' => .item (.run d') :: M)
  | .repB1 0 :: M => bumpSymL M
  | .repB1 1 :: M => .item (.run 1) :: .item (.run 1) :: M
  | .repB1 (k + 2) :: M => strictNat (k + 1) (fun k' => .item (.run 1) :: .item (.run 1) :: .repB1 k' :: M)
  | .rep2 0 :: M => bumpSymL M
  | .rep2 (p + 1) :: M => strictNat p (fun p' => .item (.run 2) :: .item (.run 0) :: .item (.run 1) :: .rep2 p' :: M)
  | .rep12 0 :: M => bumpSymL M
  | .rep12 (m + 1) :: M => strictNat m (fun m' => .item (.run 2) :: .item (.run 0) :: .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep12 m' :: M)

def bumpSymR : List SymTok → List SymTok
  | [] => [.item (.run 0)]
  | .item .zero :: M => .item (.run 0) :: M
  | .item (.run d) :: M => strictNat (d + 1) (fun d' => .item (.run d') :: M)
  | .repB1 0 :: M => bumpSymR M
  | .repB1 1 :: M => .item (.run 1) :: .item (.run 1) :: M
  | .repB1 (k + 2) :: M => strictNat (k + 1) (fun k' => .item (.run 1) :: .item (.run 1) :: .repB1 k' :: M)
  | .rep2 0 :: M => bumpSymR M
  | .rep2 (p + 1) :: M => strictNat p (fun p' => .item (.run 1) :: .item (.run 1) :: .item (.run 1) :: .rep2 p' :: M)
  | .rep12 0 :: M => bumpSymR M
  | .rep12 (m + 1) :: M => strictNat m (fun m' => .item (.run 1) :: .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .item (.run 1) :: .rep12 m' :: M)

def prependZeroSym : ℕ → List SymTok → List SymTok
  | 0, acc => acc
  | n + 1, acc => prependZeroSym n (.item .zero :: acc)

def stepElemBB (L R : List SymTok) : SymMode × List SymTok × List SymTok :=
  match L with
  | [] => strictList (bumpSymR R) (fun R' => (.CB, [], R'))
  | .item .zero :: L1 => strictList (bumpSymR R) (fun R' => (.CB, L1, R'))
  | .item (.run 0) :: L1 => (.BB, L1, .item (.run 0) :: R)
  | .item (.run 1) :: L1 => strictList (bumpSymR R) (fun R' => (.BB, L1, .item (.run 0) :: R'))
  | .item (.run 2) :: L1 => strictList (bumpSymR R) (fun R' => (.DL, L1, .item (.run 0) :: .item (.run 0) :: R'))
  | .item (.run 3) :: L1 => strictList (bumpSymR R) (fun R' => (.BB, .item (.run 0) :: .item .zero :: .item .zero :: L1, R'))
  | .item (.run (d + 4)) :: L1 =>
    strictNat d (fun d' => strictList (bumpSymR R) (fun R' => (.BB, .item (.run 0) :: .item .zero :: .item (.run d') :: L1, R')))
  | .repB1 k :: L1 => (.BB, .repB1 k :: L1, R)
  | .rep2 p :: L1 => (.BB, .rep2 p :: L1, R)
  | .rep12 m :: L1 => (.BB, .rep12 m :: L1, R)

def stepElemDL (L R : List SymTok) : SymMode × List SymTok × List SymTok :=
  match L with
  | [] => (.DL, [], R)
  | .item .zero :: L1 => (.HALT, .item .zero :: L1, R)
  | .item (.run 0) :: L1 => strictList (bumpSymR R) (fun R' => (.BB, L1, R'))
  | .item (.run 1) :: L1 => strictList (bumpSymR R) (fun R' => (.DL, L1, .item (.run 0) :: R'))
  | .item (.run 2) :: L1 =>
    match R with
    | .item (.run d0) :: R1 =>
      strictList (prependZeroSym (d0 + 1) L1) (fun L' => (.CB, .item (.run 0) :: .item (.run 0) :: L', R1))
    | [] => (.DL, .item (.run 2) :: L1, [])
    | .item .zero :: R1 => (.DL, .item (.run 2) :: L1, .item .zero :: R1)
    | .repB1 k :: R1 => (.DL, .item (.run 2) :: L1, .repB1 k :: R1)
    | .rep2 p :: R1 => (.DL, .item (.run 2) :: L1, .rep2 p :: R1)
    | .rep12 m :: R1 => (.DL, .item (.run 2) :: L1, .rep12 m :: R1)
  | .item (.run (d + 3)) :: L1 => (.DL, .item (.run (d + 3)) :: L1, R)
  | .repB1 k :: L1 => (.DL, .repB1 k :: L1, R)
  | .rep2 p :: L1 => (.DL, .rep2 p :: L1, R)
  | .rep12 m :: L1 => (.DL, .rep12 m :: L1, R)

def stepElemCB_run0 (L : List SymTok) : List SymTok → SymMode × List SymTok × List SymTok
  | [] => strictList (bumpSymL L) (fun L' => (.BB, .item (.run 0) :: L', []))
  | .item .zero :: R2 => strictList (bumpSymL L) (fun L' => (.BB, .item (.run 0) :: L', R2))
  | .item (.run 0) :: R2 => strictList (bumpSymL L) (fun L' => (.BB, .item (.run 0) :: .item .zero :: L', R2))
  | .item (.run (d2 + 1)) :: R2 =>
    strictList (bumpSymL L) (fun L1 => strictList (prependZeroSym d2 L1) (fun L2 => (.CB, .item (.run 0) :: .item (.run 0) :: L2, R2)))
  | .repB1 k :: R2 => (.CB, L, .item (.run 0) :: .repB1 k :: R2)
  | .rep2 p :: R2 => (.CB, L, .item (.run 0) :: .rep2 p :: R2)
  | .rep12 m :: R2 => (.CB, L, .item (.run 0) :: .rep12 m :: R2)

def stepElemCB (L R : List SymTok) : SymMode × List SymTok × List SymTok :=
  match R with
  | [] => strictList (bumpSymL L) (fun L' => (.DL, L', [.item (.run 0)]))
  | .item .zero :: R1 =>
    strictList (bumpSymL L) (fun L' => strictList (bumpSymR R1) (fun R' => (.DL, L', R')))
  | .item (.run 0) :: R1 => stepElemCB_run0 L R1
  | .item (.run 1) :: R1 => strictList (bumpSymL L) (fun L' => (.CB, .item (.run 0) :: L', R1))
  | .item (.run 2) :: R1 => strictList (bumpSymL L) (fun L' => (.BB, L', .item (.run 0) :: .item .zero :: R1))
  | .item (.run (d + 3)) :: R1 =>
    strictNat d (fun d' => strictList (bumpSymL L) (fun L' => (.BB, L', .item (.run 0) :: .item (.run d') :: R1)))
  | .repB1 k :: R1 => (.CB, L, .repB1 k :: R1)
  | .rep2 p :: R1 => (.CB, L, .rep2 p :: R1)
  | .rep12 m :: R1 => (.CB, L, .rep12 m :: R1)

def stepElemSym : SymMode → List SymTok → List SymTok → SymMode × List SymTok × List SymTok
  | .BB, L, R => stepElemBB L R
  | .DL, L, R => stepElemDL L R
  | .CB, L, R => stepElemCB L R
  | .HALT, L, R => (.HALT, L, R)

def sweepBB : List SymTok → List SymTok → SymMode × List SymTok × List SymTok
  | [], R => stepElemBB [] R
  | .item .zero :: L1, R => stepElemBB (.item .zero :: L1) R
  | .item (.run 0) :: L1, R => sweepBB L1 (.item (.run 0) :: R)
  | .item (.run 1) :: L1, R => strictList (bumpSymR R) (fun R' => sweepBB L1 (.item (.run 0) :: R'))
  | .item (.run (d + 2)) :: L1, R => strictNat (d + 2) (fun d' => stepElemBB (.item (.run d') :: L1) R)
  | .repB1 k :: L1, R => strictList (eatB1 k R) (fun R' => sweepBB L1 R')
  | .rep2 p :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => strictList (eatB2 p R2) (fun R' => sweepBB L1 (.item (.run 0) :: .item (.run 1) :: R'))
    | none => strictList (peelTok (.rep2 p) L1) (fun L' => stepElemBB L' R)
  | .rep12 m :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => strictList (eatB12R m R2) (fun R' => sweepBB L1 (.item (.run 0) :: .item (.run 1) :: R'))
    | none => strictList (peelTok (.rep12 m) L1) (fun L' => stepElemBB L' R)

def sweepCB (L : List SymTok) : List SymTok → List SymTok × List SymTok
  | [] => (L, [])
  | .item .zero :: R1 => (L, .item .zero :: R1)
  | .item (.run 0) :: .item (.run 1) :: R2 =>
    strictList (bumpSymL L) (fun L' => sweepCB (.item (.run 0) :: .item (.run 0) :: L') R2)
  | .item (.run 0) :: R1 => (L, .item (.run 0) :: R1)
  | .item (.run 1) :: R1 =>
    strictList (bumpSymL L) (fun L' => sweepCB (.item (.run 0) :: L') R1)
  | .item (.run (d + 2)) :: R1 => strictNat (d + 2) (fun d' => (L, .item (.run d') :: R1))
  | .repB1 k :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => strictList (eatB1 k L1) (fun L' => sweepCB (.item (.run 0) :: L') R1)
    | none => (L, .repB1 k :: R1)
  | .rep2 p :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => strictList (eatC2 p L1) (fun L' => sweepCB (.item (.run 0) :: L') R1)
    | none => (L, .rep2 p :: R1)
  | .rep12 m :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => strictList (eatC12 m L1) (fun L' => sweepCB (.item (.run 0) :: L') R1)
    | none => (L, .rep12 m :: R1)

def finishThenBB : SymMode × List SymTok × List SymTok → SymMode × List SymTok × List SymTok
  | (.BB, L1, R1) => sweepBB L1 R1
  | (.DL, L1, R1) => (.DL, L1, R1)
  | (.CB, L1, R1) => (.CB, L1, R1)
  | (.HALT, L1, R1) => (.HALT, L1, R1)

def stepElemThenBB (m : SymMode) (L R : List SymTok) : SymMode × List SymTok × List SymTok :=
  finishThenBB (stepElemSym m L R)

def tryRuleA (L : List SymTok) (d : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List SymTok :=
  match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
     .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)] L with
  | some rest =>
    match matchEndB1 rest with
    | some k =>
      strictNat (d / 6) (fun n1 =>
        match Nat.ble 2 n1 && Nat.ble n1 k with
        | true =>
          strictNat (n1 - 1) (fun m_new =>
          strictNat (k - n1) (fun k_new =>
          strictNat (d - 6 * n1) (fun d_new =>
            (.CB,
             [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
              .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
              .rep12 m_new, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
              .item .zero, .item (.run 1), .repB1 k_new, .item (.run 0)],
             .item (.run d_new) :: R_tail))))
        | false => stepElemThenBB .CB L (.item (.run d) :: R_tail))
    | none => stepElemThenBB .CB L (.item (.run d) :: R_tail)
  | none => stepElemThenBB .CB L (.item (.run d) :: R_tail)

def afterSplitB2 (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) (res : ℕ × List SymTok) : SymMode × List SymTok × List SymTok :=
  match popSep3 res.2 with
  | some (s_sep, rest0) =>
    match popRep12 rest0 with
    | some (m12, rest1) =>
      match stripPrefixSym [.item (.run 1), .item (.run 0), .item (.run 1)] rest1 with
      | some rest2 =>
        match popSep3 rest2 with
        | some (m_sep, rest3) =>
          match matchEndB1 rest3 with
          | some k1 =>
            let p := res.1
            match Nat.ble 2 p && Nat.ble 2 m12 && Nat.ble m12 k1 with
            | true =>
              strictNat (m12 - 1) (fun n3 =>
              strictNat (p + 2 * n3 - 1) (fun p_new =>
              strictNat (k1 - n3) (fun k_new =>
              strictNat (d2 + 4 * n3) (fun d_new =>
                (.CB,
                 [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 p_new, .item (.run 1)] ++
                   s_sep ++ [.rep12 1, .item (.run 1), .item (.run 0), .item (.run 1)] ++
                   m_sep ++ [.repB1 k_new, .item (.run 0)],
                 .item .zero :: .item (.run d_new) :: R_tail)))))
            | false => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
          | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
        | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
      | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
    | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
  | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)

def tryRuleB (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List SymTok :=
  match stripPrefixSym [.item (.run 0)] L with
  | some restL => afterSplitB2 L d2 R_tail (splitB2 0 restL)
  | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)

def tryRuleBC (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List SymTok :=
  match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
  | some rest1 =>
    match popRep2 rest1 with
    | some (p, restC) =>
      match stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1)] restC with
      | some rest2 =>
        match matchEndB1 rest2 with
        | some k1 =>
          match Nat.ble 3 p && Nat.ble 1 k1 with
          | true =>
            strictNat (p - 2) (fun n4 =>
            strictNat (k1 + 2 * n4) (fun k_new =>
            strictNat (d2 + 2 * n4) (fun d_new =>
              (.CB,
               [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 2,
                .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1),
                .repB1 k_new, .item (.run 0)],
               .item .zero :: .item (.run d_new) :: R_tail))))
          | false => tryRuleB L d2 R_tail
        | none => tryRuleB L d2 R_tail
      | none => tryRuleB L d2 R_tail
    | none => tryRuleB L d2 R_tail
  | none => tryRuleB L d2 R_tail

def afterSweepCB : List SymTok × List SymTok → SymMode × List SymTok × List SymTok
  | (L, .item .zero :: .item (.run d2) :: R_tail) => tryRuleBC L d2 R_tail
  | (L, .item (.run (d + 12)) :: R_tail) => strictNat (d + 12) (fun d' => tryRuleA L d' R_tail)
  | (L, R) => stepElemThenBB .CB L R

def stepSym : SymMode × List SymTok × List SymTok → SymMode × List SymTok × List SymTok
  | (.BB, L, R) => sweepBB L R
  | (.DL, L, R) => strictList (peelL L) (fun L' => stepElemThenBB .DL L' R)
  | (.HALT, L, R) => (.HALT, L, R)
  | (.CB, L0, R0) => afterSweepCB (sweepCB L0 R0)

def stepSym16 := iterStep stepSym 16
def stepSym256 := iterStep stepSym16 16
def stepSym4096 := iterStep stepSym256 16

def initSymCyc3 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 46, .item (.run 0)], [.item (.run 79), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk4096 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .rep12 69932, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 349284, .item (.run 0)], [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk8192 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .rep12 293731192, .item (.run 2), .repB1 1468655224, .item (.run 0)], [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 6), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk12288 : SymMode × List SymTok × List SymTok :=
  (.CB, [], [.item (.run 1), .repB1 7401584263016, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .rep2 1, .item (.run 0), .item (.run 1), .item .zero, .item (.run 7401584264101), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero, .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1)])

def symChk16384 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 0), .item (.run 1), .rep2 5828399623694162, .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .repB1 11656799247386921, .item (.run 0)], [.item (.run 0), .item (.run 11656799247388309), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 2), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 3), .item (.run 3), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 5), .item (.run 3), .item (.run 1), .item (.run 1)])

def symChk20480 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .rep12 9179181364734787724, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 45895906823673936877, .item (.run 0)], [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk24576 : SymMode × List SymTok × List SymTok :=
  (.DL, [.repB1 192751300452273201788429, .item (.run 0)], [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .rep12 38550260090454640358104, .item (.run 0), .item (.run 2), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero, .item (.run 3), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1)])

def symChk28672 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .rep12 161901426063024309850221340, .item (.run 2), .repB1 809507130315121549251104250, .item (.run 0)], [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 5), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk32768 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .repB1 3399726966787864888523559563277, .item (.run 0)], [.item (.run 0), .item (.run 1), .item (.run 1), .rep12 679945393357572977704711913207, .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 4), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk36864 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .repB1 8566800475893506045311193103085396, .item (.run 0)], [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .rep2 4283400237946753022655596551544268, .item (.run 0), .item (.run 1), .item .zero, .item (.run 8566800475893506045311193103088524), .item (.run 1), .item (.run 2), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1), .item (.run 1)])

def symChk40960 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .repB1 59964023182123780301115281865963814445, .item (.run 0)], [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .rep12 11992804636424756060223056373192763585, .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1), .item (.run 7), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk45056 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .rep12 28331309434081290173749125880312046958998, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 141656547170406450868745629401560234791159, .item (.run 0)], [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 7), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk49152 : SymMode × List SymTok × List SymTok :=
  (.BB, [.item (.run 0), .item (.run 1), .rep2 1, .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .repB1 535429780494748407225024473657428158523986309, .item (.run 0)], [.item (.run 0), .item (.run 1), .item (.run 2), .item (.run 535429780494748407225024473657428158523990526), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk53248 : SymMode × List SymTok × List SymTok :=
  (.CB, [], [.item (.run 1), .repB1 1873892351078590533629325742230370269117066257558, .item (.run 0), .item (.run 2), .item (.run 0), .item (.run 1), .item (.run 1), .rep12 374778470215718106725865148446074053823413252433, .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 6), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 5), .item (.run 1), .item (.run 6), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk57344 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .rep2 996031434861122243531684763682732439419162283857463, .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 1992062869722244487063369527365464878838324567709997, .item (.run 0)], [.item (.run 1992062869722244487063369527365464878838324567714920), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk61440 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .rep12 661776688146251534887371767366373046443244305364132822, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 3308883440731257674436858836831865232216221526820658827, .item (.run 0)], [.item (.run 4), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk65536 : SymMode × List SymTok × List SymTok :=
  (.DL, [.rep12 659540004931999983852102031802319817808504446014405329671, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 3297700024659999919260510159011599089042522230072026642750, .item (.run 0)], [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 4), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero, .item (.run 1), .item (.run 3), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk69632 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 2629243525178812812679392664523750958759518709707280000200843, .item (.run 0)], [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .rep2 1314621762589406406339696332261875479379759354853640000103353, .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 2629243525178812812679392664523750958759518709707280000206708), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk70511 : SymMode × List SymTok × List SymTok :=
  (.HALT, [.item .zero, .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .rep12 2077426982857333580388655932463210634081595029892171852015193, .item (.run 2), .repB1 10387134914286667901943279662316053170407975149460859260070043, .item (.run 0)], [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 3), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])



lemma stepStar_refl {M : Machine Γ Λ} {c : Cfg Γ Λ} : c [M]⊢* c := ⟨0, rfl⟩

lemma step_BB_r0_r1 (L R : List MItem) :
    (cfgBB (.run 0 :: .run 1 :: L) R) [target_tm]⊢⁺ cfgBB L (.run 0 :: .run 1 :: R) :=
  stepPlus_trans (step_BB_run0 (.run 1 :: L) R) (step_BB_run1 L (.run 0 :: R))

lemma step_BB_r1_r0_r1_comm (L R : List MItem) :
    (cfgBB (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R)) [target_tm]⊢⁺
      cfgBB L (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R) :=
  stepPlus_trans (step_BB_run1 (.run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
    (stepPlus_trans (step_BB_run0 (.run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: R))
      (step_BB_run1 L (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R)))

def evalM : SymMode × List MItem × List MItem → Cfg (Fin 2) (Fin 6)
  | (.BB, L, R) => cfgBB L R
  | (.DL, L, R) => cfgDL L R
  | (.CB, L, R) => cfgCB L R
  | (.HALT, L, R) => cfgDL L R

lemma prependZeroM_eq (n : ℕ) (acc : List MItem) :
    prependZeroM n acc = List.replicate n .zero ++ acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [prependZeroM, ih, List.replicate_succ', List.append_assoc]
    rfl

lemma stepElemM_sound (s : SymMode × List MItem × List MItem) :
    (evalM s) [target_tm]⊢* (evalM (stepElemM s)) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | BB =>
    cases L with
    | nil =>
      simp only [stepElemM, strictMList_eq, evalM]
      exact stepPlus_stepStar (step_BB_nil R)
    | cons x L1 =>
      cases x with
      | zero =>
        simp only [stepElemM, strictMList_eq, evalM]
        exact stepPlus_stepStar (step_BB_zero L1 R)
      | run d =>
        rcases d with _ | _ | _ | _ | d <;>
          simp only [stepElemM, strictMList_eq, strictNat_eq, evalM]
        · exact stepPlus_stepStar (step_BB_run0 L1 R)
        · exact stepPlus_stepStar (step_BB_run1 L1 R)
        · exact stepPlus_stepStar (step_BB_run2 L1 R)
        · exact stepPlus_stepStar (step_BB_run3 L1 R)
        · exact stepPlus_stepStar (step_BB_run_ge4 d L1 R)
  | DL =>
    cases L with
    | nil => exact stepStar_refl
    | cons x L1 =>
      cases x with
      | zero => exact stepStar_refl
      | run d =>
        rcases d with _ | _ | _ | d
        · simp only [stepElemM, strictMList_eq, evalM]
          exact stepPlus_stepStar (step_DL_run0 L1 R)
        · simp only [stepElemM, strictMList_eq, evalM]
          exact stepPlus_stepStar (step_DL_run1 L1 R)
        · cases R with
          | nil => exact stepStar_refl
          | cons y R1 =>
            cases y with
            | zero => exact stepStar_refl
            | run d0 =>
              simp only [stepElemM, strictMList_eq, evalM, prependZeroM_eq]
              exact stepPlus_stepStar (step_DL_run2 d0 L1 R1)
        · exact stepStar_refl
  | CB =>
    cases R with
    | nil =>
      simp only [stepElemM, strictMList_eq, evalM]
      exact stepPlus_stepStar (step_CB_nil L)
    | cons x R1 =>
      cases x with
      | zero =>
        simp only [stepElemM, strictMList_eq, evalM]
        exact stepPlus_stepStar (step_CB_zero L R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · cases R1 with
          | nil =>
            simp only [stepElemM, strictMList_eq, evalM]
            exact stepPlus_stepStar (step_CB_run0_nil L)
          | cons y R2 =>
            cases y with
            | zero =>
              simp only [stepElemM, strictMList_eq, evalM]
              exact stepPlus_stepStar (step_CB_run0_zero L R2)
            | run d2 =>
              rcases d2 with _ | d2 <;>
                simp only [stepElemM, strictMList_eq, evalM, prependZeroM_eq]
              · exact stepPlus_stepStar (step_CB_run0_run0 L R2)
              · exact stepPlus_stepStar (step_CB_run0_run_pos d2 L R2)
        · simp only [stepElemM, strictMList_eq, evalM]
          exact stepPlus_stepStar (step_CB_run1 L R1)
        · simp only [stepElemM, strictMList_eq, evalM]
          exact stepPlus_stepStar (step_CB_run2 L R1)
        · simp only [stepElemM, strictMList_eq, strictNat_eq, evalM]
          exact stepPlus_stepStar (step_CB_run_ge3 d L R1)
  | HALT => exact stepStar_refl

lemma iterStep_sound {α : Type*} (f : α → α) (ev : α → Cfg (Fin 2) (Fin 6))
    (hf : ∀ s, (ev s) [target_tm]⊢* (ev (f s))) (n : ℕ) (s : α) :
    (ev s) [target_tm]⊢* (ev (iterStep f n s)) := by
  induction n generalizing s with
  | zero => exact stepStar_refl
  | succ n ih => exact stepStar_trans (hf s) (ih (f s))

def repBlock (blk : List MItem) : ℕ → List MItem
  | 0 => []
  | k + 1 => blk ++ repBlock blk k

lemma repBlock_add (blk : List MItem) (k1 k2 : ℕ) :
    repBlock blk (k1 + k2) = repBlock blk k1 ++ repBlock blk k2 := by
  induction k1 with
  | zero => simp [repBlock]
  | succ k1 ih => simp [repBlock, Nat.succ_add, ih, List.append_assoc]

lemma repBlock_succ_right (blk : List MItem) (k : ℕ) :
    repBlock blk (k + 1) = repBlock blk k ++ blk := by
  rw [repBlock_add]
  simp [repBlock]

def encSymL : List SymTok → List MItem
  | [] => []
  | .item x :: xs => x :: encSymL xs
  | .repB1 k :: xs => repBlock [.run 0, .run 1] k ++ encSymL xs
  | .rep2 p :: xs => repBlock [.run 1, .run 0, .run 1] p ++ encSymL xs
  | .rep12 m :: xs => repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ encSymL xs

def encSymR : List SymTok → List MItem
  | [] => []
  | .item x :: xs => x :: encSymR xs
  | .repB1 k :: xs => repBlock [.run 0, .run 1] k ++ encSymR xs
  | .rep2 p :: xs => repBlock [.run 0, .run 1, .run 1] p ++ encSymR xs
  | .rep12 m :: xs => repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ encSymR xs

def evalSym (s : SymMode × List SymTok × List SymTok) : Cfg (Fin 2) (Fin 6) :=
  evalM (s.1, encSymL s.2.1, encSymR s.2.2)

lemma enc_eatFuel (enc : List SymTok → List MItem) (mblk : List MItem)
    (blk : List SymTok) (mkRep : ℕ → SymTok) (getRep : SymTok → Option ℕ)
    (hmk : ∀ k xs, enc (mkRep k :: xs) = repBlock mblk k ++ enc xs)
    (hget : ∀ x k2 rest, getRep x = some k2 → enc (x :: rest) = repBlock mblk k2 ++ enc rest)
    (hblk : ∀ rest, enc (blk ++ rest) = mblk ++ enc rest)
    (fuel k : ℕ) (xs : List SymTok) :
    enc (eatFuel blk mkRep getRep fuel k xs) = repBlock mblk k ++ enc xs := by
  induction fuel generalizing k xs with
  | zero => exact hmk k xs
  | succ fuel ih =>
    simp only [eatFuel]
    cases hstep : eatStep blk getRep k xs with
    | none => exact hmk k xs
    | some kr =>
      rcases kr with ⟨k', rest⟩
      simp only [strictNat_eq, ih k' rest]
      cases xs with
      | nil => simp [eatStep] at hstep
      | cons x rest0 =>
        simp only [eatStep] at hstep
        cases hg : getRep x with
        | some k2 =>
          rw [hg] at hstep
          simp at hstep
          rcases hstep with ⟨rfl, rfl⟩
          rw [repBlock_add, List.append_assoc, ← hget x k2 rest0 hg]
        | none =>
          rw [hg] at hstep
          cases hs : stripPrefixSym blk (x :: rest0) with
          | none => rw [hs] at hstep; contradiction
          | some rest2 =>
            rw [hs] at hstep
            simp at hstep
            rcases hstep with ⟨rfl, rfl⟩
            have hxs := stripPrefixSym_some blk (x :: rest0) rest2 hs
            rw [repBlock_succ_right, List.append_assoc, ← hblk rest2, ← hxs]

lemma encSymL_eatB1 (k : ℕ) (xs : List SymTok) :
    encSymL (eatB1 k xs) = repBlock [.run 0, .run 1] k ++ encSymL xs :=
  enc_eatFuel encSymL [.run 0, .run 1] [.item (.run 0), .item (.run 1)] .repB1 getRepB1
    (fun _ _ => rfl)
    (fun x k2 rest h => by cases x <;> simp [getRepB1] at h; subst h; rfl)
    (fun _ => rfl) 4 k xs

lemma encSymR_eatB1 (k : ℕ) (xs : List SymTok) :
    encSymR (eatB1 k xs) = repBlock [.run 0, .run 1] k ++ encSymR xs :=
  enc_eatFuel encSymR [.run 0, .run 1] [.item (.run 0), .item (.run 1)] .repB1 getRepB1
    (fun _ _ => rfl)
    (fun x k2 rest h => by cases x <;> simp [getRepB1] at h; subst h; rfl)
    (fun _ => rfl) 4 k xs

lemma encSymL_eatC2 (p : ℕ) (xs : List SymTok) :
    encSymL (eatC2 p xs) = repBlock [.run 1, .run 0, .run 1] p ++ encSymL xs :=
  enc_eatFuel encSymL [.run 1, .run 0, .run 1] [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2
    (fun _ _ => rfl)
    (fun x k2 rest h => by cases x <;> simp [getRep2] at h; subst h; rfl)
    (fun _ => rfl) 4 p xs

lemma encSymR_eatB2 (p : ℕ) (xs : List SymTok) :
    encSymR (eatB2 p xs) = repBlock [.run 0, .run 1, .run 1] p ++ encSymR xs :=
  enc_eatFuel encSymR [.run 0, .run 1, .run 1] [.item (.run 0), .item (.run 1), .item (.run 1)] .rep2 getRep2
    (fun _ _ => rfl)
    (fun x k2 rest h => by cases x <;> simp [getRep2] at h; subst h; rfl)
    (fun _ => rfl) 4 p xs

lemma encSymL_eatC12 (m : ℕ) (xs : List SymTok) :
    encSymL (eatC12 m xs) = repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ encSymL xs :=
  enc_eatFuel encSymL [.run 1, .run 0, .run 1, .run 0, .run 1]
    [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12
    (fun _ _ => rfl)
    (fun x k2 rest h => by cases x <;> simp [getRep12] at h; subst h; rfl)
    (fun _ => rfl) 4 m xs

lemma encSymR_eatB12R (m : ℕ) (xs : List SymTok) :
    encSymR (eatB12R m xs) = repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ encSymR xs :=
  enc_eatFuel encSymR [.run 0, .run 1, .run 0, .run 1, .run 1]
    [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)] .rep12 getRep12
    (fun _ _ => rfl)
    (fun x k2 rest h => by cases x <;> simp [getRep12] at h; subst h; rfl)
    (fun _ => rfl) 4 m xs

lemma encSymL_peelTok (t : SymTok) (xs : List SymTok) :
    encSymL (peelTok t xs) = encSymL (t :: xs) := by
  cases t with
  | item x => rfl
  | repB1 k => rcases k with _ | _ | k <;> simp [peelTok, strictNat_eq, encSymL, repBlock]
  | rep2 p => rcases p with _ | _ | p <;> simp [peelTok, strictNat_eq, encSymL, repBlock]
  | rep12 m => rcases m with _ | _ | m <;> simp [peelTok, strictNat_eq, encSymL, repBlock]

lemma encSymL_peelL (xs : List SymTok) : encSymL (peelL xs) = encSymL xs := by
  cases xs with
  | nil => rfl
  | cons t rest => exact encSymL_peelTok t rest

lemma encSymL_prependZeroSym (n : ℕ) (acc : List SymTok) :
    encSymL (prependZeroSym n acc) = List.replicate n .zero ++ encSymL acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [prependZeroSym, ih, encSymL, List.replicate_succ', List.append_assoc]
    rfl

lemma sweep_BB_B1 (k : ℕ) (L R : List MItem) :
    (cfgBB (repBlock [.run 0, .run 1] k ++ L) R) [target_tm]⊢*
    (cfgBB L (repBlock [.run 0, .run 1] k ++ R)) := by
  induction k generalizing R with
  | zero => exact stepStar_refl
  | succ k ih =>
    have h_eq : repBlock [.run 0, .run 1] (k + 1) ++ R =
        repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: R) := by
      rw [repBlock_succ_right, List.append_assoc]; rfl
    rw [h_eq]
    exact stepStar_trans (stepPlus_stepStar (step_BB_r0_r1 (repBlock [.run 0, .run 1] k ++ L) R))
      (ih (.run 0 :: .run 1 :: R))

lemma sweep_BB_C2 (p : ℕ) (L R : List MItem) :
    (cfgBB (repBlock [.run 1, .run 0, .run 1] p ++ L) (.run 0 :: .run 1 :: R)) [target_tm]⊢*
    (cfgBB L (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
  induction p generalizing R with
  | zero => exact stepStar_refl
  | succ p ih =>
    have h_eq : (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] (p + 1) ++ R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ (.run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    exact stepStar_trans (stepPlus_stepStar (step_BB_r1_r0_r1_comm (repBlock [.run 1, .run 0, .run 1] p ++ L) R))
      (ih (.run 0 :: .run 1 :: .run 1 :: R))

lemma sweep_BB_C12 (m : ℕ) (L R : List MItem) :
    (cfgBB (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) (.run 0 :: .run 1 :: R)) [target_tm]⊢*
    (cfgBB L (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
  induction m generalizing R with
  | zero => exact stepStar_refl
  | succ m ih =>
    have h_eq : (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] (m + 1) ++ R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := stepPlus_trans
      (step_BB_r1_r0_r1_comm (.run 0 :: .run 1 :: (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)) R)
      (step_BB_r0_r1 (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R))
    exact stepStar_trans (stepPlus_stepStar h1)
      (ih (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R))

lemma sweep_CB_B1 (k : ℕ) (L R : List MItem) :
    (cfgCB (.run 0 :: L) (repBlock [.run 0, .run 1] k ++ R)) [target_tm]⊢*
    (cfgCB (.run 0 :: repBlock [.run 0, .run 1] k ++ L) R) := by
  induction k generalizing L with
  | zero => exact stepStar_refl
  | succ k ih =>
    have h_eq : (.run 0 :: repBlock [.run 0, .run 1] (k + 1) ++ L) =
        (.run 0 :: repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : (cfgCB (.run 0 :: L) (.run 0 :: .run 1 :: (repBlock [.run 0, .run 1] k ++ R))) [target_tm]⊢⁺
        cfgCB (.run 0 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1] k ++ R) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: L) (repBlock [.run 0, .run 1] k ++ R)
    exact stepStar_trans (stepPlus_stepStar h1) (ih (.run 0 :: .run 1 :: L))

lemma sweep_CB_B2 (p : ℕ) (L R : List MItem) :
    (cfgCB (.run 0 :: L) (repBlock [.run 0, .run 1, .run 1] p ++ R)) [target_tm]⊢*
    (cfgCB (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ L) R) := by
  induction p generalizing L with
  | zero => exact stepStar_refl
  | succ p ih =>
    have h_eq : (.run 0 :: repBlock [.run 1, .run 0, .run 1] (p + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ (.run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : (cfgCB (.run 0 :: L) (.run 0 :: .run 1 :: .run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))) [target_tm]⊢⁺
        cfgCB (.run 0 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: L) (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))
    have h2 : (cfgCB (.run 0 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))) [target_tm]⊢⁺
        cfgCB (.run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1, .run 1] p ++ R) := by
      simpa [bumpM] using step_CB_run1 (.run 0 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1, .run 1] p ++ R)
    exact stepStar_trans (stepPlus_stepStar (stepPlus_trans h1 h2)) (ih (.run 1 :: .run 0 :: .run 1 :: L))

lemma sweep_CB_B12R (m : ℕ) (L R : List MItem) :
    (cfgCB (.run 0 :: L) (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) [target_tm]⊢*
    (cfgCB (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) R) := by
  induction m generalizing L with
  | zero => exact stepStar_refl
  | succ m ih =>
    have h_eq : (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : (cfgCB (.run 0 :: L) (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) [target_tm]⊢⁺
        cfgCB (.run 0 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: L) (.run 0 :: .run 1 :: .run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h2 : (cfgCB (.run 0 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) [target_tm]⊢⁺
        cfgCB (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h3 : (cfgCB (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) [target_tm]⊢⁺
        cfgCB (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R) := by
      simpa [bumpM] using step_CB_run1 (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)
    exact stepStar_trans (stepPlus_stepStar (stepPlus_trans h1 (stepPlus_trans h2 h3)))
      (ih (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L))

lemma encSymL_bumpSymL (L : List SymTok) : encSymL (bumpSymL L) = bumpM (encSymL L) := by
  induction L with
  | nil => rfl
  | cons x M ih =>
    cases x with
    | item it =>
      cases it with
      | zero => rfl
      | run d => simp [bumpSymL, strictNat_eq, encSymL, bumpM]
    | repB1 k =>
      rcases k with _ | _ | k
      · simpa [bumpSymL, encSymL, repBlock] using ih
      · rfl
      · simp [bumpSymL, strictNat_eq, encSymL, repBlock, bumpM]
    | rep2 p =>
      rcases p with _ | p
      · simpa [bumpSymL, encSymL, repBlock] using ih
      · simp [bumpSymL, encSymL, repBlock, bumpM]
    | rep12 m =>
      rcases m with _ | m
      · simpa [bumpSymL, encSymL, repBlock] using ih
      · simp [bumpSymL, encSymL, repBlock, bumpM]

lemma encSymR_bumpSymR (R : List SymTok) : encSymR (bumpSymR R) = bumpM (encSymR R) := by
  induction R with
  | nil => rfl
  | cons x M ih =>
    cases x with
    | item it =>
      cases it with
      | zero => rfl
      | run d => simp [bumpSymR, strictNat_eq, encSymR, bumpM]
    | repB1 k =>
      rcases k with _ | _ | k
      · simpa [bumpSymR, encSymR, repBlock] using ih
      · rfl
      · simp [bumpSymR, strictNat_eq, encSymR, repBlock, bumpM]
    | rep2 p =>
      rcases p with _ | p
      · simpa [bumpSymR, encSymR, repBlock] using ih
      · simp [bumpSymR, encSymR, repBlock, bumpM]
    | rep12 m =>
      rcases m with _ | m
      · simpa [bumpSymR, encSymR, repBlock] using ih
      · simp [bumpSymR, encSymR, repBlock, bumpM]

lemma stepElemBB_sound (L R : List SymTok) :
    (evalSym (.BB, L, R)) [target_tm]⊢* (evalSym (stepElemBB L R)) := by
  cases L with
  | nil =>
    simp only [stepElemBB, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR]
    exact stepPlus_stepStar (step_BB_nil _)
  | cons t L1 =>
    cases t with
    | item it =>
      cases it with
      | zero =>
        simp only [stepElemBB, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR]
        exact stepPlus_stepStar (step_BB_zero _ _)
      | run d =>
        rcases d with _ | _ | _ | _ | d <;>
          simp only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
        · exact stepPlus_stepStar (step_BB_run0 _ _)
        · exact stepPlus_stepStar (step_BB_run1 _ _)
        · exact stepPlus_stepStar (step_BB_run2 _ _)
        · exact stepPlus_stepStar (step_BB_run3 _ _)
        · exact stepPlus_stepStar (step_BB_run_ge4 _ _ _)
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

lemma stepElemDL_sound (L R : List SymTok) :
    (evalSym (.DL, L, R)) [target_tm]⊢* (evalSym (stepElemDL L R)) := by
  cases L with
  | nil => exact stepStar_refl
  | cons t L1 =>
    cases t with
    | item it =>
      cases it with
      | zero => exact stepStar_refl
      | run d =>
        rcases d with _ | _ | _ | d
        · simp only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR_bumpSymR]
          exact stepPlus_stepStar (step_DL_run0 _ _)
        · simp only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
          exact stepPlus_stepStar (step_DL_run1 _ _)
        · cases R with
          | nil => exact stepStar_refl
          | cons rt R1 =>
            cases rt with
            | item rit =>
              cases rit with
              | zero => exact stepStar_refl
              | run d0 =>
                simp only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymL_prependZeroSym]
                exact stepPlus_stepStar (step_DL_run2 _ _ _)
            | repB1 _ => exact stepStar_refl
            | rep2 _ => exact stepStar_refl
            | rep12 _ => exact stepStar_refl
        · exact stepStar_refl
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

lemma stepElemCB_run0_sound (L R1 : List SymTok) :
    (evalSym (.CB, L, .item (.run 0) :: R1)) [target_tm]⊢* (evalSym (stepElemCB_run0 L R1)) := by
  cases R1 with
  | nil =>
    simp only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
    exact stepPlus_stepStar (step_CB_run0_nil _)
  | cons rt R2 =>
    cases rt with
    | item rit =>
      cases rit with
      | zero =>
        simp only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
        exact stepPlus_stepStar (step_CB_run0_zero _ _)
      | run d2 =>
        rcases d2 with _ | d2 <;>
          simp only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL, encSymL_prependZeroSym]
        · exact stepPlus_stepStar (step_CB_run0_run0 _ _)
        · exact stepPlus_stepStar (step_CB_run0_run_pos _ _ _)
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

lemma stepElemCB_sound (L R : List SymTok) :
    (evalSym (.CB, L, R)) [target_tm]⊢* (evalSym (stepElemCB L R)) := by
  cases R with
  | nil =>
    simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL, encSymR]
    exact stepPlus_stepStar (step_CB_nil _)
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero =>
        simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL, encSymR, encSymR_bumpSymR]
        exact stepPlus_stepStar (step_CB_zero _ _)
      | run d =>
        rcases d with _ | _ | _ | d
        · exact stepElemCB_run0_sound L R1
        · simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run1 _ _)
        · simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymR, encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run2 _ _)
        · simp only [stepElemCB, strictList_eq, strictNat_eq, evalSym, evalM, encSymR, encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run_ge3 _ _ _)
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

lemma stepElemSym_sound (m : SymMode) (L R : List SymTok) :
    (evalSym (m, L, R)) [target_tm]⊢* (evalSym (stepElemSym m L R)) := by
  cases m with
  | BB => exact stepElemBB_sound L R
  | DL => exact stepElemDL_sound L R
  | CB => exact stepElemCB_sound L R
  | HALT => exact stepStar_refl

lemma sweepBB_sound (L R : List SymTok) :
    (evalSym (.BB, L, R)) [target_tm]⊢* (evalSym (sweepBB L R)) := by
  induction L generalizing R with
  | nil => exact stepElemBB_sound [] R
  | cons t L1 ih =>
    cases t with
    | item it =>
      cases it with
      | zero => exact stepElemBB_sound (.item .zero :: L1) R
      | run d =>
        rcases d with _ | _ | d
        · simp only [sweepBB]
          exact stepStar_trans (stepPlus_stepStar (step_BB_run0 (encSymL L1) (encSymR R))) (ih (.item (.run 0) :: R))
        · simp only [sweepBB, strictList_eq]
          have h1 : (evalSym (.BB, .item (.run 1) :: L1, R)) [target_tm]⊢*
              (evalSym (.BB, L1, .item (.run 0) :: bumpSymR R)) := by
            simp only [evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            exact stepPlus_stepStar (step_BB_run1 (encSymL L1) (encSymR R))
          exact stepStar_trans h1 (ih (.item (.run 0) :: bumpSymR R))
        · exact stepElemBB_sound (.item (.run (d + 2)) :: L1) R
    | repB1 k =>
      simp only [sweepBB, strictList_eq]
      have h1 : (evalSym (.BB, .repB1 k :: L1, R)) [target_tm]⊢*
          (evalSym (.BB, L1, eatB1 k R)) := by
        simp only [evalSym, evalM, encSymL, encSymR_eatB1]
        exact sweep_BB_B1 k (encSymL L1) (encSymR R)
      exact stepStar_trans h1 (ih (eatB1 k R))
    | rep2 p =>
      simp only [sweepBB]
      cases hstrip : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hstrip
        simp only [strictList_eq]
        have h1 : (evalSym (.BB, .rep2 p :: L1, R)) [target_tm]⊢*
            (evalSym (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB2 p R2)) := by
          rw [hR]
          simp only [evalSym, evalM, encSymL, encSymR, encSymR_eatB2, List.cons_append, List.nil_append]
          exact sweep_BB_C2 p (encSymL L1) (encSymR R2)
        exact stepStar_trans h1 (ih (.item (.run 0) :: .item (.run 1) :: eatB2 p R2))
      | none =>
        simp only [strictList_eq]
        have heq : evalSym (.BB, .rep2 p :: L1, R) = evalSym (.BB, peelTok (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelTok]
        rw [heq]
        exact stepElemBB_sound (peelTok (.rep2 p) L1) R
    | rep12 m =>
      simp only [sweepBB]
      cases hstrip : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hstrip
        simp only [strictList_eq]
        have h1 : (evalSym (.BB, .rep12 m :: L1, R)) [target_tm]⊢*
            (evalSym (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB12R m R2)) := by
          rw [hR]
          simp only [evalSym, evalM, encSymL, encSymR, encSymR_eatB12R, List.cons_append, List.nil_append]
          exact sweep_BB_C12 m (encSymL L1) (encSymR R2)
        exact stepStar_trans h1 (ih (.item (.run 0) :: .item (.run 1) :: eatB12R m R2))
      | none =>
        simp only [strictList_eq]
        have heq : evalSym (.BB, .rep12 m :: L1, R) = evalSym (.BB, peelTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelTok]
        rw [heq]
        exact stepElemBB_sound (peelTok (.rep12 m) L1) R

lemma sweepCB_sound (L R : List SymTok) :
    (evalSym (.CB, L, R)) [target_tm]⊢* (evalSym (.CB, (sweepCB L R).1, (sweepCB L R).2)) := by
  induction L, R using sweepCB.induct with
  | case1 L => exact stepStar_refl
  | case2 L R1 => exact stepStar_refl
  | case3 L R2 ih =>
    simp only [sweepCB, strictList_eq]
    have h1 : (evalSym (.CB, L, .item (.run 0) :: .item (.run 1) :: R2)) [target_tm]⊢*
        (evalSym (.CB, .item (.run 0) :: .item (.run 0) :: bumpSymL L, R2)) := by
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
      simpa using stepPlus_stepStar (step_CB_run0_run_pos 0 (encSymL L) (encSymR R2))
    exact stepStar_trans h1 (ih (bumpSymL L))
  | case4 L R1 hnot =>
    have heq : sweepCB L (.item (.run 0) :: R1) = (L, .item (.run 0) :: R1) := by
      cases R1 with
      | nil => rfl
      | cons y R2 =>
        cases y with
        | item it =>
          cases it with
          | zero => rfl
          | run d =>
            rcases d with _ | _ | d
            · rfl
            · exfalso; exact hnot R2 rfl
            · rfl
        | repB1 _ => rfl
        | rep2 _ => rfl
        | rep12 _ => rfl
    rw [heq]; exact stepStar_refl
  | case5 L R1 ih =>
    simp only [sweepCB, strictList_eq]
    have h1 : (evalSym (.CB, L, .item (.run 1) :: R1)) [target_tm]⊢*
        (evalSym (.CB, .item (.run 0) :: bumpSymL L, R1)) := by
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
      exact stepPlus_stepStar (step_CB_run1 (encSymL L) (encSymR R1))
    exact stepStar_trans h1 (ih (bumpSymL L))
  | case6 L d R1 => exact stepStar_refl
  | case7 L k R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : (evalSym (.CB, L, .repB1 k :: R1)) [target_tm]⊢*
        (evalSym (.CB, .item (.run 0) :: eatB1 k L1, R1)) := by
      rw [hL]
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatB1, List.cons_append, List.nil_append]
      exact sweep_CB_B1 k (encSymL L1) (encSymR R1)
    exact stepStar_trans h1 (ih (eatB1 k L1))
  | case8 L k R1 hstrip =>
    simp only [sweepCB, hstrip]; exact stepStar_refl
  | case9 L p R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : (evalSym (.CB, L, .rep2 p :: R1)) [target_tm]⊢*
        (evalSym (.CB, .item (.run 0) :: eatC2 p L1, R1)) := by
      rw [hL]
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC2, List.cons_append, List.nil_append]
      exact sweep_CB_B2 p (encSymL L1) (encSymR R1)
    exact stepStar_trans h1 (ih (eatC2 p L1))
  | case10 L p R1 hstrip =>
    simp only [sweepCB, hstrip]; exact stepStar_refl
  | case11 L m R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : (evalSym (.CB, L, .rep12 m :: R1)) [target_tm]⊢*
        (evalSym (.CB, .item (.run 0) :: eatC12 m L1, R1)) := by
      rw [hL]
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC12, List.cons_append, List.nil_append]
      exact sweep_CB_B12R m (encSymL L1) (encSymR R1)
    exact stepStar_trans h1 (ih (eatC12 m L1))
  | case12 L m R1 hstrip =>
    simp only [sweepCB, hstrip]; exact stepStar_refl

lemma finishThenBB_sound (s : SymMode × List SymTok × List SymTok) :
    (evalSym s) [target_tm]⊢* (evalSym (finishThenBB s)) := by
  rcases s with ⟨m, L, R⟩
  cases m <;> try exact stepStar_refl
  exact sweepBB_sound L R

lemma stepElemThenBB_sound (m : SymMode) (L R : List SymTok) :
    (evalSym (m, L, R)) [target_tm]⊢* (evalSym (stepElemThenBB m L R)) :=
  stepStar_trans (stepElemSym_sound m L R) (finishThenBB_sound (stepElemSym m L R))

def peelPureTok : SymTok → List SymTok → List SymTok
  | .repB1 0, xs => .repB1 0 :: xs
  | .repB1 (k + 1), xs => .item (.run 0) :: .item (.run 1) :: .repB1 k :: xs
  | .rep2 0, xs => .rep2 0 :: xs
  | .rep2 (p + 1), xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep2 p :: xs
  | .rep12 0, xs => .rep12 0 :: xs
  | .rep12 (m + 1), xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep12 m :: xs
  | .item x, xs => .item x :: xs

lemma encSymL_peelPureTok (t : SymTok) (xs : List SymTok) :
    encSymL (peelPureTok t xs) = encSymL (t :: xs) := by
  cases t with
  | item x => rfl
  | repB1 k => cases k <;> simp [peelPureTok, encSymL, repBlock]
  | rep2 p => cases p <;> simp [peelPureTok, encSymL, repBlock]
  | rep12 m => cases m <;> simp [peelPureTok, encSymL, repBlock]

def stepPureBB : List SymTok → List SymTok → SymMode × List SymTok × List SymTok
  | [], R => stepElemBB [] R
  | .item x :: L1, R => stepElemBB (.item x :: L1) R
  | .repB1 k :: L1, R => (.BB, L1, .repB1 k :: R)
  | .rep2 p :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => (.BB, L1, .item (.run 0) :: .item (.run 1) :: .rep2 p :: R2)
    | none => stepElemBB (peelPureTok (.rep2 p) L1) R
  | .rep12 m :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => (.BB, L1, .item (.run 0) :: .item (.run 1) :: .rep12 m :: R2)
    | none => stepElemBB (peelPureTok (.rep12 m) L1) R

def stepPureDL : List SymTok → List SymTok → SymMode × List SymTok × List SymTok
  | [], R => (.DL, [], R)
  | t :: L1, R => stepElemDL (peelPureTok t L1) R

def stepPureCB (L : List SymTok) : List SymTok → SymMode × List SymTok × List SymTok
  | [] => stepElemCB L []
  | .item .zero :: R1 => stepElemCB L (.item .zero :: R1)
  | .item (.run 0) :: R1 => stepElemCB_run0 L R1
  | .item (.run 1) :: R1 => stepElemCB L (.item (.run 1) :: R1)
  | .item (.run 2) :: R1 => stepElemCB L (.item (.run 2) :: R1)
  | .item (.run (d + 3)) :: R1 => (.BB, bumpSymL L, .item (.run 0) :: .item (.run d) :: R1)
  | .repB1 k :: R1 =>
    match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
    | some L2 => (.CB, .item (.run 0) :: .repB1 (k + 1) :: L2, R1)
    | none =>
      match stripPrefixSym [.item (.run 0)] L with
      | some L1 => (.CB, .item (.run 0) :: .repB1 k :: L1, R1)
      | none => (.CB, L, .repB1 k :: R1)
  | .rep2 p :: R1 =>
    match stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
    | some L2 => (.CB, .item (.run 0) :: .rep2 (p + 1) :: L2, R1)
    | none =>
      match stripPrefixSym [.item (.run 0)] L with
      | some L1 => (.CB, .item (.run 0) :: .rep2 p :: L1, R1)
      | none => (.CB, L, .rep2 p :: R1)
  | .rep12 m :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => (.CB, .item (.run 0) :: .rep12 m :: L1, R1)
    | none => (.CB, L, .rep12 m :: R1)

def stepPure : SymMode × List SymTok × List SymTok → SymMode × List SymTok × List SymTok
  | (.BB, L, R) => stepPureBB L R
  | (.DL, L, R) => stepPureDL L R
  | (.CB, L, R) => stepPureCB L R
  | (.HALT, L, R) => (.HALT, L, R)

lemma stepPureBB_sound (L R : List SymTok) :
    (evalSym (.BB, L, R)) [target_tm]⊢* (evalSym (stepPureBB L R)) := by
  cases L with
  | nil => exact stepElemBB_sound [] R
  | cons t L1 =>
    cases t with
    | item x => exact stepElemBB_sound (.item x :: L1) R
    | repB1 k => exact sweep_BB_B1 k (encSymL L1) (encSymR R)
    | rep2 p =>
      simp only [stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
        exact sweep_BB_C2 p (encSymL L1) (encSymR R2)
      | none =>
        have heq : evalSym (.BB, .rep2 p :: L1, R) = evalSym (.BB, peelPureTok (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact stepElemBB_sound (peelPureTok (.rep2 p) L1) R
    | rep12 m =>
      simp only [stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
        exact sweep_BB_C12 m (encSymL L1) (encSymR R2)
      | none =>
        have heq : evalSym (.BB, .rep12 m :: L1, R) = evalSym (.BB, peelPureTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact stepElemBB_sound (peelPureTok (.rep12 m) L1) R

lemma stepPureDL_sound (L R : List SymTok) :
    (evalSym (.DL, L, R)) [target_tm]⊢* (evalSym (stepPureDL L R)) := by
  cases L with
  | nil => exact stepStar_refl
  | cons t L1 =>
    have heq : evalSym (.DL, t :: L1, R) = evalSym (.DL, peelPureTok t L1, R) := by
      simp only [evalSym, encSymL_peelPureTok]
    rw [heq]
    exact stepElemDL_sound (peelPureTok t L1) R

lemma stepPureCB_sound (L R : List SymTok) :
    (evalSym (.CB, L, R)) [target_tm]⊢* (evalSym (stepPureCB L R)) := by
  cases R with
  | nil => exact stepElemCB_sound L []
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero => exact stepElemCB_sound L (.item .zero :: R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · exact stepElemCB_run0_sound L R1
        · exact stepElemCB_sound L (.item (.run 1) :: R1)
        · exact stepElemCB_sound L (.item (.run 2) :: R1)
        · simp only [stepPureCB, evalSym, evalM, encSymR, encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run_ge3 d (encSymL L) (encSymR R1))
    | repB1 k =>
      simp only [stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
        exact sweep_CB_B1 k (.run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
          exact sweep_CB_B1 k (encSymL L1) (encSymR R1)
        | none => exact stepStar_refl
    | rep2 p =>
      simp only [stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
        exact sweep_CB_B2 p (.run 1 :: .run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
          exact sweep_CB_B2 p (encSymL L1) (encSymR R1)
        | none => exact stepStar_refl
    | rep12 m =>
      simp only [stepPureCB]
      cases hs1 : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL := stripPrefixSym_some _ L L1 hs1
        rw [hL]
        simp only [evalSym, evalM, encSymL, encSymR, List.cons_append, List.nil_append]
        exact sweep_CB_B12R m (encSymL L1) (encSymR R1)
      | none => exact stepStar_refl

lemma stepPure_sound (s : SymMode × List SymTok × List SymTok) :
    (evalSym s) [target_tm]⊢* (evalSym (stepPure s)) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | BB => exact stepPureBB_sound L R
  | DL => exact stepPureDL_sound L R
  | CB => exact stepPureCB_sound L R
  | HALT => exact stepStar_refl

lemma repBlock12_snoc (m : ℕ) (xs : List MItem) :
    repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++
      (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: xs) =
    repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ xs := by
  rw [repBlock_succ_right, List.append_assoc]; rfl

lemma popRepB1_some (xs : List SymTok) (k : ℕ) (rest : List SymTok)
    (h : popRepB1 xs = some (k, rest)) :
    xs = .repB1 k :: rest := by
  rcases xs with _ | ⟨t, tl⟩
  · simp [popRepB1] at h
  · cases t <;> simp [popRepB1] at h
    rcases h with ⟨rfl, rfl⟩; rfl

lemma matchEndB1_some (xs : List SymTok) (k : ℕ) (h : matchEndB1 xs = some k) :
    xs = [.repB1 k, .item (.run 0)] := by
  unfold matchEndB1 at h
  cases hp : popRepB1 xs with
  | none => rw [hp] at h; contradiction
  | some kr =>
    rcases kr with ⟨k', rest⟩
    rw [hp] at h; dsimp only at h
    cases hs : stripPrefixSym [.item (.run 0)] rest with
    | none => rw [hs] at h; contradiction
    | some rest2 =>
      rw [hs] at h; dsimp only at h
      cases rest2 with
      | nil =>
        simp only [Option.some.injEq] at h; subst h
        have h1 := popRepB1_some xs k' rest hp
        have h2 := stripPrefixSym_some _ rest [] hs
        rw [h1, h2]; rfl
      | cons _ _ => contradiction

lemma popRep2_some (xs : List SymTok) (p : ℕ) (rest : List SymTok) (h : popRep2 xs = some (p, rest)) :
    xs = .rep2 p :: rest := by
  rcases xs with _ | ⟨t, rest0⟩ <;> try contradiction
  cases t <;> simp [popRep2] at h
  rcases h with ⟨rfl, rfl⟩; rfl

lemma popRep12_some (xs : List SymTok) (m : ℕ) (rest : List SymTok) (h : popRep12 xs = some (m, rest)) :
    xs = .rep12 m :: rest := by
  rcases xs with _ | ⟨t, rest0⟩ <;> try contradiction
  cases t <;> simp [popRep12] at h
  rcases h with ⟨rfl, rfl⟩; rfl

lemma popSep3_some (xs sep rest : List SymTok) (h : popSep3 xs = some (sep, rest)) :
    xs = sep ++ rest ∧ (sep = sep3A ∨ sep = sep3B) := by
  unfold popSep3 at h
  cases hsA : stripPrefixSym sep3A xs with
  | some rA =>
    rw [hsA] at h; simp at h; rcases h with ⟨rfl, rfl⟩
    exact ⟨stripPrefixSym_some _ _ _ hsA, Or.inl rfl⟩
  | none =>
    rw [hsA] at h
    cases hsB : stripPrefixSym sep3B xs with
    | some rB =>
      rw [hsB] at h; simp at h; rcases h with ⟨rfl, rfl⟩
      exact ⟨stripPrefixSym_some _ _ _ hsB, Or.inr rfl⟩
    | none => rw [hsB] at h; contradiction

def stateA0 (k d : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List SymTok :=
  (.CB,
   [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
    .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero,
    .item (.run 1), .repB1 k, .item (.run 0)],
   .item (.run d) :: R_tail)

def stateA (m k d : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List SymTok :=
  (.CB,
   [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
    .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
    .rep12 m, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
    .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
   .item (.run d) :: R_tail)

lemma ruleA0_sound (k d : ℕ) (R_tail : List SymTok) :
    (evalSym (stateA0 (k + 1) (d + 6) R_tail)) [target_tm]⊢*
    (evalSym (stateA 0 k d R_tail)) :=
  iterStep_sound stepPure evalSym stepPure_sound 46 (stateA0 (k + 1) (d + 6) R_tail)

lemma ruleA_step_eq (m k d : ℕ) (R_tail : List SymTok) :
    evalSym (iterStep stepPure 66 (stateA m (k + 1) (d + 6) R_tail)) =
    evalSym (stateA (m + 1) k d R_tail) := by
  have h : iterStep stepPure 66 (stateA m (k + 1) (d + 6) R_tail) =
    (.CB,
     [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
      .rep12 m, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
     .item (.run d) :: R_tail) := rfl
  rw [h]
  simp only [stateA, evalSym, encSymL, repBlock12_snoc]

lemma ruleA_step_sound (m k d : ℕ) (R_tail : List SymTok) :
    (evalSym (stateA m (k + 1) (d + 6) R_tail)) [target_tm]⊢*
    (evalSym (stateA (m + 1) k d R_tail)) :=
  ruleA_step_eq m k d R_tail ▸
    iterStep_sound stepPure evalSym stepPure_sound 66 (stateA m (k + 1) (d + 6) R_tail)

lemma ruleA_iter (n m k d : ℕ) (R_tail : List SymTok) :
    (evalSym (stateA m (k + n) (d + 6 * n) R_tail)) [target_tm]⊢*
    (evalSym (stateA (m + n) k d R_tail)) := by
  induction n generalizing m k d with
  | zero => simp; exact stepStar_refl
  | succ n ih =>
    have h1 : k + (n + 1) = (k + n) + 1 := by omega
    have h2 : d + 6 * (n + 1) = (d + 6 * n) + 6 := by omega
    have h3 : m + (n + 1) = (m + 1) + n := by omega
    rw [h1, h2, h3]
    exact stepStar_trans (ruleA_step_sound m (k + n) (d + 6 * n) R_tail) (ih (m + 1) k d)

lemma tryRuleA_sound (L : List SymTok) (d : ℕ) (R_tail : List SymTok) :
    (evalSym (.CB, L, .item (.run d) :: R_tail)) [target_tm]⊢* (evalSym (tryRuleA L d R_tail)) := by
  unfold tryRuleA
  cases hs : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
     .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)] L with
  | none => dsimp only; exact stepElemThenBB_sound .CB L (.item (.run d) :: R_tail)
  | some rest =>
    dsimp only
    cases hm : matchEndB1 rest with
    | none => dsimp only; exact stepElemThenBB_sound .CB L (.item (.run d) :: R_tail)
    | some k =>
      simp only [strictNat_eq]
      cases hcond : (Nat.ble 2 (d / 6) && Nat.ble (d / 6) k)
      · exact stepElemThenBB_sound .CB L (.item (.run d) :: R_tail)
      · have hrest := matchEndB1_some rest k hm
        have hL := stripPrefixSym_some _ L rest hs
        rw [hrest] at hL
        have hble : 2 ≤ d / 6 ∧ d / 6 ≤ k := by
          simpa [Bool.and_eq_true, Nat.ble_eq] using hcond
        set n1 := d / 6
        set m_new := n1 - 1
        set k_new := k - n1
        set d_new := d - 6 * n1
        have hk_eq : k = (k_new + m_new) + 1 := by omega
        have hd_eq : d = (d_new + 6 * m_new) + 6 := by omega
        have hlhs : (.CB, L, .item (.run d) :: R_tail) =
            stateA0 ((k_new + m_new) + 1) ((d_new + 6 * m_new) + 6) R_tail := by
          rw [hL, hk_eq, hd_eq]; rfl
        rw [hlhs]
        exact stepStar_trans (ruleA0_sound (k_new + m_new) (d_new + 6 * m_new) R_tail)
          (by simpa [stateA] using ruleA_iter m_new 0 k_new d_new R_tail)

def stateC (p k d2 : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List SymTok :=
  (.CB,
   [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 p,
    .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1),
    .repB1 k, .item (.run 0)],
   .item .zero :: .item (.run d2) :: R_tail)

lemma ruleC_step_eq (p k d2 : ℕ) (R_tail : List SymTok) :
    evalSym (iterStep stepPure 46 (stateC (p + 3) (k + 1) d2 R_tail)) =
    evalSym (stateC (p + 2) (k + 3) (d2 + 2) R_tail) := by
  have h : iterStep stepPure 46 (stateC (p + 3) (k + 1) d2 R_tail) =
    (.CB,
     [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 2),
      .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
      .repB1 (k + 1), .item (.run 0)],
     .item .zero :: .item (.run (d2 + 2)) :: R_tail) := rfl
  rw [h]
  simp only [stateC, evalSym, encSymL, repBlock, List.cons_append, List.nil_append]

lemma ruleC_step_sound (p k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateC (p + 3) (k + 1) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateC (p + 2) (k + 3) (d2 + 2) R_tail)) :=
  ruleC_step_eq p k d2 R_tail ▸
    iterStep_sound stepPure evalSym stepPure_sound 46 (stateC (p + 3) (k + 1) d2 R_tail)

lemma ruleC_iter (n p k d2 : ℕ) (R_tail : List SymTok) (hk : 1 ≤ k) :
    (evalSym (stateC (p + n + 2) k d2 R_tail)) [target_tm]⊢*
    (evalSym (stateC (p + 2) (k + 2 * n) (d2 + 2 * n) R_tail)) := by
  induction n generalizing p k d2 with
  | zero => simp; exact stepStar_refl
  | succ n ih =>
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    have h1 : p + (n + 1) + 2 = (p + n) + 3 := by omega
    have h2 : k0 + 1 + 2 * (n + 1) = (k0 + 3) + 2 * n := by omega
    have h3 : d2 + 2 * (n + 1) = (d2 + 2) + 2 * n := by omega
    rw [h1, h2, h3]
    exact stepStar_trans (ruleC_step_sound (p + n) k0 d2 R_tail)
      (ih p (k0 + 3) (d2 + 2) (by omega))

def stateB (s_sep m_sep : List SymTok) (p m k d2 : ℕ) (R_tail : List SymTok) :
    SymMode × List SymTok × List SymTok :=
  (.CB,
   [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 p, .item (.run 1)] ++
     s_sep ++ [.rep12 m, .item (.run 1), .item (.run 0), .item (.run 1)] ++
     m_sep ++ [.repB1 k, .item (.run 0)],
   .item .zero :: .item (.run d2) :: R_tail)

lemma ruleB_step_AA (p m k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure evalSym stepPure_sound 126
    (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 126 (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : evalSym (iterStep stepPure 126 (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      evalSym (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, evalSym, encSymL, List.cons_append, List.nil_append, repBlock12_snoc]
  exact heq ▸ h

lemma ruleB_step_AB (p m k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure evalSym stepPure_sound 118
    (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 118 (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : evalSym (iterStep stepPure 118 (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      evalSym (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append, repBlock12_snoc]
  exact heq ▸ h

lemma ruleB_step_BA (p m k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure evalSym stepPure_sound 106
    (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 106 (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : evalSym (iterStep stepPure 106 (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      evalSym (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append, repBlock12_snoc]
  exact heq ▸ h

lemma ruleB_step_BB (p m k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure evalSym stepPure_sound 98
    (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 98 (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : evalSym (iterStep stepPure 98 (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) =
      evalSym (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3B, evalSym, encSymL, List.cons_append, List.nil_append, repBlock12_snoc]
  exact heq ▸ h

lemma ruleB_step_sound (s_sep m_sep : List SymTok) (hs : s_sep = sep3A ∨ s_sep = sep3B)
    (hm : m_sep = sep3A ∨ m_sep = sep3B) (p m k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateB s_sep m_sep (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateB s_sep m_sep (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  rcases hs with rfl | rfl <;> rcases hm with rfl | rfl
  · exact ruleB_step_AA p m k d2 R_tail
  · exact ruleB_step_AB p m k d2 R_tail
  · exact ruleB_step_BA p m k d2 R_tail
  · exact ruleB_step_BB p m k d2 R_tail

lemma ruleB_iter (s_sep m_sep : List SymTok) (hs : s_sep = sep3A ∨ s_sep = sep3B)
    (hm : m_sep = sep3A ∨ m_sep = sep3B) (n p m k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (stateB s_sep m_sep (p + 1) (m + n + 1) (k + n) d2 R_tail)) [target_tm]⊢*
    (evalSym (stateB s_sep m_sep (p + 1 + 2 * n) (m + 1) k (d2 + 4 * n) R_tail)) := by
  induction n generalizing p m k d2 with
  | zero => simp; exact stepStar_refl
  | succ n ih =>
    have h1 : m + (n + 1) + 1 = (m + n) + 2 := by omega
    have h2 : k + (n + 1) = (k + n) + 1 := by omega
    have h3 : p + 1 + 2 * (n + 1) = (p + 2) + 1 + 2 * n := by omega
    have h4 : d2 + 4 * (n + 1) = (d2 + 4) + 4 * n := by omega
    rw [h1, h2, h3, h4]
    exact stepStar_trans (ruleB_step_sound s_sep m_sep hs hm p (m + n) (k + n) d2 R_tail)
      (ih (p + 2) m k (d2 + 4))

lemma splitB2Aux_spec (fuel p : ℕ) (xs : List SymTok) :
    repBlock [.run 0, .run 1, .run 1] p ++ encSymL xs =
    repBlock [.run 0, .run 1, .run 1] (splitB2Aux fuel p xs).1 ++ encSymL (splitB2Aux fuel p xs).2 := by
  induction fuel generalizing p xs with
  | zero => rfl
  | succ fuel ih =>
    simp only [splitB2Aux]
    cases hs : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1)] xs with
    | none => rfl
    | some rest =>
      have hxs := stripPrefixSym_some _ xs rest hs
      simp only [strictNat_eq, ← ih (p + 1) rest, repBlock_succ_right, List.append_assoc, hxs]
      rfl

lemma repBlock_B2_shift (q : ℕ) (tail : List MItem) :
    .run 0 :: (repBlock [.run 0, .run 1, .run 1] (q + 1) ++ tail) =
    [.run 0, .run 0, .run 1] ++ (repBlock [.run 1, .run 0, .run 1] q ++ (.run 1 :: tail)) := by
  induction q generalizing tail with
  | zero => rfl
  | succ q ih =>
    have h1 : repBlock [.run 0, .run 1, .run 1] (q + 1 + 1) ++ tail =
        repBlock [.run 0, .run 1, .run 1] (q + 1) ++ (.run 0 :: .run 1 :: .run 1 :: tail) := by
      rw [repBlock_succ_right, List.append_assoc]; rfl
    rw [h1, ih (.run 0 :: .run 1 :: .run 1 :: tail)]
    simp [repBlock_succ_right [.run 1, .run 0, .run 1] q, List.append_assoc]

lemma tryRuleB_sound (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (.CB, L, .item .zero :: .item (.run d2) :: R_tail)) [target_tm]⊢*
    (evalSym (tryRuleB L d2 R_tail)) := by
  unfold tryRuleB
  cases hsL : stripPrefixSym [.item (.run 0)] L with
  | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
  | some restL =>
    dsimp only [afterSplitB2]
    cases hsep1 : popSep3 (splitB2 0 restL).2 with
    | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
    | some sr1 =>
      rcases sr1 with ⟨s_sep, rest0⟩
      dsimp only
      cases h12 : popRep12 rest0 with
      | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
      | some mr1 =>
        rcases mr1 with ⟨m12, rest1⟩
        dsimp only
        cases hs1 : stripPrefixSym [.item (.run 1), .item (.run 0), .item (.run 1)] rest1 with
        | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
        | some rest2 =>
          dsimp only
          cases hsep2 : popSep3 rest2 with
          | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
          | some mr2 =>
            rcases mr2 with ⟨m_sep, rest3⟩
            dsimp only
            cases hend : matchEndB1 rest3 with
            | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
            | some k1 =>
              dsimp only
              cases hcond : (Nat.ble 2 (splitB2 0 restL).1 && Nat.ble 2 m12 && Nat.ble m12 k1)
              · exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
              · simp only [strictNat_eq]
                have hL := stripPrefixSym_some _ L restL hsL
                have hspec := splitB2Aux_spec 32 0 restL
                simp only [repBlock, List.nil_append] at hspec
                change encSymL restL = repBlock [.run 0, .run 1, .run 1] (splitB2 0 restL).1 ++ encSymL (splitB2 0 restL).2 at hspec
                obtain ⟨h_s, hs_or⟩ := popSep3_some (splitB2 0 restL).2 s_sep rest0 hsep1
                have h_m12 := popRep12_some rest0 m12 rest1 h12
                have h_r1 := stripPrefixSym_some _ rest1 rest2 hs1
                obtain ⟨h_m, hm_or⟩ := popSep3_some rest2 m_sep rest3 hsep2
                have h_k1 := matchEndB1_some rest3 k1 hend
                simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
                rcases hcond with ⟨⟨hp, hm12⟩, hk1⟩
                set p := (splitB2 0 restL).1
                set n3 := m12 - 1
                set p0 := p - 2
                set k_new := k1 - n3
                have hp_eq : p = (p0 + 1) + 1 := by omega
                have hm_eq : m12 = 0 + n3 + 1 := by omega
                have hk_eq : k1 = k_new + n3 := by omega
                have hp_new : (splitB2 0 restL).1 + 2 * (m12 - 1) - 1 = p0 + 1 + 2 * n3 := by omega
                have hk_new : k1 - (m12 - 1) = k_new := rfl
                have hd_new : d2 + 4 * (m12 - 1) = d2 + 4 * n3 := rfl
                have hlhs : evalSym (.CB, L, .item .zero :: .item (.run d2) :: R_tail) =
                    evalSym (stateB s_sep m_sep (p0 + 1) (0 + n3 + 1) (k_new + n3) d2 R_tail) := by
                  simp only [evalSym, stateB, hL, encSymL, hspec, h_s, h_m12, h_r1, h_m, h_k1,
                    hp_eq, hm_eq, hk_eq, repBlock_B2_shift (p0 + 1), List.cons_append, List.nil_append, List.append_assoc]
                rw [hlhs, hp_new]
                exact ruleB_iter s_sep m_sep hs_or hm_or n3 p0 0 k_new d2 R_tail

lemma tryRuleBC_sound (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) :
    (evalSym (.CB, L, .item .zero :: .item (.run d2) :: R_tail)) [target_tm]⊢*
    (evalSym (tryRuleBC L d2 R_tail)) := by
  unfold tryRuleBC
  cases hs1 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
  | none => dsimp only; exact tryRuleB_sound L d2 R_tail
  | some rest1 =>
    dsimp only
    cases hp2 : popRep2 rest1 with
    | none => dsimp only; exact tryRuleB_sound L d2 R_tail
    | some pr =>
      rcases pr with ⟨p, restC⟩
      dsimp only
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1)] restC with
      | none => dsimp only; exact tryRuleB_sound L d2 R_tail
      | some rest2 =>
        dsimp only
        cases hend : matchEndB1 rest2 with
        | none => dsimp only; exact tryRuleB_sound L d2 R_tail
        | some k1 =>
          dsimp only
          cases hcond : (Nat.ble 3 p && Nat.ble 1 k1)
          · exact tryRuleB_sound L d2 R_tail
          · simp only [strictNat_eq]
            have hL1 := stripPrefixSym_some _ L rest1 hs1
            have hL2 := popRep2_some rest1 p restC hp2
            have hL3 := stripPrefixSym_some _ restC rest2 hs2
            have hL4 := matchEndB1_some rest2 k1 hend
            simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
            rcases hcond with ⟨hp, hk1⟩
            set n4 := p - 2
            have hp_eq : p = 0 + n4 + 2 := by omega
            have hlhs : (.CB, L, .item .zero :: .item (.run d2) :: R_tail) =
                stateC (0 + n4 + 2) k1 d2 R_tail := by
              rw [hL1, hL2, hL3, hL4, hp_eq]; rfl
            rw [hlhs]
            exact ruleC_iter n4 0 k1 d2 R_tail hk1

lemma afterSweepCB_sound (p : List SymTok × List SymTok) :
    (evalSym (.CB, p.1, p.2)) [target_tm]⊢* (evalSym (afterSweepCB p)) := by
  rcases p with ⟨L, R⟩
  rcases R with _ | ⟨t1, R1⟩
  · exact stepElemThenBB_sound .CB L []
  · cases t1 with
    | item it1 =>
      cases it1 with
      | zero =>
        rcases R1 with _ | ⟨t2, R_tail⟩
        · exact stepElemThenBB_sound .CB L [.item .zero]
        · cases t2 with
          | item it2 =>
            cases it2 with
            | zero => exact stepElemThenBB_sound .CB L (.item .zero :: .item .zero :: R_tail)
            | run d2 => exact tryRuleBC_sound L d2 R_tail
          | repB1 k => exact stepElemThenBB_sound .CB L (.item .zero :: .repB1 k :: R_tail)
          | rep2 p => exact stepElemThenBB_sound .CB L (.item .zero :: .rep2 p :: R_tail)
          | rep12 m => exact stepElemThenBB_sound .CB L (.item .zero :: .rep12 m :: R_tail)
      | run d =>
        rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
        · exact stepElemThenBB_sound .CB L (.item (.run 0) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 1) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 2) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 3) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 4) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 5) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 6) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 7) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 8) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 9) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 10) :: R1)
        · exact stepElemThenBB_sound .CB L (.item (.run 11) :: R1)
        · exact tryRuleA_sound L (d + 12) R1
    | repB1 k => exact stepElemThenBB_sound .CB L (.repB1 k :: R1)
    | rep2 p => exact stepElemThenBB_sound .CB L (.rep2 p :: R1)
    | rep12 m => exact stepElemThenBB_sound .CB L (.rep12 m :: R1)

lemma stepSym_sound (s : SymMode × List SymTok × List SymTok) :
    (evalSym s) [target_tm]⊢* (evalSym (stepSym s)) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | BB => exact sweepBB_sound L R
  | DL =>
    simp only [stepSym, strictList_eq]
    have heq : evalSym (.DL, L, R) = evalSym (.DL, peelL L, R) := by
      simp only [evalSym, encSymL_peelL]
    rw [heq]
    exact stepElemThenBB_sound .DL (peelL L) R
  | HALT => exact stepStar_refl
  | CB =>
    exact stepStar_trans (sweepCB_sound L R) (afterSweepCB_sound (sweepCB L R))

lemma stepSym16_sound (s : SymMode × List SymTok × List SymTok) :
    (evalSym s) [target_tm]⊢* (evalSym (stepSym16 s)) :=
  iterStep_sound stepSym evalSym stepSym_sound 16 s

lemma stepSym256_sound (s : SymMode × List SymTok × List SymTok) :
    (evalSym s) [target_tm]⊢* (evalSym (stepSym256 s)) :=
  iterStep_sound stepSym16 evalSym stepSym16_sound 16 s

lemma stepSym4096_sound (s : SymMode × List SymTok × List SymTok) :
    (evalSym s) [target_tm]⊢* (evalSym (stepSym4096 s)) :=
  iterStep_sound stepSym256 evalSym stepSym256_sound 16 s

lemma stepElem16_sound (s : SymMode × List MItem × List MItem) :
    (evalM s) [target_tm]⊢* (evalM (stepElem16 s)) :=
  iterStep_sound stepElemM evalM stepElemM_sound 16 s

lemma stepElem256_sound (s : SymMode × List MItem × List MItem) :
    (evalM s) [target_tm]⊢* (evalM (stepElem256 s)) :=
  iterStep_sound stepElem16 evalM stepElem16_sound 16 s

lemma stepElem4096_sound (s : SymMode × List MItem × List MItem) :
    (evalM s) [target_tm]⊢* (evalM (stepElem4096 s)) :=
  iterStep_sound stepElem256 evalM stepElem256_sound 16 s

lemma runElemFast_sound (s : SymMode × List MItem × List MItem) :
    (evalM s) [target_tm]⊢* (evalM (runElemFast s)) := by
  unfold runElemFast
  exact stepStar_trans (iterStep_sound stepElem4096 evalM stepElem4096_sound 4 s)
    (stepStar_trans (iterStep_sound stepElem256 evalM stepElem256_sound 11 _)
      (stepStar_trans (iterStep_sound stepElem16 evalM stepElem16_sound 1 _)
        (iterStep_sound stepElemM evalM stepElemM_sound 1 _)))

lemma test_elem_rfl :
    runElemFast (.CB, [], [.run 1, .run 0]) = (initSymCyc3.1, encSymL initSymCyc3.2.1, encSymR initSymCyc3.2.2) := by decide +kernel

lemma sym_chk1 : stepSym4096 initSymCyc3 = symChk4096 := by decide +kernel
lemma sym_chk2 : stepSym4096 symChk4096 = symChk8192 := by decide +kernel
lemma sym_chk3 : stepSym4096 symChk8192 = symChk12288 := by decide +kernel
lemma sym_chk4 : stepSym4096 symChk12288 = symChk16384 := by decide +kernel
lemma sym_chk5 : stepSym4096 symChk16384 = symChk20480 := by decide +kernel
lemma sym_chk6 : stepSym4096 symChk20480 = symChk24576 := by decide +kernel
lemma sym_chk7 : stepSym4096 symChk24576 = symChk28672 := by decide +kernel
lemma sym_chk8 : stepSym4096 symChk28672 = symChk32768 := by decide +kernel
lemma sym_chk9 : stepSym4096 symChk32768 = symChk36864 := by decide +kernel
lemma sym_chk10 : stepSym4096 symChk36864 = symChk40960 := by decide +kernel
lemma sym_chk11 : stepSym4096 symChk40960 = symChk45056 := by decide +kernel
lemma sym_chk12 : stepSym4096 symChk45056 = symChk49152 := by decide +kernel
lemma sym_chk13 : stepSym4096 symChk49152 = symChk53248 := by decide +kernel
lemma sym_chk14 : stepSym4096 symChk53248 = symChk57344 := by decide +kernel
lemma sym_chk15 : stepSym4096 symChk57344 = symChk61440 := by decide +kernel
lemma sym_chk16 : stepSym4096 symChk61440 = symChk65536 := by decide +kernel
lemma sym_chk17 : stepSym4096 symChk65536 = symChk69632 := by decide +kernel
lemma sym_chk18 : iterStep stepSym 15 (iterStep stepSym16 6 (iterStep stepSym256 3 symChk69632)) = symChk70511 := by decide +kernel

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  have h0 : (init []) [target_tm]⊢* (evalM (.CB, [], [.run 1, .run 0])) :=
    stepPlus_stepStar init_to_CB
  have h1 : (evalM (.CB, [], [.run 1, .run 0])) [target_tm]⊢* (evalSym initSymCyc3) := by
    have h := runElemFast_sound (.CB, [], [.run 1, .run 0])
    rw [test_elem_rfl] at h
    exact h
  have hc1 : (evalSym initSymCyc3) [target_tm]⊢* (evalSym symChk4096) := by rw [← sym_chk1]; exact stepSym4096_sound initSymCyc3
  have hc2 : (evalSym symChk4096) [target_tm]⊢* (evalSym symChk8192) := by rw [← sym_chk2]; exact stepSym4096_sound symChk4096
  have hc3 : (evalSym symChk8192) [target_tm]⊢* (evalSym symChk12288) := by rw [← sym_chk3]; exact stepSym4096_sound symChk8192
  have hc4 : (evalSym symChk12288) [target_tm]⊢* (evalSym symChk16384) := by rw [← sym_chk4]; exact stepSym4096_sound symChk12288
  have hc5 : (evalSym symChk16384) [target_tm]⊢* (evalSym symChk20480) := by rw [← sym_chk5]; exact stepSym4096_sound symChk16384
  have hc6 : (evalSym symChk20480) [target_tm]⊢* (evalSym symChk24576) := by rw [← sym_chk6]; exact stepSym4096_sound symChk20480
  have hc7 : (evalSym symChk24576) [target_tm]⊢* (evalSym symChk28672) := by rw [← sym_chk7]; exact stepSym4096_sound symChk24576
  have hc8 : (evalSym symChk28672) [target_tm]⊢* (evalSym symChk32768) := by rw [← sym_chk8]; exact stepSym4096_sound symChk28672
  have hc9 : (evalSym symChk32768) [target_tm]⊢* (evalSym symChk36864) := by rw [← sym_chk9]; exact stepSym4096_sound symChk32768
  have hc10 : (evalSym symChk36864) [target_tm]⊢* (evalSym symChk40960) := by rw [← sym_chk10]; exact stepSym4096_sound symChk36864
  have hc11 : (evalSym symChk40960) [target_tm]⊢* (evalSym symChk45056) := by rw [← sym_chk11]; exact stepSym4096_sound symChk40960
  have hc12 : (evalSym symChk45056) [target_tm]⊢* (evalSym symChk49152) := by rw [← sym_chk12]; exact stepSym4096_sound symChk45056
  have hc13 : (evalSym symChk49152) [target_tm]⊢* (evalSym symChk53248) := by rw [← sym_chk13]; exact stepSym4096_sound symChk49152
  have hc14 : (evalSym symChk53248) [target_tm]⊢* (evalSym symChk57344) := by rw [← sym_chk14]; exact stepSym4096_sound symChk53248
  have hc15 : (evalSym symChk57344) [target_tm]⊢* (evalSym symChk61440) := by rw [← sym_chk15]; exact stepSym4096_sound symChk57344
  have hc16 : (evalSym symChk61440) [target_tm]⊢* (evalSym symChk65536) := by rw [← sym_chk16]; exact stepSym4096_sound symChk61440
  have hc17 : (evalSym symChk65536) [target_tm]⊢* (evalSym symChk69632) := by rw [← sym_chk17]; exact stepSym4096_sound symChk65536
  have hc18 : (evalSym symChk69632) [target_tm]⊢* (evalSym symChk70511) := by
    rw [← sym_chk18]
    exact stepStar_trans (iterStep_sound stepSym256 evalSym stepSym256_sound 3 symChk69632)
      (stepStar_trans (iterStep_sound stepSym16 evalSym stepSym16_sound 6 _)
        (iterStep_sound stepSym evalSym stepSym_sound 15 _))
  have h_to_halt_sym : (init []) [target_tm]⊢* (evalSym symChk70511) :=
    stepStar_trans h0 (stepStar_trans h1 (stepStar_trans hc1 (stepStar_trans hc2
      (stepStar_trans hc3 (stepStar_trans hc4 (stepStar_trans hc5 (stepStar_trans hc6
      (stepStar_trans hc7 (stepStar_trans hc8 (stepStar_trans hc9 (stepStar_trans hc10
      (stepStar_trans hc11 (stepStar_trans hc12 (stepStar_trans hc13 (stepStar_trans hc14
      (stepStar_trans hc15 (stepStar_trans hc16 (stepStar_trans hc17 hc18))))))))))))))))))
  have h_final := step_DL_zero_halt
    (encSymL symChk70511.2.1.tail)
    (encSymR symChk70511.2.2.tail)
  exact ⟨_, stepStar_trans h_to_halt_sym (stepPlus_stepStar h_final), rfl⟩

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
