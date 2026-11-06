/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter

/-!
# Shared Halting Proof Infrastructure (`BusyBeaver.Calculi.HaltShared`)

Common lemmas, bounded-reachability lemmas, and step-reduction tactics
shared across multiple Busy Beaver halting machine proofs.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

/-- `true` iff `M` reaches, after exactly `n` steps, a configuration without a successor. -/
def BusyBeaver.haltsAt (M : Machine (Fin 2) (Fin 6)) (n : ℕ) : Bool :=
  match multiStep M (init []) n with
  | some cfg => (step M cfg).isNone
  | none => false

theorem BusyBeaver.is_halt_of_haltsAt (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (h : BusyBeaver.haltsAt M n = true) : IsHalt M := by
  unfold BusyBeaver.haltsAt at h
  cases hm : multiStep M (init []) n with
  | none =>
    rw [hm] at h
    exact absurd h Bool.false_ne_true
  | some cfg =>
    rw [hm] at h
    exact ⟨cfg, ⟨n, hm⟩, h⟩

namespace BusyBeaver.RleStackEngine

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[simp] theorem multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl

@[simp] theorem pow_zero_list (u : List (Fin 2)) : u ^ (0 : Nat) = [] := rfl
@[simp] theorem pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
@[simp] theorem nil_append_list (l : List (Fin 2)) : ([] : List (Fin 2)) ++ l = l := rfl
@[simp] theorem cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] theorem append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] theorem listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] theorem listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] theorem zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] theorem default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

@[simp]
theorem listblank_append_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (s <+ (([1] : List (Fin 2)) ^ n)) <+ (([1] : List (Fin 2)) ^ m) =
    s <+ (([1] : List (Fin 2)) ^ (n + m)) := by
  rw [listblank_append_append, list_pow_add_comm, ← list_pow_add]

theorem listblank_right_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (([1] : List (Fin 2)) ^ n) +> ((([1] : List (Fin 2)) ^ m) +> s) =
    (([1] : List (Fin 2)) ^ (n + m)) +> s := by
  rw [← listblank_append_right_assoc, ← list_pow_add]

def encLeft1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))

def encRight1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | d :: R => (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0)

@[simp] theorem encLeft_nil : encLeft1 [] = default := rfl
@[simp] theorem encLeft_cons (a : ℕ) (L : List ℕ) :
    encLeft1 (a :: L) = ((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) := rfl
@[simp] theorem encRight_nil : encRight1 [] = default := rfl
@[simp] theorem encRight_cons (d : ℕ) (R : List ℕ) :
    encRight1 (d :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight1 R).cons 0) := rfl

def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | b :: L => (b + 1) :: L

@[simp] theorem encLeft_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encLeft1 L = encLeft1 (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encLeft1]
  | cons b L' => rfl

@[simp] theorem encRight_cons_one (R : List ℕ) :
    (1 : Fin 2) >> encRight1 R = encRight1 (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encRight1]
  | cons d R' => rfl

theorem encLeft_zero (L : List ℕ) :
    encLeft1 (0 :: L) = (1 : Fin 2) >> ((0 : Fin 2) >> encLeft1 L) := rfl
theorem encLeft_succ (a : ℕ) (L : List ℕ) :
    encLeft1 ((a + 1) :: L) = (1 : Fin 2) >> encLeft1 (a :: L) := rfl
theorem encRight_zero (R : List ℕ) :
    encRight1 (0 :: R) = (1 : Fin 2) >> ((0 : Fin 2) >> encRight1 R) := rfl
theorem encRight_succ (d : ℕ) (R : List ℕ) :
    encRight1 ((d + 1) :: R) = (1 : Fin 2) >> encRight1 (d :: R) := rfl

theorem encRight_expose (d : ℕ) (R : List ℕ) :
    encRight1 (d :: R) =
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ d) +> ((encRight1 R).cons 0)) := by
  rw [encRight_cons d R, Nat.add_comm d 1, ← listblank_right_pow_add ((encRight1 R).cons 0) 1 d]
  rfl

theorem encLeft_expose (a : ℕ) (L : List ℕ) :
    encLeft1 (a :: L) =
      (1 : Fin 2) >> (((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a)) := by
  rw [encLeft_cons a L, ← listblank_append_pow_add ((encLeft1 L).cons 0) a 1]
  rfl

def isFlipped (target_tm : Machine (Fin 2) (Fin 6)) : Bool :=
  match target_tm 0 1 with
  | some (some 5, _) => true
  | _ => false

def cfg_BR (target_tm : Machine (Fin 2) (Fin 6)) (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  if isFlipped target_tm then
    (encLeft1 R) <{{(4 : Fin 6)}} (encRight1 L)
  else
    (encLeft1 L) {{(1 : Fin 6)}}> (encRight1 R)

def cfg_C (target_tm : Machine (Fin 2) (Fin 6)) (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  if isFlipped target_tm then
    ⟨some 1, ⟨0, encLeft1 R, encRight1 L⟩⟩
  else
    ⟨some 2, ⟨0, encLeft1 L, encRight1 R⟩⟩

def cfg_B (target_tm : Machine (Fin 2) (Fin 6)) (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  if isFlipped target_tm then
    ⟨some 4, ⟨0, encLeft1 R, encRight1 L⟩⟩
  else
    ⟨some 1, ⟨0, encLeft1 L, encRight1 R⟩⟩

def cfg_DR0 (target_tm : Machine (Fin 2) (Fin 6)) (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  if isFlipped target_tm then
    ⟨some 2, ⟨0, (0 : Fin 2) >> encLeft1 R, encRight1 L⟩⟩
  else
    ⟨some 3, ⟨0, encLeft1 L, (0 : Fin 2) >> encRight1 R⟩⟩

inductive StackMode
  | BR
  | C
  | B
  | DR0
  deriving DecidableEq

def evalStackCfg1 (target_tm : Machine (Fin 2) (Fin 6)) :
    StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .BR, L, R => cfg_BR target_tm L R
  | .C, L, R => cfg_C target_tm L R
  | .B, L, R => cfg_B target_tm L R
  | .DR0, L, R => cfg_DR0 target_tm L R

class HasRleStackRules (target_tm : Machine (Fin 2) (Fin 6)) : Prop where
  rule_B_nil (L : List ℕ) :
    (cfg_B target_tm L []) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) [])
  rule_B_zero (L R : List ℕ) :
    (cfg_B target_tm L (0 :: R)) [target_tm]⊢⁺ (cfg_B target_tm (0 :: L) R)
  rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR target_tm L (0 :: d :: R))
  rule_BR_nil (L : List ℕ) :
    (cfg_BR target_tm L []) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) [])
  rule_BR_zero (L R : List ℕ) :
    (cfg_BR target_tm L (0 :: R)) [target_tm]⊢⁺ (cfg_BR target_tm (0 :: L) R)
  rule_BR_one (L R : List ℕ) :
    (cfg_BR target_tm L (1 :: R)) [target_tm]⊢⁺ (cfg_DR0 target_tm L (bumpHead R))
  rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm L ((d + 2) :: R)) [target_tm]⊢⁺ (cfg_B target_tm (bumpHead L) (d :: R))
  rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 target_tm [] R) [target_tm]⊢⁺ (cfg_C target_tm [1] R)
  rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 target_tm (0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 target_tm L (0 :: R))
  rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 target_tm ((a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (a :: L) (0 :: R))
  rule_C_nil (R : List ℕ) :
    (cfg_C target_tm [] R) [target_tm]⊢⁺ (cfg_DR0 target_tm [] R)
  rule_C_zero_nil (R : List ℕ) :
    (cfg_C target_tm [0] R) [target_tm]⊢⁺ (cfg_C target_tm [] (1 :: R))
  rule_C_zero_zero (L R : List ℕ) :
    (cfg_C target_tm (0 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) (1 :: R))
  rule_C_zero_one (L R : List ℕ) :
    (cfg_C target_tm (0 :: 1 :: L) R) [target_tm]⊢⁺
      (cfg_C target_tm (bumpHead (bumpHead L)) (0 :: bumpHead R))
  rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (0 :: (a + 2) :: L) R) [target_tm]⊢⁺
      (cfg_BR target_tm (a :: L) (0 :: 1 :: R))
  rule_C_one_nil (R : List ℕ) :
    (cfg_C target_tm [1] R) [target_tm]⊢⁺ (cfg_B target_tm [0] (1 :: R))
  rule_C_one_zero (L R : List ℕ) :
    (cfg_C target_tm (1 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 target_tm L (2 :: R))
  rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (a :: L) (2 :: R))
  rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone

variable {target_tm : Machine (Fin 2) (Fin 6)} [HasRleStackRules target_tm]

abbrev rule_B_nil := HasRleStackRules.rule_B_nil (target_tm := target_tm)
abbrev rule_B_zero := HasRleStackRules.rule_B_zero (target_tm := target_tm)
abbrev rule_B_succ := HasRleStackRules.rule_B_succ (target_tm := target_tm)
abbrev rule_BR_nil := HasRleStackRules.rule_BR_nil (target_tm := target_tm)
abbrev rule_BR_zero := HasRleStackRules.rule_BR_zero (target_tm := target_tm)
abbrev rule_BR_one := HasRleStackRules.rule_BR_one (target_tm := target_tm)
abbrev rule_BR_add_two := HasRleStackRules.rule_BR_add_two (target_tm := target_tm)
abbrev rule_DR0_nil := HasRleStackRules.rule_DR0_nil (target_tm := target_tm)
abbrev rule_DR0_zero := HasRleStackRules.rule_DR0_zero (target_tm := target_tm)
abbrev rule_DR0_succ := HasRleStackRules.rule_DR0_succ (target_tm := target_tm)
abbrev rule_C_nil := HasRleStackRules.rule_C_nil (target_tm := target_tm)
abbrev rule_C_zero_nil := HasRleStackRules.rule_C_zero_nil (target_tm := target_tm)
abbrev rule_C_zero_zero := HasRleStackRules.rule_C_zero_zero (target_tm := target_tm)
abbrev rule_C_zero_one := HasRleStackRules.rule_C_zero_one (target_tm := target_tm)
abbrev rule_C_zero_add_two := HasRleStackRules.rule_C_zero_add_two (target_tm := target_tm)
abbrev rule_C_one_nil := HasRleStackRules.rule_C_one_nil (target_tm := target_tm)
abbrev rule_C_one_zero := HasRleStackRules.rule_C_one_zero (target_tm := target_tm)
abbrev rule_C_one_succ := HasRleStackRules.rule_C_one_succ (target_tm := target_tm)
abbrev rule_C_add_two_halt := HasRleStackRules.rule_C_add_two_halt (target_tm := target_tm)




-- ============================================================================
-- Section 2: Semantic Multi-Step Contractions on `List ℕ`
-- ============================================================================

@[simp] theorem stepStar_refl {M : Machine Γ Λ} (c : Cfg Γ Λ) : c [M]⊢* c := ⟨0, rfl⟩
theorem pow_zero_list_gen {α : Type*} (l : List α) : l ^ (0 : ℕ) = [] := rfl
theorem pow_succ_list_gen {α : Type*} (l : List α) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := rfl

theorem pow_succ_right_list {α : Type*} (l : List α) : ∀ (n : ℕ),
    l ^ (n + 1) = l ^ n ++ l
  | 0 => List.append_nil l
  | n + 1 => by
    change l ++ l ^ (n + 1) = (l ++ l ^ n) ++ l
    rw [pow_succ_right_list l n, List.append_assoc]

abbrev rep0 (n : ℕ) : List ℕ := List.replicate n 0
def blkL (r : ℕ) : List ℕ := rep0 (r + 2) ++ [1]
def blkR (r : ℕ) : List ℕ := rep0 r ++ [2, 1]

theorem rep0_zero : rep0 0 = [] := rfl
theorem rep0_succ (n : ℕ) : rep0 (n + 1) = 0 :: rep0 n := rfl

theorem rep0_append_zero_cons (k : ℕ) (L : List ℕ) :
    rep0 k ++ (0 :: L) = 0 :: (rep0 k ++ L) := by
  induction k with
  | zero => rfl
  | succ k' ih => simp only [List.replicate_succ, List.cons_append]; rw [ih]

theorem rep0_add_split (a b : ℕ) : rep0 (a + b) = rep0 a ++ rep0 b :=
  List.replicate_add a b 0

macro "norm_list" : tactic => `(tactic|
  simp only [HPow.hPow, List.append_eq,
    blkL, blkR, bumpHead,
    List.replicate_succ, List.replicate_zero, rep0_add_split,
    List.nil_append, List.cons_append, List.append_nil, List.append_assoc,
    rep0_append_zero_cons, List.flatten_cons, List.flatten_nil])

theorem rule_BR_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_BR target_tm L (rep0 k ++ R)) [target_tm]⊢* (cfg_BR target_tm (rep0 k ++ L) R) := by
  induction k generalizing L with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (rule_BR_zero (target_tm := target_tm) L (rep0 k ++ R))
    have h2 := ih (0 :: L)
    rw [rep0_append_zero_cons k L] at h2
    exact stepStar_trans h1 h2

theorem rule_B_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_B target_tm L (rep0 k ++ R)) [target_tm]⊢* (cfg_B target_tm (rep0 k ++ L) R) := by
  induction k generalizing L with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (rule_B_zero (target_tm := target_tm) L (rep0 k ++ R))
    have h2 := ih (0 :: L)
    rw [rep0_append_zero_cons k L] at h2
    exact stepStar_trans h1 h2

theorem rule_DR0_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_DR0 target_tm (rep0 k ++ L) R) [target_tm]⊢* (cfg_DR0 target_tm L (rep0 k ++ R)) := by
  induction k generalizing R with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (rule_DR0_zero (target_tm := target_tm) (rep0 k ++ L) R)
    have h2 := ih (0 :: R)
    rw [rep0_append_zero_cons k R] at h2
    exact stepStar_trans h1 h2

theorem rule_B_succ_step (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR target_tm (0 :: L) (d :: R)) :=
  stepPlus_trans (rule_B_succ d L R) (rule_BR_zero L (d :: R))

theorem rule_C_one_prefix (c0 : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (rep0 c0 ++ 1 :: L)) R) [target_tm]⊢*
    (cfg_C target_tm (0 :: L) (rep0 c0 ++ 2 :: R)) := by
  cases c0 with
  | zero => exact stepPlus_stepStar (rule_C_one_succ 0 L R)
  | succ n =>
    have h1 := stepPlus_stepStar (rule_C_one_zero (target_tm := target_tm) (rep0 n ++ 1 :: L) R)
    have h2 := rule_DR0_zeros_all (target_tm := target_tm) (1 :: L) (2 :: R) n
    have h3 := stepPlus_stepStar (rule_DR0_succ (target_tm := target_tm) 0 L (rep0 n ++ 2 :: R))
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem rule_C_r_add_three (r : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (rep0 (r + 3) ++ 1 :: L) R) [target_tm]⊢*
    (cfg_C target_tm (0 :: L) (blkR r ++ R)) := by
  have heq1 : rep0 (r + 3) ++ 1 :: L = 0 :: 0 :: 0 :: (rep0 r ++ 1 :: L) := by norm_list
  rw [heq1]
  have h1 := stepPlus_stepStar (rule_C_zero_zero (target_tm := target_tm) (0 :: (rep0 r ++ 1 :: L))
      R)
  have h2 := rule_C_one_prefix (target_tm := target_tm) r L (1 :: R)
  have heq2 : rep0 r ++ 2 :: 1 :: R = blkR r ++ R := by norm_list
  rw [heq2] at h2
  exact stepStar_trans h1 h2

theorem rule_C_blkL_pow : ∀ (c r : ℕ) (L R : List ℕ),
    (cfg_C target_tm (0 :: ((blkL r) ^ c ++ L)) R) [target_tm]⊢*
    (cfg_C target_tm (0 :: L) ((blkR r) ^ c ++ R))
  | 0, r, L, R => ⟨0, rfl⟩
  | c + 1, r, L, R => by
    have heq : 0 :: ((blkL r) ^ (c + 1) ++ L) =
        rep0 (r + 3) ++ 1 :: ((blkL r) ^ c ++ L) := by norm_list
    rw [heq]
    have h1 := rule_C_r_add_three (target_tm := target_tm) r ((blkL r) ^ c ++ L) R
    have h2 := rule_C_blkL_pow c r L (blkR r ++ R)
    have h3 : (blkR r) ^ c ++ (blkR r ++ R) = (blkR r) ^ (c + 1) ++ R := by
      rw [← List.append_assoc, ← pow_succ_right_list]
    rw [h3] at h2
    exact stepStar_trans h1 h2

theorem rule_C_bot_four (r : ℕ) (R : List ℕ) :
    (cfg_C target_tm (rep0 (r + 4)) R) [target_tm]⊢*
    (cfg_DR0 target_tm [] (blkR r ++ R)) := by
  have heq : rep0 (r + 4) = 0 :: 0 :: 0 :: 0 :: rep0 r := by norm_list
  rw [heq]
  have h1 := stepPlus_stepStar (rule_C_zero_zero (target_tm := target_tm) (0 :: 0 :: rep0 r) R)
  have h2 := stepPlus_stepStar (rule_C_one_zero (target_tm := target_tm) (rep0 r) (1 :: R))
  have h3 := rule_DR0_zeros_all (target_tm := target_tm) [] (2 :: 1 :: R) r
  have heq0 : rep0 r ++ [] = rep0 r := List.append_nil _
  have heq2 : rep0 r ++ 2 :: 1 :: R = blkR r ++ R := by norm_list
  rw [heq0, heq2] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem rule_DR0_bot (k : ℕ) (R : List ℕ) :
    (cfg_DR0 target_tm (rep0 k) R) [target_tm]⊢* (cfg_BR target_tm (rep0 (k + 3)) R) := by
  have h0 : rep0 k = rep0 k ++ [] := (List.append_nil _).symm
  rw [h0]
  have h1 := rule_DR0_zeros_all (target_tm := target_tm) [] R k
  have h2 := stepPlus_stepStar (rule_DR0_nil (target_tm := target_tm) (rep0 k ++ R))
  have h3 := stepPlus_stepStar (rule_C_one_nil (target_tm := target_tm) (rep0 k ++ R))
  have h4 := stepPlus_stepStar (rule_B_succ_step (target_tm := target_tm) 0 [0] (rep0 k ++ R))
  have h5 := rule_BR_zeros_all (target_tm := target_tm) [0, 0] R (k + 1)
  have heqR : 0 :: (rep0 k ++ R) = rep0 (k + 1) ++ R := rfl
  have heqL : rep0 (k + 1) ++ [0, 0] = rep0 (k + 3) := by norm_list
  rw [heqR] at h4; rw [heqL] at h5
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem rule_DR0_bot_zeros : ∀ (q k : ℕ) (R : List ℕ),
    (cfg_DR0 target_tm (rep0 k) (1 :: (rep0 q ++ R))) [target_tm]⊢*
    (cfg_DR0 target_tm (rep0 (k + 3 * q)) (1 :: R))
  | 0, k, R => by simp
  | q + 1, k, R => by
    have h1 := rule_DR0_bot (target_tm := target_tm) k (1 :: (0 :: (rep0 q ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_one (target_tm := target_tm) (rep0 (k + 3))
        (0 :: (rep0 q ++ R)))
    have h3 := rule_DR0_bot_zeros q (k + 3) R
    have heq : k + 3 + 3 * q = k + 3 * (q + 1) := by omega
    rw [heq] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem rule_BR_blkR_one (r : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm (0 :: L) (blkR r ++ R)) [target_tm]⊢*
    (cfg_BR target_tm (rep0 3 ++ 1 :: (rep0 r ++ L)) R) := by
  have h0 : blkR r ++ R = rep0 r ++ (2 :: 1 :: R) := by norm_list
  rw [h0]
  have h1 := rule_BR_zeros_all (target_tm := target_tm) (0 :: L) (2 :: 1 :: R) r
  rw [rep0_append_zero_cons r L] at h1
  have h2 := stepPlus_stepStar (rule_BR_add_two (target_tm := target_tm) 0
      (0 :: (rep0 r ++ L)) (1 :: R))
  have h3 := stepPlus_stepStar (rule_B_zero (target_tm := target_tm) (1 :: (rep0 r ++ L)) (1 :: R))
  have h4 := stepPlus_stepStar (rule_B_succ_step (target_tm := target_tm) 0
      (0 :: 1 :: (rep0 r ++ L)) R)
  have h5 := stepPlus_stepStar (rule_BR_zero (target_tm := target_tm)
      (0 :: 0 :: 1 :: (rep0 r ++ L)) R)
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem rule_BR_blkR_succ : ∀ (k r : ℕ) (L R : List ℕ),
    (cfg_BR target_tm (0 :: L) ((blkR r) ^ (k + 1) ++ R)) [target_tm]⊢*
    (cfg_BR target_tm (rep0 3 ++ 1 :: ((blkL r) ^ k ++ (rep0 r ++ L))) R)
  | 0, r, L, R => by
    simpa [HPow.hPow, List.append_eq, List.replicate_succ, List.replicate_zero, List.flatten_cons
        , List.flatten_nil] using rule_BR_blkR_one r L R
  | k + 1, r, L, R => by
    have heqR : (blkR r) ^ (k + 2) ++ R = blkR r ++ ((blkR r) ^ (k + 1) ++ R) := by
      simp [HPow.hPow, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [heqR]
    have h1 := rule_BR_blkR_one (target_tm := target_tm) r L ((blkR r) ^ (k + 1) ++ R)
    have h2 := rule_BR_blkR_succ k r (0 :: 0 :: 1 :: (rep0 r ++ L)) R
    have heqL1 : rep0 3 ++ 1 :: (rep0 r ++ L) = 0 :: (0 :: 0 :: 1 :: (rep0 r ++ L)) := rfl
    rw [heqL1] at h1
    have heqL2 : (blkL r) ^ k ++ (rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L))) =
        (blkL r) ^ (k + 1) ++ (rep0 r ++ L) := by
      have hb : rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L)) = blkL r ++ (rep0 r ++ L) := by norm_list
      rw [hb, ← List.append_assoc, ← pow_succ_right_list]
    rw [heqL2] at h2
    exact stepStar_trans h1 h2

theorem rule_BR_blkR_clean (c r : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm (rep0 3 ++ 1 :: L) ((blkR r) ^ c ++ R)) [target_tm]⊢*
    (cfg_BR target_tm (rep0 3 ++ 1 :: ((blkL r) ^ c ++ L)) R) := by
  cases c with
  | zero => exact ⟨0, rfl⟩
  | succ k =>
    have h := rule_BR_blkR_succ (target_tm := target_tm) k r (0 :: 0 :: 1 :: L) R
    have heq1 : (blkL r) ^ k ++ (rep0 r ++ (0 :: 0 :: 1 :: L)) =
        (blkL r) ^ (k + 1) ++ L := by
      have hb : rep0 r ++ (0 :: 0 :: 1 :: L) = blkL r ++ L := by norm_list
      rw [hb, ← List.append_assoc, ← pow_succ_right_list]
    rw [heq1] at h
    exact h

-- ============================================================================
-- Section 3: Clean-Mode Invariant Structure & O(1) Contraction Theorems
-- ============================================================================

def decSegs : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (r, c) :: ss => (blkL r) ^ c ++ decSegs ss

inductive Item where
  | z (c : ℕ)
  | d (v : ℕ)
  | k (r c : ℕ)

inductive LState where
  | raw (items : List Item)
  | clean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ)

def decL : List Item → List ℕ
  | [] => []
  | .z c :: xs => rep0 c ++ decL xs
  | .d v :: xs => v :: decL xs
  | .k r c :: xs => (blkL r) ^ c ++ decL xs

def decR : List Item → List ℕ
  | [] => []
  | .z c :: xs => rep0 c ++ decR xs
  | .d v :: xs => v :: decR xs
  | .k r c :: xs => (blkR r) ^ c ++ decR xs

def decLState : LState → List ℕ
  | .raw items => decL items
  | .clean c0 segs bot => rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))

def pushSeg (r c : ℕ) (segs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if Nat.beq c 0 then segs
  else match segs with
    | (r2, c2) :: ss => if Nat.beq r r2 then (r, c + c2) :: ss else (r, c) :: segs
    | [] => [(r, c)]

theorem decSegs_pushSeg (r c : ℕ) (segs : List (ℕ × ℕ)) :
    decSegs (pushSeg r c segs) = (blkL r) ^ c ++ decSegs segs := by
  unfold pushSeg
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases segs with
    | nil => rfl
    | cons hd ss =>
      rcases hd with ⟨r2, c2⟩
      dsimp only
      split
      · next hr =>
        rw [Nat.beq_eq] at hr; subst hr
        simp [decSegs, list_pow_add, List.append_assoc]
      · rfl

macro "norm_all" : tactic => `(tactic|
  simp only [decL, decR, decSegs, decLState, decSegs_pushSeg,
    HPow.hPow, List.append_eq,
    blkL, blkR, bumpHead,
    List.replicate_succ, List.replicate_zero, rep0_add_split,
    List.nil_append, List.cons_append, List.append_nil, List.append_assoc,
    rep0_append_zero_cons, List.flatten_cons, List.flatten_nil])

theorem clean_sweep_core : ∀ (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_C target_tm (0 :: (decSegs segs ++ rep0 (bot + 3))) R) [target_tm]⊢*
    (cfg_BR target_tm (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R)
  | [], bot, R => by
    dsimp only [decSegs]
    have heq : (0 :: ([] ++ rep0 (bot + 3))) = rep0 (bot + 4) := by norm_all
    rw [heq]
    have h1 := rule_C_bot_four (target_tm := target_tm) bot R
    have h2 := rule_DR0_bot (target_tm := target_tm) 0 (blkR bot ++ R)
    have h3 := rule_BR_blkR_one (target_tm := target_tm) bot [0, 0] R
    have heq2 : rep0 bot ++ [0, 0] = rep0 (bot + 2) := by norm_all
    rw [heq2] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)
  | (r, c) :: ss, bot, R => by
    dsimp only [decSegs]
    rw [List.append_assoc]
    have h1 := rule_C_blkL_pow (target_tm := target_tm) c r (decSegs ss ++ rep0 (bot + 3)) R
    have h2 := clean_sweep_core ss bot ((blkR r) ^ c ++ R)
    have h3 := rule_BR_blkR_clean (target_tm := target_tm) c r (decSegs ss ++ rep0 (bot + 2)) R
    rw [← List.append_assoc] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem clean_DR0_one (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_DR0 target_tm (decLState (.clean c0 segs (bot + 1))) R) [target_tm]⊢*
    (cfg_BR target_tm (decLState (.clean (c0 + 4) segs bot)) R) := by
  dsimp only [decLState]
  have h1 := rule_DR0_zeros_all (target_tm := target_tm)
      (1 :: (decSegs segs ++ rep0 (bot + 3))) R c0
  have h2 := stepPlus_stepStar (rule_DR0_succ (target_tm := target_tm) 0
      (decSegs segs ++ rep0 (bot + 3)) (rep0 c0 ++ R))
  have h3 := clean_sweep_core (target_tm := target_tm) segs bot (0 :: (rep0 c0 ++ R))
  have h4 := rule_BR_zeros_all (target_tm := target_tm)
      (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R (c0 + 1)
  have heqL : rep0 (c0 + 1) ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      rep0 (c0 + 4) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)) := by norm_all
  rw [heqL] at h4
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem clean_DR0_zeros : ∀ (q c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_DR0 target_tm (decLState (.clean c0 segs (bot + q))) (1 :: (rep0 q ++ R))) [target_tm]⊢*
    (cfg_DR0 target_tm (decLState (.clean (c0 + 4 * q) segs bot)) (1 :: R))
  | 0, c0, segs, bot, R => ⟨0, rfl⟩
  | q + 1, c0, segs, bot, R => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have h1 := clean_DR0_one (target_tm := target_tm) c0 segs (bot + q) (1 :: (0 :: (rep0 q ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_one (target_tm := target_tm)
        (decLState (.clean (c0 + 4) segs (bot + q))) (0 :: (rep0 q ++ R)))
    have h3 := clean_DR0_zeros q (c0 + 4) segs bot R
    have heq : c0 + 4 + 4 * q = c0 + 4 * (q + 1) := by omega
    rw [heq] at h3
    exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem clean_RNIL_one (m : StackMode) (hm : m = .B ∨ m = .BR)
    (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) :
    (evalStackCfg1 target_tm m (decLState (.clean (c0 + 1) segs (bot + 1))) []) [target_tm]⊢*
    (cfg_B target_tm (decLState (.clean 1 (pushSeg c0 1 segs) bot)) []) := by
  have h0 : (evalStackCfg1 target_tm m (decLState (.clean (c0 + 1) segs (bot + 1))) [])
      [target_tm]⊢*
      (cfg_C target_tm (1 :: (rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3)))) []) := by
    have heqL : bumpHead (decLState (.clean (c0 + 1) segs (bot + 1))) =
        1 :: (rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3))) := by norm_all
    rcases hm with rfl | rfl
    · rw [← heqL]; exact stepPlus_stepStar (rule_B_nil _)
    · rw [← heqL]; exact stepPlus_stepStar (rule_BR_nil _)
  have h1 := rule_C_one_prefix (target_tm := target_tm) c0 (decSegs segs ++ rep0 (bot + 3)) []
  have h2 := clean_sweep_core (target_tm := target_tm) segs bot (rep0 c0 ++ [2])
  have h3 := rule_BR_zeros_all (target_tm := target_tm)
      (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) [2] c0
  have heq3 : rep0 c0 ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      0 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) := by norm_all
  rw [heq3] at h3
  have h4 := stepPlus_stepStar (rule_BR_add_two (target_tm := target_tm) 0
      (0 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])
  have h5 := stepPlus_stepStar (rule_B_zero (target_tm := target_tm)
      (1 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])
  have heq5 : 0 :: 1 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      decLState (.clean 1 (pushSeg c0 1 segs) bot) := by norm_all
  rw [heq5] at h5
  exact stepStar_trans h0 (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans
      h4 h5))))

theorem decSegs_pushSeg_succ (r q : ℕ) (segs : List (ℕ × ℕ)) :
    decSegs (pushSeg r q (pushSeg r 1 segs)) = decSegs (pushSeg r (q + 1) segs) := by
  rw [decSegs_pushSeg, decSegs_pushSeg, decSegs_pushSeg, ← List.append_assoc,
      ← list_pow_add]

theorem clean_RNIL_zero_pow : ∀ (q : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ),
    (cfg_B target_tm (decLState (.clean 1 segs (bot + q))) []) [target_tm]⊢*
    (cfg_B target_tm (decLState (.clean 1 (pushSeg 0 q segs) bot)) [])
  | 0, segs, bot => by simp [pushSeg]
  | q + 1, segs, bot => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have h1 := clean_RNIL_one (target_tm := target_tm) .B (Or.inl rfl) 0 segs (bot + q)
    have h2 := clean_RNIL_zero_pow q (pushSeg 0 1 segs) bot
    have heqL : decLState (.clean 1 (pushSeg 0 q (pushSeg 0 1 segs)) bot) =
        decLState (.clean 1 (pushSeg 0 (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    exact stepStar_trans h1 h2

theorem clean_P1_one (r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_B target_tm (decLState (.clean 0 segs (bot + 1))) (0 :: (blkR r ++ R))) [target_tm]⊢*
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (r + 3) 1 segs) bot)) (0 :: R)) := by
  have heqR : 0 :: (blkR r ++ R) = rep0 (r + 1) ++ (2 :: 1 :: R) := by norm_all
  rw [heqR]
  have h1 := rule_B_zeros_all (target_tm := target_tm)
      (decLState (.clean 0 segs (bot + 1))) (2 :: 1 :: R) (r + 1)
  have h2 := stepPlus_stepStar (rule_B_succ_step (target_tm := target_tm) 1
      (rep0 (r + 1) ++ decLState (.clean 0 segs (bot + 1))) (1 :: R))
  have heq2 : 0 :: (rep0 (r + 1) ++ decLState (.clean 0 segs (bot + 1))) =
      decLState (.clean (r + 2) segs (bot + 1)) := by norm_all
  rw [heq2] at h2
  have h3 := stepPlus_stepStar (rule_BR_one (target_tm := target_tm)
      (decLState (.clean (r + 2) segs (bot + 1))) (1 :: R))
  have h4 := clean_DR0_one (target_tm := target_tm) (r + 2) segs bot (2 :: R)
  have h5 := stepPlus_stepStar (rule_BR_add_two (target_tm := target_tm) 0
      (decLState (.clean (r + 6) segs bot)) R)
  have heq5 : bumpHead (decLState (.clean (r + 6) segs bot)) =
      decLState (.clean 0 (pushSeg (r + 3) 1 segs) bot) := by norm_all
  rw [heq5] at h5
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem clean_P1_pow : ∀ (q r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_B target_tm (decLState (.clean 0 segs (bot + q))) (0 :: ((blkR r) ^ q ++ R)))
        [target_tm]⊢*
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (r + 3) q segs) bot)) (0 :: R))
  | 0, r, segs, bot, R => by simp [pushSeg, HPow.hPow, List.flatten_nil]
  | q + 1, r, segs, bot, R => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have heqR : (blkR r) ^ (q + 1) ++ R = blkR r ++ ((blkR r) ^ q ++ R) := by
      simp [HPow.hPow, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [heqR]
    have h1 := clean_P1_one (target_tm := target_tm) r segs (bot + q) ((blkR r) ^ q ++ R)
    have h2 := clean_P1_pow q r (pushSeg (r + 3) 1 segs) bot R
    have heqL : decLState (.clean 0 (pushSeg (r + 3) q (pushSeg (r + 3) 1 segs)) bot) =
        decLState (.clean 0 (pushSeg (r + 3) (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    exact stepStar_trans h1 h2

theorem clean_P2_one (r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_B target_tm (decLState (.clean 0 segs (bot + (r + 1)))) (1 :: 1 :: (blkR r ++ R)))
        [target_tm]⊢*
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (4 * r + 3) 1 segs) bot)) (1 :: 1 :: R)) := by
  cases r with
  | zero =>
    have h1 := stepPlus_stepStar (rule_B_succ_step (target_tm := target_tm) 0
        (decLState (.clean 0 segs (bot + 1))) (1 :: (blkR 0 ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_zero (target_tm := target_tm)
        (0 :: decLState (.clean 0 segs (bot + 1))) (1 :: (blkR 0 ++ R)))
    have heq2 : 0 :: 0 :: decLState (.clean 0 segs (bot + 1)) =
        decLState (.clean 2 segs (bot + 1)) := rfl
    rw [heq2] at h2
    have h3 := stepPlus_stepStar (rule_BR_one (target_tm := target_tm)
        (decLState (.clean 2 segs (bot + 1))) (blkR 0 ++ R))
    have hb0 : bumpHead (blkR 0 ++ R) = 3 :: 1 :: R := rfl
    rw [hb0] at h3
    have h4 := clean_DR0_one (target_tm := target_tm) 2 segs bot (3 :: 1 :: R)
    have h5 := stepPlus_stepStar (rule_BR_add_two (target_tm := target_tm) 1
        (decLState (.clean 6 segs bot)) (1 :: R))
    have heq5 : bumpHead (decLState (.clean 6 segs bot)) =
        decLState (.clean 0 (pushSeg 3 1 segs) bot) := by norm_all
    rw [heq5] at h5
    exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))
  | succ r' =>
    rw [show bot + (r' + 1 + 1) = (bot + 2) + r' by omega]
    have h1 := stepPlus_stepStar (rule_B_succ_step (target_tm := target_tm) 0
        (decLState (.clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))
    have h2 := stepPlus_stepStar (rule_BR_zero (target_tm := target_tm)
        (0 :: decLState (.clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))
    have heq2 : 0 :: 0 :: decLState (.clean 0 segs ((bot + 2) + r')) =
        decLState (.clean 2 segs ((bot + 2) + r')) := rfl
    rw [heq2] at h2
    have h3 := stepPlus_stepStar (rule_BR_one (target_tm := target_tm)
        (decLState (.clean 2 segs ((bot + 2) + r'))) (blkR (r' + 1) ++ R))
    have hb : bumpHead (blkR (r' + 1) ++ R) = 1 :: (rep0 r' ++ (2 :: 1 :: R)) := by norm_all
    rw [hb] at h3
    have h4 := clean_DR0_zeros (target_tm := target_tm) r' 2 segs (bot + 2) (2 :: 1 :: R)
    have h5 := clean_DR0_one (target_tm := target_tm) (2 + 4 * r') segs (bot + 1) (1 :: 2 :: 1 :: R)
    have h6 := stepPlus_stepStar (rule_BR_one (target_tm := target_tm)
        (decLState (.clean (2 + 4 * r' + 4) segs (bot + 1))) (2 :: 1 :: R))
    have h7 := clean_DR0_one (target_tm := target_tm) (2 + 4 * r' + 4) segs bot (3 :: 1 :: R)
    have h8 := stepPlus_stepStar (rule_BR_add_two (target_tm := target_tm) 1
        (decLState (.clean (2 + 4 * r' + 8) segs bot)) (1 :: R))
    have heq8 : bumpHead (decLState (.clean (2 + 4 * r' + 8) segs bot)) =
        decLState (.clean 0 (pushSeg (4 * (r' + 1) + 3) 1 segs) bot) := by
      rw [show 4 * (r' + 1) + 3 = 4 * r' + 7 by omega]
      norm_all
    rw [heq8] at h8
    exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3
      (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 (stepStar_trans h7 h8))))))

theorem clean_P2_pow : ∀ (q r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_B target_tm (decLState (.clean 0 segs (bot + q * (r + 1)))) (1 :: 1 :: ((blkR r) ^ q ++
        R))) [target_tm]⊢*
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (4 * r + 3) q segs) bot)) (1 :: 1 :: R))
  | 0, r, segs, bot, R => by simp [pushSeg, HPow.hPow, List.flatten_nil]
  | q + 1, r, segs, bot, R => by
    rw [show bot + (q + 1) * (r + 1) = (bot + q * (r + 1)) + (r + 1) by
      rw [Nat.succ_mul, Nat.add_assoc]]
    have heqR : (blkR r) ^ (q + 1) ++ R = blkR r ++ ((blkR r) ^ q ++ R) := by
      simp [HPow.hPow, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [heqR]
    have h1 := clean_P2_one (target_tm := target_tm) r segs (bot + q * (r + 1))
        ((blkR r) ^ q ++ R)
    have h2 := clean_P2_pow q r (pushSeg (4 * r + 3) 1 segs) bot R
    have heqL : decLState (.clean 0 (pushSeg (4 * r + 3) q (pushSeg (4 * r + 3) 1 segs)) bot) =
        decLState (.clean 0 (pushSeg (4 * r + 3) (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    exact stepStar_trans h1 h2

-- ============================================================================
-- Section 4: Executable RLE Stack Engine & Denotational Soundness
-- ============================================================================

def pushL0 (c : ℕ) (L : List Item) : List Item :=
  if Nat.beq c 0 then L
  else match L with
    | .z c2 :: xs => .z (c + c2) :: xs
    | _ => .z c :: L

def pushLk2 (r c : ℕ) (L : List Item) : List Item :=
  if Nat.beq c 0 then L
  else match L with
    | .k r2 c2 :: xs => if Nat.beq r r2 then .k r (c + c2) :: xs else .k r c :: L
    | _ => .k r c :: L

def pushLd (v : ℕ) (L : List Item) : List Item :=
  if Nat.beq v 0 then pushL0 1 L
  else if Nat.beq v 1 then
    match L with
    | .z c :: .d v2 :: xs =>
      if Nat.beq v2 1 && Nat.ble 2 c then .d 1 :: pushLk2 (c - 2) 1 xs
      else .d 1 :: L
    | _ => .d 1 :: L
  else .d v :: L

def popKTail (r c : ℕ) (xs : List Item) : List Item :=
  if Nat.beq c 1 then xs else .k r (c - 1) :: xs

def popL1 : List Item → Option (ℕ × List Item)
  | [] => none
  | .z c :: xs =>
    if Nat.beq c 0 then popL1 xs
    else if Nat.beq c 1 then some (0, xs)
    else some (0, .z (c - 1) :: xs)
  | .k r c :: xs =>
    if Nat.beq c 0 then popL1 xs
    else some (0, pushL0 (r + 1) (pushLd 1 (popKTail r c xs)))
  | .d v :: xs => some (v, xs)

def bumpL (L : List Item) : List Item :=
  match popL1 L with
  | none => [.z 1]
  | some (a, L1) => pushLd (a + 1) L1

def pushR0 (c : ℕ) (R : List Item) : List Item :=
  if Nat.beq c 0 then R
  else match R with
    | .z c2 :: xs => .z (c + c2) :: xs
    | _ => .z c :: R

def mergeRk2Pre (r c : ℕ) (R : List Item) : ℕ × List Item :=
  if Nat.ble 1 r then
    match R with
    | .z rz :: .d v2 :: .d v1 :: xs =>
      if Nat.beq rz r && Nat.beq v2 2 && Nat.beq v1 1 then (c + 1, xs) else (c, R)
    | _ => (c, R)
  else (c, R)

def pushRk2 (r c : ℕ) (R : List Item) : List Item :=
  if Nat.beq c 0 then R
  else
    let p := mergeRk2Pre r c R
    match p.2 with
    | .k r2 c2 :: xs => if Nat.beq r r2 then .k r (p.1 + c2) :: xs else .k r p.1 :: p.2
    | _ => .k r p.1 :: p.2

def pushRd (v : ℕ) (R : List Item) : List Item :=
  if Nat.beq v 0 then pushR0 1 R
  else if Nat.beq v 2 then
    match R with
    | .d v1 :: xs => if Nat.beq v1 1 then pushRk2 0 1 xs else .d 2 :: R
    | _ => .d 2 :: R
  else .d v :: R

def popR1 : List Item → Option (ℕ × List Item)
  | [] => none
  | .z c :: xs =>
    if Nat.beq c 0 then popR1 xs
    else if Nat.beq c 1 then some (0, xs)
    else some (0, .z (c - 1) :: xs)
  | .k r c :: xs =>
    if Nat.beq c 0 then popR1 xs
    else if Nat.beq r 0 then some (2, .d 1 :: popKTail r c xs)
    else some (0, pushR0 (r - 1) (.d 2 :: .d 1 :: popKTail r c xs))
  | .d v :: xs => some (v, xs)

def bumpR (R : List Item) : List Item :=
  match popR1 R with
  | none => [.z 1]
  | some (d, R1) => pushRd (d + 1) R1

def segsToItems : List (ℕ × ℕ) → List Item → List Item
  | [], acc => acc
  | (r, c) :: ss, acc =>
    if Nat.beq c 0 then segsToItems ss acc
    else .k r c :: segsToItems ss acc

def unpackClean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) : List Item :=
  let tail := segsToItems segs [.z (bot + 2)]
  if Nat.beq c0 0 then .d 1 :: tail else .z c0 :: .d 1 :: tail

def packTail (cur0 : ℕ) : List Item → Option (List (ℕ × ℕ) × ℕ)
  | [] => if Nat.ble 2 cur0 then some ([], cur0 - 2) else none
  | .z c :: rest => packTail (cur0 + c) rest
  | .d v :: rest =>
    if Nat.beq v 1 && Nat.ble 2 cur0 then
      match packTail 0 rest with
      | some (segs, bot) => some (pushSeg (cur0 - 2) 1 segs, bot)
      | none => none
    else none
  | .k r c :: rest =>
    if Nat.beq c 0 then packTail cur0 rest
    else
      match packTail 0 rest with
      | some (segs, bot) =>
        some (pushSeg (cur0 + r) 1 (pushSeg r (c - 1) segs), bot)
      | none => none

def packHead (cur0 : ℕ) : List Item → Option LState
  | [] => none
  | .z c :: rest => packHead (cur0 + c) rest
  | .d v :: rest =>
    if Nat.beq v 1 then
      match packTail 0 rest with
      | some (segs, bot) => some (.clean cur0 segs bot)
      | none => none
    else none
  | .k r c :: rest =>
    if Nat.beq c 0 then packHead cur0 rest
    else
      match packTail 0 rest with
      | some (segs, bot) =>
        some (.clean (cur0 + r + 2) (pushSeg r (c - 1) segs) bot)
      | none => none

theorem decL_pushL0 (c : ℕ) (L : List Item) :
    decL (pushL0 c L) = rep0 c ++ decL L := by
  unfold pushL0
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases L with
    | nil => rfl
    | cons hd xs =>
      cases hd with
      | z c2 => norm_all
      | d _ => rfl
      | k _ _ => rfl

theorem decL_pushLk2 (r c : ℕ) (L : List Item) :
    decL (pushLk2 r c L) = (blkL r) ^ c ++ decL L := by
  unfold pushLk2
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases L with
    | nil => rfl
    | cons hd xs =>
      cases hd with
      | z _ => rfl
      | d _ => rfl
      | k r2 c2 =>
        dsimp only; split
        · next hr =>
          rw [Nat.beq_eq] at hr; subst hr
          simp [decL, list_pow_add, List.append_assoc]
        · rfl

theorem decL_pushLd (v : ℕ) (L : List Item) :
    decL (pushLd v L) = v :: decL L := by
  unfold pushLd
  split
  · next h => rw [Nat.beq_eq] at h; subst h; simpa using decL_pushL0 1 L
  · split
    · next h =>
      rw [Nat.beq_eq] at h; subst h
      rcases L with _ | ⟨hd1, _ | ⟨hd2, xs⟩⟩
      · rfl
      · cases hd1 <;> rfl
      · cases hd1 with
        | z c =>
          cases hd2 with
          | d v2 =>
            dsimp only; split
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
              rcases hb with ⟨rfl, hc⟩
              simp only [decL, decL_pushLk2]
              conv_rhs => rw [show c = (c - 2) + 2 by omega]
              norm_all
            · rfl
          | _ => rfl
        | _ => rfl
    · rfl

theorem decL_popKTail (r c : ℕ) (xs : List Item) :
    decL (popKTail r c xs) = (blkL r) ^ (c - 1) ++ decL xs := by
  unfold popKTail; split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · rfl

theorem decR_popKTail (r c : ℕ) (xs : List Item) :
    decR (popKTail r c xs) = (blkR r) ^ (c - 1) ++ decR xs := by
  unfold popKTail; split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · rfl

theorem decL_popL1_none : ∀ (L : List Item), popL1 L = none → decL L = []
  | [], _ => rfl
  | .z c :: xs, h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_none xs h
    · split at h <;> cases h
  | .d _ :: _, h => by cases h
  | .k r c :: xs, h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_none xs h
    · cases h

theorem decL_popL1_some : ∀ (L : List Item) (a : ℕ) (L' : List Item),
    popL1 L = some (a, L') → decL L = a :: decL L'
  | [], _, _, h => by cases h
  | .z c :: xs, a, L', h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_some xs a L' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      split at h
      · next hc1 =>
        rw [Nat.beq_eq] at hc1; subst hc1
        cases h; rfl
      · cases h
        conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
        norm_all
  | .d v :: xs, a, L', h => by cases h; rfl
  | .k r c :: xs, a, L', h => by
    unfold popL1 at h
    split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decL_popL1_some xs a L' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      cases h
      rw [decL_pushL0, decL_pushLd, decL_popKTail]
      conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
      norm_all

theorem decL_bumpL (L : List Item) : decL (bumpL L) = bumpHead (decL L) := by
  unfold bumpL
  cases hp : popL1 L with
  | none => rw [decL_popL1_none L hp]; rfl
  | some p =>
    rcases p with ⟨a, L1⟩
    rw [decL_popL1_some L a L1 hp, decL_pushLd]; rfl

theorem decR_pushR0 (c : ℕ) (R : List Item) :
    decR (pushR0 c R) = rep0 c ++ decR R := by
  unfold pushR0
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · cases R with
    | nil => rfl
    | cons hd xs =>
      cases hd with
      | z c2 => norm_all
      | d _ => rfl
      | k _ _ => rfl

theorem mergeRk2Pre_spec (r c : ℕ) (R : List Item) :
    (blkR r) ^ (mergeRk2Pre r c R).1 ++ decR (mergeRk2Pre r c R).2 =
    (blkR r) ^ c ++ decR R := by
  unfold mergeRk2Pre
  split
  · rcases R with _ | ⟨hd1, _ | ⟨hd2, _ | ⟨hd3, xs⟩⟩⟩
    · rfl
    · cases hd1 <;> rfl
    · cases hd1 <;> cases hd2 <;> rfl
    · cases hd1 with
      | z rz =>
        cases hd2 with
        | d v2 =>
          cases hd3 with
          | d v1 =>
            dsimp only; split
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq] at hb
              rcases hb with ⟨⟨rfl, rfl⟩, rfl⟩
              rw [pow_succ_right_list]
              norm_all
            · rfl
          | _ => rfl
        | _ => rfl
      | _ => rfl
  · rfl

theorem decR_pushRk2 (r c : ℕ) (R : List Item) :
    decR (pushRk2 r c R) = (blkR r) ^ c ++ decR R := by
  unfold pushRk2
  split
  · next h => rw [Nat.beq_eq] at h; subst h; rfl
  · have key := mergeRk2Pre_spec r c R
    generalize mergeRk2Pre r c R = p at key ⊢
    rcases p with ⟨c', R'⟩
    dsimp only at key ⊢
    cases R' with
    | nil => exact key
    | cons hd xs =>
      cases hd with
      | z _ => exact key
      | d _ => exact key
      | k r2 c2 =>
        dsimp only; split
        · next hr =>
          rw [Nat.beq_eq] at hr; subst hr
          rw [← key]; simp [decR, list_pow_add, List.append_assoc]
        · exact key

theorem decR_pushRd (v : ℕ) (R : List Item) :
    decR (pushRd v R) = v :: decR R := by
  unfold pushRd
  split
  · next h => rw [Nat.beq_eq] at h; subst h; simpa using decR_pushR0 1 R
  · split
    · next h =>
      rw [Nat.beq_eq] at h; subst h
      cases R with
      | nil => rfl
      | cons hd xs =>
        cases hd with
        | d v1 =>
          dsimp only; split
          · next hv =>
            rw [Nat.beq_eq] at hv; subst hv
            rw [decR_pushRk2]; norm_all
          · rfl
        | _ => rfl
    · rfl

theorem decR_popR1_none : ∀ (R : List Item), popR1 R = none → decR R = []
  | [], _ => rfl
  | .z c :: xs, h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_none xs h
    · split at h <;> cases h
  | .d _ :: _, h => by cases h
  | .k r c :: xs, h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_none xs h
    · split at h <;> cases h

theorem decR_popR1_some : ∀ (R : List Item) (d : ℕ) (R' : List Item),
    popR1 R = some (d, R') → decR R = d :: decR R'
  | [], _, _, h => by cases h
  | .z c :: xs, d, R', h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_some xs d R' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      split at h
      · next hc1 => rw [Nat.beq_eq] at hc1; subst hc1; cases h; rfl
      · cases h
        conv_lhs => rw [decR, show c = (c - 1) + 1 by omega]
        norm_all
  | .d v :: xs, d, R', h => by cases h; rfl
  | .k r c :: xs, d, R', h => by
    unfold popR1 at h; split at h
    · next hc => rw [Nat.beq_eq] at hc; subst hc; exact decR_popR1_some xs d R' h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      split at h
      · next hr0 =>
        rw [Nat.beq_eq] at hr0; subst hr0; cases h
        rw [decR, decR_popKTail]
        conv_lhs => rw [decR, show c = (c - 1) + 1 by omega]
        norm_all
      · next hr0 =>
        have hrne : r ≠ 0 := fun heq => hr0 (Nat.beq_eq.mpr heq)
        cases h
        have hc : (blkR r) ^ c = rep0 ((r - 1) + 1) ++ ([2, 1] ++ (blkR r) ^ (c - 1)) := by
          conv_lhs =>
            rw [show c = (c - 1) + 1 by omega, pow_succ_list_gen]
            arg 1
            rw [blkR, show r = (r - 1) + 1 by omega]
          exact List.append_assoc _ _ _
        rw [decR_pushR0, decR, decR, decR_popKTail, decR, hc]
        simp only [rep0, List.replicate_succ, List.cons_append, List.nil_append,
            List.append_assoc]

theorem decR_bumpR (R : List Item) : decR (bumpR R) = bumpHead (decR R) := by
  unfold bumpR
  cases hp : popR1 R with
  | none => rw [decR_popR1_none R hp]; rfl
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [decR_popR1_some R d R1 hp, decR_pushRd]; rfl

theorem decL_segsToItems : ∀ (segs : List (ℕ × ℕ)) (acc : List Item),
    decL (segsToItems segs acc) = decSegs segs ++ decL acc
  | [], acc => rfl
  | (r, c) :: ss, acc => by
    unfold segsToItems; split
    · next hc =>
      rw [Nat.beq_eq] at hc; subst hc
      simpa [decSegs, HPow.hPow] using decL_segsToItems ss acc
    · simp [decL, decSegs, decL_segsToItems ss acc, List.append_assoc]

theorem decL_unpackClean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) :
    decL (unpackClean c0 segs bot) = decLState (.clean c0 segs bot) := by
  unfold unpackClean
  split
  · next hc => rw [Nat.beq_eq] at hc; subst hc; simp [decL, decLState, decL_segsToItems]
  · simp [decL, decLState, decL_segsToItems]

theorem packTail_spec : ∀ (items : List Item) (cur0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ),
    packTail cur0 items = some (segs, bot) →
    rep0 cur0 ++ decL items = decSegs segs ++ rep0 (bot + 2)
  | [], cur0, segs, bot, h => by
    unfold packTail at h; split at h
    · next hb =>
      have hge : 2 ≤ cur0 := Nat.ble_eq.mp hb
      cases h
      rw [show cur0 - 2 + 2 = cur0 by omega]; norm_all
    · cases h
  | .z c :: rest, cur0, segs, bot, h => by
    unfold packTail at h
    have ih := packTail_spec rest (cur0 + c) segs bot h
    rw [decL, ← List.append_assoc, ← rep0_add_split]; exact ih
  | .d v :: rest, cur0, segs, bot, h => by
    unfold packTail at h; split at h
    · next hb =>
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
      rcases hb with ⟨rfl, hge⟩
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        have ih := packTail_spec rest 0 ss b hp
        rw [hp] at h; cases h
        rw [rep0_zero, List.nil_append] at ih
        rw [decSegs_pushSeg]
        conv_lhs => rw [decL, show cur0 = (cur0 - 2) + 2 by omega]
        rw [ih]; norm_all
    · cases h
  | .k r c :: rest, cur0, segs, bot, h => by
    unfold packTail at h; split at h
    · next hc =>
      rw [Nat.beq_eq] at hc; subst hc
      simpa [decL, HPow.hPow] using packTail_spec rest cur0 segs bot h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        have ih := packTail_spec rest 0 ss b hp
        rw [hp] at h; cases h
        rw [rep0_zero, List.nil_append] at ih
        conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
        rw [ih]; norm_all

theorem packHead_spec : ∀ (items : List Item) (cur0 : ℕ) (ls : LState),
    packHead cur0 items = some ls →
    rep0 cur0 ++ decL items = decLState ls
  | [], _, _, h => by cases h
  | .z c :: rest, cur0, ls, h => by
    unfold packHead at h
    have ih := packHead_spec rest (cur0 + c) ls h
    rw [decL, ← List.append_assoc, ← rep0_add_split]; exact ih
  | .d v :: rest, cur0, ls, h => by
    unfold packHead at h; split at h
    · next hv =>
      rw [Nat.beq_eq] at hv; subst hv
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        rw [hp] at h; cases h
        have ih := packTail_spec rest 0 ss b hp
        rw [rep0_zero, List.nil_append] at ih
        simp [decL, decLState, ih]
    · cases h
  | .k r c :: rest, cur0, ls, h => by
    unfold packHead at h; split at h
    · next hc =>
      rw [Nat.beq_eq] at hc; subst hc
      simpa [decL, HPow.hPow] using packHead_spec rest cur0 ls h
    · next hc0 =>
      have hne : c ≠ 0 := fun heq => hc0 (Nat.beq_eq.mpr heq)
      cases hp : packTail 0 rest with
      | none => rw [hp] at h; cases h
      | some p =>
        rcases p with ⟨ss, b⟩
        rw [hp] at h; cases h
        have ih := packTail_spec rest 0 ss b hp
        rw [rep0_zero, List.nil_append] at ih
        conv_lhs => rw [decL, show c = (c - 1) + 1 by omega]
        rw [ih]; norm_all

-- ============================================================================
-- Section 5: Modular Transition Engine `rleStep` & Per-Mode Soundness
-- ============================================================================

structure RleFullState where
  mode : StackMode
  ls : LState
  R : List Item
  halted : Bool

def CanHalt (target_tm : Machine (Fin 2) (Fin 6)) (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg, (c [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone

omit [HasRleStackRules target_tm] in
theorem canHalt_of_stepStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [target_tm]⊢* c₂) (hc : CanHalt target_tm c₂) : CanHalt target_tm c₁ := by
  obtain ⟨cfg, h₂, hnone⟩ := hc
  exact ⟨cfg, stepStar_trans h h₂, hnone⟩

omit [HasRleStackRules target_tm] in
theorem canHalt_of_stepPlus {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [target_tm]⊢⁺ c₂) (hc : CanHalt target_tm c₂) : CanHalt target_tm c₁ :=
  canHalt_of_stepStar (stepPlus_stepStar h) hc

def evalRle (target_tm : Machine (Fin 2) (Fin 6)) (s : RleFullState) : Cfg (Fin 2) (Fin 6) :=
  evalStackCfg1 target_tm s.mode (decLState s.ls) (decR s.R)

def StateHalts (target_tm : Machine (Fin 2) (Fin 6)) (s : RleFullState) : Prop :=
  s.halted = true ∨ CanHalt target_tm (evalRle target_tm s)

omit [HasRleStackRules target_tm] in
theorem stateHalts_of_stepStar {c : Cfg (Fin 2) (Fin 6)} {s' : RleFullState}
    (hf : s'.halted = false)
    (hstep : c [target_tm]⊢* evalRle target_tm s')
    (hh : StateHalts target_tm s') : CanHalt target_tm c := by
  rcases hh with hh | hh
  · rw [hf] at hh; cases hh
  · exact canHalt_of_stepStar hstep hh

def isTopD1 : List Item → Bool
  | .d v :: _ => Nat.beq v 1
  | _ => false

def modeCanPack (m : StackMode) (items R : List Item) : Bool :=
  match m with
  | .B => R.isEmpty || isTopD1 items
  | .BR => R.isEmpty
  | .DR0 => true
  | .C => false

def minNat (a b : ℕ) : ℕ := if Nat.ble a b then a else b

theorem minNat_le_left (a b : ℕ) : minNat a b ≤ a := by
  unfold minNat; split
  · exact le_rfl
  · next h => have : ¬ a ≤ b := fun hab => h (Nat.ble_eq.mpr hab); omega

theorem minNat_le_right (a b : ℕ) : minNat a b ≤ b := by
  unfold minNat; split
  · next h => exact Nat.ble_eq.mp h
  · exact le_rfl

-- 5.1 Raw B
def stepRawB (items R : List Item) : RleFullState :=
  match R with
  | [] => ⟨.C, .raw (bumpL items), [], false⟩
  | .z c :: R1 => ⟨.B, .raw (pushL0 c items), R1, false⟩
  | _ =>
    match popR1 R with
    | none => ⟨.C, .raw (bumpL items), [], false⟩
    | some (d, R1) =>
      if Nat.beq d 0 then ⟨.B, .raw (pushL0 1 items), R1, false⟩
      else ⟨.BR, .raw items, pushR0 1 (pushRd (d - 1) R1), false⟩

theorem stepRawB_halts (items R : List Item) (hh : StateHalts target_tm (stepRawB items R)) :
    CanHalt target_tm (cfg_B target_tm (decL items) (decR R)) := by
  unfold stepRawB at hh
  cases R with
  | nil =>
    refine stateHalts_of_stepStar rfl ?_ hh
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      stepPlus_stepStar (rule_B_nil (decL items))
  | cons hd R1 =>
    cases hd with
    | z c =>
      refine stateHalts_of_stepStar rfl ?_ hh
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR] using
        rule_B_zeros_all (decL items) (decR R1) c
    | d v =>
      dsimp only at hh
      cases hp : popR1 (.d v :: R1) with
      | none => cases hp
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR]
          simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
            stepPlus_stepStar (rule_B_zero (decL items) (decR R2))
        · next hd0 =>
          have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR, show d = (d - 1) + 1 by omega]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0, decR_pushRd]
              using
            stepPlus_stepStar (rule_B_succ (d - 1) (decL items) (decR R2))
    | k r c =>
      dsimp only at hh
      cases hp : popR1 (.k r c :: R1) with
      | none =>
        rw [hp] at hh
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [decR_popR1_none _ hp]
        simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
          stepPlus_stepStar (rule_B_nil (decL items))
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR]
          simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
            stepPlus_stepStar (rule_B_zero (decL items) (decR R2))
        · next hd0 =>
          have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR, show d = (d - 1) + 1 by omega]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0, decR_pushRd]
              using
            stepPlus_stepStar (rule_B_succ (d - 1) (decL items) (decR R2))

-- 5.2 Raw BR
def stepRawBRPop (items R : List Item) : RleFullState :=
  match popR1 R with
  | none => ⟨.C, .raw (bumpL items), [], false⟩
  | some (d, R1) =>
    if Nat.beq d 0 then ⟨.BR, .raw (pushL0 1 items), R1, false⟩
    else if Nat.beq d 1 then ⟨.DR0, .raw items, bumpR R1, false⟩
    else ⟨.B, .raw (bumpL items), pushRd (d - 2) R1, false⟩

theorem stepRawBRPop_halts (items R : List Item) (hh : StateHalts target_tm (stepRawBRPop items
    R)) :
    CanHalt target_tm (cfg_BR target_tm (decL items) (decR R)) := by
  unfold stepRawBRPop at hh
  cases hp : popR1 R with
  | none =>
    rw [hp] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    rw [decR_popR1_none R hp]
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      stepPlus_stepStar (rule_BR_nil (decL items))
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [hp] at hh
    have hR := decR_popR1_some R d R1 hp
    dsimp only at hh; split at hh
    · next hd0 =>
      rw [Nat.beq_eq] at hd0; subst hd0
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hR]
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
        stepPlus_stepStar (rule_BR_zero (decL items) (decR R1))
    · next hd0 =>
      have hdne0 : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
      split at hh
      · next hd1 =>
        rw [Nat.beq_eq] at hd1; subst hd1
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [hR]
        simpa [evalRle, evalStackCfg1, decLState, decR_bumpR] using
          stepPlus_stepStar (rule_BR_one (decL items) (decR R1))
      · next hd1 =>
        have hdne1 : d ≠ 1 := fun h => hd1 (Nat.beq_eq.mpr h)
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [hR, show d = (d - 2) + 2 by omega]
        simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushRd]
            using
          stepPlus_stepStar (rule_BR_add_two (d - 2) (decL items) (decR R1))

def stepRawBR (items R : List Item) : RleFullState :=
  match R with
  | [] => ⟨.C, .raw (bumpL items), [], false⟩
  | .z c :: R1 => ⟨.BR, .raw (pushL0 c items), R1, false⟩
  | .k r m :: R1 =>
    if Nat.ble 1 m then
      match popL1 items with
      | some (a, L1) =>
        if Nat.beq a 0 then
          ⟨.BR, .raw (pushL0 3 (pushLd 1 (pushLk2 r (m - 1) (pushL0 r L1)))), R1, false⟩
        else stepRawBRPop items (.k r m :: R1)
      | none => stepRawBRPop items (.k r m :: R1)
    else ⟨.BR, .raw items, R1, false⟩
  | .d v :: R1 => stepRawBRPop items (.d v :: R1)

theorem stepRawBR_halts (items R : List Item) (hh : StateHalts target_tm (stepRawBR items R)) :
    CanHalt target_tm (cfg_BR target_tm (decL items) (decR R)) := by
  unfold stepRawBR at hh
  cases R with
  | nil =>
    refine stateHalts_of_stepStar rfl ?_ hh
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      stepPlus_stepStar (rule_BR_nil (decL items))
  | cons hd R1 =>
    cases hd with
    | z c =>
      refine stateHalts_of_stepStar rfl ?_ hh
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR] using
        rule_BR_zeros_all (decL items) (decR R1) c
    | d v => exact stepRawBRPop_halts items (.d v :: R1) hh
    | k r m =>
      dsimp only at hh; split at hh
      · next hm1 =>
        have hmge : 1 ≤ m := Nat.ble_eq.mp hm1
        cases hpL : popL1 items with
        | none =>
          rw [hpL] at hh
          exact stepRawBRPop_halts items (.k r m :: R1) hh
        | some pL =>
          rcases pL with ⟨a, L1⟩
          rw [hpL] at hh; dsimp only at hh; split at hh
          · next ha0 =>
            rw [Nat.beq_eq] at ha0; subst ha0
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [decL_popL1_some items 0 L1 hpL, decR, show m = (m - 1) + 1 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushL0,
                decL_pushLd,
              decL_pushLk2, List.append_assoc] using
              rule_BR_blkR_succ (m - 1) r (decL L1) (decR R1)
          · exact stepRawBRPop_halts items (.k r m :: R1) hh
      · next hm0 =>
        have hmeq : m = 0 := by
          have : ¬ 1 ≤ m := fun h => hm0 (Nat.ble_eq.mpr h); omega
        subst hmeq
        refine stateHalts_of_stepStar rfl ?_ hh
        exact ⟨0, rfl⟩

-- 5.3 Raw DR0
def stepRawDR0Atomic (items R : List Item) : RleFullState :=
  match popL1 items with
  | none => ⟨.C, .raw [.d 1], R, false⟩
  | some (a, L1) =>
    if Nat.beq a 0 then
      match items with
      | .z c :: Lrest => ⟨.DR0, .raw Lrest, pushR0 c R, false⟩
      | _ => ⟨.DR0, .raw L1, pushR0 1 R, false⟩
    else ⟨.C, .raw (pushLd (a - 1) L1), pushR0 1 R, false⟩

theorem stepRawDR0Atomic_halts (items R : List Item) (hh : StateHalts target_tm (stepRawDR0Atomic
    items R)) :
    CanHalt target_tm (cfg_DR0 target_tm (decL items) (decR R)) := by
  unfold stepRawDR0Atomic at hh
  cases hpL : popL1 items with
  | none =>
    rw [hpL] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    rw [decL_popL1_none items hpL]
    simpa [evalRle, evalStackCfg1, decLState, decL] using
      stepPlus_stepStar (rule_DR0_nil (decR R))
  | some pL =>
    rcases pL with ⟨a, L1⟩
    rw [hpL] at hh
    have hL := decL_popL1_some items a L1 hpL
    dsimp only at hh; split at hh
    · next ha0 =>
      rw [Nat.beq_eq] at ha0; subst ha0
      cases items with
      | nil => cases hpL
      | cons hd Lrest =>
        cases hd with
        | z c =>
          refine stateHalts_of_stepStar rfl ?_ hh
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushR0] using
            rule_DR0_zeros_all (decL Lrest) (decR R) c
        | d _ =>
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0] using
            stepPlus_stepStar (rule_DR0_zero (decL L1) (decR R))
        | k _ _ =>
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0] using
            stepPlus_stepStar (rule_DR0_zero (decL L1) (decR R))
    · next ha0 =>
      have hane : a ≠ 0 := fun h => ha0 (Nat.beq_eq.mpr h)
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hL, show a = (a - 1) + 1 by omega]
      simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushR0]
          using
        stepPlus_stepStar (rule_DR0_succ (a - 1) (decL L1) (decR R))

def stepRawDR0 (items R : List Item) : RleFullState :=
  match items with
  | [.z c] =>
    match R with
    | .d v1 :: .z q :: R2 =>
      if Nat.beq v1 1 then ⟨.DR0, .raw [.z (c + 3 * q)], .d 1 :: R2, false⟩
      else ⟨.BR, .raw [.z (c + 3)], R, false⟩
    | _ => ⟨.BR, .raw [.z (c + 3)], R, false⟩
  | _ => stepRawDR0Atomic items R

theorem stepRawDR0_halts (items R : List Item) (hh : StateHalts target_tm (stepRawDR0 items R)) :
    CanHalt target_tm (cfg_DR0 target_tm (decL items) (decR R)) := by
  unfold stepRawDR0 at hh
  rcases items with _ | ⟨hd1, _ | ⟨hd2, xs⟩⟩
  · exact stepRawDR0Atomic_halts [] R hh
  · cases hd1 with
    | z c =>
      have hbot : ∀ (hhb : StateHalts target_tm ⟨.BR, .raw [.z (c + 3)], R, false⟩),
          CanHalt target_tm (cfg_DR0 target_tm (decL [.z c]) (decR R)) := by
        intro hhb
        refine stateHalts_of_stepStar rfl ?_ hhb
        simpa [evalRle, evalStackCfg1, decLState, decL] using rule_DR0_bot c
            (decR R)
      rcases R with _ | ⟨r1, _ | ⟨r2, R2⟩⟩
      · exact hbot hh
      · cases r1 <;> exact hbot hh
      · cases r1 with
        | d v1 =>
          cases r2 with
          | z q =>
            dsimp only at hh; split at hh
            · next hv1 =>
              rw [Nat.beq_eq] at hv1; subst hv1
              refine stateHalts_of_stepStar rfl ?_ hh
              simpa [evalRle, evalStackCfg1, decLState, decL, decR] using
                rule_DR0_bot_zeros q c (decR R2)
            · exact hbot hh
          | _ => exact hbot hh
        | _ => exact hbot hh
    | d _ => exact stepRawDR0Atomic_halts _ R hh
    | k _ _ => exact stepRawDR0Atomic_halts _ R hh
  · cases hd1 <;> exact stepRawDR0Atomic_halts _ R hh

-- 5.4 Raw C
def stepRawCAtomic (items R : List Item) : RleFullState :=
  match popL1 items with
  | none => ⟨.DR0, .raw [], R, false⟩
  | some (a, L1) =>
    if Nat.beq a 0 then
      match popL1 L1 with
      | none => ⟨.C, .raw [], pushRd 1 R, false⟩
      | some (a1, L3) =>
        if Nat.beq a1 0 then ⟨.C, .raw (bumpL L3), pushRd 1 R, false⟩
        else if Nat.beq a1 1 then ⟨.C, .raw (bumpL (bumpL L3)), pushR0 1 (bumpR R), false⟩
        else ⟨.BR, .raw (pushLd (a1 - 2) L3), pushR0 1 (pushRd 1 R), false⟩
    else if Nat.beq a 1 then
      match popL1 L1 with
      | none => ⟨.B, .raw [.z 1], pushRd 1 R, false⟩
      | some (a1, L3) =>
        if Nat.beq a1 0 then ⟨.DR0, .raw L3, pushRd 2 R, false⟩
        else ⟨.C, .raw (pushLd (a1 - 1) L3), pushRd 2 R, false⟩
    else ⟨.C, .raw (pushLd a L1), R, true⟩

theorem stepRawCAtomic_halts (items R : List Item) (hh : StateHalts target_tm (stepRawCAtomic
    items R)) :
    CanHalt target_tm (cfg_C target_tm (decL items) (decR R)) := by
  unfold stepRawCAtomic at hh
  cases hp1 : popL1 items with
  | none =>
    rw [hp1] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    rw [decL_popL1_none items hp1]
    exact stepPlus_stepStar (rule_C_nil _)
  | some p1 =>
    rcases p1 with ⟨a, L1⟩
    rw [hp1] at hh
    have hL1 := decL_popL1_some items a L1 hp1
    dsimp only at hh; split at hh
    · next ha0 =>
      rw [Nat.beq_eq] at ha0; subst ha0
      cases hp2 : popL1 L1 with
      | none =>
        rw [hp2] at hh
        refine stateHalts_of_stepStar rfl ?_ hh
        rw [hL1, decL_popL1_none L1 hp2]
        simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRd] using
          stepPlus_stepStar (rule_C_zero_nil (decR R))
      | some p2 =>
        rcases p2 with ⟨a1, L3⟩
        rw [hp2] at hh
        have hL2 := decL_popL1_some L1 a1 L3 hp2
        dsimp only at hh; split at hh
        · next ha10 =>
          rw [Nat.beq_eq] at ha10; subst ha10
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL1, hL2]
          simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushRd]
              using
            stepPlus_stepStar (rule_C_zero_zero (decL L3) (decR R))
        · next ha10 =>
          have hne0 : a1 ≠ 0 := fun h => ha10 (Nat.beq_eq.mpr h)
          split at hh
          · next ha11 =>
            rw [Nat.beq_eq] at ha11; subst ha11
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2]
            simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushR0
                , decR_bumpR] using
              stepPlus_stepStar (rule_C_zero_one (decL L3) (decR R))
          · next ha11 =>
            have hne1 : a1 ≠ 1 := fun h => ha11 (Nat.beq_eq.mpr h)
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2, show a1 = (a1 - 2) + 2 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushR0
                , decR_pushRd] using
              stepPlus_stepStar (rule_C_zero_add_two (a1 - 2) (decL L3) (decR R))
    · next ha0 =>
      have hane0 : a ≠ 0 := fun h => ha0 (Nat.beq_eq.mpr h)
      split at hh
      · next ha1 =>
        rw [Nat.beq_eq] at ha1; subst ha1
        cases hp2 : popL1 L1 with
        | none =>
          rw [hp2] at hh
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hL1, decL_popL1_none L1 hp2]
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRd] using
            stepPlus_stepStar (rule_C_one_nil (decR R))
        | some p2 =>
          rcases p2 with ⟨a1, L3⟩
          rw [hp2] at hh
          have hL2 := decL_popL1_some L1 a1 L3 hp2
          dsimp only at hh; split at hh
          · next ha10 =>
            rw [Nat.beq_eq] at ha10; subst ha10
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2]
            simpa [evalRle, evalStackCfg1, decLState, decR_pushRd] using
              stepPlus_stepStar (rule_C_one_zero (decL L3) (decR R))
          · next ha10 =>
            have hne0 : a1 ≠ 0 := fun h => ha10 (Nat.beq_eq.mpr h)
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hL1, hL2, show a1 = (a1 - 1) + 1 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushLd,
                decR_pushRd] using
              stepPlus_stepStar (rule_C_one_succ (a1 - 1) (decL L3) (decR R))
      · next ha1 =>
        have hane1 : a ≠ 1 := fun h => ha1 (Nat.beq_eq.mpr h)
        rw [hL1, show a = (a - 2) + 2 by omega]
        obtain ⟨cfg', hstep, hnone⟩ :=
          rule_C_add_two_halt (target_tm := target_tm) (a - 2) (decL L1) (decR R)
        exact ⟨cfg', stepPlus_stepStar hstep, hnone⟩

def stepRawC (items R : List Item) : RleFullState :=
  match items with
  | .z cz :: .k r m :: L2 =>
    if Nat.beq cz 1 then ⟨.C, .raw (pushL0 1 L2), pushRk2 r m R, false⟩
    else stepRawCAtomic items R
  | .z cz :: .d v1 :: L2 =>
    if Nat.ble 4 cz && Nat.beq v1 1 then
      ⟨.C, .raw (pushL0 1 L2), pushRk2 (cz - 3) 1 R, false⟩
    else stepRawCAtomic items R
  | [.z cz] =>
    if Nat.ble 4 cz then ⟨.DR0, .raw [], pushRk2 (cz - 4) 1 R, false⟩
    else stepRawCAtomic items R
  | _ => stepRawCAtomic items R

theorem stepRawC_halts (items R : List Item) (hh : StateHalts target_tm (stepRawC items R)) :
    CanHalt target_tm (cfg_C target_tm (decL items) (decR R)) := by
  unfold stepRawC at hh
  rcases items with _ | ⟨hd1, rest1⟩
  · exact stepRawCAtomic_halts [] R hh
  · cases hd1 with
    | z cz =>
      rcases rest1 with _ | ⟨hd2, L2⟩
      · dsimp only at hh; split at hh
        · next h4 =>
          have hge4 : 4 ≤ cz := Nat.ble_eq.mp h4
          refine stateHalts_of_stepStar rfl ?_ hh
          have heq : decL [.z cz] = rep0 ((cz - 4) + 4) := by
            rw [decL, decL, List.append_nil, show cz - 4 + 4 = cz by omega]
          rw [heq]
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRk2,
            HPow.hPow, List.append_eq] using
            rule_C_bot_four (cz - 4) (decR R)
        · exact stepRawCAtomic_halts [.z cz] R hh
      · cases hd2 with
        | k r m =>
          dsimp only at hh; split at hh
          · next hcz =>
            rw [Nat.beq_eq] at hcz; subst hcz
            refine stateHalts_of_stepStar rfl ?_ hh
            simpa [evalRle, evalStackCfg1, decLState, decL, decL_pushL0,
                decR_pushRk2] using
              rule_C_blkL_pow m r (decL L2) (decR R)
          · exact stepRawCAtomic_halts _ R hh
        | d v1 =>
          dsimp only at hh; split at hh
          · next hb =>
            simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hb
            rcases hb with ⟨hge4, rfl⟩
            refine stateHalts_of_stepStar rfl ?_ hh
            have heq : decL (.z cz :: .d 1 :: L2) = rep0 ((cz - 3) + 3) ++ 1 :: decL L2 := by
              rw [decL, decL, show cz - 3 + 3 = cz by omega]
            rw [heq]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushL0,
                decR_pushRk2,
              HPow.hPow, List.append_eq] using
              rule_C_r_add_three (cz - 3) (decL L2) (decR R)
          · exact stepRawCAtomic_halts _ R hh
        | z _ => exact stepRawCAtomic_halts _ R hh
    | d _ => exact stepRawCAtomic_halts _ R hh
    | k _ _ => exact stepRawCAtomic_halts _ R hh

-- 5.5 Clean B
def stepCleanBPop (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match popR1 R with
  | none => ⟨.B, .raw (unpackClean c0 segs bot), R, false⟩
  | some (d, R1) =>
    if Nat.beq d 0 then ⟨.B, .clean (c0 + 1) segs bot, R1, false⟩
    else ⟨.BR, .clean c0 segs bot, pushR0 1 (pushRd (d - 1) R1), false⟩

theorem stepCleanBPop_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts target_tm (stepCleanBPop c0 segs bot R)) :
    CanHalt target_tm (cfg_B target_tm (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanBPop at hh
  cases hp : popR1 R with
  | none =>
    rw [hp] at hh
    refine stateHalts_of_stepStar rfl ?_ hh
    simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [hp] at hh
    have hR := decR_popR1_some R d R1 hp
    dsimp only at hh; split at hh
    · next hd0 =>
      rw [Nat.beq_eq] at hd0; subst hd0
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hR]
      have heq : 0 :: decLState (.clean c0 segs bot) = decLState (.clean (c0 + 1) segs bot) := by
        norm_all
      simpa [evalRle, evalStackCfg1, ← heq] using
        stepPlus_stepStar (rule_B_zero (decLState (.clean c0 segs bot)) (decR R1))
    · next hd0 =>
      have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
      refine stateHalts_of_stepStar rfl ?_ hh
      rw [hR, show d = (d - 1) + 1 by omega]
      simpa [evalRle, evalStackCfg1, decR_pushR0, decR_pushRd] using
        stepPlus_stepStar (rule_B_succ (d - 1) (decLState (.clean c0 segs bot)) (decR R1))

def stepCleanB (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then
      ⟨.B, .clean 1 (pushSeg 0 (bot - 1) (pushSeg (c0 - 1) 1 segs)) 0, [], false⟩
    else ⟨.B, .raw (unpackClean c0 segs bot), [], false⟩
  | .z cz :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.ble 1 bot && Nat.beq cz 1 then
      let q := minNat cnt bot
      if Nat.ble 1 q then
        let Rnew := if Nat.beq cnt q then .z 1 :: Rrem else .z 1 :: .k r (cnt - q) :: Rrem
        ⟨.B, .clean 0 (pushSeg (r + 3) q segs) (bot - q), Rnew, false⟩
      else ⟨.B, .clean (c0 + cz) segs bot, .k r cnt :: Rrem, false⟩
    else ⟨.B, .clean (c0 + cz) segs bot, .k r cnt :: Rrem, false⟩
  | .z cz :: R1 =>
    ⟨.B, .clean (c0 + cz) segs bot, R1, false⟩
  | .d v1 :: .d v2 :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.beq v1 1 && Nat.beq v2 1 then
      let q := minNat cnt (bot / (r + 1))
      if Nat.ble 1 q then
        let Rnew := if Nat.beq cnt q then .d 1 :: .d 1 :: Rrem else .d 1 :: .d 1 :: .k r (cnt - q)
            :: Rrem
        ⟨.B, .clean 0 (pushSeg (4 * r + 3) q segs) (bot - q * (r + 1)), Rnew, false⟩
      else ⟨.BR, .clean c0 segs bot, pushR0 1 (pushRd 0 (.d v2 :: .k r cnt :: Rrem)), false⟩
    else stepCleanBPop c0 segs bot (.d v1 :: .d v2 :: .k r cnt :: Rrem)
  | _ => stepCleanBPop c0 segs bot R

theorem stepCleanB_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts target_tm (stepCleanB c0 segs bot R)) :
    CanHalt target_tm (cfg_B target_tm (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanB at hh
  rcases R with _ | ⟨hd1, R1⟩
  · dsimp only at hh; split at hh
    · next hb =>
      simp only [Bool.and_eq_true, Nat.ble_eq] at hb
      rcases hb with ⟨hc0, hbot⟩
      refine stateHalts_of_stepStar rfl ?_ hh
      have h1 := clean_RNIL_one (target_tm := target_tm) .B (Or.inl rfl) (c0 - 1) segs (bot - 1)
      have h2 := clean_RNIL_zero_pow (target_tm := target_tm) (bot - 1) (pushSeg (c0 - 1) 1 segs) 0
      rw [show c0 - 1 + 1 = c0 by omega, show bot - 1 + 1 = bot by omega] at h1
      rw [show 0 + (bot - 1) = bot - 1 by omega] at h2
      exact stepStar_trans h1 h2
    · refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  · cases hd1 with
    | z cz =>
      have h_zonly : ∀ (Rtail : List Item)
          (hhz : StateHalts target_tm ⟨.B, .clean (c0 + cz) segs bot, Rtail, false⟩),
          CanHalt target_tm (cfg_B target_tm (decLState (.clean c0 segs bot)) (decR (.z cz ::
              Rtail))) := by
        intro Rtail hhz
        refine stateHalts_of_stepStar rfl ?_ hhz
        have hstep := rule_B_zeros_all (target_tm := target_tm)
            (decLState (.clean c0 segs bot)) (decR Rtail) cz
        have heq : rep0 cz ++ decLState (.clean c0 segs bot) =
            decLState (.clean (c0 + cz) segs bot) := by
          rw [Nat.add_comm c0 cz]; norm_all
        rw [heq] at hstep
        exact hstep
      rcases R1 with _ | ⟨hd2, Rrem⟩
      · exact h_zonly [] hh
      · cases hd2 with
        | k r cnt =>
          dsimp only at hh; split at hh
          · next hb =>
            simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
            rcases hb with ⟨⟨rfl, hbot⟩, rfl⟩
            split at hh
            · next hq1 =>
              set q := minNat cnt bot
              have hqcnt : q ≤ cnt := minNat_le_left cnt bot
              have hqbot : q ≤ bot := minNat_le_right cnt bot
              refine stateHalts_of_stepStar rfl ?_ hh
              have hstep := clean_P1_pow (target_tm := target_tm) q r segs (bot - q)
                  ((blkR r) ^ (cnt - q) ++ decR Rrem)
              rw [show bot - q + q = bot by omega] at hstep
              have heqR1 : 0 :: ((blkR r) ^ q ++ ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                  decR (.z 1 :: .k r cnt :: Rrem) := by
                rw [← List.append_assoc, ← list_pow_add, show q + (cnt - q) = cnt by omega]
                norm_all
              have heqR2 : (0 :: ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                  decR (if Nat.beq cnt q then .z 1 :: Rrem else .z 1 :: .k r (cnt - q) :: Rrem) :=
                      by
                split
                · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; norm_all
                · norm_all
              rw [heqR1, heqR2] at hstep
              exact hstep
            · exact h_zonly _ hh
          · exact h_zonly _ hh
        | _ => exact h_zonly _ hh
    | d v1 =>
      rcases R1 with _ | ⟨hd2, _ | ⟨hd3, Rrem⟩⟩
      · exact stepCleanBPop_halts c0 segs bot _ hh
      · cases hd2 <;> exact stepCleanBPop_halts c0 segs bot _ hh
      · cases hd2 with
        | d v2 =>
          cases hd3 with
          | k r cnt =>
            dsimp only at hh; split at hh
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq] at hb
              rcases hb with ⟨⟨rfl, rfl⟩, rfl⟩
              split at hh
              · next hq1 =>
                set q := minNat cnt (bot / (r + 1))
                have hqcnt : q ≤ cnt := minNat_le_left cnt _
                have hqdiv : q ≤ bot / (r + 1) := minNat_le_right cnt _
                have hqmul : q * (r + 1) ≤ bot :=
                  Nat.le_trans (Nat.mul_le_mul_right (r + 1) hqdiv) (Nat.div_mul_le_self bot (r +
                      1))
                refine stateHalts_of_stepStar rfl ?_ hh
                have hstep := clean_P2_pow (target_tm := target_tm) q r segs (bot - q * (r + 1))
                    ((blkR r) ^ (cnt - q) ++ decR Rrem)
                rw [show bot - q * (r + 1) + q * (r + 1) = bot by omega] at hstep
                have heqR1 : 1 :: 1 :: ((blkR r) ^ q ++ ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                    decR (.d 1 :: .d 1 :: .k r cnt :: Rrem) := by
                  rw [← List.append_assoc, ← list_pow_add, show q + (cnt - q) = cnt by omega]
                  norm_all
                have heqR2 : (1 :: 1 :: ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                    decR (if Nat.beq cnt q then .d 1 :: .d 1 :: Rrem else .d 1 :: .d 1 :: .k r
                        (cnt - q) :: Rrem) := by
                  split
                  · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; norm_all
                  · norm_all
                rw [heqR1, heqR2] at hstep
                exact hstep
              · refine stateHalts_of_stepStar rfl ?_ hh
                simpa [evalRle, evalStackCfg1, decR_pushR0, decR_pushRd, decR]
                    using
                  stepPlus_stepStar (rule_B_succ 0 (decLState (.clean 0 segs bot)) (decR (.d 1 ::
                      .k r cnt :: Rrem)))
            · exact stepCleanBPop_halts c0 segs bot _ hh
          | _ => exact stepCleanBPop_halts c0 segs bot _ hh
        | _ => exact stepCleanBPop_halts c0 segs bot _ hh
    | k _ _ => exact stepCleanBPop_halts c0 segs bot _ hh

-- 5.6 Clean BR
def stepCleanBR (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then
      ⟨.B, .clean 1 (pushSeg 0 (bot - 1) (pushSeg (c0 - 1) 1 segs)) 0, [], false⟩
    else ⟨.BR, .raw (unpackClean c0 segs bot), [], false⟩
  | .z cz :: R1 =>
    ⟨.BR, .clean (c0 + cz) segs bot, R1, false⟩
  | .k r m :: R1 =>
    if Nat.ble 1 m && Nat.ble 1 c0 && Nat.ble 3 (r + c0) then
      ⟨.BR, .clean 3 (pushSeg r (m - 1) (pushSeg (r + c0 - 3) 1 segs)) bot, R1, false⟩
    else ⟨.BR, .raw (unpackClean c0 segs bot), .k r m :: R1, false⟩
  | .d v :: R1 =>
    match popR1 (.d v :: R1) with
    | none => ⟨.BR, .raw (unpackClean c0 segs bot), .d v :: R1, false⟩
    | some (d, R2) =>
      if Nat.beq d 0 then ⟨.BR, .clean (c0 + 1) segs bot, R2, false⟩
      else if Nat.beq d 1 then ⟨.DR0, .clean c0 segs bot, bumpR R2, false⟩
      else if Nat.ble 3 c0 then
        ⟨.B, .clean 0 (pushSeg (c0 - 3) 1 segs) bot, pushRd (d - 2) R2, false⟩
      else ⟨.BR, .raw (unpackClean c0 segs bot), .d v :: R1, false⟩

theorem stepCleanBR_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts target_tm (stepCleanBR c0 segs bot R)) :
    CanHalt target_tm (cfg_BR target_tm (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanBR at hh
  rcases R with _ | ⟨hd1, R1⟩
  · dsimp only at hh; split at hh
    · next hb =>
      simp only [Bool.and_eq_true, Nat.ble_eq] at hb
      rcases hb with ⟨hc0, hbot⟩
      refine stateHalts_of_stepStar rfl ?_ hh
      have h1 := clean_RNIL_one (target_tm := target_tm) .BR (Or.inr rfl) (c0 - 1) segs (bot - 1)
      have h2 := clean_RNIL_zero_pow (target_tm := target_tm) (bot - 1) (pushSeg (c0 - 1) 1 segs) 0
      rw [show c0 - 1 + 1 = c0 by omega, show bot - 1 + 1 = bot by omega] at h1
      rw [show 0 + (bot - 1) = bot - 1 by omega] at h2
      exact stepStar_trans h1 h2
    · refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  · cases hd1 with
    | z cz =>
      refine stateHalts_of_stepStar rfl ?_ hh
      have hstep := rule_BR_zeros_all (target_tm := target_tm)
          (decLState (.clean c0 segs bot)) (decR R1) cz
      have heq : rep0 cz ++ decLState (.clean c0 segs bot) =
          decLState (.clean (c0 + cz) segs bot) := by
        rw [Nat.add_comm c0 cz]; norm_all
      rw [heq] at hstep
      exact hstep
    | k r m =>
      dsimp only at hh; split at hh
      · next hb =>
        simp only [Bool.and_eq_true, Nat.ble_eq] at hb
        rcases hb with ⟨⟨hm, hc0⟩, hrc⟩
        refine stateHalts_of_stepStar rfl ?_ hh
        have heqL0 : decLState (.clean c0 segs bot) =
            0 :: (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) := by
          conv_lhs => rw [decLState, show c0 = (c0 - 1) + 1 by omega]
          norm_all
        have hstep := rule_BR_blkR_succ (target_tm := target_tm) (m - 1) r
            (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) (decR R1)
        have heqR : decR (.k r m :: R1) = (blkR r) ^ ((m - 1) + 1) ++ decR R1 := by
          rw [decR, show m - 1 + 1 = m by omega]
        have heqL1 : rep0 3 ++ 1 :: ((blkL r) ^ (m - 1) ++ (rep0 r ++ (rep0 (c0 - 1) ++ 1 ::
            (decSegs segs ++ rep0 (bot + 2))))) =
            decLState (.clean 3 (pushSeg r (m - 1) (pushSeg (r + c0 - 3) 1 segs)) bot) := by
          have hmerge : rep0 r ++ (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
              rep0 ((r + c0 - 3) + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)) := by
            rw [← List.append_assoc, ← rep0_add_split, show r + (c0 - 1) = (r + c0 - 3) + 2 by
                omega]
          rw [hmerge]
          norm_all
        dsimp only [evalRle, evalStackCfg1]
        rw [heqL0, heqR, ← heqL1]
        exact hstep
      · refine stateHalts_of_stepStar rfl ?_ hh
        simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
    | d v =>
      dsimp only at hh
      cases hp : popR1 (.d v :: R1) with
      | none => cases hp
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          refine stateHalts_of_stepStar rfl ?_ hh
          rw [hR]
          have heq : 0 :: decLState (.clean c0 segs bot) = decLState (.clean (c0 + 1) segs bot) :=
              by
            norm_all
          simpa [evalRle, evalStackCfg1, ← heq] using
            stepPlus_stepStar (rule_BR_zero (decLState (.clean c0 segs bot)) (decR R2))
        · next hd0 =>
          have hdne0 : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          split at hh
          · next hd1 =>
            rw [Nat.beq_eq] at hd1; subst hd1
            refine stateHalts_of_stepStar rfl ?_ hh
            rw [hR]
            simpa [evalRle, evalStackCfg1, decR_bumpR] using
              stepPlus_stepStar (rule_BR_one (decLState (.clean c0 segs bot)) (decR R2))
          · next hd1 =>
            have hdne1 : d ≠ 1 := fun h => hd1 (Nat.beq_eq.mpr h)
            split at hh
            · next hc3 =>
              have hcge : 3 ≤ c0 := Nat.ble_eq.mp hc3
              refine stateHalts_of_stepStar rfl ?_ hh
              rw [hR, show d = (d - 2) + 2 by omega]
              have hstep := stepPlus_stepStar (rule_BR_add_two (target_tm := target_tm) (d - 2)
                  (decLState (.clean c0 segs bot)) (decR R2))
              have heq : bumpHead (decLState (.clean c0 segs bot)) =
                  decLState (.clean 0 (pushSeg (c0 - 3) 1 segs) bot) := by
                conv_lhs => rw [decLState, show c0 = (c0 - 3) + 3 by omega]
                norm_all
              rw [heq] at hstep
              simpa [evalRle, evalStackCfg1, decR_pushRd] using hstep
            · refine stateHalts_of_stepStar rfl ?_ hh
              simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

-- 5.7 Clean DR0
def stepCleanDR0 (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  if Nat.ble 1 bot then
    match R with
    | .d v1 :: .z rz :: R2 =>
      if Nat.beq v1 1 then
        let q := minNat rz bot
        if Nat.ble 1 q then
          let Rnew := if Nat.beq rz q then .d 1 :: R2 else .d 1 :: .z (rz - q) :: R2
          ⟨.DR0, .clean (c0 + 4 * q) segs (bot - q), Rnew, false⟩
        else ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
      else ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
    | _ => ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
  else ⟨.DR0, .raw (unpackClean c0 segs bot), R, false⟩

theorem stepCleanDR0_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (hh : StateHalts target_tm (stepCleanDR0 c0 segs bot R)) :
    CanHalt target_tm (cfg_DR0 target_tm (decLState (.clean c0 segs bot)) (decR R)) := by
  unfold stepCleanDR0 at hh
  split at hh
  · next hbot =>
    have hbge : 1 ≤ bot := Nat.ble_eq.mp hbot
    have h_one : ∀ (hh1 : StateHalts target_tm ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩),
        CanHalt target_tm (cfg_DR0 target_tm (decLState (.clean c0 segs bot)) (decR R)) := by
      intro hh1
      refine stateHalts_of_stepStar rfl ?_ hh1
      have hstep := clean_DR0_one (target_tm := target_tm) c0 segs (bot - 1) (decR R)
      rw [show bot - 1 + 1 = bot by omega] at hstep
      exact hstep
    rcases R with _ | ⟨r1, _ | ⟨r2, R2⟩⟩
    · exact h_one hh
    · cases r1 <;> exact h_one hh
    · cases r1 with
      | d v1 =>
        cases r2 with
        | z rz =>
          dsimp only at hh; split at hh
          · next hv1 =>
            rw [Nat.beq_eq] at hv1; subst hv1
            split at hh
            · next hq1 =>
              set q := minNat rz bot
              have hqrz : q ≤ rz := minNat_le_left rz bot
              have hqbot : q ≤ bot := minNat_le_right rz bot
              refine stateHalts_of_stepStar rfl ?_ hh
              have hstep := clean_DR0_zeros (target_tm := target_tm) q c0 segs (bot - q)
                  (rep0 (rz - q) ++ decR R2)
              rw [show bot - q + q = bot by omega] at hstep
              have heqR1 : 1 :: (rep0 q ++ (rep0 (rz - q) ++ decR R2)) =
                  decR (.d 1 :: .z rz :: R2) := by
                rw [← List.append_assoc, ← rep0_add_split, show q + (rz - q) = rz by omega]
                norm_all
              have heqR2 : (1 :: (rep0 (rz - q) ++ decR R2)) =
                  decR (if Nat.beq rz q then .d 1 :: R2 else .d 1 :: .z (rz - q) :: R2) := by
                split
                · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; norm_all
                · norm_all
              rw [heqR1, heqR2] at hstep
              exact hstep
            · exact h_one hh
          · exact h_one hh
        | _ => exact h_one hh
      | _ => exact h_one hh
  · refine stateHalts_of_stepStar rfl ?_ hh
    simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

-- 5.8 Top-Level Dispatch `rleStep`
def tryPack (m : StackMode) (items R : List Item) : Option LState :=
  if modeCanPack m items R then
    match packHead 0 items with
    | some (LState.clean c0 segs bot) =>
      if Nat.ble 1 bot then some (LState.clean c0 segs bot) else none
    | _ => none
  else none

theorem tryPack_spec (m : StackMode) (items R : List Item) (ls' : LState)
    (h : tryPack m items R = some ls') : decL items = decLState ls' := by
  unfold tryPack at h
  split at h
  · cases hph : packHead 0 items with
    | none => rw [hph] at h; cases h
    | some l0 =>
      rw [hph] at h
      cases l0 with
      | raw _ => cases h
      | clean c0 segs bot =>
        dsimp only at h; split at h
        · cases h
          have hspec := packHead_spec items 0 (LState.clean c0 segs bot) hph
          simpa using hspec
        · cases h
  · cases h

def rleStep (s : RleFullState) : RleFullState :=
  match s.ls with
  | .raw items =>
    match tryPack s.mode items s.R with
    | some ls' => ⟨s.mode, ls', s.R, false⟩
    | none =>
      match s.mode with
      | .B => stepRawB items s.R
      | .BR => stepRawBR items s.R
      | .DR0 => stepRawDR0 items s.R
      | .C => stepRawC items s.R
  | .clean c0 segs bot =>
    match s.mode with
    | .B => stepCleanB c0 segs bot s.R
    | .BR => stepCleanBR c0 segs bot s.R
    | .DR0 => stepCleanDR0 c0 segs bot s.R
    | .C => ⟨.C, .raw (unpackClean c0 segs bot), s.R, false⟩

theorem rleStep_halts (s : RleFullState) (hh : StateHalts target_tm (rleStep s)) :
    CanHalt target_tm (evalRle target_tm s) := by
  rcases s with ⟨mode, ls, R, halted⟩
  unfold rleStep at hh
  dsimp only at hh
  cases ls with
  | raw items =>
    dsimp only at hh
    cases hpk : tryPack mode items R with
    | some ls' =>
      rw [hpk] at hh
      refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, decLState, tryPack_spec mode items R ls' hpk]
    | none =>
      rw [hpk] at hh
      cases mode with
      | B => exact stepRawB_halts items R hh
      | BR => exact stepRawBR_halts items R hh
      | DR0 => exact stepRawDR0_halts items R hh
      | C => exact stepRawC_halts items R hh
  | clean c0 segs bot =>
    dsimp only at hh
    cases mode with
    | B => exact stepCleanB_halts c0 segs bot R hh
    | BR => exact stepCleanBR_halts c0 segs bot R hh
    | DR0 => exact stepCleanDR0_halts c0 segs bot R hh
    | C =>
      refine stateHalts_of_stepStar rfl ?_ hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

-- ============================================================================
-- Section 6: Strict Evaluation + 19 Checkpointed 500-Step Chunks (`9,500 > 9,101`)
-- ============================================================================

def strictNat {α : Type*} (n : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn (Nat.add n 1) (f 0) (fun m => f m)

@[simp] theorem strictNat_eq {α : Type*} (n : ℕ) (f : ℕ → α) :
    strictNat n f = f n := rfl

def strictItem {α : Type*} (it : Item) (f : Item → α) : α :=
  match it with
  | .z c => strictNat c (fun c' => f (.z c'))
  | .d v => strictNat v (fun v' => f (.d v'))
  | .k r c => strictNat r (fun r' => strictNat c (fun c' => f (.k r' c')))

@[simp] theorem strictItem_eq {α : Type*} (it : Item) (f : Item → α) :
    strictItem it f = f it := by
  cases it <;> simp [strictItem]

def strictItems {α : Type*} : List Item → (List Item → α) → α
  | [], f => f []
  | x :: xs, f => strictItem x (fun x' => strictItems xs (fun xs' => f (x' :: xs')))

@[simp] theorem strictItems_eq {α : Type*} :
    ∀ (xs : List Item) (f : List Item → α), strictItems xs f = f xs
  | [], _ => rfl
  | x :: xs, f => by simp [strictItems, strictItems_eq xs]

def strictSegs {α : Type*} : List (ℕ × ℕ) → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | (r, c) :: xs, f =>
    strictNat r (fun r' => strictNat c (fun c' => strictSegs xs (fun xs' => f ((r', c') :: xs'))))

@[simp] theorem strictSegs_eq {α : Type*} :
    ∀ (xs : List (ℕ × ℕ)) (f : List (ℕ × ℕ) → α), strictSegs xs f = f xs
  | [], _ => rfl
  | (r, c) :: xs, f => by simp [strictSegs, strictSegs_eq xs]

def strictLState {α : Type*} (ls : LState) (f : LState → α) : α :=
  match ls with
  | .raw items => strictItems items (fun items' => f (.raw items'))
  | .clean c0 segs bot =>
    strictNat c0 (fun c0' =>
      strictSegs segs (fun segs' =>
        strictNat bot (fun bot' => f (.clean c0' segs' bot'))))

@[simp] theorem strictLState_eq {α : Type*} (ls : LState) (f : LState → α) :
    strictLState ls f = f ls := by
  cases ls <;> simp [strictLState]

def strictMode {α : Type*} (m : StackMode) (f : StackMode → α) : α :=
  match m with
  | .B => f .B
  | .BR => f .BR
  | .DR0 => f .DR0
  | .C => f .C

@[simp] theorem strictMode_eq {α : Type*} (m : StackMode) (f : StackMode → α) :
    strictMode m f = f m := by
  cases m <;> rfl

def strictState {α : Type*} (s : RleFullState) (f : RleFullState → α) : α :=
  match s with
  | ⟨m, ls, R, h⟩ =>
    strictMode m (fun m' =>
      strictLState ls (fun ls' =>
        strictItems R (fun R' =>
          Bool.casesOn h (f ⟨m', ls', R', false⟩) (f ⟨m', ls', R', true⟩))))

@[simp] theorem strictState_eq {α : Type*} (s : RleFullState) (f : RleFullState → α) :
    strictState s f = f s := by
  rcases s with ⟨m, ls, R, h⟩
  cases h <;> simp [strictState]

def strictItems4 {α : Type*} : List Item → (List Item → α) → α
  | [], f => f []
  | [x0], f => strictItem x0 (fun y0 => f [y0])
  | [x0, x1], f => strictItem x0 (fun y0 => strictItem x1 (fun y1 => f [y0, y1]))
  | [x0, x1, x2], f =>
    strictItem x0 (fun y0 => strictItem x1 (fun y1 => strictItem x2 (fun y2 => f [y0, y1, y2])))
  | x0 :: x1 :: x2 :: x3 :: xs, f =>
    strictItem x0 (fun y0 => strictItem x1 (fun y1 => strictItem x2 (fun y2 =>
      strictItem x3 (fun y3 => f (y0 :: y1 :: y2 :: y3 :: xs)))))

@[simp] theorem strictItems4_eq {α : Type*} (xs : List Item) (f : List Item → α) :
    strictItems4 xs f = f xs := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;> simp [strictItems4]

def strictSegs3 {α : Type*} : List (ℕ × ℕ) → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | [(r0, c0)], f => strictNat r0 (fun r0' => strictNat c0 (fun c0' => f [(r0', c0')]))
  | [(r0, c0), (r1, c1)], f =>
    strictNat r0 (fun r0' => strictNat c0 (fun c0' =>
      strictNat r1 (fun r1' => strictNat c1 (fun c1' => f [(r0', c0'), (r1', c1')]))))
  | (r0, c0) :: (r1, c1) :: (r2, c2) :: xs, f =>
    strictNat r0 (fun r0' => strictNat c0 (fun c0' =>
      strictNat r1 (fun r1' => strictNat c1 (fun c1' =>
        strictNat r2 (fun r2' => strictNat c2 (fun c2' =>
          f ((r0', c0') :: (r1', c1') :: (r2', c2') :: xs)))))))

@[simp] theorem strictSegs3_eq {α : Type*} (xs : List (ℕ × ℕ)) (f : List (ℕ × ℕ) → α) :
    strictSegs3 xs f = f xs := by
  rcases xs with _ | ⟨⟨r0, c0⟩, _ | ⟨⟨r1, c1⟩, _ | ⟨⟨r2, c2⟩, xs⟩⟩⟩ <;> simp [strictSegs3]

def strictStateFast {α : Type*} (s : RleFullState) (f : RleFullState → α) : α :=
  match s with
  | ⟨m, .raw items, R, h⟩ =>
    strictMode m (fun m' =>
      strictItems4 items (fun items' =>
        strictItems4 R (fun R' =>
          Bool.casesOn h (f ⟨m', .raw items', R', false⟩) (f ⟨m', .raw items', R', true⟩))))
  | ⟨m, .clean c0 segs bot, R, h⟩ =>
    strictMode m (fun m' =>
      strictNat c0 (fun c0' =>
        strictSegs3 segs (fun segs' =>
          strictNat bot (fun bot' =>
            strictItems4 R (fun R' =>
              Bool.casesOn h (f ⟨m', .clean c0' segs' bot', R', false⟩)
                             (f ⟨m', .clean c0' segs' bot', R', true⟩))))))

@[simp] theorem strictStateFast_eq {α : Type*} (s : RleFullState) (f : RleFullState → α) :
    strictStateFast s f = f s := by
  rcases s with ⟨m, (_ | ⟨c0, segs, bot⟩), R, h⟩ <;> cases h <;> simp [strictStateFast]

def runStepsInner (n : ℕ) (s : RleFullState) : RleFullState :=
  Nat.rec
    (fun s => s)
    (fun _ ih s =>
      match s with
      | ⟨m, ls, R, true⟩ => ⟨m, ls, R, true⟩
      | ⟨m, ls, R, false⟩ => strictStateFast (rleStep ⟨m, ls, R, false⟩) ih)
    n s

theorem runStepsInner_succ (n : ℕ) (s : RleFullState) :
    runStepsInner (n + 1) s =
      match s with
      | ⟨m, ls, R, true⟩ => ⟨m, ls, R, true⟩
      | ⟨m, ls, R, false⟩ => strictStateFast (rleStep ⟨m, ls, R, false⟩) (runStepsInner n) := rfl

theorem runStepsInner_halts : ∀ (n : ℕ) (s : RleFullState),
    StateHalts target_tm (runStepsInner n s) → StateHalts target_tm s
  | 0, _, h => h
  | n + 1, ⟨m, ls, R, true⟩, _ => Or.inl rfl
  | n + 1, ⟨m, ls, R, false⟩, h => by
    rw [runStepsInner_succ] at h
    dsimp only at h
    rw [strictStateFast_eq] at h
    exact Or.inr (rleStep_halts ⟨m, ls, R, false⟩ (runStepsInner_halts n (rleStep ⟨m, ls, R,
        false⟩) h))

def runBatches (b : ℕ) (s : RleFullState) : RleFullState :=
  Nat.rec
    (fun s => s)
    (fun _ ih s => strictState (runStepsInner 25 s) ih)
    b s

theorem runBatches_succ (b : ℕ) (s : RleFullState) :
    runBatches (b + 1) s = strictState (runStepsInner 25 s) (runBatches b) := rfl

theorem runBatches_halts : ∀ (b : ℕ) (s : RleFullState),
    StateHalts target_tm (runBatches b s) → StateHalts target_tm s
  | 0, _, h => h
  | b + 1, s, h => by
    rw [runBatches_succ, strictState_eq] at h
    exact runStepsInner_halts 25 s (runBatches_halts b (runStepsInner 25 s) h)

def runSteps (s : RleFullState) : RleFullState :=
  runBatches 20 s

theorem runSteps_halts (s : RleFullState) (h : StateHalts target_tm (runSteps s)) :
    StateHalts target_tm s :=
  runBatches_halts 20 s h

theorem chunk_back {s₁ s₂ : RleFullState} (heq : runSteps s₁ = s₂) (h : StateHalts target_tm s₂) :
    StateHalts target_tm s₁ := by
  rw [← heq] at h
  exact runSteps_halts s₁ h


theorem chunk_back_batches {b : ℕ} {s₁ s₂ : RleFullState}
    (heq : runBatches b s₁ = s₂) (h : StateHalts target_tm s₂) :
    StateHalts target_tm s₁ := by
  rw [← heq] at h
  exact runBatches_halts b s₁ h

end BusyBeaver.RleStackEngine

namespace BusyBeaver.SymRunEngine

open BusyBeaver.RleStackEngine

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L =>
    (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 1))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1))

def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R =>
    (([1] : List (Fin 2)) ^ (1 * d + 1)) +>
      ((([0] : List (Fin 2)) ^ (1 + b % 1)) +> encRight R)

def enc1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: R => (([1] : List (Fin 2)) ^ (a + 1)) +> ((0 : Fin 2) >> enc1 R)

@[simp] theorem encLeft_nil : encLeft [] = default := rfl
@[simp] theorem encRight_nil : encRight [] = default := rfl
@[simp] theorem enc1_nil : enc1 [] = default := rfl
@[simp] theorem enc1_cons (a : ℕ) (R : List ℕ) :
    enc1 (a :: R) = (([1] : List (Fin 2)) ^ (a + 1)) +> ((0 : Fin 2) >> enc1 R) := rfl

theorem encLeft_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = (([1] : List (Fin 2)) ^ (a + 1)) +> ((0 : Fin 2) >> encLeft L) := by
  simp only [encLeft, Nat.mod_one, Nat.add_zero, Nat.one_mul]
  rfl

theorem encRight_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d, b) :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encRight R) := by
  simp only [encRight, Nat.mod_one, Nat.add_zero, Nat.one_mul]
  rfl

@[simp] theorem encLeft_cons_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: L)).head = (1 : Fin 2) := by
  rw [encLeft_cons]; simp

@[simp] theorem cons_one_encLeft_tail (a b : ℕ) (L : List (ℕ × ℕ)) :
    (1 : Fin 2) >> (encLeft ((a, b) :: L)).tail = encLeft ((a, b) :: L) := by
  rw [encLeft_cons]; simp

@[simp] theorem encRight_cons_head (d b : ℕ) (R : List (ℕ × ℕ)) :
    (encRight ((d, b) :: R)).head = (1 : Fin 2) := by
  rw [encRight_cons]; simp

@[simp] theorem cons_one_encRight_tail (d b : ℕ) (R : List (ℕ × ℕ)) :
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

@[simp] theorem encM_nil : encM [] = default := rfl
@[simp] theorem encM_cons_zero (M : List MItem) :
    encM (.zero :: M) = (0 : Fin 2) >> encM M := rfl
@[simp] theorem encM_cons_run (d : ℕ) (M : List MItem) :
    encM (.run d :: M) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encM M) := rfl

@[simp] theorem encM_cons_run_head (d : ℕ) (M : List MItem) :
    (encM (.run d :: M)).head = (1 : Fin 2) := by
  rw [encM_cons_run]; simp

@[simp] theorem cons_one_encM_cons_run_tail (d : ℕ) (M : List MItem) :
    (1 : Fin 2) >> (encM (.run d :: M)).tail = encM (.run d :: M) := by
  rw [encM_cons_run]; simp

def strictNat {α : Type*} (n : ℕ) (f : ℕ → α) : α :=
  @Nat.rec (fun _ => α) (f 0) (fun k _ => f k) (Nat.add n 1)

@[simp] theorem strictNat_eq {α : Type*} (n : ℕ) (f : ℕ → α) : strictNat n f = f n := rfl

def bumpM : List MItem → List MItem
  | [] => [.run 0]
  | .zero :: M => .run 0 :: M
  | .run d :: M => strictNat (d + 1) (fun d' => .run d' :: M)

theorem encM_bumpM (M : List MItem) : (1 : Fin 2) >> encM M = encM (bumpM M) := by
  cases M with
  | nil => simp [bumpM]
  | cons x M' =>
    cases x with
    | zero => simp [bumpM]
    | run d => simp [bumpM]

theorem encM_replicate_zero (k : ℕ) (L : List MItem) :
    ((([0] : List (Fin 2)) ^ k) +> encM L) = encM (List.replicate k .zero ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_list, nil_append_list, listblank_append_cons, ih,
      List.replicate_succ, List.cons_append, encM_cons_zero]

def isVarA (target_tm : Machine (Fin 2) (Fin 6)) : Bool :=
  match target_tm 0 1 with
  | some (some 2, Stmt.write 0 _) => true
  | _ => false

def cfgBB (target_tm : Machine (Fin 2) (Fin 6)) (L R : List MItem) : Cfg (Fin 2) (Fin 6) :=
  if isVarA target_tm then
    ⟨some 3, ⟨0, encM L, encM R⟩⟩
  else
    ⟨some 1, ⟨0, encM L, encM R⟩⟩

def cfgCB (target_tm : Machine (Fin 2) (Fin 6)) (L R : List MItem) : Cfg (Fin 2) (Fin 6) :=
  if isVarA target_tm then
    ⟨some 0, ⟨0, encM L, encM R⟩⟩
  else
    ⟨some 2, ⟨0, encM L, encM R⟩⟩

def cfgDL (target_tm : Machine (Fin 2) (Fin 6)) (L R : List MItem) : Cfg (Fin 2) (Fin 6) :=
  if isVarA target_tm then
    (encM L) <{{(2 : Fin 6)}} (encM R)
  else
    (encM L) <{{(3 : Fin 6)}} (encM R)

class HasSymRunRules (target_tm : Machine (Fin 2) (Fin 6)) : Prop where
  step_BB_nil (R : List MItem) :
    (cfgBB target_tm [] R) [target_tm]⊢⁺ cfgCB target_tm [] (bumpM R)
  step_BB_zero (L1 R : List MItem) :
    (cfgBB target_tm (.zero :: L1) R) [target_tm]⊢⁺ cfgCB target_tm L1 (bumpM R)
  step_BB_run0 (L1 R : List MItem) :
    (cfgBB target_tm (.run 0 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm L1 (.run 0 :: R)
  step_BB_run1 (L1 R : List MItem) :
    (cfgBB target_tm (.run 1 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm L1 (.run 0 :: bumpM R)
  step_BB_run2 (L1 R : List MItem) :
    (cfgBB target_tm (.run 2 :: L1) R) [target_tm]⊢⁺
      cfgDL target_tm L1 (.run 0 :: .run 0 :: bumpM R)
  step_BB_run3 (L1 R : List MItem) :
    (cfgBB target_tm (.run 3 :: L1) R) [target_tm]⊢⁺
      cfgBB target_tm (.run 0 :: .zero :: .zero :: L1) (bumpM R)
  step_BB_run_ge4 (d : ℕ) (L1 R : List MItem) :
    (cfgBB target_tm (.run (d + 4) :: L1) R) [target_tm]⊢⁺
      cfgBB target_tm (.run 0 :: .zero :: .run d :: L1) (bumpM R)
  step_DL_run0 (L1 R : List MItem) :
    (cfgDL target_tm (.run 0 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm L1 (bumpM R)
  step_DL_run1 (L1 R : List MItem) :
    (cfgDL target_tm (.run 1 :: L1) R) [target_tm]⊢⁺ cfgDL target_tm L1 (.run 0 :: bumpM R)
  step_DL_run2 (d0 : ℕ) (L1 R1 : List MItem) :
    (cfgDL target_tm (.run 2 :: L1) (.run d0 :: R1)) [target_tm]⊢⁺
      cfgCB target_tm (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1
  step_CB_nil (L : List MItem) :
    (cfgCB target_tm L []) [target_tm]⊢⁺ cfgDL target_tm (bumpM L) [.run 0]
  step_CB_zero (L R1 : List MItem) :
    (cfgCB target_tm L (.zero :: R1)) [target_tm]⊢⁺ cfgDL target_tm (bumpM L) (bumpM R1)
  step_CB_run0_nil (L : List MItem) :
    (cfgCB target_tm L [.run 0]) [target_tm]⊢⁺ cfgBB target_tm (.run 0 :: bumpM L) []
  step_CB_run0_zero (L R2 : List MItem) :
    (cfgCB target_tm L (.run 0 :: .zero :: R2)) [target_tm]⊢⁺
      cfgBB target_tm (.run 0 :: bumpM L) R2
  step_CB_run0_run0 (L R2 : List MItem) :
    (cfgCB target_tm L (.run 0 :: .run 0 :: R2)) [target_tm]⊢⁺
      cfgBB target_tm (.run 0 :: .zero :: bumpM L) R2
  step_CB_run0_run_pos (d2 : ℕ) (L R2 : List MItem) :
    (cfgCB target_tm L (.run 0 :: .run (d2 + 1) :: R2)) [target_tm]⊢⁺
      cfgCB target_tm (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2
  step_CB_run1 (L R1 : List MItem) :
    (cfgCB target_tm L (.run 1 :: R1)) [target_tm]⊢⁺ cfgCB target_tm (.run 0 :: bumpM L) R1
  step_CB_run2 (L R1 : List MItem) :
    (cfgCB target_tm L (.run 2 :: R1)) [target_tm]⊢⁺
      cfgBB target_tm (bumpM L) (.run 0 :: .zero :: R1)
  step_CB_run_ge3 (d : ℕ) (L R1 : List MItem) :
    (cfgCB target_tm L (.run (d + 3) :: R1)) [target_tm]⊢⁺
      cfgBB target_tm (bumpM L) (.run 0 :: .run d :: R1)

variable {target_tm : Machine (Fin 2) (Fin 6)} [HasSymRunRules target_tm]

abbrev step_BB_nil := HasSymRunRules.step_BB_nil (target_tm := target_tm)
abbrev step_BB_zero := HasSymRunRules.step_BB_zero (target_tm := target_tm)
abbrev step_BB_run0 := HasSymRunRules.step_BB_run0 (target_tm := target_tm)
abbrev step_BB_run1 := HasSymRunRules.step_BB_run1 (target_tm := target_tm)
abbrev step_BB_run2 := HasSymRunRules.step_BB_run2 (target_tm := target_tm)
abbrev step_BB_run3 := HasSymRunRules.step_BB_run3 (target_tm := target_tm)
abbrev step_BB_run_ge4 := HasSymRunRules.step_BB_run_ge4 (target_tm := target_tm)
abbrev step_DL_run0 := HasSymRunRules.step_DL_run0 (target_tm := target_tm)
abbrev step_DL_run1 := HasSymRunRules.step_DL_run1 (target_tm := target_tm)
abbrev step_DL_run2 := HasSymRunRules.step_DL_run2 (target_tm := target_tm)
abbrev step_CB_nil := HasSymRunRules.step_CB_nil (target_tm := target_tm)
abbrev step_CB_zero := HasSymRunRules.step_CB_zero (target_tm := target_tm)
abbrev step_CB_run0_nil := HasSymRunRules.step_CB_run0_nil (target_tm := target_tm)
abbrev step_CB_run0_zero := HasSymRunRules.step_CB_run0_zero (target_tm := target_tm)
abbrev step_CB_run0_run0 := HasSymRunRules.step_CB_run0_run0 (target_tm := target_tm)
abbrev step_CB_run0_run_pos := HasSymRunRules.step_CB_run0_run_pos (target_tm := target_tm)
abbrev step_CB_run1 := HasSymRunRules.step_CB_run1 (target_tm := target_tm)
abbrev step_CB_run2 := HasSymRunRules.step_CB_run2 (target_tm := target_tm)
abbrev step_CB_run_ge3 := HasSymRunRules.step_CB_run_ge3 (target_tm := target_tm)

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

theorem strictMList_eq {α : Type*} (xs : List MItem) (f : List MItem → α) : strictMList xs f = f
    xs := by
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
  | (.BB, .run 3 :: L1, R) => strictMList (bumpM R) (fun R' => (.BB, .run 0 :: .zero :: .zero ::
      L1, R'))
  | (.BB, .run (d + 4) :: L1, R) =>
    strictNat d (fun d' => strictMList (bumpM R) (fun R' => (.BB, .run 0 :: .zero :: .run d' :: L1
        , R')))
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
  | (.CB, L, .run 0 :: .run 0 :: R2) => strictMList (bumpM L) (fun L' => (.BB, .run 0 :: .zero ::
      L', R2))
  | (.CB, L, .run 0 :: .run (d2 + 1) :: R2) =>
    strictMList (bumpM L) (fun L1 => strictMList (prependZeroM d2 L1) (fun L2 => (.CB, .run 0 ::
        .run 0 :: L2, R2)))
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


def runElemFast (a b c d : ℕ) (s : SymMode × List MItem × List MItem) :
    SymMode × List MItem × List MItem :=
  iterStep stepElemM a (iterStep stepElem16 b (iterStep stepElem256 c (iterStep stepElem4096 d s)))

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

theorem strictList_eq {α : Type*} (xs : List SymTok) (f : List SymTok → α) : strictList xs f = f
    xs := by
  cases xs <;> rfl

def stripPrefixSym : List SymTok → List SymTok → Option (List SymTok)
  | [], xs => some xs
  | p :: ps, x :: xs => if p = x then stripPrefixSym ps xs else none
  | _ :: _, [] => none

theorem stripPrefixSym_some (pre xs rest : List SymTok)
    (h : stripPrefixSym pre xs = some rest) : xs = pre ++ rest := by
  induction pre generalizing xs with
  | nil => injection h
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

def eatStep (blk : List SymTok) (getRep : SymTok → Option ℕ) (k : ℕ) (xs : List SymTok) : Option
    (ℕ × List SymTok) :=
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
  eatFuel [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12
      getRep12 4 m xs

def eatB12R (m : ℕ) (xs : List SymTok) : List SymTok :=
  eatFuel [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)] .rep12
      getRep12 4 m xs

def peelTok : SymTok → List SymTok → List SymTok
  | .repB1 0, xs => .repB1 0 :: xs
  | .repB1 1, xs => .item (.run 0) :: .item (.run 1) :: xs
  | .repB1 (k + 2), xs => strictNat (k + 1) (fun k' => .item (.run 0) :: .item (.run 1) :: .repB1
      k' :: xs)
  | .rep2 0, xs => .rep2 0 :: xs
  | .rep2 1, xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: xs
  | .rep2 (p + 2), xs => strictNat (p + 1) (fun p' => .item (.run 1) :: .item (.run 0) :: .item
      (.run 1) :: .rep2 p' :: xs)
  | .rep12 0, xs => .rep12 0 :: xs
  | .rep12 1, xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .item (.run 0) :: .item
      (.run 1) :: xs
  | .rep12 (m + 2), xs => strictNat (m + 1) (fun m' => .item (.run 1) :: .item (.run 0) :: .item
      (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep12 m' :: xs)
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
  | .repB1 (k + 2) :: M => strictNat (k + 1) (fun k' => .item (.run 1) :: .item (.run 1) :: .repB1
      k' :: M)
  | .rep2 0 :: M => bumpSymL M
  | .rep2 (p + 1) :: M => strictNat p (fun p' => .item (.run 2) :: .item (.run 0) :: .item (.run
      1) :: .rep2 p' :: M)
  | .rep12 0 :: M => bumpSymL M
  | .rep12 (m + 1) :: M => strictNat m (fun m' => .item (.run 2) :: .item (.run 0) :: .item (.run
      1) :: .item (.run 0) :: .item (.run 1) :: .rep12 m' :: M)

def bumpSymR : List SymTok → List SymTok
  | [] => [.item (.run 0)]
  | .item .zero :: M => .item (.run 0) :: M
  | .item (.run d) :: M => strictNat (d + 1) (fun d' => .item (.run d') :: M)
  | .repB1 0 :: M => bumpSymR M
  | .repB1 1 :: M => .item (.run 1) :: .item (.run 1) :: M
  | .repB1 (k + 2) :: M => strictNat (k + 1) (fun k' => .item (.run 1) :: .item (.run 1) :: .repB1
      k' :: M)
  | .rep2 0 :: M => bumpSymR M
  | .rep2 (p + 1) :: M => strictNat p (fun p' => .item (.run 1) :: .item (.run 1) :: .item (.run
      1) :: .rep2 p' :: M)
  | .rep12 0 :: M => bumpSymR M
  | .rep12 (m + 1) :: M => strictNat m (fun m' => .item (.run 1) :: .item (.run 1) :: .item (.run
      0) :: .item (.run 1) :: .item (.run 1) :: .rep12 m' :: M)

def prependZeroSym : ℕ → List SymTok → List SymTok
  | 0, acc => acc
  | n + 1, acc => prependZeroSym n (.item .zero :: acc)

def stepElemBB (L R : List SymTok) : SymMode × List SymTok × List SymTok :=
  match L with
  | [] => strictList (bumpSymR R) (fun R' => (.CB, [], R'))
  | .item .zero :: L1 => strictList (bumpSymR R) (fun R' => (.CB, L1, R'))
  | .item (.run 0) :: L1 => (.BB, L1, .item (.run 0) :: R)
  | .item (.run 1) :: L1 => strictList (bumpSymR R) (fun R' => (.BB, L1, .item (.run 0) :: R'))
  | .item (.run 2) :: L1 => strictList (bumpSymR R) (fun R' => (.DL, L1, .item (.run 0) :: .item
      (.run 0) :: R'))
  | .item (.run 3) :: L1 => strictList (bumpSymR R) (fun R' => (.BB, .item (.run 0) :: .item .zero
      :: .item .zero :: L1, R'))
  | .item (.run (d + 4)) :: L1 =>
    strictNat d (fun d' => strictList (bumpSymR R) (fun R' => (.BB, .item (.run 0) :: .item .zero
        :: .item (.run d') :: L1, R')))
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
      strictList (prependZeroSym (d0 + 1) L1) (fun L' => (.CB, .item (.run 0) :: .item (.run 0) ::
          L', R1))
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
  | .item (.run 0) :: R2 => strictList (bumpSymL L) (fun L' => (.BB, .item (.run 0) :: .item .zero
      :: L', R2))
  | .item (.run (d2 + 1)) :: R2 =>
    strictList (bumpSymL L) (fun L1 => strictList (prependZeroSym d2 L1) (fun L2 => (.CB, .item
        (.run 0) :: .item (.run 0) :: L2, R2)))
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
  | .item (.run 2) :: R1 => strictList (bumpSymL L) (fun L' => (.BB, L', .item (.run 0) :: .item
      .zero :: R1))
  | .item (.run (d + 3)) :: R1 =>
    strictNat d (fun d' => strictList (bumpSymL L) (fun L' => (.BB, L', .item (.run 0) :: .item
        (.run d') :: R1)))
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
  | .item (.run 1) :: L1, R => strictList (bumpSymR R) (fun R' => sweepBB L1 (.item (.run 0) ::
      R'))
  | .item (.run (d + 2)) :: L1, R => strictNat (d + 2) (fun d' => stepElemBB (.item (.run d') ::
      L1) R)
  | .repB1 k :: L1, R => strictList (eatB1 k R) (fun R' => sweepBB L1 R')
  | .rep2 p :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => strictList (eatB2 p R2) (fun R' => sweepBB L1 (.item (.run 0) :: .item (.run 1)
        :: R'))
    | none => strictList (peelTok (.rep2 p) L1) (fun L' => stepElemBB L' R)
  | .rep12 m :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => strictList (eatB12R m R2) (fun R' => sweepBB L1 (.item (.run 0) :: .item (.run 1)
        :: R'))
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

def tryRuleA (L : List SymTok) (d : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List
    SymTok :=
  match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0),
     .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)]
         L with
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

def afterSplitB2 (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) (res : ℕ × List SymTok) :
    SymMode × List SymTok × List SymTok :=
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

def tryRuleB (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List
    SymTok :=
  match stripPrefixSym [.item (.run 0)] L with
  | some restL => afterSplitB2 L d2 R_tail (splitB2 0 restL)
  | none => stepElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)

def tryRuleBC (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) : SymMode × List SymTok × List
    SymTok :=
  match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
  | some rest1 =>
    match popRep2 rest1 with
    | some (p, restC) =>
      match stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1)] restC
          with
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

theorem stepStar_refl {M : Machine Γ Λ} {c : Cfg Γ Λ} : c [M]⊢* c := ⟨0, rfl⟩

theorem step_BB_r0_r1 (L R : List MItem) :
    (cfgBB target_tm (.run 0 :: .run 1 :: L) R) [target_tm]⊢⁺ cfgBB target_tm L (.run 0 :: .run 1
        :: R) :=
  stepPlus_trans (step_BB_run0 (.run 1 :: L) R) (step_BB_run1 L (.run 0 :: R))

theorem step_BB_r1_r0_r1_comm (L R : List MItem) :
    (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R)) [target_tm]⊢⁺
      cfgBB target_tm L (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R) :=
  stepPlus_trans (step_BB_run1 (.run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
    (stepPlus_trans (step_BB_run0 (.run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: R))
      (step_BB_run1 L (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R)))

def evalM (target_tm : Machine (Fin 2) (Fin 6)) : SymMode × List MItem × List MItem → Cfg (Fin 2)
    (Fin 6)
  | (.BB, L, R) => cfgBB target_tm L R
  | (.DL, L, R) => cfgDL target_tm L R
  | (.CB, L, R) => cfgCB target_tm L R
  | (.HALT, L, R) => cfgDL target_tm L R

theorem prependZeroM_eq (n : ℕ) (acc : List MItem) :
    prependZeroM n acc = List.replicate n .zero ++ acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [prependZeroM, ih, List.replicate_succ', List.append_assoc]
    rfl

theorem stepElemM_sound (s : SymMode × List MItem × List MItem) :
    ((evalM target_tm) s) [target_tm]⊢* ((evalM target_tm) (stepElemM s)) := by
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

omit [HasSymRunRules target_tm] in
theorem iterStep_sound {α : Type*} (f : α → α) (ev : α → Cfg (Fin 2) (Fin 6))
    (hf : ∀ s, (ev s) [target_tm]⊢* (ev (f s))) (n : ℕ) (s : α) :
    (ev s) [target_tm]⊢* (ev (iterStep f n s)) := by
  induction n generalizing s with
  | zero => exact stepStar_refl
  | succ n ih => exact stepStar_trans (hf s) (ih (f s))

def repBlock (blk : List MItem) : ℕ → List MItem
  | 0 => []
  | k + 1 => blk ++ repBlock blk k

theorem repBlock_add (blk : List MItem) (k1 k2 : ℕ) :
    repBlock blk (k1 + k2) = repBlock blk k1 ++ repBlock blk k2 := by
  induction k1 with
  | zero => simp [repBlock]
  | succ k1 ih => simp [repBlock, Nat.succ_add, ih, List.append_assoc]

theorem repBlock_succ_right (blk : List MItem) (k : ℕ) :
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

def evalSym (target_tm : Machine (Fin 2) (Fin 6)) (s : SymMode × List SymTok × List SymTok) : Cfg
    (Fin 2) (Fin 6) :=
  (evalM target_tm) (s.1, encSymL s.2.1, encSymR s.2.2)

theorem enc_eatFuel (enc : List SymTok → List MItem) (mblk : List MItem)
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
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          rw [repBlock_add, List.append_assoc, ← hget x k2 rest0 hg]
        | none =>
          rw [hg] at hstep
          cases hs : stripPrefixSym blk (x :: rest0) with
          | none => rw [hs] at hstep; contradiction
          | some rest2 =>
            rw [hs] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            have hxs := stripPrefixSym_some blk (x :: rest0) rest2 hs
            rw [repBlock_succ_right, List.append_assoc, ← hblk rest2, ← hxs]

theorem encSymL_eatB1 (k : ℕ) (xs : List SymTok) :
    encSymL (eatB1 k xs) = repBlock [.run 0, .run 1] k ++ encSymL xs :=
  enc_eatFuel encSymL [.run 0, .run 1] [.item (.run 0), .item (.run 1)] .repB1 getRepB1
    (fun _ _ => rfl)
    (fun x _ _ h => by
      cases x <;> dsimp only [getRepB1] at h <;> try contradiction
      injection h with h'; subst h'; rfl)
    (fun _ => rfl) 4 k xs

theorem encSymR_eatB1 (k : ℕ) (xs : List SymTok) :
    encSymR (eatB1 k xs) = repBlock [.run 0, .run 1] k ++ encSymR xs :=
  enc_eatFuel encSymR [.run 0, .run 1] [.item (.run 0), .item (.run 1)] .repB1 getRepB1
    (fun _ _ => rfl)
    (fun x _ _ h => by
      cases x <;> dsimp only [getRepB1] at h <;> try contradiction
      injection h with h'; subst h'; rfl)
    (fun _ => rfl) 4 k xs

theorem encSymL_eatC2 (p : ℕ) (xs : List SymTok) :
    encSymL (eatC2 p xs) = repBlock [.run 1, .run 0, .run 1] p ++ encSymL xs :=
  enc_eatFuel encSymL [.run 1, .run 0, .run 1] [.item (.run 1), .item (.run 0), .item (.run 1)]
      .rep2 getRep2
    (fun _ _ => rfl)
    (fun x _ _ h => by
      cases x <;> dsimp only [getRep2] at h <;> try contradiction
      injection h with h'; subst h'; rfl)
    (fun _ => rfl) 4 p xs

theorem encSymR_eatB2 (p : ℕ) (xs : List SymTok) :
    encSymR (eatB2 p xs) = repBlock [.run 0, .run 1, .run 1] p ++ encSymR xs :=
  enc_eatFuel encSymR [.run 0, .run 1, .run 1] [.item (.run 0), .item (.run 1), .item (.run 1)]
      .rep2 getRep2
    (fun _ _ => rfl)
    (fun x _ _ h => by
      cases x <;> dsimp only [getRep2] at h <;> try contradiction
      injection h with h'; subst h'; rfl)
    (fun _ => rfl) 4 p xs

theorem encSymL_eatC12 (m : ℕ) (xs : List SymTok) :
    encSymL (eatC12 m xs) = repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ encSymL xs :=
  enc_eatFuel encSymL [.run 1, .run 0, .run 1, .run 0, .run 1]
    [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12
        getRep12
    (fun _ _ => rfl)
    (fun x _ _ h => by
      cases x <;> dsimp only [getRep12] at h <;> try contradiction
      injection h with h'; subst h'; rfl)
    (fun _ => rfl) 4 m xs

theorem encSymR_eatB12R (m : ℕ) (xs : List SymTok) :
    encSymR (eatB12R m xs) = repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ encSymR xs :=
  enc_eatFuel encSymR [.run 0, .run 1, .run 0, .run 1, .run 1]
    [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)] .rep12
        getRep12
    (fun _ _ => rfl)
    (fun x _ _ h => by
      cases x <;> dsimp only [getRep12] at h <;> try contradiction
      injection h with h'; subst h'; rfl)
    (fun _ => rfl) 4 m xs

theorem encSymL_peelTok (t : SymTok) (xs : List SymTok) :
    encSymL (peelTok t xs) = encSymL (t :: xs) := by
  cases t with
  | item x => rfl
  | repB1 k => rcases k with _ | _ | k <;> simp [peelTok, strictNat_eq, encSymL, repBlock]
  | rep2 p => rcases p with _ | _ | p <;> simp [peelTok, strictNat_eq, encSymL, repBlock]
  | rep12 m => rcases m with _ | _ | m <;> simp [peelTok, strictNat_eq, encSymL, repBlock]

theorem encSymL_peelL (xs : List SymTok) : encSymL (peelL xs) = encSymL xs := by
  cases xs with
  | nil => rfl
  | cons t rest => exact encSymL_peelTok t rest

theorem encSymL_prependZeroSym (n : ℕ) (acc : List SymTok) :
    encSymL (prependZeroSym n acc) = List.replicate n .zero ++ encSymL acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [prependZeroSym, ih, encSymL, List.replicate_succ', List.append_assoc]
    rfl

theorem sweep_BB_B1 (k : ℕ) (L R : List MItem) :
    (cfgBB target_tm (repBlock [.run 0, .run 1] k ++ L) R) [target_tm]⊢*
    (cfgBB target_tm L (repBlock [.run 0, .run 1] k ++ R)) := by
  induction k generalizing R with
  | zero => exact stepStar_refl
  | succ k ih =>
    have h_eq : repBlock [.run 0, .run 1] (k + 1) ++ R =
        repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: R) := by
      rw [repBlock_succ_right, List.append_assoc]; rfl
    rw [h_eq]
    exact stepStar_trans (stepPlus_stepStar (step_BB_r0_r1 (repBlock [.run 0, .run 1] k ++ L) R))
      (ih (.run 0 :: .run 1 :: R))

theorem sweep_BB_C2 (p : ℕ) (L R : List MItem) :
    (cfgBB target_tm (repBlock [.run 1, .run 0, .run 1] p ++ L) (.run 0 :: .run 1 :: R))
        [target_tm]⊢*
    (cfgBB target_tm L (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
  induction p generalizing R with
  | zero => exact stepStar_refl
  | succ p ih =>
    have h_eq : (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] (p + 1) ++ R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ (.run 0 :: .run 1 :: .run 1 ::
            R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    exact stepStar_trans (stepPlus_stepStar (step_BB_r1_r0_r1_comm (repBlock [.run 1, .run 0, .run
        1] p ++ L) R))
      (ih (.run 0 :: .run 1 :: .run 1 :: R))

theorem sweep_BB_C12 (m : ℕ) (L R : List MItem) :
    (cfgBB target_tm (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) (.run 0 :: .run 1
        :: R)) [target_tm]⊢*
    (cfgBB target_tm L (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++
        R)) := by
  induction m generalizing R with
  | zero => exact stepStar_refl
  | succ m ih =>
    have h_eq : (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] (m + 1) ++
        R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ (.run 0 ::
            .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := stepPlus_trans
      (step_BB_r1_r0_r1_comm (target_tm := target_tm)
        (.run 0 :: .run 1 :: (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)) R)
      (step_BB_r0_r1 (target_tm := target_tm)
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
        (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R))
    exact stepStar_trans (stepPlus_stepStar h1)
      (ih (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R))

theorem sweep_CB_B1 (k : ℕ) (L R : List MItem) :
    (cfgCB target_tm (.run 0 :: L) (repBlock [.run 0, .run 1] k ++ R)) [target_tm]⊢*
    (cfgCB target_tm (.run 0 :: repBlock [.run 0, .run 1] k ++ L) R) := by
  induction k generalizing L with
  | zero => exact stepStar_refl
  | succ k ih =>
    have h_eq : (.run 0 :: repBlock [.run 0, .run 1] (k + 1) ++ L) =
        (.run 0 :: repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : (cfgCB target_tm (.run 0 :: L) (.run 0 :: .run 1 :: (repBlock [.run 0, .run 1] k ++
        R))) [target_tm]⊢⁺
        cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1] k ++ R) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: L) (repBlock [.run 0, .run 1] k ++ R)
    exact stepStar_trans (stepPlus_stepStar h1) (ih (.run 0 :: .run 1 :: L))

theorem sweep_CB_B2 (p : ℕ) (L R : List MItem) :
    (cfgCB target_tm (.run 0 :: L) (repBlock [.run 0, .run 1, .run 1] p ++ R)) [target_tm]⊢*
    (cfgCB target_tm (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ L) R) := by
  induction p generalizing L with
  | zero => exact stepStar_refl
  | succ p ih =>
    have h_eq : (.run 0 :: repBlock [.run 1, .run 0, .run 1] (p + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ (.run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : (cfgCB target_tm (.run 0 :: L) (.run 0 :: .run 1 :: .run 1 :: (repBlock [.run 0,
        .run 1, .run 1] p ++ R))) [target_tm]⊢⁺
        cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0, .run 1,
            .run 1] p ++ R)) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: L) (.run 1 :: (repBlock [.run 0, .run
          1, .run 1] p ++ R))
    have h2 : (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock [.run 0,
        .run 1, .run 1] p ++ R))) [target_tm]⊢⁺
        cfgCB target_tm (.run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1,
            .run 1] p ++ R) := by
      simpa [bumpM] using step_CB_run1 (.run 0 :: .run 0 :: .run 1 :: L) (repBlock [.run 0, .run 1
          , .run 1] p ++ R)
    exact stepStar_trans (stepPlus_stepStar (stepPlus_trans h1 h2)) (ih (.run 1 :: .run 0 :: .run
        1 :: L))

theorem sweep_CB_B12R (m : ℕ) (L R : List MItem) :
    (cfgCB target_tm (.run 0 :: L) (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
        [target_tm]⊢*
    (cfgCB target_tm (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) R) := by
  induction m generalizing L with
  | zero => exact stepStar_refl
  | succ m ih =>
    have h_eq : (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ (.run 1 :: .run 0 ::
            .run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : (cfgCB target_tm (.run 0 :: L) (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 ::
        (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) [target_tm]⊢⁺
        cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: (repBlock
            [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: L) (.run 0 :: .run 1 :: .run 1 ::
          (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h2 : (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: .run 1 ::
        (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) [target_tm]⊢⁺
        cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (.run 1 :: (repBlock
            [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
      simpa [bumpM] using step_CB_run0_run_pos 0 (.run 0 :: .run 0 :: .run 1 :: L) (.run 1 ::
          (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h3 : (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (.run 1 ::
        (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) [target_tm]⊢⁺
        cfgCB target_tm (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L) (repBlock
            [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R) := by
      simpa [bumpM] using step_CB_run1 (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)
    exact stepStar_trans (stepPlus_stepStar (stepPlus_trans h1 (stepPlus_trans h2 h3)))
      (ih (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L))

theorem encSymL_bumpSymL (L : List SymTok) : encSymL (bumpSymL L) = bumpM (encSymL L) := by
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

theorem encSymR_bumpSymR (R : List SymTok) : encSymR (bumpSymR R) = bumpM (encSymR R) := by
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

theorem stepElemBB_sound (L R : List SymTok) :
    ((evalSym target_tm) (.BB, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepElemBB L R)) := by
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
          simp only [stepElemBB, strictList_eq, strictNat_eq, evalSym, evalM, encSymL, encSymR,
              encSymR_bumpSymR]
        · exact stepPlus_stepStar (step_BB_run0 _ _)
        · exact stepPlus_stepStar (step_BB_run1 _ _)
        · exact stepPlus_stepStar (step_BB_run2 _ _)
        · exact stepPlus_stepStar (step_BB_run3 _ _)
        · exact stepPlus_stepStar (step_BB_run_ge4 _ _ _)
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

theorem stepElemDL_sound (L R : List SymTok) :
    ((evalSym target_tm) (.DL, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepElemDL L R)) := by
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
        · simp only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymR_bumpSymR]
          exact stepPlus_stepStar (step_DL_run1 _ _)
        · cases R with
          | nil => exact stepStar_refl
          | cons rt R1 =>
            cases rt with
            | item rit =>
              cases rit with
              | zero => exact stepStar_refl
              | run d0 =>
                simp only [stepElemDL, strictList_eq, evalSym, evalM, encSymL, encSymR,
                    encSymL_prependZeroSym]
                exact stepPlus_stepStar (step_DL_run2 _ _ _)
            | repB1 _ => exact stepStar_refl
            | rep2 _ => exact stepStar_refl
            | rep12 _ => exact stepStar_refl
        · exact stepStar_refl
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

theorem stepElemCB_run0_sound (L R1 : List SymTok) :
    ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1)) [target_tm]⊢* ((evalSym target_tm)
        (stepElemCB_run0 L R1)) := by
  cases R1 with
  | nil =>
    simp only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
    exact stepPlus_stepStar (step_CB_run0_nil _)
  | cons rt R2 =>
    cases rt with
    | item rit =>
      cases rit with
      | zero =>
        simp only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL]
        exact stepPlus_stepStar (step_CB_run0_zero _ _)
      | run d2 =>
        rcases d2 with _ | d2 <;>
          simp only [stepElemCB_run0, strictList_eq, evalSym, evalM, encSymL, encSymR,
              encSymL_bumpSymL, encSymL_prependZeroSym]
        · exact stepPlus_stepStar (step_CB_run0_run0 _ _)
        · exact stepPlus_stepStar (step_CB_run0_run_pos _ _ _)
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

theorem stepElemCB_sound (L R : List SymTok) :
    ((evalSym target_tm) (.CB, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepElemCB L R)) := by
  cases R with
  | nil =>
    simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL, encSymR]
    exact stepPlus_stepStar (step_CB_nil _)
  | cons t R1 =>
    cases t with
    | item it =>
      cases it with
      | zero =>
        simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymL_bumpSymL, encSymR,
            encSymR_bumpSymR]
        exact stepPlus_stepStar (step_CB_zero _ _)
      | run d =>
        rcases d with _ | _ | _ | d
        · exact stepElemCB_run0_sound L R1
        · simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run1 _ _)
        · simp only [stepElemCB, strictList_eq, evalSym, evalM, encSymR, encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run2 _ _)
        · simp only [stepElemCB, strictList_eq, strictNat_eq, evalSym, evalM, encSymR,
            encSymL_bumpSymL]
          exact stepPlus_stepStar (step_CB_run_ge3 _ _ _)
    | repB1 _ => exact stepStar_refl
    | rep2 _ => exact stepStar_refl
    | rep12 _ => exact stepStar_refl

theorem stepElemSym_sound (m : SymMode) (L R : List SymTok) :
    ((evalSym target_tm) (m, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepElemSym m L R)) := by
  cases m with
  | BB => exact stepElemBB_sound L R
  | DL => exact stepElemDL_sound L R
  | CB => exact stepElemCB_sound L R
  | HALT => exact stepStar_refl

theorem sweepBB_sound (L R : List SymTok) :
    ((evalSym target_tm) (.BB, L, R)) [target_tm]⊢* ((evalSym target_tm) (sweepBB L R)) := by
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
          exact stepStar_trans (stepPlus_stepStar (step_BB_run0 (encSymL L1) (encSymR R))) (ih
              (.item (.run 0) :: R))
        · simp only [sweepBB, strictList_eq]
          have h1 : ((evalSym target_tm) (.BB, .item (.run 1) :: L1, R)) [target_tm]⊢*
              ((evalSym target_tm) (.BB, L1, .item (.run 0) :: bumpSymR R)) := by
            simp only [evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            exact stepPlus_stepStar (step_BB_run1 (encSymL L1) (encSymR R))
          exact stepStar_trans h1 (ih (.item (.run 0) :: bumpSymR R))
        · exact stepElemBB_sound (.item (.run (d + 2)) :: L1) R
    | repB1 k =>
      simp only [sweepBB, strictList_eq]
      have h1 : ((evalSym target_tm) (.BB, .repB1 k :: L1, R)) [target_tm]⊢*
          ((evalSym target_tm) (.BB, L1, eatB1 k R)) := by
        simp only [evalSym, evalM, encSymL, encSymR_eatB1]
        exact sweep_BB_B1 k (encSymL L1) (encSymR R)
      exact stepStar_trans h1 (ih (eatB1 k R))
    | rep2 p =>
      simp only [sweepBB]
      cases hstrip : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hstrip
        simp only [strictList_eq]
        have h1 : ((evalSym target_tm) (.BB, .rep2 p :: L1, R)) [target_tm]⊢*
            ((evalSym target_tm) (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB2 p R2)) := by
          rw [hR]
          simp only [evalSym, evalM, encSymL, encSymR, encSymR_eatB2, List.cons_append,
              List.nil_append]
          exact sweep_BB_C2 p (encSymL L1) (encSymR R2)
        exact stepStar_trans h1 (ih (.item (.run 0) :: .item (.run 1) :: eatB2 p R2))
      | none =>
        simp only [strictList_eq]
        have heq : (evalSym target_tm) (.BB, .rep2 p :: L1, R) = (evalSym target_tm) (.BB, peelTok
            (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelTok]
        rw [heq]
        exact stepElemBB_sound (peelTok (.rep2 p) L1) R
    | rep12 m =>
      simp only [sweepBB]
      cases hstrip : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hstrip
        simp only [strictList_eq]
        have h1 : ((evalSym target_tm) (.BB, .rep12 m :: L1, R)) [target_tm]⊢*
            ((evalSym target_tm) (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB12R m R2)) :=
                by
          rw [hR]
          simp only [evalSym, evalM, encSymL, encSymR, encSymR_eatB12R, List.cons_append,
              List.nil_append]
          exact sweep_BB_C12 m (encSymL L1) (encSymR R2)
        exact stepStar_trans h1 (ih (.item (.run 0) :: .item (.run 1) :: eatB12R m R2))
      | none =>
        simp only [strictList_eq]
        have heq : (evalSym target_tm) (.BB, .rep12 m :: L1, R) = (evalSym target_tm) (.BB,
            peelTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelTok]
        rw [heq]
        exact stepElemBB_sound (peelTok (.rep12 m) L1) R

theorem sweepCB_sound (L R : List SymTok) :
    ((evalSym target_tm) (.CB, L, R)) [target_tm]⊢* ((evalSym target_tm) (.CB, (sweepCB L R).1,
        (sweepCB L R).2)) := by
  induction L, R using sweepCB.induct with
  | case1 L => exact stepStar_refl
  | case2 L R1 => exact stepStar_refl
  | case3 L R2 ih =>
    simp only [sweepCB, strictList_eq]
    have h1 : ((evalSym target_tm) (.CB, L, .item (.run 0) :: .item (.run 1) :: R2)) [target_tm]⊢*
        ((evalSym target_tm) (.CB, .item (.run 0) :: .item (.run 0) :: bumpSymL L, R2)) := by
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
    rw [heq]; try exact stepStar_refl
  | case5 L R1 ih =>
    simp only [sweepCB, strictList_eq]
    have h1 : ((evalSym target_tm) (.CB, L, .item (.run 1) :: R1)) [target_tm]⊢*
        ((evalSym target_tm) (.CB, .item (.run 0) :: bumpSymL L, R1)) := by
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
      exact stepPlus_stepStar (step_CB_run1 (encSymL L) (encSymR R1))
    exact stepStar_trans h1 (ih (bumpSymL L))
  | case6 L d R1 => exact stepStar_refl
  | case7 L k R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : ((evalSym target_tm) (.CB, L, .repB1 k :: R1)) [target_tm]⊢*
        ((evalSym target_tm) (.CB, .item (.run 0) :: eatB1 k L1, R1)) := by
      rw [hL]
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatB1, List.cons_append,
          List.nil_append]
      exact sweep_CB_B1 k (encSymL L1) (encSymR R1)
    exact stepStar_trans h1 (ih (eatB1 k L1))
  | case8 L k R1 hstrip =>
    simp only [sweepCB, hstrip]; try exact stepStar_refl
  | case9 L p R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : ((evalSym target_tm) (.CB, L, .rep2 p :: R1)) [target_tm]⊢*
        ((evalSym target_tm) (.CB, .item (.run 0) :: eatC2 p L1, R1)) := by
      rw [hL]
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC2, List.cons_append,
          List.nil_append]
      exact sweep_CB_B2 p (encSymL L1) (encSymR R1)
    exact stepStar_trans h1 (ih (eatC2 p L1))
  | case10 L p R1 hstrip =>
    simp only [sweepCB, hstrip]; try exact stepStar_refl
  | case11 L m R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB, hstrip, strictList_eq]
    have h1 : ((evalSym target_tm) (.CB, L, .rep12 m :: R1)) [target_tm]⊢*
        ((evalSym target_tm) (.CB, .item (.run 0) :: eatC12 m L1, R1)) := by
      rw [hL]
      simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC12, List.cons_append,
          List.nil_append]
      exact sweep_CB_B12R m (encSymL L1) (encSymR R1)
    exact stepStar_trans h1 (ih (eatC12 m L1))
  | case12 L m R1 hstrip =>
    simp only [sweepCB, hstrip]; try exact stepStar_refl

theorem finishThenBB_sound (s : SymMode × List SymTok × List SymTok) :
    ((evalSym target_tm) s) [target_tm]⊢* ((evalSym target_tm) (finishThenBB s)) := by
  rcases s with ⟨m, L, R⟩
  cases m <;> try exact stepStar_refl
  exact sweepBB_sound L R

theorem stepElemThenBB_sound (m : SymMode) (L R : List SymTok) :
    ((evalSym target_tm) (m, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepElemThenBB m L R)) :=
  stepStar_trans (stepElemSym_sound m L R) (finishThenBB_sound (stepElemSym m L R))

def peelPureTok : SymTok → List SymTok → List SymTok
  | .repB1 0, xs => .repB1 0 :: xs
  | .repB1 (k + 1), xs => .item (.run 0) :: .item (.run 1) :: .repB1 k :: xs
  | .rep2 0, xs => .rep2 0 :: xs
  | .rep2 (p + 1), xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .rep2 p :: xs
  | .rep12 0, xs => .rep12 0 :: xs
  | .rep12 (m + 1), xs => .item (.run 1) :: .item (.run 0) :: .item (.run 1) :: .item (.run 0) ::
      .item (.run 1) :: .rep12 m :: xs
  | .item x, xs => .item x :: xs

theorem encSymL_peelPureTok (t : SymTok) (xs : List SymTok) :
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

theorem stepPureBB_sound (L R : List SymTok) :
    ((evalSym target_tm) (.BB, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepPureBB L R)) := by
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
        have heq : (evalSym target_tm) (.BB, .rep2 p :: L1, R) = (evalSym target_tm) (.BB,
            peelPureTok (.rep2 p) L1, R) := by
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
        have heq : (evalSym target_tm) (.BB, .rep12 m :: L1, R) = (evalSym target_tm) (.BB,
            peelPureTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact stepElemBB_sound (peelPureTok (.rep12 m) L1) R

theorem stepPureDL_sound (L R : List SymTok) :
    ((evalSym target_tm) (.DL, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepPureDL L R)) := by
  cases L with
  | nil => exact stepStar_refl
  | cons t L1 =>
    have heq : (evalSym target_tm) (.DL, t :: L1, R) = (evalSym target_tm) (.DL, peelPureTok t L1
        , R) := by
      simp only [evalSym, encSymL_peelPureTok]
    rw [heq]
    exact stepElemDL_sound (peelPureTok t L1) R

theorem stepPureCB_sound (L R : List SymTok) :
    ((evalSym target_tm) (.CB, L, R)) [target_tm]⊢* ((evalSym target_tm) (stepPureCB L R)) := by
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
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)]
          L with
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

theorem stepPure_sound (s : SymMode × List SymTok × List SymTok) :
    ((evalSym target_tm) s) [target_tm]⊢* ((evalSym target_tm) (stepPure s)) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | BB => exact stepPureBB_sound L R
  | DL => exact stepPureDL_sound L R
  | CB => exact stepPureCB_sound L R
  | HALT => exact stepStar_refl

theorem repBlock12_snoc (m : ℕ) (xs : List MItem) :
    repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++
      (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: xs) =
    repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ xs := by
  rw [repBlock_succ_right, List.append_assoc]; rfl

theorem popRepB1_some (xs : List SymTok) (k : ℕ) (rest : List SymTok)
    (h : popRepB1 xs = some (k, rest)) :
    xs = .repB1 k :: rest := by
  rcases xs with _ | ⟨t, tl⟩
  · simp [popRepB1] at h
  · cases t <;> try contradiction
    injection h with h'; injection h' with h1 h2; subst h1; subst h2; rfl

theorem matchEndB1_some (xs : List SymTok) (k : ℕ) (h : matchEndB1 xs = some k) :
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

theorem popRep2_some (xs : List SymTok) (p : ℕ) (rest : List SymTok) (h : popRep2 xs = some (p,
    rest)) :
    xs = .rep2 p :: rest := by
  rcases xs with _ | ⟨t, rest0⟩ <;> try contradiction
  cases t <;> try contradiction
  injection h with h'; injection h' with h1 h2; subst h1; subst h2; rfl

theorem popRep12_some (xs : List SymTok) (m : ℕ) (rest : List SymTok) (h : popRep12 xs = some (m,
    rest)) :
    xs = .rep12 m :: rest := by
  rcases xs with _ | ⟨t, rest0⟩ <;> try contradiction
  cases t <;> try contradiction
  injection h with h'; injection h' with h1 h2; subst h1; subst h2; rfl

theorem popSep3_some (xs sep rest : List SymTok) (h : popSep3 xs = some (sep, rest)) :
    xs = sep ++ rest ∧ (sep = sep3A ∨ sep = sep3B) := by
  unfold popSep3 at h
  cases hsA : stripPrefixSym sep3A xs with
  | some rA =>
    rw [hsA] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨stripPrefixSym_some _ _ _ hsA, Or.inl rfl⟩
  | none =>
    rw [hsA] at h
    cases hsB : stripPrefixSym sep3B xs with
    | some rB =>
      rw [hsB] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
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

theorem ruleA0_sound (k d : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateA0 (k + 1) (d + 6) R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateA 0 k d R_tail)) :=
  iterStep_sound stepPure (evalSym target_tm) (stepPure_sound (target_tm := target_tm)) 46
    (stateA0 (k + 1) (d + 6) R_tail)

omit [HasSymRunRules target_tm] in
theorem ruleA_step_eq (m k d : ℕ) (R_tail : List SymTok) :
    (evalSym target_tm) (iterStep stepPure 66 (stateA m (k + 1) (d + 6) R_tail)) =
    (evalSym target_tm) (stateA (m + 1) k d R_tail) := by
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

theorem ruleA_step_sound (m k d : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateA m (k + 1) (d + 6) R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateA (m + 1) k d R_tail)) :=
  ruleA_step_eq m k d R_tail ▸
    iterStep_sound stepPure (evalSym target_tm) (stepPure_sound (target_tm := target_tm)) 66
      (stateA m (k + 1) (d + 6) R_tail)

theorem ruleA_iter (n m k d : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateA m (k + n) (d + 6 * n) R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateA (m + n) k d R_tail)) := by
  induction n generalizing m k d with
  | zero => simp; try exact stepStar_refl
  | succ n ih =>
    have h1 : k + (n + 1) = (k + n) + 1 := by omega
    have h2 : d + 6 * (n + 1) = (d + 6 * n) + 6 := by omega
    have h3 : m + (n + 1) = (m + 1) + n := by omega
    rw [h1, h2, h3]
    exact stepStar_trans (ruleA_step_sound m (k + n) (d + 6 * n) R_tail) (ih (m + 1) k d)

theorem tryRuleA_sound (L : List SymTok) (d : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (.CB, L, .item (.run d) :: R_tail)) [target_tm]⊢* ((evalSym target_tm)
        (tryRuleA L d R_tail)) := by
  unfold tryRuleA
  cases hs : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0),
     .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)]
         L with
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

omit [HasSymRunRules target_tm] in
theorem ruleC_step_eq (p k d2 : ℕ) (R_tail : List SymTok) :
    (evalSym target_tm) (iterStep stepPure 46 (stateC (p + 3) (k + 1) d2 R_tail)) =
    (evalSym target_tm) (stateC (p + 2) (k + 3) (d2 + 2) R_tail) := by
  have h : iterStep stepPure 46 (stateC (p + 3) (k + 1) d2 R_tail) =
    (.CB,
     [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 2),
      .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
      .repB1 (k + 1), .item (.run 0)],
     .item .zero :: .item (.run (d2 + 2)) :: R_tail) := rfl
  rw [h]
  simp only [stateC, evalSym, encSymL, repBlock, List.cons_append, List.nil_append]

theorem ruleC_step_sound (p k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateC (p + 3) (k + 1) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateC (p + 2) (k + 3) (d2 + 2) R_tail)) :=
  ruleC_step_eq p k d2 R_tail ▸
    iterStep_sound stepPure (evalSym target_tm) (stepPure_sound (target_tm := target_tm)) 46
      (stateC (p + 3) (k + 1) d2 R_tail)

theorem ruleC_iter (n p k d2 : ℕ) (R_tail : List SymTok) (hk : 1 ≤ k) :
    ((evalSym target_tm) (stateC (p + n + 2) k d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateC (p + 2) (k + 2 * n) (d2 + 2 * n) R_tail)) := by
  induction n generalizing p k d2 with
  | zero => simp; try exact stepStar_refl
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

set_option maxRecDepth 2000000 in
theorem ruleB_step_AA (p m k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure (evalSym target_tm)
    (stepPure_sound (target_tm := target_tm)) 126
    (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 126 (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 126 (stateB sep3A sep3A (p + 1) (m + 2) (k +
      1) d2 R_tail)) =
      (evalSym target_tm) (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

set_option maxRecDepth 2000000 in
theorem ruleB_step_AB (p m k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure (evalSym target_tm)
    (stepPure_sound (target_tm := target_tm)) 118
    (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 118 (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 118 (stateB sep3A sep3B (p + 1) (m + 2) (k +
      1) d2 R_tail)) =
      (evalSym target_tm) (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

set_option maxRecDepth 2000000 in
theorem ruleB_step_BA (p m k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure (evalSym target_tm)
    (stepPure_sound (target_tm := target_tm)) 106
    (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 106 (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 106 (stateB sep3B sep3A (p + 1) (m + 2) (k +
      1) d2 R_tail)) =
      (evalSym target_tm) (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

set_option maxRecDepth 2000000 in
theorem ruleB_step_BB (p m k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  have h := iterStep_sound stepPure (evalSym target_tm)
    (stepPure_sound (target_tm := target_tm)) 98
    (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail)
  have hrfl : iterStep stepPure 98 (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 98 (stateB sep3B sep3B (p + 1) (m + 2) (k + 1)
      d2 R_tail)) =
      (evalSym target_tm) (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

theorem ruleB_step_sound (s_sep m_sep : List SymTok) (hs : s_sep = sep3A ∨ s_sep = sep3B)
    (hm : m_sep = sep3A ∨ m_sep = sep3B) (p m k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateB s_sep m_sep (p + 1) (m + 2) (k + 1) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateB s_sep m_sep (p + 3) (m + 1) k (d2 + 4) R_tail)) := by
  rcases hs with rfl | rfl <;> rcases hm with rfl | rfl
  · exact ruleB_step_AA p m k d2 R_tail
  · exact ruleB_step_AB p m k d2 R_tail
  · exact ruleB_step_BA p m k d2 R_tail
  · exact ruleB_step_BB p m k d2 R_tail

theorem ruleB_iter (s_sep m_sep : List SymTok) (hs : s_sep = sep3A ∨ s_sep = sep3B)
    (hm : m_sep = sep3A ∨ m_sep = sep3B) (n p m k d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (stateB s_sep m_sep (p + 1) (m + n + 1) (k + n) d2 R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (stateB s_sep m_sep (p + 1 + 2 * n) (m + 1) k (d2 + 4 * n) R_tail)) := by
  induction n generalizing p m k d2 with
  | zero => simp; try exact stepStar_refl
  | succ n ih =>
    have h1 : m + (n + 1) + 1 = (m + n) + 2 := by omega
    have h2 : k + (n + 1) = (k + n) + 1 := by omega
    have h3 : p + 1 + 2 * (n + 1) = (p + 2) + 1 + 2 * n := by omega
    have h4 : d2 + 4 * (n + 1) = (d2 + 4) + 4 * n := by omega
    rw [h1, h2, h3, h4]
    exact stepStar_trans (ruleB_step_sound s_sep m_sep hs hm p (m + n) (k + n) d2 R_tail)
      (ih (p + 2) m k (d2 + 4))

theorem splitB2Aux_spec (fuel p : ℕ) (xs : List SymTok) :
    repBlock [.run 0, .run 1, .run 1] p ++ encSymL xs =
    repBlock [.run 0, .run 1, .run 1] (splitB2Aux fuel p xs).1 ++ encSymL (splitB2Aux fuel p xs).2
        := by
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

theorem repBlock_B2_shift (q : ℕ) (tail : List MItem) :
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

theorem tryRuleB_sound (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (.CB, L, .item .zero :: .item (.run d2) :: R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (tryRuleB L d2 R_tail)) := by
  unfold tryRuleB
  cases hsL : stripPrefixSym [.item (.run 0)] L with
  | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) ::
      R_tail)
  | some restL =>
    dsimp only [afterSplitB2]
    cases hsep1 : popSep3 (splitB2 0 restL).2 with
    | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) ::
        R_tail)
    | some sr1 =>
      rcases sr1 with ⟨s_sep, rest0⟩
      dsimp only
      cases h12 : popRep12 rest0 with
      | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) ::
          R_tail)
      | some mr1 =>
        rcases mr1 with ⟨m12, rest1⟩
        dsimp only
        cases hs1 : stripPrefixSym [.item (.run 1), .item (.run 0), .item (.run 1)] rest1 with
        | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) ::
            R_tail)
        | some rest2 =>
          dsimp only
          cases hsep2 : popSep3 rest2 with
          | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2)
              :: R_tail)
          | some mr2 =>
            rcases mr2 with ⟨m_sep, rest3⟩
            dsimp only
            cases hend : matchEndB1 rest3 with
            | none => dsimp only; exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2)
                :: R_tail)
            | some k1 =>
              dsimp only
              cases hcond : (Nat.ble 2 (splitB2 0 restL).1 && Nat.ble 2 m12 && Nat.ble m12 k1)
              · exact stepElemThenBB_sound .CB L (.item .zero :: .item (.run d2) :: R_tail)
              · simp only [strictNat_eq]
                have hL := stripPrefixSym_some _ L restL hsL
                have hspec := splitB2Aux_spec 32 0 restL
                simp only [repBlock, List.nil_append] at hspec
                change encSymL restL = repBlock [.run 0, .run 1, .run 1] (splitB2 0 restL).1 ++
                    encSymL (splitB2 0 restL).2 at hspec
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
                have hp_new : (splitB2 0 restL).1 + 2 * (m12 - 1) - 1 = p0 + 1 + 2 * n3 := by
                    omega
                have hk_new : k1 - (m12 - 1) = k_new := rfl
                have hd_new : d2 + 4 * (m12 - 1) = d2 + 4 * n3 := rfl
                have hlhs : (evalSym target_tm) (.CB, L, .item .zero :: .item (.run d2) :: R_tail)
                    =
                    (evalSym target_tm) (stateB s_sep m_sep (p0 + 1) (0 + n3 + 1) (k_new + n3) d2
                        R_tail) := by
                  simp only [evalSym, stateB, hL, encSymL, hspec, h_s, h_m12, h_r1, h_m, h_k1,
                    hp_eq, hm_eq, hk_eq, repBlock_B2_shift (p0 + 1), List.cons_append,
                        List.nil_append, List.append_assoc]
                rw [hlhs, hp_new]
                exact ruleB_iter s_sep m_sep hs_or hm_or n3 p0 0 k_new d2 R_tail

theorem tryRuleBC_sound (L : List SymTok) (d2 : ℕ) (R_tail : List SymTok) :
    ((evalSym target_tm) (.CB, L, .item .zero :: .item (.run d2) :: R_tail)) [target_tm]⊢*
    ((evalSym target_tm) (tryRuleBC L d2 R_tail)) := by
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
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1)]
          restC with
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

theorem afterSweepCB_sound (p : List SymTok × List SymTok) :
    ((evalSym target_tm) (.CB, p.1, p.2)) [target_tm]⊢* ((evalSym target_tm) (afterSweepCB p)) :=
        by
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

theorem stepSym_sound (s : SymMode × List SymTok × List SymTok) :
    ((evalSym target_tm) s) [target_tm]⊢* ((evalSym target_tm) (stepSym s)) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | BB => exact sweepBB_sound L R
  | DL =>
    simp only [stepSym, strictList_eq]
    have heq : (evalSym target_tm) (.DL, L, R) = (evalSym target_tm) (.DL, peelL L, R) := by
      simp only [evalSym, encSymL_peelL]
    rw [heq]
    exact stepElemThenBB_sound .DL (peelL L) R
  | HALT => exact stepStar_refl
  | CB =>
    exact stepStar_trans (sweepCB_sound L R) (afterSweepCB_sound (sweepCB L R))

theorem stepSym16_sound (s : SymMode × List SymTok × List SymTok) :
    ((evalSym target_tm) s) [target_tm]⊢* ((evalSym target_tm) (stepSym16 s)) :=
  iterStep_sound stepSym (evalSym target_tm) (stepSym_sound (target_tm := target_tm)) 16 s

theorem stepSym256_sound (s : SymMode × List SymTok × List SymTok) :
    ((evalSym target_tm) s) [target_tm]⊢* ((evalSym target_tm) (stepSym256 s)) :=
  iterStep_sound stepSym16 (evalSym target_tm) (stepSym16_sound (target_tm := target_tm)) 16 s

theorem stepSym4096_sound (s : SymMode × List SymTok × List SymTok) :
    ((evalSym target_tm) s) [target_tm]⊢* ((evalSym target_tm) (stepSym4096 s)) :=
  iterStep_sound stepSym256 (evalSym target_tm) (stepSym256_sound (target_tm := target_tm)) 16 s

theorem stepElem16_sound (s : SymMode × List MItem × List MItem) :
    ((evalM target_tm) s) [target_tm]⊢* ((evalM target_tm) (stepElem16 s)) :=
  iterStep_sound stepElemM (evalM target_tm) (stepElemM_sound (target_tm := target_tm)) 16 s

theorem stepElem256_sound (s : SymMode × List MItem × List MItem) :
    ((evalM target_tm) s) [target_tm]⊢* ((evalM target_tm) (stepElem256 s)) :=
  iterStep_sound stepElem16 (evalM target_tm) (stepElem16_sound (target_tm := target_tm)) 16 s

theorem stepElem4096_sound (s : SymMode × List MItem × List MItem) :
    ((evalM target_tm) s) [target_tm]⊢* ((evalM target_tm) (stepElem4096 s)) :=
  iterStep_sound stepElem256 (evalM target_tm) (stepElem256_sound (target_tm := target_tm)) 16 s

theorem runElemFast_sound (a b c d : ℕ) (s : SymMode × List MItem × List MItem) :
    (evalM target_tm s) [target_tm]⊢* (evalM target_tm (runElemFast a b c d s)) := by
  unfold runElemFast
  exact stepStar_trans
    (iterStep_sound stepElem4096 (evalM target_tm)
      (stepElem4096_sound (target_tm := target_tm)) d s)
    (stepStar_trans
      (iterStep_sound stepElem256 (evalM target_tm)
        (stepElem256_sound (target_tm := target_tm)) c _)
      (stepStar_trans
        (iterStep_sound stepElem16 (evalM target_tm)
          (stepElem16_sound (target_tm := target_tm)) b _)
        (iterStep_sound stepElemM (evalM target_tm)
          (stepElemM_sound (target_tm := target_tm)) a _)))

end BusyBeaver.SymRunEngine

namespace BusyBeaver.BufferChainEngine

open Counter SixState

@[simp] theorem init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
    ⟨some A, ⟨0, default, default⟩⟩ := rfl

def encWord : LD → List (Fin 2)
  | .W0 => [1, 0, 0]
  | .W1 => [1, 1, 1]

/-- Left tape encoding with the invariant MSB sentinel `[.W1, .W1]` (`[1, 1, 1, 1, 1, 1]`) built
in. -/
def Lmp (x : List LD) : ListBlank (Fin 2) :=
  encTape encWord ([1, 1, 1, 1, 1, 1] +> default) x

@[simp] theorem Lmp_nil : Lmp [] = [1, 1, 1, 1, 1, 1] +> default := rfl

theorem Lmp_cons (d : LD) (xs : List LD) : Lmp (d :: xs) = encWord d +> Lmp xs :=
  encTape_cons encWord ([1, 1, 1, 1, 1, 1] +> default) d xs

@[simp] theorem Lmp_W0 (xs : List LD) :
    Lmp (.W0 :: xs) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> Lmp xs := by
  rw [Lmp_cons]; rfl

@[simp] theorem Lmp_W1 (xs : List LD) :
    Lmp (.W1 :: xs) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lmp xs := by
  rw [Lmp_cons]; rfl

@[simp] theorem Lmp_head (x : List LD) : (Lmp x).head = 1 := by
  cases x with
  | nil => rfl
  | cons d xs => cases d <;> simp [Lmp_W0, Lmp_W1]

@[simp] theorem Lmp_cons_tail (x : List LD) :
    (1 : Fin 2) >> (Lmp x).tail = Lmp x := by
  rw [← Lmp_head x, Turing.ListBlank.cons_head_tail]

def RC (m : ℕ) : ListBlank (Fin 2) :=
  [1] +> ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default))

def cfgL (qL : Fin 6) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l <{{qL}} ([0, 1, 0] +> r)

def cfgR (qR : Fin 6) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l {{qR}}> ([1] +> r)

def x0 : List LD := [.W1, .W0, .W0, .W0, .W1, .W1, .W1, .W0]

def x1 : List LD :=
  [.W1, .W0, .W1, .W0, .W1, .W1, .W0, .W0, .W1, .W1, .W0, .W1, .W0, .W1, .W0]

def ux2 : List LD :=
  [.W1, .W1, .W0, .W1, .W0, .W1, .W0, .W0, .W1, .W1, .W0, .W0, .W0, .W0, .W1, .W1, .W1, .W0]

def x2 : List LD := (([.W1, .W0] : List LD) ^ 25) ++ ux2

def u0_tail : List LD :=
  [.W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1,
   .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1,
   .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W0, .W0, .W0,
   .W1, .W1, .W0, .W0, .W0, .W0, .W1, .W1, .W1, .W1, .W0, .W1, .W0, .W1, .W0]

def u0 : List LD := .W1 :: .W1 :: u0_tail

def c_init_30 : CCfg (Fin 2) (Fin 6) := ⟨A, 0, [], ([0] : List (Fin 2)) ^ 30⟩

def c_x0 (qL : Fin 6) : CCfg (Fin 2) (Fin 6) :=
  ⟨qL, 1,
   [1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1],
   [0, 1, 0, 1, 0, 1, 1, 0, 1]⟩

set_option maxRecDepth 200000 in
theorem isBuffer_191_B1 : IsBuffer 191 [.W1, .W1, .W0] := by decide

def msb_17 : List LD :=
  [.W0, .W1, .W1, .W0, .W1, .W1, .W0, .W1, .W1, .W0, .W1, .W1, .W0, .W1, .W1, .W1, .W1]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
-- `runU 191 u0` unfolds 191 rounds of finite macro-stepping.
def u191 : List LD := (runU 191 u0).getD []

set_option maxRecDepth 200000 in
def u191_pre' : List LD := ((lincspFinite u191).getD []).take 436

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
-- Kernel verification of the 191-round `runU` trajectory.
theorem runU_191_eq : runU 191 u0 = some u191 := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
-- Kernel verification of `lincspFinite u191`.
theorem u191_lincsp_eq : lincspFinite u191 = some (u191_pre' ++ msb_17) := by decide

set_option maxRecDepth 200000 in
theorem u191_pre'_only011 : checkOnly011 u191_pre' = true := by decide

structure Spec (tm : Machine (Fin 2) (Fin 6)) (qL qR : Fin 6) : Prop where
  w0_1 : ∀ xs r, (cfgL qL (Lmp (.W0 :: xs)) ([1] +> r)) [tm]⊢*
    (cfgL qL (Lmp xs) ([1, 0, 1, 1] +> r))
  w10 : ∀ xs r, (cfgL qL (Lmp (.W1 :: .W0 :: xs)) ([1] +> r)) [tm]⊢*
    (cfgR qR (Lmp (.W1 :: .W1 :: xs)) ([0, 1, 1] +> r))
  w11_1 : ∀ xs r, (cfgL qL (Lmp (.W1 :: .W1 :: xs)) ([1] +> r)) [tm]⊢*
    (cfgL qL (Lmp xs) ([1, 0, 1, 0, 1, 0, 1] +> r))
  rw0 : ∀ xs r, (cfgR qR (Lmp xs) ([0, 1, 1] +> r)) [tm]⊢*
    (cfgR qR (Lmp (.W0 :: xs)) r)
  rw11 : ∀ xs' r, (cfgR qR (Lmp xs') ([0, 1, 1, 0, 1, 0, 1, 0, 1] +> r)) [tm]⊢*
    (cfgR qR (Lmp (.W1 :: .W0 :: xs')) ([0, 1, 1] +> r))
  turn : ∀ x, (cfgR qR (Lmp x) ([0, 1] +> default)) [tm]⊢*
    (cfgL qL (Lmp x) (RC 0))
  lov_nil : ∀ r, (cfgL qL (Lmp []) ([1] +> r)) [tm]⊢*
    ((Lmp [.W0, .W0]) {{qR}}> r)
  lov_w0 : ∀ u r, ((Lmp u) {{qR}}> ([0, 1, 1] +> r)) [tm]⊢*
    ((Lmp (.W1 :: u)) {{qR}}> r)
  lov_w11_0 : ∀ x r, ((Lmp (.W0 :: x)) {{qR}}> ([0, 1, 0, 1, 0, 1] +> r)) [tm]⊢*
    ((Lmp (.W0 :: .W0 :: .W1 :: x)) {{qR}}> r)
  lov_w11_1_start : ∀ z r, ((Lmp (.W1 :: z)) {{qR}}> ([0, 1, 0, 1, 0, 1] +> r)) [tm]⊢*
    (cfgL qL (Lmp z) ([1, 0, 1, 1, 0, 1] +> r))
  lov_w11_1_end : ∀ z' r, (cfgR qR (Lmp z') ([0, 1, 1, 0, 1, 1, 0, 1] +> r)) [tm]⊢*
    ((Lmp (.W0 :: .W0 :: .W0 :: z')) {{qR}}> r)
  lov_finish : ∀ y, ((Lmp (.W1 :: y)) {{qR}}> ([0, 1] +> default)) [tm]⊢*
    (cfgL qL (Lmp y) (RC 0))

section WithSpec

variable {tm : Machine (Fin 2) (Fin 6)} {qL qR : Fin 6} (S : Spec tm qL qR)
include S

theorem LInc_step {x x' : List LD} (h : LInc x x') :
    ∀ (r : ListBlank (Fin 2)),
      (cfgL qL (Lmp x) ([1] +> r)) [tm]⊢* (cfgR qR (Lmp x') ([0, 1, 1] +> r)) := by
  induction h with
  | @w0 xs xs' _ ih =>
    intro r
    exact stepStar_trans (S.w0_1 xs r)
      (stepStar_trans (ih ([0, 1, 1] +> r)) (S.rw0 xs' ([0, 1, 1] +> r)))
  | w10 xs =>
    intro r; exact S.w10 xs r
  | @w11 xs xs' _ ih =>
    intro r
    exact stepStar_trans (S.w11_1 xs r)
      (stepStar_trans (ih ([0, 1, 0, 1, 0, 1] +> r)) (S.rw11 xs' r))

theorem RC_return : ∀ (m : ℕ) (x : List LD),
    (cfgR qR (Lmp x) ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default)))
      [tm]⊢* (cfgL qL (Lmp x) (RC m))
  | 0, x => S.turn x
  | m + 1, x => by
    rw [pow_succ_list, listblank_append_assoc]
    exact stepStar_trans (S.rw0 x ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default)))
      (stepStar_trans (RC_return m (.W0 :: x))
        (S.w0_1 x ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default))))

theorem LInc_RC {x x' : List LD} (h : LInc x x') (m : ℕ) :
    (cfgL qL (Lmp x) (RC m)) [tm]⊢* (cfgL qL (Lmp x') (RC (m + 1))) := by
  refine stepStar_trans
    (LInc_step S h ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default))) ?_
  exact RC_return S (m + 1) x'

theorem LIncs_RC {n : ℕ} {x x' : List LD} (h : LIncs n x x') :
    ∀ (m : ℕ), (cfgL qL (Lmp x) (RC m)) [tm]⊢* (cfgL qL (Lmp x') (RC (m + n))) :=
  IterRel_lift_rc (fun x m => cfgL qL (Lmp x) (RC m)) (LInc_RC S) h

theorem LOv2_correct_aux {w u y : List LD} (h : LOv2 w u y) (hu : u = [.W0, .W0]) :
    ∀ (r : ListBlank (Fin 2)),
      (cfgL qL (Lmp w) ([1] +> r)) [tm]⊢* ((Lmp y) {{qR}}> r) := by
  induction h with
  | nil =>
    subst hu; intro r; exact S.lov_nil r
  | @w0 xs _ u' _ ih =>
    intro r
    exact stepStar_trans (S.w0_1 xs r)
      (stepStar_trans (ih hu ([0, 1, 1] +> r)) (S.lov_w0 u' r))
  | @w11_0 xs _ x _ ih =>
    intro r
    exact stepStar_trans (S.w11_1 xs r)
      (stepStar_trans (ih hu ([0, 1, 0, 1, 0, 1] +> r)) (S.lov_w11_0 x r))
  | @w11_1 xs _ z z' _ hz ih =>
    intro r
    exact stepStar_trans (S.w11_1 xs r)
      (stepStar_trans (ih hu ([0, 1, 0, 1, 0, 1] +> r))
        (stepStar_trans (S.lov_w11_1_start z r)
          (stepStar_trans (LInc_step S hz ([0, 1, 1, 0, 1] +> r))
            (S.lov_w11_1_end z' r))))

theorem LOv2_correct {w y : List LD} (h : LOv2 w [.W0, .W0] y) :
    ∀ (r : ListBlank (Fin 2)),
      (cfgL qL (Lmp w) ([1] +> r)) [tm]⊢* ((Lmp y) {{qR}}> r) :=
  LOv2_correct_aux S h rfl

theorem lov_w0_iter : ∀ (m : ℕ) (y : List LD) (r : ListBlank (Fin 2)),
    ((Lmp y) {{qR}}> ((([0, 1, 1] : List (Fin 2)) ^ m) +> r))
      [tm]⊢*
    ((Lmp ((([.W1] : List LD) ^ m) ++ y)) {{qR}}> r)
  | 0, _, _ => stepStar_refl _ _
  | m + 1, y, r => by
    rw [pow_succ_right, listblank_append_assoc]
    refine stepStar_trans (lov_w0_iter m y ([0, 1, 1] +> r)) ?_
    have h3 := S.lov_w0 ((([.W1] : List LD) ^ m) ++ y) r
    rw [pow_succ_list, List.singleton_append, List.cons_append]
    exact h3

theorem full_overflow_step {w y : List LD} (m : ℕ) (h : LOv2 w [.W0, .W0] y) :
    (cfgL qL (Lmp w) (RC (m + 1))) [tm]⊢*
      (cfgL qL (Lmp ((([.W1] : List LD) ^ m) ++ y)) (RC 0)) := by
  refine stepStar_trans
    (LOv2_correct S h ((([0, 1, 1] : List (Fin 2)) ^ (m + 1)) +> ([0, 1] +> default))) ?_
  refine stepStar_trans (lov_w0_iter S (m + 1) y ([0, 1] +> default)) ?_
  rw [pow_succ_list, List.singleton_append, List.cons_append]
  exact S.lov_finish ((([.W1] : List LD) ^ m) ++ y)

theorem round_step {X X' Y Z : List LD} (m : ℕ)
    (h1 : LIncsP (2 * m + 1) X X')
    (h2 : LOv2 X' [.W0, .W0] Y)
    (h3 : LInc ((([.W1] : List LD) ^ (2 * m + 1)) ++ Y) Z) :
    (cfgL qL (Lmp X) (RC 1)) [tm]⊢* (cfgL qL (Lmp Z) (RC 1)) := by
  have h_incs := LIncs_RC S (LIncsP_to_LIncs h1) 1
  rw [Nat.add_comm 1 (2 * m + 1)] at h_incs
  exact stepStar_trans h_incs
    (stepStar_trans (full_overflow_step S (2 * m + 1) h2) (LInc_RC S h3 0))

set_option maxRecDepth 200000 in
theorem x0_to_x1 : (cfgL qL (Lmp x0) (RC 1)) [tm]⊢* (cfgL qL (Lmp x1) (RC 1)) := by
  let x0' : List LD := [.W1, .W1, .W0, .W0, .W1, .W1, .W1, .W1]
  let y0 : List LD := [.W0, .W0, .W0, .W1, .W1, .W0, .W1, .W0, .W1, .W0]
  have h1 : LIncsP (2 * 2 + 1) x0 x0' :=
    lincspFinite_sound (by decide : lincspFinite x0 = some x0')
  have h2 : LOv2 x0' [.W0, .W0] y0 :=
    lov2Finite_sound (by decide : lov2Finite x0' [.W0, .W0] = some y0)
  have h3 : LInc ((([.W1] : List LD) ^ (2 * 2 + 1)) ++ y0) x1 :=
    lincFinite_sound (by decide : lincFinite ((([.W1] : List LD) ^ 5) ++ y0) = some x1)
  exact round_step S 2 h1 h2 h3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
-- `x1_to_x2` verifies a 51-increment round via `decide`.
theorem x1_to_x2 : (cfgL qL (Lmp x1) (RC 1)) [tm]⊢* (cfgL qL (Lmp x2) (RC 1)) := by
  let x1' := (lincspFinite x1).getD []
  let y1 := (lov2Finite x1' [.W0, .W0]).getD []
  have h1 : LIncsP (2 * 25 + 1) x1 x1' :=
    lincspFinite_sound (by decide : lincspFinite x1 = some x1')
  have h2 : LOv2 x1' [.W0, .W0] y1 :=
    lov2Finite_sound (by decide : lov2Finite x1' [.W0, .W0] = some y1)
  have h3 : LInc ((([.W1] : List LD) ^ (2 * 25 + 1)) ++ y1) x2 :=
    lincFinite_sound (by decide : lincFinite ((([.W1] : List LD) ^ 51) ++ y1) = some x2)
  exact round_step S 25 h1 h2 h3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
-- `x2_to_x3` verifies the `x2` overflow round via `decide`.
theorem x2_to_x3 :
    ∃ m3 ≥ 511,
      (cfgL qL (Lmp x2) (RC 1)) [tm]⊢*
        (cfgL qL (Lmp ((([.W1, .W0] : List LD) ^ m3) ++ u0)) (RC 1)) := by
  let ux2' := (lincspFinite ux2).getD []
  have h_ux2 : LIncsP (lincspCount ux2) ux2 ux2' :=
    lincspFinite_sound (by decide : lincspFinite ux2 = some ux2')
  rcases LIncsP_pow_10 15 h_ux2 with ⟨n_suf, h_suf⟩
  have h_10 := LIncsP_pow10_bound h_suf
  have hx2_eq :
      ((([.W1, .W0] : List LD) ^ 10) ++ ((([.W1, .W0] : List LD) ^ 15) ++ ux2)) = x2 := by
    rw [← List.append_assoc, ← list_pow_add]; rfl
  let x2' := ((([.W1, .W1] : List LD) ^ 10) ++ ((([.W1, .W1] : List LD) ^ 15) ++ ux2'))
  rw [hx2_eq] at h_10
  have h_ov : LOv2 x2' [.W0, .W0] (.W0 :: u0_tail) :=
    lov2Finite_sound (by decide : lov2Finite x2' [.W0, .W0] = some (.W0 :: u0_tail))
  let m3 := 512 * n_suf + 511
  refine ⟨m3, by omega, ?_⟩
  have h_inc : LInc ((([.W1] : List LD) ^ (2 * m3 + 1)) ++ (.W0 :: u0_tail))
      ((([.W1, .W0] : List LD) ^ m3) ++ u0) := by
    rw [pow_W1_odd m3 (.W0 :: u0_tail)]
    exact LInc_pow_11_10 m3 u0_tail
  exact round_step S m3 h_10 h_ov h_inc

set_option maxRecDepth 200000 in
theorem chain_round_step {r : ℕ} (hr : r ≤ 191) {T : List LD} (hT : ChainTail (r + 1) T)
    {u u' : List LD} (hu : macroStepFinite u = some u') :
    ∃ T', ChainTail r T' ∧
      ((cfgL qL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T ++ u))) (RC 1))
        [tm]⊢*
      (cfgL qL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u'))) (RC 1))) := by
  rcases ChainTail_step hT hu with ⟨n, W', T₀', h_lp, h_ov, h_ct0⟩
  have h_10 := LIncsP_pow10_bound h_lp
  have h_ov10 : LOv2 ((([.W1, .W1] : List LD) ^ 10) ++ W') [.W0, .W0]
      ([.W0, .W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ (T₀' ++ u'))) :=
    LOv2_append (LOv2_pow_11 10 (T₀' ++ u')) h_ov
  let m := 512 * n + 511
  let B1 : List LD := [.W1, .W1, .W0]
  let tail_rest := ((([.W1, .W0] : List LD) ^ 11) ++ (T₀' ++ u'))
  have h_inc : LInc ((([.W1] : List LD) ^ (2 * m + 1)) ++
      ([.W0, .W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ (T₀' ++ u'))))
      ((([.W1, .W0] : List LD) ^ m) ++ (B1 ++ tail_rest)) := by
    dsimp only [m, B1, tail_rest]
    rw [pow_W1_odd]
    exact LInc_pow_11_10 (512 * n + 511)
      ([.W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ (T₀' ++ u')))
  have h_step := round_step S m h_10 h_ov10 h_inc
  have hm_split : m = 10 + ((m - 10 - 2 * r) + 2 * r) := by omega
  let T' := ((([.W1, .W0] : List LD) ^ (m - 10 - 2 * r)) ++
    ((([.W1, .W0] : List LD) ^ (2 * r)) ++ (B1 ++ ((([.W1, .W0] : List LD) ^ 11) ++ T₀'))))
  have hB1 : IsBuffer r B1 := isBuffer_le hr isBuffer_191_B1
  have h_ct_T' : ChainTail r T' :=
    ChainTail_pow_pair (m - 10 - 2 * r) (.buf hB1 (ChainTail_pow_pair 11 h_ct0))
  have h_eq : ((([.W1, .W0] : List LD) ^ m) ++ (B1 ++ tail_rest)) =
      ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u')) := by
    conv_lhs => rw [hm_split, list_pow_add, list_pow_add]
    simp only [T', tail_rest, List.append_assoc]
  rw [h_eq] at h_step
  exact ⟨T', h_ct_T', h_step⟩

theorem runU_steps : ∀ (k : ℕ) (r : ℕ), r + k ≤ 191 →
    ∀ {T u u' : List LD},
      ChainTail (r + k) T →
      runU k u = some u' →
      ∃ T', ChainTail r T' ∧
        ((cfgL qL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T ++ u))) (RC 1))
          [tm]⊢*
        (cfgL qL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u'))) (RC 1)))
  | 0, r, _, T, _, _, hT, hu => by
    injection hu with hu'; subst hu'
    exact ⟨T, hT, stepStar_refl _ _⟩
  | k + 1, r, hrk, T, u, u', hT, hu => by
    simp only [runU, Option.bind_eq_some_iff] at hu
    rcases hu with ⟨u₁, hu₁, hu₂⟩
    have h_eq : r + (k + 1) = (r + k) + 1 := by omega
    rw [h_eq] at hT
    rcases chain_round_step S (by omega : r + k ≤ 191) hT hu₁ with ⟨T₁, hT₁, h_step1⟩
    rcases runU_steps k r (by omega) hT₁ hu₂ with ⟨T', hT', h_step2⟩
    exact ⟨T', hT', stepStar_trans h_step1 h_step2⟩

theorem Only011_skip_1 {P : List LD} (hP : Only011 P) (s : List LD) :
    ∀ (r : ListBlank (Fin 2)),
      ∃ r', (cfgL qL (Lmp (P ++ s)) ([1] +> r)) [tm]⊢*
        (cfgL qL (Lmp s) ([1] +> r')) := by
  induction hP with
  | nil =>
    intro r; exact ⟨r, stepStar_refl _ _⟩
  | @w0 xs _ ih =>
    intro r
    rcases ih ([0, 1, 1] +> r) with ⟨r', hr'⟩
    exact ⟨r', stepStar_trans (S.w0_1 (xs ++ s) r) hr'⟩
  | @w11 xs _ ih =>
    intro r
    rcases ih ([0, 1, 0, 1, 0, 1] +> r) with ⟨r', hr'⟩
    exact ⟨r', stepStar_trans (S.w11_1 (xs ++ s) r) hr'⟩

theorem Only011_skip_10 {P : List LD} (hP : Only011 P) (s : List LD) :
    ∀ (r : ListBlank (Fin 2)),
      ∃ r', (cfgL qL (Lmp (P ++ s)) ([1, 0] +> r)) [tm]⊢*
        (cfgL qL (Lmp s) ([1, 0] +> r')) := by
  induction hP with
  | nil =>
    intro r; exact ⟨r, stepStar_refl _ _⟩
  | @w0 xs _ ih =>
    intro r
    rcases ih ([1, 1, 0] +> r) with ⟨r', hr'⟩
    exact ⟨r', stepStar_trans (S.w0_1 (xs ++ s) ([0] +> r)) hr'⟩
  | @w11 xs _ ih =>
    intro r
    rcases ih ([1, 0, 1, 0, 1, 0] +> r) with ⟨r', hr'⟩
    exact ⟨r', stepStar_trans (S.w11_1 (xs ++ s) ([0] +> r)) hr'⟩

set_option maxRecDepth 200000 in
theorem init_to_msb17
    (h_init : (init []) [tm]⊢* (cfgL qL (Lmp x0) (RC 1))) :
    ∃ P_all nAll, Only011 P_all ∧
      ((init []) [tm]⊢* (cfgL qL (Lmp (P_all ++ msb_17)) (RC (1 + nAll)))) := by
  have h01 := stepStar_trans h_init (stepStar_trans (x0_to_x1 S) (x1_to_x2 S))
  rcases x2_to_x3 S with ⟨m3, hm3, h23⟩
  have h_init_x3 := stepStar_trans h01 h23
  have hm3_split : m3 = 10 + ((m3 - 392) + 2 * 191) := by omega
  let T0 := ((([.W1, .W0] : List LD) ^ (m3 - 392)) ++ (([.W1, .W0] : List LD) ^ (2 * 191)))
  have h_T0 : ChainTail (0 + 191) T0 :=
    ChainTail_pow_pair (m3 - 392) .nil
  have h_x3_eq : ((([.W1, .W0] : List LD) ^ m3) ++ u0) =
      ((([.W1, .W0] : List LD) ^ 10) ++ (T0 ++ u0)) := by
    conv_lhs => rw [hm3_split, list_pow_add, list_pow_add]
    simp only [T0, List.append_assoc]
  rw [h_x3_eq] at h_init_x3
  rcases runU_steps S 191 0 (by omega) h_T0 runU_191_eq with ⟨T191, h_T191, h_rounds⟩
  have h_to_191 := stepStar_trans h_init_x3 h_rounds
  rcases ChainTail_zero_lincsp h_T191 with ⟨_, T191', h_lpT⟩
  have h_lpU := lincspFinite_sound u191_lincsp_eq
  rcases LIncsP_append h_lpT h_lpU with ⟨_, h_lpTU⟩
  rcases LIncsP_pow_10 10 h_lpTU with ⟨nAll, h_lpAll⟩
  have h_incs_final := LIncs_RC S (LIncsP_to_LIncs h_lpAll) 1
  have h_to_inc := stepStar_trans h_to_191 h_incs_final
  have h_10T_only : Only011 ((([.W1, .W1] : List LD) ^ 10) ++ T191') := by
    rcases LIncsP_pow_10 10 h_lpT with ⟨_, h10T⟩
    exact LIncsP_only011 h10T
  let P_all := ((([.W1, .W1] : List LD) ^ 10) ++ T191') ++ u191_pre'
  have h_P_only : Only011 P_all :=
    Only011_append h_10T_only (checkOnly011_sound u191_pre'_only011)
  have h_assoc : ((([.W1, .W1] : List LD) ^ 10) ++ (T191' ++ (u191_pre' ++ msb_17))) =
      P_all ++ msb_17 := by
    simp only [P_all, List.append_assoc]
  rw [h_assoc] at h_to_inc
  exact ⟨P_all, nAll, h_P_only, h_to_inc⟩

theorem is_halt_of_msb17_10
    (h_init : (init []) [tm]⊢* (cfgL qL (Lmp x0) (RC 1)))
    (h_msb : ∀ r, ∃ cfg, ((cfgL qL (Lmp msb_17) ([1, 0] +> r)) [tm]⊢* cfg) ∧
      (step tm cfg).isNone) :
    IsHalt tm := by
  rcases init_to_msb17 S h_init with ⟨P_all, nAll, h_P_only, h_to_inc⟩
  have h_rc_eq : RC (1 + nAll) =
      [1, 0] +> ([1, 1] +> ((([0, 1, 1] : List (Fin 2)) ^ nAll) +> ([0, 1] +> default))) := by
    rw [Nat.add_comm 1 nAll]; rfl
  rw [h_rc_eq] at h_to_inc
  rcases Only011_skip_10 S h_P_only msb_17
      ([1, 1] +> ((([0, 1, 1] : List (Fin 2)) ^ nAll) +> ([0, 1] +> default))) with ⟨r', h_skip⟩
  rcases h_msb r' with ⟨cfg_halt, h_halt_steps, h_is_none⟩
  exact ⟨cfg_halt, stepStar_trans (stepStar_trans h_to_inc h_skip) h_halt_steps, h_is_none⟩

theorem is_halt_of_msb17_1
    (h_init : (init []) [tm]⊢* (cfgL qL (Lmp x0) (RC 1)))
    (h_msb : ∀ r, ∃ cfg, ((cfgL qL (Lmp msb_17) ([1] +> r)) [tm]⊢* cfg) ∧
      (step tm cfg).isNone) :
    IsHalt tm := by
  rcases init_to_msb17 S h_init with ⟨P_all, nAll, h_P_only, h_to_inc⟩
  rcases Only011_skip_1 S h_P_only msb_17
      ((([0, 1, 1] : List (Fin 2)) ^ (1 + nAll)) +> ([0, 1] +> default)) with ⟨r', h_skip⟩
  rcases h_msb r' with ⟨cfg_halt, h_halt_steps, h_is_none⟩
  exact ⟨cfg_halt, stepStar_trans (stepStar_trans h_to_inc h_skip) h_halt_steps, h_is_none⟩

end WithSpec

macro "buf_step1" : tactic => `(tactic| (
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, cfgL, cfgR, RC, Lmp_W0,
    Lmp_W1, Lmp_nil, Lmp_head, Lmp_cons_tail, pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append, listblank_append_cons,
    listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  refine multiStep_step (by rfl) ?_
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move, Tape.write,
    Lmp_head, Lmp_cons_tail, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
    default_tail]))

macro "buf_run_steps" n:num : tactic => `(tactic| (
  iterate $n buf_step1
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, cfgL, cfgR, RC, Lmp_W0, Lmp_W1,
    Lmp_nil, Lmp_head, Lmp_cons_tail, pow_succ_list, pow_zero_list, List.singleton_append,
    List.nil_append, List.cons_append, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
    default_tail, multiStep_zero]))

theorem init_to_x0_of_cmultiStep {tm : Machine (Fin 2) (Fin 6)} {qL : Fin 6} {k : ℕ}
    (h_steps : cmultiStep tm k c_init_30 = some (c_x0 qL)) :
    (init []) [tm]⊢* (cfgL qL (Lmp x0) (RC 1)) := by
  have h_eq1 : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = evalCCfg default c_init_30 := by
    rw [init_nil]
    simp [evalCCfg, evalWindow, c_init_30]
  have h_eq2 : evalCCfg default (c_x0 qL) = cfgL qL (Lmp x0) (RC 1) := rfl
  rw [h_eq1, ← h_eq2]
  exact ⟨k, cmultiStep_sound k c_init_30 (c_x0 qL) default h_steps⟩

end BusyBeaver.BufferChainEngine

end
