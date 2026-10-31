/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_HHH1RD

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 3, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

-- ============================================================================
-- Section 1: Execution Helpers, Closed-Invariant Criterion & Stack Rules
-- ============================================================================

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

lemma multiStep_step_isSome {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₀ cfg cfg' : Cfg Γ Λ) (n m : Nat)
    (hn : multiStep M c₀ n = some cfg)
    (hnm : multiStep M c₀ (n + (1 + m)) = some cfg') :
    (step M cfg).isSome := by
  rw [multiStep_add M c₀ n (1 + m), hn] at hnm
  dsimp [Option.bind] at hnm
  rw [multiStep_add M cfg 1 m, multiStep_one] at hnm
  cases hs : step M cfg with
  | none => rw [hs] at hnm; nomatch hnm
  | some _ => rfl

lemma inv_reaches_beyond {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ cfg₀, ((init []) [M]⊢* cfg₀) ∧ Inv cfg₀)
    (h_step : ∀ cfg, Inv cfg → ∃ cfg', (cfg [M]⊢⁺ cfg') ∧ Inv cfg')
    (N : Nat) :
    ∃ (m : Nat) (cfg' : Cfg Γ Λ), multiStep M (init []) (N + m) = some cfg' ∧ Inv cfg' := by
  induction N with
  | zero =>
    obtain ⟨cfg₀, ⟨n₀, hn₀⟩, h_inv₀⟩ := h_init
    refine ⟨n₀, cfg₀, ?_, h_inv₀⟩
    rwa [Nat.zero_add]
  | succ N ih =>
    obtain ⟨m, cfg₁, hm, h_inv₁⟩ := ih
    cases m with
    | zero =>
      obtain ⟨cfg₂, ⟨k, hk_pos, hk⟩, h_inv₂⟩ := h_step cfg₁ h_inv₁
      cases k with
      | zero => omega
      | succ k' =>
        refine ⟨k', cfg₂, ?_, h_inv₂⟩
        have h_trans := multiStep_trans M (init []) cfg₁ cfg₂ N (k' + 1) hm hk
        have h_eq : (N + 1) + k' = N + (k' + 1) := by omega
        rwa [h_eq]
    | succ m' =>
      refine ⟨m', cfg₁, ?_, h_inv₁⟩
      have h_eq : (N + 1) + m' = N + (m' + 1) := by omega
      rwa [h_eq]

theorem closed_inv_does_not_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ cfg₀, ((init []) [M]⊢* cfg₀) ∧ Inv cfg₀)
    (h_step : ∀ cfg, Inv cfg → ∃ cfg', (cfg [M]⊢⁺ cfg') ∧ Inv cfg') :
    IsNotHalt M := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome M (init []) cfg cfg' n m hn hnm

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

def tailWeight : List ℕ → ℕ
  | [] => 0
  | d :: _ => d

def headWeight : List ℕ → ℕ
  | [] => 0
  | a :: _ => a + 1

@[simp] lemma encRight_tail_cons_one (R : List ℕ) :
    (1 : Fin 2) >> (encRight1 R).tail = encRight1 (tailWeight R :: R.tail) := by
  cases R with
  | nil => simp [tailWeight, encRight1]
  | cons d R' => dsimp [tailWeight, List.tail]; simp

@[simp] lemma encRight_bumpHead_tail (R : List ℕ) :
    (encRight1 (bumpHead R)).tail = encRight1 R := by
  cases R with
  | nil => simp [bumpHead, encRight1]
  | cons d R' => dsimp [bumpHead, encRight1]; simp

lemma encRight_tail_decomp (R : List ℕ) :
    (encRight1 R).tail = (([1] : List (Fin 2)) ^ (tailWeight R)) +> ((encRight1 R.tail).cons 0) := by
  cases R with
  | nil => simp [tailWeight, encRight1]
  | cons d R' => dsimp [tailWeight, List.tail, encRight1]; simp

lemma encLeft_decomp (L : List ℕ) :
    encLeft1 L = ((encLeft1 L.tail).cons 0) <+ (([1] : List (Fin 2)) ^ (headWeight L)) := by
  cases L <;> simp [headWeight, encLeft1]

macro "finish" : tactic => `(tactic| (refine ⟨0, ?_⟩; simp only [zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one, encRight_cons_one, encRight_tail_cons_one, encRight_bumpHead_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]; try rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

def cfg_BR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encLeft1 L, (encRight1 R).tail⟩⟩

def cfg_ER (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((encLeft1 L).cons 0) {{E}}> ((encRight1 R).tail)

def cfg_E00 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_ER L (0 :: R)

lemma b_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{B}} r) [target_tm]⊢*
    (l <{{B}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero =>
    dsimp [HPow.hPow, list_nat_repeat]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, listblank_append_right_assoc]
    have h1 : (((l <+ (([1] : List (Fin 2)) ^ k)) <+ (([1] : List (Fin 2)) ^ 1)) <{{B}} r)
        [target_tm]⊢⁺
        ((l <+ (([1] : List (Fin 2)) ^ k)) <{{B}} (([1] : List (Fin 2)) ^ 1 +> r)) := by
      dsimp [HPow.hPow, list_nat_repeat]
      execute 1
    refine stepStar_trans (stepPlus_stepStar h1) ?_
    refine stepStar_trans (ih l (([1] : List (Fin 2)) ^ 1 +> r)) ?_
    rw [← listblank_append_right_assoc, list_pow_add_comm]
    exact ⟨0, rfl⟩

theorem rule_BR_nil (R : List ℕ) :
    (cfg_BR [] R) [target_tm]⊢⁺ (cfg_ER [0] R) := by
  unfold cfg_BR cfg_ER
  rw [encLeft_cons, encLeft_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR (0 :: L) R) [target_tm]⊢⁺
    (cfg_BR L.tail ((tailWeight R + headWeight L + 3) :: R.tail)) := by
  unfold cfg_BR
  rw [encLeft_cons 0 L, encLeft_decomp L, encRight_tail_decomp R]
  have h_pre : (⟨some B, ⟨0, ((((encLeft1 L.tail).cons 0) <+ (([1] : List (Fin 2)) ^ (headWeight L))).cons 0) <+ (([1] : List (Fin 2)) ^ (0 + 1)), (([1] : List (Fin 2)) ^ (tailWeight R)) +> ((encRight1 R.tail).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      ((((encLeft1 L.tail).cons 0) <+ (([1] : List (Fin 2)) ^ (headWeight L))) <{{B}} ((([1] : List (Fin 2)) ^ 3) +> ((([1] : List (Fin 2)) ^ (tailWeight R)) +> ((encRight1 R.tail).cons 0)))) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 5
  refine stepPlus_stepStar_stepPlus h_pre ?_
  refine stepStar_trans (b_walk_left (headWeight L) ((encLeft1 L.tail).cons 0) ((([1] : List (Fin 2)) ^ 3) +> ((([1] : List (Fin 2)) ^ (tailWeight R)) +> ((encRight1 R.tail).cons 0)))) ?_
  rw [listblank_right_pow_add, listblank_right_pow_add]
  have h_eq : headWeight L + 3 + tailWeight R = tailWeight R + headWeight L + 3 := by omega
  rw [h_eq, encRight_tail_decomp ((tailWeight R + headWeight L + 3) :: R.tail)]
  dsimp [tailWeight, List.tail]
  finish

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR (1 :: L) R) [target_tm]⊢⁺ (cfg_BR L (0 :: (tailWeight R + 1) :: R.tail)) := by
  unfold cfg_BR
  rw [encLeft_cons 1 L]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_BR_ge2 (a : ℕ) (L R : List ℕ) :
    (cfg_BR ((a + 2) :: L) R) [target_tm]⊢⁺
    (cfg_BR L ((a + 1) :: (tailWeight R + 1) :: R.tail)) := by
  unfold cfg_BR
  rw [encLeft_cons (a + 2) L]
  have h_split : a + 2 + 1 = 2 + (a + 1) := by omega
  rw [h_split, list_pow_add, listblank_append_right_assoc]
  have h_pre : (⟨some B, ⟨0, (((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <+ (([1] : List (Fin 2)) ^ 2), (encRight1 R).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
      ((((encLeft1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <{{B}} ((encRight1 ((tailWeight R + 1) :: R.tail)).cons 0)) := by
    dsimp [HPow.hPow, list_nat_repeat]
    execute 3
  refine stepPlus_stepStar_stepPlus h_pre ?_
  refine stepStar_trans (b_walk_left (a + 1) ((encLeft1 L).cons 0) ((encRight1 ((tailWeight R + 1) :: R.tail)).cons 0)) ?_
  rw [encRight_tail_decomp ((a + 1) :: (tailWeight R + 1) :: R.tail)]
  dsimp [tailWeight, List.tail]
  finish

theorem rule_ER_nil (L : List ℕ) :
    (cfg_ER L []) [target_tm]⊢⁺ (cfg_BR L [3]) := by
  unfold cfg_ER cfg_BR
  rw [encRight_cons 3 [], encRight_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 7

theorem rule_ER_zero_zero_nil (L : List ℕ) :
    (cfg_ER L [0, 0]) [target_tm]⊢⁺ (cfg_BR (bumpHead L) [3]) := by
  unfold cfg_ER cfg_BR
  rw [encRight_cons 0 [0], encRight_cons 0 [], encRight_cons 3 [], encRight_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 12

theorem rule_ER_zero_zero_cons (e : ℕ) (L R' : List ℕ) :
    (cfg_ER L (0 :: 0 :: e :: R')) [target_tm]⊢⁺
    (cfg_ER (bumpHead (bumpHead L)) ((e + 2) :: R')) := by
  unfold cfg_ER
  rw [encRight_cons 0 (0 :: e :: R'), encRight_cons 0 (e :: R'), encRight_cons e R', encRight_cons (e + 2) R']
  dsimp [HPow.hPow, list_nat_repeat]
  execute 12

theorem rule_ER_zero_succ (d : ℕ) (L R' : List ℕ) :
    (cfg_ER L (0 :: (d + 1) :: R')) [target_tm]⊢⁺ (cfg_ER (bumpHead L) (0 :: d :: R')) := by
  unfold cfg_ER
  rw [encRight_cons 0 ((d + 1) :: R'), encRight_cons (d + 1) R', encRight_cons 0 (d :: R'), encRight_cons d R']
  dsimp [HPow.hPow, list_nat_repeat]
  execute 5

theorem rule_ER_two (L R' : List ℕ) :
    (cfg_ER L (2 :: R')) [target_tm]⊢⁺ (cfg_ER (1 :: L) (bumpHead R')) := by
  unfold cfg_ER
  rw [encRight_cons 2 R', encLeft_cons 1 L]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_ER_ge3 (d : ℕ) (L R' : List ℕ) :
    (cfg_ER L ((d + 3) :: R')) [target_tm]⊢⁺ (cfg_ER (1 :: L) (d :: R')) := by
  unfold cfg_ER
  rw [encRight_tail_decomp ((d + 3) :: R'), encRight_tail_decomp (d :: R'), encLeft_cons 1 L]
  dsimp [tailWeight, List.tail, HPow.hPow, list_nat_repeat]
  execute 3

theorem rule_ER_peel_all (L R : List ℕ) (d k : ℕ) :
    (cfg_ER L ((d + 3 * k) :: R)) [target_tm]⊢*
    (cfg_ER (List.replicate k 1 ++ L) (d :: R)) := by
  induction k generalizing L with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, List.replicate, List.nil_append]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_arith : d + 3 * (k + 1) = (d + 3 * k) + 3 := by omega
    rw [h_arith]
    refine stepStar_trans (stepPlus_stepStar (rule_ER_ge3 (d + 3 * k) L R)) ?_
    refine stepStar_trans (ih (1 :: L)) ?_
    have h_rep : List.replicate k 1 ++ (1 :: L) = List.replicate (k + 1) 1 ++ L := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [h_rep]
    exact ⟨0, rfl⟩

theorem rule_E00_peel_all (a d k : ℕ) (L R : List ℕ) :
    (cfg_E00 (a :: L) ((d + k) :: R)) [target_tm]⊢*
    (cfg_E00 ((a + k) :: L) (d :: R)) := by
  unfold cfg_E00
  induction k generalizing a with
  | zero =>
    simp only [Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_arith : d + (k + 1) = (d + k) + 1 := by omega
    rw [h_arith]
    have h1 := rule_ER_zero_succ (d + k) (a :: L) R
    dsimp [bumpHead] at h1
    refine stepStar_trans (stepPlus_stepStar h1) ?_
    refine stepStar_trans (ih (a + 1)) ?_
    have h_eq : (a + 1) + k = a + (k + 1) := by omega
    rw [h_eq]
    exact ⟨0, rfl⟩

theorem init_to_cfg_BR :
    (init []) [target_tm]⊢⁺ (cfg_BR [0] []) := by
  unfold cfg_BR
  rw [encLeft_cons, encLeft_nil, encRight_nil]
  dsimp [HPow.hPow, list_nat_repeat]
  execute 1

-- ============================================================================
-- Section 2: `B`-Coordinates, `SweepRel`, and Machine Soundness (`SweepRel_sound`)
-- ============================================================================

def incList (B : List ℕ) : List ℕ := B.map (· + 1)

@[simp] lemma incList_nil : incList [] = [] := rfl
@[simp] lemma incList_cons (b : ℕ) (B : List ℕ) : incList (b :: B) = (b + 1) :: incList B := rfl

lemma incList_append (X Y : List ℕ) : incList (X ++ Y) = incList X ++ incList Y :=
  List.map_append

lemma incList_replicate_zero (n : ℕ) : incList (List.replicate n 0) = List.replicate n 1 := by
  induction n <;> simp [incList, *]

def midR : List ℕ → List ℕ
  | [] => []
  | b₀ :: B' => b₀ :: incList B'

def toR_B : List ℕ → List ℕ
  | [] => []
  | b₀ :: B' => (b₀ + 3) :: incList B'

def evalB (B : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_ER [0] (toR_B B)

def fromQ (u : List ℕ) : List ℕ := u.map (3 * ·)

@[simp] lemma fromQ_nil : fromQ [] = [] := rfl
@[simp] lemma fromQ_cons (q : ℕ) (u : List ℕ) : fromQ (q :: u) = (3 * q) :: fromQ u := rfl

lemma fromQ_append (u v : List ℕ) : fromQ (u ++ v) = fromQ u ++ fromQ v :=
  List.map_append

lemma fromQ_replicate_zero (n : ℕ) : fromQ (List.replicate n 0) = List.replicate n 0 := by
  induction n <;> simp [fromQ, *]

def stepBlock : List ℕ → List ℕ
  | [] => []
  | [q] => List.replicate q 0
  | q :: y :: rest => List.replicate q 0 ++ (y + 1) :: stepBlock rest

def sb₁ (u : List ℕ) : List ℕ := stepBlock (0 :: u)

def sumQ1 : List ℕ → ℕ
  | [] => 0
  | q :: rest => (q + 1) + sumQ1 rest

def weightDigit (b : ℕ) : ℕ :=
  if b % 3 == 2 then b + 4 else b + 3

def weightB : List ℕ → ℕ
  | [] => 0
  | b :: rest => weightDigit b + weightB rest

lemma rule_BR_midR (a : ℕ) (L B : List ℕ) (hB : B ≠ []) :
    (cfg_BR ((a + 1) :: L) (midR B)) [target_tm]⊢⁺ (cfg_BR L (midR (a :: B))) := by
  cases B with
  | nil => contradiction
  | cons b₀ B' =>
    cases a with
    | zero =>
      have h := rule_BR_one L (b₀ :: incList B')
      dsimp [tailWeight, List.tail, midR] at h ⊢
      exact h
    | succ a' =>
      have h := rule_BR_ge2 a' L (b₀ :: incList B')
      dsimp [tailWeight, List.tail, midR] at h ⊢
      exact h

lemma br_sweep_midR (A B : List ℕ) (hB : B ≠ []) :
    (cfg_BR (incList A ++ [0]) (midR B)) [target_tm]⊢* (cfg_BR [0] (midR (A.reverse ++ B))) := by
  induction A generalizing B with
  | nil =>
    simp only [incList_nil, List.nil_append, List.reverse_nil]
    exact ⟨0, rfl⟩
  | cons a A' ih =>
    simp only [incList_cons, List.cons_append, List.reverse_cons, List.append_assoc]
    refine stepStar_trans (stepPlus_stepStar (rule_BR_midR a (incList A' ++ [0]) B hB)) ?_
    exact ih (a :: B) (List.cons_ne_nil a B)

lemma br_sweep (A : List ℕ) :
    (cfg_BR (incList A.reverse ++ [0]) [3]) [target_tm]⊢⁺ evalB (A ++ [3]) := by
  have h1 : (cfg_BR (incList A.reverse ++ [0]) (midR [3])) [target_tm]⊢*
      (cfg_BR [0] (midR (A.reverse.reverse ++ [3]))) :=
    br_sweep_midR A.reverse [3] (by decide)
  have h_mid3 : midR [3] = [3] := rfl
  rw [h_mid3, List.reverse_reverse] at h1
  refine stepStar_stepPlus_stepPlus h1 ?_
  cases hA : A ++ [3] with
  | nil =>
    have : (A ++ [3]).length = ([] : List ℕ).length := congrArg List.length hA
    simp at this
  | cons b₀ B' =>
    dsimp [midR]
    have h2 := rule_BR_zero [] (b₀ :: incList B')
    dsimp [tailWeight, headWeight, List.tail] at h2
    have h_add : b₀ + 0 + 3 = b₀ + 3 := by omega
    rw [h_add] at h2
    refine stepPlus_trans h2 ?_
    have h3 := rule_BR_nil ((b₀ + 3) :: incList B')
    dsimp [evalB, toR_B]
    exact h3

inductive SweepRel : List ℕ → List ℕ → Prop
  | single_end (P : List ℕ) (hP : P.length % 2 = 0) :
      SweepRel (fromQ (P ++ [1])) (fromQ (stepBlock P ++ [0, 0, 1]))
  | pair_end (P : List ℕ) (hP : P.length % 2 = 1) :
      SweepRel (fromQ (P ++ [1])) (fromQ (stepBlock P) ++ [5, 3])
  | append_odd (P : List ℕ) (k : ℕ) (Q Q' : List ℕ)
      (hP : P.length % 2 = 1) (hk : 1 ≤ k) (hQ : SweepRel Q Q') :
      SweepRel (fromQ P ++ (3 * k + 2) :: Q) (fromQ (stepBlock P) ++ (3 * (k + 1) + 2) :: Q')
  | two_end (P : List ℕ) (k : ℕ) (C : List ℕ) (hP : P.length % 2 = 0) :
      SweepRel (fromQ P ++ (3 * k + 2) :: fromQ (C ++ [1]))
        (fromQ (stepBlock P ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0 ++ [1]))

inductive SweepSteps : ℕ → List ℕ → List ℕ → Prop
  | zero (X : List ℕ) : SweepSteps 0 X X
  | succ {t : ℕ} {X Y Z : List ℕ} (h1 : SweepRel X Y) (h2 : SweepSteps t Y Z) :
      SweepSteps (t + 1) X Z

lemma SweepSteps_trans {s t : ℕ} {X Y Z : List ℕ}
    (h1 : SweepSteps s X Y) (h2 : SweepSteps t Y Z) : SweepSteps (s + t) X Z := by
  induction h1 with
  | zero _ =>
    rw [Nat.zero_add]
    exact h2
  | @succ s' X' Y' _ hrel _ ih =>
    rw [Nat.succ_add]
    exact SweepSteps.succ hrel (ih h2)

lemma SweepRel_nonempty {X Y : List ℕ} (h : SweepRel X Y) : X ≠ [] := by
  cases h <;> simp [fromQ]

lemma incList_rev_append_zeros (A : List ℕ) (m : ℕ) :
    List.replicate m 1 ++ (incList A.reverse ++ [0]) =
    incList (A ++ List.replicate m 0).reverse ++ [0] := by
  simp [incList, List.map_replicate, List.append_assoc]

lemma incList_rev_append_zeros_cons (A : List ℕ) (q z : ℕ) :
    (z + 1) :: (List.replicate q 1 ++ (incList A.reverse ++ [0])) =
    incList (A ++ List.replicate q 0 ++ [z]).reverse ++ [0] := by
  simp [incList, List.map_replicate, List.append_assoc]

lemma er_pair_step (q y : ℕ) (A rest : List ℕ) (hrest : rest ≠ []) :
    (cfg_ER (incList A.reverse ++ [0]) (toR_B (3 * q :: 3 * y :: rest))) [target_tm]⊢⁺
    (cfg_ER (incList (A ++ List.replicate q 0 ++ [3 * (y + 1)]).reverse ++ [0]) (toR_B rest)) := by
  cases rest with
  | nil => contradiction
  | cons r₀ rest' =>
    have h_toR : toR_B (3 * q :: 3 * y :: r₀ :: rest') =
        (0 + 3 * (q + 1)) :: (3 * y + 1) :: (r₀ + 1) :: incList rest' := by
      dsimp [toR_B, incList]; congr 1; omega
    rw [h_toR]
    have h1 := rule_ER_peel_all (incList A.reverse ++ [0])
      ((3 * y + 1) :: (r₀ + 1) :: incList rest') 0 (q + 1)
    rw [List.replicate_succ, List.cons_append] at h1
    refine stepStar_stepPlus_stepPlus h1 ?_
    have h2 := rule_E00_peel_all 1 0 (3 * y + 1)
      (List.replicate q 1 ++ (incList A.reverse ++ [0])) ((r₀ + 1) :: incList rest')
    unfold cfg_E00 at h2
    rw [Nat.zero_add] at h2
    refine stepStar_stepPlus_stepPlus h2 ?_
    have h3 := rule_ER_zero_zero_cons (r₀ + 1)
      ((1 + (3 * y + 1)) :: (List.replicate q 1 ++ (incList A.reverse ++ [0]))) (incList rest')
    dsimp [bumpHead] at h3
    have h_l : 1 + (3 * y + 1) + 1 + 1 = 3 * (y + 1) + 1 := by omega
    have h_r : r₀ + 1 + 2 = r₀ + 3 := by omega
    rw [h_l, h_r, incList_rev_append_zeros_cons A q (3 * (y + 1))] at h3
    exact h3

lemma er_even_prefix : ∀ (P : List ℕ), P.length % 2 = 0 → ∀ (A rest : List ℕ), rest ≠ [] →
    (cfg_ER (incList A.reverse ++ [0]) (toR_B (fromQ P ++ rest))) [target_tm]⊢*
    (cfg_ER (incList (A ++ fromQ (stepBlock P)).reverse ++ [0]) (toR_B rest))
  | [], _, A, rest, _ => by
    simp [fromQ, stepBlock]
    exact ⟨0, rfl⟩
  | [q], hP, _, _, _ => by
    simp at hP
  | q :: y :: P', hP, A, rest, hrest => by
    have hP' : P'.length % 2 = 0 := by simp only [List.length_cons] at hP; omega
    have h_rest' : fromQ P' ++ rest ≠ [] := by
      intro h; exact hrest (List.append_eq_nil_iff.mp h).2
    have h1 := er_pair_step q y A (fromQ P' ++ rest) h_rest'
    have h2 := er_even_prefix P' hP' (A ++ List.replicate q 0 ++ [3 * (y + 1)]) rest hrest
    refine stepStar_trans (stepPlus_stepStar h1) ?_
    have h_eq : A ++ List.replicate q 0 ++ [3 * (y + 1)] ++ fromQ (stepBlock P') =
        A ++ fromQ (stepBlock (q :: y :: P')) := by
      simp [stepBlock, fromQ, List.map_replicate, List.append_assoc]
    rw [h_eq] at h2
    exact h2

lemma er_single_end_base (A : List ℕ) :
    (cfg_ER (incList A.reverse ++ [0]) (toR_B (fromQ [1]))) [target_tm]⊢⁺
    evalB (A ++ fromQ [0, 0, 1]) := by
  have h_toR : toR_B (fromQ [1]) = [0 + 3 * 2] := rfl
  rw [h_toR]
  refine stepStar_stepPlus_stepPlus (rule_ER_peel_all (incList A.reverse ++ [0]) [] 0 2) ?_
  have h_er0 : cfg_ER (List.replicate 2 1 ++ (incList A.reverse ++ [0])) [0] =
      cfg_ER (incList (A ++ [0, 0]).reverse ++ [0]) [] := by
    rw [incList_rev_append_zeros A 2]
    simp [cfg_ER, encRight1]
  rw [h_er0]
  refine stepPlus_trans (rule_ER_nil (incList (A ++ [0, 0]).reverse ++ [0])) ?_
  have h_br := br_sweep (A ++ [0, 0])
  have h_eq : A ++ [0, 0] ++ [3] = A ++ fromQ [0, 0, 1] := by simp [fromQ, List.append_assoc]
  rwa [h_eq] at h_br

lemma er_pair_end_base (q : ℕ) (A : List ℕ) :
    (cfg_ER (incList A.reverse ++ [0]) (toR_B (fromQ [q, 1]))) [target_tm]⊢⁺
    evalB (A ++ fromQ (stepBlock [q]) ++ [5, 3]) := by
  have h_toR : toR_B (fromQ [q, 1]) = (0 + 3 * (q + 1)) :: [4] := by
    dsimp [fromQ, toR_B, incList]; congr 1; omega
  rw [h_toR]
  have h1 := rule_ER_peel_all (incList A.reverse ++ [0]) [4] 0 (q + 1)
  rw [List.replicate_succ, List.cons_append] at h1
  refine stepStar_stepPlus_stepPlus h1 ?_
  have h2 := rule_E00_peel_all 1 0 4 (List.replicate q 1 ++ (incList A.reverse ++ [0])) []
  unfold cfg_E00 at h2
  rw [Nat.zero_add] at h2
  refine stepStar_stepPlus_stepPlus h2 ?_
  have h3 := rule_ER_zero_zero_nil ((1 + 4) :: (List.replicate q 1 ++ (incList A.reverse ++ [0])))
  dsimp [bumpHead] at h3
  rw [incList_rev_append_zeros_cons A q 5] at h3
  refine stepPlus_trans h3 ?_
  have h_br := br_sweep (A ++ List.replicate q 0 ++ [5])
  have h_eq : A ++ List.replicate q 0 ++ [5] ++ [3] =
      A ++ fromQ (stepBlock [q]) ++ [5, 3] := by
    simp [stepBlock, fromQ, List.map_replicate, List.append_assoc]
  rwa [h_eq] at h_br

lemma er_odd_cons_base (q k : ℕ) (A Q : List ℕ) (hQ : Q ≠ []) :
    (cfg_ER (incList A.reverse ++ [0]) (toR_B (3 * q :: (3 * k + 2) :: Q))) [target_tm]⊢⁺
    (cfg_ER (incList (A ++ fromQ (stepBlock [q]) ++ [3 * (k + 1) + 2]).reverse ++ [0]) (toR_B Q)) := by
  cases Q with
  | nil => contradiction
  | cons r₀ Q' =>
    have h_toR : toR_B (3 * q :: (3 * k + 2) :: r₀ :: Q') =
        (0 + 3 * (q + 1)) :: (3 * k + 3) :: (r₀ + 1) :: incList Q' := by
      dsimp [toR_B, incList]; congr 1; omega
    rw [h_toR]
    have h1 := rule_ER_peel_all (incList A.reverse ++ [0])
      ((3 * k + 3) :: (r₀ + 1) :: incList Q') 0 (q + 1)
    rw [List.replicate_succ, List.cons_append] at h1
    refine stepStar_stepPlus_stepPlus h1 ?_
    have h2 := rule_E00_peel_all 1 0 (3 * k + 3)
      (List.replicate q 1 ++ (incList A.reverse ++ [0])) ((r₀ + 1) :: incList Q')
    unfold cfg_E00 at h2
    rw [Nat.zero_add] at h2
    refine stepStar_stepPlus_stepPlus h2 ?_
    have h3 := rule_ER_zero_zero_cons (r₀ + 1)
      ((1 + (3 * k + 3)) :: (List.replicate q 1 ++ (incList A.reverse ++ [0]))) (incList Q')
    dsimp [bumpHead] at h3
    have h_l : 1 + (3 * k + 3) + 1 + 1 = (3 * (k + 1) + 2) + 1 := by omega
    have h_r : r₀ + 1 + 2 = r₀ + 3 := by omega
    rw [h_l, h_r, incList_rev_append_zeros_cons A q (3 * (k + 1) + 2)] at h3
    have h_eq : A ++ List.replicate q 0 ++ [3 * (k + 1) + 2] =
        A ++ fromQ (stepBlock [q]) ++ [3 * (k + 1) + 2] := by
      simp [stepBlock, fromQ, List.map_replicate, List.append_assoc]
    rwa [h_eq] at h3

lemma er_peel_two_chain (C : List ℕ) (L : List ℕ) :
    (cfg_ER L (bumpHead (incList (fromQ (C ++ [1]))))) [target_tm]⊢*
    (cfg_ER (List.replicate (sumQ1 (C ++ [1])) 1 ++ L) [0]) := by
  induction C generalizing L with
  | nil =>
    dsimp [fromQ, incList, bumpHead, sumQ1]
    have h1 := rule_ER_peel_all L [] 2 1
    refine stepStar_trans h1 ?_
    have h2 := rule_ER_two (1 :: L) []
    dsimp [bumpHead] at h2
    exact stepPlus_stepStar h2
  | cons q C' ih =>
    have h_head : bumpHead (incList (fromQ ((q :: C') ++ [1]))) =
        (2 + 3 * q) :: incList (fromQ (C' ++ [1])) := by
      simp [fromQ, incList, bumpHead]; omega
    rw [h_head]
    refine stepStar_trans (rule_ER_peel_all L (incList (fromQ (C' ++ [1]))) 2 q) ?_
    refine stepStar_trans (stepPlus_stepStar (rule_ER_two (List.replicate q 1 ++ L)
      (incList (fromQ (C' ++ [1]))))) ?_
    refine stepStar_trans (ih (1 :: (List.replicate q 1 ++ L))) ?_
    have h_rep : List.replicate (sumQ1 (C' ++ [1])) 1 ++ (1 :: (List.replicate q 1 ++ L)) =
        List.replicate (sumQ1 ((q :: C') ++ [1])) 1 ++ L := by
      simp only [sumQ1, List.cons_append]
      rw [show (q + 1) + sumQ1 (C' ++ [1]) = sumQ1 (C' ++ [1]) + 1 + q by omega]
      rw [List.replicate_add, List.replicate_add, List.replicate_one]
      simp [List.append_assoc]
    rw [h_rep]
    exact ⟨0, rfl⟩

lemma er_two_end_base (k : ℕ) (C A : List ℕ) :
    (cfg_ER (incList A.reverse ++ [0]) (toR_B ((3 * k + 2) :: fromQ (C ++ [1])))) [target_tm]⊢⁺
    evalB (A ++ fromQ (List.replicate (k + 2 + sumQ1 (C ++ [1])) 0 ++ [1])) := by
  have h_toR : toR_B ((3 * k + 2) :: fromQ (C ++ [1])) =
      (2 + 3 * (k + 1)) :: incList (fromQ (C ++ [1])) := by
    dsimp [toR_B]; congr 1; omega
  rw [h_toR]
  refine stepStar_stepPlus_stepPlus
    (rule_ER_peel_all (incList A.reverse ++ [0]) (incList (fromQ (C ++ [1]))) 2 (k + 1)) ?_
  refine stepPlus_stepStar_stepPlus
    (rule_ER_two (List.replicate (k + 1) 1 ++ (incList A.reverse ++ [0]))
      (incList (fromQ (C ++ [1])))) ?_
  refine stepStar_trans
    (er_peel_two_chain C (1 :: (List.replicate (k + 1) 1 ++ (incList A.reverse ++ [0])))) ?_
  have h_er0 : cfg_ER (List.replicate (sumQ1 (C ++ [1])) 1 ++
      (1 :: (List.replicate (k + 1) 1 ++ (incList A.reverse ++ [0])))) [0] =
      cfg_ER (incList (A ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0).reverse ++ [0]) [] := by
    have h_l : List.replicate (sumQ1 (C ++ [1])) 1 ++
        (1 :: (List.replicate (k + 1) 1 ++ (incList A.reverse ++ [0]))) =
        incList (A ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0).reverse ++ [0] := by
      change List.replicate (sumQ1 (C ++ [1])) 1 ++
        (List.replicate (k + 2) 1 ++ (incList A.reverse ++ [0])) = _
      rw [← List.append_assoc, ← List.replicate_add,
        show sumQ1 (C ++ [1]) + (k + 2) = k + 2 + sumQ1 (C ++ [1]) by omega,
        incList_rev_append_zeros]
    rw [h_l]
    simp [cfg_ER, encRight1]
  rw [h_er0]
  refine stepPlus_stepStar (stepPlus_trans
    (rule_ER_nil (incList (A ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0).reverse ++ [0])) ?_)
  have h_br := br_sweep (A ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0)
  have h_eq : A ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0 ++ [3] =
      A ++ fromQ (List.replicate (k + 2 + sumQ1 (C ++ [1])) 0 ++ [1]) := by
    simp [fromQ, List.map_replicate, List.append_assoc]
  rwa [h_eq] at h_br

-- ============================================================================
-- Section 3: Graded Homomorphism Laws for `stepBlock` & `SweepRel_sound`
-- ============================================================================

@[simp] lemma stepBlock_nil : stepBlock [] = [] := rfl
@[simp] lemma sb₁_nil : sb₁ [] = [] := rfl
lemma sb₁_cons (x : ℕ) (rest : List ℕ) : sb₁ (x :: rest) = (x + 1) :: stepBlock rest := rfl

lemma stepBlock_iterate_nil (s : ℕ) : stepBlock^[s] [] = [] := by
  induction s <;> simp [*]

lemma length_append_even {u v : List ℕ} (hu : u.length % 2 = 0) (hv : v.length % 2 = 0) :
    (u ++ v).length % 2 = 0 := by
  rw [List.length_append]; omega

lemma length_append_odd_odd {u v : List ℕ} (hu : u.length % 2 = 1) (hv : v.length % 2 = 1) :
    (u ++ v).length % 2 = 0 := by
  rw [List.length_append]; omega

lemma length_append_odd_even {u v : List ℕ} (hu : u.length % 2 = 1) (hv : v.length % 2 = 0) :
    (u ++ v).length % 2 = 1 := by
  rw [List.length_append]; omega

lemma pow_two_succ (n : ℕ) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  rw [Nat.pow_succ]; omega

lemma stepBlock_append_even : ∀ (P Q : List ℕ), P.length % 2 = 0 →
    stepBlock (P ++ Q) = stepBlock P ++ stepBlock Q
  | [], Q, _ => rfl
  | [q], _, hP => by simp at hP
  | q :: y :: P', Q, hP => by
    have hP' : P'.length % 2 = 0 := by simp only [List.length_cons] at hP; omega
    simp only [List.cons_append, stepBlock, stepBlock_append_even P' Q hP', List.append_assoc]

lemma stepBlock_append_odd : ∀ (P Q : List ℕ), P.length % 2 = 1 →
    stepBlock (P ++ Q) = stepBlock P ++ sb₁ Q
  | [], _, hP => by simp at hP
  | [q], Q, _ => by
    cases Q with
    | nil => simp [stepBlock, sb₁]
    | cons y Q' => simp [stepBlock, sb₁]
  | q :: y :: P', Q, hP => by
    have hP' : P'.length % 2 = 1 := by simp only [List.length_cons] at hP; omega
    simp only [List.cons_append, stepBlock, stepBlock_append_odd P' Q hP', List.append_assoc]

lemma sb₁_append_even (P Q : List ℕ) (hP : P.length % 2 = 0) :
    sb₁ (P ++ Q) = sb₁ P ++ sb₁ Q := by
  cases P with
  | nil => rfl
  | cons x P' =>
    have hP' : P'.length % 2 = 1 := by simp only [List.length_cons] at hP; omega
    simp only [List.cons_append, sb₁_cons, stepBlock_append_odd P' Q hP']

lemma sb₁_append_odd (P Q : List ℕ) (hP : P.length % 2 = 1) :
    sb₁ (P ++ Q) = sb₁ P ++ stepBlock Q := by
  cases P with
  | nil => simp at hP
  | cons x P' =>
    have hP' : P'.length % 2 = 0 := by simp only [List.length_cons] at hP; omega
    simp only [List.cons_append, sb₁_cons, stepBlock_append_even P' Q hP']

lemma odd_split_even_last : ∀ (P : List ℕ), P.length % 2 = 1 →
    ∃ P₀ q, P = P₀ ++ [q] ∧ P₀.length % 2 = 0 ∧ stepBlock P = stepBlock P₀ ++ stepBlock [q]
  | [], hP => by simp at hP
  | [q], _ => ⟨[], q, rfl, rfl, rfl⟩
  | x :: y :: P', hP => by
    have hP' : P'.length % 2 = 1 := by simp only [List.length_cons] at hP; omega
    obtain ⟨P₀, q, rfl, hP₀, hsb⟩ := odd_split_even_last P' hP'
    refine ⟨x :: y :: P₀, q, by simp, by simp only [List.length_cons] at hP₀ ⊢; omega, ?_⟩
    simp only [List.cons_append, stepBlock, hsb, List.append_assoc]

theorem SweepRel_sound_acc {X Y : List ℕ} (h : SweepRel X Y) (A : List ℕ) :
    (cfg_ER (incList A.reverse ++ [0]) (toR_B X)) [target_tm]⊢⁺ evalB (A ++ Y) := by
  induction h generalizing A with
  | single_end P hP =>
    rw [fromQ_append]
    have h_pre := er_even_prefix P hP A (fromQ [1]) (by decide)
    refine stepStar_stepPlus_stepPlus h_pre ?_
    have h_base := er_single_end_base (A ++ fromQ (stepBlock P))
    have h_eq : A ++ fromQ (stepBlock P) ++ fromQ [0, 0, 1] =
        A ++ fromQ (stepBlock P ++ [0, 0, 1]) := by
      simp [fromQ_append, List.append_assoc]
    rwa [h_eq] at h_base
  | pair_end P hP =>
    obtain ⟨P₀, q, rfl, hP₀, hsb⟩ := odd_split_even_last P hP
    rw [List.append_assoc, fromQ_append]
    have h_pre := er_even_prefix P₀ hP₀ A (fromQ [q, 1]) (by simp [fromQ])
    refine stepStar_stepPlus_stepPlus h_pre ?_
    have h_base := er_pair_end_base q (A ++ fromQ (stepBlock P₀))
    have h_eq : A ++ fromQ (stepBlock P₀) ++ fromQ (stepBlock [q]) ++ [5, 3] =
        A ++ (fromQ (stepBlock (P₀ ++ [q])) ++ [5, 3]) := by
      rw [hsb, fromQ_append]
      simp [List.append_assoc]
    rwa [h_eq] at h_base
  | append_odd P k Q Q' hP _ hQ ih =>
    obtain ⟨P₀, q, rfl, hP₀, hsb⟩ := odd_split_even_last P hP
    have h_split : fromQ (P₀ ++ [q]) ++ (3 * k + 2) :: Q =
        fromQ P₀ ++ (3 * q :: (3 * k + 2) :: Q) := by
      simp [fromQ_append]
    rw [h_split]
    have h_pre := er_even_prefix P₀ hP₀ A (3 * q :: (3 * k + 2) :: Q) (by simp)
    refine stepStar_stepPlus_stepPlus h_pre ?_
    have h_mid := er_odd_cons_base q k (A ++ fromQ (stepBlock P₀)) Q (SweepRel_nonempty hQ)
    refine stepPlus_trans h_mid ?_
    have h_rec := ih (A ++ fromQ (stepBlock P₀) ++ fromQ (stepBlock [q]) ++ [3 * (k + 1) + 2])
    have h_eq : A ++ fromQ (stepBlock P₀) ++ fromQ (stepBlock [q]) ++ [3 * (k + 1) + 2] ++ Q' =
        A ++ (fromQ (stepBlock (P₀ ++ [q])) ++ (3 * (k + 1) + 2) :: Q') := by
      rw [hsb, fromQ_append]
      simp [List.append_assoc]
    rwa [h_eq] at h_rec
  | two_end P k C hP =>
    have h_pre := er_even_prefix P hP A ((3 * k + 2) :: fromQ (C ++ [1])) (by simp)
    refine stepStar_stepPlus_stepPlus h_pre ?_
    have h_base := er_two_end_base k C (A ++ fromQ (stepBlock P))
    have h_eq : A ++ fromQ (stepBlock P) ++
        fromQ (List.replicate (k + 2 + sumQ1 (C ++ [1])) 0 ++ [1]) =
        A ++ fromQ (stepBlock P ++ List.replicate (k + 2 + sumQ1 (C ++ [1])) 0 ++ [1]) := by
      simp [fromQ_append, List.append_assoc]
    rwa [h_eq] at h_base

theorem SweepRel_sound {X Y : List ℕ} (h : SweepRel X Y) :
    (evalB X) [target_tm]⊢⁺ (evalB Y) := by
  have h0 := SweepRel_sound_acc h []
  simpa [evalB, incList] using h0

theorem SweepSteps_sound_plus {t : ℕ} {X Y : List ℕ} (h : SweepSteps (t + 1) X Y) :
    (evalB X) [target_tm]⊢⁺ (evalB Y) := by
  induction t generalizing X with
  | zero =>
    cases h with
    | succ h1 h2 =>
      cases h2
      exact SweepRel_sound h1
  | succ t' ih =>
    cases h with
    | succ h1 h2 =>
      exact stepPlus_trans (SweepRel_sound h1) (ih h2)

-- ============================================================================
-- Section 4: Additive Weight Conservation & Even-Prefix Prepend
-- ============================================================================

@[simp] lemma sumQ1_nil : sumQ1 [] = 0 := rfl
@[simp] lemma sumQ1_cons (q : ℕ) (rest : List ℕ) : sumQ1 (q :: rest) = (q + 1) + sumQ1 rest := rfl
@[simp] lemma weightB_nil : weightB [] = 0 := rfl
@[simp] lemma weightB_cons (b : ℕ) (rest : List ℕ) : weightB (b :: rest) = weightDigit b + weightB rest := rfl

lemma weightDigit_mul_three (q : ℕ) : weightDigit (3 * q) = 3 * (q + 1) := by
  unfold weightDigit
  have h : (3 * q) % 3 = 0 := Nat.mul_mod_right 3 q
  simp [h]; omega

lemma weightDigit_two_mod_three (k : ℕ) : weightDigit (3 * k + 2) = 3 * k + 6 := by
  unfold weightDigit
  have h : (3 * k + 2) % 3 = 2 := by omega
  simp [h]

lemma sumQ1_append (u v : List ℕ) : sumQ1 (u ++ v) = sumQ1 u + sumQ1 v := by
  induction u with
  | nil => simp
  | cons q u' ih => simp only [List.cons_append, sumQ1_cons, ih]; omega

lemma sumQ1_replicate_zero (n : ℕ) : sumQ1 (List.replicate n 0) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, sumQ1_cons, ih]; omega

lemma weightB_append (X Y : List ℕ) : weightB (X ++ Y) = weightB X + weightB Y := by
  induction X with
  | nil => simp
  | cons b X' ih => simp only [List.cons_append, weightB_cons, ih]; omega

lemma weightB_fromQ (u : List ℕ) : weightB (fromQ u) = 3 * sumQ1 u := by
  induction u with
  | nil => rfl
  | cons q u' ih => simp only [fromQ_cons, weightB_cons, weightDigit_mul_three, sumQ1_cons, ih]; omega

lemma sumQ1_stepBlock_even : ∀ (P : List ℕ), P.length % 2 = 0 →
    sumQ1 (stepBlock P) = sumQ1 P
  | [], _ => rfl
  | [q], hP => by simp at hP
  | q :: y :: P', hP => by
    have hP' : P'.length % 2 = 0 := by simp only [List.length_cons] at hP; omega
    simp only [stepBlock, sumQ1_append, sumQ1_replicate_zero, sumQ1_cons,
      sumQ1_stepBlock_even P' hP']
    omega

lemma sumQ1_stepBlock_odd : ∀ (P : List ℕ), P.length % 2 = 1 →
    sumQ1 P = sumQ1 (stepBlock P) + 1
  | [], hP => by simp at hP
  | [q], _ => by simp [stepBlock, sumQ1_replicate_zero]
  | q :: y :: P', hP => by
    have hP' : P'.length % 2 = 1 := by simp only [List.length_cons] at hP; omega
    have ih := sumQ1_stepBlock_odd P' hP'
    simp only [stepBlock, sumQ1_append, sumQ1_replicate_zero, sumQ1_cons]
    omega

lemma SweepRel_weightB {X Y : List ℕ} (h : SweepRel X Y) : weightB Y = weightB X + 6 := by
  induction h with
  | single_end P hP =>
    have h_ev := sumQ1_stepBlock_even P hP
    simp only [weightB_fromQ, sumQ1_append, h_ev, sumQ1_cons, sumQ1_nil]
    omega
  | pair_end P hP =>
    have h_od := sumQ1_stepBlock_odd P hP
    simp only [weightB_append, weightB_fromQ, sumQ1_append, h_od,
      sumQ1_cons, sumQ1_nil, weightB_cons, weightB_nil]
    dsimp [weightDigit]
    omega
  | append_odd P k Q Q' hP _ _ ih =>
    have h_od := sumQ1_stepBlock_odd P hP
    simp only [weightB_append, weightB_fromQ, h_od, weightB_cons, weightDigit_two_mod_three]
    omega
  | two_end P k C hP =>
    have h_ev := sumQ1_stepBlock_even P hP
    rw [weightB_fromQ, sumQ1_append, sumQ1_append, sumQ1_replicate_zero, h_ev,
      weightB_append, weightB_fromQ, weightB_cons, weightDigit_two_mod_three, weightB_fromQ]
    simp only [sumQ1_cons, sumQ1_nil]
    omega

lemma SweepSteps_weightB {t : ℕ} {X Y : List ℕ} (h : SweepSteps t X Y) :
    weightB Y = weightB X + 6 * t := by
  induction h with
  | zero _ => simp
  | succ h1 _ ih =>
    have hw := SweepRel_weightB h1
    omega

lemma SweepSteps_sumQ1 {t : ℕ} {C : List ℕ}
    (h : SweepSteps t (fromQ [1]) (fromQ (C ++ [1]))) :
    sumQ1 (C ++ [1]) = 2 * t + 2 := by
  have hw := SweepSteps_weightB h
  rw [weightB_fromQ, weightB_fromQ] at hw
  dsimp [sumQ1] at hw
  omega

lemma SweepRel_prepend_even (P : List ℕ) (hP : P.length % 2 = 0) {Q Q' : List ℕ}
    (hQ : SweepRel Q Q') :
    SweepRel (fromQ P ++ Q) (fromQ (stepBlock P) ++ Q') := by
  cases hQ with
  | single_end P₂ hP₂ =>
    rw [← fromQ_append, ← List.append_assoc]
    have h_step := SweepRel.single_end (P ++ P₂) (length_append_even hP hP₂)
    rw [stepBlock_append_even P P₂ hP] at h_step
    simpa [fromQ_append, List.append_assoc] using h_step
  | pair_end P₂ hP₂ =>
    rw [← fromQ_append, ← List.append_assoc]
    have h_step := SweepRel.pair_end (P ++ P₂) (by rw [List.length_append]; omega)
    rw [stepBlock_append_even P P₂ hP] at h_step
    simpa [fromQ_append, List.append_assoc] using h_step
  | append_odd P₂ k R R' hP₂ hk hR =>
    rw [← List.append_assoc, ← fromQ_append]
    have h_step := SweepRel.append_odd (P ++ P₂) k R R' (by rw [List.length_append]; omega) hk hR
    rw [stepBlock_append_even P P₂ hP] at h_step
    simpa [fromQ_append, List.append_assoc] using h_step
  | two_end P₂ k C hP₂ =>
    rw [← List.append_assoc, ← fromQ_append]
    have h_step := SweepRel.two_end (P ++ P₂) k C (length_append_even hP hP₂)
    rw [stepBlock_append_even P P₂ hP] at h_step
    simpa [fromQ_append, List.append_assoc] using h_step

lemma SweepSteps_prepend_even {t : ℕ} (P : List ℕ) {Q Q' : List ℕ}
    (hQ : SweepSteps t Q Q')
    (hEven : ∀ s < t, (stepBlock^[s] P).length % 2 = 0) :
    SweepSteps t (fromQ P ++ Q) (fromQ (stepBlock^[t] P) ++ Q') := by
  induction hQ generalizing P with
  | zero _ =>
    simp only [Function.iterate_zero, id_eq]
    exact SweepSteps.zero _
  | @succ t' X Y Z h1 _ ih =>
    have hP0 : P.length % 2 = 0 := hEven 0 (Nat.zero_lt_succ t')
    refine SweepSteps.succ (SweepRel_prepend_even P hP0 h1) ?_
    have h_rec := ih (stepBlock P) (fun s hs => by
      have h_lt : s + 1 < t' + 1 := Nat.succ_lt_succ hs
      have h_it := hEven (s + 1) h_lt
      rwa [Function.iterate_succ_apply] at h_it)
    rwa [← Function.iterate_succ_apply stepBlock t' P] at h_rec

-- ============================================================================
-- Section 5: Iterated `stepBlock` Lemmas, `zBlock`, and `psi` / `phi` Lifts
-- ============================================================================

lemma stepBlock_iterate_append_even (t : ℕ) (P Q : List ℕ)
    (hEven : ∀ s < t, (stepBlock^[s] P).length % 2 = 0) :
    stepBlock^[t] (P ++ Q) = stepBlock^[t] P ++ stepBlock^[t] Q := by
  induction t generalizing P Q with
  | zero => rfl
  | succ t' ih =>
    have h0 : P.length % 2 = 0 := hEven 0 (Nat.zero_lt_succ t')
    rw [Function.iterate_succ_apply, stepBlock_append_even P Q h0]
    have h_rec := ih (stepBlock P) (stepBlock Q) (fun s hs => by
      have h_it := hEven (s + 1) (Nat.succ_lt_succ hs)
      rwa [Function.iterate_succ_apply] at h_it)
    rwa [← Function.iterate_succ_apply stepBlock t' P,
      ← Function.iterate_succ_apply stepBlock t' Q] at h_rec

lemma stepBlock_iterate_append_singleton (j : ℕ) (u : List ℕ) (d : ℕ)
    (hEven : ∀ s < j, (stepBlock^[s] (u ++ [d])).length % 2 = 0) :
    stepBlock^[j] (u ++ [d]) = stepBlock^[j] u ++ [d + j] := by
  induction j generalizing u d with
  | zero => simp
  | succ j' ih =>
    have h0 : (u ++ [d]).length % 2 = 0 := hEven 0 (Nat.zero_lt_succ j')
    have hu : u.length % 2 = 1 := by rw [List.length_append] at h0; dsimp at h0; omega
    have h1 : stepBlock (u ++ [d]) = stepBlock u ++ [d + 1] := by
      rw [stepBlock_append_odd u [d] hu]
      rfl
    rw [Function.iterate_succ_apply, h1]
    have h_rec := ih (stepBlock u) (d + 1) (fun s hs => by
      have h_it := hEven (s + 1) (Nat.succ_lt_succ hs)
      rwa [Function.iterate_succ_apply, h1] at h_it)
    rw [h_rec, ← Function.iterate_succ_apply stepBlock j' u]
    have h_add : d + 1 + j' = d + (j' + 1) := by omega
    rw [h_add]

def zBlock (k d : ℕ) : List ℕ :=
  List.replicate (2 ^ k - 1) 0 ++ [d]

lemma zBlock_zero (d : ℕ) : zBlock 0 d = [d] := rfl

lemma zBlock_succ (k d : ℕ) : zBlock (k + 1) d = zBlock k 0 ++ zBlock k d := by
  unfold zBlock
  have h_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have h_pow : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 + (2 ^ k - 1) := by
    rw [pow_two_succ k]; omega
  rw [h_pow, List.replicate_add, List.replicate_add, List.replicate_one]
  simp [List.append_assoc]

lemma zBlock_props (k : ℕ) :
    (∀ d, ∀ s < 2 ^ k - 1, (stepBlock^[s] (zBlock k d)).length % 2 = 0) ∧
    (∀ d, stepBlock^[2 ^ k - 1] (zBlock k d) = [d + (2 ^ k - 1)]) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro d s hs; change s < 0 at hs; omega
    · intro d; rfl
  | succ k ih =>
    obtain ⟨ih_even, ih_end⟩ := ih
    have h_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have h_mid : ∀ d, stepBlock^[2 ^ k - 1] (zBlock (k + 1) d) =
        [2 ^ k - 1, d + (2 ^ k - 1)] := by
      intro d
      rw [zBlock_succ]
      rw [stepBlock_iterate_append_even (2 ^ k - 1) (zBlock k 0) (zBlock k d) (ih_even 0)]
      rw [ih_end 0, ih_end d, Nat.zero_add]
      rfl
    have h_mid_next : ∀ d, stepBlock^[2 ^ k] (zBlock (k + 1) d) = zBlock k (d + 2 ^ k) := by
      intro d
      have h_split : 2 ^ k = (2 ^ k - 1) + 1 := by omega
      have h_step : stepBlock^[2 ^ k] (zBlock (k + 1) d) =
          stepBlock (stepBlock^[2 ^ k - 1] (zBlock (k + 1) d)) := by
        rw [h_split]
        exact Function.iterate_succ_apply' stepBlock (2 ^ k - 1) (zBlock (k + 1) d)
      rw [h_step, h_mid d]
      dsimp [stepBlock, zBlock]
      have h_add : d + (2 ^ k - 1) + 1 = d + 2 ^ k := by omega
      rw [h_add]
    refine ⟨?_, ?_⟩
    · intro d s hs
      rcases (by omega : s < 2 ^ k - 1 ∨ s = 2 ^ k - 1 ∨ 2 ^ k ≤ s) with hlt | rfl | hge
      · rw [zBlock_succ]
        rw [stepBlock_iterate_append_even s (zBlock k 0) (zBlock k d)
          (fun s' hs' => ih_even 0 s' (Nat.lt_trans hs' hlt))]
        exact length_append_even (ih_even 0 s hlt) (ih_even d s hlt)
      · rw [h_mid d]; simp
      · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 ^ k := ⟨s - 2 ^ k, by omega⟩
        have hs' : s' < 2 ^ k - 1 := by
          rw [pow_two_succ k] at hs; omega
        rw [Function.iterate_add_apply, h_mid_next d]
        exact ih_even (d + 2 ^ k) s' hs'
    · intro d
      have h_split : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
        rw [pow_two_succ k]; omega
      have h_step : stepBlock^[2 ^ (k + 1) - 1] (zBlock (k + 1) d) =
          stepBlock^[2 ^ k - 1] (stepBlock^[2 ^ k] (zBlock (k + 1) d)) := by
        rw [← Function.iterate_add_apply, h_split]
      rw [h_step, h_mid_next d, ih_end (d + 2 ^ k)]
      have h_add : d + 2 ^ k + (2 ^ k - 1) = d + (2 ^ (k + 1) - 1) := by
        rw [pow_two_succ k]; omega
      rw [h_add]

lemma zBlock_double_props (k d : ℕ) :
    (∀ s ≤ 2 ^ (k + 1) - 1, (stepBlock^[s] (zBlock (k + 2) d)).length % 2 = 0) ∧
    stepBlock^[2 ^ (k + 1) - 1] (zBlock (k + 2) d) =
      [2 ^ (k + 1) - 1, d + (2 ^ (k + 1) - 1)] := by
  have h_pos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
  have h_lt : ∀ s ≤ 2 ^ (k + 1) - 1, s < 2 ^ (k + 2) - 1 := by
    intro s hs; rw [pow_two_succ (k + 1)]; omega
  refine ⟨fun s hs => (zBlock_props (k + 2)).1 d s (h_lt s hs), ?_⟩
  rw [zBlock_succ (k + 1) d]
  rw [stepBlock_iterate_append_even (2 ^ (k + 1) - 1) (zBlock (k + 1) 0) (zBlock (k + 1) d)
    ((zBlock_props (k + 1)).1 0)]
  rw [(zBlock_props (k + 1)).2 0, (zBlock_props (k + 1)).2 d, Nat.zero_add]
  rfl

lemma zBlock_shift_sb1 (k d : ℕ) (rest : List ℕ) :
    List.replicate (2 ^ (k + 1) - 1) 0 ++
      sb₁ ((2 ^ (k + 1) - 1) :: (d + (2 ^ (k + 1) - 1)) :: rest) =
    zBlock (k + 1) (2 ^ (k + 1)) ++
      (List.replicate (d + (2 ^ (k + 1) - 1)) 0 ++ sb₁ rest) := by
  change List.replicate (2 ^ (k + 1) - 1) 0 ++
    sb₁ ([2 ^ (k + 1) - 1, d + (2 ^ (k + 1) - 1)] ++ rest) = _
  rw [sb₁_append_even [2 ^ (k + 1) - 1, d + (2 ^ (k + 1) - 1)] rest (by simp)]
  have h_pos : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow (k + 1) 2 (by decide))
  have h_sb1 : sb₁ [2 ^ (k + 1) - 1, d + (2 ^ (k + 1) - 1)] =
      [2 ^ (k + 1)] ++ List.replicate (d + (2 ^ (k + 1) - 1)) 0 := by
    simp [sb₁, stepBlock, h_pos]
  rw [h_sb1]
  simp [zBlock, List.append_assoc]

lemma zBlock_shift_sb1_zero (k : ℕ) (rest : List ℕ) :
    List.replicate (2 ^ (k + 1) - 1) 0 ++
      sb₁ ((2 ^ (k + 1) - 1) :: (2 ^ (k + 1) - 1) :: rest) =
    zBlock (k + 1) (2 ^ (k + 1)) ++
      (List.replicate (2 ^ (k + 1) - 1) 0 ++ sb₁ rest) := by
  simpa using zBlock_shift_sb1 k 0 rest

def psi : List ℕ → List ℕ
  | [] => []
  | x :: u => 0 :: (2 * x) :: psi u

def phi (u : List ℕ) : List ℕ :=
  psi u ++ [0]

def oddMap : List ℕ → List ℕ
  | [] => []
  | x :: u => (2 * x + 1) :: oddMap u

lemma psi_append (u v : List ℕ) : psi (u ++ v) = psi u ++ psi v := by
  induction u with
  | nil => rfl
  | cons x u' ih => simp [psi, ih]

lemma phi_append (u v : List ℕ) : phi (u ++ v) = psi u ++ phi v := by
  simp [phi, psi_append, List.append_assoc]

lemma psi_replicate_zero (n : ℕ) : psi (List.replicate n 0) = List.replicate (2 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, psi, Nat.mul_zero, ih]
    have h_eq : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [h_eq, List.replicate_add]
    rfl

lemma phi_replicate_zero (n : ℕ) : phi (List.replicate n 0) = List.replicate (2 * n + 1) 0 := by
  unfold phi
  rw [psi_replicate_zero, ← List.replicate_succ']

lemma psi_length_even (u : List ℕ) : (psi u).length % 2 = 0 := by
  induction u with
  | nil => rfl
  | cons x u' ih => simp [psi]; omega

lemma phi_length_odd (u : List ℕ) : (phi u).length % 2 = 1 := by
  unfold phi
  have h := psi_length_even u
  simp [List.length_append]; omega

lemma oddMap_length (u : List ℕ) : (oddMap u).length = u.length := by
  induction u with
  | nil => rfl
  | cons x u' ih => simp [oddMap, ih]

lemma stepBlock_psi (u : List ℕ) : stepBlock (psi u) = oddMap u := by
  induction u with
  | nil => rfl
  | cons x u' ih => simp [psi, stepBlock, oddMap, ih]

lemma stepBlock_phi (u : List ℕ) : stepBlock (phi u) = oddMap u := by
  unfold phi
  rw [stepBlock_append_even (psi u) [0] (psi_length_even u), stepBlock_psi]
  simp [stepBlock]

lemma stepBlock_oddMap_even : ∀ (u : List ℕ), u.length % 2 = 0 →
    stepBlock (oddMap u) = psi (stepBlock u)
  | [], _ => rfl
  | [q], hu => by simp at hu
  | q :: y :: u', hu => by
    have hu' : u'.length % 2 = 0 := by simp only [List.length_cons] at hu; omega
    simp only [oddMap, stepBlock, psi_append, psi_replicate_zero,
      stepBlock_oddMap_even u' hu']
    rw [List.replicate_succ', List.append_assoc]
    dsimp [psi]
    have h_y : 2 * y + 1 + 1 = 2 * (y + 1) := by omega
    rw [h_y]

lemma stepBlock_oddMap_odd : ∀ (u : List ℕ), u.length % 2 = 1 →
    stepBlock (oddMap u) = phi (stepBlock u)
  | [], hu => by simp at hu
  | [q], _ => by
    dsimp [oddMap, stepBlock]
    rw [← phi_replicate_zero q]
  | q :: y :: u', hu => by
    have hu' : u'.length % 2 = 1 := by simp only [List.length_cons] at hu; omega
    simp only [oddMap, stepBlock, phi_append, psi_replicate_zero,
      stepBlock_oddMap_odd u' hu']
    rw [List.replicate_succ', List.append_assoc]
    dsimp [psi]
    have h_y : 2 * y + 1 + 1 = 2 * (y + 1) := by omega
    rw [h_y]
    simp [phi, psi]

lemma stepBlock_iterate_psi (j : ℕ) (u : List ℕ)
    (hEven : ∀ s < j, (stepBlock^[s] u).length % 2 = 0) :
    (∀ s < 2 * j, (stepBlock^[s] (psi u)).length % 2 = 0) ∧
    stepBlock^[2 * j] (psi u) = psi (stepBlock^[j] u) := by
  induction j generalizing u with
  | zero =>
    refine ⟨fun s hs => by omega, rfl⟩
  | succ j' ih =>
    have h0 : u.length % 2 = 0 := hEven 0 (Nat.zero_lt_succ j')
    have h1 : stepBlock (psi u) = oddMap u := stepBlock_psi u
    have h2 : stepBlock^[2] (psi u) = psi (stepBlock u) := by
      change stepBlock (stepBlock (psi u)) = psi (stepBlock u)
      rw [h1, stepBlock_oddMap_even u h0]
    have h_rec := ih (stepBlock u) (fun s hs => by
      have h_it := hEven (s + 1) (Nat.succ_lt_succ hs)
      rwa [Function.iterate_succ_apply] at h_it)
    refine ⟨?_, ?_⟩
    · intro s hs
      rcases (by omega : s = 0 ∨ s = 1 ∨ 2 ≤ s) with rfl | rfl | hge
      · exact psi_length_even u
      · rw [Function.iterate_one, h1, oddMap_length]; exact h0
      · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
        rw [Function.iterate_add_apply, h2]
        exact h_rec.1 s' (by omega)
    · have h_mul : 2 * (j' + 1) = 2 * j' + 2 := by omega
      rw [h_mul, Function.iterate_add_apply, h2, h_rec.2,
        ← Function.iterate_succ_apply stepBlock j' u]

lemma stepBlock_iterate_phi (j : ℕ) (u : List ℕ)
    (hOdd : ∀ s < j, (stepBlock^[s] u).length % 2 = 1)
    (hEnd : (stepBlock^[j] u).length % 2 = 0) :
    (∀ s < 2 * j + 1, (stepBlock^[s] (phi u)).length % 2 = 1) ∧
    (stepBlock^[2 * j + 1] (phi u)).length % 2 = 0 ∧
    stepBlock^[2 * j + 2] (phi u) = psi (stepBlock^[j + 1] u) := by
  induction j generalizing u with
  | zero =>
    dsimp at hEnd
    have h1 : stepBlock (phi u) = oddMap u := stepBlock_phi u
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      have hs0 : s = 0 := by omega
      subst hs0
      exact phi_length_odd u
    · rw [Function.iterate_one, h1, oddMap_length]; exact hEnd
    · change stepBlock (stepBlock (phi u)) = psi (stepBlock u)
      rw [h1, stepBlock_oddMap_even u hEnd]
  | succ j' ih =>
    have h0 : u.length % 2 = 1 := hOdd 0 (Nat.zero_lt_succ j')
    have h1 : stepBlock (phi u) = oddMap u := stepBlock_phi u
    have h2 : stepBlock^[2] (phi u) = phi (stepBlock u) := by
      change stepBlock (stepBlock (phi u)) = phi (stepBlock u)
      rw [h1, stepBlock_oddMap_odd u h0]
    have h_rec := ih (stepBlock u) (fun s hs => by
      have h_it := hOdd (s + 1) (Nat.succ_lt_succ hs)
      rwa [Function.iterate_succ_apply] at h_it) (by
      rwa [← Function.iterate_succ_apply stepBlock j' u])
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      rcases (by omega : s = 0 ∨ s = 1 ∨ 2 ≤ s) with rfl | rfl | hge
      · exact phi_length_odd u
      · rw [Function.iterate_one, h1, oddMap_length]; exact h0
      · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
        rw [Function.iterate_add_apply, h2]
        exact h_rec.1 s' (by omega)
    · have h_idx : 2 * (j' + 1) + 1 = (2 * j' + 1) + 2 := by omega
      rw [h_idx, Function.iterate_add_apply, h2]
      exact h_rec.2.1
    · have h_idx : 2 * (j' + 1) + 2 = (2 * j' + 2) + 2 := by omega
      rw [h_idx, Function.iterate_add_apply, h2, h_rec.2.2,
        ← Function.iterate_succ_apply stepBlock (j' + 1) u]

-- ============================================================================
-- Section 6: 0-Indexed `Pc` / `Sc`, `rawP'` / `rawS`, and Stage-$k$ Cascade
-- ============================================================================

def PSc : Bool → ℕ → ℕ → List ℕ
  | true, 0, c => [1 + c]
  | false, 0, c => [c]
  | true, k + 1, c => PSc true k 1 ++ PSc false k c
  | false, k + 1, c => PSc false k 0 ++ PSc true k c

def Pc (k c : ℕ) : List ℕ := PSc true k c
def Sc (k c : ℕ) : List ℕ := PSc false k c

@[simp] lemma Pc_zero (c : ℕ) : Pc 0 c = [1 + c] := rfl
@[simp] lemma Sc_zero (c : ℕ) : Sc 0 c = [c] := rfl
lemma Pc_succ (k c : ℕ) : Pc (k + 1) c = Pc k 1 ++ Sc k c := rfl
lemma Sc_succ (k c : ℕ) : Sc (k + 1) c = Sc k 0 ++ Pc k c := rfl

def nextMid : List Bool → List Bool
  | [] => []
  | false :: bs => true :: nextMid bs
  | true :: bs => true :: false :: false :: nextMid bs

def stepBs (bs : List Bool) : List Bool :=
  nextMid bs ++ [true]

def bsSeq : ℕ → List Bool
  | 0 => []
  | k + 1 => stepBs (bsSeq k)

lemma stepBs_iterate_eq (k : ℕ) : stepBs^[k] [] = bsSeq k := by
  induction k with
  | zero => rfl
  | succ k' ih => rw [Function.iterate_succ_apply', ih]; rfl

def evalW : List Bool → List ℕ
  | [] => []
  | false :: bs => 1 :: evalW bs
  | true :: bs => 1 :: 0 :: 0 :: evalW bs

def tailRaw (rkind : Bool) (d : ℕ) : List ℕ :=
  if rkind then [d + 1] else [0, d]

def MSeq1 (m : ℕ) : List ℕ :=
  evalW (bsSeq m) ++ [1]

def rawP' (m d : ℕ) : List ℕ :=
  MSeq1 m ++ tailRaw ((m + 1) % 2 == 1) d

def rawS (m d : ℕ) : List ℕ :=
  MSeq1 m ++ tailRaw ((m + 1) % 2 == 0) d

lemma nextMid_append (xs ys : List Bool) : nextMid (xs ++ ys) = nextMid xs ++ nextMid ys := by
  induction xs with
  | nil => rfl
  | cons b xs' ih => cases b <;> simp [nextMid, ih]

lemma evalW_append (xs ys : List Bool) : evalW (xs ++ ys) = evalW xs ++ evalW ys := by
  induction xs with
  | nil => rfl
  | cons b xs' ih => cases b <;> simp [evalW, ih]

lemma bsSeq_succ_eq (m : ℕ) :
    bsSeq (m + 1) = bsSeq m ++ (if (m + 1) % 2 = 1 then [true] else [false, false]) ++ bsSeq m := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    have h_lhs : bsSeq (m' + 2) =
        nextMid (bsSeq m' ++ (if (m' + 1) % 2 = 1 then [true] else [false, false]) ++ bsSeq m') ++ [true] := by
      change nextMid (bsSeq (m' + 1)) ++ [true] = _
      rw [ih]
    rw [h_lhs, nextMid_append, nextMid_append]
    change _ = (nextMid (bsSeq m') ++ [true]) ++
      (if (m' + 1 + 1) % 2 = 1 then [true] else [false, false]) ++
      (nextMid (bsSeq m') ++ [true])
    rcases (by omega : (m' + 1) % 2 = 1 ∨ (m' + 1) % 2 = 0) with hod | hev
    · have h_next : (m' + 1 + 1) % 2 = 0 := by omega
      simp [hod, h_next, nextMid, List.append_assoc]
    · have h_next : (m' + 1 + 1) % 2 = 1 := by omega
      simp [hev, h_next, nextMid, List.append_assoc]

lemma MSeq1_succ_eq (m : ℕ) :
    MSeq1 (m + 1) = rawS m 0 ++ MSeq1 m := by
  unfold rawS MSeq1
  rw [bsSeq_succ_eq m, evalW_append, evalW_append]
  rcases (by omega : (m + 1) % 2 = 1 ∨ (m + 1) % 2 = 0) with hod | hev
  · simp [hod, evalW, tailRaw, List.append_assoc]
  · simp [hev, evalW, tailRaw, List.append_assoc]

lemma rawP'_succ (m d : ℕ) : rawP' (m + 1) d = rawS m 0 ++ rawS m d := by
  unfold rawP'
  rw [MSeq1_succ_eq m, List.append_assoc]
  have h_b : ((m + 1 + 1) % 2 == 1) = ((m + 1) % 2 == 0) := by
    rcases (by omega : (m + 1) % 2 = 0 ∨ (m + 1) % 2 = 1) with h | h
    · have h2 : (m + 1 + 1) % 2 = 1 := by omega
      simp [h, h2]
    · have h2 : (m + 1 + 1) % 2 = 0 := by omega
      simp [h, h2]
  rw [h_b]
  rfl

lemma rawS_succ (m d : ℕ) : rawS (m + 1) d = rawS m 0 ++ rawP' m d := by
  unfold rawS
  rw [MSeq1_succ_eq m, List.append_assoc]
  have h_b : ((m + 1 + 1) % 2 == 0) = ((m + 1) % 2 == 1) := by
    rcases (by omega : (m + 1) % 2 = 0 ∨ (m + 1) % 2 = 1) with h | h
    · have h2 : (m + 1 + 1) % 2 = 1 := by omega
      simp [h, h2]
    · have h2 : (m + 1 + 1) % 2 = 0 := by omega
      simp [h, h2]
  rw [h_b]
  rfl

lemma rawP'_rawS_len (m : ℕ) :
    (∀ d, (rawP' m d).length % 2 = 0) ∧ (∀ d, (rawS m d).length % 2 = 1) := by
  induction m with
  | zero =>
    refine ⟨fun d => by simp [rawP', MSeq1, bsSeq, evalW, tailRaw],
            fun d => by simp [rawS, MSeq1, bsSeq, evalW, tailRaw]⟩
  | succ m' ih =>
    refine ⟨fun d => ?_, fun d => ?_⟩
    · rw [rawP'_succ]; exact length_append_odd_odd (ih.2 0) (ih.2 d)
    · rw [rawS_succ]; exact length_append_odd_even (ih.2 0) (ih.1 d)

lemma rawP'_rawS_eval (m : ℕ) :
    (∀ d, sb₁ (rawP' m d) = Pc (m + 1) 0 ++ List.replicate d 0) ∧
    (∀ d, stepBlock (rawS m d) = Sc (m + 1) 0 ++ List.replicate d 0) ∧
    (∀ d, stepBlock (rawP' m d) = Sc (m + 1) (d + 1)) ∧
    (∀ d, sb₁ (rawS m d) = Pc (m + 1) (d + 1)) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d; simp [rawP', MSeq1, bsSeq, evalW, tailRaw, sb₁, stepBlock, Pc, PSc, List.replicate_succ]
    · intro d; simp [rawS, MSeq1, bsSeq, evalW, tailRaw, stepBlock, Sc, PSc, List.replicate_succ]
    · intro d
      dsimp [rawP', MSeq1, bsSeq, evalW, tailRaw, stepBlock, Sc, PSc]
      rw [show d + 1 + 1 = 1 + (d + 1) by omega]
    · intro d; simp [rawS, MSeq1, bsSeq, evalW, tailRaw, sb₁, stepBlock, Pc, PSc]
  | succ m' ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have h_odd0 : (rawS m' 0).length % 2 = 1 := (rawP'_rawS_len m').2 0
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d
      rw [rawP'_succ, sb₁_append_odd (rawS m' 0) (rawS m' d) h_odd0, ih4 0, ih2 d]
      simp [Pc_succ, List.append_assoc]
    · intro d
      rw [rawS_succ, stepBlock_append_odd (rawS m' 0) (rawP' m' d) h_odd0, ih2 0, ih1 d]
      simp [Sc_succ, List.append_assoc]
    · intro d
      rw [rawP'_succ, stepBlock_append_odd (rawS m' 0) (rawS m' d) h_odd0, ih2 0, ih4 d]
      simp [Sc_succ]
    · intro d
      rw [rawS_succ, sb₁_append_odd (rawS m' 0) (rawP' m' d) h_odd0, ih4 0, ih3 d]
      rfl

def endP : ℕ → ℕ → List ℕ
  | 0, c => [0, 0, 1 + c]
  | m + 1, c => 0 :: rawP' m (2 ^ (m + 2) - 1 + c)

def endS : ℕ → ℕ → List ℕ
  | 0, c => [2 + c]
  | m + 1, c => rawS m (2 ^ (m + 2) - 1 + c)

lemma endP_len_odd (k c : ℕ) : (endP k c).length % 2 = 1 := by
  cases k with
  | zero => simp [endP]
  | succ m =>
    dsimp [endP]
    have h := (rawP'_rawS_len m).1 (2 ^ (m + 2) - 1 + c)
    omega

lemma endS_len_odd (k c : ℕ) : (endS k c).length % 2 = 1 := by
  cases k with
  | zero => simp [endS]
  | succ m => exact (rawP'_rawS_len m).2 (2 ^ (m + 2) - 1 + c)

lemma stepBlock_endP (k c : ℕ) :
    stepBlock (endP k c) = Pc k 0 ++ List.replicate (2 ^ (k + 1) - 1 + c) 0 := by
  cases k with
  | zero => rfl
  | succ m => exact (rawP'_rawS_eval m).1 (2 ^ (m + 2) - 1 + c)

lemma stepBlock_endS (k c : ℕ) :
    stepBlock (endS k c) = Sc k 0 ++ List.replicate (2 ^ (k + 1) - 1 + c) 0 := by
  cases k with
  | zero =>
    dsimp [endS, stepBlock, Sc_zero]
    rw [show 2 + c = (1 + c) + 1 by omega, List.replicate_succ]
  | succ m => exact (rawP'_rawS_eval m).2.1 (2 ^ (m + 2) - 1 + c)

lemma sb₁_endP (k c : ℕ) :
    sb₁ (endP k c) = [1] ++ Sc k (2 ^ (k + 1) + c) := by
  cases k with
  | zero =>
    dsimp [endP, sb₁, stepBlock, Sc_zero]
    rw [show 1 + c + 1 = 2 + c by omega]
  | succ m =>
    change stepBlock ([0, 0] ++ rawP' m (2 ^ (m + 2) - 1 + c)) = _
    rw [stepBlock_append_even [0, 0] _ (by simp), (rawP'_rawS_eval m).2.2.1]
    have h_pos : 1 ≤ 2 ^ (m + 2) := Nat.one_le_pow (m + 2) 2 (by decide)
    have h_add : 2 ^ (m + 2) - 1 + c + 1 = 2 ^ (m + 2) + c := by omega
    rw [h_add]
    rfl

lemma sb₁_endS (k c : ℕ) :
    sb₁ (endS k c) = Pc k (2 ^ (k + 1) + c) := by
  cases k with
  | zero =>
    dsimp [endS, sb₁, stepBlock, Pc_zero]
    rw [show 2 + c + 1 = 1 + (2 + c) by omega]
  | succ m =>
    dsimp [endS]
    rw [(rawP'_rawS_eval m).2.2.2]
    have h_pos : 1 ≤ 2 ^ (m + 2) := Nat.one_le_pow (m + 2) 2 (by decide)
    have h_add : 2 ^ (m + 2) - 1 + c + 1 = 2 ^ (m + 2) + c := by omega
    rw [h_add]

def evalMid (k : ℕ) : List Bool → List ℕ
  | [] => []
  | false :: bs => zBlock (k + 1) 0 ++ evalMid k bs
  | true :: bs => zBlock (k + 1) (2 ^ (k + 1)) ++ evalMid k bs

def tailStage (k : ℕ) (rkind : Bool) (c : ℕ) : List ℕ :=
  if rkind then
    zBlock (k + 1) 0 ++ Pc k c
  else
    zBlock (k + 1) 1 ++ Sc k c

def stage (k : ℕ) (lkind rkind : Bool) (bs : List Bool) (c : ℕ) : List ℕ :=
  PSc lkind k 0 ++ evalMid k bs ++ tailStage k rkind c

lemma evalMid_append (k : ℕ) (xs ys : List Bool) :
    evalMid k (xs ++ ys) = evalMid k xs ++ evalMid k ys := by
  induction xs with
  | nil => rfl
  | cons b xs' ih => cases b <;> simp [evalMid, ih, List.append_assoc]

lemma evalMid_zero_props (bs : List Bool) :
    (evalMid 0 bs).length % 2 = 0 ∧ sb₁ (evalMid 0 bs) = evalW bs := by
  induction bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs' ih =>
    cases b
    · have h_zb : zBlock 1 0 = [0, 0] := rfl
      dsimp [evalMid, evalW]
      rw [h_zb]
      refine ⟨length_append_even (by simp) ih.1, ?_⟩
      rw [sb₁_append_even [0, 0] (evalMid 0 bs') (by simp), ih.2]
      rfl
    · have h_zb : zBlock 1 2 = [0, 2] := rfl
      dsimp [evalMid, evalW]
      rw [h_zb]
      refine ⟨length_append_even (by simp) ih.1, ?_⟩
      rw [sb₁_append_even [0, 2] (evalMid 0 bs') (by simp), ih.2]
      rfl

lemma stage_zero_props (lkind rkind : Bool) (bs : List Bool) (c : ℕ) :
    (stage 0 lkind rkind bs c).length % 2 = 0 ∧
    stepBlock (stage 0 lkind rkind bs c) =
      (if lkind then [0] else []) ++ evalW bs ++ [1] ++ tailRaw rkind (1 + c) := by
  unfold stage
  have h_left : (PSc lkind 0 0).length % 2 = 1 ∧
      stepBlock (PSc lkind 0 0) = (if lkind then [0] else []) := by
    cases lkind <;> exact ⟨by simp [PSc], rfl⟩
  have h_mid := evalMid_zero_props bs
  have h_tail : (tailStage 0 rkind c).length % 2 = 1 ∧
      sb₁ (tailStage 0 rkind c) = [1] ++ tailRaw rkind (1 + c) := by
    cases rkind
    · refine ⟨by simp [tailStage, zBlock, Sc_zero], ?_⟩
      dsimp [tailStage, zBlock, Sc_zero, tailRaw, sb₁, stepBlock]
      rw [Nat.add_comm c 1]
    · refine ⟨by simp [tailStage, zBlock, Pc_zero], ?_⟩
      rfl
  refine ⟨length_append_odd_odd (length_append_odd_even h_left.1 h_mid.1) h_tail.1, ?_⟩
  rw [List.append_assoc, stepBlock_append_odd _ _ h_left.1, h_left.2]
  rw [sb₁_append_even (evalMid 0 bs) (tailStage 0 rkind c) h_mid.1, h_mid.2, h_tail.2]
  simp [List.append_assoc]

def evalMid1 (k : ℕ) : List Bool → List ℕ
  | [] => []
  | false :: bs => [2 ^ (k + 1) - 1, 2 ^ (k + 1) - 1] ++ evalMid1 k bs
  | true :: bs => [2 ^ (k + 1) - 1, 2 ^ (k + 2) + (2 ^ (k + 1) - 1)] ++ evalMid1 k bs

def tailStage1 (k : ℕ) (rkind : Bool) (c : ℕ) : List ℕ :=
  if rkind then
    [2 ^ (k + 1) - 1, 2 ^ (k + 1) - 1] ++ endP k c
  else
    [2 ^ (k + 1) - 1, 1 + (2 ^ (k + 1) - 1)] ++ endS k c

lemma evalMid_succ_step (k : ℕ) (bs : List Bool) :
    (∀ s ≤ 2 ^ (k + 1) - 1, (stepBlock^[s] (evalMid (k + 1) bs)).length % 2 = 0) ∧
    stepBlock^[2 ^ (k + 1) - 1] (evalMid (k + 1) bs) = evalMid1 k bs := by
  induction bs with
  | nil =>
    refine ⟨fun s _ => by simp [evalMid, stepBlock_iterate_nil], stepBlock_iterate_nil _⟩
  | cons b bs' ih =>
    cases b
    · dsimp [evalMid, evalMid1]
      have hz := zBlock_double_props k 0
      refine ⟨fun s hs => ?_, ?_⟩
      · rw [stepBlock_iterate_append_even s _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt (Nat.lt_of_lt_of_le hs' hs)))]
        exact length_append_even (hz.1 s hs) (ih.1 s hs)
      · rw [stepBlock_iterate_append_even (2 ^ (k + 1) - 1) _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt hs'))]
        rw [hz.2, ih.2, Nat.zero_add]
        rfl
    · dsimp [evalMid, evalMid1]
      have hz := zBlock_double_props k (2 ^ (k + 2))
      refine ⟨fun s hs => ?_, ?_⟩
      · rw [stepBlock_iterate_append_even s _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt (Nat.lt_of_lt_of_le hs' hs)))]
        exact length_append_even (hz.1 s hs) (ih.1 s hs)
      · rw [stepBlock_iterate_append_even (2 ^ (k + 1) - 1) _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt hs'))]
        rw [hz.2, ih.2]
        rfl

lemma evalMid1_shift_sb1 (k : ℕ) (bs : List Bool) (rest : List ℕ) :
    List.replicate (2 ^ (k + 1) - 1) 0 ++ sb₁ (evalMid1 k bs ++ rest) =
    evalMid k (nextMid bs) ++ (List.replicate (2 ^ (k + 1) - 1) 0 ++ sb₁ rest) := by
  induction bs with
  | nil => simp [evalMid1, nextMid, evalMid]
  | cons b bs' ih =>
    cases b
    · dsimp [evalMid1, nextMid, evalMid]
      rw [zBlock_shift_sb1_zero k (evalMid1 k bs' ++ rest), ih]
      simp [List.append_assoc]
    · dsimp [evalMid1, nextMid, evalMid]
      rw [zBlock_shift_sb1 k (2 ^ (k + 2)) (evalMid1 k bs' ++ rest)]
      have h_split : 2 ^ (k + 2) + (2 ^ (k + 1) - 1) =
          2 ^ (k + 1) + 2 ^ (k + 1) + (2 ^ (k + 1) - 1) := by
        rw [pow_two_succ (k + 1)]
      have h_z0 : zBlock (k + 1) 0 = List.replicate (2 ^ (k + 1)) 0 := by
        unfold zBlock
        have h_pos : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) :=
          Nat.sub_add_cancel (Nat.one_le_pow (k + 1) 2 (by decide))
        rw [← List.replicate_succ', h_pos]
      rw [h_split, List.replicate_add, List.replicate_add, ← h_z0, List.append_assoc,
        List.append_assoc, ih]
      simp [List.append_assoc]

lemma tailStage1_shift_sb1 (k : ℕ) (rkind : Bool) (c : ℕ) :
    List.replicate (2 ^ (k + 1) - 1) 0 ++ sb₁ (tailStage1 k rkind c) =
    evalMid k [true] ++ tailStage k (!rkind) (2 ^ (k + 1) + c) := by
  have h_pos : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow (k + 1) 2 (by decide))
  cases rkind
  · dsimp [tailStage1, evalMid, tailStage]
    rw [zBlock_shift_sb1 k 1 (endS k c), Nat.add_comm 1 (2 ^ (k + 1) - 1), h_pos, sb₁_endS k c]
    have h_z0 : zBlock (k + 1) 0 = List.replicate (2 ^ (k + 1)) 0 := by
      unfold zBlock; rw [← List.replicate_succ', h_pos]
    rw [h_z0]
    simp
  · dsimp [tailStage1, evalMid, tailStage]
    rw [zBlock_shift_sb1_zero k (endP k c), sb₁_endP k c]
    unfold zBlock
    simp [List.append_assoc]

lemma flip_iterate_eq (k : ℕ) :
    (! ·)^[k] true = ((k + 1) % 2 == 1) ∧ (! ·)^[k] false = ((k + 1) % 2 == 0) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k' ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1, ih.2]
    rcases (by omega : (k' + 1) % 2 = 0 ∨ (k' + 1) % 2 = 1) with h | h
    · have h2 : (k' + 1 + 1) % 2 = 1 := by omega
      simp [h, h2]
    · have h2 : (k' + 1 + 1) % 2 = 0 := by omega
      simp [h, h2]

lemma Pc_Sc_cascade (k : ℕ) :
    (∀ b c, ∀ s < 2 ^ (k + 1) - 1, (stepBlock^[s] (PSc b (k + 1) c)).length % 2 = 0) ∧
    (∀ c, stepBlock^[2 ^ (k + 1) - 1] (Pc (k + 1) c) = endP k c) ∧
    (∀ c, stepBlock^[2 ^ (k + 1) - 1] (Sc (k + 1) c) = endS k c) ∧
    (∀ lkind rkind bs c,
      (∀ s < 2 ^ (k + 1) - 1, (stepBlock^[s] (stage k lkind rkind bs c)).length % 2 = 0) ∧
      stepBlock^[2 ^ (k + 1) - 1] (stage k lkind rkind bs c) =
        (if lkind then [0] else []) ++ evalW (stepBs^[k] bs) ++ [1] ++
          tailRaw ((! ·)^[k] rkind) (2 ^ (k + 1) - 1 + c)) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b c s hs
      have hs0 : s = 0 := by change s < 1 at hs; omega
      subst hs0
      cases b <;> simp [PSc]
    · intro c
      change [0, 0, c + 1] = [0, 0, 1 + c]
      rw [Nat.add_comm c 1]
    · intro c
      change [1 + c + 1] = [2 + c]
      rw [show 1 + c + 1 = 2 + c by omega]
    · intro lkind rkind bs c
      have h_st := stage_zero_props lkind rkind bs c
      refine ⟨?_, ?_⟩
      · intro s hs
        have hs0 : s = 0 := by change s < 1 at hs; omega
        subst hs0
        exact h_st.1
      · change stepBlock (stage 0 lkind rkind bs c) = _
        rw [h_st.2]
        rfl
  | succ k' ih =>
    obtain ⟨ih_even, ih_endP, ih_endS, ih_stage⟩ := ih
    have h_pos : 1 ≤ 2 ^ (k' + 1) := Nat.one_le_pow (k' + 1) 2 (by decide)
    have h_PSc_end : ∀ (b : Bool) (c : ℕ), stepBlock^[2 ^ (k' + 1) - 1] (PSc b (k' + 1) c) =
        if b then endP k' c else endS k' c := by
      intro b c; cases b
      · exact ih_endS c
      · exact ih_endP c
    have h_PSc_end_odd : ∀ (b : Bool) (c : ℕ), (if b then endP k' c else endS k' c).length % 2 = 1 := by
      intro b c; cases b
      · exact endS_len_odd k' c
      · exact endP_len_odd k' c
    have h_stage_succ : ∀ lkind rkind bs c,
        (∀ s < 2 ^ (k' + 2) - 1, (stepBlock^[s] (stage (k' + 1) lkind rkind bs c)).length % 2 = 0) ∧
        stepBlock^[2 ^ (k' + 2) - 1] (stage (k' + 1) lkind rkind bs c) =
          (if lkind then [0] else []) ++ evalW (stepBs^[k' + 1] bs) ++ [1] ++
            tailRaw ((! ·)^[k' + 1] rkind) (2 ^ (k' + 2) - 1 + c) := by
      intro lkind rkind bs c
      have h_mid := evalMid_succ_step k' bs
      have h_tail : (∀ s < 2 ^ (k' + 1) - 1,
            (stepBlock^[s] (tailStage (k' + 1) rkind c)).length % 2 = 0) ∧
          stepBlock^[2 ^ (k' + 1) - 1] (tailStage (k' + 1) rkind c) = tailStage1 k' rkind c := by
        cases rkind
        · change (∀ s < 2 ^ (k' + 1) - 1, (stepBlock^[s] (zBlock (k' + 2) 1 ++ Sc (k' + 1) c)).length % 2 = 0) ∧
            stepBlock^[2 ^ (k' + 1) - 1] (zBlock (k' + 2) 1 ++ Sc (k' + 1) c) =
              [2 ^ (k' + 1) - 1, 1 + (2 ^ (k' + 1) - 1)] ++ endS k' c
          have hz := zBlock_double_props k' 1
          refine ⟨fun s hs => ?_, ?_⟩
          · rw [stepBlock_iterate_append_even s _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt (Nat.lt_trans hs' hs)))]
            exact length_append_even (hz.1 s (Nat.le_of_lt hs)) (ih_even false c s hs)
          · rw [stepBlock_iterate_append_even (2 ^ (k' + 1) - 1) _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt hs'))]
            rw [hz.2, ih_endS c]
        · change (∀ s < 2 ^ (k' + 1) - 1, (stepBlock^[s] (zBlock (k' + 2) 0 ++ Pc (k' + 1) c)).length % 2 = 0) ∧
            stepBlock^[2 ^ (k' + 1) - 1] (zBlock (k' + 2) 0 ++ Pc (k' + 1) c) =
              [2 ^ (k' + 1) - 1, 2 ^ (k' + 1) - 1] ++ endP k' c
          have hz := zBlock_double_props k' 0
          refine ⟨fun s hs => ?_, ?_⟩
          · rw [stepBlock_iterate_append_even s _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt (Nat.lt_trans hs' hs)))]
            exact length_append_even (hz.1 s (Nat.le_of_lt hs)) (ih_even true c s hs)
          · rw [stepBlock_iterate_append_even (2 ^ (k' + 1) - 1) _ _ (fun s' hs' => hz.1 s' (Nat.le_of_lt hs'))]
            rw [hz.2, ih_endP c, Nat.zero_add]
      have h_at_mid : stepBlock^[2 ^ (k' + 1) - 1] (stage (k' + 1) lkind rkind bs c) =
          (if lkind then endP k' 0 else endS k' 0) ++ evalMid1 k' bs ++ tailStage1 k' rkind c := by
        unfold stage
        rw [List.append_assoc]
        rw [stepBlock_iterate_append_even (2 ^ (k' + 1) - 1) (PSc lkind (k' + 1) 0) _ (ih_even lkind 0)]
        rw [stepBlock_iterate_append_even (2 ^ (k' + 1) - 1) (evalMid (k' + 1) bs) _
          (fun s' hs' => h_mid.1 s' (Nat.le_of_lt hs'))]
        rw [h_PSc_end lkind 0, h_mid.2, h_tail.2, List.append_assoc]
      have h_at_next : stepBlock^[2 ^ (k' + 1)] (stage (k' + 1) lkind rkind bs c) =
          stage k' lkind (!rkind) (stepBs bs) (2 ^ (k' + 1) + c) := by
        have h_split : 2 ^ (k' + 1) = (2 ^ (k' + 1) - 1) + 1 := by omega
        have h_step : stepBlock^[2 ^ (k' + 1)] (stage (k' + 1) lkind rkind bs c) =
            stepBlock (stepBlock^[2 ^ (k' + 1) - 1] (stage (k' + 1) lkind rkind bs c)) := by
          rw [h_split]
          exact Function.iterate_succ_apply' stepBlock (2 ^ (k' + 1) - 1)
            (stage (k' + 1) lkind rkind bs c)
        rw [h_step, h_at_mid]
        rw [List.append_assoc, stepBlock_append_odd _ _ (h_PSc_end_odd lkind 0)]
        have h_sb_left : stepBlock (if lkind then endP k' 0 else endS k' 0) =
            PSc lkind k' 0 ++ List.replicate (2 ^ (k' + 1) - 1) 0 := by
          cases lkind
          · exact stepBlock_endS k' 0
          · exact stepBlock_endP k' 0
        rw [h_sb_left, List.append_assoc, evalMid1_shift_sb1 k' bs (tailStage1 k' rkind c),
          tailStage1_shift_sb1 k' rkind c]
        unfold stage stepBs
        rw [evalMid_append]
        simp [List.append_assoc]
      have h_sub := ih_stage lkind (!rkind) (stepBs bs) (2 ^ (k' + 1) + c)
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases (by omega : s < 2 ^ (k' + 1) - 1 ∨ s = 2 ^ (k' + 1) - 1 ∨ 2 ^ (k' + 1) ≤ s) with hlt | rfl | hge
        · unfold stage
          rw [List.append_assoc]
          rw [stepBlock_iterate_append_even s (PSc lkind (k' + 1) 0) _
            (fun s' hs' => ih_even lkind 0 s' (Nat.lt_trans hs' hlt))]
          rw [stepBlock_iterate_append_even s (evalMid (k' + 1) bs) _
            (fun s' hs' => h_mid.1 s' (Nat.le_of_lt (Nat.lt_trans hs' hlt)))]
          exact length_append_even (ih_even lkind 0 s hlt)
            (length_append_even (h_mid.1 s (Nat.le_of_lt hlt)) (h_tail.1 s hlt))
        · rw [h_at_mid]
          have h1 := h_PSc_end_odd lkind 0
          have h2 : (evalMid1 k' bs).length % 2 = 0 := by
            rw [← h_mid.2]; exact h_mid.1 (2 ^ (k' + 1) - 1) (le_refl _)
          have h3 : (tailStage1 k' rkind c).length % 2 = 1 := by
            cases rkind <;> dsimp [tailStage1]
            · have h := endS_len_odd k' c; omega
            · have h := endP_len_odd k' c; omega
          exact length_append_odd_odd (length_append_odd_even h1 h2) h3
        · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 ^ (k' + 1) := ⟨s - 2 ^ (k' + 1), by omega⟩
          have hs' : s' < 2 ^ (k' + 1) - 1 := by
            rw [pow_two_succ (k' + 1)] at hs; omega
          rw [Function.iterate_add_apply, h_at_next]
          exact h_sub.1 s' hs'
      · have h_split : 2 ^ (k' + 2) - 1 = (2 ^ (k' + 1) - 1) + 2 ^ (k' + 1) := by
          rw [pow_two_succ (k' + 1)]; omega
        have h_step : stepBlock^[2 ^ (k' + 2) - 1] (stage (k' + 1) lkind rkind bs c) =
            stepBlock^[2 ^ (k' + 1) - 1] (stepBlock^[2 ^ (k' + 1)] (stage (k' + 1) lkind rkind bs c)) := by
          rw [← Function.iterate_add_apply, h_split]
        rw [h_step, h_at_next, h_sub.2]
        have h_add : 2 ^ (k' + 1) - 1 + (2 ^ (k' + 1) + c) = 2 ^ (k' + 2) - 1 + c := by
          rw [pow_two_succ (k' + 1)]; omega
        rw [← Function.iterate_succ_apply stepBs k' bs,
          ← Function.iterate_succ_apply (! ·) k' rkind, h_add]
    have h_Pc_mid : ∀ c, stepBlock^[2 ^ (k' + 1) - 1] (Pc (k' + 2) c) =
        endP k' 1 ++ endS k' c := by
      intro c
      rw [Pc_succ]
      rw [stepBlock_iterate_append_even (2 ^ (k' + 1) - 1) (Pc (k' + 1) 1) (Sc (k' + 1) c)
        (ih_even true 1)]
      rw [ih_endP 1, ih_endS c]
    have h_Pc_next : ∀ c, stepBlock^[2 ^ (k' + 1)] (Pc (k' + 2) c) =
        stage k' true true [] (2 ^ (k' + 1) + c) := by
      intro c
      have h_split : 2 ^ (k' + 1) = (2 ^ (k' + 1) - 1) + 1 := by omega
      have h_step : stepBlock^[2 ^ (k' + 1)] (Pc (k' + 2) c) =
          stepBlock (stepBlock^[2 ^ (k' + 1) - 1] (Pc (k' + 2) c)) := by
        rw [h_split]
        exact Function.iterate_succ_apply' stepBlock (2 ^ (k' + 1) - 1) (Pc (k' + 2) c)
      rw [h_step, h_Pc_mid c]
      rw [stepBlock_append_odd (endP k' 1) (endS k' c) (endP_len_odd k' 1),
        stepBlock_endP k' 1, sb₁_endS k' c]
      rw [List.replicate_succ']
      unfold stage evalMid tailStage zBlock Pc
      simp only [List.append_assoc, List.nil_append, ↓reduceIte]
    have h_Sc_mid : ∀ c, stepBlock^[2 ^ (k' + 1) - 1] (Sc (k' + 2) c) =
        endS k' 0 ++ endP k' c := by
      intro c
      rw [Sc_succ]
      rw [stepBlock_iterate_append_even (2 ^ (k' + 1) - 1) (Sc (k' + 1) 0) (Pc (k' + 1) c)
        (ih_even false 0)]
      rw [ih_endS 0, ih_endP c]
    have h_Sc_next : ∀ c, stepBlock^[2 ^ (k' + 1)] (Sc (k' + 2) c) =
        stage k' false false [] (2 ^ (k' + 1) + c) := by
      intro c
      have h_split : 2 ^ (k' + 1) = (2 ^ (k' + 1) - 1) + 1 := by omega
      have h_step : stepBlock^[2 ^ (k' + 1)] (Sc (k' + 2) c) =
          stepBlock (stepBlock^[2 ^ (k' + 1) - 1] (Sc (k' + 2) c)) := by
        rw [h_split]
        exact Function.iterate_succ_apply' stepBlock (2 ^ (k' + 1) - 1) (Sc (k' + 2) c)
      rw [h_step, h_Sc_mid c]
      rw [stepBlock_append_odd (endS k' 0) (endP k' c) (endS_len_odd k' 0),
        stepBlock_endS k' 0, sb₁_endP k' c]
      unfold stage evalMid tailStage zBlock Sc
      simp only [Nat.add_zero, List.append_assoc, List.nil_append, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, ?_, h_stage_succ⟩
    · intro b c s hs
      cases b
      · change (stepBlock^[s] (Sc (k' + 2) c)).length % 2 = 0
        rcases (by omega : s < 2 ^ (k' + 1) - 1 ∨ s = 2 ^ (k' + 1) - 1 ∨ 2 ^ (k' + 1) ≤ s) with hlt | rfl | hge
        · rw [Sc_succ, stepBlock_iterate_append_even s (Sc (k' + 1) 0) (Pc (k' + 1) c)
            (fun s' hs' => ih_even false 0 s' (Nat.lt_trans hs' hlt))]
          exact length_append_even (ih_even false 0 s hlt) (ih_even true c s hlt)
        · rw [h_Sc_mid c]
          exact length_append_odd_odd (endS_len_odd k' 0) (endP_len_odd k' c)
        · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 ^ (k' + 1) := ⟨s - 2 ^ (k' + 1), by omega⟩
          have hs' : s' < 2 ^ (k' + 1) - 1 := by rw [pow_two_succ (k' + 1)] at hs; omega
          rw [Function.iterate_add_apply, h_Sc_next c]
          exact (ih_stage false false [] (2 ^ (k' + 1) + c)).1 s' hs'
      · change (stepBlock^[s] (Pc (k' + 2) c)).length % 2 = 0
        rcases (by omega : s < 2 ^ (k' + 1) - 1 ∨ s = 2 ^ (k' + 1) - 1 ∨ 2 ^ (k' + 1) ≤ s) with hlt | rfl | hge
        · rw [Pc_succ, stepBlock_iterate_append_even s (Pc (k' + 1) 1) (Sc (k' + 1) c)
            (fun s' hs' => ih_even true 1 s' (Nat.lt_trans hs' hlt))]
          exact length_append_even (ih_even true 1 s hlt) (ih_even false c s hlt)
        · rw [h_Pc_mid c]
          exact length_append_odd_odd (endP_len_odd k' 1) (endS_len_odd k' c)
        · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 ^ (k' + 1) := ⟨s - 2 ^ (k' + 1), by omega⟩
          have hs' : s' < 2 ^ (k' + 1) - 1 := by rw [pow_two_succ (k' + 1)] at hs; omega
          rw [Function.iterate_add_apply, h_Pc_next c]
          exact (ih_stage true true [] (2 ^ (k' + 1) + c)).1 s' hs'
    · intro c
      have h_split : 2 ^ (k' + 2) - 1 = (2 ^ (k' + 1) - 1) + 2 ^ (k' + 1) := by
        rw [pow_two_succ (k' + 1)]; omega
      have h_step : stepBlock^[2 ^ (k' + 2) - 1] (Pc (k' + 2) c) =
          stepBlock^[2 ^ (k' + 1) - 1] (stepBlock^[2 ^ (k' + 1)] (Pc (k' + 2) c)) := by
        rw [← Function.iterate_add_apply, h_split]
      rw [h_step, h_Pc_next c, (ih_stage true true [] (2 ^ (k' + 1) + c)).2]
      rw [stepBs_iterate_eq k', (flip_iterate_eq k').1]
      have h_add : 2 ^ (k' + 1) - 1 + (2 ^ (k' + 1) + c) = 2 ^ (k' + 2) - 1 + c := by
        rw [pow_two_succ (k' + 1)]; omega
      rw [h_add]
      rfl
    · intro c
      have h_split : 2 ^ (k' + 2) - 1 = (2 ^ (k' + 1) - 1) + 2 ^ (k' + 1) := by
        rw [pow_two_succ (k' + 1)]; omega
      have h_step : stepBlock^[2 ^ (k' + 2) - 1] (Sc (k' + 2) c) =
          stepBlock^[2 ^ (k' + 1) - 1] (stepBlock^[2 ^ (k' + 1)] (Sc (k' + 2) c)) := by
        rw [← Function.iterate_add_apply, h_split]
      rw [h_step, h_Sc_next c, (ih_stage false false [] (2 ^ (k' + 1) + c)).2]
      rw [stepBs_iterate_eq k', (flip_iterate_eq k').2]
      have h_add : 2 ^ (k' + 1) - 1 + (2 ^ (k' + 1) + c) = 2 ^ (k' + 2) - 1 + c := by
        rw [pow_two_succ (k' + 1)]; omega
      rw [h_add]
      rfl

-- ============================================================================
-- Section 7: Simultaneous Era Induction (`tail` & `top`) and `is_does_not_halt`
-- ============================================================================

def BSeq (k : ℕ) : List ℕ :=
  Pc k 0 ++ List.replicate (2 ^ (k + 1)) 0

def mSteps : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => 2 ^ (k + 1) + mSteps k

def ESeq : ℕ → List ℕ
  | 0 => BSeq 0
  | 1 => stepBlock (BSeq 1) ++ [0, 0]
  | k + 2 => stepBlock^[mSteps (k + 2)] (BSeq (k + 2)) ++ ESeq k

lemma mSteps_sum (k : ℕ) : mSteps k + mSteps (k + 1) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    have h_pos : 1 ≤ 2 ^ (k' + 1) := Nat.one_le_pow (k' + 1) 2 (by decide)
    change mSteps (k' + 1) + (2 ^ (k' + 1) + mSteps k') = 2 ^ (k' + 2) - 1
    rw [pow_two_succ (k' + 1)]
    omega

lemma mSteps_pos (k : ℕ) : 1 ≤ mSteps (k + 1) := by
  cases k with
  | zero => rfl
  | succ k' =>
    change 1 ≤ 2 ^ (k' + 1) + mSteps k'
    have h_pos : 1 ≤ 2 ^ (k' + 1) := Nat.one_le_pow (k' + 1) 2 (by decide)
    omega

lemma mSteps_lt_pow (k : ℕ) : mSteps k < 2 ^ k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | k'
    · decide
    · decide
    · have hk' := ih k' (by omega)
      change 2 ^ (k' + 1) + mSteps k' < 2 ^ (k' + 2)
      have h_pow : 2 ^ (k' + 2) = 2 ^ (k' + 1) + 2 ^ k' + 2 ^ k' := by
        rw [pow_two_succ (k' + 1), pow_two_succ k']; omega
      omega

lemma two_mul_mSteps (k : ℕ) :
    2 * mSteps (k + 1) = if k % 2 = 0 then mSteps (k + 2) else mSteps (k + 2) - 1 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | k'
    · rfl
    · rfl
    · have hk' := ih k' (by omega)
      have h_pos : 1 ≤ mSteps (k' + 2) := mSteps_pos (k' + 1)
      have h_pow : 2 ^ (k' + 3) = 2 ^ (k' + 2) + 2 ^ (k' + 2) := pow_two_succ (k' + 2)
      change 2 * (2 ^ (k' + 2) + mSteps (k' + 1)) =
        if (k' + 2) % 2 = 0 then 2 ^ (k' + 3) + mSteps (k' + 2)
        else 2 ^ (k' + 3) + mSteps (k' + 2) - 1
      rw [Nat.add_mod_right k' 2, Nat.mul_add, hk']
      rcases (by omega : k' % 2 = 0 ∨ ¬(k' % 2 = 0)) with hev | hod
      · simp only [hev, ↓reduceIte]; omega
      · simp only [hod, ↓reduceIte]; omega

lemma Pc_step_pow (k c : ℕ) :
    stepBlock^[2 ^ (k + 1)] (Pc (k + 2) c) = BSeq k ++ Pc k (2 ^ (k + 1) + c) := by
  have h_pos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
  have h_split : 2 ^ (k + 1) = (2 ^ (k + 1) - 1) + 1 := by omega
  have h_step : stepBlock^[2 ^ (k + 1)] (Pc (k + 2) c) =
      stepBlock (stepBlock^[2 ^ (k + 1) - 1] (Pc (k + 2) c)) := by
    rw [h_split]
    exact Function.iterate_succ_apply' stepBlock (2 ^ (k + 1) - 1) (Pc (k + 2) c)
  rw [h_step, Pc_succ]
  rw [stepBlock_iterate_append_even (2 ^ (k + 1) - 1) (Pc (k + 1) 1) (Sc (k + 1) c)
    ((Pc_Sc_cascade k).1 true 1)]
  rw [(Pc_Sc_cascade k).2.1 1, (Pc_Sc_cascade k).2.2.1 c]
  rw [stepBlock_append_odd (endP k 1) (endS k c) (endP_len_odd k 1),
    stepBlock_endP k 1, sb₁_endS k c]
  have h_sub : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by omega
  rw [h_sub]
  simp [BSeq, List.append_assoc]

lemma BSeq_even_succ (k : ℕ) :
    ∀ s < 2 ^ (k + 1) - 1, (stepBlock^[s] (BSeq (k + 1))).length % 2 = 0 := by
  intro s hs
  have h_pos : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow (k + 2) 2 (by decide)
  have h_B : BSeq (k + 1) = Pc (k + 1) 0 ++ zBlock (k + 2) 0 := by
    unfold BSeq zBlock
    have h_sub : 2 ^ (k + 2) - 1 + 1 = 2 ^ (k + 2) := by omega
    rw [← List.replicate_succ', h_sub]
  rw [h_B]
  rw [stepBlock_iterate_append_even s (Pc (k + 1) 0) (zBlock (k + 2) 0)
    (fun s' hs' => (Pc_Sc_cascade k).1 true 0 s' (Nat.lt_trans hs' hs))]
  exact length_append_even ((Pc_Sc_cascade k).1 true 0 s hs)
    ((zBlock_double_props k 0).1 s (Nat.le_of_lt hs))

lemma BSeq_even_mSteps (k : ℕ) :
    ∀ s < mSteps k, (stepBlock^[s] (BSeq k)).length % 2 = 0 := by
  rcases k with _ | _ | k'
  · intro s hs; change s < 0 at hs; omega
  · intro s hs
    have hs0 : s = 0 := by change s < 1 at hs; omega
    subst hs0; rfl
  · intro s hs
    have h_lt : mSteps (k' + 2) ≤ 2 ^ (k' + 2) - 1 := by
      have := mSteps_lt_pow (k' + 2); omega
    exact BSeq_even_succ (k' + 1) s (Nat.lt_of_lt_of_le hs h_lt)

lemma Pc_to_ESeq (k : ℕ) :
    ∀ c, stepBlock^[2 ^ (k + 1) + mSteps k] (Pc (k + 2) c) =
      ESeq k ++ [2 * mSteps (k + 1) + 1 + c] := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | k'
    · intro c
      change stepBlock^[2 ^ 1] (Pc 2 c) = BSeq 0 ++ [3 + c]
      rw [Pc_step_pow 0 c]
      dsimp [Pc, PSc]
      congr 2; omega
    · intro c
      change stepBlock^[2 ^ 2 + 1] (Pc 3 c) = (stepBlock (BSeq 1) ++ [0, 0]) ++ [5 + c]
      have h_step : stepBlock^[2 ^ 2 + 1] (Pc 3 c) =
          stepBlock (stepBlock^[2 ^ 2] (Pc 3 c)) :=
        Function.iterate_succ_apply' stepBlock (2 ^ 2) (Pc 3 c)
      rw [h_step, Pc_step_pow 1 c]
      rw [stepBlock_append_even (BSeq 1) (Pc 1 (2 ^ (1 + 1) + c)) rfl]
      have h_pc1 : stepBlock (Pc 1 (2 ^ (1 + 1) + c)) = [0, 0, 5 + c] := by
        dsimp [Pc, PSc, stepBlock]
        congr 3; omega
      rw [h_pc1]
      simp [List.append_assoc]
    · intro c
      have h_split : 2 ^ (k' + 3) + mSteps (k' + 2) = mSteps (k' + 2) + 2 ^ (k' + 3) := by omega
      rw [h_split, Function.iterate_add_apply, Pc_step_pow (k' + 2) c]
      rw [stepBlock_iterate_append_even (mSteps (k' + 2)) (BSeq (k' + 2))
        (Pc (k' + 2) (2 ^ (k' + 3) + c)) (BSeq_even_mSteps (k' + 2))]
      have h_sub := ih k' (by omega) (2 ^ (k' + 3) + c)
      change stepBlock^[mSteps (k' + 2)] (Pc (k' + 2) (2 ^ (k' + 3) + c)) = _ at h_sub
      rw [h_sub]
      change _ = (stepBlock^[mSteps (k' + 2)] (BSeq (k' + 2)) ++ ESeq k') ++
        [2 * mSteps (k' + 3) + 1 + c]
      have h_arith : 2 * mSteps (k' + 1) + 1 + (2 ^ (k' + 3) + c) =
          2 * mSteps (k' + 3) + 1 + c := by
        change 2 * mSteps (k' + 1) + 1 + (2 ^ (k' + 3) + c) =
          2 * (2 ^ (k' + 2) + mSteps (k' + 1)) + 1 + c
        rw [pow_two_succ (k' + 2)]; omega
      rw [h_arith, List.append_assoc]

lemma ESeq_append_singleton_even (k : ℕ) :
    ∀ s < mSteps (k + 1),
      (stepBlock^[s] (ESeq k ++ [2 * mSteps (k + 1) + 1])).length % 2 = 0 := by
  intro s hs
  have h_eq := (Pc_to_ESeq k 0).symm
  rw [Nat.add_zero] at h_eq
  rw [h_eq, ← Function.iterate_add_apply]
  have h_pos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
  have h_sum := mSteps_sum k
  have h_lt : s + (2 ^ (k + 1) + mSteps k) < 2 ^ (k + 2) - 1 := by
    rw [pow_two_succ (k + 1)]; omega
  exact (Pc_Sc_cascade (k + 1)).1 true 0 _ h_lt

lemma ESeq_odd_lt (k : ℕ) :
    ∀ j < mSteps (k + 1), (stepBlock^[j] (ESeq k)).length % 2 = 1 := by
  intro j hj
  have h_ev := ESeq_append_singleton_even k j hj
  have h_iter := stepBlock_iterate_append_singleton j (ESeq k) (2 * mSteps (k + 1) + 1)
    (fun s hs => ESeq_append_singleton_even k s (Nat.lt_trans hs hj))
  rw [h_iter, List.length_append] at h_ev
  dsimp at h_ev
  omega

lemma ESeq_at_mSteps_eq (k : ℕ) :
    stepBlock^[mSteps (k + 1)] (ESeq k) ++ [3 * mSteps (k + 1) + 1] = endP (k + 1) 0 := by
  have h_iter := stepBlock_iterate_append_singleton (mSteps (k + 1)) (ESeq k)
    (2 * mSteps (k + 1) + 1) (ESeq_append_singleton_even k)
  have h_add : 2 * mSteps (k + 1) + 1 + mSteps (k + 1) = 3 * mSteps (k + 1) + 1 := by omega
  rw [h_add] at h_iter
  rw [← h_iter]
  have h_eq := (Pc_to_ESeq k 0).symm
  rw [Nat.add_zero] at h_eq
  rw [h_eq, ← Function.iterate_add_apply]
  have h_pos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
  have h_sum := mSteps_sum k
  have h_idx : mSteps (k + 1) + (2 ^ (k + 1) + mSteps k) = 2 ^ (k + 2) - 1 := by
    rw [pow_two_succ (k + 1)]; omega
  rw [h_idx]
  exact (Pc_Sc_cascade (k + 1)).2.1 0

lemma ESeq_even_at (k : ℕ) :
    (stepBlock^[mSteps (k + 1)] (ESeq k)).length % 2 = 0 := by
  have h_eq := congrArg List.length (ESeq_at_mSteps_eq k)
  have h_odd := endP_len_odd (k + 1) 0
  rw [List.length_append] at h_eq
  dsimp at h_eq
  omega

lemma ESeq_to_next_BSeq (k : ℕ) :
    stepBlock^[mSteps (k + 1) + 1] (ESeq k) ++ List.replicate (3 * mSteps (k + 1) + 2) 0 =
    BSeq (k + 1) := by
  have h_sb := congrArg stepBlock (ESeq_at_mSteps_eq k)
  rw [stepBlock_append_even (stepBlock^[mSteps (k + 1)] (ESeq k)) [3 * mSteps (k + 1) + 1]
    (ESeq_even_at k), stepBlock_endP (k + 1) 0, Nat.add_zero] at h_sb
  dsimp [stepBlock] at h_sb
  rw [← Function.iterate_succ_apply' stepBlock (mSteps (k + 1)) (ESeq k)] at h_sb
  have h_app := congrArg (· ++ [0]) h_sb
  have h_pos : 2 ^ (k + 2) - 1 + 1 = 2 ^ (k + 2) :=
    Nat.sub_add_cancel (Nat.one_le_pow (k + 2) 2 (by decide))
  simp only [List.append_assoc, ← List.replicate_succ'] at h_app
  rw [h_pos] at h_app
  exact h_app

lemma SweepSteps_append_odd_iter {t : ℕ} (P : List ℕ) (k : ℕ) {Q Q' : List ℕ}
    (hk : 1 ≤ k) (hQ : SweepSteps t Q Q')
    (hOdd : ∀ s < t, (stepBlock^[s] P).length % 2 = 1) :
    SweepSteps t (fromQ P ++ (3 * k + 2) :: Q)
      (fromQ (stepBlock^[t] P) ++ (3 * (k + t) + 2) :: Q') := by
  induction hQ generalizing P k with
  | zero _ =>
    simp only [Function.iterate_zero, id_eq, Nat.add_zero]
    exact SweepSteps.zero _
  | @succ t' X Y Z h1 _ ih =>
    have hP0 : P.length % 2 = 1 := hOdd 0 (Nat.zero_lt_succ t')
    refine SweepSteps.succ (SweepRel.append_odd P k X Y hP0 hk h1) ?_
    have h_rec := ih (stepBlock P) (k + 1) (by omega) (fun s hs => by
      have h_it := hOdd (s + 1) (Nat.succ_lt_succ hs)
      rwa [Function.iterate_succ_apply] at h_it)
    have h_add : k + 1 + t' = k + (t' + 1) := by omega
    rwa [← Function.iterate_succ_apply stepBlock t' P, h_add] at h_rec

theorem tail_era_induction (k : ℕ) :
    SweepSteps (2 ^ (k + 1)) (fromQ [1]) (fromQ (BSeq k ++ [1])) ∧
    SweepSteps (mSteps (k + 2)) (fromQ [1]) (fromQ (ESeq k ++ [1])) ∧
    (∃ C, SweepSteps (mSteps (k + 1) - 1) (fromQ [1]) (fromQ (C ++ [1]))) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have h_df : ∃ C, SweepSteps (mSteps (k + 1) - 1) (fromQ [1]) (fromQ (C ++ [1])) := by
      rcases k with _ | _ | k'
      · exact ⟨[], SweepSteps.zero _⟩
      · exact ⟨[0, 0], SweepSteps.succ (SweepRel.single_end [] rfl) (SweepSteps.zero _)⟩
      · obtain ⟨hB_prev, _, _⟩ := ih (k' + 1) (by omega)
        obtain ⟨_, _, ⟨C₀, hC₀⟩⟩ := ih k' (by omega)
        have h_pos : 1 ≤ mSteps (k' + 1) := mSteps_pos k'
        have h_lt : mSteps (k' + 1) - 1 < 2 ^ (k' + 1) - 1 := by
          have := mSteps_lt_pow (k' + 1); omega
        have h_prep := SweepSteps_prepend_even (BSeq (k' + 1)) hC₀ (fun s hs =>
          BSeq_even_succ k' s (Nat.lt_trans hs h_lt))
        rw [← fromQ_append, ← fromQ_append, ← List.append_assoc] at h_prep
        have h_tr := SweepSteps_trans hB_prev h_prep
        have h_steps : 2 ^ (k' + 2) + (mSteps (k' + 1) - 1) = mSteps (k' + 3) - 1 :=
          (Nat.add_sub_assoc h_pos (2 ^ (k' + 2))).symm
        rw [h_steps] at h_tr
        exact ⟨_, h_tr⟩
    rcases k with _ | k₀
    · have h1 : SweepRel (fromQ ([] ++ [1])) (fromQ (stepBlock [] ++ [0, 0, 1])) :=
        SweepRel.single_end [] rfl
      have h2 : SweepRel (fromQ ([0, 0] ++ [1])) (fromQ (stepBlock [0, 0] ++ [0, 0, 1])) :=
        SweepRel.single_end [0, 0] rfl
      have h_two : SweepSteps 2 (fromQ [1]) (fromQ (BSeq 0 ++ [1])) :=
        SweepSteps.succ h1 (SweepSteps.succ h2 (SweepSteps.zero _))
      exact ⟨h_two, h_two, h_df⟩
    · obtain ⟨_, hE_prev, h_df_prev⟩ := ih k₀ (by omega)
      obtain ⟨C, hC⟩ := h_df_prev
      have h_pos : 1 ≤ mSteps (k₀ + 1) := mSteps_pos k₀
      have h_pair := SweepRel.pair_end (ESeq k₀) (ESeq_odd_lt k₀ 0 h_pos)
      have h_iter := SweepSteps_append_odd_iter (stepBlock (ESeq k₀)) 1 (le_refl 1) hC
        (fun s hs => by
          have h_lt : s + 1 < mSteps (k₀ + 1) := by omega
          have h_od := ESeq_odd_lt k₀ (s + 1) h_lt
          rwa [Function.iterate_succ_apply] at h_od)
      have h_idx1 : 1 + (mSteps (k₀ + 1) - 1) = mSteps (k₀ + 1) := by omega
      have h_idx2 : (mSteps (k₀ + 1) - 1).succ = mSteps (k₀ + 1) := by omega
      rw [← Function.iterate_succ_apply stepBlock (mSteps (k₀ + 1) - 1) (ESeq k₀),
        h_idx1, h_idx2] at h_iter
      have h_two := SweepRel.two_end (stepBlock^[mSteps (k₀ + 1)] (ESeq k₀))
        (mSteps (k₀ + 1)) C (ESeq_even_at k₀)
      have h_sumQ := SweepSteps_sumQ1 hC
      have h_zeros : mSteps (k₀ + 1) + 2 + sumQ1 (C ++ [1]) = 3 * mSteps (k₀ + 1) + 2 := by omega
      rw [h_zeros, ← Function.iterate_succ_apply' stepBlock (mSteps (k₀ + 1)) (ESeq k₀),
        ESeq_to_next_BSeq k₀] at h_two
      have h_phase2 : SweepSteps (mSteps (k₀ + 1) + 1)
          (fromQ (ESeq k₀ ++ [1])) (fromQ (BSeq (k₀ + 1) ++ [1])) := by
        have h_tail := SweepSteps_trans h_iter (SweepSteps.succ h_two (SweepSteps.zero _))
        have h_full := SweepSteps.succ h_pair h_tail
        have h_cnt : (mSteps (k₀ + 1) - 1) + 1 + 1 = mSteps (k₀ + 1) + 1 := by omega
        rwa [h_cnt] at h_full
      have hB_curr : SweepSteps (2 ^ (k₀ + 2)) (fromQ [1]) (fromQ (BSeq (k₀ + 1) ++ [1])) := by
        have h_tr := SweepSteps_trans hE_prev h_phase2
        have h_sum := mSteps_sum k₀
        have h_cnt : mSteps (k₀ + 2) + (mSteps (k₀ + 1) + 1) = 2 ^ (k₀ + 2) := by
          change 2 ^ (k₀ + 1) + mSteps k₀ + (mSteps (k₀ + 1) + 1) = 2 ^ (k₀ + 2)
          have h_p : 1 ≤ 2 ^ (k₀ + 1) := Nat.one_le_pow (k₀ + 1) 2 (by decide)
          rw [pow_two_succ (k₀ + 1)]; omega
        rwa [h_cnt] at h_tr
      have hE_curr : SweepSteps (mSteps (k₀ + 3)) (fromQ [1]) (fromQ (ESeq (k₀ + 1) ++ [1])) := by
        cases k₀ with
        | zero =>
          have h_step1 := SweepRel.single_end (BSeq 1) rfl
          have h_tr := SweepSteps_trans hB_curr (SweepSteps.succ h_step1 (SweepSteps.zero _))
          simpa [ESeq, mSteps, List.append_assoc] using h_tr
        | succ k' =>
          obtain ⟨_, hE_k', _⟩ := ih k' (by omega)
          have h_prep := SweepSteps_prepend_even (BSeq (k' + 2)) hE_k' (BSeq_even_mSteps (k' + 2))
          rw [← fromQ_append, ← fromQ_append, ← List.append_assoc] at h_prep
          have h_tr := SweepSteps_trans hB_curr h_prep
          exact h_tr
      exact ⟨hB_curr, hE_curr, h_df⟩

lemma reach_tail_two_mul_mSteps (k : ℕ) :
    ∃ C, SweepSteps (2 * mSteps (k + 1)) (fromQ [1]) (fromQ (C ++ [1])) := by
  have h_eq := two_mul_mSteps k
  rcases (by omega : k % 2 = 0 ∨ ¬(k % 2 = 0)) with hev | hod
  · rw [hev, if_pos rfl] at h_eq
    rw [h_eq]
    exact ⟨ESeq k, (tail_era_induction k).2.1⟩
  · rw [if_neg hod] at h_eq
    rw [h_eq]
    exact (tail_era_induction (k + 1)).2.2

lemma top_ESeq_to_next_BSeq (k : ℕ) :
    SweepSteps (2 * mSteps (k + 1) + 2)
      (fromQ (phi (ESeq k) ++ [1])) (fromQ (phi (BSeq (k + 1)) ++ [1])) := by
  set L := mSteps (k + 1)
  obtain ⟨h_odd, h_even, h_end⟩ := stepBlock_iterate_phi L (ESeq k) (ESeq_odd_lt k) (ESeq_even_at k)
  obtain ⟨C, hC⟩ := reach_tail_two_mul_mSteps k
  have h_pair := SweepRel.pair_end (phi (ESeq k)) (phi_length_odd (ESeq k))
  have h_iter := SweepSteps_append_odd_iter (stepBlock (phi (ESeq k))) 1 (le_refl 1) hC
    (fun s hs => by
      have h_it := h_odd (s + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h_it)
  rw [← Function.iterate_succ_apply stepBlock (2 * L) (phi (ESeq k)),
    Nat.add_comm 1 (2 * L)] at h_iter
  have h_two := SweepRel.two_end (stepBlock^[2 * L + 1] (phi (ESeq k))) (2 * L + 1) C h_even
  have h_sumQ := SweepSteps_sumQ1 hC
  have h_zeros : (2 * L + 1) + 2 + sumQ1 (C ++ [1]) = 2 * (3 * L + 2) + 1 := by omega
  rw [h_zeros, ← Function.iterate_succ_apply' stepBlock (2 * L + 1) (phi (ESeq k)),
    h_end, ← phi_replicate_zero (3 * L + 2), ← phi_append, ESeq_to_next_BSeq k] at h_two
  have h_tail := SweepSteps_trans h_iter (SweepSteps.succ h_two (SweepSteps.zero _))
  exact SweepSteps.succ h_pair h_tail

lemma top_zero_to_phi_00 :
    SweepSteps 2 (fromQ [0, 1]) (fromQ (phi [0, 0] ++ [1])) := by
  have h1 : SweepRel (fromQ ([0] ++ [1])) (fromQ (stepBlock [0]) ++ [5, 3]) :=
    SweepRel.pair_end [0] rfl
  have h2 : SweepRel (fromQ [] ++ (3 * 1 + 2) :: fromQ ([] ++ [1]))
      (fromQ (stepBlock [] ++ List.replicate (1 + 2 + sumQ1 ([] ++ [1])) 0 ++ [1])) :=
    SweepRel.two_end [] 1 [] rfl
  exact SweepSteps.succ h1 (SweepSteps.succ h2 (SweepSteps.zero _))

lemma top_phi_00_to_ESeq0 :
    SweepSteps 2 (fromQ (phi [0, 0] ++ [1])) (fromQ (phi (ESeq 0) ++ [1])) := by
  have h1 : SweepRel (fromQ (phi [0, 0] ++ [1])) (fromQ (stepBlock (phi [0, 0])) ++ [5, 3]) :=
    SweepRel.pair_end (phi [0, 0]) rfl
  have h2 : SweepRel (fromQ [1, 1] ++ (3 * 1 + 2) :: fromQ ([] ++ [1]))
      (fromQ (stepBlock [1, 1] ++ List.replicate (1 + 2 + sumQ1 ([] ++ [1])) 0 ++ [1])) :=
    SweepRel.two_end [1, 1] 1 [] rfl
  exact SweepSteps.succ h1 (SweepSteps.succ h2 (SweepSteps.zero _))

lemma top_BSeq_to_ESeq (k : ℕ)
    (h_prev : ∀ k' < k, SweepSteps (2 * mSteps (k' + 2)) (fromQ [0, 1]) (fromQ (phi (ESeq k') ++ [1]))) :
    SweepSteps (2 * mSteps (k + 1))
      (fromQ (phi (BSeq (k + 1)) ++ [1])) (fromQ (phi (ESeq (k + 1)) ++ [1])) := by
  have h_start : fromQ (phi (BSeq (k + 1)) ++ [1]) = fromQ (psi (BSeq (k + 1))) ++ fromQ [0, 1] := by
    unfold phi
    simp [fromQ_append, List.append_assoc]
  rw [h_start]
  cases k with
  | zero =>
    have h_psi := stepBlock_iterate_psi 1 (BSeq 1) (BSeq_even_mSteps 1)
    have h_prep := SweepSteps_prepend_even (psi (BSeq 1)) top_zero_to_phi_00 h_psi.1
    rw [h_psi.2, ← fromQ_append (psi (stepBlock^[1] (BSeq 1))), ← List.append_assoc,
      ← phi_append] at h_prep
    exact h_prep
  | succ k' =>
    have h_psi := stepBlock_iterate_psi (mSteps (k' + 2)) (BSeq (k' + 2)) (BSeq_even_mSteps (k' + 2))
    have h_sub := h_prev k' (Nat.lt_succ_self k')
    have h_prep := SweepSteps_prepend_even (psi (BSeq (k' + 2))) h_sub h_psi.1
    rw [h_psi.2, ← fromQ_append (psi (stepBlock^[mSteps (k' + 2)] (BSeq (k' + 2)))),
      ← List.append_assoc, ← phi_append] at h_prep
    exact h_prep

theorem top_era_reach (k : ℕ) :
    SweepSteps (2 * mSteps (k + 2)) (fromQ [0, 1]) (fromQ (phi (ESeq k) ++ [1])) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero =>
      exact SweepSteps_trans top_zero_to_phi_00 top_phi_00_to_ESeq0
    | succ k₀ =>
      have h_prev := ih k₀ (Nat.lt_succ_self k₀)
      have h_to_B := top_ESeq_to_next_BSeq k₀
      have h_to_E := top_BSeq_to_ESeq k₀ (fun k' hk' => ih k' (Nat.lt_trans hk' (Nat.lt_succ_self k₀)))
      have h_tr := SweepSteps_trans h_prev (SweepSteps_trans h_to_B h_to_E)
      have h_sum := mSteps_sum k₀
      have h_cnt : 2 * mSteps (k₀ + 2) + ((2 * mSteps (k₀ + 1) + 2) + 2 * mSteps (k₀ + 1)) =
          2 * mSteps (k₀ + 3) := by
        change 2 * (2 ^ (k₀ + 1) + mSteps k₀) + ((2 * mSteps (k₀ + 1) + 2) + 2 * mSteps (k₀ + 1)) =
          2 * (2 ^ (k₀ + 2) + mSteps (k₀ + 1))
        have h_p : 1 ≤ 2 ^ (k₀ + 1) := Nat.one_le_pow (k₀ + 1) 2 (by decide)
        rw [pow_two_succ (k₀ + 1)]; omega
      rwa [h_cnt] at h_tr

theorem top_era_step (k : ℕ) :
    (evalB (fromQ (phi (ESeq k) ++ [1]))) [target_tm]⊢⁺ (evalB (fromQ (phi (ESeq (k + 1)) ++ [1]))) := by
  have h_to_B := top_ESeq_to_next_BSeq k
  have h_to_E := top_BSeq_to_ESeq k (fun k' _ => top_era_reach k')
  have h_tr := SweepSteps_trans h_to_B h_to_E
  have h_cnt : (2 * mSteps (k + 1) + 2) + 2 * mSteps (k + 1) =
      (4 * mSteps (k + 1) + 1) + 1 := by omega
  rw [h_cnt] at h_tr
  exact SweepSteps_sound_plus h_tr

theorem init_reaches_fromQ_01 :
    (init []) [target_tm]⊢⁺ (evalB (fromQ [0, 1])) := by
  refine stepPlus_trans init_to_cfg_BR ?_
  have h1 := rule_BR_zero [] []
  dsimp [tailWeight, headWeight, List.tail] at h1
  refine stepPlus_trans h1 ?_
  refine stepPlus_trans (rule_BR_nil [3]) ?_
  refine stepPlus_trans (rule_ER_ge3 0 [0] []) ?_
  have h_er0 : cfg_ER [1, 0] [0] = cfg_ER [1, 0] [] := by simp [cfg_ER, encRight1]
  rw [h_er0]
  refine stepPlus_trans (rule_ER_nil [1, 0]) ?_
  exact br_sweep [0]

def EraInv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ k : ℕ, cfg = evalB (fromQ (phi (ESeq k) ++ [1]))

lemma era_inv_init : ∃ cfg₀, ((init []) [target_tm]⊢* cfg₀) ∧ EraInv cfg₀ := by
  have h1 := init_reaches_fromQ_01
  have h2 := SweepSteps_sound_plus (top_era_reach 0)
  exact ⟨_, stepPlus_stepStar (stepPlus_trans h1 h2), ⟨0, rfl⟩⟩

lemma era_inv_step (cfg : Cfg (Fin 2) (Fin 6)) (hinv : EraInv cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧ EraInv cfg' := by
  obtain ⟨k, rfl⟩ := hinv
  exact ⟨_, top_era_step k, ⟨k + 1, rfl⟩⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  closed_inv_does_not_halt target_tm EraInv era_inv_init era_inv_step

end BusyBeaver.M_1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_HHH1RD
