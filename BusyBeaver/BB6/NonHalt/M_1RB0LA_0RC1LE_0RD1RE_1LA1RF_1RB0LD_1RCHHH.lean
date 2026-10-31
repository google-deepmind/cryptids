/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
-- ============================================================================
-- Section 2: Turing Machine Infrastructure & Notations
-- ============================================================================


/- A Turing machine statement writing a symbol and moving in direction `dir`. -/
-- ============================================================================
-- Section 5: Specific Turing Machine: holdout_0010
-- ============================================================================
/- Transition function for holdout_0010: `1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---` -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

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

lemma list_pow_append_one (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := list_pow_add_comm u k 1
  dsimp -failIfUnchanged [HPow.hPow, list_nat_repeat] at h ⊢
  rw [List.append_nil] at h
  exact h

lemma cons_eq_singleton_append (x : Fin 2) (r : ListBlank (Fin 2)) :
    x >> r = [x] +> r := rfl

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

lemma pow_succ_append_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

lemma pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

lemma pow_succ_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m : Nat) :
    (s <+ (u ^ m)) <+ u = s <+ (u ^ (m + 1)) := by
  rw [listblank_append_append, ← pow_succ_list]

lemma multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (stepPlus_stepStar h₂)

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

/-- Universal non-halting principle from an infinite `⊢⁺` chain. -/
theorem nonhalt_of_chain {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Nat → Cfg Γ Λ)
    (h0 : (init []) [M]⊢* c 0)
    (hstep : ∀ k, (c k) [M]⊢⁺ c (k + 1)) :
    IsDoesNotHalt M := by
  have hreach : ∀ k, ∃ m ≥ k, multiStep M (init []) m = some (c k) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨m, hm⟩ := h0
      exact ⟨m, Nat.zero_le m, hm⟩
    | succ k ih =>
      obtain ⟨m, hge, hm⟩ := ih
      obtain ⟨d, hd_pos, hd⟩ := hstep k
      refine ⟨m + d, by omega, multiStep_trans M (init []) (c k) (c (k + 1)) m d hm hd⟩
  intro cfg ⟨n, hn⟩
  rw [Option.isSome_iff_ne_none]
  intro hnone
  obtain ⟨m, hge, hm⟩ := hreach (n + 1)
  have hm_eq : m = n + (1 + (m - n - 1)) := by omega
  rw [hm_eq, multiStep_add M (init []) n (1 + (m - n - 1)), hn] at hm
  simp only [Option.bind] at hm
  rw [multiStep_add M cfg 1 (m - n - 1), multiStep_one, hnone] at hm
  simp only [Option.bind] at hm
  cases hm

-- ============================================================================
-- Section 6: Row9 Evaluator (`Row9Eval.v`)
-- ============================================================================

namespace Row9

abbrev word := List Nat
abbrev result := Option word

def bind_res (r : result) (h : word → result) : result :=
  match r with
  | none => none
  | some W => h W

def first_plus (k : Nat) (W : word) : word :=
  match W with
  | [] => []
  | a :: U => (a + k) :: U

def lift_plus (k : Nat) (r : result) : result :=
  Option.map (first_plus k) r

def lift_prefix (U : word) (r : result) : result :=
  Option.map (U ++ ·) r

inductive Eval : word → result → Prop where
  | nil : Eval [] (some [1])
  | one {U r} : Eval U r → Eval (1 :: U) (lift_plus 4 r)
  | two {U r} : Eval U r → Eval (2 :: U) (lift_prefix [2] r)
  | three_halt {U} : Eval U none → Eval (3 :: U) none
  | three {U V r} : Eval U (some V) → Eval V r → Eval (3 :: U) (lift_prefix [3] r)
  | large (g : Nat) (U : word) : Eval ((g + 4) :: U) (some (1 :: g :: U))
  | zero : Eval [0] (some [2, 2])
  | zero_zero (U : word) : Eval (0 :: 0 :: U) none
  | zero_one {U r} : Eval U r → Eval (0 :: 1 :: U) (lift_prefix [2] (lift_plus 2 r))
  | zero_two {U r} : Eval U r → Eval (0 :: 2 :: U) (lift_prefix [2, 0] r)
  | zero_large (g : Nat) {U r} : Eval (g :: U) r → Eval (0 :: (g + 3) :: U) (lift_prefix [2] (lift_plus 1 r))

def label_weight (a : Nat) : Nat := (a + 3) % 4

def Pplus : word → Nat
  | [] => 0
  | a :: U => label_weight a + Pplus U

def positive_head (W : word) : Prop :=
  ∃ a U, W = a :: U ∧ 0 < a ∧ a % 4 ≠ 0

lemma label_weight_period (a : Nat) : label_weight (a + 4) = label_weight a := by
  unfold label_weight; omega

lemma label_weight_bound (a : Nat) : label_weight a < 4 := by
  unfold label_weight; omega

lemma label_weight_shift (a k : Nat) : label_weight (a + k) ≤ label_weight a + k := by
  unfold label_weight; omega

lemma label_weight_back_three (a : Nat) : label_weight a ≤ label_weight (a + 3) + 1 := by
  unfold label_weight; omega

lemma Pplus_first_plus_four (W : word) : Pplus (first_plus 4 W) = Pplus W := by
  cases W with
  | nil => rfl
  | cons a U => simp [first_plus, Pplus, label_weight_period]

lemma Pplus_first_plus_bound (W : word) (k : Nat) : Pplus (first_plus k W) ≤ Pplus W + k := by
  cases W with
  | nil => simp [first_plus, Pplus]
  | cons a U =>
    simp only [first_plus, Pplus]
    have h := label_weight_shift a k
    (try omega)
lemma positive_head_plus_four {W : word} (h : positive_head W) : positive_head (first_plus 4 W) := by
  rcases h with ⟨a, U, rfl, ha, hmod⟩
  refine ⟨a + 4, U, rfl, by omega, by omega⟩

theorem Eval_deterministic {W : word} {r : result} (E : Eval W r) :
    ∀ {s : result}, Eval W s → r = s := by
  induction E with
  | nil => intro s E'; cases E'; rfl
  | one h ih =>
    intro s E'; cases E' with
    | one h' => rw [ih h']
  | two h ih =>
    intro s E'; cases E' with
    | two h' => rw [ih h']
  | three_halt h ih =>
    intro s E'; cases E' with
    | three_halt h' => rfl
    | three h1 _ => have := ih h1; contradiction
  | three h1 h2 ih1 ih2 =>
    intro s E'; cases E' with
    | three_halt h' => have := ih1 h'; contradiction
    | three h1' h2' =>
      have hv := Option.some.inj (ih1 h1')
      subst hv
      rw [ih2 h2']
  | large g U =>
    intro s E'; cases E'; rfl
  | zero =>
    intro s E'; cases E'; rfl
  | zero_zero U =>
    intro s E'; cases E'; rfl
  | zero_one h ih =>
    intro s E'; cases E' with
    | zero_one h' => rw [ih h']
  | zero_two h ih =>
    intro s E'; cases E' with
    | zero_two h' => rw [ih h']
  | zero_large g h ih =>
    intro s E'; cases E' with
    | zero_large _ h' => rw [ih h']

theorem Eval_success_properties {W : word} {r : result} (E : Eval W r) :
    ∀ {V : word}, r = some V → positive_head V ∧ Pplus V ≤ Pplus W := by
  induction E with
  | nil =>
    intro V hV; injection hV with hV; subst hV
    exact ⟨⟨1, [], rfl, by decide, by decide⟩, by decide⟩
  | one h ih =>
    rename_i U r'
    intro V hV
    rcases r' with _ | V'
    · cases hV
    · simp only [lift_plus, Option.map] at hV
      injection hV with hV; subst hV
      obtain ⟨hpos, hp⟩ := ih rfl
      refine ⟨positive_head_plus_four hpos, ?_⟩
      rw [Pplus_first_plus_four]
      simp only [Pplus, label_weight]
      (try omega)
  | two h ih =>
    rename_i U r'
    intro V hV
    rcases r' with _ | V'
    · cases hV
    · simp only [lift_prefix, Option.map, List.singleton_append] at hV
      injection hV with hV; subst hV
      obtain ⟨_, hp⟩ := ih rfl
      refine ⟨⟨2, V', rfl, by decide, by decide⟩, ?_⟩
      simp only [Pplus, label_weight]; omega
  | three_halt _ =>
    intro V hV; cases hV
  | three h1 h2 ih1 ih2 =>
    rename_i U V1 r'
    intro V hV
    rcases r' with _ | V2
    · cases hV
    · simp only [lift_prefix, Option.map, List.singleton_append] at hV
      injection hV with hV; subst hV
      obtain ⟨_, hp1⟩ := ih1 rfl
      obtain ⟨_, hp2⟩ := ih2 rfl
      refine ⟨⟨3, V2, rfl, by decide, by decide⟩, ?_⟩
      simp only [Pplus, label_weight]; omega
  | large g U =>
    intro V hV; injection hV with hV; subst hV
    refine ⟨⟨1, g :: U, rfl, by decide, by decide⟩, ?_⟩
    simp only [Pplus, label_weight_period, label_weight]; omega
  | zero =>
    intro V hV; injection hV with hV; subst hV
    exact ⟨⟨2, [2], rfl, by decide, by decide⟩, by decide⟩
  | zero_zero _ =>
    intro V hV; cases hV
  | zero_one h ih =>
    rename_i U r'
    intro V hV
    rcases r' with _ | V'
    · cases hV
    · simp only [lift_prefix, lift_plus, Option.map, List.singleton_append] at hV
      injection hV with hV; subst hV
      obtain ⟨_, hp⟩ := ih rfl
      refine ⟨⟨2, first_plus 2 V', rfl, by decide, by decide⟩, ?_⟩
      simp only [Pplus, label_weight]
      have hb := Pplus_first_plus_bound V' 2
      (try omega)
  | zero_two h ih =>
    rename_i U r'
    intro V hV
    rcases r' with _ | V'
    · cases hV
    · simp only [lift_prefix, Option.map] at hV
      injection hV with hV; subst hV
      obtain ⟨_, hp⟩ := ih rfl
      refine ⟨⟨2, 0 :: V', rfl, by decide, by decide⟩, ?_⟩
      simp only [Pplus, label_weight, List.cons_append, List.nil_append]; omega
  | zero_large g h ih =>
    rename_i U r'
    intro V hV
    rcases r' with _ | V'
    · cases hV
    · simp only [lift_prefix, lift_plus, Option.map, List.singleton_append] at hV
      injection hV with hV; subst hV
      obtain ⟨_, hp⟩ := ih rfl
      refine ⟨⟨2, first_plus 1 V', rfl, by decide, by decide⟩, ?_⟩
      simp only [Pplus, label_weight] at hp ⊢
      have hb1 := Pplus_first_plus_bound V' 1
      (try omega)
theorem Eval_exists_aux (p : Nat) :
    ∀ (n : Nat) (W : word), Pplus W = p → W.length = n → ∃ r, Eval W r := by
  induction p using Nat.strongRecOn with
  | ind p ihp =>
    intro n
    induction n using Nat.strongRecOn with
    | ind n ihn =>
      intro W hp hn
      rcases W with _ | ⟨a, U⟩
      · exact ⟨some [1], .nil⟩
      · rcases a with _ | _ | _ | _ | g
        · rcases U with _ | ⟨b, U'⟩
          · exact ⟨some [2, 2], .zero⟩
          · rcases b with _ | _ | _ | g'
            · exact ⟨none, .zero_zero U'⟩
            · have hlt : Pplus U' < p := by
                subst hp; simp only [Pplus, label_weight]; omega
              obtain ⟨r, hr⟩ := ihp (Pplus U') hlt U'.length U' rfl rfl
              exact ⟨lift_prefix [2] (lift_plus 2 r), .zero_one hr⟩
            · have hlt : Pplus U' < p := by
                subst hp; simp only [Pplus, label_weight]; omega
              obtain ⟨r, hr⟩ := ihp (Pplus U') hlt U'.length U' rfl rfl
              exact ⟨lift_prefix [2, 0] r, .zero_two hr⟩
            · have hlt : Pplus (g' :: U') < p := by
                subst hp; simp only [Pplus, label_weight]; omega
              obtain ⟨r, hr⟩ := ihp (Pplus (g' :: U')) hlt (g' :: U').length (g' :: U') rfl rfl
              exact ⟨lift_prefix [2] (lift_plus 1 r), .zero_large g' hr⟩
        · have hp' : Pplus U = p := by
            subst hp; simp [Pplus, label_weight]
          have hn' : U.length < n := by
            subst hn; simp
          obtain ⟨r, hr⟩ := ihn U.length hn' U hp' rfl
          exact ⟨lift_plus 4 r, .one hr⟩
        · have hlt : Pplus U < p := by
            subst hp; simp only [Pplus, label_weight]; omega
          obtain ⟨r, hr⟩ := ihp (Pplus U) hlt U.length U rfl rfl
          exact ⟨lift_prefix [2] r, .two hr⟩
        · have hlt : Pplus U < p := by
            subst hp; simp only [Pplus, label_weight]; omega
          obtain ⟨r1, hr1⟩ := ihp (Pplus U) hlt U.length U rfl rfl
          rcases r1 with _ | V
          · exact ⟨none, .three_halt hr1⟩
          · have hV : Pplus V ≤ Pplus U := (Eval_success_properties hr1 rfl).2
            have hltV : Pplus V < p := by omega
            obtain ⟨r2, hr2⟩ := ihp (Pplus V) hltV V.length V rfl rfl
            exact ⟨lift_prefix [3] r2, .three hr1 hr2⟩
        · exact ⟨some (1 :: g :: U), .large g U⟩

theorem Eval_exists (W : word) : ∃ r, Eval W r :=
  Eval_exists_aux (Pplus W) W.length W rfl rfl

noncomputable def f (W : word) : result :=
  Classical.choose (Eval_exists W)

theorem f_spec (W : word) : Eval W (f W) :=
  Classical.choose_spec (Eval_exists W)


theorem Eval_iff_f {W : word} {r : result} : Eval W r ↔ f W = r :=
  ⟨fun h => Eval_deterministic (f_spec W) h, fun h => h ▸ f_spec W⟩

theorem f_nil : f [] = some [1] := Eval_iff_f.mp .nil
theorem f_one (U : word) : f (1 :: U) = lift_plus 4 (f U) := Eval_iff_f.mp (.one (f_spec U))
theorem f_two (U : word) : f (2 :: U) = lift_prefix [2] (f U) := Eval_iff_f.mp (.two (f_spec U))
theorem f_three (U : word) : f (3 :: U) = lift_prefix [3] (bind_res (f U) f) := by
  apply Eval_iff_f.mp
  have h := f_spec U
  rcases hU : f U with _ | V
  · rw [hU] at h; exact .three_halt h
  · rw [hU] at h; exact .three h (f_spec V)
theorem f_large (g : Nat) (U : word) : f ((g + 4) :: U) = some (1 :: g :: U) := Eval_iff_f.mp (.large g U)
theorem f_zero : f [0] = some [2, 2] := Eval_iff_f.mp .zero
theorem f_zero_zero (U : word) : f (0 :: 0 :: U) = none := Eval_iff_f.mp (.zero_zero U)
theorem f_zero_one (U : word) : f (0 :: 1 :: U) = lift_prefix [2] (lift_plus 2 (f U)) := Eval_iff_f.mp (.zero_one (f_spec U))
theorem f_zero_two (U : word) : f (0 :: 2 :: U) = lift_prefix [2, 0] (f U) := Eval_iff_f.mp (.zero_two (f_spec U))
theorem f_zero_large (g : Nat) (U : word) : f (0 :: (g + 3) :: U) = lift_prefix [2] (lift_plus 1 (f (g :: U))) :=
  Eval_iff_f.mp (.zero_large g (f_spec (g :: U)))

theorem f_success_nonempty {W V : word} (h : f W = some V) : V ≠ [] := by
  have he := Eval_iff_f.mpr h
  obtain ⟨⟨a, U, rfl, _, _⟩, _⟩ := Eval_success_properties he rfl
  intro hnil; cases hnil

-- ============================================================================
-- Section 7: Abstract Clock Algebra & Operators (`Row9Algebra.v` + `Row9Operators.v`)
-- ============================================================================

def power {α : Type*} (fn : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => fn (power fn n x)

lemma power_add {α : Type*} (fn : α → α) (a b : Nat) (x : α) :
    power fn (a + b) x = power fn a (power fn b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => simp only [Nat.succ_add, power, ih]

lemma power_succ_r {α : Type*} (fn : α → α) (a : Nat) (x : α) :
    power fn (a + 1) x = power fn a (fn x) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change fn (power fn (a + 1) x) = fn (power fn a (fn x))
    rw [ih]

lemma power_commute {α : Type*} (fn gn : α → α) (h : ∀ x, fn (gn x) = gn (fn x)) (n : Nat) (x : α) :
    power fn n (gn x) = gn (power fn n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, ih, h]

lemma power_ext {α : Type*} (fn gn : α → α) (h : ∀ x, fn x = gn x) (n : Nat) (x : α) :
    power fn n x = power gn n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, ih, h]

lemma power_mul {α : Type*} (fn : α → α) (a b : Nat) (x : α) :
    power fn (a * b) x = power (fun y => power fn b y) a x := by
  induction a with
  | zero => rw [Nat.zero_mul]; rfl
  | succ a ih => rw [Nat.succ_mul, Nat.add_comm _ b, power_add, ih]; rfl

lemma power_strict {α : Type*} (fn : Option α → Option α) (h : fn none = none) (n : Nat) :
    power fn n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, ih, h]

lemma power_halt_mono {α : Type*} (fn : Option α → Option α) (h : fn none = none)
    {a b : Nat} {x : Option α} (hab : a ≤ b) (ha : power fn a x = none) :
    power fn b x = none := by
  have hb : b = (b - a) + a := by omega
  rw [hb, power_add, ha, power_strict fn h]

lemma power_injective_none {α : Type*} (fn : Option α → Option α)
    (h : ∀ x, fn x = none ↔ x = none) (n : Nat) (x : Option α) :
    power fn n x = none ↔ x = none := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih => simp only [power, h, ih]

lemma power_product {α : Type*} (fn gn : α → α) (h : ∀ x, fn (gn x) = gn (fn x)) (n : Nat) (x : α) :
    power (fun y => fn (gn y)) n x = power fn n (power gn n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, ih, power_commute fn gn h]

def eventually {α : Type*} (fn : Option α → Option α) (x : Option α) : Prop :=
  ∃ k, power fn k x = none

lemma eventually_step {α : Type*} (fn : Option α → Option α) (h : fn none = none) (x : Option α) :
    eventually fn x ↔ eventually fn (fn x) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← power_succ_r]
    exact power_halt_mono fn h (Nat.le_succ k) hk
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [power_succ_r, hk]⟩

lemma eventually_rotate {α : Type*} (fn gn : Option α → Option α)
    (hf : fn none = none) (hg : gn none = none) (x : Option α) :
    eventually (fun y => fn (gn y)) x ↔ eventually (fun y => gn (fn y)) (gn x) := by
  have hC : ∀ k y, power (fun z => gn (fn z)) k (gn y) = gn (power (fun z => fn (gn z)) k y) := by
    intro k; induction k with
    | zero => intro y; rfl
    | succ k ih => intro y; simp only [power, ih]
  have hD : ∀ k y, power (fun z => fn (gn z)) k (fn y) = fn (power (fun z => gn (fn z)) k y) := by
    intro k; induction k with
    | zero => intro y; rfl
    | succ k ih => intro y; simp only [power, ih]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hC, hk, hg]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [power_succ_r, hD, hk, hf]⟩

noncomputable def opF (x : result) : result := bind_res x f
def pfx (d : Nat) (x : result) : result := Option.map (d :: ·) x
def Q : result → result := pfx 2
def Z : result → result := pfx 0
noncomputable def G (x : result) : result := Option.map List.tail (opF (Z x))
noncomputable def T (n : Nat) (x : result) : result := Z (power opF n x)
noncomputable def H (n : Nat) (x : result) : result := G (power opF n x)
def P (n : Nat) (x : result) : result := Z (power Q n x)
def K (n : Nat) (x : result) : Prop := eventually (H n) x

lemma opF_none : opF none = none := rfl
lemma G_none : G none = none := rfl

lemma pfx_none (d : Nat) (x : result) : pfx d x = none ↔ x = none := by
  cases x <;> simp [pfx]

lemma Q_none (x : result) : Q x = none ↔ x = none := pfx_none 2 x
lemma Z_none (x : result) : Z x = none ↔ x = none := pfx_none 0 x

lemma opF_Q (x : result) : opF (Q x) = Q (opF x) := by
  rcases x with _ | U; · rfl
  simp only [opF, Q, pfx, bind_res, Option.map, f_two]
  cases f U <;> rfl

lemma f_zero_head_eq (U : word) : f (0 :: U) = Q (Option.map List.tail (f (0 :: U))) := by
  rcases U with _ | ⟨a, U'⟩
  · rw [f_zero]; rfl
  · rcases a with _ | _ | _ | a'
    · rw [f_zero_zero]; rfl
    · rw [f_zero_one]; cases f U' <;> rfl
    · rw [f_zero_two]; cases f U' <;> rfl
    · rw [f_zero_large]; cases f (a' :: U') <;> rfl

lemma opF_Z (x : result) : opF (Z x) = Q (G x) := by
  rcases x with _ | U; · rfl
  exact f_zero_head_eq U

lemma G_Q (x : result) : G (Q x) = Z (opF x) := by
  rcases x with _ | U; · rfl
  simp only [G, opF, Z, Q, pfx, bind_res, Option.map, f_zero_two]
  cases f U <;> rfl

lemma G_nine (U : word) : G (some (9 :: U)) = some (2 :: 2 :: U) := by
  unfold G opF Z pfx bind_res
  simp only [Option.map]
  have h9 : (9 : Nat) = 6 + 3 := rfl
  rw [h9, f_zero_large]
  have h6 : (6 : Nat) = 2 + 4 := rfl
  rw [h6, f_large]
  rfl

lemma opF_three (x : result) : opF (pfx 3 x) = pfx 3 (opF (opF x)) := by
  rcases x with _ | U; · rfl
  simp only [opF, pfx, bind_res, Option.map, f_three]
  cases f U <;> rfl

lemma G_three (x : result) : G (pfx 3 x) = pfx 3 (G x) := by
  rcases x with _ | U; · rfl
  unfold G opF Z pfx bind_res
  simp only [Option.map]
  have h3 : (3 : Nat) = 0 + 3 := rfl
  rw [h3, f_zero_large]
  have hfz := f_zero_head_eq U
  rcases hfu : f (0 :: U) with _ | V
  · rfl
  · rw [hfu] at hfz
    rcases V with _ | ⟨a, V'⟩
    · cases hfz
    · simp only [Q, pfx, Option.map] at hfz
      injection hfz with hfz
      injection hfz with ha _
      subst ha
      rfl

lemma opF_power_Q (n : Nat) (x : result) : power opF n (Q x) = Q (power opF n x) :=
  power_commute opF Q opF_Q n x

lemma opF_power_Z (n : Nat) (x : result) : power opF (n + 1) (Z x) = Q (power opF n (G x)) := by
  rw [power_succ_r, opF_Z, opF_power_Q]

lemma H_Q (n : Nat) (x : result) : H n (Q x) = T n (opF x) := by
  unfold H T
  rw [opF_power_Q, G_Q, ← power_succ_r]
  rfl

lemma H_T (n : Nat) (x : result) (hn : 1 ≤ n) : H n (T n x) = T n (H n x) := by
  rcases n with _ | m; · omega
  unfold H T
  rw [opF_power_Z, G_Q]
  rfl

lemma H_strict (n : Nat) : H n none = none := by
  unfold H; rw [power_strict opF opF_none]; rfl

lemma T_strict (n : Nat) : T n none = none := by
  unfold T; rw [power_strict opF opF_none]; rfl

lemma P_none (n : Nat) (x : result) : P n x = none ↔ x = none := by
  unfold P; rw [Z_none]; exact power_injective_none Q Q_none n x

lemma opF_Q_power (k : Nat) (x : result) : opF (power Q k x) = power Q k (opF x) :=
  (power_commute Q opF (fun y => (opF_Q y).symm) k x).symm

lemma transport (j : Nat) :
    ∀ (l : Nat) (x : result),
      power opF j (Z (power Q (j + l) x)) = power Q j (Z (power Q l (power opF j x))) := by
  induction j with
  | zero => intro l x; rw [Nat.zero_add]; rfl
  | succ j ih =>
    intro l x
    rw [Nat.succ_add]
    change power opF (j + 1) (Z (Q (power Q (j + l) x))) = Q (power Q j (Z (power Q l (power opF (j + 1) x))))
    rw [opF_power_Z, G_Q, opF_Q_power, ih, ← power_succ_r]

lemma H_P (n : Nat) (x : result) (hn : 1 ≤ n) : H n (P n x) = P n (H n x) := by
  unfold H P
  have htr := transport n 0 x
  rw [Nat.add_zero] at htr
  rw [htr]
  simp only [power]
  rcases n with _ | m; · omega
  simp only [power]
  rw [G_Q, opF_Q_power, opF_Z, power_commute Q Q (fun _ => rfl) m]

lemma bounded_factor (n : Nat) (hn : 1 ≤ n) (j : Nat) :
    ∀ (x : result), j ≤ n →
      power (T n) (j + 1) x = Z (power Q j (power opF (n - j) (power (H n) j x))) := by
  induction j with
  | zero =>
    intro x _; simp only [power, Nat.sub_zero]; rfl
  | succ j ih =>
    intro x hj
    rw [power_succ_r, ih (T n x) (by omega)]
    rw [power_commute (H n) (T n) (fun y => H_T n y hn)]
    unfold T
    have hsub : n - j = (n - (j + 1)) + 1 := by omega
    rw [hsub, opF_power_Z, ← power_succ_r]
    rfl

lemma T_factor (n : Nat) (x : result) (hn : 1 ≤ n) :
    power (T n) (n + 1) x = P n (power (H n) n x) := by
  rw [bounded_factor n hn n x (Nat.le_refl n)]
  unfold P
  rw [Nat.sub_self]
  rfl

lemma T_cofinal_factor (n k : Nat) (x : result) (hn : 1 ≤ n) :
    power (T n) (k * (n + 1)) x = power (P n) k (power (H n) (k * n) x) := by
  rw [power_mul, power_mul]
  rw [power_ext (fun y => power (T n) (n + 1) y) (fun y => P n (power (H n) n y)) (fun y => T_factor n y hn)]
  refine power_product (P n) (fun y => power (H n) n y) ?_ k x
  intro y
  exact (power_commute (H n) (P n) (fun z => H_P n z hn) n y).symm

theorem K_T_equiv (n : Nat) (x : result) (hn : 1 ≤ n) :
    eventually (T n) x ↔ K n x := by
  unfold K
  constructor
  · rintro ⟨k, hk⟩
    have hD : power (T n) (k * (n + 1)) x = none :=
      power_halt_mono (T n) (T_strict n) (by exact Nat.le_mul_of_pos_right k (by omega)) hk
    rw [T_cofinal_factor n k x hn] at hD
    have hH := (power_injective_none (P n) (P_none n) k _).mp hD
    exact ⟨k * n, hH⟩
  · rintro ⟨k, hk⟩
    refine ⟨k * (n + 1), ?_⟩
    rw [T_cofinal_factor n k x hn]
    have hD : power (H n) (k * n) x = none :=
      power_halt_mono (H n) (H_strict n) (by exact Nat.le_mul_of_pos_right k hn) hk
    rw [hD]
    exact power_strict (P n) ((P_none n none).mpr rfl) k

lemma H_Q_power (n k : Nat) (x : result) (hn : 1 ≤ n) :
    power (H n) (k + 1) (Q x) = T n (power (H n) k (opF x)) := by
  rw [power_succ_r, H_Q]
  exact power_commute (H n) (T n) (fun y => H_T n y hn) k (opF x)

lemma T_halt_G (n : Nat) (x : result) (h : T n x = none) : H n x = none := by
  unfold T H at *
  have hz := (Z_none _).mp h
  rw [hz]; rfl

theorem Q_index_nonincrease (n k : Nat) (x : result) (hn : 1 ≤ n)
    (h : power (H n) k (Q x) = none) : power (H n) k (opF x) = none := by
  rcases k with _ | k
  · simp only [power] at h ⊢
    rw [(Q_none x).mp h]; rfl
  · rw [H_Q_power n k x hn] at h
    exact T_halt_G n _ h

lemma H_Z (n : Nat) (x : result) (hn : 1 ≤ n) : H n (Z x) = T n (G x) := by
  rcases n with _ | m; · omega
  unfold H T
  rw [opF_power_Z, G_Q]
  rfl

lemma H_Z_power (n k : Nat) (x : result) (hn : 1 ≤ n) :
    power (H n) (k + 1) (Z x) = T n (power (H n) k (G x)) := by
  rw [power_succ_r, H_Z n x hn]
  exact power_commute (H n) (T n) (fun y => H_T n y hn) k (G x)

theorem K_Z (n : Nat) (x : result) (hn : 1 ≤ n) :
    K n (Z x) ↔ K n (G x) := by
  unfold K eventually
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp only [power] at hk
      rw [(Z_none x).mp hk]
      exact ⟨0, rfl⟩
    · rw [H_Z_power n k x hn] at hk
      exact ⟨k + 1, T_halt_G n _ hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [H_Z_power n k x hn, hk, T_strict]

theorem K_H (n : Nat) (x : result) : K n x ↔ K n (H n x) :=
  eventually_step (H n) (H_strict n) x

theorem K_T (n : Nat) (x : result) (hn : 1 ≤ n) : K n x ↔ K n (T n x) := by
  rw [← K_T_equiv n x hn, ← K_T_equiv n (T n x) hn]
  exact eventually_step (T n) (T_strict n) x

lemma opF_power_three (n : Nat) (x : result) :
    power opF n (pfx 3 x) = pfx 3 (power opF (2 * n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [power, ih, opF_three]
    have h2 : 2 * (n + 1) = (2 * n) + 1 + 1 := by omega
    rw [h2]; rfl

lemma H_three (n : Nat) (x : result) : H n (pfx 3 x) = pfx 3 (H (2 * n) x) := by
  unfold H; rw [opF_power_three, G_three]

lemma H_power_three (n k : Nat) (x : result) :
    power (H n) k (pfx 3 x) = pfx 3 (power (H (2 * n)) k x) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [power, ih, H_three]

theorem K_three (n : Nat) (x : result) : K n (pfx 3 x) ↔ K (2 * n) x := by
  unfold K eventually
  constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩
  · rw [H_power_three] at hk; exact (pfx_none 3 _).mp hk
  · rw [H_power_three, hk]; rfl

-- ============================================================================
-- Section 8: Binary Prefix Rules & Four Clock (`Row9Binary.v` + `Row9Four.v`)
-- ============================================================================

def opD (x : result) : result := lift_plus 4 x
def L1 (x : result) : result := pfx 1 x

lemma acc_F_valid (x : result) : opF x ≠ some [] := by
  rcases x with _ | w; · intro h; cases h
  exact fun h => f_success_nonempty h rfl

lemma acc_power_valid (n : Nat) {x : result} (hx : x ≠ some []) : power opF n x ≠ some [] := by
  cases n with
  | zero => exact hx
  | succ n => exact acc_F_valid _

lemma acc_F_D {x : result} (hx : x ≠ some []) : opF (opD x) = L1 x := by
  rcases x with _ | ⟨_ | ⟨a, u⟩⟩
  · rfl
  · exact False.elim (hx rfl)
  · exact f_large a u

lemma acc_F_L (x : result) : opF (L1 x) = opD (opF x) := by
  rcases x with _ | w; · rfl
  exact f_one w

lemma acc_D_even (n : Nat) {x : result} (hx : x ≠ some []) :
    power opF (2 * n) (opD x) = opD (power opF n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n) + 1 + 1 := by omega
    rw [h2]
    simp only [power]
    rw [ih, acc_F_D (acc_power_valid n hx), acc_F_L]

lemma acc_D_odd (n : Nat) {x : result} (hx : x ≠ some []) :
    power opF (2 * n + 1) (opD x) = L1 (power opF n x) := by
  simp only [power]
  rw [acc_D_even n hx, acc_F_D (acc_power_valid n hx)]

lemma acc_L_even (n : Nat) (x : result) :
    power opF (2 * n) (L1 x) = L1 (power opF n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n) + 1 + 1 := by omega
    rw [h2]
    simp only [power]
    rw [ih, acc_F_L, acc_F_D (acc_F_valid _)]

lemma acc_L_odd (n : Nat) (x : result) :
    power opF (2 * n + 1) (L1 x) = opD (power opF (n + 1) x) := by
  simp only [power]
  rw [acc_L_even, acc_F_L]

lemma acc_power_two (n : Nat) (x : result) :
    power opF n (pfx 2 x) = pfx 2 (power opF n x) := opF_power_Q n x

lemma acc_power_three (n : Nat) (x : result) :
    power opF n (pfx 3 x) = pfx 3 (power opF (2 * n) x) := opF_power_three n x

lemma four_G_one (x : result) : G (pfx 1 x) = lift_plus 2 (opF x) := by
  rcases x with _ | U; · rfl
  unfold G opF Z pfx bind_res
  simp only [Option.map, f_zero_one]
  cases f U <;> rfl

lemma four_G_six (x : result) : G (pfx 6 x) = pfx 4 (opF (opF x)) := by
  rcases x with _ | U; · rfl
  unfold G opF Z pfx
  simp only [Option.map, bind_res]
  have h6 : (6 : Nat) = 3 + 3 := rfl
  rw [h6, f_zero_large, f_three]
  simp only [bind_res, lift_prefix, lift_plus, first_plus, Option.map]
  rcases f U with _ | V
  · rfl
  · dsimp -failIfUnchanged only
    rcases f V with _ | W <;> rfl

lemma four_prefix_D_Z (x : result) : pfx 4 x = opD (Z x) := by
  cases x <;> rfl

lemma four_D_Q (x : result) : opD (Q x) = pfx 6 x := by
  cases x <;> rfl

lemma four_plus_Q (x : result) : lift_plus 2 (Q x) = pfx 4 x := by
  cases x <;> rfl

lemma H_four_even (m : Nat) (x : result) (hm : 1 ≤ m) :
    H (2 * m) (pfx 4 x) = pfx 4 (power opF (m + 1) (G x)) := by
  unfold H
  rw [four_prefix_D_Z, acc_D_even m (by cases x <;> intro h <;> cases h)]
  rcases m with _ | m'; · omega
  rw [opF_power_Z, four_D_Q, four_G_six]
  rfl

lemma H_four_odd (m : Nat) (x : result) (hm : 1 ≤ m) :
    H (2 * m + 1) (pfx 4 x) = pfx 4 (power opF m (G x)) := by
  unfold H
  rw [four_prefix_D_Z, acc_D_odd m (by cases x <;> intro h <;> cases h)]
  rcases m with _ | m'; · omega
  rw [opF_power_Z]
  unfold L1
  rw [four_G_one, opF_Q, four_plus_Q]
  rfl

lemma H_four_one (x : result) : H 1 (pfx 4 x) = pfx 4 (G x) := by
  unfold H
  rw [four_prefix_D_Z]
  have h1 : (1 : Nat) = 2 * 0 + 1 := rfl
  rw [h1, acc_D_odd 0 (by cases x <;> intro h <;> cases h)]
  simp only [power]
  unfold L1
  rw [four_G_one, opF_Z, four_plus_Q]

lemma K_four_transfer (n e : Nat) (x : result)
    (hE : ∀ y, H n (pfx 4 y) = pfx 4 (power opF e (G y))) :
    K n (pfx 4 x) ↔ K e (G x) := by
  have hC : ∀ k y, power (H n) k (pfx 4 y) = pfx 4 (power (fun z => power opF e (G z)) k y) := by
    intro k; induction k with
    | zero => intro y; rfl
    | succ k ih => intro y; simp only [power, ih, hE]
  have hB : K n (pfx 4 x) ↔ eventually (fun z => power opF e (G z)) x := by
    unfold K eventually
    constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩
    · rw [hC] at hk; exact (pfx_none 4 _).mp hk
    · rw [hC, hk]; rfl
  rw [hB]
  unfold K H
  exact eventually_rotate (power opF e) G (power_strict opF opF_none e) G_none x

def four_clock (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 + 1 else (n - 1) / 2

lemma four_clock_even (m : Nat) : four_clock (2 * m) = m + 1 := by
  unfold four_clock
  have h : ((2 * m) % 2 == 0) = true := by rw [beq_iff_eq]; omega
  rw [if_pos h]; omega

lemma four_clock_odd (m : Nat) : four_clock (2 * m + 1) = m := by
  unfold four_clock
  have h : ¬ (((2 * m + 1) % 2 == 0) = true) := by rw [beq_iff_eq]; omega
  rw [if_neg h]; omega

theorem H_four (n : Nat) (x : result) (hn : 1 ≤ n) :
    H n (pfx 4 x) = pfx 4 (power opF (four_clock n) (G x)) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [four_clock_even]; exact H_four_even m x (by omega)
  · rw [four_clock_odd]
    rcases m with _ | m'
    · exact H_four_one x
    · exact H_four_odd (m' + 1) x (by omega)

theorem K_four (n : Nat) (x : result) (hn : 2 ≤ n) :
    K n (pfx 4 x) ↔ K (four_clock n) (G x) :=
  K_four_transfer n (four_clock n) x (fun y => H_four n y (by omega))

-- ============================================================================
-- Section 9: Binary Gap Numerals & Productive Family (`Row9Numerals.v` + `Row9Family.v`)
-- ============================================================================

def numeral_fuel : Nat → Nat → word
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, n + 1 =>
    if (n + 1) % 2 == 1 then 1 :: numeral_fuel fuel ((n + 1) / 2)
    else first_plus 4 (numeral_fuel fuel ((n + 1) / 2))

def numeral (n : Nat) : word := numeral_fuel n n

lemma numeral_fuel_eq (f1 : Nat) :
    ∀ (f2 n : Nat), n ≤ f1 → n ≤ f2 → numeral_fuel f1 n = numeral_fuel f2 n := by
  induction f1 with
  | zero =>
    intro f2 n h1 _
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> rfl
  | succ f1 ih =>
    intro f2 n h1 h2
    cases n with
    | zero => cases f2 <;> rfl
    | succ m =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        simp only [numeral_fuel]
        rw [ih f2 ((m + 1) / 2) (by omega) (by omega)]

lemma numeral_zero : numeral 0 = [] := rfl

lemma numeral_double (n : Nat) : numeral (2 * n) = first_plus 4 (numeral n) := by
  cases n with
  | zero => rfl
  | succ m =>
    unfold numeral
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h2]
    simp only [numeral_fuel]
    have hmod : ¬ (((2 * m + 1 + 1) % 2 == 1) = true) := by
      rw [beq_iff_eq]; omega
    have hdiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [if_neg hmod, hdiv]
    rw [numeral_fuel_eq (2 * m + 1) (m + 1) (m + 1) (by omega) (by omega)]
    rfl

lemma numeral_odd (n : Nat) : numeral (2 * n + 1) = 1 :: numeral n := by
  unfold numeral
  simp only [numeral_fuel]
  have hmod : ((2 * n + 1) % 2 == 1) = true := by
    rw [beq_iff_eq]; omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [if_pos hmod, hdiv]
  rw [numeral_fuel_eq (2 * n) n n (by omega) (by omega)]

lemma numeral_nonempty (n : Nat) (hn : 0 < n) : numeral n ≠ [] := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hnil
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hk : 0 < k := by omega
      rw [numeral_double] at hnil
      cases h : numeral k with
      | nil => exact ih k (by omega) hk h
      | cons a u => simp [first_plus, h] at hnil
    · rw [numeral_odd] at hnil
      cases hnil

lemma Eval_numeral_succ (n : Nat) : Eval (numeral n) (some (numeral (n + 1))) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | m
    · exact .nil
    · rcases Nat.even_or_odd' (m + 1) with ⟨k, hk | hk⟩
      · have hk_pos : 0 < k := by omega
        have hne := numeral_nonempty k hk_pos
        rw [hk, numeral_double k, numeral_odd k]
        cases hnum : numeral k with
        | nil => exact False.elim (hne hnum)
        | cons a u =>
          simp only [first_plus]
          exact .large a u
      · have hsucc : m + 1 + 1 = 2 * (k + 1) := by omega
        rw [hsucc, hk, numeral_odd k, numeral_double (k + 1)]
        exact .one (ih k (by omega))

theorem f_numeral (n : Nat) : f (numeral n) = some (numeral (n + 1)) :=
  Eval_iff_f.mp (Eval_numeral_succ n)

theorem opF_numeral (n : Nat) : opF (some (numeral n)) = some (numeral (n + 1)) :=
  f_numeral n

theorem power_F_numeral (a n : Nat) :
    power opF a (some (numeral n)) = some (numeral (n + a)) := by
  induction a with
  | zero => rw [Nat.add_zero]; rfl
  | succ a ih =>
    simp only [power, ih, opF_numeral, Nat.add_succ]

theorem power_F_nil (a : Nat) : power opF a (some []) = some (numeral a) := by
  have h := power_F_numeral a 0
  rw [Nat.zero_add] at h
  exact h

lemma numeral_eight_four (n : Nat) : numeral (8 * n + 4) = 9 :: numeral n := by
  have h : 8 * n + 4 = 2 * (2 * (2 * n + 1)) := by omega
  rw [h, numeral_double, numeral_double, numeral_odd]
  rfl

lemma numeral_boundary (m : Nat) (hm : 2 ≤ m) :
    numeral (m + (7 * m - 12)) = 9 :: numeral (m - 2) := by
  have h : m + (7 * m - 12) = 8 * (m - 2) + 4 := by omega
  rw [h, numeral_eight_four]

lemma H_numeral_boundary (m : Nat) (hm : 2 ≤ m) :
    H (7 * m - 12) (some (numeral m)) = Q (Q (some (numeral (m - 2)))) := by
  unfold H
  rw [power_F_numeral, numeral_boundary m hm, G_nine]
  rfl

theorem productive_numeric_family_index (m : Nat) (hm : 2 ≤ m) (k : Nat) :
    power (H (7 * m - 12)) k (some (numeral m)) ≠ none := by
  induction k with
  | zero => intro h; cases h
  | succ k ih =>
    intro h
    rw [power_succ_r, H_numeral_boundary m hm] at h
    have h1 := Q_index_nonincrease (7 * m - 12) k (Q (some (numeral (m - 2)))) (by omega) h
    rw [opF_Q, opF_numeral] at h1
    have h2 := Q_index_nonincrease (7 * m - 12) k (some (numeral (m - 2 + 1))) (by omega) h1
    rw [opF_numeral] at h2
    have hm_eq : m - 2 + 1 + 1 = m := by omega
    rw [hm_eq] at h2
    exact ih h2

theorem productive_numeric_family_boundary (m : Nat) (hm : 2 ≤ m) :
    ¬ K (7 * m - 12) (Q (Q (some (numeral (m - 2))))) := by
  rintro ⟨k, hk⟩
  apply productive_numeric_family_index m hm (k + 1)
  rw [power_succ_r, H_numeral_boundary m hm]
  exact hk

lemma numeral_9070 : numeral 9070 = [5, 1, 1, 5, 1, 5, 1, 13] := rfl

theorem selected_numeric_endpoint_nonhalting :
    ¬ K 63492 (some [2, 2, 5, 1, 1, 5, 1, 5, 1, 13]) := by
  have h := productive_numeric_family_boundary 9072 (by decide)
  have h1 : 7 * 9072 - 12 = 63492 := rfl
  have h2 : 9072 - 2 = 9070 := rfl
  rw [h1, h2, numeral_9070] at h
  exact h

-- ============================================================================
-- Section 10: Fast Binary Prefix Accelerator (`Row9Acceleration.v`)
-- ============================================================================

def fast_power : Nat → Nat → word → Option word
  | 0, _, _ => none
  | _ + 1, 0, w => some w
  | fuel + 1, p + 1, [] => some (numeral (p + 1))
  | _ + 1, _ + 1, 0 :: _ => none
  | fuel + 1, p + 1, 1 :: u =>
    if (p + 1) % 2 == 1 then
      Option.map (first_plus 4) (fast_power fuel ((p + 1) / 2 + 1) u)
    else
      Option.map (1 :: ·) (fast_power fuel ((p + 1) / 2) u)
  | fuel + 1, p + 1, 2 :: u =>
    Option.map (2 :: ·) (fast_power fuel (p + 1) u)
  | fuel + 1, p + 1, 3 :: u =>
    Option.map (3 :: ·) (fast_power fuel (2 * (p + 1)) u)
  | fuel + 1, p + 1, (g + 4) :: u =>
    if (p + 1) % 2 == 1 then
      Option.map (1 :: ·) (fast_power fuel ((p + 1) / 2) (g :: u))
    else
      Option.map (first_plus 4) (fast_power fuel ((p + 1) / 2) (g :: u))

def checked_f : Nat → Nat → word → Option result
  | _, 0, _ => none
  | accel, fuel + 1, w =>
    match fast_power accel 1 w with
    | some v => some (some v)
    | none =>
      match w with
      | [] => some (some [1])
      | 1 :: u => Option.map (lift_plus 4) (checked_f accel fuel u)
      | 2 :: u => Option.map (lift_prefix [2]) (checked_f accel fuel u)
      | 3 :: u =>
        match checked_f accel fuel u with
        | none => none
        | some none => some none
        | some (some v) => Option.map (lift_prefix [3]) (checked_f accel fuel v)
      | (g + 4) :: u => some (some (1 :: g :: u))
      | [0] => some (some [2, 2])
      | 0 :: 0 :: _ => some none
      | 0 :: 1 :: u => Option.map (fun r => lift_prefix [2] (lift_plus 2 r)) (checked_f accel fuel u)
      | 0 :: 2 :: u => Option.map (lift_prefix [2, 0]) (checked_f accel fuel u)
      | 0 :: (g + 3) :: u => Option.map (fun r => lift_prefix [2] (lift_plus 1 r)) (checked_f accel fuel (g :: u))

lemma acc_D_binary (n : Nat) {x : result} (hx : x ≠ some []) :
    power opF n (opD x) =
      if n % 2 == 1 then L1 (power opF (n / 2) x)
      else opD (power opF (n / 2) x) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hmod : ¬ (((2 * k) % 2 == 1) = true) := by rw [beq_iff_eq]; omega
    have hdiv : (2 * k) / 2 = k := by omega
    rw [if_neg hmod, hdiv]
    exact acc_D_even k hx
  · have hmod : ((2 * k + 1) % 2 == 1) = true := by rw [beq_iff_eq]; omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [if_pos hmod, hdiv]
    exact acc_D_odd k hx

lemma acc_L_binary (n : Nat) (x : result) :
    power opF n (L1 x) =
      if n % 2 == 1 then opD (power opF (n / 2 + 1) x)
      else L1 (power opF (n / 2) x) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hmod : ¬ (((2 * k) % 2 == 1) = true) := by rw [beq_iff_eq]; omega
    have hdiv : (2 * k) / 2 = k := by omega
    rw [if_neg hmod, hdiv]
    exact acc_L_even k x
  · have hmod : ((2 * k + 1) % 2 == 1) = true := by rw [beq_iff_eq]; omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [if_pos hmod, hdiv]
    exact acc_L_odd k x

theorem fast_power_sound (fuel : Nat) :
    ∀ (p : Nat) (w v : word), fast_power fuel p w = some v → power opF p (some w) = some v := by
  induction fuel with
  | zero => intro p w v h; cases h
  | succ fuel ih =>
    intro p w v h
    rcases p with _ | p
    · simp only [fast_power] at h; injection h with h; subst h; rfl
    · rcases w with _ | ⟨g, u⟩
      · simp only [fast_power] at h; injection h with h; subst h
        exact power_F_nil (p + 1)
      · rcases g with _ | _ | _ | _ | g'
        · simp only [fast_power] at h; cases h
        · simp only [fast_power] at h
          change power opF (p + 1) (L1 (some u)) = some v
          rw [acc_L_binary]
          split at h <;> rename_i hcond
          · rcases hfp : fast_power fuel ((p + 1) / 2 + 1) u with _ | a
            · rw [hfp] at h; cases h
            · rw [hfp] at h; simp only [Option.map] at h; injection h with h; subst h
              rw [if_pos hcond, ih _ _ _ hfp]; rfl
          · rcases hfp : fast_power fuel ((p + 1) / 2) u with _ | a
            · rw [hfp] at h; cases h
            · rw [hfp] at h; simp only [Option.map] at h; injection h with h; subst h
              rw [if_neg hcond, ih _ _ _ hfp]; rfl
        · simp only [fast_power] at h
          change power opF (p + 1) (pfx 2 (some u)) = some v
          rw [acc_power_two]
          rcases hfp : fast_power fuel (p + 1) u with _ | a
          · rw [hfp] at h; cases h
          · rw [hfp] at h; simp only [Option.map] at h; injection h with h; subst h
            rw [ih _ _ _ hfp]; rfl
        · simp only [fast_power] at h
          change power opF (p + 1) (pfx 3 (some u)) = some v
          rw [acc_power_three]
          rcases hfp : fast_power fuel (2 * (p + 1)) u with _ | a
          · rw [hfp] at h; cases h
          · rw [hfp] at h; simp only [Option.map] at h; injection h with h; subst h
            rw [ih _ _ _ hfp]; rfl
        · simp only [fast_power] at h
          change power opF (p + 1) (opD (some (g' :: u))) = some v
          rw [acc_D_binary (p + 1) (by intro hc; cases hc)]
          split at h <;> rename_i hcond
          · rcases hfp : fast_power fuel ((p + 1) / 2) (g' :: u) with _ | a
            · rw [hfp] at h; cases h
            · rw [hfp] at h; simp only [Option.map] at h; injection h with h; subst h
              rw [if_pos hcond, ih _ _ _ hfp]; rfl
          · rcases hfp : fast_power fuel ((p + 1) / 2) (g' :: u) with _ | a
            · rw [hfp] at h; cases h
            · rw [hfp] at h; simp only [Option.map] at h; injection h with h; subst h
              rw [if_neg hcond, ih _ _ _ hfp]; rfl

theorem checked_f_sound (accel fuel : Nat) :
    ∀ (w : word) (r : result), checked_f accel fuel w = some r → f w = r := by
  induction fuel with
  | zero => intro w r h; cases h
  | succ fuel ih =>
    intro w r h
    unfold checked_f at h
    rcases hfp : fast_power accel 1 w with _ | v
    · rw [hfp] at h
      rcases w with _ | ⟨g, u⟩
      · dsimp -failIfUnchanged only at h; injection h with h; subst h; exact f_nil
      · rcases g with _ | _ | _ | _ | g'
        · rcases u with _ | ⟨b, u'⟩
          · dsimp -failIfUnchanged only at h; injection h with h; subst h; exact f_zero
          · rcases b with _ | _ | _ | b'
            · dsimp -failIfUnchanged only at h; injection h with h; subst h; exact f_zero_zero u'
            · dsimp -failIfUnchanged only at h
              rcases hcf : checked_f accel fuel u' with _ | a
              · rw [hcf] at h; cases h
              · rw [hcf] at h; simp only [Option.map] at h; injection h with h; subst h
                rw [f_zero_one, ih _ _ hcf]
            · dsimp -failIfUnchanged only at h
              rcases hcf : checked_f accel fuel u' with _ | a
              · rw [hcf] at h; cases h
              · rw [hcf] at h; simp only [Option.map] at h; injection h with h; subst h
                rw [f_zero_two, ih _ _ hcf]
            · dsimp -failIfUnchanged only at h
              rcases hcf : checked_f accel fuel (b' :: u') with _ | a
              · rw [hcf] at h; cases h
              · rw [hcf] at h; simp only [Option.map] at h; injection h with h; subst h
                rw [f_zero_large, ih _ _ hcf]
        · dsimp -failIfUnchanged only at h
          rcases hcf : checked_f accel fuel u with _ | a
          · rw [hcf] at h; cases h
          · rw [hcf] at h; simp only [Option.map] at h; injection h with h; subst h
            rw [f_one, ih _ _ hcf]
        · dsimp -failIfUnchanged only at h
          rcases hcf : checked_f accel fuel u with _ | a
          · rw [hcf] at h; cases h
          · rw [hcf] at h; simp only [Option.map] at h; injection h with h; subst h
            rw [f_two, ih _ _ hcf]
        · dsimp -failIfUnchanged only at h
          rcases hcf : checked_f accel fuel u with _ | ⟨_ | a⟩
          · rw [hcf] at h; cases h
          · rw [hcf] at h; injection h with h; subst h
            rw [f_three, ih _ _ hcf]; rfl
          · rw [hcf] at h; dsimp -failIfUnchanged only at h
            rcases hcf2 : checked_f accel fuel a with _ | b
            · rw [hcf2] at h; cases h
            · rw [hcf2] at h; simp only [Option.map] at h; injection h with h; subst h
              rw [f_three, ih _ _ hcf]
              simp only [bind_res]
              rw [ih _ _ hcf2]
        · dsimp -failIfUnchanged only at h; injection h with h; subst h; exact f_large g' u
    · rw [hfp] at h
      dsimp -failIfUnchanged only at h
      injection h with h; subst h
      exact fast_power_sound accel 1 w v hfp

lemma row9_cert_G {u v : word} (h : f (0 :: u) = some (2 :: v)) : G (some u) = some v := by
  unfold G opF Z pfx bind_res
  simp only [Option.map, h, List.tail_cons]

lemma row9_cert_T {u a b v : word}
    (h0 : f u = some a) (h1 : f a = some b) (h2 : f b = some v) :
    T 3 (some u) = some (0 :: v) := by
  unfold T
  simp only [power, opF, bind_res, h0, h1, h2, Z, pfx, Option.map]

lemma row9_cert_H {u a b c v : word}
    (h0 : f u = some a) (h1 : f a = some b) (h2 : f b = some c) (h3 : f (0 :: c) = some (2 :: v)) :
    H 3 (some u) = some v := by
  unfold H
  simp only [power, opF, bind_res, h0, h1, h2]
  exact row9_cert_G h3

lemma step_edge_T {u a b v : word}
    (h0 : f u = some a) (h1 : f a = some b) (h2 : f b = some v) :
    K 3 (some u) ↔ K 3 (some (0 :: v)) := by
  rw [K_T 3 (some u) (by decide), row9_cert_T h0 h1 h2]

lemma step_edge_H {u a b c v : word}
    (h0 : f u = some a) (h1 : f a = some b) (h2 : f b = some c) (h3 : f (0 :: c) = some (2 :: v)) :
    K 3 (some u) ↔ K 3 (some v) := by
  rw [K_H 3 (some u), row9_cert_H h0 h1 h2 h3]

lemma step_normal_Z {n : Nat} {u v : word} (hn : 1 ≤ n) (h : f (0 :: u) = some (2 :: v)) :
    K n (some (0 :: u)) ↔ K n (some v) := by
  change K n (Z (some u)) ↔ K n (some v)
  rw [K_Z n (some u) hn, row9_cert_G h]

lemma step_normal_three {n m : Nat} {u : word} (hm : 2 * n = m) :
    K n (some (3 :: u)) ↔ K m (some u) := by
  subst hm; exact K_three n (some u)

lemma step_normal_four {n m : Nat} {u v : word} (hn : 2 ≤ n) (hm : four_clock n = m)
    (h : f (0 :: u) = some (2 :: v)) :
    K n (some (4 :: u)) ↔ K m (some v) := by
  subst hm
  change K n (pfx 4 (some u)) ↔ K (four_clock n) (some v)
  rw [K_four n (some u) hn, row9_cert_G h]

-- ============================================================================
-- Section 11: 222 Certificate Calls (`Row9CertificateCalls.v`)
-- ============================================================================

lemma row9_f_0 : f [] = some [1] := checked_f_sound 256 128 [] (some [1]) rfl
lemma row9_f_1 : f [1] = some [5] := checked_f_sound 256 128 [1] (some [5]) rfl
lemma row9_f_2 : f [5] = some [1, 1] := checked_f_sound 256 128 [5] (some [1, 1]) rfl
lemma row9_f_3 : f [0, 1, 1] = some [2, 7] := checked_f_sound 256 128 [0, 1, 1] (some [2, 7]) rfl
lemma row9_f_8 : f [2, 7] = some [2, 1, 3] := checked_f_sound 256 128 [2, 7] (some [2, 1, 3]) rfl
lemma row9_f_9 : f [2, 1, 3] = some [2, 7, 5] := checked_f_sound 256 128 [2, 1, 3] (some [2, 7, 5]) rfl
lemma row9_f_10 : f [0, 2, 7, 5] = some [2, 0, 1, 3, 5] := checked_f_sound 256 128 [0, 2, 7, 5] (some [2, 0, 1, 3, 5]) rfl
lemma row9_f_22 : f [2, 0, 1, 3, 5] = some [2, 2, 5, 9] := checked_f_sound 256 128 [2, 0, 1, 3, 5] (some [2, 2, 5, 9]) rfl
lemma row9_f_23 : f [2, 2, 5, 9] = some [2, 2, 1, 1, 9] := checked_f_sound 256 128 [2, 2, 5, 9] (some [2, 2, 1, 1, 9]) rfl
lemma row9_f_24 : f [0, 2, 2, 1, 1, 9] = some [2, 0, 2, 9, 5] := checked_f_sound 256 128 [0, 2, 2, 1, 1, 9] (some [2, 0, 2, 9, 5]) rfl
lemma row9_f_49 : f [2, 0, 2, 9, 5] = some [2, 2, 0, 1, 5, 5] := checked_f_sound 256 128 [2, 0, 2, 9, 5] (some [2, 2, 0, 1, 5, 5]) rfl
lemma row9_f_50 : f [2, 2, 0, 1, 5, 5] = some [2, 2, 2, 3, 1, 5] := checked_f_sound 256 128 [2, 2, 0, 1, 5, 5] (some [2, 2, 2, 3, 1, 5]) rfl
lemma row9_f_52 : f [0, 2, 2, 2, 3, 1, 5] = some [2, 0, 2, 2, 3, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 1, 5] (some [2, 0, 2, 2, 3, 1, 1, 1]) rfl
lemma row9_f_60 : f [0, 2, 2, 3, 1, 1, 1] = some [2, 0, 2, 3, 1, 9] := checked_f_sound 256 128 [0, 2, 2, 3, 1, 1, 1] (some [2, 0, 2, 3, 1, 9]) rfl
lemma row9_f_79 : f [2, 0, 2, 3, 1, 9] = some [2, 2, 0, 3, 1, 1, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 1, 9] (some [2, 2, 0, 3, 1, 1, 5]) rfl
lemma row9_f_80 : f [2, 2, 0, 3, 1, 1, 5] = some [2, 2, 2, 3, 7, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 1, 1, 5] (some [2, 2, 2, 3, 7, 1]) rfl
lemma row9_f_82 : f [0, 2, 2, 2, 3, 7, 1] = some [2, 0, 2, 2, 3, 7, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 7, 1] (some [2, 0, 2, 2, 3, 7, 1, 1]) rfl
lemma row9_f_89 : f [0, 2, 2, 3, 7, 1, 1] = some [2, 0, 2, 3, 7, 1, 5] := checked_f_sound 256 128 [0, 2, 2, 3, 7, 1, 1] (some [2, 0, 2, 3, 7, 1, 5]) rfl
lemma row9_f_111 : f [2, 0, 2, 3, 7, 1, 5] = some [2, 2, 0, 3, 7, 1, 1, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 7, 1, 5] (some [2, 2, 0, 3, 7, 1, 1, 1]) rfl
lemma row9_f_112 : f [2, 2, 0, 3, 7, 1, 1, 1] = some [2, 2, 2, 3, 2, 0, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 7, 1, 1, 1] (some [2, 2, 2, 3, 2, 0, 1, 1, 1]) rfl
lemma row9_f_114 : f [0, 2, 2, 2, 3, 2, 0, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 1, 7] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 2, 0, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 1, 7]) rfl
lemma row9_f_125 : f [0, 2, 2, 3, 2, 2, 1, 7] = some [2, 0, 2, 3, 2, 2, 1, 1, 3] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 1, 7] (some [2, 0, 2, 3, 2, 2, 1, 1, 3]) rfl
lemma row9_f_145 : f [2, 0, 2, 3, 2, 2, 1, 1, 3] = some [2, 2, 0, 3, 2, 2, 1, 7, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 1, 1, 3] (some [2, 2, 0, 3, 2, 2, 1, 7, 5]) rfl
lemma row9_f_146 : f [2, 2, 0, 3, 2, 2, 1, 7, 5] = some [2, 2, 2, 3, 0, 2, 5, 3, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 1, 7, 5] (some [2, 2, 2, 3, 0, 2, 5, 3, 5]) rfl
lemma row9_f_148 : f [0, 2, 2, 2, 3, 0, 2, 5, 3, 5] = some [2, 0, 2, 2, 3, 2, 2, 9, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 5, 3, 5] (some [2, 0, 2, 2, 3, 2, 2, 9, 9]) rfl
lemma row9_f_173 : f [0, 2, 2, 3, 2, 2, 9, 9] = some [2, 0, 2, 3, 2, 2, 5, 1, 9] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 9, 9] (some [2, 0, 2, 3, 2, 2, 5, 1, 9]) rfl
lemma row9_f_191 : f [2, 0, 2, 3, 2, 2, 5, 1, 9] = some [2, 2, 0, 3, 2, 2, 13, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 5, 1, 9] (some [2, 2, 0, 3, 2, 2, 13, 5]) rfl
lemma row9_f_192 : f [2, 2, 0, 3, 2, 2, 13, 5] = some [2, 2, 2, 3, 0, 2, 1, 9, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 13, 5] (some [2, 2, 2, 3, 0, 2, 1, 9, 5]) rfl
lemma row9_f_194 : f [0, 2, 2, 2, 3, 0, 2, 1, 9, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 1, 1, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 1, 9, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 1, 1, 5]) rfl
lemma row9_f_220 : f [0, 2, 2, 3, 2, 2, 3, 1, 1, 5] = some [2, 0, 2, 3, 2, 2, 3, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 1, 1, 5] (some [2, 0, 2, 3, 2, 2, 3, 1, 1, 1, 1]) rfl
lemma row9_f_238 : f [2, 0, 2, 3, 2, 2, 3, 1, 1, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 1, 1, 9] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 1, 1, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 1, 1, 9]) rfl
lemma row9_f_239 : f [2, 2, 0, 3, 2, 2, 3, 1, 1, 9] = some [2, 2, 2, 3, 0, 2, 3, 1, 5, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 1, 1, 9] (some [2, 2, 2, 3, 0, 2, 3, 1, 5, 5]) rfl
lemma row9_f_241 : f [0, 2, 2, 2, 3, 0, 2, 3, 1, 5, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 11, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 1, 5, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 11, 1]) rfl
lemma row9_f_278 : f [0, 2, 2, 3, 2, 2, 3, 11, 1] = some [2, 0, 2, 3, 2, 2, 3, 11, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 11, 1] (some [2, 0, 2, 3, 2, 2, 3, 11, 1, 1]) rfl
lemma row9_f_295 : f [2, 0, 2, 3, 2, 2, 3, 11, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 11, 1, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 11, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 11, 1, 5]) rfl
lemma row9_f_296 : f [2, 2, 0, 3, 2, 2, 3, 11, 1, 5] = some [2, 2, 2, 3, 0, 2, 3, 5, 3, 1, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 11, 1, 5] (some [2, 2, 2, 3, 0, 2, 3, 5, 3, 1, 5]) rfl
lemma row9_f_298 : f [0, 2, 2, 2, 3, 0, 2, 3, 5, 3, 1, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 2, 4, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 5, 3, 1, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 2, 4, 1, 1, 1]) rfl
lemma row9_f_351 : f [0, 2, 2, 3, 2, 2, 3, 2, 4, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 6, 1, 7] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 2, 4, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 6, 1, 7]) rfl
lemma row9_f_376 : f [2, 0, 2, 3, 2, 2, 3, 2, 6, 1, 7] = some [2, 2, 0, 3, 2, 2, 3, 2, 6, 1, 1, 3] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 6, 1, 7] (some [2, 2, 0, 3, 2, 2, 3, 2, 6, 1, 1, 3]) rfl
lemma row9_f_377 : f [2, 2, 0, 3, 2, 2, 3, 2, 6, 1, 1, 3] = some [2, 2, 2, 3, 0, 2, 3, 2, 6, 11, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 6, 1, 1, 3] (some [2, 2, 2, 3, 0, 2, 3, 2, 6, 11, 5]) rfl
lemma row9_f_379 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 6, 11, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 1, 2, 1, 7, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 6, 11, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 1, 2, 1, 7, 5]) rfl
lemma row9_f_455 : f [0, 2, 2, 3, 2, 2, 3, 0, 1, 2, 1, 7, 5] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 1, 2, 1, 7, 5] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9]) rfl
lemma row9_f_485 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9, 1]) rfl
lemma row9_f_486 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9, 1] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 17] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 9, 1] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 17]) rfl
lemma row9_f_488 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 17] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 17] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 13, 1]) rfl
lemma row9_f_579 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 13, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 13, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14]) rfl
lemma row9_f_614 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14, 1]) rfl
lemma row9_f_615 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14, 1] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 9, 2, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 14, 1] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 9, 2, 1]) rfl
lemma row9_f_617 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 9, 2, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 9, 2, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 9, 2, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 9, 2, 5]) rfl
lemma row9_f_709 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 9, 2, 5] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 1, 5, 2, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 9, 2, 5] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 1, 5, 2, 1, 1]) rfl
lemma row9_f_779 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 1, 5, 2, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 1, 5, 2, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 5]) rfl
lemma row9_f_780 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 5] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 5] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 1, 1]) rfl
lemma row9_f_782 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 1, 2, 5, 1, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 1, 2, 5, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 1, 2, 5, 1, 5]) rfl
lemma row9_f_874 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 1, 2, 5, 1, 5] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 1, 2, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 1, 2, 5, 1, 5] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 1, 2, 1, 1, 1, 1, 1]) rfl
lemma row9_f_951 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 1, 2, 1, 1, 1, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 1, 2] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 1, 2, 1, 1, 1, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 1, 2]) rfl
lemma row9_f_952 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 1, 2] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 6, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 1, 2] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 6, 1]) rfl
lemma row9_f_954 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 6, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 5, 6, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 5, 6, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 5, 6, 5]) rfl
lemma row9_f_1046 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 5, 6, 5] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 1, 1, 6, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 5, 6, 5] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 1, 1, 6, 1, 1]) rfl
lemma row9_f_1152 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 1, 1, 6, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 9] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 1, 1, 6, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 9]) rfl
lemma row9_f_1153 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 9] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 9] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 1]) rfl
lemma row9_f_1155 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 5]) rfl
lemma row9_f_1247 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 5] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 5, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 5] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 5, 1, 1, 1]) rfl
lemma row9_f_1370 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 5, 1, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 5, 1, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 13]) rfl
lemma row9_f_1371 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 1]) rfl
lemma row9_f_1373 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 5] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 5]) rfl
lemma row9_f_1465 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 5] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 1, 3, 9, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 5] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 1, 3, 9, 1, 1]) rfl
lemma row9_f_1634 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 1, 3, 9, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 1, 3, 9, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 1]) rfl
lemma row9_f_1635 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 1] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 1] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 5]) rfl
lemma row9_f_1637 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 9]) rfl
lemma row9_f_1729 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 9] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 1, 9, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 9] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 1, 9, 1, 1]) rfl
lemma row9_f_1916 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 1, 9, 1, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 1, 9, 1, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 1]) rfl
lemma row9_f_1917 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 1] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 1] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 5]) rfl
lemma row9_f_1919 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 9]) rfl
lemma row9_f_2011 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 9] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 5, 3, 5, 5, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 9] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 5, 3, 5, 5, 1]) rfl
lemma row9_f_2235 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 5, 3, 5, 5, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 5, 3, 5, 5, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 5]) rfl
lemma row9_f_2236 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 5] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 9] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 5] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 9]) rfl
lemma row9_f_2238 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 9] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 9] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 13]) rfl
lemma row9_f_2330 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 13] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 5, 5, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 13] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 5, 5, 1]) rfl
lemma row9_f_2578 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 5, 5, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 5, 5, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 13]) rfl
lemma row9_f_2579 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 17] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 17]) rfl
lemma row9_f_2581 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 17] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 21] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 17] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 21]) rfl
lemma row9_f_2673 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 21] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 5, 9, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 21] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 5, 9, 1]) rfl
lemma row9_f_2947 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 5, 9, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 5, 9, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 13]) rfl
lemma row9_f_2948 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 17] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 17]) rfl
lemma row9_f_2950 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 17] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 21] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 17] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 21]) rfl
lemma row9_f_3042 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 21] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 5, 9, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 21] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 5, 9, 1]) rfl
lemma row9_f_3323 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 5, 9, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 5, 9, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 13]) rfl
lemma row9_f_3324 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 17] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 17]) rfl
lemma row9_f_3326 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 17] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 21] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 17] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 21]) rfl
lemma row9_f_3418 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 21] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 5, 9, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 21] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 5, 9, 1]) rfl
lemma row9_f_3754 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 5, 9, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 0, 1, 1, 5, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 5, 9, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 0, 1, 1, 5, 1, 13]) rfl
lemma row9_f_3755 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 0, 1, 1, 5, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 21] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 0, 1, 1, 5, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 21]) rfl
lemma row9_f_3757 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 21] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 25] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 21] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 25]) rfl
lemma row9_f_3849 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 25] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 9, 9, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 25] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 9, 9, 1]) rfl
lemma row9_f_4194 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 9, 9, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 7, 1, 1, 5, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 9, 9, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 7, 1, 1, 5, 1, 13]) rfl
lemma row9_f_4195 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 7, 1, 1, 5, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 9, 9] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 7, 1, 1, 5, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 9, 9]) rfl
lemma row9_f_4197 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 9, 9] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 5, 1, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 9, 9] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 5, 1, 9]) rfl
lemma row9_f_4289 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 5, 1, 9] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 1, 1, 13, 5] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 5, 1, 9] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 1, 1, 13, 5]) rfl
lemma row9_f_4656 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 1, 1, 13, 5] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 1, 5, 1, 5, 1, 5, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 1, 1, 13, 5] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 1, 5, 1, 5, 1, 5, 5]) rfl
lemma row9_f_4657 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 1, 5, 1, 5, 1, 5, 5] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 9, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 1, 5, 1, 5, 1, 5, 5] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 9, 1]) rfl
lemma row9_f_4659 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 9, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 17] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 9, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 17]) rfl
lemma row9_f_4751 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 17] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 5, 5, 5] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 17] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 5, 5, 5]) rfl
lemma row9_f_5125 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 5, 5, 5] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 5, 5, 9, 5, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 5, 5, 5] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 5, 5, 9, 5, 1]) rfl
lemma row9_f_5126 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 5, 5, 9, 5, 1] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 5, 5, 9, 5, 1] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 5]) rfl
lemma row9_f_5128 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 9]) rfl
lemma row9_f_5220 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 9] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 5, 1, 5, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 9] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 5, 1, 5, 1]) rfl
lemma row9_f_5623 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 5, 1, 5, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 1, 1, 1, 5, 5, 9] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 5, 1, 5, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 1, 1, 1, 5, 5, 9]) rfl
lemma row9_f_5624 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 1, 1, 1, 5, 5, 9] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 17] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 1, 1, 1, 5, 5, 9] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 17]) rfl
lemma row9_f_5626 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 17] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 21] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 17] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 21]) rfl
lemma row9_f_5718 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 21] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 5, 9, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 21] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 5, 9, 1]) rfl
lemma row9_f_6135 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 5, 9, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 7, 1, 1, 1, 5, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 5, 9, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 7, 1, 1, 1, 5, 1, 13]) rfl
lemma row9_f_6136 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 7, 1, 1, 1, 5, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 7, 1, 1, 1, 5, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_6138 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_6230 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 13, 1]) rfl
lemma row9_f_6676 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 1, 3, 1, 13, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 1, 3, 1, 13, 1, 13]) rfl
lemma row9_f_6677 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 1, 3, 1, 13, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 13, 9] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 1, 3, 1, 13, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 13, 9]) rfl
lemma row9_f_6679 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 13, 9] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 9, 1, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 13, 9] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 9, 1, 9]) rfl
lemma row9_f_6771 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 9, 1, 9] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 5, 13, 5] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 9, 1, 9] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 5, 13, 5]) rfl
lemma row9_f_7223 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 5, 13, 5] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 17, 5, 1, 5, 5] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 5, 13, 5] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 17, 5, 1, 5, 5]) rfl
lemma row9_f_7224 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 17, 5, 1, 5, 5] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 9, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 17, 5, 1, 5, 5] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 9, 1]) rfl
lemma row9_f_7226 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 9, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 17] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 9, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 17]) rfl
lemma row9_f_7318 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 17] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 13, 5, 5] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 17] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 13, 5, 5]) rfl
lemma row9_f_7791 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 13, 5, 5] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 5, 5, 13, 5, 1] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 13, 5, 5] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 5, 5, 13, 5, 1]) rfl
lemma row9_f_7792 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 5, 5, 13, 5, 1] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 5] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 5, 5, 13, 5, 1] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 5]) rfl
lemma row9_f_7794 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 5] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 9] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 5] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 9]) rfl
lemma row9_f_7886 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 9] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 13, 1, 5, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 9] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 13, 1, 5, 1]) rfl
lemma row9_f_8365 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 13, 1, 5, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 1, 9, 5, 9] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 13, 1, 5, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 1, 9, 5, 9]) rfl
lemma row9_f_8366 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 1, 9, 5, 9] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 21] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 1, 9, 5, 9] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 21]) rfl
lemma row9_f_8368 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 21] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 25] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 21] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 25]) rfl
lemma row9_f_8460 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 25] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 9, 9, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 25] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 9, 9, 1]) rfl
lemma row9_f_8963 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 9, 9, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 9, 9, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 1, 13]) rfl
lemma row9_f_8964 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_8966 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_9058 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 13, 1]) rfl
lemma row9_f_9568 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 13, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 13, 1, 13]) rfl
lemma row9_f_9569 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 13, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 13, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_9571 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_9663 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 13, 1]) rfl
lemma row9_f_10217 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 17, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 17, 1, 13]) rfl
lemma row9_f_10218 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 17, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 17, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1]) rfl
lemma row9_f_10220 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_10312 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 13, 1]) rfl
lemma row9_f_10893 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 21, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 21, 1, 13]) rfl
lemma row9_f_10894 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 21, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 21, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1]) rfl
lemma row9_f_10896 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_10988 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 13, 1]) rfl
lemma row9_f_11624 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 21, 1, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 21, 1, 13]) rfl
lemma row9_f_11625 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 21, 1, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 21, 1, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1]) rfl
lemma row9_f_11627 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_11719 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 13, 1]) rfl
lemma row9_f_12389 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 13]) rfl
lemma row9_f_12390 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1]) rfl
lemma row9_f_12392 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_12484 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 13, 1]) rfl
lemma row9_f_13175 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 1, 1, 1, 5, 13]) rfl
lemma row9_f_13176 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1]) rfl
lemma row9_f_13178 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_13270 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 13, 1]) rfl
lemma row9_f_13968 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 1, 1, 1, 5, 13]) rfl
lemma row9_f_13969 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1]) rfl
lemma row9_f_13971 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_14063 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 13, 1]) rfl
lemma row9_f_14812 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 1, 1, 1, 5, 13]) rfl
lemma row9_f_14813 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1]) rfl
lemma row9_f_14815 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_14907 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 13, 1]) rfl
lemma row9_f_15663 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 1, 1, 1, 5, 13]) rfl
lemma row9_f_15664 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1]) rfl
lemma row9_f_15666 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_15758 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 13, 1]) rfl
lemma row9_f_16544 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 1, 1, 1, 5, 13]) rfl
lemma row9_f_16545 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1]) rfl
lemma row9_f_16547 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_16639 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 13, 1]) rfl
lemma row9_f_17447 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 13]) rfl
lemma row9_f_17448 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1]) rfl
lemma row9_f_17450 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_17542 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 13, 1]) rfl
lemma row9_f_18392 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 1, 1, 1, 5, 13]) rfl
lemma row9_f_18393 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1]) rfl
lemma row9_f_18395 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_18487 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 13, 1]) rfl
lemma row9_f_19358 : f [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 13, 1] = some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 13, 1] (some [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 1, 1, 1, 5, 13]) rfl
lemma row9_f_19359 : f [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 1, 1, 1, 5, 13] = some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [2, 2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 1, 1, 1, 5, 13] (some [2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1]) rfl
lemma row9_f_19361 : f [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1] = some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1] (some [2, 0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_19453 : f [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1, 1] = some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1, 1] (some [2, 0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 13, 1]) rfl
lemma row9_f_19690 : f [0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 13, 1] = some [2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 13, 1] (some [2, 0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 1, 1, 1, 5, 13]) rfl
lemma row9_f_20031 : f [0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 1, 1, 1, 5, 13] = some [2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 1, 1, 1, 5, 13] (some [2, 3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1]) rfl
lemma row9_f_20375 : f [0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1] = some [2, 0, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5] := checked_f_sound 256 128 [0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1] (some [2, 0, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5]) rfl
lemma row9_f_20378 : f [0, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5] = some [2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5] (some [2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1]) rfl
lemma row9_f_20486 : f [0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1] = some [2, 4, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 5] := checked_f_sound 256 128 [0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1] (some [2, 4, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 5]) rfl
lemma row9_f_20495 : f [0, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 5] = some [2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1] := checked_f_sound 256 128 [0, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 5] (some [2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) rfl
lemma row9_f_20727 : f [0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1] = some [2, 3, 4, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1] := checked_f_sound 256 128 [0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1] (some [2, 3, 4, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1]) rfl
lemma row9_f_20734 : f [0, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1] = some [2, 0, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5, 1] := checked_f_sound 256 128 [0, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1] (some [2, 0, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5, 1]) rfl
lemma row9_f_20742 : f [0, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5, 1] = some [2, 3, 4, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1] := checked_f_sound 256 128 [0, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5, 1] (some [2, 3, 4, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1]) rfl
lemma row9_f_20754 : f [0, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1] = some [2, 0, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1] (some [2, 0, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 1, 1, 1]) rfl
lemma row9_f_20776 : f [0, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 1, 1, 1] = some [2, 0, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1, 1] := checked_f_sound 256 128 [0, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 1, 1, 1] (some [2, 0, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1, 1]) rfl
lemma row9_f_20789 : f [0, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1, 1] = some [2, 3, 0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21] := checked_f_sound 256 128 [0, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1, 1] (some [2, 3, 0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21]) rfl
lemma row9_f_20806 : f [0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21] = some [2, 4, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 13] := checked_f_sound 256 128 [0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21] (some [2, 4, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 13]) rfl
lemma row9_f_20825 : f [0, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 13] = some [2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13] := checked_f_sound 256 128 [0, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 13] (some [2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) rfl
lemma row9_f_21086 : f [0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13] = some [2, 0, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 13, 1, 13] := checked_f_sound 256 128 [0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13] (some [2, 0, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 13, 1, 13]) rfl
lemma row9_f_21089 : f [0, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 13, 1, 13] = some [2, 3, 0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13] := checked_f_sound 256 128 [0, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 13, 1, 13] (some [2, 3, 0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13]) rfl
lemma row9_f_21096 : f [0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13] = some [2, 0, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 9, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13] (some [2, 0, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 9, 1, 13]) rfl
lemma row9_f_21099 : f [0, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 9, 1, 13] = some [2, 0, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 13, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 9, 1, 13] (some [2, 0, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 13, 5, 1, 13]) rfl
lemma row9_f_21106 : f [0, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 13, 5, 1, 13] = some [2, 0, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 13, 5, 1, 13] (some [2, 0, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 5, 1, 13]) rfl
lemma row9_f_21111 : f [0, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 5, 1, 13] = some [2, 3, 3, 3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13] := checked_f_sound 256 128 [0, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 5, 1, 13] (some [2, 3, 3, 3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) rfl
lemma row9_f_21130 : f [0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13] = some [2, 4, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13] := checked_f_sound 256 128 [0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13] (some [2, 4, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13]) rfl
lemma row9_f_21137 : f [0, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13] = some [2, 0, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13] (some [2, 0, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13]) rfl
lemma row9_f_21146 : f [0, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13] = some [2, 4, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 17, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13] (some [2, 4, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 17, 1, 5, 1, 13]) rfl
lemma row9_f_21166 : f [0, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 17, 1, 5, 1, 13] = some [2, 0, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 17, 1, 5, 1, 13] (some [2, 0, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 1, 5, 1, 13]) rfl
lemma row9_f_21186 : f [0, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 1, 5, 1, 13] = some [2, 0, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 1, 5, 1, 13] (some [2, 0, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21213 : f [0, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 5, 1, 5, 1, 13] = some [2, 3, 3, 3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 5, 1, 5, 1, 13] (some [2, 3, 3, 3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21241 : f [0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13] = some [2, 0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 5, 5, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13] (some [2, 0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 5, 5, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21244 : f [0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 5, 5, 5, 1, 5, 1, 13] = some [2, 3, 0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 5, 5, 5, 1, 5, 1, 13] (some [2, 3, 0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21251 : f [0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13] = some [2, 4, 2, 2, 2, 2, 3, 2, 2, 3, 21, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13] (some [2, 4, 2, 2, 2, 2, 3, 2, 2, 3, 21, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21260 : f [0, 2, 2, 2, 2, 3, 2, 2, 3, 21, 1, 5, 1, 5, 1, 13] = some [2, 0, 2, 2, 2, 3, 2, 2, 3, 9, 9, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 2, 2, 3, 2, 2, 3, 21, 1, 5, 1, 5, 1, 13] (some [2, 0, 2, 2, 2, 3, 2, 2, 3, 9, 9, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21272 : f [0, 2, 2, 2, 3, 2, 2, 3, 9, 9, 1, 5, 1, 5, 1, 13] = some [2, 0, 2, 2, 3, 2, 2, 3, 13, 5, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 2, 3, 2, 2, 3, 9, 9, 1, 5, 1, 5, 1, 13] (some [2, 0, 2, 2, 3, 2, 2, 3, 13, 5, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21283 : f [0, 2, 2, 3, 2, 2, 3, 13, 5, 1, 5, 1, 5, 1, 13] = some [2, 0, 2, 3, 2, 2, 3, 9, 1, 5, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 2, 3, 2, 2, 3, 13, 5, 1, 5, 1, 5, 1, 13] (some [2, 0, 2, 3, 2, 2, 3, 9, 1, 5, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21296 : f [0, 2, 3, 2, 2, 3, 9, 1, 5, 1, 5, 1, 5, 1, 13] = some [2, 0, 3, 2, 2, 3, 17, 1, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 3, 2, 2, 3, 9, 1, 5, 1, 5, 1, 5, 1, 13] (some [2, 0, 3, 2, 2, 3, 17, 1, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21309 : f [0, 3, 2, 2, 3, 17, 1, 1, 5, 1, 5, 1, 13] = some [2, 3, 0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 3, 2, 2, 3, 17, 1, 1, 5, 1, 5, 1, 13] (some [2, 3, 0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21349 : f [0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13] = some [2, 0, 3, 9, 5, 1, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13] (some [2, 0, 3, 9, 5, 1, 1, 5, 1, 5, 1, 13]) rfl
lemma row9_f_21352 : f [0, 3, 9, 5, 1, 1, 5, 1, 5, 1, 13] = some [2, 3, 2, 2, 5, 1, 1, 5, 1, 5, 1, 13] := checked_f_sound 256 128 [0, 3, 9, 5, 1, 1, 5, 1, 5, 1, 13] (some [2, 3, 2, 2, 5, 1, 1, 5, 1, 5, 1, 13]) rfl

-- ============================================================================
-- Section 12: Certificate Path (`Row9Certificate.v`)
-- ============================================================================

lemma row9_edge_0 : K 3 (some []) ↔ K 3 (some [0, 1, 1]) := step_edge_T row9_f_0 row9_f_1 row9_f_2
lemma row9_edge_6 : K 3 (some [0, 1, 1]) ↔ K 3 (some [0, 2, 7, 5]) := step_edge_T row9_f_3 row9_f_8 row9_f_9
lemma row9_edge_15 : K 3 (some [0, 2, 7, 5]) ↔ K 3 (some [0, 2, 2, 1, 1, 9]) := step_edge_T row9_f_10 row9_f_22 row9_f_23
lemma row9_edge_30 : K 3 (some [0, 2, 2, 1, 1, 9]) ↔ K 3 (some [0, 2, 2, 3, 1, 1, 1]) := step_edge_H row9_f_24 row9_f_49 row9_f_50 row9_f_52
lemma row9_edge_48 : K 3 (some [0, 2, 2, 3, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 7, 1, 1]) := step_edge_H row9_f_60 row9_f_79 row9_f_80 row9_f_82
lemma row9_edge_66 : K 3 (some [0, 2, 2, 3, 7, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 1, 7]) := step_edge_H row9_f_89 row9_f_111 row9_f_112 row9_f_114
lemma row9_edge_84 : K 3 (some [0, 2, 2, 3, 2, 2, 1, 7]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 9, 9]) := step_edge_H row9_f_125 row9_f_145 row9_f_146 row9_f_148
lemma row9_edge_102 : K 3 (some [0, 2, 2, 3, 2, 2, 9, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 1, 1, 5]) := step_edge_H row9_f_173 row9_f_191 row9_f_192 row9_f_194
lemma row9_edge_120 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 1, 1, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 11, 1]) := step_edge_H row9_f_220 row9_f_238 row9_f_239 row9_f_241
lemma row9_edge_138 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 11, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 2, 4, 1, 1, 1]) := step_edge_H row9_f_278 row9_f_295 row9_f_296 row9_f_298
lemma row9_edge_156 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 2, 4, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 1, 2, 1, 7, 5]) := step_edge_H row9_f_351 row9_f_376 row9_f_377 row9_f_379
lemma row9_edge_174 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 1, 2, 1, 7, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 13, 1]) := step_edge_H row9_f_455 row9_f_485 row9_f_486 row9_f_488
lemma row9_edge_192 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 13, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 9, 2, 5]) := step_edge_H row9_f_579 row9_f_614 row9_f_615 row9_f_617
lemma row9_edge_210 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 9, 2, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 1, 2, 5, 1, 5]) := step_edge_H row9_f_709 row9_f_779 row9_f_780 row9_f_782
lemma row9_edge_228 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 1, 2, 5, 1, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 5, 6, 5]) := step_edge_H row9_f_874 row9_f_951 row9_f_952 row9_f_954
lemma row9_edge_246 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 5, 6, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 5]) := step_edge_H row9_f_1046 row9_f_1152 row9_f_1153 row9_f_1155
lemma row9_edge_264 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 1, 5, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 5]) := step_edge_H row9_f_1247 row9_f_1370 row9_f_1371 row9_f_1373
lemma row9_edge_282 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 7, 9, 5]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 9]) := step_edge_H row9_f_1465 row9_f_1634 row9_f_1635 row9_f_1637
lemma row9_edge_300 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 1, 1, 1, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 9]) := step_edge_H row9_f_1729 row9_f_1916 row9_f_1917 row9_f_1919
lemma row9_edge_318 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 11, 5, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 13]) := step_edge_H row9_f_2011 row9_f_2235 row9_f_2236 row9_f_2238
lemma row9_edge_336 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 6, 3, 1, 1, 13]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 21]) := step_edge_H row9_f_2330 row9_f_2578 row9_f_2579 row9_f_2581
lemma row9_edge_354 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 1, 21]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 21]) := step_edge_H row9_f_2673 row9_f_2947 row9_f_2948 row9_f_2950
lemma row9_edge_372 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 1, 1, 21]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 21]) := step_edge_H row9_f_3042 row9_f_3323 row9_f_3324 row9_f_3326
lemma row9_edge_390 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 7, 1, 1, 21]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 25]) := step_edge_H row9_f_3418 row9_f_3754 row9_f_3755 row9_f_3757
lemma row9_edge_408 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3, 1, 25]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 5, 1, 9]) := step_edge_H row9_f_3849 row9_f_4194 row9_f_4195 row9_f_4197
lemma row9_edge_426 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 9, 5, 5, 1, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 17]) := step_edge_H row9_f_4289 row9_f_4656 row9_f_4657 row9_f_4659
lemma row9_edge_444 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 13, 1, 17]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 9]) := step_edge_H row9_f_4751 row9_f_5125 row9_f_5126 row9_f_5128
lemma row9_edge_462 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 1, 5, 9, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 21]) := step_edge_H row9_f_5220 row9_f_5623 row9_f_5624 row9_f_5626
lemma row9_edge_480 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 7, 1, 5, 21]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1]) := step_edge_H row9_f_5718 row9_f_6135 row9_f_6136 row9_f_6138
lemma row9_edge_498 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 9, 1, 9]) := step_edge_H row9_f_6230 row9_f_6676 row9_f_6677 row9_f_6679
lemma row9_edge_516 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 5, 1, 1, 1, 9, 1, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 17]) := step_edge_H row9_f_6771 row9_f_7223 row9_f_7224 row9_f_7226
lemma row9_edge_534 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 5, 1, 9, 17]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 9]) := step_edge_H row9_f_7318 row9_f_7791 row9_f_7792 row9_f_7794
lemma row9_edge_552 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 5, 1, 17, 9]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 25]) := step_edge_H row9_f_7886 row9_f_8365 row9_f_8366 row9_f_8368
lemma row9_edge_570 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 5, 5, 1, 25]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1]) := step_edge_H row9_f_8460 row9_f_8963 row9_f_8964 row9_f_8966
lemma row9_edge_588 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1]) := step_edge_H row9_f_9058 row9_f_9568 row9_f_9569 row9_f_9571
lemma row9_edge_606 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 11, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1, 1]) := step_edge_H row9_f_9663 row9_f_10217 row9_f_10218 row9_f_10220
lemma row9_edge_624 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 6, 1, 1, 3, 1, 9, 1, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1, 1]) := step_edge_H row9_f_10312 row9_f_10893 row9_f_10894 row9_f_10896
lemma row9_edge_642 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 6, 7, 1, 9, 1, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_10988 row9_f_11624 row9_f_11625 row9_f_11627
lemma row9_edge_660 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_11719 row9_f_12389 row9_f_12390 row9_f_12392
lemma row9_edge_678 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5, 5, 1, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_12484 row9_f_13175 row9_f_13176 row9_f_13178
lemma row9_edge_696 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 9, 5, 1, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_13270 row9_f_13968 row9_f_13969 row9_f_13971
lemma row9_edge_714 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 1, 1, 9, 1, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_14063 row9_f_14812 row9_f_14813 row9_f_14815
lemma row9_edge_732 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 1, 1, 13, 1, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_14907 row9_f_15663 row9_f_15664 row9_f_15666
lemma row9_edge_750 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 11, 1, 13, 1, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_15758 row9_f_16544 row9_f_16545 row9_f_16547
lemma row9_edge_768 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 6, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_16639 row9_f_17447 row9_f_17448 row9_f_17450
lemma row9_edge_786 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_17542 row9_f_18392 row9_f_18393 row9_f_18395
lemma row9_edge_804 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 9, 1, 5, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1, 1]) := step_edge_H row9_f_18487 row9_f_19358 row9_f_19359 row9_f_19361
lemma row9_normal_2233 : K 3 (some [0, 2, 2, 3, 2, 2, 3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 1, 1, 1, 1]) ↔ K 3 (some [0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 13, 1]) := step_normal_Z (by decide) row9_f_19453
lemma row9_normal_2234 : K 3 (some [0, 2, 3, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 5, 1, 13, 1]) ↔ K 3 (some [0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 1, 1, 1, 5, 13]) := step_normal_Z (by decide) row9_f_19690
lemma row9_normal_2235 : K 3 (some [0, 3, 2, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 7, 1, 1, 1, 5, 5, 1, 1, 1, 5, 13]) ↔ K 3 (some [3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1]) := step_normal_Z (by decide) row9_f_20031
lemma row9_normal_2236 : K 3 (some [3, 0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1]) ↔ K 6 (some [0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1]) := step_normal_three rfl
lemma row9_normal_2237 : K 6 (some [0, 2, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1]) ↔ K 6 (some [0, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5]) := step_normal_Z (by decide) row9_f_20375
lemma row9_normal_2238 : K 6 (some [0, 3, 2, 1, 2, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5]) ↔ K 6 (some [3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1]) := step_normal_Z (by decide) row9_f_20378
lemma row9_normal_2239 : K 6 (some [3, 0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1]) ↔ K 12 (some [0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1]) := step_normal_three rfl
lemma row9_normal_2240 : K 12 (some [0, 6, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1]) ↔ K 12 (some [4, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 5]) := step_normal_Z (by decide) row9_f_20486
lemma row9_normal_2241 : K 12 (some [4, 3, 3, 2, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 5]) ↔ K 7 (some [3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) := step_normal_four (by decide) rfl row9_f_20495
lemma row9_normal_2242 : K 7 (some [3, 3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) ↔ K 14 (some [3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) := step_normal_three rfl
lemma row9_normal_2243 : K 14 (some [3, 0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) ↔ K 28 (some [0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) := step_normal_three rfl
lemma row9_normal_2244 : K 28 (some [0, 3, 6, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 13, 1]) ↔ K 28 (some [3, 4, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1]) := step_normal_Z (by decide) row9_f_20727
lemma row9_normal_2245 : K 28 (some [3, 4, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1]) ↔ K 56 (some [4, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1]) := step_normal_three rfl
lemma row9_normal_2246 : K 56 (some [4, 2, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 5, 1]) ↔ K 29 (some [0, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5, 1]) := step_normal_four (by decide) rfl row9_f_20734
lemma row9_normal_2247 : K 29 (some [0, 3, 6, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 5, 1]) ↔ K 29 (some [3, 4, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1]) := step_normal_Z (by decide) row9_f_20742
lemma row9_normal_2248 : K 29 (some [3, 4, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1]) ↔ K 58 (some [4, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1]) := step_normal_three rfl
lemma row9_normal_2249 : K 58 (some [4, 2, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 5, 1, 1]) ↔ K 30 (some [0, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 1, 1, 1]) := step_normal_four (by decide) rfl row9_f_20754
lemma row9_normal_2250 : K 30 (some [0, 2, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 1, 1, 1]) ↔ K 30 (some [0, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1, 1]) := step_normal_Z (by decide) row9_f_20776
lemma row9_normal_2251 : K 30 (some [0, 3, 2, 1, 2, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 1, 1, 1, 1, 1]) ↔ K 30 (some [3, 0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21]) := step_normal_Z (by decide) row9_f_20789
lemma row9_normal_2252 : K 30 (some [3, 0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21]) ↔ K 60 (some [0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21]) := step_normal_three rfl
lemma row9_normal_2253 : K 60 (some [0, 6, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 21]) ↔ K 60 (some [4, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 13]) := step_normal_Z (by decide) row9_f_20806
lemma row9_normal_2254 : K 60 (some [4, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 1, 5, 13]) ↔ K 31 (some [3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) := step_normal_four (by decide) rfl row9_f_20825
lemma row9_normal_2255 : K 31 (some [3, 3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) ↔ K 62 (some [3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) := step_normal_three rfl
lemma row9_normal_2256 : K 62 (some [3, 3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) ↔ K 124 (some [3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) := step_normal_three rfl
lemma row9_normal_2257 : K 124 (some [3, 0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) ↔ K 248 (some [0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) := step_normal_three rfl
lemma row9_normal_2258 : K 248 (some [0, 2, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 1, 1, 5, 13]) ↔ K 248 (some [0, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 13, 1, 13]) := step_normal_Z (by decide) row9_f_21086
lemma row9_normal_2259 : K 248 (some [0, 3, 2, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 13, 1, 13]) ↔ K 248 (some [3, 0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13]) := step_normal_Z (by decide) row9_f_21089
lemma row9_normal_2260 : K 248 (some [3, 0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13]) ↔ K 496 (some [0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13]) := step_normal_three rfl
lemma row9_normal_2261 : K 496 (some [0, 2, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 9, 1, 13]) ↔ K 496 (some [0, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 9, 1, 13]) := step_normal_Z (by decide) row9_f_21096
lemma row9_normal_2262 : K 496 (some [0, 2, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 1, 9, 1, 13]) ↔ K 496 (some [0, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 13, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21099
lemma row9_normal_2263 : K 496 (some [0, 2, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 13, 5, 1, 13]) ↔ K 496 (some [0, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21106
lemma row9_normal_2264 : K 496 (some [0, 3, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 5, 5, 5, 1, 13]) ↔ K 496 (some [3, 3, 3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21111
lemma row9_normal_2265 : K 496 (some [3, 3, 3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) ↔ K 992 (some [3, 3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2266 : K 992 (some [3, 3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) ↔ K 1984 (some [3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2267 : K 1984 (some [3, 3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) ↔ K 3968 (some [3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2268 : K 3968 (some [3, 0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) ↔ K 7936 (some [0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2269 : K 7936 (some [0, 6, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 1, 5, 5, 1, 13]) ↔ K 7936 (some [4, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21130
lemma row9_normal_2270 : K 7936 (some [4, 2, 6, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13]) ↔ K 3969 (some [0, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13]) := step_normal_four (by decide) rfl row9_f_21137
lemma row9_normal_2271 : K 3969 (some [0, 1, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 1, 1, 5, 5, 1, 13]) ↔ K 3969 (some [4, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 17, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21146
lemma row9_normal_2272 : K 3969 (some [4, 2, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 17, 1, 5, 1, 13]) ↔ K 1984 (some [0, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 1, 5, 1, 13]) := step_normal_four (by decide) rfl row9_f_21166
lemma row9_normal_2273 : K 1984 (some [0, 2, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 5, 9, 1, 5, 1, 13]) ↔ K 1984 (some [0, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21186
lemma row9_normal_2274 : K 1984 (some [0, 3, 3, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 1, 9, 5, 1, 5, 1, 13]) ↔ K 1984 (some [3, 3, 3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21213
lemma row9_normal_2275 : K 1984 (some [3, 3, 3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) ↔ K 3968 (some [3, 3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2276 : K 3968 (some [3, 3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) ↔ K 7936 (some [3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2277 : K 7936 (some [3, 0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) ↔ K 15872 (some [0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2278 : K 15872 (some [0, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 17, 5, 5, 1, 5, 1, 13]) ↔ K 15872 (some [0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 5, 5, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21241
lemma row9_normal_2279 : K 15872 (some [0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 9, 5, 5, 5, 1, 5, 1, 13]) ↔ K 15872 (some [3, 0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21244
lemma row9_normal_2280 : K 15872 (some [3, 0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13]) ↔ K 31744 (some [0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2281 : K 31744 (some [0, 6, 2, 2, 2, 2, 3, 2, 2, 3, 13, 1, 5, 5, 1, 5, 1, 13]) ↔ K 31744 (some [4, 2, 2, 2, 2, 3, 2, 2, 3, 21, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21251
lemma row9_normal_2282 : K 31744 (some [4, 2, 2, 2, 2, 3, 2, 2, 3, 21, 1, 5, 1, 5, 1, 13]) ↔ K 15873 (some [0, 2, 2, 2, 3, 2, 2, 3, 9, 9, 1, 5, 1, 5, 1, 13]) := step_normal_four (by decide) rfl row9_f_21260
lemma row9_normal_2283 : K 15873 (some [0, 2, 2, 2, 3, 2, 2, 3, 9, 9, 1, 5, 1, 5, 1, 13]) ↔ K 15873 (some [0, 2, 2, 3, 2, 2, 3, 13, 5, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21272
lemma row9_normal_2284 : K 15873 (some [0, 2, 2, 3, 2, 2, 3, 13, 5, 1, 5, 1, 5, 1, 13]) ↔ K 15873 (some [0, 2, 3, 2, 2, 3, 9, 1, 5, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21283
lemma row9_normal_2285 : K 15873 (some [0, 2, 3, 2, 2, 3, 9, 1, 5, 1, 5, 1, 5, 1, 13]) ↔ K 15873 (some [0, 3, 2, 2, 3, 17, 1, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21296
lemma row9_normal_2286 : K 15873 (some [0, 3, 2, 2, 3, 17, 1, 1, 5, 1, 5, 1, 13]) ↔ K 15873 (some [3, 0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21309
lemma row9_normal_2287 : K 15873 (some [3, 0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13]) ↔ K 31746 (some [0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13]) := step_normal_three rfl
lemma row9_normal_2288 : K 31746 (some [0, 2, 3, 5, 9, 1, 1, 5, 1, 5, 1, 13]) ↔ K 31746 (some [0, 3, 9, 5, 1, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21349
lemma row9_normal_2289 : K 31746 (some [0, 3, 9, 5, 1, 1, 5, 1, 5, 1, 13]) ↔ K 31746 (some [3, 2, 2, 5, 1, 1, 5, 1, 5, 1, 13]) := step_normal_Z (by decide) row9_f_21352
lemma row9_normal_2290 : K 31746 (some [3, 2, 2, 5, 1, 1, 5, 1, 5, 1, 13]) ↔ K 63492 (some [2, 2, 5, 1, 1, 5, 1, 5, 1, 13]) := step_normal_three rfl

theorem row9_selected_path : K 3 (some []) ↔ K 63492 (some [2, 2, 5, 1, 1, 5, 1, 5, 1, 13]) := by
  refine Iff.trans row9_edge_0 ?_
  refine Iff.trans row9_edge_6 ?_
  refine Iff.trans row9_edge_15 ?_
  refine Iff.trans row9_edge_30 ?_
  refine Iff.trans row9_edge_48 ?_
  refine Iff.trans row9_edge_66 ?_
  refine Iff.trans row9_edge_84 ?_
  refine Iff.trans row9_edge_102 ?_
  refine Iff.trans row9_edge_120 ?_
  refine Iff.trans row9_edge_138 ?_
  refine Iff.trans row9_edge_156 ?_
  refine Iff.trans row9_edge_174 ?_
  refine Iff.trans row9_edge_192 ?_
  refine Iff.trans row9_edge_210 ?_
  refine Iff.trans row9_edge_228 ?_
  refine Iff.trans row9_edge_246 ?_
  refine Iff.trans row9_edge_264 ?_
  refine Iff.trans row9_edge_282 ?_
  refine Iff.trans row9_edge_300 ?_
  refine Iff.trans row9_edge_318 ?_
  refine Iff.trans row9_edge_336 ?_
  refine Iff.trans row9_edge_354 ?_
  refine Iff.trans row9_edge_372 ?_
  refine Iff.trans row9_edge_390 ?_
  refine Iff.trans row9_edge_408 ?_
  refine Iff.trans row9_edge_426 ?_
  refine Iff.trans row9_edge_444 ?_
  refine Iff.trans row9_edge_462 ?_
  refine Iff.trans row9_edge_480 ?_
  refine Iff.trans row9_edge_498 ?_
  refine Iff.trans row9_edge_516 ?_
  refine Iff.trans row9_edge_534 ?_
  refine Iff.trans row9_edge_552 ?_
  refine Iff.trans row9_edge_570 ?_
  refine Iff.trans row9_edge_588 ?_
  refine Iff.trans row9_edge_606 ?_
  refine Iff.trans row9_edge_624 ?_
  refine Iff.trans row9_edge_642 ?_
  refine Iff.trans row9_edge_660 ?_
  refine Iff.trans row9_edge_678 ?_
  refine Iff.trans row9_edge_696 ?_
  refine Iff.trans row9_edge_714 ?_
  refine Iff.trans row9_edge_732 ?_
  refine Iff.trans row9_edge_750 ?_
  refine Iff.trans row9_edge_768 ?_
  refine Iff.trans row9_edge_786 ?_
  refine Iff.trans row9_edge_804 ?_
  refine Iff.trans row9_normal_2233 ?_
  refine Iff.trans row9_normal_2234 ?_
  refine Iff.trans row9_normal_2235 ?_
  refine Iff.trans row9_normal_2236 ?_
  refine Iff.trans row9_normal_2237 ?_
  refine Iff.trans row9_normal_2238 ?_
  refine Iff.trans row9_normal_2239 ?_
  refine Iff.trans row9_normal_2240 ?_
  refine Iff.trans row9_normal_2241 ?_
  refine Iff.trans row9_normal_2242 ?_
  refine Iff.trans row9_normal_2243 ?_
  refine Iff.trans row9_normal_2244 ?_
  refine Iff.trans row9_normal_2245 ?_
  refine Iff.trans row9_normal_2246 ?_
  refine Iff.trans row9_normal_2247 ?_
  refine Iff.trans row9_normal_2248 ?_
  refine Iff.trans row9_normal_2249 ?_
  refine Iff.trans row9_normal_2250 ?_
  refine Iff.trans row9_normal_2251 ?_
  refine Iff.trans row9_normal_2252 ?_
  refine Iff.trans row9_normal_2253 ?_
  refine Iff.trans row9_normal_2254 ?_
  refine Iff.trans row9_normal_2255 ?_
  refine Iff.trans row9_normal_2256 ?_
  refine Iff.trans row9_normal_2257 ?_
  refine Iff.trans row9_normal_2258 ?_
  refine Iff.trans row9_normal_2259 ?_
  refine Iff.trans row9_normal_2260 ?_
  refine Iff.trans row9_normal_2261 ?_
  refine Iff.trans row9_normal_2262 ?_
  refine Iff.trans row9_normal_2263 ?_
  refine Iff.trans row9_normal_2264 ?_
  refine Iff.trans row9_normal_2265 ?_
  refine Iff.trans row9_normal_2266 ?_
  refine Iff.trans row9_normal_2267 ?_
  refine Iff.trans row9_normal_2268 ?_
  refine Iff.trans row9_normal_2269 ?_
  refine Iff.trans row9_normal_2270 ?_
  refine Iff.trans row9_normal_2271 ?_
  refine Iff.trans row9_normal_2272 ?_
  refine Iff.trans row9_normal_2273 ?_
  refine Iff.trans row9_normal_2274 ?_
  refine Iff.trans row9_normal_2275 ?_
  refine Iff.trans row9_normal_2276 ?_
  refine Iff.trans row9_normal_2277 ?_
  refine Iff.trans row9_normal_2278 ?_
  refine Iff.trans row9_normal_2279 ?_
  refine Iff.trans row9_normal_2280 ?_
  refine Iff.trans row9_normal_2281 ?_
  refine Iff.trans row9_normal_2282 ?_
  refine Iff.trans row9_normal_2283 ?_
  refine Iff.trans row9_normal_2284 ?_
  refine Iff.trans row9_normal_2285 ?_
  refine Iff.trans row9_normal_2286 ?_
  refine Iff.trans row9_normal_2287 ?_
  refine Iff.trans row9_normal_2288 ?_
  refine Iff.trans row9_normal_2289 ?_
  refine Iff.trans row9_normal_2290 ?_
  exact Iff.rfl

theorem not_K_3_nil : ¬ K 3 (some []) := by
  rw [row9_selected_path]
  exact selected_numeric_endpoint_nonhalting

theorem T3_never_none (k : Nat) : power (T 3) k (some []) ≠ none := by
  intro hk
  apply not_K_3_nil
  exact (K_T_equiv 3 (some []) (by decide)).mp ⟨k, hk⟩

end Row9

-- ============================================================================
-- Section 13: Physical Turing Machine Embedding (`Row9Machine.v` + `Row9Bridge.v`)
-- ============================================================================

open Row9

def word_tape : word → ListBlank (Fin 2)
  | [] => (1 : Fin 2) >> default
  | g :: u => (1 : Fin 2) >> (([0] : List (Fin 2)) ^ g +> ((1 : Fin 2) >> ((0 : Fin 2) >> word_tape u)))

lemma word_tape_nil : word_tape [] = (1 : Fin 2) >> default := rfl
lemma word_tape_cons (g : Nat) (u : word) :
    word_tape (g :: u) = (1 : Fin 2) >> (([0] : List (Fin 2)) ^ g +> ((1 : Fin 2) >> ((0 : Fin 2) >> word_tape u))) := rfl

def reset (l : ListBlank (Fin 2)) (w : word) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ ([1, 0, 1] : List (Fin 2))) {{B}}> word_tape w)

def scan (k : Nat) (l : ListBlank (Fin 2)) (w : word) : Cfg (Fin 2) (Fin 6) :=
  (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (2 + k)) {{C}}> word_tape w)

lemma word_tape_head (w : word) : ∃ r, word_tape w = (1 : Fin 2) >> r := by
  cases w <;> exact ⟨_, rfl⟩

lemma a_sweep (n : Nat) (l r : ListBlank (Fin 2)) :
    (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ n) <{{A}} r) [target_tm]⊢⁺
    ((l <+ ([1] : List (Fin 2))) {{B}}> (([0] : List (Fin 2)) ^ n +> r)) := by
  induction n generalizing l r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil, listblank_append_cons]
    execute
  | succ n ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : ((((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ n) <+ ([1] : List (Fin 2))) <{{A}} r)
        [target_tm]⊢⁺
        (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ n) <{{A}} ((0 : Fin 2) >> r)) := by
      dsimp -failIfUnchanged [ListBlank.append]
      execute
    have h2 := ih l ((0 : Fin 2) >> r)
    have h_eq : (([0] : List (Fin 2)) ^ n +> ((0 : Fin 2) >> r)) = (([0] : List (Fin 2)) ^ (n + 1) +> r) := by
      rw [cons_eq_singleton_append 0 r, listblank_append_append, list_pow_append_one]
    rw [h_eq] at h2
    exact stepPlus_trans h1 h2

lemma carry (l : ListBlank (Fin 2)) (w : word) (k : Nat) :
    (reset ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (2 + k)) w) [target_tm]⊢⁺
    (reset l (k :: w)) := by
  obtain ⟨r, hr⟩ := word_tape_head w
  unfold reset
  rw [hr]
  have h1 : ((((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (2 + k)) <+ ([1, 0, 1] : List (Fin 2))) {{B}}> ((1 : Fin 2) >> r))
      [target_tm]⊢⁺
      ((((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (2 + k)) <+ ([1] : List (Fin 2))) <{{A}}
        ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> r)))) := by
    dsimp -failIfUnchanged [ListBlank.append]
    execute
  rw [pow_succ_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k)] at h1
  have h2 := a_sweep (2 + k + 1) l ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> r)))
  have h12 := stepPlus_trans h1 h2
  have hk : 2 + k + 1 = 3 + k := by omega
  rw [hk, pow_add_append_right ([0] : List (Fin 2)) 3 k] at h12
  have h3 : ((l <+ ([1] : List (Fin 2))) {{B}}>
      (([0] : List (Fin 2)) ^ 3 +> (([0] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> r))))))
      [target_tm]⊢⁺
      ((l <+ ([1, 0, 1] : List (Fin 2))) {{B}}>
        ((1 : Fin 2) >> (([0] : List (Fin 2)) ^ k +> ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> r)))))) := by
    dsimp -failIfUnchanged [ListBlank.append]
    execute
  have h_tot := stepPlus_trans h12 h3
  rw [word_tape_cons, hr]
  exact h_tot

lemma short_even (l : ListBlank (Fin 2)) (w : word) :
    (reset (l <+ ([0] : List (Fin 2))) w) [target_tm]⊢⁺
    (scan 0 (l <+ ([1] : List (Fin 2))) w) := by
  obtain ⟨r, hr⟩ := word_tape_head w
  unfold reset scan
  rw [hr]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma short_one (l : ListBlank (Fin 2)) (w : word) :
    (reset (l <+ ([1, 0] : List (Fin 2))) w) [target_tm]⊢⁺
    (scan 0 (l <+ ([0, 1] : List (Fin 2))) w) := by
  obtain ⟨r, hr⟩ := word_tape_head w
  unfold reset scan
  rw [hr]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_one (k : Nat) (l : ListBlank (Fin 2)) (u : word) :
    (scan k l (1 :: u)) [target_tm]⊢⁺ (scan (k + 4) l u) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan
  rw [word_tape_cons, hr]
  have hk : 2 + (k + 4) = (2 + k) + 4 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 4]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_two (k : Nat) (l : ListBlank (Fin 2)) (u : word) :
    (scan k l (2 :: u)) [target_tm]⊢⁺
    (scan 0 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) u) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan
  rw [word_tape_cons, hr]
  have hk : 4 + k = (2 + k) + 2 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 2]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_three (k : Nat) (l : ListBlank (Fin 2)) (u : word) :
    (scan k l (3 :: u)) [target_tm]⊢⁺
    (scan 0 (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([0] : List (Fin 2))) u) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan
  rw [word_tape_cons, hr]
  have hk : 4 + k = (2 + k) + 2 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 2]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_zero_one (k : Nat) (l : ListBlank (Fin 2)) (u : word) :
    (scan k l (0 :: 1 :: u)) [target_tm]⊢⁺
    (scan 2 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) u) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan
  rw [word_tape_cons, word_tape_cons, hr]
  have hk : 4 + k = (2 + k) + 2 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 2]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_zero_two (k : Nat) (l : ListBlank (Fin 2)) (u : word) :
    (scan k l (0 :: 2 :: u)) [target_tm]⊢⁺
    (scan 0 (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([1, 1, 0] : List (Fin 2))) u) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan
  rw [word_tape_cons, word_tape_cons, hr]
  have hk : 4 + k = (2 + k) + 2 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 2]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_zero_large (k : Nat) (l : ListBlank (Fin 2)) (g : Nat) (u : word) :
    (scan k l (0 :: (g + 3) :: u)) [target_tm]⊢⁺
    (scan 1 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) (g :: u)) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan
  rw [word_tape_cons, word_tape_cons, word_tape_cons, hr]
  have hk : 4 + k = (2 + k) + 2 := by omega
  have hg : g + 3 = 3 + g := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 2,
      hg, pow_add_append_right ([0] : List (Fin 2)) 3 g]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_zero (k : Nat) (l : ListBlank (Fin 2)) :
    (scan k l [0]) [target_tm]⊢⁺
    (scan 1 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) []) := by
  unfold scan
  rw [word_tape_cons, word_tape_nil]
  have hk : 4 + k = (2 + k) + 2 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 2]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_large (k : Nat) (l : ListBlank (Fin 2)) (g : Nat) (u : word) :
    (scan k l ((g + 4) :: u)) [target_tm]⊢⁺
    (reset ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (3 + k)) (g :: u)) := by
  obtain ⟨r, hr⟩ := word_tape_head u
  unfold scan reset
  rw [word_tape_cons, word_tape_cons, hr]
  have hk : 3 + k = (2 + k) + 1 := by omega
  have hg : g + 4 = 4 + g := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 1,
      hg, pow_add_append_right ([0] : List (Fin 2)) 4 g]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma scan_nil (k : Nat) (l : ListBlank (Fin 2)) :
    (scan k l []) [target_tm]⊢⁺
    (reset ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (3 + k)) []) := by
  unfold scan reset
  rw [word_tape_nil]
  have hk : 3 + k = (2 + k) + 1 := by omega
  rw [hk, pow_add_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (2 + k) 1]
  dsimp -failIfUnchanged [ListBlank.append]
  execute

lemma first_plus_0 (w : word) : first_plus 0 w = w := by
  cases w with
  | nil => rfl
  | cons a u => simp [first_plus]

lemma first_plus_comp (k j : Nat) (w : word) :
    first_plus k (first_plus j w) = first_plus (j + k) w := by
  cases w with
  | nil => rfl
  | cons a u => simp [first_plus, Nat.add_assoc]

lemma scan_nil_return (k : Nat) (l : ListBlank (Fin 2)) :
    (scan k l []) [target_tm]⊢⁺ (reset l [1 + k]) := by
  have h1 := scan_nil k l
  have hk : 3 + k = 2 + (1 + k) := by omega
  rw [hk] at h1
  exact stepPlus_trans h1 (carry l [] (1 + k))

lemma scan_large_return (k : Nat) (l : ListBlank (Fin 2)) (g : Nat) (u : word) :
    (scan k l ((g + 4) :: u)) [target_tm]⊢⁺ (reset l ((1 + k) :: g :: u)) := by
  have h1 := scan_large k l g u
  have hk : 3 + k = 2 + (1 + k) := by omega
  rw [hk] at h1
  exact stepPlus_trans h1 (carry l (g :: u) (1 + k))

theorem eval_embedding_some {u : word} {r : result} (H : Eval u r) :
    ∀ (v : word) (k : Nat) (l : ListBlank (Fin 2)),
      r = some v → (scan k l u) [target_tm]⊢⁺ (reset l (first_plus k v)) := by
  induction H with
  | nil =>
    intro v k l hv; injection hv with hv; subst hv
    exact scan_nil_return k l
  | one h ih =>
    rename_i U r'
    intro v k l hv
    rcases r' with _ | v'
    · cases hv
    · simp only [lift_plus, Option.map] at hv
      injection hv with hv; subst hv
      rw [first_plus_comp]
      have hk : 4 + k = k + 4 := by omega
      rw [hk]
      exact stepPlus_trans (scan_one k l U) (ih v' (k + 4) l rfl)
  | two h ih =>
    rename_i U r'
    intro v k l hv
    rcases r' with _ | v'
    · cases hv
    · simp only [lift_prefix, Option.map, List.singleton_append] at hv
      injection hv with hv; subst hv
      have h1 := scan_two k l U
      have h2 := ih v' 0 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) rfl
      rw [first_plus_0] at h2
      have h3 := carry l v' (2 + k)
      have hk : 2 + (2 + k) = 4 + k := by omega
      rw [hk] at h3
      exact stepPlus_trans (stepPlus_trans h1 h2) h3
  | three_halt _ =>
    intro v k l hv; cases hv
  | three h1 h2 ih1 ih2 =>
    rename_i U V r'
    intro v k l hv
    rcases r' with _ | v'
    · cases hv
    · simp only [lift_prefix, Option.map, List.singleton_append] at hv
      injection hv with hv; subst hv
      have hs1 := scan_three k l U
      have hs2 := ih1 V 0 (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([0] : List (Fin 2))) rfl
      rw [first_plus_0] at hs2
      have hs3 := short_even ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) V
      have hs4 := ih2 v' 0 (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([1] : List (Fin 2))) rfl
      rw [first_plus_0] at hs4
      have hs1234 := stepPlus_trans (stepPlus_trans (stepPlus_trans hs1 hs2) hs3) hs4
      have h_eq : (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([1] : List (Fin 2))) =
          ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (2 + (3 + k))) := by
        rw [pow_succ_append_left (l <+ ([0] : List (Fin 2))) ([1] : List (Fin 2)) (4 + k)]
        have hk : 4 + k + 1 = 2 + (3 + k) := by omega
        rw [hk]
      rw [h_eq] at hs1234
      have hs5 := carry l v' (3 + k)
      exact stepPlus_trans hs1234 hs5
  | large g U =>
    intro v k l hv; injection hv with hv; subst hv
    exact scan_large_return k l g U
  | zero =>
    intro v k l hv; injection hv with hv; subst hv
    have hs1 := scan_zero k l
    have hs2 := scan_nil_return 1 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k))
    have hs3 := carry l [2] (2 + k)
    have hk : 2 + (2 + k) = 4 + k := by omega
    rw [hk] at hs3
    exact stepPlus_trans (stepPlus_trans hs1 hs2) hs3
  | zero_zero _ =>
    intro v k l hv; cases hv
  | zero_one h ih =>
    rename_i U r'
    intro v k l hv
    rcases r' with _ | v'
    · cases hv
    · simp only [lift_prefix, lift_plus, Option.map, List.singleton_append] at hv
      injection hv with hv; subst hv
      have hs1 := scan_zero_one k l U
      have hs2 := ih v' 2 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) rfl
      have hs3 := carry l (first_plus 2 v') (2 + k)
      have hk : 2 + (2 + k) = 4 + k := by omega
      rw [hk] at hs3
      exact stepPlus_trans (stepPlus_trans hs1 hs2) hs3
  | zero_two h ih =>
    rename_i U r'
    intro v k l hv
    rcases r' with _ | v'
    · cases hv
    · simp only [lift_prefix, Option.map] at hv
      injection hv with hv; subst hv
      have hs1 := scan_zero_two k l U
      have hs2 := ih v' 0 (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([1, 1, 0] : List (Fin 2))) rfl
      rw [first_plus_0] at hs2
      have h_eq : (((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([1, 1, 0] : List (Fin 2))) =
          ((((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (2 + 0)) := by
        rw [listblank_append_append]
        rfl
      rw [h_eq] at hs2
      have hs3 := carry ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) v' 0
      have hs4 := carry l (0 :: v') (2 + k)
      have hk : 2 + (2 + k) = 4 + k := by omega
      rw [hk] at hs4
      exact stepPlus_trans (stepPlus_trans (stepPlus_trans hs1 hs2) hs3) hs4
  | zero_large g h ih =>
    rename_i U r'
    intro v k l hv
    rcases r' with _ | v'
    · cases hv
    · simp only [lift_prefix, lift_plus, Option.map, List.singleton_append] at hv
      injection hv with hv; subst hv
      have hs1 := scan_zero_large k l g U
      have hs2 := ih v' 1 ((l <+ ([0] : List (Fin 2))) <+ ([1] : List (Fin 2)) ^ (4 + k)) rfl
      have hs3 := carry l (first_plus 1 v') (2 + k)
      have hk : 2 + (2 + k) = 4 + k := by omega
      rw [hk] at hs3
      exact stepPlus_trans (stepPlus_trans hs1 hs2) hs3

theorem f_embedding_some {u v : word} (h : f u = some v) (k : Nat) (l : ListBlank (Fin 2)) :
    (scan k l u) [target_tm]⊢⁺ (reset l (first_plus k v)) :=
  eval_embedding_some (f_spec u) v k l h

lemma init_to_reset : (init []) [target_tm]⊢⁺ (reset default []) := by
  unfold init reset word_tape
  simp only [Tape.mk₁, Tape.mk₂, Tape.mk', listblank_append_cons, listblank_append_nil,
    zero_cons_default, default_head, default_tail]
  execute

lemma default_append_zero : (default : ListBlank (Fin 2)) <+ ([0] : List (Fin 2)) = default := by
  simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]

lemma short_initial (w : word) :
    (reset default w) [target_tm]⊢⁺ (scan 0 (default <+ ([1] : List (Fin 2))) w) := by
  have h := short_even default w
  rw [default_append_zero] at h
  exact h

lemma short_second (w : word) :
    (reset (default <+ ([1] : List (Fin 2))) w) [target_tm]⊢⁺
    (scan 0 (default <+ ([0, 1] : List (Fin 2))) w) := by
  have h := short_one default w
  have heq : (default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) = default <+ ([1] : List (Fin 2)) := by
    simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]
  rw [heq] at h
  exact h

lemma short_third (w : word) :
    (reset (default <+ ([0, 1] : List (Fin 2))) w) [target_tm]⊢⁺
    (scan 0 (default <+ ([1, 1] : List (Fin 2))) w) := by
  have h := short_even (default <+ ([1] : List (Fin 2))) w
  rw [listblank_append_append, listblank_append_append] at h
  exact h

lemma phase_carry (w : word) :
    (reset (default <+ ([1, 1] : List (Fin 2))) w) [target_tm]⊢⁺
    (reset default (0 :: w)) := by
  have h := carry default w 0
  rw [default_append_zero] at h
  exact h

theorem T3_embedding {w z : word} (h : T 3 (some w) = some z) :
    (reset default w) [target_tm]⊢⁺ (reset default z) := by
  unfold T at h
  simp only [power, opF, bind_res] at h
  rcases h1 : f w with _ | u
  · rw [h1] at h; cases h
  · rw [h1] at h; simp only [bind_res] at h
    rcases h2 : f u with _ | v
    · rw [h2] at h; cases h
    · rw [h2] at h; simp only [bind_res] at h
      rcases h3 : f v with _ | y
      · rw [h3] at h; cases h
      · rw [h3] at h; simp only [Z, pfx, Option.map] at h
        injection h with h; subst h
        have s1 := short_initial w
        have s2 := f_embedding_some h1 0 (default <+ ([1] : List (Fin 2)))
        rw [first_plus_0] at s2
        have s3 := short_second u
        have s4 := f_embedding_some h2 0 (default <+ ([0, 1] : List (Fin 2)))
        rw [first_plus_0] at s4
        have s5 := short_third v
        have s6 := f_embedding_some h3 0 (default <+ ([1, 1] : List (Fin 2)))
        rw [first_plus_0] at s6
        have s7 := phase_carry y
        exact stepPlus_trans (stepPlus_trans (stepPlus_trans (stepPlus_trans (stepPlus_trans (stepPlus_trans s1 s2) s3) s4) s5) s6) s7

noncomputable def T3_word (k : Nat) : word :=
  match h : power (T 3) k (some []) with
  | some w => w
  | none => False.elim (T3_never_none k h)

lemma T3_word_spec (k : Nat) : power (T 3) k (some []) = some (T3_word k) := by
  unfold T3_word
  split
  · rename_i w hw; exact hw.symm ▸ rfl
  · rename_i hnone; exact False.elim (T3_never_none k hnone)

lemma T3_word_zero : T3_word 0 = [] := by
  have h := T3_word_spec 0
  simp only [power] at h
  exact (Option.some.inj h).symm

lemma T3_word_step (k : Nat) : T 3 (some (T3_word k)) = some (T3_word (k + 1)) := by
  have h1 := T3_word_spec k
  have h2 := T3_word_spec (k + 1)
  simp only [power, h1] at h2
  exact h2

-- ============================================================================
-- Section 14: Main Theorem Statement (`holdout_0010_nonhalt`)
-- ============================================================================

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  refine nonhalt_of_chain target_tm (fun k => reset default (T3_word k)) ?_ ?_
  · dsimp -failIfUnchanged only
    rw [T3_word_zero]
    exact stepPlus_stepStar init_to_reset
  · intro k
    exact T3_embedding (T3_word_step k)

end BusyBeaver.M_1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RCHHH
