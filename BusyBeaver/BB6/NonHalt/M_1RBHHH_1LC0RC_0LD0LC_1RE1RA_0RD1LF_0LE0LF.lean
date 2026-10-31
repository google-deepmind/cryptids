/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

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

lemma stepPlus_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, _, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

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
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

lemma rule_E_b (l r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> l) {{E}}> ([0, 1, 0, 0, 0, 1] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> l) {{C}}> ([0, 0, 0, 1, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_aa (l r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> l) {{E}}> ([0, 1, 0, 1, 0, 1] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> ([1, 1, 0, 1] +> l)) {{E}}> ([0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_ab (l r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> l) {{E}}> ([0, 1, 0, 1, 0, 0, 0, 1] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> ([0, 1, 1, 1, 0, 1] +> l)) {{E}}> ([0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_C_a (l r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> ([0, 1] +> l)) {{C}}> ([0, 0] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> l) {{C}}> ([0, 0, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_C_b (l r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> ([1, 1, 0, 1] +> l)) {{C}}> ([0, 0] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> l) {{C}}> ([0, 0, 0, 0, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_C_nil (r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> default) {{C}}> ([0, 0] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> ([0, 1] +> default)) {{E}}> ([0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_end (l : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> l) {{E}}> ([0, 1, 0, 1, 0, 0, 1] +> default)) [target_tm]⊢⁺
    (l {{E}}> ([1, 0, 0, 0, 1, 0, 0, 1] +> default)) := by
  dsimp [ListBlank.append]; execute

lemma rule_EL_a (l r : ListBlank (Fin 2)) :
    (([0, 1] +> l) {{E}}> ((1 : Fin 2) >> r)) [target_tm]⊢⁺
    (l {{E}}> ([1, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_EL_b (l r : ListBlank (Fin 2)) :
    (([1, 1, 0, 1] +> l) {{E}}> ((1 : Fin 2) >> r)) [target_tm]⊢⁺
    (l {{E}}> ([1, 0, 0, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_EL_nil (r : ListBlank (Fin 2)) :
    (default {{E}}> ((1 : Fin 2) >> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> default) {{E}}> ([0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

abbrev T0 : List (Fin 2) := [0, 0, 0, 1]
abbrev T1 : List (Fin 2) := [0, 1, 0, 1]
abbrev T2 : List (Fin 2) := [0, 1, 0, 0, 0, 1]

abbrev RoundC (r r' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    (((1 : Fin 2) >> l) {{E}}> ([0, 1] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> l) {{C}}> ([0, 0] +> r'))

abbrev RoundA (r r_out : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    (((1 : Fin 2) >> ([0, 1] +> l)) {{E}}> ([0, 1] +> r)) [target_tm]⊢⁺
    (((1 : Fin 2) >> l) {{C}}> ([0, 0] +> r_out))

lemma roundC_to_roundA {r r' : ListBlank (Fin 2)} (h : RoundC r r') :
    RoundA r ([0, 1] +> r') :=
  fun l => stepPlus_trans (h ([0, 1] +> l)) (rule_C_a l r')

lemma roundC_T0 (u : ListBlank (Fin 2)) :
    RoundC (T0 +> u) (T1 +> u) :=
  fun l => rule_E_b l u

lemma roundA_T0 (u : ListBlank (Fin 2)) :
    RoundA (T0 +> u) (T1 +> ([0, 1] +> u)) :=
  roundC_to_roundA (roundC_T0 u)

lemma roundC_T1 {u u' : ListBlank (Fin 2)} (h : RoundC u u') :
    RoundC (T1 +> u) (T0 +> u') :=
  fun l => stepPlus_trans (rule_E_aa l u) (stepPlus_trans (h ([1, 1, 0, 1] +> l)) (rule_C_b l u'))

lemma roundA_T1 {u u' : ListBlank (Fin 2)} (h : RoundC u u') :
    RoundA (T1 +> u) (T2 +> u') :=
  roundC_to_roundA (roundC_T1 h)

lemma roundC_T2 {u u' : ListBlank (Fin 2)} (h : RoundA u u') :
    RoundC (T2 +> u) (T0 +> u') :=
  fun l => stepPlus_trans (rule_E_ab l u) (stepPlus_trans (h ([1, 1, 0, 1] +> l)) (rule_C_b l u'))

lemma roundA_T2 {u u' : ListBlank (Fin 2)} (h : RoundA u u') :
    RoundA (T2 +> u) (T2 +> u') :=
  roundC_to_roundA (roundC_T2 h)

abbrev RoundE (r r' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    (((1 : Fin 2) >> l) {{E}}> ([0, 1] +> r)) [target_tm]⊢⁺
    (l {{E}}> ((1 : Fin 2) >> r'))

abbrev RoundEA (r r_out : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    (((1 : Fin 2) >> ([0, 1] +> l)) {{E}}> ([0, 1] +> r)) [target_tm]⊢⁺
    (l {{E}}> ((1 : Fin 2) >> r_out))

lemma roundE_to_roundEA {r r' : ListBlank (Fin 2)} (h : RoundE r r') :
    RoundEA r ([0, 1] +> r') :=
  fun l => stepPlus_trans (h ([0, 1] +> l)) (rule_EL_a l r')

lemma roundE_end :
    RoundE ([0, 1, 0, 0, 1] +> default) ([0, 0, 0, 1, 0, 0, 1] +> default) :=
  fun l => rule_E_end l

lemma roundE_T1 {u u' : ListBlank (Fin 2)} (h : RoundE u u') :
    RoundE (T1 +> u) (T0 +> u') :=
  fun l => stepPlus_trans (rule_E_aa l u) (stepPlus_trans (h ([1, 1, 0, 1] +> l)) (rule_EL_b l u'))

lemma roundEA_T1 {u u' : ListBlank (Fin 2)} (h : RoundE u u') :
    RoundEA (T1 +> u) (T2 +> u') :=
  roundE_to_roundEA (roundE_T1 h)

lemma roundE_T2 {u u' : ListBlank (Fin 2)} (h : RoundEA u u') :
    RoundE (T2 +> u) (T0 +> u') :=
  fun l => stepPlus_trans (rule_E_ab l u) (stepPlus_trans (h ([1, 1, 0, 1] +> l)) (rule_EL_b l u'))

lemma roundEA_T2 {u u' : ListBlank (Fin 2)} (h : RoundEA u u') :
    RoundEA (T2 +> u) (T2 +> u') :=
  roundE_to_roundEA (roundE_T2 h)

abbrev cfgE0 (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> ([0, 1] +> default)) {{E}}> ([0, 1] +> r)

lemma sweep_step {r r_out : ListBlank (Fin 2)} (h : RoundA r r_out) :
    (cfgE0 r) [target_tm]⊢⁺ (cfgE0 r_out) :=
  stepPlus_trans (h default) (rule_C_nil r_out)

lemma era_end_step {r r_era r_next : ListBlank (Fin 2)}
    (h₁ : RoundEA r r_era) (h₂ : RoundC r_era r_next) :
    (cfgE0 r) [target_tm]⊢⁺ (cfgE0 r_next) :=
  stepPlus_trans (h₁ default)
    (stepPlus_trans (rule_EL_nil r_era)
      (stepPlus_trans (h₂ default) (rule_C_nil r_next)))

abbrev bot : ListBlank (Fin 2) := [0, 0, 1] +> default
abbrev bota : ListBlank (Fin 2) := [0, 1, 0, 0, 1] +> default
abbrev botc : ListBlank (Fin 2) := [0, 1, 1] +> default

lemma roundC_bot : RoundC bot botc := by
  intro l; dsimp [bot, botc, ListBlank.append]; execute

lemma roundC_botc : RoundC botc bot := by
  intro l; dsimp [bot, botc, ListBlank.append]; execute

inductive StepsA : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop where
  | zero (u : ListBlank (Fin 2)) : StepsA 0 u u
  | succ {n : ℕ} {u v w : ListBlank (Fin 2)} :
      RoundA u v → StepsA n v w → StepsA (n + 1) u w

lemma stepsA_trans {a b : ℕ} {u v w : ListBlank (Fin 2)}
    (h1 : StepsA a u v) (h2 : StepsA b v w) : StepsA (a + b) u w := by
  induction h1 with
  | zero => rw [Nat.zero_add]; exact h2
  | succ h _ ih => rw [Nat.succ_add]; exact StepsA.succ h (ih h2)

lemma stepsA_T2 {n : ℕ} {u w : ListBlank (Fin 2)} (h : StepsA n u w) :
    StepsA n (T2 +> u) (T2 +> w) := by
  induction h with
  | zero u => exact StepsA.zero (T2 +> u)
  | succ h1 _ ih => exact StepsA.succ (roundA_T2 h1) ih

abbrev B3 (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  T2 +> (T2 +> (T2 +> r))

def powB3 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | m + 1, r => B3 (powB3 m r)

lemma powB3_B3 (m : ℕ) (r : ListBlank (Fin 2)) :
    powB3 m (B3 r) = B3 (powB3 m r) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg B3 ih

lemma powB3_T2 (m : ℕ) (r : ListBlank (Fin 2)) :
    powB3 m (T2 +> r) = T2 +> powB3 m r := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg B3 ih

lemma roundA_B3 {u u' : ListBlank (Fin 2)} (h : RoundA u u') :
    RoundA (B3 u) (B3 u') :=
  roundA_T2 (roundA_T2 (roundA_T2 h))

lemma roundA_powB3 (m : ℕ) {u u' : ListBlank (Fin 2)} (h : RoundA u u') :
    RoundA (powB3 m u) (powB3 m u') := by
  induction m with
  | zero => exact h
  | succ m ih => exact roundA_B3 ih

lemma roundEA_B3 {u u' : ListBlank (Fin 2)} (h : RoundEA u u') :
    RoundEA (B3 u) (B3 u') :=
  roundEA_T2 (roundEA_T2 (roundEA_T2 h))

lemma roundEA_powB3 (m : ℕ) {u u' : ListBlank (Fin 2)} (h : RoundEA u u') :
    RoundEA (powB3 m u) (powB3 m u') := by
  induction m with
  | zero => exact h
  | succ m ih => exact roundEA_B3 ih

lemma stepsA_B3 {n : ℕ} {u w : ListBlank (Fin 2)} (h : StepsA n u w) :
    StepsA n (B3 u) (B3 w) :=
  stepsA_T2 (stepsA_T2 (stepsA_T2 h))

lemma stepsA_powB3 (m : ℕ) {n : ℕ} {u w : ListBlank (Fin 2)} (h : StepsA n u w) :
    StepsA n (powB3 m u) (powB3 m w) := by
  induction m with
  | zero => exact h
  | succ m ih => exact stepsA_B3 ih

lemma step6_022 {v v_C : ListBlank (Fin 2)} (hC : RoundC v v_C) :
    StepsA 6 (T0 +> (T2 +> (T2 +> v))) (B3 (T0 +> (T2 +> v_C))) := by
  refine StepsA.succ (roundA_T0 (T2 +> (T2 +> v))) ?_
  refine StepsA.succ (roundA_T1 (roundC_T1 (roundC_T0 (T2 +> v)))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T0 (T1 +> (T2 +> v)))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 v))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T1 +> v))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 hC))))) ?_
  exact StepsA.zero _

lemma finish8_22 {v v_C : ListBlank (Fin 2)} (hC : RoundC v v_C) :
    StepsA 8 (T0 +> (T2 +> (T2 +> v))) (B3 (T2 +> (T0 +> (T1 +> v_C)))) := by
  have h2 : StepsA 2 (T0 +> (T2 +> v_C)) (T2 +> (T0 +> (T1 +> v_C))) := by
    refine StepsA.succ (roundA_T0 (T2 +> v_C)) ?_
    refine StepsA.succ (roundA_T1 (roundC_T1 (roundC_T0 v_C))) ?_
    exact StepsA.zero _
  exact stepsA_trans (step6_022 hC) (stepsA_B3 h2)

lemma cross_B3 {u u1 u2 u3 : ListBlank (Fin 2)}
    (h1 : RoundA u u1) (h2 : RoundA u1 u2) (h3 : RoundA u2 u3) :
    StepsA 12 (T0 +> B3 u) (B3 (B3 (T0 +> u3))) := by
  have h4 : StepsA 4 (T0 +> (T1 +> (T0 +> u1))) (T2 +> (T2 +> (T0 +> u3))) := by
    refine StepsA.succ (roundA_T0 (T1 +> (T0 +> u1))) ?_
    refine StepsA.succ (roundA_T1 (roundC_T1 (roundC_T2 h2))) ?_
    refine StepsA.succ (roundA_T2 (roundA_T0 (T0 +> u2))) ?_
    refine StepsA.succ (roundA_T2 (roundA_T1 (roundC_T2 h3))) ?_
    exact StepsA.zero _
  exact stepsA_trans (finish8_22 (roundC_T2 h1)) (stepsA_B3 (stepsA_T2 h4))

lemma cross_powB3 (m : ℕ) {u w : ListBlank (Fin 2)} (h : StepsA (3 * m) u w) :
    StepsA (12 * m) (T0 +> powB3 m u) (powB3 (2 * m) (T0 +> w)) := by
  induction m generalizing u with
  | zero =>
    cases h
    exact StepsA.zero _
  | succ m ih =>
    cases h with
    | succ h1 h =>
      cases h with
      | succ h2 h =>
        cases h with
        | succ h3 hrest =>
          have hc := cross_B3 (roundA_powB3 m h1) (roundA_powB3 m h2) (roundA_powB3 m h3)
          have hrec := stepsA_B3 (stepsA_B3 (ih hrest))
          have htot := stepsA_trans hc hrec
          rw [Nat.add_comm 12 (12 * m)] at htot
          exact htot

def fEra (k : ℕ) (u : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  T2 +> powB3 (k + 1) (T1 +> (T1 +> u))

inductive StepEra (k : ℕ) (u w : ListBlank (Fin 2)) : Prop where
  | mk (u_E w_0 w_last v_C : ListBlank (Fin 2))
      (hE : RoundE u u_E)
      (hC0 : RoundC ([0, 1] +> u_E) w_0)
      (hA : StepsA (3 * k + 2) w_0 w_last)
      (hClast : RoundC w_last v_C)
      (hw : w = [0, 1] +> v_C) : StepEra k u w

lemma stepEra_next {k : ℕ} {u w : ListBlank (Fin 2)} (h : StepEra k u w) :
    StepEra (2 * (2 * k + 2) + 2) (fEra k u) (fEra (2 * k + 2) w) := by
  rcases h with ⟨u_E, w_0, w_last, v_C, hE, hC0, hA, hClast, hw⟩
  refine StepEra.mk
    (T0 +> powB3 (k + 1) (T2 +> (T0 +> u_E)))
    (T0 +> powB3 (k + 1) (T2 +> (T1 +> ([0, 1] +> u_E))))
    (T2 +> powB3 (2 * k + 3) (T0 +> (T1 +> v_C)))
    (T0 +> powB3 (2 * k + 3) (T1 +> (T1 +> w)))
    (roundE_T2 (roundEA_powB3 (k + 1) (roundEA_T1 (roundE_T1 hE))))
    (roundC_T2 (roundA_powB3 (k + 1) (roundA_T2 (roundA_T0 u_E))))
    ?_
    ?_
    rfl
  · have h3 : StepsA (3 * (k + 1)) (T2 +> (T1 +> ([0, 1] +> u_E))) (T2 +> (T2 +> w_last)) :=
      stepsA_T2 (StepsA.succ (roundA_T1 hC0) (stepsA_T2 hA))
    have hcross := cross_powB3 (k + 1) h3
    have hfin := stepsA_powB3 (2 * (k + 1)) (finish8_22 hClast)
    have htot := stepsA_trans hcross hfin
    have heq_t :
        powB3 (2 * (k + 1)) (B3 (T2 +> (T0 +> (T1 +> v_C)))) =
        T2 +> powB3 (2 * k + 3) (T0 +> (T1 +> v_C)) := by
      rw [powB3_B3]
      change powB3 (2 * k + 3) (T2 +> (T0 +> (T1 +> v_C))) = _
      exact powB3_T2 (2 * k + 3) (T0 +> (T1 +> v_C))
    have heq_n : 12 * (k + 1) + 8 = 3 * (2 * (2 * k + 2) + 2) + 2 := by omega
    rw [heq_t, heq_n] at htot
    exact htot
  · rw [hw]
    exact roundC_T2 (roundA_powB3 (2 * k + 3) (roundA_T0 (T1 +> v_C)))

abbrev u_m2 : ListBlank (Fin 2) :=
  T2 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))

abbrev u_m1 : ListBlank (Fin 2) :=
  T2 +> (T2 +> (T2 +> (T2 +> (T1 +> (T2 +> (T1 +> (T2 +> (T2 +> (T1 +> bota)))))))))

lemma stepEra_m2 : StepEra 2 u_m2 u_m1 := by
  refine StepEra.mk
    (T0 +> (T2 +> (T0 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))
    (T0 +> (T2 +> (T1 +> (T1 +> (T0 +> (T2 +> (T2 +> (T0 +> bot))))))))
    (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> (T0 +> (T1 +> (T2 +> (T2 +> (T1 +> bota))))))))))
    (T0 +> (T2 +> (T2 +> (T2 +> (T1 +> (T2 +> (T1 +> (T2 +> (T2 +> (T1 +> bota))))))))))
    (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end))))))
    (roundC_T2 (roundA_T2 (roundA_T0 (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))
    ?_
    (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T1 +> (T2 +> (T2 +> (T1 +> bota))))))))))
    rfl
  refine StepsA.succ (roundA_T0 (T2 +> (T1 +> (T1 +> (T0 +> (T2 +> (T2 +> (T0 +> bot)))))))) ?_
  refine StepsA.succ (roundA_T1 (roundC_T1 (roundC_T0 (T1 +> (T1 +> (T0 +> (T2 +> (T2 +> (T0 +> bot))))))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T0 (T1 +> (T1 +> (T1 +> (T0 +> (T2 +> (T2 +> (T0 +> bot))))))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T0 +> (T0 +> (T2 +> (T2 +> (T1 +> bota))))))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T0 (T0 +> (T2 +> (T2 +> (T1 +> bota))))))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))) ?_
  refine StepsA.succ (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T2 +> (T2 +> (T1 +> bota)))))))))) ?_
  exact StepsA.zero _

lemma stepEra_m1 : StepEra 6 u_m1 (fEra 2 u_m2) := by
  refine StepEra.mk
    (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> (T2 +> (T0 +> (T2 +> (T2 +> (T0 +> bot)))))))))))
    (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T0 +> bot))))))))))))
    (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> (T1 +> (T0 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))))
    (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> (T1 +> (T2 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))))
    (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T1 roundE_end))))))))))
    (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 +> (T0 +> (T2 +> (T2 +> (T0 +> bot)))))))))))
    ?_
    (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> (T0 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))))
    rfl
  have hc12 := cross_B3
    (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 +> (T2 +> (T2 +> (T0 +> bot))))))))
    (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> (T0 +> (T2 +> (T2 +> (T0 +> bot))))))))
    (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))
  have hf8 := stepsA_B3 (stepsA_B3 (finish8_22 (roundC_T2 (roundA_T0 (T0 +> (T2 +> (T2 +> (T1 +> bota))))))))
  have htot := stepsA_trans hc12 hf8
  exact htot

lemma stepsA_run {n : ℕ} {u v w : ListBlank (Fin 2)}
    (h1 : (cfgE0 u) [target_tm]⊢⁺ (cfgE0 v)) (h2 : StepsA n v w) :
    (cfgE0 u) [target_tm]⊢⁺ (cfgE0 w) := by
  induction h2 generalizing u with
  | zero => exact h1
  | succ ha _ ih => exact ih (stepPlus_trans h1 (sweep_step ha))

lemma stepEra_run {k : ℕ} {u w : ListBlank (Fin 2)} (h : StepEra k u w) :
    (cfgE0 u) [target_tm]⊢⁺ (cfgE0 w) := by
  rcases h with ⟨u_E, w_0, w_last, v_C, hE, hC0, hA, hClast, hw⟩
  rw [hw]
  have h0 : (cfgE0 u) [target_tm]⊢⁺ (cfgE0 w_0) :=
    era_end_step (roundE_to_roundEA hE) hC0
  have h1 : (cfgE0 u) [target_tm]⊢⁺ (cfgE0 w_last) :=
    stepsA_run h0 hA
  exact stepPlus_trans h1 (sweep_step (roundC_to_roundA hClast))

lemma init_to_botc : (init []) [target_tm]⊢⁺ (cfgE0 botc) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  dsimp [cfgE0, botc, ListBlank.append]
  execute; exists 0

lemma botc_to_u0 : (cfgE0 botc) [target_tm]⊢⁺ (cfgE0 (fEra 2 u_m2)) := by
  refine stepPlus_trans (sweep_step (roundC_to_roundA roundC_botc)) ?_
  refine stepPlus_trans (era_end_step (roundE_to_roundEA roundE_end) (roundC_T2 (roundC_to_roundA roundC_bot))) ?_
  refine stepPlus_trans (sweep_step (roundA_T0 ([0, 1] +> botc))) ?_
  refine stepPlus_trans (sweep_step (roundA_T1 (roundC_T1 roundC_botc))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T0 bot))) ?_
  refine stepPlus_trans (era_end_step (roundEA_T2 (roundEA_T1 roundE_end)) (roundC_T2 (roundA_T2 (roundA_T0 bot)))) ?_
  refine stepPlus_trans (sweep_step (roundA_T0 (T2 +> (T1 +> bota)))) ?_
  refine stepPlus_trans (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T1 +> bota))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T0 (T1 +> (T1 +> bota))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T1 roundC_bot)))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T0 +> botc)))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T0 botc)))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> ([0, 1] +> botc))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 roundC_botc))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> bot))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundC_to_roundA roundC_bot)))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 ([0, 1] +> botc)))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 roundC_botc)))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot)))))))) ?_
  refine stepPlus_trans (era_end_step (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end))))))) (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T0 (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T0 (T1 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T1 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))) ?_
  refine stepPlus_trans (era_end_step (roundEA_T2 (roundEA_T2 (roundEA_T1 (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))))))) (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T0 (T2 +> (T2 +> (T1 +> (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T2 +> (T1 +> (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T0 (T1 +> (T2 +> (T1 +> (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T1 +> (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T1 +> (T1 +> (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 +> (T0 +> (T0 +> (T1 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 +> (T0 +> (T1 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> (T0 +> (T0 +> (T1 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T0 (T1 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T1 +> (T1 +> (T2 +> (T2 +> (T2 +> (T2 +> (T2 +> (T0 +> bot)))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot)))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> (T0 +> (T0 +> (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T0 (T2 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 +> (T1 +> (T1 +> (T0 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 +> (T0 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))))))))))) ?_
  refine stepPlus_trans (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota))))))))))))))))))) ?_
  exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 +> (T0 +> (T1 +> (T2 +> (T2 +> (T2 +> (T1 +> bota)))))))))))))))))))

lemma multiStep_step_isSome {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₀ cfg cfg' : Cfg Γ Λ) (n m : Nat)
    (hn : multiStep M c₀ n = some cfg)
    (hnm : multiStep M c₀ (n + (1 + m)) = some cfg') :
    (step M cfg).isSome := by
  rw [multiStep_add M c₀ n (1 + m), hn] at hnm
  dsimp [Option.bind] at hnm
  rw [multiStep_add M cfg 1 m, multiStep_one] at hnm
  cases hs : step M cfg with
  | none =>
    rw [hs] at hnm
    nomatch hnm
  | some c₁ => rfl

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
    IsDoesNotHalt M := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome M (init []) cfg cfg' n m hn hnm

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine closed_inv_does_not_halt target_tm
    (fun cfg => ∃ (k : ℕ) (u w : ListBlank (Fin 2)),
      cfg = cfgE0 u ∧ StepEra k u w ∧ StepEra (2 * k + 2) w (fEra k u))
    ⟨cfgE0 (fEra 2 u_m2), stepPlus_stepStar (stepPlus_trans init_to_botc botc_to_u0),
      ⟨14, fEra 2 u_m2, fEra 6 u_m1, rfl, stepEra_next stepEra_m2, stepEra_next stepEra_m1⟩⟩
    ?_
  intro cfg ⟨k, u, w, hcfg, h1, h2⟩
  subst hcfg
  exact ⟨cfgE0 w, stepEra_run h1, ⟨2 * k + 2, w, fEra k u, rfl, h2, stepEra_next h1⟩⟩

end BusyBeaver.M_1RBHHH_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF
