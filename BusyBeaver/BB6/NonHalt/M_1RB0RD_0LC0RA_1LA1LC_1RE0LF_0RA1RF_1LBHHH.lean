/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

local infixr:67 (priority := high) " >> " => (ListBlank.cons : Fin 2 → ListBlank (Fin 2) → ListBlank (Fin 2))
local notation3 (priority := high) l " {{" q "}}> " r =>
  (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg (Fin 2) (Fin 6))
local notation3 (priority := high) l " <{{" q "}} " r =>
  (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg (Fin 2) (Fin 6))

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : ListBlank (Fin 2)).head = (0 : Fin 2) := rfl
@[simp] lemma zDt : (default : ListBlank (Fin 2)).tail = default := rfl

lemma zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]
lemma zSp2 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, zSm tm c₁ c₂ h⟩
lemma zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c3) :
    c₁ [tm]⊢^{n+m} c3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma q7 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c₁ c₂ c3 n m hn hm⟩
lemma zSsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 :=
  q7 (zSp2 tm c₁ c₂ h₁) h₂

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine zSsp (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zZcd, zDh, zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

/-- General invariant theorem for `IsNotHalt`. -/
lemma isNotHalt_of_invariant {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ c₀, ((init []) [M]⊢⁺ c₀) ∧ Inv c₀)
    (h_step : ∀ c, Inv c → ∃ c', (c [M]⊢⁺ c') ∧ Inv c') :
    IsNotHalt M := by
  rcases h_init with ⟨c₀, ⟨n₀, _, hn₀⟩, hinv₀⟩
  exact BusyBeaver.Counter.does_not_halt_of_invariant Inv ⟨c₀, ⟨n₀, hn₀⟩, hinv₀⟩ h_step

-- Composite mode transitions for #303 (mirror of #559)
lemma tr_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢⁺ c₂) (h₂ : c₂ [target_tm]⊢⁺ c₃) : c₁ [target_tm]⊢⁺ c₃ :=
  q7 h₁ (zPs h₂)

lemma tr_init_18 :
    (init []) [target_tm]⊢⁺ (default {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> default)) := by
  change (default {{A}}> default) [target_tm]⊢⁺ _
  execute

lemma tr_L0_A (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (0 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    (B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)) := by execute

lemma tr_L0_B (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (0 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X)) := by execute

lemma tr_L10_A (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X)) := by execute

lemma tr_L10_B (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> X)) := by execute

lemma tr_L10_bot10 (B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> default)) [target_tm]⊢⁺
    ((0 >> 0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> default)) := by execute

lemma tr_L1010_A (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X)) := by execute

lemma tr_L1010_B (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X)) := by execute

lemma tr_L1010_bot10 (B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> default)) [target_tm]⊢⁺
    ((0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> default)) := by execute

lemma tr_R11_emp (X : ListBlank (Fin 2)) :
    (default {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 1 >> default) {{A}}> (0 >> X)) := by execute

lemma tr_R11_01 (X : ListBlank (Fin 2)) :
    ((0 >> 1 >> default) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> default) {{A}}> (1 >> 0 >> 1 >> 0 >> X)) := by execute

lemma tr_R11_0101 (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    (B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)) := by execute

lemma tr_R11_001 (X B_r : ListBlank (Fin 2)) :
    ((0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    (B_r {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> X)) := by execute

lemma tr_R11_0011 (X B_r : ListBlank (Fin 2)) :
    ((0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> B_r) {{A}}> (1 >> 0 >> X)) := by execute

lemma tr_R11_00001 (X B_r : ListBlank (Fin 2)) :
    ((0 >> 0 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X)) := by execute

lemma tr_R11_1_B (X B_r : ListBlank (Fin 2)) :
    ((1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X)) := by execute

lemma tr_L0_BB (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X)) :=
  tr_trans (tr_L0_B (1 >> 0 >> 1 >> 0 >> X) B_r) (tr_L0_B X (0 >> 1 >> 0 >> 1 >> B_r))

lemma tr_L10_BB (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> X)) :=
  tr_trans (tr_L10_B (1 >> 0 >> 1 >> 0 >> X) B_r) (tr_L10_B X (0 >> 0 >> 1 >> 1 >> B_r))

lemma tr_L1010_BB (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X)) :=
  tr_trans (tr_L1010_B (1 >> 0 >> 1 >> 0 >> X) B_r) (tr_L1010_B X (0 >> 0 >> 1 >> 1 >> B_r))

lemma tr_R11_0011_emp (X : ListBlank (Fin 2)) :
    ((0 >> 0 >> 1 >> 1 >> default) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> default) {{A}}> (1 >> 0 >> X)) := by
  simpa only [zZcd] using tr_R11_0011 X default

lemma tr_R11_0101_pair (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X)) [target_tm]⊢⁺
    (B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)) :=
  tr_trans (tr_R11_0101 X (0 >> 1 >> 0 >> 1 >> B_r)) (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) B_r)

lemma tr_R11_01_B (X : ListBlank (Fin 2)) :
    ((0 >> 1 >> default) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> 1 >> default) {{A}}> (1 >> 0 >> 1 >> 0 >> X)) :=
  tr_trans (tr_R11_01 (1 >> 0 >> 1 >> 0 >> X)) (tr_L1010_B X default)

lemma tr_R11_01011_B (X B_r : ListBlank (Fin 2)) :
    ((0 >> 1 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)) [target_tm]⊢⁺
    ((0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X)) :=
  tr_trans (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) (1 >> B_r))
    (tr_trans (tr_R11_1_B (1 >> 0 >> 1 >> 0 >> X) B_r) (tr_L10_B X (0 >> 0 >> 1 >> B_r)))

-- Closed two-stack grammar and inductive invariant for #303
inductive StackL : Nat → ListBlank (Fin 2) → Prop
  | bot10 : StackL 0 (1 >> 0 >> default)
  | pushA {a X} : StackL a X → StackL (a + 1) (0 >> 1 >> 0 >> X)
  | pushBB {a X} : StackL a X → StackL a (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X)

inductive StackR : Nat → ListBlank (Fin 2) → Prop
  | emp {a} : StackR (a + 1) default
  | c0011_emp {a} : StackR a (0 >> 0 >> 1 >> 1 >> default)
  | c001 {a B} : StackR (a + 1) B → StackR a (0 >> 0 >> 1 >> B)
  | c0011_001 {a B} : StackR (a + 1) B → StackR a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B)
  | c0011_0011 {a B} : StackR a B → StackR a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B)
  | c00001 {a B} : StackR a B → StackR (a + 1) (0 >> 0 >> 0 >> 0 >> 1 >> B)
  | c000011 {a B} : StackR a B → StackR (a + 1) (0 >> 0 >> 0 >> 0 >> 1 >> 1 >> B)

lemma StackR.weaken {a B} (h : StackR a B) : StackR (a + 1) B := by
  induction h with
  | emp => exact StackR.emp
  | c0011_emp => exact StackR.c0011_emp
  | c001 _ ih => exact StackR.c001 ih
  | c0011_001 _ ih => exact StackR.c0011_001 ih
  | c0011_0011 _ ih => exact StackR.c0011_0011 ih
  | c00001 _ ih => exact StackR.c00001 ih
  | c000011 _ ih => exact StackR.c000011 ih

inductive StackR1010 : Nat → ListBlank (Fin 2) → Prop
  | emp {a} : StackR1010 (a + 1) default
  | c0011_emp {a} : StackR1010 (a + 1) (0 >> 0 >> 1 >> 1 >> default)
  | c001 {a B} : StackR1010 (a + 1) B → StackR1010 a (0 >> 0 >> 1 >> B)
  | c0011_0011 {a B} : StackR1010 a B → StackR1010 a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B)

lemma StackR1010.toStackR {a B} (h : StackR1010 a B) : StackR a B := by
  induction h with
  | emp => exact StackR.emp
  | c0011_emp => exact StackR.c0011_emp
  | c001 _ ih => exact StackR.c001 ih
  | c0011_0011 _ ih => exact StackR.c0011_0011 ih

lemma StackR1010.push0011 {a B} (h : StackR1010 a B) : StackR a (0 >> 0 >> 1 >> 1 >> B) := by
  induction h with
  | emp => exact StackR.c0011_emp
  | c0011_emp => exact StackR.c0011_0011 StackR.emp
  | c001 h' _ => exact StackR.c0011_001 h'.toStackR
  | c0011_0011 _ ih => exact StackR.c0011_0011 ih

inductive PopTarget : Nat → ListBlank (Fin 2) → Prop
  | emp {a} : PopTarget a (0 >> 1 >> default)
  | c0101 {a B_0} : StackR a B_0 → PopTarget a (0 >> 1 >> 0 >> 1 >> B_0)
  | c01011 {a B_0} : StackR a B_0 → PopTarget a (0 >> 1 >> 0 >> 1 >> 1 >> B_0)

inductive R0101 : Nat → ListBlank (Fin 2) → Prop
  | base {a B} : PopTarget a B → R0101 a B
  | step {a B} : R0101 a B → R0101 a (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B)

inductive Inv : Cfg (Fin 2) (Fin 6) → Prop
  | Mode_L0 {a X B} : StackL (a + 1) X → R0101 a B → Inv ((0 >> 1 >> B) {{A}}> (0 >> X))
  | Mode_L10 {a X B} : StackL a X → StackR (a + 2) B → Inv ((0 >> 1 >> B) {{A}}> (1 >> 0 >> X))
  | Mode_L1010 {a X B} : StackL a X → StackR1010 (a + 1) B → Inv ((0 >> 1 >> B) {{A}}> (1 >> 0 >> 1 >> 0 >> X))
  | Mode_R11 {a X B} : StackL a X → StackR a B → Inv (B {{A}}> (1 >> 1 >> X))
  | Mode_R11_pop {a X B} : StackL a X → R0101 a B → Inv (B {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X))

lemma step_Inv : ∀ c, Inv c → ∃ c', (c [target_tm]⊢⁺ c') ∧ Inv c' := by
  intro c hc
  cases hc with
  | Mode_L0 hX hB =>
    cases hX with
    | pushA hX' =>
      exact ⟨_, tr_L0_A _ _, Inv.Mode_R11_pop hX' hB⟩
    | pushBB hX' =>
      exact ⟨_, tr_L0_BB _ _, Inv.Mode_L0 hX' (R0101.step hB)⟩
  | Mode_L10 hX hB =>
    cases hX with
    | bot10 =>
      exact ⟨_, tr_L10_bot10 _, Inv.Mode_R11 StackL.bot10 (StackR.c001 (StackR.c001 hB))⟩
    | pushA hX' =>
      exact ⟨_, tr_L10_A _ _, Inv.Mode_L10 hX' (StackR.c001 hB)⟩
    | pushBB hX' =>
      exact ⟨_, tr_L10_BB _ _, Inv.Mode_L10 hX' (StackR.c0011_0011 hB)⟩
  | Mode_L1010 hX hB =>
    cases hX with
    | bot10 =>
      exact ⟨_, tr_L1010_bot10 _, Inv.Mode_R11 StackL.bot10 (StackR.c001 hB.push0011)⟩
    | pushA hX' =>
      exact ⟨_, tr_L1010_A _ _, Inv.Mode_L1010 hX' (StackR1010.c001 hB)⟩
    | pushBB hX' =>
      exact ⟨_, tr_L1010_BB _ _, Inv.Mode_L1010 hX' (StackR1010.c0011_0011 hB)⟩
  | Mode_R11 hX hB =>
    cases hB with
    | emp =>
      exact ⟨_, tr_R11_emp _, Inv.Mode_L0 hX (R0101.base PopTarget.emp)⟩
    | c0011_emp =>
      exact ⟨_, tr_R11_0011_emp _, Inv.Mode_L10 hX StackR.emp⟩
    | c001 hB' =>
      exact ⟨_, tr_R11_001 _ _, Inv.Mode_R11 (StackL.pushA hX) hB'⟩
    | c0011_001 hB' =>
      exact ⟨_, tr_R11_0011 _ _, Inv.Mode_L10 hX (StackR.c00001 hB')⟩
    | c0011_0011 hB' =>
      exact ⟨_, tr_R11_0011 _ _, Inv.Mode_L10 hX (StackR.c000011 hB'.weaken)⟩
    | c00001 hB' =>
      exact ⟨_, tr_R11_00001 _ _, Inv.Mode_L0 hX (R0101.base (PopTarget.c0101 hB'))⟩
    | c000011 hB' =>
      exact ⟨_, tr_R11_00001 _ _, Inv.Mode_L0 hX (R0101.base (PopTarget.c01011 hB'))⟩
  | Mode_R11_pop hX hB =>
    cases hB with
    | step hB' =>
      exact ⟨_, tr_R11_0101_pair _ _, Inv.Mode_R11_pop (StackL.pushBB hX) hB'⟩
    | base hT =>
      cases hT with
      | emp =>
        exact ⟨_, tr_R11_01_B _, Inv.Mode_L1010 hX StackR1010.c0011_emp⟩
      | c0101 hB' =>
        exact ⟨_, tr_R11_0101 _ _, Inv.Mode_R11 (StackL.pushBB hX) hB'⟩
      | c01011 hB' =>
        exact ⟨_, tr_R11_01011_B _ _, Inv.Mode_L10 hX (StackR.c0011_001 hB'.weaken.weaken.weaken)⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  apply isNotHalt_of_invariant target_tm Inv
  · exact ⟨_, tr_init_18, Inv.Mode_R11 (StackL.pushA StackL.bot10) StackR.emp⟩
  · exact step_Inv

end BusyBeaver.M_1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LBHHH
