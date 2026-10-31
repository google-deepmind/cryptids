/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RF_1LC0RD_---0LD_1LE0LD_1RA0RF_0RE0LB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_1LC0RD_---0LD_1LE0LD_1RA0RF_0RE0LB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_1LC0RD_HHH0LD_1LE0LD_1RA0RF_0RE0LB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_1LC0RD_---0LD_1LE0LD_1RA0RF_0RE0LB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
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

lemma stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

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

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))
local macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5)

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
    IsDoesNotHalt M := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome M (init []) cfg cfg' n m hn hnm

-- ============================================================================
-- Section 2: Macro Rules, Round, Sweeps, EraRound
-- ============================================================================

def B : Fin 6 := 4
def E : Fin 6 := 3

lemma rule_B_000 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 0, 0] +> r)) [target_tm]⊢⁺ (l <{{E}} ([0, 0, 1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_0011 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 0, 1, 1] +> r)) [target_tm]⊢⁺ (l <{{E}} ([0, 1, 0, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_00100 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 0, 1, 0, 0] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1, 1, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_001010 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 0, 1, 0, 1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1, 1, 1, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_0010110 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 0, 1, 0, 1, 1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1, 1, 1, 1, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_010 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_0110 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([0, 1, 1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [0, 1, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_B_10 (l r : ListBlank (Fin 2)) :
    (l {{B}}> ([1, 0] +> r)) [target_tm]⊢⁺ ((l <+ [0, 0]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_01111 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1, 1, 1, 1]) <{{E}} r) [target_tm]⊢⁺ (l <{{E}} ([0, 0, 0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_011111 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1, 1, 1, 1, 1]) <{{E}} r) [target_tm]⊢⁺ (l <{{E}} ([0, 0, 0, 0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_0111111 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1, 1, 1, 1, 1, 1]) <{{E}} r) [target_tm]⊢⁺ (l <{{E}} ([0, 0, 0, 0, 0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_011 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1, 1]) <{{E}} r) [target_tm]⊢⁺ (l <{{E}} ([0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_0111 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1, 1, 1]) <{{E}} r) [target_tm]⊢⁺ (l <{{E}} ([0, 0, 1, 0] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_00 (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 0]) <{{E}} ((0 : Fin 2) >> r)) [target_tm]⊢⁺ ((l <+ [0, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

lemma rule_E_nil (r : ListBlank (Fin 2)) :
    (default <{{E}} ((0 : Fin 2) >> r)) [target_tm]⊢⁺ ((default <+ [0, 1, 1]) {{B}}> r) := by
  dsimp [ListBlank.append]; execute

def Round (r r' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2), (l {{B}}> r) [target_tm]⊢⁺ (l <{{E}} r')

inductive Sweeps : Nat → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | zero (r : ListBlank (Fin 2)) : Sweeps 0 r r
  | succ {n : Nat} {r r₁ r₂ : ListBlank (Fin 2)} :
      Round r r₁ → Sweeps n r₁ r₂ → Sweeps (n + 1) r r₂

lemma Sweeps.trans {a b : Nat} {r₁ r₂ r₃ : ListBlank (Fin 2)}
    (h₁ : Sweeps a r₁ r₂) (h₂ : Sweeps b r₂ r₃) : Sweeps (a + b) r₁ r₃ := by
  induction h₁ with
  | zero _ => simpa using h₂
  | succ hr _ ih =>
    rw [Nat.succ_add]
    exact Sweeps.succ hr (ih h₂)

lemma round_000 (r : ListBlank (Fin 2)) :
    Round ([0, 0, 0] +> r) ([0, 0, 1] +> r) :=
  fun l => rule_B_000 l r

lemma round_0011 (r : ListBlank (Fin 2)) :
    Round ([0, 0, 1, 1] +> r) ([0, 1, 0, 0] +> r) :=
  fun l => rule_B_0011 l r

lemma round_00100 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 0, 1, 0, 0] +> r) ([0, 0, 0, 1, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_00100 l r)
    (stepPlus_trans (h (l <+ [0, 1, 1, 1, 1])) (rule_E_01111 l r'))

lemma round_001010 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 0, 1, 0, 1, 0] +> r) ([0, 0, 0, 0, 1, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_001010 l r)
    (stepPlus_trans (h (l <+ [0, 1, 1, 1, 1, 1])) (rule_E_011111 l r'))

lemma round_0010110 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 0, 1, 0, 1, 1, 0] +> r) ([0, 0, 0, 0, 0, 1, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_0010110 l r)
    (stepPlus_trans (h (l <+ [0, 1, 1, 1, 1, 1, 1])) (rule_E_0111111 l r'))

lemma round_010 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 1, 0] +> r) ([0, 1, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_010 l r)
    (stepPlus_trans (h (l <+ [0, 1, 1])) (rule_E_011 l r'))

lemma round_0110 {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round ([0, 1, 1, 0] +> r) ([0, 0, 1, 0] +> r') :=
  fun l => stepPlus_trans (rule_B_0110 l r)
    (stepPlus_trans (h (l <+ [0, 1, 1, 1])) (rule_E_0111 l r'))

lemma round_10 {r₁ r r₂ : ListBlank (Fin 2)}
    (h₁ : Round r₁ ((0 : Fin 2) >> r)) (h₂ : Round r r₂) :
    Round ([1, 0] +> r₁) ([0, 1, 0] +> r₂) :=
  fun l => stepPlus_trans (rule_B_10 l r₁)
    (stepPlus_trans (h₁ (l <+ [0, 0]))
      (stepPlus_trans (rule_E_00 l r)
        (stepPlus_trans (h₂ (l <+ [0, 1, 1])) (rule_E_011 l r₂))))

-- ============================================================================
-- Section 3: Fueled Bool-List Round Runner (for Base Cases & Era 0 -> Era 1)
-- ============================================================================

lemma opt_map_some {α β : Type*} {f : α → β} {x : Option α} {y : β}
    (h : x.map f = some y) : ∃ a, x = some a ∧ f a = y := by
  cases x with
  | none => nomatch h
  | some a => simp at h; exact ⟨a, rfl, h⟩

def b2f (b : Bool) : Fin 2 := if b then 1 else 0

def toTape : List Bool → ListBlank (Fin 2)
  | [] => default
  | b :: bs => b2f b >> toTape bs

def pad7B (bs : List Bool) : List Bool :=
  bs ++ [false, false, false, false, false, false, false]

lemma toTape_pad7B (bs : List Bool) : toTape (pad7B bs) = toTape bs := by
  induction bs with
  | nil => simp [pad7B, toTape, b2f, zero_cons_default]
  | cons b bs ih =>
    simp only [pad7B, List.cons_append, toTape]
    rw [← pad7B, ih]

def dropTrailingFalse : List Bool → List Bool
  | [] => []
  | b :: bs =>
    match dropTrailingFalse bs with
    | [] => if b then [true] else []
    | rest => b :: rest

lemma toTape_dropTrailingFalse : ∀ (bs : List Bool),
    toTape (dropTrailingFalse bs) = toTape bs
  | [] => rfl
  | b :: bs => by
    have ih := toTape_dropTrailingFalse bs
    unfold dropTrailingFalse
    cases hrest : dropTrailingFalse bs with
    | nil =>
      rw [hrest] at ih
      have hbs : toTape bs = default := ih.symm
      cases b <;> simp [toTape, b2f, hbs, zero_cons_default]
    | cons r rs =>
      rw [hrest] at ih
      change b2f b >> toTape (r :: rs) = b2f b >> toTape bs
      rw [ih]

def roundBool : Nat → List Bool → Option (List Bool)
  | 0, _ => none
  | fuel + 1, bs =>
    match pad7B bs with
    | false :: false :: false :: rest =>
      some (false :: false :: true :: rest)
    | false :: false :: true :: true :: rest =>
      some (false :: true :: false :: false :: rest)
    | false :: false :: true :: false :: false :: rest =>
      (roundBool fuel rest).map (fun r' => false :: false :: false :: true :: false :: r')
    | false :: false :: true :: false :: true :: false :: rest =>
      (roundBool fuel rest).map (fun r' => false :: false :: false :: false :: true :: false :: r')
    | false :: false :: true :: false :: true :: true :: false :: rest =>
      (roundBool fuel rest).map (fun r' => false :: false :: false :: false :: false :: true :: false :: r')
    | false :: true :: false :: rest =>
      (roundBool fuel rest).map (fun r' => false :: true :: false :: r')
    | false :: true :: true :: false :: rest =>
      (roundBool fuel rest).map (fun r' => false :: false :: true :: false :: r')
    | true :: false :: rest =>
      match roundBool fuel rest with
      | some (false :: r1) => (roundBool fuel r1).map (fun r2 => false :: true :: false :: r2)
      | _ => none
    | _ => none

lemma roundBool_sound : ∀ (fuel : Nat) (bs ys : List Bool),
    roundBool fuel bs = some ys → Round (toTape bs) (toTape ys)
  | 0, _, _, h => by nomatch h
  | fuel + 1, bs, ys, h => by
    rw [← toTape_pad7B bs]
    unfold roundBool at h
    generalize pad7B bs = pbs at h ⊢
    split at h
    · injection h with h; subst h; exact round_000 _
    · injection h with h; subst h; exact round_0011 _
    · obtain ⟨r', hr', rfl⟩ := opt_map_some h
      exact round_00100 (roundBool_sound fuel _ r' hr')
    · obtain ⟨r', hr', rfl⟩ := opt_map_some h
      exact round_001010 (roundBool_sound fuel _ r' hr')
    · obtain ⟨r', hr', rfl⟩ := opt_map_some h
      exact round_0010110 (roundBool_sound fuel _ r' hr')
    · obtain ⟨r', hr', rfl⟩ := opt_map_some h
      exact round_010 (roundBool_sound fuel _ r' hr')
    · obtain ⟨r', hr', rfl⟩ := opt_map_some h
      exact round_0110 (roundBool_sound fuel _ r' hr')
    · next rest =>
      cases hr1 : roundBool fuel rest with
      | none => rw [hr1] at h; nomatch h
      | some p1 =>
        rw [hr1] at h
        cases p1 with
        | nil => nomatch h
        | cons b0 r1 =>
          cases b0 with
          | true => nomatch h
          | false =>
            obtain ⟨r2, hr2, rfl⟩ := opt_map_some h
            exact round_10 (roundBool_sound fuel rest (false :: r1) hr1) (roundBool_sound fuel r1 r2 hr2)
    · nomatch h

def sweepsBool (fuel : Nat) : Nat → List Bool → Option (List Bool)
  | 0, bs => some bs
  | n + 1, bs =>
    match roundBool fuel bs with
    | some bs1 => sweepsBool fuel n bs1
    | none => none

lemma sweepsBool_sound (fuel : Nat) : ∀ (n : Nat) (bs ys : List Bool),
    sweepsBool fuel n bs = some ys → Sweeps n (toTape bs) (toTape ys)
  | 0, bs, ys, h => by injection h with h; subst h; exact Sweeps.zero _
  | n + 1, bs, ys, h => by
    unfold sweepsBool at h
    cases hr : roundBool fuel bs with
    | none => rw [hr] at h; nomatch h
    | some bs1 =>
      rw [hr] at h
      exact Sweeps.succ (roundBool_sound fuel bs bs1 hr) (sweepsBool_sound fuel n bs1 ys h)

def roundBoolTrim (fuel : Nat) (bs : List Bool) : Option (List Bool) :=
  (roundBool fuel bs).map dropTrailingFalse

lemma roundBoolTrim_sound (fuel : Nat) (bs ys : List Bool)
    (h : roundBoolTrim fuel bs = some ys) : Round (toTape bs) (toTape ys) := by
  obtain ⟨raw, hraw, rfl⟩ := opt_map_some h
  rw [toTape_dropTrailingFalse]
  exact roundBool_sound fuel bs raw hraw

def sweepsBoolTrim (fuel n : Nat) (bs : List Bool) : Option (List Bool) :=
  (sweepsBool fuel n bs).map dropTrailingFalse

lemma sweepsBoolTrim_sound (fuel n : Nat) (bs ys : List Bool)
    (h : sweepsBoolTrim fuel n bs = some ys) : Sweeps n (toTape bs) (toTape ys) := by
  obtain ⟨raw, hraw, rfl⟩ := opt_map_some h
  rw [toTape_dropTrailingFalse]
  exact sweepsBool_sound fuel n bs raw hraw

-- ============================================================================
-- Section 4: rep010, EraRound, pDiv0, pDiv1, pB & Parameterized Lemmas
-- ============================================================================

def rep010 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | k + 1, r => [0, 1, 0] +> rep010 k r

lemma rep010_add (a b : Nat) (r : ListBlank (Fin 2)) :
    rep010 (a + b) r = rep010 a (rep010 b r) := by
  induction a with
  | zero => simp [rep010]
  | succ a ih => simp [rep010, Nat.succ_add, ih]

def EraRound (u r' : ListBlank (Fin 2)) : Prop :=
  ∃ v : ListBlank (Fin 2), u = (0 : Fin 2) >> v ∧ Round v r'

lemma eraRound_tm_step {u r' : ListBlank (Fin 2)} (h : EraRound u r') :
    (default <{{E}} u) [target_tm]⊢⁺ (default <{{E}} ([0, 1, 0] +> r')) := by
  obtain ⟨v, rfl, hv⟩ := h
  exact stepPlus_trans (rule_E_nil v)
    (stepPlus_trans (hv (default <+ [0, 1, 1])) (rule_E_011 default r'))

lemma round_rep010 (k : Nat) {r r' : ListBlank (Fin 2)} (h : Round r r') :
    Round (rep010 k r) (rep010 k r') := by
  induction k with
  | zero => exact h
  | succ k ih => exact round_010 ih

lemma sweeps_rep010 (k : Nat) {n : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps n r r') :
    Sweeps n (rep010 k r) (rep010 k r') := by
  induction h with
  | zero _ => exact Sweeps.zero _
  | succ hr _ ih => exact Sweeps.succ (round_rep010 k hr) ih

lemma sweeps_010 {n : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps n r r') :
    Sweeps n ([0, 1, 0] +> r) ([0, 1, 0] +> r') :=
  sweeps_rep010 1 h

lemma eraRound_010 {s s₁ r' : ListBlank (Fin 2)}
    (hR : Round s s₁) (hE : EraRound s₁ r') :
    EraRound ([0, 1, 0] +> s) ([0, 1, 0] +> r') := by
  obtain ⟨v₁, rfl, hv₁⟩ := hE
  exact ⟨[1, 0] +> s, rfl, round_10 hR hv₁⟩

lemma eraRound_rep010 {N : Nat} {rem u r' : ListBlank (Fin 2)}
    (hS : Sweeps N rem u) (hE : EraRound u r') :
    EraRound (rep010 N rem) (rep010 N r') := by
  induction hS with
  | zero _ => exact hE
  | @succ n _ _ _ hr _ ih =>
    exact eraRound_010 (round_rep010 n hr) (ih hE)

def pDiv0 (r : ListBlank (Fin 2)) : ListBlank (Fin 2) := [0, 0, 0, 0, 1, 0] +> r
def pDiv1 (r : ListBlank (Fin 2)) : ListBlank (Fin 2) := [0, 0, 1, 0, 1, 0] +> r
def pB (r : ListBlank (Fin 2)) : ListBlank (Fin 2) := [0, 0, 1, 1, 0] +> r

lemma round_pDiv0 (r : ListBlank (Fin 2)) : Round (pDiv0 r) (pDiv1 r) :=
  round_000 ([0, 1, 0] +> r)

lemma round_pDiv1 {r r' : ListBlank (Fin 2)} (h : Round r r') : Round (pDiv1 r) (pDiv0 r') :=
  round_001010 h

lemma sweeps_pDiv0_even {k : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps k r r') :
    Sweeps (2 * k) (pDiv0 r) (pDiv0 r') := by
  induction h with
  | zero _ => exact Sweeps.zero _
  | @succ m r₀ r₁ r₂ hr _ ih =>
    have h2 : Sweeps 2 (pDiv0 r₀) (pDiv0 r₁) :=
      Sweeps.succ (round_pDiv0 r₀) (Sweeps.succ (round_pDiv1 hr) (Sweeps.zero _))
    have htr := Sweeps.trans h2 ih
    rw [show 2 + 2 * m = 2 * (m + 1) by omega] at htr
    exact htr

lemma sweeps_pDiv0_odd {k : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps k r r') :
    Sweeps (2 * k + 1) (pDiv0 r) (pDiv1 r') :=
  Sweeps.trans (sweeps_pDiv0_even h) (Sweeps.succ (round_pDiv0 r') (Sweeps.zero _))

lemma sweeps_pDiv1_even {k : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps k r r') :
    Sweeps (2 * k) (pDiv1 r) (pDiv1 r') := by
  induction h with
  | zero _ => exact Sweeps.zero _
  | @succ m r₀ r₁ r₂ hr _ ih =>
    have h2 : Sweeps 2 (pDiv1 r₀) (pDiv1 r₁) :=
      Sweeps.succ (round_pDiv1 hr) (Sweeps.succ (round_pDiv0 r₁) (Sweeps.zero _))
    have htr := Sweeps.trans h2 ih
    rw [show 2 + 2 * m = 2 * (m + 1) by omega] at htr
    exact htr

lemma sweeps_pDiv1_odd {k : Nat} {r r' : ListBlank (Fin 2)} (h : Sweeps (k + 1) r r') :
    Sweeps (2 * k + 1) (pDiv1 r) (pDiv0 r') := by
  cases h with
  | succ hr hs =>
    exact Sweeps.succ (round_pDiv1 hr) (sweeps_pDiv0_even hs)

def StartsZero (u : ListBlank (Fin 2)) : Prop :=
  ∃ v : ListBlank (Fin 2), u = (0 : Fin 2) >> v

lemma rep010_startsZero (k : Nat) {u : ListBlank (Fin 2)} (hu : StartsZero u) :
    StartsZero (rep010 k u) := by
  cases k with
  | zero => exact hu
  | succ k => exact ⟨[1, 0] +> rep010 k u, rfl⟩

lemma sweeps_pB_010_startsZero {u : ListBlank (Fin 2)} (hu : StartsZero u) :
    Sweeps 2 (pB ([0, 1, 0] +> u)) ([0, 1, 0] +> pB u) := by
  obtain ⟨v, rfl⟩ := hu
  refine Sweeps.succ (round_0011 ([0, 0, 1, 0, 0] +> v)) ?_
  refine Sweeps.succ (round_010 (round_000 ([1, 0, 0] +> v))) ?_
  exact Sweeps.zero _

lemma sweeps_pB_rep010 (k : Nat) {u : ListBlank (Fin 2)} (hu : StartsZero u) :
    Sweeps (2 * k) (pB (rep010 k u)) (rep010 k (pB u)) := by
  induction k with
  | zero => exact Sweeps.zero _
  | succ k ih =>
    have h2 := sweeps_pB_010_startsZero (rep010_startsZero k hu)
    have htr := Sweeps.trans h2 (sweeps_010 ih)
    rw [show 2 + 2 * k = 2 * (k + 1) by omega] at htr
    exact htr

lemma sweeps_pB_pDiv0 {u u₁ : ListBlank (Fin 2)} (h1 : Round u u₁) :
    Sweeps 6 (pB (pDiv0 u)) (rep010 2 (pB u₁)) := by
  refine Sweeps.succ (round_0011 ([0, 0, 0, 0, 0, 1, 0] +> u)) ?_
  refine Sweeps.succ (round_010 (round_000 ([0, 0, 0, 1, 0] +> u))) ?_
  refine Sweeps.succ (round_010 (round_00100 (round_010 h1))) ?_
  refine Sweeps.succ (round_010 (round_000 ([1, 0, 0, 1, 0] +> u₁))) ?_
  refine Sweeps.succ (round_010 (round_0011 ([0, 0, 1, 0] +> u₁))) ?_
  refine Sweeps.succ (round_010 (round_010 (round_000 ([1, 0] +> u₁)))) ?_
  exact Sweeps.zero _

lemma sweeps_pB_pDiv1 {u u₁ r₁' : ListBlank (Fin 2)}
    (h1 : Round u u₁) (hE : EraRound u₁ r₁') :
    Sweeps 3 (pB (pDiv1 u)) ([0, 1, 0] +> pDiv0 ([0, 1, 0] +> r₁')) := by
  obtain ⟨v₁, rfl, hv₁⟩ := hE
  refine Sweeps.succ (round_0011 ([0, 0, 0, 1, 0, 1, 0] +> u)) ?_
  refine Sweeps.succ (round_010 (round_000 ([0, 1, 0, 1, 0] +> u))) ?_
  refine Sweeps.succ (round_010 (round_001010 (round_10 h1 hv₁))) ?_
  exact Sweeps.zero _

lemma eraRound_pDiv0 (u : ListBlank (Fin 2)) :
    EraRound (pDiv0 u) (pB u) :=
  ⟨[0, 0, 0, 1, 0] +> u, rfl, round_000 ([1, 0] +> u)⟩

lemma eraRound_pDiv1 {u u₁ r₁' : ListBlank (Fin 2)}
    (h1 : Round u u₁) (hE : EraRound u₁ r₁') :
    EraRound (pDiv1 u) (rep010 2 r₁') := by
  obtain ⟨v₁, rfl, hv₁⟩ := hE
  exact ⟨[0, 1, 0, 1, 0] +> u, rfl, round_010 (round_10 h1 hv₁)⟩

-- ============================================================================
-- Section 5: CoreTree, UTree, stepDefaultAux, stepCore, stepU & Soundness
-- ============================================================================

inductive CoreTree : Type where
  | sw0 : CoreTree
  | sw1 : CoreTree
  | sw2 : CoreTree
  | sw3 : CoreTree
  | div0 : Nat → CoreTree → CoreTree
  | div1 : Nat → CoreTree → CoreTree
  deriving DecidableEq

abbrev UTree := Nat × CoreTree

def evalCore : CoreTree → ListBlank (Fin 2)
  | .sw0 => default
  | .sw1 => [0, 0, 1] +> default
  | .sw2 => [0, 0, 0, 1, 0, 0, 0, 1, 0] +> default
  | .sw3 => [0, 0, 1, 1, 0, 0, 0, 1, 0] +> default
  | .div0 k ch => pDiv0 (rep010 k (evalCore ch))
  | .div1 k ch => pDiv1 (rep010 k (evalCore ch))

def evalU (u : UTree) : ListBlank (Fin 2) :=
  rep010 u.1 (evalCore u.2)

lemma evalCore_startsZero (w : CoreTree) : StartsZero (evalCore w) := by
  cases w with
  | sw0 => exact ⟨default, zero_cons_default.symm⟩
  | sw1 => exact ⟨[0, 1] +> default, rfl⟩
  | sw2 => exact ⟨[0, 0, 1, 0, 0, 0, 1, 0] +> default, rfl⟩
  | sw3 => exact ⟨[0, 1, 1, 0, 0, 0, 1, 0] +> default, rfl⟩
  | div0 k ch => exact ⟨[0, 0, 0, 1, 0] +> rep010 k (evalCore ch), rfl⟩
  | div1 k ch => exact ⟨[0, 1, 0, 1, 0] +> rep010 k (evalCore ch), rfl⟩

def levelCore : CoreTree → Nat
  | .sw0 => 1
  | .sw1 => 2
  | .sw2 => 3
  | .sw3 => 4
  | .div0 k ch => 2 * (3 * k + levelCore ch)
  | .div1 k ch => 2 * (3 * k + levelCore ch) + 1

def levelU (u : UTree) : Nat :=
  3 * u.1 + levelCore u.2

lemma levelCore_pos (w : CoreTree) : 1 ≤ levelCore w := by
  induction w <;> simp [levelCore] <;> omega

def mkSw : Nat → CoreTree
  | 0 => .sw0
  | 1 => .sw1
  | 2 => .sw2
  | _ => .sw3

def coreTagIdx : CoreTree → Option Nat
  | .sw0 => some 0
  | .sw1 => some 1
  | .sw2 => some 2
  | .sw3 => some 3
  | .div0 _ _ => none
  | .div1 _ _ => none

def stepDefaultAux : Nat → Nat → UTree
  | 0, s => (0, mkSw s)
  | fuel + 1, s =>
    if s ≤ 3 then (0, mkSw s)
    else
      let m := s - 4
      let sub := stepDefaultAux fuel (m / 2)
      if m % 2 = 0 then (1, .div0 sub.1 sub.2) else (1, .div1 sub.1 sub.2)

lemma stepDefaultAux_le3 (fuel s : Nat) (hs : s ≤ 3) :
    stepDefaultAux fuel s = (0, mkSw s) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [stepDefaultAux, hs]

lemma stepDefaultAux_add4 (fuel m : Nat) :
    stepDefaultAux (fuel + 1) (m + 4) =
      (let sub := stepDefaultAux fuel (m / 2)
       if m % 2 = 0 then (1, .div0 sub.1 sub.2) else (1, .div1 sub.1 sub.2)) := by
  have h : ¬(m + 4 ≤ 3) := by omega
  have hm : m + 4 - 4 = m := by omega
  simp [stepDefaultAux, h, hm]

def stepDefault (s : Nat) : UTree :=
  stepDefaultAux s s

def stepCore (s : Nat) : CoreTree → UTree
  | .sw0 => stepDefault s
  | .sw1 => stepDefault (s + 1)
  | .sw2 => stepDefault (s + 2)
  | .sw3 => stepDefault (s + 3)
  | .div0 k ch =>
    let sub := stepCore (s / 2) ch
    if s % 2 = 0 then (0, .div0 (k + sub.1) sub.2) else (0, .div1 (k + sub.1) sub.2)
  | .div1 k ch =>
    let sub := stepCore ((s + 1) / 2) ch
    if s % 2 = 0 then (0, .div1 (k + sub.1) sub.2) else (0, .div0 (k + sub.1) sub.2)

def stepU (s : Nat) (u : UTree) : UTree :=
  let sub := stepCore s u.2
  (u.1 + sub.1, sub.2)

def stepDiv0Sw0 (s : Nat) : CoreTree :=
  let sub := stepDefault (s / 2)
  if s % 2 = 0 then .div0 sub.1 sub.2 else .div1 sub.1 sub.2

def stepDivCore (s : Nat) : CoreTree → CoreTree
  | .div0 k ch =>
    let sub := stepCore (s / 2) ch
    if s % 2 = 0 then .div0 (k + sub.1) sub.2 else .div1 (k + sub.1) sub.2
  | .div1 k ch =>
    let sub := stepCore ((s + 1) / 2) ch
    if s % 2 = 0 then .div1 (k + sub.1) sub.2 else .div0 (k + sub.1) sub.2
  | w => w

lemma levelU_stepDefaultAux : ∀ (fuel s : Nat), s ≤ fuel →
    levelU (stepDefaultAux fuel s) = s + 1
  | 0, s, hs => by
    have hs0 : s = 0 := by omega
    subst hs0; rfl
  | fuel + 1, s, hs => by
    rcases (by omega : s ≤ 3 ∨ 4 ≤ s) with hle | hge
    · rw [stepDefaultAux_le3 (fuel + 1) s hle]
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, s = m + 4 := ⟨s - 4, by omega⟩
      rw [stepDefaultAux_add4]
      have ih := levelU_stepDefaultAux fuel (m / 2) (by omega)
      rcases (by omega : m % 2 = 0 ∨ ¬(m % 2 = 0)) with hev | hod
      · simp only [hev, ↓reduceIte, levelU, levelCore]
        unfold levelU at ih; omega
      · simp only [hod, ↓reduceIte, levelU, levelCore]
        unfold levelU at ih; omega

lemma levelU_stepDefault (s : Nat) : levelU (stepDefault s) = s + 1 :=
  levelU_stepDefaultAux s s (le_refl s)

lemma levelU_stepCore (s : Nat) (w : CoreTree) :
    levelU (stepCore s w) = levelCore w + s := by
  induction w generalizing s with
  | sw0 => simp [stepCore, levelU_stepDefault, levelCore]; omega
  | sw1 => simp [stepCore, levelU_stepDefault, levelCore]; omega
  | sw2 => simp [stepCore, levelU_stepDefault, levelCore]; omega
  | sw3 => simp [stepCore, levelU_stepDefault, levelCore]; omega
  | div0 k ch ih =>
    have hsub := ih (s / 2)
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simp only [stepCore, hev, ↓reduceIte, levelU, levelCore]
      unfold levelU at hsub; omega
    · simp only [stepCore, hod, ↓reduceIte, levelU, levelCore]
      unfold levelU at hsub; omega
  | div1 k ch ih =>
    have hsub := ih ((s + 1) / 2)
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simp only [stepCore, hev, ↓reduceIte, levelU, levelCore]
      unfold levelU at hsub; omega
    · simp only [stepCore, hod, ↓reduceIte, levelU, levelCore]
      unfold levelU at hsub; omega

lemma levelU_stepU (s : Nat) (u : UTree) : levelU (stepU s u) = levelU u + s := by
  rcases u with ⟨k, w⟩
  have hsub := levelU_stepCore s w
  unfold stepU levelU at *
  dsimp only at *
  omega

lemma levelCore_stepDiv0Sw0 (s : Nat) : levelCore (stepDiv0Sw0 s) = s + 2 := by
  have hsub := levelU_stepDefault (s / 2)
  rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
  · simp only [stepDiv0Sw0, hev, ↓reduceIte, levelCore]
    unfold levelU at hsub; omega
  · simp only [stepDiv0Sw0, hod, ↓reduceIte, levelCore]
    unfold levelU at hsub; omega

lemma levelCore_stepDivCore (s : Nat) (w : CoreTree) (hw : coreTagIdx w = none) :
    levelCore (stepDivCore s w) = levelCore w + s := by
  cases w with
  | sw0 | sw1 | sw2 | sw3 => nomatch hw
  | div0 k ch =>
    have hsub := levelU_stepCore (s / 2) ch
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simp only [stepDivCore, hev, ↓reduceIte, levelCore]
      unfold levelU at hsub; omega
    · simp only [stepDivCore, hod, ↓reduceIte, levelCore]
      unfold levelU at hsub; omega
  | div1 k ch =>
    have hsub := levelU_stepCore ((s + 1) / 2) ch
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simp only [stepDivCore, hev, ↓reduceIte, levelCore]
      unfold levelU at hsub; omega
    · simp only [stepDivCore, hod, ↓reduceIte, levelCore]
      unfold levelU at hsub; omega

lemma round_sw0_sw1 : Round (evalCore .sw0) (evalCore .sw1) :=
  roundBoolTrim_sound 5 [] [false, false, true] rfl

lemma round_sw1_sw2 : Round (evalCore .sw1) (evalCore .sw2) := by
  have h := roundBoolTrim_sound 10 [false, false, true]
    [false, false, false, true, false, false, false, true] rfl
  simpa [toTape, b2f, evalCore, zero_cons_default] using h

lemma round_sw2_sw3 : Round (evalCore .sw2) (evalCore .sw3) := by
  have h := roundBoolTrim_sound 10 [false, false, false, true, false, false, false, true]
    [false, false, true, true, false, false, false, true] rfl
  simpa [toTape, b2f, evalCore, zero_cons_default] using h

lemma round_sw3_div0 : Round (evalCore .sw3) (evalU (1, .div0 0 .sw0)) := by
  have h := roundBoolTrim_sound 10 [false, false, true, true, false, false, false, true]
    [false, true, false, false, false, false, false, true] rfl
  simpa [toTape, b2f, evalCore, evalU, rep010, pDiv0, zero_cons_default] using h

lemma stepDefaultAux_eq (fuel₁ fuel₂ s : Nat) (h1 : s ≤ fuel₁) (h2 : s ≤ fuel₂) :
    stepDefaultAux fuel₁ s = stepDefaultAux fuel₂ s := by
  induction fuel₁ generalizing fuel₂ s with
  | zero =>
    have hs0 : s = 0 := by omega
    subst hs0
    exact (stepDefaultAux_le3 fuel₂ 0 (by omega)).symm
  | succ fuel₁ ih =>
    rcases (by omega : s ≤ 3 ∨ 4 ≤ s) with hle | hge
    · rw [stepDefaultAux_le3 _ s hle, stepDefaultAux_le3 _ s hle]
    · obtain ⟨m, rfl⟩ : ∃ m, s = m + 4 := ⟨s - 4, by omega⟩
      cases fuel₂ with
      | zero => omega
      | succ fuel₂ =>
        rw [stepDefaultAux_add4, stepDefaultAux_add4]
        have heq := ih fuel₂ (m / 2) (by omega) (by omega)
        simp only [heq]

lemma stepDefault_add4_eq (m : Nat) :
    stepDefault (m + 4) = (1, stepDiv0Sw0 m) := by
  change stepDefaultAux ((m + 3) + 1) (m + 4) = (1, stepDiv0Sw0 m)
  rw [stepDefaultAux_add4]
  have h := stepDefaultAux_eq (m + 3) (m / 2) (m / 2) (by omega) (le_refl _)
  unfold stepDiv0Sw0 stepDefault
  rw [h]
  rcases (by omega : m % 2 = 0 ∨ ¬(m % 2 = 0)) with hev | hod
  · simp only [hev, ↓reduceIte]
  · simp only [hod, ↓reduceIte]

lemma stepDefault_one_more : ∀ (q : Nat),
    Round (evalU (stepDefault q)) (evalU (stepDefault (q + 1))) := by
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ 4 ≤ q) with rfl | rfl | rfl | rfl | hq4
    · exact round_sw0_sw1
    · exact round_sw1_sw2
    · exact round_sw2_sw3
    · exact round_sw3_div0
    · obtain ⟨m, rfl⟩ : ∃ m, q = m + 4 := ⟨q - 4, by omega⟩
      have h1 := stepDefault_add4_eq m
      have h2 := stepDefault_add4_eq (m + 1)
      have h_add : m + 4 + 1 = m + 1 + 4 := by omega
      rw [h1, h_add, h2]
      refine round_010 ?_
      unfold stepDiv0Sw0
      rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with hev | hod
      · have hev1 : (m + 1) % 2 = 1 := by omega
        have hdiv : (m + 1) / 2 = m / 2 := by omega
        simp [hev, hev1, hdiv, evalCore]
        exact round_pDiv0 _
      · have hod1 : (m + 1) % 2 = 0 := by omega
        have hdiv : (m + 1) / 2 = m / 2 + 1 := by omega
        have hev' : ¬(m % 2 = 0) := by omega
        simp [hev', hod1, hdiv, evalCore]
        exact round_pDiv1 (ih (m / 2) (by omega))

lemma round_stepDiv0Sw0 (m : Nat) :
    Round (evalCore (stepDiv0Sw0 m)) (evalCore (stepDiv0Sw0 (m + 1))) := by
  unfold stepDiv0Sw0
  rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with hev | hod
  · have hev1 : (m + 1) % 2 = 1 := by omega
    have hdiv : (m + 1) / 2 = m / 2 := by omega
    simp [hev, hev1, hdiv, evalCore]
    exact round_pDiv0 _
  · have hod1 : (m + 1) % 2 = 0 := by omega
    have hdiv : (m + 1) / 2 = m / 2 + 1 := by omega
    have hev' : ¬(m % 2 = 0) := by omega
    simp [hev', hod1, hdiv, evalCore]
    exact round_pDiv1 (stepDefault_one_more (m / 2))

lemma stepDefault_from (t s : Nat) :
    Sweeps s (evalU (stepDefault t)) (evalU (stepDefault (s + t))) := by
  induction s with
  | zero => simp; exact Sweeps.zero _
  | succ s ih =>
    have h1 := Sweeps.succ (stepDefault_one_more (s + t)) (Sweeps.zero _)
    have htr := Sweeps.trans ih h1
    rw [show s + t + 1 = (s + 1) + t by omega] at htr
    exact htr

lemma stepDefault_sound (s : Nat) : Sweeps s (evalCore .sw0) (evalU (stepDefault s)) := by
  change Sweeps s (evalU (stepDefault 0)) (evalU (stepDefault s))
  simpa using stepDefault_from 0 s

lemma stepCore_sound (s : Nat) (w : CoreTree) :
    Sweeps s (evalCore w) (evalU (stepCore s w)) := by
  induction w generalizing s with
  | sw0 => exact stepDefault_sound s
  | sw1 => exact stepDefault_from 1 s
  | sw2 => exact stepDefault_from 2 s
  | sw3 => exact stepDefault_from 3 s
  | div0 k ch ih =>
    have hsub := sweeps_rep010 k (ih (s / 2))
    rw [evalU, ← rep010_add] at hsub
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simp only [stepCore, hev, ↓reduceIte, evalU, rep010, evalCore]
      have h := sweeps_pDiv0_even hsub
      rwa [show 2 * (s / 2) = s by omega] at h
    · simp only [stepCore, hod, ↓reduceIte, evalU, rep010, evalCore]
      have h := sweeps_pDiv0_odd hsub
      rwa [show 2 * (s / 2) + 1 = s by omega] at h
  | div1 k ch ih =>
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simp only [stepCore, hev, ↓reduceIte, evalU, rep010, evalCore]
      have h_eq : (s + 1) / 2 = s / 2 := by omega
      have hsub := sweeps_rep010 k (ih ((s + 1) / 2))
      rw [evalU, ← rep010_add] at hsub
      have hsub' : Sweeps (s / 2) (rep010 k (evalCore ch)) (rep010 (k + (stepCore ((s + 1) / 2) ch).1) (evalCore (stepCore ((s + 1) / 2) ch).2)) := by
        rwa [← h_eq]
      have h := sweeps_pDiv1_even hsub'
      rwa [show 2 * (s / 2) = s by omega] at h
    · simp only [stepCore, hod, ↓reduceIte, evalU, rep010, evalCore]
      have h_eq : (s + 1) / 2 = s / 2 + 1 := by omega
      have hsub := sweeps_rep010 k (ih ((s + 1) / 2))
      rw [evalU, ← rep010_add] at hsub
      have hsub' : Sweeps (s / 2 + 1) (rep010 k (evalCore ch)) (rep010 (k + (stepCore ((s + 1) / 2) ch).1) (evalCore (stepCore ((s + 1) / 2) ch).2)) := by
        rwa [← h_eq]
      have h := sweeps_pDiv1_odd hsub'
      rwa [show 2 * (s / 2) + 1 = s by omega] at h

lemma stepU_sound (s : Nat) (u : UTree) :
    Sweeps s (evalU u) (evalU (stepU s u)) := by
  have h := sweeps_rep010 u.1 (stepCore_sound s u.2)
  unfold stepU evalU at *
  rwa [← rep010_add] at h

lemma stepDivCore_sound (s : Nat) (w : CoreTree) (hw : coreTagIdx w = none) :
    Sweeps s (evalCore w) (evalCore (stepDivCore s w)) := by
  cases w with
  | sw0 | sw1 | sw2 | sw3 => nomatch hw
  | div0 k ch =>
    have h := stepCore_sound s (.div0 k ch)
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simpa [stepCore, stepDivCore, hev, evalU, rep010] using h
    · simpa [stepCore, stepDivCore, hod, evalU, rep010] using h
  | div1 k ch =>
    have h := stepCore_sound s (.div1 k ch)
    rcases (by omega : s % 2 = 0 ∨ ¬(s % 2 = 0)) with hev | hod
    · simpa [stepCore, stepDivCore, hev, evalU, rep010] using h
    · simpa [stepCore, stepDivCore, hod, evalU, rep010] using h

lemma round_of_sweeps_one {r r' : ListBlank (Fin 2)} (h : Sweeps 1 r r') : Round r r' := by
  cases h with
  | succ hr h0 =>
    cases h0 with
    | zero _ => exact hr

-- ============================================================================
-- Section 6: Fueled 2-Function opsAux & Soundness
-- ============================================================================

structure ResB where
  c : Nat
  u : UTree

structure ResP where
  p : Nat
  c : Nat
  u : UTree

structure Ops where
  bCore : CoreTree → ResB
  aCore : CoreTree → ResP

def bUFrom (bCoreFn : CoreTree → ResB) : UTree → ResB
  | (k, w) =>
    let sub := bCoreFn w
    ⟨2 * k + sub.c, (k + sub.u.1, sub.u.2)⟩

def aPullSucc (aCoreFn : CoreTree → ResP) (k : Nat) (w : CoreTree) : ResP :=
  match coreTagIdx w with
  | some t =>
    if k + t ≤ 3 then
      let sub := aCoreFn (mkSw (k + t))
      ⟨k + sub.p, sub.c, sub.u⟩
    else
      let sub := aCoreFn (stepDiv0Sw0 (k + t - 3))
      ⟨k + 1 + sub.p, sub.c, sub.u⟩
  | none =>
    let sub := aCoreFn (stepDivCore k w)
    ⟨k + sub.p, sub.c, sub.u⟩

def aPullFrom (aCoreFn : CoreTree → ResP) : UTree → ResP
  | (0, w) => aCoreFn w
  | (k' + 1, w) => aPullSucc aCoreFn (k' + 1) w

def opsAux : Nat → Ops
  | 0 => {
      bCore := fun _ => ⟨0, (0, .sw0)⟩
      aCore := fun _ => ⟨0, 0, (0, .sw0)⟩
    }
  | fuel + 1 =>
    let prev := opsAux fuel
    {
      bCore := fun w =>
        match w with
        | .sw0 => ⟨1, (1, .sw0)⟩
        | .sw1 => ⟨0, (0, .sw3)⟩
        | .sw2 => ⟨15, (6, .div0 0 .sw2)⟩
        | .sw3 => ⟨9, (3, .div0 0 .sw2)⟩
        | .div0 k ch =>
          if k = 0 ∧ ch = .sw0 then
            ⟨6, (2, .sw3)⟩
          else
            let u1 := stepU 1 (k, ch)
            let sub := bUFrom prev.bCore u1
            ⟨6 + sub.c, (2 + sub.u.1, sub.u.2)⟩
        | .div1 k ch =>
          if k = 0 ∧ ch = .sw0 then
            ⟨3, (1, .div0 2 .sw1)⟩
          else
            let u1 := stepU 1 (k, ch)
            let sub := aPullFrom prev.aCore u1
            ⟨3 + 2 * sub.c, (1, .div0 (1 + sub.p + sub.u.1) sub.u.2)⟩
      aCore := fun w =>
        match w with
        | .sw0 => ⟨0, 0, (0, .sw1)⟩
        | .sw1 => ⟨1, 0, (0, .sw1)⟩
        | .sw2 => ⟨0, 2, (1, .sw2)⟩
        | .sw3 => ⟨0, 11, (4, .div0 0 .sw2)⟩
        | .div0 k ch =>
          if k = 0 ∧ ch = .sw0 then
            ⟨0, 1, (1, .sw0)⟩
          else
            let sub := bUFrom prev.bCore (k, ch)
            ⟨0, sub.c, sub.u⟩
        | .div1 k ch =>
          if k = 0 ∧ ch = .sw0 then
            ⟨3, 0, (0, .sw1)⟩
          else
            let u1 := stepU 1 (k, ch)
            let sub := aPullFrom prev.aCore u1
            ⟨2 + sub.p, sub.c, sub.u⟩
    }

lemma bCore_sw0_sound : Sweeps 1 (pB (evalCore .sw0)) (evalU (1, .sw0)) := by
  have h := sweepsBoolTrim_sound 10 1 [false, false, true, true, false]
    [false, true] rfl
  simpa [toTape, b2f, pB, evalCore, evalU, rep010, zero_cons_default] using h

lemma bCore_sw1_sound : Sweeps 0 (pB (evalCore .sw1)) (evalU (0, .sw3)) := by
  have heq : pB (evalCore .sw1) = evalU (0, .sw3) := by
    simp [pB, evalCore, evalU, rep010, zero_cons_default]
  rw [heq]; exact Sweeps.zero _

lemma bCore_sw2_sound : Sweeps 15 (pB (evalCore .sw2)) (evalU (6, .div0 0 .sw2)) := by
  have h := sweepsBoolTrim_sound 20 15
    [false, false, true, true, false, false, false, false, true, false, false, false, true]
    [false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false,
     false, false, false, false, true, false, false, false, false, true, false, false, false, true] rfl
  simpa [toTape, b2f, pB, evalCore, evalU, rep010, pDiv0, zero_cons_default] using h

lemma bCore_sw3_sound : Sweeps 9 (pB (evalCore .sw3)) (evalU (3, .div0 0 .sw2)) := by
  have h := sweepsBoolTrim_sound 20 9
    [false, false, true, true, false, false, false, true, true, false, false, false, true]
    [false, true, false, false, true, false, false, true, false,
     false, false, false, false, true, false, false, false, false, true, false, false, false, true] rfl
  simpa [toTape, b2f, pB, evalCore, evalU, rep010, pDiv0, zero_cons_default] using h

lemma bCore_div0_sw0_sound : Sweeps 6 (pB (evalCore (.div0 0 .sw0))) (evalU (2, .sw3)) := by
  have h := sweepsBoolTrim_sound 20 6
    [false, false, true, true, false, false, false, false, false, true]
    [false, true, false, false, true, false, false, false, true, true, false, false, false, true] rfl
  simpa [toTape, b2f, pB, evalCore, evalU, rep010, pDiv0, zero_cons_default] using h

lemma bCore_div1_sw0_sound : Sweeps 3 (pB (evalCore (.div1 0 .sw0))) (evalU (1, .div0 2 .sw1)) := by
  have h := sweepsBoolTrim_sound 20 3
    [false, false, true, true, false, false, false, true, false, true]
    [false, true, false, false, false, false, false, true, false,
     false, true, false, false, true, false, false, false, true] rfl
  simpa [toTape, b2f, pB, evalCore, evalU, rep010, pDiv0, pDiv1, zero_cons_default] using h

lemma aCore_sw0_sound : EraRound (evalCore .sw0) (rep010 0 (evalCore .sw1)) :=
  ⟨default, zero_cons_default.symm, round_sw0_sw1⟩

lemma aCore_sw1_sound : EraRound (evalCore .sw1) (rep010 1 (evalCore .sw1)) := by
  refine ⟨[0, 1] +> default, rfl, ?_⟩
  have h := roundBoolTrim_sound 10 [false, true] [false, true, false, false, false, true] rfl
  simpa [toTape, b2f, evalCore, rep010, zero_cons_default] using h

lemma aCore_sw2_sound :
    ∃ r', EraRound (evalCore .sw2) (rep010 0 r') ∧ Sweeps 2 r' (evalU (1, .sw2)) := by
  refine ⟨[0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1] +> default, ?_, ?_⟩
  · refine ⟨[0, 0, 1, 0, 0, 0, 1, 0] +> default, rfl, ?_⟩
    have h := roundBoolTrim_sound 10 [false, false, true, false, false, false, true]
      [false, false, false, true, false, false, true, false, false, false, true] rfl
    simpa [toTape, b2f, rep010, zero_cons_default] using h
  · have h := sweepsBoolTrim_sound 15 2
      [false, false, false, true, false, false, true, false, false, false, true]
      [false, true, false, false, false, false, true, false, false, false, true] rfl
    simpa [toTape, b2f, evalU, evalCore, rep010, zero_cons_default] using h

lemma aCore_sw3_sound :
    ∃ r', EraRound (evalCore .sw3) (rep010 0 r') ∧ Sweeps 11 r' (evalU (4, .div0 0 .sw2)) := by
  refine ⟨[0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1] +> default, ?_, ?_⟩
  · refine ⟨[0, 1, 1, 0, 0, 0, 1, 0] +> default, rfl, ?_⟩
    have h := roundBoolTrim_sound 10 [false, true, true, false, false, false, true]
      [false, false, true, false, false, false, false, true, false, false, false, true] rfl
    simpa [toTape, b2f, rep010, zero_cons_default] using h
  · have h := sweepsBoolTrim_sound 20 11
      [false, false, true, false, false, false, false, true, false, false, false, true]
      [false, true, false, false, true, false, false, true, false, false, true, false,
       false, false, false, false, true, false, false, false, false, true, false, false, false, true] rfl
    simpa [toTape, b2f, evalU, evalCore, rep010, pDiv0, zero_cons_default] using h

lemma aCore_div0_sw0_sound :
    ∃ r', EraRound (evalCore (.div0 0 .sw0)) (rep010 0 r') ∧ Sweeps 1 r' (evalU (1, .sw0)) :=
  ⟨pB (evalCore .sw0), eraRound_pDiv0 (evalCore .sw0), bCore_sw0_sound⟩

lemma aCore_div1_sw0_sound :
    EraRound (evalCore (.div1 0 .sw0)) (rep010 3 (evalCore .sw1)) := by
  have h := eraRound_pDiv1 round_sw0_sw1 aCore_sw1_sound
  simpa [evalCore, rep010] using h

lemma levelU_gt_one_of_ne_sw0 {k : Nat} {ch : CoreTree} (h : ¬(k = 0 ∧ ch = .sw0)) :
    2 ≤ levelU (k, ch) := by
  cases k with
  | zero =>
    cases ch with
    | sw0 => exact absurd ⟨rfl, rfl⟩ h
    | sw1 | sw2 | sw3 => decide
    | div0 k' ch' => have := levelCore_pos ch'; simp [levelU, levelCore]; omega
    | div1 k' ch' => have := levelCore_pos ch'; simp [levelU, levelCore]; omega
  | succ k =>
    have := levelCore_pos ch
    unfold levelU; dsimp only; omega

lemma bUFrom_sound {bCoreFn : CoreTree → ResB} {fuel : Nat}
    (hb : ∀ w : CoreTree, levelCore w ≤ fuel →
      Sweeps (bCoreFn w).c (pB (evalCore w)) (evalU (bCoreFn w).u))
    (u : UTree) (hu : levelU u ≤ fuel) :
    let res := bUFrom bCoreFn u
    Sweeps res.c (pB (evalU u)) (evalU res.u) := by
  rcases u with ⟨k, w⟩
  have hcw : levelCore w ≤ fuel := by unfold levelU at hu; dsimp only at hu; omega
  have hsub := hb w hcw
  have h1 := sweeps_pB_rep010 k (evalCore_startsZero w)
  have h2 := sweeps_rep010 k hsub
  have htr := Sweeps.trans h1 h2
  unfold bUFrom evalU at *
  dsimp only at *
  rwa [← rep010_add] at htr

lemma stepCore_eq_stepDefault {w : CoreTree} {t k : Nat} (ht : coreTagIdx w = some t) :
    stepCore k w = stepDefault (k + t) := by
  cases w <;> simp [coreTagIdx] at ht <;> subst ht <;> simp [stepCore]

lemma aPullSucc_sound {aCoreFn : CoreTree → ResP} {fuel k : Nat} {w : CoreTree}
    (hk : 1 ≤ k)
    (ha : ∀ w' : CoreTree, levelCore w' ≤ fuel →
      let res := aCoreFn w'
      ∃ r', EraRound (evalCore w') (rep010 res.p r') ∧ Sweeps res.c r' (evalU res.u))
    (hu : 3 * k + levelCore w ≤ fuel) :
    let res := aPullSucc aCoreFn k w
    ∃ r', EraRound (rep010 k (evalCore w)) (rep010 res.p r') ∧ Sweeps res.c r' (evalU res.u) := by
  dsimp only
  cases htag : coreTagIdx w with
  | some t =>
    have ht_le : t ≤ 3 ∧ levelCore w = t + 1 := by
      cases w <;> simp [coreTagIdx] at htag <;> subst htag <;> simp [levelCore]
    rcases (by omega : k + t ≤ 3 ∨ ¬(k + t ≤ 3)) with hs_le | hs_gt
    · simp only [aPullSucc, htag, hs_le, ↓reduceIte]
      have h_mk : levelCore (mkSw (k + t)) = k + t + 1 := by
        rcases (by omega : k + t = 1 ∨ k + t = 2 ∨ k + t = 3) with h1 | h2 | h3
        · rw [h1]; rfl
        · rw [h2]; rfl
        · rw [h3]; rfl
      have h_lvl : levelCore (mkSw (k + t)) ≤ fuel := by omega
      obtain ⟨r', hE, hS⟩ := ha (mkSw (k + t)) h_lvl
      refine ⟨r', ?_, hS⟩
      have h_sw : Sweeps k (evalCore w) (evalCore (mkSw (k + t))) := by
        have h_step := stepCore_sound k w
        rw [stepCore_eq_stepDefault htag] at h_step
        have h_eq : stepDefault (k + t) = (0, mkSw (k + t)) := by
          rcases (by omega : k + t = 1 ∨ k + t = 2 ∨ k + t = 3) with h1 | h2 | h3
          · rw [h1]; rfl
          · rw [h2]; rfl
          · rw [h3]; rfl
        simpa [h_eq, evalU, rep010] using h_step
      have hE_rep := eraRound_rep010 h_sw hE
      rwa [← rep010_add] at hE_rep
    · simp only [aPullSucc, htag, hs_gt, ↓reduceIte]
      have hs4 : 4 ≤ k + t := by omega
      have h_lvl : levelCore (stepDiv0Sw0 (k + t - 3)) ≤ fuel := by
        rw [levelCore_stepDiv0Sw0]; omega
      obtain ⟨r', hE, hS⟩ := ha (stepDiv0Sw0 (k + t - 3)) h_lvl
      refine ⟨r', ?_, hS⟩
      have h_step := stepCore_sound k w
      rw [stepCore_eq_stepDefault htag, show k + t = (k + t - 4) + 4 by omega, stepDefault_add4_eq] at h_step
      change Sweeps k (evalCore w) ([0, 1, 0] +> evalCore (stepDiv0Sw0 (k + t - 4))) at h_step
      have h1 : Round (evalCore (stepDiv0Sw0 (k + t - 4))) (evalCore (stepDiv0Sw0 (k + t - 3))) := by
        have := round_stepDiv0Sw0 (k + t - 4)
        rwa [show k + t - 4 + 1 = k + t - 3 by omega] at this
      have hE1 := eraRound_010 h1 hE
      have hE_rep := eraRound_rep010 h_step hE1
      have h_eq_r : rep010 k ([0, 1, 0] +> rep010 (aCoreFn (stepDiv0Sw0 (k + t - 3))).p r') =
          rep010 (k + 1 + (aCoreFn (stepDiv0Sw0 (k + t - 3))).p) r' := by
        change rep010 k (rep010 1 (rep010 (aCoreFn (stepDiv0Sw0 (k + t - 3))).p r')) = _
        rw [← rep010_add, ← rep010_add]
      rwa [h_eq_r] at hE_rep
  | none =>
    simp only [aPullSucc, htag]
    have h_lvl : levelCore (stepDivCore k w) ≤ fuel := by
      rw [levelCore_stepDivCore k w htag]; omega
    obtain ⟨r', hE, hS⟩ := ha (stepDivCore k w) h_lvl
    refine ⟨r', ?_, hS⟩
    have h_sw := stepDivCore_sound k w htag
    have hE_rep := eraRound_rep010 h_sw hE
    rwa [← rep010_add] at hE_rep

lemma aPullFrom_sound {aCoreFn : CoreTree → ResP} {fuel : Nat}
    (ha : ∀ w : CoreTree, levelCore w ≤ fuel →
      let res := aCoreFn w
      ∃ r', EraRound (evalCore w) (rep010 res.p r') ∧ Sweeps res.c r' (evalU res.u))
    (u : UTree) (hu : levelU u ≤ fuel) :
    let res := aPullFrom aCoreFn u
    ∃ r', EraRound (evalU u) (rep010 res.p r') ∧ Sweeps res.c r' (evalU res.u) := by
  rcases u with ⟨_ | k', w⟩
  · have hcw : levelCore w ≤ fuel := by unfold levelU at hu; dsimp only at hu; omega
    exact ha w hcw
  · have hlu : levelU (k' + 1, w) = 3 * (k' + 1) + levelCore w := rfl
    rw [hlu] at hu
    exact aPullSucc_sound (by omega : 1 ≤ k' + 1) ha hu

lemma opsAux_sound : ∀ (fuel : Nat),
    (∀ w : CoreTree, levelCore w ≤ fuel →
      let res := (opsAux fuel).bCore w
      Sweeps res.c (pB (evalCore w)) (evalU res.u)) ∧
    (∀ w : CoreTree, levelCore w ≤ fuel →
      let res := (opsAux fuel).aCore w
      ∃ r', EraRound (evalCore w) (rep010 res.p r') ∧ Sweeps res.c r' (evalU res.u))
  | 0 => ⟨fun w hw => by have := levelCore_pos w; omega,
          fun w hw => by have := levelCore_pos w; omega⟩
  | fuel + 1 => by
    obtain ⟨ihB, ihA⟩ := opsAux_sound fuel
    refine ⟨?_, ?_⟩
    · intro w hw
      cases w with
      | sw0 => exact bCore_sw0_sound
      | sw1 => exact bCore_sw1_sound
      | sw2 => exact bCore_sw2_sound
      | sw3 => exact bCore_sw3_sound
      | div0 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; exact bCore_div0_sw0_sound
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u1_lvl : levelU (stepU 1 (k, ch)) ≤ fuel := by
            rw [levelU_stepU]; simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          have h1 := round_of_sweeps_one (stepU_sound 1 (k, ch))
          have h6 := sweeps_pB_pDiv0 h1
          have hsub := bUFrom_sound ihB (stepU 1 (k, ch)) h_u1_lvl
          have hsub' := sweeps_rep010 2 hsub
          have htr := Sweeps.trans h6 hsub'
          simpa [evalCore, evalU, rep010_add] using htr
      | div1 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; exact bCore_div1_sw0_sound
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u1_lvl : levelU (stepU 1 (k, ch)) ≤ fuel := by
            rw [levelU_stepU]; simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          have h1 := round_of_sweeps_one (stepU_sound 1 (k, ch))
          obtain ⟨r', hE, hS⟩ := aPullFrom_sound ihA (stepU 1 (k, ch)) h_u1_lvl
          have h3 := sweeps_pB_pDiv1 h1 hE
          have hS_rep := sweeps_rep010 (aPullFrom (opsAux fuel).aCore (stepU 1 (k, ch))).p hS
          have h2c := sweeps_010 (sweeps_pDiv0_even (sweeps_010 hS_rep))
          have htr := Sweeps.trans h3 h2c
          simpa [evalU, evalCore, rep010, rep010_add, Nat.add_assoc] using htr
    · intro w hw
      cases w with
      | sw0 => exact ⟨evalCore .sw1, aCore_sw0_sound, Sweeps.zero _⟩
      | sw1 => exact ⟨evalCore .sw1, aCore_sw1_sound, Sweeps.zero _⟩
      | sw2 => exact aCore_sw2_sound
      | sw3 => exact aCore_sw3_sound
      | div0 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; exact aCore_div0_sw0_sound
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u_lvl : levelU (k, ch) ≤ fuel := by
            simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          have hsub := bUFrom_sound ihB (k, ch) h_u_lvl
          exact ⟨pB (evalU (k, ch)), eraRound_pDiv0 (evalU (k, ch)), hsub⟩
      | div1 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; exact ⟨evalCore .sw1, aCore_div1_sw0_sound, Sweeps.zero _⟩
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u1_lvl : levelU (stepU 1 (k, ch)) ≤ fuel := by
            rw [levelU_stepU]; simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          have h1 := round_of_sweeps_one (stepU_sound 1 (k, ch))
          obtain ⟨r', hE, hS⟩ := aPullFrom_sound ihA (stepU 1 (k, ch)) h_u1_lvl
          have hE' := eraRound_pDiv1 h1 hE
          refine ⟨r', ?_, hS⟩
          simpa [evalCore, evalU, rep010_add] using hE'

-- ============================================================================
-- Section 7: 4-Piecewise Linear Arithmetic Bounds (CB4, CA4, DB4, DAC4, DAU4)
-- ============================================================================

def min4 (a b c d : Nat) : Nat := min (min a b) (min c d)

def CB4 (x : Nat) : Nat := min4 (6 * x - 3) (3 * x + 10) ((3 * x) / 2 + 25) ((11 * x) / 16 + 67)
def CA4 (x : Nat) : Nat := min4 (3 * x) ((3 * x) / 2 + 10) ((3 * x) / 4 + 25) ((3 * x) / 8 + 64)
def DB4 (x : Nat) : Nat := min4 (6 * x - 2) (3 * x + 31) ((3 * x) / 2 + 70) ((5 * x) / 4 + 150)
def DAC4 (x : Nat) : Nat := min4 (4 * x - 1) ((3 * x) / 2 + 31) ((3 * x) / 4 + 70) ((21 * x) / 32 + 130)
def DAU4 (x : Nat) : Nat := min4 (4 * x - 1) ((9 * x) / 4 + 21) ((3 * x) / 2 + 31) ((5 * x) / 4 + 71)

def CAP (x : Nat) : Nat := max 11 (CB4 (x / 2))
def DAP (x : Nat) : Nat := max 7 (DB4 (x / 2))

lemma le_min4 {x a b c d : Nat} (ha : x ≤ a) (hb : x ≤ b) (hc : x ≤ c) (hd : x ≤ d) :
    x ≤ min4 a b c d := by
  unfold min4; exact le_min (le_min ha hb) (le_min hc hd)

lemma le_of_min4_1 {y a b c d : Nat} (h : y ≤ min4 a b c d) : y ≤ a :=
  le_trans h (le_trans (min_le_left _ _) (min_le_left _ _))
lemma le_of_min4_2 {y a b c d : Nat} (h : y ≤ min4 a b c d) : y ≤ b :=
  le_trans h (le_trans (min_le_left _ _) (min_le_right _ _))
lemma le_of_min4_3 {y a b c d : Nat} (h : y ≤ min4 a b c d) : y ≤ c :=
  le_trans h (le_trans (min_le_right _ _) (min_le_left _ _))
lemma le_of_min4_4 {y a b c d : Nat} (h : y ≤ min4 a b c d) : y ≤ d :=
  le_trans h (le_trans (min_le_right _ _) (min_le_right _ _))

lemma CB4_le (x : Nat) :
    CB4 x ≤ 6 * x - 3 ∧ CB4 x ≤ 3 * x + 10 ∧ CB4 x ≤ (3 * x) / 2 + 25 ∧ CB4 x ≤ (11 * x) / 16 + 67 := by
  have hd : CB4 x ≤ min4 (6 * x - 3) (3 * x + 10) ((3 * x) / 2 + 25) ((11 * x) / 16 + 67) := le_refl _
  exact ⟨le_of_min4_1 hd, le_of_min4_2 hd, le_of_min4_3 hd, le_of_min4_4 hd⟩

lemma CA4_le (x : Nat) :
    CA4 x ≤ 3 * x ∧ CA4 x ≤ (3 * x) / 2 + 10 ∧ CA4 x ≤ (3 * x) / 4 + 25 ∧ CA4 x ≤ (3 * x) / 8 + 64 := by
  have hd : CA4 x ≤ min4 (3 * x) ((3 * x) / 2 + 10) ((3 * x) / 4 + 25) ((3 * x) / 8 + 64) := le_refl _
  exact ⟨le_of_min4_1 hd, le_of_min4_2 hd, le_of_min4_3 hd, le_of_min4_4 hd⟩

lemma DB4_le (x : Nat) :
    DB4 x ≤ 6 * x - 2 ∧ DB4 x ≤ 3 * x + 31 ∧ DB4 x ≤ (3 * x) / 2 + 70 ∧ DB4 x ≤ (5 * x) / 4 + 150 := by
  have hd : DB4 x ≤ min4 (6 * x - 2) (3 * x + 31) ((3 * x) / 2 + 70) ((5 * x) / 4 + 150) := le_refl _
  exact ⟨le_of_min4_1 hd, le_of_min4_2 hd, le_of_min4_3 hd, le_of_min4_4 hd⟩

lemma DAC4_le (x : Nat) :
    DAC4 x ≤ 4 * x - 1 ∧ DAC4 x ≤ (3 * x) / 2 + 31 ∧ DAC4 x ≤ (3 * x) / 4 + 70 ∧ DAC4 x ≤ (21 * x) / 32 + 130 := by
  have hd : DAC4 x ≤ min4 (4 * x - 1) ((3 * x) / 2 + 31) ((3 * x) / 4 + 70) ((21 * x) / 32 + 130) := le_refl _
  exact ⟨le_of_min4_1 hd, le_of_min4_2 hd, le_of_min4_3 hd, le_of_min4_4 hd⟩

lemma DAU4_le (x : Nat) :
    DAU4 x ≤ 4 * x - 1 ∧ DAU4 x ≤ (9 * x) / 4 + 21 ∧ DAU4 x ≤ (3 * x) / 2 + 31 ∧ DAU4 x ≤ (5 * x) / 4 + 71 := by
  have hd : DAU4 x ≤ min4 (4 * x - 1) ((9 * x) / 4 + 21) ((3 * x) / 2 + 31) ((5 * x) / 4 + 71) := le_refl _
  exact ⟨le_of_min4_1 hd, le_of_min4_2 hd, le_of_min4_3 hd, le_of_min4_4 hd⟩

lemma CB4_mono {x y : Nat} (h : x ≤ y) : CB4 x ≤ CB4 y := by
  obtain ⟨h1, h2, h3, h4⟩ := CB4_le x
  conv_rhs => unfold CB4
  refine le_min4 (by omega) (by omega) (by omega) (by omega)

lemma CA4_mono {x y : Nat} (h : x ≤ y) : CA4 x ≤ CA4 y := by
  obtain ⟨h1, h2, h3, h4⟩ := CA4_le x
  conv_rhs => unfold CA4
  refine le_min4 (by omega) (by omega) (by omega) (by omega)

lemma DB4_mono {x y : Nat} (h : x ≤ y) : DB4 x ≤ DB4 y := by
  obtain ⟨h1, h2, h3, h4⟩ := DB4_le x
  conv_rhs => unfold DB4
  refine le_min4 (by omega) (by omega) (by omega) (by omega)

lemma CAP_mono {x y : Nat} (h : x ≤ y) : CAP x ≤ CAP y := by
  have hcb := CB4_mono (by omega : x / 2 ≤ y / 2)
  unfold CAP; omega

lemma DAP_mono {x y : Nat} (h : x ≤ y) : DAP x ≤ DAP y := by
  have hdb := DB4_mono (by omega : x / 2 ≤ y / 2)
  unfold DAP; omega

lemma bound_bCore_div0 {m c1 lu1 : Nat} (hm : 2 ≤ m)
    (hc : c1 ≤ CB4 (m + 1)) (hd : lu1 ≤ c1 + DB4 (m + 1)) :
    6 + c1 ≤ CB4 (2 * m) ∧ 6 + lu1 ≤ (6 + c1) + DB4 (2 * m) := by
  obtain ⟨h1, h2, h3, h4⟩ := CB4_le (m + 1)
  have hd_m := DB4_mono (by omega : m + 1 ≤ 2 * m)
  refine ⟨?_, by omega⟩
  unfold CB4; refine le_min4 (by omega) (by omega) (by omega) (by omega)

lemma bound_bCore_div1 {m c1 p1 lu1 : Nat} (hm : 2 ≤ m)
    (hc : c1 ≤ CA4 (m + 1)) (hd : 3 * p1 + lu1 ≤ c1 + DAU4 (m + 1)) :
    3 + 2 * c1 ≤ CB4 (2 * m + 1) ∧
    9 + 2 * (3 * p1 + lu1) ≤ (3 + 2 * c1) + DB4 (2 * m + 1) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := CA4_le (m + 1)
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DAU4_le (m + 1)
  refine ⟨?_, ?_⟩
  · unfold CB4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
  · have h_db : 6 + 2 * DAU4 (m + 1) ≤ DB4 (2 * m + 1) := by
      unfold DB4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega

lemma bound_bUFrom (k : Nat) {mc c0 lu0 : Nat} (hmc : 1 ≤ mc)
    (hc : c0 ≤ CB4 mc) (hd : lu0 ≤ c0 + DB4 mc) :
    2 * k + c0 ≤ CB4 (3 * k + mc) ∧ 3 * k + lu0 ≤ (2 * k + c0) + DB4 (3 * k + mc) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := CB4_le mc
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DB4_le mc
  refine ⟨?_, ?_⟩
  · conv_rhs => unfold CB4
    refine le_min4 (by omega) (by omega) (by omega) (by omega)
  · have h_db : k + DB4 mc ≤ DB4 (3 * k + mc) := by
      conv_rhs => unfold DB4
      refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega

lemma bound_aCore_div0 {m c0 lu0 : Nat} (hm : 2 ≤ m)
    (hc : c0 ≤ CB4 m) (hd : lu0 ≤ c0 + DB4 m) :
    c0 ≤ CA4 (2 * m) ∧ c0 ≤ CAP (2 * m) ∧
    lu0 ≤ c0 + DAC4 (2 * m) ∧ lu0 ≤ c0 + DAP (2 * m) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := CB4_le m
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DB4_le m
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CA4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
  · unfold CAP; have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]; exact le_trans hc (le_max_right _ _)
  · have h_da : DB4 m ≤ DAC4 (2 * m) := by
      unfold DAC4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega
  · unfold DAP; have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]; have : DB4 m ≤ max 7 (DB4 m) := le_max_right _ _
    omega

lemma bound_aCore_div1 {m c1 p1 lu1 : Nat} (hm : 2 ≤ m)
    (hc : c1 ≤ CA4 (m + 1)) (hcap : c1 ≤ CAP (m + 1))
    (hd : 3 * p1 + lu1 ≤ c1 + DAU4 (m + 1)) (hdap : lu1 ≤ c1 + DAP (m + 1)) :
    c1 ≤ CA4 (2 * m + 1) ∧ c1 ≤ CAP (2 * m + 1) ∧
    3 * (2 + p1) + lu1 ≤ c1 + DAC4 (2 * m + 1) ∧ lu1 ≤ c1 + DAP (2 * m + 1) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DAU4_le (m + 1)
  refine ⟨le_trans hc (CA4_mono (by omega)), le_trans hcap (CAP_mono (by omega)), ?_, ?_⟩
  · have h_da : 6 + DAU4 (m + 1) ≤ DAC4 (2 * m + 1) := by
      unfold DAC4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega
  · exact le_trans hdap (Nat.add_le_add_left (DAP_mono (by omega)) c1)

lemma bound_aPull_sw_le {k t c0 p0 lu0 : Nat} (hk : 1 ≤ k) (hs : k + t ≤ 3)
    (hc : c0 ≤ CA4 (k + t + 1)) (hcap : c0 ≤ CAP (k + t + 1))
    (hd : 3 * p0 + lu0 ≤ c0 + DAC4 (k + t + 1)) (hdap : lu0 ≤ c0 + DAP (k + t + 1)) :
    c0 ≤ CA4 (3 * k + (t + 1)) ∧ c0 ≤ CAP (3 * k + (t + 1)) ∧
    3 * (k + p0) + lu0 ≤ c0 + DAU4 (3 * k + (t + 1)) ∧
    lu0 ≤ c0 + DAP (3 * k + (t + 1)) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DAC4_le (k + t + 1)
  refine ⟨le_trans hc (CA4_mono (by omega)), le_trans hcap (CAP_mono (by omega)), ?_, ?_⟩
  · have h_da : 3 * k + DAC4 (k + t + 1) ≤ DAU4 (3 * k + (t + 1)) := by
      unfold DAU4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega
  · exact le_trans hdap (Nat.add_le_add_left (DAP_mono (by omega)) c0)

lemma bound_aPull_sw_gt {k t c0 p0 lu0 : Nat} (hk : 1 ≤ k) (ht : t ≤ 3) (hs : 4 ≤ k + t)
    (hc : c0 ≤ CA4 (k + t - 1)) (hcap : c0 ≤ CAP (k + t - 1))
    (hd : 3 * p0 + lu0 ≤ c0 + DAC4 (k + t - 1)) (hdap : lu0 ≤ c0 + DAP (k + t - 1)) :
    c0 ≤ CA4 (3 * k + (t + 1)) ∧ c0 ≤ CAP (3 * k + (t + 1)) ∧
    3 * (k + 1 + p0) + lu0 ≤ c0 + DAU4 (3 * k + (t + 1)) ∧
    lu0 ≤ c0 + DAP (3 * k + (t + 1)) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DAC4_le (k + t - 1)
  refine ⟨le_trans hc (CA4_mono (by omega)), le_trans hcap (CAP_mono (by omega)), ?_, ?_⟩
  · have h_da : 3 * (k + 1) + DAC4 (k + t - 1) ≤ DAU4 (3 * k + (t + 1)) := by
      unfold DAU4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega
  · exact le_trans hdap (Nat.add_le_add_left (DAP_mono (by omega)) c0)

lemma bound_aPull_div {k mc c0 p0 lu0 : Nat} (hk : 1 ≤ k) (hmc : 2 ≤ mc)
    (hc : c0 ≤ CA4 (mc + k)) (hcap : c0 ≤ CAP (mc + k))
    (hd : 3 * p0 + lu0 ≤ c0 + DAC4 (mc + k)) (hdap : lu0 ≤ c0 + DAP (mc + k)) :
    c0 ≤ CA4 (3 * k + mc) ∧ c0 ≤ CAP (3 * k + mc) ∧
    3 * (k + p0) + lu0 ≤ c0 + DAU4 (3 * k + mc) ∧
    lu0 ≤ c0 + DAP (3 * k + mc) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := DAC4_le (mc + k)
  refine ⟨le_trans hc (CA4_mono (by omega)), le_trans hcap (CAP_mono (by omega)), ?_, ?_⟩
  · have h_da : 3 * k + DAC4 (mc + k) ≤ DAU4 (3 * k + mc) := by
      unfold DAU4; refine le_min4 (by omega) (by omega) (by omega) (by omega)
    omega
  · exact le_trans hdap (Nat.add_le_add_left (DAP_mono (by omega)) c0)

lemma bUFrom_bounds {bCoreFn : CoreTree → ResB} {fuel : Nat}
    (hb : ∀ w : CoreTree, levelCore w ≤ fuel →
      let res := bCoreFn w
      res.c ≤ CB4 (levelCore w) ∧ levelU res.u ≤ res.c + DB4 (levelCore w))
    (u : UTree) (hu : levelU u ≤ fuel) :
    let res := bUFrom bCoreFn u
    res.c ≤ CB4 (levelU u) ∧ levelU res.u ≤ res.c + DB4 (levelU u) := by
  rcases u with ⟨k, w⟩
  have hcw : levelCore w ≤ fuel := by unfold levelU at hu; dsimp only at hu; omega
  obtain ⟨hc, hd⟩ := hb w hcw
  have hres := bound_bUFrom k (levelCore_pos w) hc hd
  unfold bUFrom levelU at *
  dsimp only at *
  simpa [Nat.mul_add, Nat.add_assoc] using hres

lemma levelCore_ge_two_of_none {w : CoreTree} (hw : coreTagIdx w = none) :
    2 ≤ levelCore w := by
  cases w with
  | sw0 | sw1 | sw2 | sw3 => nomatch hw
  | div0 k ch => have := levelCore_pos ch; simp [levelCore]; omega
  | div1 k ch => have := levelCore_pos ch; simp [levelCore]; omega

lemma DAC4_le_DAU4 (x : Nat) : DAC4 x ≤ DAU4 x := by
  obtain ⟨h1, h2, h3, h4⟩ := DAC4_le x
  conv_rhs => unfold DAU4
  rcases (by omega : x ≤ 12 ∨ x = 13 ∨ x = 14 ∨ 15 ≤ x) with hx | rfl | rfl | hx
  · refine le_min4 (by omega) (by omega) (by omega) (by omega)
  · decide
  · decide
  · refine le_min4 (by omega) (by omega) (by omega) (by omega)

lemma aPullSucc_bounds {aCoreFn : CoreTree → ResP} {fuel k : Nat} {w : CoreTree}
    (hk : 1 ≤ k)
    (ha : ∀ w' : CoreTree, levelCore w' ≤ fuel →
      let res := aCoreFn w'
      res.c ≤ CA4 (levelCore w') ∧ res.c ≤ CAP (levelCore w') ∧
      3 * res.p + levelU res.u ≤ res.c + DAC4 (levelCore w') ∧
      levelU res.u ≤ res.c + DAP (levelCore w'))
    (hu : 3 * k + levelCore w ≤ fuel) :
    let res := aPullSucc aCoreFn k w
    res.c ≤ CA4 (3 * k + levelCore w) ∧ res.c ≤ CAP (3 * k + levelCore w) ∧
    3 * res.p + levelU res.u ≤ res.c + DAU4 (3 * k + levelCore w) ∧
    levelU res.u ≤ res.c + DAP (3 * k + levelCore w) := by
  dsimp only
  cases htag : coreTagIdx w with
  | some t =>
    have ht_le : t ≤ 3 ∧ levelCore w = t + 1 := by
      cases w <;> simp [coreTagIdx] at htag <;> subst htag <;> simp [levelCore]
    rcases (by omega : k + t ≤ 3 ∨ ¬(k + t ≤ 3)) with hs_le | hs_gt
    · simp only [aPullSucc, htag, hs_le, ↓reduceIte]
      have h_mk : levelCore (mkSw (k + t)) = k + t + 1 := by
        rcases (by omega : k + t = 1 ∨ k + t = 2 ∨ k + t = 3) with h1 | h2 | h3
        · rw [h1]; rfl
        · rw [h2]; rfl
        · rw [h3]; rfl
      have h_lvl : levelCore (mkSw (k + t)) ≤ fuel := by omega
      obtain ⟨hc, hcap, hd, hdap⟩ := ha (mkSw (k + t)) h_lvl
      rw [h_mk] at hc hcap hd hdap
      rw [ht_le.2]
      exact bound_aPull_sw_le hk hs_le hc hcap hd hdap
    · simp only [aPullSucc, htag, hs_gt, ↓reduceIte]
      have hs4 : 4 ≤ k + t := by omega
      have h_mk : levelCore (stepDiv0Sw0 (k + t - 3)) = k + t - 1 := by
        rw [levelCore_stepDiv0Sw0]; omega
      have h_lvl : levelCore (stepDiv0Sw0 (k + t - 3)) ≤ fuel := by omega
      obtain ⟨hc, hcap, hd, hdap⟩ := ha (stepDiv0Sw0 (k + t - 3)) h_lvl
      rw [h_mk] at hc hcap hd hdap
      rw [ht_le.2]
      exact bound_aPull_sw_gt hk ht_le.1 hs4 hc hcap hd hdap
  | none =>
    simp only [aPullSucc, htag]
    have hmc2 := levelCore_ge_two_of_none htag
    have h_mk := levelCore_stepDivCore k w htag
    have h_lvl : levelCore (stepDivCore k w) ≤ fuel := by omega
    obtain ⟨hc, hcap, hd, hdap⟩ := ha (stepDivCore k w) h_lvl
    rw [h_mk] at hc hcap hd hdap
    exact bound_aPull_div hk hmc2 hc hcap hd hdap

lemma aPullFrom_bounds {aCoreFn : CoreTree → ResP} {fuel : Nat}
    (ha : ∀ w : CoreTree, levelCore w ≤ fuel →
      let res := aCoreFn w
      res.c ≤ CA4 (levelCore w) ∧ res.c ≤ CAP (levelCore w) ∧
      3 * res.p + levelU res.u ≤ res.c + DAC4 (levelCore w) ∧
      levelU res.u ≤ res.c + DAP (levelCore w))
    (u : UTree) (hu : levelU u ≤ fuel) :
    let res := aPullFrom aCoreFn u
    res.c ≤ CA4 (levelU u) ∧ res.c ≤ CAP (levelU u) ∧
    3 * res.p + levelU res.u ≤ res.c + DAU4 (levelU u) ∧
    levelU res.u ≤ res.c + DAP (levelU u) := by
  rcases u with ⟨_ | k', w⟩
  · have hlu0 : levelU (0, w) = levelCore w := by simp [levelU]
    have hcw : levelCore w ≤ fuel := by rw [← hlu0]; exact hu
    obtain ⟨hc, hcap, hd, hdap⟩ := ha w hcw
    have hd_u := DAC4_le_DAU4 (levelCore w)
    dsimp only [aPullFrom]
    rw [hlu0]
    exact ⟨hc, hcap, by omega, hdap⟩
  · have hlu : levelU (k' + 1, w) = 3 * (k' + 1) + levelCore w := rfl
    rw [hlu] at hu ⊢
    dsimp only [aPullFrom]
    exact aPullSucc_bounds (by omega : 1 ≤ k' + 1) ha hu

lemma opsAux_bounds : ∀ (fuel : Nat),
    (∀ w : CoreTree, levelCore w ≤ fuel →
      let res := (opsAux fuel).bCore w
      res.c ≤ CB4 (levelCore w) ∧ levelU res.u ≤ res.c + DB4 (levelCore w)) ∧
    (∀ w : CoreTree, levelCore w ≤ fuel →
      let res := (opsAux fuel).aCore w
      res.c ≤ CA4 (levelCore w) ∧ res.c ≤ CAP (levelCore w) ∧
      3 * res.p + levelU res.u ≤ res.c + DAC4 (levelCore w) ∧
      levelU res.u ≤ res.c + DAP (levelCore w))
  | 0 => ⟨fun w hw => by have := levelCore_pos w; omega,
          fun w hw => by have := levelCore_pos w; omega⟩
  | fuel + 1 => by
    obtain ⟨ihB, ihA⟩ := opsAux_bounds fuel
    refine ⟨?_, ?_⟩
    · intro w hw
      cases w with
      | sw0 => unfold opsAux; dsimp only; decide
      | sw1 => unfold opsAux; dsimp only; decide
      | sw2 => unfold opsAux; dsimp only; decide
      | sw3 => unfold opsAux; dsimp only; decide
      | div0 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; decide
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u1_lvl : levelU (stepU 1 (k, ch)) ≤ fuel := by
            rw [levelU_stepU]; simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          obtain ⟨hc, hd⟩ := bUFrom_bounds ihB (stepU 1 (k, ch)) h_u1_lvl
          rw [levelU_stepU] at hc hd
          have hres := bound_bCore_div0 hm2 hc hd
          simpa [levelCore, levelU, Nat.mul_add, Nat.add_assoc] using hres
      | div1 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; decide
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u1_lvl : levelU (stepU 1 (k, ch)) ≤ fuel := by
            rw [levelU_stepU]; simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          obtain ⟨hc, _, hd, _⟩ := aPullFrom_bounds ihA (stepU 1 (k, ch)) h_u1_lvl
          rw [levelU_stepU] at hc hd
          have hres := bound_bCore_div1 hm2 hc hd
          refine ⟨hres.1, ?_⟩
          have h_lu : levelU (1, .div0 (1 + (aPullFrom (opsAux fuel).aCore (stepU 1 (k, ch))).p + (aPullFrom (opsAux fuel).aCore (stepU 1 (k, ch))).u.1) (aPullFrom (opsAux fuel).aCore (stepU 1 (k, ch))).u.2) =
              9 + 2 * (3 * (aPullFrom (opsAux fuel).aCore (stepU 1 (k, ch))).p + levelU (aPullFrom (opsAux fuel).aCore (stepU 1 (k, ch))).u) := by
            simp [levelU, levelCore]; omega
          rw [h_lu]; exact hres.2
    · intro w hw
      cases w with
      | sw0 => unfold opsAux; dsimp only; decide
      | sw1 => unfold opsAux; dsimp only; decide
      | sw2 => unfold opsAux; dsimp only; decide
      | sw3 => unfold opsAux; dsimp only; decide
      | div0 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; decide
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u_lvl : levelU (k, ch) ≤ fuel := by
            simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          obtain ⟨hc, hd⟩ := bUFrom_bounds ihB (k, ch) h_u_lvl
          have hres := bound_aCore_div0 hm2 hc hd
          simpa [levelCore, levelU] using hres
      | div1 k ch =>
        unfold opsAux
        dsimp only
        split
        · next h0 => obtain ⟨rfl, rfl⟩ := h0; decide
        · next hne =>
          have hm2 := levelU_gt_one_of_ne_sw0 hne
          have h_u1_lvl : levelU (stepU 1 (k, ch)) ≤ fuel := by
            rw [levelU_stepU]; simp [levelCore] at hw; unfold levelU at hm2 ⊢; dsimp only at *; omega
          obtain ⟨hc, hcap, hd, hdap⟩ := aPullFrom_bounds ihA (stepU 1 (k, ch)) h_u1_lvl
          rw [levelU_stepU] at hc hcap hd hdap
          have hres := bound_aCore_div1 hm2 hc hcap hd hdap
          simpa [levelCore, levelU] using hres

-- ============================================================================
-- Section 8: Finite Bridge (init -> Era 1 -> Era 133) & Infinite Invariant
-- ============================================================================

def eraStepBool (fuel : Nat) (bs : List Bool) : Option (List Bool) :=
  match pad7B bs with
  | false :: v => (roundBool fuel v).map (fun r' => false :: true :: false :: r')
  | _ => none

lemma eraStepBool_sound (fuel : Nat) (bs ys : List Bool)
    (h : eraStepBool fuel bs = some ys) :
    (default <{{E}} (toTape bs)) [target_tm]⊢⁺ (default <{{E}} (toTape ys)) := by
  rw [← toTape_pad7B bs]
  unfold eraStepBool at h
  generalize pad7B bs = pbs at h ⊢
  split at h
  · obtain ⟨r', hr', rfl⟩ := opt_map_some h
    rename_i v
    exact eraRound_tm_step ⟨toTape v, rfl, roundBool_sound fuel v r' hr'⟩
  · nomatch h

def eraStepsBool (fuel : Nat) : Nat → List Bool → Option (List Bool)
  | 0, bs => some bs
  | m + 1, bs =>
    match eraStepBool fuel bs with
    | some bs1 => eraStepsBool fuel m bs1
    | none => none

lemma eraStepsBool_sound (fuel : Nat) : ∀ (m : Nat) (bs ys : List Bool),
    eraStepsBool fuel m bs = some ys →
    (default <{{E}} (toTape bs)) [target_tm]⊢* (default <{{E}} (toTape ys))
  | 0, bs, ys, h => by injection h with h; subst h; exact ⟨0, rfl⟩
  | m + 1, bs, ys, h => by
    unfold eraStepsBool at h
    cases hs : eraStepBool fuel bs with
    | none => rw [hs] at h; nomatch h
    | some bs1 =>
      rw [hs] at h
      exact stepStar_trans (stepPlus_stepStar (eraStepBool_sound fuel bs bs1 hs))
        (eraStepsBool_sound fuel m bs1 ys h)

def rep010Bool : Nat → List Bool → List Bool
  | 0, bs => bs
  | k + 1, bs => false :: true :: false :: rep010Bool k bs

lemma toTape_rep010Bool (k : Nat) (bs : List Bool) :
    toTape (rep010Bool k bs) = rep010 k (toTape bs) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rep010Bool, rep010, toTape, b2f, ih]

lemma init_reaches_era0 :
    (init []) [target_tm]⊢⁺ (default <{{E}} (toTape [false, true])) := by
  dsimp [init, Tape.mk₁, toTape, b2f]; execute

lemma init_reaches_era1 :
    (init []) [target_tm]⊢* (default <{{E}} (rep010 3 (evalCore .sw1))) := by
  have h1 : (eraStepsBool 20 1 [false, true]).map dropTrailingFalse =
      some (rep010Bool 3 [false, false, true]) := rfl
  obtain ⟨ys, hys, hdrop⟩ := opt_map_some h1
  have hstar := eraStepsBool_sound 20 1 [false, true] ys hys
  have h_ys : toTape ys = rep010 3 (evalCore .sw1) := by
    rw [← toTape_dropTrailingFalse ys, hdrop, toTape_rep010Bool]
    simp [toTape, b2f, evalCore, zero_cons_default]
  rw [h_ys] at hstar
  exact stepStar_trans (stepPlus_stepStar init_reaches_era0) hstar

def stepEraU (N : Nat) (u : UTree) : Option (Nat × UTree) :=
  let res := aPullFrom (opsAux (levelU u)).aCore u
  let N' := N + 1 + res.p
  if res.c ≤ N' then
    some (N', stepU (N' - res.c) res.u)
  else
    none

lemma stepEraU_sound {N N' : Nat} {rem : ListBlank (Fin 2)} {u u' : UTree}
    (hS : Sweeps N rem (evalU u)) (hstep : stepEraU N u = some (N', u')) :
    ∃ rem', ((default <{{E}} (rep010 N rem)) [target_tm]⊢⁺ (default <{{E}} (rep010 N' rem'))) ∧
      Sweeps N' rem' (evalU u') := by
  unfold stepEraU at hstep
  dsimp only at hstep
  split at hstep
  · next hle =>
    injection hstep with h1; injection h1 with hN' hu'
    subst hN' hu'
    have ha := (opsAux_sound (levelU u)).2
    obtain ⟨r', hE, hSr⟩ := aPullFrom_sound ha u (le_refl _)
    have hE_rep := eraRound_rep010 hS hE
    have htm := eraRound_tm_step hE_rep
    rw [← rep010_add] at htm
    have h_eq : [0, 1, 0] +> rep010 (N + (aPullFrom (opsAux (levelU u)).aCore u).p) r' =
        rep010 (N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p) r' := by
      rw [show N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p =
          (N + (aPullFrom (opsAux (levelU u)).aCore u).p) + 1 by omega]
      rfl
    rw [h_eq] at htm
    have hSu := stepU_sound ((N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p) - (aPullFrom (opsAux (levelU u)).aCore u).c) (aPullFrom (opsAux (levelU u)).aCore u).u
    have htr := Sweeps.trans hSr hSu
    rw [show (aPullFrom (opsAux (levelU u)).aCore u).c + ((N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p) - (aPullFrom (opsAux (levelU u)).aCore u).c) =
        N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p by omega] at htr
    exact ⟨r', htm, htr⟩
  · nomatch hstep

def runEras : Nat → Nat → UTree → Option (Nat × UTree)
  | 0, N, u => some (N, u)
  | m + 1, N, u =>
    match stepEraU N u with
    | some (N', u') => runEras m N' u'
    | none => none

lemma runEras_sound : ∀ (m N N_m : Nat) (rem : ListBlank (Fin 2)) (u u_m : UTree),
    Sweeps N rem (evalU u) → runEras m N u = some (N_m, u_m) →
    ∃ rem_m, ((default <{{E}} (rep010 N rem)) [target_tm]⊢* (default <{{E}} (rep010 N_m rem_m))) ∧
      Sweeps N_m rem_m (evalU u_m)
  | 0, N, N_m, rem, u, u_m, hS, hrun => by
    injection hrun with h1; injection h1 with hN hu; subst hN hu
    exact ⟨rem, ⟨0, rfl⟩, hS⟩
  | m + 1, N, N_m, rem, u, u_m, hS, hrun => by
    unfold runEras at hrun
    cases hs : stepEraU N u with
    | none => rw [hs] at hrun; nomatch hrun
    | some pair =>
      rcases pair with ⟨N', u'⟩
      rw [hs] at hrun
      obtain ⟨rem', htm1, hS1⟩ := stepEraU_sound hS hs
      obtain ⟨rem_m, htm_m, hS_m⟩ := runEras_sound m N' N_m rem' u' u_m hS1 hrun
      exact ⟨rem_m, stepStar_trans (stepPlus_stepStar htm1) htm_m, hS_m⟩

def checkBridge : Bool :=
  match runEras 132 3 (stepU 3 (0, .sw1)) with
  | some (N, u) => decide (2440 ≤ N ∧ 3 * levelU u ≤ 8 * N + 1200)
  | none => false

lemma checkBridge_eq_true : checkBridge = true := rfl

lemma era_inv_cap_le {N n : Nat} (hN : 2440 ≤ N) (hn : 3 * n ≤ 8 * N + 1200) :
    CAP n ≤ N + 1 := by
  obtain ⟨_, _, _, h4⟩ := CB4_le (n / 2)
  unfold CAP; omega

lemma era_inv_dap_le {N N' n c lu : Nat} (hN : 2440 ≤ N) (hN' : N + 1 ≤ N')
    (hn : 3 * n ≤ 8 * N + 1200) (hc : c ≤ N') (hd : lu ≤ c + DAP n) :
    2440 ≤ N' ∧ 3 * (lu + (N' - c)) ≤ 8 * N' + 1200 := by
  obtain ⟨_, _, _, h4⟩ := DB4_le (n / 2)
  unfold DAP at hd; omega

def EraInv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ (N : Nat) (rem : ListBlank (Fin 2)) (u : UTree),
    2440 ≤ N ∧ 3 * levelU u ≤ 8 * N + 1200 ∧
    Sweeps N rem (evalU u) ∧
    cfg = (default <{{E}} (rep010 N rem))

lemma era_inv_init : ∃ cfg₀, ((init []) [target_tm]⊢* cfg₀) ∧ EraInv cfg₀ := by
  have hb := checkBridge_eq_true
  unfold checkBridge at hb
  cases hrun : runEras 132 3 (stepU 3 (0, .sw1)) with
  | none => rw [hrun] at hb; nomatch hb
  | some pair =>
    rcases pair with ⟨N_133, u_133⟩
    rw [hrun, decide_eq_true_iff] at hb
    have hS1 : Sweeps 3 (evalCore .sw1) (evalU (stepU 3 (0, .sw1))) :=
      stepU_sound 3 (0, .sw1)
    obtain ⟨rem_133, hstar_bridge, hS_133⟩ :=
      runEras_sound 132 3 N_133 (evalCore .sw1) (stepU 3 (0, .sw1)) u_133 hS1 hrun
    exact ⟨(default <{{E}} (rep010 N_133 rem_133)),
      stepStar_trans init_reaches_era1 hstar_bridge,
      ⟨N_133, rem_133, u_133, hb.1, hb.2, hS_133, rfl⟩⟩

lemma era_inv_step (cfg : Cfg (Fin 2) (Fin 6)) (hinv : EraInv cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧ EraInv cfg' := by
  obtain ⟨N, rem, u, hN, hn, hS, rfl⟩ := hinv
  have ha_b := (opsAux_bounds (levelU u)).2
  obtain ⟨_, hcap, _, hdap⟩ := aPullFrom_bounds ha_b u (le_refl (levelU u))
  have hc_le : (aPullFrom (opsAux (levelU u)).aCore u).c ≤
      N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p := by
    have := era_inv_cap_le hN hn
    omega
  have hstep : stepEraU N u =
      some (N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p,
            stepU (N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p - (aPullFrom (opsAux (levelU u)).aCore u).c)
              (aPullFrom (opsAux (levelU u)).aCore u).u) := by
    unfold stepEraU
    dsimp only
    rw [if_pos hc_le]
  obtain ⟨rem', htm, hS'⟩ := stepEraU_sound hS hstep
  have h_inv' := era_inv_dap_le hN (by omega : N + 1 ≤ N + 1 + (aPullFrom (opsAux (levelU u)).aCore u).p) hn hc_le hdap
  refine ⟨_, htm, ⟨_, rem', _, h_inv'.1, ?_, hS', rfl⟩⟩
  rw [levelU_stepU]
  exact h_inv'.2

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  closed_inv_does_not_halt target_tm EraInv era_inv_init era_inv_step

end BusyBeaver.M_1RB1RF_1LC0RD_HHH0LD_1LE0LD_1RA0RF_0RE0LB
