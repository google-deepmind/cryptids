/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Longitudinal
import BusyBeaver.Calculi.SegCount
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RA_1RC0RC_1LD1RF_HHH1LE_1RF0LF_1RA0LE

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_1RC0RC_1LD1RF_HHH1LE_1RF0LF_1RA0LE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace SegCount

open BusyBeaver.Longitudinal

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

export BusyBeaver.SegCount (runSteps runSteps_spec)

theorem SegRLs.congr {M : Machine Γ Λ} {ls₁ ls₁' ls₂ ls₂' : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₁' w₂ w₂' : List Γ}
    (h : SegRLs M ls₁ ls₂ w₁ w₂)
    (hls₁ : ls₁ = ls₁') (hls₂ : ls₂ = ls₂') (hw₁ : w₁ = w₁') (hw₂ : w₂ = w₂') :
    SegRLs M ls₁' ls₂' w₁' w₂' := by
  subst hls₁ hls₂ hw₁ hw₂; exact h

theorem runSteps1_spec (M : Machine Γ Λ) (n : ℕ) (x y : BoundedConfig.BCfg Γ Λ)
    (h : (BoundedConfig.step M x).map (runSteps M n) = some y) (l₀ r₀ : ListBlank Γ) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢⁺ (BoundedConfig.toCfg y l₀ r₀) := by
  rcases hstep : BoundedConfig.step M x with _ | x' <;> rw [hstep] at h
  · cases h
  · dsimp only [Option.map] at h
    injection h with hy
    exact stepPlus_stepStar_trans ⟨1, by decide, BoundedConfig.step_spec M x hstep l₀ r₀⟩
      (runSteps_spec M n x' y hy l₀ r₀)

theorem SegRLs.trans_eq {M : Machine Γ Λ}
    {ls₁ ls₂ ls₃ ls₄ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₂' w₃ : List Γ}
    (h₁ : SegRLs M ls₁ ls₂ w₁ w₂) (h₂ : SegRLs M ls₃ ls₄ w₂' w₃)
    (hw : w₂ = w₂') :
    SegRLs M (ls₁ ++ ls₃) (ls₂ ++ ls₄) w₁ w₃ := by
  subst hw; exact h₁.trans h₂


theorem stepStar_congr {M : Machine Γ Λ} {c₁ c₁' c₂ c₂' : Cfg Γ Λ}
    (h : c₁ [M]⊢* c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') : c₁' [M]⊢* c₂' := by
  subst hc₁ hc₂; exact h

theorem stepPlus_congr {M : Machine Γ Λ} {c₁ c₁' c₂ c₂' : Cfg Γ Λ}
    (h : c₁ [M]⊢⁺ c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') : c₁' [M]⊢⁺ c₂' := by
  subst hc₁ hc₂; exact h

theorem run_trans {M : Machine Γ Λ} {hf ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)} {m n : ℕ}
    {w₁ w₂ w₂' w₃ : List Γ}
    (h₁ : SegRLs M (hf ^ m) ls₁ w₁ w₂)
    (h₂ : SegRLs M (hf ^ n) ls₂ w₂' w₃)
    (hw : w₂ = w₂') :
    SegRLs M (hf ^ (m + n)) (ls₁ ++ ls₂) w₁ w₃ := by
  rw [pow_add_list]
  exact SegRLs.trans_eq h₁ h₂ hw

def ucount : ℕ → ℕ
  | 0 => 1
  | k + 1 => 4 * ucount k + 1

def vcount (k : ℕ) : ℕ := 2 * ucount k - 1

def qcount : ℕ → ℕ
  | 0 => 0
  | k + 1 => ucount k

omit [Inhabited Γ] [Inhabited Λ] in
theorem ucount_positive (k : ℕ) : 0 < ucount k := by
  induction k with
  | zero => decide
  | succ k ih => dsimp [ucount]; omega

omit [Inhabited Γ] [Inhabited Λ] in
theorem ucount_power (k : ℕ) : 3 * ucount k + 1 = 4 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [ucount]
    rw [Nat.pow_succ]
    omega

omit [Inhabited Γ] [Inhabited Λ] in
theorem qcount_S (j : ℕ) : qcount (j + 1) = 4 * qcount j + 1 := by
  cases j <;> rfl

theorem H_lift_finite {M : Machine Γ Λ} {hf : List (DH0 Γ Λ × DH0 Γ Λ)}
    {hword : ℕ → ℕ → List Γ}
    (H_cycle : ∀ a b, SegRLs M (hf ^ (4 ^ (a + 2))) hf (hword a (1 + b)) (hword (1 + a) b))
    (a b j : ℕ) :
    SegRLs M (hf ^ (4 ^ (a + 2) * qcount j)) (hf ^ j)
      (hword a (j + b)) (hword (a + j) b) := by
  induction j generalizing a with
  | zero =>
    rw [qcount, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact .nil _
  | succ j ih =>
    have h1 := H_cycle a (j + b)
    have h2 := ih (a + 1)
    have h12 := run_trans h1 h2 (by rw [Nat.add_comm 1 a])
    refine SegRLs.congr h12 ?_ (by rw [pow_succ_list])
      (by rw [show j + 1 + b = 1 + (j + b) by omega])
      (by rw [show a + 1 + j = a + (j + 1) by omega])
    congr 1
    rw [qcount_S, show a + 1 + 2 = (a + 2) + 1 by omega, Nat.pow_succ]
    ring

theorem H_lift {M : Machine Γ Λ} {hf : List (DH0 Γ Λ × DH0 Γ Λ)}
    {hword : ℕ → ℕ → List Γ}
    (H_cycle : ∀ a b, SegRLs M (hf ^ (4 ^ (a + 2))) hf (hword a (1 + b)) (hword (1 + a) b))
    (a b j : ℕ) (r r' : ListBlank Γ) (H : SideRLs M (hf ^ j) r r') :
    SideRLs M (hf ^ (4 ^ (a + 2) * qcount j))
      (hword a (j + b) +> r) (hword (a + j) b +> r') :=
  (H_lift_finite H_cycle a b j).sideRLs_concat H

theorem N_run {M : Machine Γ Λ} {hf : List (DH0 Γ Λ × DH0 Γ Λ)}
    {Ncfg : ℕ → ListBlank Γ → Cfg Γ Λ}
    (h_step : ∀ n r r', SideRLs M hf r r' → (Ncfg n r) [M]⊢⁺ (Ncfg (n + 1) r')) :
    ∀ m n r r', SideRLs M (hf ^ m) r r' → (Ncfg n r) [M]⊢* (Ncfg (n + m) r') := by
  intro m
  induction m with
  | zero =>
    intro n r r' h
    cases h
    simp only [Nat.add_zero]
    exact stepStar_refl M _
  | succ m ih =>
    intro n r r' h
    rw [pow_succ_list] at h
    rcases h.split with ⟨r_mid, h1, h2⟩
    refine stepStar_trans (stepPlus_to_stepStar (h_step n r r_mid h1)) ?_
    have h_rec := ih (n + 1) r_mid r' h2
    have h_add : n + 1 + m = n + (m + 1) := by omega
    rwa [h_add] at h_rec

theorem N_H_lift {M : Machine Γ Λ} {hf : List (DH0 Γ Λ × DH0 Γ Λ)}
    {hword : ℕ → ℕ → List Γ} {Ncfg : ℕ → ListBlank Γ → Cfg Γ Λ}
    (h_N : ∀ n r r', SideRLs M hf r r' → (Ncfg n r) [M]⊢⁺ (Ncfg (n + 1) r'))
    (H_cycle : ∀ a b, SegRLs M (hf ^ (4 ^ (a + 2))) hf (hword a (1 + b)) (hword (1 + a) b))
    (n a b j : ℕ) (r r' : ListBlank Γ) (H : SideRLs M (hf ^ j) r r') :
    (Ncfg n (hword a (j + b) +> r)) [M]⊢*
      (Ncfg (n + 4 ^ (a + 2) * qcount j) (hword (a + j) b +> r')) :=
  N_run h_N (4 ^ (a + 2) * qcount j) n _ _ (H_lift H_cycle a b j r r' H)

end SegCount

section

open BusyBeaver.Longitudinal SegCount

local notation "Γ" => Fin 2
local notation "Λ" => Fin 6

set_option maxRecDepth 200000

abbrev O : Fin 2 := 0
abbrev I : Fin 2 := 1

abbrev A : Fin 6 := 0
abbrev C : Fin 6 := 2
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

abbrev tm : Machine (Fin 2) (Fin 6) := target_tm

-- ============================================================================
-- 1. Bounded Execution Helpers & Tape Words (`SOBCv14.v:13-50`)
-- ============================================================================


abbrev hf : List (DH0 Γ Λ × DH0 Γ Λ) := [((F, []), (E, []))]
abbrev z4 : List Γ := [O, O, O, O]
abbrev a4 : List Γ := [I, O, O, O]
abbrev b4 : List Γ := [I, O, O, I]
abbrev c4 : List Γ := [O, I, I, O]
abbrev d4 : List Γ := [I, I, I, O]
abbrev e4 : List Γ := [O, O, I, O]

theorem pow_one_add {α : Type*} (u : List α) (n : ℕ) : u ^ (1 + n) = u ++ u ^ n := by
  rw [Nat.add_comm 1 n, pow_succ_list]

theorem pow_two_add {α : Type*} (u : List α) (n : ℕ) : u ^ (2 + n) = u ++ (u ++ u ^ n) := by
  rw [show 2 + n = (n + 1) + 1 by omega, pow_succ_list, pow_succ_list]

theorem pow_add_two {α : Type*} (u : List α) (n : ℕ) : u ^ (n + 2) = u ++ (u ++ u ^ n) := by
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ_list, pow_succ_list]

theorem pow_add_three {α : Type*} (u : List α) (n : ℕ) : u ^ (n + 3) = u ++ (u ++ (u ++ u ^ n)) :=
    by
  rw [show n + 3 = (n + 2) + 1 by omega, pow_succ_list, pow_add_two]

theorem cons4_pow_comm {α : Type*} (a b c d : α) (k : ℕ) (s : List α) :
    [a, b, c, d] ^ k ++ (a :: b :: c :: d :: s) =
      a :: b :: c :: d :: ([a, b, c, d] ^ k ++ s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, List.append_assoc, ih]
    rfl

theorem cons4_pow_comm_end {α : Type*} (a b c d : α) (k : ℕ) :
    [a, b, c, d] ^ k ++ [a, b, c, d] =
      a :: b :: c :: d :: [a, b, c, d] ^ k := by
  simpa using cons4_pow_comm a b c d k []

theorem z4_cons_O_comm (k : ℕ) (s : List Γ) :
    [O, O, O, O] ^ k ++ (O :: s) = O :: ([O, O, O, O] ^ k ++ s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, List.append_assoc, ih]
    rfl

theorem z4_end_O_comm (k : ℕ) :
    [O, O, O, O] ^ k ++ [O] = O :: [O, O, O, O] ^ k := by
  simpa using z4_cons_O_comm k []

def hword (a b : ℕ) : List Γ :=
  [O, O, I] ++ d4 ++ e4 ^ a ++ c4 ^ b ++ [O, I, I, I, I]

abbrev seek_tail : List Γ := [O, O, O, I, O, O, O, I, I, I, I, I]
abbrev seed_tail : List Γ := [O, O, O] ++ z4 ++ a4 ++ z4 ++ [O, I, I, I] ++ [I, I, I, I] ++ a4
abbrev seed_tail40 : List Γ := [O, O, O] ++ z4 ++ [I, I, I, I] ^ 4 ++ a4
def post_input (j : ℕ) : List Γ :=
  hword j 0 ++ [O, O, O] ++ z4 ^ 2 ++ a4 ^ 44 ++ z4 ++ a4 ^ 5 ++ [I, I, I, I] ++ b4 ++ [I, I, I]
abbrev second_tail : List Γ :=
  [O, O, O, I] ++ [O, O, O, I] ++ [I, I, I, I] ++ [O, O, O, I] ++
    [I, I, I, I] ++ [O, O, O, I] ++ [I, I, I, I] ++ [I, I, I, I]
abbrev second_result_tail : List Γ :=
  a4 ++ [I, I, I, I] ++ a4 ++ [I, I, I, I] ++ a4 ++ [I, I, I, I] ^ 2 ++ [I]
abbrev entry_tail : List Γ :=
  a4 ++ [I, I, I, I] ++ a4 ++ [I, I, I, I] ++ a4 ++ [I, I, I, I] ^ 2 ++ d4 ++ [I, I]

theorem pow2_list {α : Type*} (u : List α) : u ^ 2 = u ++ u := by
  rw [pow_succ_list, pow_one_list]
theorem pow3_list {α : Type*} (u : List α) : u ^ 3 = u ++ (u ++ u) := by
  rw [pow_succ_list, pow2_list]
theorem pow4_list {α : Type*} (u : List α) : u ^ 4 = u ++ (u ++ (u ++ u)) := by
  rw [pow_succ_list, pow3_list]
theorem pow5_list {α : Type*} (u : List α) : u ^ 5 = u ++ (u ++ (u ++ (u ++ u))) := by
  rw [pow_succ_list, pow4_list]
theorem pow6_list {α : Type*} (u : List α) : u ^ 6 = u ++ (u ++ (u ++ (u ++ (u ++ u)))) := by
  rw [pow_succ_list, pow5_list]

macro "norm_word" : tactic =>
  `(tactic| simp only [hword, z4, a4, b4, c4, d4, e4, seek_tail,
    seed_tail, seed_tail40, post_input, second_tail, second_result_tail, entry_tail,
    pow_zero_list, pow_one_list, pow_succ_list, pow_one_add, pow_two_add,
    pow_add_two, pow_add_three,
    cons4_pow_comm, cons4_pow_comm_end, z4_cons_O_comm, z4_end_O_comm,
    Nat.add_zero, Nat.zero_add,
    List.append_assoc, List.nil_append, List.append_nil, List.cons_append])

macro "flat_word" : tactic =>
  `(tactic| simp only [hword, z4, a4, b4, c4, d4, e4, seek_tail,
    seed_tail, seed_tail40, post_input, second_tail, second_result_tail, entry_tail,
    pow_zero_list, pow_one_list, pow2_list, pow3_list, pow4_list, pow5_list, pow6_list,
    pow_one_add, pow_two_add, Nat.add_zero, Nat.zero_add,
    List.append_assoc, List.nil_append, List.append_nil, List.cons_append])

theorem finite_suffix {n : ℕ} {w₁ w₂ : List Γ} (s : List Γ)
    (h : SegRLs tm (hf ^ n) [] w₁ w₂) :
    SegRLs tm (hf ^ n) [] (w₁ ++ s) (w₂ ++ s) :=
  h.concat (.nil s)

theorem finite_suffix1 {w₁ w₂ : List Γ} (s : List Γ)
    (h : SegRLs tm hf [] w₁ w₂) :
    SegRLs tm (hf ^ 1) [] (w₁ ++ s) (w₂ ++ s) :=
  h.concat (.nil s)

theorem segment_suffix {ls : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ : List Γ} (s : List Γ)
    (h : SegRLs tm ls [] w₁ w₂) :
    SegRLs tm ls [] (w₁ ++ s) (w₂ ++ s) :=
  h.concat (.nil s)

theorem finite_trans {m n : ℕ} {w₁ w₂ w₂' w₃ : List Γ}
    (h₁ : SegRLs tm (hf ^ m) [] w₁ w₂)
    (h₂ : SegRLs tm (hf ^ n) [] w₂' w₃)
    (hw : w₂ = w₂' := by norm_word) :
    SegRLs tm (hf ^ (m + n)) [] w₁ w₃ := by
  rw [pow_add_list]
  exact SegRLs.trans_eq h₁ h₂ hw

theorem run_trans {m n : ℕ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ w₂' w₃ : List Γ}
    (h₁ : SegRLs tm (hf ^ m) ls₁ w₁ w₂)
    (h₂ : SegRLs tm (hf ^ n) ls₂ w₂' w₃)
    (hw : w₂ = w₂' := by norm_word) :
    SegRLs tm (hf ^ (m + n)) (ls₁ ++ ls₂) w₁ w₃ := by
  rw [pow_add_list]
  exact SegRLs.trans_eq h₁ h₂ hw

theorem segRLs_repeat_wall (h : DH0 Γ Λ × DH0 Γ Λ) {w₁ w₂ : List Γ}
    (H : SegRLs tm [h] [h] w₁ w₂) (n : ℕ) :
    SegRLs tm [h] [h] (w₁ ^ n) (w₂ ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm [h]
  | succ n ih => exact H.concat ih

-- ============================================================================
-- 2. Base 1-Block Walls & Bridges (`SOBCv14.v:21-118`, `419-443`, `582-635`, `714-757`, `836-844`)
-- ============================================================================


def Ufinite (k : ℕ) : Prop :=
  SegRLs tm (hf ^ ucount k) []
    ([O, O, O] ++ z4 ^ k ++ [O])
    ([O, O, I] ++ a4 ^ k ++ [I])

def Vfinite (k : ℕ) : Prop :=
  SegRLs tm (hf ^ vcount k) []
    ([O, O, O] ++ c4 ++ z4 ^ k)
    ([O, O, I] ++ d4 ++ e4 ^ k)

theorem Ufinite_0 : Ufinite 0 :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem Vfinite_0 : Vfinite 0 :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem Ufinite_1 : Ufinite 1 :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

-- 1-Block repeating walls (`T := 200`)
private theorem wall_CF_a4 : SegRLs tm [((C, []), (F, []))] [((C, []), (F, []))] a4 z4 :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem wall_AF_e4 : SegRLs tm [((A, []), (F, []))] [((A, []), (F, []))] e4 z4 :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem wall_AE_e4 : SegRLs tm [((A, []), (E, []))] [((A, []), (E, []))] e4 z4 :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem wall_AF0_c4 : SegRLs tm [((A, []), (F, [O]))] [((A, []), (F, [O]))] c4 [O, O, I,
    I] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem wall_FEz4_0001 : SegRLs tm [((F, []), (E, z4))] [((F, []), (E, z4))] [O, O, O,
    I] z4 :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem wall_FEz4_0011 : SegRLs tm [((F, []), (E, z4))] [((F, []), (E, z4))] [O, O, I,
    I] [I, I, O, O] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem P_F_0 : SegRLs tm hf [((C, []), (F, []))] ([O, O, I] ++ a4) ([O, O, O] ++ c4) :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem P_F (k : ℕ) :
    SegRLs tm hf [((C, []), (F, []))] ([O, O, I] ++ a4 ^ (1 + k)) ([O, O, O] ++ c4 ++ z4 ^ k) := by
  have h := P_F_0.concat (segRLs_repeat_wall ((C, []), (F, [])) wall_CF_a4 k)
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem J_F_0 : SegRLs tm hf [((A, []), (F, []))] ([O, O, I] ++ d4) ([O, O, O] ++ z4) :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem J_F (a : ℕ) :
    SegRLs tm hf [((A, []), (F, []))] ([O, O, I] ++ d4 ++ e4 ^ a) ([O, O, O] ++ z4 ^ (1 + a)) := by
  have h := J_F_0.concat (segRLs_repeat_wall ((A, []), (F, [])) wall_AF_e4 a)
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem J_E_0 : SegRLs tm [((F, []), (F, []))] [((A, []), (E, []))] ([O, O, I] ++ d4) ([O,
    O, O] ++ z4) :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem J_E (a : ℕ) :
    SegRLs tm [((F, []), (F, []))] [((A, []), (E, []))]
      ([O, O, I] ++ d4 ++ e4 ^ a) ([O, O, O] ++ z4 ^ (1 + a)) := by
  have h := J_E_0.concat (segRLs_repeat_wall ((A, []), (E, [])) wall_AE_e4 a)
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem CF_a4_0 : SegRLs tm [((C, []), (F, []))] [] (a4 ++ [O]) [O, O, O, I, I] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem bridge_L2 (m : ℕ) :
    SegRLs tm hf [] ([O, O, I] ++ a4 ^ (2 + m) ++ [O])
      ([O, O, O] ++ c4 ++ z4 ^ m ++ [O, O, O, I, I]) := by
  have h := (P_F m).concat CF_a4_0
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem CF_1110 : SegRLs tm [((C, []), (F, []))] [] [I, I, I, O] [O, O, I, O] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem bridge_L3_0 (m : ℕ) :
    SegRLs tm hf [] ([O, O, I] ++ a4 ^ (1 + m) ++ [I, I, I, O])
      ([O, O, O] ++ c4 ++ z4 ^ m ++ [O, O, I, O]) := by
  have h := (P_F m).concat CF_1110
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem CF_1111 : SegRLs tm [((C, []), (F, []))] [] [I, I, I, I] [O, O, I, I] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem bridge_L3_1 (m : ℕ) :
    SegRLs tm hf [] ([O, O, I] ++ a4 ^ (1 + m) ++ [I, I, I, I])
      ([O, O, O] ++ c4 ++ z4 ^ m ++ [O, O, I, I]) := by
  have h := (P_F m).concat CF_1111
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem AF_0000 : SegRLs tm [((A, []), (F, []))] [] [O, O, O, O] [O, I, I, O] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem bridge_L4_0 (m : ℕ) :
    SegRLs tm hf [] ([O, O, I] ++ d4 ++ e4 ^ m ++ [O, O, O, O])
      ([O, O, O] ++ z4 ^ (1 + m) ++ [O, I, I, O]) := by
  have h := (J_F m).concat AF_0000
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem AF_0001 : SegRLs tm [((A, []), (F, []))] [] [O, O, O, I] [O, I, I, I] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem bridge_L4_1 (m : ℕ) :
    SegRLs tm hf [] ([O, O, I] ++ d4 ++ e4 ^ m ++ [O, O, O, I])
      ([O, O, O] ++ z4 ^ (1 + m) ++ [O, I, I, I]) := by
  have h := (J_F m).concat AF_0001
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem AF_0011 : SegRLs tm [((A, []), (F, []))] [] [O, O, I, I] [O, O, O, O] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem bridge_L4_3 (m : ℕ) :
    SegRLs tm hf [] ([O, O, I] ++ d4 ++ e4 ^ m ++ [O, O, I, I])
      ([O, O, O] ++ z4 ^ (1 + m) ++ [O, O, O, O]) := by
  have h := (J_F m).concat AF_0011
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem H_empty_tail : SegRLs tm [((A, []), (F, []))] hf [O, I, I, I, I] (z4 ++ [O]) :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem H_empty_F (a : ℕ) :
    SegRLs tm hf hf (hword a 0) ([O, O, O] ++ z4 ^ (2 + a) ++ [O]) := by
  have h := (J_F a).concat H_empty_tail
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem I_0001_pow (a : ℕ) :
    [I] ++ [O, O, O, I] ^ a = a4 ^ a ++ [I] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ_list [O, O, O, I] a, ← List.append_assoc [I] [O, O, O, I],
      show [I] ++ [O, O, O, I] = a4 ++ [I] from rfl,
      List.append_assoc a4 [I], ih, ← List.append_assoc, ← pow_succ_list a4 a]

private theorem I_0011_pow (b : ℕ) :
    [I] ++ [O, O, I, I] ^ b = b4 ^ b ++ [I] := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ_list [O, O, I, I] b, ← List.append_assoc [I] [O, O, I, I],
      show [I] ++ [O, O, I, I] = b4 ++ [I] from rfl,
      List.append_assoc b4 [I], ih, ← List.append_assoc, ← pow_succ_list b4 b]

private theorem H_OA_c4_first : SegRLs tm [((A, []), (F, []))] [((A, []), (F, [O]))] c4 [O, O, O, I,
    I] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem H_OA_tail : SegRLs tm [((A, []), (F, [O]))] hf [O, I, I, I, I] z4 :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem H_OA (a b : ℕ) :
    SegRLs tm hf hf (hword a (1 + b))
      ([O, O, O] ++ z4 ^ (1 + a) ++ [O, O, O, I] ++ b4 ^ b ++ a4 ++ [O]) := by
  have h1 := (J_F a).concat H_OA_c4_first
  have h2 := h1.concat (segRLs_repeat_wall ((A, []), (F, [O])) wall_AF0_c4 b)
  have h3 := h2.concat H_OA_tail
  refine SegRLs.congr h3 rfl rfl (by norm_word) ?_
  have hb := I_0011_pow b
  rw [show ([O, O, O] ++ z4 ^ (1 + a) ++ [O, O, O, I, I] ++ [O, O, I, I] ^ b) ++ z4 =
    [O, O, O] ++ z4 ^ (1 + a) ++ [O, O, O, I] ++ ([I] ++ [O, O, I, I] ^ b) ++ z4 from by norm_word,
    hb]
  norm_word

private theorem H_OB_head : SegRLs tm hf [((F, []), (E, z4))] [O, O, I, I] (z4 ++ [I, I, O, O]) :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem H_OB_tail : SegRLs tm [((F, []), (E, z4))] [] ([O, O, I, I] ++ z4) [I, I, I, I] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

private theorem h_ob_out_eq (b : ℕ) :
    [O] ++ [I, I, O, O] ^ b ++ [I, I, I, I] = c4 ^ b ++ [O, I, I, I, I] := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have h1 : [O] ++ [I, I, O, O] ^ (b + 1) ++ [I, I, I, I] =
        c4 ++ ([O] ++ [I, I, O, O] ^ b ++ [I, I, I, I]) := by
      rw [pow_succ_list]; simp only [c4, List.cons_append, List.nil_append]
    rw [h1, ih, pow_succ_list, List.append_assoc]

theorem H_OB (a b : ℕ) :
    SegRLs tm hf []
      ([O, O, I] ++ a4 ^ a ++ b4 ^ (1 + b) ++ a4 ++ [O])
      ([O, O, O] ++ c4 ++ z4 ^ a ++ c4 ^ b ++ [O, I, I, I, I]) := by
  have h1 := H_OB_head.concat (segRLs_repeat_wall ((F, []), (E, z4)) wall_FEz4_0001 a)
  have h2 := h1.concat (segRLs_repeat_wall ((F, []), (E, z4)) wall_FEz4_0011 b)
  have h3 := h2.concat H_OB_tail
  refine SegRLs.congr h3 rfl rfl ?_ ?_
  · have ha := I_0001_pow a
    have hb := I_0011_pow b
    rw [show ([O, O, I, I] ++ [O, O, O, I] ^ a ++ [O, O, I, I] ^ b) ++ ([O, O, I, I] ++ z4) =
      [O, O, I] ++ ([I] ++ [O, O, O, I] ^ a) ++ [O, O, I, I] ^ b ++ ([O, O, I,
          I] ++ z4) from by norm_word,
      ha,
      show [O, O, I] ++ (a4 ^ a ++ [I]) ++ [O, O, I, I] ^ b ++ ([O, O, I, I] ++ z4) =
        [O, O, I] ++ a4 ^ a ++ ([I] ++ [O, O, I, I] ^ b) ++ ([O, O, I, I] ++ z4) from by norm_word,
      hb]
    norm_word
  · rw [show (z4 ++ [I, I, O, O] ++ z4 ^ a ++ [I, I, O, O] ^ b) ++ [I, I, I, I] =
      ([O, O, O] ++ c4 ++ z4 ^ a) ++ ([O] ++ [I, I, O, O] ^ b ++ [I, I, I, I]) from by norm_word,
      h_ob_out_eq b]
    norm_word

private theorem CF_AZ : SegRLs tm [((C, []), (F, []))] [] (a4 ++ z4) ([O, O, O, I] ++ a4) :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem C_AZ (k : ℕ) :
    SegRLs tm [((C, []), (F, []))] []
      (a4 ^ (1 + k) ++ z4) (z4 ^ k ++ [O, O, O, I] ++ a4) := by
  have h := (segRLs_repeat_wall ((C, []), (F, [])) wall_CF_a4 k).concat CF_AZ
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

private theorem F_000_CF : SegRLs tm hf [((C, []), (F, []))] [O, O, O] [O, O, O] :=
  BoundedConfig.segRLs_c_spec tm (T := 200) (by decide)

theorem F_AZ_large (k : ℕ) :
    SegRLs tm hf []
      ([O, O, O] ++ a4 ^ (1 + k) ++ z4)
      ([O, O, O] ++ z4 ^ k ++ [O, O, O, I] ++ a4) := by
  have h := F_000_CF.concat (C_AZ k)
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

-- ============================================================================
-- 3. `Ufinite` & `Vfinite` Joint Induction & Reset Seek (`SOBCv14.v:141-514`)
-- ============================================================================


theorem Vfinite_step (k : ℕ) (HU : Ufinite (k + 1)) (HV : Vfinite k) : Vfinite (k + 1) := by
  have h1 := finite_suffix z4 HV
  have h2 : SegRLs tm (hf ^ 1) [] _ _ := bridge_L4_0 k
  have h3 := finite_suffix [I, I, O] HU
  have h4 : SegRLs tm (hf ^ 1) [] _ _ := bridge_L3_0 k
  have h5 := finite_suffix e4 HV
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
  have h1234 := finite_trans h123 h4
  have h12345 := finite_trans h1234 h5
  refine SegRLs.congr h12345 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive k
  dsimp [vcount, ucount]
  omega

theorem Ufinite_step (k : ℕ) (HU : Ufinite (k + 1)) (HV : Vfinite k) : Ufinite (k + 2) := by
  have h1 := finite_suffix z4 HU
  have h2 : SegRLs tm (hf ^ 1) [] _ _ := bridge_L2 k
  have h3 := finite_suffix [O, O, O, I, I] HV
  have h4 := finite_suffix1 [I] (bridge_L4_1 k)
  have h5 := finite_suffix [I, I, I, I] HU
  have h6 := finite_suffix1 [I] (bridge_L3_1 k)
  have h7 := finite_suffix [O, O, I, I, I] HV
  have h8 := finite_suffix1 [I] (bridge_L4_3 k)
  have h9 := finite_suffix [O, O, O, I] HU
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
  have h1234 := finite_trans h123 h4
  have h12345 := finite_trans h1234 h5
  have h123456 := finite_trans h12345 h6
  have h1234567 := finite_trans h123456 h7
  have h12345678 := finite_trans h1234567 h8
  have h123456789 := finite_trans h12345678 h9
  refine SegRLs.congr h123456789 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive k
  dsimp [vcount, ucount]
  omega

theorem UVfinite (k : ℕ) : Ufinite (k + 1) ∧ Vfinite k := by
  induction k with
  | zero => exact ⟨Ufinite_1, Vfinite_0⟩
  | succ k ih => exact ⟨Ufinite_step k ih.1 ih.2, Vfinite_step k ih.1 ih.2⟩

theorem Ufinite_all (k : ℕ) : Ufinite k := by
  cases k with
  | zero => exact Ufinite_0
  | succ k => exact (UVfinite k).1

theorem Vfinite_all (k : ℕ) : Vfinite k := (UVfinite k).2


theorem pow4_next (k : ℕ) : 4 ^ (k + 1) = 4 * 4 ^ k := by
  rw [Nat.pow_succ]; ring

theorem U_prefix_M (k : ℕ) :
    SegRLs tm (hf ^ (2 * 4 ^ (k + 1))) []
      ([O, O, O] ++ z4 ^ (k + 2) ++ [O])
      ([O, O, O] ++ z4 ^ (k + 1) ++ [O, I, I, I, I]) := by
  have h1 := finite_suffix z4 (Ufinite_all (k + 1))
  have h2 : SegRLs tm (hf ^ 1) [] _ _ := bridge_L2 k
  have h3 := finite_suffix [O, O, O, I, I] (Vfinite_all k)
  have h4 := finite_suffix1 [I] (bridge_L4_1 k)
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
  have h1234 := finite_trans h123 h4
  refine SegRLs.congr h1234 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive k
  have := ucount_power k
  dsimp [vcount, ucount]
  omega

theorem U_prefix_L (k : ℕ) :
    SegRLs tm (hf ^ (4 ^ (k + 2))) []
      ([O, O, O] ++ z4 ^ (k + 2) ++ [O])
      ([O, O, O] ++ z4 ^ (k + 1) ++ [O, O, O, O, I]) := by
  have h1 := U_prefix_M k
  have h2 := finite_suffix [I, I, I, I] (Ufinite_all (k + 1))
  have h3 := finite_suffix1 [I] (bridge_L3_1 k)
  have h4 := finite_suffix [O, O, I, I, I] (Vfinite_all k)
  have h5 := finite_suffix1 [I] (bridge_L4_3 k)
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
  have h1234 := finite_trans h123 h4
  have h12345 := finite_trans h1234 h5
  refine SegRLs.congr h12345 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive k
  have := ucount_power k
  have := pow4_next (k + 1)
  rw [show k + 2 = (k + 1) + 1 by omega]
  dsimp [vcount, ucount] at *
  omega

theorem U_near_end (k : ℕ) :
    SegRLs tm (hf ^ (ucount (k + 2) - 5)) []
      ([O, O, O] ++ z4 ^ (k + 2) ++ [O])
      ([O, O, O] ++ z4 ^ 2 ++ a4 ^ k ++ [I]) := by
  induction k with
  | zero =>
    exact SegRLs.congr (U_prefix_L 0) rfl rfl (by norm_word) (by norm_word)
  | succ k ih =>
    have h1 := U_prefix_L (k + 1)
    have h2 := finite_suffix [O, O, O, I] ih
    have h12 := finite_trans h1 h2
    refine SegRLs.congr h12 ?_ rfl (by norm_word) (by norm_word)
    congr 1
    have := ucount_positive k
    have := ucount_power (k + 2)
    rw [show k + 1 + 2 = (k + 2) + 1 by omega]
    dsimp [ucount] at *
    omega

theorem near_end_count (k : ℕ) : ucount (k + 2) - 5 = 16 * ucount k := by
  dsimp [ucount]; omega

theorem seek_top3 (k : ℕ) :
    SegRLs tm (hf ^ (13 * 4 ^ (k + 7))) []
      ([O, O, O] ++ z4 ^ (k + 9) ++ [O])
      (([O, O, O] ++ z4 ^ (k + 6) ++ [O]) ++ seek_tail) := by
  have h1 := U_prefix_M (k + 7)
  have h2 := finite_suffix [I, I, I, I] (U_prefix_L (k + 6))
  have h3 := finite_suffix [O, O, O, I, I, I, I, I] (U_prefix_L (k + 5))
  have h12 := finite_trans h1 h2 (by rw [show k + 7 + 1 = k + 6 + 2 by omega]; norm_word)
  have h123 := finite_trans h12 h3 (by rw [show k + 6 + 1 = k + 5 + 2 by omega]; norm_word)
  refine SegRLs.congr h123 ?_ rfl
    (by rw [show k + 7 + 2 = k + 9 by omega])
    (by rw [show k + 5 + 1 = k + 6 by omega]; norm_word)
  congr 1
  have : 4 ^ (k + 7 + 1) = 4 * 4 ^ (k + 7) := pow4_next (k + 7)
  have : 4 ^ (k + 6 + 2) = 4 * 4 ^ (k + 7) := by
    rw [show k + 6 + 2 = (k + 7) + 1 by omega, pow4_next]
  have : 4 ^ (k + 5 + 2) = 4 ^ (k + 7) := by congr 1
  omega

theorem seek_lower (a : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 4) + 16 * ucount a)) []
      ([O, O, O] ++ z4 ^ (a + 4) ++ [O])
      ([O, O, O] ++ z4 ^ 2 ++ a4 ^ (a + 1) ++ z4 ++ [I]) := by
  have h1 := U_prefix_L (a + 2)
  have h2 := finite_suffix [O, O, O, O, O, O, O, I] (U_near_end a)
  have h12 := finite_trans h1 h2
  refine SegRLs.congr h12 ?_ rfl
    (by rw [show a + 2 + 2 = a + 4 by omega]) (by norm_word)
  congr 1
  rw [near_end_count, show a + 2 + 2 = a + 4 by omega]

theorem z4_recut (p q : ℕ) : z4 ^ (p + q) ++ [O] = (z4 ^ p ++ [O]) ++ z4 ^ q := by
  rw [pow_add_list]
  norm_word

theorem reset_seek_finite (a b : ℕ) :
    SegRLs tm (hf ^ (16 * ucount a + 4 ^ (a + 4) + 13 * 4 ^ (a + b + 7))) []
      ([O, O, O] ++ z4 ^ (a + b + 9) ++ [O])
      ([O, O, O] ++ z4 ^ 2 ++ a4 ^ (1 + a) ++ z4 ++ a4 ++
        z4 ^ (2 + b) ++ a4 ++ [I, I, I, I, I]) := by
  have h1 := seek_top3 (a + b)
  have h2 := finite_suffix (z4 ^ (b + 2) ++ seek_tail) (seek_lower a)
  have hw : ([O, O, O] ++ z4 ^ (a + b + 6) ++ [O]) ++ seek_tail =
      ([O, O, O] ++ z4 ^ (a + 4) ++ [O]) ++ (z4 ^ (b + 2) ++ seek_tail) := by
    rw [show a + b + 6 = (a + 4) + (b + 2) by omega, pow_add_list]
    norm_word
  have h12 := finite_trans h1 h2 hw
  refine SegRLs.congr h12 (by congr 1; omega) rfl (by norm_word) ?_
  rw [show b + 2 = 2 + b by omega]
  norm_word

-- ============================================================================
-- 4. `H_cycle`, `H_lift` & Normal Caller `Ncfg` (`SOBCv14.v:453-605`)
-- ============================================================================

theorem H_cycle (a b : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 2))) hf (hword a (1 + b)) (hword (1 + a) b) := by
  have h1 : SegRLs tm (hf ^ 1) hf _ _ := H_OA a b
  have h2 := finite_suffix ([O, O, I] ++ b4 ^ b ++ a4 ++ [O]) (Ufinite_all (a + 1))
  have h3 : SegRLs tm (hf ^ 1) [] _ _ := H_OB (1 + a) b
  have h4 := finite_suffix (c4 ^ b ++ [O, I, I, I, I]) (Vfinite_all (a + 1))
  have h12 := run_trans h1 h2
  have h123 := run_trans h12 h3
  have h1234 := run_trans h123 h4
  refine SegRLs.congr h1234 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive (a + 1)
  have := ucount_power (a + 1)
  rw [show a + 2 = (a + 1) + 1 by omega]
  dsimp [vcount]
  omega


theorem reset_seek (a b : ℕ) (r : ListBlank Γ) :
    SideRLs tm (hf ^ (16 * ucount a + 4 ^ (a + 4) + 13 * 4 ^ (a + b + 7)))
      (([O, O, O] ++ z4 ^ (a + b + 9) ++ [O]) +> r)
      (([O, O, O] ++ z4 ^ 2 ++ a4 ^ (1 + a) ++ z4 ++ a4 ++
        z4 ^ (2 + b) ++ a4 ++ [I, I, I, I, I]) +> r) :=
  (reset_seek_finite a b).sideRLs_concat (.nil r)

def Ncfg (n : ℕ) (r : ListBlank Γ) : Cfg Γ Λ :=
  default <{{F}} ((z4 ++ c4 ^ n ++ [O, I, I, I, I]) +> r)

def Nleft (n : ℕ) : ListBlank Γ :=
  ([I, I, I, I, I] ++ [I, I, O, I] ^ (1 + n) ++ [I, I, O, O]) +> default

private theorem shift_A_c4_step (l r : ListBlank Γ) :
    (l {{A}}> (c4 +> r)) [tm]⊢* (([I, I, O, I] +> l) {{A}}> r) :=
  runSteps_spec tm 4 ⟨[], c4, A, .right⟩ ⟨[I, I, O, I], [], A, .right⟩ (by decide) l r

private theorem shift_A_c4 (n : ℕ) (l r : ListBlank Γ) :
    (l {{A}}> (c4 ^ n +> r)) [tm]⊢* (([I, I, O, I] ^ n +> l) {{A}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_A_c4_step l (c4 ^ n +> r)) ?_
    refine stepStar_congr (ih ([I, I, O, I] +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

theorem N_out (n : ℕ) (r : ListBlank Γ) :
    (Ncfg n r) [tm]⊢* (Nleft n {{F}}> r) := by
  have h1 : (Ncfg n r) [tm]⊢*
      (([I, I, O, I] +> ([I, I, O, O] +> default)) {{A}}> (c4 ^ n +> ([O, I, I, I, I] +> r))) := by
    have h := runSteps_spec tm 13 ⟨z4, [O, O], F, .left⟩
      ⟨[I, I, O, I, I, I], [], A, .right⟩ (by decide)
      default (c4 ^ n +> ([O, I, I, I, I] +> r))
    have hd : ([O, O] : List Γ) +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    have hl : ([I, I, O, I, I, I] : List Γ) +> (default : ListBlank Γ) =
        [I, I, O, I] +> ([I, I, O, O] +> default) :=
      calc ([I, I, O, I, I, I] : List Γ) +> default
        _ = [I, I, O, I, I, I] +> ([O, O] +> default) := by rw [hd]
        _ = ([I, I, O, I] ++ [I, I, O, O]) +> default := by rw [← append_assoc]; rfl
        _ = [I, I, O, I] +> ([I, I, O, O] +> default) := by rw [append_assoc]
    simpa only [Ncfg, BoundedConfig.toCfg, append_nil, append_assoc, hd, hl] using h
  have h2 := shift_A_c4 n ([I, I, O, I] +> ([I, I, O, O] +> default)) ([O, I, I, I, I] +> r)
  have h2' : (([I, I, O, I] ^ n +> ([I, I, O, I] +> ([I, I, O, O] +> default))) {{A}}>
      ([O, I, I, I, I] +> r)) =
      (([I, I, O, I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default))) {{A}}>
        ([O, I, I, I, I] +> r)) := by
    congr 1
    rw [← append_assoc, ← pow_succ_list', pow_succ_list, append_assoc]
  have h3 : (([I, I, O, I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default))) {{A}}>
      ([O, I, I, I, I] +> r)) [tm]⊢* (Nleft n {{F}}> r) := by
    have h := runSteps_spec tm 9 ⟨[I, I, O, I], [O, I, I, I, I], A, .right⟩
      ⟨[I, I, I, I, I] ++ [I, I, O, I], [], F, .right⟩ (by decide)
      ([I, I, O, I] ^ n +> ([I, I, O, O] +> default)) r
    have hl : ([I, I, I, I, I] ++ [I, I, O, I]) +>
        ([I, I, O, I] ^ n +> ([I, I, O, O] +> (default : ListBlank Γ))) = Nleft n := by
      unfold Nleft
      rw [show (1 + n : ℕ) = n + 1 by omega, pow_succ_list]
      simp only [append_assoc]
    simpa only [BoundedConfig.toCfg, append_nil, hl] using h
  exact stepStar_trans h1 (stepStar_trans (stepStar_congr h2 rfl h2') h3)

def Nturn (n : ℕ) : ListBlank Γ :=
  ([I, I, I, I] ++ [O, I, I, I] ^ (2 + n)) +> default

private theorem shift_E_1110_step (l r : ListBlank Γ) :
    (([I] +> ([I, I, O, I] +> l)) <{{E}} ([O, O, I, I] +> r)) [tm]⊢*
      (([I] +> l) <{{E}} ([O, O, I, I] +> ([O, O, I, I] +> r))) := by
  have h := runSteps_spec tm 10 ⟨[O, O, I, I], [I, I, I, O], E, .left⟩
    ⟨[O, O, I, I] ++ [O, O, I, I], [], E, .left⟩ (by decide) ([I] +> l) r
  have hl : ([I, I, I, O] : List Γ) +> ([I] +> l) = [I] +> ([I, I, O, I] +> l) := by
    rw [← append_assoc, ← append_assoc]; rfl
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc, hl] using h

private theorem shift_E_1110 (n : ℕ) (l r : ListBlank Γ) :
    (([I] +> ([I, I, O, I] ^ n +> l)) <{{E}} ([O, O, I, I] +> r)) [tm]⊢*
      (([I] +> l) <{{E}} ([O, O, I, I] +> ([O, O, I, I] ^ n +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_E_1110_step ([I, I, O, I] ^ n +> l) r) ?_
    refine stepStar_congr (ih ([O, O, I, I] +> r)) rfl ?_
    rw [← append_assoc ([O, O, I, I] ^ n) [O, O, I, I] r, ← pow_succ_list']

private theorem shift_F_0011_step (l r : ListBlank Γ) :
    (l {{F}}> ([O, O, I, I] +> r)) [tm]⊢* (([I, O, I, I] +> l) {{F}}> r) :=
  runSteps_spec tm 4 ⟨[], [O, O, I, I], F, .right⟩ ⟨[I, O, I, I], [], F, .right⟩ (by decide) l r

private theorem shift_F_0011 (k : ℕ) (l r : ListBlank Γ) :
    (l {{F}}> ([O, O, I, I] ^ k +> r)) [tm]⊢* (([I, O, I, I] ^ k +> l) {{F}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_F_0011_step l ([O, O, I, I] ^ k +> r)) ?_
    refine stepStar_congr (ih ([I, O, I, I] +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

private theorem IOII_pow_I (k : ℕ) :
    [I, O, I, I] ^ k ++ [I] = [I] ++ [O, I, I, I] ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list [I, O, I, I] k, List.append_assoc [I, O, I, I], ih,
      ← List.append_assoc [I, O, I, I] [I],
      show [I, O, I, I] ++ [I] = [I] ++ [O, I, I, I] from rfl,
      List.append_assoc [I] [O, I, I, I], ← pow_succ_list [O, I, I, I] k]

theorem N_return_1 (n : ℕ) (r : ListBlank Γ) :
    (Nleft n <{{E}} r) [tm]⊢* (Nturn n {{C}}> ([O] +> r)) := by
  have h_nl : Nleft n = ([I, I, I, I, I, I, I, O] +>
      ([I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default)))) := by
    unfold Nleft
    rw [pow_one_add [I, I, O, I] n]
    simp only [← append_assoc]
    rfl
  have h1 : (Nleft n <{{E}} r) [tm]⊢*
      (([I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default))) <{{E}}
        ([O, O, I, I] +> (z4 +> r))) := by
    rw [h_nl]
    have h := runSteps_spec tm 14 ⟨[], [I, I, I, I, I, I, I, O], E, .left⟩
      ⟨[O, O, I, I] ++ z4, [], E, .left⟩ (by decide)
      ([I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default))) r
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  have h2 := shift_E_1110 n ([I, I, O, O] +> default) (z4 +> r)
  have h3 : (([I] +> ([I, I, O, O] +> default)) <{{E}}
      ([O, O, I, I] +> ([O, O, I, I] ^ n +> (z4 +> r)))) [tm]⊢*
      (([I, O, I, I, I] +> default) {{F}}> ([O, O, I, I] ^ (1 + n) +> (z4 +> r))) := by
    have h := runSteps_spec tm 15 ⟨[O, O, I, I], [I, I, I, O, O], E, .left⟩
      ⟨[I, O, I, I, I], [O, O, I, I], F, .right⟩ (by decide)
      default ([O, O, I, I] ^ n +> (z4 +> r))
    have hl : ([I, I, I, O, O] : List Γ) +> (default : ListBlank Γ) =
        [I] +> ([I, I, O, O] +> default) := by
      rw [← append_assoc]; rfl
    have hr : [O, O, I, I] +> ([O, O, I, I] ^ n +> (z4 +> r)) =
        [O, O, I, I] ^ (1 + n) +> (z4 +> r) := by
      rw [pow_one_add, append_assoc]
    simpa only [BoundedConfig.toCfg, append_nil, hl, hr] using h
  have h4 := shift_F_0011 (1 + n) ([I, O, I, I, I] +> default) (z4 +> r)
  have h5 : (([I, O, I, I] ^ (1 + n) +> ([I, O, I, I, I] +> default)) {{F}}> (z4 +> r)) [tm]⊢*
      (Nturn n {{C}}> ([O] +> r)) := by
    have h := runSteps_spec tm 3 ⟨[], [O, O, O], F, .right⟩
      ⟨[I, I, I], [], C, .right⟩ (by decide)
      ([I, O, I, I] ^ (1 + n) +> ([I, O, I, I, I] +> default)) ([O] +> r)
    have hl : [I, I, I] +> ([I, O, I, I] ^ (1 + n) +> ([I, O, I, I,
        I] +> (default : ListBlank Γ))) =
        Nturn n := by
      unfold Nturn
      rw [← append_assoc, ← append_assoc]
      congr 1
      have hio := IOII_pow_I (1 + n)
      rw [show [I, I, I] ++ [I, O, I, I] ^ (1 + n) ++ [I, O, I, I, I] =
        [I, I, I] ++ ([I, O, I, I] ^ (1 + n) ++ [I]) ++ [O, I, I, I] from by norm_word,
        hio]
      norm_word
    have hr : ([O, O, O] : List Γ) +> ([O] +> r) = z4 +> r := by
      rw [← append_assoc]; rfl
    simpa only [BoundedConfig.toCfg, append_nil, hl, hr] using h
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

private theorem shift_E_10111_step (l r : ListBlank Γ) :
    (([I] +> ([O, I, I, I] +> l)) <{{E}} (z4 +> r)) [tm]⊢*
      (([I] +> l) <{{E}} (z4 +> ([I, I, O, O] +> r))) := by
  have h := runSteps_spec tm 10 ⟨z4, [I, O, I, I, I], E, .left⟩
    ⟨z4 ++ [I, I, O, O], [I], E, .left⟩ (by decide) l r
  have hl : ([I, O, I, I, I] : List Γ) +> l = [I] +> ([O, I, I, I] +> l) := by
    rw [← append_assoc]; rfl
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc, hl] using h

private theorem shift_E_10111 (k : ℕ) (l r : ListBlank Γ) :
    (([I] +> ([O, I, I, I] ^ k +> l)) <{{E}} (z4 +> r)) [tm]⊢*
      (([I] +> l) <{{E}} (z4 +> ([I, I, O, O] ^ k +> r))) := by
  induction k generalizing r with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_E_10111_step ([O, I, I, I] ^ k +> l) r) ?_
    refine stepStar_congr (ih ([I, I, O, O] +> r)) rfl ?_
    rw [← append_assoc ([I, I, O, O] ^ k) [I, I, O, O] r, ← pow_succ_list']

private theorem nreturn2_out_eq (n : ℕ) :
    [O] ++ z4 ++ [I, I, O, O] ^ (1 + n) ++ [I, I, I, I] =
      z4 ++ c4 ^ (1 + n) ++ [O, I, I, I, I] := by
  have h := h_ob_out_eq (1 + n)
  rw [show [O] ++ z4 ++ [I, I, O, O] ^ (1 + n) ++ [I, I, I, I] =
    z4 ++ ([O] ++ [I, I, O, O] ^ (1 + n) ++ [I, I, I, I]) from by norm_word,
    h]
  norm_word

theorem N_return_2 (n : ℕ) (r : ListBlank Γ) :
    (Nturn n {{C}}> ([O] +> r)) [tm]⊢* (Ncfg (1 + n) r) := by
  have h_nt : Nturn n = ([I, I, I, I, O, I, I] +>
      ([I] +> ([O, I, I, I] ^ (1 + n) +> default))) := by
    unfold Nturn
    rw [show 2 + n = 1 + (1 + n) by omega, pow_one_add [O, I, I, I] (1 + n)]
    rw [← append_assoc, ← append_assoc]
    rfl
  have h1 : (Nturn n {{C}}> ([O] +> r)) [tm]⊢*
      (([I] +> ([O, I, I, I] ^ (1 + n) +> default)) <{{E}} (z4 +> ([I, I, I, I] +> r))) := by
    rw [h_nt]
    have h := runSteps_spec tm 14 ⟨[I, I, I, I, O, I, I], [O], C, .right⟩
      ⟨z4 ++ [I, I, I, I], [], E, .left⟩ (by decide)
      ([I] +> ([O, I, I, I] ^ (1 + n) +> default)) r
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  have h2 := shift_E_10111 (1 + n) default ([I, I, I, I] +> r)
  have h3 : (([I] +> default) <{{E}} (z4 +> ([I, I, O, O] ^ (1 + n) +> ([I, I, I, I] +> r)))) [tm]⊢*
      (Ncfg (1 + n) r) := by
    have h := runSteps_spec tm 1 ⟨[], [I], E, .left⟩
      ⟨[O], [], F, .left⟩ (by decide)
      default (z4 +> ([I, I, O, O] ^ (1 + n) +> ([I, I, I, I] +> r)))
    have hr : [O] +> (z4 +> ([I, I, O, O] ^ (1 + n) +> ([I, I, I, I] +> r))) =
        (z4 ++ c4 ^ (1 + n) ++ [O, I, I, I, I]) +> r := by
      rw [← append_assoc, ← append_assoc, ← append_assoc, nreturn2_out_eq]
    simpa only [BoundedConfig.toCfg, Ncfg, append_nil, hr] using h
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem N_return (n : ℕ) (r : ListBlank Γ) :
    (Nleft n <{{E}} r) [tm]⊢* (Ncfg (1 + n) r) :=
  stepStar_trans (N_return_1 n r) (N_return_2 n r)

theorem N_step (n : ℕ) (r r' : ListBlank Γ) (H : SideRL tm (F, []) (E, []) r r') :
    (Ncfg n r) [tm]⊢⁺ (Ncfg (1 + n) r') :=
  stepStar_stepPlus_trans (N_out n r)
    (stepPlus_stepStar_trans (H (Nleft n)) (N_return n r'))

theorem N_run (m n : ℕ) (r r' : ListBlank Γ) (H : SideRLs tm (hf ^ m) r r') :
    (Ncfg n r) [tm]⊢* (Ncfg (n + m) r') :=
  SegCount.N_run (fun n r r_mid h => by { cases h with | cons h_call h_rest =>
      cases h_rest; have h_step :=
      N_step n r r_mid h_call; rwa [Nat.add_comm 1 n] at h_step }) m n r r' H

theorem N_H_lift (n a b j : ℕ) (r r' : ListBlank Γ) (H : SideRLs tm (hf ^ j) r r') :
    (Ncfg n (hword a (j + b) +> r)) [tm]⊢*
      (Ncfg (n + 4 ^ (a + 2) * qcount j) (hword (a + j) b +> r')) :=
  SegCount.N_H_lift (fun n r r_mid h => by { cases h with | cons h_call h_rest =>
      cases h_rest; have h_step :=
      N_step n r r_mid h_call; rwa [Nat.add_comm 1 n] at h_step }) H_cycle n a b j r r' H

theorem H_empty_batch (a : ℕ) :
    SegRLs tm (hf ^ (1 + ucount (a + 2))) hf (hword a 0)
      ([O, O, I] ++ a4 ^ (a + 2) ++ [I]) := by
  have h1 : SegRLs tm (hf ^ 1) hf _ _ := H_empty_F a
  have h2 := Ufinite_all (a + 2)
  exact run_trans h1 h2

-- ============================================================================
-- 5. Saturated Carry, `N_E_return`, & `boundary_reset` (`SOBCv14.v:639-1085`)
-- ============================================================================

theorem saturated_bit (k : ℕ) :
    SegRLs tm (hf ^ (4 ^ (1 + k))) []
      ([O, O, I] ++ a4 ^ (1 + k) ++ [O])
      ([O, O, I] ++ a4 ^ (1 + k) ++ [I]) := by
  cases k with
  | zero => exact BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)
  | succ k =>
    have h1 : SegRLs tm (hf ^ 1) [] _ _ := bridge_L2 k
    have h2 := finite_suffix [O, O, O, I, I] (Vfinite_all k)
    have h3 := finite_suffix1 [I] (bridge_L4_1 k)
    have h4 := finite_suffix [I, I, I, I] (Ufinite_all (k + 1))
    have h5 := finite_suffix1 [I] (bridge_L3_1 k)
    have h6 := finite_suffix [O, O, I, I, I] (Vfinite_all k)
    have h7 := finite_suffix1 [I] (bridge_L4_3 k)
    have h8 := finite_suffix [O, O, O, I] (Ufinite_all (k + 1))
    have h12 := finite_trans h1 h2
    have h123 := finite_trans h12 h3
    have h1234 := finite_trans h123 h4
    have h12345 := finite_trans h1234 h5
    have h123456 := finite_trans h12345 h6
    have h1234567 := finite_trans h123456 h7
    have h12345678 := finite_trans h1234567 h8
    refine SegRLs.congr h12345678 ?_ rfl (by norm_word) (by norm_word)
    congr 1
    have := ucount_positive k
    have := ucount_power (k + 1)
    rw [show 1 + (k + 1) = (k + 1) + 1 by omega]
    dsimp [vcount, ucount] at *
    omega

theorem saturated_zeros (p k : ℕ) :
    SegRLs tm (hf ^ (4 ^ (1 + k) * ucount p)) []
      ([O, O, I] ++ a4 ^ (1 + k) ++ z4 ^ p ++ [O, O, O, I])
      ([O, O, I] ++ a4 ^ (1 + k + p) ++ b4) := by
  induction p generalizing k with
  | zero =>
    have h := finite_suffix [O, O, I] (saturated_bit k)
    refine SegRLs.congr h (by rw [ucount, Nat.mul_one]) rfl (by norm_word) ?_
    rw [Nat.add_zero]
    norm_word
  | succ p ih =>
    have h1 := finite_suffix ([O, O, O] ++ z4 ^ p ++ [O, O, O, I]) (saturated_bit k)
    have h2 := ih (k + 1)
    have h12 := finite_trans h1 h2
    refine SegRLs.congr h12 ?_ rfl (by norm_word)
      (by rw [show 1 + k + (p + 1) = 1 + (k + 1) + p by omega])
    congr 1
    rw [ucount, show 1 + (k + 1) = (1 + k) + 1 by omega, pow4_next]
    ring

private theorem shift_F_11101_step (l r : ListBlank Γ) :
    (([I] +> ([I, I, O, I] +> l)) <{{F}} ([O, O, O, I, I, O, O] +> r)) [tm]⊢*
      (([I] +> l) <{{F}} ([O, O, O, I, I, O, O] +> ([I, I, O, O] +> r))) := by
  have h := runSteps_spec tm 12 ⟨[O, O, O, I, I, O, O], [I, I, I, O, I], F, .left⟩
    ⟨[O, O, O, I, I, O, O] ++ [I, I, O, O], [I], F, .left⟩ (by decide) l r
  have hl : ([I, I, I, O, I] : List Γ) +> l = [I] +> ([I, I, O, I] +> l) := by
    rw [← append_assoc]; rfl
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc, hl] using h

private theorem shift_F_11101 (n : ℕ) (l r : ListBlank Γ) :
    (([I] +> ([I, I, O, I] ^ n +> l)) <{{F}} ([O, O, O, I, I, O, O] +> r)) [tm]⊢*
      (([I] +> l) <{{F}} ([O, O, O, I, I, O, O] +> ([I, I, O, O] ^ n +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_F_11101_step ([I, I, O, I] ^ n +> l) r) ?_
    refine stepStar_congr (ih ([I, I, O, O] +> r)) rfl ?_
    rw [← append_assoc ([I, I, O, O] ^ n) [I, I, O, O] r, ← pow_succ_list']

private theorem shift_C_b4_step (l r : ListBlank Γ) :
    (l {{C}}> (b4 +> r)) [tm]⊢* (([O, I, I, I] +> l) {{C}}> r) :=
  runSteps_spec tm 4 ⟨[], b4, C, .right⟩ ⟨[O, I, I, I], [], C, .right⟩ (by decide) l r

private theorem shift_C_b4 (n : ℕ) (l r : ListBlank Γ) :
    (l {{C}}> (b4 ^ n +> r)) [tm]⊢* (([O, I, I, I] ^ n +> l) {{C}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_b4_step l (b4 ^ n +> r)) ?_
    refine stepStar_congr (ih ([O, I, I, I] +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

private theorem shift_F_0111_step (l r : ListBlank Γ) :
    (([O, I, I, I] +> l) <{{F}} ([O, O, O, O, O, I, I] +> r)) [tm]⊢*
      (l <{{F}} ([O, O, O, O, O, I, I] +> ([O, O, I, I] +> r))) := by
  have h := runSteps_spec tm 10 ⟨[O, O, O, O, O, I, I], [O, I, I, I], F, .left⟩
    ⟨[O, O, O, O, O, I, I] ++ [O, O, I, I], [], F, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

private theorem shift_F_0111 (n : ℕ) (l r : ListBlank Γ) :
    (([O, I, I, I] ^ n +> l) <{{F}} ([O, O, O, O, O, I, I] +> r)) [tm]⊢*
      (l <{{F}} ([O, O, O, O, O, I, I] +> ([O, O, I, I] ^ n +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_F_0111_step ([O, I, I, I] ^ n +> l) r) ?_
    refine stepStar_congr (ih ([O, O, I, I] +> r)) rfl ?_
    rw [← append_assoc ([O, O, I, I] ^ n) [O, O, I, I] r, ← pow_succ_list']

private theorem neret_mid_eq (n : ℕ) :
    [I, O, O, I, I, O, O] ++ [I, I, O, O] ^ n ++ z4 =
      b4 ^ n ++ [I, O, O, I, I, O, O, O, O, O, O] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : [I, O, O, I, I, O, O] ++ [I, I, O, O] ^ (n + 1) ++ z4 =
        b4 ++ ([I, O, O, I, I, O, O] ++ [I, I, O, O] ^ n ++ z4) := by
      rw [pow_succ_list]; simp only [b4, List.cons_append, List.nil_append]
    rw [h1, ih, pow_succ_list, List.append_assoc]

private theorem neret_end_eq (n : ℕ) :
    [O, I, I] ++ [O, O, I, I] ^ n ++ [I, I, O, O] =
      c4 ^ n ++ [O, I, I, I, I, O, O] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : [O, I, I] ++ [O, O, I, I] ^ (n + 1) ++ [I, I, O, O] =
        c4 ++ ([O, I, I] ++ [O, O, I, I] ^ n ++ [I, I, O, O]) := by
      rw [pow_succ_list]; simp only [c4, List.cons_append, List.nil_append]
    rw [h1, ih, pow_succ_list, List.append_assoc]

theorem N_E_return (n : ℕ) (r : ListBlank Γ) :
    (Nleft n <{{F}} ([O, O, O] +> r)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ n ++ [O, I, I, I, I, O, O]) +> r)) := by
  have h_nl : Nleft n = ([I, I, I, I, I, I, I, O] +>
      ([I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default)))) := by
    unfold Nleft
    rw [pow_one_add [I, I, O, I] n]
    simp only [← append_assoc]
    rfl
  have h1 : (Nleft n <{{F}} ([O, O, O] +> r)) [tm]⊢⁺
      (([I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default))) <{{F}}
        ([O, O, O, I, I, O, O] +> (z4 +> r))) := by
    rw [h_nl]
    have h := runSteps1_spec tm 15 ⟨[O, O, O], [I, I, I, I, I, I, I, O], F, .left⟩
      ⟨[O, O, O, I, I, O, O] ++ z4, [], F, .left⟩ (by decide)
      ([I] +> ([I, I, O, I] ^ n +> ([I, I, O, O] +> default))) r
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  have h2 := shift_F_11101 n ([I, I, O, O] +> default) (z4 +> r)
  have h3 : (([I] +> ([I, I, O, O] +> default)) <{{F}}
      ([O, O, O, I, I, O, O] +> ([I, I, O, O] ^ n +> (z4 +> r)))) [tm]⊢*
      (([I, I, I, I, I, I, O, O] +> default) {{C}}>
        (b4 ^ n +> ([I, O, O, I, I, O, O, O, O, O, O] +> r))) := by
    have h := runSteps_spec tm 29 ⟨[O, O, O, I, I, O, O], [I, I, I, O, O, O, O, O], F, .left⟩
      ⟨[I, I, I, I, I, I, O, O], [I, O, O, I, I, O, O], C, .right⟩ (by decide)
      default ([I, I, O, O] ^ n +> (z4 +> r))
    have hl : ([I, I, I, O, O, O, O, O] : List Γ) +> (default : ListBlank Γ) =
        [I] +> ([I, I, O, O] +> default) := by
      rw [show ([I, I, I, O, O, O, O, O] : List Γ) = [I, I, I, O, O] ++ [O, O, O] from rfl,
        append_assoc, BoundedConfig.all0_spec (a := [O, O, O]) (by decide)]
      rfl
    have hr : [I, O, O, I, I, O, O] +> ([I, I, O, O] ^ n +> (z4 +> r)) =
        b4 ^ n +> ([I, O, O, I, I, O, O, O, O, O, O] +> r) := by
      rw [← append_assoc, ← append_assoc, neret_mid_eq, append_assoc]
    simpa only [BoundedConfig.toCfg, append_nil, hl, hr] using h
  have h4 := shift_C_b4 n ([I, I, I, I, I, I, O, O] +> default)
    ([I, O, O, I, I, O, O, O, O, O, O] +> r)
  have h5 : (([O, I, I, I] ^ n +> ([I, I, I, I, I, I, O, O] +> default)) {{C}}>
      ([I, O, O, I, I, O, O, O, O, O, O] +> r)) [tm]⊢*
      (([O, I, I, I] ^ n +> ([I, I, I, I, I, I, O, O] +> default)) <{{F}}
        ([O, O, O, O, O, I, I] +> ([I, I, O, O] +> r))) := by
    have h := runSteps_spec tm 23 ⟨[], [I, O, O, I, I, O, O, O, O, O, O], C, .right⟩
      ⟨[O, O, O, O, O, I, I] ++ [I, I, O, O], [], F, .left⟩ (by decide)
      ([O, I, I, I] ^ n +> ([I, I, I, I, I, I, O, O] +> default)) r
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  have h6 := shift_F_0111 n ([I, I, I, I, I, I, O, O] +> default) ([I, I, O, O] +> r)
  have h7 : (([I, I, I, I, I, I, O, O] +> default) <{{F}}
      ([O, O, O, O, O, I, I] +> ([O, O, I, I] ^ n +> ([I, I, O, O] +> r)))) [tm]⊢*
      (Ncfg 0 (([O, O, O] ++ c4 ^ n ++ [O, I, I, I, I, O, O]) +> r)) := by
    have h := runSteps_spec tm 36 ⟨[O, O, O, O, O], [I, I, I, I, I, I, O, O], F, .left⟩
      ⟨z4 ++ [O, I, I, I, I] ++ [O, O, O] ++ [O], [], F, .left⟩ (by decide)
      default ([I, I] +> ([O, O, I, I] ^ n +> ([I, I, O, O] +> r)))
    have hr1 : ([O, O, O, O, O] : List Γ) +> ([I, I] +> ([O, O, I, I] ^ n +> ([I, I, O, O] +> r))) =
        [O, O, O, O, O, I, I] +> ([O, O, I, I] ^ n +> ([I, I, O, O] +> r)) := by
      rw [← append_assoc]; rfl
    have hr2 : (z4 ++ [O, I, I, I, I] ++ [O, O, O] ++ [O]) +>
        ([I, I] +> ([O, O, I, I] ^ n +> ([I, I, O, O] +> r))) =
        (z4 ++ c4 ^ 0 ++ [O, I, I, I, I]) +> (([O, O, O] ++ c4 ^ n ++ [O, I, I, I, I, O,
            O]) +> r) := by
      rw [pow_zero_list, List.append_nil,
        show (z4 ++ [O, I, I, I, I] ++ [O, O, O] ++ [O]) +>
          ([I, I] +> ([O, O, I, I] ^ n +> ([I, I, O, O] +> r))) =
          (z4 ++ [O, I, I, I, I]) +> (([O, O, O] ++ ([O, I, I] ++ [O, O, I, I] ^ n ++ [I, I, O,
              O])) +> r)
          from by simp only [← append_assoc]; rfl,
        neret_end_eq, ← List.append_assoc [O, O, O]]
    simpa only [BoundedConfig.toCfg, Ncfg, append_nil, hr1, hr2] using h
  exact stepPlus_stepStar_trans h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6
        h7)))))

theorem N_E_reset (n : ℕ) (r r' : ListBlank Γ)
    (H : SideRL tm (F, []) (F, []) r ([O, O, O] +> r')) :
    (Ncfg n r) [tm]⊢⁺ (Ncfg 0 (([O, O, O] ++ c4 ^ n ++ [O, I, I, I, I, O, O]) +> r')) :=
  stepStar_stepPlus_trans (N_out n r) (stepPlus_trans (H (Nleft n)) (N_E_return n r'))

theorem C_BAAZ :
    SegRLs tm [((C, []), (F, []))] []
      (b4 ++ a4 ++ a4 ++ z4) (z4 ++ c4 ++ [O, O, O, I] ++ a4) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem A_C0001 :
    SegRLs tm [((A, []), (F, []))] []
      (c4 ++ [O, O, O, I]) [O, O, O, I, I, I, I, I] :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem C_B1111 :
    SegRLs tm [((C, []), (F, []))] [] (b4 ++ [I, I, I, I]) (z4 ++ z4) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem A_AZ :
    SegRLs tm [((A, []), (E, []))] [] (a4 ++ z4) (z4 ++ [I, I, I, I]) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem P_to_J (k r : ℕ) (w y : List Γ)
    (H : SegRLs tm [((C, []), (F, []))] [] w (z4 ^ r ++ y)) :
    SegRLs tm (hf ^ (1 + vcount (k + r))) []
      ([O, O, I] ++ a4 ^ (1 + k) ++ w)
      ([O, O, I] ++ d4 ++ e4 ^ (k + r) ++ y) := by
  have h1 : SegRLs tm (hf ^ 1) [] _ _ := (P_F k).concat H
  have h2 := finite_suffix y (Vfinite_all (k + r))
  have h12 := finite_trans h1 h2 (by rw [pow_add_list]; norm_word)
  exact SegRLs.congr h12 rfl rfl (by norm_word) (by norm_word)

theorem J_to_P (a s : ℕ) (w y : List Γ)
    (H : SegRLs tm [((A, []), (F, []))] [] w (z4 ^ s ++ [O] ++ y)) :
    SegRLs tm (hf ^ (1 + ucount (1 + a + s))) []
      ([O, O, I] ++ d4 ++ e4 ^ a ++ w)
      ([O, O, I] ++ a4 ^ (1 + a + s) ++ [I] ++ y) := by
  have h1 : SegRLs tm (hf ^ 1) [] _ _ := (J_F a).concat H
  have h2 := finite_suffix y (Ufinite_all (1 + a + s))
  have h12 := finite_trans h1 h2 (by rw [pow_add_list z4 (1 + a) s]; norm_word)
  exact SegRLs.congr h12 rfl rfl (by norm_word) (by norm_word)

theorem H_advance (a p : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 3))) []
      (hword a 0 ++ [O, O, O] ++ z4 ^ (2 + p))
      (hword (a + 2) 0 ++ [O, O, O] ++ z4 ^ p) := by
  have hcall := finite_suffix ([O, O, O] ++ z4 ^ (1 + p)) Ufinite_0
  have h1 := (H_empty_batch a).concat hcall
  have h2 := finite_suffix1 ([O, O, O] ++ z4 ^ p) (H_OB (a + 2) 0)
  have h3 := finite_suffix ([O, I, I, I, I, O, O, O] ++ z4 ^ p) (Vfinite_all (a + 2))
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
  refine SegRLs.congr h123 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive (a + 2)
  have := ucount_power (a + 2)
  rw [show a + 3 = (a + 2) + 1 by omega]
  dsimp [vcount]
  omega

theorem ucount_add (a b : ℕ) :
    ucount (a + b + 1) = ucount a + 4 ^ (a + 1) * ucount b := by
  have ha := ucount_power a
  have hb := ucount_power b
  have hab := ucount_power (a + b + 1)
  rw [show a + b + 1 + 1 = (a + 1) + (b + 1) by omega, Nat.pow_add] at hab
  nlinarith

theorem H_collapse (a k : ℕ) :
    SegRLs tm (hf ^ (1 + ucount (a + k + 2))) []
      (hword a 0 ++ [O, O, O] ++ a4 ^ k ++ z4)
      ([O, O, I] ++ a4 ^ (a + k + 2) ++ b4 ++ a4) := by
  cases k with
  | zero =>
    have hcall := finite_suffix [O, O, O] Ufinite_0
    have h := (H_empty_batch a).concat hcall
    exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)
  | succ k =>
    have h1 := (H_empty_batch a).concat (F_AZ_large k)
    have h2 := finite_suffix a4 (saturated_zeros k (a + 2))
    have h12 := finite_trans h1 h2
    refine SegRLs.congr h12 ?_ rfl (by norm_word)
      (by rw [show a + (k + 1) + 2 = 1 + (a + 2) + k by omega])
    congr 1
    have hc := ucount_add (a + 2) k
    rw [show a + 2 + k + 1 = a + (k + 1) + 2 by omega, show 1 + (a + 2) = a + 2 + 1 by omega] at *
    omega

theorem boundary_five (a b p : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 3) + 13 * 4 ^ (a + b + 5))) []
      (hword a 0 ++ [O, O, O] ++ z4 ^ 2 ++ a4 ^ b ++ z4 ++ a4 ++ z4 ^ (2 + p))
      ([O, O, I] ++ d4 ++ e4 ^ (a + b + 6) ++ a4 ++ z4 ^ (1 + p)) := by
  have h1 := finite_suffix (a4 ^ b ++ z4 ++ a4 ++ z4 ^ (2 + p)) (H_advance a 0)
  have h2 := finite_suffix (a4 ++ z4 ^ (2 + p)) (H_collapse (a + 2) b)
  have hc3 : SegRLs tm [((C, []), (F, []))] []
      (b4 ++ a4 ++ a4 ++ z4 ^ (2 + p))
      (z4 ^ 1 ++ (c4 ++ [O, O, O, I] ++ a4 ++ z4 ^ (1 + p))) :=
    SegRLs.congr (segment_suffix (z4 ^ (1 + p)) C_BAAZ) rfl rfl (by norm_word) (by norm_word)
  have h3 := P_to_J (a + b + 3) 1 _ _ hc3
  have hc4 : SegRLs tm [((A, []), (F, []))] []
      (c4 ++ [O, O, O, I] ++ a4 ++ z4 ^ (1 + p))
      (z4 ^ 0 ++ [O] ++ ([O, O, I, I, I, I, I] ++ a4 ++ z4 ^ (1 + p))) :=
    SegRLs.congr (segment_suffix (a4 ++ z4 ^ (1 + p)) A_C0001) rfl rfl (by norm_word) (by norm_word)
  have h4 := J_to_P (a + b + 4) 0 _ _ hc4
  have hc5 : SegRLs tm [((C, []), (F, []))] []
      (b4 ++ [I, I, I, I] ++ a4 ++ z4 ^ (1 + p))
      (z4 ^ 2 ++ (a4 ++ z4 ^ (1 + p))) :=
    SegRLs.congr (segment_suffix (a4 ++ z4 ^ (1 + p)) C_B1111) rfl rfl (by norm_word) (by norm_word)
  have h5 := P_to_J (a + b + 4) 2 _ _ hc5
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
    (by rw [show a + 2 + b + 2 = 1 + (a + b + 3) by omega]; norm_word)
  have h1234 := finite_trans h123 h4
    (by rw [show a + b + 3 + 1 = a + b + 4 by omega])
  have h12345 := finite_trans h1234 h5
    (by rw [show 1 + (a + b + 4) + 0 = 1 + (a + b + 4) by omega]; norm_word)
  refine SegRLs.congr h12345 ?_ rfl (by norm_word)
    (by rw [show a + b + 4 + 2 = a + b + 6 by omega]; norm_word)
  congr 1
  have := ucount_positive (a + b + 4)
  have := ucount_power (a + b + 4)
  rw [show a + 2 + b + 2 = a + b + 4 by omega,
    show a + b + 3 + 1 = a + b + 4 by omega,
    show 1 + (a + b + 4) + 0 = (a + b + 4) + 1 by omega,
    show a + b + 4 + 2 = (a + b + 4) + 2 by omega,
    show a + b + 5 = (a + b + 4) + 1 by omega]
  dsimp [vcount, ucount] at *
  omega

theorem finite_single_side {h₁ h₂ : DH0 Γ Λ} {w₁ w₂ : List Γ} (r : ListBlank Γ)
    (H : SegRLs tm [(h₁, h₂)] [] w₁ w₂) :
    SideRL tm h₁ h₂ (w₁ +> r) (w₂ +> r) := by
  have hs := H.sideRLs_concat (.nil r)
  cases hs with
  | cons hcall hnil =>
    cases hnil
    exact hcall

theorem J_E_finite (a p : ℕ) :
    SegRLs tm [((F, []), (F, []))] []
      ([O, O, I] ++ d4 ++ e4 ^ a ++ a4 ++ z4 ^ (1 + p))
      ([O, O, O] ++ z4 ^ (a + 2) ++ [I, I, I, I] ++ z4 ^ p) := by
  have h := segment_suffix (z4 ^ p) ((J_E a).concat A_AZ)
  exact SegRLs.congr h rfl rfl (by norm_word) (by norm_word)

theorem J_reset (n a p : ℕ) (r : ListBlank Γ) :
    (Ncfg n (([O, O, I] ++ d4 ++ e4 ^ a ++ a4 ++ z4 ^ (1 + p)) +> r)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ n ++ [O, I, I, I, I, O, O] ++
        z4 ^ (a + 2) ++ [I, I, I, I] ++ z4 ^ p) +> r)) := by
  have h := finite_single_side r (J_E_finite a p)
  have h' : SideRL tm (F, []) (F, [])
      (([O, O, I] ++ d4 ++ e4 ^ a ++ a4 ++ z4 ^ (1 + p)) +> r)
      ([O, O, O] +> ((z4 ^ (a + 2) ++ [I, I, I, I] ++ z4 ^ p) +> r)) := by
    intro l
    simpa only [append_assoc] using h l
  have hn := N_E_reset n _ _ h'
  refine stepPlus_congr hn rfl ?_
  simp only [Ncfg, append_assoc]

theorem boundary_reset (n a b p : ℕ) (r : ListBlank Γ) :
    (Ncfg n ((hword a 0 ++ [O, O, O] ++ z4 ^ 2 ++ a4 ^ b ++
      z4 ++ a4 ++ z4 ^ (2 + p)) +> r)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ (n + 4 ^ (a + 3) + 13 * 4 ^ (a + b + 5)) ++
        [O, I, I, I, I, O, O] ++ z4 ^ (a + b + 8) ++ [I, I, I, I] ++ z4 ^ p) +> r)) := by
  have hf_side := (boundary_five a b p).sideRLs_concat (.nil r)
  have hrun := N_run (4 ^ (a + 3) + 13 * 4 ^ (a + b + 5)) n _ _ hf_side
  have hreset := J_reset (n + (4 ^ (a + 3) + 13 * 4 ^ (a + b + 5))) (a + b + 6) p r
  refine stepStar_stepPlus_trans hrun (stepPlus_congr hreset rfl ?_)
  rw [show n + (4 ^ (a + 3) + 13 * 4 ^ (a + b + 5)) =
      n + 4 ^ (a + 3) + 13 * 4 ^ (a + b + 5) by omega,
    show a + b + 6 + 2 = a + b + 8 by omega]

theorem reset_lift (j : ℕ) (r r' : ListBlank Γ) (H : SideRLs tm (hf ^ j) r r') :
    (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + j) ++ [O, I, I, I, I]) +> r)) [tm]⊢⁺
      (Ncfg (1 + 16 * qcount j) (hword j 0 +> r')) := by
  have hv := finite_suffix (c4 ^ j ++ [O, I, I, I, I]) Vfinite_0
  have hs := finite_single_side r hv
  have hs' : SideRL tm (F, []) (E, [])
      (([O, O, O] ++ c4 ^ (1 + j) ++ [O, I, I, I, I]) +> r)
      (hword 0 j +> r) := by
    have hw1 : ([O, O, O] ++ c4 ++ z4 ^ 0) ++ (c4 ^ j ++ [O, I, I, I, I]) =
        [O, O, O] ++ c4 ^ (1 + j) ++ [O, I, I, I, I] := by norm_word
    have hw2 : ([O, O, I] ++ d4 ++ e4 ^ 0) ++ (c4 ^ j ++ [O, I, I, I, I]) = hword 0 j := by
      norm_word
    intro l
    simpa only [hw1, hw2] using hs l
  have h1 := N_step 0 _ _ hs'
  have h2 := N_H_lift 1 0 0 j r r' H
  refine stepPlus_stepStar_trans h1 (stepStar_congr h2 ?_ ?_)
  · rw [Nat.add_zero]
  · simp only [Nat.zero_add]; rfl

theorem reset_suffix_recut (k p : ℕ) :
    [O, I, I, I, I, O, O] ++ z4 ^ (k + 1) ++ [I, I, I, I] ++ z4 ^ p =
      [O, I, I, I, I] ++ [O, O, O] ++ z4 ^ k ++ [O, O, O, I, I, I, I] ++ z4 ^ p := by
  norm_word

def reset_budget (a b : ℕ) : ℕ := 16 * ucount a + 4 ^ (a + 4) + 13 * 4 ^ (a + b + 7)
def next_a (a b : ℕ) : ℕ := 63 + 208 * ucount a + 13 * 4 ^ (a + b + 7)

theorem reset_budget_next (a b : ℕ) : reset_budget a b = 1 + next_a a b := by
  unfold reset_budget next_a
  have := ucount_power a
  have : 4 ^ (a + 4) = 64 * 4 ^ (a + 1) := by
    rw [show a + 4 = (a + 1) + 1 + 1 + 1 by omega, pow4_next, pow4_next, pow4_next]
    ring
  omega

theorem invariant_forward_count (a b : ℕ) :
    1 + 16 * ucount a + 4 ^ (1 + a + 3) + 13 * 4 ^ (1 + a + (1 + b) + 5) = 2 + next_a a b := by
  have hnext := reset_budget_next a b
  unfold reset_budget at hnext
  rw [show 1 + a + 3 = a + 4 by omega,
    show 1 + a + (1 + b) + 5 = a + b + 7 by omega]
  omega

def invariant (a b p : ℕ) (r : ListBlank Γ) : Cfg Γ Λ :=
  Ncfg (1 + 16 * ucount a)
    ((hword (1 + a) 0 ++ [O, O, O] ++ z4 ^ 2 ++ a4 ^ (1 + b) ++
      z4 ++ a4 ++ z4 ^ (2 + p)) +> r)

theorem qcount_succ_ucount (k : ℕ) : qcount (1 + k) = ucount k := by
  rw [Nat.add_comm 1 k]; rfl

theorem reset_finish (a b p : ℕ) (r : ListBlank Γ) :
    (Ncfg 0 (([O, O, O] ++ c4 ^ (2 + next_a a b) ++ [O, I, I, I, I, O, O] ++
      z4 ^ (a + b + 10) ++ [I, I, I, I] ++ z4 ^ p) +> r)) [tm]⊢⁺
      invariant (next_a a b) a b
        ((a4 ++ [I, I, I, I] ++ b4 ++ [I, I, I] ++ z4 ^ p) +> r) := by
  have hs := reset_seek a b (([O, O, I, I, I, I] ++ z4 ^ p) +> r)
  have hl := reset_lift (reset_budget a b) _ _ hs
  refine stepPlus_congr hl ?_ ?_
  · rw [reset_budget_next, show 1 + (1 + next_a a b) = 2 + next_a a b by omega,
      show a + b + 10 = (a + b + 9) + 1 by omega]
    apply congrArg (Ncfg 0)
    simp only [← append_assoc]
    apply congrArg (· +> r)
    have hrecut := reset_suffix_recut (a + b + 9) p
    have hrhs : [O, O, O] ++ c4 ^ (2 + next_a a b) ++ [O, I, I, I, I, O, O] ++
        z4 ^ ((a + b + 9) + 1) ++ [I, I, I, I] ++ z4 ^ p =
        [O, O, O] ++ c4 ^ (2 + next_a a b) ++
          ([O, I, I, I, I, O, O] ++ z4 ^ ((a + b + 9) + 1) ++ [I, I, I, I] ++ z4 ^ p) := by
      simp only [List.append_assoc]
    rw [hrhs, hrecut]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [reset_budget_next, qcount_succ_ucount]
    unfold invariant
    apply congrArg (Ncfg _)
    simp only [← append_assoc]
    apply congrArg (· +> r)
    simp only [b4, List.append_assoc, List.cons_append, List.nil_append]

theorem invariant_forward (a b p : ℕ) (r : ListBlank Γ) :
    (invariant a b p r) [tm]⊢⁺
      invariant (next_a a b) a b
        ((a4 ++ [I, I, I, I] ++ b4 ++ [I, I, I] ++ z4 ^ p) +> r) := by
  have h1 := boundary_reset (1 + 16 * ucount a) (1 + a) (1 + b) p r
  have h1' : (invariant a b p r) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ (2 + next_a a b) ++ [O, I, I, I, I, O, O] ++
        z4 ^ (a + b + 10) ++ [I, I, I, I] ++ z4 ^ p) +> r)) := by
    refine stepPlus_congr h1 rfl ?_
    rw [invariant_forward_count a b, show 1 + a + (1 + b) + 8 = a + b + 10 by omega]
  exact stepPlus_trans h1' (reset_finish a b p r)

-- ============================================================================
-- 6. Entrance Families & `post_to_invariant` (`SOBCv14.v:1094-1872`)
-- ============================================================================

theorem A_C0011 : SegRLs tm [((A, []), (F, []))] [] (c4 ++ [O, O, I, I]) ([O, O, O, I] ++ a4) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem C_BAW : SegRLs tm [((C, []), (F, []))] [] (b4 ++ a4 ++ [I, I, I, I]) (z4 ++ c4 ++ [O, O, I,
    I]) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem C_BAA0 : SegRLs tm [((C, []), (F, []))] [] (b4 ++ a4 ++ a4 ++ [O]) (z4 ++ c4 ++ [O, O, O, I,
    I]) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem A_CZ : SegRLs tm [((A, []), (F, []))] [] (c4 ++ z4) ([O, O, O, I] ++ d4) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem C_BDZ : SegRLs tm [((C, []), (F, []))] [] (b4 ++ d4 ++ z4) (z4 ++ z4 ++ c4) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem C_BD0011 : SegRLs tm [((C, []), (F, []))] [] (b4 ++ d4 ++ [O, O, I, I]) (z4 ^ 3) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem A_B111 : SegRLs tm [((A, []), (E, []))] [] (b4 ++ [I, I, I]) [O, O, I, I, O, I, I] :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem C_BA6W :
    SegRLs tm [((C, []), (F, []))] []
      (b4 ++ a4 ^ 6 ++ [I, I, I, I]) (z4 ++ c4 ++ z4 ^ 5 ++ [O, O, I, I]) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem F_AZ_small : SegRLs tm hf [] ([O, O, O] ++ z4) ([O, O, I] ++ a4) :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

theorem J_consume (a : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 2))) []
      ([O, O, I] ++ d4 ++ e4 ^ a ++ c4 ++ [O, O, I, I] ++ [I, I, I, I])
      ([O, O, I] ++ d4 ++ e4 ^ (a + 1) ++ c4 ++ [O, O, I, I]) := by
  have hc1 : SegRLs tm [((A, []), (F, []))] [] (c4 ++ [O, O, I, I])
      (z4 ^ 0 ++ [O] ++ ([O, O, I] ++ a4)) := A_C0011
  have h1 := finite_suffix [I, I, I, I] (J_to_P a 0 _ _ hc1)
  have hc2 : SegRLs tm [((C, []), (F, []))] [] (b4 ++ a4 ++ [I, I, I, I])
      (z4 ^ 1 ++ (c4 ++ [O, O, I, I])) :=
    SegRLs.congr C_BAW rfl rfl rfl (by norm_word)
  have h2 := P_to_J a 1 _ _ hc2
  have h12 := finite_trans h1 h2
  refine SegRLs.congr h12 ?_ rfl (by norm_word) (by norm_word)
  congr 1
  have := ucount_positive (a + 1)
  have := ucount_power (a + 1)
  rw [show 1 + a + 0 = a + 1 by omega, show a + 2 = (a + 1) + 1 by omega]
  dsimp [vcount]
  omega

theorem J_consume_many (s a : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 2) * qcount s)) []
      ([O, O, I] ++ d4 ++ e4 ^ a ++ c4 ++ [O, O, I, I] ++ [I, I, I, I] ^ s)
      ([O, O, I] ++ d4 ++ e4 ^ (a + s) ++ c4 ++ [O, O, I, I]) := by
  induction s generalizing a with
  | zero =>
    simp only [qcount, Nat.mul_zero, Nat.add_zero, pow_zero_list, List.append_nil]
    exact .nil _
  | succ s ih =>
    have h1 := finite_suffix ([I, I, I, I] ^ s) (J_consume a)
    have h2 := ih (a + 1)
    have h12 := finite_trans h1 h2
    refine SegRLs.congr h12 ?_ rfl (by norm_word)
      (by rw [show a + 1 + s = a + (s + 1) by omega])
    congr 1
    rw [qcount_S, show a + 1 + 2 = (a + 2) + 1 by omega, pow4_next]
    ring

theorem J_terminal (a : ℕ) :
    SegRLs tm (hf ^ (4 ^ (a + 2) + 3 * 4 ^ (a + 3))) []
      ([O, O, I] ++ d4 ++ e4 ^ a ++ c4 ++ [O, O, I, I] ++ a4 ++ z4 ^ 2)
      ([O, O, I] ++ d4 ++ e4 ^ (a + 3) ++ a4 ++ z4) := by
  have hc1 : SegRLs tm [((A, []), (F, []))] [] (c4 ++ [O, O, I, I])
      (z4 ^ 0 ++ [O] ++ ([O, O, I] ++ a4)) := A_C0011
  have h1 := finite_suffix (a4 ++ z4 ^ 2) (J_to_P a 0 _ _ hc1)
  have hc2 : SegRLs tm [((C, []), (F, []))] [] (b4 ++ a4 ++ a4 ++ z4 ^ 2)
      (z4 ^ 1 ++ (c4 ++ [O, O, O, I] ++ a4 ++ z4)) :=
    SegRLs.congr (segment_suffix [O, O, O, O, O, O, O] C_BAA0) rfl rfl (by norm_word) (by norm_word)
  have h2 := P_to_J a 1 _ _ hc2
  have hc3 : SegRLs tm [((A, []), (F, []))] [] (c4 ++ [O, O, O, I] ++ a4 ++ z4)
      (z4 ^ 0 ++ [O] ++ ([O, O, I, I, I, I, I] ++ a4 ++ z4)) :=
    SegRLs.congr (segment_suffix (a4 ++ z4) A_C0001) rfl rfl (by norm_word) (by norm_word)
  have h3 := J_to_P (a + 1) 0 _ _ hc3
  have hc4 : SegRLs tm [((C, []), (F, []))] [] (b4 ++ [I, I, I, I] ++ a4 ++ z4)
      (z4 ^ 2 ++ (a4 ++ z4)) :=
    SegRLs.congr (segment_suffix (a4 ++ z4) C_B1111) rfl rfl (by norm_word) (by norm_word)
  have h4 := P_to_J (a + 1) 2 _ _ hc4
  have h12 := finite_trans h1 h2
  have h123 := finite_trans h12 h3
  have h1234 := finite_trans h123 h4
    (by rw [show 1 + (a + 1) + 0 = 1 + (a + 1) by omega]; norm_word)
  refine SegRLs.congr h1234 ?_ rfl (by norm_word)
    (by rw [show a + 1 + 2 = a + 3 by omega]; norm_word)
  congr 1
  have := ucount_positive (a + 1)
  have := ucount_power (a + 1)
  have := pow4_next ((a + 1) + 1)
  rw [show 1 + a + 0 = a + 1 by omega,
    show 1 + (a + 1) + 0 = (a + 1) + 1 by omega,
    show a + 1 + 2 = (a + 1) + 2 by omega,
    show a + 2 = (a + 1) + 1 by omega,
    show a + 3 = (a + 1) + 1 + 1 by omega]
  dsimp [vcount, ucount] at *
  omega

def hterminal_count (a s : ℕ) : ℕ :=
  4 ^ (a + 3) + 4 ^ (a + 4) * qcount s + 4 ^ (a + s + 4) + 3 * 4 ^ (a + s + 5)

theorem H_terminal (a s : ℕ) :
    SegRLs tm (hf ^ hterminal_count a s) []
      (hword a 0 ++ [O, O, O] ++ z4 ++ [I, I, I, I] ^ (1 + s) ++ a4 ++ z4 ^ 2)
      ([O, O, I] ++ d4 ++ e4 ^ (a + s + 5) ++ a4 ++ z4) := by
  have hh1 := (H_empty_batch a).concat F_AZ_small
  have h1 := finite_suffix ([I, I, I, I] ^ (1 + s) ++ a4 ++ z4 ^ 2) hh1
  have hc2 : SegRLs tm [((C, []), (F, []))] []
      (b4 ++ a4 ++ [I, I, I, I] ^ (1 + s) ++ a4 ++ z4 ^ 2)
      (z4 ^ 1 ++ (c4 ++ [O, O, I, I] ++ [I, I, I, I] ^ s ++ a4 ++ z4 ^ 2)) :=
    SegRLs.congr (segment_suffix ([I, I, I, I] ^ s ++ a4 ++ z4 ^ 2) C_BAW) rfl rfl
      (by norm_word) (by norm_word)
  have h2 := P_to_J (a + 1) 1 _ _ hc2
  have h3 := finite_suffix (a4 ++ z4 ^ 2) (J_consume_many s (a + 2))
  have h4 := J_terminal (a + s + 2)
  have h12 := finite_trans h1 h2
    (by rw [show 1 + (a + 1) = a + 2 by omega]; norm_word)
  have h123 := finite_trans h12 h3
    (by rw [show a + 1 + 1 = a + 2 by omega]; norm_word)
  have h1234 := finite_trans h123 h4
    (by rw [show a + 2 + s = a + s + 2 by omega]; norm_word)
  refine SegRLs.congr h1234 ?_ rfl (by norm_word)
    (by rw [show a + s + 2 + 3 = a + s + 5 by omega])
  congr 1
  unfold hterminal_count
  have := ucount_positive (a + 2)
  have := ucount_power (a + 2)
  rw [show a + 1 + 1 = a + 2 by omega,
    show a + 2 + 2 = a + 4 by omega,
    show a + s + 2 + 2 = a + s + 4 by omega,
    show a + s + 2 + 3 = a + s + 5 by omega,
    show a + 3 = (a + 2) + 1 by omega]
  dsimp [vcount]
  omega

theorem L_repeat (n k : ℕ) :
    SegRLs tm (hf ^ (4 ^ (k + 2) * qcount n)) []
      ([O, O, O] ++ z4 ^ (k + n + 1) ++ [O])
      ([O, O, O] ++ z4 ^ (k + 1) ++ [O] ++ [O, O, O, I] ^ n) := by
  induction n generalizing k with
  | zero =>
    simp only [qcount, Nat.mul_zero, Nat.add_zero, pow_zero_list, List.append_nil]
    exact .nil _
  | succ n ih =>
    have h1 := ih (k + 1)
    have h2 := finite_suffix ([O, O, O, I] ^ n) (U_prefix_L k)
    have h12 := finite_trans h1 h2 (by rw [show k + 1 + 1 = k + 2 by omega])
    refine SegRLs.congr h12 ?_ rfl
      (by rw [show k + 1 + n + 1 = k + (n + 1) + 1 by omega])
      (by norm_word)
    congr 1
    rw [qcount_S, show k + 1 + 2 = (k + 2) + 1 by omega, pow4_next]
    ring

def first_seek_count (k : ℕ) : ℕ := 2 * 4 ^ (k + 9) + 4 ^ (k + 4) * qcount 6 + 16 * ucount k

theorem first_seek_finite (k : ℕ) :
    SegRLs tm (hf ^ first_seek_count k) []
      ([O, O, O] ++ z4 ^ (k + 10) ++ [O])
      ([O, O, O] ++ z4 ^ 2 ++ a4 ^ (k + 1) ++ z4 ++ a4 ^ 5 ++ [I, I, I, I, I]) := by
  have h1 := U_prefix_M (k + 8)
  have h2 := finite_suffix [I, I, I, I] (L_repeat 6 (k + 2))
  have h3 := finite_suffix (z4 ++ [O, O, O, I] ^ 6 ++ [I, I, I, I]) (U_near_end k)
  have h12 := finite_trans h1 h2 (by rw [show k + 8 + 1 = k + 2 + 6 + 1 by omega]; norm_word)
  have h123 := finite_trans h12 h3 (by rw [show k + 2 + 1 = k + 3 by omega]; norm_word)
  refine SegRLs.congr h123 ?_ rfl
    (by rw [show k + 8 + 2 = k + 10 by omega]) (by norm_word)
  congr 1
  unfold first_seek_count
  rw [near_end_count, show k + 8 + 1 = k + 9 by omega, show k + 2 + 2 = k + 4 by omega]

theorem P_advance (k p : ℕ) :
    SegRLs tm (hf ^ (2 * 4 ^ (k + 3))) []
      ([O, O, I] ++ a4 ^ (1 + k) ++ b4 ++ d4 ++ z4 ^ (2 + p))
      ([O, O, I] ++ a4 ^ (k + 3) ++ b4 ++ d4 ++ z4 ^ p) := by
  have hc1 : SegRLs tm [((C, []), (F, []))] [] (b4 ++ d4 ++ z4 ^ (2 + p))
      (z4 ^ 2 ++ (c4 ++ z4 ^ (1 + p))) :=
    SegRLs.congr (segment_suffix (z4 ^ (1 + p)) C_BDZ) rfl rfl (by norm_word) (by norm_word)
  have h1 := P_to_J k 2 _ _ hc1
  have hc2 : SegRLs tm [((A, []), (F, []))] [] (c4 ++ z4 ^ (1 + p))
      (z4 ^ 0 ++ [O] ++ ([O, O, I] ++ d4 ++ z4 ^ p)) :=
    SegRLs.congr (segment_suffix (z4 ^ p) A_CZ) rfl rfl (by norm_word) (by norm_word)
  have h2 := J_to_P (k + 2) 0 _ _ hc2
  have h12 := finite_trans h1 h2
  refine SegRLs.congr h12 ?_ rfl (by norm_word)
    (by rw [show 1 + (k + 2) + 0 = k + 3 by omega]; norm_word)
  congr 1
  have := ucount_positive (k + 2)
  have := ucount_power (k + 2)
  rw [show 1 + (k + 2) + 0 = (k + 2) + 1 by omega, show k + 3 = (k + 2) + 1 by omega]
  dsimp [vcount, ucount] at *
  omega

def post_count (j : ℕ) : ℕ :=
  4 ^ (j + 3) + 4 ^ (j + 49) + 2731 * 4 ^ (j + 50) + 2 * 4 ^ (j + 51) + 2 * 4 ^ (j + 53)

theorem post_count_components (j : ℕ) :
    (((((4 ^ (j + 3) + (1 + ucount (j + 48))) + (1 + vcount (j + 48))) +
      (1 + ucount (j + 49))) + 2 * 4 ^ (j + 51)) + 2 * 4 ^ (j + 53)) + (1 + vcount (j + 55))
      = post_count j := by
  have hu5 : ucount 5 = 1365 := rfl
  have hsum := ucount_add (j + 49) 5
  rw [show j + 49 + 5 + 1 = j + 55 by omega, show (j + 49) + 1 = j + 50 by omega, hu5] at hsum
  have h48 := ucount_power (j + 48)
  rw [show (j + 48) + 1 = j + 49 by omega] at h48
  have h49 := ucount_power (j + 49)
  rw [show (j + 49) + 1 = j + 50 by omega] at h49
  have := ucount_positive (j + 48)
  have := ucount_positive (j + 55)
  unfold post_count vcount
  omega

theorem post_finite (j : ℕ) :
    SegRLs tm (hf ^ post_count j) [] (post_input j)
      ([O, O, I] ++ d4 ++ e4 ^ (j + 55) ++ b4 ++ [I, I, I]) := by
  have h1 := finite_suffix (a4 ^ 44 ++ z4 ++ a4 ^ 5 ++ [I, I, I, I] ++ b4 ++ [I, I, I])
    (H_advance j 0)
  have h2 := finite_suffix (a4 ^ 5 ++ [I, I, I, I] ++ b4 ++ [I, I, I])
    (H_collapse (j + 2) 44)
  have hc3 : SegRLs tm [((C, []), (F, []))] []
      (b4 ++ a4 ^ 6 ++ [I, I, I, I] ++ b4 ++ [I, I, I])
      (z4 ^ 1 ++ (c4 ++ z4 ^ 5 ++ [O, O, I, I] ++ b4 ++ [I, I, I])) :=
    SegRLs.congr (segment_suffix (b4 ++ [I, I, I]) C_BA6W) rfl rfl (by flat_word) (by flat_word)
  have h3 := P_to_J (j + 47) 1 _ _ hc3
  have hc4 : SegRLs tm [((A, []), (F, []))] []
      (c4 ++ z4 ^ 5 ++ [O, O, I, I] ++ b4 ++ [I, I, I])
      (z4 ^ 0 ++ [O] ++ ([O, O, I] ++ d4 ++ z4 ^ 4 ++ [O, O, I, I] ++ b4 ++ [I, I, I])) :=
    SegRLs.congr (segment_suffix (z4 ^ 4 ++ [O, O, I, I] ++ b4 ++ [I, I, I]) A_CZ)
      rfl rfl (by flat_word) (by flat_word)
  have h4 := J_to_P (j + 48) 0 _ _ hc4
  have h5 := finite_suffix ([O, O, I, I] ++ b4 ++ [I, I, I]) (P_advance (j + 48) 2)
  have h6 := finite_suffix ([O, O, I, I] ++ b4 ++ [I, I, I]) (P_advance (j + 50) 0)
  have hc7 : SegRLs tm [((C, []), (F, []))] []
      (b4 ++ d4 ++ [O, O, I, I] ++ b4 ++ [I, I, I])
      (z4 ^ 3 ++ (b4 ++ [I, I, I])) :=
    SegRLs.congr (segment_suffix (b4 ++ [I, I, I]) C_BD0011) rfl rfl (by flat_word) (by flat_word)
  have h7 := P_to_J (j + 52) 3 _ _ hc7
  have h12 := finite_trans h1 h2 (by flat_word)
  have h123 := finite_trans h12 h3
    (by rw [show j + 2 + 44 + 2 = 1 + (j + 47) by omega]; flat_word)
  have h1234 := finite_trans h123 h4
    (by rw [show j + 47 + 1 = j + 48 by omega])
  have h12345 := finite_trans h1234 h5
    (by rw [show 1 + (j + 48) + 0 = 1 + (j + 48) by omega]; flat_word)
  have h123456 := finite_trans h12345 h6
    (by rw [show j + 48 + 3 = 1 + (j + 50) by omega])
  have h1234567 := finite_trans h123456 h7
    (by rw [show j + 50 + 3 = 1 + (j + 52) by omega]; flat_word)
  refine SegRLs.congr h1234567 ?_ rfl (by flat_word)
    (by rw [show j + 52 + 3 = j + 55 by omega]; flat_word)
  apply congrArg (hf ^ ·)
  rw [show j + 2 + 44 + 2 = j + 48 by omega,
    show j + 47 + 1 = j + 48 by omega,
    show 1 + (j + 48) + 0 = j + 49 by omega,
    show j + 48 + 3 = j + 51 by omega,
    show j + 50 + 3 = j + 53 by omega,
    show j + 52 + 3 = j + 55 by omega]
  exact post_count_components j

theorem prefix_M (k : ℕ) :
    SegRLs tm (hf ^ (2 * 4 ^ (k + 1))) []
      ([O, O, O] ++ z4 ^ (k + 2) ++ [O]) ([O, O, O] ++ z4 ^ (k + 1) ++ [O, I, I, I, I]) :=
  U_prefix_M k

theorem prefix_L (k : ℕ) :
    SegRLs tm (hf ^ (4 ^ (k + 2))) []
      ([O, O, O] ++ z4 ^ (k + 2) ++ [O]) ([O, O, O] ++ z4 ^ (k + 1) ++ [O, O, O, O, I]) :=
  U_prefix_L k

def second_top_count (k : ℕ) : ℕ :=
  2 * 4 ^ (k + 56) + 3 * 4 ^ (k + 55) + 3 * 4 ^ (k + 53) + 3 * 4 ^ (k + 51) + 4 ^ (k + 50)

theorem second_top (k : ℕ) :
    SegRLs tm (hf ^ second_top_count k) []
      ([O, O, O] ++ z4 ^ (k + 57) ++ [O])
      ([O, O, O] ++ z4 ^ (k + 49) ++ [O] ++ second_tail) := by
  have h1 := prefix_M (k + 55)
  have h2 := finite_suffix [I, I, I, I] (prefix_M (k + 54))
  have h3 := finite_suffix ([I, I, I, I] ++ [I, I, I, I]) (prefix_L (k + 53))
  have h4 := finite_suffix ([O, O, O, I] ++ [I, I, I, I] ++ [I, I, I, I]) (prefix_M (k + 52))
  have h5 := finite_suffix ([I, I, I, I] ++ [O, O, O, I] ++ [I, I, I, I] ++ [I, I, I, I])
    (prefix_L (k + 51))
  have h6 := finite_suffix
    ([O, O, O, I] ++ [I, I, I, I] ++ [O, O, O, I] ++ [I, I, I, I] ++ [I, I, I, I])
    (prefix_M (k + 50))
  have h7 := finite_suffix
    ([I, I, I, I] ++ [O, O, O, I] ++ [I, I, I, I] ++ [O, O, O, I] ++ [I, I, I, I] ++ [I, I, I, I])
    (prefix_L (k + 49))
  have h8 := finite_suffix
    ([O, O, O, I] ++ [I, I, I, I] ++ [O, O, O, I] ++ [I, I, I, I] ++
      [O, O, O, I] ++ [I, I, I, I] ++ [I, I, I, I])
    (prefix_L (k + 48))
  have h12 := finite_trans h1 h2 (by rw [show k + 55 + 1 = k + 54 + 2 by omega]; flat_word)
  have h123 := finite_trans h12 h3 (by rw [show k + 54 + 1 = k + 53 + 2 by omega]; flat_word)
  have h1234 := finite_trans h123 h4 (by rw [show k + 53 + 1 = k + 52 + 2 by omega]; flat_word)
  have h12345 := finite_trans h1234 h5 (by rw [show k + 52 + 1 = k + 51 + 2 by omega]; flat_word)
  have h123456 := finite_trans h12345 h6 (by rw [show k + 51 + 1 = k + 50 + 2 by omega]; flat_word)
  have h1234567 :=
      finite_trans h123456 h7 (by rw [show k + 50 + 1 = k + 49 + 2 by omega]; flat_word)
  have h12345678 :=
      finite_trans h1234567 h8 (by rw [show k + 49 + 1 = k + 48 + 2 by omega]; flat_word)
  refine SegRLs.congr h12345678 ?_ rfl
    (by rw [show k + 55 + 2 = k + 57 by omega])
    (by rw [show k + 48 + 1 = k + 49 by omega]; flat_word)
  apply congrArg (hf ^ ·)
  unfold second_top_count
  rw [show k + 55 + 1 = k + 56 by omega,
    show k + 54 + 1 = k + 55 by omega,
    show k + 53 + 2 = k + 55 by omega,
    show k + 52 + 1 = k + 53 by omega,
    show k + 51 + 2 = k + 53 by omega,
    show k + 50 + 1 = k + 51 by omega,
    show k + 49 + 2 = k + 51 by omega,
    show k + 48 + 2 = k + 50 by omega]
  omega

def second_seek_count (k : ℕ) : ℕ := 16 * ucount k + post_count (1 + k)

theorem second_seek_count_sum (k : ℕ) :
    second_top_count k + (4 ^ (k + 4) + 16 * ucount k) = second_seek_count k := by
  unfold second_top_count second_seek_count post_count
  rw [show 1 + k + 3 = k + 4 by omega,
    show 1 + k + 49 = k + 50 by omega,
    show 1 + k + 50 = (k + 50) + 1 by omega,
    show 1 + k + 51 = (k + 50) + 1 + 1 by omega,
    show 1 + k + 53 = (k + 50) + 1 + 1 + 1 + 1 by omega,
    show k + 51 = (k + 50) + 1 by omega,
    show k + 53 = (k + 50) + 1 + 1 + 1 by omega,
    show k + 55 = (k + 50) + 1 + 1 + 1 + 1 + 1 by omega,
    show k + 56 = (k + 50) + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  repeat rw [pow4_next]
  omega

theorem second_tail_join (q : ℕ) :
    [I] ++ z4 ^ q ++ second_tail = a4 ++ z4 ^ q ++ second_result_tail := by
  norm_word

theorem second_seek_finite (k : ℕ) :
    SegRLs tm (hf ^ second_seek_count k) []
      ([O, O, O] ++ z4 ^ (k + 57) ++ [O])
      ([O, O, O] ++ z4 ^ 2 ++ a4 ^ (1 + k) ++ z4 ++ a4 ++ z4 ^ 45 ++ second_result_tail) := by
  have h1 := second_top k
  have h2 := finite_suffix (z4 ^ 45 ++ second_tail) (seek_lower k)
  have hw : [O, O, O] ++ z4 ^ (k + 49) ++ [O] ++ second_tail =
      ([O, O, O] ++ z4 ^ (k + 4) ++ [O]) ++ (z4 ^ 45 ++ second_tail) := by
    have hrec := z4_recut (k + 4) 45
    rw [show k + 49 = (k + 4) + 45 by omega,
      show [O, O, O] ++ z4 ^ ((k + 4) + 45) ++ [O] ++ second_tail =
        [O, O, O] ++ (z4 ^ ((k + 4) + 45) ++ [O]) ++
            second_tail from by simp only [List.append_assoc],
      hrec]
    simp only [List.append_assoc]
  have h12 := finite_trans h1 h2 hw
  refine SegRLs.congr h12 (by rw [second_seek_count_sum]) rfl rfl ?_
  rw [show k + 1 = 1 + k by omega,
    show ([O, O, O] ++ z4 ^ 2 ++ a4 ^ (1 + k) ++ z4 ++ [I]) ++ (z4 ^ 45 ++ second_tail) =
      [O, O, O] ++ z4 ^ 2 ++ a4 ^ (1 + k) ++ z4 ++ ([I] ++ z4 ^ 45 ++ second_tail)
      from by simp only [List.append_assoc],
    second_tail_join 45]
  simp only [List.append_assoc]

theorem first_seek_positive (k : ℕ) : 1 ≤ first_seek_count k := by
  have := ucount_positive k
  unfold first_seek_count
  omega

def second_index (k : ℕ) : ℕ := 15 + 16 * (ucount k - 1) + post_count (1 + k)

theorem second_index_eq (k : ℕ) : second_seek_count k = 1 + second_index k := by
  have := ucount_positive k
  unfold second_seek_count second_index
  omega

def first_index_of (k : ℕ) : ℕ := first_seek_count k - 1

theorem first_index_of_eq (k : ℕ) : first_seek_count k = 1 + first_index_of k := by
  have := first_seek_positive k
  unfold first_index_of
  omega

def first_index : ℕ := first_index_of 43

private theorem entrance_count_eq_gen (k : ℕ) :
    1 + 16 * qcount (k + 1) + hterminal_count (k + 1) 3 = 1 + first_seek_count k := by
  have hq3 : qcount 3 = 21 := rfl
  have hq6 : qcount 6 = 1365 := rfl
  have hqk : qcount (k + 1) = ucount k := rfl
  unfold hterminal_count first_seek_count
  rw [hq3, hq6, hqk,
    show k + 1 + 3 = k + 4 by omega,
    show k + 1 + 4 = (k + 4) + 1 by omega,
    show k + 1 + 3 + 4 = (k + 4) + 4 by omega,
    show k + 1 + 3 + 5 = (k + 4) + 5 by omega,
    show k + 9 = (k + 4) + 5 by omega,
    Nat.pow_add 4 (k + 4) 1,
    Nat.pow_add 4 (k + 4) 4,
    Nat.pow_add 4 (k + 4) 5]
  ring

private theorem entrance_count_eq :
    1 + 16 * qcount 44 + hterminal_count 44 3 = 1 + first_seek_count 43 :=
  entrance_count_eq_gen 43

theorem second_seek_step_eq (k : ℕ) :
    1 + 16 * ucount k + post_count (1 + k) = 1 + second_seek_count k := by
  unfold second_seek_count
  omega

theorem second_reset_recut (m : ℕ) :
    [O, I, I, I, I, O, O] ++ z4 ^ m ++ [O, O, I, I, O, I, I] =
      [O, I, I, I, I] ++ [O, O, O] ++ z4 ^ m ++ [O] ++ [I, I, O, I, I] := by
  norm_word

theorem J_short_reset (n a : ℕ) (r : ListBlank Γ) :
    (Ncfg n (([O, O, I] ++ d4 ++ e4 ^ a ++ b4 ++ [I, I, I]) +> r)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ n ++ [O, I, I, I, I, O, O] ++
        z4 ^ (1 + a) ++ [O, O, I, I, O, I, I]) +> r)) := by
  have hf_seg : SegRLs tm [((F, []), (F, []))] []
      ([O, O, I] ++ d4 ++ e4 ^ a ++ b4 ++ [I, I, I])
      ([O, O, O] ++ z4 ^ (1 + a) ++ [O, O, I, I, O, I, I]) :=
    SegRLs.congr ((J_E a).concat A_B111) rfl rfl (by norm_word) (by norm_word)
  have h := finite_single_side r hf_seg
  have h' : SideRL tm (F, []) (F, [])
      (([O, O, I] ++ d4 ++ e4 ^ a ++ b4 ++ [I, I, I]) +> r)
      ([O, O, O] +> ((z4 ^ (1 + a) ++ [O, O, I, I, O, I, I]) +> r)) := by
    intro l
    simpa only [append_assoc] using h l
  have hn := N_E_reset n _ _ h'
  refine stepPlus_congr hn rfl ?_
  simp only [Ncfg, append_assoc]

theorem post_to_invariant (k : ℕ) (r : ListBlank Γ) :
    (Ncfg (1 + 16 * ucount k) (post_input (1 + k) +> r)) [tm]⊢⁺
      invariant (second_index k) k 43 (entry_tail +> r) := by
  have hf_side := (post_finite (1 + k)).sideRLs_concat (.nil r)
  have hn := N_run (post_count (1 + k)) (1 + 16 * ucount k) _ _ hf_side
  have hr := J_short_reset (1 + second_seek_count k) (1 + k + 55) r
  have hs := (second_seek_finite k).sideRLs_concat (.nil ([I, I, O, I, I] +> r))
  have hl := reset_lift (second_seek_count k) _ _ hs
  have hn' : (Ncfg (1 + 16 * ucount k) (post_input (1 + k) +> r)) [tm]⊢*
      (Ncfg (1 + second_seek_count k) (([O, O, I] ++ d4 ++ e4 ^ (1 + k + 55) ++ b4 ++ [I, I,
          I]) +> r)) := by
    refine stepStar_congr hn rfl ?_
    rw [second_seek_step_eq k]
  have hr' : (Ncfg (1 + second_seek_count k)
      (([O, O, I] ++ d4 ++ e4 ^ (1 + k + 55) ++ b4 ++ [I, I, I]) +> r)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + second_seek_count k) ++ [O, I, I, I, I]) +>
        (([O, O, O] ++ z4 ^ (k + 57) ++ [O]) +> ([I, I, O, I, I] +> r)))) := by
    refine stepPlus_congr hr rfl ?_
    rw [show 1 + (1 + k + 55) = k + 57 by omega]
    apply congrArg (Ncfg 0)
    simp only [← append_assoc]
    apply congrArg (· +> r)
    have hrec := second_reset_recut (k + 57)
    have hlhs : [O, O, O] ++ c4 ^ (1 + second_seek_count k) ++ [O, I, I, I, I, O, O] ++
        z4 ^ (k + 57) ++ [O, O, I, I, O, I, I] =
        [O, O, O] ++ c4 ^ (1 + second_seek_count k) ++
          ([O, I, I, I, I, O, O] ++ z4 ^ (k + 57) ++ [O, O, I, I, O, I, I]) := by
      simp only [List.append_assoc]
    rw [hlhs, hrec]
    simp only [List.append_assoc]
  have hl' : (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + second_seek_count k) ++ [O, I, I, I, I]) +>
        (([O, O, O] ++ z4 ^ (k + 57) ++ [O]) +> ([I, I, O, I, I] +> r)))) [tm]⊢⁺
      invariant (second_index k) k 43 (entry_tail +> r) := by
    refine stepPlus_congr hl rfl ?_
    rw [second_index_eq k, qcount_succ_ucount]
    unfold invariant
    apply congrArg (Ncfg _)
    simp only [← append_assoc]
    apply congrArg (· +> r)
    simp only [second_result_tail, entry_tail, d4, List.append_assoc, List.cons_append,
        List.nil_append]
  exact stepStar_stepPlus_trans hn' (stepPlus_trans hr' hl')

theorem first_reset_to_post_aux (n idx : ℕ) (h_eq : n = 1 + idx)
    (h_seek : SegRLs tm (hf ^ n) []
      ([O, O, O] ++ z4 ^ 53 ++ [O])
      ([O, O, O] ++ z4 ^ 2 ++ a4 ^ 44 ++ z4 ++ a4 ^ 5 ++ [I, I, I, I, I]))
    (r : ListBlank Γ) :
    (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + n) ++ [O, I, I, I, I, O, O] ++
      z4 ^ 54 ++ [I, I, I, I]) +> r)) [tm]⊢⁺
      (Ncfg (1 + 16 * ucount idx) (post_input (1 + idx) +> r)) := by
  have hs := h_seek.sideRLs_concat (.nil ([O, O, I, I, I, I] +> r))
  have hl := reset_lift n _ _ hs
  refine stepPlus_congr hl ?_ ?_
  · apply congrArg (Ncfg 0)
    simp only [← append_assoc]
    apply congrArg (· +> r)
    have hrec := reset_suffix_recut 53 0
    rw [pow_zero_list, List.append_nil, List.append_nil] at hrec
    have hrhs : [O, O, O] ++ c4 ^ (1 + n) ++ [O, I, I, I, I, O, O] ++
        z4 ^ 54 ++ [I, I, I, I] =
        [O, O, O] ++ c4 ^ (1 + n) ++
          ([O, I, I, I, I, O, O] ++ z4 ^ 54 ++ [I, I, I, I]) := by
      simp only [List.append_assoc]
    rw [hrhs, hrec]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [h_eq, qcount_succ_ucount]
    apply congrArg (Ncfg _)
    simp only [← append_assoc]
    apply congrArg (· +> r)
    simp only [post_input, b4, List.append_assoc, List.cons_append, List.nil_append]

theorem first_reset_to_post (r : ListBlank Γ) :
    (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + first_seek_count 43) ++ [O, I, I, I, I, O, O] ++
      z4 ^ 54 ++ [I, I, I, I]) +> r)) [tm]⊢⁺
      (Ncfg (1 + 16 * ucount first_index) (post_input (1 + first_index) +> r)) :=
  first_reset_to_post_aux (first_seek_count 43) first_index (first_index_of_eq 43)
      (first_seek_finite 43) r

-- Symbolic Entrance (`init [] -> first_reset_to_post`)
private abbrev w0 : List Γ := [O, O, O, O, I, I, I, I, O, O, I, I, I, I, I, I, I, I]
private abbrev w45 : List Γ := [O, O, I, I, I, I, O, O, O, I, O, O, O, I, O, I, I, I]

private theorem w0_to_w45_side :
    SideRLs tm (hf ^ 45) (w0 +> default) (w45 +> default) :=
  BoundedConfig.sideRLs_c_spec tm (T := 1000) (by decide)

private theorem reset45_side :
    SideRLs tm [((F, []), (F, []))]
      (w45 +> default)
      (([O, O, O] ++ [O, O] ++ z4 ^ 3 ++ [I, I, I, I] ^ 2) +> default) :=
  BoundedConfig.sideRLs_c_spec tm (T := 1000) (by decide)

private theorem seed_tail_4 :
    SegRLs tm (hf ^ 4) [] (z4 ^ 4 ++ [I, I, I, I] ^ 2 ++ [O, O, O]) seed_tail :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

private theorem seed_tail_counter : SegRLs tm (hf ^ 40) [] seed_tail seed_tail40 :=
  BoundedConfig.segRLs_c_spec tm (T := 100) (by decide)

private theorem seed_tail_44 :
    SegRLs tm (hf ^ 44) [] (z4 ^ 4 ++ [I, I, I, I] ^ 2 ++ [O, O, O]) seed_tail40 :=
  finite_trans seed_tail_4 seed_tail_counter rfl

private theorem init_to_step33935 :
    (init []) [tm]⊢*
      (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + 44) ++ [O, I, I, I, I] ++
        (z4 ^ 4 ++ [I, I, I, I] ^ 2 ++ [O, O, O]) ++ z4 ^ 2) +> default)) := by
  have h1 : (init []) [tm]⊢* (Ncfg 0 (w0 +> default)) := by
    have h := runSteps_spec tm 264
      ⟨List.replicate 13 O, List.replicate 14 O, A, .right⟩
      ⟨z4 ++ [O, I, I, I, I] ++ w0, [], F, .left⟩ (by decide) default default
    have hl : List.replicate 13 O +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    have hr : List.replicate 14 O +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    refine stepStar_congr h ?_ ?_
    · simp only [BoundedConfig.toCfg, hl, hr]; rfl
    · simp only [BoundedConfig.toCfg, Ncfg, pow_zero_list, List.append_nil, append_nil,
        append_assoc]
  have h2 : (Ncfg 0 (w0 +> default)) [tm]⊢* (Ncfg 45 (w45 +> default)) :=
    N_run 45 0 _ _ w0_to_w45_side
  have h3 : (Ncfg 45 (w45 +> default)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + 44) ++ [O, I, I, I, I] ++
        (z4 ^ 4 ++ [I, I, I, I] ^ 2 ++ [O, O, O]) ++ z4 ^ 2) +> default)) := by
    have hs' : SideRL tm (F, []) (F, [])
        (w45 +> default)
        ([O, O, O] +> (([O, O] ++ z4 ^ 3 ++ [I, I, I, I] ^ 2) +> default)) := by
      cases reset45_side with
      | cons hcall hnil =>
        cases hnil
        intro l
        simpa only [append_assoc] using hcall l
    have hn := N_E_reset 45 _ _ hs'
    refine stepPlus_congr hn rfl ?_
    have hd2 : ([O, O, O] ++ z4 ^ 2) +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    have hlhs : Ncfg 0 (([O, O, O] ++ c4 ^ 45 ++ [O, I, I, I, I, O, O]) +>
        (([O, O] ++ z4 ^ 3 ++ [I, I, I, I] ^ 2) +> (default : ListBlank Γ))) =
      Ncfg 0 (([O, O, O] ++ c4 ^ 45 ++ [O, I, I, I, I, O, O]) +>
        (([O, O] ++ z4 ^ 3 ++ [I, I, I, I] ^ 2) +> (([O, O, O] ++ z4 ^ 2) +> default))) := by
      rw [hd2]
    exact hlhs
  exact stepStar_trans h1 (stepStar_trans h2 (stepPlus_to_stepStar h3))

private theorem step33935_to_first_reset :
    (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + 44) ++ [O, I, I, I, I] ++
      (z4 ^ 4 ++ [I, I, I, I] ^ 2 ++ [O, O, O]) ++ z4 ^ 2) +> default)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + first_seek_count 43) ++ [O, I, I, I, I, O, O] ++
        z4 ^ 54 ++ [I, I, I, I]) +> default)) := by
  have hs1 := seed_tail_44.sideRLs_concat (.nil (z4 ^ 2 +> default))
  have hl := reset_lift 44 _ _ hs1
  have hl' : (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + 44) ++ [O, I, I, I, I] ++
      (z4 ^ 4 ++ [I, I, I, I] ^ 2 ++ [O, O, O]) ++ z4 ^ 2) +> default)) [tm]⊢⁺
      (Ncfg (1 + 16 * qcount 44)
        ((hword 44 0 ++ [O, O, O] ++ z4 ++ [I, I, I, I] ^ (1 + 3) ++ a4 ++ z4 ^ 2) +> default)) :=
            by
    refine stepPlus_congr hl ?_ ?_
    · simp only [append_assoc]
    · rfl
  have hs2 := (H_terminal 44 3).sideRLs_concat (.nil default)
  have hrun := N_run (hterminal_count 44 3) (1 + 16 * qcount 44) _ _ hs2
  have hrun' : (Ncfg (1 + 16 * qcount 44)
      ((hword 44 0 ++ [O, O, O] ++ z4 ++ [I, I, I, I] ^ (1 + 3) ++ a4 ++ z4 ^ 2) +> default)) [tm]⊢*
      (Ncfg (1 + first_seek_count 43) (([O, O,
          I] ++ d4 ++ e4 ^ 52 ++ a4 ++ z4 ^ (1 + 0)) +> default)) := by
    refine stepStar_congr hrun rfl ?_
    rw [entrance_count_eq]
    congr 1
  have hreset := J_reset (1 + first_seek_count 43) 52 0 default
  have hreset' : (Ncfg (1 + first_seek_count 43)
      (([O, O, I] ++ d4 ++ e4 ^ 52 ++ a4 ++ z4 ^ (1 + 0)) +> default)) [tm]⊢⁺
      (Ncfg 0 (([O, O, O] ++ c4 ^ (1 + first_seek_count 43) ++ [O, I, I, I, I, O, O] ++
        z4 ^ 54 ++ [I, I, I, I]) +> default)) := by
    refine stepPlus_congr hreset rfl ?_
    apply congrArg (Ncfg _)
    simp only [pow_zero_list, List.append_nil, List.append_assoc]
  exact stepPlus_trans (stepPlus_stepStar_trans hl' hrun') hreset'

end

public section

theorem is_not_halt : IsNotHalt target := by
  have h1 := init_to_step33935
  have h2 := stepPlus_to_stepStar step33935_to_first_reset
  have h3 := stepPlus_to_stepStar (first_reset_to_post default)
  have h4 := stepPlus_to_stepStar (post_to_invariant first_index default)
  have hreach := stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))
  refine IsNotHalt.of_reachesPlus_invariant hreach
    (P := fun c => ∃ x y z t, c = invariant x y z t) ⟨_, _, _, _, rfl⟩ ?_
  rintro _ ⟨x, y, z, t, rfl⟩
  exact ⟨_, invariant_forward x y z t, next_a x y, x, y, _, rfl⟩

end

end BusyBeaver.M_1RB0RA_1RC0RC_1LD1RF_HHH1LE_1RF0LF_1RA0LE
