/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_---0RD` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_---0RD`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_HHH0RD

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_---0RD`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 3, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

open BusyBeaver.Longitudinal.BoundedConfig (BCfg toCfg step_r0inf step_r0inf_spec
  steps_spec steps1_spec_true all0_spec eqAppR0inf eqAppR0inf_spec)

lemma neverHaltsFrom_of_reachesStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢* c₂) (h₂ : NeverHaltsFrom target_tm c₂) :
    NeverHaltsFrom target_tm c₁ := by
  obtain ⟨k₀, hk₀⟩ := h₁
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step target_tm cfg with _ | _
    · have hnone : (step target_tm cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep target_tm c₁ k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, multiStep_add, hk₀, Option.bind_some] at hk
    exact h₂ cfg ⟨k - k₀, hk⟩

lemma B_ones (M : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{B}}> (([1] : List (Fin 2)) ^ M +> r)) [target_tm]⊢*
      ((([1] : List (Fin 2)) ^ M +> l) {{B}}> r) := by
  induction M generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ M ih =>
    have h₁ := steps_spec target_tm 5 ⟨[], [1], B, .right⟩
      (x' := ⟨[1], [], B, .right⟩) (by decide) l (([1] : List (Fin 2)) ^ M +> r)
    dsimp only [toCfg, ListBlank.append_nil] at h₁
    rw [pow_succ_list, ListBlank.append_assoc]
    refine stepStar_trans h₁ ?_
    have h₂ := ih ([1] +> l)
    rwa [ListBlank.append_pow_comm ([1] : List (Fin 2)) M l] at h₂

lemma back_pairs (M : ℕ) (l r : ListBlank (Fin 2)) :
    ((([1, 1] : List (Fin 2)) ^ M +> l) <{{D}} ([0] +> r)) [target_tm]⊢*
      (l <{{D}} ([0] +> (([0, 1] : List (Fin 2)) ^ M +> r))) := by
  induction M generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ M ih =>
    have h₁ := steps_spec target_tm 10 ⟨[0], [1, 1], D, .left⟩
      (x' := ⟨[0, 0, 1], [], D, .left⟩) (by decide)
      (([1, 1] : List (Fin 2)) ^ M +> l) r
    dsimp only [toCfg, ListBlank.append_nil] at h₁
    have h_lhs : ([1, 1] : List (Fin 2)) ^ (M + 1) +> l =
        [1, 1] +> (([1, 1] : List (Fin 2)) ^ M +> l) := by
      rw [pow_succ_list, ListBlank.append_assoc]
    have h_mid : ([0, 0, 1] : List (Fin 2)) +> r = [0] +> ([0, 1] +> r) := rfl
    rw [h_lhs]
    rw [h_mid] at h₁
    refine stepStar_trans h₁ ?_
    have h₂ := ih ([0, 1] +> r)
    rwa [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) M r] at h₂

lemma cross_pairs (M : ℕ) (l r : ListBlank (Fin 2)) :
    (([1, 0, 0, 1] +> l) {{B}}> (([0, 1] : List (Fin 2)) ^ M +> r)) [target_tm]⊢*
      (([1, 0, 0, 1] +> (([1, 1] : List (Fin 2)) ^ M +> l)) {{B}}> r) := by
  induction M generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ M ih =>
    have h₁ := steps_spec target_tm 20 ⟨[1, 0, 0, 1], [0, 1], B, .right⟩
      (x' := ⟨[1, 0, 0, 1, 1, 1], [], B, .right⟩) (by decide)
      l (([0, 1] : List (Fin 2)) ^ M +> r)
    dsimp only [toCfg, ListBlank.append_nil] at h₁
    have h_rhs : ([1, 0, 0, 1, 1, 1] : List (Fin 2)) +> l =
        [1, 0, 0, 1] +> ([1, 1] +> l) := rfl
    rw [pow_succ_list, ListBlank.append_assoc]
    rw [h_rhs] at h₁
    refine stepStar_trans h₁ ?_
    have h₂ := ih ([1, 1] +> l)
    rwa [ListBlank.append_pow_comm ([1, 1] : List (Fin 2)) M l] at h₂

lemma recharge_pairs (M : ℕ) (l r : ListBlank (Fin 2)) :
    (([1, 1, 0, 0, 1] +> l) {{B}}> (([0, 1] : List (Fin 2)) ^ M +> r)) [target_tm]⊢*
      (([1, 1, 0, 0, 1] +> (([0, 0] : List (Fin 2)) ^ M +> l)) {{B}}> r) := by
  induction M generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ M ih =>
    have h₁ := steps_spec target_tm 20 ⟨[1, 1, 0, 0, 1], [0, 1], B, .right⟩
      (x' := ⟨[1, 1, 0, 0, 1, 0, 0], [], B, .right⟩) (by decide)
      l (([0, 1] : List (Fin 2)) ^ M +> r)
    dsimp only [toCfg, ListBlank.append_nil] at h₁
    have h_rhs : ([1, 1, 0, 0, 1, 0, 0] : List (Fin 2)) +> l =
        [1, 1, 0, 0, 1] +> ([0, 0] +> l) := rfl
    rw [pow_succ_list, ListBlank.append_assoc]
    rw [h_rhs] at h₁
    refine stepStar_trans h₁ ?_
    have h₂ := ih ([0, 0] +> l)
    rwa [ListBlank.append_pow_comm ([0, 0] : List (Fin 2)) M l] at h₂

lemma cross_raw (N : ℕ) (l r : ListBlank (Fin 2)) :
    (([0, 0] +> l) <{{D}} ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +> r))) [target_tm]⊢*
      (([1, 0, 0, 1] +> (([1, 1] : List (Fin 2)) ^ N +> ([1] +> l))) {{B}}> r) := by
  have h₁ := steps_spec target_tm 20 ⟨[0, 1, 1], [0, 0], D, .left⟩
    (x' := ⟨[1, 0, 0, 1, 1], [], B, .right⟩) (by decide)
    l (([0, 1] : List (Fin 2)) ^ N +> r)
  dsimp only [toCfg, ListBlank.append_nil] at h₁
  have h_mid : ([1, 0, 0, 1, 1] : List (Fin 2)) +> l = [1, 0, 0, 1] +> ([1] +> l) := rfl
  rw [h_mid] at h₁
  exact stepStar_trans h₁ (cross_pairs N ([1] +> l) r)

lemma back_raw (N : ℕ) (l r : ListBlank (Fin 2)) :
    ((([1, 1] : List (Fin 2)) ^ N +> ([1, 0, 0] +> l)) <{{D}} ([0, 0, 1] +> r)) [target_tm]⊢*
      (([0] +> l) <{{D}} ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ (N + 1) +> r))) := by
  have h_lhs : ([0, 0, 1] : List (Fin 2)) +> r = [0] +> ([0, 1] +> r) := rfl
  rw [h_lhs]
  refine stepStar_trans (back_pairs N ([1, 0, 0] +> l) ([0, 1] +> r)) ?_
  have h₂ := steps_spec target_tm 20 ⟨[0, 0, 1], [1, 0], D, .left⟩
    (x' := ⟨[0, 1, 1, 0, 1], [], D, .left⟩) (by decide)
    ([0] +> l) (([0, 1] : List (Fin 2)) ^ N +> r)
  dsimp only [toCfg, ListBlank.append_nil] at h₂
  have h_mid : ([0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) ^ N +> ([0, 1] +> r)) =
      [0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ N +> r) := by
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) N r]
    rfl
  have h_l : ([1, 0] : List (Fin 2)) +> ([0] +> l) = [1, 0, 0] +> l := rfl
  have h_rhs : ([0, 1, 1, 0, 1] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) ^ N +> r) =
      [0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ (N + 1) +> r) := by
    rw [pow_succ_list, ListBlank.append_assoc]
    rfl
  rw [h_l, h_rhs] at h₂
  rwa [h_mid]

lemma bounce_pairs (k : ℕ) (L r : ListBlank (Fin 2)) :
    (([1] +> L) {{B}}> (([1, 1] : List (Fin 2)) ^ k +> ([0] +> r))) [target_tm]⊢*
      (L <{{D}} ([0] +> (([0, 1] : List (Fin 2)) ^ k +> ([1] +> r)))) := by
  have h₁ := B_ones (2 * k) ([1] +> L) ([0] +> r)
  rw [← one_pow_two_mul k] at h₁
  rw [swap_1_11_pow k L] at h₁
  have h₂ := steps_spec target_tm 10 ⟨[1], [0], B, .right⟩
    (x' := ⟨[0, 1], [], D, .left⟩) (by decide)
    (([1, 1] : List (Fin 2)) ^ k +> L) r
  dsimp only [toCfg, ListBlank.append_nil] at h₂
  have h_mid : ([0, 1] : List (Fin 2)) +> r = [0] +> ([1] +> r) := rfl
  rw [h_mid] at h₂
  exact stepStar_trans h₁ (stepStar_trans h₂ (back_pairs k L ([1] +> r)))

lemma R1_raw (l r : ListBlank (Fin 2)) (N a : ℕ) :
    (([0, 0, 0, 0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +>
        ([0, 1, 1, 1, 1, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ a +> ([0] +> r))))))
      [target_tm]⊢*
    (([0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ (N + 2) +>
        ([0, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ a +> ([0, 1, 1] +> r)))))) := by
  let L : ListBlank (Fin 2) := ([1, 1] : List (Fin 2)) ^ N +> ([1, 0, 0] +> l)
  have h₁ : (([0, 0, 0, 0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +>
        ([0, 1, 1, 1, 1, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ a +> ([0] +> r))))))
      [target_tm]⊢*
      (([1, 0, 0, 1] +> L) {{B}}>
        ([0, 1, 1, 1, 1, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ a +> ([0] +> r)))) :=
    cross_raw N ([0, 0] +> l)
      ([0, 1, 1, 1, 1, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ a +> ([0] +> r)))
  have h₂ := steps_spec target_tm 50 ⟨[1, 0, 0, 1], [0, 1, 1, 1, 1, 1, 1, 1], B, .right⟩
    (x' := ⟨[1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], [], B, .right⟩) (by decide)
    L (([1, 1] : List (Fin 2)) ^ a +> ([0] +> r))
  dsimp only [toCfg, ListBlank.append_nil] at h₂
  have h₂_rhs : ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] : List (Fin 2)) +> L =
      [1] +> ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] +> L) := rfl
  rw [h₂_rhs] at h₂
  have h₃ := bounce_pairs a ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1] +> L) r
  have h₄ := steps_spec target_tm 200 ⟨[0], [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], D, .left⟩
    (x' := ⟨[0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1], [], D, .left⟩) (by decide)
    L (([0, 1] : List (Fin 2)) ^ a +> ([1] +> r))
  dsimp only [toCfg, ListBlank.append_nil] at h₄
  have h₄_rhs : ([0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1] : List (Fin 2)) +>
      (([0, 1] : List (Fin 2)) ^ a +> ([1] +> r)) =
      [0, 0, 1] +> ([0, 1] +> ([0, 1, 1, 1, 1] +>
        (([0, 1] : List (Fin 2)) ^ a +> ([0, 1, 1] +> r)))) := by
    have h_comm := (ListBlank.append_pow_comm ([0, 1] : List (Fin 2)) a ([1] +> r)).symm
    change [0, 0, 1, 0, 1, 0, 1, 1, 1, 1] +> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ a +> ([1] +> r))) = _
    rw [h_comm]
    rfl
  rw [h₄_rhs] at h₄
  have h₅ := back_raw N l
    ([0, 1] +> ([0, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ a +> ([0, 1, 1] +> r))))
  have h₅_rhs : ([0, 1] : List (Fin 2)) ^ (N + 1) +>
      ([0, 1] +> ([0, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ a +> ([0, 1, 1] +> r)))) =
      ([0, 1] : List (Fin 2)) ^ (N + 2) +>
        ([0, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ a +> ([0, 1, 1] +> r))) := by
    exact ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (N + 1) _
  rw [h₅_rhs] at h₅
  exact stepStar_trans h₁ (stepStar_trans h₂ (stepStar_trans h₃ (stepStar_trans h₄ h₅)))

lemma R2_raw (l r : ListBlank (Fin 2)) (N : ℕ) :
    (([0, 0, 0, 0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +> ([0, 1, 1, 1, 1, 0, 1, 0] +> r))))
      [target_tm]⊢*
    (([0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ (N + 1) +> ([0, 1, 1, 1, 1, 1, 1, 1, 1] +> r)))) := by
  let L : ListBlank (Fin 2) := ([1, 1] : List (Fin 2)) ^ N +> ([1, 0, 0] +> l)
  have h₁ : (([0, 0, 0, 0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +> ([0, 1, 1, 1, 1, 0, 1, 0] +> r))))
      [target_tm]⊢*
      (([1, 0, 0, 1] +> L) {{B}}> ([0, 1, 1, 1, 1, 0, 1, 0] +> r)) :=
    cross_raw N ([0, 0] +> l) ([0, 1, 1, 1, 1, 0, 1, 0] +> r)
  have h₂ := steps_spec target_tm 200 ⟨[1, 0, 0, 1], [0, 1, 1, 1, 1, 0, 1, 0], B, .right⟩
    (x' := ⟨[0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], [], D, .left⟩) (by decide) L r
  dsimp only [toCfg, ListBlank.append_nil] at h₂
  have h₂_rhs : ([0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1] : List (Fin 2)) +> r =
      [0, 0, 1] +> ([0, 1, 1, 1, 1, 1, 1, 1, 1] +> r) := rfl
  rw [h₂_rhs] at h₂
  have h₃ := back_raw N l ([0, 1, 1, 1, 1, 1, 1, 1, 1] +> r)
  exact stepStar_trans h₁ (stepStar_trans h₂ h₃)

lemma RB_raw (l r : ListBlank (Fin 2)) (N b : ℕ) :
    (([0, 0, 0, 0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +>
        ([0, 1, 1, 1, 1, 0, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ b +> ([0] +> r))))))
      [target_tm]⊢*
    (([0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ (N + 1) +>
        ([0, 1, 1, 1, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ b +> ([0, 1, 1] +> r)))))) := by
  let L : ListBlank (Fin 2) := ([1, 1] : List (Fin 2)) ^ N +> ([1, 0, 0] +> l)
  have h₁ : (([0, 0, 0, 0] +> l) <{{D}}
      ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +>
        ([0, 1, 1, 1, 1, 0, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ b +> ([0] +> r))))))
      [target_tm]⊢*
      (([1, 0, 0, 1] +> L) {{B}}>
        ([0, 1, 1, 1, 1, 0, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ b +> ([0] +> r)))) :=
    cross_raw N ([0, 0] +> l)
      ([0, 1, 1, 1, 1, 0, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ b +> ([0] +> r)))
  have h₂ := steps_spec target_tm 200 ⟨[1, 0, 0, 1], [0, 1, 1, 1, 1, 0, 1, 1, 1], B, .right⟩
    (x' := ⟨[1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1], [], B, .right⟩) (by decide)
    L (([1, 1] : List (Fin 2)) ^ b +> ([0] +> r))
  dsimp only [toCfg, ListBlank.append_nil] at h₂
  have h₂_rhs : ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1] : List (Fin 2)) +> L =
      [1] +> ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1] +> L) := rfl
  rw [h₂_rhs] at h₂
  have h₃ := bounce_pairs b ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1] +> L) r
  have h₄ := steps_spec target_tm 200 ⟨[0], [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1], D, .left⟩
    (x' := ⟨[0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1], [], D, .left⟩) (by decide)
    L (([0, 1] : List (Fin 2)) ^ b +> ([1] +> r))
  dsimp only [toCfg, ListBlank.append_nil] at h₄
  have h₄_rhs : ([0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1] : List (Fin 2)) +>
      (([0, 1] : List (Fin 2)) ^ b +> ([1] +> r)) =
      [0, 0, 1] +> ([0, 1, 1, 1, 1, 1, 1, 1] +>
        (([0, 1] : List (Fin 2)) ^ b +> ([0, 1, 1] +> r))) := by
    have h_comm := (ListBlank.append_pow_comm ([0, 1] : List (Fin 2)) b ([1] +> r)).symm
    change [0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1] +> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ b +> ([1] +> r))) = _
    rw [h_comm]
    rfl
  rw [h₄_rhs] at h₄
  have h₅ := back_raw N l
    ([0, 1, 1, 1, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ b +> ([0, 1, 1] +> r)))
  exact stepStar_trans h₁ (stepStar_trans h₂ (stepStar_trans h₃ (stepStar_trans h₄ h₅)))

def reg : List ℕ → List (Fin 2)
  | [] => []
  | z :: t => 0 :: (([1] : List (Fin 2)) ^ z ++ reg t)

def recCfg (N : ℕ) (zs : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  default <{{D}} ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +> (reg zs +> default)))

lemma reg_ones (a : ℕ) (zs : List ℕ) :
    reg (List.replicate a 1 ++ zs) = ([0, 1] : List (Fin 2)) ^ a ++ reg zs := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append, reg, pow_succ_list, pow_zero_list,
      List.nil_append, ih]

lemma pow_one_add_7 (a : ℕ) :
    ([1] : List (Fin 2)) ^ (a * 2 + 7) =
      [1, 1, 1, 1, 1, 1, 1] ++ ([1, 1] : List (Fin 2)) ^ a := by
  have h : a * 2 + 7 = 7 + 2 * a := by omega
  rw [h, list_pow_add, ← one_pow_two_mul]
  rfl

lemma pow_one_add_3 (b : ℕ) :
    ([1] : List (Fin 2)) ^ (b * 2 + 3) =
      [1, 1, 1] ++ ([1, 1] : List (Fin 2)) ^ b := by
  have h : b * 2 + 3 = 3 + 2 * b := by omega
  rw [h, list_pow_add, ← one_pow_two_mul]
  rfl

lemma pow_one_add_2 (e : ℕ) :
    ([1] : List (Fin 2)) ^ (e + 2) = [1, 1] ++ ([1] : List (Fin 2)) ^ e := by
  have h : e + 2 = 2 + e := by omega
  rw [h, list_pow_add]
  rfl

lemma pow_one_add_8 (y : ℕ) :
    ([1] : List (Fin 2)) ^ (y + 8) = [1, 1, 1, 1, 1, 1, 1, 1] ++ ([1] : List (Fin 2)) ^ y := by
  have h : y + 8 = 8 + y := by omega
  rw [h, list_pow_add]
  rfl

lemma R1 (N a e : ℕ) (zs : List ℕ) :
    (recCfg (N + 8) ((a * 2 + 7) :: e :: zs)) [target_tm]⊢*
      (recCfg (N + 2 + 8) (4 :: (List.replicate a 1 ++ (e + 2) :: zs))) := by
  have h := R1_raw default ((([1] : List (Fin 2)) ^ e ++ reg zs) +> default) (N + 8) a
  have h_l4 : ([0, 0, 0, 0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_l1 : ([0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_r1 : reg ((a * 2 + 7) :: e :: zs) +> default =
      [0, 1, 1, 1, 1, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ a +>
        ([0] +> ((([1] : List (Fin 2)) ^ e ++ reg zs) +> default))) := by
    dsimp only [reg]
    rw [pow_one_add_7 a]
    simp only [pow_succ_list, pow_zero_list, List.nil_append, List.cons_append, List.append_assoc,
      ListBlank.append_nil, ListBlank.append_cons, ListBlank.append_assoc]
  have h_r2 : reg (4 :: (List.replicate a 1 ++ (e + 2) :: zs)) +> default =
      [0, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ a +>
        ([0, 1, 1] +> ((([1] : List (Fin 2)) ^ e ++ reg zs) +> default))) := by
    dsimp only [reg]
    rw [reg_ones a ((e + 2) :: zs)]
    dsimp only [reg]
    rw [pow_one_add_2 e]
    simp only [pow_succ_list, pow_zero_list, List.nil_append, List.cons_append, List.append_assoc,
      ListBlank.append_nil, ListBlank.append_cons, ListBlank.append_assoc]
  have hN : N + 8 + 2 = N + 2 + 8 := by omega
  unfold recCfg
  rw [h_r1, h_r2, ← hN]
  rwa [h_l4, h_l1] at h

lemma R2 (N y : ℕ) (zs : List ℕ) :
    (recCfg (N + 8) (4 :: 1 :: y :: zs)) [target_tm]⊢*
      (recCfg (N + 1 + 8) ((y + 8) :: zs)) := by
  have h := R2_raw default ((([1] : List (Fin 2)) ^ y ++ reg zs) +> default) (N + 8)
  have h_l4 : ([0, 0, 0, 0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_l1 : ([0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_r1 : reg (4 :: 1 :: y :: zs) +> default =
      [0, 1, 1, 1, 1, 0, 1, 0] +> ((([1] : List (Fin 2)) ^ y ++ reg zs) +> default) := rfl
  have h_r2 : reg ((y + 8) :: zs) +> default =
      [0, 1, 1, 1, 1, 1, 1, 1, 1] +> ((([1] : List (Fin 2)) ^ y ++ reg zs) +> default) := by
    dsimp only [reg]
    rw [pow_one_add_8 y]
    simp only [pow_succ_list, pow_zero_list, List.nil_append, List.cons_append, List.append_assoc,
      ListBlank.append_nil, ListBlank.append_cons, ListBlank.append_assoc]
  have hN : N + 8 + 1 = N + 1 + 8 := by omega
  unfold recCfg
  rw [h_r1, h_r2, ← hN]
  rwa [h_l4, h_l1] at h

lemma RB (N b y : ℕ) (zs : List ℕ) :
    (recCfg (N + 8) (4 :: (b * 2 + 3) :: y :: zs)) [target_tm]⊢*
      (recCfg (N + 1 + 8) (7 :: (List.replicate b 1 ++ (y + 2) :: zs))) := by
  have h := RB_raw default ((([1] : List (Fin 2)) ^ y ++ reg zs) +> default) (N + 8) b
  have h_l4 : ([0, 0, 0, 0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_l1 : ([0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_r1 : reg (4 :: (b * 2 + 3) :: y :: zs) +> default =
      [0, 1, 1, 1, 1, 0, 1, 1, 1] +> (([1, 1] : List (Fin 2)) ^ b +>
        ([0] +> ((([1] : List (Fin 2)) ^ y ++ reg zs) +> default))) := by
    dsimp only [reg]
    rw [pow_one_add_3 b]
    simp only [pow_succ_list, pow_zero_list, List.nil_append, List.cons_append, List.append_assoc,
      ListBlank.append_nil, ListBlank.append_cons, ListBlank.append_assoc]
  have h_r2 : reg (7 :: (List.replicate b 1 ++ (y + 2) :: zs)) +> default =
      [0, 1, 1, 1, 1, 1, 1, 1] +> (([0, 1] : List (Fin 2)) ^ b +>
        ([0, 1, 1] +> ((([1] : List (Fin 2)) ^ y ++ reg zs) +> default))) := by
    dsimp only [reg]
    rw [reg_ones b ((y + 2) :: zs)]
    dsimp only [reg]
    rw [pow_one_add_2 y]
    simp only [pow_succ_list, pow_zero_list, List.nil_append, List.cons_append, List.append_assoc,
      ListBlank.append_nil, ListBlank.append_cons, ListBlank.append_assoc]
  have hN : N + 8 + 1 = N + 1 + 8 := by omega
  unfold recCfg
  rw [h_r1, h_r2, ← hN]
  rwa [h_l4, h_l1] at h

def NH (zs : List ℕ) : Prop :=
  ∀ N : ℕ, NeverHaltsFrom target_tm (recCfg (N + 8) zs)

lemma NH_rule {zs zs' : List ℕ} (k : ℕ)
    (h : ∀ N, (recCfg (N + 8) zs) [target_tm]⊢* (recCfg (N + k + 8) zs'))
    (h' : NH zs') : NH zs := by
  intro N
  exact neverHaltsFrom_of_reachesStar (h N) (h' (N + k))

def PI (a : ℕ) : Prop :=
  ∀ y zs, NH ((a * 2 + 10 + y) :: zs) → NH ((a * 2 + 9) :: y :: zs)

def QI (a : ℕ) : Prop :=
  ∀ y zs, NH ((a * 2 + 10 + y) :: zs) → NH (9 :: (List.replicate a 1 ++ y :: zs))

lemma PI_zero : PI 0 := by
  intro y zs h
  have h₁ : 0 * 2 + 9 = 1 * 2 + 7 := rfl
  rw [h₁]
  refine NH_rule 2 (fun N => R1 N 1 y zs) ?_
  dsimp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
  refine NH_rule 1 (fun N => R2 N (y + 2) zs) ?_
  have h₂ : y + 2 + 8 = 0 * 2 + 10 + y := by omega
  rwa [h₂]

lemma PI_succ (a : ℕ) (hQ : QI a) : PI (a + 1) := by
  intro y zs h
  have h₁ : (a + 1) * 2 + 9 = (a + 2) * 2 + 7 := by omega
  rw [h₁]
  refine NH_rule 2 (fun N => R1 N (a + 2) y zs) ?_
  dsimp only [List.replicate_succ, List.cons_append]
  refine NH_rule 1 (fun N => R2 N 1 (List.replicate a 1 ++ (y + 2) :: zs)) ?_
  refine hQ (y + 2) zs ?_
  have h₂ : a * 2 + 10 + (y + 2) = (a + 1) * 2 + 10 + y := by omega
  rwa [h₂]

lemma classI_QI (a : ℕ) : QI a ∧ PI a := by
  induction a with
  | zero => exact ⟨PI_zero, PI_zero⟩
  | succ a ih =>
    have hPI : PI (a + 1) := PI_succ a ih.1
    refine ⟨?_, hPI⟩
    intro y zs h
    rw [List.replicate_succ', List.append_assoc]
    refine ih.1 1 (y :: zs) ?_
    have h₁ : a * 2 + 10 + 1 = (a + 1) * 2 + 9 := by omega
    rw [h₁]
    exact hPI y zs h

lemma classI (a : ℕ) : PI a := (classI_QI a).2

def PII (b : ℕ) : Prop :=
  ∀ y zs, NH (7 :: (b * 2 + 2 + y) :: zs) → NH (7 :: (b * 2 + 1) :: y :: zs)

def QII (b : ℕ) : Prop :=
  ∀ y zs, NH (7 :: (b * 2 + 2 + y) :: zs) → NH (7 :: 1 :: (List.replicate b 1 ++ y :: zs))

lemma PII_zero : PII 0 := by
  intro y zs h
  have h₁ : (7 : ℕ) = 0 * 2 + 7 := rfl
  rw [h₁]
  refine NH_rule 2 (fun N => R1 N 0 1 (y :: zs)) ?_
  dsimp only [List.replicate_zero, List.nil_append]
  refine NH_rule 1 (fun N => RB N 0 y zs) ?_
  dsimp only [List.replicate_zero, List.nil_append]
  have h₂ : y + 2 = 0 * 2 + 2 + y := by omega
  rwa [h₂]

lemma PII_succ (b : ℕ) (hQ : QII b) : PII (b + 1) := by
  intro y zs h
  have h₁ : (7 : ℕ) = 0 * 2 + 7 := rfl
  rw [h₁]
  refine NH_rule 2 (fun N => R1 N 0 ((b + 1) * 2 + 1) (y :: zs)) ?_
  dsimp only [List.replicate_zero, List.nil_append]
  refine NH_rule 1 (fun N => RB N (b + 1) y zs) ?_
  dsimp only [List.replicate_succ, List.cons_append]
  refine hQ (y + 2) zs ?_
  have h₃ : b * 2 + 2 + (y + 2) = (b + 1) * 2 + 2 + y := by omega
  rwa [h₃]

lemma classII_QII (b : ℕ) : QII b ∧ PII b := by
  induction b with
  | zero => exact ⟨PII_zero, PII_zero⟩
  | succ b ih =>
    have hPII : PII (b + 1) := PII_succ b ih.1
    refine ⟨?_, hPII⟩
    intro y zs h
    rw [List.replicate_succ', List.append_assoc]
    refine ih.1 1 (y :: zs) ?_
    have h₁ : b * 2 + 2 + 1 = (b + 1) * 2 + 1 := by omega
    rw [h₁]
    exact hPII y zs h

lemma classII (b : ℕ) : PII b := (classII_QII b).2

lemma RB_QII (b y : ℕ) (zs : List ℕ) (h : NH (7 :: (b * 2 + 2 + y) :: zs)) :
    NH (4 :: (b * 2 + 3) :: y :: zs) := by
  rcases b with _ | b
  · refine NH_rule 1 (fun N => RB N 0 y zs) ?_
    dsimp only [List.replicate_zero, List.nil_append]
    have h₂ : y + 2 = 0 * 2 + 2 + y := by omega
    rwa [h₂]
  · refine NH_rule 1 (fun N => RB N (b + 1) y zs) ?_
    dsimp only [List.replicate_succ, List.cons_append]
    refine (classII_QII b).1 (y + 2) zs ?_
    have h₃ : b * 2 + 2 + (y + 2) = (b + 1) * 2 + 2 + y := by omega
    rwa [h₃]

def countLead1 : List ℕ → ℕ → ℕ
  | [], d => d
  | x :: t, d => if x == 1 then countLead1 t (d + 1) else d

def dropLead1 : List ℕ → List ℕ
  | [] => []
  | x :: t => if x == 1 then dropLead1 t else x :: t

lemma classI_run (t : List ℕ) (a : ℕ) :
    match dropLead1 t with
    | y :: zs => NH ((countLead1 t a * 2 + 10 + y) :: zs) → NH ((a * 2 + 9) :: t)
    | [] => True := by
  induction t generalizing a with
  | nil => trivial
  | cons x xs ih =>
    dsimp only [dropLead1, countLead1]
    split_ifs with hx
    · rw [beq_iff_eq] at hx
      subst hx
      have ih_step := ih (a + 1)
      rcases hd : dropLead1 xs with _ | ⟨y, zs⟩
      · rw [hd] at ih_step; trivial
      · rw [hd] at ih_step
        intro h
        have h_eq : a * 2 + 10 + 1 = (a + 1) * 2 + 9 := by omega
        refine classI a 1 xs ?_
        rw [h_eq]
        exact ih_step h
    · exact classI a x xs

def mstep (zs : List ℕ) : Option (List ℕ) :=
  match zs with
  | X :: t =>
    if X == (X - 9) / 2 * 2 + 9 then
      match dropLead1 t with
      | y :: zs' => some ((countLead1 t ((X - 9) / 2) * 2 + 10 + y) :: zs')
      | [] => none
    else if X == 7 then
      match t with
      | y :: y' :: t' =>
        if y == y / 2 * 2 + 1 then
          some (7 :: (y / 2 * 2 + 2 + y') :: t')
        else
          some (4 :: (y + 2) :: y' :: t')
      | [y] => some (4 :: (y + 2) :: [])
      | [] => none
    else if X == 4 then
      match t with
      | y :: y' :: t' =>
        if y == 1 then
          some ((y' + 8) :: t')
        else if y == (y - 3) / 2 * 2 + 3 then
          some (7 :: ((y - 3) / 2 * 2 + 2 + y') :: t')
        else
          none
      | _ => none
    else
      none
  | [] => none

lemma mstep_spec (zs zs' : List ℕ) (h : mstep zs = some zs') (h' : NH zs') : NH zs := by
  rcases zs with _ | ⟨X, t⟩
  · cases h
  · dsimp only [mstep] at h
    split_ifs at h with hX9 hX7 hX4
    · have hrun := classI_run t ((X - 9) / 2)
      rcases hd : dropLead1 t with _ | ⟨y, t_rem⟩
      · rw [hd] at h; cases h
      · rw [hd] at h hrun
        cases h
        rw [beq_iff_eq] at hX9
        rw [hX9]
        exact hrun h'
    · rcases t with _ | ⟨y, _ | ⟨y', t'⟩⟩
      · cases h
      · cases h
        rw [beq_iff_eq] at hX7
        rw [hX7]
        have h_r1 := fun N => R1 N 0 y []
        dsimp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append] at h_r1
        exact NH_rule 2 h_r1 h'
      · dsimp only at h
        split_ifs at h with hy_odd
        · cases h
          rw [beq_iff_eq] at hX7 hy_odd
          rw [hX7, hy_odd]
          exact classII (y / 2) y' t' h'
        · cases h
          rw [beq_iff_eq] at hX7
          rw [hX7]
          have h_r1 := fun N => R1 N 0 y (y' :: t')
          dsimp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append] at h_r1
          exact NH_rule 2 h_r1 h'
    · rcases t with _ | ⟨y, _ | ⟨y', t'⟩⟩
      · cases h
      · cases h
      · dsimp only at h
        split_ifs at h with hy1 hy3
        · cases h
          rw [beq_iff_eq] at hX4 hy1
          rw [hX4, hy1]
          exact NH_rule 1 (fun N => R2 N y' t') h'
        · cases h
          rw [beq_iff_eq] at hX4 hy3
          rw [hX4, hy3]
          exact RB_QII ((y - 3) / 2) y' t' h'

def stripPfx : List (Fin 2) → List (Fin 2) → Option (List (Fin 2))
  | [], ys => some ys
  | x :: xs, y :: ys => if x == y then stripPfx xs ys else none
  | _ :: _, [] => none

lemma stripPfx_spec {p ys r : List (Fin 2)} (h : stripPfx p ys = some r) :
    ys = p ++ r := by
  induction p generalizing ys with
  | nil => cases h; rfl
  | cons x xs ih =>
    rcases ys with _ | ⟨y, ys⟩
    · cases h
    · dsimp only [stripPfx] at h
      split_ifs at h with heq
      · rw [beq_iff_eq] at heq
        rw [heq, List.cons_append, ih h]

def tailAfter0 : List (Fin 2) → Option (List (Fin 2))
  | [] => some []
  | x :: t => if x == 0 then some t else none

lemma tailAfter0_spec {r r' : List (Fin 2)} (h : tailAfter0 r = some r') :
    r +> (default : ListBlank (Fin 2)) = [0] +> (r' +> default) := by
  rcases r with _ | ⟨x, t⟩
  · cases h
    exact ListBlank.default_eq_append_zero
  · dsimp only [tailAfter0] at h
    split_ifs at h with hx
    · cases h
      rw [beq_iff_eq] at hx
      rw [hx]
      rfl

inductive SplitRes where
  | mk : ℕ → List (Fin 2) → SplitRes

def split1 : ℕ → List (Fin 2) → SplitRes
  | 0, xs => .mk 0 xs
  | fuel + 1, xs =>
    match stripPfx [1] xs with
    | some t => SplitRes.casesOn (split1 fuel t) (fun n r => .mk (n + 1) r)
    | none => .mk 0 xs

lemma split1_spec (fuel : ℕ) (xs : List (Fin 2)) :
    SplitRes.casesOn (split1 fuel xs) (fun n r => xs = ([1] : List (Fin 2)) ^ n ++ r) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [split1]
    rcases h : stripPfx [1] xs with _ | t
    · rfl
    · dsimp only
      have ih_t := ih t
      rcases hsp : split1 fuel t with ⟨n, r⟩
      rw [hsp] at ih_t
      dsimp only at ih_t ⊢
      rw [stripPfx_spec h, ih_t, pow_succ_list, List.append_assoc]

def split11 : ℕ → List (Fin 2) → SplitRes
  | 0, xs => .mk 0 xs
  | fuel + 1, xs =>
    match stripPfx [1, 1] xs with
    | some t => SplitRes.casesOn (split11 fuel t) (fun n r => .mk (n + 1) r)
    | none => .mk 0 xs

lemma split11_spec (fuel : ℕ) (xs : List (Fin 2)) :
    SplitRes.casesOn (split11 fuel xs) (fun n r => xs = ([1, 1] : List (Fin 2)) ^ n ++ r) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [split11]
    rcases h : stripPfx [1, 1] xs with _ | t
    · rfl
    · dsimp only
      have ih_t := ih t
      rcases hsp : split11 fuel t with ⟨n, r⟩
      rw [hsp] at ih_t
      dsimp only at ih_t ⊢
      rw [stripPfx_spec h, ih_t, pow_succ_list, List.append_assoc]

def split01Any : ℕ → List (Fin 2) → SplitRes
  | 0, xs => .mk 0 xs
  | fuel + 1, xs =>
    match stripPfx [0, 1] xs with
    | some t => SplitRes.casesOn (split01Any fuel t) (fun n r => .mk (n + 1) r)
    | none => .mk 0 xs

lemma split01Any_spec (fuel : ℕ) (xs : List (Fin 2)) :
    SplitRes.casesOn (split01Any fuel xs) (fun n r => xs = ([0, 1] : List (Fin 2)) ^ n ++ r) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [split01Any]
    rcases h : stripPfx [0, 1] xs with _ | t
    · rfl
    · dsimp only
      have ih_t := ih t
      rcases hsp : split01Any fuel t with ⟨n, r⟩
      rw [hsp] at ih_t
      dsimp only at ih_t ⊢
      rw [stripPfx_spec h, ih_t, pow_succ_list, List.append_assoc]

def split01 : ℕ → List (Fin 2) → SplitRes
  | 0, xs => .mk 0 xs
  | fuel + 1, xs =>
    match stripPfx [0, 1, 0] xs with
    | some t => SplitRes.casesOn (split01 fuel (0 :: t)) (fun n r => .mk (n + 1) r)
    | none => .mk 0 xs

lemma split01_spec (fuel : ℕ) (xs : List (Fin 2)) :
    SplitRes.casesOn (split01 fuel xs) (fun n r => xs = ([0, 1] : List (Fin 2)) ^ n ++ r) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [split01]
    rcases h : stripPfx [0, 1, 0] xs with _ | t
    · rfl
    · dsimp only
      have ih_t := ih (0 :: t)
      rcases hsp : split01 fuel (0 :: t) with ⟨n, r⟩
      rw [hsp] at ih_t
      dsimp only at ih_t ⊢
      have h_eq : xs = [0, 1] ++ (0 :: t) := by
        rw [stripPfx_spec h]; rfl
      rw [h_eq, ih_t, pow_succ_list, List.append_assoc]

inductive RStepRes where
  | mk : ℕ → List (Fin 2) → RStepRes

def rStep (N : ℕ) (r₂ : List (Fin 2)) : Option RStepRes :=
  match stripPfx [0, 1, 1, 1, 1, 1, 1, 1] r₂ with
  | some r₃ =>
    SplitRes.casesOn (split11 3000 r₃) (fun a r₄ =>
      match tailAfter0 r₄ with
      | some r₅ =>
        some (.mk (N + 2) ([0, 1, 1, 1, 1] ++ (([0, 1] : List (Fin 2)) ^ a ++ ([0, 1, 1] ++ r₅))))
      | none => none)
  | none =>
    match stripPfx [0, 1, 1, 1, 1, 0, 1, 1, 1] r₂ with
    | some r₃ =>
      SplitRes.casesOn (split11 3000 r₃) (fun b r₄ =>
        match tailAfter0 r₄ with
        | some r₅ =>
          some (.mk (N + 1)
            ([0, 1, 1, 1, 1, 1, 1, 1] ++ (([0, 1] : List (Fin 2)) ^ b ++ ([0, 1, 1] ++ r₅))))
        | none => none)
    | none =>
      match stripPfx [0, 1, 1, 1, 1, 0, 1] r₂ with
      | some r₃ =>
        match tailAfter0 r₃ with
        | some r₅ => some (.mk (N + 1) ([0, 1, 1, 1, 1, 1, 1, 1, 1] ++ r₅))
        | none => none
      | none => none

lemma rStep_spec (N : ℕ) (r₂ : List (Fin 2)) {N' : ℕ} {r₂' : List (Fin 2)}
    (h : rStep N r₂ = some (.mk N' r₂')) (l : ListBlank (Fin 2)) :
    (([0, 0, 0, 0] +> l) <{{D}} ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +> (r₂ +> default))))
      [target_tm]⊢*
    (([0] +> l) <{{D}} ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N' +> (r₂' +> default)))) := by
  dsimp only [rStep] at h
  rcases h₁ : stripPfx [0, 1, 1, 1, 1, 1, 1, 1] r₂ with _ | r₃ <;> rw [h₁] at h <;> dsimp only at h
  · rcases h₂ : stripPfx [0, 1, 1, 1, 1, 0, 1, 1, 1] r₂ with _ | r₃ <;> rw [h₂] at h <;> dsimp only at h
    · rcases h₃ : stripPfx [0, 1, 1, 1, 1, 0, 1] r₂ with _ | r₃ <;> rw [h₃] at h <;> dsimp only at h
      · cases h
      · rcases ht : tailAfter0 r₃ with _ | r₅ <;> rw [ht] at h
        · cases h
        · cases h
          have hr₂ := stripPfx_spec h₃
          have ht₀ := tailAfter0_spec ht
          have h_lhs : r₂ +> (default : ListBlank (Fin 2)) =
              [0, 1, 1, 1, 1, 0, 1, 0] +> (r₅ +> default) := by
            rw [hr₂, ListBlank.append_assoc, ht₀]
            rfl
          rw [h_lhs, ListBlank.append_assoc]
          exact R2_raw l (r₅ +> default) N
    · have hsp := split11_spec 3000 r₃
      rcases hsp_eq : split11 3000 r₃ with ⟨b, r₄⟩
      rw [hsp_eq] at h hsp
      dsimp only at h hsp
      rcases ht : tailAfter0 r₄ with _ | r₅ <;> rw [ht] at h
      · cases h
      · cases h
        have hr₂ := stripPfx_spec h₂
        have ht₀ := tailAfter0_spec ht
        have h_lhs : r₂ +> (default : ListBlank (Fin 2)) =
            [0, 1, 1, 1, 1, 0, 1, 1, 1] +>
              (([1, 1] : List (Fin 2)) ^ b +> ([0] +> (r₅ +> default))) := by
          conv_lhs => rw [hr₂, hsp]
          rw [ListBlank.append_assoc, ListBlank.append_assoc, ht₀]
        rw [h_lhs, ListBlank.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc]
        exact RB_raw l (r₅ +> default) N b
  · have hsp := split11_spec 3000 r₃
    rcases hsp_eq : split11 3000 r₃ with ⟨a, r₄⟩
    rw [hsp_eq] at h hsp
    dsimp only at h hsp
    rcases ht : tailAfter0 r₄ with _ | r₅ <;> rw [ht] at h
    · cases h
    · cases h
      have hr₂ := stripPfx_spec h₁
      have ht₀ := tailAfter0_spec ht
      have h_lhs : r₂ +> (default : ListBlank (Fin 2)) =
          [0, 1, 1, 1, 1, 1, 1, 1] +>
            (([1, 1] : List (Fin 2)) ^ a +> ([0] +> (r₅ +> default))) := by
        conv_lhs => rw [hr₂, hsp]
        rw [ListBlank.append_assoc, ListBlank.append_assoc, ht₀]
      rw [h_lhs, ListBlank.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc]
      exact R1_raw l (r₅ +> default) N a

inductive BurstRes where
  | mk : List (Fin 2) → ℕ → List (Fin 2) → BurstRes

def rBurst : ℕ → List (Fin 2) → ℕ → List (Fin 2) → BurstRes
  | 0, ahd, N, r₂ => .mk ahd N r₂
  | fuel + 1, ahd, N, r₂ =>
    match stripPfx [0, 0, 0, 0] ahd with
    | some ahd₀ =>
      match rStep N r₂ with
      | some res => RStepRes.casesOn res (fun N' r₂' => rBurst fuel (0 :: ahd₀) N' r₂')
      | none => .mk ahd N r₂
    | none => .mk ahd N r₂

lemma rBurst_spec (fuel : ℕ) (ahd : List (Fin 2)) (N : ℕ) (r₂ : List (Fin 2))
    (l₀ : ListBlank (Fin 2)) :
    BurstRes.casesOn (rBurst fuel ahd N r₂) (fun ahd' N' r₂' =>
      ((ahd +> l₀) <{{D}} ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N +> (r₂ +> default))))
        [target_tm]⊢*
      ((ahd' +> l₀) <{{D}}
        ([0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ N' +> (r₂' +> default))))) := by
  induction fuel generalizing ahd N r₂ with
  | zero => exact ⟨0, rfl⟩
  | succ fuel ih =>
    dsimp only [rBurst]
    rcases h₁ : stripPfx [0, 0, 0, 0] ahd with _ | ahd₀
    · exact ⟨0, rfl⟩
    · dsimp only
      rcases h₂ : rStep N r₂ with _ | ⟨N', r₂'⟩
      · exact ⟨0, rfl⟩
      · dsimp only
        have hahd : ahd +> l₀ = [0, 0, 0, 0] +> (ahd₀ +> l₀) := by
          rw [stripPfx_spec h₁, ListBlank.append_assoc]
        have ih_step := ih (0 :: ahd₀) N' r₂'
        rcases hb : rBurst fuel (0 :: ahd₀) N' r₂' with ⟨ahd'', N'', r₂''⟩
        rw [hb] at ih_step
        dsimp only at ih_step ⊢
        rw [hahd]
        exact stepStar_trans (rStep_spec N r₂ h₂ (ahd₀ +> l₀)) ih_step

def stepFastB (bhd ahd : List (Fin 2)) : Option (BCfg (Fin 2) (Fin 6)) :=
  match stripPfx [0, 1] ahd with
  | some ahd₁ =>
    match stripPfx [1, 1, 0, 0, 1] bhd with
    | some bhd' =>
      SplitRes.casesOn (split01Any 3000 ahd₁) (fun m rem =>
        some ⟨[1, 1, 0, 0, 1] ++ (([0, 0] : List (Fin 2)) ^ (m + 1) ++ bhd'), rem, B, .right⟩)
    | none =>
      match stripPfx [1, 0, 0, 1] bhd with
      | some bhd' =>
        SplitRes.casesOn (split01Any 3000 ahd₁) (fun m rem =>
          some ⟨[1, 0, 0, 1] ++ (([1, 1] : List (Fin 2)) ^ (m + 1) ++ bhd'), rem, B, .right⟩)
      | none => step_r0inf target_tm ⟨bhd, ahd, B, .right⟩
  | none =>
    match stripPfx [1] ahd with
    | some ahd₁ =>
      SplitRes.casesOn (split1 3000 ahd₁) (fun m rem =>
        some ⟨([1] : List (Fin 2)) ^ (m + 1) ++ bhd, rem, B, .right⟩)
    | none => step_r0inf target_tm ⟨bhd, ahd, B, .right⟩

lemma stepFastB_spec (bhd ahd : List (Fin 2)) {y : BCfg (Fin 2) (Fin 6)}
    (h : stepFastB bhd ahd = some y) (l₀ : ListBlank (Fin 2)) :
    (toCfg ⟨bhd, ahd, B, .right⟩ l₀ default) [target_tm]⊢* (toCfg y l₀ default) := by
  dsimp only [stepFastB] at h
  rcases ha₁ : stripPfx [0, 1] ahd with _ | ahd₁ <;> rw [ha₁] at h <;> dsimp only at h
  · rcases ha₂ : stripPfx [1] ahd with _ | ahd₁ <;> rw [ha₂] at h <;> dsimp only at h
    · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩
    · have hsp := split1_spec 3000 ahd₁
      rcases hsp_eq : split1 3000 ahd₁ with ⟨m, rem⟩
      rw [hsp_eq] at h hsp
      cases h
      dsimp only [toCfg] at hsp ⊢
      have ha := stripPfx_spec ha₂
      have h_r : ahd +> (default : ListBlank (Fin 2)) =
          ([1] : List (Fin 2)) ^ (m + 1) +> (rem +> default) := by
        rw [ha, hsp, pow_succ_list, ListBlank.append_assoc, ListBlank.append_assoc]
        rfl
      rw [h_r, ListBlank.append_assoc]
      exact B_ones (m + 1) (bhd +> l₀) (rem +> default)
  · rcases hb₁ : stripPfx [1, 1, 0, 0, 1] bhd with _ | bhd' <;> rw [hb₁] at h <;> dsimp only at h
    · rcases hb₂ : stripPfx [1, 0, 0, 1] bhd with _ | bhd' <;> rw [hb₂] at h <;> dsimp only at h
      · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩
      · have hsp := split01Any_spec 3000 ahd₁
        rcases hsp_eq : split01Any 3000 ahd₁ with ⟨m, rem⟩
        rw [hsp_eq] at h hsp
        cases h
        dsimp only [toCfg] at hsp ⊢
        have hb := stripPfx_spec hb₂
        have ha := stripPfx_spec ha₁
        have h_l : bhd +> l₀ = [1, 0, 0, 1] +> (bhd' +> l₀) := by
          rw [hb, ListBlank.append_assoc]
        have h_r : ahd +> (default : ListBlank (Fin 2)) =
            ([0, 1] : List (Fin 2)) ^ (m + 1) +> (rem +> default) := by
          rw [ha, hsp, pow_succ_list, ListBlank.append_assoc, ListBlank.append_assoc]
          rfl
        rw [h_l, h_r, ListBlank.append_assoc, ListBlank.append_assoc]
        exact cross_pairs (m + 1) (bhd' +> l₀) (rem +> default)
    · have hsp := split01Any_spec 3000 ahd₁
      rcases hsp_eq : split01Any 3000 ahd₁ with ⟨m, rem⟩
      rw [hsp_eq] at h hsp
      cases h
      dsimp only [toCfg] at hsp ⊢
      have hb := stripPfx_spec hb₁
      have ha := stripPfx_spec ha₁
      have h_l : bhd +> l₀ = [1, 1, 0, 0, 1] +> (bhd' +> l₀) := by
        rw [hb, ListBlank.append_assoc]
      have h_r : ahd +> (default : ListBlank (Fin 2)) =
          ([0, 1] : List (Fin 2)) ^ (m + 1) +> (rem +> default) := by
        rw [ha, hsp, pow_succ_list, ListBlank.append_assoc, ListBlank.append_assoc]
        rfl
      rw [h_l, h_r, ListBlank.append_assoc, ListBlank.append_assoc]
      exact recharge_pairs (m + 1) (bhd' +> l₀) (rem +> default)

def stepFastD (bhd ahd : List (Fin 2)) : Option (BCfg (Fin 2) (Fin 6)) :=
  match stripPfx [0, 0, 0, 0] ahd with
  | some ahd₀ =>
    match stripPfx [0, 1, 1] bhd with
    | some bhd₁ =>
      SplitRes.casesOn (split01 3000 bhd₁) (fun n₀ r₂ =>
        match rStep n₀ r₂ with
        | some res₁ =>
          RStepRes.casesOn res₁ (fun N₁ r₂' =>
            BurstRes.casesOn (rBurst 1000 (0 :: ahd₀) N₁ r₂') (fun ahd' N₂ r₂'' =>
              some ⟨[0, 1, 1] ++ (([0, 1] : List (Fin 2)) ^ N₂ ++ r₂''), ahd', D, .left⟩))
        | none => step_r0inf target_tm ⟨bhd, ahd, D, .left⟩)
    | none => step_r0inf target_tm ⟨bhd, ahd, D, .left⟩
  | none =>
    match stripPfx [1, 1] ahd with
    | some ahd₁ =>
      match stripPfx [0] bhd with
      | some bhd' =>
        SplitRes.casesOn (split11 3000 ahd₁) (fun m rem =>
          some ⟨[0] ++ (([0, 1] : List (Fin 2)) ^ (m + 1) ++ bhd'), rem, D, .left⟩)
      | none => step_r0inf target_tm ⟨bhd, ahd, D, .left⟩
    | none => step_r0inf target_tm ⟨bhd, ahd, D, .left⟩

lemma stepFastD_spec (bhd ahd : List (Fin 2)) {y : BCfg (Fin 2) (Fin 6)}
    (h : stepFastD bhd ahd = some y) (l₀ : ListBlank (Fin 2)) :
    (toCfg ⟨bhd, ahd, D, .left⟩ l₀ default) [target_tm]⊢* (toCfg y l₀ default) := by
  dsimp only [stepFastD] at h
  rcases ha₁ : stripPfx [0, 0, 0, 0] ahd with _ | ahd₀ <;> rw [ha₁] at h <;> dsimp only at h
  · rcases ha₂ : stripPfx [1, 1] ahd with _ | ahd₁ <;> rw [ha₂] at h <;> dsimp only at h
    · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩
    · rcases hb₂ : stripPfx [0] bhd with _ | bhd' <;> rw [hb₂] at h <;> dsimp only at h
      · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩
      · have hsp := split11_spec 3000 ahd₁
        rcases hsp_eq : split11 3000 ahd₁ with ⟨m, rem⟩
        rw [hsp_eq] at h hsp
        cases h
        dsimp only [toCfg] at hsp ⊢
        have hb := stripPfx_spec hb₂
        have ha := stripPfx_spec ha₂
        have h_l : ahd +> l₀ =
            ([1, 1] : List (Fin 2)) ^ (m + 1) +> (rem +> l₀) := by
          rw [ha, hsp, pow_succ_list, ListBlank.append_assoc, ListBlank.append_assoc]
          rfl
        have h_r : bhd +> (default : ListBlank (Fin 2)) =
            [0] +> (bhd' +> default) := by
          rw [hb, ListBlank.append_assoc]
        rw [h_l, h_r, ListBlank.append_assoc, ListBlank.append_assoc]
        exact back_pairs (m + 1) (rem +> l₀) (bhd' +> default)
  · rcases hb₁ : stripPfx [0, 1, 1] bhd with _ | bhd₁ <;> rw [hb₁] at h <;> dsimp only at h
    · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩
    · have hsp := split01_spec 3000 bhd₁
      rcases hsp_eq : split01 3000 bhd₁ with ⟨n₀, r₂⟩
      rw [hsp_eq] at h hsp
      dsimp only at h hsp
      rcases hr : rStep n₀ r₂ with _ | ⟨N₁, r₂'⟩ <;> rw [hr] at h <;> dsimp only at h
      · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩
      · have hburst := rBurst_spec 1000 (0 :: ahd₀) N₁ r₂' l₀
        rcases hb_eq : rBurst 1000 (0 :: ahd₀) N₁ r₂' with ⟨ahd', N₂, r₂''⟩
        rw [hb_eq] at h hburst
        cases h
        dsimp only [toCfg] at hburst ⊢
        have hb := stripPfx_spec hb₁
        have ha := stripPfx_spec ha₁
        have h_l : ahd +> l₀ = [0, 0, 0, 0] +> (ahd₀ +> l₀) := by
          rw [ha, ListBlank.append_assoc]
        have h_r : bhd +> (default : ListBlank (Fin 2)) =
            [0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ n₀ +> (r₂ +> default)) := by
          conv_lhs => rw [hb, hsp]
          rw [ListBlank.append_assoc, ListBlank.append_assoc]
        rw [h_l, h_r, ListBlank.append_assoc, ListBlank.append_assoc]
        exact stepStar_trans (rStep_spec n₀ r₂ hr (ahd₀ +> l₀)) hburst

def stepFast (x : BCfg (Fin 2) (Fin 6)) : Option (BCfg (Fin 2) (Fin 6)) :=
  BCfg.casesOn x (fun bhd ahd s sgn =>
    if s == B && sgn == .right then
      stepFastB bhd ahd
    else if s == D && sgn == .left then
      stepFastD bhd ahd
    else
      step_r0inf target_tm ⟨bhd, ahd, s, sgn⟩)

lemma stepFast_spec (x : BCfg (Fin 2) (Fin 6)) {y : BCfg (Fin 2) (Fin 6)}
    (h : stepFast x = some y) (l₀ : ListBlank (Fin 2)) :
    (toCfg x l₀ default) [target_tm]⊢* (toCfg y l₀ default) := by
  rcases x with ⟨bhd, ahd, s, sgn⟩
  dsimp only [stepFast] at h
  split_ifs at h with hB hD
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hB
    rw [hB.1, hB.2]
    exact stepFastB_spec bhd ahd h l₀
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hD
    rw [hD.1, hD.2]
    exact stepFastD_spec bhd ahd h l₀
  · exact ⟨1, step_r0inf_spec target_tm _ h l₀⟩

def run : ℕ → BCfg (Fin 2) (Fin 6) → BCfg (Fin 2) (Fin 6)
  | 0, x => x
  | n + 1, x =>
    match stepFast x with
    | some y => run n y
    | none => x

lemma run_spec (n : ℕ) (x : BCfg (Fin 2) (Fin 6)) (l₀ : ListBlank (Fin 2)) :
    (toCfg x l₀ default) [target_tm]⊢* (toCfg (run n x) l₀ default) := by
  induction n generalizing x with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    dsimp only [run]
    rcases h : stepFast x with _ | y
    · exact ⟨0, rfl⟩
    · exact stepStar_trans (stepFast_spec x h l₀) (ih y)

def frame (zs : List ℕ) : BCfg (Fin 2) (Fin 6) :=
  ⟨[1, 0, 0, 1], ([0, 1] : List (Fin 2)) ^ 8 ++ reg zs, B, .right⟩

lemma to_frame (M : ℕ) (zs : List ℕ) :
    (recCfg (M + 8) zs) [target_tm]⊢*
      (toCfg (frame zs) (([1, 1] : List (Fin 2)) ^ M +> ([1] +> default)) default) := by
  have h := cross_raw M default (([0, 1] : List (Fin 2)) ^ 8 +> (reg zs +> default))
  have h_l : ([0, 0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_pow : (([0, 1] : List (Fin 2)) ^ M +>
      (([0, 1] : List (Fin 2)) ^ 8 +> (reg zs +> default))) =
      (([0, 1] : List (Fin 2)) ^ (M + 8) +> (reg zs +> default)) := by
    rw [list_pow_add, ListBlank.append_assoc]
  rw [h_l, h_pow] at h
  dsimp only [frame, toCfg]
  rwa [ListBlank.append_assoc]

def decRuns : List (Fin 2) → ℕ → List ℕ
  | [], 0 => []
  | [], k + 1 => [k + 1]
  | x :: t, 0 => if x == 1 then decRuns t 1 else decRuns t 0
  | x :: t, k + 1 => if x == 1 then decRuns t (k + 2) else (k + 1) :: decRuns t 0

inductive SpecialRes where
  | mk : ℕ → List ℕ → SpecialRes

def specialCheck (l : List (Fin 2)) (d : ℕ) (zs' : List ℕ) : Option SpecialRes :=
  if 7 ≤ d then
    if eqAppR0inf l ([0, 0, 1] ++ (([0, 1] : List (Fin 2)) ^ d ++ reg zs')) then
      some (.mk (d - 7) zs')
    else
      none
  else
    none

def specialRuns (l : List (Fin 2)) (runs : List ℕ) : Option SpecialRes :=
  specialCheck l (countLead1 runs 0) (dropLead1 runs)

def special (zs : List ℕ) : Option SpecialRes :=
  BCfg.casesOn (run 2200 (frame zs)) (fun l r s sgn =>
    if r == [] && s == D && sgn == .left then
      specialRuns l (decRuns (l.drop 3) 0)
    else
      none)

lemma special_spec (zs : List ℕ) (k : ℕ) (zs' : List ℕ)
    (h : special zs = some (.mk k zs')) (h' : NH zs') : NH zs := by
  intro M
  dsimp only [special] at h
  have h₁ := stepStar_trans (to_frame M zs)
    (run_spec 2200 (frame zs) (([1, 1] : List (Fin 2)) ^ M +> ([1] +> default)))
  rcases hrun : run 2200 (frame zs) with ⟨l', r', s', sgn'⟩
  rw [hrun] at h h₁
  dsimp only at h
  split_ifs at h with h_res
  rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h_res
  rcases h_res with ⟨hr_nil, hs_D, hsgn_L⟩
  subst hr_nil hs_D hsgn_L
  dsimp only [specialRuns, specialCheck] at h
  split_ifs at h with hd heq
  cases h
  dsimp only [toCfg] at h₁
  have h_eq : l' +> (default : ListBlank (Fin 2)) =
      [0, 0, 1] +>
        (([0, 1] : List (Fin 2)) ^ countLead1 (decRuns (l'.drop 3) 0) 0 +>
          (reg (dropLead1 (decRuns (l'.drop 3) 0)) +> default)) := by
    rw [eqAppR0inf_spec heq, ListBlank.append_assoc, ListBlank.append_assoc]
  rw [h_eq] at h₁
  have h_back := back_raw M default
    (([0, 1] : List (Fin 2)) ^ countLead1 (decRuns (l'.drop 3) 0) 0 +>
      (reg (dropLead1 (decRuns (l'.drop 3) 0)) +> default))
  have h_l00 : ([1, 0, 0] : List (Fin 2)) +> default = [1] +> default := by
    change [1] +> ([0, 0] +> default) = [1] +> default
    rw [all0_spec (by decide)]
  have h_l0 : ([0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  have h_pow : (([0, 1] : List (Fin 2)) ^ (M + 1) +>
      (([0, 1] : List (Fin 2)) ^ countLead1 (decRuns (l'.drop 3) 0) 0 +>
        (reg (dropLead1 (decRuns (l'.drop 3) 0)) +> default))) =
      (([0, 1] : List (Fin 2)) ^ (M + (countLead1 (decRuns (l'.drop 3) 0) 0 - 7) + 8) +>
        (reg (dropLead1 (decRuns (l'.drop 3) 0)) +> default)) := by
    rw [← ListBlank.append_pow_add]
    have h_add : M + 1 + countLead1 (decRuns (l'.drop 3) 0) 0 =
        M + (countLead1 (decRuns (l'.drop 3) 0) 0 - 7) + 8 := by omega
    rw [h_add]
  rw [h_l00, h_l0, h_pow] at h_back
  exact neverHaltsFrom_of_reachesStar (stepStar_trans h₁ h_back)
    (h' (M + (countLead1 (decRuns (l'.drop 3) 0) 0 - 7)))

def cyc : List (Fin 2) := [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

lemma cycle (l : ListBlank (Fin 2)) :
    ((cyc +> l) {{B}}> default) [target_tm]⊢⁺ ((cyc +> ([0] +> l)) {{B}}> default) := by
  have h := steps1_spec_true target_tm 100 ⟨cyc, [0], B, .right⟩
    (x' := ⟨cyc ++ [0], [], B, .right⟩) (by decide) l default
  dsimp only [toCfg, ListBlank.append_nil] at h
  have h_r : ([0] : List (Fin 2)) +> default = default := all0_spec (by decide)
  rw [h_r, ListBlank.append_assoc] at h
  exact h

def final (zs : List ℕ) : Bool :=
  BCfg.casesOn (run 521 (frame zs)) (fun l r s sgn =>
    if r == [] && s == B && sgn == .right then
      (stripPfx cyc l).isSome
    else
      false)

lemma final_spec (zs : List ℕ) (h : final zs = true) : NH zs := by
  intro M
  dsimp only [final] at h
  have h₁ := stepStar_trans (to_frame M zs)
    (run_spec 521 (frame zs) (([1, 1] : List (Fin 2)) ^ M +> ([1] +> default)))
  rcases hrun : run 521 (frame zs) with ⟨l', r', s', sgn'⟩
  rw [hrun] at h h₁
  dsimp only at h
  split_ifs at h with h_res
  rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h_res
  rcases h_res with ⟨hr_nil, hs_B, hsgn_R⟩
  subst hr_nil hs_B hsgn_R
  rcases h_sp : stripPfx cyc l' with _ | t
  · rw [h_sp] at h; cases h
  · dsimp only [toCfg, ListBlank.append_nil] at h₁
    rw [stripPfx_spec h_sp, ListBlank.append_assoc] at h₁
    refine neverHaltsFrom_of_reachesStar h₁ ?_
    exact NeverHaltsFrom.of_reachesPlus_invariant
      (P := fun c => ∃ L, c = (cyc +> L) {{B}}> default)
      (fun c ⟨L, hL⟩ => by
        rw [hL]
        exact ⟨(cyc +> ([0] +> L)) {{B}}> default, cycle L, ⟨[0] +> L, rfl⟩⟩)
      ⟨t +> (([1, 1] : List (Fin 2)) ^ M +> ([1] +> default)), rfl⟩

def driveSteps : ℕ → List ℕ → Option (List ℕ)
  | 0, zs => some zs
  | k + 1, zs =>
    match mstep zs with
    | some zs₁ => driveSteps k zs₁
    | none =>
      match special zs with
      | some res => SpecialRes.casesOn res (fun _ zs₁ => driveSteps k zs₁)
      | none => none

lemma driveSteps_spec (k : ℕ) (zs zs' : List ℕ) (h : driveSteps k zs = some zs') (h' : NH zs') :
    NH zs := by
  induction k generalizing zs with
  | zero => cases h; exact h'
  | succ k ih =>
    dsimp only [driveSteps] at h
    rcases hm : mstep zs with _ | zs₁ <;> rw [hm] at h <;> dsimp only at h
    · rcases hs : special zs with _ | ⟨d, zs₁⟩ <;> rw [hs] at h
      · cases h
      · exact special_spec zs d zs₁ hs (ih zs₁ h)
    · exact mstep_spec zs zs₁ hm (ih zs₁ h)

def driveEnd (k : ℕ) (zs : List ℕ) : Bool :=
  match driveSteps k zs with
  | some zs' => final zs'
  | none => false

lemma driveEnd_spec (k : ℕ) (zs : List ℕ) (h : driveEnd k zs = true) : NH zs := by
  dsimp only [driveEnd] at h
  rcases hd : driveSteps k zs with _ | zs' <;> rw [hd] at h <;> dsimp only at h
  · cases h
  · exact driveSteps_spec k zs zs' hd (final_spec zs' h)

def Z1 : List ℕ :=
  13 :: (List.replicate 1193 1 ++ [3, 9] ++ List.replicate 8 1 ++ [2])

def checkOpen (x : BCfg (Fin 2) (Fin 6)) : Bool :=
  BCfg.casesOn x (fun l r s sgn =>
    r == [] && s == D && sgn == .left &&
      eqAppR0inf l ([0, 1, 1] ++ (([0, 1] : List (Fin 2)) ^ 10 ++ reg Z1)))

lemma checkOpen_spec (x : BCfg (Fin 2) (Fin 6)) (h : checkOpen x = true)
    (h₁ : (init []) [target_tm]⊢* (toCfg x default default)) :
    (init []) [target_tm]⊢* (recCfg 10 Z1) := by
  rcases x with ⟨l', r', s', sgn'⟩
  dsimp only [checkOpen] at h
  rw [Bool.and_assoc, Bool.and_assoc, Bool.and_eq_true, beq_iff_eq,
    Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hr_nil, hs_D, hsgn_L, heq⟩
  subst hr_nil hs_D hsgn_L
  dsimp only [toCfg] at h₁
  have h_eq : l' +> (default : ListBlank (Fin 2)) =
      [0, 1, 1] +> (([0, 1] : List (Fin 2)) ^ 10 +> (reg Z1 +> default)) := by
    rw [eqAppR0inf_spec heq, ListBlank.append_assoc, ListBlank.append_assoc]
  rw [h_eq] at h₁
  exact h₁

def initBCfg : BCfg (Fin 2) (Fin 6) :=
  ⟨([0] : List (Fin 2)) ^ 2438, [], A, .right⟩

def open_ok : Bool :=
  checkOpen (run 1189 initBCfg)

lemma opening (h : open_ok = true) : (init []) [target_tm]⊢* (recCfg 10 Z1) := by
  have h₁ := run_spec 1189 initBCfg default
  have h_init : toCfg initBCfg default default = init [] := by
    dsimp only [initBCfg, toCfg, ListBlank.append_nil]
    rw [zeros_append_default 2438]
    rfl
  rw [h_init] at h₁
  exact checkOpen_spec (run 1189 initBCfg) h h₁

lemma open_ok_true : open_ok = true := by rfl

def C9 : List ℕ := [2480, 1, 3, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2]
def C24 : List ℕ := [2558, 1, 1, 1, 3, 1, 1, 5, 1, 6]

lemma seg1 : driveSteps 3 Z1 = some [2432] := by rfl
lemma seg2 : driveSteps 6 [2432] = some [2454] := by rfl
lemma seg3 : driveSteps 13 [2454] = some [2480] := by rfl
lemma seg4 : driveSteps 6 [2480] = some [2502] := by rfl
lemma seg5 : driveSteps 4 [2502] = some C9 := by rfl
lemma seg6 : driveSteps 19 C9 = some [2532] := by rfl
lemma seg7 : driveSteps 15 [2532] = some [2560] := by rfl
lemma seg8 : driveSteps 13 [2560] = some C24 := by rfl
lemma seg9 : driveSteps 13 C24 = some [2596] := by rfl
lemma seg10 : driveEnd 9 [2596] = true := by rfl

lemma nh_Z1 : NH Z1 :=
  driveSteps_spec 3 Z1 [2432] seg1 <|
  driveSteps_spec 6 [2432] [2454] seg2 <|
  driveSteps_spec 13 [2454] [2480] seg3 <|
  driveSteps_spec 6 [2480] [2502] seg4 <|
  driveSteps_spec 4 [2502] C9 seg5 <|
  driveSteps_spec 19 C9 [2532] seg6 <|
  driveSteps_spec 15 [2532] [2560] seg7 <|
  driveSteps_spec 13 [2560] C24 seg8 <|
  driveSteps_spec 13 C24 [2596] seg9 <|
  driveEnd_spec 9 [2596] seg10

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  rw [isNotHalt_iff_neverHaltsFrom_init]
  exact neverHaltsFrom_of_reachesStar (opening open_ok_true) (nh_Z1 2)

end BusyBeaver.M_1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_HHH0RD
