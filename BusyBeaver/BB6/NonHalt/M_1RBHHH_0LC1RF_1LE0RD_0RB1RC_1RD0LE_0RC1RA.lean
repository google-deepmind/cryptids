/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Longitudinal (DH0 toDHCfg flipTM SegRL SegRR SegLL SegRLs SideRLs)
open BusyBeaver.Longitudinal.BoundedConfig (toCfg all0_spec steps_spec steps1_spec_true
  segRLs_c_spec sideRLs_c_spec)
open BusyBeaver.Longitudinal.SBC (RC0 RC1 RC2 CfgAt S)

abbrev w : List (Fin 2) := [1, 0, 0, 1, 0]
abbrev u : List (Fin 2) := [1, 0, 0, 0, 0]
abbrev v : List (Fin 2) := [0, 0, 0, 1, 0]
abbrev z : List (Fin 2) := [1, 1, 0]
abbrev d₀ : List (Fin 2) := [0, 0, 1, 0]
abbrev d₁ : List (Fin 2) := [1, 0, 1, 0]
abbrev d₁' : List (Fin 2) := [1, 0, 1, 0]
abbrev dh : ListBlank (Fin 2) := [1] +> default

abbrev hR : DH0 (Fin 2) (Fin 6) := (B, [0])
abbrev hL : DH0 (Fin 2) (Fin 6) := (E, [0])
abbrev huR : DH0 (Fin 2) (Fin 6) := (B, [0, 0])
abbrev huL : DH0 (Fin 2) (Fin 6) := (E, [0, 0])
abbrev hu : DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6) := (huR, huL)
abbrev hrstL : DH0 (Fin 2) (Fin 6) := (C, [0, 1, 0])

lemma rule_wall : SegRLs target_tm ([(hR, hL)] ^ 2) ([(hR, hL)] ^ 2) w w :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma rule_pair : SegRLs target_tm ([(hR, hL)] ^ 6) ([(hR, hL)] ^ 2) (z ++ w ++ w) (w ++ w ++ z) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_w_hu : SegRLs target_tm [hu] [hu] w w :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_u_hu : SegRLs target_tm [hu] [hu] u u :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma side_hu : SideRLs target_tm [hu] default (u +> default) :=
  sideRLs_c_spec target_tm (hs := [hu]) (r := []) (r' := u) (T := 200) (by decide)

lemma side_u_pow (m : ℕ) :
    SideRLs target_tm [hu] (u ^ m +> default) (u ^ (1 + m) +> default) := by
  induction m with
  | zero =>
    simpa [pow_zero_list, pow_succ_list] using side_hu
  | succ m ih =>
    have h := seg_u_hu.sideRLs_concat ih
    have h₁ : 1 + (m + 1) = (1 + m) + 1 := by omega
    rw [pow_succ_list u m, ListBlank.append_assoc, h₁, pow_succ_list u (1 + m),
      ListBlank.append_assoc]
    exact h

lemma side_w_u_pow (n m : ℕ) :
    SideRLs target_tm [hu] (w ^ n +> (u ^ m +> default)) (w ^ n +> (u ^ (1 + m) +> default)) := by
  induction n with
  | zero =>
    simpa [pow_zero_list] using side_u_pow m
  | succ n ih =>
    have h := seg_w_hu.sideRLs_concat ih
    rw [pow_succ_list w n, ListBlank.append_assoc, ListBlank.append_assoc]
    exact h

lemma seg_zww_hu : SegRLs target_tm ([(hR, hL)] ^ 6) [hu] (z ++ w ++ w) (w ++ w ++ z) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma rule_R (n m : ℕ) :
    SideRLs target_tm ([(hR, hL)] ^ 6) (RC0 w u z 0 (2 + n) m) (RC0 w u z 2 n (1 + m)) := by
  have h := seg_zww_hu.sideRLs_concat (side_w_u_pow n m)
  have h_lhs : (z ++ w ++ w) +> (w ^ n +> (u ^ m +> default)) = RC0 w u z 0 (2 + n) m := by
    unfold RC0
    have h2 : 2 + n = n + 1 + 1 := by omega
    rw [h2, pow_zero_list, pow_succ_list w (n + 1), pow_succ_list w n]
    simp only [List.append_assoc, ListBlank.append_nil, ListBlank.append_assoc]
  have h_rhs : (w ++ w ++ z) +> (w ^ n +> (u ^ (1 + m) +> default)) =
      RC0 w u z 2 n (1 + m) := by
    unfold RC0
    change (w ++ w ++ z) +> (w ^ n +> (u ^ (1 + m) +> default)) =
      (w ++ (w ++ [])) +> (z +> (w ^ n +> (u ^ (1 + m) +> default)))
    simp only [List.append_nil, List.append_assoc, ListBlank.append_assoc]
  rwa [h_lhs, h_rhs] at h

lemma seg_zu : SegRLs target_tm ([(hR, hL)] ^ 4) [] (z ++ u) (w ++ z) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma rule_U (m : ℕ) :
    SideRLs target_tm ([(hR, hL)] ^ 4) (RC0 w u z 0 0 (1 + m)) (RC0 w u z 1 0 m) := by
  have h := seg_zu.sideRLs_concat (SideRLs.nil (u ^ m +> default))
  have h_lhs : (z ++ u) +> (u ^ m +> default) = RC0 w u z 0 0 (1 + m) := by
    unfold RC0
    have h1 : 1 + m = m + 1 := by omega
    rw [h1, pow_succ_list u m]
    change (z ++ u) +> (u ^ m +> default) = [] +> (z +> ([] +> ((u ++ u ^ m) +> default)))
    simp only [ListBlank.append_nil, ListBlank.append_assoc]
  have h_rhs : (w ++ z) +> (u ^ m +> default) = RC0 w u z 1 0 m := by
    unfold RC0
    change (w ++ z) +> (u ^ m +> default) = (w ++ []) +> (z +> ([] +> (u ^ m +> default)))
    simp only [List.append_nil, ListBlank.append_nil, ListBlank.append_assoc]
  rwa [h_lhs, h_rhs] at h

lemma zeros3_u_pow_eq_v_pow (k : ℕ) :
    ([0, 0, 0] : List (Fin 2)) +> (u ^ k +> default) = v ^ k +> default := by
  induction k with
  | zero =>
    exact all0_spec (by decide)
  | succ k ih =>
    rw [pow_succ_list u k, pow_succ_list v k, ListBlank.append_assoc, ListBlank.append_assoc, ← ih]
    rfl

lemma seg_zw_hu : SegRLs target_tm ([(hR, hL)] ^ 2) [hu] (z ++ w) (w ++ [0, 0, 0]) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma rule_odd (m : ℕ) :
    SideRLs target_tm ([(hR, hL)] ^ 2) (RC0 w u z 0 1 m) (RC1 w v 0 (1 + m)) := by
  have h := seg_zw_hu.sideRLs_concat (side_u_pow m)
  have h_lhs : (z ++ w) +> (u ^ m +> default) = RC0 w u z 0 1 m := by
    unfold RC0
    change (z ++ w) +> (u ^ m +> default) = [] +> (z +> ((w ++ []) +> (u ^ m +> default)))
    simp only [List.append_nil, ListBlank.append_nil, ListBlank.append_assoc]
  have h_rhs : (w ++ [0, 0, 0]) +> (u ^ (1 + m) +> default) = RC1 w v 0 (1 + m) := by
    unfold RC1
    rw [ListBlank.append_assoc, zeros3_u_pow_eq_v_pow]
    change w +> (v ^ (1 + m) +> default) = (w ++ []) +> (v ^ (1 + m) +> default)
    simp only [List.append_nil]
  rwa [h_lhs, h_rhs] at h

lemma seg_wv : SegRLs target_tm ([(hR, hL)] ^ 2) [] (w ++ v) (w ++ w) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma rule_V (m : ℕ) :
    SideRLs target_tm ([(hR, hL)] ^ 2) (RC1 w v 0 (1 + m)) (RC1 w v 1 m) := by
  have h := seg_wv.sideRLs_concat (SideRLs.nil (v ^ m +> default))
  have h_lhs : (w ++ v) +> (v ^ m +> default) = RC1 w v 0 (1 + m) := by
    unfold RC1
    have h1 : 1 + m = m + 1 := by omega
    rw [h1, pow_succ_list v m]
    change (w ++ v) +> (v ^ m +> default) = (w ++ []) +> ((v ++ v ^ m) +> default)
    simp only [List.append_nil, ListBlank.append_assoc]
  have h_rhs : (w ++ w) +> (v ^ m +> default) = RC1 w v 1 m := by
    unfold RC1
    change (w ++ w) +> (v ^ m +> default) = (w ++ (w ++ [])) +> (v ^ m +> default)
    simp only [List.append_nil]
  rwa [h_lhs, h_rhs] at h

lemma rule_empty : SideRLs target_tm ([(hR, hL)] ^ 4) (RC0 w u z 0 0 0) (RC2 w u 1 0) :=
  sideRLs_c_spec target_tm (hs := [(hR, hL)] ^ 4) (r := z) (r' := w ++ w) (T := 200)
    (by decide)

lemma seg_w_grow : SegRLs target_tm ([(hR, hL)] ^ 2) [hu] w w :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma rule_grow (m : ℕ) :
    SideRLs target_tm ([(hR, hL)] ^ 2) (RC2 w u 0 m) (RC2 w u 0 (1 + m)) :=
  seg_w_grow.sideRLs_concat (side_u_pow m)

lemma seg_reset_d1 : SegRLs (flipTM target_tm) [(hL, hrstL)] [(hL, hrstL)] d₁ d₀ :=
  segRLs_c_spec (flipTM target_tm) (T := 200) (by decide)

lemma side_reset_dh : SideRLs (flipTM target_tm) [(hL, hrstL)] dh dh :=
  sideRLs_c_spec (flipTM target_tm) (hs := [(hL, hrstL)]) (r := [1]) (r' := [1])
    (T := 200) (by decide)

lemma side_reset_d1_pow (n : ℕ) :
    SideRLs (flipTM target_tm) [(hL, hrstL)] (d₁ ^ n +> dh) (d₀ ^ n +> dh) := by
  induction n with
  | zero =>
    simpa [pow_zero_list] using side_reset_dh
  | succ n ih =>
    have h := seg_reset_d1.sideRLs_concat ih
    rw [pow_succ_list d₁ n, pow_succ_list d₀ n, ListBlank.append_assoc, ListBlank.append_assoc]
    exact h

lemma reset_tail (L r : ListBlank (Fin 2)) :
    (toDHCfg (hrstL, .right) (d₀ +> L) (w +> r)) [target_tm]⊢*
      (toDHCfg (hR, .right) (d₀ +> (d₁ +> L)) (z +> r)) := by
  have h₁ := steps_spec target_tm 20 ⟨[0, 1, 0], [1, 0, 0], C, .right⟩
    (x' := ⟨[0, 1, 0, 1, 0, 1], [], E, .left⟩) (by decide) (d₀ +> L) ([1, 0] +> r)
  have h₂ := steps_spec target_tm 30 ⟨[0, 1, 0, 1, 0], d₀, E, .left⟩
    (x' := ⟨[0, 0, 0, 1, 0, 1, 0, 1, 0], [], B, .right⟩) (by decide) L (z +> r)
  simp only [toCfg, toDHCfg, w, z, d₀, d₁,
    ListBlank.append_nil, ListBlank.append_cons] at h₁ h₂ ⊢
  exact stepStar_trans h₁ h₂

lemma rule_reset (k : ℕ) (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) (d₁ ^ (1 + k) +> dh) (w +> r)) [target_tm]⊢*
      (toDHCfg (hR, .right) (d₀ +> (d₁ +> (d₀ ^ k +> dh))) (z +> r)) := by
  have h₂ := stepPlus_stepStar ((side_reset_d1_pow (1 + k)).elim_single_left (w +> r))
  have h_eq : d₀ ^ (1 + k) +> dh = d₀ +> (d₀ ^ k +> dh) := by
    have hk : 1 + k = k + 1 := by omega
    rw [hk, pow_succ_list, ListBlank.append_assoc]
  rw [h_eq] at h₂
  exact stepStar_trans h₂ (reset_tail (d₀ ^ k +> dh) r)

lemma rule_zero : SegRL (flipTM target_tm) hL hR d₀ d₁ := fun l r => by
  have h := steps1_spec_true (flipTM target_tm) 50 ⟨[0], d₀, hL.1, .right⟩
    (x' := ⟨[0] ++ d₁, [], hR.1, .left⟩) (by decide) l r
  simpa [toCfg, toDHCfg, ListBlank.append_assoc] using h

lemma rule_carry : SegRR (flipTM target_tm) hL hL d₁ d₁' := fun l r => by
  have h := steps_spec (flipTM target_tm) 50 ⟨[0], d₁, hL.1, .right⟩
    (x' := ⟨[0] ++ d₁', [], hL.1, .right⟩) (by decide) l r
  simpa [toCfg, toDHCfg, ListBlank.append_assoc] using h

lemma rule_return : SegLL (flipTM target_tm) hR hR d₁' d₀ := fun l r => by
  have h := steps_spec (flipTM target_tm) 50 ⟨[0], d₁', hR.1, .left⟩
    (x' := ⟨[0] ++ d₀, [], hR.1, .left⟩) (by decide) l r
  simpa [toCfg, toDHCfg, ListBlank.append_assoc] using h

lemma sbc_rules : Longitudinal.SBC.Rules target_tm hR hL w u v z d₀ d₁ d₁' dh where
  rule_wall := rule_wall
  rule_pair := rule_pair
  rule_R := rule_R
  rule_U := rule_U
  rule_odd := rule_odd
  rule_V := rule_V
  rule_empty := rule_empty
  rule_grow := rule_grow
  rule_reset := rule_reset
  rule_zero := rule_zero
  rule_carry := rule_carry
  rule_return := rule_return

lemma init_to_step147 :
    (init []) [target_tm]⊢*
      (([0] +> default) <{{E}}
        ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] +> ([0, 0, 0, 1] +> default))) := by
  have h := steps_spec target_tm 200
    ⟨[0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], A, .right⟩
    (x' := ⟨[0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1], [], E, .left⟩)
    (by decide) default default
  have h_l : ([0, 0, 0, 0, 0] : List (Fin 2)) +> default = default :=
    all0_spec (by decide)
  have h_r : ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List (Fin 2)) +> default = default :=
    all0_spec (by decide)
  have h_0 : ([0] : List (Fin 2)) +> default = default :=
    all0_spec (by decide)
  have h_init : (default {{A}}> default : Cfg (Fin 2) (Fin 6)) = init [] := rfl
  dsimp only [toCfg] at h
  rw [h_l, h_r, ListBlank.append_nil, h_init] at h
  rw [h_0]
  simpa [ListBlank.append_cons, ListBlank.append_nil] using h

lemma step147_to_step186 :
    (([0] +> default) <{{E}}
      ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] +> ([0, 0, 0, 1] +> default)))
      [target_tm]⊢*
    (CfgAt hR d₀ d₁ dh 1 ([1, 0, 0, 1] +> default)) := by
  have h₁ := steps_spec target_tm 200
    ⟨[0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0], [0], E, .left⟩
    (x' := ⟨[0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1], [], B, .right⟩) (by decide)
    default ([0, 0, 0, 1] +> default)
  have h₂ := steps_spec target_tm 200
    ⟨[0, 0, 0, 1, 0], [0, 0], B, .right⟩
    (x' := ⟨[0, 1, 0, 1, 0, 1, 0], [], E, .left⟩) (by decide)
    ([0, 0, 1, 0, 0, 0, 1, 0, 1] +> default) ([0, 1] +> default)
  have h₃ := steps_spec target_tm 200
    ⟨[0, 1, 0, 1, 0], [0], E, .left⟩
    (x' := ⟨[0, 0, 0, 1, 0, 1], [], B, .right⟩) (by decide)
    ([0, 1, 0, 0, 0, 1, 0, 1] +> default) ([1, 0, 0, 1] +> default)
  simp only [toCfg, CfgAt, toDHCfg, d₀, d₁, dh, pow_zero_list, pow_succ_list,
    List.cons_append, List.nil_append, ListBlank.append_nil, ListBlank.append_cons] at h₁ h₂ h₃ ⊢
  exact stepStar_trans h₁ (stepStar_trans h₂ h₃)

lemma round1 :
    (CfgAt hR d₀ d₁ dh 1 ([1, 0, 0, 1] +> default)) [target_tm]⊢⁺
      (CfgAt hR d₀ d₁ dh 2 ([1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] +> default)) := by
  have hG : Longitudinal.SBC.G target_tm hR hL 6
      ([1, 0, 0, 1] +> default)
      (w +> ([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] +> default)) := by
    have h := sideRLs_c_spec target_tm (hs := [(hR, hL)] ^ 6)
      (r := [1, 0, 0, 1]) (r' := w ++ [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]) (T := 200) (by decide)
    rwa [ListBlank.append_assoc] at h
  simpa [CfgAt, z, ListBlank.append_cons, ListBlank.append_nil] using
    Longitudinal.SBC.round sbc_rules (n := 6)
      (s := [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] +> default) (by decide) hG

lemma round2 :
    (CfgAt hR d₀ d₁ dh 2 ([1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] +> default))
      [target_tm]⊢⁺
    (CfgAt hR d₀ d₁ dh 3
      ([1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1] +> default)) := by
  have hG : Longitudinal.SBC.G target_tm hR hL 14
      ([1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] +> default)
      (w +> ([1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1] +> default)) := by
    have h := sideRLs_c_spec target_tm (hs := [(hR, hL)] ^ 14)
      (r := [1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
      (r' := w ++ [1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1]) (T := 200) (by decide)
    rwa [ListBlank.append_assoc] at h
  simpa [CfgAt, z, ListBlank.append_cons, ListBlank.append_nil] using
    Longitudinal.SBC.round sbc_rules (n := 14)
      (s := [1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1] +> default) (by decide) hG

lemma round3 :
    (CfgAt hR d₀ d₁ dh 3
      ([1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1] +> default)) [target_tm]⊢⁺
    (S hR w u z d₀ d₁ dh 4 6 5) := by
  have hG : Longitudinal.SBC.G target_tm hR hL 30
      ([1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1] +> default)
      (w +> (w ^ 6 +> (u ^ 5 +> default))) := by
    have h := sideRLs_c_spec target_tm (hs := [(hR, hL)] ^ 30)
      (r := [1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1])
      (r' := w ++ (w ^ 6 ++ u ^ 5)) (T := 400) (by decide)
    rwa [ListBlank.append_assoc, ListBlank.append_assoc] at h
  exact Longitudinal.SBC.round sbc_rules (n := 30) (s := w ^ 6 +> (u ^ 5 +> default))
    (by decide) hG

lemma init_reaches : (init []) [target_tm]⊢* (S hR w u z d₀ d₁ dh 4 6 5) :=
  stepStar_trans init_to_step147
    (stepStar_trans step147_to_step186
      (stepPlus_stepStar (stepPlus_trans round1 (stepPlus_trans round2 round3))))

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  Longitudinal.SBC.does_not_halt sbc_rules init_reaches (by decide) (by decide)

end BusyBeaver.M_1RBHHH_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA
