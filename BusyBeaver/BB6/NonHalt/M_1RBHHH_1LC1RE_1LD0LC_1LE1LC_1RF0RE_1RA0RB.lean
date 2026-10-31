/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic
import BusyBeaver.Longitudinal

/-!
# Busy Beaver Machine `1RB---_1LC1RE_1LD0LC_1LE1LC_1RF0RE_1RA0RB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`, `BusyBeaver.Longitudinal`
and defines `target_tm` for `1RB---_1LC1RE_1LD0LC_1LE1LC_1RF0RE_1RA0RB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1LC1RE_1LD0LC_1LE1LC_1RF0RE_1RA0RB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_1LC1RE_1LD0LC_1LE1LC_1RF0RE_1RA0RB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Longitudinal

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

/-- `BLECv5.v:TM4.tm` is `flipTM target_tm` (`1LB---_1RC1LE_1RD0RC_1RE1RC_1LF0LE_1LA0LB`).
Under the state relabeling `rename` (`A↦4, B↦5, C↦0, D↦1, E↦2, F↦3`), `tm` is identical
to `BLECv2.v:TM4.tm` (`1LB0LA_1LC0LD_1LD---_1RE1LA_1RF0RE_1RA1RE`). -/
abbrev tm : Machine (Fin 2) (Fin 6) := flipTM target_tm

abbrev A : Fin 6 := 4
abbrev B : Fin 6 := 5
abbrev C : Fin 6 := 0
abbrev D : Fin 6 := 1
abbrev E : Fin 6 := 2
abbrev F : Fin 6 := 3

def runSteps (M : Machine (Fin 2) (Fin 6)) :
    ℕ → BoundedConfig.BCfg (Fin 2) (Fin 6) → Option (BoundedConfig.BCfg (Fin 2) (Fin 6))
  | 0, x => some x
  | n + 1, x => (BoundedConfig.step M x).bind (runSteps M n)

lemma runSteps_spec (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (x x' : BoundedConfig.BCfg (Fin 2) (Fin 6))
    (h : runSteps M n x = some x') (l₀ r₀ : zB) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢* (BoundedConfig.toCfg x' l₀ r₀) := by
  induction n generalizing x with
  | zero => cases h; exact stepStar_refl M _
  | succ n ih =>
    dsimp [runSteps] at h
    rcases hst : BoundedConfig.step M x with _ | y <;> rw [hst] at h
    · cases h
    · exact stepStar_trans ⟨1, BoundedConfig.step_spec M x hst l₀ r₀⟩ (ih y h)

lemma runSteps1_spec (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (x x' : BoundedConfig.BCfg (Fin 2) (Fin 6))
    (h : runSteps M (n + 1) x = some x') (l₀ r₀ : zB) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢⁺ (BoundedConfig.toCfg x' l₀ r₀) := by
  dsimp [runSteps] at h
  rcases hst : BoundedConfig.step M x with _ | y <;> rw [hst] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, BoundedConfig.step_spec M x hst l₀ r₀⟩
      (runSteps_spec M n y x' h l₀ r₀)

lemma stepStar_congr {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [tm]⊢* c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') :
    c₁' [tm]⊢* c₂' := by
  subst hc₁ hc₂; exact h

lemma stepPlus_congr {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [tm]⊢⁺ c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') :
    c₁' [tm]⊢⁺ c₂' := by
  subst hc₁ hc₂; exact h

lemma SideRLs.congr {M : Machine (Fin 2) (Fin 6)}
    {ls ls' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r₁ r₁' r₂ r₂' : zB}
    (h : SideRLs M ls r₁ r₂) (hls : ls = ls') (hr₁ : r₁ = r₁') (hr₂ : r₂ = r₂') :
    SideRLs M ls' r₁' r₂' := by
  subst hls hr₁ hr₂; exact h

lemma segRLs_addmul'' {M : Machine (Fin 2) (Fin 6)}
    {h : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {a x b : ℕ} {w₁ w₂ : zF}
    (hb : SegRLs M (h ^ b) [] w₁ w₂)
    (ha : SegRLs M (h ^ a) h w₂ w₂) :
    SegRLs M (h ^ (x * a + b)) (h ^ x) w₁ w₂ := by
  simpa only [Nat.add_zero] using SegRLs.addmul (c := 0) hb ha

-- ============================================================================
-- Section 1: Right/Left Counters & Base Transitions (`BLECv2.v:910-1391`)
-- ============================================================================

inductive Tp where
  | t0 | t1 | t2 | t3 | t4 | t5 | t6 | t7
  deriving DecidableEq, Repr

def rhList : Tp → zF
  | .t0 => [1, 0, 1]
  | .t1 => [0, 0, 0, 0, 1]
  | .t2 => [1, 0, 1, 0, 1, 0, 1]
  | .t3 => [1, 0, 1, 0, 0, 0, 1, 0, 1]
  | .t4 => [0, 0, 0, 0, 1, 1, 0, 1]
  | .t5 => [0, 0, 0, 0, 1, 0, 0, 1, 0, 1]
  | .t6 => [1, 0, 1, 0, 0, 0, 0, 0, 1]
  | .t7 => [0, 0, 0, 0, 1, 0, 0, 1]

def rh (t : Tp) : zB := rhList t +> default

def nxt : Tp → Tp
  | .t0 => .t1
  | .t1 => .t2
  | .t2 => .t3
  | .t3 => .t4
  | .t4 => .t5
  | .t5 => .t6
  | .t6 => .t7
  | .t7 => .t0

def offset : Tp → ℕ
  | .t0 => 0
  | .t1 => 1
  | .t2 => 0
  | .t3 => 0
  | .t4 => 1
  | .t5 => 1
  | .t6 => 0
  | .t7 => 1

lemma offset_le_one (t : Tp) : offset t ≤ 1 := by
  cases t <;> decide

abbrev d0 : zF := [0, 0, 1, 1, 1, 1]
abbrev d1 : zF := [0, 0, 0, 1, 1, 1]
abbrev d2 : zF := [1, 0, 1, 1, 1, 1]
abbrev w : zF := [0, 1, 1, 1, 1]
abbrev v : zF := [0, 0, 0, 1, 1]
abbrev z0 : zF := [0, 0, 0, 0]
abbrev z1 : zF := [0, 0, 0, 1]

inductive RC : ℕ → Tp → zB → Prop where
  | RC_0 (t : Tp) : RC 0 t (d0 +> rh t)
  | RC_1 (t : Tp) : RC 1 t (d1 +> rh t)
  | RC_2 (t : Tp) : RC 2 t (d2 +> rh t)
  | RC_3 (n : ℕ) (t : Tp) (r : zB) :
      RC (n * 2 + (1 - offset t)) (nxt t) r →
      RC (n * 3 + 3) t (d0 +> (w ^ ((n + 1 + offset t) / 3) +> r))
  | RC_4 (n : ℕ) (t : Tp) (r : zB) :
      RC (n * 2 + (1 - offset t)) (nxt t) r →
      RC (n * 3 + 4) t (d1 +> (w ^ ((n + 1 + offset t) / 3) +> r))
  | RC_5 (n : ℕ) (t : Tp) (r : zB) :
      RC (n * 2 + (1 - offset t)) (nxt t) r →
      RC (n * 3 + 5) t (d2 +> (w ^ ((n + 1 + offset t) / 3) +> r))

lemma RC.congr {n n' : ℕ} {t t' : Tp} {r r' : zB}
    (h : RC n t r) (hn : n = n') (ht : t = t') (hr : r = r') : RC n' t' r' := by
  subst hn ht hr; exact h

private lemma rinc_d0 (l r : zB) :
    (l {{E}}> (d0 +> r)) [tm]⊢⁺ (l <{{A}} (d1 +> r)) := by
  have h := runSteps1_spec tm 4 ⟨[], d0, E, .right⟩ ⟨d1, [], A, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma rinc_d1 (l r : zB) :
    (l {{E}}> (d1 +> r)) [tm]⊢⁺ (l <{{A}} (d2 +> r)) := by
  have h := runSteps1_spec tm 4 ⟨[], d1, E, .right⟩ ⟨d2, [], A, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma shift_E_w_step (l r : zB) :
    (l {{E}}> (w +> r)) [tm]⊢* ((v +> l) {{E}}> r) := by
  have h := runSteps_spec tm 5 ⟨[], w, E, .right⟩ ⟨v, [], E, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma shift_E_w (k : ℕ) (l r : zB) :
    (l {{E}}> (w ^ k +> r)) [tm]⊢* ((v ^ k +> l) {{E}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_E_w_step l (w ^ k +> r)) ?_
    refine stepStar_congr (ih (v +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

private lemma shift_A_v_step (l r : zB) :
    ((v +> l) <{{A}} r) [tm]⊢* (l <{{A}} (w +> r)) := by
  have h := runSteps_spec tm 5 ⟨[], v, A, .left⟩ ⟨w, [], A, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma shift_A_v (k : ℕ) (l r : zB) :
    ((v ^ k +> l) <{{A}} r) [tm]⊢* (l <{{A}} (w ^ k +> r)) := by
  induction k generalizing r with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_A_v_step (v ^ k +> l) r) ?_
    refine stepStar_congr (ih (w +> r)) rfl ?_
    rw [← append_assoc (w ^ k) w r, ← pow_succ_list']

private lemma pow_v_comm (k : ℕ) (l : zB) :
    v ^ (k + 1) +> l = v +> (v ^ k +> l) := by
  rw [pow_succ_list, append_assoc]

private lemma enter_d2_base (l r : zB) :
    ((v +> l) {{E}}> (d2 +> r)) [tm]⊢* ((v +> (([0] ++ v) +> l)) {{E}}> r) := by
  have h := runSteps_spec tm 6 ⟨v, d2, E, .right⟩ ⟨v ++ ([0] ++ v), [], E, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

private lemma enter_d2 (k : ℕ) (l r : zB) :
    ((v +> l) {{E}}> (d2 +> (w ^ k +> r))) [tm]⊢*
      ((v ^ (k + 1) +> (([0] ++ v) +> l)) {{E}}> r) := by
  refine stepStar_trans (enter_d2_base l (w ^ k +> r)) ?_
  refine stepStar_congr (shift_E_w k (v +> (([0] ++ v) +> l)) r) rfl ?_
  rw [← append_assoc, ← pow_succ_list']

private lemma bounce_mid_base (l r : zB) :
    ((([0] ++ v) +> l) <{{A}} r) [tm]⊢* ((d1 +> l) {{E}}> r) := by
  have h := runSteps_spec tm 7 ⟨[], [0] ++ v, A, .left⟩ ⟨d1, [], E, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma bounce_mid (k : ℕ) (l r : zB) :
    ((v ^ k +> (([0] ++ v) +> l)) <{{A}} r) [tm]⊢*
      ((v ^ k +> (d1 +> l)) {{E}}> r) := by
  refine stepStar_trans (shift_A_v k (([0] ++ v) +> l) r) ?_
  refine stepStar_trans (bounce_mid_base l (w ^ k +> r)) ?_
  exact shift_E_w k (d1 +> l) r

private lemma exit_d0_base (l r : zB) :
    ((d1 +> l) <{{A}} r) [tm]⊢* (l <{{A}} (d0 +> r)) := by
  have h := runSteps_spec tm 6 ⟨[], d1, A, .left⟩ ⟨d0, [], A, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma exit_d0 (k : ℕ) (l r : zB) :
    ((v ^ k +> (d1 +> l)) <{{A}} r) [tm]⊢*
      (l <{{A}} (d0 +> (w ^ k +> r))) := by
  refine stepStar_trans (shift_A_v k (d1 +> l) r) ?_
  exact exit_d0_base l (w ^ k +> r)

private lemma rinc_rc2 (t : Tp) :
    ∃ r', RC 3 t r' ∧ ∀ l, ((v +> l) {{E}}> (d2 +> rh t)) [tm]⊢⁺ (l <{{A}} r') := by
  cases t
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t0) / 3) +> (d1 +> rh .t1)),
      RC.RC_3 0 .t0 _ (RC.RC_1 .t1), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t0) (r' := d0 ++ d1 ++ rhList .t1) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t0) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t1) / 3) +> (d0 +> rh .t2)),
      RC.RC_3 0 .t1 _ (RC.RC_0 .t2), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t1) (r' := d0 ++ d0 ++ rhList .t2) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t1) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t2) / 3) +> (d1 +> rh .t3)),
      RC.RC_3 0 .t2 _ (RC.RC_1 .t3), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t2) (r' := d0 ++ d1 ++ rhList .t3) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t2) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t3) / 3) +> (d1 +> rh .t4)),
      RC.RC_3 0 .t3 _ (RC.RC_1 .t4), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t3) (r' := d0 ++ d1 ++ rhList .t4) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t3) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t4) / 3) +> (d0 +> rh .t5)),
      RC.RC_3 0 .t4 _ (RC.RC_0 .t5), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t4) (r' := d0 ++ d0 ++ rhList .t5) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t4) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t5) / 3) +> (d0 +> rh .t6)),
      RC.RC_3 0 .t5 _ (RC.RC_0 .t6), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t5) (r' := d0 ++ d0 ++ rhList .t6) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t5) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t6) / 3) +> (d1 +> rh .t7)),
      RC.RC_3 0 .t6 _ (RC.RC_1 .t7), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t6) (r' := d0 ++ d1 ++ rhList .t7) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t6) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h
  · refine ⟨d0 +> (w ^ ((0 + 1 + offset .t7) / 3) +> (d0 +> rh .t0)),
      RC.RC_3 0 .t7 _ (RC.RC_0 .t0), fun l => ?_⟩
    have h := (BoundedConfig.sideRLs_c_spec tm (hs := [((E, v), (A, []))])
      (r := d2 ++ rhList .t7) (r' := d0 ++ d0 ++ rhList .t0) (T := 100) (by decide)).elim_single l
    rw [show (0 + 1 + offset .t7) / 3 = 0 by rfl, pow_zero_list, append_nil]
    simpa only [toDHCfg, rh, append_nil, append_assoc] using h

lemma RInc (n : ℕ) (t : Tp) (r : zB) (h : RC n t r) :
    ∃ r', RC (n + 1) t r' ∧
      (n % 3 ≠ 2 → ∀ l, (l {{E}}> r) [tm]⊢⁺ (l <{{A}} r')) ∧
      (n % 3 = 2 → ∀ l, ((v +> l) {{E}}> r) [tm]⊢⁺ (l <{{A}} r')) := by
  induction n using Nat.strongRecOn generalizing t r with
  | ind n ih =>
    cases h with
    | RC_0 t =>
      exact ⟨d1 +> rh t, .RC_1 t, fun _ l => rinc_d0 l (rh t), fun hm => by omega⟩
    | RC_1 t =>
      exact ⟨d2 +> rh t, .RC_2 t, fun _ l => rinc_d1 l (rh t), fun hm => by omega⟩
    | RC_2 t =>
      rcases rinc_rc2 t with ⟨r', hr', hstep⟩
      exact ⟨r', hr', fun hm => by omega, fun _ => hstep⟩
    | RC_3 n0 t r0 h0 =>
      exact ⟨_, .RC_4 n0 t r0 h0, fun _ l => rinc_d0 l _, fun hm => by omega⟩
    | RC_4 n0 t r0 h0 =>
      exact ⟨_, .RC_5 n0 t r0 h0, fun _ l => rinc_d1 l _, fun hm => by omega⟩
    | RC_5 n0 t r0 h0 =>
      have hoff := offset_le_one t
      rcases ih (n0 * 2 + (1 - offset t)) (by omega) (nxt t) r0 h0 with ⟨r1, h1, i2, i3⟩
      rcases ih (n0 * 2 + (1 - offset t) + 1) (by omega) (nxt t) r1 h1 with ⟨r2, h2, i5, i6⟩
      have h2' : RC ((n0 + 1) * 2 + (1 - offset t)) (nxt t) r2 :=
        h2.congr (by omega) rfl rfl
      refine ⟨d0 +> (w ^ (((n0 + 1) + 1 + offset t) / 3) +> r2),
        (RC.RC_3 (n0 + 1) t r2 h2').congr (by omega) rfl rfl,
        fun hm => by omega, fun _ l => ?_⟩
      set m := (n0 + 1 + offset t) / 3
      have h_enter := enter_d2 m l r0
      by_cases hm1 : (n0 * 2 + (1 - offset t)) % 3 = 2
      · have h_mid1 : ((v ^ (m + 1) +> (([0] ++ v) +> l)) {{E}}> r0) [tm]⊢⁺
            ((v ^ m +> (([0] ++ v) +> l)) <{{A}} r1) := by
          rw [pow_v_comm m]
          exact i3 hm1 _
        have h_bm := bounce_mid m l r1
        have hm2 : (n0 * 2 + (1 - offset t) + 1) % 3 ≠ 2 := by omega
        have h_mid2 := i5 hm2 (v ^ m +> (d1 +> l))
        have hm_eq : ((n0 + 1) + 1 + offset t) / 3 = m := by omega
        rw [hm_eq]
        exact stepStar_stepPlus_trans h_enter
          (stepPlus_stepStar_trans h_mid1
            (stepStar_trans h_bm
              (stepPlus_to_stepStar (stepPlus_stepStar_trans h_mid2 (exit_d0 m l r2)))))
      · have h_mid1 := i2 hm1 (v ^ (m + 1) +> (([0] ++ v) +> l))
        have h_bm := bounce_mid (m + 1) l r1
        by_cases hm2 : (n0 * 2 + (1 - offset t) + 1) % 3 = 2
        · have h_mid2 : ((v ^ (m + 1) +> (d1 +> l)) {{E}}> r1) [tm]⊢⁺
              ((v ^ m +> (d1 +> l)) <{{A}} r2) := by
            rw [pow_v_comm m]
            exact i6 hm2 _
          have hm_eq : ((n0 + 1) + 1 + offset t) / 3 = m := by omega
          rw [hm_eq]
          exact stepStar_stepPlus_trans h_enter
            (stepPlus_stepStar_trans h_mid1
              (stepStar_trans h_bm
                (stepPlus_to_stepStar (stepPlus_stepStar_trans h_mid2 (exit_d0 m l r2)))))
        · have h_mid2 := i5 hm2 (v ^ (m + 1) +> (d1 +> l))
          have hm_eq : ((n0 + 1) + 1 + offset t) / 3 = m + 1 := by omega
          rw [hm_eq]
          exact stepStar_stepPlus_trans h_enter
            (stepPlus_stepStar_trans h_mid1
              (stepStar_trans h_bm
                (stepPlus_to_stepStar (stepPlus_stepStar_trans h_mid2 (exit_d0 (m + 1) l r2)))))

abbrev hR : DH0 (Fin 2) (Fin 6) := (E, [])
abbrev hL : DH0 (Fin 2) (Fin 6) := (A, [])
abbrev hRL : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [(hR, hL)]
abbrev hLR : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [(hL, hR)]

private lemma sideRL_w_mod2 (m : ℕ) {r r0 : zB}
    (hstep : ∀ l, ((v +> l) {{E}}> r) [tm]⊢⁺ (l <{{A}} r0)) :
    SideRL tm hR hL (w +> (w ^ m +> r)) (w ^ m +> r0) := by
  intro l
  dsimp [toDHCfg]
  refine stepStar_stepPlus_trans (shift_E_w_step l (w ^ m +> r)) ?_
  refine stepStar_stepPlus_trans (shift_E_w m (v +> l) r) ?_
  have hv : v ^ m +> (v +> l) = v +> (v ^ m +> l) := by
    rw [← append_assoc, ← pow_succ_list', pow_succ_list, append_assoc]
  rw [hv]
  exact stepPlus_stepStar_trans (hstep (v ^ m +> l)) (shift_A_v m l r0)

private lemma sideRL_w_ne2 (m : ℕ) {r r0 : zB}
    (hstep : ∀ l, (l {{E}}> r) [tm]⊢⁺ (l <{{A}} r0)) :
    SideRL tm hR hL (w ^ m +> r) (w ^ m +> r0) := by
  intro l
  dsimp [toDHCfg]
  exact stepStar_stepPlus_trans (shift_E_w m l r)
    (stepPlus_stepStar_trans (hstep (v ^ m +> l)) (shift_A_v m l r0))

lemma RIncs2 (m n : ℕ) (t : Tp) (r : zB) (h : RC n t r) (hm : n % 3 = 2) :
    ∃ r', RC (n + m * 3) t r' ∧ SideRLs tm (hRL ^ (m * 3)) (w ^ m +> r) r' := by
  induction m generalizing n t r with
  | zero =>
    exact ⟨r, h, .nil r⟩
  | succ m ih =>
    rcases RInc n t r h with ⟨r0, h0, _, i2⟩
    rcases RInc (n + 1) t r0 h0 with ⟨r1, h1, i4, _⟩
    rcases RInc (n + 2) t r1 h1 with ⟨r2, h2, i6, _⟩
    rcases ih (n + 3) t r2 h2 (by omega) with ⟨r', hr', hside⟩
    refine ⟨r', hr'.congr (by omega) rfl rfl, ?_⟩
    have hm_pow : hRL ^ ((m + 1) * 3) = (hR, hL) :: (hR, hL) :: (hR, hL) :: (hRL ^ (m * 3)) := by
      have : (m + 1) * 3 = 3 + m * 3 := by omega
      rw [this, pow_add_list]; rfl
    rw [hm_pow, pow_succ_list, append_assoc]
    exact .cons (sideRL_w_mod2 m (i2 hm))
      (.cons (sideRL_w_ne2 m (i4 (by omega)))
        (.cons (sideRL_w_ne2 m (i6 (by omega))) hside))

lemma RIncs1 (m n : ℕ) (t : Tp) (r : zB) (h : RC n t r) (hm : n % 3 = 1) :
    ∃ r', RC (n + m * 3 + 1) t r' ∧ SideRLs tm (hRL ^ (m * 3 + 1)) (w ^ m +> r) r' := by
  rcases RInc n t r h with ⟨r0, h0, i2, _⟩
  rcases RIncs2 m (n + 1) t r0 h0 (by omega) with ⟨r', hr', hside⟩
  refine ⟨r', hr'.congr (by omega) rfl rfl, ?_⟩
  have hm_pow : hRL ^ (m * 3 + 1) = (hR, hL) :: (hRL ^ (m * 3)) := by
    rw [Nat.add_comm (m * 3) 1, pow_add_list]; rfl
  rw [hm_pow]
  exact .cons (sideRL_w_ne2 m (i2 (by omega))) hside

lemma RIncs0 (m n : ℕ) (t : Tp) (r : zB) (h : RC n t r) (hm : n % 3 = 0) :
    ∃ r', RC (n + m * 3 + 2) t r' ∧ SideRLs tm (hRL ^ (m * 3 + 2)) (w ^ m +> r) r' := by
  rcases RInc n t r h with ⟨r0, h0, i2, _⟩
  rcases RIncs1 m (n + 1) t r0 h0 (by omega) with ⟨r', hr', hside⟩
  refine ⟨r', hr'.congr (by omega) rfl rfl, ?_⟩
  have hm_pow : hRL ^ (m * 3 + 2) = (hR, hL) :: (hRL ^ (m * 3 + 1)) := by
    have : m * 3 + 2 = 1 + (m * 3 + 1) := by omega
    rw [this, pow_add_list]; rfl
  rw [hm_pow]
  exact .cons (sideRL_w_ne2 m (i2 (by omega))) hside

lemma RIncs (m n : ℕ) (t : Tp) (r : zB) (h : RC n t r) :
    ∃ r', RC (n + m * 3 + (2 - n % 3)) t r' ∧
      SideRLs tm (hRL ^ (m * 3 + (2 - n % 3))) (w ^ m +> r) r' := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with hm | hm | hm
  · simpa [hm] using RIncs0 m n t r h hm
  · simpa [hm] using RIncs1 m n t r h hm
  · simpa [hm] using RIncs2 m n t r h hm

inductive LC : ℕ → List ℕ → zB → Prop where
  | LC_0 : LC 0 [] default
  | LC_1 (n : ℕ) (l : zB) : LC n [] l → LC (n * 2 + 1) [] (z1 +> l)
  | LC_2 (n : ℕ) (l : zB) : LC (n + 1) [] l → LC (n * 2 + 2) [] (z0 +> l)
  | LC_1' (n h : ℕ) (t : List ℕ) (l : zB) :
      LC n (h :: t) l → LC (n * 2 + 1) ((h + 1) :: t) (z1 +> l)
  | LC_0' (n h : ℕ) (t : List ℕ) (l : zB) :
      LC n (h :: t) l → LC (n * 2) ((h + 1) :: t) (z0 +> l)
  | LC_w (n : ℕ) (ls : List ℕ) (l : zB) :
      LC n ls l → LC n (0 :: ls) (v +> l)

lemma LC.congr {n n' : ℕ} {ls ls' : List ℕ} {l l' : zB}
    (h : LC n ls l) (hn : n = n') (hls : ls = ls') (hl : l = l') : LC n' ls' l' := by
  subst hn hls hl; exact h

private lemma linc_z0 (l r : zB) :
    ((z0 +> l) <{{A}} r) [tm]⊢⁺ ((z1 +> l) {{E}}> r) := by
  have h := runSteps1_spec tm 6 ⟨[], z0, A, .left⟩ ⟨z1, [], E, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma linc_z1_left (l r : zB) :
    ((z1 +> l) <{{A}} r) [tm]⊢* (l <{{A}} ([1, 1, 1, 1] +> r)) := by
  have h := runSteps_spec tm 4 ⟨[], z1, A, .left⟩ ⟨[1, 1, 1, 1], [], A, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

private lemma linc_z1_right (l r : zB) :
    (l {{E}}> ([1, 1, 1, 1] +> r)) [tm]⊢* ((z0 +> l) {{E}}> r) := by
  have h := runSteps_spec tm 4 ⟨[], [1, 1, 1, 1], E, .right⟩ ⟨z0, [], E, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

lemma LInc (n : ℕ) (ls : List ℕ) (l : zB) (h : LC n ls l) :
    ∃ l', LC (n + 1) ls l' ∧ ∀ r, (l <{{A}} r) [tm]⊢⁺ (l' {{E}}> r) := by
  induction h with
  | LC_0 =>
    refine ⟨z1 +> default, LC.LC_1 0 default LC.LC_0, fun r => ?_⟩
    have hd : z0 +> (default : zB) = default := BoundedConfig.all0_spec (by decide)
    simpa only [hd] using linc_z0 default r
  | LC_1 n l h ih =>
    rcases ih with ⟨l', hl', hstep⟩
    refine ⟨z0 +> l', (LC.LC_2 n l' hl').congr (by omega) rfl rfl, fun r => ?_⟩
    exact stepStar_stepPlus_trans (linc_z1_left l r)
      (stepPlus_stepStar_trans (hstep ([1, 1, 1, 1] +> r)) (linc_z1_right l' r))
  | LC_2 n l h _ =>
    exact ⟨z1 +> l, (LC.LC_1 (n + 1) l h).congr (by omega) rfl rfl, fun r => linc_z0 l r⟩
  | LC_1' n h t l hlc ih =>
    rcases ih with ⟨l', hl', hstep⟩
    refine ⟨z0 +> l', (LC.LC_0' (n + 1) h t l' hl').congr (by omega) rfl rfl, fun r => ?_⟩
    exact stepStar_stepPlus_trans (linc_z1_left l r)
      (stepPlus_stepStar_trans (hstep ([1, 1, 1, 1] +> r)) (linc_z1_right l' r))
  | LC_0' n h t l hlc _ =>
    exact ⟨z1 +> l, LC.LC_1' n h t l hlc, fun r => linc_z0 l r⟩
  | LC_w n ls l hlc ih =>
    rcases ih with ⟨l', hl', hstep⟩
    refine ⟨v +> l', LC.LC_w (n + 1) ls l' hl', fun r => ?_⟩
    exact stepStar_stepPlus_trans (shift_A_v_step l r)
      (stepPlus_stepStar_trans (hstep (w +> r)) (shift_E_w_step l' r))

lemma LIncs (m n : ℕ) (ls : List ℕ) (l : zB) (h : LC n ls l) :
    ∃ l', LC (n + m) ls l' ∧ SideRLs (flipTM tm) (hLR ^ m) l l' := by
  induction m generalizing n l with
  | zero =>
    exact ⟨l, h, .nil l⟩
  | succ m ih =>
    rcases LInc n ls l h with ⟨l0, hl0, hstep⟩
    rcases ih (n + 1) l0 hl0 with ⟨l', hl', hside⟩
    refine ⟨l', hl'.congr (by omega) rfl rfl, ?_⟩
    have hm_pow : hLR ^ (m + 1) = (hL, hR) :: (hLR ^ m) := rfl
    rw [hm_pow]
    refine .cons (fun r => ?_) hside
    exact toDHCfg_stepPlus_flip (h₁ := hL) (h₂ := hR) (d₁ := .left) (d₂ := .right) (hstep r)

private lemma rov_enter (k : ℕ) (l r : zB) :
    (l {{E}}> (d2 +> (w ^ k +> r))) [tm]⊢*
      ((v ^ (k + 1) +> ([0] +> l)) {{E}}> r) := by
  have h1 : (l {{E}}> (d2 +> (w ^ k +> r))) [tm]⊢*
      ((v +> ([0] +> l)) {{E}}> (w ^ k +> r)) := by
    have h := runSteps_spec tm 6 ⟨[], d2, E, .right⟩ ⟨v ++ [0], [], E, .right⟩ (by decide) l (w ^ k +> r)
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  refine stepStar_trans h1 ?_
  refine stepStar_congr (shift_E_w k (v +> ([0] +> l)) r) rfl ?_
  rw [← append_assoc, ← pow_succ_list']

lemma ROv01 (n : ℕ) (t : Tp) (r : zB) (h : RC (n * 3 + 5) t r)
    (hm : (n * 2 + (1 - offset t)) % 3 ≠ 2) :
    ∃ r', RC (n * 2 + (1 - offset t) + 1) (nxt t) r' ∧
      ∀ l, (l {{E}}> r) [tm]⊢*
        (([0] +> l) <{{A}} (w ^ ((n + 1 + offset t) / 3 + 1) +> r')) := by
  generalize h_idx : n * 3 + 5 = idx at h
  cases h with
  | RC_5 n0 t r0 h0 =>
    have hn0 : n0 = n := by omega
    subst n0
    rcases RInc (n * 2 + (1 - offset t)) (nxt t) r0 h0 with ⟨r', hr', i2, _⟩
    refine ⟨r', hr', fun l => ?_⟩
    set k := (n + 1 + offset t) / 3
    exact stepStar_trans (rov_enter k l r0)
      (stepStar_trans (stepPlus_to_stepStar (i2 hm (v ^ (k + 1) +> ([0] +> l))))
        (shift_A_v (k + 1) ([0] +> l) r'))
  | _ => omega

lemma ROv2 (n : ℕ) (t : Tp) (r : zB) (h : RC (n * 3 + 5) t r)
    (hm : (n * 2 + (1 - offset t)) % 3 = 2) :
    ∃ r', RC (n * 2 + (1 - offset t) + 1) (nxt t) r' ∧
      ∀ l, (l {{E}}> r) [tm]⊢*
        (([0] +> l) <{{A}} (w ^ ((n + 1 + offset t) / 3) +> r')) := by
  generalize h_idx : n * 3 + 5 = idx at h
  cases h with
  | RC_5 n0 t r0 h0 =>
    have hn0 : n0 = n := by omega
    subst n0
    rcases RInc (n * 2 + (1 - offset t)) (nxt t) r0 h0 with ⟨r', hr', _, i3⟩
    refine ⟨r', hr', fun l => ?_⟩
    set k := (n + 1 + offset t) / 3
    have hmid : ((v ^ (k + 1) +> ([0] +> l)) {{E}}> r0) [tm]⊢⁺
        ((v ^ k +> ([0] +> l)) <{{A}} r') := by
      rw [pow_v_comm k]
      exact i3 hm (v ^ k +> ([0] +> l))
    exact stepStar_trans (rov_enter k l r0)
      (stepStar_trans (stepPlus_to_stepStar hmid)
        (shift_A_v k ([0] +> l) r'))
  | _ => omega

lemma ROv (n : ℕ) (t : Tp) (r : zB) (h : RC (n * 3 + 5) t r) :
    ∃ r', RC (n * 2 + (1 - offset t) + 1) (nxt t) r' ∧
      ∀ l, (l {{E}}> r) [tm]⊢*
        (([0] +> l) <{{A}}
          (w ^ ((n + 1 + offset t) / 3 + (1 - ((n * 2 + (1 - offset t)) % 3) / 2)) +> r')) := by
  by_cases hm : (n * 2 + (1 - offset t)) % 3 = 2
  · have hdiv : 1 - ((n * 2 + (1 - offset t)) % 3) / 2 = 0 := by omega
    rw [hdiv, Nat.add_zero]
    exact ROv2 n t r h hm
  · have hdiv : 1 - ((n * 2 + (1 - offset t)) % 3) / 2 = 1 := by omega
    rw [hdiv]
    exact ROv01 n t r h hm

lemma BigStep0 {k : ℕ} {ls : List ℕ} {l : zB} {n : ℕ} {t : Tp} {r : zB}
    (hlc : LC k (0 :: ls) l) (hrc : RC (n * 3 + 5) t r) :
    ∃ l' r', LC (3 + k) ls l' ∧ RC ((n + 1) * 3 + 5) t r' ∧
      (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r') := by
  generalize h_ls : (0 :: ls : List ℕ) = ls0 at hlc
  cases hlc with
  | LC_w k ls1 l0 hlc0 =>
    injection h_ls with _ h_eq
    subst h_eq
    rcases RInc (n * 3 + 5) t r hrc with ⟨r0, hrc0, _, ir1⟩
    rcases LInc k ls l0 hlc0 with ⟨l1, hlc1, il1⟩
    rcases RInc (n * 3 + 6) t r0 hrc0 with ⟨r1, hrc1, ir2, _⟩
    rcases LInc (k + 1) ls l1 hlc1 with ⟨l2, hlc2, il2⟩
    rcases RInc (n * 3 + 7) t r1 hrc1 with ⟨r2, hrc2, ir3, _⟩
    rcases LInc (k + 2) ls l2 hlc2 with ⟨l3, hlc3, il3⟩
    refine ⟨l3, r2, hlc3.congr (by omega) rfl rfl, hrc2.congr (by omega) rfl rfl, ?_⟩
    exact stepPlus_trans (ir1 (by omega) l0)
      (stepPlus_trans (il1 r0)
        (stepPlus_trans (ir2 (by omega) l1)
          (stepPlus_trans (il2 r1)
            (stepPlus_trans (ir3 (by omega) l2) (il3 r2)))))
  | _ => cases h_ls

-- ============================================================================
-- Section 2: Longitudinal Reset & Symbolic State System (`BLECv5.v:412-645`)
-- ============================================================================

abbrev Hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := hLR

abbrev LH (n : ℕ) (l l' : zB) : Prop :=
  SideRLs (flipTM tm) (Hs ^ n) l l'

lemma LH.congr {n n' : ℕ} {l l₀ l' l₀' : zB}
    (h : LH n l l') (hn : n = n') (hl : l = l₀) (hl' : l' = l₀') : LH n' l₀ l₀' := by
  subst hn hl hl'; exact h

lemma LH_add {a b : ℕ} {l l' l'' : zB} (h1 : LH a l l') (h2 : LH b l' l'') :
    LH (a + b) l l'' :=
  h1.trans_add h2

lemma LH_inc (m k : ℕ) (ls : List ℕ) (l : zB) (h : LC k ls l) :
    ∃ l', LC (k + m) ls l' ∧ LH m l l' :=
  LIncs m k ls l h

lemma LH_word {n : ℕ} {l l' : zB} (h : LH n l l') :
    LH n (v +> l) (v +> l') := by
  have hseg : SegRLs (flipTM tm) Hs Hs v v :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
  exact (SegRLs.wall_pow hseg n).sideRLs_concat h

lemma LH_zero {n : ℕ} {l l' : zB} (h : LH n l l') :
    LH (n * 2) (z0 +> l) (z0 +> l') := by
  have ha : SegRLs (flipTM tm) (Hs ^ 2) Hs z0 z0 :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
  have hseg := segRLs_addmul'' (x := n) (a := 2) (b := 0) (.nil z0) ha
  simpa only [Nat.add_zero] using hseg.sideRLs_concat h

lemma LH_cross {l l' : zB} (h : LH 3 l l') :
    LH 2 ([0] +> (v +> l)) (v +> ([0] +> l')) := by
  have hseg : SegRLs (flipTM tm) (Hs ^ 2) (Hs ^ 3) ([0] ++ v) (v ++ [0]) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 200) (by decide)
  simpa only [append_assoc, append_cons, append_nil] using hseg.sideRLs_concat h

def up : List ℕ → List ℕ
  | [] => []
  | h :: ls => (h + 1) :: ls

def down : List ℕ → List ℕ
  | [] => []
  | h :: ls => (h - 1) :: ls

lemma LC_even_intro (n : ℕ) (ls : List ℕ) (l : zB) (h : LC n ls l) :
    LC (n * 2) (up ls) (z0 +> l) := by
  rcases ls with _ | ⟨hd, tl⟩
  · rcases n with _ | n
    · generalize hm : (0 : ℕ) = m at h
      cases h with
      | LC_0 =>
        have hd0 : z0 +> (default : zB) = default := BoundedConfig.all0_spec (by decide)
        simpa only [up, Nat.zero_mul, hd0] using LC.LC_0
      | _ => omega
    · exact (LC.LC_2 n l h).congr (by omega) rfl rfl
  · exact (LC.LC_0' n hd tl l h).congr rfl (by simp [up]; try omega) rfl

lemma LC_even (n : ℕ) (ls : List ℕ) (l : zB) (h : LC (n * 2) (up ls) l) :
    ∃ l', LC n ls l' ∧ l = z0 +> l' := by
  generalize hm : n * 2 = m at h
  generalize hls : up ls = ls0 at h
  rcases ls with _ | ⟨hd, tl⟩ <;> dsimp [up] at hls
  · cases h with
    | LC_0 =>
      have hn : n = 0 := by omega
      subst hn
      have hd0 : (default : zB) = z0 +> default := (BoundedConfig.all0_spec (by decide)).symm
      exact ⟨default, .LC_0, hd0⟩
    | LC_1 n0 l0 _ => omega
    | LC_2 n0 l0 h0 =>
      exact ⟨l0, h0.congr (by omega) rfl rfl, rfl⟩
    | _ => cases hls
  · cases h with
    | LC_1' n0 h0 t0 l0 _ => omega
    | LC_0' n0 h0 t0 l0 h0 =>
      injection hls with hh ht
      exact ⟨l0, h0.congr (by omega) (by rw [ht]; congr; omega) rfl, rfl⟩
    | LC_w n0 ls1 l0 _ => injection hls with hh; omega
    | _ => cases hls

lemma LC_odd (n : ℕ) (ls : List ℕ) (l : zB) (h : LC (n * 2 + 1) (up ls) l) :
    ∃ l', LC n ls l' ∧ l = z1 +> l' := by
  generalize hm : n * 2 + 1 = m at h
  generalize hls : up ls = ls0 at h
  rcases ls with _ | ⟨hd, tl⟩ <;> dsimp [up] at hls
  · cases h with
    | LC_0 => omega
    | LC_1 n0 l0 h0 =>
      exact ⟨l0, h0.congr (by omega) rfl rfl, rfl⟩
    | LC_2 n0 l0 _ => omega
    | _ => cases hls
  · cases h with
    | LC_1' n0 h0 t0 l0 h0 =>
      injection hls with hh ht
      exact ⟨l0, h0.congr (by omega) (by rw [ht]; congr; omega) rfl, rfl⟩
    | LC_0' n0 h0 t0 l0 _ => omega
    | LC_w n0 ls1 l0 _ => injection hls with hh; omega
    | _ => cases hls

inductive Reset : ℕ → List ℕ → ℕ → ℕ → List ℕ → Prop where
  | RZero : Reset 0 [] 0 0 []
  | ROdd (n : ℕ) (ls : List ℕ) : Reset (n * 2 + 1) (up ls) 1 n (0 :: ls)
  | REven (n : ℕ) (ls : List ℕ) (c k : ℕ) (ls' : List ℕ) :
      Reset n ls c k ls' → Reset (n * 2) (up ls) (c * 2) (k * 2) (up ls')
  | RMark (n : ℕ) (ls : List ℕ) (c k : ℕ) (ls' : List ℕ) :
      Reset (n + 3) ls c k ls' → Reset n (0 :: ls) (2 + c) k (0 :: ls')

lemma Reset.congr {n n' : ℕ} {ls ls₀ : List ℕ} {c c' k k' : ℕ} {ls' ls₀' : List ℕ}
    (h : Reset n ls c k ls')
    (hn : n = n') (hls : ls = ls₀) (hc : c = c') (hk : k = k') (hls' : ls' = ls₀') :
    Reset n' ls₀ c' k' ls₀' := by
  subst hn hls hc hk hls'; exact h

lemma LH_absorb (l : zB) : LH 1 ([0] +> (z1 +> l)) (v +> l) := by
  have hseg : SegRLs (flipTM tm) (Hs ^ 1) [] ([0] ++ z1) v :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
  simpa only [append_assoc, append_cons, append_nil] using hseg.sideRLs_concat (.nil l)

lemma Reset_spec {n : ℕ} {ls : List ℕ} {c k : ℕ} {ls' : List ℕ}
    (h : Reset n ls c k ls') (l : zB) (hl : LC n ls l) :
    ∃ l', LC k ls' l' ∧ LH c ([0] +> l) l' := by
  induction h generalizing l with
  | RZero =>
    generalize hm : (0 : ℕ) = m at hl
    generalize hls : ([] : List ℕ) = ls0 at hl
    cases hl with
    | LC_0 =>
      have hd : ([0] : zF) +> (default : zB) = default := BoundedConfig.all0_spec (by decide)
      exact ⟨default, .LC_0, by rw [hd]; exact .nil default⟩
    | LC_1 => omega
    | LC_2 => omega
    | _ => cases hls
  | ROdd n ls =>
    rcases LC_odd n ls l hl with ⟨l', hl', rfl⟩
    exact ⟨v +> l', .LC_w n ls l' hl', LH_absorb l'⟩
  | REven n ls c k ls' _ ih =>
    rcases LC_even n ls l hl with ⟨l0, hl0, rfl⟩
    rcases ih l0 hl0 with ⟨l', hl', hr⟩
    refine ⟨z0 +> l', LC_even_intro k ls' l' hl', ?_⟩
    have hz : ([0] : zF) +> (z0 +> l0) = z0 +> (([0] : zF) +> l0) := rfl
    rw [hz]
    exact LH_zero hr
  | RMark n ls c k ls' _ ih =>
    generalize hls : (0 :: ls : List ℕ) = ls0 at hl
    cases hl with
    | LC_w _ ls1 l0 hl0 =>
      injection hls with _ h_eq
      subst h_eq
      rcases LH_inc 3 n ls l0 hl0 with ⟨l1, hl1, h3⟩
      rcases ih l1 hl1 with ⟨l', hl', hr⟩
      exact ⟨v +> l', .LC_w k ls' l' hl', LH_add (LH_cross h3) (LH_word hr)⟩
    | _ => cases hls

lemma LH_first {n : ℕ} {l l' : zB} (h : LH (1 + n) l l') :
    ∃ l0, LH n l0 l' ∧ ∀ r, (l <{{A}} r) [tm]⊢⁺ (l0 {{E}}> r) := by
  have hpow : Hs ^ (1 + n) = (hL, hR) :: (Hs ^ n) := by
    rw [pow_add_list]; rfl
  unfold LH at h
  rw [hpow] at h
  cases h with
  | cons h_first h_rest =>
    exact ⟨_, h_rest, fun r =>
      toDHCfg_stepPlus_unflip (h₁ := hL) (h₂ := hR) (d₁ := .right) (d₂ := .left) (h_first r)⟩

lemma phase_calls (n : ℕ) {l l' r r' : zB}
    (hl : LH (1 + n) l l') (hr : SideRLs tm (hRL ^ n) r r') :
    (l <{{A}} r) [tm]⊢⁺ (l' {{E}}> r') := by
  induction n generalizing l r with
  | zero =>
    cases hr
    rcases LH_first hl with ⟨l0, hl0, hleft⟩
    cases hl0
    exact hleft _
  | succ n ih =>
    rcases LH_first hl with ⟨l0, hl0, hleft⟩
    have hpow : hRL ^ (n + 1) = (hR, hL) :: (hRL ^ n) := rfl
    rw [hpow] at hr
    cases hr with
    | cons hr_first hr_rest =>
      have h1 : (1 + n : ℕ) = n + 1 := by omega
      rw [← h1] at hl0
      exact stepPlus_trans (hleft r)
        (stepPlus_trans (hr_first l0) (ih hl0 hr_rest))

lemma Phase {n : ℕ} {t : Tp} {r l l' : zB}
    (hr : RC (n * 3 + 5) t r) (hl : LH (n + 4 + offset t) ([0] +> l) l') :
    ∃ r', RC (n * 3 + 5) (nxt t) r' ∧ (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r') := by
  have hoff := offset_le_one t
  rcases ROv n t r hr with ⟨r0, hr0, h0⟩
  set m := (n + 1 + offset t) / 3 + (1 - ((n * 2 + (1 - offset t)) % 3) / 2)
  rcases RIncs m (n * 2 + (1 - offset t) + 1) (nxt t) r0 hr0 with ⟨r', hr', h1⟩
  have he : m * 3 + (2 - (n * 2 + (1 - offset t) + 1) % 3) = n + 3 + offset t := by omega
  refine ⟨r', hr'.congr (by omega) rfl rfl, ?_⟩
  rw [he] at h1
  exact stepStar_stepPlus_trans (h0 l)
    (phase_calls (n + 3 + offset t) (hl.congr (by omega) rfl rfl) h1)

lemma Phase_reset {n : ℕ} {t : Tp} {r : zB} {k : ℕ} {ls : List ℕ} {c k' : ℕ} {ls' : List ℕ} {l : zB}
    (hr : RC (n * 3 + 5) t r) (hl : LC k ls l)
    (hreset : Reset k ls c k' ls') (hc : c ≤ n + 4 + offset t) :
    ∃ l' r', LC (k' + (n + 4 + offset t - c)) ls' l' ∧
      RC (n * 3 + 5) (nxt t) r' ∧ (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r') := by
  rcases Reset_spec hreset l hl with ⟨l0, hl0, h0⟩
  rcases LH_inc (n + 4 + offset t - c) k' ls' l0 hl0 with ⟨l', hl', h1⟩
  have h2 : LH (n + 4 + offset t) ([0] +> l) l' :=
    (LH_add h0 h1).congr (by omega) rfl rfl
  rcases Phase hr h2 with ⟨r', hr', hrun⟩
  exact ⟨l', r', hl', hr', hrun⟩








-- ============================================================================
-- Section 3: High-Level State Machine & Phase Cycles (`BLECv5.v:573-1330`)
-- ============================================================================

inductive State where
  | st (k : ℕ) (ls : List ℕ) (n : ℕ) (t : Tp)
  deriving DecidableEq, Repr

inductive Next : State → State → Prop where
  | Drop (k : ℕ) (ls : List ℕ) (n : ℕ) (t : Tp) :
      Next (.st k (0 :: ls) n t) (.st (k + 3) ls (n + 1) t)
  | Reset_next (k : ℕ) (ls : List ℕ) (n : ℕ) (t : Tp) (c k' : ℕ) (ls' : List ℕ) :
      Reset k ls c k' ls' → c ≤ n + 4 + offset t →
      Next (.st k ls n t) (.st (k' + (n + 4 + offset t - c)) ls' n (nxt t))

def Denote (s : State) (l r : zB) : Prop :=
  match s with
  | .st k ls n t => LC k ls l ∧ RC (n * 3 + 5) t r

lemma Denote.congr {s s' : State} {l l' r r' : zB}
    (h : Denote s l r) (hs : s = s') (hl : l = l') (hr : r = r') :
    Denote s' l' r' := by
  subst hs hl hr; exact h

lemma Next_spec {s s' : State} (h : Next s s') (l r : zB) (hd : Denote s l r) :
    ∃ l' r', Denote s' l' r' ∧ (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r') := by
  rcases h with ⟨k, ls, n, t⟩ | ⟨k, ls, n, t, c, k', ls', hres, hc⟩
  · rcases hd with ⟨hl, hr⟩
    rcases BigStep0 hl hr with ⟨l', r', hl', hr', hrun⟩
    exact ⟨l', r', ⟨hl'.congr (by omega) rfl rfl, hr'.congr (by omega) rfl rfl⟩, hrun⟩
  · rcases hd with ⟨hl, hr⟩
    rcases Phase_reset hr hl hres hc with ⟨l', r', hl', hr', hrun⟩
    exact ⟨l', r', ⟨hl', hr'⟩, hrun⟩

def shift (i : ℕ) : List ℕ → List ℕ
  | [] => []
  | h :: ls => (i + h) :: ls

lemma Reset_scale (i : ℕ) {n : ℕ} {ls : List ℕ} {c k : ℕ} {ls' : List ℕ}
    (h : Reset n ls c k ls') :
    Reset (n * 2 ^ i) (shift i ls) (c * 2 ^ i) (k * 2 ^ i) (shift i ls') := by
  induction i with
  | zero =>
    refine h.congr (by omega) ?_ (by omega) (by omega) ?_
    · cases ls <;> simp [shift]
    · cases ls' <;> simp [shift]
  | succ i ih =>
    have hev := Reset.REven (n * 2 ^ i) (shift i ls) (c * 2 ^ i) (k * 2 ^ i) (shift i ls') ih
    have hp : 2 ^ (i + 1) = 2 ^ i * 2 := by rw [Nat.pow_succ]
    refine hev.congr (by rw [hp]; ring) ?_ (by rw [hp]; ring) (by rw [hp]; ring) ?_
    · cases ls <;> simp [shift, up]; omega
    · cases ls' <;> simp [shift, up]; omega

inductive Steps : State → State → Prop where
  | Done (s : State) : Steps s s
  | Advance {s t u : State} : Next s t → Steps t u → Steps s u

lemma Steps.congr {s s' t t' : State} (h : Steps s t) (hs : s = s') (ht : t = t') :
    Steps s' t' := by
  subst hs ht; exact h

lemma Steps_spec {s s' : State} (h : Steps s s') (l r : zB) (hd : Denote s l r) :
    ∃ l' r', Denote s' l' r' ∧ (l {{E}}> r) [tm]⊢* (l' {{E}}> r') := by
  induction h generalizing l r with
  | Done s =>
    exact ⟨l, r, hd, stepStar_refl tm _⟩
  | Advance hnext _ ih =>
    rcases Next_spec hnext l r hd with ⟨l0, r0, hmid, hrun⟩
    rcases ih l0 r0 hmid with ⟨l', r', h', hrun'⟩
    exact ⟨l', r', h', stepPlus_to_stepStar (stepPlus_stepStar_trans hrun hrun')⟩

lemma reset_odd (n : ℕ) (ls' : List ℕ) {k : ℕ} {ls : List ℕ}
    (hk : k = n * 2 + 1) (hls : ls = up ls') :
    Reset k ls 1 n (0 :: ls') :=
  (Reset.ROdd n ls').congr hk.symm hls.symm rfl rfl rfl

lemma reset_even (n : ℕ) (ls0 : List ℕ) {k : ℕ} {ls : List ℕ} {c k' : ℕ} {ls' : List ℕ}
    (hk : k = n * 2) (hls : ls = up ls0)
    (h : Reset n ls0 c k' ls') :
    Reset k ls (c * 2) (k' * 2) (up ls') :=
  (Reset.REven n ls0 c k' ls' h).congr hk.symm hls.symm rfl rfl rfl

lemma reset_mark {k : ℕ} {ls : List ℕ} {c k' : ℕ} {ls' : List ℕ}
    (h : Reset (k + 3) ls c k' ls') :
    Reset k (0 :: ls) (2 + c) k' (0 :: ls') :=
  .RMark k ls c k' ls' h

macro "rodd" n:term:arg ls:term:arg : tactic =>
  `(tactic| (apply reset_odd $n ($ls : List ℕ); { omega }; { rfl }))

macro "reven" n:term:arg ls:term:arg : tactic =>
  `(tactic| (apply reset_even $n ($ls : List ℕ); { omega }; { rfl }))

macro "rmark" : tactic =>
  `(tactic| apply reset_mark)

lemma step_drop {k : ℕ} {ls : List ℕ} {n : ℕ} {t : Tp} {s' : State}
    (h : Steps (.st (k + 3) ls (n + 1) t) s') :
    Steps (.st k (0 :: ls) n t) s' :=
  .Advance (.Drop k ls n t) h

lemma step_reset_as (k_new n_new : ℕ)
    {k : ℕ} {ls : List ℕ} {n : ℕ} {t : Tp} {c k' : ℕ} {ls' : List ℕ} {s' : State}
    (hr : Reset k ls c k' ls')
    (hc : c ≤ n + 4 + offset t)
    (hk : k' + (n + 4 + offset t - c) = k_new)
    (hn : n = n_new)
    (h : Steps (.st k_new ls' n_new (nxt t)) s') :
    Steps (.st k ls n t) s' := by
  subst hk hn
  exact .Advance (.Reset_next k ls n t c k' ls' hr hc) h

macro "phase_with" k_new:term:arg n_new:term:arg "{" tacs:tacticSeq "}" : tactic =>
  `(tactic| (
    repeat' apply step_drop
    refine step_reset_as $k_new $n_new (by $tacs) (by dsimp [offset]; omega) (by dsimp [offset]; omega) (by omega) ?_
    dsimp only [up, down, nxt]
  ))

def RootG (n : ℕ) : State := .st (n * 2 + 7) [0] n .t5
def RootD (h n : ℕ) : State := .st (n * 2 + 7 - 3 * 2 ^ (h - 1)) [0, h] n .t5
def RootE (n : ℕ) : State := .st (n * 2 + 3) [1, 0] n .t5
def RootF (n : ℕ) : State := .st (n * 2 + 3) [0, 0, 1] n .t5

lemma E_cycle (n : ℕ) (hn : 64 ≤ n) (hmod : n % 8 = 2) :
    Steps (RootE n) (RootG (n + 9)) := by
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  unfold RootE RootG
  phase_with (n * 2 + 5) n { rodd (q * 8 + 3) [0, 0] }
  phase_with (n * 2 + 11) (n + 3) { reven (q * 8 + 9) []; rodd (q * 4 + 4) [] }
  phase_with (n * 2 + 12) (n + 3) { rodd (q * 8 + 7) [0] }
  phase_with (n * 2 + 15) (n + 5) { reven (q * 8 + 11) []; rodd (q * 4 + 5) [] }
  phase_with (n * 2 + 16) (n + 5) { rodd (q * 8 + 9) [0] }
  phase_with (n * 2 + 19) (n + 7) { reven (q * 8 + 13) []; rodd (q * 4 + 6) [] }
  phase_with (n * 2 + 19) (n + 7) { rodd (q * 8 + 11) [0] }
  phase_with (n * 2 + 25) (n + 9) { rodd (q * 8 + 14) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma F_cycle (n : ℕ) (hn : 64 ≤ n) (hmod : n % 8 = 1) :
    Steps (RootF n) (RootG (n + 10)) := by
  set q := n / 8
  have hq : n = q * 8 + 1 := by omega
  unfold RootF RootG
  phase_with (n * 2 + 10) (n + 2) { rodd (q * 8 + 5) [0] }
  phase_with (n * 2 + 13) (n + 4) { reven (q * 8 + 9) []; rodd (q * 4 + 4) [] }
  phase_with (n * 2 + 14) (n + 4) { rodd (q * 8 + 7) [0] }
  phase_with (n * 2 + 17) (n + 6) { reven (q * 8 + 11) []; rodd (q * 4 + 5) [] }
  phase_with (n * 2 + 18) (n + 6) { rodd (q * 8 + 9) [0] }
  phase_with (n * 2 + 21) (n + 8) { reven (q * 8 + 13) []; rodd (q * 4 + 6) [] }
  phase_with (n * 2 + 21) (n + 8) { rodd (q * 8 + 11) [0] }
  phase_with (n * 2 + 27) (n + 10) { rodd (q * 8 + 14) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma D_shrink (j n : ℕ) (hn : 384 * 2 ^ j ≤ n) (hmod : n % 8 = 2) :
    Steps (RootD (9 + j) n) (RootD (1 + j) (n + 8)) := by
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  unfold RootD
  have hp : 3 * 2 ^ (9 + j - 1) = 768 * 2 ^ j := by
    rw [show 9 + j - 1 = j + 8 by omega, Nat.pow_add]; ring
  rw [hp, show 1 + j - 1 = j by omega, show 9 + j = j + 9 by omega, show 1 + j = j + 1 by omega]
  phase_with (n * 2 + 8 - 384 * 2 ^ j) (n + 1) { reven (q * 8 + 7 - 384 * 2 ^ j) [(j + 8)]; rodd (q * 4 + 3 - 192 * 2 ^ j) [(j + 7)] }
  phase_with (n * 2 + 5 - 192 * 2 ^ j) (n + 1) { reven (q * 8 + 6 - 192 * 2 ^ j) [0, (j + 7)]; rmark; rodd (q * 4 + 4 - 96 * 2 ^ j) [(j + 6)] }
  phase_with (n * 2 + 7 - 96 * 2 ^ j) (n + 1) { rodd (q * 8 + 4 - 96 * 2 ^ j) [0, 0, (j + 6)] }
  phase_with (n * 2 + 10 - 48 * 2 ^ j) (n + 4) { reven (q * 8 + 10 - 48 * 2 ^ j) [(j + 5)]; reven (q * 4 + 5 - 24 * 2 ^ j) [(j + 4)]; rodd (q * 2 + 2 - 12 * 2 ^ j) [(j + 3)] }
  phase_with (n * 2 + 11 - 24 * 2 ^ j) (n + 4) { reven (q * 8 + 7 - 24 * 2 ^ j) [1, (j + 3)]; rodd (q * 4 + 3 - 12 * 2 ^ j) [0, (j + 3)] }
  phase_with (n * 2 + 12 - 12 * 2 ^ j) (n + 4) { rodd (q * 8 + 7 - 12 * 2 ^ j) [0, 0, (j + 3)] }
  phase_with (n * 2 + 20 - 6 * 2 ^ j) (n + 7) { rodd (q * 8 + 12 - 6 * 2 ^ j) [(j + 2)] }
  phase_with (n * 2 + 23 - 3 * 2 ^ j) (n + 8) { rodd (q * 8 + 13 - 3 * 2 ^ j) [(j + 1)] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma D_small (h n : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ 5) (hn : 64 ≤ n) (hmod : n % 8 = 2) :
    Steps (RootD h n) (RootG (n + 9)) := by
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5) with rfl | rfl | rfl | rfl | rfl <;>
    dsimp [RootD, RootG]
  · -- h = 1
    phase_with (n * 2 + 8) (n + 1) { rodd (q * 8 + 5) [0] }
    phase_with (n * 2 + 11) (n + 3) { reven (q * 8 + 9) []; rodd (q * 4 + 4) [] }
    phase_with (n * 2 + 12) (n + 3) { rodd (q * 8 + 7) [0] }
    phase_with (n * 2 + 15) (n + 5) { reven (q * 8 + 11) []; rodd (q * 4 + 5) [] }
    phase_with (n * 2 + 16) (n + 5) { rodd (q * 8 + 9) [0] }
    phase_with (n * 2 + 19) (n + 7) { reven (q * 8 + 13) []; rodd (q * 4 + 6) [] }
    phase_with (n * 2 + 19) (n + 7) { rodd (q * 8 + 11) [0] }
    phase_with (n * 2 + 25) (n + 9) { rodd (q * 8 + 14) [] }
    exact (Steps.Done _).congr (by congr 1; omega) rfl
  · -- h = 2
    phase_with (n * 2) (n + 1) { reven (q * 8 + 4) [1]; reven (q * 4 + 2) [0]; rmark; rodd (q * 2 + 2) [] }
    phase_with (n * 2 - 5) (n + 1) { reven (q * 8 + 2) [1, 0]; reven (q * 4 + 1) [0, 0]; rmark; rmark; rodd (q * 2 + 3) [] }
    phase_with (n * 2 + 2) (n + 1) { rodd (q * 8 - 1) [1, 0, 0] }
    phase_with (n * 2 + 7) (n + 2) { rodd (q * 8 + 4) [0, 0, 0] }
    phase_with (n * 2 + 19) (n + 6) { rodd (q * 8 + 11) [] }
    phase_with (n * 2 + 19) (n + 7) { reven (q * 8 + 13) []; rodd (q * 4 + 6) [] }
    phase_with (n * 2 + 19) (n + 7) { rodd (q * 8 + 11) [0] }
    phase_with (n * 2 + 25) (n + 9) { rodd (q * 8 + 14) [] }
    exact (Steps.Done _).congr (by congr 1; omega) rfl
  · -- h = 3
    phase_with (n * 2 + 2) (n + 1) { reven (q * 8 + 1) [2]; rodd (q * 4) [1] }
    phase_with (n * 2 - 9) (n + 1) { reven (q * 8 + 3) [0, 1]; rmark; reven (q * 4 + 3) [0]; rmark; reven (q * 2 + 3) []; rodd (q + 1) [] }
    phase_with (n * 2) (n + 1) { rodd (q * 8 - 3) [0, 1, 1] }
    phase_with (n * 2 + 1) (n + 3) { reven (q * 8 + 5) [0, 1]; rmark; reven (q * 4 + 4) [0]; rmark; rodd (q * 2 + 3) [] }
    phase_with (n * 2 + 7) (n + 3) { rodd (q * 8 + 2) [0, 1, 0] }
    phase_with (n * 2 + 14) (n + 5) { rodd (q * 8 + 8) [0, 0] }
    phase_with (n * 2 + 22) (n + 8) { rodd (q * 8 + 13) [] }
    phase_with (n * 2 + 25) (n + 9) { rodd (q * 8 + 14) [] }
    exact (Steps.Done _).congr (by congr 1; omega) rfl
  · -- h = 4
    phase_with (n * 2 - 4) (n + 1) { reven (q * 8 - 5) [3]; rodd (q * 4 - 3) [2] }
    phase_with (n * 2 - 1) (n + 1) { reven (q * 8) [0, 2]; rmark; rodd (q * 4 + 1) [1] }
    phase_with (n * 2 + 4) (n + 1) { rodd (q * 8 + 1) [0, 0, 1] }
    phase_with (n * 2 + 13) (n + 4) { rodd (q * 8 + 8) [0] }
    phase_with (n * 2 + 19) (n + 6) { rodd (q * 8 + 11) [] }
    phase_with (n * 2 + 19) (n + 7) { reven (q * 8 + 13) []; rodd (q * 4 + 6) [] }
    phase_with (n * 2 + 19) (n + 7) { rodd (q * 8 + 11) [0] }
    phase_with (n * 2 + 25) (n + 9) { rodd (q * 8 + 14) [] }
    exact (Steps.Done _).congr (by congr 1; omega) rfl
  · -- h = 5
    phase_with (n * 2 - 16) (n + 1) { reven (q * 8 - 17) [4]; rodd (q * 4 - 9) [3] }
    phase_with (n * 2 - 7) (n + 1) { reven (q * 8 - 6) [0, 3]; rmark; rodd (q * 4 - 2) [2] }
    phase_with (n * 2 + 1) (n + 1) { rodd (q * 8 - 2) [0, 0, 2] }
    phase_with (n * 2 + 10) (n + 4) { reven (q * 8 + 7) [1]; rodd (q * 4 + 3) [0] }
    phase_with (n * 2 + 9) (n + 4) { reven (q * 8 + 7) [0, 0]; rmark; rmark; rodd (q * 4 + 6) [] }
    phase_with (n * 2 + 11) (n + 4) { rodd (q * 8 + 6) [0, 0, 0] }
    phase_with (n * 2 + 22) (n + 8) { rodd (q * 8 + 13) [] }
    phase_with (n * 2 + 25) (n + 9) { rodd (q * 8 + 14) [] }
    exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma D7 (n : ℕ) (hn : 96 ≤ n) (hmod : n % 8 = 2) :
    Steps (RootD 7 n) (RootF (n + 7)) := by
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  dsimp [RootD, RootF]
  phase_with (n * 2 - 88) (n + 1) { reven (q * 8 - 89) [6]; rodd (q * 4 - 45) [5] }
  phase_with (n * 2 - 43) (n + 1) { reven (q * 8 - 42) [0, 5]; rmark; rodd (q * 4 - 20) [4] }
  phase_with (n * 2 - 17) (n + 1) { rodd (q * 8 - 20) [0, 0, 4] }
  phase_with (n * 2 - 2) (n + 4) { reven (q * 8 - 2) [3]; reven (q * 4 - 1) [2]; rodd (q * 2 - 1) [1] }
  phase_with (n * 2 + 5) (n + 4) { reven (q * 8 + 1) [1, 1]; rodd (q * 4) [0, 1] }
  phase_with (n * 2 + 9) (n + 4) { rodd (q * 8 + 4) [0, 0, 1] }
  phase_with (n * 2 + 13) (n + 7) { reven (q * 8 + 11) [0]; rmark; reven (q * 4 + 7) []; rodd (q * 2 + 3) [] }
  phase_with (n * 2 + 17) (n + 7) { rodd (q * 8 + 8) [0, 1] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma D8 (n : ℕ) (hn : 192 ≤ n) (hmod : n % 8 = 2) :
    Steps (RootD 8 n) (RootE (n + 8)) := by
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  dsimp [RootD, RootE]
  phase_with (n * 2 - 184) (n + 1) { reven (q * 8 - 185) [7]; rodd (q * 4 - 93) [6] }
  phase_with (n * 2 - 91) (n + 1) { reven (q * 8 - 90) [0, 6]; rmark; rodd (q * 4 - 44) [5] }
  phase_with (n * 2 - 41) (n + 1) { rodd (q * 8 - 44) [0, 0, 5] }
  phase_with (n * 2 - 14) (n + 4) { reven (q * 8 - 14) [4]; reven (q * 4 - 7) [3]; rodd (q * 2 - 4) [2] }
  phase_with (n * 2 - 1) (n + 4) { reven (q * 8 - 5) [1, 2]; rodd (q * 4 - 3) [0, 2] }
  phase_with (n * 2 + 6) (n + 4) { rodd (q * 8 + 1) [0, 0, 2] }
  phase_with (n * 2 + 17) (n + 7) { rodd (q * 8 + 9) [1] }
  phase_with (n * 2 + 19) (n + 8) { reven (q * 8 + 12) [0]; rmark; rodd (q * 4 + 7) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma D6_even (n : ℕ) (hn : 64 ≤ n) (hmod : n % 16 = 10) :
    Steps (RootD 6 n) (RootE (n + 8)) := by
  set q := n / 16
  have hq : n = q * 16 + 10 := by omega
  dsimp [RootD, RootE]
  phase_with (n * 2 - 40) (n + 1) { reven (q * 16 - 33) [5]; rodd (q * 8 - 17) [4] }
  phase_with (n * 2 - 19) (n + 1) { reven (q * 16 - 10) [0, 4]; rmark; rodd (q * 8 - 4) [3] }
  phase_with (n * 2 - 5) (n + 1) { rodd (q * 16) [0, 0, 3] }
  phase_with (n * 2 - 18) (n + 4) { reven (q * 16 + 12) [2]; reven (q * 8 + 6) [1]; reven (q * 4 + 3) [0]; rmark; reven (q * 2 + 3) []; rodd (q + 1) [] }
  phase_with (n * 2 - 3) (n + 4) { reven (q * 16 + 1) [2, 1]; rodd (q * 8) [1, 1] }
  phase_with (n * 2 + 5) (n + 4) { rodd (q * 16 + 8) [0, 1, 1] }
  phase_with (n * 2 + 14) (n + 6) { rodd (q * 16 + 15) [0, 1] }
  phase_with (n * 2 + 19) (n + 8) { reven (q * 16 + 20) [0]; rmark; rodd (q * 8 + 11) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma Reset_power (i u : ℕ) :
    Reset ((u * 2 + 1) * 2 ^ i) [] (2 ^ i) (u * 2 ^ i) [i] := by
  have h := Reset_scale i (Reset.ROdd u [])
  exact h.congr rfl rfl (by omega) rfl (by simp [shift])

lemma Reset_cross (a u : ℕ) :
    Reset ((u * 2 + 3) * 32 * 2 ^ a - 24) [3] (16 + 32 * 2 ^ a) ((u + 1) * 32 * 2 ^ a) [3, a + 2] := by
  have hp : 2 ^ (a + 2) = 4 * 2 ^ a := by rw [Nat.pow_add]; ring
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hc0 : ((u + 1) * 2 + 1) * 2 ^ (a + 2) = 8 * (u * 2 ^ a) + 12 * 2 ^ a := by rw [hp]; ring
  have hc1 : (u * 2 + 3) * 2 ^ (a + 2) = 8 * (u * 2 ^ a) + 12 * 2 ^ a := by rw [hp]; ring
  have h0 : Reset (((u * 2 + 3) * 2 ^ (a + 2) - 3) + 3) [] (2 ^ (a + 2)) ((u + 1) * 2 ^ (a + 2)) [a + 2] := by
    refine (Reset_power (a + 2) (u + 1)).congr ?_ rfl rfl rfl rfl
    omega
  have hmark := Reset.RMark ((u * 2 + 3) * 2 ^ (a + 2) - 3) [] (2 ^ (a + 2)) ((u + 1) * 2 ^ (a + 2)) [a + 2] h0
  have hscale := Reset_scale 3 hmark
  refine hscale.congr ?_ rfl ?_ ?_ rfl
  · change (((u * 2 + 3) * 2 ^ (a + 2) - 3) * 8) = (u * 2 + 3) * 32 * 2 ^ a - 24
    have hc2 : (u * 2 + 3) * 32 * 2 ^ a = 64 * (u * 2 ^ a) + 96 * 2 ^ a := by ring
    omega
  · change (2 + 2 ^ (a + 2)) * 8 = 16 + 32 * 2 ^ a
    rw [hp]; omega
  · change ((u + 1) * 2 ^ (a + 2)) * 8 = (u + 1) * 32 * 2 ^ a
    rw [hp]; ring

lemma D6_odd_ge3 (a u n : ℕ) (hn : 64 ≤ n) (hval : n + 14 = (u * 2 + 3) * 16 * 2 ^ a) :
    Steps (RootD 6 n) (RootD (1 + a) (n + 8)) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hval_lin : n + 14 = 32 * (u * 2 ^ a) + 48 * 2 ^ a := by rw [hval]; ring
  have hc1 : (u * 2 + 3) * 32 * 2 ^ a = 64 * (u * 2 ^ a) + 96 * 2 ^ a := by ring
  have hc2 : (u + 1) * 32 * 2 ^ a = 32 * (u * 2 ^ a) + 32 * 2 ^ a := by ring
  have hlow : 48 * 2 ^ a ≤ n + 14 := by omega
  have hmod : n % 8 = 2 := by omega
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  dsimp [RootD]
  rw [show 1 + a - 1 = a by omega, show 1 + a = a + 1 by omega]
  phase_with (n * 2 - 40) (n + 1) { reven (q * 8 - 41) [5]; rodd (q * 4 - 21) [4] }
  phase_with (n * 2 - 19) (n + 1) { reven (q * 8 - 18) [0, 4]; rmark; rodd (q * 4 - 8) [3] }
  phase_with (n * 2 - 5) (n + 1) { rodd (q * 8 - 8) [0, 0, 3] }
  apply step_drop; apply step_drop; apply step_drop
  have hcross : Reset (n * 2 - 5 + 3 + 3 + 3) [3] (16 + 32 * 2 ^ a) ((u + 1) * 32 * 2 ^ a) [3, a + 2] :=
    (Reset_cross a u).congr (by omega) rfl rfl rfl rfl
  refine step_reset_as (n * 2 + 6 - 48 * 2 ^ a) (n + 4) hcross (by dsimp [offset]; omega) (by dsimp [offset]; omega) (by omega) ?_
  dsimp only [nxt]
  phase_with (n * 2 + 9 - 24 * 2 ^ a) (n + 4) { reven (q * 8 + 5 - 24 * 2 ^ a) [2, (a + 2)]; rodd (q * 4 + 2 - 12 * 2 ^ a) [1, (a + 2)] }
  phase_with (n * 2 + 11 - 12 * 2 ^ a) (n + 4) { rodd (q * 8 + 6 - 12 * 2 ^ a) [0, 1, (a + 2)] }
  phase_with (n * 2 + 17 - 6 * 2 ^ a) (n + 6) { rodd (q * 8 + 10 - 6 * 2 ^ a) [0, (a + 2)] }
  phase_with (n * 2 + 23 - 3 * 2 ^ a) (n + 8) { rodd (q * 8 + 13 - 3 * 2 ^ a) [(a + 1)] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma LH_one {n : ℕ} {l l' : zB} (h : LH n l l') :
    LH (n * 2) (z1 +> l) (z1 +> l') := by
  have hb : SegRLs (flipTM tm) (Hs ^ 0) [] z1 z1 := .nil z1
  have ha : SegRLs (flipTM tm) (Hs ^ 2) Hs z1 z1 :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
  have hseg := segRLs_addmul'' (x := n) (a := 2) (b := 0) hb ha
  simpa only [Nat.add_zero] using hseg.sideRLs_concat h

lemma LH_zeros (j : ℕ) {n : ℕ} {l l' : zB} (h : LH n l l') :
    LH (n * 2 ^ j) (z0 ^ j +> l) (z0 ^ j +> l') := by
  induction j with
  | zero =>
    exact h.congr (by omega) rfl rfl
  | succ j ih =>
    rw [pow_succ_list, append_assoc]
    have hz := LH_zero ih
    have hp : 2 ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
    exact hz.congr (by rw [hp]; ring) rfl rfl

lemma G_start (j u n : ℕ) (hj : 2 ≤ j) (hval : n + 5 = (u * 2 + 3) * 2 ^ (1 + j)) :
    Steps (RootG n) (.st (n * 2 + 9 - 3 * 2 ^ j) [0, 1 + j] (n + 1) .t7) := by
  have hp1 : 2 ^ (1 + j) = 2 * 2 ^ j := by rw [Nat.add_comm 1 j, Nat.pow_succ]; ring
  have hp2 : 2 ^ (2 + j) = 4 * 2 ^ j := by rw [Nat.add_comm 2 j, Nat.pow_add]; ring
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have hval_lin : n + 5 = 4 * (u * 2 ^ j) + 6 * 2 ^ j := by rw [hval, hp1]; ring
  have hc1 : ((u + 1) * 2 + 1) * 2 ^ (2 + j) = 8 * (u * 2 ^ j) + 12 * 2 ^ j := by rw [hp2]; ring
  have hc2 : (u + 1) * 2 ^ (2 + j) = 4 * (u * 2 ^ j) + 4 * 2 ^ j := by rw [hp2]; ring
  have hlow : 6 * 2 ^ j ≤ n + 5 := by omega
  unfold RootG
  apply step_drop
  have hpow : Reset (n * 2 + 7 + 3) [] (2 ^ (2 + j)) ((u + 1) * 2 ^ (2 + j)) [2 + j] := by
    refine (Reset_power (2 + j) (u + 1)).congr ?_ rfl rfl rfl rfl
    omega
  refine step_reset_as (n * 2 + 11 - 6 * 2 ^ j) (n + 1) hpow
    (by dsimp [offset]; omega)
    (by dsimp [offset]; omega)
    rfl ?_
  dsimp only [nxt]
  rw [show 2 + j = j + 2 by omega, show 1 + j = j + 1 by omega]
  phase_with (n * 2 + 9 - 3 * 2 ^ j) (n + 1) { rodd (n + 5 - 3 * 2 ^ j) [(j + 1)] }
  exact (Steps.Done _)

lemma LH_set (l : zB) : LH 1 (z0 +> l) (z1 +> l) := by
  have hseg : SegRLs (flipTM tm) (Hs ^ 1) [] z0 z1 :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
  exact hseg.sideRLs_concat (.nil l)

lemma LH_last (l : zB) : LH 1 (z1 +> ([0] +> (z1 +> l))) (z0 +> (v +> l)) := by
  have hseg : SegRLs (flipTM tm) (Hs ^ 1) [] (z1 ++ [0] ++ z1) (z0 ++ v) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
  simpa only [append_assoc, append_cons, append_nil] using hseg.sideRLs_concat (.nil l)

lemma LH_fill (j : ℕ) {n : ℕ} {l l' : zB} (h : LH n l l') :
    LH ((n + 1) * 2 ^ j - 1) (z0 ^ j +> l) (z1 ^ j +> l') := by
  induction j with
  | zero =>
    exact h.congr (by omega) rfl rfl
  | succ j ih =>
    have hb : SegRLs (flipTM tm) (Hs ^ 1) [] z0 z1 :=
      BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
    have ha : SegRLs (flipTM tm) (Hs ^ 2) Hs z1 z1 :=
      BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
    have hseg := segRLs_addmul'' (x := (n + 1) * 2 ^ j - 1) (a := 2) (b := 1) hb ha
    have hp : 2 ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
    have h_eq : ((n + 1) * 2 ^ j - 1) * 2 + 1 = (n + 1) * 2 ^ (j + 1) - 1 := by
      rw [hp, ← Nat.mul_assoc]
      have : 0 < (n + 1) * 2 ^ j := Nat.mul_pos (by omega) h1
      omega
    rw [pow_succ_list, pow_succ_list, append_assoc, append_assoc]
    exact LH.congr (hseg.sideRLs_concat ih) h_eq rfl rfl

lemma LH_clear (j : ℕ) {l l' : zB} (h : LH 1 l l') :
    LH 1 (z1 ^ j +> l) (z0 ^ j +> l') := by
  induction j with
  | zero => exact h
  | succ j ih =>
    have hseg : SegRLs (flipTM tm) (Hs ^ 1) (Hs ^ 1) z1 z0 :=
      BoundedConfig.segRLs_c_spec (flipTM tm) (T := 100) (by decide)
    rw [pow_succ_list, pow_succ_list, append_assoc, append_assoc]
    exact hseg.sideRLs_concat ih

lemma LH_partial_D (j : ℕ) :
    LH (2 ^ (5 + j) - 22)
      (z0 +> (z0 +> (z0 +> (v +> (z0 +> (z0 +> (z0 ^ j +> (z0 +> ([0] +> (z1 +> default))))))))))
      (z0 +> (z1 +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))))))))) := by
  have hp : 2 ^ (5 + j) = 32 * 2 ^ j := by rw [Nat.add_comm 5 j, Nat.pow_add]; ring
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have hb1 : SegRLs (flipTM tm) (Hs ^ 2) [] (z0 ++ z0 ++ z0 ++ v) (z0 ++ z1 ++ z0 ++ v) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 2000) (by decide)
  have ha1 : SegRLs (flipTM tm) (Hs ^ 8) Hs (z0 ++ z1 ++ z0 ++ v) (z0 ++ z1 ++ z0 ++ v) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 2000) (by decide)
  have hseg1 := segRLs_addmul'' (x := (2 ^ j - 1) * 4 + 1) (a := 8) (b := 2) hb1 ha1
  have hb2 : SegRLs (flipTM tm) (Hs ^ 1) [] (z0 ++ z0) (z1 ++ z0) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 1000) (by decide)
  have ha2 : SegRLs (flipTM tm) (Hs ^ 4) Hs (z1 ++ z0) (z1 ++ z0) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 1000) (by decide)
  have hseg2 := segRLs_addmul'' (x := 2 ^ j - 1) (a := 4) (b := 1) hb2 ha2
  have hfill : LH (2 ^ j - 1)
      (z0 ^ j +> (z0 +> ([0] +> (z1 +> default))))
      (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))) :=
    (LH_fill j (n := 0) (.nil _)).congr (by omega) rfl rfl
  have hmid := hseg2.sideRLs_concat hfill
  have htot := hseg1.sideRLs_concat hmid
  refine LH.congr htot ?_ ?_ ?_
  · rw [hp]; omega
  · simp only [append_assoc]
  · simp only [append_assoc]

lemma LH_partial (j : ℕ) (r : zB) :
    LH (1 + 2 ^ j * 2) (z0 +> (z0 ^ j +> (z0 +> ([0] +> (z1 +> r)))))
      (z1 +> (z0 ^ j +> (z1 +> ([0] +> (z1 +> r))))) := by
  refine LH_add (LH_set _) ?_
  refine LH_one ?_
  exact (LH_zeros j (LH_set ([0] +> (z1 +> r)))).congr (by omega) rfl rfl

lemma LC_zero_words (j : ℕ) {ls : List ℕ} {l : zB} (h : LC 0 ls l) :
    LC 0 (shift j ls) (z0 ^ j +> l) := by
  induction j with
  | zero =>
    refine h.congr rfl ?_ rfl
    cases ls <;> simp [shift]
  | succ j ih =>
    rw [pow_succ_list, append_assoc]
    refine (LC_even_intro 0 (shift j ls) (z0 ^ j +> l) ih).congr rfl ?_ rfl
    cases ls <;> simp [shift, up]; omega

lemma LH_partial_finish (j : ℕ) :
    ∃ l', LC (2 ^ j - 1) [0, 1 + j] l' ∧
      LH (2 ^ j * 2) ([0] +> (z1 +> (z0 ^ j +> (z1 +> ([0] +> (z1 +> default)))))) l' := by
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have hnum : LC 0 [0, 1 + j] (v +> (z0 ^ j +> (z0 +> (v +> default)))) := by
    apply LC.LC_w
    have hzw := LC_zero_words (j + 1) (LC.LC_w 0 [] default .LC_0)
    rw [pow_succ_list', append_assoc] at hzw
    exact hzw.congr rfl (by simp [shift]; omega) rfl
  rcases LH_inc (2 ^ j - 1) 0 [0, 1 + j] _ hnum with ⟨l', hl', hrun⟩
  refine ⟨l', hl'.congr (by omega) rfl rfl, ?_⟩
  have hstep1 := LH_absorb (z0 ^ j +> (z1 +> ([0] +> (z1 +> default))))
  have hstep2 : LH (2 ^ j) (v +> (z0 ^ j +> (z1 +> ([0] +> (z1 +> default)))))
      (v +> (z0 ^ j +> (z0 +> (v +> default)))) :=
    LH_word ((LH_zeros j (LH_last default)).congr (by omega) rfl rfl)
  exact (LH_add hstep1 (LH_add hstep2 hrun)).congr (by omega) rfl rfl

lemma LC_unzeros (j : ℕ) {n : ℕ} {ls : List ℕ} {l : zB} (h : LC (n * 2 ^ j) (shift j ls) l) :
    ∃ l', LC n ls l' ∧ l = z0 ^ j +> l' := by
  induction j generalizing l with
  | zero =>
    refine ⟨l, h.congr (by omega) ?_ rfl, rfl⟩
    cases ls <;> simp [shift]
  | succ j ih =>
    have hp : 2 ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
    have he : LC ((n * 2 ^ j) * 2) (up (shift j ls)) l := by
      refine h.congr (by rw [hp]; ring) ?_ rfl
      cases ls <;> simp [shift, up]; omega
    rcases LC_even (n * 2 ^ j) (shift j ls) l he with ⟨l0, hl0, rfl⟩
    rcases ih hl0 with ⟨l', hl', rfl⟩
    refine ⟨l', hl', ?_⟩
    rw [pow_succ_list, append_assoc]

lemma LC_pow (j : ℕ) {l : zB} (h : LC (2 ^ j) [] l) :
    l = z0 ^ j +> (z1 +> default) := by
  have he : LC (1 * 2 ^ j) (shift j []) l := h.congr (by omega) rfl rfl
  rcases LC_unzeros j he with ⟨l0, hl0, rfl⟩
  rcases LC_odd 0 [] l0 (hl0.congr rfl rfl rfl) with ⟨l', hl', rfl⟩
  generalize hm : (0 : ℕ) = m at hl'
  generalize hls : ([] : List ℕ) = ls0 at hl'
  cases hl' with
  | LC_0 => rfl
  | LC_w => cases hls
  | LC_0' => cases hls
  | LC_1' => cases hls
  | _ => omega

lemma zero_move (j : ℕ) (l : zB) :
    ([0] : zF) +> (z0 ^ j +> l) = z0 ^ j +> ([0] +> l) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ_list, append_assoc, append_assoc, ← ih]
    rfl

lemma LC_mark {k : ℕ} {ls : List ℕ} {l : zB} (h : LC k (0 :: ls) l) :
    ∃ l', LC k ls l' ∧ l = v +> l' := by
  generalize hls : (0 :: ls : List ℕ) = ls0 at h
  cases h with
  | LC_w _ ls1 l0 hl0 =>
    injection hls with _ heq
    subst heq
    exact ⟨l0, hl0, rfl⟩
  | _ => cases hls

lemma LH_partial_D_start (j k : ℕ) (l : zB) (hk : k + 24 = 2 ^ (6 + j)) (hl : LC k [3] l) :
    LH (2 ^ (5 + j) - 6) ([0] +> l)
      (z0 +> (z1 +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))))))))) := by
  have hp6 : 2 ^ (6 + j) = 64 * 2 ^ j := by rw [Nat.add_comm 6 j, Nat.pow_add]; ring
  have hp5 : 2 ^ (5 + j) = 32 * 2 ^ j := by rw [Nat.add_comm 5 j, Nat.pow_add]; ring
  have hp3 : 2 ^ (3 + j) = 8 * 2 ^ j := by rw [Nat.add_comm 3 j, Nat.pow_add]; ring
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have he : LC ((2 ^ (3 + j) - 3) * 2 ^ 3) (shift 3 [0]) l := by
    refine hl.congr ?_ rfl rfl
    change k = (2 ^ (3 + j) - 3) * 8
    omega
  rcases LC_unzeros 3 he with ⟨l0, hl0, rfl⟩
  rcases LC_mark hl0 with ⟨l1, hl1, rfl⟩
  rcases LH_inc 3 (2 ^ (3 + j) - 3) [] l1 hl1 with ⟨l2, hl2, hinc⟩
  have hpow : LC (2 ^ (3 + j)) [] l2 := hl2.congr (by omega) rfl rfl
  have hl2_eq := LC_pow (3 + j) hpow
  subst hl2_eq
  rw [zero_move 3]
  have hstep1 : LH 16 (z0 ^ 3 +> ([0] +> (v +> l1)))
      (z0 ^ 3 +> (v +> ([0] +> (z0 ^ (3 + j) +> (z1 +> default))))) :=
    (LH_zeros 3 (LH_cross hinc)).congr rfl rfl rfl
  rw [zero_move (3 + j)] at hstep1
  have hsplit : z0 ^ 3 +> (v +> (z0 ^ (3 + j) +> ([0] +> (z1 +> default)))) =
      z0 +> (z0 +> (z0 +> (v +> (z0 +> (z0 +> (z0 ^ j +> (z0 +> ([0] +> (z1 +> default))))))))) := by
    have h3j : 3 + j = 2 + (j + 1) := by omega
    rw [h3j, pow_add_list, pow_succ_list' z0 j]
    simp only [pow_succ_list, pow_zero_list, append_assoc, append_nil, List.nil_append]
  rw [hsplit] at hstep1
  exact (LH_add hstep1 (LH_partial_D j)).congr (by omega) rfl rfl

lemma LH_partial_D_recover (j : ℕ) :
    LH (2 ^ (4 + j) + 12)
      (z0 +> (v +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default))))))))))
      (z0 +> (v +> (z0 +> (v +> (z0 +> (z0 +> (z0 ^ j +> (z0 +> (v +> default))))))))) := by
  have hp4 : 2 ^ (4 + j) = 16 * 2 ^ j := by rw [Nat.add_comm 4 j, Nat.pow_add]; ring
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have hb : SegRLs (flipTM tm) (Hs ^ 3) (Hs ^ 1) (z1 ++ z0) (z0 ++ z0) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 1000) (by decide)
  have ha : SegRLs (flipTM tm) (Hs ^ 4) Hs (z0 ++ z0) (z0 ++ z0) :=
    BoundedConfig.segRLs_c_spec (flipTM tm) (T := 1000) (by decide)
  have hseg := SegRLs.addmul (x := 2 ^ j) (a := 4) (b := 3) (c := 1) hb ha
  have htail : LH (2 ^ j + 1)
      (z1 ^ j +> (z0 +> ([0] +> (z1 +> default))))
      (z0 ^ j +> (z0 +> (v +> default))) := by
    have hc1 : LH 1 (z1 ^ j +> (z0 +> ([0] +> (z1 +> default))))
        (z0 ^ j +> (z1 +> ([0] +> (z1 +> default)))) :=
      LH_clear j (LH_set _)
    have hc2 : LH (2 ^ j) (z0 ^ j +> (z1 +> ([0] +> (z1 +> default))))
        (z0 ^ j +> (z0 +> (v +> default))) :=
      (LH_zeros j (LH_last default)).congr (by omega) rfl rfl
    exact (LH_add hc1 hc2).congr (by omega) rfl rfl
  have hmid : LH (2 ^ j * 4 + 3)
      (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default))))))
      (z0 +> (z0 +> (z0 ^ j +> (z0 +> (v +> default))))) := by
    simpa only [append_assoc] using hseg.sideRLs_concat htail
  have houter := LH_zero (LH_word (LH_zero (LH_word hmid)))
  exact houter.congr (by rw [hp4]; omega) rfl rfl

lemma LH_partial_D_finish (j : ℕ) (hj : 2 ≤ j) :
    ∃ l', LC (2 ^ (4 + j) - 19) [1, 1, 3 + j] l' ∧
      LH (2 ^ (5 + j) - 5)
        ([0] +> (z0 +> (z1 +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default))))))))))) l' := by
  have hp4 : 2 ^ (4 + j) = 16 * 2 ^ j := by rw [Nat.add_comm 4 j, Nat.pow_add]; ring
  have hp5 : 2 ^ (5 + j) = 32 * 2 ^ j := by rw [Nat.add_comm 5 j, Nat.pow_add]; ring
  have h4 : 4 ≤ 2 ^ j := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    simpa using this
  have hnum : LC 0 [1, 1, 3 + j]
      (z0 +> (v +> (z0 +> (v +> (z0 +> (z0 +> (z0 ^ j +> (z0 +> (v +> default))))))))) := by
    rw [show 3 + j = j + 3 by omega]
    apply LC.LC_0' 0 0 [1, j + 3]
    apply LC.LC_w 0 [1, j + 3]
    apply LC.LC_0' 0 0 [j + 3]
    apply LC.LC_w 0 [j + 3]
    apply LC.LC_0' 0 (j + 2) []
    apply LC.LC_0' 0 (j + 1) []
    have hzw := LC_zero_words (j + 1) (LC.LC_w 0 [] default .LC_0)
    rw [pow_succ_list', append_assoc] at hzw
    exact hzw.congr rfl (by simp [shift]) rfl
  rcases LH_inc (2 ^ (4 + j) - 19) 0 [1, 1, 3 + j] _ hnum with ⟨l', hl', hrun⟩
  refine ⟨l', hl'.congr (by omega) rfl rfl, ?_⟩
  have h0_comm : ([0] : zF) +> (z0 +> (z1 +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))))))))) =
      z0 +> ([0] +> (z1 +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))))))))) := rfl
  rw [h0_comm]
  have hstep1 : LH 2
      (z0 +> ([0] +> (z1 +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))))))))))
      (z0 +> (v +> (z0 +> (v +> (z1 +> (z0 +> (z1 ^ j +> (z0 +> ([0] +> (z1 +> default)))))))))) :=
    LH_zero (LH_absorb _)
  exact (LH_add hstep1 (LH_add (LH_partial_D_recover j) hrun)).congr (by omega) rfl rfl

lemma G_partial (j n : ℕ) (hn : n + 5 = 2 ^ (1 + j)) (l r : zB) (hd : Denote (RootG n) l r) :
    ∃ l' r', Denote (.st (2 ^ j - 1) [0, 1 + j] (n + 1) .t7) l' r' ∧
      (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r') := by
  have hp1 : 2 ^ (1 + j) = 2 * 2 ^ j := by rw [Nat.add_comm 1 j, Nat.pow_succ]; ring
  have hp2 : 2 ^ (2 + j) = 4 * 2 ^ j := by rw [Nat.add_comm 2 j, Nat.pow_add]; ring
  rcases hd with ⟨hl, hr⟩
  rcases BigStep0 hl hr with ⟨l0, r0, hl0, hr0, hdrop⟩
  have he : LC (2 ^ (2 + j)) [] l0 := hl0.congr (by omega) rfl rfl
  have hl0_eq := LC_pow (2 + j) he
  subst hl0_eq
  set midleft : zB := z1 +> (z0 ^ j +> (z1 +> ([0] +> (z1 +> default))))
  have hfirst : LH ((n + 1) + 4 + offset .t5) ([0] +> (z0 ^ (2 + j) +> (z1 +> default))) midleft := by
    rw [zero_move (2 + j)]
    have hsplit : z0 ^ (2 + j) +> ([0] +> (z1 +> default)) =
        z0 +> (z0 ^ j +> (z0 +> ([0] +> (z1 +> default)))) := by
      have h2j : 2 + j = (j + 1) + 1 := by omega
      rw [h2j, pow_add_list, pow_succ_list z0 j]
      simp only [pow_one_list, append_assoc]
    rw [hsplit]
    exact (LH_partial j default).congr (by dsimp [offset]; omega) rfl rfl
  rcases Phase hr0 hfirst with ⟨r1, hr1, hphase1⟩
  rcases LH_partial_finish j with ⟨l', hl', hfinish⟩
  have hlast : LH ((n + 1) + 4 + offset .t6) ([0] +> midleft) l' :=
    hfinish.congr (by dsimp [offset]; omega) rfl rfl
  rcases Phase hr1 hlast with ⟨r', hr', hphase2⟩
  exact ⟨l', r', ⟨hl', hr'⟩, stepPlus_trans hdrop (stepPlus_trans hphase1 hphase2)⟩

lemma D6_partial (j n : ℕ) (hj : 2 ≤ j) (hn : n + 14 = 2 ^ (5 + j)) (l r : zB) (hd : Denote (RootD 6 n) l r) :
    ∃ l' r', Denote (RootD (2 + j) (n + 8)) l' r' ∧
      (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r') := by
  have hp5 : 2 ^ (5 + j) = 32 * 2 ^ j := by rw [Nat.add_comm 5 j, Nat.pow_add]; ring
  have hp4 : 2 ^ (4 + j) = 16 * 2 ^ j := by rw [Nat.add_comm 4 j, Nat.pow_add]; ring
  have hp6 : 2 ^ (6 + j) = 64 * 2 ^ j := by rw [Nat.add_comm 6 j, Nat.pow_add]; ring
  have h4 : 4 ≤ 2 ^ j := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    simpa using this
  have hmod : n % 8 = 2 := by omega
  set q := n / 8
  have hq : n = q * 8 + 2 := by omega
  have hfirst : Steps (RootD 6 n) (.st (n * 2 + 4) [3] (n + 4) .t0) := by
    dsimp [RootD]
    phase_with (n * 2 - 40) (n + 1) { reven (q * 8 - 41) [5]; rodd (q * 4 - 21) [4] }
    phase_with (n * 2 - 19) (n + 1) { reven (q * 8 - 18) [0, 4]; rmark; rodd (q * 4 - 8) [3] }
    phase_with (n * 2 - 5) (n + 1) { rodd (q * 8 - 8) [0, 0, 3] }
    apply step_drop; apply step_drop; apply step_drop
    exact (Steps.Done _).congr (by congr 1; omega) rfl
  rcases Steps_spec hfirst l r hd with ⟨l0, r0, ⟨hl0, hr0⟩, hrun0⟩
  have hstart : (n * 2 + 4) + 24 = 2 ^ (6 + j) := by omega
  have hleft : LH ((n + 4) + 4 + offset .t0) ([0] +> l0) _ :=
    (LH_partial_D_start j (n * 2 + 4) l0 hstart hl0).congr (by dsimp [offset]; omega) rfl rfl
  rcases Phase hr0 hleft with ⟨r1, hr1, hrun1⟩
  rcases LH_partial_D_finish j hj with ⟨l1, hl1, hleft1_raw⟩
  have hleft1 : LH ((n + 4) + 4 + offset .t1) _ l1 :=
    hleft1_raw.congr (by dsimp [offset]; omega) rfl rfl
  rcases Phase hr1 hleft1 with ⟨r2, hr2, hrun2⟩
  have htail : Steps (.st (2 ^ (4 + j) - 19) [1, 1, 3 + j] (n + 4) .t2) (RootD (2 + j) (n + 8)) := by
    rw [show 2 ^ (4 + j) - 19 = n * 2 + 9 - 48 * 2 ^ j by omega]
    rw [show 3 + j = j + 3 by omega]
    phase_with (n * 2 + 11 - 24 * 2 ^ j) (n + 4) { rodd (q * 8 + 6 - 24 * 2 ^ j) [0, 1, (j + 3)] }
    phase_with (n * 2 + 17 - 12 * 2 ^ j) (n + 6) { rodd (q * 8 + 10 - 12 * 2 ^ j) [0, (j + 3)] }
    phase_with (n * 2 + 23 - 6 * 2 ^ j) (n + 8) { rodd (q * 8 + 13 - 6 * 2 ^ j) [(j + 2)] }
    unfold RootD
    have hp1 : 2 ^ (2 + j - 1) = 2 * 2 ^ j := by
      rw [show 2 + j - 1 = j + 1 by omega, Nat.pow_succ]; ring
    rw [hp1, show 2 + j = j + 2 by omega]
    exact (Steps.Done _).congr (by congr 1; omega) rfl
  rcases Steps_spec htail l1 r2 ⟨hl1, hr2⟩ with ⟨l', r', hd', hrun3⟩
  exact ⟨l', r', hd', stepStar_stepPlus_trans hrun0 (stepPlus_trans hrun1 (stepPlus_stepStar_trans hrun2 hrun3))⟩

lemma G_large_tail (a n : ℕ) (hlow : 2 ^ 15 * 2 ^ a ≤ n + 5) (hmod : n % 8 = 3) :
    Steps (.st (n * 2 + 9 - 3 * 2 ^ 14 * 2 ^ a) [0, 15 + a] (n + 1) .t7)
      (RootD (1 + a) (n + 15)) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  set q := n / 8
  have hq : n = q * 8 + 3 := by omega
  unfold RootD
  rw [show 1 + a - 1 = a by omega, show 15 + a = a + 15 by omega, show 1 + a = a + 1 by omega]
  have hlow' : 32768 * 2 ^ a ≤ n + 5 := hlow
  change Steps (.st (n * 2 + 9 - 49152 * 2 ^ a) [0, a + 15] (n + 1) .t7) _
  phase_with (n * 2 + 10 - 24576 * 2 ^ a) (n + 2) { reven (q * 8 + 9 - 24576 * 2 ^ a) [(a + 14)]; rodd (q * 4 + 4 - 12288 * 2 ^ a) [(a + 13)] }
  phase_with (n * 2 + 7 - 12288 * 2 ^ a) (n + 2) { reven (q * 8 + 8 - 12288 * 2 ^ a) [0, (a + 13)]; rmark; rodd (q * 4 + 5 - 6144 * 2 ^ a) [(a + 12)] }
  phase_with (n * 2 + 9 - 6144 * 2 ^ a) (n + 2) { rodd (q * 8 + 6 - 6144 * 2 ^ a) [0, 0, (a + 12)] }
  phase_with (n * 2 + 6 - 3072 * 2 ^ a) (n + 5) { reven (q * 8 + 12 - 3072 * 2 ^ a) [(a + 11)]; reven (q * 4 + 6 - 1536 * 2 ^ a) [(a + 10)]; reven (q * 2 + 3 - 768 * 2 ^ a) [(a + 9)]; rodd (q + 1 - 384 * 2 ^ a) [(a + 8)] }
  phase_with (n * 2 + 6 - 1536 * 2 ^ a) (n + 5) { reven (q * 8 + 6 - 1536 * 2 ^ a) [2, (a + 8)]; reven (q * 4 + 3 - 768 * 2 ^ a) [1, (a + 8)]; rodd (q * 2 + 1 - 384 * 2 ^ a) [0, (a + 8)] }
  phase_with (n * 2 + 3 - 768 * 2 ^ a) (n + 5) { reven (q * 8 + 6 - 768 * 2 ^ a) [1, 0, (a + 8)]; reven (q * 4 + 3 - 384 * 2 ^ a) [0, 0, (a + 8)]; rmark; rmark; rodd (q * 2 + 4 - 192 * 2 ^ a) [(a + 7)] }
  phase_with (n * 2 + 10 - 384 * 2 ^ a) (n + 5) { rodd (q * 8 + 4 - 384 * 2 ^ a) [1, 0, 0, (a + 7)] }
  phase_with (n * 2 + 15 - 192 * 2 ^ a) (n + 6) { rodd (q * 8 + 9 - 192 * 2 ^ a) [0, 0, 0, (a + 7)] }
  phase_with (n * 2 + 27 - 96 * 2 ^ a) (n + 10) { rodd (q * 8 + 16 - 96 * 2 ^ a) [(a + 6)] }
  phase_with (n * 2 + 24 - 48 * 2 ^ a) (n + 11) { reven (q * 8 + 18 - 48 * 2 ^ a) [(a + 5)]; reven (q * 4 + 9 - 24 * 2 ^ a) [(a + 4)]; rodd (q * 2 + 4 - 12 * 2 ^ a) [(a + 3)] }
  phase_with (n * 2 + 25 - 24 * 2 ^ a) (n + 11) { reven (q * 8 + 15 - 24 * 2 ^ a) [1, (a + 3)]; rodd (q * 4 + 7 - 12 * 2 ^ a) [0, (a + 3)] }
  phase_with (n * 2 + 26 - 12 * 2 ^ a) (n + 11) { rodd (q * 8 + 15 - 12 * 2 ^ a) [0, 0, (a + 3)] }
  phase_with (n * 2 + 34 - 6 * 2 ^ a) (n + 14) { rodd (q * 8 + 20 - 6 * 2 ^ a) [(a + 2)] }
  phase_with (n * 2 + 37 - 3 * 2 ^ a) (n + 15) { rodd (q * 8 + 21 - 3 * 2 ^ a) [(a + 1)] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_2 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 16 = 3) :
    Steps (.st (n * 2 + 9 - 12) [0, 3] (n + 1) .t7) (RootG (n + 8)) := by
  set q := n / 16
  have hq : n = q * 16 + 3 := by omega
  dsimp [RootG]
  phase_with (n * 2 + 4) (n + 2) { reven (q * 16 + 3) [2]; rodd (q * 8 + 1) [1] }
  phase_with (n * 2 - 1) (n + 2) { reven (q * 16 + 5) [0, 1]; rmark; reven (q * 8 + 4) [0]; rmark; rodd (q * 4 + 3) [] }
  phase_with (n * 2 + 5) (n + 2) { rodd (q * 16 + 2) [0, 1, 0] }
  phase_with (n * 2 + 12) (n + 4) { rodd (q * 16 + 8) [0, 0] }
  phase_with (n * 2 + 20) (n + 7) { rodd (q * 16 + 13) [] }
  phase_with (n * 2 + 23) (n + 8) { rodd (q * 16 + 14) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_3 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 32 = 11) :
    Steps (.st (n * 2 + 9 - 24) [0, 4] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 32
  have hq : n = q * 32 + 11 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 2) (n + 2) { reven (q * 32 + 5) [3]; rodd (q * 16 + 2) [2] }
  phase_with (n * 2 + 1) (n + 2) { reven (q * 32 + 10) [0, 2]; rmark; rodd (q * 16 + 6) [1] }
  phase_with (n * 2 + 6) (n + 2) { rodd (q * 32 + 11) [0, 0, 1] }
  phase_with (n * 2 + 15) (n + 5) { rodd (q * 32 + 18) [0] }
  phase_with (n * 2 + 20) (n + 7) { rodd (q * 32 + 21) [] }
  phase_with (n * 2 + 23) (n + 8) { rodd (q * 32 + 22) [] }
  phase_with (n * 2 + 3) (n + 9) { reven (q * 32 + 24) []; reven (q * 16 + 12) []; reven (q * 8 + 6) []; reven (q * 4 + 3) []; rodd (q * 2 + 1) [] }
  phase_with (n * 2 + 13) (n + 9) { rodd (q * 32 + 12) [3] }
  phase_with (n * 2 + 20) (n + 10) { reven (q * 32 + 19) [2]; rodd (q * 16 + 9) [1] }
  phase_with (n * 2 + 15) (n + 10) { reven (q * 32 + 21) [0, 1]; rmark; reven (q * 16 + 12) [0]; rmark; rodd (q * 8 + 7) [] }
  phase_with (n * 2 + 21) (n + 10) { rodd (q * 32 + 18) [0, 1, 0] }
  phase_with (n * 2 + 28) (n + 12) { rodd (q * 32 + 24) [0, 0] }
  phase_with (n * 2 + 36) (n + 15) { rodd (q * 32 + 29) [] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 32 + 30) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_4 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 64 = 27) :
    Steps (.st (n * 2 + 9 - 48) [0, 5] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 64
  have hq : n = q * 64 + 27 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 14) (n + 2) { reven (q * 64 + 9) [4]; rodd (q * 32 + 4) [3] }
  phase_with (n * 2 - 5) (n + 2) { reven (q * 64 + 20) [0, 3]; rmark; rodd (q * 32 + 11) [2] }
  phase_with (n * 2 + 3) (n + 2) { rodd (q * 64 + 24) [0, 0, 2] }
  phase_with (n * 2 + 12) (n + 5) { reven (q * 64 + 33) [1]; rodd (q * 32 + 16) [0] }
  phase_with (n * 2 + 10) (n + 5) { reven (q * 64 + 33) [0, 0]; rmark; rmark; rodd (q * 32 + 19) [] }
  phase_with (n * 2 + 9) (n + 5) { reven (q * 64 + 32) [0, 0, 0]; rmark; rmark; rmark; rodd (q * 32 + 20) [] }
  phase_with (n * 2 + 13) (n + 5) { rodd (q * 64 + 31) [0, 0, 0, 0] }
  phase_with (n * 2 + 25) (n + 10) { reven (q * 64 + 41) []; rodd (q * 32 + 20) [] }
  phase_with (n * 2 + 26) (n + 10) { rodd (q * 64 + 39) [0] }
  phase_with (n * 2 + 29) (n + 12) { reven (q * 64 + 43) []; rodd (q * 32 + 21) [] }
  phase_with (n * 2 + 30) (n + 12) { rodd (q * 64 + 41) [0] }
  phase_with (n * 2 + 33) (n + 14) { reven (q * 64 + 45) []; rodd (q * 32 + 22) [] }
  phase_with (n * 2 + 33) (n + 14) { rodd (q * 64 + 43) [0] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 64 + 46) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_5 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 128 = 59) :
    Steps (.st (n * 2 + 9 - 96) [0, 6] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 128
  have hq : n = q * 128 + 59 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 38) (n + 2) { reven (q * 128 + 17) [5]; rodd (q * 64 + 8) [4] }
  phase_with (n * 2 - 17) (n + 2) { reven (q * 128 + 40) [0, 4]; rmark; rodd (q * 64 + 21) [3] }
  phase_with (n * 2 - 3) (n + 2) { rodd (q * 128 + 50) [0, 0, 3] }
  phase_with (n * 2 + 6) (n + 5) { reven (q * 128 + 62) [2]; reven (q * 64 + 31) [1]; rodd (q * 32 + 15) [0] }
  phase_with (n * 2 + 2) (n + 5) { reven (q * 128 + 62) [1, 0]; reven (q * 64 + 31) [0, 0]; rmark; rmark; rodd (q * 32 + 18) [] }
  phase_with (n * 2 - 1) (n + 5) { reven (q * 128 + 60) [1, 0, 0]; reven (q * 64 + 30) [0, 0, 0]; rmark; rmark; rmark; rodd (q * 32 + 19) [] }
  phase_with (n * 2 + 8) (n + 5) { rodd (q * 128 + 58) [1, 0, 0, 0] }
  phase_with (n * 2 + 14) (n + 6) { rodd (q * 128 + 64) [0, 0, 0, 0] }
  phase_with (n * 2 + 29) (n + 11) { rodd (q * 128 + 73) [] }
  phase_with (n * 2 + 29) (n + 12) { reven (q * 128 + 75) []; rodd (q * 64 + 37) [] }
  phase_with (n * 2 + 30) (n + 12) { rodd (q * 128 + 73) [0] }
  phase_with (n * 2 + 33) (n + 14) { reven (q * 128 + 77) []; rodd (q * 64 + 38) [] }
  phase_with (n * 2 + 33) (n + 14) { rodd (q * 128 + 75) [0] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 128 + 78) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_6 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 256 = 123) :
    Steps (.st (n * 2 + 9 - 192) [0, 7] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 256
  have hq : n = q * 256 + 123 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 86) (n + 2) { reven (q * 256 + 33) [6]; rodd (q * 128 + 16) [5] }
  phase_with (n * 2 - 41) (n + 2) { reven (q * 256 + 80) [0, 5]; rmark; rodd (q * 128 + 41) [4] }
  phase_with (n * 2 - 15) (n + 2) { rodd (q * 256 + 102) [0, 0, 4] }
  phase_with (n * 2 - 50) (n + 5) { reven (q * 256 + 120) [3]; reven (q * 128 + 60) [2]; reven (q * 64 + 30) [1]; reven (q * 32 + 15) [0]; rmark; reven (q * 16 + 9) []; rodd (q * 8 + 4) [] }
  phase_with (n * 2 - 22) (n + 5) { reven (q * 256 + 98) [3, 1]; reven (q * 128 + 49) [2, 1]; rodd (q * 64 + 24) [1, 1] }
  phase_with (n * 2 - 9) (n + 5) { reven (q * 256 + 112) [1, 1, 1]; reven (q * 128 + 56) [0, 1, 1]; rmark; rodd (q * 64 + 29) [0, 1] }
  phase_with (n * 2 + 4) (n + 5) { rodd (q * 256 + 118) [1, 0, 0, 1] }
  phase_with (n * 2 + 12) (n + 6) { rodd (q * 256 + 126) [0, 0, 0, 1] }
  phase_with (n * 2 + 20) (n + 10) { reven (q * 256 + 135) [0]; rmark; reven (q * 128 + 69) []; rodd (q * 64 + 34) [] }
  phase_with (n * 2 + 15) (n + 10) { reven (q * 256 + 133) [0, 1]; rmark; reven (q * 128 + 68) [0]; rmark; rodd (q * 64 + 35) [] }
  phase_with (n * 2 + 21) (n + 10) { rodd (q * 256 + 130) [0, 1, 0] }
  phase_with (n * 2 + 28) (n + 12) { rodd (q * 256 + 136) [0, 0] }
  phase_with (n * 2 + 36) (n + 15) { rodd (q * 256 + 141) [] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 256 + 142) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_7 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 512 = 251) :
    Steps (.st (n * 2 + 9 - 384) [0, 8] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 512
  have hq : n = q * 512 + 251 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 182) (n + 2) { reven (q * 512 + 65) [7]; rodd (q * 256 + 32) [6] }
  phase_with (n * 2 - 89) (n + 2) { reven (q * 512 + 160) [0, 6]; rmark; rodd (q * 256 + 81) [5] }
  phase_with (n * 2 - 39) (n + 2) { rodd (q * 512 + 206) [0, 0, 5] }
  phase_with (n * 2 - 18) (n + 5) { reven (q * 512 + 236) [4]; reven (q * 256 + 118) [3]; reven (q * 128 + 59) [2]; rodd (q * 64 + 29) [1] }
  phase_with (n * 2 - 6) (n + 5) { reven (q * 512 + 242) [2, 1]; reven (q * 256 + 121) [1, 1]; rodd (q * 128 + 60) [0, 1] }
  phase_with (n * 2 - 49) (n + 5) { reven (q * 512 + 248) [1, 0, 1]; reven (q * 256 + 124) [0, 0, 1]; rmark; rmark; reven (q * 128 + 65) [0]; rmark; reven (q * 64 + 34) []; reven (q * 32 + 17) []; rodd (q * 16 + 8) [] }
  phase_with (n * 2 - 16) (n + 5) { rodd (q * 512 + 226) [1, 0, 1, 2] }
  phase_with (n * 2 + 2) (n + 6) { rodd (q * 512 + 244) [0, 0, 1, 2] }
  phase_with (n * 2 + 18) (n + 9) { rodd (q * 512 + 256) [0, 2] }
  phase_with (n * 2 + 24) (n + 11) { reven (q * 512 + 263) [1]; rodd (q * 256 + 131) [0] }
  phase_with (n * 2 + 23) (n + 11) { reven (q * 512 + 263) [0, 0]; rmark; rmark; rodd (q * 256 + 134) [] }
  phase_with (n * 2 + 25) (n + 11) { rodd (q * 512 + 262) [0, 0, 0] }
  phase_with (n * 2 + 36) (n + 15) { rodd (q * 512 + 269) [] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 512 + 270) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_8 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 1024 = 507) :
    Steps (.st (n * 2 + 9 - 768) [0, 9] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 1024
  have hq : n = q * 1024 + 507 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 374) (n + 2) { reven (q * 1024 + 129) [8]; rodd (q * 512 + 64) [7] }
  phase_with (n * 2 - 185) (n + 2) { reven (q * 1024 + 320) [0, 7]; rmark; rodd (q * 512 + 161) [6] }
  phase_with (n * 2 - 87) (n + 2) { rodd (q * 1024 + 414) [0, 0, 6] }
  phase_with (n * 2 - 42) (n + 5) { reven (q * 1024 + 468) [5]; reven (q * 512 + 234) [4]; reven (q * 256 + 117) [3]; rodd (q * 128 + 58) [2] }
  phase_with (n * 2 - 18) (n + 5) { reven (q * 1024 + 486) [2, 2]; reven (q * 512 + 243) [1, 2]; rodd (q * 256 + 121) [0, 2] }
  phase_with (n * 2 - 9) (n + 5) { reven (q * 1024 + 498) [1, 0, 2]; reven (q * 512 + 249) [0, 0, 2]; rmark; rmark; rodd (q * 256 + 127) [1] }
  phase_with (n * 2 + 4) (n + 5) { rodd (q * 1024 + 502) [1, 0, 0, 1] }
  phase_with (n * 2 + 12) (n + 6) { rodd (q * 1024 + 510) [0, 0, 0, 1] }
  phase_with (n * 2 + 20) (n + 10) { reven (q * 1024 + 519) [0]; rmark; reven (q * 512 + 261) []; rodd (q * 256 + 130) [] }
  phase_with (n * 2 + 15) (n + 10) { reven (q * 1024 + 517) [0, 1]; rmark; reven (q * 512 + 260) [0]; rmark; rodd (q * 256 + 131) [] }
  phase_with (n * 2 + 21) (n + 10) { rodd (q * 1024 + 514) [0, 1, 0] }
  phase_with (n * 2 + 28) (n + 12) { rodd (q * 1024 + 520) [0, 0] }
  phase_with (n * 2 + 36) (n + 15) { rodd (q * 1024 + 525) [] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 1024 + 526) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_9 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 2048 = 1019) :
    Steps (.st (n * 2 + 9 - 1536) [0, 10] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 2048
  have hq : n = q * 2048 + 1019 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 758) (n + 2) { reven (q * 2048 + 257) [9]; rodd (q * 1024 + 128) [8] }
  phase_with (n * 2 - 377) (n + 2) { reven (q * 2048 + 640) [0, 8]; rmark; rodd (q * 1024 + 321) [7] }
  phase_with (n * 2 - 183) (n + 2) { rodd (q * 2048 + 830) [0, 0, 7] }
  phase_with (n * 2 - 90) (n + 5) { reven (q * 2048 + 932) [6]; reven (q * 1024 + 466) [5]; reven (q * 512 + 233) [4]; rodd (q * 256 + 116) [3] }
  phase_with (n * 2 - 42) (n + 5) { reven (q * 2048 + 974) [2, 3]; reven (q * 1024 + 487) [1, 3]; rodd (q * 512 + 243) [0, 3] }
  phase_with (n * 2 - 21) (n + 5) { reven (q * 2048 + 998) [1, 0, 3]; reven (q * 1024 + 499) [0, 0, 3]; rmark; rmark; rodd (q * 512 + 252) [2] }
  phase_with (n * 2 - 2) (n + 5) { rodd (q * 2048 + 1008) [1, 0, 0, 2] }
  phase_with (n * 2 + 9) (n + 6) { rodd (q * 2048 + 1019) [0, 0, 0, 2] }
  phase_with (n * 2 + 24) (n + 10) { rodd (q * 2048 + 1029) [1] }
  phase_with (n * 2 + 27) (n + 11) { rodd (q * 2048 + 1032) [0] }
  phase_with (n * 2 + 33) (n + 13) { rodd (q * 2048 + 1035) [] }
  phase_with (n * 2 + 33) (n + 14) { reven (q * 2048 + 1037) []; rodd (q * 1024 + 518) [] }
  phase_with (n * 2 + 33) (n + 14) { rodd (q * 2048 + 1035) [0] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 2048 + 1038) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_10 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 4096 = 2043) :
    Steps (.st (n * 2 + 9 - 3072) [0, 11] (n + 1) .t7) (RootG (n + 16)) := by
  set q := n / 4096
  have hq : n = q * 4096 + 2043 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 1526) (n + 2) { reven (q * 4096 + 513) [10]; rodd (q * 2048 + 256) [9] }
  phase_with (n * 2 - 761) (n + 2) { reven (q * 4096 + 1280) [0, 9]; rmark; rodd (q * 2048 + 641) [8] }
  phase_with (n * 2 - 375) (n + 2) { rodd (q * 4096 + 1662) [0, 0, 8] }
  phase_with (n * 2 - 186) (n + 5) { reven (q * 4096 + 1860) [7]; reven (q * 2048 + 930) [6]; reven (q * 1024 + 465) [5]; rodd (q * 512 + 232) [4] }
  phase_with (n * 2 - 90) (n + 5) { reven (q * 4096 + 1950) [2, 4]; reven (q * 2048 + 975) [1, 4]; rodd (q * 1024 + 487) [0, 4] }
  phase_with (n * 2 - 45) (n + 5) { reven (q * 4096 + 1998) [1, 0, 4]; reven (q * 2048 + 999) [0, 0, 4]; rmark; rmark; rodd (q * 1024 + 502) [3] }
  phase_with (n * 2 - 14) (n + 5) { rodd (q * 4096 + 2020) [1, 0, 0, 3] }
  phase_with (n * 2 + 3) (n + 6) { rodd (q * 4096 + 2037) [0, 0, 0, 3] }
  phase_with (n * 2 + 21) (n + 10) { rodd (q * 4096 + 2050) [2] }
  phase_with (n * 2 + 24) (n + 11) { reven (q * 4096 + 2055) [1]; rodd (q * 2048 + 1027) [0] }
  phase_with (n * 2 + 23) (n + 11) { reven (q * 4096 + 2055) [0, 0]; rmark; rmark; rodd (q * 2048 + 1030) [] }
  phase_with (n * 2 + 25) (n + 11) { rodd (q * 4096 + 2054) [0, 0, 0] }
  phase_with (n * 2 + 36) (n + 15) { rodd (q * 4096 + 2061) [] }
  phase_with (n * 2 + 39) (n + 16) { rodd (q * 4096 + 2062) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_11 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 8192 = 4091) :
    Steps (.st (n * 2 + 9 - 6144) [0, 12] (n + 1) .t7) (RootG (n + 24)) := by
  set q := n / 8192
  have hq : n = q * 8192 + 4091 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 3062) (n + 2) { reven (q * 8192 + 1025) [11]; rodd (q * 4096 + 512) [10] }
  phase_with (n * 2 - 1529) (n + 2) { reven (q * 8192 + 2560) [0, 10]; rmark; rodd (q * 4096 + 1281) [9] }
  phase_with (n * 2 - 759) (n + 2) { rodd (q * 8192 + 3326) [0, 0, 9] }
  phase_with (n * 2 - 378) (n + 5) { reven (q * 8192 + 3716) [8]; reven (q * 4096 + 1858) [7]; reven (q * 2048 + 929) [6]; rodd (q * 1024 + 464) [5] }
  phase_with (n * 2 - 186) (n + 5) { reven (q * 8192 + 3902) [2, 5]; reven (q * 4096 + 1951) [1, 5]; rodd (q * 2048 + 975) [0, 5] }
  phase_with (n * 2 - 93) (n + 5) { reven (q * 8192 + 3998) [1, 0, 5]; reven (q * 4096 + 1999) [0, 0, 5]; rmark; rmark; rodd (q * 2048 + 1002) [4] }
  phase_with (n * 2 - 38) (n + 5) { rodd (q * 8192 + 4044) [1, 0, 0, 4] }
  phase_with (n * 2 - 9) (n + 6) { rodd (q * 8192 + 4073) [0, 0, 0, 4] }
  phase_with (n * 2 + 15) (n + 10) { rodd (q * 8192 + 4092) [3] }
  phase_with (n * 2 - 28) (n + 11) { reven (q * 8192 + 4100) [2]; reven (q * 4096 + 2050) [1]; reven (q * 2048 + 1025) [0]; rmark; reven (q * 1024 + 514) []; reven (q * 512 + 257) []; rodd (q * 256 + 128) [] }
  phase_with (n * 2 - 1) (n + 11) { reven (q * 8192 + 4077) [2, 2]; rodd (q * 4096 + 2038) [1, 2] }
  phase_with (n * 2 + 13) (n + 11) { rodd (q * 8192 + 4090) [0, 1, 2] }
  phase_with (n * 2 + 25) (n + 13) { rodd (q * 8192 + 4100) [0, 2] }
  phase_with (n * 2 + 34) (n + 15) { rodd (q * 8192 + 4106) [1] }
  phase_with (n * 2 + 38) (n + 16) { rodd (q * 8192 + 4109) [0] }
  phase_with (n * 2 + 41) (n + 18) { reven (q * 8192 + 4113) []; rodd (q * 4096 + 2056) [] }
  phase_with (n * 2 + 42) (n + 18) { rodd (q * 8192 + 4111) [0] }
  phase_with (n * 2 + 45) (n + 20) { reven (q * 8192 + 4115) []; rodd (q * 4096 + 2057) [] }
  phase_with (n * 2 + 46) (n + 20) { rodd (q * 8192 + 4113) [0] }
  phase_with (n * 2 + 49) (n + 22) { reven (q * 8192 + 4117) []; rodd (q * 4096 + 2058) [] }
  phase_with (n * 2 + 49) (n + 22) { rodd (q * 8192 + 4115) [0] }
  phase_with (n * 2 + 55) (n + 24) { rodd (q * 8192 + 4118) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_12 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 16384 = 8187) :
    Steps (.st (n * 2 + 9 - 12288) [0, 13] (n + 1) .t7) (RootG (n + 24)) := by
  set q := n / 16384
  have hq : n = q * 16384 + 8187 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 6134) (n + 2) { reven (q * 16384 + 2049) [12]; rodd (q * 8192 + 1024) [11] }
  phase_with (n * 2 - 3065) (n + 2) { reven (q * 16384 + 5120) [0, 11]; rmark; rodd (q * 8192 + 2561) [10] }
  phase_with (n * 2 - 1527) (n + 2) { rodd (q * 16384 + 6654) [0, 0, 10] }
  phase_with (n * 2 - 762) (n + 5) { reven (q * 16384 + 7428) [9]; reven (q * 8192 + 3714) [8]; reven (q * 4096 + 1857) [7]; rodd (q * 2048 + 928) [6] }
  phase_with (n * 2 - 378) (n + 5) { reven (q * 16384 + 7806) [2, 6]; reven (q * 8192 + 3903) [1, 6]; rodd (q * 4096 + 1951) [0, 6] }
  phase_with (n * 2 - 189) (n + 5) { reven (q * 16384 + 7998) [1, 0, 6]; reven (q * 8192 + 3999) [0, 0, 6]; rmark; rmark; rodd (q * 4096 + 2002) [5] }
  phase_with (n * 2 - 86) (n + 5) { rodd (q * 16384 + 8092) [1, 0, 0, 5] }
  phase_with (n * 2 - 33) (n + 6) { rodd (q * 16384 + 8145) [0, 0, 0, 5] }
  phase_with (n * 2 + 3) (n + 10) { rodd (q * 16384 + 8176) [4] }
  phase_with (n * 2 + 12) (n + 11) { reven (q * 16384 + 8190) [3]; reven (q * 8192 + 4095) [2]; rodd (q * 4096 + 2047) [1] }
  phase_with (n * 2 + 19) (n + 11) { reven (q * 16384 + 8193) [1, 1]; rodd (q * 8192 + 4096) [0, 1] }
  phase_with (n * 2 + 23) (n + 11) { rodd (q * 16384 + 8196) [0, 0, 1] }
  phase_with (n * 2 + 27) (n + 14) { reven (q * 16384 + 8203) [0]; rmark; reven (q * 8192 + 4103) []; rodd (q * 4096 + 2051) [] }
  phase_with (n * 2 + 31) (n + 14) { rodd (q * 16384 + 8200) [0, 1] }
  phase_with (n * 2 + 38) (n + 16) { rodd (q * 16384 + 8205) [0] }
  phase_with (n * 2 + 41) (n + 18) { reven (q * 16384 + 8209) []; rodd (q * 8192 + 4104) [] }
  phase_with (n * 2 + 42) (n + 18) { rodd (q * 16384 + 8207) [0] }
  phase_with (n * 2 + 45) (n + 20) { reven (q * 16384 + 8211) []; rodd (q * 8192 + 4105) [] }
  phase_with (n * 2 + 46) (n + 20) { rodd (q * 16384 + 8209) [0] }
  phase_with (n * 2 + 49) (n + 22) { reven (q * 16384 + 8213) []; rodd (q * 8192 + 4106) [] }
  phase_with (n * 2 + 49) (n + 22) { rodd (q * 16384 + 8211) [0] }
  phase_with (n * 2 + 55) (n + 24) { rodd (q * 16384 + 8214) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

private lemma G_small_tail_13 (n : ℕ) (hn : 11 ≤ n) (hmod : n % 32768 = 16379) :
    Steps (.st (n * 2 + 9 - 24576) [0, 14] (n + 1) .t7) (RootG (n + 24)) := by
  set q := n / 32768
  have hq : n = q * 32768 + 16379 := by omega
  dsimp [RootG]
  phase_with (n * 2 - 12278) (n + 2) { reven (q * 32768 + 4097) [13]; rodd (q * 16384 + 2048) [12] }
  phase_with (n * 2 - 6137) (n + 2) { reven (q * 32768 + 10240) [0, 12]; rmark; rodd (q * 16384 + 5121) [11] }
  phase_with (n * 2 - 3063) (n + 2) { rodd (q * 32768 + 13310) [0, 0, 11] }
  phase_with (n * 2 - 1530) (n + 5) { reven (q * 32768 + 14852) [10]; reven (q * 16384 + 7426) [9]; reven (q * 8192 + 3713) [8]; rodd (q * 4096 + 1856) [7] }
  phase_with (n * 2 - 762) (n + 5) { reven (q * 32768 + 15614) [2, 7]; reven (q * 16384 + 7807) [1, 7]; rodd (q * 8192 + 3903) [0, 7] }
  phase_with (n * 2 - 381) (n + 5) { reven (q * 32768 + 15998) [1, 0, 7]; reven (q * 16384 + 7999) [0, 0, 7]; rmark; rmark; rodd (q * 8192 + 4002) [6] }
  phase_with (n * 2 - 182) (n + 5) { rodd (q * 32768 + 16188) [1, 0, 0, 6] }
  phase_with (n * 2 - 81) (n + 6) { rodd (q * 32768 + 16289) [0, 0, 0, 6] }
  phase_with (n * 2 - 21) (n + 10) { rodd (q * 32768 + 16344) [5] }
  phase_with (n * 2) (n + 11) { reven (q * 32768 + 16370) [4]; reven (q * 16384 + 8185) [3]; rodd (q * 8192 + 4092) [2] }
  phase_with (n * 2 + 13) (n + 11) { reven (q * 32768 + 16379) [1, 2]; rodd (q * 16384 + 8189) [0, 2] }
  phase_with (n * 2 + 20) (n + 11) { rodd (q * 32768 + 16385) [0, 0, 2] }
  phase_with (n * 2 + 31) (n + 14) { rodd (q * 32768 + 16393) [1] }
  phase_with (n * 2 + 33) (n + 15) { reven (q * 32768 + 16396) [0]; rmark; rodd (q * 16384 + 8199) [] }
  phase_with (n * 2 + 35) (n + 15) { rodd (q * 32768 + 16395) [0, 0] }
  phase_with (n * 2 + 41) (n + 18) { reven (q * 32768 + 16401) []; rodd (q * 16384 + 8200) [] }
  phase_with (n * 2 + 42) (n + 18) { rodd (q * 32768 + 16399) [0] }
  phase_with (n * 2 + 45) (n + 20) { reven (q * 32768 + 16403) []; rodd (q * 16384 + 8201) [] }
  phase_with (n * 2 + 46) (n + 20) { rodd (q * 32768 + 16401) [0] }
  phase_with (n * 2 + 49) (n + 22) { reven (q * 32768 + 16405) []; rodd (q * 16384 + 8202) [] }
  phase_with (n * 2 + 49) (n + 22) { rodd (q * 32768 + 16403) [0] }
  phase_with (n * 2 + 55) (n + 24) { rodd (q * 32768 + 16406) [] }
  exact (Steps.Done _).congr (by congr 1; omega) rfl

lemma G_small_tail (j n : ℕ) (hj1 : 2 ≤ j) (hj2 : j ≤ 13) (hn : 11 ≤ n)
    (hmod : n % 2 ^ (j + 2) = 2 ^ (j + 1) - 5) :
    Steps (.st (n * 2 + 9 - 3 * 2 ^ j) [0, 1 + j] (n + 1) .t7)
      (RootG (n + 8 * ((j + 13) / 8))) := by
  rcases (by omega : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
      j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G_small_tail_2 n hn hmod
  · exact G_small_tail_3 n hn hmod
  · exact G_small_tail_4 n hn hmod
  · exact G_small_tail_5 n hn hmod
  · exact G_small_tail_6 n hn hmod
  · exact G_small_tail_7 n hn hmod
  · exact G_small_tail_8 n hn hmod
  · exact G_small_tail_9 n hn hmod
  · exact G_small_tail_10 n hn hmod
  · exact G_small_tail_11 n hn hmod
  · exact G_small_tail_12 n hn hmod
  · exact G_small_tail_13 n hn hmod

def Forward (s s' : State) : Prop :=
  ∀ l r, Denote s l r → ∃ l' r', Denote s' l' r' ∧ (l {{E}}> r) [tm]⊢⁺ (l' {{E}}> r')

lemma Steps_forward {s s' : State} (hneq : s ≠ s') (hsteps : Steps s s') :
    Forward s s' := by
  intro l r hd
  cases hsteps with
  | Done => contradiction
  | Advance hnext hrest =>
    rcases Next_spec hnext l r hd with ⟨l0, r0, hd0, hrun0⟩
    rcases Steps_spec hrest l0 r0 hd0 with ⟨l', r', hd', hrun'⟩
    exact ⟨l', r', hd', stepPlus_stepStar_trans hrun0 hrun'⟩

lemma Forward_steps {s t u : State} (h0 : Forward s t) (h1 : Steps t u) :
    Forward s u := by
  intro l r hd
  rcases h0 l r hd with ⟨l0, r0, hd0, hrun0⟩
  rcases Steps_spec h1 l0 r0 hd0 with ⟨l', r', hd', hrun'⟩
  exact ⟨l', r', hd', stepPlus_stepStar_trans hrun0 hrun'⟩

lemma factor2 (n : ℕ) (hn : 0 < n) : ∃ i u, n = (u * 2 + 1) * 2 ^ i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hodd : n % 2 = 1
    · exact ⟨0, n / 2, by omega⟩
    · rcases ih (n / 2) (by omega) (by omega) with ⟨i, u, hu⟩
      refine ⟨i + 1, u, ?_⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega

lemma G_begin (j u n : ℕ) (hj : 2 ≤ j) (hval : n + 5 = (u * 2 + 1) * 2 ^ (1 + j)) :
    Forward (RootG n) (.st (n * 2 + 9 - 3 * 2 ^ j) [0, 1 + j] (n + 1) .t7) := by
  rcases u with _ | u
  · have hval' : n + 5 = 2 ^ (1 + j) := by simpa using hval
    have hp1 : 2 ^ (1 + j) = 2 * 2 ^ j := by rw [Nat.add_comm 1 j, Nat.pow_succ]; ring
    intro l r hd
    rcases G_partial j n hval' l r hd with ⟨l', r', hd', hrun⟩
    exact ⟨l', r', hd'.congr (by congr 1; omega) rfl rfl, hrun⟩
  · rw [show (u + 1) * 2 + 1 = u * 2 + 3 by omega] at hval
    refine Steps_forward ?_ (G_start j u n hj hval)
    unfold RootG
    intro heq
    injection heq with _ _ hn_eq
    omega

inductive Ready : State → Prop where
  | ReadyG (n : ℕ) : 11 ≤ n → n % 8 = 3 → Ready (RootG n)
  | ReadyD (h n : ℕ) : 1 ≤ h → 64 ≤ n → n % 8 = 2 → 3 * 2 ^ (h - 1) ≤ n * 2 → Ready (RootD h n)
  | ReadyE (n : ℕ) : 64 ≤ n → n % 8 = 2 → Ready (RootE n)
  | ReadyF (n : ℕ) : 64 ≤ n → n % 8 = 1 → Ready (RootF n)

lemma G_ready (n : ℕ) (hn : 11 ≤ n) (hmod : n % 8 = 3) :
    ∃ s, Ready s ∧ Forward (RootG n) s := by
  rcases factor2 ((n + 5) / 8) (by omega) with ⟨i, u, hu⟩
  have hval : n + 5 = (u * 2 + 1) * 2 ^ (1 + (2 + i)) := by
    rw [show 1 + (2 + i) = i + 3 by omega, Nat.pow_add, ← Nat.mul_assoc]
    change n + 5 = ((u * 2 + 1) * 2 ^ i) * 8
    omega
  have hlow : 2 ^ (1 + (2 + i)) ≤ n + 5 := by
    have : 1 * 2 ^ (1 + (2 + i)) ≤ (u * 2 + 1) * 2 ^ (1 + (2 + i)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hbegin := G_begin (2 + i) u n (by omega) hval
  by_cases hi : i ≤ 11
  · refine ⟨RootG (n + 8 * ((2 + i + 13) / 8)), .ReadyG _ (by omega) (by omega), ?_⟩
    refine Forward_steps hbegin (G_small_tail (2 + i) n (by omega) (by omega) hn ?_)
    have hp4 : 4 ≤ 2 ^ (2 + i) := by
      rw [Nat.add_comm 2 i, Nat.pow_add]
      have : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by decide)
      omega
    have hp_2 : 2 ^ (2 + i + 2) = 2 ^ (2 + i) * 4 := by rw [Nat.pow_add]
    have hp_1 : 2 ^ (2 + i + 1) = 2 ^ (2 + i) * 2 := by rw [Nat.pow_succ]
    have hval' : n + 5 = 2 ^ (2 + i) * 2 + (2 ^ (2 + i) * 4) * u := by
      have h0 : n + 5 = (u * 2 + 1) * (2 ^ (2 + i) * 2) := by
        rwa [show 1 + (2 + i) = 2 + i + 1 by omega, hp_1] at hval
      rw [h0]; ring
    have h_eq : n = (2 ^ (2 + i) * 2 - 5) + (2 ^ (2 + i) * 4) * u := by omega
    rw [hp_2, hp_1, h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · set a := i - 12
    have hi' : i = 12 + a := by omega
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
    have hpow : 2 ^ (1 + (2 + i)) = 2 ^ 15 * 2 ^ a := by
      rw [show 1 + (2 + i) = 15 + a by omega, Nat.pow_add]
    have hbound : 2 ^ 15 * 2 ^ a ≤ n + 5 := by
      rw [← hpow]; exact hlow
    have hbound' : 32768 * 2 ^ a ≤ n + 5 := hbound
    refine ⟨RootD (1 + a) (n + 15), .ReadyD (1 + a) (n + 15) (by omega) (by omega) (by omega) ?_, ?_⟩
    · rw [show 1 + a - 1 = a by omega]
      omega
    · refine Forward_steps hbegin ?_
      have htail := G_large_tail a n hbound hmod
      refine htail.congr ?_ rfl
      have hpow2 : 2 ^ (2 + i) = 2 ^ 14 * 2 ^ a := by
        rw [show 2 + i = 14 + a by omega, Nat.pow_add]
      rw [hpow2, show 15 + a = 1 + (2 + i) by omega, ← Nat.mul_assoc]

lemma D6_ready (n : ℕ) (hn : 64 ≤ n) (hmod : n % 8 = 2) :
    ∃ s, Ready s ∧ Forward (RootD 6 n) s := by
  by_cases he : n % 16 = 10
  · refine ⟨RootE (n + 8), .ReadyE (n + 8) (by omega) (by omega), ?_⟩
    refine Steps_forward ?_ (D6_even n hn he)
    unfold RootD RootE
    intro h; injection h with _ hls; injection hls with hh; omega
  · have hrem : n % 16 = 2 := by omega
    rcases factor2 ((n + 14) / 16) (by omega) with ⟨i, u, hu⟩
    have hval : n + 14 = (u * 2 + 1) * 16 * 2 ^ i := by
      have hdiv : n + 14 = ((u * 2 + 1) * 2 ^ i) * 16 := by omega
      rw [hdiv]; ring
    have hlow : 16 * 2 ^ i ≤ n + 14 := by
      have : n + 14 = 32 * (u * 2 ^ i) + 16 * 2 ^ i := by rw [hval]; ring
      omega
    refine ⟨RootD (1 + i) (n + 8), .ReadyD (1 + i) (n + 8) (by omega) (by omega) (by omega) ?_, ?_⟩
    · rw [show 1 + i - 1 = i by omega]; omega
    · rcases u with _ | u
      · rcases i with _ | _ | _ | i
        · dsimp at hval; omega
        · dsimp at hval; omega
        · dsimp at hval; omega
        · have hcase : n + 14 = 2 ^ (5 + (2 + i)) := by
            have hp1 : 2 ^ (5 + (2 + i)) = 2 ^ i * 128 := by
              rw [show 5 + (2 + i) = i + 7 by omega, Nat.pow_add]
            have hp2 : 2 ^ (i + 1 + 1 + 1) = 2 ^ i * 8 := by
              rw [show i + 1 + 1 + 1 = i + 3 by omega, Nat.pow_add]
            rw [hp2] at hval
            rw [hp1]
            omega
          have h_eq_d : 1 + (i + 1 + 1 + 1) = 2 + (2 + i) := by omega
          rw [h_eq_d]
          exact D6_partial (2 + i) n (by omega) hcase
      · rw [show (u + 1) * 2 + 1 = u * 2 + 3 by omega] at hval
        refine Steps_forward ?_ (D6_odd_ge3 i u n hn hval)
        unfold RootD
        intro h; injection h with _ _ hn_eq; omega

lemma D_ready (h n : ℕ) (hh : 1 ≤ h) (hn : 64 ≤ n) (hmod : n % 8 = 2)
    (hbound : 3 * 2 ^ (h - 1) ≤ n * 2) :
    ∃ s, Ready s ∧ Forward (RootD h n) s := by
  by_cases hlarge : 9 ≤ h
  · set j := h - 9
    have hj : h = 9 + j := by omega
    have hlow : 384 * 2 ^ j ≤ n := by
      have hb : 3 * 2 ^ (8 + j) ≤ n * 2 := by
        rwa [hj, show 9 + j - 1 = 8 + j by omega] at hbound
      rw [Nat.add_comm 8 j, Nat.pow_add] at hb
      change 3 * (2 ^ j * 256) ≤ n * 2 at hb
      omega
    refine ⟨RootD (1 + j) (n + 8), .ReadyD (1 + j) (n + 8) (by omega) (by omega) (by omega) ?_, ?_⟩
    · rw [show 1 + j - 1 = j by omega]; omega
    · rw [hj]
      refine Steps_forward ?_ (D_shrink j n hlow hmod)
      unfold RootD
      intro heq; injection heq with _ _ hn_eq; omega
  · by_cases hfive : h ≤ 5
    · refine ⟨RootG (n + 9), .ReadyG (n + 9) (by omega) (by omega), ?_⟩
      refine Steps_forward ?_ (D_small h n hh hfive hn hmod)
      unfold RootD RootG
      intro heq; injection heq with _ _ hn_eq; omega
    · rcases (by omega : h = 6 ∨ h = 7 ∨ h = 8) with rfl | rfl | rfl
      · exact D6_ready n hn hmod
      · refine ⟨RootF (n + 7), .ReadyF (n + 7) (by omega) (by omega), ?_⟩
        refine Steps_forward ?_ (D7 n ?_ hmod)
        · unfold RootD RootF; intro heq; injection heq with _ _ hn_eq; omega
        · change 3 * 64 ≤ n * 2 at hbound; omega
      · refine ⟨RootE (n + 8), .ReadyE (n + 8) (by omega) (by omega), ?_⟩
        refine Steps_forward ?_ (D8 n ?_ hmod)
        · unfold RootD RootE; intro heq; injection heq with _ _ hn_eq; omega
        · change 3 * 128 ≤ n * 2 at hbound; omega

lemma Ready_step {s : State} (hs : Ready s) :
    ∃ s', Ready s' ∧ Forward s s' := by
  cases hs with
  | ReadyG n hn hmod => exact G_ready n hn hmod
  | ReadyD h n hh hn hmod hbound => exact D_ready h n hh hn hmod hbound
  | ReadyE n hn hmod =>
    refine ⟨RootG (n + 9), .ReadyG (n + 9) (by omega) (by omega), ?_⟩
    refine Steps_forward ?_ (E_cycle n hn hmod)
    unfold RootE RootG; intro heq; injection heq with _ _ hn_eq; omega
  | ReadyF n hn hmod =>
    refine ⟨RootG (n + 10), .ReadyG (n + 10) (by omega) (by omega), ?_⟩
    refine Steps_forward ?_ (F_cycle n hn hmod)
    unfold RootF RootG; intro heq; injection heq with _ _ hn_eq; omega

def Inv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ s l r, Ready s ∧ Denote s l r ∧ c = (l {{E}}> r)

lemma Inv_step (c : Cfg (Fin 2) (Fin 6)) (hc : Inv c) :
    ∃ c', (c [tm]⊢⁺ c') ∧ Inv c' := by
  rcases hc with ⟨s, l, r, hs, hd, rfl⟩
  rcases Ready_step hs with ⟨s', hs', hstep⟩
  rcases hstep l r hd with ⟨l', r', hd', hrun⟩
  exact ⟨l' {{E}}> r', hrun, s', l', r', hs', hd', rfl⟩

lemma init_to_rootG :
    ∃ l r, Denote (RootG 11) l r ∧ (init []) [tm]⊢* (l {{E}}> r) := by
  refine ⟨decodeHalf 17891608, decodeHalf 202949321582694304249789, ⟨?_, ?_⟩, ?_⟩
  · have hL : LC 29 [0] (v +> (z1 +> (z0 +> (z1 +> (z1 +> (z1 +> default)))))) :=
      LC.LC_w 29 [] _
        (LC.LC_1 14 _
          (LC.LC_2 6 _
            (LC.LC_1 3 _
              (LC.LC_1 1 _
                (LC.LC_1 0 _ LC.LC_0)))))
    refine hL.congr rfl rfl ?_
    simp only [← decodeHalf_zero, decodeHalf_encodeList]
    rfl
  · have hR0 := RC.RC_0 .t2
    have hR1 := RC.RC_3 0 .t1 _ hR0
    have hR2 := RC.RC_3 1 .t0 _ hR1
    have hR3 := RC.RC_4 3 .t7 _ hR2
    have hR4 := RC.RC_4 6 .t6 _ hR3
    have hR5 := RC.RC_5 11 .t5 _ hR4
    refine hR5.congr rfl rfl ?_
    rw [show (11 + 1 + offset .t5) / 3 = 4 by rfl,
        show (6 + 1 + offset .t6) / 3 = 2 by rfl,
        show (3 + 1 + offset .t7) / 3 = 1 by rfl,
        show (1 + 1 + offset .t0) / 3 = 0 by rfl,
        show (0 + 1 + offset .t1) / 3 = 0 by rfl,
        rh]
    simp only [pow_succ_list, pow_zero_list, append_nil, ← decodeHalf_zero, decodeHalf_encodeList]
    rfl
  · have hsteps : multiStep tm (NatCfg.toCfg (K := 6) ⟨0, 0, 0, 0⟩) 11347 =
        some (NatCfg.toCfg (K := 6) ⟨2, 1, 17891608, 101474660791347152124894⟩) :=
      stepsNat_sound tm 11347 ⟨0, 0, 0, 0⟩ ⟨2, 1, 17891608, 101474660791347152124894⟩
        (by decide) (by decide)
    have hcfg : NatCfg.toCfg (K := 6) ⟨2, 1, 17891608, 101474660791347152124894⟩ =
        Cfg.headRight E (decodeHalf 17891608) (decodeHalf 202949321582694304249789) :=
      toCfg_headRight (K := 6) E 17891608 202949321582694304249789
    rw [toCfg_zero (K := 6), hcfg] at hsteps
    exact ⟨11347, hsteps⟩

lemma neverHaltsFrom_of_reachesStar {M : Machine (Fin 2) (Fin 6)} {c₁ c₀ : Cfg (Fin 2) (Fin 6)}
    (hinit : c₁ [M]⊢* c₀) (h_never : NeverHaltsFrom M c₀) : NeverHaltsFrom M c₁ := by
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M c₁ k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, BusyBeaver.multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never cfg ⟨k - k₀, hk⟩

lemma neverHaltsFrom_tm : NeverHaltsFrom tm (init []) := by
  rcases init_to_rootG with ⟨l, r, hd, hrun⟩
  refine neverHaltsFrom_of_reachesStar hrun ?_
  refine NeverHaltsFrom.of_reachesPlus_invariant Inv_step ?_
  exact ⟨RootG 11, l, r, .ReadyG 11 (by decide) (by decide), hd, rfl⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨k, hk⟩
  have hflip : multiStep tm (init []) k = some (flipCfg cfg) := by
    have h0 : flipCfg (init [] : Cfg (Fin 2) (Fin 6)) = init [] := rfl
    rw [← h0, multiStep_flipTM, hk]; rfl
  have hsome := neverHaltsFrom_tm (flipCfg cfg) ⟨k, hflip⟩
  rw [step_flipTM] at hsome
  cases hst : step target_tm cfg <;> simp_all

end BusyBeaver.M_1RBHHH_1LC1RE_1LD0LC_1LE1LC_1RF0RE_1RA0RB
