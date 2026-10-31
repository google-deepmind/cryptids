/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LE_1LC0RF_1LA0RD_1LC1RC_1LB0LB_---1RD` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LE_1LC0RF_1LA0RD_1LC1RC_1LB0LB_---1RD`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LE_1LC0RF_1LA0RD_1LC1RC_1LB0LB_HHH1RD

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LE_1LC0RF_1LA0RD_1LC1RC_1LB0LB_---1RD`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 3, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Longitudinal

local notation "Γ" => Fin 2
local notation "Λ" => Fin 6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

abbrev O : Fin 2 := 0
abbrev I : Fin 2 := 1

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

/-- `TM13.tm` in `SOBCv13.v` is the left-right mirror of `target_tm`. -/
abbrev tm : Machine (Fin 2) (Fin 6) := flipTM target_tm

-- ============================================================================
-- 1. Bounded Execution Helpers & Tape Words
-- ============================================================================

def runSteps (M : Machine (Fin 2) (Fin 6)) :
    ℕ → BoundedConfig.BCfg (Fin 2) (Fin 6) → Option (BoundedConfig.BCfg (Fin 2) (Fin 6))
  | 0, x => some x
  | n + 1, x => (BoundedConfig.step M x).bind (runSteps M n)

lemma runSteps_spec (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (x x' : BoundedConfig.BCfg (Fin 2) (Fin 6))
    (h : runSteps M n x = some x') (l₀ r₀ : ListBlank (Fin 2)) :
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
    (h : runSteps M (n + 1) x = some x') (l₀ r₀ : ListBlank (Fin 2)) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢⁺ (BoundedConfig.toCfg x' l₀ r₀) := by
  dsimp [runSteps] at h
  rcases hst : BoundedConfig.step M x with _ | y <;> rw [hst] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, BoundedConfig.step_spec M x hst l₀ r₀⟩
      (runSteps_spec M n y x' h l₀ r₀)

lemma SegRLs.congr
    {ls₁ ls₁' ls₂ ls₂' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w₁ w₁' w₂ w₂' : List (Fin 2)}
    (h : SegRLs tm ls₁ ls₂ w₁ w₂)
    (hls₁ : ls₁ = ls₁') (hls₂ : ls₂ = ls₂') (hw₁ : w₁ = w₁') (hw₂ : w₂ = w₂') :
    SegRLs tm ls₁' ls₂' w₁' w₂' := by
  subst hls₁ hls₂ hw₁ hw₂; exact h

lemma SegRLs.trans_eq
    {ls₁ ls₂ ls₃ ls₄ : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w₁ w₂ w₂' w₃ : List (Fin 2)}
    (h₁ : SegRLs tm ls₁ ls₂ w₁ w₂) (h₂ : SegRLs tm ls₃ ls₄ w₂' w₃)
    (hw : w₂ = w₂') :
    SegRLs tm (ls₁ ++ ls₃) (ls₂ ++ ls₄) w₁ w₃ := by
  subst hw; exact h₁.trans h₂

lemma SideRLs.congr
    {ls ls' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r₁ r₁' r₂ r₂' : ListBlank (Fin 2)}
    (h : SideRLs tm ls r₁ r₂) (hls : ls = ls') (hr₁ : r₁ = r₁') (hr₂ : r₂ = r₂') :
    SideRLs tm ls' r₁' r₂' := by
  subst hls hr₁ hr₂; exact h

lemma stepStar_congr {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [tm]⊢* c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') :
    c₁' [tm]⊢* c₂' := by
  subst hc₁ hc₂; exact h

lemma stepPlus_congr {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [tm]⊢⁺ c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') :
    c₁' [tm]⊢⁺ c₂' := by
  subst hc₁ hc₂; exact h

abbrev aw : List (Fin 2) := [I, O]
abbrev bw : List (Fin 2) := [O, I]
abbrev tw : List (Fin 2) := [O, I, O, I]
abbrev kw : List (Fin 2) := [I, O, I, O]
abbrev zw : List (Fin 2) := [O, I, I, O]
abbrev jw : List (Fin 2) := [O, I, O, O]
abbrev lw : List (Fin 2) := [I, O, O, I]
abbrev mw : List (Fin 2) := [O, O, O, I]
abbrev rw : List (Fin 2) := [O, O, I, O]
abbrev cw : List (Fin 2) := lw ++ rw
abbrev dw : List (Fin 2) := lw ++ mw ++ rw

def root (q : Fin 6) (n : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  default <{{q}} (zw ^ (1 + n) +> (tw +> r))

abbrev f_st : Fin 6 := C
abbrev h_st : Fin 6 := E
abbrev p_st : Fin 6 := D

abbrev fR : DH0 (Fin 2) (Fin 6) := (f_st, [I])
abbrev fL : DH0 (Fin 2) (Fin 6) := (f_st, [I])
abbrev hR : DH0 (Fin 2) (Fin 6) := (h_st, [I])
abbrev hL : DH0 (Fin 2) (Fin 6) := (f_st, [I])
abbrev hf : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [(fR, fL)]
abbrev hh : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [(hR, hL)]
abbrev hg : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := hf ++ hh

def P (n : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) := root p_st n r

-- ============================================================================
-- 2. Base Kernel Rules for TM13
-- ============================================================================

lemma F_A : SegRLs tm hf [] aw [O, O] :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma F_T : SegRLs tm hf [] tw zw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma F_11 : SegRLs tm hf [] [I, I] bw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma H_T : SegRLs tm hh [] tw lw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma H_Z : SegRLs tm hh [] zw kw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma H_R : SegRLs tm hh [] rw jw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma F_J : SegRLs tm hf hf jw tw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma H_M : SegRLs tm hh hh mw tw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma H_L : SegRLs tm hh hh lw zw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma H_K : SegRLs tm hh hf kw tw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma F_Z : SegRLs tm hf hg zw tw :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

abbrev uw : List Γ := [I, O, I, I]

private lemma shift_C_zw_step (l r : ListBlank Γ) :
    (l {{C}}> (zw +> r)) [tm]⊢* ((uw +> l) {{C}}> r) :=
  runSteps_spec tm 4 ⟨[], zw, C, .right⟩ ⟨uw, [], C, .right⟩ (by decide) l r

private lemma shift_C_zw (n : ℕ) (l r : ListBlank Γ) :
    (l {{C}}> (zw ^ n +> r)) [tm]⊢* ((uw ^ n +> l) {{C}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_zw_step l (zw ^ n +> r)) ?_
    refine stepStar_congr (ih (uw +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

private lemma shift_D_back_step (l r : ListBlank Γ) :
    ((uw +> l) <{{D}} (bw +> r)) [tm]⊢* (l <{{D}} (bw +> (zw +> r))) := by
  have h := runSteps_spec tm 10 ⟨bw, uw, D, .left⟩ ⟨bw ++ zw, [], D, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

private lemma shift_D_back (n : ℕ) (l r : ListBlank Γ) :
    ((uw ^ n +> l) <{{D}} (bw +> r)) [tm]⊢* (l <{{D}} (bw +> (zw ^ n +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_D_back_step (uw ^ n +> l) r) ?_
    refine stepStar_congr (ih (zw +> r)) rfl ?_
    rw [← append_assoc (zw ^ n) zw r, ← pow_succ_list']

private lemma bounce_D_left (r : ListBlank Γ) :
    (([I] +> default) <{{D}} (bw +> r)) [tm]⊢⁺ (default <{{D}} (zw +> r)) := by
  have h := runSteps1_spec tm 7 ⟨bw, [I, O], D, .left⟩ ⟨zw, [], D, .left⟩ (by decide) default r
  have hd : ([I, O] : List Γ) +> (default : ListBlank Γ) = [I] +> default := by
    rw [show ([I, O] : List Γ) = [I] ++ [O] from rfl, append_assoc,
      BoundedConfig.all0_spec (a := [O]) (by decide)]
  simpa only [BoundedConfig.toCfg, append_nil, hd] using h

private lemma P_enter (n : ℕ) (r : ListBlank Γ) :
    (root D n r) [tm]⊢⁺
      (toDHCfg (fR, .right) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))) r) := by
  have h1 : (root D n r) [tm]⊢⁺ (([I] +> default) {{C}}> (zw ^ (1 + n) +> (tw +> r))) := by
    have h := runSteps1_spec tm 0 ⟨[], [O], D, .left⟩ ⟨[I], [], C, .right⟩ (by decide)
      default (zw ^ (1 + n) +> (tw +> r))
    have hd : ([O] : List Γ) +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    simpa only [root, BoundedConfig.toCfg, append_nil, hd] using h
  have h2 := shift_C_zw (1 + n) ([I] +> default) (tw +> r)
  have h3 : ((uw ^ (1 + n) +> ([I] +> default)) {{C}}> (tw +> r)) [tm]⊢*
      ((uw ^ n +> ([I] +> default)) <{{D}} (bw +> (zw +> (aw +> r)))) := by
    have h' := runSteps_spec tm 17 ⟨uw, tw, C, .right⟩ ⟨bw ++ zw ++ aw, [], D, .left⟩ (by decide)
      (uw ^ n +> ([I] +> default)) r
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc,
      show (1 + n : ℕ) = n + 1 by omega, pow_succ_list] using h'
  have h4 := shift_D_back n ([I] +> default) (zw +> (aw +> r))
  have h5 := bounce_D_left (zw ^ n +> (zw +> (aw +> r)))
  have h5' : (default <{{D}} (zw +> (zw ^ n +> (zw +> (aw +> r))))) =
      (default <{{D}} (zw ^ (2 + n) +> (aw +> r))) := by
    congr 2
    rw [show (2 + n : ℕ) = (n + 1) + 1 by omega, pow_succ_list, pow_succ_list',
      append_assoc, append_assoc]
  have h6 : (default <{{D}} (zw ^ (2 + n) +> (aw +> r))) [tm]⊢*
      (([I] +> default) {{C}}> (zw ^ (2 + n) +> (aw +> r))) := by
    have h := runSteps_spec tm 1 ⟨[], [O], D, .left⟩ ⟨[I], [], C, .right⟩ (by decide)
      default (zw ^ (2 + n) +> (aw +> r))
    have hd : ([O] : List Γ) +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    simpa only [BoundedConfig.toCfg, append_nil, hd] using h
  have h7 := shift_C_zw (2 + n) ([I] +> default) (aw +> r)
  have h8 : ((uw ^ (2 + n) +> ([I] +> default)) {{C}}> (aw +> r)) [tm]⊢*
      (toDHCfg (fR, .right) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))) r) := by
    have h := runSteps_spec tm 6 ⟨uw, aw, C, .right⟩ ⟨[I] ++ [I, I, I, I, I], [], C, .right⟩ (by decide)
      (uw ^ (1 + n) +> ([I] +> default)) r
    have h2n : uw ^ (2 + n) = uw ++ uw ^ (1 + n) := by
      rw [show (2 + n : ℕ) = (1 + n) + 1 by omega, pow_succ_list]
    simpa only [BoundedConfig.toCfg, toDHCfg, append_nil, append_assoc, h2n] using h
  exact stepPlus_stepStar_trans h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4
      (stepStar_trans (stepPlus_to_stepStar (stepPlus_congr h5 rfl h5'))
        (stepStar_trans h6 (stepStar_trans h7 h8))))))

private lemma P_exit (n : ℕ) (s : ListBlank Γ) :
    (toDHCfg (fL, .left) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))) s) [tm]⊢⁺
      (root D (1 + n) s) := by
  have h1 : (toDHCfg (fL, .left) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))) s) [tm]⊢*
      ((uw ^ (1 + n) +> ([I] +> default)) <{{D}} (bw +> (tw +> s))) := by
    have h := runSteps_spec tm 5 ⟨[I], [I, I, I, I, I], C, .left⟩ ⟨bw ++ tw, [], D, .left⟩
      (by decide) (uw ^ (1 + n) +> ([I] +> default)) s
    simpa only [BoundedConfig.toCfg, toDHCfg, append_nil, append_assoc] using h
  have h2 := shift_D_back (1 + n) ([I] +> default) (tw +> s)
  have h3 := bounce_D_left (zw ^ (1 + n) +> (tw +> s))
  have h3' : (default <{{D}} (zw +> (zw ^ (1 + n) +> (tw +> s)))) = root D (1 + n) s := by
    unfold root
    rw [show (1 + (1 + n) : ℕ) = (1 + n) + 1 by omega, pow_succ_list, append_assoc]
  exact stepStar_stepPlus_trans h1 (stepStar_stepPlus_trans h2 (stepPlus_congr h3 rfl h3'))

lemma P_step (n : ℕ) (r s : ListBlank Γ) (H : SideRLs tm hf r s) :
    (P n r) [tm]⊢⁺ (P (1 + n) s) := by
  unfold P
  exact stepPlus_trans (P_enter n r)
    (stepPlus_trans (H.elim_single ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))))
      (P_exit n s))

private lemma shift_C_jw_step (l r : ListBlank Γ) :
    (l {{C}}> (jw +> r)) [tm]⊢* (([I, I, I, I] +> l) {{C}}> r) :=
  runSteps_spec tm 4 ⟨[], jw, C, .right⟩ ⟨[I, I, I, I], [], C, .right⟩ (by decide) l r

private lemma shift_C_jw (k : ℕ) (l r : ListBlank Γ) :
    (l {{C}}> (jw ^ k +> r)) [tm]⊢* (([I, I, I, I] ^ k +> l) {{C}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_jw_step l (jw ^ k +> r)) ?_
    refine stepStar_congr (ih ([I, I, I, I] +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

private lemma shift_C_IIII_step (l r : ListBlank Γ) :
    (([I, I, I, I] +> l) <{{C}} r) [tm]⊢* (l <{{C}} (kw +> r)) := by
  have h := runSteps_spec tm 4 ⟨[], [I, I, I, I], C, .left⟩ ⟨kw, [], C, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

private lemma shift_C_IIII (k : ℕ) (l r : ListBlank Γ) :
    (([I, I, I, I] ^ k +> l) <{{C}} r) [tm]⊢* (l <{{C}} (kw ^ k +> r)) := by
  induction k generalizing r with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_IIII_step ([I, I, I, I] ^ k +> l) r) ?_
    refine stepStar_congr (ih (kw +> r)) rfl ?_
    rw [← append_assoc (kw ^ k) kw r, ← pow_succ_list']

private lemma shift_C_lw_step (l r : ListBlank Γ) :
    ((uw +> l) <{{C}} ([I, O, I, O, I] +> r)) [tm]⊢*
      (l <{{C}} ([I, O, I, O, I] +> (lw +> r))) := by
  have h := runSteps_spec tm 12 ⟨[I, O, I, O, I], uw, C, .left⟩
    ⟨[I, O, I, O, I] ++ lw, [], C, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

private lemma shift_C_lw (n : ℕ) (l r : ListBlank Γ) :
    ((uw ^ n +> l) <{{C}} ([I, O, I, O, I] +> r)) [tm]⊢*
      (l <{{C}} ([I, O, I, O, I] +> (lw ^ n +> r))) := by
  induction n generalizing r with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_lw_step (uw ^ n +> l) r) ?_
    refine stepStar_congr (ih (lw +> r)) rfl ?_
    rw [← append_assoc (lw ^ n) lw r, ← pow_succ_list']

private lemma O_kw_pow (k : ℕ) (r : ListBlank Γ) :
    ([O] +> (kw ^ k +> r)) = (tw ^ k +> ([O] +> r)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, append_assoc, ← append_assoc [O] kw,
      show ([O] ++ kw : List Γ) = tw ++ [O] from rfl,
      append_assoc tw [O], ih, ← append_assoc tw (tw ^ k), ← pow_succ_list]

private lemma OI_lw_pow (n : ℕ) (r : ListBlank Γ) :
    (bw +> (lw ^ n +> r)) = (zw ^ n +> (bw +> r)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, append_assoc, ← append_assoc bw lw,
      show (bw ++ lw : List Γ) = zw ++ bw from rfl,
      append_assoc zw bw, ih, ← append_assoc zw (zw ^ n), ← pow_succ_list]

private lemma IO_zw_pow (n : ℕ) (r : ListBlank Γ) :
    (aw +> (zw ^ n +> r)) = (lw ^ n +> (aw +> r)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, append_assoc, ← append_assoc aw zw,
      show (aw ++ zw : List Γ) = lw ++ aw from rfl,
      append_assoc lw aw, ih, ← append_assoc lw (lw ^ n), ← pow_succ_list]

lemma bw_comm_T (n : ℕ) : bw ++ tw ^ n = tw ^ n ++ bw := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tw ++ (bw ++ tw ^ n) = tw ++ (tw ^ n ++ bw)
    rw [ih]

private lemma return_tail (n : ℕ) (r_tail : ListBlank Γ) :
    (([O, I, I] +> ([I, I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default)))) <{{D}}
      (tw +> r_tail)) [tm]⊢*
      (root D 0 (tw +> (lw ^ n +> (kw +> (tw +> (aw +> r_tail)))))) := by
  have h1 : (([O, I, I] +> ([I, I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default)))) <{{D}}
      (tw +> r_tail)) [tm]⊢*
      ((uw ^ (1 + n) +> ([I] +> default)) <{{C}}
        ([I, O, I, O, I] +> ([O, I, O, I, O, I, I, O] +> r_tail))) := by
    have h := runSteps_spec tm 17 ⟨tw, [O, I, I] ++ [I, I, I, I, I, I], D, .left⟩
      ⟨[I, O, I, O, I] ++ [O, I, O, I, O, I, I, O], [], C, .left⟩ (by decide)
      (uw ^ (1 + n) +> ([I] +> default)) r_tail
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  have h2 := shift_C_lw (1 + n) ([I] +> default) ([O, I, O, I, O, I, I, O] +> r_tail)
  have h2_eq : (([I] +> default) <{{C}}
      ([I, O, I, O, I] +> (lw ^ (1 + n) +> ([O, I, O, I, O, I, I, O] +> r_tail)))) =
      (([I] +> default) <{{C}}
        ([I, O, I, O, I, I, O] +> (zw ^ n +> ([O, I, O, I, O, I, O, I, I, O] +> r_tail)))) := by
    congr 1
    have h_lw : lw ^ (1 + n) +> ([O, I, O, I, O, I, I, O] +> r_tail) =
        aw +> (zw ^ n +> ([O, I, O, I, O, I, O, I, I, O] +> r_tail)) := by
      rw [show (1 + n : ℕ) = n + 1 by omega, pow_succ_list, append_assoc,
        show (lw +> (lw ^ n +> ([O, I, O, I, O, I, I, O] +> r_tail))) =
          aw +> (bw +> (lw ^ n +> ([O, I, O, I, O, I, I, O] +> r_tail))) from rfl,
        OI_lw_pow]
      rfl
    rw [h_lw]
    rfl
  have h3 : (([I] +> default) <{{C}}
        ([I, O, I, O, I, I, O] +> (zw ^ n +> ([O, I, O, I, O, I, O, I, I, O] +> r_tail)))) [tm]⊢*
      (([I, O, I, I, I, I, I, I, I, I, I] +> default) {{C}}>
        (zw ^ n +> ([O, I, O, I, O, I, O, I, I, O] +> r_tail))) := by
    have h := runSteps_spec tm 32 ⟨[I, O, I, O, I, I, O], [I, O, O, O], C, .left⟩
      ⟨[I, O, I, I, I, I, I, I, I, I, I], [], C, .right⟩ (by decide)
      default (zw ^ n +> ([O, I, O, I, O, I, O, I, I, O] +> r_tail))
    have hd : ([I, O, O, O] : List Γ) +> (default : ListBlank Γ) = [I] +> default := by
      rw [show ([I, O, O, O] : List Γ) = [I] ++ [O, O, O] from rfl, append_assoc,
        BoundedConfig.all0_spec (a := [O, O, O]) (by decide)]
    simpa only [BoundedConfig.toCfg, append_nil, hd] using h
  have h4 := shift_C_zw n ([I, O, I, I, I, I, I, I, I, I, I] +> default)
    ([O, I, O, I, O, I, O, I, I, O] +> r_tail)
  have h5 : ((uw ^ n +> ([I, O, I, I, I, I, I, I, I, I, I] +> default)) {{C}}>
        ([O, I, O, I, O, I, O, I, I, O] +> r_tail)) [tm]⊢*
      ((uw ^ n +> ([I, O, I, I, I, I, I, I, I, I, I] +> default)) <{{D}}
        (bw +> ([I, O, O, I, O, I, I, O] +> r_tail))) := by
    have h := runSteps_spec tm 7 ⟨[], [O, I, O, I, O, I], C, .right⟩
      ⟨bw ++ [I, O, O, I], [], D, .left⟩ (by decide)
      (uw ^ n +> ([I, O, I, I, I, I, I, I, I, I, I] +> default))
      ([O, I, I, O] +> r_tail)
    have hr1 : ([O, I, O, I, O, I] : List Γ) +> ([O, I, I, O] +> r_tail) =
        [O, I, O, I, O, I, O, I, I, O] +> r_tail := by
      rw [← append_assoc]; rfl
    have hr2 : ([I, O, O, I] : List Γ) +> ([O, I, I, O] +> r_tail) =
        [I, O, O, I, O, I, I, O] +> r_tail := by
      rw [← append_assoc]; rfl
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc, hr1, hr2] using h
  have h6 := shift_D_back n ([I, O, I, I, I, I, I, I, I, I, I] +> default)
    ([I, O, O, I, O, I, I, O] +> r_tail)
  have h7 : (([I, O, I, I, I, I, I, I, I, I, I] +> default) <{{D}}
        (bw +> (zw ^ n +> ([I, O, O, I, O, I, I, O] +> r_tail)))) [tm]⊢*
      (root D 0 (tw +> (lw ^ n +> (kw +> (tw +> (aw +> r_tail)))))) := by
    have h := runSteps_spec tm 24 ⟨bw, [I, O, I, I, I, I, I, I, I, I, I, O], D, .left⟩
      ⟨zw ++ tw ++ tw ++ aw, [], D, .left⟩ (by decide)
      default (zw ^ n +> ([I, O, O, I, O, I, I, O] +> r_tail))
    have hd : ([I, O, I, I, I, I, I, I, I, I, I, O] : List Γ) +> (default : ListBlank Γ) =
        [I, O, I, I, I, I, I, I, I, I, I] +> default := by
      rw [show ([I, O, I, I, I, I, I, I, I, I, I, O] : List Γ) =
          [I, O, I, I, I, I, I, I, I, I, I] ++ [O] from rfl,
        append_assoc, BoundedConfig.all0_spec (a := [O]) (by decide)]
    have hr : ((zw ++ tw ++ tw ++ aw) +>
        (zw ^ n +> ([I, O, O, I, O, I, I, O] +> r_tail))) =
        (zw ^ (1 + 0) +> (tw +> (tw +> (lw ^ n +> (kw +> (tw +> (aw +> r_tail))))))) := by
      rw [Nat.add_zero, pow_one_list, append_assoc, append_assoc, append_assoc, IO_zw_pow,
        ← append_assoc aw [I, O, O, I, O, I, I, O],
        show (aw ++ [I, O, O, I, O, I, I, O] : List Γ) = kw ++ tw ++ aw from rfl,
        append_assoc, append_assoc]
    simpa only [BoundedConfig.toCfg, root, append_nil, hd, hr] using h
  exact stepStar_trans h1 (stepStar_trans (stepStar_congr h2 rfl h2_eq)
    (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))

lemma zero_return (n k : ℕ) (r : ListBlank Γ) :
    (P n (zw +> (jw ^ (1 + k) +> ([O, O] +> r)))) [tm]⊢⁺
      (P 0 (tw +> (lw ^ n +> (kw +> (tw +> (aw +> (tw ^ k +> ([I, O, I] +> r)))))))) := by
  unfold P
  let l_base : ListBlank Γ := [I, I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))
  have h1 := P_enter n (zw +> (jw ^ (1 + k) +> ([O, O] +> r)))
  have h2 : (toDHCfg (fR, .right) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default)))
      (zw +> (jw ^ (1 + k) +> ([O, O] +> r)))) [tm]⊢*
      ((uw +> l_base) {{C}}> (jw ^ (1 + k) +> ([O, O] +> r))) :=
    shift_C_zw_step l_base (jw ^ (1 + k) +> ([O, O] +> r))
  have h3 := shift_C_jw (1 + k) (uw +> l_base) ([O, O] +> r)
  have h4 : (([I, I, I, I] ^ (1 + k) +> (uw +> l_base)) {{C}}> ([O, O] +> r)) [tm]⊢*
      (([I, I, I, I] ^ k +> (uw +> l_base)) <{{C}} ([I, O, I, I, O, I] +> r)) := by
    have h := runSteps_spec tm 7 ⟨[I, I, I, I], [O, O], C, .right⟩
      ⟨[I, O, I, I, O, I], [], C, .left⟩ (by decide)
      ([I, I, I, I] ^ k +> (uw +> l_base)) r
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc,
      show (1 + k : ℕ) = k + 1 by omega, pow_succ_list] using h
  have h5 := shift_C_IIII k (uw +> l_base) ([I, O, I, I, O, I] +> r)
  have h6 : ((uw +> l_base) <{{C}} (kw ^ k +> ([I, O, I, I, O, I] +> r))) [tm]⊢*
      (([O, I, I] +> l_base) <{{D}} (tw +> (tw ^ k +> ([I, O, I] +> r)))) := by
    have h := runSteps_spec tm 1 ⟨[], [I], C, .left⟩ ⟨[O], [], D, .left⟩ (by decide)
      ([O, I, I] +> l_base) (kw ^ k +> ([I, O, I, I, O, I] +> r))
    have hl : ([I] : List Γ) +> ([O, I, I] +> l_base) = uw +> l_base := by
      rw [← append_assoc]; rfl
    have hr : ([O] +> (kw ^ k +> ([I, O, I, I, O, I] +> r))) =
        (tw +> (tw ^ k +> ([I, O, I] +> r))) := by
      rw [O_kw_pow, show ([O] +> ([I, O, I, I, O, I] +> r)) = tw +> ([I, O, I] +> r) from rfl,
        ← append_assoc, ← pow_succ_list', pow_succ_list, append_assoc]
    simpa only [BoundedConfig.toCfg, append_nil, hl, hr] using h
  have h7 := return_tail n (tw ^ k +> ([I, O, I] +> r))
  exact stepPlus_stepStar_trans h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4
      (stepStar_trans h5 (stepStar_trans h6 h7)))))

lemma anchor_return (n k : ℕ) :
    (P n (zw +> (jw ^ k +> (zw +> ([I] +> default))))) [tm]⊢⁺
      (P 0 (tw +> (lw ^ n +> (kw +> (tw +> (aw +> (bw +> (tw ^ k +> ([I, O, I] +> default))))))))) := by
  unfold P
  let l_base : ListBlank Γ := [I, I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default))
  have h1 := P_enter n (zw +> (jw ^ k +> (zw +> ([I] +> default))))
  have h2 : (toDHCfg (fR, .right) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default)))
      (zw +> (jw ^ k +> (zw +> ([I] +> default))))) [tm]⊢*
      ((uw +> l_base) {{C}}> (jw ^ k +> (zw +> ([I] +> default)))) :=
    shift_C_zw_step l_base (jw ^ k +> (zw +> ([I] +> default)))
  have h3 := shift_C_jw k (uw +> l_base) (zw +> ([I] +> default))
  have h4 := shift_C_zw_step ([I, I, I, I] ^ k +> (uw +> l_base)) ([I] +> default)
  have h5 : ((uw +> ([I, I, I, I] ^ k +> (uw +> l_base))) {{C}}> ([I] +> default)) [tm]⊢*
      (([I, I, I, I] ^ k +> (uw +> l_base)) <{{C}} ([I, O, I, O, I, I, O, I] +> default)) := by
    have h := runSteps_spec tm 15 ⟨uw, [I, O, O, O], C, .right⟩
      ⟨[I, O, I, O, I, I, O, I], [], C, .left⟩ (by decide)
      ([I, I, I, I] ^ k +> (uw +> l_base)) default
    have hd1 : ([I, O, O, O] : List Γ) +> (default : ListBlank Γ) = [I] +> default := by
      rw [show ([I, O, O, O] : List Γ) = [I] ++ [O, O, O] from rfl, append_assoc,
        BoundedConfig.all0_spec (a := [O, O, O]) (by decide)]
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc, hd1] using h
  have h6 := shift_C_IIII k (uw +> l_base) ([I, O, I, O, I, I, O, I] +> default)
  have h7 : ((uw +> l_base) <{{C}} (kw ^ k +> ([I, O, I, O, I, I, O, I] +> default))) [tm]⊢*
      (([O, I, I] +> l_base) <{{D}} (tw +> (bw +> (tw ^ k +> ([I, O, I] +> default))))) := by
    have h := runSteps_spec tm 1 ⟨[], [I], C, .left⟩ ⟨[O], [], D, .left⟩ (by decide)
      ([O, I, I] +> l_base) (kw ^ k +> ([I, O, I, O, I, I, O, I] +> default))
    have hl : ([I] : List Γ) +> ([O, I, I] +> l_base) = uw +> l_base := by
      rw [← append_assoc]; rfl
    have hr : ([O] +> (kw ^ k +> ([I, O, I, O, I, I, O, I] +> default))) =
        (tw +> (bw +> (tw ^ k +> ([I, O, I] +> default)))) := by
      rw [O_kw_pow,
        show ([O] +> ([I, O, I, O, I, I, O, I] +> (default : ListBlank Γ))) =
          tw +> (bw +> ([I, O, I] +> default)) from rfl,
        ← append_assoc (tw ^ k) tw _, ← pow_succ_list', pow_succ_list,
        append_assoc tw (tw ^ k), ← append_assoc (tw ^ k) bw, ← bw_comm_T, append_assoc]
    simpa only [BoundedConfig.toCfg, append_nil, hl, hr] using h
  have h8 := return_tail n (bw +> (tw ^ k +> ([I, O, I] +> default)))
  exact stepPlus_stepStar_trans h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4
      (stepStar_trans h5 (stepStar_trans h6 (stepStar_trans h7 h8))))))

lemma init_raw :
    (init []) [tm]⊢* (P 0 (tw +> (lw ^ 6 +> (kw +> (tw ^ 3 +> (zw +> ([I] +> default))))))) := by
  have h := runSteps_spec tm 1581 ⟨List.replicate 46 O, List.replicate 11 O, A, .right⟩
    ⟨zw ++ tw ++ tw ++ lw ^ 6 ++ kw ++ tw ^ 3 ++ zw ++ [I], [], D, .left⟩
    (by decide) default default
  have hl : List.replicate 46 O +> (default : ListBlank Γ) = default :=
    BoundedConfig.all0_spec (by decide)
  have hr : List.replicate 11 O +> (default : ListBlank Γ) = default :=
    BoundedConfig.all0_spec (by decide)
  refine stepStar_congr h ?_ ?_
  · simp only [BoundedConfig.toCfg, hl, hr]; rfl
  · simp only [BoundedConfig.toCfg, P, root, Nat.add_zero, pow_one_list, append_nil, append_assoc]

-- ============================================================================
-- 3. Common Service Algebra & Closed Reset Family (`SOBCv13.v:79-1183`)
-- ============================================================================

lemma F_K : SegRLs tm hf [] kw rw :=
  F_A.concat (.nil aw)

lemma F_L : SegRLs tm hf [] lw mw :=
  F_A.concat (.nil bw)

lemma G_T : SegRLs tm hg [] tw kw :=
  F_T.trans H_Z

lemma G_K : SegRLs tm hg [] kw jw :=
  F_K.trans H_R

lemma G_J : SegRLs tm hg hf jw lw :=
  SegRLs.congr (F_J.trans H_T) rfl rfl rfl rfl

lemma G_L : SegRLs tm hg hh lw tw :=
  F_L.trans H_M

lemma G_Z : SegRLs tm hg hg zw lw :=
  SegRLs.congr (F_Z.trans H_T) rfl rfl rfl rfl

lemma G2_J : SegRLs tm (hg ^ 2) hg jw tw :=
  SegRLs.congr (G_J.trans G_L) (by rfl) rfl rfl rfl

lemma G4_T : SegRLs tm (hg ^ 4) hg tw tw :=
  SegRLs.congr (G_T.trans (G_K.trans G2_J)) (by rfl) rfl rfl rfl

lemma G4_J : SegRLs tm (hg ^ 4) hg jw jw :=
  SegRLs.congr (G2_J.trans (G_T.trans G_K)) (by rfl) rfl rfl rfl

lemma F_Js (n : ℕ) : SegRLs tm hf hf (jw ^ n) (tw ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm hf
  | succ n ih => exact F_J.concat ih

lemma H_Ms (n : ℕ) : SegRLs tm hh hh (mw ^ n) (tw ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm hh
  | succ n ih => exact H_M.concat ih

lemma H_Ls (n : ℕ) : SegRLs tm hh hh (lw ^ n) (zw ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm hh
  | succ n ih => exact H_L.concat ih

def q4 : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + 4 * q4 k

lemma q4_pow (n : ℕ) : 1 + 3 * q4 n = 4 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [q4]
    rw [Nat.pow_succ]
    omega

lemma q4_add (n m : ℕ) : q4 (n + m) = q4 n + 4 ^ n * q4 m := by
  induction n with
  | zero =>
    rw [Nat.zero_add, Nat.pow_zero, Nat.one_mul]
    dsimp [q4]
    omega
  | succ n ih =>
    rw [Nat.succ_add, q4, q4, ih, Nat.pow_succ]
    ring

lemma service_repeat {hs ks : List (DH0 Γ Λ × DH0 Γ Λ)} {w : List Γ} (n : ℕ)
    (H : SegRLs tm hs ks w w) : SegRLs tm (hs ^ n) (ks ^ n) w w := by
  induction n with
  | zero => exact .nil w
  | succ n ih => exact H.trans ih

lemma F2_T : SegRLs tm (hf ^ 2) hg tw tw :=
  SegRLs.congr (F_T.trans F_Z) (by rfl) rfl rfl rfl

lemma G_recycle {w : List Γ} (n : ℕ) (H : SegRLs tm (hg ^ 4) hg w w) :
    SegRLs tm (hg ^ (n * 4)) (hg ^ n) w w := by
  rw [Nat.mul_comm, pow_mul_list]
  exact service_repeat n H

lemma G_lift {w : List Γ} (a n : ℕ) (H : SegRLs tm (hg ^ 4) hg w w) :
    SegRLs tm (hg ^ (n * 4 ^ a)) (hg ^ n) (w ^ a) (w ^ a) := by
  induction a generalizing n with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    exact SegRLs.empty tm (hg ^ n)
  | succ a ih =>
    rw [pow_succ_list,
      show n * 4 ^ (a + 1) = (n * 4 ^ a) * 4 by rw [Nat.pow_succ]; ring]
    exact (G_recycle (n * 4 ^ a) H).concat (ih n)

lemma G_Ts (a n : ℕ) : SegRLs tm (hg ^ (n * 4 ^ a)) (hg ^ n) (tw ^ a) (tw ^ a) :=
  G_lift a n G4_T

lemma G_Js (a n : ℕ) : SegRLs tm (hg ^ (n * 4 ^ a)) (hg ^ n) (jw ^ a) (jw ^ a) :=
  G_lift a n G4_J

lemma F_T_calls (a n : ℕ) :
    SegRLs tm (hf ^ (2 * n * 4 ^ a)) (hg ^ n) (tw ^ (1 + a)) (tw ^ (1 + a)) := by
  have h1 : SegRLs tm (hf ^ (2 * (n * 4 ^ a))) (hg ^ (n * 4 ^ a)) tw tw := by
    rw [pow_mul_list]
    exact service_repeat (n * 4 ^ a) F2_T
  refine SegRLs.congr (h1.concat (G_Ts a n)) ?_ rfl ?_ ?_
  · rw [show 2 * (n * 4 ^ a) = 2 * n * 4 ^ a by ring]
  · rw [Nat.add_comm 1 a, pow_succ_list]
  · rw [Nat.add_comm 1 a, pow_succ_list]

lemma G2_T : SegRLs tm (hg ^ 2) [] tw jw :=
  SegRLs.congr (G_T.trans G_K) (by rfl) rfl rfl rfl

lemma G_normalize (n : ℕ) : SegRLs tm (hg ^ (2 * q4 n)) [] (tw ^ n) (jw ^ n) := by
  induction n with
  | zero => exact .nil []
  | succ n ih =>
    have h1 := G2_T.concat (.nil (tw ^ n))
    have h2 := (G_recycle (2 * q4 n) G4_J).concat ih
    refine SegRLs.congr (h1.trans h2) ?_ rfl rfl rfl
    rw [← pow_add_list, show 2 + 2 * q4 n * 4 = 2 * q4 (n + 1) by dsimp [q4]; omega]

lemma F_normalize (n : ℕ) :
    SegRLs tm (hf ^ (q4 (1 + n))) [] (tw ^ (1 + n)) (zw ++ jw ^ n) := by
  have h1 := (F_T_calls 0 (2 * q4 n)).concat (G_normalize n)
  have h2 := F_T.concat (.nil (jw ^ n))
  refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by rfl)) ?_ rfl ?_ rfl
  · rw [← pow_succ_list']
    congr 1
    rw [Nat.add_comm 1 n]
    dsimp [q4]
    omega
  · rw [Nat.add_comm 1 n, pow_succ_list]
    rfl

lemma F_outer (n : ℕ) :
    SegRLs tm hf hh (zw ++ lw ++ mw ^ n) (tw ^ (2 + n)) := by
  have h := F_Z.concat (G_L.concat (H_Ms n))
  refine SegRLs.congr h rfl rfl (by simp only [List.append_assoc]) ?_
  rw [show (2 + n : ℕ) = (n + 1) + 1 by omega, pow_succ_list, pow_succ_list]

lemma F_postJ (n : ℕ) :
    SegRLs tm hf hf (zw ++ jw ^ (1 + n)) (tw ++ lw ++ tw ^ n) := by
  have h := F_Z.concat (G_J.concat (F_Js n))
  refine SegRLs.congr h rfl rfl ?_ (by simp only [List.append_assoc])
  rw [Nat.add_comm 1 n, pow_succ_list]

lemma BIN_borrow (n : ℕ) :
    SegRLs tm (hf ^ (8 + 16 * q4 n)) []
      (zw ++ lw ++ mw ^ n ++ tw) (zw ++ lw ++ tw ^ n ++ mw) := by
  have h1 := (F_outer n).concat H_T
  have h2 := (F_normalize (1 + n)).concat (.nil lw)
  have h3 := (F_postJ n).concat F_L
  have h4 := F_T.concat (.nil (lw ++ tw ^ n ++ mw))
  have h12 := SegRLs.trans_eq h1 h2 (by rw [show 2 + n = 1 + (1 + n) by omega])
  have h34 := SegRLs.trans_eq h3 h4 (by simp only [List.append_assoc])
  have hall := SegRLs.trans_eq h12 h34 (by simp only [List.append_assoc])
  refine SegRLs.congr hall ?_ rfl (by simp only [List.append_assoc])
    (by simp only [List.append_assoc])
  rw [← List.append_assoc, ← pow_succ_list, ← pow_succ_list', ← pow_succ_list']
  congr 1
  rw [show 1 + (1 + n) = (n + 1) + 1 by omega]
  dsimp [q4]
  omega

lemma BIN (n : ℕ) :
    SegRLs tm (hf ^ (8 * q4 n)) [] (zw ++ lw ++ tw ^ n) (zw ++ lw ++ mw ^ n) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    have h1 : SegRLs tm (hf ^ (8 * q4 n)) []
        (zw ++ lw ++ tw ^ n ++ tw) (zw ++ lw ++ mw ^ n ++ tw) :=
      ih.concat (.nil tw)
    have h2 := BIN_borrow n
    have h3 : SegRLs tm (hf ^ (8 * q4 n)) []
        (zw ++ lw ++ tw ^ n ++ mw) (zw ++ lw ++ mw ^ n ++ mw) :=
      ih.concat (.nil mw)
    refine SegRLs.congr ((h1.trans h2).trans h3) ?_ rfl ?_ ?_
    · rw [← pow_add_list, ← pow_add_list]
      congr 1
      dsimp [q4]
      omega
    · rw [pow_succ_list', List.append_assoc]
    · rw [pow_succ_list', List.append_assoc]

lemma G_Zs (n : ℕ) : SegRLs tm hg hg (zw ^ n) (lw ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm hg
  | succ n ih => exact G_Z.concat ih

lemma G_Ls (n : ℕ) : SegRLs tm hg hh (lw ^ (1 + n)) (tw ++ zw ^ n) := by
  rw [Nat.add_comm 1 n, pow_succ_list]
  exact G_L.concat (H_Ls n)

lemma G_ZT (n : ℕ) :
    SegRLs tm (hg ^ 2) hf (zw ^ (1 + n) ++ tw) (tw ++ zw ^ n ++ tw) := by
  have h1 := (G_Zs (1 + n)).concat G_T
  have h2 := (G_Ls n).concat H_K
  exact SegRLs.congr (h1.trans h2) (by rfl) rfl rfl (by simp only [List.append_assoc])

lemma G_reduce_Z (n : ℕ) :
    SegRLs tm (hg ^ (2 * q4 n)) (hf ^ n) (zw ^ n ++ tw) (tw ^ (1 + n)) := by
  induction n with
  | zero => exact .nil tw
  | succ n ih =>
    have h1 := G_ZT (n := n)
    have h2 := (G_recycle (2 * q4 n) G4_T).concat ih
    refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc]))
      ?_ ?_ (by rw [Nat.add_comm 1 n]) ?_
    · rw [← pow_add_list, show 2 + 2 * q4 n * 4 = 2 * q4 (n + 1) by dsimp [q4]; omega]
    · rw [← pow_succ_list]
    · rw [show 1 + (n + 1) = (1 + n) + 1 by omega, pow_succ_list]

lemma G_column_start (n : ℕ) (w : List Γ) :
    SegRLs tm hg [] (lw ^ (1 + n) ++ kw ++ tw ++ w) (tw ++ zw ^ n ++ tw ++ zw ++ w) := by
  have h := (G_Ls n).concat (H_K.concat (F_T.concat (.nil w)))
  exact SegRLs.congr h rfl rfl (by simp only [List.append_assoc]) (by simp only [List.append_assoc])

lemma COLUMN (n : ℕ) (w e : List Γ) (hs : List (DH0 Γ Λ × DH0 Γ Λ))
    (H : SegRLs tm (hf ^ n) hs (zw ++ w) e) :
    SegRLs tm (hf ^ (2 + 16 * q4 n)) hs
      (tw ++ lw ^ (1 + n) ++ kw ++ tw ++ w) (tw ^ (n + 3) ++ e) := by
  have h_inner1 := G_column_start n w
  have h_inner2 := (G_recycle (2 * q4 n) G4_T).concat ((G_reduce_Z n).concat H)
  have h_inner : SegRLs tm (hg ^ (1 + 8 * q4 n)) hs
      (lw ^ (1 + n) ++ kw ++ tw ++ w) (tw ++ tw ^ (1 + n) ++ e) := by
    refine SegRLs.congr (SegRLs.trans_eq h_inner1 h_inner2 (by simp only [List.append_assoc]))
      ?_ (List.nil_append hs) rfl (by simp only [List.append_assoc])
    rw [← pow_succ_list]
    congr 1
    omega
  have h_outer := (F_T_calls 0 (1 + 8 * q4 n)).concat h_inner
  refine SegRLs.congr h_outer ?_ (List.nil_append hs)
    (by simp only [pow_zero_list, pow_succ_list, List.append_nil, List.append_assoc]) ?_
  · congr 1
    rw [Nat.pow_zero]
    omega
  · rw [show (1 + 0 : ℕ) = 1 from rfl, pow_one_list,
      show n + 3 = 1 + (1 + (1 + n)) by omega,
      Nat.add_comm 1 (1 + (1 + n)), pow_succ_list,
      Nat.add_comm 1 (1 + n), pow_succ_list]
    simp only [List.append_assoc]

lemma G3_T : SegRLs tm (hg ^ 3) hf tw lw :=
  SegRLs.congr (G2_T.trans G_J) (by rfl) rfl rfl rfl

lemma G_almost (n : ℕ) :
    SegRLs tm (hg ^ (3 + 12 * q4 n)) hf (tw ^ (1 + n)) (lw ++ mw ^ n) := by
  induction n with
  | zero => exact G3_T
  | succ n ih =>
    have h1 := (G_recycle (3 + 12 * q4 n) G4_T).concat ih
    have h2 := G3_T.concat (F_L.concat (.nil (mw ^ n)))
    refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc]))
      ?_ rfl ?_ ?_
    · rw [← pow_add_list]
      congr 1
      dsimp [q4]
      omega
    · rw [show 1 + (n + 1) = (1 + n) + 1 by omega, pow_succ_list]
    · rw [pow_succ_list]

lemma G_two_before (n : ℕ) :
    SegRLs tm (hg ^ (14 + 48 * q4 n)) hf (tw ^ (2 + n)) (jw ++ lw ++ mw ^ n) := by
  have h1 := (G_recycle (3 + 12 * q4 n) G4_T).concat (G_almost n)
  have h2 := G2_T.concat (.nil (lw ++ mw ^ n))
  refine SegRLs.congr (h1.trans h2) ?_ rfl ?_ (by simp only [List.append_assoc])
  · rw [← pow_add_list]
    congr 1
    omega
  · rw [show 2 + n = (1 + n) + 1 by omega, pow_succ_list]

lemma NEAR_WRAP (n j : ℕ) :
    SegRLs tm (hf ^ (29 + 96 * q4 n + 2 * j * 4 ^ (2 + n))) (hg ^ j ++ hf)
      (tw ^ (3 + n)) (zw ++ jw ++ lw ++ mw ^ n) := by
  have h1 := F_T_calls (2 + n) j
  have h2 := SegRLs.trans_eq ((F_T_calls 0 (14 + 48 * q4 n)).concat (G_two_before n))
    (F_T.concat (.nil (jw ++ lw ++ mw ^ n))) (by rfl)
  refine SegRLs.congr (SegRLs.trans_eq h1 h2 ?_) ?_ (by simp only [List.append_nil])
    (by rw [show 3 + n = 1 + (2 + n) by omega]) (by simp only [List.append_assoc])
  · rw [show (1 + 0 : ℕ) = 1 from rfl, pow_one_list,
      show 1 + (2 + n) = (2 + n) + 1 by omega, pow_succ_list]
  · rw [← pow_succ_list', ← pow_add_list]
    congr 1
    rw [Nat.pow_zero]
    omega

lemma G_append (n k : ℕ) (u v w : List Γ)
    (H : SegRLs tm (hg ^ n) [] u v)
    (H' : SegRLs tm (hg ^ k) [] (tw ++ v) w) :
    SegRLs tm (hg ^ (4 * n + k)) [] (tw ++ u) w := by
  have h1 := (G_recycle n G4_T).concat H
  refine SegRLs.congr (h1.trans H') ?_ rfl rfl rfl
  rw [← pow_add_list, Nat.mul_comm n 4]

lemma G7 : SegRLs tm (hg ^ 7) [] (tw ^ 2) cw :=
  G_append 1 3 tw kw cw G_T (G3_T.concat F_K)

lemma G125 : SegRLs tm (hg ^ 125) [] (tw ^ 4) (kw ++ dw) := by
  have H31 : SegRLs tm (hg ^ 31) [] (tw ^ 3) dw :=
    G_append 7 3 (tw ^ 2) cw dw G7
      (SegRLs.congr (G3_T.concat (F_L.concat (.nil rw))) rfl rfl rfl rfl)
  exact G_append 31 1 (tw ^ 3) dw (kw ++ dw) H31 (G_T.concat (.nil dw))

lemma G_prefix7 : SegRLs tm (hg ^ 8061) [] (tw ^ 7) (kw ++ dw ^ 2) := by
  have H5 : SegRLs tm (hg ^ 503) [] (tw ^ 5) (cw ++ dw) :=
    G_append 125 3 (tw ^ 4) (kw ++ dw) (cw ++ dw) G125
      (SegRLs.congr (G3_T.concat (F_K.concat (.nil dw))) rfl rfl rfl rfl)
  have H6 : SegRLs tm (hg ^ 2015) [] (tw ^ 6) (dw ++ dw) :=
    G_append 503 3 (tw ^ 5) (cw ++ dw) (dw ++ dw) H5
      (SegRLs.congr (G3_T.concat (F_L.concat (.nil (rw ++ dw)))) rfl rfl rfl rfl)
  exact G_append 2015 1 (tw ^ 6) (dw ++ dw) (kw ++ dw ^ 2) H6
    (SegRLs.congr (G_T.concat (.nil (dw ++ dw))) rfl rfl rfl rfl)

lemma G_pair13 : SegRLs tm (hg ^ 13) [] (tw ^ 2 ++ kw) (kw ++ cw) :=
  SegRLs.congr (G_append 3 1 (tw ++ kw) cw (kw ++ cw) (G3_T.concat F_K) (G_T.concat (.nil cw)))
    rfl rfl rfl rfl

lemma G_last61 : SegRLs tm (hg ^ 61) [] (tw ^ 3 ++ kw) (kw ++ dw) := by
  have H15 : SegRLs tm (hg ^ 15) [] (tw ^ 2 ++ kw) dw :=
    SegRLs.congr (G_append 3 3 (tw ++ kw) cw dw (G3_T.concat F_K)
      (SegRLs.congr (G3_T.concat (F_L.concat (.nil rw))) rfl rfl rfl rfl))
      rfl rfl rfl rfl
  exact SegRLs.congr (G_append 15 1 (tw ^ 2 ++ kw) dw (kw ++ dw) H15 (G_T.concat (.nil dw)))
    rfl rfl rfl rfl

def supply_d : ℕ → ℕ
  | 0 => 8061
  | r + 1 => 16 * supply_d r + 13

lemma G_supply_pairs (r : ℕ) :
    SegRLs tm (hg ^ (supply_d r)) [] (tw ^ (7 + 2 * r)) (kw ++ cw ^ r ++ dw ^ 2) := by
  induction r with
  | zero => exact G_prefix7
  | succ r ih =>
    have h1 := (G_Ts 2 (supply_d r)).concat ih
    have h2 := G_pair13.concat (.nil (cw ^ r ++ dw ^ 2))
    refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])) ?_ rfl ?_
      (by rw [pow_succ_list cw r]; simp only [List.append_assoc])
    · rw [← pow_add_list]
      congr 1
      dsimp [supply_d]
      omega
    · rw [← pow_add_list]
      congr 1
      omega

lemma G_supply_digits (r : ℕ) :
    SegRLs tm (hg ^ (64 * supply_d r + 61)) [] (tw ^ (10 + 2 * r))
      (kw ++ dw ++ cw ^ r ++ dw ^ 2) := by
  have h1 := (G_Ts 3 (supply_d r)).concat (G_supply_pairs r)
  have h2 := G_last61.concat (.nil (cw ^ r ++ dw ^ 2))
  refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])) ?_ rfl ?_ rfl
  · rw [← pow_add_list]
    congr 1
    omega
  · rw [← pow_add_list]
    congr 1
    omega

lemma G2_KK : SegRLs tm (hg ^ 2) [] (kw ++ kw) cw :=
  SegRLs.congr ((G_K.concat (.nil kw)).trans (G_J.concat F_K)) (by rfl) rfl rfl rfl

def supply_g (r : ℕ) : ℕ := 2 * 4 ^ (10 + 2 * r) + 64 * supply_d r + 61

lemma pow_add2_eq {α : Type} (l : List α) {a b d : ℕ} (h : a + b = d) :
    l ^ a ++ l ^ b = l ^ d := by
  subst h
  rw [← pow_add_list]

lemma pow_add3_eq {α : Type} (l : List α) {a b c d : ℕ} (h : a + (b + c) = d) :
    l ^ a ++ (l ^ b ++ l ^ c) = l ^ d := by
  subst h
  rw [← pow_add_list, ← pow_add_list]

lemma G_SUPPLY (r : ℕ) :
    SegRLs tm (hg ^ (supply_g r)) [] (tw ^ (10 + 2 * r) ++ kw ++ kw)
      (kw ++ dw ++ cw ^ r ++ dw ^ 2 ++ cw) := by
  have h1 := (G_Ts (10 + 2 * r) 2).concat G2_KK
  have h2 := (G_supply_digits r).concat (.nil cw)
  refine SegRLs.congr (h1.trans h2) ?_ rfl (by simp only [List.append_assoc])
    (by simp only [List.append_assoc])
  exact pow_add2_eq hg (by unfold supply_g; omega)

def supply_f (r n : ℕ) : ℕ :=
  8 * q4 (n + 11 + 2 * r) + 1 + (29 + 96 * q4 n + 2 * supply_g r * 4 ^ (2 + n))

lemma SUPPLY (r n : ℕ) :
    SegRLs tm (hf ^ (supply_f r n)) []
      (zw ++ lw ++ tw ^ (n + 11 + 2 * r) ++ zw ++ kw)
      (zw ++ jw ++ lw ++ mw ^ n ++ rw ++ dw ++ cw ^ r ++ dw ^ 2 ++ cw) := by
  have h1 := (BIN (n + 11 + 2 * r)).concat (.nil (zw ++ kw))
  have h2 := (F_outer (n + 11 + 2 * r)).concat (H_Z.concat (.nil kw))
  have h3_right := SegRLs.trans_eq (G_SUPPLY r) (F_K.concat (.nil (dw ++ cw ^ r ++ dw ^ 2 ++ cw)))
    (by simp only [List.append_assoc])
  have h3 := (NEAR_WRAP n (supply_g r)).concat h3_right
  have h12 := SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])
  have h123 := SegRLs.trans_eq h12 h3 (by
    rw [show 2 + (n + 11 + 2 * r) = (3 + n) + (10 + 2 * r) by omega, pow_add_list]
    simp only [List.append_assoc])
  refine SegRLs.congr h123 ?_ rfl (by simp only [List.append_assoc])
    (by simp only [List.append_assoc])
  rw [← pow_succ_list', ← pow_add_list]
  rfl

def q16 : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + 16 * q16 k

lemma q16_pow (n : ℕ) : 1 + 15 * q16 n = 16 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [q16]
    rw [Nat.pow_succ]
    omega

lemma pow4_double (n : ℕ) : 4 ^ (2 * n) = 16 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, Nat.pow_add, ih, Nat.pow_succ]
    rfl

lemma EVEN_END : SegRLs tm (hg ^ 8) (hg ++ hh) (tw ++ zw) (tw ^ 2) := by
  have h1 := G3_T.concat F_Z
  have h2 := G_L.concat H_T
  have h3 := G2_T.concat (.nil lw)
  have h4 := G_J.concat F_L
  have h5 := G_L.concat H_M
  exact SegRLs.congr (h1.trans (h2.trans (h3.trans (h4.trans h5))))
    (by rfl) (by rfl) rfl (by rfl)

lemma ODD_END : SegRLs tm (hg ^ 8) hf (tw ++ zw ++ tw) (tw ^ 3) := by
  have h := EVEN_END.concat (G_T.trans H_K)
  exact SegRLs.congr h rfl rfl rfl (by rfl)

lemma SHIFT : SegRLs tm (hg ^ 8) [] (tw ++ zw ++ tw ^ 2) (tw ^ 3 ++ zw) := by
  have h := ODD_END.concat F_T
  exact SegRLs.congr h rfl rfl rfl rfl

lemma SHIFTS (r : ℕ) :
    SegRLs tm (hg ^ (8 * q16 r)) [] (tw ++ zw ++ tw ^ (2 * r)) (tw ^ (1 + 2 * r) ++ zw) := by
  induction r with
  | zero => exact .nil (tw ++ zw)
  | succ r ih =>
    have h1 := SHIFT.concat (.nil (tw ^ (2 * r)))
    have h2 := (G_Ts 2 (8 * q16 r)).concat ih
    refine SegRLs.congr (SegRLs.trans_eq h1 h2 ?_) ?_ rfl ?_ ?_
    · rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add_list, pow_one_list]
      simp only [List.append_assoc]
    · rw [← pow_add_list]
      congr 1
      dsimp [q16]
      omega
    · rw [show 2 * (r + 1) = 2 + 2 * r by omega, pow_add_list]
      simp only [List.append_assoc]
    · rw [show 1 + 2 * (r + 1) = 2 + (1 + 2 * r) by omega, pow_add_list tw 2 (1 + 2 * r)]
      simp only [List.append_assoc]

lemma G_Mstart (n : ℕ) :
    SegRLs tm (hg ^ 2) hh (zw ++ jw ++ lw ++ mw ^ n) (tw ++ zw ++ tw ^ (1 + n)) := by
  have h1 := G_Z.concat (G_J.concat (F_L.concat (.nil (mw ^ n))))
  have h2 := (G_Ls 1).concat (H_Ms (1 + n))
  refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by rw [Nat.add_comm 1 n, pow_succ_list]; rfl))
    (by rfl) rfl (by simp only [List.append_assoc]) (by simp only [pow_one_list, List.append_assoc])

lemma M_ODD (r : ℕ) :
    SegRLs tm (hg ^ (2 + 8 * q16 (2 + r))) (hh ++ hg ++ hh)
      (zw ++ jw ++ lw ++ mw ^ (1 + 2 * r)) (tw ^ (4 + 2 * r)) := by
  have h1 := G_Mstart (1 + 2 * r)
  have h2 := SHIFTS (1 + r)
  have h3 := (G_Ts (2 + 2 * r) 8).concat EVEN_END
  have h12 := SegRLs.trans_eq h1 h2 (by rw [show 2 * (1 + r) = 1 + (1 + 2 * r) by omega])
  have h123 := SegRLs.trans_eq h12 h3 (by
    rw [show 1 + 2 * (1 + r) = (2 + 2 * r) + 1 by omega, pow_add_list, pow_one_list]
    simp only [List.append_assoc])
  refine SegRLs.congr h123 ?_ (by simp only [List.append_assoc, List.nil_append]) rfl
    (by rw [show 4 + 2 * r = (2 + 2 * r) + 2 by omega, pow_add_list tw (2 + 2 * r) 2])
  rw [← pow_add_list, ← pow_add_list]
  congr 1
  have hpow : 4 ^ (2 + 2 * r) = 16 ^ (1 + r) := by
    rw [show 2 + 2 * r = 2 * (1 + r) by omega, pow4_double]
  have hq := q16_pow (1 + r)
  rw [hpow, show 2 + r = (1 + r) + 1 by omega]
  dsimp [q16]
  omega

lemma GH_JC : SegRLs tm (hg ++ hh) [] (jw ++ cw) (zw ++ tw ++ jw) := by
  have h1 := G_J.concat (F_L.concat (.nil rw))
  have h2 := H_L.concat (H_M.concat H_R)
  exact SegRLs.congr (SegRLs.trans_eq h1 h2 rfl) rfl rfl rfl rfl

lemma F_JC : SegRLs tm hf [] (jw ++ cw) (tw ++ mw ++ rw) :=
  SegRLs.congr (F_J.concat (F_L.concat (.nil rw))) rfl rfl rfl rfl

lemma HGH_F : SegRLs tm (hh ++ hg ++ hh) [] (rw ++ dw) (zw ++ tw ^ 2 ++ jw) := by
  have h1 := H_R.concat (.nil dw)
  have h2 := G_J.concat (F_L.concat (.nil (mw ++ rw)))
  have h3 := H_L.concat (H_M.concat (H_M.concat H_R))
  exact SegRLs.congr (SegRLs.trans_eq h1 (SegRLs.trans_eq h2 h3 rfl) rfl) rfl rfl rfl rfl

lemma G_packet2 : SegRLs tm (hg ^ 2) [] (zw ++ tw ^ 2) (tw ^ 2 ++ zw) :=
  SegRLs.congr ((G_ZT 0).concat F_T) rfl rfl rfl rfl

lemma PACKET162 :
    SegRLs tm (hg ^ 162) [] (zw ++ tw ^ 2 ++ jw ++ cw ^ 2) (tw ^ 6 ++ mw ++ rw) := by
  have h1 := G_packet2.concat (.nil (jw ++ cw ^ 2))
  have h2 := (G_Ts 1 8).concat (EVEN_END.concat (GH_JC.concat (.nil cw)))
  have h3 := (G_Ts 2 8).concat (ODD_END.concat F_JC)
  have h12 := SegRLs.trans_eq h1 h2 (by rfl)
  have h123 := SegRLs.trans_eq h12 h3 (by rfl)
  exact SegRLs.congr h123 (by rw [← pow_add_list, ← pow_add_list]; congr 1) rfl (by rfl) (by rfl)

lemma PACKET (r : ℕ) :
    SegRLs tm (hg ^ 2892) [] (zw ++ tw ^ 2 ++ jw ++ cw ^ (2 + r))
      (jw ^ 6 ++ mw ++ rw ++ cw ^ r) := by
  have h1 := PACKET162.concat (.nil (cw ^ r))
  have h2 := (G_normalize 6).concat (.nil (mw ++ rw ++ cw ^ r))
  refine SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc]))
    (by rw [← pow_add_list]; congr 1) rfl ?_ (by simp only [List.append_assoc])
  rw [pow_add_list]
  simp only [List.append_assoc]

lemma P_calls (n k : ℕ) (r s : ListBlank Γ) (H : SideRLs tm (hf ^ k) r s) :
    (P n r) [tm]⊢* (P (n + k) s) := by
  induction k generalizing n r with
  | zero =>
    cases H
    rw [Nat.add_zero]
    exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list] at H
    obtain ⟨r₁, H₁, H₂⟩ := H.split
    refine stepStar_trans (stepPlus_to_stepStar (P_step n r r₁ H₁)) ?_
    refine stepStar_congr (ih (1 + n) r₁ H₂) rfl ?_
    rw [show 1 + n + k = n + (k + 1) by omega]

lemma supply_balance (r : ℕ) :
    6 * supply_d r + 5 = 3 * q16 (2 + r) + 755 * 4 ^ (3 + 2 * r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [show 2 + (r + 1) = (2 + r) + 1 by omega,
      show 3 + 2 * (r + 1) = (3 + 2 * r) + 2 by omega, Nat.pow_add]
    dsimp [supply_d, q16]
    omega

lemma supply_g_balance (r : ℕ) :
    24 * supply_g r = 184 + 768 * q16 (2 + r) + 3827 * 4 ^ (7 + 2 * r) := by
  have H := supply_balance r
  have P7 : 4 ^ (7 + 2 * r) = 256 * 4 ^ (3 + 2 * r) := by
    rw [show 7 + 2 * r = (3 + 2 * r) + 4 by omega, Nat.pow_add]
    omega
  have P10 : 4 ^ (10 + 2 * r) = 64 * 4 ^ (7 + 2 * r) := by
    rw [show 10 + 2 * r = (7 + 2 * r) + 3 by omega, Nat.pow_add]
    omega
  unfold supply_g
  omega

lemma budget_algebra (a b c d x y g q : ℕ)
    (Q0 : 1 + 3 * a = x) (Q1 : 1 + 3 * b = 4 * x)
    (Q11 : 1 + 3 * c = 256 * (x * y)) (Q8 : 1 + 3 * d = 4 * (x * y))
    (G : x * (24 * g) = x * (184 + 768 * q + 3827 * y)) :
    1 + (8 * c + 1 + (29 + 96 * a + 2 * g * (16 * x))) =
      2 + 16 * b + 2 * (2 + 8 * q) * (64 * x) + 2 * 2892 * (x * y) + d := by
  nlinarith

lemma supply_budget (r n : ℕ) :
    1 + supply_f r n =
      2 + 16 * q4 (1 + n) + 2 * (2 + 8 * q16 (2 + r)) * 4 ^ (3 + n) +
        2 * 2892 * 4 ^ (7 + n + 2 * r) + q4 (8 + n + 2 * r) := by
  have P1 : 4 ^ (1 + n) = 4 * 4 ^ n := by rw [Nat.add_comm 1 n, Nat.pow_succ]; ring
  have P2 : 4 ^ (2 + n) = 16 * 4 ^ n := by rw [Nat.add_comm 2 n, Nat.pow_add]; ring
  have P3 : 4 ^ (3 + n) = 64 * 4 ^ n := by rw [Nat.add_comm 3 n, Nat.pow_add]; ring
  have P7 : 4 ^ (7 + n + 2 * r) = 4 ^ n * 4 ^ (7 + 2 * r) := by
    rw [show 7 + n + 2 * r = n + (7 + 2 * r) by omega, Nat.pow_add]
  have P8 : 4 ^ (8 + n + 2 * r) = 4 * (4 ^ n * 4 ^ (7 + 2 * r)) := by
    rw [show 8 + n + 2 * r = (7 + n + 2 * r) + 1 by omega, Nat.pow_succ, P7]; ring
  have P11 : 4 ^ (n + 11 + 2 * r) = 256 * (4 ^ n * 4 ^ (7 + 2 * r)) := by
    rw [show n + 11 + 2 * r = (7 + n + 2 * r) + 4 by omega, Nat.pow_add, P7]; ring
  have Q0 := q4_pow n
  have Q1 := q4_pow (1 + n); rw [P1] at Q1
  have Q11 := q4_pow (n + 11 + 2 * r); rw [P11] at Q11
  have Q8 := q4_pow (8 + n + 2 * r); rw [P8] at Q8
  have G := congrArg (fun z => 4 ^ n * z) (supply_g_balance r)
  unfold supply_f
  rw [P2, P3, P7]
  exact budget_algebra _ _ _ _ _ _ _ _ Q0 Q1 Q11 Q8 G

def e (a b : ℕ) : ℕ :=
  11 + 4 * q4 (24 + 2 * a + 2 * b) + 48 * q4 (7 + 2 * b) +
    supply_g (3 + a) * 4 ^ (9 + 2 * b)

lemma supply_index (a b : ℕ) : supply_f (3 + a) (7 + 2 * b) = 8 + 2 * e a b := by
  unfold supply_f e
  rw [show 7 + 2 * b + 11 + 2 * (3 + a) = 24 + 2 * a + 2 * b by omega,
    show 2 + (7 + 2 * b) = 9 + 2 * b by omega]
  ring

lemma family_budget (a b : ℕ) :
    2 + 16 * q4 (8 + 2 * e a b) +
      2 * (2 + 8 * q16 (5 + b)) * 4 ^ (10 + 2 * e a b) +
      2 * 2892 * 4 ^ (20 + 2 * e a b + 2 * b) + q4 (21 + 2 * e a b + 2 * b) =
      9 + 2 * e b (e a b) := by
  have H := supply_budget (3 + b) (7 + 2 * e a b)
  rw [supply_index] at H
  rw [show 1 + (7 + 2 * e a b) = 8 + 2 * e a b by omega,
    show 2 + (3 + b) = 5 + b by omega,
    show 3 + (7 + 2 * e a b) = 10 + 2 * e a b by omega,
    show 7 + (7 + 2 * e a b) + 2 * (3 + b) = 20 + 2 * e a b + 2 * b by omega,
    show 8 + (7 + 2 * e a b) + 2 * (3 + b) = 21 + 2 * e a b + 2 * b by omega] at H
  omega

lemma service_tail {hs : List (DH0 Γ Λ × DH0 Γ Λ)} {u v : List Γ} (w : List Γ)
    (H : SegRLs tm hs [] u v) : SegRLs tm hs [] (u ++ w) (v ++ w) :=
  H.concat (.nil w)

lemma F_T_service (n k : ℕ) {u v : List Γ}
    (H : SegRLs tm (hg ^ k) [] u v) :
    SegRLs tm (hf ^ (2 * k * 4 ^ n)) [] (tw ^ (1 + n) ++ u) (tw ^ (1 + n) ++ v) :=
  (F_T_calls n k).concat H

def family_word (a b : ℕ) : List Γ :=
  tw ++ lw ^ (9 + 2 * e a b) ++ kw ++ tw ++ lw ++
    tw ^ (24 + 2 * a + 2 * b) ++ zw ++ kw ++ tw ++ [O, O]

def family_col (a b : ℕ) : List Γ :=
  tw ^ (11 + 2 * e a b) ++ zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++
    rw ++ dw ++ cw ^ (3 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]

def family_mid (a b : ℕ) : List Γ :=
  tw ^ (21 + 2 * e a b + 2 * b) ++ zw ++ tw ^ 2 ++ jw ++
    cw ^ (3 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]

def family_end (a b : ℕ) : List Γ :=
  zw ++ jw ^ (26 + 2 * e a b + 2 * b) ++ mw ++ rw ++
    cw ^ (1 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]

lemma family_column (a b : ℕ) :
    SegRLs tm (hf ^ (2 + 16 * q4 (8 + 2 * e a b))) []
      (family_word a b) (family_col a b) := by
  have h_sup := service_tail (tw ++ [O, O]) (SUPPLY (3 + a) (7 + 2 * b))
  have h_sup' : SegRLs tm (hf ^ (8 + 2 * e a b)) []
      (zw ++ (lw ++ tw ^ (24 + 2 * a + 2 * b) ++ zw ++ kw ++ tw ++ [O, O]))
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ cw ^ (3 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]) := by
    refine SegRLs.congr h_sup (by rw [supply_index a b]) rfl ?_ (by simp only [List.append_assoc])
    rw [show 7 + 2 * b + 11 + 2 * (3 + a) = 24 + 2 * a + 2 * b by omega]
    simp only [List.append_assoc]
  have h_col := COLUMN (8 + 2 * e a b)
    (lw ++ tw ^ (24 + 2 * a + 2 * b) ++ zw ++ kw ++ tw ++ [O, O])
    (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ cw ^ (3 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O])
    [] h_sup'
  unfold family_word family_col
  refine SegRLs.congr h_col rfl rfl ?_ ?_
  · rw [show 9 + 2 * e a b = 1 + (8 + 2 * e a b) by omega]
    simp only [List.append_assoc]
  · rw [show 11 + 2 * e a b = (8 + 2 * e a b) + 3 by omega]
    simp only [List.append_assoc]

lemma M_block (r : ℕ) :
    SegRLs tm (hg ^ (2 + 8 * q16 (2 + r))) []
      (zw ++ jw ++ lw ++ mw ^ (1 + 2 * r) ++ rw ++ dw)
      (tw ^ (4 + 2 * r) ++ zw ++ tw ^ 2 ++ jw) := by
  have h := (M_ODD r).concat HGH_F
  exact SegRLs.congr h rfl rfl (by simp only [List.append_assoc]) (by simp only [List.append_assoc])

lemma family_m (a b : ℕ) :
    SegRLs tm (hf ^ (2 * (2 + 8 * q16 (5 + b)) * 4 ^ (10 + 2 * e a b))) []
      (family_col a b) (family_mid a b) := by
  have h_mb := service_tail (cw ^ (3 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]) (M_block (3 + b))
  have h := F_T_service (10 + 2 * e a b) (2 + 8 * q16 (2 + (3 + b))) h_mb
  unfold family_col family_mid
  refine SegRLs.congr h ?_ rfl ?_ ?_
  · rw [show 2 + (3 + b) = 5 + b by omega]
  · rw [show 11 + 2 * e a b = 1 + (10 + 2 * e a b) by omega,
      show 7 + 2 * b = 1 + 2 * (3 + b) by omega]
    simp only [List.append_assoc]
  · rw [show 21 + 2 * e a b + 2 * b = (1 + (10 + 2 * e a b)) + (4 + 2 * (3 + b)) by omega,
      pow_add_list tw (1 + (10 + 2 * e a b)) (4 + 2 * (3 + b))]
    simp only [List.append_assoc]

lemma family_finish (a b : ℕ) :
    SegRLs tm (hf ^ (2 * 2892 * 4 ^ (20 + 2 * e a b + 2 * b) + q4 (21 + 2 * e a b + 2 * b))) []
      (family_mid a b) (family_end a b) := by
  have h1 := F_T_service (20 + 2 * e a b + 2 * b) 2892
    (service_tail (dw ^ 2 ++ cw ++ tw ++ [O, O]) (PACKET (1 + a)))
  have h2 := service_tail (jw ^ 6 ++ mw ++ rw ++ cw ^ (1 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O])
    (F_normalize (20 + 2 * e a b + 2 * b))
  have h12 := SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])
  unfold family_mid family_end
  refine SegRLs.congr h12 ?_ rfl ?_ ?_
  · exact pow_add2_eq hf (by rw [show 1 + (20 + 2 * e a b + 2 * b) = 21 + 2 * e a b + 2 * b by omega])
  · rw [show 21 + 2 * e a b + 2 * b = 1 + (20 + 2 * e a b + 2 * b) by omega,
      show 3 + a = 2 + (1 + a) by omega]
    simp only [List.append_assoc]
  · rw [show 26 + 2 * e a b + 2 * b = (20 + 2 * e a b + 2 * b) + 6 by omega,
      pow_add_list jw (20 + 2 * e a b + 2 * b) 6]
    simp only [List.append_assoc]

lemma family_services (a b : ℕ) :
    SegRLs tm (hf ^ (9 + 2 * e b (e a b))) [] (family_word a b) (family_end a b) := by
  have h := (family_column a b).trans ((family_m a b).trans (family_finish a b))
  refine SegRLs.congr h ?_ rfl rfl rfl
  exact pow_add3_eq hf (by have := family_budget a b; omega)

def family_prefix (a : ℕ) : List Γ :=
  [I] ++ rw ++ cw ^ a ++ dw ^ 2 ++ cw ++ tw ++ [O, O]

def family_after_zero (a b : ℕ) : List Γ :=
  tw ++ lw ^ (9 + 2 * e b (e a b)) ++ kw ++ tw ++ aw ++
    tw ^ (25 + 2 * e a b + 2 * b) ++ [I, O, I] ++ bw ++ rw ++
    cw ^ (1 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]

lemma reset_recut (a k : ℕ) :
    aw ++ tw ^ (1 + k) ++ [I, O, I] ++ bw ++ rw ++ cw ^ (1 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O] =
      lw ++ tw ^ k ++ zw ++ kw ++ tw ++ [O, O] ++ family_prefix a := by
  unfold family_prefix
  rw [Nat.add_comm 1 k, pow_succ_list, Nat.add_comm 1 a, pow_succ_list]
  have hbw := bw_comm_T k
  have haw : aw ++ tw ++ tw ^ k = lw ++ (bw ++ tw ^ k) := rfl
  rw [← List.append_assoc aw tw (tw ^ k), haw, hbw]
  simp only [List.append_assoc]
  rfl

lemma family_recut (a b : ℕ) :
    family_after_zero a b = family_word b (e a b) ++ family_prefix a := by
  unfold family_after_zero family_word
  have h := reset_recut a (24 + 2 * b + 2 * e a b)
  rw [show 25 + 2 * e a b + 2 * b = 1 + (24 + 2 * b + 2 * e a b) by omega]
  simp only [List.append_assoc] at h ⊢
  rw [h]

lemma P_service (n k : ℕ) (w1 w2 : List Γ) (u : ListBlank Γ)
    (H : SegRLs tm (hf ^ k) [] w1 w2) :
    (P n (w1 +> u)) [tm]⊢* (P (n + k) (w2 +> u)) :=
  P_calls n k (w1 +> u) (w2 +> u) (H.sideRLs_concat (.nil u))

lemma P_service_zero (k : ℕ) (w1 w2 : List Γ) (u : ListBlank Γ)
    (H : SegRLs tm (hf ^ k) [] w1 w2) :
    (P 0 (w1 +> u)) [tm]⊢* (P k (w2 +> u)) := by
  have h := P_service 0 k w1 w2 u H
  rwa [Nat.zero_add] at h

lemma family_reset (a b : ℕ) (u : ListBlank Γ) :
    (P (9 + 2 * e b (e a b)) (family_end a b +> u)) [tm]⊢⁺
      (P 0 (family_word b (e a b) +> (family_prefix a +> u))) := by
  have h := zero_return (9 + 2 * e b (e a b)) (25 + 2 * e a b + 2 * b)
    ((bw ++ rw ++ cw ^ (1 + a) ++ dw ^ 2 ++ cw ++ tw ++ [O, O]) +> u)
  refine stepPlus_congr h ?_ ?_
  · unfold family_end
    rw [show 26 + 2 * e a b + 2 * b = 1 + (25 + 2 * e a b + 2 * b) by omega]
    simp only [append_assoc]
    rfl
  · rw [← append_assoc (family_word b (e a b)), ← family_recut a b]
    unfold family_after_zero
    simp only [append_assoc]

def Inv (a b : ℕ) (u : ListBlank Γ) : Cfg Γ Λ :=
  P 0 (family_word a b +> u)

lemma I_step (a b : ℕ) (u : ListBlank Γ) :
    (Inv a b u) [tm]⊢⁺ (Inv b (e a b) (family_prefix a +> u)) :=
  stepStar_stepPlus_trans
    (P_service_zero (9 + 2 * e b (e a b)) (family_word a b) (family_end a b) u
      (family_services a b))
    (family_reset a b u)

lemma tower_budget (a b : ℕ) :
    2 + 16 * q4 (8 + 2 * b) + 2 * (2 + 8 * q16 (5 + a)) * 4 ^ (10 + 2 * b) +
      2 * 2892 * 4 ^ (20 + 2 * a + 2 * b) + q4 (21 + 2 * a + 2 * b) = 9 + 2 * e a b := by
  have H := supply_budget (3 + a) (7 + 2 * b)
  rw [supply_index] at H
  rw [show 1 + (7 + 2 * b) = 8 + 2 * b by omega,
    show 2 + (3 + a) = 5 + a by omega,
    show 3 + (7 + 2 * b) = 10 + 2 * b by omega,
    show 7 + (7 + 2 * b) + 2 * (3 + a) = 20 + 2 * a + 2 * b by omega,
    show 8 + (7 + 2 * b) + 2 * (3 + a) = 21 + 2 * a + 2 * b by omega] at H
  omega

def supply_count (n k j : ℕ) : ℕ :=
  8 * q4 k + 1 + (4 * 4 ^ (1 + k) + (29 + 96 * q4 n + 2 * j * 4 ^ (2 + n)))

lemma reset_supply (n k z j : ℕ) (u v w t : List Γ) (E_eq : k + 2 = 3 + n + z)
    (H : SegRLs tm hh [] u v) (K : SegRLs tm (hg ^ 2) [] v w)
    (L : SegRLs tm (hg ^ j ++ hf) [] (tw ^ z ++ w) t) :
    SegRLs tm (hf ^ (supply_count n k j)) []
      (zw ++ lw ++ tw ^ k ++ u) (zw ++ jw ++ lw ++ mw ^ n ++ t) := by
  have h1 := service_tail u (BIN k)
  have h2 := (F_outer k).concat H
  have h3 := F_T_service (1 + k) 2 K
  have h4 := (NEAR_WRAP n j).concat L
  have h12 := SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])
  have h123 := SegRLs.trans_eq h12 h3 (by rw [show 2 + k = 1 + (1 + k) by omega])
  have h1234 := SegRLs.trans_eq h123 h4 (by
    rw [show 1 + (1 + k) = (3 + n) + z by omega, pow_add_list]
    simp only [List.append_assoc])
  refine SegRLs.congr h1234 ?_ rfl (by simp only [List.append_assoc])
    (by simp only [List.append_assoc])
  rw [← pow_succ_list', ← pow_add_list, ← pow_add_list]
  congr 1
  unfold supply_count
  omega

-- ============================================================================
-- 4. Blank-Start Entrance for TM13 (`SOBCv13.v:1867-2440`)
-- ============================================================================

lemma entry_F5 : SegRLs tm (hf ^ 5) [] (zw ++ tw ^ 2) (tw ++ lw ++ zw) :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma entry_G4 : SegRLs tm (hg ^ 4) [] (tw ++ lw ++ zw) (tw ^ 2 ++ kw) :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma entry_G30 : SegRLs tm (hg ^ 30) [] (tw ++ lw ++ zw) (jw ^ 3) := by
  have h1 := entry_G4
  have h2 := (G_Ts 2 1).concat G_K
  have h3 := (G_normalize 2).concat (.nil jw)
  exact SegRLs.congr (h1.trans (h2.trans h3))
    (by rw [← pow_add_list, ← pow_add_list]; congr 1) rfl rfl (by rfl)

lemma G_append' (n k m : ℕ) (hm : 4 * n + k = m) (u v w : List Γ)
    (H : SegRLs tm (hg ^ n) [] u v)
    (H' : SegRLs tm (hg ^ k) [] (tw ++ v) w) :
    SegRLs tm (hg ^ m) [] (tw ++ u) w := by
  subst hm; exact G_append n k u v w H H'

def entry10_calls : ℕ := 4 * (4 * (4 * 2431 + 3) + 3) + 2

lemma entry_G10 : SegRLs tm (hg ^ entry10_calls) [] (tw ^ 10)
    (jw ++ lw ++ mw ^ 4 ++ rw ++ kw ++ jw ++ tw) := by
  have H2 := G_append' 0 2 2 rfl tw tw (jw ++ tw) (.nil tw)
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H3 := G_append' 2 1 9 rfl (tw ^ 2) (jw ++ tw) (kw ++ jw ++ tw) H2
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H4 := G_append' 9 1 37 rfl (tw ^ 3) (kw ++ jw ++ tw) (kw ++ kw ++ jw ++ tw) H3
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H5 := G_append' 37 3 151 rfl (tw ^ 4) (kw ++ kw ++ jw ++ tw)
    (lw ++ rw ++ kw ++ jw ++ tw) H4
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H6 := G_append' 151 3 607 rfl (tw ^ 5)
    (lw ++ rw ++ kw ++ jw ++ tw) (lw ++ mw ++ rw ++ kw ++ jw ++ tw) H5
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H7 := G_append' 607 3 2431 rfl (tw ^ 6)
    (lw ++ mw ++ rw ++ kw ++ jw ++ tw) (lw ++ mw ^ 2 ++ rw ++ kw ++ jw ++ tw) H6
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H8 := G_append' 2431 3 9727 rfl (tw ^ 7)
    (lw ++ mw ^ 2 ++ rw ++ kw ++ jw ++ tw) (lw ++ mw ^ 3 ++ rw ++ kw ++ jw ++ tw) H7
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H9 := G_append' 9727 3 38911 rfl (tw ^ 8)
    (lw ++ mw ^ 3 ++ rw ++ kw ++ jw ++ tw) (lw ++ mw ^ 4 ++ rw ++ kw ++ jw ++ tw) H8
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  exact G_append' 38911 2 entry10_calls rfl (tw ^ 9)
    (lw ++ mw ^ 4 ++ rw ++ kw ++ jw ++ tw)
    (jw ++ lw ++ mw ^ 4 ++ rw ++ kw ++ jw ++ tw) H9
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))

def entry_b : List Γ := [I, O, O, I, O, O, O, I, O, I, I, O, O, I, I, O, I]
@[irreducible] def entry_first_calls : ℕ := 8 * q4 9 + 1 + (2 * entry10_calls + 1)

lemma entry_first_service : SegRLs tm (hf ^ entry_first_calls) []
    (zw ++ lw ++ tw ^ 10 ++ [I, O, I])
    (zw ++ jw ++ lw ++ mw ^ 4 ++ rw ++ aw ++ entry_b) := by
  have h1 := (BIN 9).concat (.nil (tw ++ [I, O, I]))
  have h2 := (F_outer 9).concat (H_T.concat (.nil [I, O, I]))
  have h3 := (F_T_calls 0 entry10_calls).concat (entry_G10.concat (.nil (lw ++ [I, O, I])))
  have h4 := F_T.concat (.nil (jw ++ lw ++ mw ^ 4 ++ rw ++ kw ++ jw ++ tw ++ lw ++ [I, O, I]))
  have h12 := SegRLs.trans_eq h1 h2 (by rfl)
  have h123 := SegRLs.trans_eq h12 h3 (by rfl)
  have h1234 := SegRLs.trans_eq h123 h4 (by rfl)
  refine SegRLs.congr h1234 ?_ rfl (by rfl) (by rfl)
  rw [← pow_succ_list', ← pow_add_list, ← pow_succ_list']
  congr 1
  unfold entry_first_calls
  rw [Nat.pow_zero]
  omega

def entry8_calls : ℕ := 4 * (4 * 1911 + 3) + 1

lemma entry_G8 : SegRLs tm (hg ^ entry8_calls) [] (tw ^ 8) (kw ++ dw ++ cw ^ 2) := by
  have H2 := G7
  have H3 := G_append' 7 1 29 rfl (tw ^ 2) cw (kw ++ cw) H2
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H4 := G_append' 29 3 119 rfl (tw ^ 3) (kw ++ cw) (cw ^ 2) H3
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H5 := G_append' 119 1 477 rfl (tw ^ 4) (cw ^ 2) (kw ++ cw ^ 2) H4
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H6 := G_append' 477 3 1911 rfl (tw ^ 5) (kw ++ cw ^ 2) (cw ^ 3) H5
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  have H7 := G_append' 1911 3 7647 rfl (tw ^ 6) (cw ^ 3) (dw ++ cw ^ 2) H6
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))
  exact G_append' 7647 1 entry8_calls rfl (tw ^ 7)
    (dw ++ cw ^ 2) (kw ++ dw ++ cw ^ 2) H7
    (BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide))

def entry_clean_calls : ℕ := 2 + 8 * q16 2 + 8 * 4 ^ 4 + 2 * q4 8

lemma entry_clean : SegRLs tm (hg ^ entry_clean_calls) []
    (zw ++ jw ++ lw ++ mw ^ 4 ++ rw ++ aw) (jw ^ 8 ++ [O, O]) := by
  have h1 := (G_Mstart 4).concat (H_R.concat (.nil aw))
  have h2 := (SHIFTS 2).concat (.nil (tw ++ jw ++ aw))
  have h3 := (G_Ts 4 8).concat (ODD_END.concat (F_J.concat F_A))
  have h4 := (G_normalize 8).concat (.nil [O, O])
  have h12 := SegRLs.trans_eq h1 h2 (by rfl)
  have h123 := SegRLs.trans_eq h12 h3 (by rfl)
  have h1234 := SegRLs.trans_eq h123 h4 (by rfl)
  exact SegRLs.congr h1234
    (by rw [← pow_add_list, ← pow_add_list, ← pow_add_list]; rfl)
    rfl (by rfl) (by rfl)

@[irreducible] def entry_m : ℕ := 2 + 16 * q4 5 + 2 * 30 * 4 ^ 7 + q4 8

lemma entry_services : SegRLs tm (hf ^ entry_m) []
    (tw ++ lw ^ 6 ++ kw ++ tw ^ 3 ++ zw ++ [I]) (zw ++ jw ^ 10 ++ zw ++ [I]) := by
  have h1 := COLUMN 5 (tw ^ 2 ++ zw ++ [I]) (tw ++ lw ++ zw ++ zw ++ [I]) []
    (SegRLs.congr (entry_F5.concat (.nil (zw ++ [I]))) rfl rfl (by rfl) (by rfl))
  have h2 := (F_T_calls 7 30).concat (entry_G30.concat (.nil (zw ++ [I])))
  have h3 := (F_normalize 7).concat (.nil (jw ^ 3 ++ zw ++ [I]))
  have h12 := SegRLs.trans_eq h1 h2 (by rfl)
  have h123 := SegRLs.trans_eq h12 h3 (by rfl)
  refine SegRLs.congr h123 ?_ rfl (by rfl) (by rfl)
  rw [show (1 + 7 : ℕ) = 8 from rfl, ← pow_add_list, ← pow_add_list]
  unfold entry_m
  rfl

lemma entry_before_anchor :
    (init []) [tm]⊢* (P entry_m (zw +> (jw ^ 10 +> (zw +> ([I] +> default))))) := by
  refine stepStar_trans init_raw ?_
  have h := P_service_zero entry_m
    (tw ++ lw ^ 6 ++ kw ++ tw ^ 3 ++ zw ++ [I])
    (zw ++ jw ^ 10 ++ zw ++ [I]) default entry_services
  refine stepStar_congr h ?_ ?_
  · simp only [append_assoc]
  · simp only [append_assoc]

lemma entry_after_anchor :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ entry_m +> (kw +> (tw +> (aw +> (bw +> (tw ^ 10 +> ([I, O, I] +> default))))))))) :=
  stepStar_trans entry_before_anchor (stepPlus_to_stepStar (anchor_return entry_m 10))

lemma entry_m_count : entry_m = 1 + entry_first_calls := by
  unfold entry_m entry_first_calls
  decide

@[irreducible] def entry_a0 : ℕ := 167 + 505 * 1000

lemma entry_m_odd : entry_m = 9 + 2 * entry_a0 := by
  unfold entry_m entry_a0
  decide

def entry_H_of (p : ℕ) : ℕ := 2 + 16 * q4 p
def entry_B_of (m p : ℕ) : ℕ := entry_H_of p + 2 * entry_clean_calls * 4 ^ (1 + m) + q4 (2 + m)
local notation "entry_H" => entry_H_of entry_first_calls
local notation "entry_B" => entry_B_of entry_m entry_first_calls

lemma entry_m_first : entry_m = 1 + entry_first_calls := entry_m_count

lemma entry_second_services_gen (m p : ℕ)
    (hm : m = 1 + p)
    (h_first : SegRLs tm (hf ^ p) []
      (zw ++ lw ++ tw ^ 10 ++ [I, O, I])
      (zw ++ jw ++ lw ++ mw ^ 4 ++ rw ++ aw ++ entry_b)) :
    SegRLs tm (hf ^ (entry_B_of m p)) []
      (tw ++ lw ^ m ++ kw ++ tw ++ aw ++ bw ++ tw ^ 10 ++ [I, O, I])
      (zw ++ jw ^ (m + 9) ++ [O, O] ++ entry_b) := by
  subst hm
  unfold entry_B_of entry_H_of
  have h1 := COLUMN p (lw ++ tw ^ 10 ++ [I, O, I])
    (zw ++ jw ++ lw ++ mw ^ 4 ++ rw ++ aw ++ entry_b) []
    (SegRLs.congr h_first rfl rfl (by simp only [List.append_assoc]) rfl)
  have h2 := (F_T_calls (1 + (1 + p)) entry_clean_calls).concat
    (entry_clean.concat (.nil entry_b))
  have h3 := (F_normalize (1 + (1 + p))).concat (.nil (jw ^ 8 ++ [O, O] ++ entry_b))
  have h1' : SegRLs tm (hf ^ (2 + 16 * q4 p)) []
      (tw ++ lw ^ (1 + p) ++ kw ++ tw ++ aw ++ bw ++ tw ^ 10 ++ [I, O, I])
      (tw ^ (1 + p + 2) ++ zw ++ jw ++ lw ++ mw ^ 4 ++ rw ++ aw ++ entry_b) := by
    refine SegRLs.congr h1 rfl rfl ?_ ?_
    · have h_aw : aw ++ (bw ++ (tw ^ 10 ++ [I, O, I])) = lw ++ (tw ^ 10 ++ [I, O, I]) := rfl
      simp only [List.append_assoc, h_aw]
    · rw [show p + 3 = 1 + p + 2 by omega]
      simp only [List.append_assoc]
  have h2' : SegRLs tm (hf ^ (2 * entry_clean_calls * 4 ^ (1 + (1 + p)))) []
      (tw ^ (1 + p + 2) ++ zw ++ jw ++ lw ++ mw ^ 4 ++ rw ++ aw ++ entry_b)
      (tw ^ (1 + p + 2) ++ jw ^ 8 ++ [O, O] ++ entry_b) := by
    refine SegRLs.congr h2 rfl rfl ?_ ?_
    · rw [show 1 + (1 + (1 + p)) = 1 + p + 2 by omega]
      simp only [List.append_assoc]
    · rw [show 1 + (1 + (1 + p)) = 1 + p + 2 by omega]
      simp only [List.append_assoc]
  have h3' : SegRLs tm (hf ^ q4 (2 + (1 + p))) []
      (tw ^ (1 + p + 2) ++ jw ^ 8 ++ [O, O] ++ entry_b)
      (zw ++ jw ^ (1 + p + 9) ++ [O, O] ++ entry_b) := by
    refine SegRLs.congr h3 ?_ rfl ?_ ?_
    · rw [show 1 + (1 + (1 + p)) = 2 + (1 + p) by omega]
    · rw [show 1 + (1 + (1 + p)) = 1 + p + 2 by omega]
      simp only [List.append_assoc]
    · rw [show 1 + p + 9 = (1 + (1 + p)) + 8 by omega,
        pow_add_list jw (1 + (1 + p)) 8]
      simp only [List.append_assoc]
  refine SegRLs.congr ((h1'.trans h2').trans h3') ?_ rfl rfl rfl
  rw [← pow_add_list, ← pow_add_list]

lemma entry_second_services : SegRLs tm (hf ^ entry_B) []
    (tw ++ lw ^ entry_m ++ kw ++ tw ++ aw ++ bw ++ tw ^ 10 ++ [I, O, I])
    (zw ++ jw ^ (entry_m + 9) ++ [O, O] ++ entry_b) :=
  entry_second_services_gen entry_m entry_first_calls entry_m_first entry_first_service

lemma entry_after_zero_gen (m B : ℕ)
    (h_anch : (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ m +> (kw +> (tw +> (aw +> (bw +> (tw ^ 10 +> ([I, O, I] +> default))))))))))
    (h_sec : SegRLs tm (hf ^ B) []
      (tw ++ lw ^ m ++ kw ++ tw ++ aw ++ bw ++ tw ^ 10 ++ [I, O, I])
      (zw ++ jw ^ (m + 9) ++ [O, O] ++ entry_b)) :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ B +> (kw +> (tw +> (aw +> (tw ^ (m + 8) +>
        ([I, O, I] +> (entry_b +> default))))))))) := by
  have h_bef : (init []) [tm]⊢*
      (P B (zw +> (jw ^ (m + 9) +> ([O, O] +> (entry_b +> default))))) := by
    refine stepStar_trans h_anch ?_
    have h := P_service_zero B
      (tw ++ lw ^ m ++ kw ++ tw ++ aw ++ bw ++ tw ^ 10 ++ [I, O, I])
      (zw ++ jw ^ (m + 9) ++ [O, O] ++ entry_b) default h_sec
    refine stepStar_congr h ?_ ?_
    · simp only [append_assoc]
    · simp only [append_assoc]
  refine stepStar_trans h_bef ?_
  have h := zero_return B (m + 8) (entry_b +> default)
  rw [show 1 + (m + 8) = m + 9 by omega] at h
  exact stepPlus_to_stepStar h

lemma entry_after_zero :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ entry_B +> (kw +> (tw +> (aw +> (tw ^ (entry_m + 8) +>
        ([I, O, I] +> (entry_b +> default))))))))) :=
  entry_after_zero_gen entry_m entry_B entry_after_anchor entry_second_services

def entry_b0_of (m : ℕ) : ℕ := 501 + 183 * 1000 + (522 + 550 * 1000) * q4 m
local notation "entry_b0" => entry_b0_of entry_m

lemma q4_succ (n : ℕ) : q4 (1 + n) = 1 + 4 * q4 n := by
  rw [Nat.add_comm 1 n]
  rfl

lemma second_budget_identity (m p : ℕ) (hm : m = 1 + p) :
    entry_B_of m p = 9 + 2 * entry_b0_of m := by
  subst hm
  unfold entry_B_of entry_H_of entry_b0_of
  have hc : entry_clean_calls = 876 + 45 * 1000 := by decide
  rw [hc]
  have P4 := q4_pow (1 + p)
  have Q2 := q4_add 2 (1 + p)
  have hpow : 4 ^ (1 + (1 + p)) = 4 * 4 ^ (1 + p) := by
    rw [Nat.add_comm 1 (1 + p), Nat.pow_succ]; ring
  have hq2 : q4 2 = 5 := rfl
  have hp2 : 4 ^ 2 = 16 := rfl
  have hq1 : q4 (1 + p) = 1 + 4 * q4 p := q4_succ p
  rw [hq2, hp2] at Q2
  rw [hpow, Q2, hq1]
  omega

lemma entry_B_index : entry_B = 9 + 2 * entry_b0 :=
  second_budget_identity entry_m entry_first_calls entry_m_first

def third_u0 : List Γ := zw ++ [I, I]
def third_u1 : List Γ := kw ++ [I, I]
def third_u2 : List Γ := lw ++ bw

lemma third_H : SegRLs tm hh [] third_u0 third_u1 :=
  service_tail [I, I] H_Z

lemma third_G2 : SegRLs tm (hg ^ 2) [] third_u1 third_u2 :=
  SegRLs.congr ((service_tail [I, I] G_K).trans (G_J.concat F_11)) (by rfl) rfl rfl rfl

lemma third_G8F :
    SegRLs tm (hg ^ entry8_calls ++ hf) []
      (tw ^ 8 ++ third_u2) (rw ++ dw ++ cw ^ 2 ++ third_u2) := by
  have h1 := service_tail third_u2 entry_G8
  have h2 := F_K.concat (.nil (dw ++ cw ^ 2 ++ third_u2))
  exact SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc]))
    rfl rfl rfl (by simp only [List.append_assoc])

def third_f (n : ℕ) : ℕ :=
  8 * q4 (n + 9) + (1 + (4 * 4 ^ (n + 10) + (29 + 96 * q4 n + 2 * entry8_calls * 4 ^ (2 + n))))

def third_input (n : ℕ) : List Γ := zw ++ lw ++ tw ^ (n + 9) ++ third_u0
def third_output (n : ℕ) : List Γ := zw ++ jw ++ lw ++ mw ^ n ++ rw ++ dw ++ cw ^ 2 ++ third_u2

lemma third_supply (n : ℕ) :
    SegRLs tm (hf ^ (third_f n)) [] (third_input n) (third_output n) := by
  have h := reset_supply n (n + 9) 8 entry8_calls third_u0 third_u1 third_u2
    (rw ++ dw ++ cw ^ 2 ++ third_u2) (by omega) third_H third_G2 third_G8F
  unfold third_f third_input third_output
  refine SegRLs.congr h ?_ rfl (by simp only [List.append_assoc]) (by simp only [List.append_assoc])
  congr 1
  unfold supply_count
  rw [show 1 + (n + 9) = n + 10 by omega]
  ring

def third_source (a b : ℕ) : List Γ :=
  tw ++ lw ^ (9 + 2 * b) ++ kw ++ tw ++ lw ++ tw ^ (16 + 2 * a) ++ third_u0

def third_col (a b : ℕ) : List Γ := tw ^ (11 + 2 * b) ++ third_output (7 + 2 * a)

def third_mid (a b : ℕ) : List Γ :=
  tw ^ (21 + 2 * a + 2 * b) ++ zw ++ tw ^ 2 ++ jw ++ cw ^ 2 ++ third_u2

def third_end (a b : ℕ) : List Γ :=
  zw ++ jw ^ (26 + 2 * a + 2 * b) ++ mw ++ rw ++ third_u2

lemma third_column (a b : ℕ) (H : third_f (7 + 2 * a) = 8 + 2 * b) :
    SegRLs tm (hf ^ (2 + 16 * q4 (8 + 2 * b))) []
      (third_source a b) (third_col a b) := by
  have h_sup : SegRLs tm (hf ^ (8 + 2 * b)) []
      (zw ++ (lw ++ tw ^ (16 + 2 * a) ++ third_u0)) (third_output (7 + 2 * a)) := by
    refine SegRLs.congr (third_supply (7 + 2 * a)) (by rw [H]) rfl ?_ rfl
    unfold third_input
    rw [show 7 + 2 * a + 9 = 16 + 2 * a by omega]
    simp only [List.append_assoc]
  have h := COLUMN (8 + 2 * b) (lw ++ tw ^ (16 + 2 * a) ++ third_u0)
    (third_output (7 + 2 * a)) [] h_sup
  unfold third_source third_col
  refine SegRLs.congr h rfl rfl ?_ ?_
  · rw [show 9 + 2 * b = 1 + (8 + 2 * b) by omega]
    simp only [List.append_assoc]
  · rw [show 11 + 2 * b = (8 + 2 * b) + 3 by omega]

lemma third_m (a b : ℕ) :
    SegRLs tm (hf ^ (2 * (2 + 8 * q16 (5 + a)) * 4 ^ (10 + 2 * b))) []
      (third_col a b) (third_mid a b) := by
  have h := F_T_service (10 + 2 * b) (2 + 8 * q16 (2 + (3 + a)))
    (service_tail (cw ^ 2 ++ third_u2) (M_block (3 + a)))
  unfold third_col third_output third_mid
  refine SegRLs.congr h ?_ rfl ?_ ?_
  · rw [show 2 + (3 + a) = 5 + a by omega]
  · rw [show 11 + 2 * b = 1 + (10 + 2 * b) by omega,
      show 7 + 2 * a = 1 + 2 * (3 + a) by omega]
    simp only [List.append_assoc]
  · rw [show 21 + 2 * a + 2 * b = (1 + (10 + 2 * b)) + (4 + 2 * (3 + a)) by omega,
      pow_add_list tw (1 + (10 + 2 * b)) (4 + 2 * (3 + a))]
    simp only [List.append_assoc]

lemma third_finish (a b : ℕ) :
    SegRLs tm (hf ^ (2 * 2892 * 4 ^ (20 + 2 * a + 2 * b) + q4 (21 + 2 * a + 2 * b))) []
      (third_mid a b) (third_end a b) := by
  have h1 := F_T_service (20 + 2 * a + 2 * b) 2892 (service_tail third_u2 (PACKET 0))
  have h2 := service_tail (jw ^ 6 ++ mw ++ rw ++ third_u2) (F_normalize (20 + 2 * a + 2 * b))
  have h12 := SegRLs.trans_eq h1 h2 (by simp only [pow_zero_list, List.append_nil, List.append_assoc])
  unfold third_mid third_end
  refine SegRLs.congr h12 ?_ rfl ?_ ?_
  · exact pow_add2_eq hf (by rw [show 1 + (20 + 2 * a + 2 * b) = 21 + 2 * a + 2 * b by omega])
  · rw [show 21 + 2 * a + 2 * b = 1 + (20 + 2 * a + 2 * b) by omega]
    simp only [List.append_assoc]
  · rw [show 26 + 2 * a + 2 * b = (20 + 2 * a + 2 * b) + 6 by omega,
      pow_add_list jw (20 + 2 * a + 2 * b) 6]
    simp only [List.append_assoc]

lemma third_services (a b : ℕ) (H : third_f (7 + 2 * a) = 8 + 2 * b) :
    SegRLs tm (hf ^ (9 + 2 * e a b)) [] (third_source a b) (third_end a b) := by
  have h := (third_column a b H).trans ((third_m a b).trans (third_finish a b))
  refine SegRLs.congr h ?_ rfl rfl rfl
  exact pow_add3_eq hf (by clear H h; have := tower_budget a b; omega)

lemma third_recut (k : ℕ) :
    aw ++ tw ^ (1 + k) ++ [I, O, I] ++ bw ++ rw ++ lw ++ bw =
      lw ++ tw ^ k ++ zw ++ kw ++ tw ++ [O, O] ++ [I, O, I] := by
  rw [Nat.add_comm 1 k, pow_succ_list]
  have hbw := bw_comm_T k
  have haw : aw ++ tw ++ tw ^ k = lw ++ (bw ++ tw ^ k) := rfl
  rw [← List.append_assoc aw tw (tw ^ k), haw, hbw]
  simp only [List.append_assoc]
  rfl

def third_after_zero (a b : ℕ) : List Γ :=
  tw ++ lw ^ (9 + 2 * e a b) ++ kw ++ tw ++ aw ++
    tw ^ (25 + 2 * a + 2 * b) ++ [I, O, I] ++ bw ++ rw ++ third_u2

lemma third_recut_family (a b : ℕ) :
    third_after_zero a b = family_word a b ++ [I, O, I] := by
  unfold third_after_zero third_u2 family_word
  have h := third_recut (24 + 2 * a + 2 * b)
  rw [show 25 + 2 * a + 2 * b = 1 + (24 + 2 * a + 2 * b) by omega]
  simp only [List.append_assoc] at h ⊢
  rw [h]

lemma third_reset (a b : ℕ) (u : ListBlank Γ) :
    (P (9 + 2 * e a b) (third_end a b +> u)) [tm]⊢⁺
      (Inv a b ([I, O, I] +> u)) := by
  have h := zero_return (9 + 2 * e a b) (25 + 2 * a + 2 * b)
    ((bw ++ rw ++ third_u2) +> u)
  refine stepPlus_congr h ?_ ?_
  · unfold third_end
    rw [show 26 + 2 * a + 2 * b = 1 + (25 + 2 * a + 2 * b) by omega]
    simp only [append_assoc]
    rfl
  · unfold Inv
    rw [← append_assoc (family_word a b), ← third_recut_family a b]
    unfold third_after_zero
    simp only [append_assoc]

lemma third_run (a b : ℕ) (u : ListBlank Γ) (H : third_f (7 + 2 * a) = 8 + 2 * b) :
    (P 0 (third_source a b +> u)) [tm]⊢⁺ (Inv a b ([I, O, I] +> u)) :=
  stepStar_stepPlus_trans
    (P_service_zero (9 + 2 * e a b) (third_source a b) (third_end a b) u
      (third_services a b H))
    (third_reset a b u)

lemma third_index_algebra (q0 q2 q9 x : ℕ)
    (H0 : 1 + 3 * q0 = x) (H2 : 1 + 3 * q2 = 16 * x)
    (H9 : 1 + 3 * q9 = (4 * 256 * 256) * x) :
    8 * q9 + (1 + (4 * ((16 * 256 * 256) * x) +
      (29 + 96 * q0 + 2 * (4 * (4 * 1911 + 3) + 1) * (16 * x)))) =
      8 + 2 * (501 + 183 * 1000 + (522 + 550 * 1000) * q2) := by
  omega

lemma third_index (n : ℕ) :
    third_f n = 8 + 2 * (501 + 183 * 1000 + (522 + 550 * 1000) * q4 (n + 2)) := by
  have P2 : 4 ^ (n + 2) = 16 * 4 ^ n := by rw [Nat.pow_add]; ring
  have P2' : 4 ^ (2 + n) = 16 * 4 ^ n := by rw [Nat.add_comm 2 n, Nat.pow_add]; ring
  have P9 : 4 ^ (n + 9) = (4 * 256 * 256) * 4 ^ n := by rw [Nat.pow_add]; ring
  have P10 : 4 ^ (n + 10) = (16 * 256 * 256) * 4 ^ n := by rw [Nat.pow_add]; ring
  have H0 := q4_pow n
  have H2 := q4_pow (n + 2); rw [P2] at H2
  have H9 := q4_pow (n + 9); rw [P9] at H9
  unfold third_f entry8_calls
  rw [P10, P2']
  exact third_index_algebra _ _ _ _ H0 H2 H9

def entry_v : List Γ := [O, O, I, O, O, O, I, O, I, I, O, O, I, I, O, I]

lemma entry_recut (k : ℕ) :
    aw ++ tw ^ (1 + k) ++ [I, O, I] ++ entry_b =
      lw ++ tw ^ k ++ third_u0 ++ entry_v := by
  rw [Nat.add_comm 1 k, pow_succ_list]
  have hbw := bw_comm_T k
  have haw : aw ++ tw ++ tw ^ k = lw ++ (bw ++ tw ^ k) := rfl
  rw [← List.append_assoc aw tw (tw ^ k), haw, hbw]
  simp only [List.append_assoc]
  rfl

lemma entry_third_guard_gen (m a0 : ℕ) (hm : m = 9 + 2 * a0) :
    third_f (7 + 2 * a0) = 8 + 2 * entry_b0_of m := by
  subst hm
  unfold entry_b0_of
  rw [third_index, show 7 + 2 * a0 + 2 = 9 + 2 * a0 by omega]

lemma entry_third_guard : third_f (7 + 2 * entry_a0) = 8 + 2 * entry_b0 :=
  entry_third_guard_gen entry_m entry_a0 entry_m_odd

lemma entry_third_gen (m B a0 b0 : ℕ)
    (hm : m = 9 + 2 * a0)
    (hB : B = 9 + 2 * b0)
    (h_zero : (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ B +> (kw +> (tw +> (aw +> (tw ^ (m + 8) +>
        ([I, O, I] +> (entry_b +> default)))))))))) :
    (init []) [tm]⊢* (P 0 (third_source a0 b0 +> (entry_v +> default))) := by
  refine stepStar_congr h_zero rfl ?_
  have hrec := entry_recut (m + 7)
  rw [show 1 + (m + 7) = m + 8 by omega] at hrec
  have hrec' : (aw +> (tw ^ (m + 8) +> ([I, O, I] +> (entry_b +> (default : ListBlank Γ))))) =
      (lw +> (tw ^ (m + 7) +> (third_u0 +> (entry_v +> default)))) := by
    simpa only [append_assoc] using congrArg (· +> (default : ListBlank Γ)) hrec
  unfold third_source
  rw [hB, show 16 + 2 * a0 = m + 7 by omega]
  simp only [append_assoc, hrec']

lemma entry_third :
    (init []) [tm]⊢* (P 0 (third_source entry_a0 entry_b0 +> (entry_v +> default))) :=
  entry_third_gen entry_m entry_B entry_a0 entry_b0 entry_m_odd entry_B_index entry_after_zero

lemma init_family :
    (init []) [tm]⊢* (Inv entry_a0 entry_b0 ([I, O, I] +> (entry_v +> default))) :=
  stepStar_trans entry_third
    (stepPlus_to_stepStar (third_run entry_a0 entry_b0 (entry_v +> default) entry_third_guard))

lemma init_family_target :
    (init []) [target_tm]⊢*
      flipCfg (Inv entry_a0 entry_b0 ([I, O, I] +> (entry_v +> default))) := by
  have h := stepStar_flipTM init_family
  rw [flipTM_flipTM] at h
  exact h

lemma I_step_target (a b : ℕ) (u : ListBlank Γ) :
    (flipCfg (Inv a b u)) [target_tm]⊢⁺
      (flipCfg (Inv b (e a b) (family_prefix a +> u))) := by
  have h := stepPlus_flipTM (I_step a b u)
  rw [flipTM_flipTM] at h
  exact h

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ a b u, c = flipCfg (Inv a b u))
    ⟨flipCfg (Inv entry_a0 entry_b0 ([I, O, I] +> (entry_v +> default))),
      init_family_target,
      entry_a0, entry_b0, [I, O, I] +> (entry_v +> default), rfl⟩ ?_
  rintro _ ⟨a, b, u, rfl⟩
  exact ⟨flipCfg (Inv b (e a b) (family_prefix a +> u)),
    I_step_target a b u,
    b, e a b, family_prefix a +> u, rfl⟩

end BusyBeaver.M_1RB1LE_1LC0RF_1LA0RD_1LC1RC_1LB0LB_HHH1RD
