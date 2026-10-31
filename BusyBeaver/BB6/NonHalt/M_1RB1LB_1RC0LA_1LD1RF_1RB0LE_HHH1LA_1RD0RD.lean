/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LB_1RC0LA_1LD1RF_1RB0LE_---1LA_1RD0RD` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LB_1RC0LA_1LD1RF_1RB0LE_---1LA_1RD0RD`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LB_1RC0LA_1LD1RF_1RB0LE_HHH1LA_1RD0RD

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LB_1RC0LA_1LD1RF_1RB0LE_---1LA_1RD0RD`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 3, Stmt.write 0 Dir.right)

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

/-- State relabeling isomorphism between `TM13` and `TM12` (`D↔0, C↔1, A↔2, B↔3, F↔4, E↔5`). -/
abbrev A : Fin 6 := 2
abbrev B : Fin 6 := 3
abbrev C : Fin 6 := 1
abbrev D : Fin 6 := 0
abbrev E : Fin 6 := 5
abbrev F : Fin 6 := 4

abbrev tm : Machine (Fin 2) (Fin 6) := target_tm

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


lemma init_raw12 :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ 12 +> (kw +> (tw +> (lw +> (zw +> ([I] +> default)))))))) := by
  have h := runSteps_spec tm 3686 ⟨List.replicate 67 O, List.replicate 10 O, D, .right⟩
    ⟨zw ++ tw ++ tw ++ lw ^ 12 ++ kw ++ tw ++ lw ++ zw ++ [I], [], D, .left⟩
    (by decide) default default
  have hl : List.replicate 67 O +> (default : ListBlank Γ) = default :=
    BoundedConfig.all0_spec (by decide)
  have hr : List.replicate 10 O +> (default : ListBlank Γ) = default :=
    BoundedConfig.all0_spec (by decide)
  refine stepStar_congr h ?_ ?_
  · simp only [BoundedConfig.toCfg, hl, hr]; rfl
  · simp only [BoundedConfig.toCfg, P, root, Nat.add_zero, pow_one_list, append_nil, append_assoc]

lemma one_return_15 (n : ℕ) :
    (P n (zw +> (jw ^ 16 +> ([I] +> default)))) [tm]⊢⁺
      (P (1 + n) (tw +> (lw +> (tw ^ 15 +> default)))) := by
  unfold P
  have h1 := P_enter n (zw +> (jw ^ 16 +> ([I] +> default)))
  have h2 : (toDHCfg (fR, .right) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default)))
      (zw +> (jw ^ 16 +> ([I] +> default)))) [tm]⊢*
      ((uw ^ (1 + n) +> ([I] +> default)) <{{D}}
        (bw +> (tw +> (tw +> (lw +> (tw ^ 15 +> default)))))) := by
    have h := runSteps_spec tm 149 ⟨[I] ++ [I, I, I, I, I], zw ++ jw ^ 16 ++ [I], C, .right⟩
      ⟨bw ++ tw ++ tw ++ lw ++ tw ^ 15 ++ [O], [], D, .left⟩
      (by decide) (uw ^ (1 + n) +> ([I] +> default)) default
    have hd : ([O] : List Γ) +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    simpa only [BoundedConfig.toCfg, toDHCfg, append_nil, append_assoc, hd] using h
  have h3 := shift_D_back (1 + n) ([I] +> default) (tw +> (tw +> (lw +> (tw ^ 15 +> default))))
  have h4 := bounce_D_left (zw ^ (1 + n) +> (tw +> (tw +> (lw +> (tw ^ 15 +> default)))))
  have h4' : (default <{{D}} (zw +> (zw ^ (1 + n) +> (tw +> (tw +> (lw +> (tw ^ 15 +> default))))))) =
      root D (1 + n) (tw +> (lw +> (tw ^ 15 +> default))) := by
    unfold root
    rw [show (1 + (1 + n) : ℕ) = (1 + n) + 1 by omega, pow_succ_list zw (1 + n), append_assoc zw (zw ^ (1 + n))]
  exact stepPlus_stepStar_trans h1
    (stepStar_trans h2 (stepStar_trans h3 (stepPlus_to_stepStar (stepPlus_congr h4 rfl h4'))))

lemma ten_return_15 (n : ℕ) :
    (P n (zw +> (lw +> (mw ^ 15 +> default)))) [tm]⊢⁺
      (P 0 (tw +> (lw ^ n +> (kw +> (tw ^ 17 +> ([I, O, I] +> default)))))) := by
  unfold P
  have h1 := P_enter n (zw +> (lw +> (mw ^ 15 +> default)))
  have h2 : (toDHCfg (fR, .right) ([I, I, I, I, I] +> (uw ^ (1 + n) +> ([I] +> default)))
      (zw +> (lw +> (mw ^ 15 +> default)))) [tm]⊢*
      ((uw ^ (1 + n) +> ([I] +> default)) <{{C}}
        ([I, O, I, O, I] +> ([O, I, O, I, O, I] +> (tw ^ 16 +> ([I, O, I] +> default))))) := by
    have h := runSteps_spec tm 153 ⟨[I] ++ [I, I, I, I, I], zw ++ lw ++ mw ^ 15 ++ [O, O, O, O], C, .right⟩
      ⟨[I, O, I, O, I] ++ [O, I, O, I, O, I] ++ tw ^ 16 ++ [I, O, I], [], C, .left⟩
      (by decide) (uw ^ (1 + n) +> ([I] +> default)) default
    have hd : ([O, O, O, O] : List Γ) +> (default : ListBlank Γ) = default :=
      BoundedConfig.all0_spec (by decide)
    simpa only [BoundedConfig.toCfg, toDHCfg, append_nil, append_assoc, hd] using h
  have h3 := shift_C_lw (1 + n) ([I] +> default) ([O, I, O, I, O, I] +> (tw ^ 16 +> ([I, O, I] +> default)))
  have h3_eq : (([I] +> default) <{{C}}
      ([I, O, I, O, I] +> (lw ^ (1 + n) +> ([O, I, O, I, O, I] +> (tw ^ 16 +> ([I, O, I] +> default)))))) =
      (([I] +> default) <{{C}}
        ([I, O, I, O, I, I, O] +> (zw ^ n +> ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))))) := by
    congr 1
    have h_lw : lw ^ (1 + n) +> ([O, I, O, I, O, I] +> (tw ^ 16 +> ([I, O, I] +> (default : ListBlank Γ)))) =
        aw +> (zw ^ n +> ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))) := by
      rw [show (1 + n : ℕ) = n + 1 by omega, pow_succ_list lw n, append_assoc lw (lw ^ n),
        show (lw +> (lw ^ n +> ([O, I, O, I, O, I] +> (tw ^ 16 +> ([I, O, I] +> (default : ListBlank Γ)))))) =
          aw +> (bw +> (lw ^ n +> ([O, I, O, I, O, I] +> (tw ^ 16 +> ([I, O, I] +> default))))) from rfl,
        OI_lw_pow]
      rfl
    rw [h_lw]
    rfl
  have h4 : (([I] +> default) <{{C}}
        ([I, O, I, O, I, I, O] +> (zw ^ n +> ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))))) [tm]⊢*
      (([I, O, I, I, I, I, I, I, I, I, I] +> default) {{C}}>
        (zw ^ n +> ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default)))))) := by
    have h := runSteps_spec tm 32 ⟨[I, O, I, O, I, I, O], [I, O, O, O], C, .left⟩
      ⟨[I, O, I, I, I, I, I, I, I, I, I], [], C, .right⟩ (by decide)
      default (zw ^ n +> ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default)))))
    have hd : ([I, O, O, O] : List Γ) +> (default : ListBlank Γ) = [I] +> default := by
      rw [show ([I, O, O, O] : List Γ) = [I] ++ [O, O, O] from rfl, append_assoc,
        BoundedConfig.all0_spec (a := [O, O, O]) (by decide)]
    simpa only [BoundedConfig.toCfg, append_nil, hd] using h
  have h5 := shift_C_zw n ([I, O, I, I, I, I, I, I, I, I, I] +> default)
    ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))
  have h6 : ((uw ^ n +> ([I, O, I, I, I, I, I, I, I, I, I] +> default)) {{C}}>
        ([O, I, O, I, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))) [tm]⊢*
      ((uw ^ n +> ([I, O, I, I, I, I, I, I, I, I, I] +> default)) <{{D}}
        (bw +> ([I, O, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default)))))) := by
    have h := runSteps_spec tm 7 ⟨[], [O, I, O, I, O, I], C, .right⟩
      ⟨bw ++ [I, O, O, I], [], D, .left⟩ (by decide)
      (uw ^ n +> ([I, O, I, I, I, I, I, I, I, I, I] +> default))
      (bw +> (tw ^ 16 +> ([I, O, I] +> default)))
    simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h
  have h7 := shift_D_back n ([I, O, I, I, I, I, I, I, I, I, I] +> default)
    ([I, O, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))
  have h8 : (([I, O, I, I, I, I, I, I, I, I, I] +> default) <{{D}}
        (bw +> (zw ^ n +> ([I, O, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default))))))) [tm]⊢*
      (root D 0 (tw +> (lw ^ n +> (kw +> (tw ^ 17 +> ([I, O, I] +> default)))))) := by
    have h := runSteps_spec tm 24 ⟨bw, [I, O, I, I, I, I, I, I, I, I, I, O], D, .left⟩
      ⟨zw ++ tw ++ tw ++ aw, [], D, .left⟩ (by decide)
      default (zw ^ n +> ([I, O, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> default)))))
    have hd : ([I, O, I, I, I, I, I, I, I, I, I, O] : List Γ) +> (default : ListBlank Γ) =
        [I, O, I, I, I, I, I, I, I, I, I] +> default := by
      rw [show ([I, O, I, I, I, I, I, I, I, I, I, O] : List Γ) =
          [I, O, I, I, I, I, I, I, I, I, I] ++ [O] from rfl,
        append_assoc, BoundedConfig.all0_spec (a := [O]) (by decide)]
    have hr : ((zw ++ tw ++ tw ++ aw) +>
        (zw ^ n +> ([I, O, O, I] +> (bw +> (tw ^ 16 +> ([I, O, I] +> (default : ListBlank Γ))))))) =
        (zw ^ (1 + 0) +> (tw +> (tw +> (lw ^ n +> (kw +> (tw ^ 17 +> ([I, O, I] +> default))))))) := by
      rw [Nat.add_zero, pow_one_list, append_assoc, append_assoc, append_assoc, IO_zw_pow,
        ← append_assoc aw [I, O, O, I],
        ← append_assoc (aw ++ [I, O, O, I]) bw,
        show (aw ++ [I, O, O, I] ++ bw : List Γ) = kw ++ tw from rfl,
        append_assoc kw tw,
        show (tw +> (tw ^ 16 +> ([I, O, I] +> (default : ListBlank Γ)))) =
          (tw ^ 17 +> ([I, O, I] +> default)) from rfl]
    simpa only [BoundedConfig.toCfg, root, append_nil, hd, hr] using h
  exact stepPlus_stepStar_trans h1
    (stepStar_trans h2 (stepStar_trans (stepStar_congr h3 rfl h3_eq)
      (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 (stepStar_trans h7 h8))))))

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


-- ============================================================================
-- 4. TM12 Entrance & Tower-Scale Specialization (`SOBCv13.v:1220-1832`)
-- ============================================================================

lemma init_F11 : SegRLs tm (hf ^ 11) [] (zw ++ lw ++ zw) (tw ++ kw ++ jw) :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

@[irreducible] def init_h : ℕ := 2 + 16 * q4 11 + 2 * 4 ^ 14 + q4 15

lemma init_services :
    SegRLs tm (hf ^ init_h) [] (tw ++ lw ^ 12 ++ kw ++ tw ++ lw ++ zw) (zw ++ jw ^ 16) := by
  have h1 := COLUMN 11 (lw ++ zw) (tw ++ kw ++ jw) []
    (SegRLs.congr init_F11 rfl rfl (by simp only [List.append_assoc]) rfl)
  have h1' : SegRLs tm (hf ^ (2 + 16 * q4 11)) []
      (tw ++ lw ^ 12 ++ kw ++ tw ++ lw ++ zw) (tw ^ 15 ++ kw ++ jw) := by
    refine SegRLs.congr h1 rfl rfl ?_ ?_
    · change tw ++ lw ^ 12 ++ kw ++ tw ++ (lw ++ zw) ++ [] =
        tw ++ lw ^ 12 ++ kw ++ tw ++ lw ++ zw
      simp only [List.append_nil, List.append_assoc]
    · rfl
  have h2 := F_T_service 14 1 (G_K.concat (.nil jw))
  have h2' : SegRLs tm (hf ^ (2 * 4 ^ 14)) [] (tw ^ 15 ++ kw ++ jw) (tw ^ 15 ++ jw ^ 2) := by
    refine SegRLs.congr h2 (by rfl) rfl ?_ ?_
    · change tw ^ 15 ++ (kw ++ jw) = tw ^ 15 ++ kw ++ jw
      simp only [List.append_assoc]
    · change tw ^ 15 ++ (jw ++ jw) = tw ^ 15 ++ jw ^ 2
      rfl
  have h3 := (F_normalize 14).concat (.nil (jw ^ 2))
  have h3' : SegRLs tm (hf ^ (q4 15)) [] (tw ^ 15 ++ jw ^ 2) (zw ++ jw ^ 16) := by
    refine SegRLs.congr h3 (by rfl) rfl (by rfl) ?_
    rw [List.append_assoc, ← pow_add_list]
  have h123 := h1'.trans (h2'.trans h3')
  refine SegRLs.congr h123 ?_ rfl rfl rfl
  exact pow_add3_eq hf (by unfold init_h; omega)

@[irreducible] def m0 : ℕ := init_h + 2 + 8 * q4 15

lemma m0_eq_init_h : 1 + init_h + 1 + 8 * q4 15 = m0 := by
  unfold m0
  omega

lemma init_anchor_gen (h m : ℕ) (hm : 1 + h + 1 + 8 * q4 15 = m)
    (h_serv : SegRLs tm (hf ^ h) [] (tw ++ lw ^ 12 ++ kw ++ tw ++ lw ++ zw) (zw ++ jw ^ 16)) :
    (init []) [tm]⊢* (P 0 (tw +> (lw ^ m +> (kw +> (tw ^ 17 +> ([I, O, I] +> default)))))) := by
  have s1 : (init []) [tm]⊢* (P h (zw +> (jw ^ 16 +> ([I] +> default)))) := by
    refine stepStar_trans init_raw12 ?_
    have hs := P_service_zero h (tw ++ lw ^ 12 ++ kw ++ tw ++ lw ++ zw) (zw ++ jw ^ 16)
      ([I] +> default) h_serv
    refine stepStar_congr hs ?_ ?_
    · simp only [append_assoc]
    · simp only [append_assoc]
  have s2 : (P h (zw +> (jw ^ 16 +> ([I] +> default)))) [tm]⊢*
      (P (1 + h) (tw +> (lw +> (tw ^ 15 +> default)))) :=
    stepPlus_to_stepStar (one_return_15 h)
  have s3 : (P (1 + h) (tw +> (lw +> (tw ^ 15 +> default)))) [tm]⊢*
      (P (1 + h + 1) (zw +> (lw +> (tw ^ 15 +> default)))) :=
    P_service (1 + h) 1 tw zw (lw +> (tw ^ 15 +> default)) F_T
  have s4 : (P (1 + h + 1) (zw +> (lw +> (tw ^ 15 +> default)))) [tm]⊢*
      (P m (zw +> (lw +> (mw ^ 15 +> default)))) := by
    have hb := P_service (1 + h + 1) (8 * q4 15) (zw ++ lw ++ tw ^ 15) (zw ++ lw ++ mw ^ 15)
      default (BIN 15)
    refine stepStar_congr hb ?_ ?_
    · simp only [append_assoc]
    · rw [hm]; simp only [append_assoc]
  have s5 : (P m (zw +> (lw +> (mw ^ 15 +> default)))) [tm]⊢*
      (P 0 (tw +> (lw ^ m +> (kw +> (tw ^ 17 +> ([I, O, I] +> default)))))) :=
    stepPlus_to_stepStar (ten_return_15 m)
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 s5)))

lemma init_anchor :
    (init []) [tm]⊢* (P 0 (tw +> (lw ^ m0 +> (kw +> (tw ^ 17 +> ([I, O, I] +> default)))))) :=
  init_anchor_gen init_h m0 m0_eq_init_h init_services

lemma G_digits (j k n : ℕ) (u v w : List Γ)
    (H : SegRLs tm (hg ^ n) [] u v) (K : SegRLs tm (hg ^ k) [] tw w) :
    SegRLs tm (hg ^ (n * 4 ^ j + k * q4 j)) [] (tw ^ j ++ u) (w ^ j ++ v) := by
  induction j with
  | zero =>
    have h0 : n * 4 ^ 0 + k * q4 0 = n := by dsimp [q4]; omega
    exact SegRLs.congr H (by rw [h0]) rfl rfl rfl
  | succ j ih =>
    have h := G_append (n * 4 ^ j + k * q4 j) k (tw ^ j ++ u) (w ^ j ++ v) (w ++ (w ^ j ++ v))
      ih (service_tail (w ^ j ++ v) K)
    refine SegRLs.congr h ?_ rfl ?_ ?_
    · refine congrArg (hg ^ ·) ?_
      dsimp [q4]
      rw [Nat.pow_succ]
      ring
    · rw [pow_succ_list tw j, List.append_assoc]
    · rw [pow_succ_list w j, List.append_assoc]

lemma short1_start (r : ℕ) :
    SegRLs tm (hg ^ 2) [] (zw ++ tw ++ jw ^ r ++ tw ^ 2 ++ lw) (tw ^ (r + 2) ++ zw ++ tw ++ lw) := by
  have h1 := G_Z.concat (service_tail (jw ^ r ++ tw ^ 2 ++ lw) G_T)
  have h2 := G_L.concat (H_K.concat ((F_Js r).concat (service_tail (tw ++ lw) F_T)))
  have h12 := SegRLs.trans_eq h1 h2 (by rw [show (tw ^ 2 : List Γ) = tw ++ tw from rfl]; simp only [List.append_assoc])
  refine SegRLs.congr h12 (by rfl) rfl (by simp only [List.append_assoc]) ?_
  rw [show r + 2 = 2 + r by omega, pow_add_list tw 2 r]
  change tw ++ (tw ++ (tw ^ r ++ (zw ++ (tw ++ lw)))) =
    (tw ++ (tw ++ [])) ++ tw ^ r ++ zw ++ tw ++ lw
  simp only [List.append_nil, List.append_assoc]

def short1_count (r : ℕ) : ℕ := 2 + 8 * 4 ^ (1 + r) + 2 * q4 (r + 4)

lemma short1 (r : ℕ) :
    SegRLs tm (hg ^ (short1_count r)) []
      (zw ++ tw ++ jw ^ r ++ tw ^ 2 ++ lw) (jw ^ (r + 4) ++ mw) := by
  have h1 := short1_start r
  have h2_mid : SegRLs tm (hg ^ (8 * 4 ^ (1 + r))) []
      (tw ^ (1 + r) ++ ((tw ++ zw ++ tw) ++ lw))
      (tw ^ (1 + r) ++ (tw ^ 3 ++ mw)) :=
    (G_Ts (1 + r) 8).concat (ODD_END.concat F_L)
  have h2 : SegRLs tm (hg ^ (8 * 4 ^ (1 + r))) []
      (tw ^ (r + 2) ++ zw ++ tw ++ lw) (tw ^ (r + 4) ++ mw) := by
    refine SegRLs.congr h2_mid rfl rfl ?_ ?_
    · rw [show r + 2 = (1 + r) + 1 by omega, pow_add_list tw (1 + r) 1, pow_one_list]
      simp only [List.append_assoc]
    · rw [show r + 4 = (1 + r) + 3 by omega, pow_add_list tw (1 + r) 3]
      simp only [List.append_assoc]
  have h3 := service_tail mw (G_normalize (r + 4))
  have h123 := h1.trans (h2.trans h3)
  refine SegRLs.congr h123 ?_ rfl rfl rfl
  exact pow_add3_eq hg (by unfold short1_count; omega)

def reset_count (p j : ℕ) : ℕ := 2 + 16 * q4 p + 2 * j * 4 ^ (2 + p) + q4 (3 + p)

lemma reset_services (p j k : ℕ) (w v u : List Γ)
    (H : SegRLs tm (hf ^ p) [] (zw ++ w) v)
    (K : SegRLs tm (hg ^ j) [] v (jw ^ (1 + k) ++ [O, O] ++ u)) :
    SegRLs tm (hf ^ (reset_count p j)) []
      (tw ++ lw ^ (1 + p) ++ kw ++ tw ++ w) (zw ++ jw ^ (3 + p + k) ++ [O, O] ++ u) := by
  have h1 : SegRLs tm (hf ^ (2 + 16 * q4 p)) []
      (tw ++ lw ^ (1 + p) ++ kw ++ tw ++ w) (tw ^ (3 + p) ++ v) := by
    have hc := COLUMN p w v [] H
    refine SegRLs.congr hc rfl rfl ?_ ?_
    · simp only [List.append_nil, List.append_assoc]
    · rw [show p + 3 = 3 + p by omega]
  have h2 : SegRLs tm (hf ^ (2 * j * 4 ^ (2 + p))) []
      (tw ^ (3 + p) ++ v) (tw ^ (3 + p) ++ jw ^ (1 + k) ++ [O, O] ++ u) := by
    have hf_t := F_T_service (2 + p) j K
    refine SegRLs.congr hf_t rfl rfl ?_ ?_
    · rw [show 1 + (2 + p) = 3 + p by omega]
    · rw [show 1 + (2 + p) = 3 + p by omega]
      simp only [List.append_assoc]
  have h3 : SegRLs tm (hf ^ (q4 (3 + p))) []
      (tw ^ (3 + p) ++ jw ^ (1 + k) ++ [O, O] ++ u)
      (zw ++ jw ^ (3 + p + k) ++ [O, O] ++ u) := by
    have hfn := service_tail (jw ^ (1 + k) ++ [O, O] ++ u) (F_normalize (2 + p))
    refine SegRLs.congr hfn ?_ rfl ?_ ?_
    · rw [show 1 + (2 + p) = 3 + p by omega]
    · rw [show 1 + (2 + p) = 3 + p by omega]
      simp only [List.append_assoc]
    · rw [show 3 + p + k = (2 + p) + (1 + k) by omega, pow_add_list jw (2 + p) (1 + k)]
      simp only [List.append_assoc]
  have h123 := h1.trans (h2.trans h3)
  refine SegRLs.congr h123 ?_ rfl rfl rfl
  exact pow_add3_eq hf (by unfold reset_count; omega)

lemma reset_run (p j k : ℕ) (w v u : List Γ) (r : ListBlank Γ)
    (H : SegRLs tm (hf ^ p) [] (zw ++ w) v)
    (K : SegRLs tm (hg ^ j) [] v (jw ^ (1 + k) ++ [O, O] ++ u)) :
    (P 0 ((tw ++ lw ^ (1 + p) ++ kw ++ tw ++ w) +> r)) [tm]⊢⁺
      (P 0 (tw +> (lw ^ (reset_count p j) +> (kw +> (tw +> (aw +>
        (tw ^ (2 + p + k) +> ([I, O, I] +> (u +> r))))))))) := by
  have h1 := P_service_zero (reset_count p j)
    (tw ++ lw ^ (1 + p) ++ kw ++ tw ++ w) (zw ++ jw ^ (3 + p + k) ++ [O, O] ++ u) r
    (reset_services p j k w v u H K)
  have h2 := zero_return (reset_count p j) (2 + p + k) (u +> r)
  have h2' : (P (reset_count p j) ((zw ++ jw ^ (3 + p + k) ++ [O, O] ++ u) +> r)) [tm]⊢⁺
      (P 0 (tw +> (lw ^ (reset_count p j) +> (kw +> (tw +> (aw +>
        (tw ^ (2 + p + k) +> ([I, O, I] +> (u +> r))))))))) := by
    refine stepPlus_congr h2 ?_ rfl
    rw [show 1 + (2 + p + k) = 3 + p + k by omega]
    simp only [append_assoc]
  exact stepStar_stepPlus_trans h1 h2'

@[irreducible] def p0 : ℕ := (7 * 4 ^ 13 + 2 * q4 11) * 4

lemma first_g :
    SegRLs tm (hg ^ p0) [] (tw ^ 16) (tw ++ jw ^ 11 ++ tw ^ 2 ++ cw) := by
  have H : SegRLs tm (hg ^ (7 * 4 ^ 2)) [] (tw ^ 4) (tw ^ 2 ++ cw) :=
    (G_Ts 2 7).concat G7
  have K : SegRLs tm (hg ^ (7 * 4 ^ 13 + 2 * q4 11)) [] (tw ^ 15) (jw ^ 11 ++ tw ^ 2 ++ cw) := by
    have hd := G_digits 11 2 (7 * 4 ^ 2) (tw ^ 4) (tw ^ 2 ++ cw) jw H G2_T
    refine SegRLs.congr hd ?_ rfl (by rfl) (by simp only [List.append_assoc])
    refine congrArg (hg ^ ·) ?_
    decide
  have h_app := G_append (7 * 4 ^ 13 + 2 * q4 11) 0 (tw ^ 15) (jw ^ 11 ++ tw ^ 2 ++ cw)
    (tw ++ (jw ^ 11 ++ tw ^ 2 ++ cw)) K (.nil (tw ++ (jw ^ 11 ++ tw ^ 2 ++ cw)))
  refine SegRLs.congr h_app ?_ rfl (by rfl) (by simp only [List.append_assoc])
  unfold p0
  refine congrArg (hg ^ ·) ?_
  omega

lemma m0_first : m0 = 1 + 2 * p0 := by
  unfold m0 init_h p0
  decide

@[irreducible] def a0 : ℕ := p0 - 4

lemma m0_odd : m0 = 9 + 2 * a0 := by
  unfold m0 a0 p0 init_h
  decide

lemma first_supply_gen (p : ℕ) (hg_p : SegRLs tm (hg ^ p) [] (tw ^ 16) (tw ++ jw ^ 11 ++ tw ^ 2 ++ cw)) :
    SegRLs tm (hf ^ (2 * p)) [] (zw ++ tw ^ 16) (zw ++ tw ++ jw ^ 11 ++ tw ^ 2 ++ cw) := by
  have H : SegRLs tm (hf ^ 2) hg zw zw :=
    SegRLs.congr (F_Z.trans F_T) (by rfl) (by rfl) rfl rfl
  have h_rep := (service_repeat p H).concat hg_p
  refine SegRLs.congr h_rep ?_ rfl rfl (by simp only [List.append_assoc])
  rw [← pow_mul_list]

lemma first_supply :
    SegRLs tm (hf ^ (2 * p0)) [] (zw ++ tw ^ 16) (zw ++ tw ++ jw ^ 11 ++ tw ^ 2 ++ cw) :=
  first_supply_gen p0 first_g

def reset_index (p j : ℕ) : ℕ := 7 + 40 * q4 p + 16 * j * 4 ^ p

lemma reset_index_spec (p j : ℕ) : reset_count p j = 9 + 2 * reset_index p j := by
  unfold reset_count reset_index
  have hq3 := q4_add 3 p
  have hp2 : 4 ^ (2 + p) = 16 * 4 ^ p := by rw [Nat.pow_add]
  have hq3_val : q4 3 = 21 := rfl
  have hp3_val : 4 ^ 3 = 64 := rfl
  rw [hq3_val, hp3_val] at hq3
  rw [hq3, hp2]
  ring

local notation "b0" => reset_index (2 * p0) (short1_count 11)
def u1 : List Γ := zw ++ kw ++ tw ++ bw

lemma recut1 (k : ℕ) :
    aw ++ tw ^ (1 + k) ++ [I, O, I] ++ bw ++ rw ++ [I, O, I] = lw ++ tw ^ k ++ u1 := by
  unfold u1
  rw [Nat.add_comm 1 k, pow_succ_list]
  have hbw := bw_comm_T k
  have haw : aw ++ tw ++ tw ^ k = lw ++ (bw ++ tw ^ k) := rfl
  rw [← List.append_assoc aw tw (tw ^ k), haw, hbw]
  simp only [List.append_assoc]
  rfl

lemma first_reset_gen (m p a : ℕ) (hm : m = 1 + 2 * p) (ha : m = 9 + 2 * a)
    (h_anch : (init []) [tm]⊢* (P 0 (tw +> (lw ^ m +> (kw +> (tw ^ 17 +> ([I, O, I] +> default)))))))
    (h_sup : SegRLs tm (hf ^ (2 * p)) [] (zw ++ tw ^ 16) (zw ++ tw ++ jw ^ 11 ++ tw ^ 2 ++ cw)) :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ (9 + 2 * reset_index (2 * p) (short1_count 11)) +>
        (kw +> (tw +> (lw +> (tw ^ (23 + 2 * a) +> (u1 +> default)))))))) := by
  have H : SegRLs tm (hf ^ (2 * p)) []
      (zw ++ (tw ^ 16 ++ [I, O, I]))
      ((zw ++ tw ++ jw ^ 11 ++ tw ^ 2 ++ lw) ++ rw ++ [I, O, I]) := by
    refine SegRLs.congr (service_tail [I, O, I] h_sup) rfl rfl ?_ ?_
    · simp only [List.append_assoc]
    · simp only [List.append_assoc]
  have K : SegRLs tm (hg ^ (short1_count 11)) []
      ((zw ++ tw ++ jw ^ 11 ++ tw ^ 2 ++ lw) ++ rw ++ [I, O, I])
      (jw ^ 15 ++ [O, O] ++ (bw ++ rw ++ [I, O, I])) := by
    refine SegRLs.congr (service_tail (rw ++ [I, O, I]) (short1 11)) rfl rfl ?_ ?_
    · simp only [List.append_assoc]
    · simp only [List.append_assoc]; rfl
  have R := reset_run (2 * p) (short1_count 11) 14
    (tw ^ 16 ++ [I, O, I])
    ((zw ++ tw ++ jw ^ 11 ++ tw ^ 2 ++ lw) ++ rw ++ [I, O, I])
    (bw ++ rw ++ [I, O, I]) default H K
  refine stepStar_trans h_anch ?_
  refine stepPlus_to_stepStar (stepPlus_congr R ?_ ?_)
  · have h17 : (tw ^ 17 : List Γ) = tw ++ tw ^ 16 := rfl
    rw [hm, h17]
    simp only [append_assoc]
  · have h_rec := recut1 (23 + 2 * a)
    have h_rec' : (aw +> (tw ^ (1 + (23 + 2 * a)) +> ([I, O, I] +> ((bw ++ rw ++ [I, O, I]) +> (default : ListBlank Γ))))) =
        (lw +> (tw ^ (23 + 2 * a) +> (u1 +> default))) := by
      simpa only [append_assoc] using congrArg (· +> (default : ListBlank Γ)) h_rec
    rw [reset_index_spec, show 2 + 2 * p + 14 = 1 + (23 + 2 * a) by omega]
    simp only [append_assoc] at h_rec' ⊢
    rw [h_rec']

lemma first_reset :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ (9 + 2 * b0) +>
        (kw +> (tw +> (lw +> (tw ^ (23 + 2 * a0) +> (u1 +> default)))))))) :=
  first_reset_gen m0 p0 a0 m0_first m0_odd init_anchor first_supply

def ww : List Γ := rw ++ tw ++ bw
def v1 : List Γ := kw ++ kw ++ tw ++ bw
def w1 : List Γ := cw ++ tw ++ bw
def tail1 : List Γ := kw ^ 11 ++ lw ++ mw ++ ww
@[irreducible] def j1 : ℕ := 4 * (4 * (3 * 4 ^ 12 + q4 12) + 3) + 1

lemma second_g : SegRLs tm (hg ^ j1) [] (tw ^ 15 ++ w1) (kw ++ cw ++ tail1) := by
  have H : SegRLs tm (hg ^ 3) [] (tw ++ w1) (lw ++ mw ++ ww) := by
    have h := G3_T.concat (service_tail (rw ++ tw ++ bw) F_L)
    exact SegRLs.congr h rfl rfl (by unfold w1; simp only [List.append_assoc])
      (by unfold ww; simp only [List.append_assoc])
  have K : SegRLs tm (hg ^ (3 * 4 ^ 12 + 1 * q4 12)) [] (tw ^ 12 ++ (tw ++ w1))
      (kw ^ 12 ++ (lw ++ mw ++ ww)) :=
    G_digits 12 1 3 (tw ++ w1) (lw ++ mw ++ ww) kw H G_T
  have K' : SegRLs tm (hg ^ (3 * 4 ^ 12 + q4 12)) [] (tw ^ 13 ++ w1)
      (kw ^ 12 ++ lw ++ mw ++ ww) := by
    refine SegRLs.congr K (by rw [Nat.one_mul]) rfl ?_ (by simp only [List.append_assoc])
    have h13 : (tw ^ 13 : List Γ) = tw ^ 12 ++ tw := rfl
    rw [h13, List.append_assoc]
  have L_step : SegRLs tm (hg ^ 3) [] (tw ++ (kw ^ 12 ++ lw ++ mw ++ ww)) (cw ++ tail1) := by
    have h := G3_T.concat (service_tail (kw ^ 11 ++ lw ++ mw ++ ww) F_K)
    refine SegRLs.congr h rfl rfl ?_ (by unfold tail1; simp only [List.append_assoc])
    have h12 : (kw ^ 12 : List Γ) = kw ++ kw ^ 11 := rfl
    rw [h12]
    simp only [List.append_assoc]
  have L : SegRLs tm (hg ^ (4 * (3 * 4 ^ 12 + q4 12) + 3)) [] (tw ^ 14 ++ w1) (cw ++ tail1) := by
    have h := G_append (3 * 4 ^ 12 + q4 12) 3 (tw ^ 13 ++ w1) (kw ^ 12 ++ lw ++ mw ++ ww)
      (cw ++ tail1) K' L_step
    refine SegRLs.congr h rfl rfl ?_ rfl
    have h14 : (tw ^ 14 : List Γ) = tw ++ tw ^ 13 := rfl
    rw [h14, List.append_assoc]
  have M := G_append (4 * (3 * 4 ^ 12 + q4 12) + 3) 1 (tw ^ 14 ++ w1) (cw ++ tail1)
    (kw ++ (cw ++ tail1)) L (service_tail (cw ++ tail1) G_T)
  refine SegRLs.congr M (by unfold j1; rfl) rfl ?_ (by simp only [List.append_assoc])
  have h15 : (tw ^ 15 : List Γ) = tw ++ tw ^ 14 := rfl
  rw [h15, List.append_assoc]

lemma second_supply (a : ℕ) :
    SegRLs tm (hf ^ (supply_count (7 + 2 * a) (23 + 2 * a) j1)) []
      (zw ++ lw ++ tw ^ (23 + 2 * a) ++ u1)
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * a) ++ rw ++ cw ++ tail1) := by
  have hH : SegRLs tm hh [] u1 v1 := service_tail (kw ++ tw ++ bw) H_Z
  have hK : SegRLs tm (hg ^ 2) [] v1 w1 :=
    SegRLs.congr (service_tail (tw ++ bw) G2_KK) rfl rfl (by unfold v1; simp only [List.append_assoc])
      (by unfold w1; simp only [List.append_assoc])
  have hL : SegRLs tm (hg ^ j1 ++ hf) [] (tw ^ 15 ++ w1) (rw ++ cw ++ tail1) := by
    have h := second_g.trans (service_tail (cw ++ tail1) F_K)
    exact SegRLs.congr h rfl rfl rfl (by simp only [List.append_assoc])
  have h := reset_supply (7 + 2 * a) (23 + 2 * a) 15 j1 u1 v1 w1 (rw ++ cw ++ tail1)
    (by omega) hH hK hL
  exact SegRLs.congr h rfl rfl rfl (by simp only [List.append_assoc])

lemma HGH_C : SegRLs tm (hh ++ hg ++ hh) [] (rw ++ cw) (zw ++ tw ++ jw) :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma short2 : SegRLs tm (hg ^ 44) [] (zw ++ tw ++ jw ++ kw) (jw ^ 3 ++ rw) :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

def clean2 (a : ℕ) : ℕ := 2 + 8 * q16 (5 + a) + 44 * 4 ^ (10 + 2 * a) + 2 * q4 (10 + 2 * a)
def v2 : List Γ := aw ++ kw ^ 10 ++ lw ++ mw ++ ww
def u2 : List Γ := zw ++ [I, I, O] ++ kw ^ 10 ++ lw ++ mw ++ ww

lemma second_clean (a : ℕ) :
    SegRLs tm (hg ^ (clean2 a)) []
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * a) ++ rw ++ cw ++ tail1)
      (jw ^ (13 + 2 * a) ++ [O, O] ++ v2) := by
  have h1_raw := (M_ODD (3 + a)).concat (service_tail tail1 HGH_C)
  have h1 : SegRLs tm (hg ^ (2 + 8 * q16 (5 + a))) []
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * a) ++ rw ++ cw ++ tail1)
      (tw ^ (10 + 2 * a) ++ zw ++ tw ++ jw ++ tail1) := by
    refine SegRLs.congr h1_raw ?_ rfl ?_ ?_
    · rw [show 2 + (3 + a) = 5 + a by omega]
    · rw [show 1 + 2 * (3 + a) = 7 + 2 * a by omega]
      simp only [List.append_assoc]
    · rw [show 4 + 2 * (3 + a) = 10 + 2 * a by omega]
      simp only [List.append_assoc]
  have h2_raw := (G_Ts (10 + 2 * a) 44).concat (service_tail (kw ^ 10 ++ lw ++ mw ++ ww) short2)
  have h2 : SegRLs tm (hg ^ (44 * 4 ^ (10 + 2 * a))) []
      (tw ^ (10 + 2 * a) ++ zw ++ tw ++ jw ++ tail1)
      (tw ^ (10 + 2 * a) ++ jw ^ 3 ++ [O, O] ++ v2) := by
    refine SegRLs.congr h2_raw rfl rfl ?_ ?_
    · unfold tail1
      have h11 : (kw ^ 11 : List Γ) = kw ++ kw ^ 10 := rfl
      rw [h11]
      simp only [List.append_assoc]
    · unfold v2
      simp only [List.append_assoc]
      rfl
  have h3_raw := service_tail (jw ^ 3 ++ [O, O] ++ v2) (G_normalize (10 + 2 * a))
  have h3 : SegRLs tm (hg ^ (2 * q4 (10 + 2 * a))) []
      (tw ^ (10 + 2 * a) ++ jw ^ 3 ++ [O, O] ++ v2)
      (jw ^ (13 + 2 * a) ++ [O, O] ++ v2) := by
    refine SegRLs.congr h3_raw rfl rfl (by simp only [List.append_assoc]) ?_
    rw [show 13 + 2 * a = (10 + 2 * a) + 3 by omega, pow_add_list jw (10 + 2 * a) 3]
    simp only [List.append_assoc]
  have h123 := h1.trans (h2.trans h3)
  refine SegRLs.congr h123 ?_ rfl rfl rfl
  exact pow_add3_eq hg (by unfold clean2; omega)

lemma recut2 (k : ℕ) : aw ++ tw ^ (1 + k) ++ [I, O, I] ++ v2 = lw ++ tw ^ k ++ u2 := by
  unfold v2 u2
  rw [Nat.add_comm 1 k, pow_succ_list]
  have hbw := bw_comm_T k
  have haw : aw ++ tw ++ tw ^ k = lw ++ (bw ++ tw ^ k) := rfl
  rw [← List.append_assoc aw tw (tw ^ k), haw, hbw]
  simp only [List.append_assoc]
  rfl

lemma first_constants : 72 + 128 * short1_count 11 = 8 * q4 16 + 4 * 4 ^ 17 + 32 * j1 := by
  unfold short1_count j1
  decide

lemma first_budget_algebra (qn q16_v p17 s11 j1_v xn : ℕ)
    (hc : 72 + 128 * s11 = 8 * q16_v + 4 * p17 + 32 * j1_v)
    (hk : 1 + 3 * qn = xn) :
    2 + 16 * (qn + xn) + 2 * s11 * (xn * 64) + (qn + xn * 85) =
      1 + (8 * (qn + xn * q16_v) + 1 + (4 * (xn * p17) + (29 + 96 * qn + 2 * j1_v * (xn * 16)))) := by
  nlinarith

lemma first_budget (n : ℕ) :
    reset_count (1 + n) (short1_count 11) = 1 + supply_count n (16 + n) j1 := by
  unfold reset_count supply_count
  have h1 : 2 + (1 + n) = n + 3 := by omega
  have h2 : 3 + (1 + n) = n + 4 := by omega
  have h3 : 1 + (16 + n) = n + 17 := by omega
  have h4 : 2 + n = n + 2 := by omega
  have h5 : 1 + n = n + 1 := by omega
  have h6 : 16 + n = n + 16 := by omega
  rw [h1, h2, h3, h4, h5, h6]
  rw [q4_add n 1, q4_add n 4, q4_add n 16]
  rw [Nat.pow_add 4 n 3, Nat.pow_add 4 n 17, Nat.pow_add 4 n 2]
  have hq1 : q4 1 = 1 := rfl
  have hq4 : q4 4 = 85 := rfl
  have hp3 : 4 ^ 3 = 64 := rfl
  have hp2 : 4 ^ 2 = 16 := rfl
  rw [hq1, Nat.mul_one, hq4, hp3, hp2]
  exact first_budget_algebra (q4 n) (q4 16) (4 ^ 17) (short1_count 11) j1 (4 ^ n)
    first_constants (q4_pow n)

lemma first_supply_index_gen (m p a : ℕ) (hm : m = 1 + 2 * p) (ha : m = 9 + 2 * a) :
    supply_count (7 + 2 * a) (23 + 2 * a) j1 = 8 + 2 * reset_index (2 * p) (short1_count 11) := by
  have H := first_budget (7 + 2 * a)
  rw [show 1 + (7 + 2 * a) = 2 * p by omega,
    reset_index_spec (2 * p) (short1_count 11),
    show 16 + (7 + 2 * a) = 23 + 2 * a by omega] at H
  omega

lemma first_supply_index : supply_count (7 + 2 * a0) (23 + 2 * a0) j1 = 8 + 2 * b0 :=
  first_supply_index_gen m0 p0 a0 m0_first m0_odd

local notation "c0_index" => reset_index (8 + 2 * b0) (clean2 a0)

lemma second_run (a b : ℕ) (E : supply_count (7 + 2 * a) (23 + 2 * a) j1 = 8 + 2 * b) :
    (P 0 (tw +> (lw ^ (9 + 2 * b) +> (kw +> (tw +> (lw +> (tw ^ (23 + 2 * a) +> (u1 +> default)))))))) [tm]⊢*
      (P 0 (tw +> (lw ^ (9 + 2 * reset_index (8 + 2 * b) (clean2 a)) +>
        (kw +> (tw +> (lw +> (tw ^ (21 + 2 * a + 2 * b) +> (u2 +> default)))))))) := by
  have H : SegRLs tm (hf ^ (8 + 2 * b)) []
      (zw ++ (lw ++ tw ^ (23 + 2 * a) ++ u1))
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * a) ++ rw ++ cw ++ tail1) :=
    SegRLs.congr (second_supply a) (by rw [E]) rfl (by simp only [List.append_assoc]) rfl
  have K : SegRLs tm (hg ^ (clean2 a)) []
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * a) ++ rw ++ cw ++ tail1)
      (jw ^ (1 + (12 + 2 * a)) ++ [O, O] ++ v2) :=
    SegRLs.congr (second_clean a) rfl rfl rfl
      (by rw [show 13 + 2 * a = 1 + (12 + 2 * a) by omega])
  have R := reset_run (8 + 2 * b) (clean2 a) (12 + 2 * a)
    (lw ++ tw ^ (23 + 2 * a) ++ u1)
    (zw ++ jw ++ lw ++ mw ^ (7 + 2 * a) ++ rw ++ cw ++ tail1)
    v2 default H K
  refine stepPlus_to_stepStar (stepPlus_congr R ?_ ?_)
  · rw [show 1 + (8 + 2 * b) = 9 + 2 * b by omega]
    simp only [append_assoc]
  · have h_rec := recut2 (21 + 2 * a + 2 * b)
    have h_rec' : (aw +> (tw ^ (1 + (21 + 2 * a + 2 * b)) +> ([I, O, I] +> (v2 +> (default : ListBlank Γ))))) =
        (lw +> (tw ^ (21 + 2 * a + 2 * b) +> (u2 +> default))) := by
      simpa only [append_assoc] using congrArg (· +> (default : ListBlank Γ)) h_rec
    rw [reset_index_spec, show 2 + (8 + 2 * b) + (12 + 2 * a) = 1 + (21 + 2 * a + 2 * b) by omega, h_rec']

lemma second_reset :
    (init []) [tm]⊢*
      (P 0 (tw +> (lw ^ (9 + 2 * c0_index) +>
        (kw +> (tw +> (lw +> (tw ^ (21 + 2 * a0 + 2 * b0) +> (u2 +> default)))))))) :=
  stepStar_trans first_reset (second_run a0 b0 first_supply_index)

def pair_count (r : ℕ) : ℕ := 125 * 16 ^ r + 13 * q16 r

lemma pair_digits (r : ℕ) :
    SegRLs tm (hg ^ (pair_count r)) [] (tw ^ (4 + 2 * r)) (kw ++ cw ^ r ++ dw) := by
  induction r with
  | zero =>
    have h0 : pair_count 0 = 125 := rfl
    exact SegRLs.congr G125 (by rw [h0]) rfl rfl rfl
  | succ r ih =>
    have E : pair_count (r + 1) = 16 * pair_count r + 13 := by
      unfold pair_count
      dsimp [q16]
      rw [Nat.pow_succ]
      ring
    have h1 := (G_Ts 2 (pair_count r)).concat ih
    have h2 := service_tail (cw ^ r ++ dw) G_pair13
    have h12 := SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])
    refine SegRLs.congr h12 ?_ rfl ?_ ?_
    · exact pow_add2_eq hg (by rw [E]; omega)
    · rw [← pow_add_list]
      exact congrArg (tw ^ ·) (by omega)
    · rw [pow_succ_list cw r]
      simp only [List.append_assoc]

def j2 (r : ℕ) : ℕ := 64 * pair_count r + 61

lemma third_g (r : ℕ) :
    SegRLs tm (hg ^ (j2 r)) [] (tw ^ (7 + 2 * r)) (kw ++ dw ++ cw ^ r ++ dw) := by
  have h1 := (G_Ts 3 (pair_count r)).concat (pair_digits r)
  have h2 := service_tail (cw ^ r ++ dw) G_last61
  have h12 := SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc])
  refine SegRLs.congr h12 ?_ rfl ?_ rfl
  · exact pow_add2_eq hg (by unfold j2; omega)
  · rw [← pow_add_list]
    exact congrArg (tw ^ ·) (by omega)

def v3 : List Γ := kw ++ [I, I, O] ++ kw ^ 10 ++ lw ++ mw ++ ww
def w3 : List Γ := lw ++ [O, I, O] ++ kw ^ 10 ++ lw ++ mw ++ ww
def tail3 (a : ℕ) : List Γ := cw ^ (3 + a) ++ dw ++ w3

lemma third_H : SegRLs tm hh [] u2 v3 := by
  unfold u2 v3
  exact SegRLs.congr (service_tail ([I, I, O] ++ kw ^ 10 ++ lw ++ mw ++ ww) H_Z)
    rfl rfl (by simp only [List.append_assoc]) (by simp only [List.append_assoc])

lemma third_G2 : SegRLs tm (hg ^ 2) [] v3 w3 :=
  BoundedConfig.segRLs_c_spec tm (T := 1000) (by decide)

lemma third_supply (a b : ℕ) :
    SegRLs tm (hf ^ (supply_count (7 + 2 * b) (21 + 2 * a + 2 * b) (j2 (3 + a)))) []
      (zw ++ lw ++ tw ^ (21 + 2 * a + 2 * b) ++ u2)
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ tail3 a) := by
  have h1 : SegRLs tm (hg ^ (j2 (3 + a))) [] (tw ^ (7 + 2 * (3 + a)) ++ w3) (kw ++ dw ++ tail3 a) :=
    SegRLs.congr (service_tail w3 (third_g (3 + a))) rfl rfl rfl
      (by unfold tail3; simp only [List.append_assoc])
  have h2 := service_tail (dw ++ tail3 a) F_K
  have hL : SegRLs tm (hg ^ (j2 (3 + a)) ++ hf) [] (tw ^ (7 + 2 * (3 + a)) ++ w3) (rw ++ dw ++ tail3 a) :=
    SegRLs.congr (SegRLs.trans_eq h1 h2 (by simp only [List.append_assoc]))
      rfl rfl rfl (by simp only [List.append_assoc])
  have h := reset_supply (7 + 2 * b) (21 + 2 * a + 2 * b) (7 + 2 * (3 + a)) (j2 (3 + a))
    u2 v3 w3 (rw ++ dw ++ tail3 a) (by omega) third_H third_G2 hL
  exact SegRLs.congr h rfl rfl rfl (by simp only [List.append_assoc])

def clean3 (b : ℕ) : ℕ := 2 + 8 * q16 (5 + b) + 2892 * 4 ^ (10 + 2 * b) + 2 * q4 (10 + 2 * b)
def v4 (a : ℕ) : List Γ := bw ++ rw ++ cw ^ (1 + a) ++ dw ++ w3

lemma third_clean (a b : ℕ) :
    SegRLs tm (hg ^ (clean3 b)) []
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ tail3 a)
      (jw ^ (16 + 2 * b) ++ [O, O] ++ v4 a) := by
  have h1_raw := service_tail (tail3 a) (M_block (3 + b))
  have h1 : SegRLs tm (hg ^ (2 + 8 * q16 (5 + b))) []
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ tail3 a)
      (tw ^ (10 + 2 * b) ++ zw ++ tw ^ 2 ++ jw ++ tail3 a) := by
    refine SegRLs.congr h1_raw ?_ rfl ?_ ?_
    · rw [show 2 + (3 + b) = 5 + b by omega]
    · rw [show 1 + 2 * (3 + b) = 7 + 2 * b by omega]
    · rw [show 4 + 2 * (3 + b) = 10 + 2 * b by omega]
  have h2_raw := (G_Ts (10 + 2 * b) 2892).concat (service_tail (dw ++ w3) (PACKET (1 + a)))
  have h2 : SegRLs tm (hg ^ (2892 * 4 ^ (10 + 2 * b))) []
      (tw ^ (10 + 2 * b) ++ zw ++ tw ^ 2 ++ jw ++ tail3 a)
      (tw ^ (10 + 2 * b) ++ jw ^ 6 ++ [O, O] ++ v4 a) := by
    refine SegRLs.congr h2_raw rfl rfl ?_ ?_
    · unfold tail3
      rw [show 3 + a = 2 + (1 + a) by omega]
      simp only [List.append_assoc]
    · unfold v4
      simp only [List.append_assoc]
      rfl
  have h3_raw := service_tail (jw ^ 6 ++ [O, O] ++ v4 a) (G_normalize (10 + 2 * b))
  have h3 : SegRLs tm (hg ^ (2 * q4 (10 + 2 * b))) []
      (tw ^ (10 + 2 * b) ++ jw ^ 6 ++ [O, O] ++ v4 a)
      (jw ^ (16 + 2 * b) ++ [O, O] ++ v4 a) := by
    refine SegRLs.congr h3_raw rfl rfl (by simp only [List.append_assoc]) ?_
    rw [show 16 + 2 * b = (10 + 2 * b) + 6 by omega, pow_add_list jw (10 + 2 * b) 6]
    simp only [List.append_assoc]
  have h123 := h1.trans (h2.trans h3)
  refine SegRLs.congr h123 ?_ rfl rfl rfl
  exact pow_add3_eq hg (by unfold clean3; omega)

def v5 (a : ℕ) : List Γ := [I] ++ rw ++ cw ^ a ++ dw ++ w3

lemma recut3 (a k : ℕ) :
    aw ++ tw ^ (1 + k) ++ [I, O, I] ++ v4 a = lw ++ tw ^ k ++ zw ++ kw ++ tw ++ [O, O] ++ v5 a := by
  unfold v4 v5
  rw [Nat.add_comm 1 k, pow_succ_list, Nat.add_comm 1 a, pow_succ_list]
  have hbw := bw_comm_T k
  have haw : aw ++ tw ++ tw ^ k = lw ++ (bw ++ tw ^ k) := rfl
  rw [← List.append_assoc aw tw (tw ^ k), haw, hbw]
  simp only [List.append_assoc]
  rfl

lemma reset_supply_balance_algebra (qn qt j k xn xt : ℕ)
    (h1 : 9 + 16 * j = qt + 2 * xt + 4 * k)
    (h2 : 1 + 3 * qn = xn) :
    2 + 16 * (qn + xn) + 2 * j * (xn * 64) + (qn + xn * 85) =
      1 + (8 * (qn + xn * qt) + 1 + (4 * (xn * (4 * xt)) + (29 + 96 * qn + 2 * k * (xn * 16)))) := by
  nlinarith

lemma reset_supply_balance (n t j k : ℕ) (H : 9 + 16 * j = q4 t + 2 * 4 ^ t + 4 * k) :
    reset_count (1 + n) j = 1 + supply_count n (n + t) k := by
  unfold reset_count supply_count
  have h1 : 2 + (1 + n) = n + 3 := by omega
  have h2 : 3 + (1 + n) = n + 4 := by omega
  have h3 : 1 + (n + t) = n + (1 + t) := by omega
  have h4 : 2 + n = n + 2 := by omega
  have h5 : 1 + n = n + 1 := by omega
  rw [h1, h2, h3, h4, h5]
  rw [q4_add n 1, q4_add n 4, q4_add n t]
  rw [Nat.pow_add 4 n 3, Nat.pow_add 4 n (1 + t), Nat.pow_add 4 n 2]
  have hq1 : q4 1 = 1 := rfl
  have hq4 : q4 4 = 85 := rfl
  have hp3 : 4 ^ 3 = 64 := rfl
  have hp2 : 4 ^ 2 = 16 := rfl
  have hp1t : 4 ^ (1 + t) = 4 * 4 ^ t := by rw [Nat.pow_add]
  rw [hq1, Nat.mul_one, hq4, hp3, hp2, hp1t]
  exact reset_supply_balance_algebra (q4 n) (q4 t) j k (4 ^ n) (4 ^ t) H (q4_pow n)

lemma bridge_constants_algebra (q10 q14 q16_3 x : ℕ)
    (H1 : 1 + 3 * q10 = 256 * x)
    (H2 : 1 + 3 * q14 = 65536 * x)
    (H3 : 1 + 15 * q16_3 = x) :
    9 + 16 * (2 + 8 * (1 + 16 * (1 + 16 * q16_3)) + 44 * (256 * x) + 2 * q10) =
      q14 + 2 * (65536 * x) + 4 * (64 * (125 * x + 13 * q16_3) + 61) := by
  omega

lemma bridge_constants (a : ℕ) :
    9 + 16 * clean2 a = q4 (14 + 2 * a) + 2 * 4 ^ (14 + 2 * a) + 4 * j2 (3 + a) := by
  have E1 : 4 ^ (10 + 2 * a) = 256 * 16 ^ (3 + a) := by
    rw [show 10 + 2 * a = 4 + 2 * (3 + a) by omega, Nat.pow_add, pow4_double]
  have E2 : 4 ^ (14 + 2 * a) = 65536 * 16 ^ (3 + a) := by
    rw [show 14 + 2 * a = 4 + (10 + 2 * a) by omega, Nat.pow_add, E1]
    ring
  have H1 := q4_pow (10 + 2 * a); rw [E1] at H1
  have H2 := q4_pow (14 + 2 * a); rw [E2] at H2
  have H3 := q16_pow (3 + a)
  have hq16 : q16 (5 + a) = 1 + 16 * (1 + 16 * q16 (3 + a)) := by
    rw [show 5 + a = (3 + a) + 1 + 1 by omega]
    rfl
  unfold clean2 j2 pair_count
  rw [E1, E2, hq16]
  exact bridge_constants_algebra (q4 (10 + 2 * a)) (q4 (14 + 2 * a)) (q16 (3 + a)) (16 ^ (3 + a))
    H1 H2 H3

lemma bridge_budget (a b : ℕ) :
    reset_count (8 + 2 * b) (clean2 a) =
      1 + supply_count (7 + 2 * b) (21 + 2 * a + 2 * b) (j2 (3 + a)) := by
  have h := reset_supply_balance (7 + 2 * b) (14 + 2 * a) (clean2 a) (j2 (3 + a)) (bridge_constants a)
  rwa [show 1 + (7 + 2 * b) = 8 + 2 * b by omega,
    show 7 + 2 * b + (14 + 2 * a) = 21 + 2 * a + 2 * b by omega] at h

lemma third_supply_index_gen (a b : ℕ) :
    supply_count (7 + 2 * b) (21 + 2 * a + 2 * b) (j2 (3 + a)) =
      8 + 2 * reset_index (8 + 2 * b) (clean2 a) := by
  have H := bridge_budget a b
  rw [reset_index_spec (8 + 2 * b) (clean2 a)] at H
  omega

lemma third_supply_index :
    supply_count (7 + 2 * b0) (21 + 2 * a0 + 2 * b0) (j2 (3 + a0)) = 8 + 2 * c0_index :=
  third_supply_index_gen a0 b0

lemma final_budget (a b : ℕ) : reset_count (8 + 2 * b) (clean3 a) = 9 + 2 * e a b := by
  rw [← tower_budget a b]
  unfold reset_count clean3
  have hp : 4 ^ (20 + 2 * a + 2 * b) = 4 ^ (10 + 2 * a) * 4 ^ (10 + 2 * b) := by
    rw [show 20 + 2 * a + 2 * b = (10 + 2 * a) + (10 + 2 * b) by omega, Nat.pow_add]
  have hq : q4 (21 + 2 * a + 2 * b) = q4 (11 + 2 * b) + 4 ^ (11 + 2 * b) * q4 (10 + 2 * a) := by
    rw [show 21 + 2 * a + 2 * b = (11 + 2 * b) + (10 + 2 * a) by omega, q4_add]
  have hp11 : 4 ^ (11 + 2 * b) = 4 * 4 ^ (10 + 2 * b) := by
    rw [show 11 + 2 * b = 1 + (10 + 2 * b) by omega, Nat.pow_add]
  have h28 : 2 + (8 + 2 * b) = 10 + 2 * b := by omega
  have h38 : 3 + (8 + 2 * b) = 11 + 2 * b := by omega
  rw [h28, h38, hp, hq, hp11]
  ring

lemma third_run (a b c : ℕ)
    (E : supply_count (7 + 2 * b) (21 + 2 * a + 2 * b) (j2 (3 + a)) = 8 + 2 * c) :
    (P 0 (tw +> (lw ^ (9 + 2 * c) +> (kw +> (tw +> (lw +>
      (tw ^ (21 + 2 * a + 2 * b) +> (u2 +> default)))))))) [tm]⊢*
      (Inv b c (v5 a +> default)) := by
  have H : SegRLs tm (hf ^ (8 + 2 * c)) []
      (zw ++ (lw ++ tw ^ (21 + 2 * a + 2 * b) ++ u2))
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ tail3 a) :=
    SegRLs.congr (third_supply a b) (by rw [E]) rfl (by simp only [List.append_assoc]) rfl
  have K : SegRLs tm (hg ^ (clean3 b)) []
      (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ tail3 a)
      (jw ^ (1 + (15 + 2 * b)) ++ [O, O] ++ v4 a) :=
    SegRLs.congr (third_clean a b) rfl rfl rfl
      (by rw [show 16 + 2 * b = 1 + (15 + 2 * b) by omega])
  have R := reset_run (8 + 2 * c) (clean3 b) (15 + 2 * b)
    (lw ++ tw ^ (21 + 2 * a + 2 * b) ++ u2)
    (zw ++ jw ++ lw ++ mw ^ (7 + 2 * b) ++ rw ++ dw ++ tail3 a)
    (v4 a) default H K
  refine stepPlus_to_stepStar (stepPlus_congr R ?_ ?_)
  · rw [show 1 + (8 + 2 * c) = 9 + 2 * c by omega]
    simp only [append_assoc]
  · have h_rec := recut3 a (24 + 2 * b + 2 * c)
    have h_rec' : (aw +> (tw ^ (1 + (24 + 2 * b + 2 * c)) +> ([I, O, I] +> (v4 a +> (default : ListBlank Γ))))) =
        (lw +> (tw ^ (24 + 2 * b + 2 * c) +> (zw +> (kw +> (tw +> ([O, O] +> (v5 a +> default))))))) := by
      simpa only [append_assoc] using congrArg (· +> (default : ListBlank Γ)) h_rec
    unfold Inv family_word
    rw [final_budget, show 2 + (8 + 2 * c) + (15 + 2 * b) = 1 + (24 + 2 * b + 2 * c) by omega]
    simp only [append_assoc] at h_rec' ⊢
    rw [h_rec']

lemma init_family : (init []) [tm]⊢* (Inv b0 c0_index (v5 a0 +> default)) :=
  stepStar_trans second_reset (third_run a0 b0 c0_index third_supply_index)

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ a b u, c = Inv a b u)
    ⟨Inv b0 c0_index (v5 a0 +> default), init_family, b0, c0_index, v5 a0 +> default, rfl⟩ ?_
  rintro _ ⟨a, b, u, rfl⟩
  exact ⟨Inv b (e a b) (family_prefix a +> u), I_step a b u, b, e a b, family_prefix a +> u, rfl⟩

end BusyBeaver.M_1RB1LB_1RC0LA_1LD1RF_1RB0LE_HHH1LA_1RD0RD
