/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.Longitudinal


/-!
# Busy Beaver Machine `1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.Longitudinal`
and defines `target_tm` for `1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 3, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Longitudinal

abbrev zB := ListBlank (Fin 2)

/-- Right half-tape unit block `X = [1, 1, 0, 1]`. -/
abbrev X : List (Fin 2) := [1, 1, 0, 1]

/-- Left half-tape unit block `Dr = [1, 1, 0, 0]` (head-adjacent bit first). -/
abbrev Dr : List (Fin 2) := [1, 1, 0, 0]

/--
Right-side boundary bounce signal: enter right in state `C` (`2`), exit left in state `B` (`1`). -/
abbrev hf : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) :=
  [((2, []), (1, []))]

/-- Left-side dual bounce signal: enter left in state `B` (`1`), exit right in state `C` (`2`). -/
abbrev hfb : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) :=
  [((1, []), (2, []))]

/--
A right-side tape `r` is an `m`-call wall if `m` consecutive `C`/`B` bounces prepend `[0, 0]`. -/
def Wall (m : ℕ) (r : zB) : Prop :=
  SideRLs target_tm (hf ^ m) r ([0, 0] +> r)

-- ============================================================================
-- Section 1: ListBlank / Pow Helpers
-- ============================================================================

private theorem lb_append_assoc (w₁ w₂ : List (Fin 2)) (s : zB) :
    (w₁ ++ w₂) +> s = w₁ +> (w₂ +> s) :=
  Longitudinal.append_assoc w₁ w₂ s

private theorem lb_append_pow_succ (w : List (Fin 2)) (n : ℕ) (s : zB) :
    (w ^ (n + 1)) +> s = w +> ((w ^ n) +> s) := by
  rw [Longitudinal.pow_succ_list, lb_append_assoc]

private theorem lb_append_pow_add (w : List (Fin 2)) (m n : ℕ) (s : zB) :
    (w ^ (m + n)) +> s = (w ^ m) +> ((w ^ n) +> s) := by
  rw [Longitudinal.pow_add_list, lb_append_assoc]

private theorem lb_append_pow_one (w : List (Fin 2)) (s : zB) :
    (w ^ 1) +> s = w +> s := by
  rw [Longitudinal.pow_one_list]

private theorem lb_append_00_default : ([0, 0] : List (Fin 2)) +> (default : zB) = default := by
  change (0 : Fin 2) >> ((0 : Fin 2) >> (default : zB)) = default
  rw [zero_cons_default, zero_cons_default]

private theorem sideRL_flip_of_stepPlus {q₁ q₂ : Fin 6} {l₁ l₂ : zB}
    (h : ∀ r : zB, (l₁ <{{q₁}} r) [target_tm]⊢⁺ (l₂ {{q₂}}> r)) :
    SideRL (flipTM target_tm) (q₁, []) (q₂, []) l₁ l₂ := by
  intro r
  exact toDHCfg_stepPlus_flip (h₁ := (q₁, [])) (d₁ := .left) (h₂ := (q₂, [])) (d₂ := .right) (h r)

private theorem wall_zero_default : Wall 0 default := by
  unfold Wall
  rw [lb_append_00_default]
  exact SideRLs.nil default

-- ============================================================================
-- Section 2: Fundamental Shift Lemmas & 2D Space-Time Tiles (`SegRLs`)
-- ============================================================================

private theorem step_C_X_one (l r : zB) :
    (l {{2}}> (X +> r)) [target_tm]⊢* ((Dr +> l) {{2}}> r) := by
  bb_steps

private theorem shift_C_X (n : ℕ) (l r : zB) :
    (l {{2}}> ((X ^ n) +> r)) [target_tm]⊢* (((Dr ^ n) +> l) {{2}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl target_tm _
  | succ n ih =>
    rw [lb_append_pow_succ]
    refine stepStar_trans (step_C_X_one l ((X ^ n) +> r)) ?_
    have h := ih (Dr +> l)
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list'] at h
    exact h

private theorem step_B_Dr_one (l r : zB) :
    ((Dr +> l) <{{1}} r) [target_tm]⊢* (l <{{1}} (X +> r)) := by
  bb_steps

private theorem shift_B_Dr (n : ℕ) (l r : zB) :
    (((Dr ^ n) +> l) <{{1}} r) [target_tm]⊢* (l <{{1}} ((X ^ n) +> r)) := by
  induction n generalizing r with
  | zero => exact stepStar_refl target_tm _
  | succ n ih =>
    rw [lb_append_pow_succ]
    refine stepStar_trans (step_B_Dr_one ((Dr ^ n) +> l) r) ?_
    have h := ih (X +> r)
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list'] at h
    exact h

private theorem seg_X : SegRLs target_tm hf hf X X := by
  have hrr : SegRR target_tm (2, []) (2, []) X Dr := fun l r => step_C_X_one l r
  have hll : SegLL target_tm (1, []) (1, []) Dr X := fun l r => step_B_Dr_one l r
  simpa [hf, Longitudinal.lrcons] using
    SegRLs.lrcons hrr hll (SegLRs.nil Dr) (SegRLs.nil X)

private theorem seg_X_pow (n : ℕ) : SegRLs target_tm hf hf (X ^ n) (X ^ n) := by
  induction n with
  | zero =>
    have hrr : SegRR target_tm (2, []) (2, []) [] [] := fun l r => stepStar_refl target_tm _
    have hll : SegLL target_tm (1, []) (1, []) [] [] := fun l r => stepStar_refl target_tm _
    simpa [hf, Longitudinal.lrcons] using
      SegRLs.lrcons hrr hll (SegLRs.nil []) (SegRLs.nil [])
  | succ n ih =>
    rw [Longitudinal.pow_succ_list]
    exact seg_X.concat ih

private theorem seg_X_pow_iter (k n : ℕ) :
    SegRLs target_tm (hf ^ k) (hf ^ k) (X ^ n) (X ^ n) := by
  induction k with
  | zero => exact SegRLs.nil (X ^ n)
  | succ k ih =>
    rw [Longitudinal.pow_succ_list]
    exact (seg_X_pow n).trans ih

private theorem seg_0X_rr : SegRR target_tm (2, []) (2, []) ([0] ++ X) [1, 1, 0, 1, 1] := by
  intro l r
  dsimp [toDHCfg, X]
  bb_steps

private theorem seg_0X_lr :
    SegLR target_tm (1, []) (2, []) [1, 1, 0, 1, 1] [1, 1, 0, 0, 1] := by
  intro l r
  dsimp [toDHCfg]
  bb_steps

private theorem seg_0X_ll :
    SegLL target_tm (1, []) (1, []) [1, 1, 0, 0, 1] ([0] ++ X) := by
  intro l r
  dsimp [toDHCfg, X]
  bb_steps

/-- Doubling tile: `[0] ++ X` converts 1 left `hf` call into 2 right `hf` calls. -/
private theorem seg_0X : SegRLs target_tm hf (hf ^ 2) ([0] ++ X) ([0] ++ X) := by
  have hlrs : SegLRs target_tm [((1, []), (2, []))] [1, 1, 0, 1, 1] [1, 1, 0, 0, 1] :=
    SegLRs.cons seg_0X_lr (SegLRs.nil _)
  simpa [hf, Longitudinal.lrcons, Longitudinal.pow_succ_list, Longitudinal.pow_zero_list] using
    SegRLs.lrcons seg_0X_rr seg_0X_ll hlrs (SegRLs.nil ([0] ++ X))

private theorem seg_0X_iter (a : ℕ) :
    SegRLs target_tm (hf ^ a) (hf ^ (2 * a)) ([0] ++ X) ([0] ++ X) := by
  induction a with
  | zero => exact SegRLs.nil ([0] ++ X)
  | succ a ih =>
    have hmul : 2 * (a + 1) = 2 + 2 * a := by omega
    rw [Longitudinal.pow_succ_list, hmul, Longitudinal.pow_add_list]
    exact seg_0X.trans ih

-- ============================================================================
-- Section 3: Shifting `[0, 0]` Left Across `X` and `Wall` Constructor Lemmas
-- ============================================================================

private theorem sideRL_X_00 (r : zB) :
    SideRL target_tm (2, []) (1, []) (X +> ([0, 0] +> r)) ([0, 0] +> (X +> r)) := by
  intro l
  dsimp [toDHCfg, X]
  bb_steps

private theorem sideRL_X_pow_00 (k : ℕ) (r : zB) :
    SideRL target_tm (2, []) (1, [])
      ((X ^ (k + 1)) +> ([0, 0] +> r))
      ((X ^ k) +> ([0, 0] +> (X +> r))) := by
  intro l
  change (l {{2}}> ((X ^ (k + 1)) +> ([0, 0] +> r))) [target_tm]⊢⁺
    (l <{{1}} ((X ^ k) +> ([0, 0] +> (X +> r))))
  have hsplit : (X ^ (k + 1)) +> ([0, 0] +> r) = (X ^ k) +> (X +> ([0, 0] +> r)) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rw [hsplit]
  refine stepStar_stepPlus_trans (shift_C_X k l (X +> ([0, 0] +> r))) ?_
  refine stepPlus_stepStar_trans (sideRL_X_00 r ((Dr ^ k) +> l)) ?_
  exact shift_B_Dr k l ([0, 0] +> (X +> r))

private theorem sideRL_0X_00 (r : zB) :
    SideRL target_tm (2, []) (5, [])
      ([0] +> (X +> ([0, 0] +> r)))
      ([1, 0, 1] +> (X +> r)) := by
  intro l
  dsimp [toDHCfg, X]
  bb_steps

private theorem sideRL_0X2_00 (r : zB) :
    SideRL target_tm (2, []) (1, [])
      ([0] +> ((X ^ 2) +> ([0, 0] +> r)))
      ([0, 0] +> ([0] +> ((X ^ 2) +> r))) := by
  intro l
  dsimp [toDHCfg, X]
  change (l {{2}}> ([0] +> (X +> (X +> ([0, 0] +> r))))) [target_tm]⊢⁺
    (l <{{1}} ([0, 0] +> ([0] +> (X +> (X +> r)))))
  bb_steps

/-- One `hf` call across `[0] +> X^(k+3) +> [0,0]` shifts `[0,0]` left across two `X` blocks. -/
private theorem sideRLs_0X_shift2 (k : ℕ) (r : zB) :
    SideRLs target_tm hf
      ([0] +> ((X ^ (k + 3)) +> ([0, 0] +> r)))
      ([0] +> ((X ^ (k + 1)) +> ([0, 0] +> ((X ^ 2) +> r)))) := by
  have h1 : SideRLs target_tm hf
      ((X ^ (k + 2)) +> ([0, 0] +> r))
      ((X ^ (k + 1)) +> ([0, 0] +> (X +> r))) :=
    SideRLs.single (sideRL_X_pow_00 (k + 1) r)
  have h2 : SideRLs target_tm hf
      ((X ^ (k + 1)) +> ([0, 0] +> (X +> r)))
      ((X ^ k) +> ([0, 0] +> (X +> (X +> r)))) :=
    SideRLs.single (sideRL_X_pow_00 k (X +> r))
  have h12 : SideRLs target_tm (hf ^ 2)
      ((X ^ (k + 2)) +> ([0, 0] +> r))
      ((X ^ k) +> ([0, 0] +> ((X ^ 2) +> r))) := by
    have h := h1.trans h2
    simpa [Longitudinal.pow_succ_list, Longitudinal.pow_zero_list, lb_append_assoc] using h
  have hres := seg_0X.sideRLs_concat h12
  have hl : ([0] ++ X) +> ((X ^ (k + 2)) +> ([0, 0] +> r)) =
      [0] +> ((X ^ (k + 3)) +> ([0, 0] +> r)) := by
    rw [lb_append_assoc, ← lb_append_pow_succ]
  have hr : ([0] ++ X) +> ((X ^ k) +> ([0, 0] +> ((X ^ 2) +> r))) =
      [0] +> ((X ^ (k + 1)) +> ([0, 0] +> ((X ^ 2) +> r))) := by
    rw [lb_append_assoc, ← lb_append_pow_succ]
  rwa [hl, hr] at hres

private theorem sideRLs_0X_shift2_iter (b : ℕ) :
    ∀ (k : ℕ) (r : zB),
      SideRLs target_tm (hf ^ b)
        ([0] +> ((X ^ (2 * b + k + 1)) +> ([0, 0] +> r)))
        ([0] +> ((X ^ (k + 1)) +> ([0, 0] +> ((X ^ (2 * b)) +> r)))) := by
  induction b with
  | zero =>
    intro k r
    simpa using SideRLs.nil ([0] +> ((X ^ (k + 1)) +> ([0, 0] +> r)))
  | succ b ih =>
    intro k r
    have hstep := sideRLs_0X_shift2 (2 * b + k) r
    have hidx : 2 * (b + 1) + k + 1 = (2 * b + k) + 3 := by omega
    rw [hidx, Longitudinal.pow_succ_list]
    refine hstep.trans ?_
    have hrest := ih k ((X ^ 2) +> r)
    have hexp : (X ^ (2 * b)) +> ((X ^ 2) +> r) = (X ^ (2 * (b + 1))) +> r := by
      rw [← lb_append_pow_add, Nat.add_comm (2 * b) 2]
      have : 2 + 2 * b = 2 * (b + 1) := by omega
      rw [this]
    rw [hexp] at hrest
    exact hrest

private theorem sideRLs_0X_finish_even (b : ℕ) (r : zB) :
    SideRLs target_tm (hf ^ (b + 1))
      ([0] +> ((X ^ (2 * b + 2)) +> ([0, 0] +> r)))
      ([0, 0] +> ([0] +> ((X ^ (2 * b + 2)) +> r))) := by
  have h1 := sideRLs_0X_shift2_iter b 1 r
  have h2 := SideRLs.single (sideRL_0X2_00 ((X ^ (2 * b)) +> r))
  have h12 := h1.trans_succ h2
  have hexp : (X ^ 2) +> ((X ^ (2 * b)) +> r) = (X ^ (2 * b + 2)) +> r := by
    rw [← lb_append_pow_add, Nat.add_comm 2 (2 * b)]
  simpa [hexp] using h12

private theorem sideRLs_0X_finish_odd (b : ℕ) (r : zB) :
    SideRLs target_tm (hf ^ b ++ [((2, []), (5, []))])
      ([0] +> ((X ^ (2 * b + 1)) +> ([0, 0] +> r)))
      ([1, 0, 1] +> ((X ^ (2 * b + 1)) +> r)) := by
  have h1 := sideRLs_0X_shift2_iter b 0 r
  have h2 := SideRLs.single (sideRL_0X_00 ((X ^ (2 * b)) +> r))
  have h12 := h1.trans h2
  have hexp : X +> ((X ^ (2 * b)) +> r) = (X ^ (2 * b + 1)) +> r := by
    rw [← lb_append_pow_succ, Nat.add_comm (2 * b) 1]
  simpa [hexp] using h12

/--
Even wall-building step: if `Wall m r`, `n ≥ 2`, and `m + n = 2 * k`, then `Wall k ([0] +> X^n +>
r)`. -/
private theorem wall_cons_even {m n k : ℕ} {r : zB}
    (hw : Wall m r) (hn : n ≥ 2) (hsum : m + n = 2 * k) :
    Wall k ([0] +> ((X ^ n) +> r)) := by
  unfold Wall at hw ⊢
  rcases Nat.even_or_odd' m with ⟨a, rfl | rfl⟩
  · -- m = 2 * a, so n = 2 * b + 2
    obtain ⟨b, hb⟩ : ∃ b, n = 2 * b + 2 := ⟨(n - 2) / 2, by omega⟩
    have hk : k = a + (b + 1) := by omega
    subst hb hk
    have htile := (seg_0X_iter a).concat (seg_X_pow_iter (2 * a) (2 * b + 1))
    have h1 := htile.sideRLs_concat hw
    have hrew1 : (([0] ++ X) ++ X ^ (2 * b + 1)) +> r = [0] +> ((X ^ (2 * b + 2)) +> r) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    have hrew2 : (([0] ++ X) ++ X ^ (2 * b + 1)) +> ([0, 0] +> r) =
        [0] +> ((X ^ (2 * b + 2)) +> ([0, 0] +> r)) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    rw [hrew1, hrew2] at h1
    exact h1.trans_add (sideRLs_0X_finish_even b r)
  · -- m = 2 * a + 1, so n = 2 * b + 3
    obtain ⟨b, hb⟩ : ∃ b, n = 2 * b + 3 := ⟨(n - 3) / 2, by omega⟩
    have hk : k = a + 1 + (b + 1) := by omega
    subst hb hk
    have hpow : hf ^ (2 * a + 1) = hf ^ (2 * a) ++ hf := by
      rw [Longitudinal.pow_add_list, Longitudinal.pow_one_list]
    rw [hpow] at hw
    obtain ⟨r_mid, hw1, hw2⟩ := hw.split
    -- First `a` calls consume `2 * a` calls of `r`
    have htileA := (seg_0X_iter a).concat (seg_X_pow_iter (2 * a) (2 * b + 2))
    have hA := htileA.sideRLs_concat hw1
    have hrewA1 : (([0] ++ X) ++ X ^ (2 * b + 2)) +> r = [0] +> ((X ^ (2 * b + 3)) +> r) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    have hrewA2 : (([0] ++ X) ++ X ^ (2 * b + 2)) +> r_mid = [0] +> ((X ^ (2 * b + 3)) +> r_mid)
      := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    rw [hrewA1, hrewA2] at hA
    -- Next `1` call consumes the last call of `r` AND shifts `[0, 0]` past 1 `X`
    have hB1 : SideRLs target_tm hf
        ((X ^ (2 * b + 2)) +> r_mid)
        ((X ^ (2 * b + 2)) +> ([0, 0] +> r)) :=
      (seg_X_pow (2 * b + 2)).sideRLs_concat hw2
    have hB2 : SideRLs target_tm hf
        ((X ^ (2 * b + 2)) +> ([0, 0] +> r))
        ((X ^ (2 * b + 1)) +> ([0, 0] +> (X +> r))) :=
      SideRLs.single (sideRL_X_pow_00 (2 * b + 1) r)
    have hB12 : SideRLs target_tm (hf ^ 2)
        ((X ^ (2 * b + 2)) +> r_mid)
        ((X ^ (2 * b + 1)) +> ([0, 0] +> (X +> r))) := by
      have h := hB1.trans hB2
      simpa [Longitudinal.pow_succ_list, Longitudinal.pow_zero_list] using h
    have hB := seg_0X.sideRLs_concat hB12
    have hrewB1 : ([0] ++ X) +> ((X ^ (2 * b + 2)) +> r_mid) =
        [0] +> ((X ^ (2 * b + 3)) +> r_mid) := by
      rw [lb_append_assoc, ← lb_append_pow_succ]
    have hrewB2 : ([0] ++ X) +> ((X ^ (2 * b + 1)) +> ([0, 0] +> (X +> r))) =
        [0] +> ((X ^ (2 * b + 2)) +> ([0, 0] +> (X +> r))) := by
      rw [lb_append_assoc, ← lb_append_pow_succ]
    rw [hrewB1, hrewB2] at hB
    -- Remaining `b + 1` calls shift `[0, 0]` across `X^(2*b+2)`
    have hC := sideRLs_0X_finish_even b (X +> r)
    have hrewC : (X ^ (2 * b + 2)) +> (X +> r) = (X ^ (2 * b + 3)) +> r := by
      rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
    rw [hrewC] at hC
    exact (hA.trans_succ hB).trans_add hC

/-- Odd wall-building step: if `Wall m r`, `n ≥ 2`, and `m + n = 2 * k + 1`, then `k` `hf` calls
followed by one `(C, F)` call rewrite `[0] +> X^n +> r` to `[1, 0, 1] +> X^n +> r`. -/
private theorem wall_cons_odd {m n k : ℕ} {r : zB}
    (hw : Wall m r) (hn : n ≥ 2) (hsum : m + n = 2 * k + 1) :
    SideRLs target_tm (hf ^ k ++ [((2, []), (5, []))])
      ([0] +> ((X ^ n) +> r))
      ([1, 0, 1] +> ((X ^ n) +> r)) := by
  unfold Wall at hw
  rcases Nat.even_or_odd' m with ⟨a, rfl | rfl⟩
  · -- m = 2 * a, so n = 2 * b + 1 (b ≥ 1 since n ≥ 2)
    obtain ⟨b, hb⟩ : ∃ b, n = 2 * b + 1 := ⟨(n - 1) / 2, by omega⟩
    have hb1 : b ≥ 1 := by omega
    have hk : k = a + b := by omega
    subst hb hk
    have htile := (seg_0X_iter a).concat (seg_X_pow_iter (2 * a) (2 * b))
    have h1 := htile.sideRLs_concat hw
    have hrew1 : (([0] ++ X) ++ X ^ (2 * b)) +> r = [0] +> ((X ^ (2 * b + 1)) +> r) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    have hrew2 : (([0] ++ X) ++ X ^ (2 * b)) +> ([0, 0] +> r) =
        [0] +> ((X ^ (2 * b + 1)) +> ([0, 0] +> r)) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    rw [hrew1, hrew2] at h1
    have h2 := sideRLs_0X_finish_odd b r
    have hres := h1.trans h2
    rw [← List.append_assoc, ← Longitudinal.pow_add_list] at hres
    exact hres
  · -- m = 2 * a + 1, so n = 2 * b + 2
    obtain ⟨b, hb⟩ : ∃ b, n = 2 * b + 2 := ⟨(n - 2) / 2, by omega⟩
    have hk : k = a + 1 + b := by omega
    subst hb hk
    have hpow : hf ^ (2 * a + 1) = hf ^ (2 * a) ++ hf := by
      rw [Longitudinal.pow_add_list, Longitudinal.pow_one_list]
    rw [hpow] at hw
    obtain ⟨r_mid, hw1, hw2⟩ := hw.split
    have htileA := (seg_0X_iter a).concat (seg_X_pow_iter (2 * a) (2 * b + 1))
    have hA := htileA.sideRLs_concat hw1
    have hrewA1 : (([0] ++ X) ++ X ^ (2 * b + 1)) +> r = [0] +> ((X ^ (2 * b + 2)) +> r) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    have hrewA2 : (([0] ++ X) ++ X ^ (2 * b + 1)) +> r_mid =
        [0] +> ((X ^ (2 * b + 2)) +> r_mid) := by
      rw [lb_append_assoc, lb_append_assoc, ← lb_append_pow_succ]
    rw [hrewA1, hrewA2] at hA
    have hB1 : SideRLs target_tm hf
        ((X ^ (2 * b + 1)) +> r_mid)
        ((X ^ (2 * b + 1)) +> ([0, 0] +> r)) :=
      (seg_X_pow (2 * b + 1)).sideRLs_concat hw2
    have hB2 : SideRLs target_tm hf
        ((X ^ (2 * b + 1)) +> ([0, 0] +> r))
        ((X ^ (2 * b)) +> ([0, 0] +> (X +> r))) :=
      SideRLs.single (sideRL_X_pow_00 (2 * b) r)
    have hB12 : SideRLs target_tm (hf ^ 2)
        ((X ^ (2 * b + 1)) +> r_mid)
        ((X ^ (2 * b)) +> ([0, 0] +> (X +> r))) := by
      have h := hB1.trans hB2
      simpa [Longitudinal.pow_succ_list, Longitudinal.pow_zero_list] using h
    have hB := seg_0X.sideRLs_concat hB12
    have hrewB1 : ([0] ++ X) +> ((X ^ (2 * b + 1)) +> r_mid) =
        [0] +> ((X ^ (2 * b + 2)) +> r_mid) := by
      rw [lb_append_assoc, ← lb_append_pow_succ]
    have hrewB2 : ([0] ++ X) +> ((X ^ (2 * b)) +> ([0, 0] +> (X +> r))) =
        [0] +> ((X ^ (2 * b + 1)) +> ([0, 0] +> (X +> r))) := by
      rw [lb_append_assoc, ← lb_append_pow_succ]
    rw [hrewB1, hrewB2] at hB
    have hC := sideRLs_0X_finish_odd b (X +> r)
    have hrewC : (X ^ (2 * b + 1)) +> (X +> r) = (X ^ (2 * b + 2)) +> r := by
      rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
    rw [hrewC] at hC
    have hAB := hA.trans_succ hB
    have hres := hAB.trans hC
    rw [← List.append_assoc, ← Longitudinal.pow_add_list] at hres
    exact hres

-- ============================================================================
-- Section 4: Left-Boundary Period-3 Counters (`SideRLs (flipTM target_tm)`)
-- ============================================================================

private theorem lb_phase0_base (r : zB) :
    ((Dr +> ([1] +> default)) <{{1}} r) [target_tm]⊢⁺
      (([1, 1, 0, 1, 1, 1] +> default) {{2}}> r) := by
  dsimp [Dr]
  bb_steps

private theorem lb_phase1_base (r : zB) :
    (([1, 1, 0, 1, 1, 1] +> default) <{{1}} r) [target_tm]⊢⁺
      ((Dr +> ([1, 1] +> default)) {{2}}> r) := by
  dsimp [Dr]
  bb_steps

private theorem lb_phase2_base (r : zB) :
    ((Dr +> ([1, 1] +> default)) <{{1}} r) [target_tm]⊢⁺
      (((Dr ^ 2) +> ([1] +> default)) {{2}}> r) := by
  change ((Dr +> ([1, 1] +> default)) <{{1}} r) [target_tm]⊢⁺
    ((Dr +> (Dr +> ([1] +> default))) {{2}}> r)
  dsimp [Dr]
  bb_steps

private theorem left_p0 (k : ℕ) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ (k + 1)) +> ([1] +> default))
      ((Dr ^ k) +> ([1, 1, 0, 1, 1, 1] +> default)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  have hs : (Dr ^ (k + 1)) +> ([1] +> default) = (Dr ^ k) +> (Dr +> ([1] +> default)) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rw [hs]
  refine stepStar_stepPlus_trans (shift_B_Dr k (Dr +> ([1] +> default)) r) ?_
  refine stepPlus_stepStar_trans (lb_phase0_base ((X ^ k) +> r)) ?_
  exact shift_C_X k ([1, 1, 0, 1, 1, 1] +> default) r

private theorem left_p1 (k : ℕ) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ k) +> ([1, 1, 0, 1, 1, 1] +> default))
      ((Dr ^ (k + 1)) +> ([1, 1] +> default)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  refine stepStar_stepPlus_trans (shift_B_Dr k ([1, 1, 0, 1, 1, 1] +> default) r) ?_
  refine stepPlus_stepStar_trans (lb_phase1_base ((X ^ k) +> r)) ?_
  have ht := shift_C_X k (Dr +> ([1, 1] +> default)) r
  have hs : (Dr ^ k) +> (Dr +> ([1, 1] +> default)) = (Dr ^ (k + 1)) +> ([1, 1] +> default) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rwa [hs] at ht

private theorem left_p2 (k : ℕ) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ (k + 1)) +> ([1, 1] +> default))
      ((Dr ^ (k + 2)) +> ([1] +> default)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  have hs : (Dr ^ (k + 1)) +> ([1, 1] +> default) = (Dr ^ k) +> (Dr +> ([1, 1] +> default)) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rw [hs]
  refine stepStar_stepPlus_trans (shift_B_Dr k (Dr +> ([1, 1] +> default)) r) ?_
  refine stepPlus_stepStar_trans (lb_phase2_base ((X ^ k) +> r)) ?_
  have ht := shift_C_X k ((Dr ^ 2) +> ([1] +> default)) r
  have hs2 : (Dr ^ k) +> ((Dr ^ 2) +> ([1] +> default)) =
      (Dr ^ (k + 2)) +> ([1] +> default) := by
    rw [← lb_append_pow_add]
  rwa [hs2] at ht

private theorem left_plain_3 (k : ℕ) :
    SideRLs (flipTM target_tm) (hfb ^ 3)
      ((Dr ^ (k + 1)) +> ([1] +> default))
      ((Dr ^ (k + 2)) +> ([1] +> default)) := by
  exact SideRLs.cons (left_p0 k) (SideRLs.cons (left_p1 k) (SideRLs.single (left_p2 k)))

private theorem left_plain_3j (j : ℕ) :
    ∀ k : ℕ,
      SideRLs (flipTM target_tm) (hfb ^ (3 * j))
        ((Dr ^ (k + 1)) +> ([1] +> default))
        ((Dr ^ (k + j + 1)) +> ([1] +> default)) := by
  induction j with
  | zero =>
    intro k
    simpa using SideRLs.nil ((Dr ^ (k + 1)) +> ([1] +> default))
  | succ j ih =>
    intro k
    have hmul : 3 * (j + 1) = 3 + 3 * j := by omega
    rw [hmul]
    have h1 := left_plain_3 k
    have h2 := ih (k + 1)
    have hexp : k + 1 + j + 1 = k + (j + 1) + 1 := by omega
    rw [hexp] at h2
    exact h1.trans_add h2

-- `[1, 0, 0]` counter (universal left tail `l`)

private theorem lb_100_p0_base (l r : zB) :
    ((Dr +> ([1, 0, 0] +> l)) <{{1}} r) [target_tm]⊢⁺
      (([1, 1, 0, 1, 1, 1, 0] +> l) {{2}}> r) := by
  dsimp [Dr]
  bb_steps

private theorem lb_100_p1_base (l r : zB) :
    (([1, 1, 0, 1, 1, 1, 0] +> l) <{{1}} r) [target_tm]⊢⁺
      ((Dr +> ([1, 1, 0] +> l)) {{2}}> r) := by
  dsimp [Dr]
  bb_steps

private theorem lb_100_p2_step_base (l r : zB) :
    (([1, 1, 0] +> (Dr +> l)) <{{1}} r) [target_tm]⊢⁺
      ((Dr +> ([1, 0, 0] +> l)) {{2}}> r) := by
  dsimp [Dr]
  bb_steps

private theorem lb_100_p2_base_def (r : zB) :
    (([1, 1, 0, 1] +> default) <{{1}} r) [target_tm]⊢⁺
      (((Dr ^ 2) +> ([1] +> default)) {{2}}> r) := by
  change (([1, 1, 0, 1] +> default) <{{1}} r) [target_tm]⊢⁺
    ((Dr +> (Dr +> ([1] +> default))) {{2}}> r)
  dsimp [Dr]
  bb_steps

private theorem left100_p0 (k : ℕ) (l : zB) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ (k + 1)) +> ([1, 0, 0] +> l))
      ((Dr ^ k) +> ([1, 1, 0, 1, 1, 1, 0] +> l)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  have hs : (Dr ^ (k + 1)) +> ([1, 0, 0] +> l) = (Dr ^ k) +> (Dr +> ([1, 0, 0] +> l)) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rw [hs]
  refine stepStar_stepPlus_trans (shift_B_Dr k (Dr +> ([1, 0, 0] +> l)) r) ?_
  refine stepPlus_stepStar_trans (lb_100_p0_base l ((X ^ k) +> r)) ?_
  exact shift_C_X k ([1, 1, 0, 1, 1, 1, 0] +> l) r

private theorem left100_p1 (k : ℕ) (l : zB) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ k) +> ([1, 1, 0, 1, 1, 1, 0] +> l))
      ((Dr ^ (k + 1)) +> ([1, 1, 0] +> l)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  refine stepStar_stepPlus_trans (shift_B_Dr k ([1, 1, 0, 1, 1, 1, 0] +> l) r) ?_
  refine stepPlus_stepStar_trans (lb_100_p1_base l ((X ^ k) +> r)) ?_
  have ht := shift_C_X k (Dr +> ([1, 1, 0] +> l)) r
  have hs : (Dr ^ k) +> (Dr +> ([1, 1, 0] +> l)) = (Dr ^ (k + 1)) +> ([1, 1, 0] +> l) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rwa [hs] at ht

private theorem left100_p2_step (k : ℕ) (l : zB) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ (k + 1)) +> ([1, 1, 0] +> (Dr +> l)))
      ((Dr ^ (k + 2)) +> ([1, 0, 0] +> l)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  refine stepStar_stepPlus_trans (shift_B_Dr (k + 1) ([1, 1, 0] +> (Dr +> l)) r) ?_
  refine stepPlus_stepStar_trans (lb_100_p2_step_base l ((X ^ (k + 1)) +> r)) ?_
  have ht := shift_C_X (k + 1) (Dr +> ([1, 0, 0] +> l)) r
  have hs : (Dr ^ (k + 1)) +> (Dr +> ([1, 0, 0] +> l)) = (Dr ^ (k + 2)) +> ([1, 0, 0] +> l) := by
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
  rwa [hs] at ht

private theorem left100_p2_base (k : ℕ) :
    SideRL (flipTM target_tm) (1, []) (2, [])
      ((Dr ^ (k + 1)) +> ([1, 1, 0, 1] +> default))
      ((Dr ^ (k + 3)) +> ([1] +> default)) := by
  apply sideRL_flip_of_stepPlus
  intro r
  refine stepStar_stepPlus_trans (shift_B_Dr (k + 1) ([1, 1, 0, 1] +> default) r) ?_
  refine stepPlus_stepStar_trans (lb_100_p2_base_def ((X ^ (k + 1)) +> r)) ?_
  have ht := shift_C_X (k + 1) ((Dr ^ 2) +> ([1] +> default)) r
  have hs : (Dr ^ (k + 1)) +> ((Dr ^ 2) +> ([1] +> default)) =
      (Dr ^ (k + 3)) +> ([1] +> default) := by
    rw [← lb_append_pow_add]
  rwa [hs] at ht

private theorem left100_3_step (k : ℕ) (l : zB) :
    SideRLs (flipTM target_tm) (hfb ^ 3)
      ((Dr ^ (k + 1)) +> ([1, 0, 0] +> (Dr +> l)))
      ((Dr ^ (k + 2)) +> ([1, 0, 0] +> l)) :=
  SideRLs.cons (left100_p0 k (Dr +> l))
    (SideRLs.cons (left100_p1 k (Dr +> l)) (SideRLs.single (left100_p2_step k l)))

private theorem left100_3_base (k : ℕ) :
    SideRLs (flipTM target_tm) (hfb ^ 3)
      ((Dr ^ (k + 1)) +> ([1, 0, 0] +> ([1] +> default)))
      ((Dr ^ (k + 3)) +> ([1] +> default)) :=
  SideRLs.cons (left100_p0 k ([1] +> default))
    (SideRLs.cons (left100_p1 k ([1] +> default)) (SideRLs.single (left100_p2_base k)))

private theorem left100_3t (t : ℕ) :
    ∀ (k : ℕ) (l : zB),
      SideRLs (flipTM target_tm) (hfb ^ (3 * t))
        ((Dr ^ (k + 1)) +> ([1, 0, 0] +> ((Dr ^ t) +> l)))
        ((Dr ^ (k + t + 1)) +> ([1, 0, 0] +> l)) := by
  induction t with
  | zero =>
    intro k l
    simpa using SideRLs.nil ((Dr ^ (k + 1)) +> ([1, 0, 0] +> l))
  | succ t ih =>
    intro k l
    have hmul : 3 * (t + 1) = 3 + 3 * t := by omega
    rw [hmul, lb_append_pow_succ]
    have h1 := left100_3_step k ((Dr ^ t) +> l)
    have h2 := ih (k + 1) l
    have hexp : k + 1 + t + 1 = k + (t + 1) + 1 := by omega
    rw [hexp] at h2
    exact h1.trans_add h2

-- ============================================================================
-- Section 5: Drains After `[0, 0] +> r` Returns
-- ============================================================================

private theorem step_B_default_entry (r : zB) :
    (default <{{1}} r) [target_tm]⊢⁺ (([1] +> default) {{2}}> r) := by
  bb_steps

private theorem step_C_00_Dr (l r : zB) :
    ((Dr +> l) {{2}}> ([0, 0] +> r)) [target_tm]⊢⁺ (l <{{1}} ([0, 0] +> (X +> r))) := by
  dsimp [Dr, X]
  bb_steps

private theorem step_B_11_default (r : zB) :
    (([1, 1] +> default) <{{1}} r) [target_tm]⊢⁺ (default <{{1}} ([0, 0] +> r)) := by
  bb_steps

private theorem step_B_1101_default (r : zB) :
    (([1, 1, 0, 1] +> default) <{{1}} r) [target_tm]⊢⁺ (default <{{1}} ([0, 0] +> (X +> r))) := by
  dsimp [X]
  bb_steps

private theorem step_B_00_def (r : zB) :
    (default <{{1}} ([0, 0] +> r)) [target_tm]⊢⁺ (default <{{1}} (X +> r)) := by
  dsimp [X]
  bb_steps

private theorem step_B_X_00_def (r : zB) :
    (default <{{1}} (X +> ([0, 0] +> r))) [target_tm]⊢⁺
      (default <{{1}} (X +> ([0] +> (X +> r)))) := by
  dsimp [X]
  bb_steps

private theorem step_B_X2_00_def (r : zB) :
    (default <{{1}} ((X ^ 2) +> ([0, 0] +> r))) [target_tm]⊢⁺
      (default <{{1}} ((X ^ 4) +> r)) := by
  change (default <{{1}} (X +> (X +> ([0, 0] +> r)))) [target_tm]⊢⁺
    (default <{{1}} (X +> (X +> (X +> (X +> r)))))
  dsimp [X]
  bb_steps

private theorem step_F_exit_entry (l r : zB) :
    ((Dr +> l) <{{5}} ([1, 0, 1] +> r)) [target_tm]⊢⁺
      ((Dr +> ([1, 0, 0] +> l)) {{2}}> r) := by
  dsimp [Dr]
  bb_steps

/--
Drains `Dr^u +> [1,1,0,1,1,1] <{{1}} ([0,0] +> r)` to `default <{{1}} (X^(u+1) +> [0,0] +> X +> r)`. -/
private theorem drain_A2 (u : ℕ) (r : zB) :
    (((Dr ^ u) +> ([1, 1, 0, 1, 1, 1] +> default)) <{{1}} ([0, 0] +> r)) [target_tm]⊢⁺
      (default <{{1}} ((X ^ (u + 1)) +> ([0, 0] +> (X +> r)))) := by
  refine stepStar_stepPlus_trans (shift_B_Dr u ([1, 1, 0, 1, 1, 1] +> default) ([0, 0] +> r)) ?_
  refine stepPlus_trans (lb_phase1_base ((X ^ u) +> ([0, 0] +> r))) ?_
  refine stepStar_stepPlus_trans (shift_C_X u (Dr +> ([1, 1] +> default)) ([0, 0] +> r)) ?_
  have h1 : (Dr ^ u) +> (Dr +> ([1, 1] +> default)) = Dr +> ((Dr ^ u) +> ([1, 1] +> default)) := by
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list', Longitudinal.pow_succ_list,
      lb_append_assoc]
  rw [h1]
  refine stepPlus_trans (step_C_00_Dr ((Dr ^ u) +> ([1, 1] +> default)) r) ?_
  refine stepStar_stepPlus_trans (shift_B_Dr u ([1, 1] +> default) ([0, 0] +> (X +> r))) ?_
  refine stepPlus_trans (step_B_11_default ((X ^ u) +> ([0, 0] +> (X +> r)))) ?_
  have h2 := step_B_00_def ((X ^ u) +> ([0, 0] +> (X +> r)))
  rwa [← lb_append_pow_succ] at h2

/-- One `X`-drain step: `X^(k+3) +> [0,0] +> r ⊢⁺ X^(k+1) +> [0,0] +> X^3 +> r`. -/
private theorem drain_X_00_step (k : ℕ) (r : zB) :
    (default <{{1}} ((X ^ (k + 3)) +> ([0, 0] +> r))) [target_tm]⊢⁺
      (default <{{1}} ((X ^ (k + 1)) +> ([0, 0] +> ((X ^ 3) +> r)))) := by
  refine stepPlus_trans (step_B_default_entry ((X ^ (k + 3)) +> ([0, 0] +> r))) ?_
  refine stepStar_stepPlus_trans (shift_C_X (k + 3) ([1] +> default) ([0, 0] +> r)) ?_
  have h1 : (Dr ^ (k + 3)) +> ([1] +> default) =
      Dr +> ((Dr ^ (k + 2)) +> ([1] +> default)) := by
    rw [lb_append_pow_succ]
  rw [h1]
  refine stepPlus_trans (step_C_00_Dr ((Dr ^ (k + 2)) +> ([1] +> default)) r) ?_
  have h2 : (Dr ^ (k + 2)) +> ([1] +> default) =
      (Dr ^ (k + 1)) +> (Dr +> ([1] +> default)) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rw [h2]
  refine stepStar_stepPlus_trans
    (shift_B_Dr (k + 1) (Dr +> ([1] +> default)) ([0, 0] +> (X +> r))) ?_
  refine stepPlus_trans (lb_phase0_base ((X ^ (k + 1)) +> ([0, 0] +> (X +> r)))) ?_
  refine stepStar_stepPlus_trans
    (shift_C_X (k + 1) ([1, 1, 0, 1, 1, 1] +> default) ([0, 0] +> (X +> r))) ?_
  have h3 : (Dr ^ (k + 1)) +> ([1, 1, 0, 1, 1, 1] +> default) =
      Dr +> ((Dr ^ k) +> ([1, 1, 0, 1, 1, 1] +> default)) := by
    rw [lb_append_pow_succ]
  rw [h3]
  refine stepPlus_trans (step_C_00_Dr ((Dr ^ k) +> ([1, 1, 0, 1, 1, 1] +> default)) (X +> r)) ?_
  have h4 := drain_A2 k (X +> (X +> r))
  have hr : X +> (X +> (X +> r)) = (X ^ 3) +> r := by
    simp only [Longitudinal.pow_succ_list, Longitudinal.pow_zero_list, List.append_nil,
      lb_append_assoc]
  rwa [hr] at h4

private theorem drain_X_00_odd (m : ℕ) :
    ∀ r : zB,
      (default <{{1}} ((X ^ (2 * m + 1)) +> ([0, 0] +> r))) [target_tm]⊢⁺
        (default <{{1}} (X +> ([0] +> ((X ^ (3 * m + 1)) +> r)))) := by
  induction m with
  | zero =>
    intro r
    simpa [lb_append_pow_one] using step_B_X_00_def r
  | succ m ih =>
    intro r
    have hidx : 2 * (m + 1) + 1 = (2 * m) + 3 := by omega
    rw [hidx]
    refine stepPlus_trans (drain_X_00_step (2 * m) r) ?_
    have hrest := ih ((X ^ 3) +> r)
    have hexp : (X ^ (3 * m + 1)) +> ((X ^ 3) +> r) = (X ^ (3 * (m + 1) + 1)) +> r := by
      rw [← lb_append_pow_add]
      have : (3 * m + 1) + 3 = 3 * (m + 1) + 1 := by omega
      rw [this]
    rwa [hexp] at hrest

private theorem drain_X_00_even (m : ℕ) :
    ∀ r : zB,
      (default <{{1}} ((X ^ (2 * m + 2)) +> ([0, 0] +> r))) [target_tm]⊢⁺
        (default <{{1}} ((X ^ (3 * m + 4)) +> r)) := by
  induction m with
  | zero =>
    intro r
    exact step_B_X2_00_def r
  | succ m ih =>
    intro r
    have hidx : 2 * (m + 1) + 2 = (2 * m + 1) + 3 := by omega
    rw [hidx]
    refine stepPlus_trans (drain_X_00_step (2 * m + 1) r) ?_
    have hrest := ih ((X ^ 3) +> r)
    have hexp : (X ^ (3 * m + 4)) +> ((X ^ 3) +> r) = (X ^ (3 * (m + 1) + 4)) +> r := by
      rw [← lb_append_pow_add]
      have : (3 * m + 4) + 3 = 3 * (m + 1) + 4 := by omega
      rw [this]
    rwa [hexp] at hrest

/-- One decrement of the inner `Dr` count `b` during the `[1, 1, 0, 1, 1, 1, 0]` drain. -/
private theorem drain_B1_step (a : ℕ) (l r : zB) :
    (((Dr ^ (a + 2)) +> ([1, 1, 0, 1, 1, 1, 0] +> (Dr +> l))) <{{1}} ([0, 0] +> r))
      [target_tm]⊢⁺
    (((Dr ^ a) +> ([1, 1, 0, 1, 1, 1, 0] +> l)) <{{1}} ([0, 0] +> ((X ^ 3) +> r))) := by
  -- Pass 1: p1
  refine stepStar_stepPlus_trans
    (shift_B_Dr (a + 2) ([1, 1, 0, 1, 1, 1, 0] +> (Dr +> l)) ([0, 0] +> r)) ?_
  refine stepPlus_trans (lb_100_p1_base (Dr +> l) ((X ^ (a + 2)) +> ([0, 0] +> r))) ?_
  refine stepStar_stepPlus_trans
    (shift_C_X (a + 2) (Dr +> ([1, 1, 0] +> (Dr +> l))) ([0, 0] +> r)) ?_
  have hc1 : (Dr ^ (a + 2)) +> (Dr +> ([1, 1, 0] +> (Dr +> l))) =
      Dr +> ((Dr ^ (a + 2)) +> ([1, 1, 0] +> (Dr +> l))) := by
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list', Longitudinal.pow_succ_list,
      lb_append_assoc]
  rw [hc1]
  refine stepPlus_trans (step_C_00_Dr ((Dr ^ (a + 2)) +> ([1, 1, 0] +> (Dr +> l))) r) ?_
  -- Pass 2: p2_step
  refine stepStar_stepPlus_trans
    (shift_B_Dr (a + 2) ([1, 1, 0] +> (Dr +> l)) ([0, 0] +> (X +> r))) ?_
  refine stepPlus_trans (lb_100_p2_step_base l ((X ^ (a + 2)) +> ([0, 0] +> (X +> r)))) ?_
  refine stepStar_stepPlus_trans
    (shift_C_X (a + 2) (Dr +> ([1, 0, 0] +> l)) ([0, 0] +> (X +> r))) ?_
  have hc2 : (Dr ^ (a + 2)) +> (Dr +> ([1, 0, 0] +> l)) =
      Dr +> ((Dr ^ (a + 2)) +> ([1, 0, 0] +> l)) := by
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list', Longitudinal.pow_succ_list,
      lb_append_assoc]
  rw [hc2]
  refine stepPlus_trans (step_C_00_Dr ((Dr ^ (a + 2)) +> ([1, 0, 0] +> l)) (X +> r)) ?_
  -- Pass 3: p0
  have hc3 : (Dr ^ (a + 2)) +> ([1, 0, 0] +> l) =
      (Dr ^ (a + 1)) +> (Dr +> ([1, 0, 0] +> l)) := by
    rw [Longitudinal.pow_succ_list', lb_append_assoc]
  rw [hc3]
  refine stepStar_stepPlus_trans
    (shift_B_Dr (a + 1) (Dr +> ([1, 0, 0] +> l)) ([0, 0] +> (X +> (X +> r)))) ?_
  refine stepPlus_trans (lb_100_p0_base l ((X ^ (a + 1)) +> ([0, 0] +> (X +> (X +> r))))) ?_
  refine stepStar_stepPlus_trans
    (shift_C_X (a + 1) ([1, 1, 0, 1, 1, 1, 0] +> l) ([0, 0] +> (X +> (X +> r)))) ?_
  have hc4 : (Dr ^ (a + 1)) +> ([1, 1, 0, 1, 1, 1, 0] +> l) =
      Dr +> ((Dr ^ a) +> ([1, 1, 0, 1, 1, 1, 0] +> l)) := by
    rw [lb_append_pow_succ]
  rw [hc4]
  have hfin := step_C_00_Dr ((Dr ^ a) +> ([1, 1, 0, 1, 1, 1, 0] +> l)) (X +> (X +> r))
  have hr : X +> (X +> (X +> r)) = (X ^ 3) +> r := by
    simp only [Longitudinal.pow_succ_list, Longitudinal.pow_zero_list, List.append_nil,
      lb_append_assoc]
  rwa [hr] at hfin

private theorem drain_B1_base (a : ℕ) (r : zB) :
    (((Dr ^ a) +> ([1, 1, 0, 1, 1, 1, 0] +> ([1] +> default))) <{{1}} ([0, 0] +> r))
      [target_tm]⊢⁺
    (default <{{1}} ((X ^ (a + 2)) +> ([0, 0] +> (X +> r)))) := by
  refine stepStar_stepPlus_trans
    (shift_B_Dr a ([1, 1, 0, 1, 1, 1, 0] +> ([1] +> default)) ([0, 0] +> r)) ?_
  refine stepPlus_trans (lb_100_p1_base ([1] +> default) ((X ^ a) +> ([0, 0] +> r))) ?_
  refine stepStar_stepPlus_trans
    (shift_C_X a (Dr +> ([1, 1, 0] +> ([1] +> default))) ([0, 0] +> r)) ?_
  have h1 : (Dr ^ a) +> (Dr +> ([1, 1, 0] +> ([1] +> default))) =
      Dr +> ((Dr ^ a) +> ([1, 1, 0, 1] +> default)) := by
    rw [← lb_append_assoc, ← Longitudinal.pow_succ_list', Longitudinal.pow_succ_list,
      lb_append_assoc]
    rfl
  rw [h1]
  refine stepPlus_trans (step_C_00_Dr ((Dr ^ a) +> ([1, 1, 0, 1] +> default)) r) ?_
  refine stepStar_stepPlus_trans
    (shift_B_Dr a ([1, 1, 0, 1] +> default) ([0, 0] +> (X +> r))) ?_
  refine stepPlus_trans (step_B_1101_default ((X ^ a) +> ([0, 0] +> (X +> r)))) ?_
  have h2 := step_B_00_def (X +> ((X ^ a) +> ([0, 0] +> (X +> r))))
  have hexp : X +> (X +> ((X ^ a) +> ([0, 0] +> (X +> r)))) =
      (X ^ (a + 2)) +> ([0, 0] +> (X +> r)) := by
    rw [← lb_append_pow_succ, ← lb_append_pow_succ]
  rwa [hexp] at h2

private theorem drain_B1_iter (b : ℕ) :
    ∀ (k : ℕ) (r : zB),
      (((Dr ^ (2 * b + k)) +> ([1, 1, 0, 1, 1, 1, 0] +> ((Dr ^ b) +> ([1] +> default))))
        <{{1}} ([0, 0] +> r)) [target_tm]⊢*
      (((Dr ^ k) +> ([1, 1, 0, 1, 1, 1, 0] +> ([1] +> default)))
        <{{1}} ([0, 0] +> ((X ^ (3 * b)) +> r))) := by
  induction b with
  | zero =>
    intro k r
    simpa using stepStar_refl target_tm _
  | succ b ih =>
    intro k r
    have hidx : 2 * (b + 1) + k = (2 * b + k) + 2 := by omega
    rw [hidx, lb_append_pow_succ]
    refine stepStar_trans
      (stepPlus_to_stepStar (drain_B1_step (2 * b + k) ((Dr ^ b) +> ([1] +> default)) r)) ?_
    have hrest := ih k ((X ^ 3) +> r)
    have hexp : (X ^ (3 * b)) +> ((X ^ 3) +> r) = (X ^ (3 * (b + 1))) +> r := by
      rw [← lb_append_pow_add]
      have : 3 * b + 3 = 3 * (b + 1) := by omega
      rw [this]
    rwa [hexp] at hrest

private theorem drain_B1_full (k b : ℕ) (r : zB) :
    (((Dr ^ (2 * b + (2 * k + 1))) +> ([1, 1, 0, 1, 1, 1, 0] +> ((Dr ^ b) +> ([1] +> default))))
      <{{1}} ([0, 0] +> r)) [target_tm]⊢⁺
    (default <{{1}} (X +> ([0] +> ((X ^ (3 * (k + b + 1) + 2)) +> r)))) := by
  refine stepStar_stepPlus_trans (drain_B1_iter b (2 * k + 1) r) ?_
  refine stepPlus_trans (drain_B1_base (2 * k + 1) ((X ^ (3 * b)) +> r)) ?_
  have h1 : (2 * k + 1) + 2 = 2 * (k + 1) + 1 := by omega
  rw [h1]
  have h2 := drain_X_00_odd (k + 1) (X +> ((X ^ (3 * b)) +> r))
  have hexp : (X ^ (3 * (k + 1) + 1)) +> (X +> ((X ^ (3 * b)) +> r)) =
      (X ^ (3 * (k + b + 1) + 2)) +> r := by
    rw [← lb_append_pow_succ, ← lb_append_pow_add]
    have : (3 * (k + 1) + 1) + (3 * b + 1) = 3 * (k + b + 1) + 2 := by omega
    rw [this]
  rwa [hexp] at h2

-- ============================================================================
-- Section 6: Closed Two-State Invariant `Inv` & Progress Theorem
-- ============================================================================

/--
Recurrent configuration family for BB(6) Holdout `797:#771 / 608:#585`
(`1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD`). -/
inductive Inv : Cfg (Fin 2) (Fin 6) → Prop where
  | normal (d a : ℕ) (r : zB) :
      d ≥ 1 → a ≥ 1 → Wall (3 * d - 1) r →
      Inv (default <{{1}} ((X ^ a) +> r))
  | merging (d q : ℕ) (r : zB) :
      d ≥ 1 → Wall (3 * d - 1) r →
      Inv (default <{{1}} (X +> ([0] +> ((X ^ (3 * q + 2)) +> r))))

/-- Progress from `Inv.normal d a r`. -/
private theorem step_normal {d a : ℕ} {r : zB}
    (hd : d ≥ 1) (ha : a ≥ 1) (hw : Wall (3 * d - 1) r) :
    ∃ c', ((default <{{1}} ((X ^ a) +> r)) [target_tm]⊢⁺ c') ∧ Inv c' := by
  have h1 : (default <{{1}} ((X ^ a) +> r)) [target_tm]⊢⁺
      (((Dr ^ a) +> ([1] +> default)) {{2}}> r) :=
    stepPlus_stepStar_trans (step_B_default_entry ((X ^ a) +> r))
      (shift_C_X a ([1] +> default) r)
  have hm_ne : 3 * d - 1 ≠ 0 := by omega
  -- Left bounces: `3 * (d - 1) + 1` calls of `hfb`
  have hl1 := left_plain_3j (d - 1) (a - 1)
  have hl2 := SideRLs.single (left_p0 (a - 1 + (d - 1)))
  have hl : SideRLs (flipTM target_tm) (hfb ^ (3 * d - 1 - 1))
      ((Dr ^ a) +> ([1] +> default))
      ((Dr ^ (a + d - 2)) +> ([1, 1, 0, 1, 1, 1] +> default)) := by
    have hcomb := hl1.trans_succ hl2
    have hpow : 3 * (d - 1) + 1 = 3 * d - 1 - 1 := by omega
    have hda1 : a - 1 + 1 = a := by omega
    have hda2 : a - 1 + (d - 1) = a + d - 2 := by omega
    simpa [hpow, hda1, hda2] using hcomb
  -- Glue left bounces with `Wall (3 * d - 1) r`
  have hr : SideRLs target_tm (Longitudinal.lrcons (2, []) (hfb ^ (3 * d - 1 - 1)) (1, []))
      r ([0, 0] +> r) := by
    rw [Longitudinal.lrcons_lpow1 (2, []) (1, []) hm_ne]
    exact hw
  have hglue : (((Dr ^ a) +> ([1] +> default)) {{2}}> r) [target_tm]⊢⁺
      (((Dr ^ (a + d - 2)) +> ([1, 1, 0, 1, 1, 1] +> default)) <{{1}} ([0, 0] +> r)) :=
    SideRLs.concat hl hr
  have hmid := stepPlus_trans h1 hglue
  have hdrain := drain_A2 (a + d - 2) r
  have hreach := stepPlus_trans hmid hdrain
  rcases Nat.even_or_odd' (a + d - 2) with ⟨k, hkeq | hko⟩
  · -- `a + d - 2 = 2 * k` (even) -> `Inv.merging d k r`
    have hlen : (a + d - 2) + 1 = 2 * k + 1 := by omega
    rw [hlen] at hreach
    have hfin := drain_X_00_odd k (X +> r)
    have hexp : (X ^ (3 * k + 1)) +> (X +> r) = (X ^ (3 * k + 2)) +> r := by
      rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
    rw [hexp] at hfin
    exact ⟨_, stepPlus_trans hreach hfin, Inv.merging d k r hd hw⟩
  · -- `a + d - 2 = 2 * k + 1` (odd) -> `Inv.normal d (3 * k + 5) r`
    have hlen : (a + d - 2) + 1 = 2 * k + 2 := by omega
    rw [hlen] at hreach
    have hfin := drain_X_00_even k (X +> r)
    have hexp : (X ^ (3 * k + 4)) +> (X +> r) = (X ^ (3 * k + 5)) +> r := by
      rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
    rw [hexp] at hfin
    exact ⟨_, stepPlus_trans hreach hfin, Inv.normal d (3 * k + 5) r hd (by omega) hw⟩

/-- Progress from `Inv.merging d q r`. -/
private theorem step_merging {d q : ℕ} {r : zB}
    (hd : d ≥ 1) (hw : Wall (3 * d - 1) r) :
    ∃ c', ((default <{{1}} (X +> ([0] +> ((X ^ (3 * q + 2)) +> r)))) [target_tm]⊢⁺ c') ∧ Inv c' :=
      by
  rcases Nat.even_or_odd' (d + q) with ⟨s, hs | hs⟩
  · -- `d + q = 2 * s` (even, `s ≥ 1` since `d ≥ 1`) -> merge to `Inv.merging d (q + s + 1) r`
    have hs1 : s ≥ 1 := by omega
    have hsum : (3 * d - 1) + (3 * q + 2) = 2 * (3 * s) + 1 := by omega
    have hodd := wall_cons_odd hw (by omega) hsum
    obtain ⟨r_mid, hr1, hr2⟩ := hodd.split
    -- Enter `(Dr +> [1]) {{2}}> ([0] +> X^(3q+2) +> r)`
    have hentry : (default <{{1}} (X +> ([0] +> ((X ^ (3 * q + 2)) +> r)))) [target_tm]⊢⁺
        ((Dr +> ([1] +> default)) {{2}}> ([0] +> ((X ^ (3 * q + 2)) +> r))) := by
      refine stepPlus_stepStar_trans
        (step_B_default_entry (X +> ([0] +> ((X ^ (3 * q + 2)) +> r)))) ?_
      exact step_C_X_one ([1] +> default) ([0] +> ((X ^ (3 * q + 2)) +> r))
    -- Ping-pong `3 * s` calls of `hf` on `[0] +> X^(3q+2) +> r`
    have hl_ping := left_plain_3j s 0
    have hping : ((Dr +> ([1] +> default)) {{2}}> ([0] +> ((X ^ (3 * q + 2)) +> r))) [target_tm]⊢*
        (((Dr ^ (s + 1)) +> ([1] +> default)) {{2}}> r_mid) := by
      have h := SideRLs.concat_1 hr1 hl_ping
      simpa [lb_append_pow_one, Nat.zero_add] using h
    -- Final `(C, F)` exit
    have hf_exit : (((Dr ^ (s + 1)) +> ([1] +> default)) {{2}}> r_mid) [target_tm]⊢⁺
        (((Dr ^ (s + 1)) +> ([1] +> default)) <{{5}} ([1, 0, 1] +> ((X ^ (3 * q + 2)) +> r))) :=
      hr2.elim_single ((Dr ^ (s + 1)) +> ([1] +> default))
    -- Bounce off `F` back right across `X^(3q+2)`
    have hF : (((Dr ^ (s + 1)) +> ([1] +> default)) <{{5}}
        ([1, 0, 1] +> ((X ^ (3 * q + 2)) +> r))) [target_tm]⊢⁺
        (((Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default)))) {{2}}> r) := by
      rw [lb_append_pow_succ]
      refine stepPlus_stepStar_trans
        (step_F_exit_entry ((Dr ^ s) +> ([1] +> default)) ((X ^ (3 * q + 2)) +> r)) ?_
      have hsh := shift_C_X (3 * q + 2) (Dr +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default)))) r
      have hexp : (Dr ^ (3 * q + 2)) +> (Dr +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default)))) =
          (Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default))) := by
        rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
      rwa [hexp] at hsh
    have hpre : (default <{{1}} (X +> ([0] +> ((X ^ (3 * q + 2)) +> r)))) [target_tm]⊢⁺
        (((Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default)))) {{2}}> r) :=
      stepPlus_trans (stepPlus_stepStar_trans hentry hping) (stepPlus_trans hf_exit hF)
    -- Feed `Wall (3 * d - 1) r` (`3 * (d - 1) + 1` left bounces of `[1, 0, 0]` counter)
    have hm_ne : 3 * d - 1 ≠ 0 := by omega
    have hr_wall : SideRLs target_tm (Longitudinal.lrcons (2, []) (hfb ^ (3 * d - 1 - 1)) (1, []))
        r ([0, 0] +> r) := by
      rw [Longitudinal.lrcons_lpow1 (2, []) (1, []) hm_ne]
      exact hw
    rcases Nat.lt_or_ge (d - 1) (s + 1) with hle | hgt
    · -- Subcase B1: `d - 1 ≤ s`
      let t := d - 1
      let b := s - t
      have hs_eq : s = t + b := by omega
      have h3t := left100_3t t (3 * q + 2) ((Dr ^ b) +> ([1] +> default))
      have h1p := SideRLs.single (left100_p0 (3 * q + 2 + t) ((Dr ^ b) +> ([1] +> default)))
      have hleft : SideRLs (flipTM target_tm) (hfb ^ (3 * d - 1 - 1))
          ((Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default))))
          ((Dr ^ (3 * q + 2 + t)) +> ([1, 1, 0, 1, 1, 1, 0] +> ((Dr ^ b) +> ([1] +> default)))) :=
            by
        have hcomb := h3t.trans_succ h1p
        have hpow : 3 * t + 1 = 3 * d - 1 - 1 := by omega
        have hDr : (Dr ^ t) +> ((Dr ^ b) +> ([1] +> default)) =
            (Dr ^ s) +> ([1] +> default) := by
          rw [← lb_append_pow_add, ← hs_eq]
        have h3q : (3 * q + 2) + 1 = 3 * q + 3 := by omega
        rw [hpow, hDr, h3q] at hcomb
        exact hcomb
      have hglue : (((Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default)))) {{2}}> r)
          [target_tm]⊢⁺
          (((Dr ^ (3 * q + 2 + t)) +> ([1, 1, 0, 1, 1, 1, 0] +> ((Dr ^ b) +> ([1] +> default))))
            <{{1}} ([0, 0] +> r)) :=
        SideRLs.concat hleft hr_wall
      let k := q + s - b
      have hb_le : b ≤ q + s := by omega
      have ha_eq : 3 * q + 2 + t = 2 * b + (2 * k + 1) := by omega
      have hkb : k + b + 1 = q + s + 1 := by omega
      rw [ha_eq] at hglue
      have hdrain := drain_B1_full k b r
      rw [hkb] at hdrain
      exact ⟨_, stepPlus_trans (stepPlus_trans hpre hglue) hdrain,
        Inv.merging d (q + s + 1) r hd hw⟩
    · -- Subcase B2: `s < d - 1`
      let j := (d - 1) - (s + 1)
      have hds : d - 1 = s + 1 + j := by omega
      have h3s := left100_3t s (3 * q + 2) ([1] +> default)
      have hbase := left100_3_base (3 * q + 2 + s)
      have hplain := left_plain_3j j (3 * q + 4 + s)
      have hp0 := SideRLs.single (left_p0 (3 * q + 4 + s + j))
      have hleft : SideRLs (flipTM target_tm) (hfb ^ (3 * d - 1 - 1))
          ((Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default))))
          ((Dr ^ (3 * q + 4 + s + j)) +> ([1, 1, 0, 1, 1, 1] +> default)) := by
        have h12 := h3s.trans_add hbase
        have hexp1 : 3 * q + 2 + s + 3 = (3 * q + 4 + s) + 1 := by omega
        rw [hexp1] at h12
        have h123 := h12.trans_add hplain
        have h1234 := h123.trans_succ hp0
        have hpow : 3 * s + 3 + 3 * j + 1 = 3 * d - 1 - 1 := by omega
        have h3q : 3 * q + 2 + 1 = 3 * q + 3 := by omega
        simpa [hpow, h3q] using h1234
      have hglue : (((Dr ^ (3 * q + 3)) +> ([1, 0, 0] +> ((Dr ^ s) +> ([1] +> default)))) {{2}}> r)
          [target_tm]⊢⁺
          (((Dr ^ (3 * q + 4 + s + j)) +> ([1, 1, 0, 1, 1, 1] +> default))
            <{{1}} ([0, 0] +> r)) :=
        SideRLs.concat hleft hr_wall
      have hu_eq : 3 * q + 4 + s + j = 2 * (q + s + 1) := by omega
      rw [hu_eq] at hglue
      have hdrain := drain_A2 (2 * (q + s + 1)) r
      have hfin := drain_X_00_odd (q + s + 1) (X +> r)
      have hexp : (X ^ (3 * (q + s + 1) + 1)) +> (X +> r) =
          (X ^ (3 * (q + s + 1) + 2)) +> r := by
        rw [← lb_append_assoc, ← Longitudinal.pow_succ_list']
      rw [hexp] at hfin
      exact ⟨_, stepPlus_trans (stepPlus_trans hpre hglue) (stepPlus_trans hdrain hfin),
        Inv.merging d (q + s + 1) r hd hw⟩
  · -- `d + q = 2 * s + 1` (odd) -> freezes into `Wall (3 * (s + 1) - 1) ([0] +> X^(3*q+2) +> r)`!
    let r' : zB := [0] +> ((X ^ (3 * q + 2)) +> r)
    have hsum : (3 * d - 1) + (3 * q + 2) = 2 * (3 * (s + 1) - 1) := by omega
    have hw' : Wall (3 * (s + 1) - 1) r' := wall_cons_even hw (by omega) hsum
    have hcfg : (default <{{1}} (X +> r') : Cfg (Fin 2) (Fin 6)) =
        (default <{{1}} ((X ^ 1) +> r')) := by
      rw [lb_append_pow_one]
    rw [hcfg]
    exact step_normal (by omega) (by omega) hw'

private theorem inv_progress (c : Cfg (Fin 2) (Fin 6)) (hc : Inv c) :
    ∃ c', (c [target_tm]⊢⁺ c') ∧ Inv c' := by
  cases hc with
  | normal d a r hd ha hw => exact step_normal hd ha hw
  | merging d q r hd hw => exact step_merging hd hw

-- ============================================================================
-- Section 7: Blank-Tape Reachability (`init [] ⊢* Inv`)
-- ============================================================================

private theorem init_to_X2 :
    (init []) [target_tm]⊢* (default <{{1}} ((X ^ 2) +> default)) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{0}}> default) := rfl
  rw [h0]
  change (default {{0}}> default) [target_tm]⊢* (default <{{1}} (X +> (X +> default)))
  dsimp [X]
  bb_steps

private theorem init_reaches_inv :
    ∃ c₀, ((init []) [target_tm]⊢* c₀) ∧ Inv c₀ := by
  have h1 : (default <{{1}} ((X ^ 2) +> default)) [target_tm]⊢⁺
      (default <{{1}} ((X ^ 4) +> default)) := by
    have h := step_B_X2_00_def (default : zB)
    rwa [lb_append_00_default] at h
  have h2 : (default <{{1}} ((X ^ 4) +> default)) [target_tm]⊢⁺
      (default <{{1}} ((X ^ 7) +> default)) := by
    have h := drain_X_00_even 1 (default : zB)
    rwa [lb_append_00_default] at h
  have h3 : (default <{{1}} ((X ^ 7) +> default)) [target_tm]⊢⁺
      (default <{{1}} (X +> ([0] +> ((X ^ 10) +> default)))) := by
    have h := drain_X_00_odd 3 (default : zB)
    rwa [lb_append_00_default] at h
  have hw5 : Wall 5 ([0] +> ((X ^ 10) +> default)) :=
    wall_cons_even wall_zero_default (by decide) (by decide)
  have hinv : Inv (default <{{1}} ((X ^ 1) +> ([0] +> ((X ^ 10) +> default)))) :=
    Inv.normal 2 1 ([0] +> ((X ^ 10) +> default)) (by decide) (by decide) hw5
  refine ⟨default <{{1}} (X +> ([0] +> ((X ^ 10) +> default))), ?_, ?_⟩
  · exact stepStar_trans init_to_X2
      (stepPlus_to_stepStar (stepPlus_trans h1 (stepPlus_trans h2 h3)))
  · rw [lb_append_pow_one] at hinv
    exact hinv

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  obtain ⟨c₀, hinit, h0⟩ := init_reaches_inv
  exact IsNotHalt.of_reachesPlus_invariant hinit h0 inv_progress


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD
