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
import BusyBeaver.Calculi.PairStackA
import BusyBeaver.Calculi.PairStackB

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 0 Dir.left)


open BusyBeaver.Calculi.PairStackB

/-! ## Exact 12/12 Mirrored E1 Conjugacy (`tm484 → tm689`) & `W19` Entry -/

private def tm689 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 0 Dir.left)

private def perm689 : Fin 6 → Fin 6
  | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5

private def mirrorTape (T : Tape (Fin 2)) : Tape (Fin 2) :=
  ⟨T.head, T.right, T.left⟩

private def mapCfg689 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map perm689, mirrorTape c.tape⟩

private theorem step_iso_689 (c : Cfg (Fin 2) (Fin 6)) :
    step tm689 (mapCfg689 c) = (step tm484 c).map mapCfg689 := by
  rcases c with ⟨q, T⟩
  cases q with
  | none => rfl
  | some q =>
    rcases T with ⟨hd, l, r⟩
    match q, hd with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
    | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

private theorem multiStep_map_iso_689 (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep tm689 (mapCfg689 c) n = (multiStep tm484 c n).map mapCfg689 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ, multiStep_succ, step_iso_689 c]
    cases step tm484 c with
    | none => rfl
    | some c' => exact ih c'

private def start689 : State484 := ⟨.mC0, [], []⟩

private def enc689 (s : State484) : Cfg (Fin 2) (Fin 6) := mapCfg689 (enc484 s)

private theorem tm689_entry : init ([] : List (Fin 2)) = enc689 start689 := by
  simp only [init, enc689, mapCfg689, mirrorTape, enc484, start689, encStack]
  rfl

private theorem isNotHalt_of_orbit_safe_689
    (hsafe : ∀ n : ℕ, isDoor (stepTot^[n] start689) = false) :
    IsNotHalt tm689 := by
  intro cfg hreach
  rcases hreach with ⟨m, hm⟩
  rw [tm689_entry] at hm
  obtain ⟨t, ht, hmt⟩ := multiStep_ge_of_orbit_safe start689 hsafe (m + 1)
  have hmt' : multiStep tm689 (enc689 start689) t = some (enc689 (stepTot^[m + 1] start689)) := by
    rw [enc689, multiStep_map_iso_689, hmt]; rfl
  have hdiff : t = m + ((t - m - 1) + 1) := by omega
  rw [hdiff, multiStep_add_eq m ((t - m - 1) + 1), hm, Option.bind_some] at hmt'
  exact isSome_step_of_multiStep_succ hmt'

private def entry689 : State484 :=
  ⟨.mAL, [(2, false)], [(1, false), (1, false), (2, false), (1, false), (1, false), (1, false), (1,
      false), (2, false), (1, false), (1, false), (1, false), (1, false), (2, false), (0, true), (1,
      true), (1, false), (1, false), (1, false), (2, false)]⟩

private def s689_1 : State484 :=
  ⟨.mAL, [(1, false), (0, false), (4, false)], [(1, false)]⟩
private def s689_2 : State484 :=
  ⟨.mC0, [(0, false), (5, false), (1, false)], [(0, false), (0, true), (0, false)]⟩
private def s689_3 : State484 :=
  ⟨.mAL, [(0, false), (1, false), (1, false), (3, false), (4, false)], [(0, true), (0, false)]⟩
private def s689_4 : State484 :=
  ⟨.mC0, [(1, false), (3, false), (4, false)], [(0, false), (1, false), (1, false), (2, false)]⟩
private def s689_5 : State484 :=
  ⟨.mBR, [(3, false), (1, false), (1, false), (0, false), (7, false)], [(3, false), (0, true), (0,
      false)]⟩
private def s689_6 : State484 :=
  ⟨.mD0, [(2, false), (1, false)], [(1, false), (1, false), (1, true), (0, true), (1, false), (1,
      false), (1, false), (2, false)]⟩
private def s689_7 : State484 :=
  ⟨.mAL, [(1, false), (1, false), (0, false), (0, false), (1, false), (3, false), (1, false)], [(2,
      false), (1, false), (1, false), (2, false)]⟩
private def s689_8 : State484 :=
  ⟨.mD0, [(0, false), (3, false), (1, false)], [(2, false), (1, false), (1, true), (2, false), (1,
      false), (1, false), (2, false)]⟩
private def s689_9 : State484 :=
  ⟨.mD0, [(0, false), (3, false), (3, false), (3, false), (1, false), (0, false), (3, false), (1,
      false), (3, false), (1, false)], []⟩
private def s689_10 : State484 :=
  ⟨.mD0, [(0, false), (1, false), (1, false), (1, false), (0, false), (4, false), (0, false), (3,
      false), (1, false), (3, false), (1, false)], [(2, false)]⟩
private def s689_11 : State484 :=
  ⟨.mAL, [(10, false), (1, false), (1, false), (0, false), (4, false), (0, false), (3, false), (1,
      false), (3, false), (1, false)], [(2, false)]⟩
private def s689_12 : State484 :=
  ⟨.mAL, [(1, false), (0, false), (5, false), (3, false), (1, false), (3, false), (1, false)], [(1,
      false), (1, true), (1, false), (1, false), (1, false), (2, false)]⟩
private def s689_13 : State484 :=
  ⟨.mD0, [(2, false), (2, false), (3, false), (1, false), (3, false), (6, false), (1, false), (3,
      false), (1, false)], [(1, false), (2, false)]⟩
private def s689_14 : State484 :=
  ⟨.mC0, [(12, false), (2, false), (3, false), (1, false), (3, false), (6, false), (1, false), (3,
      false), (1, false)], [(1, false)]⟩
private def s689_15 : State484 :=
  ⟨.mAL, [(1, false), (3, false), (3, false), (3, false), (5, false), (3, false), (1, false), (3,
      false), (6, false), (1, false), (3, false), (1, false)], [(0, false)]⟩
private def s689_16 : State484 :=
  ⟨.mDR, [(0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (0, false), (8,
      false), (3, false), (1, false), (3, false), (6, false), (1, false), (3, false), (1,
      false)], []⟩
private def s689_17 : State484 :=
  ⟨.mAL, [(7, false), (1, false), (1, false), (0, false), (8, false), (3, false), (1, false), (3,
      false), (6, false), (1, false), (3, false), (1, false)], [(1, false), (2, false)]⟩
private def s689_18 : State484 :=
  ⟨.mBR, [(6, false), (1, false), (3, false), (6, false), (1, false), (3, false), (1, false)], [(3,
      false), (0, true), (0, true), (0, true), (1, true), (1, false), (1, false), (1, false), (2,
      false)]⟩
private def s689_19 : State484 :=
  ⟨.mBR, [(11, false), (1, false), (3, false), (1, false)], [(0, true), (1, false), (1, false), (1,
      false), (1, false), (1, false), (2, false), (0, true), (1, true), (1, false), (1, false), (1,
      false), (2, false)]⟩

private theorem run689_0 : runTot 40 start689 = s689_1 := rfl
private theorem run689_1 : runTot 40 s689_1 = s689_2 := rfl
private theorem run689_2 : runTot 40 s689_2 = s689_3 := rfl
private theorem run689_3 : runTot 40 s689_3 = s689_4 := rfl
private theorem run689_4 : runTot 40 s689_4 = s689_5 := rfl
private theorem run689_5 : runTot 40 s689_5 = s689_6 := rfl
private theorem run689_6 : runTot 40 s689_6 = s689_7 := rfl
private theorem run689_7 : runTot 40 s689_7 = s689_8 := rfl
private theorem run689_8 : runTot 40 s689_8 = s689_9 := rfl
private theorem run689_9 : runTot 40 s689_9 = s689_10 := rfl
private theorem run689_10 : runTot 40 s689_10 = s689_11 := rfl
private theorem run689_11 : runTot 40 s689_11 = s689_12 := rfl
private theorem run689_12 : runTot 40 s689_12 = s689_13 := rfl
private theorem run689_13 : runTot 40 s689_13 = s689_14 := rfl
private theorem run689_14 : runTot 40 s689_14 = s689_15 := rfl
private theorem run689_15 : runTot 40 s689_15 = s689_16 := rfl
private theorem run689_16 : runTot 40 s689_16 = s689_17 := rfl
private theorem run689_17 : runTot 40 s689_17 = s689_18 := rfl
private theorem run689_18 : runTot 40 s689_18 = s689_19 := rfl
private theorem run689_19 : runTot 34 s689_19 = entry689 := rfl

private theorem safe689_0 : safePrefix 40 start689 = true := rfl
private theorem safe689_1 : safePrefix 40 s689_1 = true := rfl
private theorem safe689_2 : safePrefix 40 s689_2 = true := rfl
private theorem safe689_3 : safePrefix 40 s689_3 = true := rfl
private theorem safe689_4 : safePrefix 40 s689_4 = true := rfl
private theorem safe689_5 : safePrefix 40 s689_5 = true := rfl
private theorem safe689_6 : safePrefix 40 s689_6 = true := rfl
private theorem safe689_7 : safePrefix 40 s689_7 = true := rfl
private theorem safe689_8 : safePrefix 40 s689_8 = true := rfl
private theorem safe689_9 : safePrefix 40 s689_9 = true := rfl
private theorem safe689_10 : safePrefix 40 s689_10 = true := rfl
private theorem safe689_11 : safePrefix 40 s689_11 = true := rfl
private theorem safe689_12 : safePrefix 40 s689_12 = true := rfl
private theorem safe689_13 : safePrefix 40 s689_13 = true := rfl
private theorem safe689_14 : safePrefix 40 s689_14 = true := rfl
private theorem safe689_15 : safePrefix 40 s689_15 = true := rfl
private theorem safe689_16 : safePrefix 40 s689_16 = true := rfl
private theorem safe689_17 : safePrefix 40 s689_17 = true := rfl
private theorem safe689_18 : safePrefix 40 s689_18 = true := rfl
private theorem safe689_19 : safePrefix 34 s689_19 = true := rfl

private theorem tm689_reaches_entry : stepTot^[794] start689 = entry689 := by
  rw [← runTot_eq_iterate]
  have hr_1 : runTot 80 start689 = s689_2 := by
    change runTot (40 + 40) start689 = s689_2
    rw [runTot_add, run689_0, run689_1]
  have hr_2 : runTot 120 start689 = s689_3 := by
    change runTot (80 + 40) start689 = s689_3
    rw [runTot_add, hr_1, run689_2]
  have hr_3 : runTot 160 start689 = s689_4 := by
    change runTot (120 + 40) start689 = s689_4
    rw [runTot_add, hr_2, run689_3]
  have hr_4 : runTot 200 start689 = s689_5 := by
    change runTot (160 + 40) start689 = s689_5
    rw [runTot_add, hr_3, run689_4]
  have hr_5 : runTot 240 start689 = s689_6 := by
    change runTot (200 + 40) start689 = s689_6
    rw [runTot_add, hr_4, run689_5]
  have hr_6 : runTot 280 start689 = s689_7 := by
    change runTot (240 + 40) start689 = s689_7
    rw [runTot_add, hr_5, run689_6]
  have hr_7 : runTot 320 start689 = s689_8 := by
    change runTot (280 + 40) start689 = s689_8
    rw [runTot_add, hr_6, run689_7]
  have hr_8 : runTot 360 start689 = s689_9 := by
    change runTot (320 + 40) start689 = s689_9
    rw [runTot_add, hr_7, run689_8]
  have hr_9 : runTot 400 start689 = s689_10 := by
    change runTot (360 + 40) start689 = s689_10
    rw [runTot_add, hr_8, run689_9]
  have hr_10 : runTot 440 start689 = s689_11 := by
    change runTot (400 + 40) start689 = s689_11
    rw [runTot_add, hr_9, run689_10]
  have hr_11 : runTot 480 start689 = s689_12 := by
    change runTot (440 + 40) start689 = s689_12
    rw [runTot_add, hr_10, run689_11]
  have hr_12 : runTot 520 start689 = s689_13 := by
    change runTot (480 + 40) start689 = s689_13
    rw [runTot_add, hr_11, run689_12]
  have hr_13 : runTot 560 start689 = s689_14 := by
    change runTot (520 + 40) start689 = s689_14
    rw [runTot_add, hr_12, run689_13]
  have hr_14 : runTot 600 start689 = s689_15 := by
    change runTot (560 + 40) start689 = s689_15
    rw [runTot_add, hr_13, run689_14]
  have hr_15 : runTot 640 start689 = s689_16 := by
    change runTot (600 + 40) start689 = s689_16
    rw [runTot_add, hr_14, run689_15]
  have hr_16 : runTot 680 start689 = s689_17 := by
    change runTot (640 + 40) start689 = s689_17
    rw [runTot_add, hr_15, run689_16]
  have hr_17 : runTot 720 start689 = s689_18 := by
    change runTot (680 + 40) start689 = s689_18
    rw [runTot_add, hr_16, run689_17]
  have hr_18 : runTot 760 start689 = s689_19 := by
    change runTot (720 + 40) start689 = s689_19
    rw [runTot_add, hr_17, run689_18]
  have hr_19 : runTot 794 start689 = entry689 := by
    change runTot (760 + 34) start689 = entry689
    rw [runTot_add, hr_18, run689_19]
  exact hr_19

private theorem tm689_safe_prefix : ∀ j < 794, isDoor (stepTot^[j] start689) = false := by
  have hs_0 : ∀ j < 40, isDoor (stepTot^[j] start689) = false :=
    safePrefix_sound 40 start689 safe689_0
  have hr_1 : runTot 80 start689 = s689_2 := by
    change runTot (40 + 40) start689 = s689_2
    rw [runTot_add, run689_0, run689_1]
  have hs_1 : ∀ j < 80, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_1 40 40 run689_0 hs_0 (safePrefix_sound 40 s689_1 safe689_1)
  have hr_2 : runTot 120 start689 = s689_3 := by
    change runTot (80 + 40) start689 = s689_3
    rw [runTot_add, hr_1, run689_2]
  have hs_2 : ∀ j < 120, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_2 80 40 hr_1 hs_1 (safePrefix_sound 40 s689_2 safe689_2)
  have hr_3 : runTot 160 start689 = s689_4 := by
    change runTot (120 + 40) start689 = s689_4
    rw [runTot_add, hr_2, run689_3]
  have hs_3 : ∀ j < 160, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_3 120 40 hr_2 hs_2 (safePrefix_sound 40 s689_3 safe689_3)
  have hr_4 : runTot 200 start689 = s689_5 := by
    change runTot (160 + 40) start689 = s689_5
    rw [runTot_add, hr_3, run689_4]
  have hs_4 : ∀ j < 200, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_4 160 40 hr_3 hs_3 (safePrefix_sound 40 s689_4 safe689_4)
  have hr_5 : runTot 240 start689 = s689_6 := by
    change runTot (200 + 40) start689 = s689_6
    rw [runTot_add, hr_4, run689_5]
  have hs_5 : ∀ j < 240, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_5 200 40 hr_4 hs_4 (safePrefix_sound 40 s689_5 safe689_5)
  have hr_6 : runTot 280 start689 = s689_7 := by
    change runTot (240 + 40) start689 = s689_7
    rw [runTot_add, hr_5, run689_6]
  have hs_6 : ∀ j < 280, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_6 240 40 hr_5 hs_5 (safePrefix_sound 40 s689_6 safe689_6)
  have hr_7 : runTot 320 start689 = s689_8 := by
    change runTot (280 + 40) start689 = s689_8
    rw [runTot_add, hr_6, run689_7]
  have hs_7 : ∀ j < 320, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_7 280 40 hr_6 hs_6 (safePrefix_sound 40 s689_7 safe689_7)
  have hr_8 : runTot 360 start689 = s689_9 := by
    change runTot (320 + 40) start689 = s689_9
    rw [runTot_add, hr_7, run689_8]
  have hs_8 : ∀ j < 360, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_8 320 40 hr_7 hs_7 (safePrefix_sound 40 s689_8 safe689_8)
  have hr_9 : runTot 400 start689 = s689_10 := by
    change runTot (360 + 40) start689 = s689_10
    rw [runTot_add, hr_8, run689_9]
  have hs_9 : ∀ j < 400, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_9 360 40 hr_8 hs_8 (safePrefix_sound 40 s689_9 safe689_9)
  have hr_10 : runTot 440 start689 = s689_11 := by
    change runTot (400 + 40) start689 = s689_11
    rw [runTot_add, hr_9, run689_10]
  have hs_10 : ∀ j < 440, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_10 400 40 hr_9 hs_9 (safePrefix_sound 40 s689_10 safe689_10)
  have hr_11 : runTot 480 start689 = s689_12 := by
    change runTot (440 + 40) start689 = s689_12
    rw [runTot_add, hr_10, run689_11]
  have hs_11 : ∀ j < 480, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_11 440 40 hr_10 hs_10 (safePrefix_sound 40 s689_11 safe689_11)
  have hr_12 : runTot 520 start689 = s689_13 := by
    change runTot (480 + 40) start689 = s689_13
    rw [runTot_add, hr_11, run689_12]
  have hs_12 : ∀ j < 520, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_12 480 40 hr_11 hs_11 (safePrefix_sound 40 s689_12 safe689_12)
  have hr_13 : runTot 560 start689 = s689_14 := by
    change runTot (520 + 40) start689 = s689_14
    rw [runTot_add, hr_12, run689_13]
  have hs_13 : ∀ j < 560, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_13 520 40 hr_12 hs_12 (safePrefix_sound 40 s689_13 safe689_13)
  have hr_14 : runTot 600 start689 = s689_15 := by
    change runTot (560 + 40) start689 = s689_15
    rw [runTot_add, hr_13, run689_14]
  have hs_14 : ∀ j < 600, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_14 560 40 hr_13 hs_13 (safePrefix_sound 40 s689_14 safe689_14)
  have hr_15 : runTot 640 start689 = s689_16 := by
    change runTot (600 + 40) start689 = s689_16
    rw [runTot_add, hr_14, run689_15]
  have hs_15 : ∀ j < 640, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_15 600 40 hr_14 hs_14 (safePrefix_sound 40 s689_15 safe689_15)
  have hr_16 : runTot 680 start689 = s689_17 := by
    change runTot (640 + 40) start689 = s689_17
    rw [runTot_add, hr_15, run689_16]
  have hs_16 : ∀ j < 680, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_16 640 40 hr_15 hs_15 (safePrefix_sound 40 s689_16 safe689_16)
  have hr_17 : runTot 720 start689 = s689_18 := by
    change runTot (680 + 40) start689 = s689_18
    rw [runTot_add, hr_16, run689_17]
  have hs_17 : ∀ j < 720, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_17 680 40 hr_16 hs_16 (safePrefix_sound 40 s689_17 safe689_17)
  have hr_18 : runTot 760 start689 = s689_19 := by
    change runTot (720 + 40) start689 = s689_19
    rw [runTot_add, hr_17, run689_18]
  have hs_18 : ∀ j < 760, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_18 720 40 hr_17 hs_17 (safePrefix_sound 40 s689_18 safe689_18)
  have hs_19 : ∀ j < 794, isDoor (stepTot^[j] start689) = false :=
    safePrefix_chunks start689 s689_19 760 34 hr_18 hs_18 (safePrefix_sound 34 s689_19 safe689_19)
  exact hs_19

/-- Direct `IsNotHalt tm689` corollary for `1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA`, connecting
`tm689_reaches_entry`
(`entry689 = ⟨.mAL, [(2, false)], (1, false) :: S689⟩`) to any `EvalF`-closed predicate `W`
containing `W₂ ++ tail689`. -/
private theorem isNotHalt_689_of_evalF_W_closed
    (W : List (ℕ × Bool) → Prop)
    (hW : ∀ n S Δ Z, EvalF n ((3, false) :: S) Δ Z →
      StrictNo0F ((3, false) :: S) → W ((3, false) :: S) →
      (Δ = 7 ∧ W ((3, false) :: (1, false) :: Z)) ∨
      (Δ = 10 ∧ W ((3, false) :: (1, false) :: (1, false) :: Z)))
    (hW2 : W [(3, false), (1, false), (2, false), (1, false), (1, false), (1, false), (1, false),
        (2, false), (1, false), (1, false), (1, false), (1, false), (2, false), (0, true), (1,
        true), (1, false), (1, false), (1, false), (2, false)]) :
    IsNotHalt tm689 := by
  have hS : StrictNo0F [(1, false), (2, false), (1, false), (1, false), (1, false), (1, false), (2,
      false), (1, false), (1, false), (1, false), (1, false), (2, false), (0, true), (1, true), (1,
      false), (1, false), (1, false), (2, false)] := trivial
  have hwall : ∀ k : ℕ, isDoor (stepTot^[k] entry689) = false :=
    orbit_safe_of_evalF_W_closed W hW
      [(1, false), (2, false), (1, false), (1, false), (1, false), (1, false), (2, false), (1,
          false), (1, false), (1, false), (1, false), (2, false), (0, true), (1, true), (1,
          false), (1, false), (1, false), (2, false)] hS hW2
  refine isNotHalt_of_orbit_safe_689 ?_
  intro n
  rcases Nat.lt_or_ge n 794 with hlt | hge
  · exact tm689_safe_prefix n hlt
  · have hsplit : n = 794 + (n - 794) := by omega
    rw [hsplit, stepTot_iter_add, tm689_reaches_entry]
    exact hwall (n - 794)

private theorem target_tm_eq_local : target_tm = tm689 := by
  funext s b
  match s, b with
  | 0, 0 => rfl | 0, 1 => rfl | 1, 0 => rfl | 1, 1 => rfl
  | 2, 0 => rfl | 2, 1 => rfl | 3, 0 => rfl | 3, 1 => rfl
  | 4, 0 => rfl | 4, 1 => rfl | 5, 0 => rfl | 5, 1 => rfl


private theorem is_does_not_halt : IsNotHalt target_tm := by
  rw [target_tm_eq_local]
  exact isNotHalt_689_of_evalF_W_closed W_closed W_closed_step (Or.inl ⟨_, rfl,
      BusyBeaver.Calculi.PairStackA.strong2_of_2_1_1 _⟩)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA
