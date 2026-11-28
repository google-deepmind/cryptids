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

namespace BusyBeaver.M_1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 1, Stmt.write 0 Dir.left)


open BusyBeaver.Calculi.PairStackB

/-! ## Exact 12/12 Mirrored E1 Conjugacy (`tm484 → tm505`) & `W19` Entry -/

private def tm505 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 1, Stmt.write 0 Dir.left)

private def perm505 : Fin 6 → Fin 6
  | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5

private def mirrorTape (T : Tape (Fin 2)) : Tape (Fin 2) :=
  ⟨T.head, T.right, T.left⟩

private def mapCfg505 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map perm505, mirrorTape c.tape⟩

private theorem step_iso_505 (c : Cfg (Fin 2) (Fin 6)) :
    step tm505 (mapCfg505 c) = (step tm484 c).map mapCfg505 := by
  rcases c with ⟨q, T⟩
  cases q with
  | none => rfl
  | some q =>
    rcases T with ⟨hd, l, r⟩
    match q, hd with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
    | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

private theorem multiStep_map_iso_505 (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep tm505 (mapCfg505 c) n = (multiStep tm484 c n).map mapCfg505 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ, multiStep_succ, step_iso_505 c]
    cases step tm484 c with
    | none => rfl
    | some c' => exact ih c'

private def start505 : State484 := ⟨.mBR, [], []⟩

private def enc505 (s : State484) : Cfg (Fin 2) (Fin 6) := mapCfg505 (enc484 s)

private theorem tm505_entry : init ([] : List (Fin 2)) = enc505 start505 := by
  simp only [init, enc505, mapCfg505, mirrorTape, enc484, start505, encStack,
    Cfg.headRight, default_head, default_tail]
  rfl

private theorem isNotHalt_of_orbit_safe_505
    (hsafe : ∀ n : ℕ, isDoor (stepTot^[n] start505) = false) :
    IsNotHalt tm505 := by
  intro cfg hreach
  rcases hreach with ⟨m, hm⟩
  rw [tm505_entry] at hm
  obtain ⟨t, ht, hmt⟩ := multiStep_ge_of_orbit_safe start505 hsafe (m + 1)
  have hmt' : multiStep tm505 (enc505 start505) t = some (enc505 (stepTot^[m + 1] start505)) := by
    rw [enc505, multiStep_map_iso_505, hmt]; rfl
  have hdiff : t = m + ((t - m - 1) + 1) := by omega
  rw [hdiff, multiStep_add_eq m ((t - m - 1) + 1), hm, Option.bind_some] at hmt'
  exact isSome_step_of_multiStep_succ hmt'

private def entry505 : State484 :=
  ⟨.mAL, [(2, false)], [(1, false), (1, false), (1, false), (2, false), (0, true), (2, false), (1,
      false), (1, false), (2, false)]⟩

private def s505_1 : State484 :=
  ⟨.mDR, [(5, false)], [(2, false), (0, false)]⟩
private def s505_2 : State484 :=
  ⟨.mE1, [(1, false)], [(1, false), (0, true), (0, true), (0, true), (0, false)]⟩
private def s505_3 : State484 :=
  ⟨.mBR, [(2, false), (1, false), (3, false), (1, false)], [(0, true), (1, false)]⟩
private def s505_4 : State484 :=
  ⟨.mDR, [(0, false), (1, false), (3, false), (1, false)], [(0, false), (1, false), (2, false)]⟩
private def s505_5 : State484 :=
  ⟨.mBR, [(1, false), (0, false), (3, false), (5, false), (1, false)], [(0, false), (1, false)]⟩
private def s505_6 : State484 :=
  ⟨.mDR, [(8, false), (1, false)], [(0, false), (0, true), (1, false), (1, false), (2, false)]⟩
private def s505_7 : State484 :=
  ⟨.mD0, [(0, false), (0, false), (6, false), (1, false), (0, false), (8, false), (1, false)], [(0,
      false)]⟩
private def s505_8 : State484 :=
  ⟨.mBR, [(3, false)], [(1, false), (1, false), (1, false), (1, false), (1, true), (1, false), (1,
      false), (1, false), (2, false)]⟩

private theorem run505_0 : runTot 35 start505 = s505_1 := rfl
private theorem run505_1 : runTot 35 s505_1 = s505_2 := rfl
private theorem run505_2 : runTot 35 s505_2 = s505_3 := rfl
private theorem run505_3 : runTot 35 s505_3 = s505_4 := rfl
private theorem run505_4 : runTot 35 s505_4 = s505_5 := rfl
private theorem run505_5 : runTot 35 s505_5 = s505_6 := rfl
private theorem run505_6 : runTot 35 s505_6 = s505_7 := rfl
private theorem run505_7 : runTot 35 s505_7 = s505_8 := rfl
private theorem run505_8 : runTot 35 s505_8 = entry505 := rfl

private theorem safe505_0 : safePrefix 35 start505 = true := rfl
private theorem safe505_1 : safePrefix 35 s505_1 = true := rfl
private theorem safe505_2 : safePrefix 35 s505_2 = true := rfl
private theorem safe505_3 : safePrefix 35 s505_3 = true := rfl
private theorem safe505_4 : safePrefix 35 s505_4 = true := rfl
private theorem safe505_5 : safePrefix 35 s505_5 = true := rfl
private theorem safe505_6 : safePrefix 35 s505_6 = true := rfl
private theorem safe505_7 : safePrefix 35 s505_7 = true := rfl
private theorem safe505_8 : safePrefix 35 s505_8 = true := rfl

private theorem tm505_reaches_entry : stepTot^[315] start505 = entry505 := by
  rw [← runTot_eq_iterate]
  have hr_1 : runTot 70 start505 = s505_2 := by
    change runTot (35 + 35) start505 = s505_2
    rw [runTot_add, run505_0, run505_1]
  have hr_2 : runTot 105 start505 = s505_3 := by
    change runTot (70 + 35) start505 = s505_3
    rw [runTot_add, hr_1, run505_2]
  have hr_3 : runTot 140 start505 = s505_4 := by
    change runTot (105 + 35) start505 = s505_4
    rw [runTot_add, hr_2, run505_3]
  have hr_4 : runTot 175 start505 = s505_5 := by
    change runTot (140 + 35) start505 = s505_5
    rw [runTot_add, hr_3, run505_4]
  have hr_5 : runTot 210 start505 = s505_6 := by
    change runTot (175 + 35) start505 = s505_6
    rw [runTot_add, hr_4, run505_5]
  have hr_6 : runTot 245 start505 = s505_7 := by
    change runTot (210 + 35) start505 = s505_7
    rw [runTot_add, hr_5, run505_6]
  have hr_7 : runTot 280 start505 = s505_8 := by
    change runTot (245 + 35) start505 = s505_8
    rw [runTot_add, hr_6, run505_7]
  have hr_8 : runTot 315 start505 = entry505 := by
    change runTot (280 + 35) start505 = entry505
    rw [runTot_add, hr_7, run505_8]
  exact hr_8

private theorem tm505_safe_prefix : ∀ j < 315, isDoor (stepTot^[j] start505) = false := by
  have hs_0 : ∀ j < 35, isDoor (stepTot^[j] start505) = false :=
    safePrefix_sound 35 start505 safe505_0
  have hr_1 : runTot 70 start505 = s505_2 := by
    change runTot (35 + 35) start505 = s505_2
    rw [runTot_add, run505_0, run505_1]
  have hs_1 : ∀ j < 70, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_1 35 35 run505_0 hs_0 (safePrefix_sound 35 s505_1 safe505_1)
  have hr_2 : runTot 105 start505 = s505_3 := by
    change runTot (70 + 35) start505 = s505_3
    rw [runTot_add, hr_1, run505_2]
  have hs_2 : ∀ j < 105, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_2 70 35 hr_1 hs_1 (safePrefix_sound 35 s505_2 safe505_2)
  have hr_3 : runTot 140 start505 = s505_4 := by
    change runTot (105 + 35) start505 = s505_4
    rw [runTot_add, hr_2, run505_3]
  have hs_3 : ∀ j < 140, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_3 105 35 hr_2 hs_2 (safePrefix_sound 35 s505_3 safe505_3)
  have hr_4 : runTot 175 start505 = s505_5 := by
    change runTot (140 + 35) start505 = s505_5
    rw [runTot_add, hr_3, run505_4]
  have hs_4 : ∀ j < 175, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_4 140 35 hr_3 hs_3 (safePrefix_sound 35 s505_4 safe505_4)
  have hr_5 : runTot 210 start505 = s505_6 := by
    change runTot (175 + 35) start505 = s505_6
    rw [runTot_add, hr_4, run505_5]
  have hs_5 : ∀ j < 210, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_5 175 35 hr_4 hs_4 (safePrefix_sound 35 s505_5 safe505_5)
  have hr_6 : runTot 245 start505 = s505_7 := by
    change runTot (210 + 35) start505 = s505_7
    rw [runTot_add, hr_5, run505_6]
  have hs_6 : ∀ j < 245, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_6 210 35 hr_5 hs_5 (safePrefix_sound 35 s505_6 safe505_6)
  have hr_7 : runTot 280 start505 = s505_8 := by
    change runTot (245 + 35) start505 = s505_8
    rw [runTot_add, hr_6, run505_7]
  have hs_7 : ∀ j < 280, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_7 245 35 hr_6 hs_6 (safePrefix_sound 35 s505_7 safe505_7)
  have hs_8 : ∀ j < 315, isDoor (stepTot^[j] start505) = false :=
    safePrefix_chunks start505 s505_8 280 35 hr_7 hs_7 (safePrefix_sound 35 s505_8 safe505_8)
  exact hs_8

/-- Direct `IsNotHalt tm505` corollary for `1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB`, connecting
`tm505_reaches_entry`
(`entry505 = ⟨.mAL, [(2, false)], (1, false) :: S505⟩`) to any `EvalF`-closed predicate `W`
containing `W₉ ++ [1, 1, 2]`. -/
private theorem isNotHalt_505_of_evalF_W_closed
    (W : List (ℕ × Bool) → Prop)
    (hW : ∀ n S Δ Z, EvalF n ((3, false) :: S) Δ Z →
      StrictNo0F ((3, false) :: S) → W ((3, false) :: S) →
      (Δ = 7 ∧ W ((3, false) :: (1, false) :: Z)) ∨
      (Δ = 10 ∧ W ((3, false) :: (1, false) :: (1, false) :: Z)))
    (hW9 : W [(3, false), (1, false), (1, false), (2, false), (0, true), (2, false), (1, false), (1,
        false), (2, false)]) :
    IsNotHalt tm505 := by
  have hS : StrictNo0F [(1, false), (1, false), (2, false), (0, true), (2, false), (1, false), (1,
      false), (2, false)] := trivial
  have hwall : ∀ k : ℕ, isDoor (stepTot^[k] entry505) = false :=
    orbit_safe_of_evalF_W_closed W hW
      [(1, false), (1, false), (2, false), (0, true), (2, false), (1, false), (1, false), (2,
          false)] hS hW9
  refine isNotHalt_of_orbit_safe_505 ?_
  intro n
  rcases Nat.lt_or_ge n 315 with hlt | hge
  · exact tm505_safe_prefix n hlt
  · have hsplit : n = 315 + (n - 315) := by omega
    rw [hsplit, stepTot_iter_add, tm505_reaches_entry]
    exact hwall (n - 315)

private theorem target_tm_eq_local : target_tm = tm505 := by
  funext s b
  match s, b with
  | 0, 0 => rfl | 0, 1 => rfl | 1, 0 => rfl | 1, 1 => rfl
  | 2, 0 => rfl | 2, 1 => rfl | 3, 0 => rfl | 3, 1 => rfl
  | 4, 0 => rfl | 4, 1 => rfl | 5, 0 => rfl | 5, 1 => rfl


private theorem is_does_not_halt : IsNotHalt target_tm := by
  rw [target_tm_eq_local]
  exact isNotHalt_505_of_evalF_W_closed W_closed W_closed_step (Or.inr ⟨_, rfl,
      BusyBeaver.Calculi.PairStackA.good2_of_2_0s [(2, false), (1, false), (1, false), (2, false)]⟩)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB
