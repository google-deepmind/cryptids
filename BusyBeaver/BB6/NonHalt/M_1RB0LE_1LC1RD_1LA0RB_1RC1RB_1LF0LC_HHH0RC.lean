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

namespace BusyBeaver.M_1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)


open BusyBeaver.Calculi.PairStackB

/-- Blank-tape entry state for `tm484`. -/
private def start484 : State484 := ⟨.mAL, [], []⟩

/-- Blank-tape entry for `tm484`: `init []` equals `enc484 start484` in `0` raw TM steps. -/
private theorem tm484_entry : (init [] : Cfg (Fin 2) (Fin 6)) = enc484 start484 := by
  simp only [init, enc484, start484, encStack, Cfg.headLeft]
  rfl

/-- Doorway-avoidance of the `stepTot` orbit from `start484` implies `IsNotHalt tm484`. -/
private theorem isNotHalt_of_orbit_safe
    (hsafe : ∀ n : ℕ, isDoor (stepTot^[n] start484) = false) :
    IsNotHalt tm484 := by
  intro cfg hreach
  rcases hreach with ⟨m, hm⟩
  rw [tm484_entry] at hm
  obtain ⟨t, ht, hmt⟩ := multiStep_ge_of_orbit_safe start484 hsafe (m + 1)
  have hdiff : t = m + ((t - m - 1) + 1) := by omega
  rw [hdiff, multiStep_add_eq m ((t - m - 1) + 1), hm, Option.bind_some] at hmt
  exact isSome_step_of_multiStep_succ hmt

private theorem safePrefix_add (a b : ℕ) (s : State484)
    (ha : safePrefix a s = true) (hb : safePrefix b (runTot a s) = true) :
    ∀ j < a + b, isDoor (stepTot^[j] s) = false := by
  intro j hj
  by_cases hja : j < a
  · exact safePrefix_sound a s ha j hja
  · have hjb : j - a < b := by omega
    have hsplit : j = a + (j - a) := by omega
    rw [hsplit, stepTot_iter_add, ← runTot_eq_iterate a]
    exact safePrefix_sound b (runTot a s) hb (j - a) hjb

/-- Soliton-wall entry configuration `BR [0] ([1] ++ [1,1,2]^2)` reached by `tm484` at `t = 174`. -/
private def solitonStart484 : State484 :=
  ⟨.mBR, [(0, false)],
    [(1, false), (1, false), (1, false), (2, false), (1, false), (1, false), (2, false)]⟩

private def s29_484 : State484 :=
  ⟨.mDR, [(5, false)], [(1, true), (0, false)]⟩
private def s58_484 : State484 :=
  ⟨.mAL, [(1, false), (0, false), (4, false)], [(1, false), (0, false)]⟩
private def s87_484 : State484 :=
  ⟨.mAL, [(4, false), (1, false), (3, false), (1, false)], [(1, false)]⟩
private def s116_484 : State484 :=
  ⟨.mDR, [(0, false), (1, false)],
    [(1, false), (1, false), (2, false), (1, false), (1, false)]⟩
private def s145_484 : State484 :=
  ⟨.mAL, [(7, false), (1, false), (3, false), (1, false)], [(2, false)]⟩

private theorem run29_0 : runTot 29 start484 = s29_484 := rfl
private theorem run29_1 : runTot 29 s29_484 = s58_484 := rfl
private theorem run29_2 : runTot 29 s58_484 = s87_484 := rfl
private theorem run29_3 : runTot 29 s87_484 = s116_484 := rfl
private theorem run29_4 : runTot 29 s116_484 = s145_484 := rfl
private theorem run29_5 : runTot 29 s145_484 = solitonStart484 := rfl

private theorem tm484_reaches_soliton_174 :
    stepTot^[174] start484 = solitonStart484 := by
  rw [← runTot_eq_iterate]
  have hsplit : (174 : ℕ) = ((((29 + 29) + 29) + 29) + 29) + 29 := rfl
  rw [hsplit, runTot_add, runTot_add, runTot_add, runTot_add, runTot_add,
    run29_0, run29_1, run29_2, run29_3, run29_4, run29_5]

private theorem safe29_0 : safePrefix 29 start484 = true := rfl
private theorem safe29_1 : safePrefix 29 s29_484 = true := rfl
private theorem safe29_2 : safePrefix 29 s58_484 = true := rfl
private theorem safe29_3 : safePrefix 29 s87_484 = true := rfl
private theorem safe29_4 : safePrefix 29 s116_484 = true := rfl
private theorem safe29_5 : safePrefix 29 s145_484 = true := rfl

private theorem tm484_safe_prefix_174 :
    ∀ j < 174, isDoor (stepTot^[j] start484) = false := by
  have h01 : ∀ j < 58, isDoor (stepTot^[j] start484) = false :=
    safePrefix_add 29 29 start484 safe29_0 (run29_0 ▸ safe29_1)
  have h23 : ∀ j < 58, isDoor (stepTot^[j] s58_484) = false :=
    safePrefix_add 29 29 s58_484 safe29_2 (run29_2 ▸ safe29_3)
  have h45 : ∀ j < 58, isDoor (stepTot^[j] s116_484) = false :=
    safePrefix_add 29 29 s116_484 safe29_4 (run29_4 ▸ safe29_5)
  have hr58_0 : runTot 58 start484 = s58_484 := by
    change runTot (29 + 29) start484 = s58_484
    rw [runTot_add, run29_0, run29_1]
  have hr58_1 : runTot 58 s58_484 = s116_484 := by
    change runTot (29 + 29) s58_484 = s116_484
    rw [runTot_add, run29_2, run29_3]
  have h03 : ∀ j < 116, isDoor (stepTot^[j] start484) = false :=
    safePrefix_chunks start484 s58_484 58 58 hr58_0 h01 h23
  have hr116 : runTot 116 start484 = s116_484 := by
    change runTot (58 + 58) start484 = s116_484
    rw [runTot_add, hr58_0, hr58_1]
  exact safePrefix_chunks start484 s116_484 116 58 hr116 h03 h45

/-- Direct `IsNotHalt tm484` corollary for `1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`, connecting
`tm484_reaches_soliton_174`
(`solitonStart484 = stepTot ⟨.mAL, [(2, false)], P₀⟩`) to any `EvalF`-closed predicate `W`
containing `W₀ = [3, 1, 2, 1, 1, 2]`. -/
private theorem isNotHalt_484_of_evalF_W_closed
    (W : List (ℕ × Bool) → Prop)
    (hW : ∀ n S Δ Z, EvalF n ((3, false) :: S) Δ Z →
      StrictNo0F ((3, false) :: S) → W ((3, false) :: S) →
      (Δ = 7 ∧ W ((3, false) :: (1, false) :: Z)) ∨
      (Δ = 10 ∧ W ((3, false) :: (1, false) :: (1, false) :: Z)))
    (hW0 : W [(3, false), (1, false), (2, false), (1, false), (1, false), (2, false)]) :
    IsNotHalt tm484 := by
  have hS0 : StrictNo0F [(1, false), (2, false), (1, false), (1, false), (2, false)] := trivial
  have hwall : ∀ k : ℕ,
      isDoor (stepTot^[k] ⟨.mAL, [(2, false)],
        [(1, false), (1, false), (2, false), (1, false), (1, false), (2, false)]⟩) = false :=
    orbit_safe_of_evalF_W_closed W hW
      [(1, false), (2, false), (1, false), (1, false), (2, false)] hS0 hW0
  refine isNotHalt_of_orbit_safe ?_
  intro n
  rcases Nat.lt_or_ge n 174 with hlt | hge
  · exact tm484_safe_prefix_174 n hlt
  · have hsplit : n = 174 + (n - 174) := by omega
    rw [hsplit, stepTot_iter_add, tm484_reaches_soliton_174]
    have hsol : solitonStart484 = stepTot ⟨.mAL, [(2, false)],
        [(1, false), (1, false), (2, false), (1, false), (1, false), (2, false)]⟩ := rfl
    rw [hsol, ← Function.iterate_succ_apply]
    exact hwall (n - 174 + 1)

private theorem target_tm_eq_local : target_tm = tm484 := by
  funext s b
  match s, b with
  | 0, 0 => rfl | 0, 1 => rfl | 1, 0 => rfl | 1, 1 => rfl
  | 2, 0 => rfl | 2, 1 => rfl | 3, 0 => rfl | 3, 1 => rfl
  | 4, 0 => rfl | 4, 1 => rfl | 5, 0 => rfl | 5, 1 => rfl


private theorem is_does_not_halt : IsNotHalt target_tm := by
  rw [target_tm_eq_local]
  exact isNotHalt_484_of_evalF_W_closed W_closed W_closed_step (Or.inl ⟨_, rfl,
      BusyBeaver.Calculi.PairStackA.strong2_of_2_1_1 [(2, false)]⟩)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC
