/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.RleCarryData

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1LF_HHH1RA

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1LF_HHH1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution

open Counter BusyBeaver.RleCarryEngine

def σ_BCADFE : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 3
  | 5 => 5

theorem tableIso_144_521 : ∀ (q : Fin 6) (a : Fin 2),
    target_tm (σ_BCADFE q) a = (tm521 q a).map (conjOut σ_BCADFE true)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 3, 0 => rfl
  | 3, 1 => rfl
  | 4, 0 => rfl
  | 4, 1 => rfl
  | 5, 0 => rfl
  | 5, 1 => rfl

theorem step_conj_144 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (conjCfg σ_BCADFE true c) = (step tm521 c).map (conjCfg σ_BCADFE true) :=
  step_conj_of_tableIso tableIso_144_521 c

theorem multiStep_conj_144 (c : Cfg (Fin 2) (Fin 6)) (k : ℕ) :
    multiStep target_tm (conjCfg σ_BCADFE true c) k =
      (multiStep tm521 c k).map (conjCfg σ_BCADFE true) :=
  multiStep_conj_of_tableIso tableIso_144_521 c k

-- `bmultiStep_sound` reduces 1,901 TM steps via `rfl`.
set_option maxRecDepth 2000000 in
theorem init_to_initRle144 :
    (init []) [target_tm]⊢*
      (conjCfg σ_BCADFE true (carryCfg tm521 (evalRleAux default initRle) (evalWK 1))) := by
  have hstep : (evalBCfg ⟨A, 0, [], []⟩) [target_tm]⊢^{1901}
      (evalBCfg ⟨C, 1,
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1],
        [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0,
          1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1]⟩) :=
    Counter.bmultiStep_sound (tm := target_tm) 1901 ⟨A, 0, [], []⟩
      ⟨C, 1,
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1],
        [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0,
          1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1]⟩ rfl
  exact ⟨1901, hstep⟩

end Solution

public section

open Solution Counter BusyBeaver.RleCarryEngine in
theorem is_halt : IsHalt target := by
  rcases runCarryChunks_sound (target_tm := tm521) 28 500 initRle 1
      runCarryChunks_28_500 with ⟨cfg', ⟨k, hk⟩, hnone⟩
  have hk144 :
      (conjCfg σ_BCADFE true (carryCfg tm521 (evalRleAux default initRle) (evalWK 1)))
        [target_tm]⊢* (conjCfg σ_BCADFE true cfg') := by
    refine ⟨k, ?_⟩
    rw [multiStep_conj_144, hk]
    rfl
  have hnone144 : (step target_tm (conjCfg σ_BCADFE true cfg')).isNone := by
    rw [step_conj_144]
    cases hstep : step tm521 cfg' with
    | none => rfl
    | some val => rw [hstep] at hnone; contradiction
  exact ⟨conjCfg σ_BCADFE true cfg', stepStar_trans init_to_initRle144 hk144, hnone144⟩

end

end BusyBeaver.M_1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1LF_HHH1RA
