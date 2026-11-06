/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.RleCarryData

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_HHH1LC

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_HHH1LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

namespace Solution

open Counter BusyBeaver.RleCarryEngine

def bc0 : CCfg (Fin 2) (Fin 6) := ⟨A, 0, [], []⟩
def bc1 : CCfg (Fin 2) (Fin 6) :=
  ⟨A, 0,
    [1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩
def bc2 : CCfg (Fin 2) (Fin 6) :=
  ⟨A, 0,
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
      1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1,
      1, 0, 1],
    [1, 0, 0, 1, 1]⟩
def bc3 : CCfg (Fin 2) (Fin 6) :=
  ⟨A, 1,
    [1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
      1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    [0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
      0, 0, 1, 1]⟩
def bc4 : CCfg (Fin 2) (Fin 6) :=
  ⟨A, 0,
    [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
      1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
      1, 0, 0, 0, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩
def bc5 : CCfg (Fin 2) (Fin 6) :=
  ⟨A, 0,
    [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
      0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0,
      0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩
def bc6 : CCfg (Fin 2) (Fin 6) :=
  ⟨B, 1,
    [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
      0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
      0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1,
      0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩

-- Each `bmultiStep_sound` chunk reduces 1,500 (or 928) TM steps via `rfl`.
set_option maxRecDepth 2000000 in
theorem step_bc1 : (evalBCfg bc0) [tm521]⊢* (evalBCfg bc1) :=
  ⟨1500, Counter.bmultiStep_sound (tm := tm521) 1500 bc0 bc1 rfl⟩
set_option maxRecDepth 2000000 in
theorem step_bc2 : (evalBCfg bc1) [tm521]⊢* (evalBCfg bc2) :=
  ⟨1500, Counter.bmultiStep_sound (tm := tm521) 1500 bc1 bc2 rfl⟩
set_option maxRecDepth 2000000 in
theorem step_bc3 : (evalBCfg bc2) [tm521]⊢* (evalBCfg bc3) :=
  ⟨1500, Counter.bmultiStep_sound (tm := tm521) 1500 bc2 bc3 rfl⟩
set_option maxRecDepth 2000000 in
theorem step_bc4 : (evalBCfg bc3) [tm521]⊢* (evalBCfg bc4) :=
  ⟨1500, Counter.bmultiStep_sound (tm := tm521) 1500 bc3 bc4 rfl⟩
set_option maxRecDepth 2000000 in
theorem step_bc5 : (evalBCfg bc4) [tm521]⊢* (evalBCfg bc5) :=
  ⟨1500, Counter.bmultiStep_sound (tm := tm521) 1500 bc4 bc5 rfl⟩
set_option maxRecDepth 2000000 in
theorem step_bc6 : (evalBCfg bc5) [tm521]⊢* (evalBCfg bc6) :=
  ⟨928, Counter.bmultiStep_sound (tm := tm521) 928 bc5 bc6 rfl⟩

set_option maxRecDepth 2000000 in
theorem init_to_ckpt0 :
    (init []) [tm521]⊢* (carryCfg tm521 (evalRleAux default ckptRle_0) (evalWK 1)) := by
  have h1 : evalRleAux default ckptRle_0 = bc6.l +> default := rfl
  rw [h1]
  exact stepStar_trans step_bc1 (stepStar_trans step_bc2 (stepStar_trans step_bc3
    (stepStar_trans step_bc4 (stepStar_trans step_bc5 step_bc6))))

end Solution

public section

open Solution BusyBeaver.RleCarryEngine in
theorem is_halt : IsHalt target := by
  rcases runCarryTruncChunks_sound (target_tm := tm521)
      [3746, 3999, 4000, 4000, 4000, 4000, 4000, 3298] 30 ckptRle_0 1 default
      runCarryTruncChunks_ckpt0 with ⟨cfg', hstep, hnone⟩
  exact ⟨cfg', stepStar_trans init_to_ckpt0 hstep, hnone⟩

end

end BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_HHH1LC
