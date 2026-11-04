/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.RleCarryData

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1LD_1RA0RF_1RAHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_0LC0RE_1LA1LD_0LB1LD_1RA0RF_1RAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution

open Counter BusyBeaver.RleCarryEngine

set_option maxRecDepth 4000000 in
instance : HasRleCarryRules target_tm where
  carry_Z := fun l r =>
    ⟨46,
      Counter.wmultiStep_sound (tm := target_tm) 46 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0,
        1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_P := fun l r =>
    ⟨16,
      Counter.wmultiStep_sound (tm := target_tm) 16 ⟨B, 1, [0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0,
        1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_PMUTM := fun l r =>
    ⟨68,
      Counter.wmultiStep_sound (tm := target_tm) 68 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0,
        1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTW := fun l r =>
    ⟨102,
      Counter.wmultiStep_sound (tm := target_tm) 102 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTT := fun l r =>
    ⟨72,
      Counter.wmultiStep_sound (tm := target_tm) 72 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTTM := fun l r =>
    ⟨85,
      Counter.wmultiStep_sound (tm := target_tm) 85 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1, 1, 0, 1]⟩ l r rfl⟩
  turn_UM := fun r =>
    ⟨53,
      Counter.cmultiStep_sound (tm := target_tm) 53 ⟨B, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1], []⟩ r rfl⟩
  turn_UMT := fun r =>
    ⟨83,
      Counter.cmultiStep_sound (tm := target_tm) 83 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], []⟩ r rfl⟩
  turn_ZT := fun l r =>
    ⟨53,
      Counter.wmultiStep_sound (tm := target_tm) 53 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0,
        0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_WM := fun l r =>
    ⟨47,
      Counter.wmultiStep_sound (tm := target_tm) 47 ⟨B, 1, [0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0,
        0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PT := fun l r =>
    ⟨97,
      Counter.wmultiStep_sound (tm := target_tm) 97 ⟨B, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0,
        0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZM := fun l r =>
    ⟨47,
      Counter.wmultiStep_sound (tm := target_tm) 47 ⟨B, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  turn_PTW := fun l r =>
    ⟨119,
      Counter.wmultiStep_sound (tm := target_tm) 119 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl⟩
  turn_PTM := fun l r =>
    ⟨83,
      Counter.wmultiStep_sound (tm := target_tm) 83 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PTT := fun l r =>
    ⟨87,
      Counter.wmultiStep_sound (tm := target_tm) 87 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl⟩
  turn_ZMU := fun l r =>
    ⟨93,
      Counter.wmultiStep_sound (tm := target_tm) 93 ⟨B, 1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1,
        0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTM := fun l r =>
    ⟨103,
      Counter.wmultiStep_sound (tm := target_tm) 103 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTT := fun l r =>
    ⟨105,
      Counter.wmultiStep_sound (tm := target_tm) 105 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTW := fun l r =>
    ⟨105,
      Counter.wmultiStep_sound (tm := target_tm) 105 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_MUTW := fun l r =>
    ⟨119,
      Counter.wmultiStep_sound (tm := target_tm) 119 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PTTM := fun l r =>
    ⟨137,
      Counter.wmultiStep_sound (tm := target_tm) 137 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTW := fun l r =>
    ⟨137,
      Counter.wmultiStep_sound (tm := target_tm) 137 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTM := fun l r =>
    ⟨91,
      Counter.wmultiStep_sound (tm := target_tm) 91 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
      []⟩ l r rfl⟩
  turn_ZPMU := fun l r =>
    ⟨135,
      Counter.wmultiStep_sound (tm := target_tm) 135 ⟨B, 1, [0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
      []⟩ l r rfl⟩
  turn_ZMUTM := fun l r =>
    ⟨133,
      Counter.wmultiStep_sound (tm := target_tm) 133 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0,
        0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_PTTTW := fun l r =>
    ⟨173,
      Counter.wmultiStep_sound (tm := target_tm) 173 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
      0, 1, 1, 1], []⟩ l r rfl⟩
  carry_MU_to_pmuCfg := fun l r =>
    ⟨15,
      Counter.wmultiStep_sound (tm := target_tm) 15 ⟨B, 1, [0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmu_step := fun l r =>
    ⟨50,
      Counter.wmultiStep_sound (tm := target_tm) 50 ⟨D, 1, [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmuCfg_Z_turn := fun l r =>
    ⟨30,
      Counter.wmultiStep_sound (tm := target_tm) 30 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1,
        1, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  pmuCfg_M_to_carry := fun l r =>
    ⟨5,
      Counter.wmultiStep_sound (tm := target_tm) 5 ⟨D, 1, [0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmuCfg_T_to_carry := fun l r =>
    ⟨5,
      Counter.wmultiStep_sound (tm := target_tm) 5 ⟨D, 1, [0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0,
        1]⟩
    ⟨B, 1, [0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_PTU := fun l r =>
    ⟨24,
      Counter.wmultiStep_sound (tm := target_tm) 24 ⟨B, 1, [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  turn_PTMT := fun l r =>
    ⟨137,
      Counter.wmultiStep_sound (tm := target_tm) 137 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTT := fun l r =>
    ⟨137,
      Counter.wmultiStep_sound (tm := target_tm) 137 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTTM := fun l r =>
    ⟨123,
      Counter.wmultiStep_sound (tm := target_tm) 123 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      0, 1, 1], []⟩ l r rfl⟩
  turn_ZTU_halt := fun l r =>
    ⟨_, ⟨26,
      Counter.wmultiStep_sound (tm := target_tm) 26 ⟨B, 1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨F, 1, [0, 0, 1, 1, 0, 1, 1, 1], [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩, rfl⟩
  r0_Z := fun l r =>
    ⟨10,
      Counter.wmultiStep_sound (tm := target_tm) 10 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r0_P := fun l r =>
    ⟨40,
      Counter.wmultiStep_sound (tm := target_tm) 40 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  r0_PTTTM_TAIL := fun l r =>
    ⟨13,
      Counter.wmultiStep_sound (tm := target_tm) 13 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_Z := fun l r =>
    ⟨10,
      Counter.wmultiStep_sound (tm := target_tm) 10 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_P := fun l r =>
    ⟨58,
      Counter.wmultiStep_sound (tm := target_tm) 58 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1OddShort_Z := fun l r =>
    ⟨10,
      Counter.wmultiStep_sound (tm := target_tm) 10 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0,
        1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1Odd_P := fun l r =>
    ⟨8,
      Counter.wmultiStep_sound (tm := target_tm) 8 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_start := fun l =>
    ⟨2,
      Counter.rcmultiStep_sound (tm := target_tm) 2 ⟨B, 0, [1, 1], []⟩
    ⟨D, 1, [], [1]⟩ l rfl⟩
  wSweep_step := fun l r =>
    ⟨4,
      Counter.wmultiStep_sound (tm := target_tm) 4 ⟨D, 1, [0, 0, 1, 1], [1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 1]⟩ l r rfl⟩
  dSweep_step := fun l r =>
    ⟨4,
      Counter.wmultiStep_sound (tm := target_tm) 4 ⟨E, 1, [0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  dSweep_end := fun l =>
    ⟨3,
      Counter.rcmultiStep_sound (tm := target_tm) 3 ⟨E, 1, [0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1], []⟩ l rfl⟩
  tSweep_step := fun l r =>
    ⟨20,
      Counter.wmultiStep_sound (tm := target_tm) 20 ⟨E, 0, [0, 0, 0, 0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  tSweep_end := fun l =>
    ⟨2,
      Counter.rcmultiStep_sound (tm := target_tm) 2 ⟨E, 0, [0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩ l rfl⟩
  r0_to_dSweep := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := target_tm) 6 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0,
        1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_to_dSweep := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := target_tm) 6 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [1, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1Odd_to_tSweep := fun l r =>
    ⟨8,
      Counter.wmultiStep_sound (tm := target_tm) 8 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [1, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_Z_to_dSweep := fun l r =>
    ⟨9,
      Counter.wmultiStep_sound (tm := target_tm) 9 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1]⟩
    ⟨E, 1, [0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  wSweep_ZT_to_dSweep := fun l r =>
    ⟨45,
      Counter.wmultiStep_sound (tm := target_tm) 45 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0,
        1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_PT_to_carry := fun l r =>
    ⟨34,
      Counter.wmultiStep_sound (tm := target_tm) 34 ⟨D, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 0,
        1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]⟩ l r rfl⟩
  wSweep_ZMT_to_tSweep := fun l r =>
    ⟨65,
      Counter.wmultiStep_sound (tm := target_tm) 65 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [1, 0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  cfgR_Z_to_TW := fun l =>
    ⟨14,
      Counter.rcmultiStep_sound (tm := target_tm) 14 ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l rfl⟩
  cfgR_TW_to_t3Cfg := fun l =>
    ⟨24,
      Counter.rcmultiStep_sound (tm := target_tm) 24 ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩ l rfl⟩
  t3_step := fun l r =>
    ⟨56,
      Counter.wmultiStep_sound (tm := target_tm) 56 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0,
        1, 0, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  t3Cfg_Z_zero_to_carry := fun l =>
    ⟨96,
      Counter.rcmultiStep_sound (tm := target_tm) 96 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1,
        0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl⟩
  t3Cfg_Z_succ_to_r0 := fun l r =>
    ⟨31,
      Counter.wmultiStep_sound (tm := target_tm) 31 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  t3Cfg_TZ_to_r1OddShort := fun l r =>
    ⟨45,
      Counter.wmultiStep_sound (tm := target_tm) 45 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0,
        0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  r1OddShortCfg_evalWK0_to_carry := fun l =>
    ⟨144,
      Counter.rcmultiStep_sound (tm := target_tm) 144 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl⟩
  t3Cfg_TTZ_to_r0 := fun l r =>
    ⟨65,
      Counter.wmultiStep_sound (tm := target_tm) 65 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 1, 0, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩

set_option maxRecDepth 4000000 in
theorem init_to_ckpt0 :
    (init []) [target_tm]⊢* (carryCfg target_tm (evalRleAux default ckptRle_0) (evalWK 1)) := by
  have h1 : evalRleAux default ckptRle_0 =
      [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
        0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
        1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1] +> default := rfl
  rw [h1]
  exact stepStar_trans ⟨1120, Counter.bmultiStep_sound (tm := target_tm) 1120 ⟨A, 0, [], []⟩ ⟨D, 0,
    [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1,
      1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩
    (stepStar_trans ⟨1120, Counter.bmultiStep_sound (tm := target_tm) 1120 _ ⟨A, 1, [1, 0, 0, 0, 1,
      1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1,
        1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
          0, 0, 1, 1]⟩ rfl⟩
    (stepStar_trans ⟨1120, Counter.bmultiStep_sound (tm := target_tm) 1120 _ ⟨B, 0, [1, 1, 0, 0, 1,
      1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
        1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0,
          0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩
    (stepStar_trans ⟨1120, Counter.bmultiStep_sound (tm := target_tm) 1120 _ ⟨B, 0, [0, 0, 0, 0, 1,
      1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [0, 1, 1, 0, 1, 0,
        0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
          0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0,
            0, 1, 1]⟩ rfl⟩
    (stepStar_trans ⟨1120, Counter.bmultiStep_sound (tm := target_tm) 1120 _ ⟨B, 0, [1, 1, 0, 0, 1,
      1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
        1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
          1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
            1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [0, 1, 1]⟩ rfl⟩
      ⟨1124, Counter.bmultiStep_sound (tm := target_tm) 1124 _ ⟨B, 1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
        1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0,
          1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
            0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0,
              0, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩))))

end Solution

public section

open Solution BusyBeaver.RleCarryEngine in
theorem is_halt : IsHalt target := by
  rcases runCarryTruncChunks_sound (target_tm := target_tm)
      [3746, 3999, 4000, 4000, 4000, 4000, 4000, 3298] 30 ckptRle_0 1 default
      runCarryTruncChunks_ckpt0 with ⟨cfg', hstep, hnone⟩
  exact ⟨cfg', stepStar_trans init_to_ckpt0 hstep, hnone⟩

end

end BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1LD_1RA0RF_1RAHHH
