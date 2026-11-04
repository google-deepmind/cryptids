/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.RleCarryData

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LDHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LDHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution

open Counter BusyBeaver.RleCarryEngine

set_option maxRecDepth 4000000 in
instance : HasRleCarryRules target_tm where
  carry_Z := fun l r =>
    ⟨62,
      Counter.wmultiStep_sound (tm := target_tm) 62 ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0,
        1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_P := fun l r =>
    ⟨22,
      Counter.wmultiStep_sound (tm := target_tm) 22 ⟨D, 1, [0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0,
        1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_PMUTM := fun l r =>
    ⟨90,
      Counter.wmultiStep_sound (tm := target_tm) 90 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0,
        1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTW := fun l r =>
    ⟨134,
      Counter.wmultiStep_sound (tm := target_tm) 134 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTT := fun l r =>
    ⟨94,
      Counter.wmultiStep_sound (tm := target_tm) 94 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTTM := fun l r =>
    ⟨111,
      Counter.wmultiStep_sound (tm := target_tm) 111 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1, 1, 0, 1]⟩ l r rfl⟩
  turn_UM := fun r =>
    ⟨67,
      Counter.cmultiStep_sound (tm := target_tm) 67 ⟨D, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1], []⟩ r rfl⟩
  turn_UMT := fun r =>
    ⟨105,
      Counter.cmultiStep_sound (tm := target_tm) 105 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0,
        0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], []⟩ r rfl⟩
  turn_ZT := fun l r =>
    ⟨67,
      Counter.wmultiStep_sound (tm := target_tm) 67 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0,
        0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_WM := fun l r =>
    ⟨59,
      Counter.wmultiStep_sound (tm := target_tm) 59 ⟨D, 1, [0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0,
        0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PT := fun l r =>
    ⟨125,
      Counter.wmultiStep_sound (tm := target_tm) 125 ⟨D, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1,
        0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZM := fun l r =>
    ⟨59,
      Counter.wmultiStep_sound (tm := target_tm) 59 ⟨D, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  turn_PTW := fun l r =>
    ⟨151,
      Counter.wmultiStep_sound (tm := target_tm) 151 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl⟩
  turn_PTM := fun l r =>
    ⟨105,
      Counter.wmultiStep_sound (tm := target_tm) 105 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PTT := fun l r =>
    ⟨109,
      Counter.wmultiStep_sound (tm := target_tm) 109 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl⟩
  turn_ZMU := fun l r =>
    ⟨121,
      Counter.wmultiStep_sound (tm := target_tm) 121 ⟨D, 1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTM := fun l r =>
    ⟨133,
      Counter.wmultiStep_sound (tm := target_tm) 133 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTT := fun l r =>
    ⟨137,
      Counter.wmultiStep_sound (tm := target_tm) 137 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTW := fun l r =>
    ⟨137,
      Counter.wmultiStep_sound (tm := target_tm) 137 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_MUTW := fun l r =>
    ⟨151,
      Counter.wmultiStep_sound (tm := target_tm) 151 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PTTM := fun l r =>
    ⟨175,
      Counter.wmultiStep_sound (tm := target_tm) 175 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTW := fun l r =>
    ⟨175,
      Counter.wmultiStep_sound (tm := target_tm) 175 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTM := fun l r =>
    ⟨117,
      Counter.wmultiStep_sound (tm := target_tm) 117 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
      []⟩ l r rfl⟩
  turn_ZPMU := fun l r =>
    ⟨177,
      Counter.wmultiStep_sound (tm := target_tm) 177 ⟨D, 1, [0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
      []⟩ l r rfl⟩
  turn_ZMUTM := fun l r =>
    ⟨171,
      Counter.wmultiStep_sound (tm := target_tm) 171 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0,
        0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_PTTTW := fun l r =>
    ⟨221,
      Counter.wmultiStep_sound (tm := target_tm) 221 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
      0, 1, 1, 1], []⟩ l r rfl⟩
  carry_MU_to_pmuCfg := fun l r =>
    ⟨19,
      Counter.wmultiStep_sound (tm := target_tm) 19 ⟨D, 1, [0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨A, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmu_step := fun l r =>
    ⟨66,
      Counter.wmultiStep_sound (tm := target_tm) 66 ⟨A, 1, [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨A, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmuCfg_Z_turn := fun l r =>
    ⟨40,
      Counter.wmultiStep_sound (tm := target_tm) 40 ⟨A, 1, [0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1,
        1, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  pmuCfg_M_to_carry := fun l r =>
    ⟨7,
      Counter.wmultiStep_sound (tm := target_tm) 7 ⟨A, 1, [0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmuCfg_T_to_carry := fun l r =>
    ⟨7,
      Counter.wmultiStep_sound (tm := target_tm) 7 ⟨A, 1, [0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0,
        1]⟩
    ⟨D, 1, [0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_PTU := fun l r =>
    ⟨30,
      Counter.wmultiStep_sound (tm := target_tm) 30 ⟨D, 1, [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  turn_PTMT := fun l r =>
    ⟨175,
      Counter.wmultiStep_sound (tm := target_tm) 175 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTT := fun l r =>
    ⟨175,
      Counter.wmultiStep_sound (tm := target_tm) 175 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
        0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTTM := fun l r =>
    ⟨155,
      Counter.wmultiStep_sound (tm := target_tm) 155 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      0, 1, 1], []⟩ l r rfl⟩
  turn_ZTU_halt := fun l r =>
    ⟨_, ⟨34,
      Counter.wmultiStep_sound (tm := target_tm) 34 ⟨D, 1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨F, 1, [1, 0, 1, 1, 0, 1, 1, 1], [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩, rfl⟩
  r0_Z := fun l r =>
    ⟨12,
      Counter.wmultiStep_sound (tm := target_tm) 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r0_P := fun l r =>
    ⟨52,
      Counter.wmultiStep_sound (tm := target_tm) 52 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  r0_PTTTM_TAIL := fun l r =>
    ⟨15,
      Counter.wmultiStep_sound (tm := target_tm) 15 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_Z := fun l r =>
    ⟨12,
      Counter.wmultiStep_sound (tm := target_tm) 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_P := fun l r =>
    ⟨74,
      Counter.wmultiStep_sound (tm := target_tm) 74 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1OddShort_Z := fun l r =>
    ⟨12,
      Counter.wmultiStep_sound (tm := target_tm) 12 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0,
        1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1Odd_P := fun l r =>
    ⟨10,
      Counter.wmultiStep_sound (tm := target_tm) 10 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_start := fun l =>
    ⟨2,
      Counter.rcmultiStep_sound (tm := target_tm) 2 ⟨D, 0, [1, 1], []⟩
    ⟨A, 1, [], [1]⟩ l rfl⟩
  wSweep_step := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := target_tm) 6 ⟨A, 1, [0, 0, 1, 1], [1]⟩
    ⟨A, 1, [], [1, 0, 0, 1, 1]⟩ l r rfl⟩
  dSweep_step := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := target_tm) 6 ⟨E, 1, [0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  dSweep_end := fun l =>
    ⟨5,
      Counter.rcmultiStep_sound (tm := target_tm) 5 ⟨E, 1, [0, 1, 1], []⟩
    ⟨D, 0, [1, 1, 0, 0, 1, 1], []⟩ l rfl⟩
  tSweep_step := fun l r =>
    ⟨26,
      Counter.wmultiStep_sound (tm := target_tm) 26 ⟨E, 0, [0, 0, 0, 0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  tSweep_end := fun l =>
    ⟨2,
      Counter.rcmultiStep_sound (tm := target_tm) 2 ⟨E, 0, [0, 0, 0, 0, 1, 1], []⟩
    ⟨D, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩ l rfl⟩
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
    ⟨10,
      Counter.wmultiStep_sound (tm := target_tm) 10 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
        1], [1, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_Z_to_dSweep := fun l r =>
    ⟨13,
      Counter.wmultiStep_sound (tm := target_tm) 13 ⟨A, 1, [0, 0, 0, 0, 1, 1], [1]⟩
    ⟨E, 1, [0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  wSweep_ZT_to_dSweep := fun l r =>
    ⟨57,
      Counter.wmultiStep_sound (tm := target_tm) 57 ⟨A, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0,
        1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_PT_to_carry := fun l r =>
    ⟨46,
      Counter.wmultiStep_sound (tm := target_tm) 46 ⟨A, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 0,
        1, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]⟩ l r rfl⟩
  wSweep_ZMT_to_tSweep := fun l r =>
    ⟨83,
      Counter.wmultiStep_sound (tm := target_tm) 83 ⟨A, 1, [0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [1, 0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  cfgR_Z_to_TW := fun l =>
    ⟨20,
      Counter.rcmultiStep_sound (tm := target_tm) 20 ⟨D, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩
    ⟨D, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l rfl⟩
  cfgR_TW_to_t3Cfg := fun l =>
    ⟨32,
      Counter.rcmultiStep_sound (tm := target_tm) 32 ⟨D, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩ l rfl⟩
  t3_step := fun l r =>
    ⟨72,
      Counter.wmultiStep_sound (tm := target_tm) 72 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0,
        1, 0, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  t3Cfg_Z_zero_to_carry := fun l =>
    ⟨130,
      Counter.rcmultiStep_sound (tm := target_tm) 130 ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1,
        0, 1, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl⟩
  t3Cfg_Z_succ_to_r0 := fun l r =>
    ⟨39,
      Counter.wmultiStep_sound (tm := target_tm) 39 ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  t3Cfg_TZ_to_r1OddShort := fun l r =>
    ⟨57,
      Counter.wmultiStep_sound (tm := target_tm) 57 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0,
        0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  r1OddShortCfg_evalWK0_to_carry := fun l =>
    ⟨194,
      Counter.rcmultiStep_sound (tm := target_tm) 194 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl⟩
  t3Cfg_TTZ_to_r0 := fun l r =>
    ⟨85,
      Counter.wmultiStep_sound (tm := target_tm) 85 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1,
        1], [0, 1, 0, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩

-- `bmultiStep_sound` reduces 2,049 TM steps via `rfl`.
set_option maxRecDepth 2000000 in
theorem init_to_initRle :
    (init []) [target_tm]⊢* (carryCfg target_tm (evalRleAux default initRle) (evalWK 1)) :=
  ⟨2049, Counter.bmultiStep_sound (tm := target_tm) 2049 ⟨A, 0, [], []⟩
    ⟨D, 1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0,
      1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩

end Solution

public section

open Solution BusyBeaver.RleCarryEngine in
theorem is_halt : IsHalt target := by
  rcases runCarryChunks_sound (target_tm := target_tm) 28 500 initRle 1
      runCarryChunks_28_500 with ⟨cfg', hstep, hnone⟩
  exact ⟨cfg', stepStar_trans init_to_initRle hstep, hnone⟩

end

end BusyBeaver.M_1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LDHHH
