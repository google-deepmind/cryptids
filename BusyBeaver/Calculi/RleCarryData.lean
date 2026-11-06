/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.RleCarryEngine

/-!
# Run-Length Encoded Carry Data (`BusyBeaver.Calculi.RleCarryData`)

Precomputed run-length encoded tape patterns and check-point configurations
for multi-digit carry-propagation engines.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.RleCarryEngine

def machine521 : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_HHH1LC"

abbrev tm521 : Machine (Fin 2) (Fin 6) := machine521.toBB

set_option maxRecDepth 4000000 in
instance : HasRleCarryRules tm521 where
  carry_Z := fun l r =>
    ⟨54,
      Counter.wmultiStep_sound (tm := tm521) 54 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_P := fun l r =>
    ⟨18,
      Counter.wmultiStep_sound (tm := tm521) 18 ⟨B, 1, [0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1,
        1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_PMUTM := fun l r =>
    ⟨78,
      Counter.wmultiStep_sound (tm := tm521) 78 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0,
        0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTW := fun l r =>
    ⟨120,
      Counter.wmultiStep_sound (tm := tm521) 120 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTT := fun l r =>
    ⟨84,
      Counter.wmultiStep_sound (tm := tm521) 84 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0,
        0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1]⟩ l r rfl⟩
  carry_PTTTM := fun l r =>
    ⟨99,
      Counter.wmultiStep_sound (tm := tm521) 99 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
        0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1, 1, 0, 1]⟩ l r rfl⟩
  turn_UM := fun r =>
    ⟨61,
      Counter.cmultiStep_sound (tm := tm521) 61 ⟨B, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1,
        0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1], []⟩ r rfl⟩
  turn_UMT := fun r =>
    ⟨97,
      Counter.cmultiStep_sound (tm := tm521) 97 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1,
        0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], []⟩ r rfl⟩
  turn_ZT := fun l r =>
    ⟨61,
      Counter.wmultiStep_sound (tm := tm521) 61 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_WM := fun l r =>
    ⟨55,
      Counter.wmultiStep_sound (tm := tm521) 55 ⟨B, 1, [0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0,
        1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PT := fun l r =>
    ⟨115,
      Counter.wmultiStep_sound (tm := tm521) 115 ⟨B, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0,
        1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZM := fun l r =>
    ⟨55,
      Counter.wmultiStep_sound (tm := tm521) 55 ⟨B, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1,
        0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  turn_PTW := fun l r =>
    ⟨141,
      Counter.wmultiStep_sound (tm := tm521) 141 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl⟩
  turn_PTM := fun l r =>
    ⟨97,
      Counter.wmultiStep_sound (tm := tm521) 97 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PTT := fun l r =>
    ⟨103,
      Counter.wmultiStep_sound (tm := tm521) 103 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl⟩
  turn_ZMU := fun l r =>
    ⟨111,
      Counter.wmultiStep_sound (tm := tm521) 111 ⟨B, 1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0,
        0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTM := fun l r =>
    ⟨121,
      Counter.wmultiStep_sound (tm := tm521) 121 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTT := fun l r =>
    ⟨127,
      Counter.wmultiStep_sound (tm := tm521) 127 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_ZTW := fun l r =>
    ⟨127,
      Counter.wmultiStep_sound (tm := tm521) 127 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_MUTW := fun l r =>
    ⟨141,
      Counter.wmultiStep_sound (tm := tm521) 141 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1], [0,
        1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  turn_PTTM := fun l r =>
    ⟨163,
      Counter.wmultiStep_sound (tm := tm521) 163 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0,
        0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTW := fun l r =>
    ⟨163,
      Counter.wmultiStep_sound (tm := tm521) 163 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTM := fun l r =>
    ⟨109,
      Counter.wmultiStep_sound (tm := tm521) 109 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0,
        0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
      []⟩ l r rfl⟩
  turn_ZPMU := fun l r =>
    ⟨163,
      Counter.wmultiStep_sound (tm := tm521) 163 ⟨B, 1, [0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0,
        0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
      []⟩ l r rfl⟩
  turn_ZMUTM := fun l r =>
    ⟨157,
      Counter.wmultiStep_sound (tm := tm521) 157 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_PTTTW := fun l r =>
    ⟨205,
      Counter.wmultiStep_sound (tm := tm521) 205 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
        1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
      0, 1, 1, 1], []⟩ l r rfl⟩
  carry_MU_to_pmuCfg := fun l r =>
    ⟨17,
      Counter.wmultiStep_sound (tm := tm521) 17 ⟨B, 1, [0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1,
        0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmu_step := fun l r =>
    ⟨60,
      Counter.wmultiStep_sound (tm := tm521) 60 ⟨D, 1, [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1,
        0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmuCfg_Z_turn := fun l r =>
    ⟨38,
      Counter.wmultiStep_sound (tm := tm521) 38 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1,
        0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  pmuCfg_M_to_carry := fun l r =>
    ⟨7,
      Counter.wmultiStep_sound (tm := tm521) 7 ⟨D, 1, [0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  pmuCfg_T_to_carry := fun l r =>
    ⟨7,
      Counter.wmultiStep_sound (tm := tm521) 7 ⟨D, 1, [0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  carry_PTU := fun l r =>
    ⟨30,
      Counter.wmultiStep_sound (tm := tm521) 30 ⟨B, 1, [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1,
        0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  turn_PTMT := fun l r =>
    ⟨163,
      Counter.wmultiStep_sound (tm := tm521) 163 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0,
        0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTT := fun l r =>
    ⟨163,
      Counter.wmultiStep_sound (tm := tm521) 163 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0,
        0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      []⟩ l r rfl⟩
  turn_ZTTTM := fun l r =>
    ⟨145,
      Counter.wmultiStep_sound (tm := tm521) 145 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
        1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      0, 1, 1], []⟩ l r rfl⟩
  turn_ZTU_halt := fun l r =>
    ⟨_, ⟨33,
      Counter.wmultiStep_sound (tm := tm521) 33 ⟨B, 1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1,
        0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨F, 0, [1, 1, 0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl⟩, rfl⟩
  r0_Z := fun l r =>
    ⟨12,
      Counter.wmultiStep_sound (tm := tm521) 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1,
        1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r0_P := fun l r =>
    ⟨48,
      Counter.wmultiStep_sound (tm := tm521) 48 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1,
        1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  r0_PTTTM_TAIL := fun l r =>
    ⟨15,
      Counter.wmultiStep_sound (tm := tm521) 15 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1,
        0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_Z := fun l r =>
    ⟨12,
      Counter.wmultiStep_sound (tm := tm521) 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_P := fun l r =>
    ⟨68,
      Counter.wmultiStep_sound (tm := tm521) 68 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1OddShort_Z := fun l r =>
    ⟨12,
      Counter.wmultiStep_sound (tm := tm521) 12 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1Odd_P := fun l r =>
    ⟨10,
      Counter.wmultiStep_sound (tm := tm521) 10 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_start := fun l =>
    ⟨2,
      Counter.rcmultiStep_sound (tm := tm521) 2 ⟨B, 0, [1, 1], []⟩
    ⟨D, 1, [], [1]⟩ l rfl⟩
  wSweep_step := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := tm521) 6 ⟨D, 1, [0, 0, 1, 1], [1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 1]⟩ l r rfl⟩
  dSweep_step := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := tm521) 6 ⟨E, 1, [0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  dSweep_end := fun l =>
    ⟨5,
      Counter.rcmultiStep_sound (tm := tm521) 5 ⟨E, 1, [0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1], []⟩ l rfl⟩
  tSweep_step := fun l r =>
    ⟨24,
      Counter.wmultiStep_sound (tm := tm521) 24 ⟨E, 0, [0, 0, 0, 0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  tSweep_end := fun l =>
    ⟨2,
      Counter.rcmultiStep_sound (tm := tm521) 2 ⟨E, 0, [0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩ l rfl⟩
  r0_to_dSweep := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := tm521) 6 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1,
        1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1_to_dSweep := fun l r =>
    ⟨6,
      Counter.wmultiStep_sound (tm := tm521) 6 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [1, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  r1Odd_to_tSweep := fun l r =>
    ⟨10,
      Counter.wmultiStep_sound (tm := tm521) 10 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1],
        [1, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_Z_to_dSweep := fun l r =>
    ⟨11,
      Counter.wmultiStep_sound (tm := tm521) 11 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1]⟩
    ⟨E, 1, [0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  wSweep_ZT_to_dSweep := fun l r =>
    ⟨53,
      Counter.wmultiStep_sound (tm := tm521) 53 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1,
        1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  wSweep_PT_to_carry := fun l r =>
    ⟨40,
      Counter.wmultiStep_sound (tm := tm521) 40 ⟨D, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 0, 1,
        1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]⟩ l r rfl⟩
  wSweep_ZMT_to_tSweep := fun l r =>
    ⟨77,
      Counter.wmultiStep_sound (tm := tm521) 77 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1,
        0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  cfgR_Z_to_TW := fun l =>
    ⟨18,
      Counter.rcmultiStep_sound (tm := tm521) 18 ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l rfl⟩
  cfgR_TW_to_t3Cfg := fun l =>
    ⟨30,
      Counter.rcmultiStep_sound (tm := tm521) 30 ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩ l rfl⟩
  t3_step := fun l r =>
    ⟨66,
      Counter.wmultiStep_sound (tm := tm521) 66 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1,
        0, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl⟩
  t3Cfg_Z_zero_to_carry := fun l =>
    ⟨120,
      Counter.rcmultiStep_sound (tm := tm521) 120 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0,
        1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl⟩
  t3Cfg_Z_succ_to_r0 := fun l r =>
    ⟨37,
      Counter.wmultiStep_sound (tm := tm521) 37 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1,
        1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl⟩
  t3Cfg_TZ_to_r1OddShort := fun l r =>
    ⟨51,
      Counter.wmultiStep_sound (tm := tm521) 51 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0,
        1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩
  r1OddShortCfg_evalWK0_to_carry := fun l =>
    ⟨180,
      Counter.rcmultiStep_sound (tm := tm521) 180 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl⟩
  t3Cfg_TTZ_to_r0 := fun l r =>
    ⟨79,
      Counter.wmultiStep_sound (tm := tm521) 79 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
        [0, 1, 0, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl⟩

def ckptRle_0 : Rle :=
  [([.Z], 6), ([.M], 1), ([.T], 1), ([.Z], 4), ([.P], 5), ([.Z], 1), ([.U], 1)]

def initRle : Rle :=
  pushToksLtr [.U, .M, .Z, .Z, .P, .T, .M, .Z, .Z] []

set_option maxRecDepth 4000000 in
theorem runCarryTruncChunks_ckpt0 :
    runCarryTruncChunks [3746, 3999, 4000, 4000, 4000, 4000, 4000, 3298] 30 ckptRle_0 1 = true := by
  decide +kernel

set_option maxRecDepth 4000000 in
theorem runCarryChunks_28_500 :
    runCarryChunks 28 500 initRle 1 = true := by
  decide +kernel

end BusyBeaver.RleCarryEngine
