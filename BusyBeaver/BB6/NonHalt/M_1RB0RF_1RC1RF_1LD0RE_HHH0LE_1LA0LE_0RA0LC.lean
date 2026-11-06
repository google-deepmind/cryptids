/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF0LA_HHH0RA

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB0RF_1RC1RF_1LD0RE_HHH0LE_1LA0LE_0RA0LC


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1RC1RF_1LD0RE_HHH0LE_1LA0LE_0RA0LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0471 : Fin 6 → Fin 6
  | 0 => 4 -- m0471 state A
  | 1 => 0 -- m0471 state B
  | 2 => 1 -- m0471 state C
  | 3 => 5 -- m0471 state D
  | 4 => 2 -- m0471 state E
  | 5 => 3 -- m0471 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF0LA_HHH0RA.target)
    (σ := stateMap_m0471) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{1}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF0LA_HHH0RA.is_not_halt_from_0471

end

end BusyBeaver.M_1RB0RF_1RC1RF_1LD0RE_HHH0LE_1LA0LE_0RA0LC
