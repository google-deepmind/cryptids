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


namespace BusyBeaver.M_1RB1RF_1LC0RD_HHH0LD_1LE0LD_1RA0RF_0RE0LB


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC0RD_HHH0LD_1LE0LD_1RA0RF_0RE0LB"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0689 : Fin 6 → Fin 6
  | 0 => 3 -- m0689 state A
  | 1 => 4 -- m0689 state B
  | 2 => 0 -- m0689 state C
  | 3 => 5 -- m0689 state D
  | 4 => 1 -- m0689 state E
  | 5 => 2 -- m0689 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF0LA_HHH0RA.target)
    (σ := stateMap_m0689) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{2}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF0LA_HHH0RA.is_not_halt_from_0689

end

end BusyBeaver.M_1RB1RF_1LC0RD_HHH0LD_1LE0LD_1RA0RF_0RE0LB
