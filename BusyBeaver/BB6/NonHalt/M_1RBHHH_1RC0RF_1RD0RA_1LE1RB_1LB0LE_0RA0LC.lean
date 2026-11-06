/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0RA_1LC0LF_1LE0LD_1LBHHH_1RA1LB_0LD0RC

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RBHHH_1RC0RF_1RD0RA_1LE1RB_1LB0LE_0RA0LC


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1RC0RF_1RD0RA_1LE1RB_1LB0LE_0RA0LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0762 : Fin 6 → Fin 6
  | 0 => 4
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 3
  | 5 => 5

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0RA_1LC0LF_1LE0LD_1LBHHH_1RA1LB_0LD0RC.target)
    (σ := stateMap_m0762) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{3}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0RA_1LC0LF_1LE0LD_1LBHHH_1RA1LB_0LD0RC.is_not_halt_from_0756

end

end BusyBeaver.M_1RBHHH_1RC0RF_1RD0RA_1LE1RB_1LB0LE_0RA0LC
