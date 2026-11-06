/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RCHHH

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RBHHH_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0792 : Fin 6 → Fin 6
  | 0 => 4 -- m0792 state A
  | 1 => 3 -- m0792 state B
  | 2 => 1 -- m0792 state C
  | 3 => 2 -- m0792 state D
  | 4 => 5 -- m0792 state E
  | 5 => 0 -- m0792 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RCHHH.target)
    (σ := stateMap_m0792) (f := false)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RCHHH.is_not_halt_from_0792

end

end BusyBeaver.M_1RBHHH_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA
