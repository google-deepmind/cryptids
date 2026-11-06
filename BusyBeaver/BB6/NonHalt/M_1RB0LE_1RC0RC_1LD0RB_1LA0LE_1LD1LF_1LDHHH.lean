/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0399 : Fin 6 → Fin 6
  | 0 => 2 -- m0399 state A
  | 1 => 3 -- m0399 state B
  | 2 => 0 -- m0399 state C
  | 3 => 1 -- m0399 state D
  | 4 => 4 -- m0399 state E
  | 5 => 5 -- m0399 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH.target)
    (σ := stateMap_m0399) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{2}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH.is_not_halt_from_0399

end

end BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH
