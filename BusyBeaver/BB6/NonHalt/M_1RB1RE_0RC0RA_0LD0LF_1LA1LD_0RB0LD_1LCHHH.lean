/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB1RE_0RC0RA_0LD0LF_1LA1LD_0RB0LD_1LCHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_0RC0RA_0LD0LF_1LA1LD_0RB0LD_1LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0699 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 5

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH.target)
    (σ := stateMap_m0699) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{1}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH.is_not_halt_from_0682

end

end BusyBeaver.M_1RB1RE_0RC0RA_0LD0LF_1LA1LD_0RB0LD_1LCHHH
