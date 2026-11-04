/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LFHHH_1LA1LC

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH

end

namespace BusyBeaver.M_1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH

def stateMap_m0676 : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 0

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LFHHH_1LA1LC.target)
    (σ := stateMap_m0676) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LFHHH_1LA1LC.is_not_halt_from_0676

end

end BusyBeaver.M_1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH
