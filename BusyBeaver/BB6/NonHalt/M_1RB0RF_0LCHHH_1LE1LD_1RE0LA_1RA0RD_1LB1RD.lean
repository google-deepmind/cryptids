/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RF_0LCHHH_1LE1LD_1RE0LA_1RA0RD_1LB1RD

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_0LCHHH_1LE1LD_1RE0LA_1RA0RD_1LB1RD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

def stateMap_m0221 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 5

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.target)
    (σ := stateMap_m0221) (f := false)
    (c₁ := (default : ListBlank (Fin 2)) {{2}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.is_not_halt_from_0221

end

end BusyBeaver.M_1RB0RF_0LCHHH_1LE1LD_1RE0LA_1RA0RD_1LB1RD
