/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LBHHH

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RBHHH_0RC0LD_1RD1RC_1LB0LE_1LF0RA_0LD1LA

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_0RC0LD_1RD1RC_1LB0LE_1LF0RA_0LD1LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RBHHH_0RC0LD_1RD1RC_1LB0LE_1LF0RA_0LD1LA

end

namespace BusyBeaver.M_1RBHHH_0RC0LD_1RD1RC_1LB0LE_1LF0RA_0LD1LA

def stateMap_m0725 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 0

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LBHHH.target)
    (σ := stateMap_m0725) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LBHHH.is_not_halt_from_0559

end

end BusyBeaver.M_1RBHHH_0RC0LD_1RD1RC_1LB0LE_1LF0RA_0LD1LA
