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

namespace BusyBeaver.M_1RB1LF_0RCHHH_1RD1RF_1LE0LF_1LB0LA_1LD0RE

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RCHHH_1RD1RF_1LE0LF_1LB0LA_1LD0RE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

def stateMap_m0554 : Fin 6 → Fin 6
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.target)
    (σ := stateMap_m0554) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.is_not_halt_from_0554

end

end BusyBeaver.M_1RB1LF_0RCHHH_1RD1RF_1LE0LF_1LB0LA_1LD0RE
