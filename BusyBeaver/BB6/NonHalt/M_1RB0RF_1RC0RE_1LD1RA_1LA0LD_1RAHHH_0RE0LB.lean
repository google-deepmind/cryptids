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

@[expose] public section

namespace BusyBeaver.M_1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB

end

namespace BusyBeaver.M_1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB

def stateMap_m0693 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 5 => 5

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0RA_1LC0LF_1LE0LD_1LBHHH_1RA1LB_0LD0RC.target)
    (σ := stateMap_m0693) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{1}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0RA_1LC0LF_1LE0LD_1LBHHH_1RA1LB_0LD0RC.is_not_halt_from_0446

end

end BusyBeaver.M_1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB
