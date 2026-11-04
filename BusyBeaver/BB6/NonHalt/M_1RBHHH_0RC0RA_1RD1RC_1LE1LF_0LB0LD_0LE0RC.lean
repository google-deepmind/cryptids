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

@[expose] public section

namespace BusyBeaver.M_1RBHHH_0RC0RA_1RD1RC_1LE1LF_0LB0LD_0LE0RC

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_0RC0RA_1RD1RC_1LE1LF_0LB0LD_0LE0RC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RBHHH_0RC0RA_1RD1RC_1LE1LF_0LB0LD_0LE0RC

end

namespace BusyBeaver.M_1RBHHH_0RC0RA_1RD1RC_1LE1LF_0LB0LD_0LE0RC

def stateMap_m0724 : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 5
  | 5 => 0

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH.target)
    (σ := stateMap_m0724) (f := false)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH.is_not_halt_from_0713

end

end BusyBeaver.M_1RBHHH_0RC0RA_1RD1RC_1LE1LF_0LB0LD_0LE0RC
