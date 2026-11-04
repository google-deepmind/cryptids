/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RAHHH

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB0RE_1LC0RA_1LD0LB_1LA1LF_1LE1RA_0LCHHH

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1LD0LB_1LA1LF_1LE1RA_0LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB0RE_1LC0RA_1LD0LB_1LA1LF_1LE1RA_0LCHHH

end

namespace BusyBeaver.M_1RB0RE_1LC0RA_1LD0LB_1LA1LF_1LE1RA_0LCHHH

def stateMap_m0685 : Fin 6 → Fin 6
  | 0 => 2 -- m0685 state A
  | 1 => 3 -- m0685 state B
  | 2 => 0 -- m0685 state C
  | 3 => 1 -- m0685 state D
  | 4 => 4 -- m0685 state E
  | 5 => 5 -- m0685 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_src := BusyBeaver.M_1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RAHHH.target)
    (σ := stateMap_m0685) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{2}}> default)
    (by decide) ⟨0, rfl⟩
    BusyBeaver.M_1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RAHHH.is_not_halt_from_0685

end

end BusyBeaver.M_1RB0RE_1LC0RA_1LD0LB_1LA1LF_1LE1RA_0LCHHH
