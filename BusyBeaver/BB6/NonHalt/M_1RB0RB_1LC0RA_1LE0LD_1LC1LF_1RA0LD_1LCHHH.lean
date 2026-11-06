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


namespace BusyBeaver.M_1RB0RB_1LC0RA_1LE0LD_1LC1LF_1RA0LD_1LCHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_1LC0RA_1LE0LD_1LC1LF_1RA0LD_1LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0457 : Fin 6 → Fin 6
  | 0 => 1 -- m0457 state A
  | 1 => 2 -- m0457 state B
  | 2 => 4 -- m0457 state C
  | 3 => 0 -- m0457 state D
  | 4 => 3 -- m0457 state E
  | 5 => 5 -- m0457 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH.target)
    (σ := stateMap_m0457) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{3}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH.is_not_halt_from_0457

end

end BusyBeaver.M_1RB0RB_1LC0RA_1LE0LD_1LC1LF_1RA0LD_1LCHHH
