/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LCHHH

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RBHHH_0RC1LF_0RD1RB_1LE1RC_0LB0LE_0LE0LA

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_0RC1LF_0RD1RB_1LE1RC_0LB0LE_0LE0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RBHHH_0RC1LF_0RD1RB_1LE1RC_0LB0LE_0LE0LA

end

namespace BusyBeaver.M_1RBHHH_0RC1LF_0RD1RB_1LE1RC_0LB0LE_0LE0LA

def stateMap_m0715 : Fin 6 → Fin 6
  | 0 => 3 -- m0715 state A
  | 1 => 4 -- m0715 state B
  | 2 => 1 -- m0715 state C
  | 3 => 2 -- m0715 state D
  | 4 => 5 -- m0715 state E
  | 5 => 0 -- m0715 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_src := BusyBeaver.M_1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LCHHH.target)
    (σ := stateMap_m0715) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) ⟨0, rfl⟩
    BusyBeaver.M_1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LCHHH.is_not_halt_from_0715

end

end BusyBeaver.M_1RBHHH_0RC1LF_0RD1RB_1LE1RC_0LB0LE_0LE0LA
