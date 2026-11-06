/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB1LA_1LA1RC_1RD0RB_1LE0LF_HHH1LD_0LE1LA


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LA1RC_1RD0RB_1LE0LF_HHH1LD_0LE1LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0831 : Fin 6 → Fin 6
  | 0 => 1 -- m0831 state A
  | 1 => 0 -- m0831 state B
  | 2 => 2 -- m0831 state C
  | 3 => 3 -- m0831 state D
  | 4 => 4 -- m0831 state E
  | 5 => 5 -- m0831 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_src := BusyBeaver.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB.target)
    (σ := stateMap_m0831) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{1}}> default)
    (by decide) ⟨0, rfl⟩
    BusyBeaver.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB.is_not_halt_from_0831

end

end BusyBeaver.M_1RB1LA_1LA1RC_1RD0RB_1LE0LF_HHH1LD_0LE1LA
