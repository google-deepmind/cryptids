/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB0RC_1LC1RA_0RF0LD_1LE0RB_1LB0LD_HHH1RD


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC1RA_0RF0LD_1LE0RB_1LB0LD_HHH1RD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0426 : Fin 6 → Fin 6
  | 0 => 4 -- m0426 state A
  | 1 => 1 -- m0426 state B
  | 2 => 2 -- m0426 state C
  | 3 => 5 -- m0426 state D
  | 4 => 3 -- m0426 state E
  | 5 => 0 -- m0426 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_src := BusyBeaver.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC.target)
    (σ := stateMap_m0426) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) ⟨0, rfl⟩
    BusyBeaver.M_1RB0RE_1RC1LF_0LD0RE_HHH1LE_1RA0LB_1LB0LC.is_not_halt_from_0426

end

end BusyBeaver.M_1RB0RC_1LC1RA_0RF0LD_1LE0RB_1LB0LD_HHH1RD
