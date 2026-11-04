/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_HHH1RD

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_HHH1LC

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_HHH1LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_HHH1LC

end

namespace BusyBeaver.M_1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_HHH1LC

def stateMap_m0608 : Fin 6 → Fin 6
  | 0 => 4 -- m0608 state A
  | 1 => 0 -- m0608 state B
  | 2 => 1 -- m0608 state C
  | 3 => 2 -- m0608 state D
  | 4 => 3 -- m0608 state E
  | 5 => 5 -- m0608 state F

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_HHH1RD.target)
    (σ := stateMap_m0608) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{1}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_HHH1RD.is_not_halt_from_0608

end

end BusyBeaver.M_1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_HHH1LC
