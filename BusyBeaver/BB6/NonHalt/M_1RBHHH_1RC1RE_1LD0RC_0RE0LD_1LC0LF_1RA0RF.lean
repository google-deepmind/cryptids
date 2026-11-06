/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LFHHH_1LA1LC

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RBHHH_1RC1RE_1LD0RC_0RE0LD_1LC0LF_1RA0RF


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1RC1RE_1LD0RC_0RE0LD_1LC0LF_1RA0RF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


def stateMap_m0772 : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LFHHH_1LA1LC.target)
    (σ := stateMap_m0772) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{4}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LFHHH_1LA1LC.is_not_halt_from_0772

end

end BusyBeaver.M_1RBHHH_1RC1RE_1LD0RC_0RE0LD_1LC0LF_1RA0RF
