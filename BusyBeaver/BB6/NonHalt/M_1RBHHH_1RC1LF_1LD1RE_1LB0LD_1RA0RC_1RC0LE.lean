/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE

end

namespace BusyBeaver.M_1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE

def stateMap_m0781 : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 0

public section

theorem is_not_halt : IsNotHalt target := by
  exact Counter.does_not_halt_of_conj_stem
    (M_tgt := target)
    (M_src := BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.target)
    (σ := stateMap_m0781) (f := true)
    (c₁ := (default : ListBlank (Fin 2)) {{5}}> default)
    (by decide) (Counter.init_reaches_conjCfg_default rfl)
    BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.is_not_halt_from_0757

end

end BusyBeaver.M_1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE
