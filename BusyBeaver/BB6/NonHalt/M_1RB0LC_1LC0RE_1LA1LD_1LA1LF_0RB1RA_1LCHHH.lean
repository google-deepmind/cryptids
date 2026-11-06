/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE


open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LCHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

open BusyBeaver.Longitudinal
open BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE

public section

set_option maxHeartbeats 2000000 in
-- Justification: Finite computation of the 17 elementary tile rules and initial stem.
theorem is_not_halt : IsNotHalt target := by
  refine does_not_halt_of_elem_rules target
    (mkElemRules (flipTM target)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold stateCfg toDHCfg left1
  dsimp [tape, word]
  bb_steps

end

end BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LCHHH
