/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB1LA_1LC0RA_0LD1RC_HHH0LE_0LF1LE_1RF1LB

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState
open BusyBeaver.M_1RB1LA_1LC0RA_0LD1RC_HHH0LE_0LF1LE_1RF1LB

namespace BusyBeaver.M_1RB1LC_1RC1LB_1LD0RB_0LE1RD_HHH0LF_0LA1LF

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC1LB_1LD0RB_0LE1RD_HHH0LF_0LA1LF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

set_option maxHeartbeats 2000000 in
-- Justification: Finite symbolic execution of the 15 elementary stack rules.
theorem is_not_halt : IsNotHalt target := by
  refine does_not_halt_of_stack_rules
    (mkStackRules target 2 3 5 1
      (fun _ _ => by execute)
      (fun _ _ _ => by execute)
      (fun _ _ _ => by execute)
      (fun _ _ => by execute)
      (fun _ _ _ => by execute)
      (fun _ _ _ => by execute)
      (fun _ _ _ _ => by execute)
      (fun _ _ _ => by execute)
      (fun _ _ _ _ => by execute)
      (fun _ _ _ _ => by execute)
      (fun _ => by execute)
      (by execute_init)
      (by execute_init)
      (by execute_init)
      (by execute_init))

end BusyBeaver.M_1RB1LC_1RC1LB_1LD0RB_0LE1RD_HHH0LF_0LA1LF
