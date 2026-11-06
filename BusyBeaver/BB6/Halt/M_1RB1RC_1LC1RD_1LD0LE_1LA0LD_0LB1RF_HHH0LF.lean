/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB1RC_1LC1RD_1LD0LE_1LA0LD_0LB1RF_HHH0LF

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1RD_1LD0LE_1LA0LD_0LB1RF_HHH0LF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

theorem trans_A0_1RC : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
theorem trans_B0_1RC : target B 0 = some (some C, Stmt.write 1 Dir.left) := rfl
theorem trans_C1_1RC : target C 1 = some (some E, Stmt.write 0 Dir.left) := rfl
theorem trans_D1_1RC : target D 1 = some (some D, Stmt.write 0 Dir.left) := rfl
theorem trans_F0_1RC : target F 0 = none := rfl
theorem trans_F1_1RC : target F 1 = some (some F, Stmt.write 0 Dir.left) := rfl

public section

theorem is_halt : IsHalt target :=
  is_halt_of_haltsAt target 19 (by decide +kernel)

end

end BusyBeaver.M_1RB1RC_1LC1RD_1LD0LE_1LA0LD_0LB1RF_HHH0LF
