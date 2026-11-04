/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RD_1RC0LC_1RE1RA_0LD1LA_0LF0LD_0REHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_1RC0LC_1RE1RA_0LD1LA_0LF0LD_0REHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

theorem trans_A0_0RD : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
theorem trans_B0_0RD : target B 0 = some (some C, Stmt.write 1 Dir.right) := rfl
theorem trans_C0_0RD : target C 0 = some (some E, Stmt.write 1 Dir.right) := rfl
theorem trans_E0_0RD : target E 0 = some (some F, Stmt.write 0 Dir.left) := rfl
theorem trans_F0_0RD : target F 0 = some (some E, Stmt.write 0 Dir.right) := rfl
theorem trans_F1_0RD : target F 1 = none := rfl

public section

theorem is_halt : IsHalt target :=
  is_halt_of_haltsAt target 4 (by decide +kernel)

end

end BusyBeaver.M_1RB0RD_1RC0LC_1RE1RA_0LD1LA_0LF0LD_0REHHH
