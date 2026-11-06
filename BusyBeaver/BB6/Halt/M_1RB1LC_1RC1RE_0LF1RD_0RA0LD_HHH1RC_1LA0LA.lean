/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

theorem trans_A0_1LC : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
theorem trans_B0_1LC : target B 0 = some (some C, Stmt.write 1 Dir.right) := rfl
theorem trans_C0_1LC : target C 0 = some (some F, Stmt.write 0 Dir.left) := rfl
theorem trans_F1_1LC : target F 1 = some (some A, Stmt.write 0 Dir.left) := rfl
theorem trans_E0_1LC : target E 0 = none := rfl
theorem trans_E1_1LC : target E 1 = some (some C, Stmt.write 1 Dir.right) := rfl

public section

theorem is_halt : IsHalt target :=
  is_halt_of_haltsAt target 9 (by decide +kernel)

end

end BusyBeaver.M_1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA
