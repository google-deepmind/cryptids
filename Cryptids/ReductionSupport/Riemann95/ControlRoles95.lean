/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ControlStep95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open Schema

def unwindId : Fin 22 := 21
def finalTestId : Fin 97 := 95
def finalHaltId : Fin 97 := 96
def enterBodyId : Fin 22 := 0

def unwind (d : Nat) : ControlWord := .local d unwindId

theorem unwind_word (d : Nat) : word (unwind d) = callerPrefix d ++ [1,1,1,1,1] := rfl

theorem finalTest_word : word (.outside finalTestId) = [1,1,1,1,1,1] := rfl

theorem finalHalt_word : word (.outside finalHaltId) = [1,1,1,1,1,1,1] := rfl

theorem entry_zero : instruction (.entry 0) =
    .decnz 4 (.local 0 enterBodyId) (.outside finalTestId) := rfl

theorem entry_succ (d : Nat) : instruction (.entry (d+1)) =
    .decnz 4 (.local (d+1) enterBodyId) (unwind d) := rfl

theorem unwind_zero : instruction (unwind 0) =
    .decnz 2 (.outside finalTestId) (.outside 0) := rfl

theorem unwind_one : instruction (unwind 1) =
    .decnz 2 (unwind 0) (.outside finalTestId) := rfl

theorem unwind_succ_succ (d : Nat) : instruction (unwind (d+2)) =
    .decnz 2 (unwind (d+1)) (unwind d) := rfl

theorem final_test : instruction (.outside finalTestId) =
    .decnz 2 (.outside finalHaltId) (.outside 0) := rfl

theorem final_halt : instruction (.outside finalHaltId) = .halt := rfl

end ConjectureMachines.Riemann95.Control
