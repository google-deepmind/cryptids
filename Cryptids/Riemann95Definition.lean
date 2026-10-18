/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104

/-! 95-state machine and initial-root geometry. -/

@[expose] public section

namespace ConjectureMachines.Riemann95

open Turing ConjectureMachines

/-- 104-state Riemann Hypothesis reference machine. -/
abbrev reference : BundledMachine 2 := Machines.riemann104.bundle

/-- The 95-state machine loaded from the exported transition table. -/
abbrev machine : Machine 95 2 := Machines.riemann95

abbrev candidate : BundledMachine 2 := Machines.riemann95.bundle

def nSteps : Nat → Cfg 95 2 → Option (Cfg 95 2)
  | 0, c => some c
  | n + 1, c => (step machine c).bind (nSteps n)

def initialRegs : List Nat := [0,0,0,0,0]

def initialExtra : List Nat := List.replicate 4 0

def initialRoot : Cfg 95 2 :=
  ⟨15, Tape.mk' (ListBlank.cons 1 default)
    (ListBlank.mk
      (Riemann120.mapStack [] ++ List.replicate (22 - (Riemann120.mapStack []).length) 0 ++
        [1,0] ++ Semantics.Riemann.Layer1.encodeRegs (initialRegs ++ initialExtra)))⟩

end ConjectureMachines.Riemann95
