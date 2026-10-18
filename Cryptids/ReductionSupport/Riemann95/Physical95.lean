/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Projection95
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Contracts

@[expose] public section
namespace ConjectureMachines.Riemann95.Physical

open Turing ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1 (regsTape encodeRegs)

def incLeaf (r : Fin 5) : Fin 95 :=
  Projection.stateMap (Riemann95Auxiliary.Physical.incLeaf98 r)

def decLeaf (r : Fin 5) : Fin 95 :=
  Projection.stateMap (Riemann95Auxiliary.Physical.decLeaf98 r)

def rootCfg (pad : Nat) (word : List (Fin 2)) (bank : List Nat) : Cfg 95 2 :=
  ⟨15, Tape.mk' (ListBlank.cons 1 default)
    (ListBlank.mk (word ++ List.replicate (pad - word.length) 0 ++
      [1, 0] ++ encodeRegs bank))⟩

theorem cfgMap_root (pad : Nat) (word : List (Fin 2)) (bank : List Nat) :
    Projection.cfgMap (Riemann95Auxiliary.Physical.rawRoot98 pad word bank) =
      rootCfg pad word bank := by
  have h := Riemann95Auxiliary.Physical.rawRoot98_eq_layout pad word bank []
  simp only [List.append_nil] at h
  rw [h]
  simp only [Riemann95Auxiliary.rawRootCfg, Projection.cfgMap, rootCfg, List.append_nil]
  rfl

theorem initialRoot_eq_rootCfg :
    initialRoot = rootCfg 22 [] (initialRegs ++ initialExtra) := rfl

end ConjectureMachines.Riemann95.Physical
