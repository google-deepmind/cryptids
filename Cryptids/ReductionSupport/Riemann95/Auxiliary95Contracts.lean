/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Physical

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary.Physical

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2
open ConjectureMachines.Semantics.Riemann.Layer1 (regsTape)

theorem rawRoot98_eq_layout (pad : Nat) (word : List (Fin 2)) (regs extra : List Nat) :
    rawRoot98 pad word (regs ++ extra) = rawRootCfg pad word regs extra := by
  simp only [rawRoot98, rawRootCfg, rootLeftOf, ite_true,
    Semantics.Riemann.Layer1.default_eq_mk_nil, ListBlank.append_mk, List.append_nil]

theorem leaf98_fill (r : Fin 5) (inc : Bool) (fill : Nat)
    (L R : ListBlank (Fin 2)) : nSteps fill
      ⟨if inc then incLeaf98 r else decLeaf98 r,
        Tape.mk' L (ListBlank.append (List.replicate fill 0) R)⟩ =
      some ⟨if inc then incLeaf98 r else decLeaf98 r,
        Tape.mk' (ListBlank.append (List.replicate fill 1) L) R⟩ := by
  apply Return.right_scan
  have h : ∀ (r : Fin 5) (inc : Bool),
      machine.transition (if inc then incLeaf98 r else decLeaf98 r) 0 =
        some (1, .right, if inc then incLeaf98 r else decLeaf98 r) := by decide
  exact h r inc

end ConjectureMachines.Riemann95Auxiliary.Physical
