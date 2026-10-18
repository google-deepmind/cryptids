/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Layout
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Return
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95RawPhysical
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Swap

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary.Physical

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2
open ConjectureMachines.Semantics.Riemann.Layer1 (encodeRegs)

def decLeaf98 : Fin 5 → Fin 98
  | ⟨0, _⟩ => 18
  | ⟨1, _⟩ => 32
  | ⟨2, _⟩ => 56
  | ⟨3, _⟩ => 31
  | _ => 58

def incLeaf98 : Fin 5 → Fin 98
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 29
  | ⟨2, _⟩ => 79
  | ⟨3, _⟩ => 23
  | _ => 55

def rawRoot98 (pad : Nat) (w : List (Fin 2)) (bank : List Nat) : Cfg 98 2 :=
  ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append (w ++ List.replicate (pad - w.length) 0 ++ [1,
    0] ++ encodeRegs bank) default)⟩

theorem swap_incLeaf (r : Fin 5) :
    Renaming.swap (PhysicalRaw.incLeaf98 r) = incLeaf98 r := by fin_cases r <;> rfl

theorem swap_decLeaf (r : Fin 5) :
    Renaming.swap (PhysicalRaw.decLeaf98 r) = decLeaf98 r := by fin_cases r <;> rfl

theorem rename_rawRoot (pad : Nat) (word : List (Fin 2)) (bank : List Nat) :
    Renaming.renameCfg (PhysicalRaw.rawRoot98 pad word bank) = rawRoot98 pad word bank := rfl

theorem swap_fence (k : Fin 2) :
    Renaming.swap (if k = 0 then 9 else 63) = (if k = 0 then 9 else 63) := by fin_cases k <;> rfl

theorem nSteps98_eq (n : Nat) (c : Cfg 98 2) : nSteps n c =
  ConjectureMachines.Semantics.Riemann.Layer1.nSteps machine n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [nSteps, Semantics.Riemann.Layer1.nSteps, ih]

theorem decScanShift98 (suff : List Nat) (m : Nat) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, nSteps s
  ⟨74, Tape.mk' (ListBlank.append (ConjectureMachines.Semantics.Riemann.Layer1.encodeReg
  m).reverse (L.cons 0)) (ConjectureMachines.Semantics.Riemann.Layer1.regsTape suff)⟩ = some ⟨86,
  ConjectureMachines.Semantics.Riemann.Layer1.Tape.mkL L
  (ConjectureMachines.Semantics.Riemann.Layer1.regsTape (m :: (suff ++ [0])))⟩ := by
  obtain ⟨s, hs, h⟩ := PhysicalRaw.decScanShift98 suff m L
  refine ⟨s, hs, ?_⟩
  simpa only [Renaming.renameCfg, show Renaming.swap 74 = 74 from rfl,
    show Renaming.swap 86 = 86 from rfl] using Renaming.of_raw h

theorem fenceReturn98 (k : Fin 2) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill) (hk :
  k.val ≤ walked.count 0) (hguard : Riemann104.OnePassGuard.NoThreeZeros (1 :: (popBreakRev k.val
  walked.reverse).reverse).reverse = true) (bank : List Nat) : ∃ pad' ≥ walked.length + fill, ∃ s
  ≥ 1, nSteps s ⟨(if k = 0 then 9 else 63), Tape.mk' (ListBlank.append (List.replicate fill 1)
  (stackLeftOf true walked)) (ListBlank.append [0, 0]
  (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some (rawRoot98 pad'
  (popBreakRev k.val walked.reverse).reverse bank) := by
  obtain ⟨pad', hp, s, hs, h⟩ := PhysicalRaw.fenceReturn98 k walked fill hfill hk hguard bank
  refine ⟨pad', hp, s, hs, ?_⟩
  have ht := Renaming.of_raw h
  rw [rename_rawRoot] at ht
  simpa only [Renaming.renameCfg, swap_fence] using ht

theorem unary98_dec_pos (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length) (hpos : 0 <
  bank.getD r.val 0) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, nSteps s ⟨decLeaf98 r, Tape.mk' L
  (ListBlank.append [1, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some
  ⟨9, Tape.mk' L (ListBlank.append [0, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape
  (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])))⟩ := by
  obtain ⟨s, hs, h⟩ := PhysicalRaw.unary98_dec_pos r bank hr hpos L
  refine ⟨s, hs, ?_⟩
  simpa only [Renaming.renameCfg, swap_decLeaf,
    show Renaming.swap 9 = 9 from rfl] using Renaming.of_raw h

theorem unary98_dec_zero (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length) (hz : bank.getD
  r.val 0 = 0) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, nSteps s ⟨decLeaf98 r, Tape.mk' L
  (ListBlank.append [1, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some
  ⟨63, Tape.mk' L (ListBlank.append [0, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape
  bank))⟩ := by
  obtain ⟨s, hs, h⟩ := PhysicalRaw.unary98_dec_zero r bank hr hz L
  refine ⟨s, hs, ?_⟩
  simpa only [Renaming.renameCfg, swap_decLeaf,
    show Renaming.swap 63 = 63 from rfl] using Renaming.of_raw h

theorem unary98_inc (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length) (L : ListBlank (Fin
  2)) : ∃ s ≥ 1, nSteps s ⟨incLeaf98 r, Tape.mk' L (ListBlank.append [1, 0]
  (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some ⟨9, Tape.mk' L
  (ListBlank.append [0, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape (bank.set r.val
  (bank.getD r.val 0 + 1))))⟩ := by
  obtain ⟨s, hs, h⟩ := PhysicalRaw.unary98_inc r bank hr L
  refine ⟨s, hs, ?_⟩
  simpa only [Renaming.renameCfg, swap_incLeaf,
    show Renaming.swap 9 = 9 from rfl] using Renaming.of_raw h

end ConjectureMachines.Riemann95Auxiliary.Physical
