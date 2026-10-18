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

/-- All arithmetic inputs remain arbitrary natural banks; only the caller guard is required. -/
theorem macro_inc (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (Riemann120.Layer2.popBreakRev 0 walked.reverse).reverse).reverse = true) :
    ∃ pad' ≥ walked.length + fill, ∃ s ≥ 1, nSteps s
      ⟨incLeaf r, Tape.mk' (Riemann120.stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0)
          (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rootCfg pad' (Riemann120.Layer2.popBreakRev 0 walked.reverse).reverse
        (bank.set r.val (bank.getD r.val 0 + 1))) := by
  obtain ⟨pad', hp, s, hs, h⟩ :=
    Riemann95Auxiliary.Physical.macro98_inc r bank hr walked fill hfill hguard
  have ht := Projection.of_aux h
  rw [cfgMap_root] at ht
  exact ⟨pad', hp, s, hs, ht⟩

theorem macro_dec_pos (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (hpos : 0 < bank.getD r.val 0) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (Riemann120.Layer2.popBreakRev 0 walked.reverse).reverse).reverse = true) :
    ∃ pad' ≥ walked.length + fill, ∃ s ≥ 1, nSteps s
      ⟨decLeaf r, Tape.mk' (Riemann120.stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0)
          (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rootCfg pad' (Riemann120.Layer2.popBreakRev 0 walked.reverse).reverse
        (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])) := by
  obtain ⟨pad', hp, s, hs, h⟩ :=
    Riemann95Auxiliary.Physical.macro98_dec_pos r bank hr hpos walked fill hfill hguard
  have ht := Projection.of_aux h
  rw [cfgMap_root] at ht
  exact ⟨pad', hp, s, hs, ht⟩

theorem macro_dec_zero (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (hz : bank.getD r.val 0 = 0) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hk : 1 ≤ walked.count 0) (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (Riemann120.Layer2.popBreakRev 1 walked.reverse).reverse).reverse = true) :
    ∃ pad' ≥ walked.length + fill, ∃ s ≥ 1, nSteps s
      ⟨decLeaf r, Tape.mk' (Riemann120.stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0)
          (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rootCfg pad' (Riemann120.Layer2.popBreakRev 1 walked.reverse).reverse bank) := by
  obtain ⟨pad', hp, s, hs, h⟩ :=
    Riemann95Auxiliary.Physical.macro98_dec_zero r bank hr hz walked fill hfill hk hguard
  have ht := Projection.of_aux h
  rw [cfgMap_root] at ht
  exact ⟨pad', hp, s, hs, ht⟩

end ConjectureMachines.Riemann95.Physical
