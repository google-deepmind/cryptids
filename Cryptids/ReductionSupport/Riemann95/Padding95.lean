/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.PaddingRaw95
public import Cryptids.ReductionSupport.Riemann95.Physical95

@[expose] public section
namespace ConjectureMachines.Riemann95Auxiliary.Physical

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2
open ConjectureMachines.Semantics.Riemann.Layer1 (regsTape)

theorem fenceReturn_exact (k : Fin 2) (walked : List (Fin 2)) (fill : Nat)
    (hfill : 3 ≤ fill) (hk : k.val ≤ walked.count 0)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev k.val walked.reverse).reverse).reverse = true) (bank : List Nat) :
    ∃ s ≥ 1, nSteps s
      ⟨(if k = 0 then 9 else 63), Tape.mk'
        (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
        (ListBlank.append [0, 0] (regsTape bank))⟩ =
      some (rawRoot98 (PhysicalRaw.exactPad k walked fill)
        (popBreakRev k.val walked.reverse).reverse bank) := by
  obtain ⟨s, hs, h⟩ := PhysicalRaw.fenceReturn_exact k walked fill hfill hk hguard bank
  have ht := Renaming.of_raw h
  rw [rename_rawRoot] at ht
  refine ⟨s, hs, ?_⟩
  simpa only [Renaming.renameCfg, swap_fence] using ht

end ConjectureMachines.Riemann95Auxiliary.Physical

namespace ConjectureMachines.Riemann95.Physical

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2
open ConjectureMachines.Semantics.Riemann.Layer1 (regsTape)

abbrev exactPad := Riemann95Auxiliary.PhysicalRaw.exactPad

theorem exactPad_ge (k : Fin 2) (walked : List (Fin 2)) (fill : Nat) :
    walked.length + fill ≤ exactPad k walked fill := by
  unfold exactPad Riemann95Auxiliary.PhysicalRaw.exactPad
  omega

theorem exactPad_of_lt (k : Fin 2) (walked : List (Fin 2)) (fill : Nat)
    (h : k.val < walked.count 0) : exactPad k walked fill = walked.length + fill := by
  simp only [exactPad, Riemann95Auxiliary.PhysicalRaw.exactPad, h, ite_true, Nat.add_zero]

theorem exactPad_of_eq (k : Fin 2) (walked : List (Fin 2)) (fill : Nat)
    (h : k.val = walked.count 0) : exactPad k walked fill = walked.length + fill + 1 := by
  simp only [exactPad, Riemann95Auxiliary.PhysicalRaw.exactPad, h, lt_self_iff_false,
    ite_false]

/-- A genuine caller zero remains precisely when the root marker is not exhausted. -/
theorem popBreakRev_ne_nil (j : Nat) (rev : List (Fin 2)) (h : j < rev.count 0) :
    popBreakRev j rev ≠ [] := by
  induction rev generalizing j with
  | nil => simp only [List.count_nil] at h; omega
  | cons b xs ih =>
    rcases Semantics.Riemann.Layer1.fin2_cases b with rfl | rfl
    · cases j with
      | zero =>
        change (1 :: xs : List (Fin 2)) ≠ []
        intro hnil
        cases hnil
      | succ j =>
        have hj : j < xs.count 0 := by simp only [List.count_cons_self] at h; omega
        simpa only [popBreakRev, beq_self_eq_true, ↓reduceIte] using ih j hj
    · have hj : j < xs.count 0 := by
        simpa only [List.count_cons, show ((1 : Fin 2) == 0) = false from rfl,
          Bool.false_eq_true, ite_false, Nat.add_zero] using h
      have hp : popBreakRev j (1 :: xs) = popBreakRev j xs := by cases j <;> rfl
      rw [hp]
      exact ih j hj

theorem exactPad_of_return_empty (k : Fin 2) (walked : List (Fin 2)) (fill : Nat)
    (hk : k.val ≤ walked.count 0)
    (he : (popBreakRev k.val walked.reverse).reverse = []) :
    exactPad k walked fill = walked.length + fill + 1 := by
  have hp : popBreakRev k.val walked.reverse = [] := by
    have h := congrArg List.reverse he
    simpa only [List.reverse_reverse, List.reverse_nil] using h
  have hnot : ¬ k.val < walked.count 0 := by
    intro h
    exact popBreakRev_ne_nil k.val walked.reverse (by simpa only [List.count_reverse] using h) hp
  exact exactPad_of_eq k walked fill (by omega)

theorem macro_inc_exact (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 walked.reverse).reverse).reverse = true) :
    ∃ s ≥ 1, nSteps s
      ⟨incLeaf r, Tape.mk' (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0) (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rootCfg (exactPad 0 walked fill) (popBreakRev 0 walked.reverse).reverse
        (bank.set r.val (bank.getD r.val 0 + 1))) := by
  have hf := Riemann95Auxiliary.Physical.leaf98_fill r true fill (stackLeftOf true walked)
    (ListBlank.append [1, 0] (regsTape bank))
  obtain ⟨su, hsu, hu⟩ := Riemann95Auxiliary.Physical.unary98_inc r bank hr
    (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
  obtain ⟨sf, hsf, hret⟩ := Riemann95Auxiliary.Physical.fenceReturn_exact
    0 walked fill hfill (by simp) hguard (bank.set r.val (bank.getD r.val 0 + 1))
  have h := Riemann95Auxiliary.Return.nSteps_bind_eq
    (Riemann95Auxiliary.Return.nSteps_bind_eq hf hu) hret
  have ht := Projection.of_aux h
  rw [cfgMap_root] at ht
  exact ⟨fill + su + sf, by omega, ht⟩

theorem macro_dec_pos_exact (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (hpos : 0 < bank.getD r.val 0) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 walked.reverse).reverse).reverse = true) :
    ∃ s ≥ 1, nSteps s
      ⟨decLeaf r, Tape.mk' (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0) (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rootCfg (exactPad 0 walked fill) (popBreakRev 0 walked.reverse).reverse
        (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])) := by
  have hf := Riemann95Auxiliary.Physical.leaf98_fill r false fill (stackLeftOf true walked)
    (ListBlank.append [1, 0] (regsTape bank))
  obtain ⟨su, hsu, hu⟩ := Riemann95Auxiliary.Physical.unary98_dec_pos r bank hr hpos
    (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
  obtain ⟨sf, hsf, hret⟩ := Riemann95Auxiliary.Physical.fenceReturn_exact
    0 walked fill hfill (by simp) hguard (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])
  have h := Riemann95Auxiliary.Return.nSteps_bind_eq
    (Riemann95Auxiliary.Return.nSteps_bind_eq hf hu) hret
  have ht := Projection.of_aux h
  rw [cfgMap_root] at ht
  exact ⟨fill + su + sf, by omega, ht⟩

theorem macro_dec_zero_exact (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (hz : bank.getD r.val 0 = 0) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hk : 1 ≤ walked.count 0) (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 1 walked.reverse).reverse).reverse = true) :
    ∃ s ≥ 1, nSteps s
      ⟨decLeaf r, Tape.mk' (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0) (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rootCfg (exactPad 1 walked fill) (popBreakRev 1 walked.reverse).reverse bank) := by
  have hf := Riemann95Auxiliary.Physical.leaf98_fill r false fill (stackLeftOf true walked)
    (ListBlank.append [1, 0] (regsTape bank))
  obtain ⟨su, hsu, hu⟩ := Riemann95Auxiliary.Physical.unary98_dec_zero r bank hr hz
    (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
  obtain ⟨sf, hsf, hret⟩ := Riemann95Auxiliary.Physical.fenceReturn_exact
    1 walked fill hfill (by simpa only [Fin.val_one] using hk) hguard bank
  have h := Riemann95Auxiliary.Return.nSteps_bind_eq
    (Riemann95Auxiliary.Return.nSteps_bind_eq hf hu) hret
  have ht := Projection.of_aux h
  rw [cfgMap_root] at ht
  exact ⟨fill + su + sf, by omega, ht⟩

end ConjectureMachines.Riemann95.Physical
