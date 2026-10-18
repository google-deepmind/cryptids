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

/-- Each of the five selectors preserves the entire extra register suffix. -/
theorem unary98_inc_five (r : Fin 5) (regs extra : List Nat) (hlen : regs.length = 5)
    (L : ListBlank (Fin 2)) : ∃ s ≥ 1, nSteps s
      ⟨incLeaf98 r, Tape.mk' L (ListBlank.append [1, 0] (regsTape (regs ++ extra)))⟩ =
        some ⟨9, Tape.mk' L (ListBlank.append [0, 0]
          (regsTape (regs.set r.val (regs.getD r.val 0 + 1) ++ extra)))⟩ := by
  have hr : r.val < regs.length := by omega
  simpa only [List.getD_append regs extra 0 r.val hr, List.set_append_left _ _ hr] using
    unary98_inc r (regs ++ extra) (by simp only [List.length_append]; omega) L

theorem unary98_dec_pos_five (r : Fin 5) (regs extra : List Nat) (hlen : regs.length = 5)
    (hpos : 0 < regs.getD r.val 0) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, nSteps s
      ⟨decLeaf98 r, Tape.mk' L (ListBlank.append [1, 0] (regsTape (regs ++ extra)))⟩ =
        some ⟨9, Tape.mk' L (ListBlank.append [0, 0]
          (regsTape (regs.set r.val (regs.getD r.val 0 - 1) ++ extra ++ [0])))⟩ := by
  have hr : r.val < regs.length := by omega
  have hget := List.getD_append regs extra 0 r.val hr
  simpa only [hget, List.set_append_left _ _ hr] using
    unary98_dec_pos r (regs ++ extra) (by simp only [List.length_append]; omega)
      (by simpa only [hget] using hpos) L

theorem unary98_dec_zero_five (r : Fin 5) (regs extra : List Nat) (hlen : regs.length = 5)
    (hz : regs.getD r.val 0 = 0) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, nSteps s
      ⟨decLeaf98 r, Tape.mk' L (ListBlank.append [1, 0] (regsTape (regs ++ extra)))⟩ =
        some ⟨63, Tape.mk' L (ListBlank.append [0, 0] (regsTape (regs ++ extra)))⟩ := by
  have hr : r.val < regs.length := by omega
  exact unary98_dec_zero r (regs ++ extra) (by simp only [List.length_append]; omega)
    (by simpa only [List.getD_append regs extra 0 r.val hr] using hz) L

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

/-- INC from a cleared caller suffix through its intrinsic guarded return. -/
theorem macro98_inc (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 walked.reverse).reverse).reverse = true) :
    ∃ pad' ≥ walked.length + fill, ∃ s ≥ 1, nSteps s
      ⟨incLeaf98 r, Tape.mk' (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0)
          (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rawRoot98 pad' (popBreakRev 0 walked.reverse).reverse
        (bank.set r.val (bank.getD r.val 0 + 1))) := by
  have hf := leaf98_fill r true fill (stackLeftOf true walked)
    (ListBlank.append [1, 0] (regsTape bank))
  obtain ⟨su, hsu, hu⟩ := unary98_inc r bank hr
    (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
  obtain ⟨pad', hp, sf, hsf, hret⟩ := fenceReturn98 0 walked fill hfill
    (by simp) hguard (bank.set r.val (bank.getD r.val 0 + 1))
  refine ⟨pad', hp, fill + su + sf, by omega, ?_⟩
  exact Return.nSteps_bind_eq (Return.nSteps_bind_eq hf hu) hret

theorem macro98_dec_pos (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (hpos : 0 < bank.getD r.val 0) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 walked.reverse).reverse).reverse = true) :
    ∃ pad' ≥ walked.length + fill, ∃ s ≥ 1, nSteps s
      ⟨decLeaf98 r, Tape.mk' (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0)
          (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rawRoot98 pad' (popBreakRev 0 walked.reverse).reverse
        (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])) := by
  have hf := leaf98_fill r false fill (stackLeftOf true walked)
    (ListBlank.append [1, 0] (regsTape bank))
  obtain ⟨su, hsu, hu⟩ := unary98_dec_pos r bank hr hpos
    (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
  obtain ⟨pad', hp, sf, hsf, hret⟩ := fenceReturn98 0 walked fill hfill
    (by simp) hguard (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])
  refine ⟨pad', hp, fill + su + sf, by omega, ?_⟩
  exact Return.nSteps_bind_eq (Return.nSteps_bind_eq hf hu) hret

theorem macro98_dec_zero (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length)
    (hz : bank.getD r.val 0 = 0) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill)
    (hk : 1 ≤ walked.count 0) (hguard : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 1 walked.reverse).reverse).reverse = true) :
    ∃ pad' ≥ walked.length + fill, ∃ s ≥ 1, nSteps s
      ⟨decLeaf98 r, Tape.mk' (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0)
          (ListBlank.append [1, 0] (regsTape bank)))⟩ =
      some (rawRoot98 pad' (popBreakRev 1 walked.reverse).reverse bank) := by
  have hf := leaf98_fill r false fill (stackLeftOf true walked)
    (ListBlank.append [1, 0] (regsTape bank))
  obtain ⟨su, hsu, hu⟩ := unary98_dec_zero r bank hr hz
    (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
  obtain ⟨pad', hp, sf, hsf, hret⟩ := fenceReturn98 1 walked fill hfill hk hguard bank
  refine ⟨pad', hp, fill + su + sf, by omega, ?_⟩
  exact Return.nSteps_bind_eq (Return.nSteps_bind_eq hf hu) hret

end ConjectureMachines.Riemann95Auxiliary.Physical
