/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ParserTape95
public import Cryptids.ReductionSupport.Riemann95.Padding95

@[expose] public section

namespace ConjectureMachines.Riemann95.Dispatch

open Turing ConjectureMachines

theorem nSteps_composition (m n : Nat) (c : ConjectureMachines.Cfg 95 2) :
    nSteps (m + n) c = (nSteps m c).bind (nSteps n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    simp [nSteps, Nat.succ_add, ih, Option.bind_assoc]

/-- From the complete root frame through native arithmetic and the guarded exact return. -/
theorem arithmetic_dispatch_exact (pad : Nat) (word walked : List (Fin 2)) (bank : List Nat)
    (r : Fin 5) (inc : Bool) (hfill : 3 ≤ pad - walked.length)
    (htape : word ++ List.replicate (pad - word.length) 0 =
      walked ++ List.replicate (pad - walked.length) 0)
    (hparse : CryptidsResearch.Recursive95Parser.walkInternal 15 walked =
      some (if inc then Physical.incLeaf r else Physical.decLeaf r))
    (hr : r.val < bank.length) (hk : inc = false → 1 ≤ walked.count 0)
    (hguard0 : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (Riemann120.Layer2.popBreakRev 0 walked.reverse).reverse).reverse = true)
    (hguard1 : inc = false → Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (Riemann120.Layer2.popBreakRev 1 walked.reverse).reverse).reverse = true) :
    let k : Fin 2 := if inc then 0 else if bank.getD r.val 0 = 0 then 1 else 0
    let bank' := if inc then bank.set r.val (bank.getD r.val 0 + 1)
      else if bank.getD r.val 0 = 0 then bank else bank.set r.val (bank.getD r.val 0 - 1) ++ [0]
    ∃ s ≥ 1, nSteps s (Physical.rootCfg pad word bank) =
      some (Physical.rootCfg (Physical.exactPad k walked (pad - walked.length))
        (Riemann120.Layer2.popBreakRev k.val walked.reverse).reverse bank') := by
  have hp := CryptidsResearch.Recursive95Parser.walkInternal_nSteps walked 15
    (if inc then Physical.incLeaf r else Physical.decLeaf r)
    (Riemann120.rootLeftOf true)
    (Turing.ListBlank.append (List.replicate (pad - walked.length) 0)
      (Turing.ListBlank.append [1, 0] (Semantics.Riemann.Layer1.regsTape bank))) hparse
  have hroot : Physical.rootCfg pad word bank =
      ⟨15, Turing.Tape.mk' (Riemann120.rootLeftOf true)
        (Turing.ListBlank.append walked
          (Turing.ListBlank.append (List.replicate (pad - walked.length) 0)
            (Turing.ListBlank.append [1, 0] (Semantics.Riemann.Layer1.regsTape bank))))⟩ := by
    unfold Physical.rootCfg
    rw [htape]
    unfold Semantics.Riemann.Layer1.regsTape
    rw [show (default : Turing.ListBlank (Fin 2)) = Turing.ListBlank.mk [] from rfl]
    simp only [Turing.ListBlank.append_mk, List.append_nil, List.append_assoc]
    rfl
  rw [← hroot] at hp
  have hstack : Turing.ListBlank.append walked.reverse (Riemann120.rootLeftOf true) =
      Riemann120.stackLeftOf true walked := by
    rfl
  rw [hstack] at hp
  cases inc with
  | true =>
    obtain ⟨s, hs, hm⟩ := Physical.macro_inc_exact r bank hr walked
      (pad - walked.length) hfill hguard0
    refine ⟨walked.length + s, by omega, ?_⟩
    rw [nSteps_composition, hp]
    simpa only [Option.bind_some, ↓reduceIte, Fin.val_zero] using hm
  | false =>
    by_cases hz : bank.getD r.val 0 = 0
    · obtain ⟨s, hs, hm⟩ := Physical.macro_dec_zero_exact r bank hr hz walked
        (pad - walked.length) hfill (hk rfl) (hguard1 rfl)
      refine ⟨walked.length + s, by omega, ?_⟩
      rw [nSteps_composition, hp]
      simpa only [Option.bind_some, hz, Bool.false_eq_true, ↓reduceIte, Fin.val_one] using hm
    · obtain ⟨s, hs, hm⟩ := Physical.macro_dec_pos_exact r bank hr
        (by omega) walked (pad - walked.length) hfill hguard0
      refine ⟨walked.length + s, by omega, ?_⟩
      rw [nSteps_composition, hp]
      simpa only [Option.bind_some, hz, Bool.false_eq_true, ↓reduceIte, Fin.val_zero] using hm

end ConjectureMachines.Riemann95.Dispatch
