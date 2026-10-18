/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ArithmeticDispatch95
public import Cryptids.ReductionSupport.Riemann95.NativeGuard95

@[expose] public section

namespace ConjectureMachines.Riemann95.Dispatch

open Turing ConjectureMachines
open Riemann120.Layer2

/-- Every typed native arithmetic call executes on the complete 95-state tape frame. -/
theorem root_native (c : Schema.ControlWord) (r : Fin 5) (inc : Bool)
    (he : Control.effect c = if inc then .inc r else .decnz r)
    (pad : Nat) (bank : List Nat) (hr : r.val < bank.length)
    (hfill : 3 ≤ pad - (Control.walked c).length) :
    let walked := Control.walked c
    let k : Fin 2 := if inc then 0 else if bank.getD r.val 0 = 0 then 1 else 0
    let bank' := if inc then bank.set r.val (bank.getD r.val 0 + 1)
      else if bank.getD r.val 0 = 0 then bank else bank.set r.val (bank.getD r.val 0 - 1) ++ [0]
    ∃ s ≥ 1, nSteps s (Physical.rootCfg pad (Schema.word c) bank) =
      some (Physical.rootCfg (Physical.exactPad k walked (pad - walked.length))
        (popBreakRev k.val walked.reverse).reverse bank') := by
  have hterminal : terminal c = if inc then Physical.incLeaf r else Physical.decLeaf r := by
    have ht := nativeCorrect_all c
    cases inc <;> simpa only [nativeCorrect, he, Bool.false_eq_true, ↓reduceIte] using ht
  have hparse := actual_parse c
  rw [hterminal] at hparse
  have hext : Control.walked c = Schema.word c ++
      List.replicate ((Control.walked c).length - (Schema.word c).length) 0 := by
    have hp := arithmeticPrefix_all c
    cases inc <;> simpa only [arithmeticPrefix, he, Bool.false_eq_true, ↓reduceIte] using hp
  have hlen : (Schema.word c).length ≤ (Control.walked c).length := by
    rw [hext]
    simp
  have htape : Schema.word c ++ List.replicate (pad - (Schema.word c).length) 0 =
      Control.walked c ++ List.replicate (pad - (Control.walked c).length) 0 := by
    calc
      _ = Schema.word c ++ List.replicate
          (((Control.walked c).length - (Schema.word c).length) +
            (pad - (Control.walked c).length)) 0 := by
        have hz : pad - (Schema.word c).length =
            ((Control.walked c).length - (Schema.word c).length) +
              (pad - (Control.walked c).length) := by omega
        rw [hz]
      _ = _ := by rw [List.replicate_add, ← List.append_assoc, ← hext]
  have hg0 : Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 (Control.walked c).reverse).reverse).reverse = true := by
    cases inc with
    | false => exact (dec_return_guards c r he).1
    | true => exact inc_return_guard c r he
  have hk : inc = false → 1 ≤ (Control.walked c).count 0 := by
    intro hi
    subst inc
    exact dec_walk_count c r he
  have hg1 : inc = false → Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 1 (Control.walked c).reverse).reverse).reverse = true := by
    intro hi
    subst inc
    exact (dec_return_guards c r he).2
  exact arithmetic_dispatch_exact pad (Schema.word c) (Control.walked c) bank r inc
    hfill htape hparse hr hk hg0 hg1

end ConjectureMachines.Riemann95.Dispatch
