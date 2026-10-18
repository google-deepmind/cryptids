/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95RawReturn
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Swap

/-! The return scanner is proved once for the raw labels, then transported by renaming. -/

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary.Return

open Turing ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1 (append_replicate_cons Tape.mkL)
open ConjectureMachines.Riemann120 (rootLeftOf stackLeftOf)
open ConjectureMachines.Riemann104.OnePassGuard (NoThreeZeros)

theorem nSteps_bind_eq {m n : Nat} {c c' c'' : Cfg 98 2}
    (h : nSteps m c = some c') (h' : nSteps n c' = some c'') :
    nSteps (m + n) c = some c'' := by
  have hadd (m n : Nat) (c : Cfg 98 2) :
      nSteps (m + n) c = (nSteps m c).bind (nSteps n) := by
    induction m generalizing c with
    | zero => simp only [Nat.zero_add, nSteps, Option.bind_some]
    | succ m ih => simp only [Nat.succ_add, nSteps, ih, Option.bind_assoc]
  rw [hadd, h]
  exact h'

theorem right_scan {q : Fin 98} {a b : Fin 2}
    (h : machine.transition q a = some (b, .right, q)) (k : Nat)
    (L R : ListBlank (Fin 2)) :
    nSteps k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  have hs (L R : ListBlank (Fin 2)) :
      step machine ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q, Tape.mk' (L.cons b) R⟩ := by
    simp [step, h, Tape.mk', Tape.write, Tape.move]
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps, hs]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-- The relabelled table has the same complete NoThree return scanner. -/
theorem run_return98 (word : List (Fin 2))
    (hok : NoThreeZeros (1 :: word).reverse = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps s
      ⟨5, Tape.mkL (stackLeftOf true word) R⟩ =
        some ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append word R)⟩ := by
  obtain ⟨s, hs, h⟩ := ReturnRaw.run_return98 word hok R
  exact ⟨s, hs, Renaming.of_raw h⟩

/-- Renaming also preserves the positive run after its first ONE step. -/
theorem run_return98_after_one (word : List (Fin 2))
    (hok : NoThreeZeros (1 :: word).reverse = true)
    (hhead : (stackLeftOf true word).head = 1) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps s
      ⟨5, Tape.mkL (stackLeftOf true word).tail (R.cons 1)⟩ =
        some ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append word R)⟩ := by
  obtain ⟨s, hs, h⟩ := ReturnRaw.run_return98_after_one word hok hhead R
  exact ⟨s, hs, Renaming.of_raw h⟩

end ConjectureMachines.Riemann95Auxiliary.Return
