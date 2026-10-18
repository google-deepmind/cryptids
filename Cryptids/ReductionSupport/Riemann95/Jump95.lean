/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Return95
public import Cryptids.ReductionSupport.Riemann95.FinitePrefix95

/-! Universal local jump rewrites on the actual95 table. All right tails and
caller prefixes are arbitrary; only the resulting caller's NoThree guard is
required by the existing intrinsic return scanner. -/

@[expose] public section

namespace ConjectureMachines.Riemann95.Jump

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 (rootLeftOf stackLeftOf)
open ConjectureMachines.Semantics.Riemann.Layer1 (Tape.mkL)
open ConjectureMachines.Riemann104.OnePassGuard (NoThreeZeros)
open FinitePrefix

theorem nSteps_add (m n : Nat) (c : Cfg 95 2) :
    nSteps (m + n) c = (nSteps m c).bind (nSteps n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    simp only [Nat.succ_add, nSteps]
    cases step machine c <;> simp [ih]

theorem nSteps_bind {m n : Nat} {c c' c'' : Cfg 95 2}
    (h : nSteps m c = some c') (h' : nSteps n c' = some c'') :
    nSteps (m + n) c = some c'' := by
  rw [nSteps_add, h, Option.bind_some, h']

theorem prefix43 :
    prefixRun95 5 43 [1, 1, 0, 0, 1] [1] =
      some (10, [], [1, 0, 0, 0, 0, 0]) := by decide +kernel

theorem prefix59 :
    prefixRun95 4 59 [1, 1] [1] = some (14, [], [0, 0, 0]) := by decide +kernel

theorem prefix19 :
    prefixRun95 2 19 [1, 1] [1] = some (5, [], [1, 0, 0]) := by decide +kernel

theorem step_header_left {q q' : Fin 95} {a b : Fin 2}
    (h : machine.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step machine ⟨q, Tape.mk' L (R.cons a)⟩ =
      some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mk', Tape.mkL, Tape.write, Tape.move]

theorem last_one_head (P : List (Fin 2)) :
    (stackLeftOf true (P ++ [1])).head = 1 := by
  simp [stackLeftOf, List.reverse_append, ListBlank.append]

theorem last_one_tail (P : List (Fin 2)) :
    (stackLeftOf true (P ++ [1])).tail = stackLeftOf true P := by
  simp [stackLeftOf, List.reverse_append, ListBlank.append]

/-- CONT2 on the full input word P100111: all five erased cells are retained
as zero padding to the right of the new caller P1. -/
theorem jump43 (P : List (Fin 2)) (R : ListBlank (Fin 2))
    (hok : NoThreeZeros (1 :: (P ++ [1])).reverse = true) :
    ∃ s ≥ 1, nSteps s
      ⟨43, Tape.mk' (stackLeftOf true (P ++ [1, 0, 0, 1, 1])) (R.cons 1)⟩ =
      some ⟨15, Tape.mk' (rootLeftOf true)
        (ListBlank.append (P ++ [1]) (ListBlank.append [0, 0, 0, 0, 0] R))⟩ := by
  have hp := prefixRun96_sound prefix43 (stackLeftOf true P) R
  have hp' : nSteps 5
      ⟨43, Tape.mk' (stackLeftOf true (P ++ [1, 0, 0, 1, 1])) (R.cons 1)⟩ =
      some ⟨10, Tape.mk' (stackLeftOf true P)
        ((ListBlank.append [0, 0, 0, 0, 0] R).cons 1)⟩ := by
    simpa [stackLeftOf, List.reverse_append, ListBlank.append_assoc,
      ListBlank.append] using hp
  have ht : machine.transition 10 1 = some (1, .left, 5) := by decide +kernel
  have hstep := step_header_left ht (stackLeftOf true P)
    (ListBlank.append [0, 0, 0, 0, 0] R)
  have hstep' : nSteps 1
      ⟨10, Tape.mk' (stackLeftOf true P)
        ((ListBlank.append [0, 0, 0, 0, 0] R).cons 1)⟩ =
      some ⟨5, Tape.mkL (stackLeftOf true P)
        ((ListBlank.append [0, 0, 0, 0, 0] R).cons 1)⟩ := by
    simpa [nSteps] using hstep
  obtain ⟨s, hs, hr⟩ := Return.run_return_after_one (P ++ [1]) hok
    (last_one_head P) (ListBlank.append [0, 0, 0, 0, 0] R)
  rw [last_one_tail] at hr
  exact ⟨5 + 1 + s, by omega, nSteps_bind (nSteps_bind hp' hstep') hr⟩

/-- CONT1 on the full input word P111, using the q59 bounce which restores
the retained adjacent ONE before entering the peeled scanner. -/
theorem jump59 (P : List (Fin 2)) (R : ListBlank (Fin 2))
    (hok : NoThreeZeros (1 :: (P ++ [1])).reverse = true) :
    ∃ s ≥ 1, nSteps s
      ⟨59, Tape.mk' (stackLeftOf true (P ++ [1, 1])) (R.cons 1)⟩ =
      some ⟨15, Tape.mk' (rootLeftOf true)
        (ListBlank.append (P ++ [1]) (ListBlank.append [0, 0] R))⟩ := by
  have hp := prefixRun96_sound prefix59 (stackLeftOf true P) R
  have hp' : nSteps 4
      ⟨59, Tape.mk' (stackLeftOf true (P ++ [1, 1])) (R.cons 1)⟩ =
      some ⟨14, Tape.mk' (stackLeftOf true P)
        ((ListBlank.append [0, 0] R).cons 0)⟩ := by
    simpa [stackLeftOf, List.reverse_append, ListBlank.append_assoc,
      ListBlank.append] using hp
  have ht : machine.transition 14 0 = some (1, .left, 5) := by decide +kernel
  have hstep := step_header_left ht (stackLeftOf true P) (ListBlank.append [0, 0] R)
  have hstep' : nSteps 1
      ⟨14, Tape.mk' (stackLeftOf true P) ((ListBlank.append [0, 0] R).cons 0)⟩ =
      some ⟨5, Tape.mkL (stackLeftOf true P) ((ListBlank.append [0, 0] R).cons 1)⟩ := by
    simpa [nSteps] using hstep
  obtain ⟨s, hs, hr⟩ := Return.run_return_after_one (P ++ [1]) hok
    (last_one_head P) (ListBlank.append [0, 0] R)
  rw [last_one_tail] at hr
  exact ⟨4 + 1 + s, by omega, nSteps_bind (nSteps_bind hp' hstep') hr⟩

/-- CONT1 on the full input word P111, entering the scanner on its retained
ONE directly rather than taking the q59 bounce. -/
theorem jump19 (P : List (Fin 2)) (R : ListBlank (Fin 2))
    (hok : NoThreeZeros (1 :: (P ++ [1])).reverse = true) :
    ∃ s ≥ 1, nSteps s
      ⟨19, Tape.mk' (stackLeftOf true (P ++ [1, 1])) (R.cons 1)⟩ =
      some ⟨15, Tape.mk' (rootLeftOf true)
        (ListBlank.append (P ++ [1]) (ListBlank.append [0, 0] R))⟩ := by
  have hp := prefixRun96_sound prefix19 (stackLeftOf true P) R
  have hp' : nSteps 2
      ⟨19, Tape.mk' (stackLeftOf true (P ++ [1, 1])) (R.cons 1)⟩ =
      some ⟨5, Tape.mkL (stackLeftOf true (P ++ [1]))
        (ListBlank.append [0, 0] R)⟩ := by
    simpa [stackLeftOf, List.reverse_append, ListBlank.append_assoc,
      ListBlank.append, Tape.mkL, Tape.mk'] using hp
  obtain ⟨s, hs, hr⟩ := Return.run_return (P ++ [1]) hok (ListBlank.append [0, 0] R)
  exact ⟨2 + s, by omega, nSteps_bind hp' hr⟩

end ConjectureMachines.Riemann95.Jump
