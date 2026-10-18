/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Parser95

@[expose] public section

namespace CryptidsResearch.Recursive95Parser

open Turing ConjectureMachines
open ConjectureMachines.Riemann95

/-- A successful read-preserving parser walk is its exact physical tape traversal. -/
theorem walkInternal_nSteps (bits : List (Fin 2)) (q q' : Fin 95)
    (L R : ListBlank (Fin 2)) (hwalk : walkInternal q bits = some q') :
    nSteps bits.length ⟨q, Tape.mk' L (ListBlank.append bits R)⟩ =
      some ⟨q', Tape.mk' (ListBlank.append bits.reverse L) R⟩ := by
  induction bits generalizing q q' L with
  | nil =>
    simp only [walkInternal, Option.some.injEq] at hwalk
    subst q'
    rfl
  | cons bit bits ih =>
    rw [walkInternal] at hwalk
    cases ht : machine.transition q bit with
    | none => simp only [ht] at hwalk; cases hwalk
    | some triple =>
      rcases triple with ⟨w, direction, next⟩
      cases direction with
      | left => simp only [ht] at hwalk; cases hwalk
      | right =>
        by_cases hw : w = bit
        · subst w
          simp only [ht, ite_true] at hwalk
          have hstep : step machine
              ⟨q, Tape.mk' L (ListBlank.cons bit (ListBlank.append bits R))⟩ =
              some ⟨next, Tape.mk' (ListBlank.cons bit L) (ListBlank.append bits R)⟩ := by
            simp [step, ht, Tape.mk', Tape.write, Tape.move]
          rw [List.length_cons, nSteps, ListBlank.append, hstep, Option.bind_some]
          simpa only [List.reverse_cons, ListBlank.append_assoc, ListBlank.append] using
            ih next q' (ListBlank.cons bit L) hwalk
        · simp only [ht, hw, ite_false] at hwalk; cases hwalk

/-- The unbounded recursive prefix executes before every arbitrary parser suffix. -/
theorem callerPrefix_nSteps (d : Nat) (L R : ListBlank (Fin 2)) :
    nSteps (6 + 5 * d)
      ⟨15, Tape.mk' L (ListBlank.append (prefixBits ++ repetitions d) R)⟩ =
      some ⟨46, Tape.mk' (ListBlank.append (prefixBits ++ repetitions d).reverse L) R⟩ := by
  have hparse : walkInternal 15 (prefixBits ++ repetitions d) = some 46 := by
    simpa only [List.append_nil, walkInternal] using prefix_parse d []
  have h := walkInternal_nSteps (prefixBits ++ repetitions d) 15 46 L R hparse
  simpa only [List.length_append, prefixBits, List.length_cons, List.length_nil,
    repetitions_length] using h

end CryptidsResearch.Recursive95Parser
