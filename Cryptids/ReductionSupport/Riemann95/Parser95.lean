/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition
public import Cryptids.ReductionSupport.Riemann95.ControllerSchema95

/-! # Decoder and tape correctness -/

@[expose] public section

/-! ## Recursive decoder -/

section

/-! Actual recursive95 decoder prefix. This proves arbitrary repetition and
arbitrary suffix behavior of the read-preserving rightward parser, not the
whole machine or caller-language closure. -/
namespace CryptidsResearch.Recursive95Parser

open Turing

def walkInternal (q : Fin 95) : List (Fin 2) → Option (Fin 95)
  | [] => some q
  | b :: bs =>
    match ConjectureMachines.Riemann95.machine.transition q b with
    | some (w, .right, next) =>
      if w = b then walkInternal next bs else none
    | _ => none

theorem walkInternal_append (q : Fin 95) (a b : List (Fin 2)) :
    walkInternal q (a ++ b) = (walkInternal q a).bind (fun r => walkInternal r b) := by
  induction a generalizing q with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, walkInternal]
    cases ht : ConjectureMachines.Riemann95.machine.transition q x with
    | none => rfl
    | some triple =>
      rcases triple with ⟨w, dir, next⟩
      cases dir with
      | left => rfl
      | right =>
        by_cases h : w = x
        · simp only [h, ite_true, ih]
        · simp only [h, ite_false, Option.bind_none]

def prefixBits : List (Fin 2) := [1,1,1,1,1,0]
def block : List (Fin 2) := [1,1,1,1,0]

def repetitions : Nat → List (Fin 2)
  | 0 => []
  | n + 1 => block ++ repetitions n

theorem actual_prefix : walkInternal 15 prefixBits = some 46 := by rfl
theorem actual_cycle : walkInternal 46 block = some 46 := by rfl

theorem repetitions_parse (n : Nat) (tail : List (Fin 2)) :
    walkInternal 46 (repetitions n ++ tail) = walkInternal 46 tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repetitions, List.append_assoc, walkInternal_append,
      actual_cycle, Option.bind_some, ih]

theorem prefix_parse (n : Nat) (tail : List (Fin 2)) :
    walkInternal 15 (prefixBits ++ repetitions n ++ tail) = walkInternal 46 tail := by
  rw [List.append_assoc, walkInternal_append, actual_prefix,
    Option.bind_some, repetitions_parse]

theorem repetitions_length (n : Nat) : (repetitions n).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [repetitions, List.length_append, block, List.length_cons,
      List.length_nil, ih]
    omega

theorem prefix_length (n : Nat) (tail : List (Fin 2)) :
    (prefixBits ++ repetitions n ++ tail).length = 6 + 5 * n + tail.length := by
  simp only [List.length_append, prefixBits, List.length_cons,
    List.length_nil, repetitions_length]


end CryptidsResearch.Recursive95Parser

end

/-! ## Tape interpretation -/

section

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

end

/-! ## Decoder correctness -/

section

namespace CryptidsResearch.Recursive95Parser

open Turing ConjectureMachines
open ConjectureMachines.Riemann95

theorem repetitions_snoc (d : Nat) : repetitions (d + 1) = repetitions d ++ block := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change block ++ repetitions (d + 1) = (block ++ repetitions d) ++ block
    rw [ih, List.append_assoc]

theorem callerPrefix_eq (d : Nat) : Schema.callerPrefix d = prefixBits ++ repetitions d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Schema.callerPrefix, ih, repetitions_snoc, ← List.append_assoc]
    rfl

def localTerminal (s : Fin 22) : Fin 95 :=
  (walkInternal 46 (Schema.localWalkSuffix s)).getD 0

def outsideTerminal (s : Fin 97) : Fin 95 :=
  (walkInternal 15 (Schema.outsideWalk s)).getD 0

theorem localTerminal_walk : ∀ s : Fin 22,
    walkInternal 46 (Schema.localWalkSuffix s) = some (localTerminal s) := by
  decide +kernel

theorem outsideTerminal_walk : ∀ s : Fin 97,
    walkInternal 15 (Schema.outsideWalk s) = some (outsideTerminal s) := by
  decide +kernel

/-- Every local suffix follows the exact physical decoder at every recursion depth. -/
theorem localWalk_parse (d : Nat) (s : Fin 22) :
    walkInternal 15 (Schema.localWalk d s) = some (localTerminal s) := by
  rw [Schema.localWalk, callerPrefix_eq, prefix_parse]
  exact localTerminal_walk s

/-- Entry inspects the mandatory zero after the regular prefix and reaches native DECj. -/
theorem entryWalk_parse (d : Nat) :
    walkInternal 15 (Schema.callerPrefix d ++ [0]) = some 58 := by
  rw [callerPrefix_eq, prefix_parse]
  rfl

theorem localWalk_nSteps (d : Nat) (s : Fin 22) (L R : ListBlank (Fin 2)) :
    nSteps (Schema.localWalk d s).length
      ⟨15, Tape.mk' L (ListBlank.append (Schema.localWalk d s) R)⟩ =
      some ⟨localTerminal s,
        Tape.mk' (ListBlank.append (Schema.localWalk d s).reverse L) R⟩ :=
  walkInternal_nSteps _ _ _ _ _ (localWalk_parse d s)

theorem outsideWalk_nSteps (s : Fin 97) (L R : ListBlank (Fin 2)) :
    nSteps (Schema.outsideWalk s).length
      ⟨15, Tape.mk' L (ListBlank.append (Schema.outsideWalk s) R)⟩ =
      some ⟨outsideTerminal s,
        Tape.mk' (ListBlank.append (Schema.outsideWalk s).reverse L) R⟩ :=
  walkInternal_nSteps _ _ _ _ _ (outsideTerminal_walk s)

theorem entryWalk_nSteps (d : Nat) (L R : ListBlank (Fin 2)) :
    nSteps (Schema.callerPrefix d ++ [0]).length
      ⟨15, Tape.mk' L (ListBlank.append (Schema.callerPrefix d ++ [0]) R)⟩ =
      some ⟨58, Tape.mk' (ListBlank.append (Schema.callerPrefix d ++ [0]).reverse L) R⟩ :=
  walkInternal_nSteps _ _ _ _ _ (entryWalk_parse d)

end CryptidsResearch.Recursive95Parser

end
