/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ParserTape95
public import Cryptids.ReductionSupport.Riemann95.ControllerSchema95

@[expose] public section

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
