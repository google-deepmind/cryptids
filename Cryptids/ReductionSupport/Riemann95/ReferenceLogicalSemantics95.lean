/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ReferenceLogical95

@[expose] public section

namespace ConjectureMachines.Riemann95.ReferenceLogical

open Turing StateTransition ConjectureMachines.Riemann120
open ConjectureMachines.Riemann120.Layer2

attribute [local irreducible] rows row word oldWord rowInstr role decoded instruction

def incReg (r : Nat) (regs : List Nat) : List Nat :=
  regs.set r (regs.getD r 0 + 1)

def applyInstr (i : RhInstr) (regs : List Nat) : Option RhRegCfg :=
  match i with
  | .halt => none
  | .jump target => some ⟨target,regs⟩
  | .inc r target => some ⟨target,incReg r regs⟩
  | .decnz r positive zero =>
    if regs.getD r 0 == 0 then some ⟨zero,regs⟩
    else some ⟨positive,regs.set r (regs.getD r 0 - 1)⟩

theorem step_effect (c : RhRegCfg) :
    step c = applyInstr (instruction c.stack) c.regs := by
  unfold step
  cases instruction c.stack <;> rfl

theorem step_on_word (s : Fin 121) (regs : List Nat) :
    step ⟨word s,regs⟩ = applyInstr (decoded s) regs := by
  calc
    _ = applyInstr (instruction (word s)) regs := step_effect _
    _ = applyInstr (decoded s) regs := congrArg (fun i => applyInstr i regs) (instruction_word s)

theorem old_step (w : Word) (i : RhInstr) (regs : List Nat)
    (h : evalStackOf true w = i) :
    rhRegStepOf true ⟨w,regs⟩ = applyInstr i regs := by
  simp only [rhRegStepOf, h]
  rfl

def RegRel (s : Fin 121) (fresh old : List Nat) : Prop :=
  match role s with
  | .secondSwap r => ∃ base : List Nat,
      base.length = 5 ∧ fresh = incReg r base ∧ old = incReg 4 base
  | _ => fresh.length = 5 ∧ old = fresh

theorem regRel_ordinary (s : Fin 121) (ho : ordinary s)
    (fresh old : List Nat) (hlen : fresh.length = 5) (heq : old = fresh) :
    RegRel s fresh old := by
  unfold RegRel
  cases h : role s with
  | secondSwap r => simp only [ordinary, h] at ho
  | plain => exact ⟨hlen,heq⟩
  | firstSwap r => exact ⟨hlen,heq⟩
  | halfDec => exact ⟨hlen,heq⟩

theorem inc_length (r : Nat) (regs : List Nat) :
    (incReg r regs).length = regs.length := by simp [incReg]

theorem inc_commute (r : Nat) (regs : List Nat) (hlen : regs.length = 5)
    (hr : r = 2 ∨ r = 3) :
    incReg r (incReg 4 regs) = incReg 4 (incReg r regs) := by
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, rest⟩⟩⟩⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at hlen
  all_goals try omega
  have he : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst rest
  rcases hr with rfl | rfl <;> rfl

end ConjectureMachines.Riemann95.ReferenceLogical
