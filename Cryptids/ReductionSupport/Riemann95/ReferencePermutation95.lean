/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ReferenceProgram95
public import Cryptids.ReductionSupport.Riemann95.ReferenceLogicalSemantics95

@[expose] public section

namespace ConjectureMachines.Riemann95.ReferenceProgram

open Turing StateTransition ConjectureMachines.Riemann120
open ConjectureMachines.Riemann120.Layer2

attribute [local irreducible] rows row word oldWord rowInstr role decoded instruction
attribute [local irreducible] ReferenceLogical.rows ReferenceLogical.row ReferenceLogical.word
  ReferenceLogical.oldWord ReferenceLogical.rowInstr ReferenceLogical.role
  ReferenceLogical.decoded ReferenceLogical.instruction

def encodeBank (regs : List Nat) : List Nat :=
  [regs.getD 2 0,regs.getD 4 0,regs.getD 3 0,regs.getD 0 0,regs.getD 1 0]

def decodeBank (regs : List Nat) : List Nat :=
  [regs.getD 3 0,regs.getD 4 0,regs.getD 0 0,regs.getD 2 0,regs.getD 1 0]

theorem bank_five (regs : List Nat) (hlen : regs.length = 5) :
    ∃ a b c d e, regs = [a,b,c,d,e] := by
  rcases regs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at hlen
  all_goals try omega
  have he : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst rest
  exact ⟨a,b,c,d,e,rfl⟩

theorem encodeBank_length (regs : List Nat) : (encodeBank regs).length = 5 := rfl
theorem decodeBank_length (regs : List Nat) : (decodeBank regs).length = 5 := rfl

theorem decode_encode (regs : List Nat) (hlen : regs.length = 5) :
    decodeBank (encodeBank regs) = regs := by
  obtain ⟨a,b,c,d,e,rfl⟩ := bank_five regs hlen
  rfl

theorem encode_decode (regs : List Nat) (hlen : regs.length = 5) :
    encodeBank (decodeBank regs) = regs := by
  obtain ⟨a,b,c,d,e,rfl⟩ := bank_five regs hlen
  rfl

theorem encodeBank_getD (regs : List Nat) (hlen : regs.length = 5) (r : Nat) :
    (encodeBank regs).getD (perm r) 0 = regs.getD r 0 := by
  obtain ⟨a,b,c,d,e,rfl⟩ := bank_five regs hlen
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> rfl

theorem encodeBank_set (regs : List Nat) (hlen : regs.length = 5) (r value : Nat) :
    encodeBank (regs.set r value) = (encodeBank regs).set (perm r) value := by
  obtain ⟨a,b,c,d,e,rfl⟩ := bank_five regs hlen
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> rfl

def encodeCfg (c : RhRegCfg) : RhRegCfg := ⟨c.stack,encodeBank c.regs⟩

theorem step_encode (c : RhRegCfg) (hlen : c.regs.length = 5) :
    step (encodeCfg c) = (ReferenceLogical.step c).map encodeCfg := by
  unfold step instruction ReferenceLogical.step
  dsimp only [encodeCfg]
  cases h : ReferenceLogical.instruction c.stack with
  | halt => rfl
  | jump target => rfl
  | inc r target =>
    simp only [encodeCfg,mapInstr,encodeBank_getD _ hlen,Option.map_some]
    rw [encodeBank_set _ hlen]
  | decnz r positive zero =>
    simp only [mapInstr,encodeBank_getD _ hlen]
    split <;> simp only [Option.map_some,encodeCfg]
    rw [encodeBank_set _ hlen]

theorem logical_step_length (c next : RhRegCfg) (hs : ReferenceLogical.step c = some next) :
    next.regs.length = c.regs.length := by
  unfold ReferenceLogical.step at hs
  cases h : ReferenceLogical.instruction c.stack with
  | halt => simp only [h] at hs; contradiction
  | jump target => simp only [h,Option.some.injEq] at hs; subst next; rfl
  | inc r target =>
    simp only [h,Option.some.injEq] at hs
    subst next
    simp
  | decnz r positive zero =>
    simp only [h] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst next <;> simp

def BankRel (physical logical : RhRegCfg) : Prop :=
  physical = encodeCfg logical ∧ logical.regs.length = 5

theorem physProgramRespectsLogical :
    StateTransition.Respects step ReferenceLogical.step BankRel := by
  intro physical logical hrel
  obtain ⟨rfl,hlen⟩ := hrel
  rw [step_encode logical hlen]
  cases hs : ReferenceLogical.step logical with
  | none => rfl
  | some next =>
    refine ⟨next,⟨rfl,?_⟩,Relation.TransGen.single hs⟩
    exact (logical_step_length logical next hs).trans hlen

theorem stage_bank_related (M : Nat) : BankRel (stageCfg M) (ReferenceLogical.stageCfg M) :=
  ⟨rfl,rfl⟩

theorem stage_halts_iff_edited (M : Nat) :
    (StateTransition.eval step (stageCfg M)).Dom ↔
      (StateTransition.eval (rhRegStepOf true) (ReferenceLogical.stageCfg M)).Dom := by
  exact (StateTransition.tr_eval_dom physProgramRespectsLogical
    (stage_bank_related M)).symm.trans (ReferenceLogical.stage_halts_iff_edited M)

end ConjectureMachines.Riemann95.ReferenceProgram
