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

def R (fresh old : RhRegCfg) : Prop :=
  ∃ s : Fin 121, fresh.stack = word s ∧ old.stack = oldWord s ∧
    RegRel s fresh.regs old.regs

theorem regRel_ordinary (s : Fin 121) (ho : ordinary s)
    (fresh old : List Nat) (hlen : fresh.length = 5) (heq : old = fresh) :
    RegRel s fresh old := by
  unfold RegRel
  cases h : role s with
  | secondSwap r => simp only [ordinary, h] at ho
  | plain => exact ⟨hlen,heq⟩
  | firstSwap r => exact ⟨hlen,heq⟩
  | halfDec => exact ⟨hlen,heq⟩

theorem relates_ordinary (s : Fin 121) (ho : ordinary s)
    (regs : List Nat) (hlen : regs.length = 5) :
    R ⟨word s,regs⟩ ⟨oldWord s,regs⟩ :=
  ⟨s,rfl,rfl,regRel_ordinary s ho regs regs hlen rfl⟩

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

def Matched (fresh old : RhRegCfg) : Prop :=
  match step fresh with
  | none => rhRegStepOf true old = none
  | some next => ∃ nextOld, R next nextOld ∧ Reaches₁ (rhRegStepOf true) old nextOld

theorem plain_match (s : Fin 121) (regs : List Nat) (hlen : regs.length = 5)
    (hOld : evalStackOf true (oldWord s) = toInstr oldWord (rowInstr s))
    (hTargets : ordinaryTargets (rowInstr s)) :
    Matched ⟨word s,regs⟩ ⟨oldWord s,regs⟩ := by
  unfold Matched
  rw [step_on_word]
  unfold decoded
  cases hi : rowInstr s with
  | halt =>
    simp only [toInstr, applyInstr]
    exact old_step (oldWord s) .halt regs (by simpa only [hi,toInstr] using hOld)
  | jump n =>
    simp only [toInstr, applyInstr]
    have ho : ordinary n := by simpa only [hi,ordinaryTargets] using hTargets
    have hs := old_step (oldWord s) (.jump (oldWord n)) regs
      (by simpa only [hi,toInstr] using hOld)
    exact ⟨⟨oldWord n,regs⟩,relates_ordinary n ho regs hlen,Relation.TransGen.single hs⟩
  | inc r n =>
    simp only [toInstr, applyInstr]
    have ho : ordinary n := by simpa only [hi,ordinaryTargets] using hTargets
    have hs := old_step (oldWord s) (.inc r (oldWord n)) regs
      (by simpa only [hi,toInstr] using hOld)
    exact ⟨⟨oldWord n,incReg r regs⟩,
      relates_ordinary n ho _ (by rw [inc_length];exact hlen),Relation.TransGen.single hs⟩
  | decnz r p z =>
    simp only [toInstr, applyInstr]
    have ho : ordinary p ∧ ordinary z := by simpa only [hi,ordinaryTargets] using hTargets
    have hs := old_step (oldWord s) (.decnz r (oldWord p) (oldWord z)) regs
      (by simpa only [hi,toInstr] using hOld)
    by_cases hz : (regs.getD r 0 == 0) = true
    · simp only [hz, ↓reduceIte]
      simp only [applyInstr,hz, ↓reduceIte] at hs
      exact ⟨⟨oldWord z,regs⟩,relates_ordinary z ho.2 regs hlen,Relation.TransGen.single hs⟩
    · have hf : (regs.getD r 0 == 0) = false := Bool.eq_false_iff.mpr hz
      simp only [hf]
      simp only [applyInstr,hf] at hs
      exact ⟨⟨oldWord p,regs.set r (regs.getD r 0 - 1)⟩,
        relates_ordinary p ho.1 _ (by simpa using hlen),Relation.TransGen.single hs⟩

theorem first_match (s : Fin 121) (r : Nat) (hrole : role s = .firstSwap r)
    (regs : List Nat) (hlen : regs.length = 5) :
    Matched ⟨word s,regs⟩ ⟨oldWord s,regs⟩ := by
  have hc := specs s
  simp only [Spec,hrole] at hc
  cases hi : rowInstr s <;> simp only [hi] at hc
  case inc r' n =>
    obtain ⟨hr,hn,hOld,_⟩ := hc
    subst r'
    unfold Matched
    rw [step_on_word]
    simp only [decoded,hi,toInstr,applyInstr]
    have hs := old_step (oldWord s) (.inc 4 (oldWord n)) regs hOld
    refine ⟨⟨oldWord n,incReg 4 regs⟩,⟨n,rfl,rfl,?_⟩,Relation.TransGen.single hs⟩
    simp only [RegRel,hn]
    exact ⟨regs,hlen,rfl,rfl⟩

theorem second_match (s : Fin 121) (r : Nat) (hrole : role s = .secondSwap r)
    (fresh old : List Nat) (hreg : RegRel s fresh old) :
    Matched ⟨word s,fresh⟩ ⟨oldWord s,old⟩ := by
  have hc := specs s
  simp only [Spec,hrole] at hc
  simp only [RegRel,hrole] at hreg
  obtain ⟨base,hlen,rfl,rfl⟩ := hreg
  cases hi : rowInstr s <;> simp only [hi] at hc
  case inc r' n =>
    obtain ⟨hr,hn,hOld,hrange⟩ := hc
    subst r'
    unfold Matched
    rw [step_on_word]
    simp only [decoded,hi,toInstr,applyInstr]
    have hs := old_step (oldWord s) (.inc r (oldWord n)) (incReg 4 base) hOld
    have hcomm := inc_commute r base hlen hrange
    refine ⟨⟨oldWord n,incReg r (incReg 4 base)⟩,⟨n,rfl,rfl,?_⟩,Relation.TransGen.single hs⟩
    apply regRel_ordinary n hn
    · rw [inc_length,inc_length];exact hlen
    · exact hcomm

theorem half_match (s : Fin 121) (hrole : role s = .halfDec)
    (regs : List Nat) (hlen : regs.length = 5) :
    Matched ⟨word s,regs⟩ ⟨oldWord s,regs⟩ := by
  have hc := specs s
  simp only [Spec,hrole] at hc
  cases hi : rowInstr s <;> simp only [hi] at hc
  case decnz r p z =>
    obtain ⟨hr,hp,hz,hOld,hJump,hLoop⟩ := hc
    subst r
    unfold Matched
    rw [step_on_word]
    simp only [decoded,hi,toInstr,applyInstr]
    have hs := old_step (oldWord s) (.decnz 3 (oldWord p) halfJump) regs hOld
    by_cases hzero : (regs.getD 3 0 == 0) = true
    · simp only [hzero, ↓reduceIte]
      simp only [applyInstr,hzero, ↓reduceIte] at hs
      have hj := old_step halfJump (.jump halfLoop) regs hJump
      simp only [applyInstr] at hj
      have hl := old_step halfLoop (.decnz 3 (oldWord s) (oldWord z)) regs hLoop
      simp only [applyInstr,hzero, ↓reduceIte] at hl
      refine ⟨⟨oldWord z,regs⟩,relates_ordinary z hz regs hlen,?_⟩
      have h1 : Reaches₁ (rhRegStepOf true) ⟨oldWord s,regs⟩ ⟨halfJump,regs⟩ :=
        Relation.TransGen.single hs
      have h2 : Reaches₁ (rhRegStepOf true) ⟨halfJump,regs⟩ ⟨halfLoop,regs⟩ :=
        Relation.TransGen.single hj
      have h3 : Reaches₁ (rhRegStepOf true) ⟨halfLoop,regs⟩ ⟨oldWord z,regs⟩ :=
        Relation.TransGen.single hl
      exact h1.trans (h2.trans h3)
    · have hf : (regs.getD 3 0 == 0) = false := Bool.eq_false_iff.mpr hzero
      simp only [hf]
      simp only [applyInstr,hf] at hs
      exact ⟨⟨oldWord p,regs.set 3 (regs.getD 3 0 - 1)⟩,
        relates_ordinary p hp _ (by simpa using hlen),Relation.TransGen.single hs⟩

theorem step_respects : StateTransition.Respects step (rhRegStepOf true) R := by
  intro fresh old hrel
  obtain ⟨s,hfresh,hold,hreg⟩ := hrel
  rcases fresh with ⟨freshWord,freshRegs⟩
  rcases old with ⟨oldWord',oldRegs⟩
  dsimp only at hfresh hold hreg
  subst freshWord
  subst oldWord'
  have hm : Matched ⟨word s,freshRegs⟩ ⟨oldWord s,oldRegs⟩ := by
    cases hrole : role s with
    | plain =>
      obtain ⟨hlen,heq⟩ : freshRegs.length = 5 ∧ oldRegs = freshRegs := by
        simpa only [RegRel,hrole] using hreg
      subst oldRegs
      have hc := specs s
      simp only [Spec,hrole] at hc
      exact plain_match s freshRegs hlen hc.1 hc.2
    | firstSwap r =>
      obtain ⟨hlen,heq⟩ : freshRegs.length = 5 ∧ oldRegs = freshRegs := by
        simpa only [RegRel,hrole] using hreg
      subst oldRegs
      exact first_match s r hrole freshRegs hlen
    | secondSwap r => exact second_match s r hrole freshRegs oldRegs hreg
    | halfDec =>
      obtain ⟨hlen,heq⟩ : freshRegs.length = 5 ∧ oldRegs = freshRegs := by
        simpa only [RegRel,hrole] using hreg
      subst oldRegs
      exact half_match s hrole freshRegs hlen
  cases hstep : step ⟨word s,freshRegs⟩ <;> simpa only [Matched,hstep] using hm

def stageCfg (M : Nat) : RhRegCfg := ⟨[],[M,0,0,0,0]⟩

theorem stage_related (M : Nat) : R (stageCfg M) (stageCfg M) := by
  have hw : word 0 = [] := by decide +kernel
  have ho : oldWord 0 = [] := by decide +kernel
  have hr : role 0 = .plain := by decide +kernel
  refine ⟨0,hw.symm,ho.symm,?_⟩
  simp only [RegRel,hr,stageCfg]
  simp

theorem stage_halts_iff_edited (M : Nat) :
    (StateTransition.eval step (stageCfg M)).Dom ↔
      (StateTransition.eval (rhRegStepOf true) (stageCfg M)).Dom :=
  (StateTransition.tr_eval_dom step_respects (stage_related M)).symm

end ConjectureMachines.Riemann95.ReferenceLogical
