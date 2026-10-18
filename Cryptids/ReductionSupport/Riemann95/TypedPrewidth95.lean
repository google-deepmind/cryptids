/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.SwapBank95
public import Cryptids.ReductionSupport.Riemann95.Initializer95

@[expose] public section

namespace ConjectureMachines.Riemann95.TypedPrewidth

open Schema
open ConjectureMachines.Riemann120.Layer2 (RhRegCfg)

attribute [local irreducible] ReferenceProgram.word ReferenceProgram.decoded
  ReferenceProgram.instruction ReferenceLogical.word ReferenceLogical.decoded
  ReferenceLogical.instruction ReferencePreStep95

def ctl89 (s : Fin 89) : Fin 97 := s.castLE (by decide)
def ref89 (s : Fin 89) : Fin 121 := s.castLE (by decide)
def ctl85 (s : Fin 85) : Fin 97 := ⟨s.val+3,by omega⟩
def ref85 (s : Fin 85) : Fin 121 := ⟨s.val+3,by omega⟩

theorem words_match : ∀ s : Fin 89,
    outsideWord (ctl89 s) = ReferenceProgram.word (ref89 s) := by decide +kernel

theorem instructions_match : ∀ s : Fin 85,
    Control.rawInstr (.outside (ctl85 s)) = swapInstr (ReferenceProgram.decoded (ref85 s)) := by
  decide +kernel

theorem word88_unique : ∀ s : Fin 89,
    ReferenceProgram.word (ref89 s) = ReferenceProgram.word 88 → s.val = 88 := by
  decide +kernel

theorem word88_match : word (.outside 88) = ReferenceProgram.word 88 := by decide +kernel
theorem word3_match : word (.outside 3) = ReferenceProgram.word 3 := by decide +kernel

def InPrewidth : ControlWord → Prop
  | .outside i => 3 ≤ i.val ∧ i.val < 89
  | _ => False

instance (c : ControlWord) : Decidable (InPrewidth c) := by
  cases c <;> simp only [InPrewidth] <;> infer_instance

def nextControls : Control.Instr → List ControlWord
  | .halt => []
  | .jump n | .inc _ n => [n]
  | .decnz _ p z => [p,z]

theorem targets_match : ∀ s : Fin 85,
    (nextControls (Control.instruction (.outside (ctl85 s)))).all
      (fun c => decide (InPrewidth c)) = true := by decide +kernel

def encodeCfg (c : Control.Cfg) : RhRegCfg := ⟨word c.control,swapBank c.regs⟩

def preStep (c : Control.Cfg) : Option Control.Cfg :=
  if c.control = .outside 88 then none else Control.step c

theorem word_range (i : Fin 97) (hi : i.val < 89) :
    word (.outside i) = ReferenceProgram.word (ref89 ⟨i.val,hi⟩) := by
  have h := words_match ⟨i.val,hi⟩
  have he : ctl89 ⟨i.val,hi⟩ = i := by apply Fin.ext; rfl
  simpa only [he,word] using h

theorem instruction_range (i : Fin 97) (hlo : 3 ≤ i.val) (hi : i.val < 88) :
    Control.rawInstr (.outside i) =
      swapInstr (ReferenceProgram.decoded (ref85 ⟨i.val-3,by omega⟩)) := by
  let j : Fin 85 := ⟨i.val-3,by omega⟩
  have he : ctl85 j = i := by apply Fin.ext; dsimp [ctl85,j]; omega
  simpa only [he] using instructions_match j

theorem step_control_mem (c next : Control.Cfg) (h : Control.step c = some next) :
    next.control ∈ nextControls (Control.instruction c.control) := by
  unfold Control.step at h
  cases hi : Control.instruction c.control with
  | halt => simp only [hi] at h; cases h
  | jump n => simp only [hi] at h; cases h; simp [nextControls]
  | inc r n => simp only [hi] at h; cases h; simp [nextControls]
  | decnz r p z =>
    simp only [hi] at h
    split at h <;> cases h <;> simp [nextControls]

theorem preStep_closed (c next : Control.Cfg) (hc : InPrewidth c.control)
    (h : preStep c = some next) : InPrewidth next.control := by
  cases hctrl : c.control with
  | entry d => simp only [hctrl,InPrewidth] at hc
  | «local» d s => simp only [hctrl,InPrewidth] at hc
  | outside i =>
    rw [hctrl] at hc
    change 3 ≤ i.val ∧ i.val < 89 at hc
    have hcut : c.control ≠ .outside 88 := by
      intro he
      simp only [preStep,he,ite_true] at h
      cases h
    have hi : i.val ≠ 88 := by
      intro hv
      apply hcut
      rw [hctrl]
      congr 1
      exact Fin.ext hv
    have hi88 : i.val < 88 := by omega
    let j : Fin 85 := ⟨i.val-3,by omega⟩
    have hj : ctl85 j = i := by apply Fin.ext; dsimp [ctl85,j]; omega
    have hs : Control.step c = some next := by
      simpa only [preStep,ite_eq_right hcut] using h
    have hm := step_control_mem c next hs
    rw [hctrl,←hj] at hm
    exact of_decide_eq_true ((List.all_eq_true.mp (targets_match j)) _ hm)

theorem preStep_encode (c : Control.Cfg) (hc : InPrewidth c.control)
    (hlen : c.regs.length = 5) :
    (preStep c).map encodeCfg = ReferencePreStep95 (encodeCfg c) := by
  rcases c with ⟨control,regs⟩
  cases control with
  | entry d => cases hc
  | «local» d s => cases hc
  | outside i =>
    change 3 ≤ i.val ∧ i.val < 89 at hc
    by_cases hi : i.val = 88
    · have he : i = (88 : Fin 97) := Fin.ext hi
      subst i
      simp [preStep,ReferencePreStep95,encodeCfg,word88_match]
    · have hi88 : i.val < 88 := by omega
      have hword := word_range i hc.2
      have hword_ne : word (.outside i) ≠ ReferenceProgram.word 88 := by
        intro he
        rw [hword] at he
        exact hi (word88_unique ⟨i.val,hc.2⟩ he)
      have hctrl_ne : (ControlWord.outside i) ≠ .outside 88 := by
        intro he
        exact hi (congrArg Fin.val (ControlWord.outside.inj he))
      have hinstr := instruction_range i hc.1 hi88
      have href_index : ref89 ⟨i.val,hc.2⟩ = ref85 ⟨i.val-3,by omega⟩ := by
        apply Fin.ext
        dsimp [ref89,ref85]
        omega
      have hbase : (Control.step ⟨.outside i,regs⟩).map encodeCfg =
          ReferenceProgram.step (encodeCfg ⟨.outside i,regs⟩) := by
        have hmap : (Control.step ⟨.outside i,regs⟩).map encodeCfg =
            ((Control.step ⟨.outside i,regs⟩).map Control.encodeCfg).map swapCfg := by
          rw [Option.map_map]
          rfl
        rw [hmap,Control.step_encode,hinstr,apply_swapInstr _ _ hlen]
        change Control.applyInstr (ReferenceProgram.decoded (ref85 ⟨i.val-3,by omega⟩))
          (swapBank regs) = ReferenceProgram.step ⟨word (.outside i),swapBank regs⟩
        rw [hword,href_index]
        unfold ReferenceProgram.step
        rw [ReferenceProgram.instruction_word]
        cases ReferenceProgram.decoded (ref85 ⟨i.val-3,by omega⟩) <;> rfl
      have hpre : preStep ⟨.outside i,regs⟩ = Control.step ⟨.outside i,regs⟩ := by
        unfold preStep
        exact ite_eq_right hctrl_ne
      have href : ReferencePreStep95 (encodeCfg ⟨.outside i,regs⟩) =
          ReferenceProgram.step (encodeCfg ⟨.outside i,regs⟩) := by
        unfold ReferencePreStep95
        exact ite_eq_right hword_ne
      rw [hpre,href]
      exact hbase

theorem edge_transport (c : Control.Cfg) (next : RhRegCfg) (hc : InPrewidth c.control)
    (hlen : c.regs.length = 5) (h : ReferencePreStep95 (encodeCfg c) = some next) :
    ∃ target : Control.Cfg, Control.BoundedEdge 19 c target ∧ encodeCfg target = next ∧
      InPrewidth target.control ∧ target.regs.length = 5 := by
  have hm := (preStep_encode c hc hlen).trans h
  cases hs : preStep c with
  | none => simp only [hs,Option.map_none] at hm; cases hm
  | some target =>
    have he : encodeCfg target = next := by
      simpa only [hs,Option.map_some,Option.some.injEq] using hm
    have ht := preStep_closed c target hc hs
    have hstep : Control.step c = some target := by
      unfold preStep at hs
      split at hs
      · cases hs
      · exact hs
    have hbound : (Control.walked c.control).length + 3 ≤ 19 := by
      cases hctrl : c.control with
      | entry d => simp only [hctrl,InPrewidth] at hc
      | «local» d s => simp only [hctrl,InPrewidth] at hc
      | outside i =>
        have hl := outsideWalk_length i
        change (outsideWalk i).length + 3 ≤ 19
        omega
    exact ⟨target,⟨hstep,hbound⟩,he,ht,(Control.step_regs_length c target hstep).trans hlen⟩

theorem trace_transport {a b : RhRegCfg}
    (h : StateTransition.Reaches₁ ReferencePreStep95 a b)
    (c : Control.Cfg) (he : encodeCfg c = a) (hc : InPrewidth c.control)
    (hlen : c.regs.length = 5) :
    ∃ target : Control.Cfg, Relation.TransGen (Control.BoundedEdge 19) c target ∧
      encodeCfg target = b ∧ InPrewidth target.control ∧ target.regs.length = 5 := by
  induction h generalizing c with
  | @single b hs =>
    have hs' : ReferencePreStep95 a = some b := by simpa only [Option.mem_def] using hs
    rw [←he] at hs'
    obtain ⟨target,ht,he',hc',hl'⟩ := edge_transport c b hc hlen hs'
    exact ⟨target,Relation.TransGen.single ht,he',hc',hl'⟩
  | @tail b d h hs ih =>
    obtain ⟨mid,ht,hem,hcm,hlm⟩ := ih c he hc hlen
    have hs' : ReferencePreStep95 b = some d := by simpa only [Option.mem_def] using hs
    rw [←hem] at hs'
    obtain ⟨target,hlast,he',hc',hl'⟩ := edge_transport mid d hcm hlm hs'
    exact ⟨target,ht.tail hlast,he',hc',hl'⟩

theorem post_prewidth (M : Nat) :
    Relation.TransGen (Control.BoundedEdge 19)
      (⟨.outside 3,[0,0,M,0,0]⟩ : Control.Cfg)
      ⟨.outside 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ := by
  let start : Control.Cfg := ⟨.outside 3,[0,0,M,0,0]⟩
  have hstart : encodeCfg start = ⟨ReferenceProgram.word 3,[0,0,M,0,0]⟩ := by
    change (⟨word (.outside 3),[0,0,M,0,0]⟩ : RhRegCfg) = _
    rw [word3_match]
  have hscope : InPrewidth start.control := by change 3 ≤ (3 : Nat) ∧ 3 < 89; decide
  obtain ⟨target,ht,he,hc,hlen⟩ := trace_transport (post_reference_trace M) start hstart hscope rfl
  rcases target with ⟨control,regs⟩
  cases control with
  | entry d => cases hc
  | «local» d s => cases hc
  | outside i =>
    change 3 ≤ i.val ∧ i.val < 89 at hc
    have hstack := congrArg RhRegCfg.stack he
    have hregs := congrArg RhRegCfg.regs he
    change word (.outside i) = ReferenceProgram.word 88 at hstack
    rw [word_range i hc.2] at hstack
    have hi := word88_unique ⟨i.val,hc.2⟩ hstack
    have hi' : i = (88 : Fin 97) := Fin.ext hi
    subst i
    change swapBank regs = [0,0,Riemann120.shuniaDeficit (M+2),0,M+1] at hregs
    have hr := congrArg swapBank hregs
    rw [swapBank_twice regs hlen] at hr
    change regs = [0,0,Riemann120.shuniaDeficit (M+2),0,M+1] at hr
    subst regs
    exact ht

theorem stage_prewidth (M : Nat) :
    Relation.TransGen (Control.BoundedEdge 19)
      (⟨.outside 0,[0,0,0,M,0]⟩ : Control.Cfg)
      ⟨.outside 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ := by
  have hi := initializer M 0
  simp only [Nat.zero_add] at hi
  exact hi.trans (post_prewidth M)

end ConjectureMachines.Riemann95.TypedPrewidth
