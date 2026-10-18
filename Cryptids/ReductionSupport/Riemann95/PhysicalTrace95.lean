/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.RootNative95
public import Cryptids.ReductionSupport.Riemann95.Return95
public import Cryptids.ReductionSupport.Riemann95.ControlStep95
public import Cryptids.ReductionSupport.Riemann95.StrictExit95
public import Cryptids.ReductionSupport.Riemann95.PrecreditTrace95

/-! # Physical execution and width -/

@[expose] public section

/-! ## Instruction traces -/

section

namespace ConjectureMachines.Riemann95.Trace

open Riemann120.Layer2 Schema Control

attribute [local irreducible] Control.instruction Control.effect Control.walked
  Control.localEffects Control.outsideEffects Control.outsideInstrs Control.localInstr

theorem physical_arithmetic_step (c : ControlWord) (regs extra : List Nat)
    (hlen : regs.length = 5) (P : Nat) (hP : (walked c).length + 3 ≤ P)
    (next : RhRegCfg) (hnext : applyInstr (rawInstr c) regs = some next)
    (r : Fin 5) (inc : Bool) (he : effect c = if inc then .inc r else .decnz r) :
    ∃ P' ≥ P, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P (word c) (regs ++ extra)) =
        some (Physical.rootCfg P' next.stack (next.regs ++ extra')) ∧
      (next.stack = [] → P + 1 ≤ P') := by
  have hr : r.val < regs.length := by omega
  have hrbank : r.val < (regs ++ extra).length := by simp only [List.length_append]; omega
  obtain ⟨n,hn,hsteps⟩ := Dispatch.root_native c r inc he P (regs ++ extra) hrbank (by omega)
  simp only [List.getD_append regs extra 0 r.val hr] at hsteps
  have strict (k : Fin 2) (hk : k.val ≤ (walked c).count 0)
      (hempty : (popBreakRev k.val (walked c).reverse).reverse = []) :
      P + 1 ≤ Physical.exactPad k (walked c) (P - (walked c).length) := by
    have hh := Physical.exactPad_of_return_empty k (walked c)
      (P - (walked c).length) hk hempty
    omega
  cases inc with
  | true =>
    simp only [ite_true] at he hsteps
    simp only [rawInstr,he,applyInstr,returned,Bool.false_eq_true,ite_false,
      Option.some.injEq] at hnext
    subst next
    have hge := Physical.exactPad_ge 0 (walked c) (P - (walked c).length)
    refine ⟨_,by omega,n,hn,extra,?_,strict 0 (by omega)⟩
    simpa only [List.set_append_left _ _ hr,Fin.val_zero] using hsteps
  | false =>
    simp only [Bool.false_eq_true,ite_false] at he hsteps
    simp only [rawInstr,he,applyInstr,returned,Bool.false_eq_true,ite_false,beq_iff_eq] at hnext
    by_cases hz : regs.getD r.val 0 = 0
    · simp only [hz,ite_true,Option.some.injEq] at hnext hsteps
      subst next
      have hge := Physical.exactPad_ge 1 (walked c) (P - (walked c).length)
      refine ⟨_,by omega,n,hn,extra,hsteps,strict 1 ?_⟩
      exact Dispatch.dec_walk_count c r he
    · simp only [hz,ite_false,Option.some.injEq] at hnext hsteps
      subst next
      have hge := Physical.exactPad_ge 0 (walked c) (P - (walked c).length)
      refine ⟨_,by omega,n,hn,extra ++ [0],?_,strict 0 (by omega)⟩
      simpa only [List.set_append_left _ _ hr,List.append_assoc,Fin.val_zero] using hsteps

theorem physical_step (a b : Control.Cfg) (hlen : a.regs.length = 5)
    (P : Nat) (hP : (walked a.control).length + 3 ≤ P)
    (hs : Control.step a = some b) (extra : List Nat) :
    ∃ P' ≥ P, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P (word a.control) (a.regs ++ extra)) =
        some (Physical.rootCfg P' (word b.control) (b.regs ++ extra')) := by
  have hnext : applyInstr (rawInstr a.control) a.regs = some ⟨word b.control,b.regs⟩ := by
    rw [← step_encode,hs]
    rfl
  cases he : effect a.control with
  | halt => simp only [rawInstr,he,applyInstr] at hnext; contradiction
  | inc r =>
    obtain ⟨P',hge,n,hn,tail,ht,_⟩ :=
      physical_arithmetic_step a.control a.regs extra hlen P hP _ hnext r true he
    exact ⟨P',hge,n,hn,tail,ht⟩
  | decnz r =>
    obtain ⟨P',hge,n,hn,tail,ht,_⟩ :=
      physical_arithmetic_step a.control a.regs extra hlen P hP _ hnext r false he
    exact ⟨P',hge,n,hn,tail,ht⟩
  | jump cont k =>
    have hj : rawInstr a.control = .jump (returned cont k (walked a.control)) := by
      simp only [rawInstr,he]
    rw [hj] at hnext
    simp only [applyInstr,Option.some.injEq] at hnext
    obtain ⟨n,hn,ht⟩ := RootJump.root_jump a.control _ hj P hP (a.regs ++ extra)
    have hw : returned cont k (walked a.control) = word b.control := congrArg RhRegCfg.stack hnext
    have hr : a.regs = b.regs := congrArg RhRegCfg.regs hnext
    refine ⟨P,le_rfl,n,hn,extra,?_⟩
    rw [←hw,←hr]
    exact ht

end ConjectureMachines.Riemann95.Trace

end

/-! ## Lifting traces -/

section

namespace ConjectureMachines.Riemann95.Trace

open Riemann120.Layer2 Schema Control

theorem bounded_trace_regs_length {B : Nat} {a b : Control.Cfg}
    (ht : Relation.TransGen (BoundedEdge B) a b) (hlen : a.regs.length = 5) :
    b.regs.length = 5 := by
  induction ht with
  | single he => exact (step_regs_length _ _ he.1).trans hlen
  | tail ht he ih => exact (step_regs_length _ _ he.1).trans ih

theorem bounded_rtrace_regs_length {B : Nat} {a b : Control.Cfg}
    (ht : Relation.ReflTransGen (BoundedEdge B) a b) (hlen : a.regs.length = 5) :
    b.regs.length = 5 := by
  induction ht with
  | refl => exact hlen
  | tail ht he ih => exact (step_regs_length _ _ he.1).trans ih

theorem bounded_trace_lift (B P : Nat) (hP : B ≤ P) (a b : Control.Cfg)
    (hlen : a.regs.length = 5) (ht : Relation.TransGen (BoundedEdge B) a b)
    (extra : List Nat) :
    ∃ P' ≥ P, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P (word a.control) (a.regs ++ extra)) =
        some (Physical.rootCfg P' (word b.control) (b.regs ++ extra')) := by
  induction ht generalizing P extra with
  | single he => exact physical_step a _ hlen P (le_trans he.2 hP) he.1 extra
  | @tail c d ht he ih =>
    obtain ⟨Q,hQ,n,hn,tail,hrun⟩ := ih P hP extra
    have hc : c.regs.length = 5 := bounded_trace_regs_length ht hlen
    obtain ⟨Q',hQ',s,hs,tail',hnext⟩ :=
      physical_step c d hc Q (le_trans he.2 (le_trans hP hQ)) he.1 tail
    refine ⟨Q',le_trans hQ hQ',n+s,by omega,tail',?_⟩
    rw [Dispatch.nSteps_composition,hrun]
    exact hnext

theorem bounded_rtrace_lift (B P : Nat) (hP : B ≤ P) (a b : Control.Cfg)
    (hlen : a.regs.length = 5) (ht : Relation.ReflTransGen (BoundedEdge B) a b)
    (extra : List Nat) :
    ∃ P' ≥ P, ∃ n : Nat, ∃ extra',
      nSteps n (Physical.rootCfg P (word a.control) (a.regs ++ extra)) =
        some (Physical.rootCfg P' (word b.control) (b.regs ++ extra')) := by
  obtain heq | ht := Relation.reflTransGen_iff_eq_or_transGen.mp ht
  · subst b
    exact ⟨P,le_rfl,0,extra,rfl⟩
  · obtain ⟨P',hP',n,_,extra',hrun⟩ := bounded_trace_lift B P hP a b hlen ht extra
    exact ⟨P',hP',n,extra',hrun⟩

theorem strict_exit_lift (B P : Nat) (hP : B ≤ P) (a b : Control.Cfg)
    (hlen : a.regs.length = 5) (hb : word b.control = [])
    (ht : StrictExitTrace B a b) (extra : List Nat) :
    ∃ P' ≥ P+1, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P (word a.control) (a.regs ++ extra)) =
        some (Physical.rootCfg P' (word b.control) (b.regs ++ extra')) := by
  obtain ⟨mid,hprefix,hedge,heffect,_,_⟩ := ht
  have hmidlen : mid.regs.length = 5 := bounded_rtrace_regs_length hprefix hlen
  obtain ⟨Q,hQ,n,tail,hrun⟩ := bounded_rtrace_lift B P hP a mid hlen hprefix extra
  have hnext : applyInstr (rawInstr mid.control) mid.regs = some ⟨word b.control,b.regs⟩ := by
    rw [← step_encode,hedge.1]
    rfl
  obtain ⟨Q',_,s,hs,tail',hfinal,hgrow⟩ :=
    physical_arithmetic_step mid.control mid.regs tail hmidlen Q
      (le_trans hedge.2 (le_trans hP hQ)) _ hnext 2 false heffect
  have hstrict := hgrow hb
  refine ⟨Q',by omega,n+s,by omega,tail',?_⟩
  rw [Dispatch.nSteps_composition,hrun]
  exact hfinal

end ConjectureMachines.Riemann95.Trace

end

/-! ## Width execution -/

section

namespace ConjectureMachines.Riemann95.Trace

open Riemann120.Layer2 Schema Control

theorem physical_precredit_width (P x j f : Nat) (extra : List Nat)
    (hP : widthBudget j ≤ P) :
    ∃ P' ≥ P, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P [1,1,1,1] ([0,0,f,x,j] ++ extra)) =
        some (Physical.rootCfg P'
          (if Algorithm.residual j f = 0 then [] else word (.outside finalHaltId))
          ([0,0,Algorithm.residual j f-1,x+j,0] ++ extra')) := by
  have h := bounded_trace_lift (widthBudget j) P hP _ _ (by rfl)
    (bounded_precredit_width x j f) extra
  rw [widthCall_word] at h
  by_cases hz : Algorithm.residual j f = 0
  · simpa only [hz,ite_true,initial_word] using h
  · simpa only [hz,ite_false] using h

theorem physical_precredit_width_zero (P x j f : Nat) (extra : List Nat)
    (hP : widthBudget j ≤ P) (hr : Algorithm.residual j f = 0) :
    ∃ P' ≥ P+1, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P [1,1,1,1] ([0,0,f,x,j] ++ extra)) =
        some (Physical.rootCfg P' [] ([0,0,0,x+j,0] ++ extra')) := by
  have h := strict_exit_lift (widthBudget j) P hP _ _ (by rfl) (by rfl)
    (strict_precredit_width_zero x j f hr) extra
  simpa only [widthCall_word,initial_word] using h

end ConjectureMachines.Riemann95.Trace

end
