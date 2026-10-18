/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.PhysicalTrace95
public import Cryptids.ReductionSupport.Riemann95.StrictExit95

@[expose] public section

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
