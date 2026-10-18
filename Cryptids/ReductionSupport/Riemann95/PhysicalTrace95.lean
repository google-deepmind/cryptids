/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.RootNative95
public import Cryptids.ReductionSupport.Riemann95.RootJump95
public import Cryptids.ReductionSupport.Riemann95.TypedClosure95

@[expose] public section

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
