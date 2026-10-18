/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Cryptids.ReductionSupport.Riemann.ControlWords

@[expose] public section

namespace ConjectureMachines.Riemann104.PhaseB1

open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2

def cap1 (v : Nat) : Nat := min 1 v

def capRegs (regs : List Nat) : List Nat := regs.map cap1

def Allowed (c : RhRegCfg) : Prop :=
  ∃ (s : Fin 121) (m : Fin 32), c.stack = stack s ∧
    capRegs c.regs = decode m ∧ allowed s m = true

theorem cap1_zero_iff (v : Nat) : cap1 v = 0 ↔ v = 0 := by
  unfold cap1
  omega

theorem cap1_succ (v : Nat) : cap1 (v + 1) = 1 := by
  unfold cap1
  omega

theorem cap1_le_one (v : Nat) : cap1 v ≤ 1 := by
  unfold cap1
  omega

theorem cap_getD (regs : List Nat) (r : Nat) :
    (capRegs regs).getD r 0 = cap1 (regs.getD r 0) := by
  induction regs generalizing r with
  | nil => cases r <;> simp [capRegs, cap1]
  | cons x xs ih =>
    cases r with
    | zero => simp [capRegs]
    | succ r => simpa [capRegs, List.getD_cons_succ] using ih r

theorem cap_set (regs : List Nat) (r v : Nat) :
    capRegs (regs.set r v) = (capRegs regs).set r (cap1 v) :=
  List.map_set

theorem initial_member : Allowed rhRegInit := by
  refine ⟨0, 0, initial_allowed.1, ?_, initial_allowed.2.2⟩
  rfl

/-- Every actual edited register step preserves the certified B1 masks.
Positive decrement retains both possible capped results: zero and one. -/
theorem native_step_closed {c c' : RhRegCfg} (hinv : Allowed c)
    (hstep : rhRegStepOf true c = some c') : Allowed c' := by
  rcases c with ⟨bits, regs⟩
  rcases c' with ⟨bits', regs'⟩
  rcases hinv with ⟨s, m, hstack, hregs, hallowed⟩
  dsimp only at hstack hregs
  subst bits
  have he := instruction_exact s
  have hc := finite_closed s m
  unfold closedCheck at hc
  specialize hc hallowed
  unfold rhRegStepOf at hstep
  cases hi : instr s with
  | halt =>
    rw [hi] at he hc
    simp only [expand] at he
    simp [he] at hstep
  | jump t =>
    rw [hi] at he hc
    simp only [expand] at he
    simp only [he, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact ⟨t, m, rfl, hregs, hc⟩
  | inc r t =>
    rw [hi] at he hc
    simp only [expand] at he
    simp only [he, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    refine ⟨t, setMask m r 1, rfl, ?_, hc⟩
    rw [cap_set, cap1_succ, hregs, decode_set]
    rfl
  | decnz r t f =>
    rw [hi] at he hc
    simp only [expand] at he
    rw [he] at hstep
    change (if regs.getD r.val 0 == 0 then some (RhRegCfg.mk (stack f) regs)
      else some (RhRegCfg.mk (stack t) (regs.set r.val (regs.getD r.val 0 - 1)))) =
        some (RhRegCfg.mk bits' regs') at hstep
    have hget := cap_getD regs r.val
    rw [hregs] at hget
    by_cases hz : regs.getD r.val 0 = 0
    · have hzero : (decode m).getD r.val 0 = 0 := by
        rw [hz] at hget
        simpa [cap1] using hget
      simp only [hzero, ite_true] at hc
      have hb : (regs.getD r.val 0 == 0) = true := beq_iff_eq.mpr hz
      rw [hb] at hstep
      simp only [ite_true, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      exact ⟨f, m, rfl, hregs, hc⟩
    · have hnonzero : (decode m).getD r.val 0 ≠ 0 := by
        intro hzero
        exact hz ((cap1_zero_iff _).mp (hget.symm.trans hzero))
      simp only [hnonzero, ite_false] at hc
      have hb : (regs.getD r.val 0 == 0) = false :=
        Bool.eq_false_iff.mpr (fun h => hz (beq_iff_eq.mp h))
      rw [hb] at hstep
      simp only [Bool.false_eq_true, ite_false, Option.some.injEq,
        RhRegCfg.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      by_cases hv : cap1 (regs.getD r.val 0 - 1) = 0
      · refine ⟨t, setMask m r 0, rfl, ?_, hc.1⟩
        rw [cap_set, hv, hregs, decode_set]
        rfl
      · have hone : cap1 (regs.getD r.val 0 - 1) = 1 := by
          have hbound := cap1_le_one (regs.getD r.val 0 - 1)
          omega
        refine ⟨t, setMask m r 1, rfl, ?_, hc.2⟩
        rw [cap_set, hone, hregs, decode_set]
        rfl

theorem reachable_cap_allowed {c : RhRegCfg}
    (hreach : Relation.ReflTransGen
      (fun a b => rhRegStepOf true a = some b) rhRegInit c) : Allowed c := by
  induction hreach with
  | refl => exact initial_member
  | tail _ hs ih => exact native_step_closed ih hs

theorem nSteps_preserves_allowed (k : Nat) {c c' : RhRegCfg}
    (hinv : Allowed c) (hsteps : rhRegNStepsOf true k c = some c') : Allowed c' := by
  induction k generalizing c with
  | zero =>
    simp only [rhRegNStepsOf, Option.some.injEq] at hsteps
    subst c'
    exact hinv
  | succ k ih =>
    unfold rhRegNStepsOf at hsteps
    cases hs : rhRegStepOf true c with
    | none => simp [hs] at hsteps
    | some next =>
      rw [hs, Option.bind_some] at hsteps
      exact ih (native_step_closed hinv hs) hsteps

theorem executed_cap_allowed (k : Nat) {c : RhRegCfg}
    (hsteps : rhRegNStepsOf true k rhRegInit = some c) : Allowed c :=
  nSteps_preserves_allowed k initial_member hsteps

end ConjectureMachines.Riemann104.PhaseB1
