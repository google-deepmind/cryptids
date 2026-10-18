/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ControlStep95

/-! Atomic control steps for register halving, recursive entry, and unwinding. -/

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open StateTransition Schema

section

attribute [local irreducible] localEffects outsideEffects outsideInstrs rawInstr

def halfWord (k : Fin 3) (d : Nat) (s : Fin 8) : ControlWord :=
  if s.val = 7 then
    match k.val with
    | 0 => .local d 7
    | 1 => .local d 14
    | _ => .entry (d+1)
  else .local d ⟨7*k.val+s.val, by omega⟩

def halfCfg (k : Fin 3) (d : Nat) (s : Fin 8) (m v a x other : Nat) : Cfg :=
  ⟨halfWord k d s,
    if k.val = 2 then [m,v,a,x,other] else [m,v,other,x,a]⟩

theorem half_step0 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 0 m v a x other) =
      some (halfCfg k d (if a = 0 then 4 else 1) m v (a-1) x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step1 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 1 m v a x other) =
      some (halfCfg k d (if a = 0 then 4 else 2) m v (a-1) x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step2 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 2 m v a x other) = some (halfCfg k d 3 m (v+1) a x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step3 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 3 m v a x other) = some (halfCfg k d 0 m v a x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step4 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 4 m v a x other) =
      some (halfCfg k d (if v = 0 then 7 else 5) m (v-1) a x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step5 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 5 m v a x other) = some (halfCfg k d 6 m v (a+1) x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step6 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 6 m v a x other) = some (halfCfg k d 4 m v a x other) := by
  fin_cases k <;> rcases d with _ | (_ | d) <;>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

end

section

attribute [local irreducible] localEffects outsideEffects outsideInstrs rawInstr localInstr

theorem entry_positive_step (d f x j : Nat) :
    step ⟨.entry d,[0,0,f,x,j+1]⟩ = some ⟨.local d 0,[0,0,f,x,j]⟩ := by
  cases d <;> simp [step,instruction]

end

section

attribute [local irreducible] localEffects outsideEffects outsideInstrs rawInstr
  localInstr instruction

theorem unwind0_step (f x : Nat) :
    step ⟨unwind 0,[0,0,f,x,0]⟩ =
      some ⟨if f = 0 then .outside 0 else .outside finalTestId,[0,0,f-1,x,0]⟩ := by
  simp only [step,unwind_zero]
  by_cases hf : f = 0 <;> simp [hf]

theorem unwind1_zero_step (x : Nat) :
    step ⟨unwind 1,[0,0,0,x,0]⟩ = some ⟨.outside finalTestId,[0,0,0,x,0]⟩ := by
  simp [step,unwind_one]

theorem unwind_succ_positive_step (d f x : Nat) :
    step ⟨unwind (d+1),[0,0,f+1,x,0]⟩ = some ⟨unwind d,[0,0,f,x,0]⟩ := by
  cases d with
  | zero => simp [step,unwind_one]
  | succ d => simp [step,unwind_succ_succ]

theorem unwind_succ_succ_zero_step (d x : Nat) :
    step ⟨unwind (d+2),[0,0,0,x,0]⟩ = some ⟨unwind d,[0,0,0,x,0]⟩ := by
  simp [step,unwind_succ_succ]

theorem final_test_step (f x : Nat) :
    step ⟨.outside finalTestId,[0,0,f,x,0]⟩ =
      some ⟨if f = 0 then .outside 0 else .outside finalHaltId,[0,0,f-1,x,0]⟩ := by
  simp only [step,final_test]
  by_cases hf : f = 0 <;> simp [hf]

end

end ConjectureMachines.Riemann95.Control
