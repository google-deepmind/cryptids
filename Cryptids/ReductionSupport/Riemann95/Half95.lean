/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ControlStep95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open StateTransition Schema

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
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step1 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 1 m v a x other) =
      some (halfCfg k d (if a = 0 then 4 else 2) m v (a-1) x other) := by
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step2 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 2 m v a x other) = some (halfCfg k d 3 m (v+1) a x other) := by
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step3 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 3 m v a x other) = some (halfCfg k d 0 m v a x other) := by
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step4 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 4 m v a x other) =
      some (halfCfg k d (if v = 0 then 7 else 5) m (v-1) a x other) := by
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step5 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 5 m v a x other) = some (halfCfg k d 6 m v (a+1) x other) := by
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]

theorem half_step6 (k : Fin 3) (d : Nat) (m v a x other : Nat) :
    step (halfCfg k d 6 m v a x other) = some (halfCfg k d 4 m v a x other) := by
  fin_cases k <;> cases d with
  | zero =>
    by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
      simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
  | succ d =>
    cases d with
    | zero =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]
    | succ d =>
      by_cases ha : a = 0 <;> by_cases hv : v = 0 <;>
        simp [step, instruction, localInstr, halfCfg, halfWord, ha, hv]


end ConjectureMachines.Riemann95.Control
