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


theorem half_restore (k : Fin 3) (d m v a x other : Nat) :
    Reaches₁ step (halfCfg k d 4 m v a x other)
      (halfCfg k d 7 m 0 (a+v) x other) := by
  induction v generalizing a with
  | zero =>
    exact Relation.TransGen.single (by
        simpa using (half_step4 k d m 0 a x other))
  | succ v ih =>
    have h1 : Reaches₁ step (halfCfg k d 4 m (v+1) a x other)
        (halfCfg k d 5 m v a x other) :=
      Relation.TransGen.single (by
        simpa using (half_step4 k d m (v+1) a x other))
    have h2 : Reaches₁ step (halfCfg k d 5 m v a x other)
        (halfCfg k d 6 m v (a+1) x other) :=
      Relation.TransGen.single (half_step5 k d m v a x other)
    have h3 : Reaches₁ step (halfCfg k d 6 m v (a+1) x other)
        (halfCfg k d 4 m v (a+1) x other) :=
      Relation.TransGen.single (half_step6 k d m v (a+1) x other)
    have he : a + (v+1) = (a+1)+v := by omega
    rw [he]
    exact h1.trans (h2.trans (h3.trans (ih (a+1))))

theorem half_eval (k : Fin 3) (d m v a x other : Nat) :
    Reaches₁ step (halfCfg k d 0 m v a x other)
      (halfCfg k d 7 m 0 (a/2+v) x other) := by
  induction a using Nat.twoStepInduction generalizing v with
  | zero =>
    have h : Reaches₁ step (halfCfg k d 0 m v 0 x other)
        (halfCfg k d 4 m v 0 x other) :=
      Relation.TransGen.single (by
        simpa using (half_step0 k d m v 0 x other))
    simpa only [Reaches₁, Nat.zero_div, Nat.zero_add, Nat.add_zero] using
      h.trans (half_restore k d m v 0 x other)
  | one =>
    have h1 : Reaches₁ step (halfCfg k d 0 m v 1 x other)
        (halfCfg k d 1 m v 0 x other) :=
      Relation.TransGen.single (by
        simpa using (half_step0 k d m v 1 x other))
    have h2 : Reaches₁ step (halfCfg k d 1 m v 0 x other)
        (halfCfg k d 4 m v 0 x other) :=
      Relation.TransGen.single (by
        simpa using (half_step1 k d m v 0 x other))
    simpa only [Reaches₁, Nat.reduceDiv, Nat.zero_add, Nat.add_zero] using
      h1.trans (h2.trans (half_restore k d m v 0 x other))
  | more a ih _ =>
    have h1 : Reaches₁ step (halfCfg k d 0 m v (a+2) x other)
        (halfCfg k d 1 m v (a+1) x other) :=
      Relation.TransGen.single (by
        simpa using (half_step0 k d m v (a+2) x other))
    have h2 : Reaches₁ step (halfCfg k d 1 m v (a+1) x other)
        (halfCfg k d 2 m v a x other) :=
      Relation.TransGen.single (by
        simpa using (half_step1 k d m v (a+1) x other))
    have h3 : Reaches₁ step (halfCfg k d 2 m v a x other)
        (halfCfg k d 3 m (v+1) a x other) :=
      Relation.TransGen.single (half_step2 k d m v a x other)
    have h4 : Reaches₁ step (halfCfg k d 3 m (v+1) a x other)
        (halfCfg k d 0 m (v+1) a x other) :=
      Relation.TransGen.single (half_step3 k d m (v+1) a x other)
    have he : (a+2)/2+v = a/2+(v+1) := by omega
    rw [he]
    exact h1.trans (h2.trans (h3.trans (h4.trans (ih (v+1)))))

theorem halfj_first (d m v f x j : Nat) :
    Reaches₁ step ⟨.local d 0,[m,v,f,x,j]⟩ ⟨.local d 7,[m,0,f,x,j/2+v]⟩ :=
  half_eval 0 d m v j x f

theorem halfj_second (d m v f x j : Nat) :
    Reaches₁ step ⟨.local d 7,[m,v,f,x,j]⟩ ⟨.local d 14,[m,0,f,x,j/2+v]⟩ :=
  half_eval 1 d m v j x f

theorem halff (d m v f x j : Nat) :
    Reaches₁ step ⟨.local d 14,[m,v,f,x,j]⟩ ⟨.entry (d+1),[m,0,f/2+v,x,j]⟩ :=
  half_eval 2 d m v f x j

end ConjectureMachines.Riemann95.Control
