/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104

@[expose] public section

namespace ConjectureMachines.Riemann95.Algorithm

open ConjectureMachines.Riemann120 (quarterClock)

/-- Destructive clock evaluation with one saturated decrement on each unwind. -/
def residual : Nat → Nat → Nat
  | 0, f => f
  | n+1, f => residual (n/4) (f/2) - 1
termination_by n _ => n
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self n 4)

theorem residual_eq (j f : Nat) :
    residual j f = f / 2 ^ quarterClock j - quarterClock j := by
  induction j using Nat.strong_induction_on generalizing f with
  | h j ih =>
    cases j with
    | zero => simp [residual,quarterClock]
    | succ n =>
      rw [residual,quarterClock,
        ih (n/4) (Nat.lt_succ_of_le (Nat.div_le_self n 4)) (f/2),
        Nat.div_div_eq_div_mul,Nat.pow_add,Nat.pow_one,Nat.sub_sub]
      omega

theorem residual_pos_iff (j f : Nat) :
    0 < residual j f ↔ quarterClock j < f / 2 ^ quarterClock j := by
  rw [residual_eq,Nat.sub_pos_iff_lt]

theorem residual_zero (j : Nat) : residual j 0 = 0 := by simp [residual_eq]

theorem skip_saturated_debts (debt : Nat) : (0 : Nat) - debt = 0 := by simp

/-- The stage counter is completed before entering recursion. -/
def resultBank (x j f : Nat) : List Nat := [0,0,residual j f,x+j,0]

theorem resultBank_eq (x j f : Nat) :
    resultBank x j f = [0,0,f/2^quarterClock j-quarterClock j,x+j,0] := by
  rw [resultBank,residual_eq]

theorem resultBank_zero (x j : Nat) : resultBank x j 0 = [0,0,0,x+j,0] := by
  rw [resultBank,residual_zero]

end ConjectureMachines.Riemann95.Algorithm
