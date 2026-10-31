/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF
public import BusyBeaver.BB6.Accelerations.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA
public import BusyBeaver.BB6.Accelerations.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA
public import BusyBeaver.BB6.Accelerations.M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB
public import BusyBeaver.BB6.Accelerations.M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD
public import BusyBeaver.BB6.Accelerations.M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA
public import BusyBeaver.BB6.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
public import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
public import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC
public import BusyBeaver.BB6.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE
public import BusyBeaver.BB6.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
public import BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
public import BusyBeaver.BB6.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
public import BusyBeaver.BB6.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC
public import BusyBeaver.BB6.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA
public import BusyBeaver.BB6.M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD
public import BusyBeaver.BB6.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
public import BusyBeaver.BB6.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
public import BusyBeaver.BB6.M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE
public import BusyBeaver.BB6.M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE
public import BusyBeaver.BB6.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
public import BusyBeaver.BB6.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE
public import BusyBeaver.BB6.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
public import BusyBeaver.BB6.M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE
public import BusyBeaver.BB6.M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD
public import BusyBeaver.BB6.M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB

/-!
# Formal Hardness Evidence for `BB(6)` Accelerated Machines (`BusyBeaver.BB6.HardnessEvidence`)

Kernel-checked theorems certifying that the halting transitions discussed in
`BusyBeaver.BB6.Hardness` are **live** and **arithmetically structured** on the certified
accelerated state spaces (`State` / `HighLevelState`) of the 26 `BB(6)` machines in this
repository that expose an explicit Collatz-like map `next` or `highLevelNext`:

1. **Live hazard witnesses** (`halting_state_witness`): an explicit accelerated configuration `s`
   with `highLevelNext s = none` (or `next s = none`). By `IsValidAcceleration.step_none`, every
   such witness corresponds to a concrete Turing machine configuration `highLevelEncode s` (or
   `encode s`) that reaches the undefined transition in a positive number of raw steps (`⊢⁺`).
2. **Parametric halting residue classes** (`halting_residue_class`): infinite arithmetic,
   divisibility, or power-of-two families of accelerated configurations that halt in one (or
   finitely many) accelerated steps, certifying the exact exit gates (`MOD`, `EQ`, `DIV`, `POW`)
   classified in `BusyBeaver.BB6.Hardness`.

These theorems characterize the preimage of `none` under the certified accelerated maps; they do
not decide whether the forward orbit from `start` / `highLevelStart` enters that preimage.
-/

@[expose] public section

namespace BusyBeaver.HardnessEvidence

/-! ## Problems 1–5 (Named Community Cryptids) -/

namespace M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA

open BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA

/-- Live hazard witness for `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`: `S6 2` halts in one
accelerated step. -/
theorem halting_state_witness : next (.S6 2) = none :=
  rfl

/-- Second halting witness on `S6`: `S6 17` halts in one accelerated step. -/
theorem halting_state_witness_17 : next (.S6 17) = none :=
  rfl

/-- Third halting witness on `S6`: `S6 25` halts in one accelerated step. -/
theorem halting_state_witness_25 : next (.S6 25) = none :=
  rfl

/-- Remainder-`3 mod 5` halting family for `next_HubTail_r_3`. -/
theorem halting_residue_class (a k : ℕ) : next_HubTail_r_3 a (5 * k + 3) = none := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [show 5 * (k + 1) + 3 = (5 * k + 3) + 5 by omega, next_HubTail_r_3]
    exact ih (a + 31)

end M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA

namespace M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

open BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

/-- Live hazard witness for `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`: `P_1 1 2` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.P_1 1 2) = none := by
  simp [highLevelNext]

/-- Odd-`a` halting family at `b = 2`: `P_1 (2k + 1) 2` halts for all `k`. -/
theorem halting_residue_class (k : ℕ) : highLevelNext (.P_1 (2 * k + 1) 2) = none := by
  have h : (2 * k + 1) % 2 = 1 := by omega
  simp [highLevelNext, h]

/-- Exact characterization of one-step halting at `b = 2`: `P_1 a 2` halts iff `a` is odd. -/
theorem halting_residue_class_iff (a : ℕ) : highLevelNext (.P_1 a 2) = none ↔ a % 2 = 1 := by
  simp only [highLevelNext]
  split_ifs <;> simp <;> omega

end M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

open BusyBeaver.M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

/-- Live hazard witness for `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`: `D false 0 2` halts in
one high-level step. -/
theorem halting_state_witness : highLevelNext (.D false 0 2) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family (`p = false`): `D false a (2a + 2)` halts for all `a`. -/
theorem halting_residue_class (a : ℕ) : highLevelNext (.D false a (2 * a + 2)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Exact-equality halting family (`p = true`): `D true a (2a + 2)` halts for all `a`. -/
theorem halting_residue_class_true (a : ℕ) : highLevelNext (.D true a (2 * a + 2)) = none := by
  simp only [highLevelNext]
  rw [drainJ1]
  split_ifs <;> first | rfl | omega

/-- Next-rung halting family (`p = true`): `D true a (6a + 16)` halts in one `drainJ1` peel. -/
theorem halting_residue_class_two_step (a : ℕ) :
    highLevelNext (.D true a (6 * a + 16)) = none := by
  simp only [highLevelNext]
  rw [drainJ1]
  split_ifs <;> first | rfl | omega | skip
  rw [drainJ1]
  split_ifs <;> first | rfl | omega

end M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

open BusyBeaver.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

/-- Live hazard witness for `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`: `D 0 2` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.D 0 2) = none := by
  simp [highLevelNext]

/-- First-rung halting family: `D a (2a + 2)` halts for all `a`. -/
theorem halting_residue_class (a : ℕ) : highLevelNext (.D a (2 * a + 2)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Second-rung halting family: `D a (6a + 12)` halts via `evalK2` for all `a`. -/
theorem halting_residue_class_two_step (a : ℕ) : highLevelNext (.D a (6 * a + 12)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega | skip
  rw [evalK2]
  split_ifs <;> first | rfl | omega

end M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

namespace M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Live hazard witness for `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`: `J 1 1` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.J 1 1) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family (`n = 2m - 1`): `J (k + 1) (2k + 1)` halts for all `k`. -/
theorem halting_residue_class (k : ℕ) : highLevelNext (.J (k + 1) (2 * k + 1)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

end M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

namespace M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

open BusyBeaver.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

/-- Live hazard witness for `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`: `C 1 8` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.C 1 8) = none := by
  simp [highLevelNext]

/-- Even-`b` halting family (`b = 2a + 8`): `C (a + 1) (2a + 8)` halts for all `a`. -/
theorem halting_residue_class (a : ℕ) : highLevelNext (.C (a + 1) (2 * a + 8)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Second even-`b` halting family (`b = 2a + 10`): `C (a + 1) (2a + 10)` halts for all `a`. -/
theorem halting_residue_class' (a : ℕ) : highLevelNext (.C (a + 1) (2 * a + 10)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Odd-`b` halting family (`a = j + 3`): `C (j + 3) (2j + 1)` halts for all `j`. -/
theorem halting_residue_class_odd (j : ℕ) : highLevelNext (.C (j + 3) (2 * j + 1)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Second odd-`b` halting family (`a = j + 4`): `C (j + 4) (2j + 1)` halts for all `j`. -/
theorem halting_residue_class_odd' (j : ℕ) : highLevelNext (.C (j + 4) (2 * j + 1)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

end M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

namespace M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

open BusyBeaver.M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

/-- Live hazard witness for `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`: `C 0 0 false` halts in
one high-level step. -/
theorem halting_state_witness : highLevelNext (.C 0 0 false) = none := by
  simp [highLevelNext]

/-- Diagonal halting family (`b = a`): `C a a p` halts for all `a` and `p`. -/
theorem halting_residue_class (a : ℕ) (p : Bool) : highLevelNext (.C a a p) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Superdiagonal halting family (`b = a + 1`): `C a (a + 1) p` halts for all `a` and `p`. -/
theorem halting_residue_class' (a : ℕ) (p : Bool) : highLevelNext (.C a (a + 1) p) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

end M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

/-! ## Shielded Exponential Cascades -/

namespace M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

open BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

/-- Live hazard witness for `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`: `E false 1 1` halts in
one high-level step. -/
theorem halting_state_witness : highLevelNext (.E false 1 1) = none := by
  simp [highLevelNext]

/-- Odd-`c` halting family at `d = 1`: `E p (2j + 1) 1` halts for all `p` and `j`. -/
theorem halting_residue_class (p : Bool) (j : ℕ) : highLevelNext (.E p (2 * j + 1) 1) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

end M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

namespace M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

open BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

/-- Live hazard witness for `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`: `A 4 0` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.A 4 0) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family: `A (2 * (c / 2) + 4) c` halts for all `c`. -/
theorem halting_residue_class (c : ℕ) : highLevelNext (.A (2 * (c / 2) + 4) c) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Exact characterization: `A b c` halts in one high-level step iff `b = 2 * (c / 2) + 4`. -/
theorem halting_residue_class_iff (b c : ℕ) :
    highLevelNext (.A b c) = none ↔ b = 2 * (c / 2) + 4 := by
  simp only [highLevelNext]
  split_ifs <;> simp <;> omega

end M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

namespace M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

open BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

/-- Live hazard witness for `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`: `A 4 0` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.A 4 0) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family: `A (2 * (c / 2) + 4) c` halts for all `c`. -/
theorem halting_residue_class (c : ℕ) : highLevelNext (.A (2 * (c / 2) + 4) c) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Exact characterization: `A b c` halts in one high-level step iff `b = 2 * (c / 2) + 4`. -/
theorem halting_residue_class_iff (b c : ℕ) :
    highLevelNext (.A b c) = none ↔ b = 2 * (c / 2) + 4 := by
  simp only [highLevelNext]
  split_ifs <;> simp <;> omega

end M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

namespace M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE

open BusyBeaver.M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE

/-- Live hazard witness on `C0` for `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`: `C0 0 1` halts in
one high-level step. -/
theorem halting_state_witness : highLevelNext (.C0 0 1) = none := by
  simp [highLevelNext]

/-- Live hazard witness on `C1`: `C1 0 0 0` halts in one high-level step. -/
theorem halting_state_witness_C1 : highLevelNext (.C1 0 0 0) = none := by
  simp [highLevelNext]

private theorem evalM_halt (k u : ℕ) : evalM k u (2 * k + 4) 0 false = none := by
  induction k generalizing u with
  | zero => simp [evalM, evalS, evalR]
  | succ k ih =>
    rw [evalM]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have hb1 : ¬ (2 * (k + 1) + 4 = 1) := by omega
    have hsub : 2 * (k + 1) + 4 - 2 = 2 * k + 4 := by omega
    simp only [hb1, ↓reduceIte, hsub]
    exact ih (u + 2)

/-- Linear equality halting family on `C0`: `C0 (k + 1) (2k + 3)` halts for all `k`. -/
theorem halting_residue_class (k : ℕ) : highLevelNext (.C0 (k + 1) (2 * k + 3)) = none := by
  rcases k with _ | k
  · simp [highLevelNext, evalCPos, evalS, evalR]
  · simp only [highLevelNext, evalCPos]
    have ha0 : ¬ (k + 1 + 1 = 0) := by omega
    have ha1 : ¬ (k + 1 + 1 = 1) := by omega
    have hb0 : ¬ (2 * (k + 1) + 3 = 0) := by omega
    have h1 : k + 1 + 1 - 2 = k := by omega
    have h2 : 2 * (k + 1) + 3 - 1 = 2 * k + 4 := by omega
    simp only [ha0, ha1, hb0, ↓reduceIte, h1, h2]
    exact evalM_halt k 0

end M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE

namespace M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

open BusyBeaver.M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

/-- Live hazard witness for `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`: `C 0 2` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.C 0 2) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family (`c = b + 2`): `C b (b + 2)` halts for all `b`. -/
theorem halting_residue_class (b : ℕ) : highLevelNext (.C b (b + 2)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

end M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

namespace M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

open BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

/-- Live hazard witness for `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`: `S false 2 1` halts in
one high-level step. -/
theorem halting_state_witness : highLevelNext (.S false 2 1) = none := by
  simp [highLevelNext]

/-- Linear halting family (`hat = false`): `S false (3q + 2) (q + 1)` halts for all `q`. -/
theorem halting_residue_class (q : ℕ) : highLevelNext (.S false (3 * q + 2) (q + 1)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Linear halting family (`hat = true`): `S true (3q + 2) (q + 2)` halts for all `q`. -/
theorem halting_residue_class_hat (q : ℕ) :
    highLevelNext (.S true (3 * q + 2) (q + 2)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

end M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

namespace M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB

open BusyBeaver.M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB

/-- Live hazard witness for `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`: `P 0 2` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.P 0 2) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family (`c = b + 2`): `P b (b + 2)` halts for all `b`. -/
theorem halting_residue_class (b : ℕ) : highLevelNext (.P b (b + 2)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Exact characterization: `P b c` halts in one high-level step iff `c = b + 2`. -/
theorem halting_residue_class_iff (b c : ℕ) : highLevelNext (.P b c) = none ↔ c = b + 2 := by
  simp only [highLevelNext]
  split_ifs <;> simp <;> omega

end M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB

namespace M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Live hazard witness for `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`: `D 1 0` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.D 1 0) = none := by
  simp [highLevelNext]

/-- Odd-`a` halting cone (`a % 2 = 1` and `a < d + 3`): `D a d` halts in one high-level step. -/
theorem halting_residue_class (a d : ℕ) (ha : a % 2 = 1) (had : a < d + 3) :
    highLevelNext (.D a d) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Diagonal odd halting family: `D (2k + 1) (2k + 1)` halts for all `k`. -/
theorem halting_residue_class_diag (k : ℕ) : highLevelNext (.D (2 * k + 1) (2 * k + 1)) = none :=
  halting_residue_class _ _ (by omega) (by omega)

end M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

namespace M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

/-- Live hazard witness for `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC`: `D 1 0` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.D 1 0) = none := by
  simp [highLevelNext]

/-- Odd-`a` halting cone (`a % 2 = 1` and `a < d + 3`): `D a d` halts in one high-level step. -/
theorem halting_residue_class (a d : ℕ) (ha : a % 2 = 1) (had : a < d + 3) :
    highLevelNext (.D a d) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Diagonal odd halting family: `D (2k + 1) (2k + 1)` halts for all `k`. -/
theorem halting_residue_class_diag (k : ℕ) : highLevelNext (.D (2 * k + 1) (2 * k + 1)) = none :=
  halting_residue_class _ _ (by omega) (by omega)

end M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

namespace M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

open BusyBeaver.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

/-- Live hazard witness for `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`: `E 0 2` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.E 0 2) = none := by
  simp [highLevelNext]

/-- Exact-equality halting family (`d = 2b + 2`): `E b (2b + 2)` halts for all `b`. -/
theorem halting_residue_class (b : ℕ) : highLevelNext (.E b (2 * b + 2)) = none := by
  simp only [highLevelNext]
  split_ifs <;> first | rfl | omega

/-- Exact characterization: `E b d` halts in one high-level step iff `d = 2b + 2`. -/
theorem halting_residue_class_iff (b d : ℕ) : highLevelNext (.E b d) = none ↔ d = 2 * b + 2 := by
  simp only [highLevelNext]
  split_ifs <;> simp <;> omega

end M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

namespace M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD

open BusyBeaver.M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD

/-- Live hazard witness for `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`: `E 0 0 6` halts in one
accelerated step. -/
theorem halting_state_witness : next (.E 0 0 6) = none := by
  simp [next]

/-- One-step halting family (`b = 0, c = 6`): `E a 0 6` halts for all `a`. -/
theorem halting_residue_class (a : ℕ) : next (.E a 0 6) = none := by
  simp [next]

/-- Multi-step halting cone (`c = 2b + 6`): `E a b (2b + 6)` halts in `b + 1` steps for all `a, b`.
-/
theorem halting_residue_class_multi_step (a b : ℕ) : CollatzHalts next (.E a b (2 * b + 6)) := by
  induction b generalizing a with
  | zero => exact ⟨1, by simp [next]⟩
  | succ b ih =>
    obtain ⟨n, hn⟩ := ih (a + 2)
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply]
    have h : next (.E a (b + 1) (2 * (b + 1) + 6)) = some (.E (a + 2) b (2 * b + 6)) := by
      rw [show 2 * (b + 1) + 6 = (2 * b + 6) + 2 by omega]
      cases b <;> rfl
    simpa [h] using hn

end M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD

namespace M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

open BusyBeaver.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

/-- Live hazard witness for `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`: `C 0 0` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.C 0 0) = none := by
  simp [highLevelNext]

/-- One-step halting family (`b = 0`): `C a 0` halts for all `a`. -/
theorem halting_residue_class (a : ℕ) : highLevelNext (.C a 0) = none := by
  simp [highLevelNext]

/-- Pre-halting family (`b = a / 2 + 4`): `C a (a / 2 + 4)` steps directly into the `C _ 0` halting
family. -/
theorem halting_residue_class_two_step (a : ℕ) :
    highLevelNext (.C a (a / 2 + 4)) = some (.C (6 * (a / 2 + 2) + 3 * (a % 2) + 5) 0) := by
  rw [show a / 2 + 4 = (a / 2 + 2) + 2 by omega]
  simp only [highLevelNext]
  split_ifs <;> first | omega | (congr 2; omega)

end M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

namespace M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

/-- Live hazard witness for `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`: `C 0 1` halts in one
high-level step. -/
theorem halting_state_witness : highLevelNext (.C 0 1) = none := by
  simp [highLevelNext]

/-- One-step halting family (`b = 1`): `C a 1` halts for all `a`. -/
theorem halting_residue_class (a : ℕ) : highLevelNext (.C a 1) = none := by
  simp [highLevelNext]

/-- Pre-halting family (`b = 2a + 3`): `C a (2a + 3)` steps directly to `C (2a + 2) 1`, which halts
on the next high-level step. -/
theorem halting_residue_class_two_step (a : ℕ) :
    highLevelNext (.C a (2 * a + 3)) = some (.C (2 * a + 2) 1) := by
  rw [show 2 * a + 3 = (2 * a + 1) + 2 by omega]
  simp only [highLevelNext]
  split_ifs <;> first | omega | (congr 2; omega)

end M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

/-! ## True Stacked Cryptids and Odometer Calibration (`BusyBeaver/BB6/Accelerations/`) -/

namespace M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA

open BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA

/-- Live hazard witness for `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` (Problem S2): `D 0 0 []`
halts in one high-level epoch. -/
theorem halting_state_witness : highLevelNext (.D 0 0 []) = none := by
  rw [highLevelNext, runE]
  simp

private theorem runE_pow2_sub2 (m r₀ : ℕ) (R' : List ℕ) :
    runE (2 ^ (m + 1) - 2) [] r₀ R' = none := by
  induction m generalizing r₀ R' with
  | zero =>
    rw [runE]
    simp
  | succ m ih =>
    rw [runE]
    have hpow : 2 ^ (m + 1 + 1) ≥ 4 := by
      have : 2 ^ m ≥ 1 := Nat.one_le_pow m 2 (by decide)
      omega
    have ha0 : ¬ (2 ^ (m + 1 + 1) - 2 = 0) := by omega
    have ha1 : ¬ (2 ^ (m + 1 + 1) - 2 = 1) := by omega
    have hmod : ¬ ((2 ^ (m + 1 + 1) - 2 - 2) % 2 = 1) := by omega
    have hdiv : (2 ^ (m + 1 + 1) - 2 - 2) / 2 = 2 ^ (m + 1) - 2 := by omega
    simp only [↓reduceIte, ha0, ha1, hmod, hdiv]
    exact ih (2 ^ (m + 1) - 2 + 1) (r₀ :: R')

/-- Power-of-two bottom funnel (`x + 2 = 2^{m+1}`): `D 0 (2^{m+1} - 2) []` halts in one high-level
epoch for all `m`. -/
theorem halting_residue_class (m : ℕ) :
    highLevelNext (.D 0 (2 ^ (m + 1) - 2) []) = none := by
  simp only [highLevelNext, Nat.zero_mod, Nat.zero_div, Nat.add_zero]
  exact runE_pow2_sub2 m 0 []

end M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA

namespace M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA

open BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA

/-- Live hazard witness for `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` (Problem S3):
`F 0 0 [] 1 []` halts in one high-level step. -/
theorem halting_state_witness : highLevelNext (.F 0 0 [] 1 []) = none := by
  simp [highLevelNext, exitC]

/-- Depth-two gate halting family: `F 0 0 L 1 []` halts in one high-level step for every left stack
`L`. -/
theorem halting_residue_class (L : List ℕ) : highLevelNext (.F 0 0 L 1 []) = none := by
  cases L <;> simp [highLevelNext, exitC]

end M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA

namespace M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

/-- Live hazard witness for `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` (Problem S4): `C 0 []`
halts in one high-level epoch. -/
theorem halting_state_witness : highLevelNext (.C 0 []) = none := by
  rw [highLevelNext, stepEpoch]
  simp

private theorem stepEpoch_pow2_sub1 (m : ℕ) (R : List ℕ) :
    stepEpoch (2 ^ m - 1) [] R = none := by
  induction m generalizing R with
  | zero =>
    rw [stepEpoch]
    simp
  | succ m ih =>
    rw [stepEpoch]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hpow : 2 ^ m ≥ 2 := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hm)
        have : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by decide)
        rw [Nat.pow_add]
        omega
      have hle : ¬ (2 ^ (m + 1) - 1 ≤ 1) := by
        rw [Nat.pow_succ]
        omega
      have hmod : ¬ ((2 ^ (m + 1) - 1) % 2 = 0) := by
        rw [Nat.pow_succ]
        omega
      have hdiv : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by
        rw [Nat.pow_succ]
        omega
      simp only [↓reduceIte, hle, hmod, hdiv]
      exact ih (0 :: Stack.bumpHeadBy (2 ^ m - 1) R)

/-- Power-of-two bottom-exposure halting family: `C (2^m - 1) []` halts in one high-level epoch for
all `m`. -/
theorem halting_residue_class (m : ℕ) : highLevelNext (.C (2 ^ m - 1) []) = none :=
  stepEpoch_pow2_sub1 m [0]

end M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

namespace M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB

open BusyBeaver.M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB

/-- Live hazard witness for `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB` (Problem S4): `C 0 []`
halts in one high-level epoch. -/
theorem halting_state_witness : highLevelNext (.C 0 []) = none := by
  rw [highLevelNext, runEpoch]
  simp

private theorem runEpoch_pow2_sub2 (m : ℕ) (R : List ℕ) :
    runEpoch (2 ^ (m + 1) - 2) [] R = none := by
  induction m generalizing R with
  | zero =>
    rw [runEpoch]
    simp
  | succ m ih =>
    rw [runEpoch]
    have hpow : 2 ^ (m + 1) ≥ 2 := by
      have : 2 ^ m ≥ 1 := Nat.one_le_pow m 2 (by decide)
      rw [Nat.pow_succ]
      omega
    have ha0 : ¬ (2 ^ (m + 1 + 1) - 2 = 0) := by
      rw [Nat.pow_succ]
      omega
    have hmod : ¬ ((2 ^ (m + 1 + 1) - 2 - 1) % 2 = 0) := by
      rw [Nat.pow_succ]
      omega
    have hdiv : (2 ^ (m + 1 + 1) - 2 - 1) / 2 = 2 ^ (m + 1) - 2 := by
      rw [Nat.pow_succ]
      omega
    simp only [↓reduceIte, ha0, hmod, hdiv]
    exact ih (0 :: (R.headD 0 + (2 ^ (m + 1) - 2)) :: R.tail)

/-- Power-of-two bottom-exposure halting family: `C (2^{m+1} - 2) []` halts in one high-level epoch
for all `m`. -/
theorem halting_residue_class (m : ℕ) : highLevelNext (.C (2 ^ (m + 1) - 2) []) = none :=
  runEpoch_pow2_sub2 m []

end M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB

namespace M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA

open BusyBeaver.M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA

/-- Live hazard witness for `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA` (Problem S5):
`CR 1 0 [] 1 []` halts in one accelerated step. -/
theorem halting_state_witness : next (.CR 1 0 [] 1 []) = none := by
  simp [next]

/-- Halting family (`a = 1, r ≥ 1`): `CR 1 b L (d + 1) R` halts in one step for all `b, L, d, R`.
-/
theorem halting_residue_class (b : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    next (.CR 1 b L (d + 1) R) = none := by
  simp [next]

/-- Pre-halting family (`r = 1`): `CR (a + 2) b L 1 R` steps directly into the `CR 1 ...` halting
family whenever `bump1 R` has positive head. -/
theorem halting_residue_class_two_step (a b : ℕ) (L R : List ℕ) :
    next (.CR (a + 2) b L 1 R) = some (.CR 1 (a + 1) (b :: L) (bump1 R).1 (bump1 R).2) := by
  simp [next]

end M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA

namespace M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD

open BusyBeaver.M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD

/-- Live hazard witness for the base-4 odometer `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`:
`EL 0 [] 0 []` halts in one high-level step. -/
theorem halting_state_witness : highLevelNext (.EL 0 [] 0 []) = none := by
  simp [highLevelNext]

/-- Residue-`0 mod 4` halting family at empty left stack: `EL (4k) [] d R` halts for all `k, d, R`.
-/
theorem halting_residue_class (k d : ℕ) (R : List ℕ) :
    highLevelNext (.EL (4 * k) [] d R) = none := by
  simp [highLevelNext]

end M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD

end BusyBeaver.HardnessEvidence
