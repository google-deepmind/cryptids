/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`.

## Collatz-like Acceleration Rules

The proofs are carried out on `mirrorMachine`, the left-right mirror image of the machine with
control states relabelled by `π` (`A ↦ B`, `B ↦ C`, `C ↦ F`, `D ↦ D`, `E ↦ E`, `F ↦ A`), whose
canonical configuration family is `F(b, k, c) = 0^∞ 1^b (10)^k {{F}}> 00 1^c 0^∞`. The primary
canonical configuration family of the machine itself is the mirror image
`A(b, k, c) = 0^∞ 1^c 0 {{A}}> 0 (10)^k 1^b 0^∞`,
obtained by mirroring and permuting the control states of `F(b, k, c)`. Together with the
intermediate families `Odd(p, k, n, m, c)` and `ETail(k, m, c)` for the `b = 2` branch, starting
from the blank tape the machine reaches `A(4, 0, 3)`. The accelerated rules on `A` are:

```text
A(b, k + 1, 0)     -> A(b, k, 1)
A(0, 0, 0)         -> A(4, 0, 3)
A(1, 0, 0)         -> A(6, 0, 3)
A(2, 0, 0)         -> A(3, 0, 3)
A(3, 0, 0)         -> A(6, 0, 3)
A(4, 0, 0)         -> Halt
A(b + 5, 0, 0)     -> A(b + 1, 0, 5)

A(0, k, 1)         -> A(2k + 6, 0, 3)
A(1, k, 1)         -> A(2k + 8, 0, 3)
A(2, 0, c + 1)     -> A(5, 0, c)
A(2, k + 1, c + 1) -> Odd(2, 0, 0, k, c)
A(3, k, 1)         -> A(2k + 8, 0, 3)
A(4, k, 1)         -> Halt
A(b + 5, k, 1)     -> A(b + 1, 0, 2k + 7)

A(0, k, c + 2)     -> A(1, k + 1, c)
A(1, k, c + 2)     -> A(1, k + 2, c)
A(b + 3, k, c + 2) -> A(b + 1, k + 2, c)
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- The left-right mirror image of `target`, with control states relabelled by `π`, so that
`step target (mirrorCfg c) = (step mirrorMachine c).map mirrorCfg` (`step_mirror`); all sweeps
are analysed on this machine. -/
private def mirrorMachine : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

/-! ## Shift Lemmas -/

private theorem shift_E_ones (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1] : List (Fin 2)) ^ k +> r)) [mirrorMachine]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{E}}> ([1] +> (([1] : List (Fin 2)) ^ k +> r)))
        [mirrorMachine]⊢*
        ((l <+ [1]) {{E}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      bb_steps
    have h2 := ih (l <+ [1]) r
    rw [ListBlank.append_pow_succ' ([1] : List (Fin 2)) k l] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_CB_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [mirrorMachine]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, <- ListBlank.append_append]
    have h1 : (((l <+ ([0, 1] : List (Fin 2)) ^ k) <+ [0, 1]) {{C}}> ([1] +> r))
        [mirrorMachine]⊢*
        ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ' ([1, 1] : List (Fin 2)) k r] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_D_right_100 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) [mirrorMachine]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{D}}> ([1, 0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
        [mirrorMachine]⊢*
        ((l <+ [0, 1]) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
      bb_steps
    have h2 := ih (l <+ [0, 1]) r
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k l] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_FA_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> r)) [mirrorMachine]⊢*
    (l {{F}}> ([0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, <- ListBlank.append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{F}}> ([0] +> r))
        [mirrorMachine]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> ([0, 1] +> r))) := by
      bb_steps
    have h2 := ih l (([0, 1] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k r] at h2
    exact ReachesStar.trans h1 h2

/-! ## Canonical Configurations of `mirrorMachine` -/

private def cfg_E (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ a)
          {{E}}> default

def F_R (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
          {{F}}>
    ([0, 0] +> r)

def cfg_F (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
          {{F}}>
    ([0, 0] +> (([1] : List (Fin 2)) ^ c +> default))

private theorem cfg_F_eq_F_R (b k c : Nat) :
    cfg_F b k c = F_R b k (([1] : List (Fin 2)) ^ c +> default) := rfl

/-- Tape pattern of `mirrorMachine` describing the configurations `cfg_F b k c`. -/
private def mirrorPat : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 0] 1 (.rep [1] 0 .default)
    head  := some F
    right := .sym 0 (.sym 0 (.rep [1] 2 .default)) }

/-- Pattern set of `mirrorMachine`; its closure is transported to `ps` on `target` below. -/
private def mirrorPs : TapePatternSet (Fin 2) (Fin 6) :=
  [(mirrorPat, .true)]

private theorem eval_mirrorPat (vars : Nat → Nat) :
    evalTapePattern mirrorPat vars = cfg_F (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_F (b k c : Nat) : IsInPatternSet mirrorPs (cfg_F b k c) := by
  refine ⟨(mirrorPat, .true), List.Mem.head _, fun i => match i with | 0 => b | 1 => k | _ => c,
    ?_, trivial⟩
  exact (eval_mirrorPat (fun i => match i with | 0 => b | 1 => k | _ => c)).symm

/-! ## Accelerated Transition Rules -/

private theorem step_E_b0 (a : Nat) :
    (cfg_E a 0) [mirrorMachine]⊢⁺ (cfg_E 0 (2 * a + 4)) := by
  unfold cfg_E
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) {{E}}> default)
      [mirrorMachine]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) <+ [0]) {{C}}> ([1] +> ([1]
              +> default))) := by
    bb_steps
  rw [ListBlank.append_cons, ListBlank.append_nil, <- default_append_01_pow a] at h1
  have h2 := shift_CB_left a default ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have h3 : ((default : ListBlank (Fin 2)) {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1]
          +> default))))
      [mirrorMachine]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          3) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 (2 * a + 1)] at h4
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4

private theorem step_E_b1 (a : Nat) :
    (cfg_E a 1) [mirrorMachine]⊢⁺ (cfg_E 0 (2 * a + 6)) := by
  unfold cfg_E
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin
          2)) ^ a) {{E}}> default)
      [mirrorMachine]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin 2)) ^
              a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- append_01_pow_zero a ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)] at h1
  have h2 := shift_CB_left a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+
          [0]) ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [mirrorMachine]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          5) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 (2 * a + 1)] at h4
  have ha : 5 + (2 * a + 1) = 2 * a + 6 := by omega
  rw [ha] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4

private theorem step_E_b2_to_D_halt (a : Nat) :
    (cfg_E a 2) [mirrorMachine]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ (2 * a + 4) +>
            default))) := by
  unfold cfg_E
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin
          2)) ^ a) {{E}}> default)
      [mirrorMachine]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin 2)) ^
              a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- append_01_pow_zero a ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2)] at h1
  have h2 := shift_CB_left a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+
          [0]) ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [mirrorMachine]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
                (Fin 2)) ^ 1 +> default))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default,
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (2 * a + 1) default] at h3
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem step_E_b3_to_F (a b : Nat) :
    (cfg_E a (b + 3)) [mirrorMachine]⊢⁺ (cfg_F (b + 1) 0 (2 * a + 3)) := by
  unfold cfg_E cfg_F
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List
          (Fin 2)) ^ a) {{E}}> default)
      [mirrorMachine]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List (Fin
              2)) ^ a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- append_01_pow_zero a ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3))]
      at h1
  have h2 := shift_CB_left a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
          3)) <+ [0]) ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (b + 1) 2] at h1 h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
          (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [mirrorMachine]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) {{F}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
                (Fin 2)) ^ 1 +> default))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default,
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * a + 1) default] at h3
  have ha : 2 + (2 * a + 1) = 2 * a + 3 := by omega
  rw [ha] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem step_F_b2_k0 (c : Nat) :
    (cfg_F 2 0 (c + 1)) [mirrorMachine]⊢⁺ (cfg_F 5 0 c) := by
  unfold cfg_F
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem isNone_step_D_00 (l r : ListBlank (Fin 2)) :
    (step mirrorMachine (l {{D}}> ([0, 0] +> r))).isNone = true := by
  bb_halt

private theorem closes_E (a b : Nat) : StepsToClosed mirrorMachine mirrorPs (cfg_E a b) := by
  rcases b with _ | _ | _ | b'
  · have h1 := step_E_b0 a
    have hb : 2 * a + 4 = (2 * a + 1) + 3 := by omega
    rw [hb] at h1
    exact StepsToClosed.of_isInPatternSet (ReachesPlus.trans h1 (step_E_b3_to_F 0 (2 * a + 1)))
      (in_ps_F (2 * a + 2) 0 3)
  · have h1 := step_E_b1 a
    have hb : 2 * a + 6 = (2 * a + 3) + 3 := by omega
    rw [hb] at h1
    exact StepsToClosed.of_isInPatternSet (ReachesPlus.trans h1 (step_E_b3_to_F 0 (2 * a + 3)))
      (in_ps_F (2 * a + 4) 0 3)
  · exact StepsToClosed.of_halting (step_E_b2_to_D_halt a) (isNone_step_D_00 _ _)
  · exact StepsToClosed.of_isInPatternSet (step_E_b3_to_F a b') (in_ps_F (b' + 1) 0 (2 * a + 3))

private def D100 (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k) <+
          [0]) {{D}}>
    ([1, 0, 0] +> r)

private def C_bounce (b : Nat) (s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) {{C}}> ([1] +> s)

private theorem step_F0_sweep_right (k : Nat) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
    [mirrorMachine]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  have h1 : ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
      [mirrorMachine]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    bb_steps
  have h2 := shift_D_right_100 k default r
  exact ReachesPlus.trans_star h1 h2

private theorem F_R_b0_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 0 k r) [mirrorMachine]⊢⁺ (D100 0 k r) := by
  unfold F_R D100
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_FA_left k default ([0] +> r)
  rw [append_01_pow_zero k r] at h1
  have h2 := step_F0_sweep_right k r
  rw [default_append_01_pow k] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem F_R_b1_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 1 k r) [mirrorMachine]⊢⁺ (D100 0 (k + 1) r) := by
  unfold F_R D100
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_FA_left k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) ([0]
          +> r)
  rw [append_01_pow_zero k r] at h1
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [mirrorMachine]⊢⁺
      ((default : ListBlank (Fin 2)) {{F}}>
        ([0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) k r] at h2
  have h3 := step_F0_sweep_right (k + 1) r
  rw [default_append_01_pow (k + 1)] at h3
  exact ReachesPlus.trans (ReachesStar.trans_plus h1 h2) h3

private theorem F_R_b3_to_D100 (b k : Nat) (r : ListBlank (Fin 2)) :
    (F_R (b + 3) k r) [mirrorMachine]⊢⁺ (D100 (b + 1) k r) := by
  unfold F_R D100
  have h1 := shift_FA_left k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3))
          ([0] +> r)
  rw [append_01_pow_zero k r] at h1
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (b + 1) 2] at h1
  have h2 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List (Fin
          2)) ^ 2) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [mirrorMachine]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) {{D}}>
        ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h3 := shift_D_right_100 k
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) r
  rw [append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1))] at h3
  exact ReachesPlus.trans_star (ReachesStar.trans_plus h1 h2) h3

private theorem D100_0_11 (k : Nat) (r : ListBlank (Fin 2)) :
    (D100 0 k ([1, 1] +> r)) [mirrorMachine]⊢⁺ (F_R 1 (k + 1) r) := by
  unfold D100 F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_cons, ListBlank.append_nil, <- default_append_01_pow k]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [mirrorMachine]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2))
              ^ 1) <+ [1]) {{F}}>
        ([0, 0] +> r)) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) k 1,
    <- append_10_pow_one (k + 1) default] at h1
  exact h1

private theorem D100_succ_11 (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 (b + 1) k ([1, 1] +> r)) [mirrorMachine]⊢⁺ (F_R (b + 1) (k + 2) r) := by
  unfold D100 F_R
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List
          (Fin 2)) ^ k) <+ [0]) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [mirrorMachine]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List (Fin
              2)) ^ k) <+
        ([1, 0] : List (Fin 2)) ^ 2) {{F}}>
        ([0, 0] +> r)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1))
    ([1, 0] : List (Fin 2)) k 2] at h1
  exact h1

private theorem D100_nil_to_C_bounce (b k : Nat) :
    (D100 b k default) [mirrorMachine]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 3) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> default))
      [mirrorMachine]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0])
    ([0, 1] : List (Fin 2)) k 1] at h1
  have h2 := shift_CB_left (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 (k + 1),
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 1)) 1 default] at h2
  have hk : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hk] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem D100_one_to_C_bounce (b k : Nat) :
    (D100 b k ([1] +> default)) [mirrorMachine]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 5) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1] +> default)))
      [mirrorMachine]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 2) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0])
    ([0, 1] : List (Fin 2)) k 2] at h1
  have h2 := shift_CB_left (k + 2) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 (k + 2),
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 2)) 1 default] at h2
  have hk : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rw [hk] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem D100_01_to_C_bounce (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 b k ([0, 1] +> r)) [mirrorMachine]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 4) +> r)) := by
  unfold D100 C_bounce
  rw [<- append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([0, 1] +> r)))
      [mirrorMachine]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 2 +> r))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0])
    ([0, 1] : List (Fin 2)) k 1] at h1
  have h2 := shift_CB_left (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 2 +> r)
  rw [pair_pow_eq_singleton_pow_two_mul 1 (k + 1),
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 1)) 2 r] at h2
  have hk : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  rw [hk] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem C_bounce_0 (s : ListBlank (Fin 2)) :
    (C_bounce 0 s) [mirrorMachine]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}> s) := by
  unfold C_bounce
  simp only [list_pow_zero, ListBlank.append_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_1 (s : ListBlank (Fin 2)) :
    (C_bounce 1 s) [mirrorMachine]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}> s) := by
  unfold C_bounce
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_2 (s : ListBlank (Fin 2)) :
    (C_bounce 2 s) [mirrorMachine]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> s))) := by
  unfold C_bounce
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_3 (b : Nat) (s : ListBlank (Fin 2)) :
    (C_bounce (b + 3) s) [mirrorMachine]⊢⁺
    (F_R (b + 1) 0 (([1] : List (Fin 2)) ^ 2 +> s)) := by
  unfold C_bounce F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (b + 1) 2]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_F_ksucc_c0 (b k : Nat) :
    (cfg_F b (k + 1) 0) [mirrorMachine]⊢⁺ (cfg_F b k 1) := by
  unfold cfg_F
  rw [ListBlank.append_pow_add_rev ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)
    ([1, 0] : List (Fin 2)) k 1]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
    ListBlank.append_nil]
  bb_steps

private theorem step_F_b2_k0_c0 :
    (cfg_F 2 0 0) [mirrorMachine]⊢⁺ (cfg_F 3 0 3) := by
  unfold cfg_F
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_0_ones (n : Nat) :
    (C_bounce 0 (([1] : List (Fin 2)) ^ n +> default)) [mirrorMachine]⊢⁺
    (cfg_F (n + 1) 0 3) := by
  have h1 := C_bounce_0 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 n] at h2
  have hn : 3 + n = n + 3 := by omega
  rw [hn] at h2
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (n + 3)) {{E}}> default) =
      cfg_E 0 (n + 3) := rfl
  rw [h_eq] at h2
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) (step_E_b3_to_F 0 n)

private theorem C_bounce_1_ones (n : Nat) :
    (C_bounce 1 (([1] : List (Fin 2)) ^ n +> default)) [mirrorMachine]⊢⁺
    (cfg_F (n + 3) 0 3) := by
  have h1 := C_bounce_1 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 n] at h2
  have hn : 5 + n = (n + 2) + 3 := by omega
  rw [hn] at h2
  have h_eq :
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ ((n + 2) + 3)) {{E}}> default) =
      cfg_E 0 ((n + 2) + 3) := rfl
  rw [h_eq] at h2
  have h3 := step_E_b3_to_F 0 (n + 2)
  have hn2 : (n + 2) + 1 = n + 3 := by omega
  rw [hn2] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem C_bounce_2_ones_halt (n : Nat) :
    ∃ cfg', ((C_bounce 2 (([1] : List (Fin 2)) ^ n +> default)) [mirrorMachine]⊢⁺ cfg') ∧
            (step mirrorMachine cfg').isNone :=
  ⟨_, C_bounce_2 (([1] : List (Fin 2)) ^ n +> default), isNone_step_D_00 _ _⟩

private theorem C_bounce_3_ones (b n : Nat) :
    (C_bounce (b + 3) (([1] : List (Fin 2)) ^ n +> default)) [mirrorMachine]⊢⁺
    (cfg_F (b + 1) 0 (n + 2)) := by
  have h1 := C_bounce_3 b (([1] : List (Fin 2)) ^ n +> default)
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 n default, <- cfg_F_eq_F_R] at h1
  have hn : 2 + n = n + 2 := by omega
  rwa [hn] at h1

private theorem rule_F_ksucc_c0 (b k : Nat) :
    (cfg_F b (k + 1) 0) [mirrorMachine]⊢⁺ (cfg_F b k 1) :=
  step_F_ksucc_c0 b k

private theorem rule_F_b0_k0_c0 :
    (cfg_F 0 0 0) [mirrorMachine]⊢⁺ (cfg_F 4 0 3) :=
  ReachesPlus.trans (ReachesPlus.trans (F_R_b0_to_D100 0 default) (D100_nil_to_C_bounce 0 0))
    (C_bounce_0_ones 3)

private theorem rule_F_b1_k0_c0 :
    (cfg_F 1 0 0) [mirrorMachine]⊢⁺ (cfg_F 6 0 3) :=
  ReachesPlus.trans (ReachesPlus.trans (F_R_b1_to_D100 0 default) (D100_nil_to_C_bounce 0 1))
    (C_bounce_0_ones 5)

private theorem rule_F_b2_k0_c0 :
    (cfg_F 2 0 0) [mirrorMachine]⊢⁺ (cfg_F 3 0 3) :=
  step_F_b2_k0_c0

private theorem rule_F_b3_k0_c0 :
    (cfg_F 3 0 0) [mirrorMachine]⊢⁺ (cfg_F 6 0 3) :=
  ReachesPlus.trans (ReachesPlus.trans (F_R_b3_to_D100 0 0 default) (D100_nil_to_C_bounce 1 0))
    (C_bounce_1_ones 3)

private theorem rule_F_b4_k0_c0_halt :
    ∃ cfg', ((cfg_F 4 0 0) [mirrorMachine]⊢⁺ cfg') ∧ (step mirrorMachine cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt 3
  exact ⟨cfg', ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 1 0 default) (D100_nil_to_C_bounce 2 0)) h_step, h_halt⟩

private theorem rule_F_b5_k0_c0 (b : Nat) :
    (cfg_F (b + 5) 0 0) [mirrorMachine]⊢⁺ (cfg_F (b + 1) 0 5) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  exact ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 (b + 2) 0 default) (D100_nil_to_C_bounce (b + 3) 0))
    (C_bounce_3_ones b 3)

private theorem rule_F_b0_c1 (k : Nat) :
    (cfg_F 0 k 1) [mirrorMachine]⊢⁺ (cfg_F (2 * k + 6) 0 3) :=
  ReachesPlus.trans
    (ReachesPlus.trans (F_R_b0_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 k))
    (C_bounce_0_ones (2 * k + 5))

private theorem rule_F_b1_c1 (k : Nat) :
    (cfg_F 1 k 1) [mirrorMachine]⊢⁺ (cfg_F (2 * k + 8) 0 3) := by
  have h := ReachesPlus.trans
    (ReachesPlus.trans (F_R_b1_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 (k + 1)))
    (C_bounce_0_ones (2 * (k + 1) + 5))
  have hk : (2 * (k + 1) + 5) + 1 = 2 * k + 8 := by omega
  rwa [hk] at h

private theorem rule_F_b2_k0_c1 (c : Nat) :
    (cfg_F 2 0 (c + 1)) [mirrorMachine]⊢⁺ (cfg_F 5 0 c) :=
  step_F_b2_k0 c

private theorem rule_F_b3_c1 (k : Nat) :
    (cfg_F 3 k 1) [mirrorMachine]⊢⁺ (cfg_F (2 * k + 8) 0 3) := by
  have h := ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 0 k ([1] +> default)) (D100_one_to_C_bounce 1 k))
    (C_bounce_1_ones (2 * k + 5))
  have hk : (2 * k + 5) + 3 = 2 * k + 8 := by omega
  rwa [hk] at h

private theorem rule_F_b4_c1_halt (k : Nat) :
    ∃ cfg', ((cfg_F 4 k 1) [mirrorMachine]⊢⁺ cfg') ∧ (step mirrorMachine cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt (2 * k + 5)
  exact ⟨cfg', ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 1 k ([1] +> default)) (D100_one_to_C_bounce 2 k)) h_step,
    h_halt⟩

private theorem rule_F_b5_c1 (b k : Nat) :
    (cfg_F (b + 5) k 1) [mirrorMachine]⊢⁺ (cfg_F (b + 1) 0 (2 * k + 7)) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  have h := ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 (b + 2) k ([1] +> default)) (D100_one_to_C_bounce (b + 3) k))
    (C_bounce_3_ones b (2 * k + 5))
  have hk : (2 * k + 5) + 2 = 2 * k + 7 := by omega
  rwa [hk] at h

private theorem rule_F_b0_c2 (k c : Nat) :
    (cfg_F 0 k (c + 2)) [mirrorMachine]⊢⁺ (cfg_F 1 (k + 1) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b0_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 k (([1] : List (Fin 2)) ^ c +> default)
  exact ReachesPlus.trans h1 h2

private theorem rule_F_b1_c2 (k c : Nat) :
    (cfg_F 1 k (c + 2)) [mirrorMachine]⊢⁺ (cfg_F 1 (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ c +> default)
  exact ReachesPlus.trans h1 h2

private theorem rule_F_b3_c2 (b k c : Nat) :
    (cfg_F (b + 3) k (c + 2)) [mirrorMachine]⊢⁺ (cfg_F (b + 1) (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b3_to_D100 b k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_succ_11 b k (([1] : List (Fin 2)) ^ c +> default)
  exact ReachesPlus.trans h1 h2

/-! ## Closure on `mirrorMachine` -/

private theorem closes_F_c0 (b k : Nat) : StepsToClosed mirrorMachine mirrorPs (cfg_F b k 0) := by
  rcases k with _ | k'
  · rcases b with _ | _ | _ | _ | _ | b'
    · exact StepsToClosed.of_isInPatternSet rule_F_b0_k0_c0 (in_ps_F 4 0 3)
    · exact StepsToClosed.of_isInPatternSet rule_F_b1_k0_c0 (in_ps_F 6 0 3)
    · exact StepsToClosed.of_isInPatternSet rule_F_b2_k0_c0 (in_ps_F 3 0 3)
    · exact StepsToClosed.of_isInPatternSet rule_F_b3_k0_c0 (in_ps_F 6 0 3)
    · obtain ⟨cfg', h_step, h_halt⟩ := rule_F_b4_k0_c0_halt
      exact StepsToClosed.of_halting h_step h_halt
    · exact StepsToClosed.of_isInPatternSet (rule_F_b5_k0_c0 b') (in_ps_F (b' + 1) 0 5)
  · exact StepsToClosed.of_isInPatternSet (rule_F_ksucc_c0 b k') (in_ps_F b k' 1)

private theorem closes_F_b0 (k c : Nat) : StepsToClosed mirrorMachine mirrorPs (cfg_F 0 k c) := by
  rcases c with _ | _ | c'
  · exact closes_F_c0 0 k
  · exact StepsToClosed.of_isInPatternSet (rule_F_b0_c1 k) (in_ps_F (2 * k + 6) 0 3)
  · exact StepsToClosed.of_isInPatternSet (rule_F_b0_c2 k c') (in_ps_F 1 (k + 1) c')

private theorem closes_F_b1 (k c : Nat) : StepsToClosed mirrorMachine mirrorPs (cfg_F 1 k c) := by
  rcases c with _ | _ | c'
  · exact closes_F_c0 1 k
  · exact StepsToClosed.of_isInPatternSet (rule_F_b1_c1 k) (in_ps_F (2 * k + 8) 0 3)
  · exact StepsToClosed.of_isInPatternSet (rule_F_b1_c2 k c') (in_ps_F 1 (k + 2) c')

private theorem closes_F_b3 (b k c : Nat) :
    StepsToClosed mirrorMachine mirrorPs (cfg_F (b + 3) k c) := by
  rcases c with _ | _ | c'
  · exact closes_F_c0 (b + 3) k
  · rcases b with _ | _ | b'
    · exact StepsToClosed.of_isInPatternSet (rule_F_b3_c1 k) (in_ps_F (2 * k + 8) 0 3)
    · obtain ⟨cfg', h_step, h_halt⟩ := rule_F_b4_c1_halt k
      exact StepsToClosed.of_halting h_step h_halt
    · exact StepsToClosed.of_isInPatternSet (rule_F_b5_c1 b' k) (in_ps_F (b' + 1) 0 (2 * k + 7))
  · exact StepsToClosed.of_isInPatternSet (rule_F_b3_c2 b k c') (in_ps_F (b + 1) (k + 2) c')

private theorem step_F_R_b2_one (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 2 k ([1] +> r)) [mirrorMachine]⊢⁺
    (F_R 5 0 (([0, 1] : List (Fin 2)) ^ k +> r)) := by
  unfold F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_FA_left k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) ([0,
          1] +> r)
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{F}}>
      ([0] +> (([0, 1] : List (Fin 2)) ^ k +> ([0, 1] +> r))))
      [mirrorMachine]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{F}}>
        ([0, 0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k r,
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k r]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesStar.trans_plus h1 h2

private theorem step_E_01_to_F_R (b : Nat) (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) {{E}}> ([0, 1] +> r))
    [mirrorMachine]⊢⁺
    (F_R b 0 r) := by
  unfold F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  bb_steps

def Odd_cfg (p k n m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  F_R (2 * p + 1) k
    (([1] : List (Fin 2)) ^ (2 * n) +>
      (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default)))

def ETail_cfg (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) {{E}}>
    (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default)))

private theorem rule_F_b2_ksucc_c1 (k c : Nat) :
    (cfg_F 2 (k + 1) (c + 1)) [mirrorMachine]⊢⁺ (Odd_cfg 2 0 0 k c) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [cfg_F_eq_F_R, ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  exact step_F_R_b2_one (k + 1) (([1] : List (Fin 2)) ^ c +> default)

private theorem step_Odd_nsucc_p0 (k n m c : Nat) :
    (Odd_cfg 0 k (n + 1) m c) [mirrorMachine]⊢⁺ (Odd_cfg 0 (k + 2) n m c) := by
  unfold Odd_cfg
  set r := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hn : 2 * (n + 1) = 2 + 2 * n := by omega
  rw [hn, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * n) r]
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +> r))
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
  exact ReachesPlus.trans h1 h2

private theorem step_Odd_nsucc_psucc (p k n m c : Nat) :
    (Odd_cfg (p + 1) k (n + 1) m c) [mirrorMachine]⊢⁺ (Odd_cfg p (k + 2) n m c) := by
  unfold Odd_cfg
  set r := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hn : 2 * (n + 1) = 2 + 2 * n := by omega
  have hp : 2 * (p + 1) + 1 = (2 * p) + 3 := by omega
  rw [hn, hp, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * n) r]
  have h1 :=
    F_R_b3_to_D100 (2 * p) k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +> r))
  have h2 := D100_succ_11 (2 * p) k (([1] : List (Fin 2)) ^ (2 * n) +> r)
  exact ReachesPlus.trans h1 h2

private theorem step_Odd_n0_p0 (k m c : Nat) :
    (Odd_cfg 0 k 0 m c) [mirrorMachine]⊢⁺ (ETail_cfg k m c) := by
  unfold Odd_cfg ETail_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
  set r' := (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))
  have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce 0 (k + 1) r'
  have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
  have h4 := shift_E_ones (2 * (k + 1) + 4)
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) r'
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
  have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
  rw [hk] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4

private theorem step_Odd_n0_p1 (k m c : Nat) :
    (Odd_cfg 1 k 0 m c) [mirrorMachine]⊢⁺ (ETail_cfg k m c) := by
  unfold Odd_cfg ETail_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
  set r' := (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))
  have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce 1 k r'
  have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  have h4 := shift_E_ones (2 * k + 4)
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) r'
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
  have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
  rw [hk] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4

private theorem step_Odd_n0_p2_m0 (p k c : Nat) :
    (Odd_cfg (p + 2) k 0 0 c) [mirrorMachine]⊢⁺ (cfg_F (2 * p + 1) 0 (2 * (k + 3) + c)) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) 0]
  simp only [list_pow_zero, ListBlank.append_nil]
  set r' := (([1] : List (Fin 2)) ^ c +> default)
  have hp : 2 * (p + 2) + 1 = (2 * p + 2) + 3 := by omega
  rw [hp]
  have h1 := F_R_b3_to_D100 (2 * p + 2) k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce (2 * p + 3) k r'
  have h3 := C_bounce_3 (2 * p) (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
  have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
  rw [hk, <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 3)) c default,
    <- cfg_F_eq_F_R] at h3
  exact ReachesPlus.trans (ReachesPlus.trans h1 h2) h3

private theorem step_Odd_n0_p2_msucc (p k m c : Nat) :
    (Odd_cfg (p + 2) k 0 (m + 1) c) [mirrorMachine]⊢⁺ (Odd_cfg p 0 (k + 3) m c) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (m + 1)]
  set r' := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hp : 2 * (p + 2) + 1 = (2 * p + 2) + 3 := by omega
  rw [hp]
  have h1 := F_R_b3_to_D100 (2 * p + 2) k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce (2 * p + 3) k r'
  have h3 := C_bounce_3 (2 * p) (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
  have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
  rw [hk] at h3
  exact ReachesPlus.trans (ReachesPlus.trans h1 h2) h3

private theorem step_ETail_m0 (k c : Nat) :
    (ETail_cfg k 0 c) [mirrorMachine]⊢⁺ (cfg_F (2 * k + c + 7) 0 3) := by
  unfold ETail_cfg
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_E_ones c
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (2 * (k + 4) + 1) c] at h1
  have hk : 2 * (k + 4) + 1 + c = (2 * k + c + 6) + 3 := by omega
  rw [hk] at h1
  have h2 := step_E_b3_to_F 0 (2 * k + c + 6)
  have hk2 : (2 * k + c + 6) + 1 = 2 * k + c + 7 := by omega
  rw [hk2] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem step_ETail_m1 (k c : Nat) :
    (ETail_cfg k 1 c) [mirrorMachine]⊢⁺ (cfg_F (2 * (k + 4) + 1) 0 c) := by
  unfold ETail_cfg
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) 0]
  simp only [list_pow_zero, ListBlank.append_nil]
  exact step_E_01_to_F_R (2 * (k + 4) + 1) (([1] : List (Fin 2)) ^ c +> default)

private theorem step_ETail_m2 (k m c : Nat) :
    (ETail_cfg k (m + 2) c) [mirrorMachine]⊢⁺ (Odd_cfg (k + 4) 0 0 m c) := by
  unfold ETail_cfg Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (m + 1)]
  exact step_E_01_to_F_R (2 * (k + 4) + 1)
    (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))

private theorem closes_E_01_tail (b m c : Nat)
    (ih : ∀ m' < m + 1, ∀ p k, StepsToClosed mirrorMachine mirrorPs (F_R (2 * p + 1) k
      (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2)) ^ c +> default)))) :
    StepsToClosed mirrorMachine mirrorPs
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1)) {{E}}>
        (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))) := by
  rcases m with _ | m'
  · simp only [list_pow_zero, ListBlank.append_nil]
    have h1 := shift_E_ones c ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b
            + 1)) default
    rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (2 * b + 1) c] at h1
    have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1 + c)) {{E}}>
            default) =
        cfg_E 0 (2 * b + 1 + c) := rfl
    rw [h_eq] at h1
    exact StepsToClosed.of_reachesStar h1 (closes_E 0 (2 * b + 1 + c))
  · rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m']
    have h1 := step_E_01_to_F_R (2 * b + 1) (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2))
            ^ c +> default))
    exact StepsToClosed.of_reachesPlus h1 (ih m' (by omega) b 0)

private theorem closes_odd_even_ones (n : Nat) (r : ListBlank (Fin 2))
    (h_base : ∀ p k, StepsToClosed mirrorMachine mirrorPs (F_R (2 * p + 1) k r)) :
    ∀ p k, StepsToClosed mirrorMachine mirrorPs
      (F_R (2 * p + 1) k (([1] : List (Fin 2)) ^ (2 * n) +> r)) := by
  induction n with
  | zero =>
    intro p k
    simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
    exact h_base p k
  | succ n ih =>
    intro p k
    have hn : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [hn, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * n) r]
    rcases p with _ | p'
    · have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +>
            r))
      have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact StepsToClosed.of_reachesPlus (ReachesPlus.trans h1 h2) (ih 0 (k + 2))
    · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
      rw [hp]
      have h1 := F_R_b3_to_D100 (2 * p') k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2
              * n) +> r))
      have h2 := D100_succ_11 (2 * p') k (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact StepsToClosed.of_reachesPlus (ReachesPlus.trans h1 h2) (ih p' (k + 2))

private theorem closes_odd_m (m : Nat) (c : Nat) :
    ∀ p k, StepsToClosed mirrorMachine mirrorPs (F_R (2 * p + 1) k
      (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro p k
    rcases m with _ | m'
    · simp only [list_pow_zero, ListBlank.append_nil, <- cfg_F_eq_F_R]
      rcases p with _ | p'
      · exact closes_F_b1 k c
      · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
        rw [hp]
        exact closes_F_b3 (2 * p') k c
    · rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m']
      set r' := (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2)) ^ c +> default))
      rcases p with _ | _ | p''
      · have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 0 (k + 1) r'
        have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
        have h4 := shift_E_ones (2 * (k + 1) + 4) ((default : ListBlank (Fin 2)) <+ ([1] :
                List (Fin 2)) ^ 3) r'
        rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
        have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact StepsToClosed.of_reachesPlus
          (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 1 k r'
        have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        have h4 := shift_E_ones (2 * k + 4) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin
                2)) ^ 5) r'
        rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
        have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact StepsToClosed.of_reachesPlus
          (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have hp : 2 * (p'' + 2) + 1 = (2 * p'' + 2) + 3 := by omega
        rw [hp]
        have h1 := F_R_b3_to_D100 (2 * p'' + 2) k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce (2 * p'' + 3) k r'
        have h3 := C_bounce_3 (2 * p'') (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
        have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
        rw [hk] at h3
        exact StepsToClosed.of_reachesPlus (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3)
          (closes_odd_even_ones (k + 3) r' (ih m' (by omega)) p'' 0)

private theorem closes_F_b2 (k c : Nat) : StepsToClosed mirrorMachine mirrorPs (cfg_F 2 k c) := by
  rcases c with _ | c'
  · exact closes_F_c0 2 k
  · rw [cfg_F_eq_F_R, ListBlank.append_pow_succ ([1] : List (Fin 2)) c' default]
    have h1 := step_F_R_b2_one k (([1] : List (Fin 2)) ^ c' +> default)
    exact StepsToClosed.of_reachesPlus h1 (closes_odd_m k c' 2 0)

private theorem closes_F_all (b k c : Nat) :
    StepsToClosed mirrorMachine mirrorPs (cfg_F b k c) := by
  rcases b with _ | _ | _ | b'
  · exact closes_F_b0 k c
  · exact closes_F_b1 k c
  · exact closes_F_b2 k c
  · exact closes_F_b3 b' k c

/-! ## Transport Through the Mirror Symmetry -/

/-- Relabelling of control states between `mirrorMachine` and `target`. -/
def π : Fin 6 -> Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 4
  | 5 => 0

/-- Swap the two half-tapes. -/
def mirrorTape : Tape (Fin 2) -> Tape (Fin 2)
  | ⟨head, l, r⟩ => ⟨head, r, l⟩

/-- Mirror a configuration of `mirrorMachine` into a configuration of `target`. -/
def mirrorCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map π, mirrorTape c.tape⟩

private theorem step_mirror (c : Cfg (Fin 2) (Fin 6)) :
    step target (mirrorCfg c) = (step mirrorMachine c).map mirrorCfg := by
  rcases c with ⟨_ | q, ⟨head, l, r⟩⟩
  · rfl
  · rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases head with ⟨_ | _ | head, hhead⟩ <;>
    first | rfl | omega

private theorem multiStep_mirror (n : Nat) (c : Cfg (Fin 2) (Fin 6)) :
    multiStep target (mirrorCfg c) n = (multiStep mirrorMachine c n).map mirrorCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ', multiStep_succ', ih]
    cases multiStep mirrorMachine c n with
    | none => rfl
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      exact step_mirror c'

private theorem reachesPlus_mirror {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h : c_1 [mirrorMachine]⊢⁺ c_2) :
    (mirrorCfg c_1) [target]⊢⁺ (mirrorCfg c_2) := by
  rcases h with ⟨n, hn, hstep⟩
  refine ⟨n, hn, ?_⟩
  rw [multiStep_mirror, hstep]
  rfl

private theorem isNone_step_mirror {c : Cfg (Fin 2) (Fin 6)}
    (h : (step mirrorMachine c).isNone) :
    (step target (mirrorCfg c)).isNone := by
  rw [step_mirror]
  revert h
  cases step mirrorMachine c <;> intro h <;> first | rfl | cases h

/-- Canonical tape pattern
$A(b, k, c) := 0^\infty\,1^c\,0\,\mathrm{A}{>}\,0\,(10)^k\,1^b\,0^\infty$,
the mirror image of `cfg_F b k c`. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 0 (.rep [1] 2 .default)
    head  := some A
    right := .sym 0 (.rep [1, 0] 1 (.rep [1] 0 .default)) }

/-- Closed pattern set for `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

private theorem eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars = mirrorCfg (cfg_F (vars 0) (vars 1) (vars 2)) := by
  unfold evalTapePattern pat_A mirrorCfg mirrorTape cfg_F Cfg.headRight evalTapeExpr π A F
  simp only [evalTapeExpr, ListBlank.append_cons, ListBlank.append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Option.map_some]

private theorem in_ps_A (b k c : Nat) : IsInPatternSet ps (mirrorCfg (cfg_F b k c)) := by
  refine ⟨(pat_A, .true), List.Mem.head _, fun i => match i with | 0 => b | 1 => k | _ => c, ?_,
    trivial⟩
  exact (eval_pat_A (fun i => match i with | 0 => b | 1 => k | _ => c)).symm

private theorem mirrorCfg_F_403_eq :
    mirrorCfg (cfg_F 4 0 3) =
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) {{A}}>
      ([0] +> (([1] : List (Fin 2)) ^ 4 +> default)) := rfl

private theorem init_reaches_A_403 :
    (init []) [target]⊢* mirrorCfg (cfg_F 4 0 3) := by
  rw [mirrorCfg_F_403_eq]
  refine ReachesPlus.to_star ?_
  unfold init
  simp only [Tape.mk₁, list_pow_zero, list_pow_succ, List.cons_append,
    List.append_nil, ListBlank.append_nil, ListBlank.append_cons]
  bb_steps

private theorem in_ps_A_of_in_mirrorPs {cfg : Cfg (Fin 2) (Fin 6)}
    (h : IsInPatternSet mirrorPs cfg) :
    IsInPatternSet ps (mirrorCfg cfg) := by
  rcases h with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [mirrorPs, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_mirrorPat]
  exact in_ps_A (vars 0) (vars 1) (vars 2)

private theorem stepsToClosed_mirror {cfg : Cfg (Fin 2) (Fin 6)}
    (h : StepsToClosed mirrorMachine mirrorPs cfg) :
    StepsToClosed target ps (mirrorCfg cfg) := by
  rcases h with ⟨cfg', h_step, h_end⟩
  refine ⟨mirrorCfg cfg', reachesPlus_mirror h_step, ?_⟩
  rcases h_end with h_in | h_halt
  · exact Or.inl (in_ps_A_of_in_mirrorPs h_in)
  · exact Or.inr (isNone_step_mirror h_halt)

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨mirrorCfg (cfg_F 4 0 3), init_reaches_A_403, in_ps_A 4 0 3⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_pat_A]
  exact stepsToClosed_mirror (closes_F_all (vars 0) (vars 1) (vars 2))

/-- `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`. -/
inductive State
  /-- $A(b, k, c)$, the mirror image of `cfg_F b k c`. -/
  | A (b k c : ℕ)
  /-- $Odd(p, k, n, m, c)$, the mirror image of `Odd_cfg p k n m c`. -/
  | Odd (p k n m c : ℕ)
  /-- $ETail(k, m, c)$, the mirror image of `ETail_cfg k m c`. -/
  | ETail (k m c : ℕ)

/-- Initial symbolic state $A(4, 0, 3)$, reached from the blank tape. -/
def start : State := .A 4 0 3

/-- Decode a symbolic `State` into a configuration of `mirrorMachine`. -/
def encode_F : State → Cfg (Fin 2) (Fin 6)
  | .A b k c => cfg_F b k c
  | .Odd p k n m c => Odd_cfg p k n m c
  | .ETail k m c => ETail_cfg k m c

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode (s : State) : Cfg (Fin 2) (Fin 6) :=
  mirrorCfg (encode_F s)

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.A 4 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b (some (.A 3 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.A (b + 1) 0 5))
      fun k => some (.A b k 1)
  | .A b k 1 =>
    Nat.casesOn b (some (.A (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 0)) fun k => some (.Odd 2 0 0 k 0)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.A (b + 1) 0 (2 * k + 7))
  | .A b k (c + 2) =>
    Nat.casesOn b (some (.A 1 (k + 1) c)) fun b =>
    Nat.casesOn b (some (.A 1 (k + 2) c)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 (c + 1))) fun k => some (.Odd 2 0 0 k (c + 1))) fun b =>
    some (.A (b + 1) (k + 2) c)
  | .Odd p k (n + 1) m c =>
    Nat.casesOn p (some (.Odd 0 (k + 2) n m c)) fun p =>
    some (.Odd p (k + 2) n m c)
  | .Odd p k 0 m c =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn m (some (.A (2 * p + 1) 0 (2 * (k + 3) + c))) fun m =>
    some (.Odd p 0 (k + 3) m c)
  | .ETail k 0 c => some (.A (2 * k + c + 7) 0 3)
  | .ETail k 1 c => some (.A (2 * (k + 4) + 1) 0 c)
  | .ETail k (m + 2) c => some (.Odd (k + 4) 0 0 m c)

private theorem step_F (s : State) :
    match next s with
    | some s' => (encode_F s) [mirrorMachine]⊢⁺ (encode_F s')
    | none => ∃ cfg', ((encode_F s) [mirrorMachine]⊢⁺ cfg') ∧ (step mirrorMachine cfg').isNone := by
  match s with
  | .A b (k + 1) 0 => exact rule_F_ksucc_c0 b k
  | .A 0 0 0 => exact rule_F_b0_k0_c0
  | .A 1 0 0 => exact rule_F_b1_k0_c0
  | .A 2 0 0 => exact rule_F_b2_k0_c0
  | .A 3 0 0 => exact rule_F_b3_k0_c0
  | .A 4 0 0 => exact rule_F_b4_k0_c0_halt
  | .A (b + 5) 0 0 => exact rule_F_b5_k0_c0 b
  | .A 0 k 1 => exact rule_F_b0_c1 k
  | .A 1 k 1 => exact rule_F_b1_c1 k
  | .A 2 0 1 => exact rule_F_b2_k0_c1 0
  | .A 2 (k + 1) 1 => exact rule_F_b2_ksucc_c1 k 0
  | .A 3 k 1 => exact rule_F_b3_c1 k
  | .A 4 k 1 => exact rule_F_b4_c1_halt k
  | .A (b + 5) k 1 => exact rule_F_b5_c1 b k
  | .A 0 k (c + 2) => exact rule_F_b0_c2 k c
  | .A 1 k (c + 2) => exact rule_F_b1_c2 k c
  | .A 2 0 (c + 2) => exact rule_F_b2_k0_c1 (c + 1)
  | .A 2 (k + 1) (c + 2) => exact rule_F_b2_ksucc_c1 k (c + 1)
  | .A (b + 3) k (c + 2) => exact rule_F_b3_c2 b k c
  | .Odd 0 k (n + 1) m c => exact step_Odd_nsucc_p0 k n m c
  | .Odd (p + 1) k (n + 1) m c => exact step_Odd_nsucc_psucc p k n m c
  | .Odd 0 k 0 m c => exact step_Odd_n0_p0 k m c
  | .Odd 1 k 0 m c => exact step_Odd_n0_p1 k m c
  | .Odd (p + 2) k 0 0 c => exact step_Odd_n0_p2_m0 p k c
  | .Odd (p + 2) k 0 (m + 1) c => exact step_Odd_n0_p2_msucc p k m c
  | .ETail k 0 c => exact step_ETail_m0 k c
  | .ETail k 1 c => exact step_ETail_m1 k c
  | .ETail k (m + 2) c => exact step_ETail_m2 k m c

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_A_403 (fun s => ?_)
  have hs := step_F s
  rcases h : next s with _ | s'
  · rw [h] at hs
    obtain ⟨cfg', h1, h2⟩ := hs
    exact ⟨mirrorCfg cfg', (reachesPlus_mirror h1).to_star, isNone_step_mirror h2⟩
  · rw [h] at hs
    exact reachesPlus_mirror hs

/-- `target` halts from the blank tape iff `next` halts from `start` (Level B). -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC
