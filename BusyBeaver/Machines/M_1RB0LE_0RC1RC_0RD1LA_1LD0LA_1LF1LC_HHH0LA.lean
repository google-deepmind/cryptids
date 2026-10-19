/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`.

## Collatz-like Acceleration Rules

The primary canonical configuration family is:
`D(a, b, c, d) = 0^∞ {{D}}> (10)^a (110)^b 0^c 1^d 0^∞` (`c ∈ {0, 1}`),
together with the intermediate families:
- `B_mid(a, k, b, d) = 0^∞ (01)^a 1^k {{B}}> 00 (110)^b 0 1^d 0^∞`
- `H_mid(a, b, m) = 0^∞ (01)^a 1 (111)^b 0 {{D}}> 1^m 0^∞`
- `A_rem(a, k, q, m) = 0^∞ (01)^a 1^k <{{A}} (110)^q 0 1^m 0^∞`

Starting from the blank tape, the machine reaches $D(0, 0, 0, 4)$. The accelerated rules are:

```text
D(a, b, 0, 0)         =  D(a, b, 1, 0)
D(0, 0, 0, 1)         -> D(0, 0, 0, 4)
D(a + 1, 0, 0, 1)     -> B_mid(a + 1, 1, 0, 0)
D(a, b + 1, 0, 1)     -> D(a + 2, b, 1, 3)
D(a, b, 0, 2)         =  D(a, b + 1, 1, 0)
D(a, b, 0, d + 3)     -> D(a + 2, b, 0, d + 1)

D(0, 0, 1, d)         -> D(0, 0, 1, d + 1)
D(0, b + 1, 1, d)     -> D(1, b, 1, d + 2)
D(a + 1, b, 1, d)     -> B_mid(a, 1, b, d)

B_mid(a, k+1, b+1, d) -> B_mid(a, k + 2, b, d + 2)
B_mid(0, 1, 0, d)     -> D(0, 0, 0, d + 4)
B_mid(1, 1, 0, d)     -> Halt
B_mid(2, 1, 0, 0)     -> D(1, 2, 1, 2)
B_mid(2, 1, 0, d + 1) -> D(2, 2, 0, d + 1)
B_mid(a + 3, 1, 0, d) -> H_mid(a, 2, d + 2)
B_mid(a, k + 2, 0, d) -> A_rem(a, k + 1, 0, d + 3)
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

private theorem split_111_succ (b : Nat) (l_0 : ListBlank (Fin 2)) :
    l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1) =
    ((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1] := by
  induction b generalizing l_0 with
  | zero =>
    simp only [list_pow_zero, list_pow_succ, List.append_nil, ListBlank.append_append]
    rfl
  | succ b ih =>
    have h1 : l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1 + 1) =
        (l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] := by
      rw [ListBlank.append_pow_add_rev l_0 ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [h1, ih l_0]
    have h2 : ((((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ [1, 1, 1]) =
        (((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1, 1, 1]) <+ [1] := by
      simp only [ListBlank.append_append]
      rfl
    rw [h2, <- ListBlank.append_pow_succ ([1, 1, 1] : List (Fin 2)) b]

private theorem comm_1_111 (b : Nat) (l_0 : ListBlank (Fin 2)) :
    (l_0 <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^b =
    (l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1] := by
  induction b generalizing l_0 with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
  | succ b ih =>
    rw [ListBlank.append_pow_add_rev (l_0 <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1, ih l_0]
    have h1 : (((l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) =
        ((l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ ([1, 1, 1] : List (Fin 2))^1) <+ [1] := by
      simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_append]
      rfl
    rw [h1, <- ListBlank.append_pow_add_rev l_0 ([1, 1, 1] : List (Fin 2)) b 1]

private theorem shift_A_left_111 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1, 1] : List (Fin 2))^k) <{{A}} r) [target]⊢*
    (l <{{A}} (([1, 1, 0] : List (Fin 2))^k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, <- ListBlank.append_append]
    have h1 : (((l <+ ([1, 1, 1] : List (Fin 2))^k) <+ [1, 1, 1]) <{{A}} r)
        [target]⊢⁺
        ((l <+ ([1, 1, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> r)) := by
      bb_steps
    have h2 := ih l (([1, 1, 0] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ' ([1, 1, 0] : List (Fin 2)) k r] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

private theorem shift_D_right_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (([1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    (((l <+ ([0, 1] : List (Fin 2))^k) <+ [0]) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : ((l <+ [0]) {{D}}> ([1, 0] +> (([1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        (((l <+ [0, 1]) <+ [0]) {{D}}> (([1, 0] : List (Fin 2))^k +> r)) := by
      bb_steps
    have h2 := ih (l <+ [0, 1]) r
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k l] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

private theorem shift_D_right_110 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    (((l <+ ([1, 1, 1] : List (Fin 2))^k) <+ [0]) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : ((l <+ [0]) {{D}}> ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        (((l <+ [1, 1, 1]) <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^k +> r)) := by
      bb_steps
    have h2 := ih (l <+ [1, 1, 1]) r
    rw [ListBlank.append_pow_succ' ([1, 1, 1] : List (Fin 2)) k l] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

private theorem shift_A_left_01_with_110 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> r)) [target]⊢*
    (l <{{A}} ([1, 1, 0] +> (([1, 0] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, <- ListBlank.append_append]
    have h1 : (((l <+ ([0, 1] : List (Fin 2))^k) <+ [0, 1]) <{{A}} ([1, 1, 0] +> r))
        [target]⊢⁺
        ((l <+ ([0, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> ([1, 0] +> r))) := by
      bb_steps
    have h2 := ih l ([1, 0] +> r)
    rw [ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) k r] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

private theorem bounce_A_left_with_110 (r : ListBlank (Fin 2)) :
    (default <{{A}} ([1, 1, 0] +> r)) [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^2 +> r)) := by
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem drain_A_left_01_with_110 (a : Nat) (r : ListBlank (Fin 2)) :
    ((default <+ ([0, 1] : List (Fin 2))^a) <{{A}} ([1, 1, 0] +> r)) [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^(a + 2) +> r)) := by
  have h1 := shift_A_left_01_with_110 a default r
  have h2 := bounce_A_left_with_110 (([1, 0] : List (Fin 2))^a +> r)
  have h_eq : (([1, 0] : List (Fin 2))^2 +> (([1, 0] : List (Fin 2))^a +> r)) =
      (([1, 0] : List (Fin 2))^(a + 2) +> r) := by
    rw [<- ListBlank.append_pow_add ([1, 0] : List (Fin 2)) 2 a r, Nat.add_comm]
  rw [h_eq] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem drain_A_left_111_01_with_110 (a b : Nat) (r : ListBlank (Fin 2)) :
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}} ([1, 1, 0]
        +> r))
    [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^(a + 2) +> (([1, 1, 0] : List (Fin 2))^b +> r))) := by
  have h1 := shift_A_left_111 b (default <+ ([0, 1] : List (Fin 2))^a) ([1, 1, 0] +> r)
  have h_eq : (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> r)) =
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> r)) := by
    rw [ListBlank.append_pow_succ', ListBlank.append_pow_succ]
  rw [h_eq] at h1
  exact ReachesStar.trans_plus h1 (drain_A_left_01_with_110 a (([1, 1, 0] : List (Fin 2))^b +> r))

private theorem roundtrip_D_110_cap0 (b d : Nat) (l_0 : ListBlank (Fin 2)) :
    ((l_0 <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^d
        +> default))))
    [target]⊢⁺
    ((l_0 <+ [1, 1]) <{{A}} (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^(d +
        2) +> default)))) := by
  have h1 := shift_D_right_110 (b + 1) l_0 ([0] +> (([1] : List (Fin 2))^d +> default))
  rw [split_111_succ b l_0] at h1
  have h2 : (((((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ [0]) {{D}}>
      ([0] +> (([1] : List (Fin 2))^d +> default)))
      [target]⊢⁺
      (((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}}
        ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))) := by
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d]
      rfl
    rw [hd]
    bb_steps
  have h3 := shift_A_left_111 b (l_0 <+ [1, 1]) ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))
  exact ReachesStar.trans_plus h1 (ReachesPlus.trans_star h2 h3)

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left  := .default
    head  := some D
    right := .rep [1, 0] 0 (.rep [1, 1, 0] 1 (.rep [0] 2 (.rep [1] 3 .default))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .not (.ge_const 2 2))]

def D_cfg (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default {{D}}>
    (([1, 0] : List (Fin 2))^a +>
      (([1, 1, 0] : List (Fin 2))^b +>
        (([0] : List (Fin 2))^c +>
          (([1] : List (Fin 2))^d +> default))))

private theorem eval_pat_D (vars : Nat -> Nat) :
    evalTapePattern pat_D vars = D_cfg (vars 0) (vars 1) (vars 2) (vars 3) := by
  rfl

private theorem in_ps_D (a b c d : Nat) (hc : c <= 1) : IsInPatternSet ps (D_cfg a b c d) := by
  refine ⟨(pat_D, .not (.ge_const 2 2)), by simp [ps],
    fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0, rfl, ?_⟩
  simp only [evalVarCond]
  omega

private theorem closes_of_in_ps {c_1 : Cfg (Fin 2) (Fin 6)} {a b c d : Nat}
    (h₁ : c_1 [target]⊢⁺ D_cfg a b c d) (hc : c <= 1) : StepsToClosed target ps c_1 :=
  StepsToClosed.of_isInPatternSet h₁ (in_ps_D a b c d hc)

def H_mid (a b m : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [0]) {{D}}>
    (([1] : List (Fin 2))^m +> default)

private theorem step_H_mid_a0_m1 (b : Nat) :
    ∃ cfg', ((H_mid 0 (b + 1) 1) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^0) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b
      + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      ((((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <{{A}}
        ([0] +> (([1] : List (Fin 2))^3 +> default)))) := by
    rw [ListBlank.append_pow_add_rev (default <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_left_111 (b + 1) (default <+ [1]) ([0] +> (([1] : List (Fin 2))^3 +> default))
  have h3 : (((default <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
      [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin
          2))^3 +> default))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ⟨_, ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3, rfl⟩

private theorem closes_H_mid_a0_m1 (b : Nat) : StepsToClosed target ps (H_mid 0 (b + 1) 1) := by
  obtain ⟨cfg', h1, h2⟩ := step_H_mid_a0_m1 b
  exact StepsToClosed.of_halting h1 h2

private theorem step_H_mid_asucc_m1 (a b : Nat) :
    (H_mid (a + 1) (b + 1) 1) [target]⊢⁺ (D_cfg (if a = 0 then 1 else a + 1) (b + 1) 1 5) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) <+ ([1, 1, 1] : List (Fin
      2))^(b + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
          1)) <{{A}}
        ([0] +> (([1] : List (Fin 2))^3 +> default))) := by
    rw [ListBlank.append_pow_add_rev ((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1])
      ([1, 1, 1] : List (Fin 2)) b 1]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_left_111 (b + 1) ((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1])
    ([0] +> (([1] : List (Fin 2))^3 +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  rcases a with _ | a'
  · have h3 : ((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
        [target]⊢⁺
        ((((default <+ [1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
              := by
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) b]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    have h4 := roundtrip_D_110_cap0 b 3 (default <+ [1, 1, 1])
    have h5 : ((((default <+ [1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^5 +> default)))))
        [target]⊢⁺ D_cfg 1 (b + 1) 1 5 := by
      unfold D_cfg
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) b]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    exact ReachesPlus.trans h12 (ReachesPlus.trans h3 (ReachesPlus.trans h4 h5))
  · have h3 : ((((default <+ ([0, 1] : List (Fin 2))^(a' + 2)) <+ [1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
        [target]⊢⁺
        (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
              := by
      rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) a' 2]
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) b]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    have h4 := roundtrip_D_110_cap0 b 3 ((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1])
    have h5 : (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^5 +> default)))))
        [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a') <{{A}}
          ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] :
              List (Fin 2))^5 +> default)))))) := by
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) b]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    have h6 := drain_A_left_01_with_110 a'
      ((([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^5
          +> default))))
    exact ReachesPlus.trans h12
      (ReachesPlus.trans h3 (ReachesPlus.trans h4 (ReachesPlus.trans h5 h6)))

private theorem closes_H_mid_asucc_m1 (a b : Nat) :
    StepsToClosed target ps (H_mid (a + 1) (b + 1) 1) :=
  closes_of_in_ps (step_H_mid_asucc_m1 a b) (by decide)

private theorem step_H_mid_m2 (a b : Nat) :
    (H_mid a (b + 1) 2) [target]⊢⁺ (D_cfg (a + 2) (b + 1) 1 2) := by
  unfold H_mid
  rw [comm_1_111 (b + 1) (default <+ ([0, 1] : List (Fin 2))^a)]
  have h1 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+
      [1]) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^2 +> default))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default)))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := drain_A_left_111_01_with_110 a (b + 1)
    (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))
  exact ReachesPlus.trans h1 h2

private theorem closes_H_mid_m2 (a b : Nat) : StepsToClosed target ps (H_mid a (b + 1) 2) :=
  closes_of_in_ps (step_H_mid_m2 a b) (by decide)

private theorem step_H_mid_a0_m3 (b m : Nat) :
    ∃ cfg', ((H_mid 0 (b + 1) (m + 3)) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^0) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b
      + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default)))
      [target]⊢⁺
      ((((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default))) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 m]
      rfl
    have hb : (default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2) =
        ((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] := by
      rw [ListBlank.append_pow_add_rev (default <+ [1]) ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [hm, hb, ListBlank.append_pow_succ ([1] : List (Fin 2)) m]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_left_111 (b + 2) (default <+ [1]) (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))))
      [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m
          + 1) +> default)))) := by
    simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  exact ⟨_, ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3, rfl⟩

private theorem closes_H_mid_a0_m3 (b m : Nat) :
    StepsToClosed target ps (H_mid 0 (b + 1) (m + 3)) := by
  obtain ⟨cfg', h1, h2⟩ := step_H_mid_a0_m3 b m
  exact StepsToClosed.of_halting h1 h2

private theorem step_H_mid_a1_m3_prefix (b m : Nat) :
    (H_mid 1 (b + 1) (m + 3)) [target]⊢⁺
    (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 1) +> default)) := by
  unfold H_mid
  have h1 : (((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
      1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2))
          <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 m]
      rfl
    have hb : ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
        2) =
        (((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1))
            <+ [1, 1, 1] := by
      rw [ListBlank.append_pow_add_rev ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1])
        ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [hm, hb, ListBlank.append_pow_succ ([1] : List (Fin 2)) m]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_left_111 (b + 2) ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1])
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (((default <+ ([1, 1, 1] : List (Fin 2))^1) <+ [0]) {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))) := by
    rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) (b + 1)]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h4 := shift_D_right_110 (b + 2) (default <+ ([1, 1, 1] : List (Fin 2))^1)
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h_eq : ((default <+ ([1, 1, 1] : List (Fin 2))^1) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) =
      (default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) := by
    rw [<- ListBlank.append_pow_add_rev default ([1, 1, 1] : List (Fin 2)) 1 (b + 2)]
    have h_add : 1 + (b + 2) = b + 3 := by omega
    rw [h_add]
  rw [h_eq] at h4
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) (ReachesPlus.trans_star h3 h4)

private theorem step_H_mid_a1_m3_0 (b : Nat) :
    (H_mid 1 (b + 1) 3) [target]⊢⁺ (D_cfg 2 (b + 2) 1 3) := by
  have h_pref := step_H_mid_a1_m3_prefix b 0
  have h1 : (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default))
      [target]⊢⁺
      ((default <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default)))) := by
    rw [ListBlank.append_pow_add_rev default ([1, 1, 1] : List (Fin 2)) (b + 2) 1]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := drain_A_left_111_01_with_110 0 (b + 2)
    (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default))
  exact ReachesPlus.trans h_pref (ReachesPlus.trans h1 h2)

private theorem step_H_mid_a1_m3_1 (b : Nat) :
    (H_mid 1 (b + 1) 4) [target]⊢⁺ (D_cfg 1 (b + 3) 1 2) := by
  have h_pref := step_H_mid_a1_m3_prefix b 1
  have h1 : (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^2 +> default))
      [target]⊢⁺
      (((default <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <{{A}}
        (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))) := by
    rw [split_111_succ (b + 2) default]
    rw [ListBlank.append_pow_add_rev (default <+ [1, 1]) ([1, 1, 1] : List (Fin 2)) (b + 2) 1]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_left_111 (b + 3) (default <+ [1, 1])
    (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))
  have h3 : ((default <+ [1, 1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 3) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2
          +> default))))
      [target]⊢⁺ D_cfg 1 (b + 3) 1 2 := by
    unfold D_cfg
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.trans h_pref (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3)

private theorem step_H_mid_a1_m3_succ2 (b m' : Nat) :
    (H_mid 1 (b + 1) (m' + 5)) [target]⊢⁺ (D_cfg 2 (b + 3) 0 (m' + 1)) := by
  have h_pref := step_H_mid_a1_m3_prefix b (m' + 2)
  have h1 : (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m' + 3) +> default))
      [target]⊢⁺
      ((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(m' + 1) +> default))))
            := by
    have hm : (([1] : List (Fin 2))^(m' + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m' +> default)) := by
      rw [Nat.add_comm m' 3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 m']
      rfl
    rw [hm, ListBlank.append_pow_succ ([1] : List (Fin 2)) m']
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := drain_A_left_111_01_with_110 0 (b + 3)
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(m' + 1) +> default))
  exact ReachesPlus.trans h_pref (ReachesPlus.trans h1 h2)

private theorem closes_H_mid_a1_m3 (b m : Nat) :
    StepsToClosed target ps (H_mid 1 (b + 1) (m + 3)) := by
  rcases m with _ | _ | m'
  · exact closes_of_in_ps (step_H_mid_a1_m3_0 b) (by decide)
  · exact closes_of_in_ps (step_H_mid_a1_m3_1 b) (by decide)
  · exact closes_of_in_ps (step_H_mid_a1_m3_succ2 b m') (by decide)

private theorem step_H_mid_asucc2_m3 (a b m : Nat) :
    (H_mid (a + 2) (b + 1) (m + 3)) [target]⊢⁺ (H_mid a (b + 3) (m + 1)) := by
  unfold H_mid
  have h1 : (((((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin
      2))^(b + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
          2)) <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 m]
      rfl
    have hb : ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin
        2))^(b + 2) =
        (((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
            1)) <+ [1, 1, 1] := by
      rw [ListBlank.append_pow_add_rev ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1])
        ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [hm, hb, ListBlank.append_pow_succ ([1] : List (Fin 2)) m]
    simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_left_111 (b + 2) ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1])
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) <+ [0])
          {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))) := by
    rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) a 2]
    rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) (b + 1)]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h4 := shift_D_right_110 (b + 2)
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1)
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h_eq : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) <+
      ([1, 1, 1] : List (Fin 2))^(b + 2)) =
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) := by
    rw [<- ListBlank.append_pow_add_rev ((default <+ ([0, 1] : List (Fin 2))^a) <+ [1])
      ([1, 1, 1] : List (Fin 2)) 1 (b + 2)]
    have h_add : 1 + (b + 2) = b + 3 := by omega
    rw [h_add]
  rw [h_eq] at h4
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) (ReachesPlus.trans_star h3 h4)

private theorem closes_H_mid (a : Nat) :
    ∀ b m, StepsToClosed target ps (H_mid a (b + 1) (m + 1)) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b m
    rcases m with _ | _ | m'
    · rcases a with _ | a'
      · exact closes_H_mid_a0_m1 b
      · exact closes_H_mid_asucc_m1 a' b
    · exact closes_H_mid_m2 a b
    · rcases a with _ | _ | a'
      · exact closes_H_mid_a0_m3 b m'
      · exact closes_H_mid_a1_m3 b m'
      · exact StepsToClosed.of_reachesPlus (step_H_mid_asucc2_m3 a' b m')
          (ih a' (by omega) (b + 2) m')

def B_mid (a k b d : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^k) {{B}}>
    ([0, 0] +> (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^d +> default)))))

def A_rem (a k q m : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^k) <{{A}}
    (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^m +> default))))

private theorem step_B_mid_bsucc (a k b d : Nat) :
    (B_mid a (k + 1) (b + 1) d) [target]⊢⁺ (B_mid a (k + 2) b (d + 2)) := by
  unfold B_mid
  have h1 : (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) {{B}}>
      ([0, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^d +>
          default)))))
      [target]⊢⁺
      (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0]) <+ [0])
          {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^d +> default)))) := by
    simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  have h2 := roundtrip_D_110_cap0 b d
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0])
  have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0])
      <+ [1, 1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 2)) {{B}}>
        ([0, 0] +> (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^(d + 2) +>
            default))))) := by
    rw [ListBlank.append_pow_add_rev (default <+ ([0, 1] : List (Fin 2))^a)
      ([1] : List (Fin 2)) (k + 1) 1]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)

private theorem step_B_mid_bsucc_star (b : Nat) : ∀ a k d,
    (B_mid a (k + 1) b d) [target]⊢* (B_mid a (k + 1 + b) 0 (d + 2 * b)) := by
  induction b with
  | zero =>
    intro a k d
    simp only [Nat.add_zero, Nat.mul_zero]
    exact ReachesStar.refl _ _
  | succ b ih =>
    intro a k d
    have h1 := ReachesPlus.to_star (step_B_mid_bsucc a k b d)
    have h2 := ih a (k + 1) (d + 2)
    have hk : k + 1 + 1 + b = k + 1 + (b + 1) := by omega
    have hd : d + 2 + 2 * b = d + 2 * (b + 1) := by omega
    rw [hk, hd] at h2
    exact ReachesStar.trans h1 h2

private theorem step_B_mid_ksucc2_b0 (a k d : Nat) :
    (B_mid a (k + 2) 0 d) [target]⊢⁺ (A_rem a (k + 1) 0 (d + 3)) := by
  unfold B_mid A_rem
  rw [ListBlank.append_pow_add_rev (default <+ ([0, 1] : List (Fin 2))^a)
    ([1] : List (Fin 2)) (k + 1) 1]
  have hd : (([1] : List (Fin 2))^(d + 3) +> default) =
      ([1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 d]
    rfl
  rw [hd]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_A_rem_ksucc3 (a k q m : Nat) :
    (A_rem a (k + 3) q m) [target]⊢⁺ (A_rem a k (q + 1) m) := by
  unfold A_rem
  rw [ListBlank.append_pow_add_rev (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin 2)) k 3]
  have hq : (([1, 1, 0] : List (Fin 2))^(q + 1) +> ([0] +> (([1] : List (Fin 2))^m +> default))) =
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^m +>
          default)))) := by
    rw [ListBlank.append_pow_succ]
  rw [hq]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_A_rem_k0_qsucc (a q m : Nat) :
    (A_rem a 0 (q + 1) m) [target]⊢⁺ (D_cfg (a + 2) q 1 m) := by
  have h1 := drain_A_left_01_with_110 a
    ((([1, 1, 0] : List (Fin 2))^q +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^m +>
        default))))
  have h_eq : (((default <+ ([0, 1] : List (Fin 2))^a) <{{A}}
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^q +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
          2))^m +> default)))))) =
      A_rem a 0 (q + 1) m := by
    unfold A_rem
    rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) q]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
  rwa [h_eq] at h1

private theorem closes_A_rem_k0_qsucc (a q m : Nat) :
    StepsToClosed target ps (A_rem a 0 (q + 1) m) :=
  closes_of_in_ps (step_A_rem_k0_qsucc a q m) (by decide)

private theorem step_A_rem_a0_k1 (q m : Nat) :
    ∃ cfg', ((A_rem 0 1 q m) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  have h1 : (A_rem 0 1 q m) [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^m
          +> default))))) := by
    unfold A_rem
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  exact ⟨_, h1, rfl⟩

private theorem closes_A_rem_a0_k1 (q m : Nat) : StepsToClosed target ps (A_rem 0 1 q m) := by
  obtain ⟨cfg', h1, h2⟩ := step_A_rem_a0_k1 q m
  exact StepsToClosed.of_halting h1 h2

private theorem step_A_rem_asucc_k1_q0 (a m : Nat) :
    (A_rem (a + 1) 1 0 m) [target]⊢⁺ (D_cfg (if a = 0 then 1 else a + 1) 0 1 (m + 2)) := by
  rcases a with _ | a'
  · have h1 : (A_rem 1 1 0 m) [target]⊢⁺ D_cfg 1 0 1 (m + 2) := by
      unfold A_rem D_cfg
      have hm : (([1] : List (Fin 2))^(m + 2) +> default) =
          ([1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
        rw [Nat.add_comm m 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 m]
        rfl
      rw [hm]
      simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
        ListBlank.append_nil]
      bb_steps
    exact h1
  · have h1 : (A_rem (a' + 2) 1 0 m) [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a') <{{A}}
          ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^1 +> (([1] : List
              (Fin 2))^(m + 2) +> default)))))) := by
      unfold A_rem
      rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) a' 2]
      have hm : (([1] : List (Fin 2))^(m + 2) +> default) =
          ([1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
        rw [Nat.add_comm m 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 m]
        rfl
      rw [hm]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    have h2 := drain_A_left_01_with_110 a'
      ((([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^(m + 2)
          +> default))))
    exact ReachesPlus.trans h1 h2

private theorem closes_A_rem_asucc_k1_q0 (a m : Nat) :
    StepsToClosed target ps (A_rem (a + 1) 1 0 m) :=
  closes_of_in_ps (step_A_rem_asucc_k1_q0 a m) (by decide)

private theorem step_A_rem_asucc_k1_qsucc (a q m : Nat) :
    (A_rem (a + 1) 1 (q + 1) m) [target]⊢⁺
      (D_cfg (if a = 0 then 1 else a + 1) (q + 1) 1 (m + 2)) := by
  rcases a with _ | a'
  · have h1 : (A_rem 1 1 (q + 1) m) [target]⊢⁺
        ((((default <+ [1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(q + 1) +> ([0] +> (([1] : List (Fin 2))^m +> default)))))
              := by
      unfold A_rem
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) q]
      simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
        ListBlank.append_nil]
      bb_steps
    have h2 := roundtrip_D_110_cap0 q m (default <+ [1, 1, 1])
    have h3 : ((((default <+ [1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^(m + 2) +> default)))))
        [target]⊢⁺ D_cfg 1 (q + 1) 1 (m + 2) := by
      unfold D_cfg
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) q]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)
  · have h1 : (A_rem (a' + 2) 1 (q + 1) m) [target]⊢⁺
        (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(q + 1) +> ([0] +> (([1] : List (Fin 2))^m +> default)))))
              := by
      unfold A_rem
      rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) a' 2]
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) q]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    have h2 := roundtrip_D_110_cap0 q m ((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1])
    have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^(m + 2) +> default)))))
        [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a') <{{A}}
          ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^(q + 1) +> (([0] : List (Fin 2))^1 +> (([1] :
              List (Fin 2))^(m + 2) +> default)))))) := by
      rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) q]
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
        ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    have h4 := drain_A_left_01_with_110 a'
      ((([1, 1, 0] : List (Fin 2))^(q + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^(m
          + 2) +> default))))
    exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))

private theorem closes_A_rem_asucc_k1_qsucc (a q m : Nat) :
    StepsToClosed target ps (A_rem (a + 1) 1 (q + 1) m) :=
  closes_of_in_ps (step_A_rem_asucc_k1_qsucc a q m) (by decide)

private theorem step_A_rem_a0_k2 (q m : Nat) :
    (A_rem 0 2 q m) [target]⊢⁺ (D_cfg 1 q 1 m) := by
  unfold A_rem D_cfg
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem closes_A_rem_a0_k2 (q m : Nat) : StepsToClosed target ps (A_rem 0 2 q m) :=
  closes_of_in_ps (step_A_rem_a0_k2 q m) (by decide)

private theorem step_A_rem_asucc_k2 (a q m : Nat) :
    (A_rem (a + 1) 2 q m) [target]⊢⁺ (B_mid a 2 q m) := by
  unfold A_rem B_mid
  rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) a 1]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_A_rem_asucc_k2_to_A_rem (a q m : Nat) :
    (A_rem (a + 1) 2 q m) [target]⊢⁺ (A_rem a (q + 1) 0 (m + 2 * q + 3)) := by
  have h1 := step_A_rem_asucc_k2 a q m
  have h2 := step_B_mid_bsucc_star q a 1 m
  have hq : 1 + 1 + q = q + 2 := by omega
  rw [hq] at h2
  have h3 := step_B_mid_ksucc2_b0 a q (m + 2 * q)
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem closes_A_rem (a : Nat) :
    ∀ k q m, k + q >= 1 -> StepsToClosed target ps (A_rem a k q m) := by
  induction a using Nat.strong_induction_on with
  | h a iha =>
    intro k
    induction k using Nat.strong_induction_on with
    | h k ihk =>
      intro q m hkq
      rcases k with _ | _ | _ | k'
      · rcases q with _ | q'
        · omega
        · exact closes_A_rem_k0_qsucc a q' m
      · rcases a with _ | a'
        · exact closes_A_rem_a0_k1 q m
        · rcases q with _ | q'
          · exact closes_A_rem_asucc_k1_q0 a' m
          · exact closes_A_rem_asucc_k1_qsucc a' q' m
      · rcases a with _ | a'
        · exact closes_A_rem_a0_k2 q m
        · exact StepsToClosed.of_reachesPlus (step_A_rem_asucc_k2_to_A_rem a' q m)
            (iha a' (by omega) (q + 1) 0 (m + 2 * q + 3) (by omega))
      · exact StepsToClosed.of_reachesPlus (step_A_rem_ksucc3 a k' q m)
          (ihk k' (by omega) (q + 1) m (by omega))

private theorem step_B_mid_a0_k1_b0 (d : Nat) :
    (B_mid 0 1 0 d) [target]⊢⁺ (D_cfg 0 0 0 (d + 4)) := by
  unfold B_mid D_cfg
  have hd : (([1] : List (Fin 2))^(d + 4) +> default) =
      ([1, 1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 d]
    rfl
  rw [hd]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
    ListBlank.append_nil]
  bb_steps

private theorem closes_B_mid_a0_k1_b0 (d : Nat) : StepsToClosed target ps (B_mid 0 1 0 d) :=
  closes_of_in_ps (step_B_mid_a0_k1_b0 d) (by decide)

private theorem step_B_mid_a1_k1_b0 (d : Nat) :
    ∃ cfg', ((B_mid 1 1 0 d) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  have h1 : (B_mid 1 1 0 d) [target]⊢⁺
      (default <{{F}} ([1, 0, 1, 1, 0] +> (([1] : List (Fin 2))^(d + 2) +> default))) := by
    unfold B_mid
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d]
      rfl
    rw [hd]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  exact ⟨_, h1, rfl⟩

private theorem closes_B_mid_a1_k1_b0 (d : Nat) : StepsToClosed target ps (B_mid 1 1 0 d) := by
  obtain ⟨cfg', h1, h2⟩ := step_B_mid_a1_k1_b0 d
  exact StepsToClosed.of_halting h1 h2

private theorem step_B_mid_a2_k1_b0_0 :
    (B_mid 2 1 0 0) [target]⊢⁺ (D_cfg 1 2 1 2) := by
  unfold B_mid D_cfg
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    List.append_nil, ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default]
  bb_steps

private theorem step_B_mid_a2_k1_b0_succ (d' : Nat) :
    (B_mid 2 1 0 (d' + 1)) [target]⊢⁺ (D_cfg 2 2 0 (d' + 1)) := by
  unfold B_mid D_cfg
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d']
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem closes_B_mid_a2_k1_b0 (d : Nat) : StepsToClosed target ps (B_mid 2 1 0 d) := by
  rcases d with _ | d'
  · exact closes_of_in_ps step_B_mid_a2_k1_b0_0 (by decide)
  · exact closes_of_in_ps (step_B_mid_a2_k1_b0_succ d') (by decide)

private theorem step_B_mid_asucc3_k1_b0 (a d : Nat) :
    (B_mid (a + 3) 1 0 d) [target]⊢⁺ (H_mid a 2 (d + 2)) := by
  unfold B_mid H_mid
  rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) a 3]
  have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
      ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d]
    rfl
  rw [hd]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem closes_B_mid_b0 (k : Nat) :
    ∀ a d, StepsToClosed target ps (B_mid a (k + 1) 0 d) := by
  intro a d
  rcases k with _ | k'
  · rcases a with _ | _ | _ | a''
    · exact closes_B_mid_a0_k1_b0 d
    · exact closes_B_mid_a1_k1_b0 d
    · exact closes_B_mid_a2_k1_b0 d
    · exact StepsToClosed.of_reachesPlus (step_B_mid_asucc3_k1_b0 a'' d)
        (closes_H_mid a'' 1 (d + 1))
  · exact StepsToClosed.of_reachesPlus (step_B_mid_ksucc2_b0 a k' d)
      (closes_A_rem a (k' + 1) 0 (d + 3) (by omega))

private theorem closes_B_mid (b : Nat) :
    ∀ a k d, StepsToClosed target ps (B_mid a (k + 1) b d) := by
  induction b with
  | zero =>
    intro a k d
    exact closes_B_mid_b0 k a d
  | succ b ih =>
    intro a k d
    exact StepsToClosed.of_reachesPlus (step_B_mid_bsucc a k b d) (ih a (k + 1) (d + 2))

private theorem step_D_cfg_to_D_mid (a : Nat) (r : ListBlank (Fin 2)) :
    (default {{D}}> (([1, 0] : List (Fin 2))^a +> r)) [target]⊢*
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ [0]) {{D}}> r) := by
  have h := shift_D_right_10 a default r
  have h_def : (default <+ ([0] : List (Fin 2))) = default :=
    ListBlank.default_eq_append_zero.symm
  rwa [h_def] at h

private theorem step_D_cfg_c1_a0_b0 (d : Nat) :
    (D_cfg 0 0 1 d) [target]⊢⁺ (D_cfg 0 0 1 (d + 1)) := by
  unfold D_cfg
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
    ListBlank.append_nil]
  bb_steps

private theorem step_D_cfg_c1_a0_bsucc (b' d : Nat) :
    (D_cfg 0 (b' + 1) 1 d) [target]⊢⁺ (D_cfg 1 b' 1 (d + 2)) := by
  have h1 := roundtrip_D_110_cap0 b' d default
  have h_def : (default <+ ([0] : List (Fin 2))) = default :=
    ListBlank.default_eq_append_zero.symm
  rw [h_def] at h1
  have h2 : ((default <+ [1, 1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^b' +> ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))))
      [target]⊢⁺ D_cfg 1 b' 1 (d + 2) := by
    unfold D_cfg
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h_start : ((default {{D}}>
      (([1, 1, 0] : List (Fin 2))^(b' + 1) +> ([0] +> (([1] : List (Fin 2))^d +> default))))) =
      D_cfg 0 (b' + 1) 1 d := by
    unfold D_cfg; rfl
  rw [h_start] at h1
  exact ReachesPlus.trans h1 h2

private theorem step_D_cfg_c1_asucc (a' b d : Nat) :
    (D_cfg (a' + 1) b 1 d) [target]⊢⁺ (B_mid a' 1 b d) := by
  have h1 := step_D_cfg_to_D_mid a'
    ([1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
        2))^d +> default))))
  have h_start : (default {{D}}>
      (([1, 0] : List (Fin 2))^a' +> ([1, 0] +>
        (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^d +>
            default)))))) =
      D_cfg (a' + 1) b 1 d := by
    unfold D_cfg
    rw [ListBlank.append_pow_succ']
  rw [h_start] at h1
  have h2 : (((default <+ ([0, 1] : List (Fin 2))^a') <+ [0]) {{D}}>
      ([1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
          2))^d +> default)))))
      [target]⊢⁺ B_mid a' 1 b d := by
    unfold B_mid
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  exact ReachesStar.trans_plus h1 h2

private theorem closes_D_cfg_c1 (a b d : Nat) : StepsToClosed target ps (D_cfg a b 1 d) := by
  rcases a with _ | a'
  · rcases b with _ | b'
    · exact closes_of_in_ps (step_D_cfg_c1_a0_b0 d) (by decide)
    · exact closes_of_in_ps (step_D_cfg_c1_a0_bsucc b' d) (by decide)
  · exact StepsToClosed.of_reachesPlus (step_D_cfg_c1_asucc a' b d) (closes_B_mid b a' 0 d)

private theorem D_cfg_c0_d0_eq (a b : Nat) : D_cfg a b 0 0 = D_cfg a b 1 0 := by
  unfold D_cfg
  simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
    ListBlank.append_nil, ListBlank.cons_zero_default]

private theorem D_cfg_c0_d2_eq (a b : Nat) : D_cfg a b 0 2 = D_cfg a (b + 1) 1 0 := by
  unfold D_cfg
  have h_b : (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
      2))^0 +> default))) =
      (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
          2))^0 +> default)))) := by
    rw [← ListBlank.append_pow_succ']
  rw [h_b]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    List.append_nil, ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default]

private theorem step_D_cfg_c0_d1_a0_b0 :
    (D_cfg 0 0 0 1) [target]⊢⁺ (D_cfg 0 0 0 4) := by
  unfold D_cfg
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_D_cfg_c0_d1_asucc_b0 (a' : Nat) :
    (D_cfg (a' + 1) 0 0 1) [target]⊢⁺ (B_mid (a' + 1) 1 0 0) := by
  have h1 := step_D_cfg_to_D_mid (a' + 1)
    (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
        default)))
  have h_start : (default {{D}}>
      (([1, 0] : List (Fin 2))^(a' + 1) +>
        (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1
            +> default))))) =
      D_cfg (a' + 1) 0 0 1 := by
    unfold D_cfg; rfl
  rw [h_start] at h1
  have h2 : (((default <+ ([0, 1] : List (Fin 2))^(a' + 1)) <+ [0]) {{D}}>
      (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
          default))))
      [target]⊢⁺ B_mid (a' + 1) 1 0 0 := by
    unfold B_mid
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      List.append_nil, ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default]
    bb_steps
  exact ReachesStar.trans_plus h1 h2

private theorem step_D_cfg_c0_d1_bsucc (a b' : Nat) :
    (D_cfg a (b' + 1) 0 1) [target]⊢⁺ (D_cfg (a + 2) b' 1 3) := by
  have h1 := step_D_cfg_to_D_mid a
    (([1, 1, 0] : List (Fin 2))^(b' + 1) +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1
        +> default)))
  have h2 := shift_D_right_110 (b' + 1) (default <+ ([0, 1] : List (Fin 2))^a)
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +> default))
  have h3 : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b' + 1))
      <+ [0]) {{D}}>
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b') <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default)))) := by
    rw [ListBlank.append_pow_add_rev (default <+ ([0, 1] : List (Fin 2))^a)
      ([1, 1, 1] : List (Fin 2)) b' 1]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h4 := drain_A_left_111_01_with_110 a b'
    (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default))
  exact ReachesStar.trans_plus (ReachesStar.trans h1 h2) (ReachesPlus.trans h3 h4)

private theorem closes_D_cfg_c0_d1 (a b : Nat) : StepsToClosed target ps (D_cfg a b 0 1) := by
  rcases b with _ | b'
  · rcases a with _ | a'
    · exact closes_of_in_ps step_D_cfg_c0_d1_a0_b0 (by decide)
    · exact StepsToClosed.of_reachesPlus (step_D_cfg_c0_d1_asucc_b0 a')
        (closes_B_mid 0 (a' + 1) 0 0)
  · exact closes_of_in_ps (step_D_cfg_c0_d1_bsucc a b') (by decide)

private theorem step_D_cfg_c0_d3 (a b d : Nat) :
    (D_cfg a b 0 (d + 3)) [target]⊢⁺ (D_cfg (a + 2) b 0 (d + 1)) := by
  have h1 := step_D_cfg_to_D_mid a
    (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +>
        default)))
  have h2 := shift_D_right_110 b (default <+ ([0, 1] : List (Fin 2))^a)
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +> default))
  have h3 : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [0])
      {{D}}>
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +> default)))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 1) +> default)))) := by
    have hd : (([1] : List (Fin 2))^(d + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 d]
      rfl
    rw [hd, ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    simp only [list_pow_zero, ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h4 := drain_A_left_111_01_with_110 a b
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 1) +> default))
  exact ReachesStar.trans_plus (ReachesStar.trans h1 h2) (ReachesPlus.trans h3 h4)

private theorem closes_D_cfg_c0_d3 (a b d : Nat) : StepsToClosed target ps (D_cfg a b 0 (d + 3)) :=
  closes_of_in_ps (step_D_cfg_c0_d3 a b d) (by decide)

private theorem closes_D_cfg (a b c d : Nat) (hc : c <= 1) :
    StepsToClosed target ps (D_cfg a b c d) := by
  have hc_cases : c = 0 \/ c = 1 := by omega
  rcases hc_cases with rfl | rfl
  · rcases d with _ | _ | _ | d'
    · rw [D_cfg_c0_d0_eq]
      exact closes_D_cfg_c1 a b 0
    · exact closes_D_cfg_c0_d1 a b
    · rw [D_cfg_c0_d2_eq]
      exact closes_D_cfg_c1 a (b + 1) 0
    · exact closes_D_cfg_c0_d3 a b d'
  · exact closes_D_cfg_c1 a b d

private theorem init_reaches_D :
    (init []) [target]⊢* (D_cfg 0 0 0 4) := by
  have h_init : (init []) [target]⊢⁺ (D_cfg 0 0 0 4) := by
    unfold init D_cfg
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.to_star h_init

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  constructor
  · exact ⟨D_cfg 0 0 0 4, init_reaches_D, in_ps_D 0 0 0 4 (by decide)⟩
  · intro cfg h_in
    rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
    simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
    subst h_mem
    rw [eval_pat_D]
    simp only [evalVarCond] at h_cond
    exact closes_D_cfg (vars 0) (vars 1) (vars 2) (vars 3) (by omega)

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

inductive State
  | D0 (a b d : ℕ)
  | D1 (a b d : ℕ)
  | H (a b m : ℕ)
  | B (a k b d : ℕ)
  | A_pos (a k q m : ℕ)
  | A_zero (a q m : ℕ)

def start : State := .D0 0 0 4

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D0 a b d => D_cfg a b 0 d
  | .D1 a b d => D_cfg a b 1 d
  | .H a b m => H_mid a (b + 1) (m + 1)
  | .B a k b d => B_mid a (k + 1) b d
  | .A_pos a k q m => A_rem a (k + 1) q m
  | .A_zero a q m => A_rem a 0 (q + 1) m

def next : State → Option State
  | .D1 0 0 d => some (.D1 0 0 (d + 1))
  | .D1 0 (b + 1) d => some (.D1 1 b (d + 2))
  | .D1 (a + 1) b d => some (.B a 0 b d)
  | .D0 a b 0 =>
    Nat.casesOn a
      (Nat.casesOn b (some (.D1 0 0 1)) fun b => some (.D1 1 b 2))
      fun a => some (.B a 0 b 0)
  | .D0 a b 1 =>
    Nat.casesOn b
      (Nat.casesOn a (some (.D0 0 0 4)) fun a => some (.B (a + 1) 0 0 0))
      fun b => some (.D1 (a + 2) b 3)
  | .D0 a b 2 =>
    Nat.casesOn a (some (.D1 1 b 2)) fun a => some (.B a 0 (b + 1) 0)
  | .D0 a b (d + 3) => some (.D0 (a + 2) b (d + 1))
  | .H a b 0 =>
    Nat.casesOn a none fun a =>
    some (.D1 (if a = 0 then 1 else a + 1) (b + 1) 5)
  | .H a b 1 => some (.D1 (a + 2) (b + 1) 2)
  | .H a b (m + 2) =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn m (some (.D1 2 (b + 2) 3)) fun m =>
       Nat.casesOn m (some (.D1 1 (b + 3) 2)) fun m =>
       some (.D0 2 (b + 3) (m + 1)))
      fun a => some (.H a (b + 2) m)
  | .B a k (b + 1) d => some (.B a (k + 1) b (d + 2))
  | .B a 0 0 d =>
    Nat.casesOn a (some (.D0 0 0 (d + 4))) fun a =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn d (some (.D1 1 2 2)) fun d => some (.D0 2 2 (d + 1)))
      fun a => some (.H a 1 (d + 1))
  | .B a (k + 1) 0 d => some (.A_pos a k 0 (d + 3))
  | .A_zero a q m => some (.D1 (a + 2) q m)
  | .A_pos a 0 q m =>
    Nat.casesOn a none fun a =>
    Nat.casesOn q
      (some (.D1 (if a = 0 then 1 else a + 1) 0 (m + 2)))
      fun q => some (.D1 (if a = 0 then 1 else a + 1) (q + 1) (m + 2))
  | .A_pos a 1 q m =>
    Nat.casesOn a (some (.D1 1 q m)) fun a =>
    some (.A_pos a q 0 (m + 2 * q + 3))
  | .A_pos a 2 q m => some (.A_zero a q m)
  | .A_pos a (k + 3) q m => some (.A_pos a k (q + 1) m)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_D (fun s => ?_)
  match s with
  | .D1 0 0 d => exact step_D_cfg_c1_a0_b0 d
  | .D1 0 (b + 1) d => exact step_D_cfg_c1_a0_bsucc b d
  | .D1 (a + 1) b d => exact step_D_cfg_c1_asucc a b d
  | .D0 0 0 0 =>
    dsimp [next, encode]
    rw [D_cfg_c0_d0_eq]
    exact step_D_cfg_c1_a0_b0 0
  | .D0 0 (b + 1) 0 =>
    dsimp [next, encode]
    rw [D_cfg_c0_d0_eq]
    exact step_D_cfg_c1_a0_bsucc b 0
  | .D0 (a + 1) b 0 =>
    dsimp [next, encode]
    rw [D_cfg_c0_d0_eq]
    exact step_D_cfg_c1_asucc a b 0
  | .D0 0 0 1 => exact step_D_cfg_c0_d1_a0_b0
  | .D0 (a + 1) 0 1 => exact step_D_cfg_c0_d1_asucc_b0 a
  | .D0 a (b + 1) 1 => exact step_D_cfg_c0_d1_bsucc a b
  | .D0 0 b 2 =>
    dsimp [next, encode]
    rw [D_cfg_c0_d2_eq]
    exact step_D_cfg_c1_a0_bsucc b 0
  | .D0 (a + 1) b 2 =>
    dsimp [next, encode]
    rw [D_cfg_c0_d2_eq]
    exact step_D_cfg_c1_asucc a (b + 1) 0
  | .D0 a b (d + 3) => exact step_D_cfg_c0_d3 a b d
  | .H 0 b 0 =>
    obtain ⟨cfg', h1, h2⟩ := step_H_mid_a0_m1 b
    exact ⟨cfg', ReachesPlus.to_star h1, h2⟩
  | .H (a + 1) b 0 => exact step_H_mid_asucc_m1 a b
  | .H a b 1 => exact step_H_mid_m2 a b
  | .H 0 b (m + 2) =>
    obtain ⟨cfg', h1, h2⟩ := step_H_mid_a0_m3 b m
    exact ⟨cfg', ReachesPlus.to_star h1, h2⟩
  | .H 1 b 2 => exact step_H_mid_a1_m3_0 b
  | .H 1 b 3 => exact step_H_mid_a1_m3_1 b
  | .H 1 b (m + 4) => exact step_H_mid_a1_m3_succ2 b m
  | .H (a + 2) b (m + 2) => exact step_H_mid_asucc2_m3 a b m
  | .B a k (b + 1) d => exact step_B_mid_bsucc a k b d
  | .B 0 0 0 d => exact step_B_mid_a0_k1_b0 d
  | .B 1 0 0 d =>
    obtain ⟨cfg', h1, h2⟩ := step_B_mid_a1_k1_b0 d
    exact ⟨cfg', ReachesPlus.to_star h1, h2⟩
  | .B 2 0 0 0 => exact step_B_mid_a2_k1_b0_0
  | .B 2 0 0 (d + 1) => exact step_B_mid_a2_k1_b0_succ d
  | .B (a + 3) 0 0 d => exact step_B_mid_asucc3_k1_b0 a d
  | .B a (k + 1) 0 d => exact step_B_mid_ksucc2_b0 a k d
  | .A_zero a q m => exact step_A_rem_k0_qsucc a q m
  | .A_pos 0 0 q m =>
    obtain ⟨cfg', h1, h2⟩ := step_A_rem_a0_k1 q m
    exact ⟨cfg', ReachesPlus.to_star h1, h2⟩
  | .A_pos (a + 1) 0 0 m => exact step_A_rem_asucc_k1_q0 a m
  | .A_pos (a + 1) 0 (q + 1) m => exact step_A_rem_asucc_k1_qsucc a q m
  | .A_pos 0 1 q m => exact step_A_rem_a0_k2 q m
  | .A_pos (a + 1) 1 q m => exact step_A_rem_asucc_k2_to_A_rem a q m
  | .A_pos a 2 q m => exact step_A_rem_ksucc3 a 0 q m
  | .A_pos a (k + 3) q m => exact step_A_rem_ksucc3 a (k + 1) q m

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

