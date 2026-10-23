/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`
(see <https://wiki.bbchallenge.org/wiki/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC>)
(holdout #528, `suspect_25`, TMBR August 2025).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration
family
$$A(a, b) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,0^\infty$$
at $A(2, 0)$ in 15 steps. Together with the auxiliary family
$$B(a, b, c) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,110\,(1010)^c\,0^\infty,$$
every configuration advances via 7 exact Collatz-like macro-transitions, and every $B(a, b, c)$
collapses back to $A(2, b')$ in finitely many macro-steps.

## Collatz-like Acceleration Rules

```text
Consider:
A(a, b)    = 0^inf <C (10)^a 110 (10)^b 0^inf
B(a, b, c) = 0^inf <C (10)^a 110 (10)^b 110 (1010)^c 0^inf

A(a, a+d+1)   -> A(2a+2, d)
A(a, a)       -> Halt
A(b+2m+1, b)  -> A(2m+2, 2b+2)
A(b+2m+2, b)  -> B(2, 2m+1, b+1)

B(a, a+d+1, c) -> B(2a+2, d, c)
B(a, a, c)     -> A(2, 4a+2c+6)
B(b+k+1, b, c) -> A(2, 2(b+k+1)+2c+2)

Start: A(2, 0), reached after 15 raw TM steps
```

## High-Level Collatz-like Acceleration

Writing $a = 2k + 2$ ($k \ge 0$), eliminating the auxiliary family $B(a, b, c)$ via `evalB`, and
contracting the $a < b$ phases of both $A$ and $B$ via `drainA` yields a single-family, 2-counter
map $T$ on $A(k, b) := A(2k + 2, b)$ starting at $A(0, 0)$:

$$
T(A(k, b)) = \begin{cases}
  T(A(2k+2, b - 2k - 3)) & \text{if } 2k + 2 < b, \\
  \text{Halt} & \text{if } 2k + 2 = b, \\
  A\bigl(\lfloor (2k + 1 - b) / 2 \rfloor,\ 2b + 2\bigr)
    & \text{if } 2k + 2 > b \text{ and } 2k + 1 - b \text{ is even}, \\
  B\bigl(2,\ 2\lfloor (2k + 1 - b) / 2 \rfloor + 1,\ b + 1\bigr)
    & \text{if } 2k + 2 > b \text{ and } 2k + 1 - b \text{ is odd},
\end{cases}
$$

where $B(a, b, c)$ evaluates to $A(0, b')$ via:

$$
B(a, b, c) = \begin{cases}
  B(2a + 2, b - a - 1, c) & \text{if } a < b, \\
  A(0, 4a + 2c + 6) & \text{if } a = b, \\
  A(0, 2a + 2c + 2) & \text{if } a > b.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Block Algebra and Tape Normalization -/

private abbrev b10 : List (Fin 2) := [1, 0]
private abbrev b01 : List (Fin 2) := [0, 1]

local macro "norm_tape" : tactic =>
  `(tactic| simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default])

local macro "norm_cfg" : tactic =>
  `(tactic| simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default])

private theorem pow_two_mul_01 (k : ℕ) :
    b01 ^ (2 * k) = ([0, 1, 0, 1] : List (Fin 2)) ^ k :=
  list_pow_mul b01 2 k

private theorem pow_two_mul_10 (k : ℕ) :
    b10 ^ (2 * k) = ([1, 0, 1, 0] : List (Fin 2)) ^ k :=
  list_pow_mul b10 2 k

private theorem r1010_one (k : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ k) (ListBlank.cons 1 r) =
      ListBlank.cons 1 (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ k) r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    norm_tape
    rw [ih]

private theorem r01_zero (k : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (b01 ^ k) (ListBlank.cons 0 r) =
      ListBlank.cons 0 (ListBlank.append (b10 ^ k) r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    norm_tape
    rw [ih]

private theorem r10_one_default (k : ℕ) :
    ListBlank.append (b10 ^ k) (ListBlank.cons 1 default) =
      ListBlank.append (b10 ^ (k + 1)) default := by
  rw [ListBlank.append_pow_add]
  norm_tape

private theorem r_zero_10_one (k : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.cons 0 (ListBlank.append (b10 ^ k) (ListBlank.cons 1 r)) =
      ListBlank.append (b01 ^ (k + 1)) r := by
  rw [ListBlank.append_pow_add, ← r01_zero]
  norm_tape

private theorem l10_pow_succ (k : ℕ) : b10 ^ (k + 1) = 1 :: (b01 ^ k ++ [0]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [list_pow_succ, ih]
    simp only [list_pow_succ, List.cons_append, List.nil_append]

private theorem l_default_10_succ (k : ℕ) :
    ListBlank.append (b10 ^ (k + 1)) (default : ListBlank (Fin 2)) =
      ListBlank.append [1] (ListBlank.append (b01 ^ k) default) := by
  rw [l10_pow_succ, ListBlank.append_cons, ← ListBlank.append_append]
  norm_tape

/-! ## Sweep Lemmas -/

private theorem sweep_C_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (b01 ^ k) r))
      (Cfg.headRight C (ListBlank.append (b10 ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (b01 ^ (k + 1)) r))
          (Cfg.headRight C (ListBlank.append b10 l) (ListBlank.append (b01 ^ k) r)) := by
      norm_tape
      bb_steps
    have h2 := ih (ListBlank.append b10 l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (b10 ^ k) (ListBlank.append b10 l) =
          ListBlank.append (b10 ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_A_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (b01 ^ k) r))
      (Cfg.headRight A (ListBlank.append (b01 ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (b01 ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append b01 l) (ListBlank.append (b01 ^ k) r)) := by
      norm_tape
      bb_steps
    have h2 := ih (ListBlank.append b01 l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (b01 ^ k) (ListBlank.append b01 l) =
          ListBlank.append (b01 ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A (ListBlank.append (b01 ^ k) l) (ListBlank.cons 1 r))
      (Cfg.headRight A l (ListBlank.cons 1 (ListBlank.append (b10 ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A (ListBlank.append (b01 ^ (k + 1)) l) (ListBlank.cons 1 r))
          (Cfg.headRight A (ListBlank.append (b01 ^ k) l)
            (ListBlank.cons 1 (ListBlank.append b10 r))) := by
      norm_tape
      bb_steps
    have h2 := ih l (ListBlank.append b10 r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (b10 ^ k) (ListBlank.append b10 r) =
          ListBlank.append (b10 ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.cons 1 r))
      (Cfg.headRight C l
        (ListBlank.cons 1 (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) l)
            (ListBlank.cons 1 r))
          (Cfg.headRight C
            (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.cons 1 (ListBlank.append [1, 0, 1, 0] r))) := by
      norm_tape
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0, 1, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ k)
          (ListBlank.append [1, 0, 1, 0] r) =
          ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_C_left_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append [1, 1] (ListBlank.append (b01 ^ k) l))
        (ListBlank.cons 1 r))
      (Cfg.headRight C
        (ListBlank.append [1, 1] l)
        (ListBlank.cons 1 (ListBlank.append (b10 ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1, 1] (ListBlank.append (b01 ^ (k + 1)) l))
            (ListBlank.cons 1 r))
          (Cfg.headRight C
            (ListBlank.append [1, 1] (ListBlank.append (b01 ^ k) l))
            (ListBlank.cons 1 (ListBlank.append b10 r))) := by
      norm_tape
      bb_steps
    have h2 := ih l (ListBlank.append b10 r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (b10 ^ k) (ListBlank.append b10 r) =
          ListBlank.append (b10 ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-! ## Composite Macro-Transitions -/

private theorem step_T1 (i : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1] l)
        (ListBlank.append (b01 ^ (2 * i + 1)) (ListBlank.cons 0 (ListBlank.cons 0 r))))
      (Cfg.headRight A (ListBlank.append [0] l)
        (ListBlank.append (b01 ^ (2 * i + 2)) r)) := by
  have h1 := sweep_A_right (2 * i + 1) (ListBlank.append [1] l)
    (ListBlank.cons 0 (ListBlank.cons 0 r))
  have e1 :
      ListBlank.append (b01 ^ (2 * i + 1)) (ListBlank.append [1] l) =
        ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ i)
          (ListBlank.append [0, 1, 1] l) := by
    rw [list_pow_succ', ← ListBlank.append_append, pow_two_mul_01]
    rfl
  rw [e1] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ i)
            (ListBlank.append [0, 1, 1] l))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))
        (Cfg.headRight C
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ i)
            (ListBlank.append [0, 1, 1] l))
          (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left i (ListBlank.append [0, 1, 1] l) (ListBlank.cons 1 r)
  have h4 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [0, 1, 1] l)
          (ListBlank.cons 1
            (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ i) (ListBlank.cons 1 r))))
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append (b01 ^ (2 * i + 2)) r)) := by
    rw [r1010_one]
    norm_tape
    rw [pow_two_mul_01]
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus h4))

private theorem step_T2 (i : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [0, 0] l)
        (ListBlank.append (b01 ^ (2 * i + 2)) (ListBlank.cons 1 (ListBlank.cons 0 r))))
      (Cfg.headRight A l
        (ListBlank.append (b01 ^ (2 * i + 3)) (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
  have h1 := sweep_A_right (2 * i + 2) (ListBlank.append [0, 0] l)
    (ListBlank.cons 1 (ListBlank.cons 0 r))
  have h2 := sweep_A_left (2 * i + 2) (ListBlank.append [0, 0] l) (ListBlank.cons 0 r)
  have h3 :
      ReachesPlus target
        (Cfg.headRight A (ListBlank.append [0, 0] l)
          (ListBlank.cons 1 (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 0 r))))
        (Cfg.headRight A l
          (ListBlank.append (b01 ^ (2 * i + 3)) (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
    rw [r01_zero]
    norm_tape
    bb_steps
  exact h1.trans_plus (h2.trans_plus h3)

private theorem step_T1_blank (i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (2 * i + 1)) (ListBlank.cons 0 (ListBlank.cons 0 r))))
      (Cfg.headRight C default
        (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r)))) := by
  have h1 := sweep_A_right (2 * i + 1) default (ListBlank.cons 0 (ListBlank.cons 0 r))
  have e1 :
      ListBlank.append (b01 ^ (2 * i + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ i)
          (ListBlank.append [0, 1] default) := by
    rw [list_pow_succ', ← ListBlank.append_append, pow_two_mul_01]
  rw [e1] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ i)
            (ListBlank.append [0, 1] default))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))
        (Cfg.headRight C
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ i)
            (ListBlank.append [0, 1] default))
          (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left i (ListBlank.append [0, 1] default) (ListBlank.cons 1 r)
  have h4 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [0, 1] default)
          (ListBlank.cons 1
            (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ i) (ListBlank.cons 1 r))))
        (Cfg.headRight C default
          (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r)))) := by
    norm_tape
    rw [pow_two_mul_10]
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus h4))

private theorem step_E2 (p : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (2 * p + 2)) (ListBlank.cons 0 (ListBlank.cons 0 r))))
      (Cfg.headRight C default
        (ListBlank.cons 0
          (ListBlank.append (b10 ^ 2)
            (ListBlank.cons 1
              (ListBlank.append (b10 ^ (2 * p + 2)) (ListBlank.cons 1 r)))))) := by
  have h1 := sweep_A_right (2 * p + 2) default (ListBlank.cons 0 (ListBlank.cons 0 r))
  have e1 :
      ListBlank.append (b01 ^ (2 * p + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (p + 1)) default := by
    rw [show 2 * p + 2 = 2 * (p + 1) by omega, pow_two_mul_01]
  rw [e1] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (p + 1)) default)
          (ListBlank.cons 0 (ListBlank.cons 0 r)))
        (Cfg.headRight C
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (p + 1)) default)
          (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left (p + 1) default (ListBlank.cons 1 r)
  have h4 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.cons 1
            (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (p + 1))
              (ListBlank.cons 1 r))))
        (Cfg.headRight C default
          (ListBlank.cons 0
            (ListBlank.append (b10 ^ 2)
              (ListBlank.cons 1
                (ListBlank.append (b10 ^ (2 * p + 2)) (ListBlank.cons 1 r)))))) := by
    rw [show 2 * p + 2 = 2 * (p + 1) by omega, pow_two_mul_10]
    norm_tape
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus h4))

private theorem step_E1A_zero (i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (2 * i + 2)) (ListBlank.cons 0 (ListBlank.cons 0 r))))
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ 1)
          (ListBlank.cons 0
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r)))))) := by
  have h1 := sweep_A_right (2 * i + 2) default (ListBlank.cons 0 (ListBlank.cons 0 r))
  have e1 :
      ListBlank.append (b01 ^ (2 * i + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1)) default := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega, pow_two_mul_01]
  rw [e1] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1)) default)
          (ListBlank.cons 0 (ListBlank.cons 0 r)))
        (Cfg.headRight C
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1)) default)
          (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left (i + 1) default (ListBlank.cons 1 r)
  have h4 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.cons 1
            (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (i + 1))
              (ListBlank.cons 1 r))))
        (Cfg.headRight A default
          (ListBlank.append (b01 ^ 1)
            (ListBlank.cons 0
              (ListBlank.cons 0
                (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r)))))) := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega, pow_two_mul_10]
    norm_tape
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus h4))

private theorem step_E1A_succ (j i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default))
        (ListBlank.append (b01 ^ (2 * i + 2)) (ListBlank.cons 0 (ListBlank.cons 0 r))))
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (j + 2))
          (ListBlank.cons 0
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r)))))) := by
  have h1 := sweep_A_right (2 * i + 2)
    (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default))
    (ListBlank.cons 0 (ListBlank.cons 0 r))
  have e1 :
      ListBlank.append (b01 ^ (2 * i + 2))
        (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1))
          (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default)) := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega, pow_two_mul_01]
  rw [e1] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1))
            (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default)))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))
        (Cfg.headRight C
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1))
            (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default)))
          (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left (i + 1)
    (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default))
    (ListBlank.cons 1 r)
  have h4 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append (b01 ^ (j + 1)) default))
          (ListBlank.cons 1
            (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (i + 1))
              (ListBlank.cons 1 r))))
        (Cfg.headRight C
          (ListBlank.append [1, 1] (ListBlank.append (b01 ^ j) default))
          (ListBlank.cons 1
            (ListBlank.cons 0
              (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (i + 1))
                (ListBlank.cons 1 r))))) := by
    norm_tape
    bb_steps
  have h5 := sweep_C_left_11 j default
    (ListBlank.cons 0
      (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (i + 1))
        (ListBlank.cons 1 r)))
  have h6 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.cons 1
            (ListBlank.append (b10 ^ j)
              (ListBlank.cons 0
                (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (i + 1))
                  (ListBlank.cons 1 r))))))
        (Cfg.headRight A default
          (ListBlank.append (b01 ^ (j + 2))
            (ListBlank.cons 0
              (ListBlank.cons 0
                (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r)))))) := by
    rw [r01_zero, show 2 * i + 2 = 2 * (i + 1) by omega, pow_two_mul_10]
    norm_tape
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus (h4.trans (h5.trans_plus h6))))

private theorem step_E1B (i : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [0] l)
        (ListBlank.append (b01 ^ (2 * i + 2))
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 r)))))
      (Cfg.headLeft A l
        (ListBlank.cons 1
          (ListBlank.cons 0
            (ListBlank.cons 1
              (ListBlank.cons 0
                (ListBlank.append (b10 ^ (2 * i + 1))
                  (ListBlank.cons 1 (ListBlank.cons 0 r)))))))) := by
  have h1 := sweep_A_right (2 * i + 2) (ListBlank.append [0] l)
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 r)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (b01 ^ (2 * i + 2)) (ListBlank.append [0] l))
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 r))))
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (b01 ^ (2 * i + 1)) (ListBlank.append [0] l)))
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 r)))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left_11 (2 * i + 1) (ListBlank.append [0] l)
    (ListBlank.cons 1 (ListBlank.cons 0 r))
  have h4 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1, 1] (ListBlank.append [0] l))
          (ListBlank.cons 1
            (ListBlank.append (b10 ^ (2 * i + 1))
              (ListBlank.cons 1 (ListBlank.cons 0 r)))))
        (Cfg.headLeft A l
          (ListBlank.cons 1
            (ListBlank.cons 0
              (ListBlank.cons 1
                (ListBlank.cons 0
                  (ListBlank.append (b10 ^ (2 * i + 1))
                    (ListBlank.cons 1 (ListBlank.cons 0 r)))))))) := by
    norm_tape
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus h4))

private theorem step_Z (i : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1] l)
        (ListBlank.append (b01 ^ (2 * i + 2)) (ListBlank.cons 0 (ListBlank.cons 0 r))))
      (Cfg.headLeft A l
        (ListBlank.cons 1
          (ListBlank.cons 0
            (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r))))) := by
  have h1 := sweep_A_right (2 * i + 2) (ListBlank.append [1] l)
    (ListBlank.cons 0 (ListBlank.cons 0 r))
  have e1 :
      ListBlank.append (b01 ^ (2 * i + 2)) (ListBlank.append [1] l) =
        ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1))
          (ListBlank.append [1] l) := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega, pow_two_mul_01]
  rw [e1] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1))
            (ListBlank.append [1] l))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))
        (Cfg.headRight C
          (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (i + 1))
            (ListBlank.append [1] l))
          (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
    norm_tape
    bb_steps
  have h3 := sweep_C_left (i + 1) (ListBlank.append [1] l) (ListBlank.cons 1 r)
  have h4 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1] l)
          (ListBlank.cons 1
            (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ (i + 1))
              (ListBlank.cons 1 r))))
        (Cfg.headLeft A l
          (ListBlank.cons 1
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 r))))) := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega, pow_two_mul_10]
    norm_tape
    bb_steps
  exact h1.trans_plus (h2.trans (h3.trans_plus h4))

private theorem entry_succ (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C default
        (ListBlank.cons 0
          (ListBlank.append (b10 ^ (a + 1))
            (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 r))))))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ a) default))
        (ListBlank.append (b01 ^ 1) (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
  rw [r_zero_10_one]
  have h1 := sweep_C_right (a + 1 + 1) default (ListBlank.cons 1 (ListBlank.cons 0 r))
  rw [l_default_10_succ] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append (b01 ^ (a + 1)) default))
          (ListBlank.cons 1 (ListBlank.cons 0 r)))
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append (b01 ^ a) default))
          (ListBlank.append (b01 ^ 1) (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
    norm_tape
    bb_steps
  exact h1.trans_plus h2

private theorem entry_zero (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C default
        (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 r)))))
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ 1) (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
  norm_tape
  bb_steps

private theorem step_ZB (i c : ℕ) :
    ReachesPlus target
      (Cfg.headRight C default
        (ListBlank.cons 0
          (ListBlank.append (b10 ^ (2 * i + 2))
            (ListBlank.cons 1
              (ListBlank.cons 1
                (ListBlank.cons 1
                  (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default))))))))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ (2 * i + 1)) default))
        (ListBlank.append (b01 ^ (2 * c + 2)) default)) := by
  rw [r_zero_10_one]
  have h1 := sweep_C_right (2 * i + 2 + 1) default
    (ListBlank.cons 1
      (ListBlank.cons 1
        (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default))))
  rw [l_default_10_succ] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append (b01 ^ (2 * i + 2)) default))
          (ListBlank.cons 1
            (ListBlank.cons 1
              (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default)))))
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append (b01 ^ (2 * i + 1)) default))
          (ListBlank.append (b01 ^ (2 * c + 2)) default)) := by
    rw [← r01_zero (2 * c) default, ListBlank.cons_zero_default]
    norm_tape
    bb_steps
  exact h1.trans_plus h2

private def cfg_halt (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F (ListBlank.append [0] (ListBlank.append (b10 ^ (n + 1)) default)) default

private theorem halt_reach (n : ℕ) :
    ReachesPlus target
      (Cfg.headRight C default (ListBlank.append (b01 ^ (n + 1)) default))
      (cfg_halt n) := by
  have h1 := sweep_C_right (n + 1) default default
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append (b10 ^ (n + 1)) default) default)
        (cfg_halt n) := by
    unfold cfg_halt
    norm_tape
    bb_steps
  exact h1.trans_plus h2

private theorem isNone_halt (n : ℕ) : (step target (cfg_halt n)).isNone := by
  unfold cfg_halt
  bb_halt

/-! ## Inductive Loops and Canonical Pattern Set -/

/-- Canonical tape pattern
$A(a, b) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 .default))))) }

/-- Closed pattern set for `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

private def cfg_A (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default
    (ListBlank.cons 0
      (ListBlank.append (b10 ^ a)
        (ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0 (ListBlank.append (b10 ^ b) default))))))

private def cfg_B (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default
    (ListBlank.cons 0
      (ListBlank.append (b10 ^ a)
        (ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ b)
                (ListBlank.cons 1
                  (ListBlank.cons 1
                    (ListBlank.cons 0
                      (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ c)
                        default))))))))))

private theorem in_ps_A (a b : ℕ) : IsInPatternSet ps (cfg_A a b) := by
  refine ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | _ => 0, ?_, trivial⟩
  unfold cfg_A evalTapePattern pat_A evalTapeExpr b10
  rfl

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) :=
  rfl

private theorem init_reaches_A : ReachesStar target (init []) (cfg_A 2 0) := by
  have h : ReachesPlus target (init []) (cfg_A 2 0) := by
    unfold cfg_A
    norm_tape
    bb_steps
  exact h.to_star

private theorem step_T12_base (i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1] default)
        (ListBlank.append (b01 ^ (2 * i + 1))
          (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0 r))))))
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (2 * (i + 1) + 1))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
  have h1 := step_T1 i default (ListBlank.cons 1 (ListBlank.cons 0 r))
  have heq :
      ListBlank.append [0] (default : ListBlank (Fin 2)) =
        ListBlank.append [0, 0] default := by
    norm_tape
  rw [heq] at h1
  exact h1.trans (step_T2 i default r)

private theorem step_T12_succ (k i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ (k + 1)) default))
        (ListBlank.append (b01 ^ (2 * i + 1))
          (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0 r))))))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ (2 * (i + 1) + 1))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
  have h1 := step_T1 i (ListBlank.append (b01 ^ (k + 1)) default)
    (ListBlank.cons 1 (ListBlank.cons 0 r))
  have heq :
      ListBlank.append [0]
        (ListBlank.append (b01 ^ (k + 1)) (default : ListBlank (Fin 2))) =
        ListBlank.append [0, 0]
          (ListBlank.append [1] (ListBlank.append (b01 ^ k) default)) := by
    norm_tape
  rw [heq] at h1
  exact h1.trans (step_T2 i (ListBlank.append [1] (ListBlank.append (b01 ^ k) default)) r)

private theorem step_T12_iter (j k i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ (k + j)) default))
        (ListBlank.append (b01 ^ (2 * i + 1))
          (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.append (b10 ^ j) r)))))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ (2 * (i + j) + 1))
          (ListBlank.cons 0 (ListBlank.cons 0 r)))) := by
  induction j generalizing i r with
  | zero =>
    have h_k : k + 0 = k := by omega
    have h_i : i + 0 = i := by omega
    rw [h_k, h_i]
    exact ReachesStar.refl _ _
  | succ j ih =>
    have h_kj : k + (j + 1) = (k + j) + 1 := by omega
    have h_r :
        ListBlank.append (b10 ^ (j + 1)) r =
          ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.append (b10 ^ j) r)) := by
      norm_tape
    rw [h_kj, h_r]
    have h1 := (step_T12_succ (k + j) i (ListBlank.append (b10 ^ j) r)).to_star
    have h2 := ih (i + 1) r
    have h_ij : i + 1 + j = i + (j + 1) := by omega
    rw [h_ij] at h2
    exact h1.trans h2

private theorem phase1_le (a d : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C default
        (ListBlank.cons 0
          (ListBlank.append (b10 ^ a)
            (ListBlank.cons 1
              (ListBlank.cons 1
                (ListBlank.cons 0 (ListBlank.append (b10 ^ (a + d)) r)))))))
      (Cfg.headRight C default
        (ListBlank.cons 0
          (ListBlank.append (b10 ^ (2 * a + 2))
            (ListBlank.cons 1 (ListBlank.append (b10 ^ d) r))))) := by
  rcases a with _ | a'
  · rw [Nat.zero_add]
    have h1 := entry_zero (ListBlank.append (b10 ^ d) r)
    exact h1.trans (step_T1_blank 0 (ListBlank.append (b10 ^ d) r))
  · have h_entry := entry_succ a' (ListBlank.append (b10 ^ (a' + 1 + d)) r)
    have h_rhs :
        ListBlank.append (b10 ^ (a' + 1 + d)) r =
          ListBlank.append (b10 ^ a')
            (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.append (b10 ^ d) r))) := by
      have h_ad : a' + 1 + d = a' + (d + 1) := by omega
      rw [h_ad, ListBlank.append_pow_add b10 a' (d + 1) r]
      norm_tape
    have h_entry' :
        ReachesPlus target
          (Cfg.headRight C default
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (a' + 1))
                (ListBlank.cons 1
                  (ListBlank.cons 1
                    (ListBlank.cons 0 (ListBlank.append (b10 ^ (a' + 1 + d)) r)))))))
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append (b01 ^ a') default))
            (ListBlank.append (b01 ^ 1)
              (ListBlank.cons 0
                (ListBlank.cons 0
                  (ListBlank.append (b10 ^ a')
                    (ListBlank.cons 1
                      (ListBlank.cons 0 (ListBlank.append (b10 ^ d) r)))))))) := by
      rw [← h_rhs]
      exact h_entry
    have h_iter := step_T12_iter a' 0 0
      (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.append (b10 ^ d) r)))
    have h_0a : 0 + a' = a' := Nat.zero_add a'
    rw [h_0a] at h_iter
    have h12 := h_entry'.trans_star h_iter
    have h_base := step_T12_base a' (ListBlank.append (b10 ^ d) r)
    have h123 := h12.trans h_base
    exact h123.trans (step_T1_blank (a' + 1) (ListBlank.append (b10 ^ d) r))

private theorem phase1_gt (b k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C default
        (ListBlank.cons 0
          (ListBlank.append (b10 ^ (b + k + 1))
            (ListBlank.cons 1
              (ListBlank.cons 1
                (ListBlank.cons 0 (ListBlank.append (b10 ^ b) r)))))))
      (Cfg.headRight A
        (ListBlank.append [0] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ (2 * b + 2)) r)) := by
  have h_bk : b + k + 1 = (k + b) + 1 := by omega
  rw [h_bk]
  have h_entry := entry_succ (k + b) (ListBlank.append (b10 ^ b) r)
  have h_iter := step_T12_iter b k 0 r
  have h_0b : 0 + b = b := Nat.zero_add b
  rw [h_0b] at h_iter
  have h12 := h_entry.trans_star h_iter
  exact h12.trans (step_T1 b (ListBlank.append (b01 ^ k) default) r)

private theorem r_Z_simplify (i : ℕ) :
    ListBlank.cons (1 : Fin 2)
      (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * i + 2)) (ListBlank.cons 1 default))) =
      ListBlank.append (b10 ^ (2 * (i + 1) + 2)) default := by
  rw [r10_one_default (2 * i + 2)]
  have h_eq : 2 * (i + 1) + 2 = 1 + (2 * i + 2 + 1) := by omega
  rw [h_eq, ListBlank.append_pow_add b10 1 (2 * i + 2 + 1) default]
  norm_tape

private theorem r_b01_default (m : ℕ) :
    ListBlank.append (b01 ^ m) (ListBlank.cons 0 (ListBlank.cons 0 default)) =
      ListBlank.append (b01 ^ m) default := by
  norm_tape

private theorem b01_default_eq_zero_b10 (m : ℕ) :
    ListBlank.append (b01 ^ m) (default : ListBlank (Fin 2)) =
      ListBlank.cons 0 (ListBlank.append (b10 ^ m) default) := by
  rw [← r01_zero m default, ListBlank.cons_zero_default]

private theorem left_A_to_right_A_succ (k m : ℕ) :
    Cfg.headLeft A (ListBlank.append (b01 ^ (k + 1)) default)
      (ListBlank.append (b10 ^ m) default) =
      Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ m) default) := by
  rw [b01_default_eq_zero_b10 m]
  unfold Cfg.headLeft Cfg.headRight
  norm_cfg

private theorem left_A_to_right_A_zero (m : ℕ) :
    Cfg.headLeft A default (ListBlank.append (b10 ^ m) default) =
      Cfg.headRight A default (ListBlank.append (b01 ^ m) default) := by
  rw [b01_default_eq_zero_b10 m]
  unfold Cfg.headLeft Cfg.headRight
  norm_cfg

private theorem step_Z_succ (k i : ℕ) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ (k + 1)) default))
        (ListBlank.append (b01 ^ (2 * i + 2)) default))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ (2 * (i + 1) + 2)) default)) := by
  have h1 := step_Z i (ListBlank.append (b01 ^ (k + 1)) default) default
  rw [r_b01_default (2 * i + 2), r_Z_simplify i,
    left_A_to_right_A_succ k (2 * (i + 1) + 2)] at h1
  exact h1

private theorem step_Z_iter (k i : ℕ) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ (2 * i + 2)) default))
      (Cfg.headRight A (ListBlank.append [1] default)
        (ListBlank.append (b01 ^ (2 * (i + k) + 2)) default)) := by
  induction k generalizing i with
  | zero =>
    have h_i : i + 0 = i := by omega
    rw [h_i]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 := (step_Z_succ k i).to_star
    have h2 := ih (i + 1)
    have h_ik : i + 1 + k = i + (k + 1) := by omega
    rw [h_ik] at h2
    exact h1.trans h2

private theorem step_Z_base (i : ℕ) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1] default)
        (ListBlank.append (b01 ^ (2 * i + 2)) default))
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (2 * (i + 1) + 2))
          (ListBlank.cons 0 (ListBlank.cons 0 default)))) := by
  have h1 := step_Z i default default
  rw [r_b01_default (2 * i + 2), r_Z_simplify i,
    left_A_to_right_A_zero (2 * (i + 1) + 2),
    ← r_b01_default (2 * (i + 1) + 2)] at h1
  exact h1

private theorem step_E1A_all (k b : ℕ) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0] (ListBlank.append (b01 ^ k) default))
        (ListBlank.append (b01 ^ (2 * b + 2)) default))
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (k + 1))
          (ListBlank.cons 0
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (2 * b + 2)) (ListBlank.cons 1 default)))))) := by
  rcases k with _ | j
  · have h_l :
        ListBlank.append [0] (ListBlank.append (b01 ^ 0) (default : ListBlank (Fin 2))) =
          default := by
      norm_tape
    rw [h_l, ← r_b01_default (2 * b + 2)]
    exact step_E1A_zero b default
  · rw [← r_b01_default (2 * b + 2)]
    exact step_E1A_succ j b default

private theorem step_E2_to_A (p : ℕ) :
    ReachesPlus target
      (Cfg.headRight A default
        (ListBlank.append (b01 ^ (2 * p + 2))
          (ListBlank.cons 0 (ListBlank.cons 0 default))))
      (cfg_A 2 (2 * p + 2)) := by
  have h1 := step_E2 p default
  have h_r :
      ListBlank.cons (1 : Fin 2)
        (ListBlank.append (b10 ^ (2 * p + 2)) (ListBlank.cons 1 default)) =
        ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * p + 2)) default))) := by
    rw [r10_one_default (2 * p + 2)]
    norm_tape
  unfold cfg_A
  rwa [h_r] at h1

/-! ## Canonical Macro-Transition Rules on $A(a, b)$ and $B(a, b, c)$ -/

private theorem rule_A_lt (a d : ℕ) :
    ReachesPlus target (cfg_A a (a + d + 1)) (cfg_A (2 * a + 2) d) := by
  unfold cfg_A
  have h_ad : a + d + 1 = a + (d + 1) := by omega
  rw [h_ad]
  have h1 := phase1_le a (d + 1) default
  have h_r :
      ListBlank.cons (1 : Fin 2) (ListBlank.append (b10 ^ (d + 1)) default) =
        ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0 (ListBlank.append (b10 ^ d) default))) := by
    norm_tape
  rwa [h_r] at h1

private theorem rule_A_eq_halt (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a a) cfg' ∧ (step target cfg').isNone := by
  refine ⟨cfg_halt (2 * a + 2), ?_, isNone_halt (2 * a + 2)⟩
  unfold cfg_A
  have h1 := phase1_le a 0 default
  rw [Nat.add_zero] at h1
  have h_r :
      ListBlank.cons (0 : Fin 2)
        (ListBlank.append (b10 ^ (2 * a + 2))
          (ListBlank.cons 1 (ListBlank.append (b10 ^ 0) default))) =
        ListBlank.append (b01 ^ (2 * a + 2 + 1)) default := by
    change ListBlank.cons 0
      (ListBlank.append (b10 ^ (2 * a + 2)) (ListBlank.cons 1 default)) = _
    exact r_zero_10_one (2 * a + 2) default
  rw [h_r] at h1
  exact h1.trans (halt_reach (2 * a + 2))

private theorem rule_A_gt_odd (b m : ℕ) :
    ReachesPlus target (cfg_A (b + 2 * m + 1) b) (cfg_A (2 * m + 2) (2 * b + 2)) := by
  unfold cfg_A
  have h1 := phase1_gt b (2 * m) default
  have h2 := step_E1A_all (2 * m) b
  have h3 := step_T1_blank m (ListBlank.append (b10 ^ (2 * b + 2)) (ListBlank.cons 1 default))
  have h123 := (h1.trans h2).trans h3
  have h_r :
      ListBlank.cons (1 : Fin 2)
        (ListBlank.append (b10 ^ (2 * b + 2)) (ListBlank.cons 1 default)) =
        ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * b + 2)) default))) := by
    rw [r10_one_default (2 * b + 2)]
    norm_tape
  rwa [h_r] at h123

private theorem rule_A_gt_even (b m : ℕ) :
    ReachesPlus target (cfg_A (b + (2 * m + 1) + 1) b) (cfg_B 2 (2 * m + 1) (b + 1)) := by
  unfold cfg_A cfg_B
  have h1 := phase1_gt b (2 * m + 1) default
  have h2 := step_E1A_all (2 * m + 1) b
  have h3 := step_E2 m (ListBlank.append (b10 ^ (2 * b + 2)) (ListBlank.cons 1 default))
  have h123 := (h1.trans h2).trans h3
  have h_r :
      ListBlank.cons (1 : Fin 2)
        (ListBlank.append (b10 ^ (2 * m + 2))
          (ListBlank.cons 1
            (ListBlank.append (b10 ^ (2 * b + 2)) (ListBlank.cons 1 default)))) =
        ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (2 * m + 1))
                (ListBlank.cons 1
                  (ListBlank.cons 1
                    (ListBlank.cons 0
                      (ListBlank.append
                        (([1, 0, 1, 0] : List (Fin 2)) ^ (b + 1)) default))))))) := by
    have h_m : 2 * m + 2 = (2 * m + 1) + 1 := by omega
    have h_b : 2 * (b + 1) = 2 * b + 2 := by omega
    rw [← pow_two_mul_10 (b + 1), h_b, h_m, r10_one_default (2 * b + 2)]
    norm_tape
  rwa [h_r] at h123

private theorem rule_B_lt (a d c : ℕ) :
    ReachesPlus target (cfg_B a (a + d + 1) c) (cfg_B (2 * a + 2) d c) := by
  unfold cfg_B
  set r_c :=
    ListBlank.cons (1 : Fin 2)
      (ListBlank.cons 1
        (ListBlank.cons 0
          (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ c) default)))
  have h_ad : a + d + 1 = a + (d + 1) := by omega
  rw [h_ad]
  have h1 := phase1_le a (d + 1) r_c
  have h_r :
      ListBlank.cons (1 : Fin 2) (ListBlank.append (b10 ^ (d + 1)) r_c) =
        ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 0 (ListBlank.append (b10 ^ d) r_c))) := by
    norm_tape
  rwa [h_r] at h1

private theorem rule_B_eq (a c : ℕ) :
    ReachesPlus target (cfg_B a a c) (cfg_A 2 (4 * a + 2 * c + 6)) := by
  unfold cfg_B
  rw [← pow_two_mul_10 c]
  set r_c :=
    ListBlank.cons (1 : Fin 2)
      (ListBlank.cons 1
        (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default)))
  have h1 := phase1_le a 0 r_c
  rw [Nat.add_zero] at h1
  have h_zb :
      ListBlank.cons (1 : Fin 2) (ListBlank.append (b10 ^ 0) r_c) =
        ListBlank.cons 1
          (ListBlank.cons 1
            (ListBlank.cons 1
              (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default)))) :=
    rfl
  rw [h_zb] at h1
  have h2 := h1.trans (step_ZB a c)
  have h3 := h2.trans_star (step_Z_iter (2 * a + 1) c)
  have h4 := h3.trans (step_Z_base (c + (2 * a + 1)))
  have h5 := h4.trans (step_E2_to_A (c + (2 * a + 1) + 1))
  have h_eq : 2 * (c + (2 * a + 1) + 1) + 2 = 4 * a + 2 * c + 6 := by omega
  rwa [h_eq] at h5

private theorem rule_B_gt (b k c : ℕ) :
    ReachesPlus target (cfg_B (b + k + 1) b c) (cfg_A 2 (2 * (b + k + 1) + 2 * c + 2)) := by
  unfold cfg_B
  rw [← pow_two_mul_10 c]
  set r_c :=
    ListBlank.cons (1 : Fin 2)
      (ListBlank.cons 1
        (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default)))
  have h1 := phase1_gt b k r_c
  have h2 := h1.trans (step_E1B b (ListBlank.append (b01 ^ k) default)
    (ListBlank.append (b10 ^ (2 * c)) default))
  have h_e1b_r :
      ListBlank.cons (1 : Fin 2)
        (ListBlank.cons 0
          (ListBlank.cons 1
            (ListBlank.cons 0
              (ListBlank.append (b10 ^ (2 * b + 1))
                (ListBlank.cons 1
                  (ListBlank.cons 0 (ListBlank.append (b10 ^ (2 * c)) default))))))) =
        ListBlank.append (b10 ^ (2 * (b + c + 1) + 2)) default := by
    have h_eq : 2 * (b + c + 1) + 2 = 2 + ((2 * b + 1) + (1 + 2 * c)) := by omega
    rw [h_eq, ListBlank.append_pow_add b10 2 _,
      ListBlank.append_pow_add b10 (2 * b + 1) _,
      ListBlank.append_pow_add b10 1 (2 * c)]
    norm_tape
  rw [h_e1b_r] at h2
  rcases k with _ | k'
  · have h_l0 : ListBlank.append (b01 ^ 0) (default : ListBlank (Fin 2)) = default := rfl
    rw [h_l0, left_A_to_right_A_zero (2 * (b + c + 1) + 2),
      ← r_b01_default (2 * (b + c + 1) + 2)] at h2
    have h3 := h2.trans (step_E2_to_A (b + c + 1))
    have h_eq : 2 * (b + c + 1) + 2 = 2 * (b + 0 + 1) + 2 * c + 2 := by omega
    rwa [h_eq] at h3
  · rw [left_A_to_right_A_succ k' (2 * (b + c + 1) + 2)] at h2
    have h3 := h2.trans_star (step_Z_iter k' (b + c + 1))
    have h4 := h3.trans (step_Z_base ((b + c + 1) + k'))
    have h5 := h4.trans (step_E2_to_A ((b + c + 1) + k' + 1))
    have h_eq : 2 * ((b + c + 1) + k' + 1) + 2 = 2 * (b + (k' + 1) + 1) + 2 * c + 2 := by
      omega
    rwa [h_eq] at h5

private theorem step_B_reaches_A (b a c : ℕ) :
    ∃ b', ReachesPlus target (cfg_B a b c) (cfg_A 2 b') := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    have h_cmp : a < b ∨ a = b ∨ b < a := by omega
    rcases h_cmp with h_lt | rfl | h_gt
    · obtain ⟨b', h_rest⟩ := ih (b - a - 1) (by omega) (2 * a + 2)
      have h_b : b = a + (b - a - 1) + 1 := by omega
      rw [h_b]
      exact ⟨b', (rule_B_lt a (b - a - 1) c).trans h_rest⟩
    · exact ⟨4 * a + 2 * c + 6, rule_B_eq a c⟩
    · have h_a : a = b + (a - b - 1) + 1 := by omega
      rw [h_a]
      exact ⟨2 * (b + (a - b - 1) + 1) + 2 * c + 2, rule_B_gt b (a - b - 1) c⟩

private theorem step_A_all (a b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have h_cmp : a < b ∨ a = b ∨ b < a := by omega
  rcases h_cmp with h_lt | rfl | h_gt
  · have h_b : b = a + (b - a - 1) + 1 := by omega
    rw [h_b]
    exact ⟨cfg_A (2 * a + 2) (b - a - 1), rule_A_lt a (b - a - 1),
      Or.inl (in_ps_A (2 * a + 2) (b - a - 1))⟩
  · obtain ⟨cfg', h_plus, h_halt⟩ := rule_A_eq_halt a
    exact ⟨cfg', h_plus, Or.inr h_halt⟩
  · have h_par : (a - b - 1) % 2 = 0 ∨ (a - b - 1) % 2 = 1 := by omega
    rcases h_par with h_even | h_odd
    · have h_a : a = b + 2 * ((a - b - 1) / 2) + 1 := by omega
      rw [h_a]
      exact ⟨cfg_A (2 * ((a - b - 1) / 2) + 2) (2 * b + 2),
        rule_A_gt_odd b ((a - b - 1) / 2),
        Or.inl (in_ps_A (2 * ((a - b - 1) / 2) + 2) (2 * b + 2))⟩
    · have h_a : a = b + (2 * ((a - b - 1) / 2) + 1) + 1 := by omega
      rw [h_a]
      obtain ⟨b', h_to_A⟩ := step_B_reaches_A (2 * ((a - b - 1) / 2) + 1) 2 (b + 1)
      exact ⟨cfg_A 2 b', (rule_A_gt_even b ((a - b - 1) / 2)).trans h_to_A,
        Or.inl (in_ps_A 2 b')⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 2 0, init_reaches_A, in_ps_A 2 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A_all (vars 0) (vars 1)

/-- `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`. -/
inductive State where
  /-- $A(a, b) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,0^\infty$. -/
  | A (a b : ℕ)
  /-- $B(a, b, c) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,110\,(1010)^c\,0^\infty$. -/
  | B (a b c : ℕ)

/-- Initial symbolic state $A(2, 0)$, reached after 15 raw TM steps. -/
def start : State := .A 2 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b =>
    Cfg.headRight SixState.C default
      (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
          (ListBlank.cons 1
            (ListBlank.cons 1
              (ListBlank.cons 0
                (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default))))))
  | .B a b c =>
    Cfg.headRight SixState.C default
      (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
          (ListBlank.cons 1
            (ListBlank.cons 1
              (ListBlank.cons 0
                (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
                  (ListBlank.cons 1
                    (ListBlank.cons 1
                      (ListBlank.cons 0
                        (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ c)
                          default))))))))))

private theorem encode_A (a b : ℕ) : encode (.A a b) = cfg_A a b := rfl

private theorem encode_B (a b c : ℕ) : encode (.B a b c) = cfg_B a b c := rfl

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A a b =>
    if a < b then
      some (.A (2 * a + 2) (b - a - 1))
    else if a = b then
      none
    else if (a - b - 1) % 2 = 0 then
      some (.A (2 * ((a - b - 1) / 2) + 2) (2 * b + 2))
    else
      some (.B 2 (2 * ((a - b - 1) / 2) + 1) (b + 1))
  | .B a b c =>
    if a < b then
      some (.B (2 * a + 2) (b - a - 1) c)
    else if a = b then
      some (.A 2 (4 * a + 2 * c + 6))
    else
      some (.A 2 (2 * a + 2 * c + 2))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_A
  step_some := by
    rintro (⟨a, b⟩ | ⟨a, b, c⟩) s' hnext
    · simp only [next] at hnext
      split_ifs at hnext with h1 h2 h3
      · simp only [Option.some.injEq] at hnext
        subst hnext
        rw [encode_A, encode_A]
        have h_b : b = a + (b - a - 1) + 1 := by omega
        nth_rw 1 [h_b]
        exact rule_A_lt a (b - a - 1)
      · simp only [Option.some.injEq] at hnext
        subst hnext
        rw [encode_A, encode_A]
        have h_a : a = b + 2 * ((a - b - 1) / 2) + 1 := by omega
        nth_rw 1 [h_a]
        exact rule_A_gt_odd b ((a - b - 1) / 2)
      · simp only [Option.some.injEq] at hnext
        subst hnext
        rw [encode_A, encode_B]
        have h_a : a = b + (2 * ((a - b - 1) / 2) + 1) + 1 := by omega
        nth_rw 1 [h_a]
        exact rule_A_gt_even b ((a - b - 1) / 2)
    · simp only [next] at hnext
      split_ifs at hnext with h1 h2
      · simp only [Option.some.injEq] at hnext
        subst hnext
        rw [encode_B, encode_B]
        have h_b : b = a + (b - a - 1) + 1 := by omega
        nth_rw 1 [h_b]
        exact rule_B_lt a (b - a - 1) c
      · simp only [Option.some.injEq] at hnext
        subst hnext
        subst h2
        rw [encode_B, encode_A]
        exact rule_B_eq a c
      · simp only [Option.some.injEq] at hnext
        subst hnext
        rw [encode_B, encode_A]
        have h_a : a = b + (a - b - 1) + 1 := by omega
        have h_step := rule_B_gt b (a - b - 1) c
        rw [← h_a] at h_step
        exact h_step
  step_none := by
    rintro (⟨a, b⟩ | ⟨a, b, c⟩) hnext
    · simp only [next] at hnext
      split_ifs at hnext with h1 h2 h3
      subst h2
      rw [encode_A]
      obtain ⟨cfg', hp, hh⟩ := rule_A_eq_halt a
      exact ⟨cfg', hp.to_star, hh⟩
    · simp only [next] at hnext
      split_ifs at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- Single-family high-level symbolic configuration state space
$A(k, b) := 0^\infty\,{<}\mathrm{C}\,(10)^{2k+2}\,110\,(10)^b\,0^\infty$
for `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`. -/
inductive HighLevelState where
  /-- $A(k, b) := 0^\infty\,{<}\mathrm{C}\,(10)^{2k+2}\,110\,(10)^b\,0^\infty$. -/
  | A (k b : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $A(0, 0)$, corresponding to $A(2, 0)$. -/
def highLevelStart : HighLevelState := .A 0 0

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .A k b => .A (2 * k + 2) b

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Outcome of the intermediate family $B(a, b, c)$ when run until returning to $A(0, b')$. -/
def evalB (a b c : ℕ) : HighLevelState :=
  if a < b then evalB (2 * a + 2) (b - a - 1) c
  else if a = b then .A 0 (4 * a + 2 * c + 6)
  else .A 0 (2 * a + 2 * c + 2)
termination_by b
decreasing_by omega

/-- Contracted transition from $A(k, b)$ across $2k + 2 < b$ steps and $B$-sweeps. -/
def drainA (k b : ℕ) : Option HighLevelState :=
  let a := 2 * k + 2
  if a < b then drainA (2 * k + 2) (b - a - 1)
  else if a = b then none
  else if (a - b - 1) % 2 = 0 then
    some (.A ((a - b - 1) / 2) (2 * b + 2))
  else
    some (evalB 2 (2 * ((a - b - 1) / 2) + 1) (b + 1))
termination_by b
decreasing_by omega

/-- High-level accelerated Collatz-like transition function on $A(k, b)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .A k b => drainA k b

private theorem stepsTo_evalB (a b c : ℕ) :
    CollatzStepsTo next (.B a b c) (some (toState (evalB a b c))) := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    rw [evalB]
    split_ifs with hlt heq
    · have h1 : next (.B a b c) = some (.B (2 * a + 2) (b - a - 1) c) := by
        simp [next, hlt]
      exact CollatzStepsTo.head h1 (ih (b - a - 1) (by omega) (2 * a + 2))
    · refine CollatzStepsTo.of_eq ?_
      simp [next, heq, toState]
    · refine CollatzStepsTo.of_eq ?_
      simp [next, hlt, heq, toState]

private theorem stepsTo_drainA (k b : ℕ) :
    CollatzStepsTo next (toState (.A k b)) ((drainA k b).map toState) := by
  induction b using Nat.strongRecOn generalizing k with
  | ind b ih =>
    rw [drainA]
    split_ifs with hlt heq hpar
    · have h1 :
          next (toState (.A k b)) =
            some (toState (.A (2 * k + 2) (b - (2 * k + 2) - 1))) := by
        simp [toState, next, hlt]
      exact CollatzStepsTo.head h1 (ih (b - (2 * k + 2) - 1) (by omega) (2 * k + 2))
    · refine CollatzStepsTo.of_eq ?_
      simp [toState, next, heq]
    · refine CollatzStepsTo.of_eq ?_
      simp [toState, next, hlt, heq, hpar]
    · have h1 :
          next (toState (.A k b)) =
            some (.B 2 (2 * ((2 * k + 2 - b - 1) / 2) + 1) (b + 1)) := by
        simp [toState, next, hlt, heq, hpar]
      simpa only [Option.map_some] using
        CollatzStepsTo.head h1 (stepsTo_evalB 2 (2 * ((2 * k + 2 - b - 1) / 2) + 1) (b + 1))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨k, b⟩
  exact stepsTo_drainA k b

/-- `target` halts from the blank tape if and only if the high-level acceleration `highLevelNext`
halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` if and only if the high-level acceleration
`highLevelNext` halts from `highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC
