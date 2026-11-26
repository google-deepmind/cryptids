/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`
(see <https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps>)
(holdout #634 (suspect_112, listed on User:RobinCodes/Next_Steps)).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(k, a, b) := 0^\infty\,(10101)^k\,\mathrm{C}{>}\,0\,1\,0\,1^a\,0\,1^b\,0^\infty$$
at $C(0, 2, 0)$ in 10 steps, and every $C(k, a, b)$ advances in `ReachesPlus` either to another
$C(k', a', b')$ or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
C(k, a, b) = 0^inf (10101)^k C> 0 1 0 1^a 0 1^b 0^inf

Helper drainB(b, w):
  drainB(0, w)        = (w + 1, 0)
  drainB(2m + 2, w)   = (5m + w + 6, 0)
  drainB(1, w)        = (w + 1, 0)
  drainB(3, w)        = (w + 1, 1)
  drainB(5, w)        = Halt
  drainB(6q + 7, w)   = (6q + w + 7, 0)
  drainB(6q + 9, w)   = (5q + w + 6, q + 2)
  drainB(6q + 11, w)  = drainB(q, 5q + w + 12)

Accelerated transitions:
  C(k, 0, b)          -> Halt
  C(k, 1, 0)          -> Halt
  C(k, 1, 1)          -> Halt
  C(k, 1, b + 2)      -> C(0, a', b')     if drainB(b, 5k + 7) = (a', b'), else Halt
  C(k, 2, 0)          -> C(0, 5k + 6, 0)
  C(k, 2, 2)          -> C(0, 5k + 6, 1)
  C(k, 2, 2m + 4)     -> C(k + 1, 2m + 1, 1)
  C(k, 2, 2m + 1)     -> C(k + 1, 2m + 2, 0)
  C(k, 2n + 4, b)     -> C(k + 1, a', b') if drainB(b, 2n + 1) = (a', b'), else Halt
  C(k, 3, b)          -> C(0, 5k + b + 6, 0)
  C(k, 5, b)          -> C(0, 5k + 6, b + 1)
  C(k, 2n + 7, b)     -> C(k + 1, 2n + 1, b + 1)

Start: C(0, 2, 0), reached after 10 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Left-Tape Block Stack and Sweep Lemmas -/

/-- Symbolic block types accumulated on the left half-tape before an `E`-sweep. -/
private inductive EBlock where
  | b1
  | b01
  | b10101

/-- Decode a list of `EBlock`s on top of base left half-tape `L`. -/
@[simp]
private def e_tape (L : ListBlank (Fin 2)) : List EBlock → ListBlank (Fin 2)
  | [] => ListBlank.append [0, 0] L
  | .b1 :: xs => ListBlank.append [1] (e_tape L xs)
  | .b01 :: xs => ListBlank.append [0, 1] (e_tape L xs)
  | .b10101 :: xs => ListBlank.append [1, 0, 1, 0, 1] (e_tape L xs)

/-- Prepend `m` copies of `.b01` to an `EBlock` list. -/
@[simp]
private def add_b01 : ℕ → List EBlock → List EBlock
  | 0, xs => xs
  | m + 1, xs => .b01 :: add_b01 m xs

/-- Prepend `m` copies of `.b10101` to an `EBlock` list. -/
@[simp]
private def add_b10101 : ℕ → List EBlock → List EBlock
  | 0, xs => xs
  | m + 1, xs => .b10101 :: add_b10101 m xs

/-- Number of `1`s added to the right half-tape when state `E` sweeps across an `EBlock` list. -/
@[simp]
private def eblockWeight : List EBlock → ℕ
  | [] => 1
  | .b1 :: xs => eblockWeight xs + 1
  | .b01 :: xs => eblockWeight xs + 2
  | .b10101 :: xs => eblockWeight xs + 5

private theorem add_b01_cons (m : ℕ) (xs : List EBlock) :
    add_b01 m (.b01 :: xs) = .b01 :: add_b01 m xs := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (EBlock.b01 :: ·) ih

private theorem add_b10101_cons (m : ℕ) (xs : List EBlock) :
    add_b10101 m (.b10101 :: xs) = .b10101 :: add_b10101 m xs := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (EBlock.b10101 :: ·) ih

private theorem eblockWeight_add_b01 (m : ℕ) (xs : List EBlock) :
    eblockWeight (add_b01 m xs) = 2 * m + eblockWeight xs := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [add_b01, eblockWeight, ih]
    omega

private theorem eblockWeight_add_b10101 (m : ℕ) (xs : List EBlock) :
    eblockWeight (add_b10101 m xs) = 5 * m + eblockWeight xs := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [add_b10101, eblockWeight, ih]
    omega

private theorem e_tape_default_b10101 (k : ℕ) :
    e_tape default (add_b10101 k []) =
      ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [add_b10101, e_tape]
    rw [ih, ← ListBlank.append_pow_succ]

private theorem append_10101_pow (k : ℕ) :
    ListBlank.append [1, 0, 1, 0, 1]
      (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default) =
    ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default :=
  (ListBlank.append_pow_succ ([1, 0, 1, 0, 1] : List (Fin 2)) k default).symm

/-- Rightward shift across `1^{2m}` in state `A`, pushing `m` `.b01` blocks onto `e_tape`. -/
private theorem shift_A_11_eblock (m : ℕ) (L : ListBlank (Fin 2)) (xs : List EBlock)
    (r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A (e_tape L xs)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) r))
      (Cfg.headRight A (e_tape L (add_b01 m xs)) r) := by
  induction m generalizing xs r with
  | zero => exact ReachesStar.refl _ _
  | succ m ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A (e_tape L xs)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (m + 1))) r))
          (Cfg.headRight A (e_tape L (.b01 :: xs))
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) r)) := by
      have h_mul : 2 * (m + 1) = 2 + 2 * m := by omega
      rw [h_mul, ListBlank.append_pow_add]
      simp only [e_tape, list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih (.b01 :: xs) r
    rw [add_b01_cons] at h2
    exact (h1.trans_star h2).to_star

/-- Full leftward `E`-sweep across `e_tape L xs`, adding `eblockWeight xs` to the right `1`-run. -/
private theorem sweep_E_tape (xs : List EBlock) (L : ListBlank (Fin 2)) (a : ℕ)
    (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (e_tape L xs)
        (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) r)))
      (Cfg.headRight C L
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + eblockWeight xs)) r))) := by
  induction xs generalizing a with
  | nil =>
    have h_add : a + eblockWeight [] = 1 + a := by simp [Nat.add_comm]
    rw [h_add, ListBlank.append_pow_add]
    simp only [e_tape, list_pow_one]
    bb_steps
  | cons blk xs ih =>
    cases blk with
    | b1 =>
      have h1 :
          ReachesPlus target
            (Cfg.headRight E (e_tape L (.b1 :: xs))
              (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) r)))
            (Cfg.headRight E (e_tape L xs)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) r))) := by
        have h_add : a + 1 = 1 + a := by omega
        rw [h_add, ListBlank.append_pow_add]
        simp only [e_tape, list_pow_one]
        bb_steps
      have h2 := ih (a + 1)
      have h_eq : a + 1 + eblockWeight xs = a + eblockWeight (.b1 :: xs) := by
        simp only [eblockWeight]
        omega
      rw [h_eq] at h2
      exact h1.trans h2
    | b01 =>
      have h1 :
          ReachesPlus target
            (Cfg.headRight E (e_tape L (.b01 :: xs))
              (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) r)))
            (Cfg.headRight E (e_tape L xs)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) r))) := by
        have h_add : a + 2 = 2 + a := by omega
        rw [h_add, ListBlank.append_pow_add]
        simp only [e_tape, list_pow_succ, list_pow_zero]
        bb_steps
      have h2 := ih (a + 2)
      have h_eq : a + 2 + eblockWeight xs = a + eblockWeight (.b01 :: xs) := by
        simp only [eblockWeight]
        omega
      rw [h_eq] at h2
      exact h1.trans h2
    | b10101 =>
      have h1 :
          ReachesPlus target
            (Cfg.headRight E (e_tape L (.b10101 :: xs))
              (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) r)))
            (Cfg.headRight E (e_tape L xs)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) r))) := by
        have h_add : a + 5 = 5 + a := by omega
        rw [h_add, ListBlank.append_pow_add]
        simp only [e_tape, list_pow_succ, list_pow_zero]
        bb_steps
      have h2 := ih (a + 5)
      have h_eq : a + 5 + eblockWeight xs = a + eblockWeight (.b10101 :: xs) := by
        simp only [eblockWeight]
        omega
      rw [h_eq] at h2
      exact h1.trans h2

/-- Bounce from state `B` across `1^{2m+2} 0^\infty`. -/
private theorem bounce_B_even (m : ℕ) (L : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B L
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2)) default))
      (Cfg.headRight C L
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight B L
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2)) default))
        (Cfg.headRight A (e_tape L [])
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) default)) := by
    have h_add : 2 * m + 2 = 2 + 2 * m := by omega
    rw [h_add, ListBlank.append_pow_add]
    simp only [e_tape, list_pow_succ, list_pow_zero]
    bb_steps
  have h2 := shift_A_11_eblock m L [] default
  have h3 :
      ReachesPlus target
        (Cfg.headRight A (e_tape L (add_b01 m [])) default)
        (Cfg.headRight E (e_tape L (add_b01 m []))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
    simp only [list_pow_zero, list_pow_one]
    bb_steps
  have h4 := sweep_E_tape (add_b01 m []) L 1
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
  have h_w : 1 + eblockWeight (add_b01 m []) = 2 * m + 2 := by
    simp only [eblockWeight_add_b01, eblockWeight]
    omega
  rw [h_w] at h4
  exact ((h1.trans_star h2).trans h3).trans h4

/-- Bounce from state `B` across `1^{2m+5} 0^\infty`. -/
private theorem bounce_B_odd (m : ℕ) (L : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B L
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 5)) default))
      (Cfg.headRight C L
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight B L
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 5)) default))
        (Cfg.headRight A (e_tape L [])
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m))
            (ListBlank.append [1, 1, 1] default))) := by
    have h_eq : 2 * m + 5 = 2 + (2 * m + 3) := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * m + 3),
      ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * m) 3]
    simp only [e_tape, list_pow_succ, list_pow_zero]
    bb_steps
  have h2 := shift_A_11_eblock m L [] (ListBlank.append [1, 1, 1] default)
  have h3 :
      ReachesPlus target
        (Cfg.headRight A (e_tape L (add_b01 m [])) (ListBlank.append [1, 1, 1] default))
        (Cfg.headRight E (e_tape L (add_b01 m []))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))))) := by
    simp only [list_pow_zero, list_pow_one]
    bb_steps
  have h4 := sweep_E_tape (add_b01 m []) L 0
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
  have h_w : 0 + eblockWeight (add_b01 m []) = 2 * m + 1 := by
    simp only [eblockWeight_add_b01, eblockWeight, Nat.zero_add]
  rw [h_w] at h4
  exact ((h1.trans_star h2).trans h3).trans h4

/-- Odd step from state `C` with `a = 2m + 7`: pushes `10101` to `L`, reduces `a` by 6,
and increments `b`. -/
private theorem step_C_odd_ge7 (m : ℕ) (L : ListBlank (Fin 2)) (b : ℕ) :
    ReachesPlus target
      (Cfg.headRight C L
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 7))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))
      (Cfg.headRight C (ListBlank.append [1, 0, 1, 0, 1] L)
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C L
          (ListBlank.append [0, 1, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 7))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))
        (Cfg.headRight A (e_tape (ListBlank.append [1, 0, 1, 0, 1] L) [])
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m))
            (ListBlank.append [1, 1, 1, 0]
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
    have h_eq : 2 * m + 7 = 4 + (2 * m + 3) := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (2 * m + 3),
      ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * m) 3]
    simp only [e_tape, list_pow_succ, list_pow_zero]
    bb_steps
  have h2 := shift_A_11_eblock m (ListBlank.append [1, 0, 1, 0, 1] L) []
    (ListBlank.append [1, 1, 1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
  have h3 :
      ReachesPlus target
        (Cfg.headRight A (e_tape (ListBlank.append [1, 0, 1, 0, 1] L) (add_b01 m []))
          (ListBlank.append [1, 1, 1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
        (Cfg.headRight E (e_tape (ListBlank.append [1, 0, 1, 0, 1] L) (add_b01 m []))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
    simp only [list_pow_zero]
    bb_steps
  have h4 := sweep_E_tape (add_b01 m []) (ListBlank.append [1, 0, 1, 0, 1] L) 0
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))
  have h_w : 0 + eblockWeight (add_b01 m []) = 2 * m + 1 := by
    simp only [eblockWeight_add_b01, eblockWeight, Nat.zero_add]
  rw [h_w] at h4
  exact ((h1.trans_star h2).trans h3).trans h4

/-- Even step from state `C` with `a = 2m + 4, b = 0`: pushes `10101` to `L`, reduces `a` by 2. -/
private theorem step_C_even_b0 (m : ℕ) (L : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C L
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 4))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))))
      (Cfg.headRight C (ListBlank.append [1, 0, 1, 0, 1] L)
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C L
          (ListBlank.append [0, 1, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))))
        (Cfg.headRight A (e_tape (ListBlank.append [1, 0, 1, 0, 1] L) [])
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) default)) := by
    have h_add : 2 * m + 4 = 4 + 2 * m := by omega
    rw [h_add, ListBlank.append_pow_add]
    simp only [e_tape, list_pow_succ, list_pow_zero]
    bb_steps
  have h2 := shift_A_11_eblock m (ListBlank.append [1, 0, 1, 0, 1] L) [] default
  have h3 :
      ReachesPlus target
        (Cfg.headRight A (e_tape (ListBlank.append [1, 0, 1, 0, 1] L) (add_b01 m [])) default)
        (Cfg.headRight E (e_tape (ListBlank.append [1, 0, 1, 0, 1] L) (add_b01 m []))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
    simp only [list_pow_zero, list_pow_one]
    bb_steps
  have h4 := sweep_E_tape (add_b01 m []) (ListBlank.append [1, 0, 1, 0, 1] L) 1
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
  have h_w : 1 + eblockWeight (add_b01 m []) = 2 * m + 2 := by
    simp only [eblockWeight_add_b01, eblockWeight]
    omega
  rw [h_w] at h4
  exact ((h1.trans_star h2).trans h3).trans h4

/-- Iterate `step_C_even_b0` `m` times, reducing `a = 2m + 2` to `2`. -/
private theorem loop_C_even_b0 (m : ℕ) (L : ListBlank (Fin 2)) (xs : List EBlock) :
    ReachesStar target
      (Cfg.headRight C (e_tape L xs)
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))))
      (Cfg.headRight C (e_tape L (add_b10101 m xs))
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
  induction m generalizing xs with
  | zero => exact ReachesStar.refl _ _
  | succ m ih =>
    have h_idx : 2 * (m + 1) + 2 = 2 * m + 4 := by omega
    rw [h_idx]
    have h1 := step_C_even_b0 m (e_tape L xs)
    have h2 := ih (.b10101 :: xs)
    rw [add_b10101_cons] at h2
    exact (h1.trans_star h2).to_star

/-- Iterate `step_C_odd_ge7` `q` times, reducing `a = 2(r_rem + 3q) + 3` to `2*r_rem + 3`. -/
private theorem loop_C_odd_ge7 (q r_rem : ℕ) (L : ListBlank (Fin 2)) (xs : List EBlock) (b : ℕ) :
    ReachesStar target
      (Cfg.headRight C (e_tape L xs)
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (r_rem + 3 * q) + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))
      (Cfg.headRight C (e_tape L (add_b10101 q xs))
        (ListBlank.append [0, 1, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * r_rem + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (b + q)) default))))) := by
  induction q generalizing xs b with
  | zero => exact ReachesStar.refl _ _
  | succ q ih =>
    have h_idx1 : 2 * (r_rem + 3 * (q + 1)) + 3 = 2 * (r_rem + 3 * q + 1) + 7 := by omega
    have h_idx2 : 2 * (r_rem + 3 * q + 1) + 1 = 2 * (r_rem + 3 * q) + 3 := by omega
    rw [h_idx1]
    have h1 := step_C_odd_ge7 (r_rem + 3 * q + 1) (e_tape L xs) b
    rw [h_idx2] at h1
    have h2 := ih (.b10101 :: xs) (b + 1)
    rw [add_b10101_cons] at h2
    have h_b : b + 1 + q = b + (q + 1) := by omega
    rw [h_b] at h2
    exact (h1.trans_star h2).to_star

/-- Compute the resulting `(a', b')` parameters after draining `1^b` in state `B` with left-tape
block weight `w = eblockWeight xs`, or `none` if the drain halts. -/
def drainB (b w : ℕ) : Option (ℕ × ℕ) :=
  if b % 2 = 0 then
    if b = 0 then some (w + 1, 0)
    else some (5 * (b / 2 - 1) + w + 6, 0)
  else if b = 1 then some (w + 1, 0)
  else if b = 3 then some (w + 1, 1)
  else if b = 5 then none
  else
    let m := b / 2 - 3
    let q := m / 3
    if m % 3 = 0 then some (6 * q + w + 7, 0)
    else if m % 3 = 1 then some (5 * q + w + 6, q + 2)
    else drainB q (5 * q + w + 12)
termination_by b

private theorem B_drain (b : ℕ) (L : ListBlank (Fin 2)) (xs : List EBlock) :
    match drainB b (eblockWeight xs) with
    | some (a', b') =>
      ReachesPlus target
        (Cfg.headRight B (e_tape L (.b1 :: xs))
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
        (Cfg.headRight C L
          (ListBlank.append [0, 1, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ a')
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ b') default)))))
    | none =>
      ∃ cfg',
        ReachesPlus target
          (Cfg.headRight B (e_tape L (.b1 :: xs))
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
          cfg' ∧
        (step target cfg').isNone := by
  refine Nat.strong_induction_on b (fun b ih => ?_) L xs
  clear L xs
  intro L xs
  rcases nat_even_or_odd_two_mul b with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases m with _ | m'
    · rw [drainB]
      simp only [Nat.mul_zero, ↓reduceIte]
      have h1 :
          ReachesPlus target
            (Cfg.headRight B (e_tape L (.b1 :: xs))
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
            (Cfg.headRight E (e_tape L xs)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
        simp only [e_tape, list_pow_zero, list_pow_one]
        bb_steps
      have h2 := sweep_E_tape xs L 1
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
      rw [Nat.add_comm 1 (eblockWeight xs)] at h2
      exact h1.trans h2
    · have h_b : 2 * (m' + 1) = 2 * m' + 2 := by omega
      rw [h_b, drainB]
      have h_mod : (2 * m' + 2) % 2 = 0 := by omega
      have h_ne : 2 * m' + 2 ≠ 0 := by omega
      have h_div : (2 * m' + 2) / 2 - 1 = m' := by omega
      simp only [h_mod, h_ne, h_div, ↓reduceIte]
      have h1 := bounce_B_even m' (e_tape L (.b1 :: xs))
      have h2 := loop_C_even_b0 m' L (.b1 :: xs)
      have h3 :
          ReachesPlus target
            (Cfg.headRight C (e_tape L (add_b10101 m' (.b1 :: xs)))
              (ListBlank.append [0, 1, 0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 2)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))))
            (Cfg.headRight E (e_tape L (.b10101 :: add_b10101 m' (.b1 :: xs)))
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
        simp only [e_tape, list_pow_zero, list_pow_succ]
        bb_steps
      have h4 := sweep_E_tape (.b10101 :: add_b10101 m' (.b1 :: xs)) L 0
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
      have h_w :
          0 + eblockWeight (.b10101 :: add_b10101 m' (.b1 :: xs)) =
            5 * m' + eblockWeight xs + 6 := by
        simp only [eblockWeight, eblockWeight_add_b10101]
        omega
      rw [h_w] at h4
      exact ((h1.trans_star h2).trans h3).trans h4
  · rcases m with _ | _ | _ | m'
    · rw [drainB]
      simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte]
      have h1 :
          ReachesPlus target
            (Cfg.headRight B (e_tape L (.b1 :: xs))
              (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
            (Cfg.headRight E (e_tape L xs)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
        simp only [e_tape, list_pow_zero, list_pow_one]
        bb_steps
      have h2 := sweep_E_tape xs L 1
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
      rw [Nat.add_comm 1 (eblockWeight xs)] at h2
      exact h1.trans h2
    · rw [drainB]
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
      have h1 :
          ReachesPlus target
            (Cfg.headRight B (e_tape L (.b1 :: xs))
              (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
            (Cfg.headRight E (e_tape L xs)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))))) := by
        simp only [e_tape, list_pow_zero, list_pow_succ]
        bb_steps
      have h2 := sweep_E_tape xs L 1
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
      rw [Nat.add_comm 1 (eblockWeight xs)] at h2
      exact h1.trans h2
    · rw [drainB]
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
      refine ⟨Cfg.headRight F
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1] (e_tape L (.b1 :: xs))) default, ?_, by bb_halt⟩
      simp only [e_tape, list_pow_zero, list_pow_succ]
      bb_steps
    · have h_b : 2 * (m' + 3) + 1 = 2 * (m' + 1) + 5 := by omega
      have h_mod2 : (2 * (m' + 3) + 1) % 2 = 1 := by omega
      have h_ne1 : 2 * (m' + 3) + 1 ≠ 1 := by omega
      have h_ne3 : 2 * (m' + 3) + 1 ≠ 3 := by omega
      have h_ne5 : 2 * (m' + 3) + 1 ≠ 5 := by omega
      have h_div2 : (2 * (m' + 3) + 1) / 2 - 3 = m' := by omega
      rw [drainB]
      simp only [h_mod2, h_ne1, h_ne3, h_ne5, h_div2, Nat.reduceEqDiff, ↓reduceIte]
      have h1 := bounce_B_odd (m' + 1) (e_tape L (.b1 :: xs))
      rw [← h_b] at h1
      have h_div : m' % 3 = 0 ∨ m' % 3 = 1 ∨ m' % 3 = 2 := by omega
      let q := m' / 3
      rcases h_div with h_r0 | h_r1 | h_r2
      · simp only [h_r0, ↓reduceIte]
        have h_m : 2 * (m' + 1) + 1 = 2 * (0 + 3 * q) + 3 := by omega
        rw [h_m] at h1
        have h2 := loop_C_odd_ge7 q 0 L (.b1 :: xs) 1
        have h3 :
            ReachesPlus target
              (Cfg.headRight C (e_tape L (add_b10101 q (.b1 :: xs)))
                (ListBlank.append [0, 1, 0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (2 * 0 + 3))
                    (ListBlank.append [0]
                      (ListBlank.append (([1] : List (Fin 2)) ^ (1 + q)) default)))))
              (Cfg.headRight E (e_tape L (.b10101 :: add_b10101 q (.b1 :: xs)))
                (ListBlank.append [0, 1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (1 + q))
                    (ListBlank.append [0]
                      (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
          simp only [e_tape, list_pow_zero, list_pow_succ]
          bb_steps
        have h4 := sweep_E_tape (.b10101 :: add_b10101 q (.b1 :: xs)) L (1 + q)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
        have h_w :
            1 + q + eblockWeight (.b10101 :: add_b10101 q (.b1 :: xs)) =
              6 * q + eblockWeight xs + 7 := by
          simp only [eblockWeight, eblockWeight_add_b10101]
          omega
        rw [h_w] at h4
        exact ((h1.trans_star h2).trans h3).trans h4
      · simp only [h_r1, Nat.reduceEqDiff, ↓reduceIte]
        have h_m : 2 * (m' + 1) + 1 = 2 * (1 + 3 * q) + 3 := by omega
        rw [h_m] at h1
        have h2 := loop_C_odd_ge7 q 1 L (.b1 :: xs) 1
        have h3 :
            ReachesPlus target
              (Cfg.headRight C (e_tape L (add_b10101 q (.b1 :: xs)))
                (ListBlank.append [0, 1, 0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (2 * 1 + 3))
                    (ListBlank.append [0]
                      (ListBlank.append (([1] : List (Fin 2)) ^ (1 + q)) default)))))
              (Cfg.headRight E (e_tape L (.b10101 :: add_b10101 q (.b1 :: xs)))
                (ListBlank.append [0, 1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                    (ListBlank.append [0]
                      (ListBlank.append (([1] : List (Fin 2)) ^ (q + 2)) default))))) := by
          have h_q : q + 2 = 1 + (1 + q) := by omega
          rw [h_q, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (1 + q)]
          simp only [e_tape, list_pow_zero, list_pow_succ]
          bb_steps
        have h4 := sweep_E_tape (.b10101 :: add_b10101 q (.b1 :: xs)) L 0
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (q + 2)) default))
        have h_w :
            0 + eblockWeight (.b10101 :: add_b10101 q (.b1 :: xs)) =
              5 * q + eblockWeight xs + 6 := by
          simp only [eblockWeight, eblockWeight_add_b10101]
          omega
        rw [h_w] at h4
        exact ((h1.trans_star h2).trans h3).trans h4
      · simp only [h_r2, Nat.reduceEqDiff, ↓reduceIte]
        have h_m : 2 * (m' + 1) + 1 = 2 * (2 + 3 * q) + 3 := by omega
        rw [h_m] at h1
        have h2 := loop_C_odd_ge7 q 2 L (.b1 :: xs) 1
        have h3 := step_C_odd_ge7 0 (e_tape L (add_b10101 q (.b1 :: xs))) (1 + q)
        have h4 :
            ReachesPlus target
              (Cfg.headRight C (e_tape L (.b10101 :: add_b10101 q (.b1 :: xs)))
                (ListBlank.append [0, 1, 0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                    (ListBlank.append [0]
                      (ListBlank.append (([1] : List (Fin 2)) ^ (q + 2)) default)))))
              (Cfg.headRight B
                (e_tape L (.b1 :: .b01 :: .b01 :: .b01 :: .b10101 :: add_b10101 q (.b1 :: xs)))
                (ListBlank.append (([1] : List (Fin 2)) ^ q) default)) := by
          have h_q : q + 2 = 2 + q := by omega
          rw [h_q, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 q]
          simp only [e_tape, list_pow_zero, list_pow_succ]
          bb_steps
        have h_q_eq : 1 + q + 1 = q + 2 := by omega
        rw [h_q_eq] at h3
        have h_pre := (((h1.trans_star h2).trans h3).trans h4)
        have h_lt : q < 2 * (m' + 3) + 1 := by omega
        let xs' := .b01 :: .b01 :: .b01 :: .b10101 :: add_b10101 q (.b1 :: xs)
        have h_ih := ih q h_lt L xs'
        have h_w : eblockWeight xs' = 5 * q + eblockWeight xs + 12 := by
          simp only [xs', eblockWeight, eblockWeight_add_b10101]
          omega
        rw [h_w] at h_ih
        rcases h_d : drainB q (5 * q + eblockWeight xs + 12) with _ | ⟨a', b'⟩
        · rw [h_d] at h_ih
          obtain ⟨cfg', h_halt, h_none⟩ := h_ih
          exact ⟨cfg', h_pre.trans h_halt, h_none⟩
        · rw [h_d] at h_ih
          exact h_pre.trans h_ih

/-! ## Canonical Pattern Set (Level A) -/

/-- Canonical tape pattern
$C(k, a, b) := 0^\infty\,(10101)^k\,\mathrm{C}{>}\,0\,1\,0\,1^a\,0\,1^b\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1, 0, 1, 0, 1] 0 .default
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 .default))))) }

/-- Closed pattern set for `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Configuration $C(k, a, b)$. -/
def cfg_C (k a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default)
    (ListBlank.append [0, 1, 0]
      (ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_C (k a b : ℕ) : IsInPatternSet ps (cfg_C k a b) :=
  ⟨(pat_C, .true), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => a | 2 => b | _ => 0, rfl, trivial⟩

/-! ## Collatz-Like Acceleration (Level B) and Transition Proofs -/

/-- Symbolic configuration state space for `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`. -/
inductive State where
  /-- $C(k, a, b) := 0^\infty\,(10101)^k\,\mathrm{C}{>}\,0\,1\,0\,1^a\,0\,1^b\,0^\infty$. -/
  | C (k a b : ℕ)

/-- Initial symbolic state $C(0, 2, 0)$, reached after 10 raw TM steps. -/
def start : State := .C 0 2 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C k a b => cfg_C k a b

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C k a b =>
    if a % 2 = 0 then
      if a = 0 then none
      else if a = 2 then
        if b % 2 = 0 then
          if b = 0 then some (.C 0 (5 * k + 6) 0)
          else if b = 2 then some (.C 0 (5 * k + 6) 1)
          else some (.C (k + 1) (b - 3) 1)
        else some (.C (k + 1) (b + 1) 0)
      else
        match drainB b (a - 3) with
        | some (a', b') => some (.C (k + 1) a' b')
        | none => none
    else if a = 1 then
      if b = 0 then none
      else if b = 1 then none
      else
        match drainB (b - 2) (5 * k + 7) with
        | some (a', b') => some (.C 0 a' b')
        | none => none
    else if a = 3 then some (.C 0 (5 * k + b + 6) 0)
    else if a = 5 then some (.C 0 (5 * k + 6) (b + 1))
    else some (.C (k + 1) (a - 6) (b + 1))

private theorem step_C_a0 (k b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C k 0 b) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 0, 1]
      (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default))
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)),
    ?_, by bb_halt⟩
  unfold cfg_C
  simp only [list_pow_zero]
  bb_steps

private theorem step_C_a1_b0 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C k 1 0) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 0, 1, 0, 1]
      (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default))
    default, ?_, by bb_halt⟩
  unfold cfg_C
  simp only [list_pow_zero, list_pow_one]
  bb_steps

private theorem step_C_a1_b1 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C k 1 1) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1]
      (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default))
    default, ?_, by bb_halt⟩
  unfold cfg_C
  simp only [list_pow_one]
  bb_steps

private theorem step_state (k a b : ℕ) :
    match next (.C k a b) with
    | some s' => ReachesPlus target (encode (.C k a b)) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode (.C k a b)) cfg' ∧ (step target cfg').isNone := by
  rcases nat_even_or_odd_two_mul a with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rcases n with _ | _ | n'
    · simp only [next, Nat.mul_zero, ↓reduceIte]
      exact step_C_a0 k b
    · rcases nat_even_or_odd_two_mul b with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rcases m with _ | _ | m'
        · simp only [next, Nat.reduceMul, Nat.reduceMod, ↓reduceIte]
          have h1 :
              ReachesPlus target (cfg_C k 2 0)
                (Cfg.headRight E (e_tape default (.b10101 :: add_b10101 k []))
                  (ListBlank.append [0, 1]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                      (ListBlank.append [0]
                        (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
            unfold cfg_C
            rw [← e_tape_default_b10101 k]
            simp only [e_tape, list_pow_zero, list_pow_succ]
            bb_steps
          have h2 := sweep_E_tape (.b10101 :: add_b10101 k []) default 0
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
          have h_w :
              0 + eblockWeight (.b10101 :: add_b10101 k []) = 5 * k + 6 := by
            simp only [eblockWeight, eblockWeight_add_b10101]
            omega
          rw [h_w] at h2
          exact h1.trans h2
        · simp only [next, ↓reduceIte]
          have h1 :
              ReachesPlus target (cfg_C k 2 2)
                (Cfg.headRight E (e_tape default (.b10101 :: add_b10101 k []))
                  (ListBlank.append [0, 1]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                      (ListBlank.append [0]
                        (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))))) := by
            unfold cfg_C
            rw [← e_tape_default_b10101 k]
            simp only [e_tape, list_pow_zero, list_pow_succ]
            bb_steps
          have h2 := sweep_E_tape (.b10101 :: add_b10101 k []) default 0
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
          have h_w :
              0 + eblockWeight (.b10101 :: add_b10101 k []) = 5 * k + 6 := by
            simp only [eblockWeight, eblockWeight_add_b10101]
            omega
          rw [h_w] at h2
          exact h1.trans h2
        · have h_b : 2 * (m' + 2) = 2 * m' + 4 := by omega
          have h_mod : (2 * m' + 4) % 2 = 0 := by omega
          have h_ne0 : 2 * m' + 4 ≠ 0 := by omega
          have h_ne2 : 2 * m' + 4 ≠ 2 := by omega
          have h_sub : 2 * m' + 4 - 3 = 2 * m' + 1 := by omega
          rw [h_b]
          simp only [next, h_mod, h_ne0, h_ne2, h_sub, ↓reduceIte]
          have h1 :
              ReachesPlus target (cfg_C k 2 (2 * m' + 4))
                (Cfg.headRight B
                  (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default)
                  (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m' + 5)) default)) := by
            unfold cfg_C
            rw [← append_10101_pow k]
            have h_r : 2 * m' + 5 = 1 + (2 * m' + 4) := by omega
            rw [h_r, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * m' + 4)]
            simp only [list_pow_zero, list_pow_succ]
            bb_steps
          have h2 := bounce_B_odd m'
            (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default)
          exact h1.trans h2
      · have h_mod : (2 * m + 1) % 2 = 1 := by omega
        simp only [next, Nat.reduceEqDiff, h_mod, ↓reduceIte]
        have h1 :
            ReachesPlus target (cfg_C k 2 (2 * m + 1))
              (Cfg.headRight B
                (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default)
                (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2)) default)) := by
          unfold cfg_C
          rw [← append_10101_pow k]
          have h_r : 2 * m + 2 = 1 + (2 * m + 1) := by omega
          rw [h_r, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * m + 1)]
          simp only [list_pow_zero, list_pow_succ]
          bb_steps
        have h2 := bounce_B_even m
          (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default)
        exact h1.trans h2
    · have h_a : 2 * (n' + 2) = 2 * n' + 4 := by omega
      have h_mod : (2 * n' + 4) % 2 = 0 := by omega
      have h_ne0 : 2 * n' + 4 ≠ 0 := by omega
      have h_ne2 : 2 * n' + 4 ≠ 2 := by omega
      have h_sub : 2 * n' + 4 - 3 = 2 * n' + 1 := by omega
      rw [h_a]
      simp only [next, h_mod, h_ne0, h_ne2, h_sub, ↓reduceIte]
      let L_next := ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default
      have h1 :
          ReachesPlus target (cfg_C k (2 * n' + 4) b)
            (Cfg.headRight A (e_tape L_next [])
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n'))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
        unfold cfg_C
        change ReachesPlus target _
          (Cfg.headRight A
            (e_tape (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ (k + 1)) default) []) _)
        rw [← append_10101_pow k]
        have h_add : 2 * n' + 4 = 4 + 2 * n' := by omega
        rw [h_add, ListBlank.append_pow_add]
        simp only [e_tape, list_pow_zero, list_pow_succ]
        bb_steps
      have h2 := shift_A_11_eblock n' L_next []
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
      have h3 :
          ReachesPlus target
            (Cfg.headRight A (e_tape L_next (add_b01 n' []))
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
            (Cfg.headRight B (e_tape L_next (.b1 :: add_b01 n' []))
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default)) := by
        simp only [e_tape]
        bb_steps
      have h_pre := (h1.trans_star h2).trans h3
      have h_drain := B_drain b L_next (add_b01 n' [])
      have h_w : eblockWeight (add_b01 n' []) = 2 * n' + 1 := by
        simp only [eblockWeight_add_b01, eblockWeight]
      rw [h_w] at h_drain
      rcases h_d : drainB b (2 * n' + 1) with _ | ⟨a', b'⟩
      · rw [h_d] at h_drain
        obtain ⟨cfg', h_halt, h_none⟩ := h_drain
        exact ⟨cfg', h_pre.trans h_halt, h_none⟩
      · rw [h_d] at h_drain
        exact h_pre.trans h_drain
  · rcases n with _ | _ | _ | n'
    · rcases b with _ | _ | b'
      · simp only [next, Nat.mul_zero, Nat.zero_add, ↓reduceIte]
        exact step_C_a1_b0 k
      · simp only [next, Nat.mul_zero, Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte]
        exact step_C_a1_b1 k
      · have h_ne0 : b' + 2 ≠ 0 := by omega
        have h_ne1 : b' + 2 ≠ 1 := by omega
        have h_sub : b' + 2 - 2 = b' := by omega
        simp only [next, Nat.mul_zero, Nat.zero_add, h_ne0, h_ne1, h_sub, ↓reduceIte]
        have h1 :
            ReachesPlus target (cfg_C k 1 (b' + 2))
              (Cfg.headRight B
                (e_tape default (.b1 :: .b01 :: .b01 :: .b01 :: add_b10101 k []))
                (ListBlank.append (([1] : List (Fin 2)) ^ b') default)) := by
          unfold cfg_C
          rw [← e_tape_default_b10101 k]
          have h_add : b' + 2 = 2 + b' := by omega
          rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 b']
          simp only [e_tape, list_pow_zero, list_pow_succ]
          bb_steps
        let xs := .b01 :: .b01 :: .b01 :: add_b10101 k []
        have h_drain := B_drain b' default xs
        have h_w : eblockWeight xs = 5 * k + 7 := by
          simp only [xs, eblockWeight, eblockWeight_add_b10101]
        rw [h_w] at h_drain
        rcases h_d : drainB b' (5 * k + 7) with _ | ⟨a', b''⟩
        · rw [h_d] at h_drain
          obtain ⟨cfg', h_halt, h_none⟩ := h_drain
          exact ⟨cfg', h1.trans h_halt, h_none⟩
        · rw [h_d] at h_drain
          exact h1.trans h_drain
    · simp only [next, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
      have h1 :
          ReachesPlus target (cfg_C k 3 b)
            (Cfg.headRight E (e_tape default (.b10101 :: add_b10101 k []))
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ b)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
        unfold cfg_C
        rw [← e_tape_default_b10101 k]
        simp only [e_tape, list_pow_zero, list_pow_succ]
        bb_steps
      have h2 := sweep_E_tape (.b10101 :: add_b10101 k []) default b
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
      have h_w :
          b + eblockWeight (.b10101 :: add_b10101 k []) = 5 * k + b + 6 := by
        simp only [eblockWeight, eblockWeight_add_b10101]
        omega
      rw [h_w] at h2
      exact h1.trans h2
    · simp only [next, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
      have h1 :
          ReachesPlus target (cfg_C k 5 b)
            (Cfg.headRight E (e_tape default (.b10101 :: add_b10101 k []))
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))))) := by
        unfold cfg_C
        rw [← e_tape_default_b10101 k]
        rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
        simp only [e_tape, list_pow_zero, list_pow_succ]
        bb_steps
      have h2 := sweep_E_tape (.b10101 :: add_b10101 k []) default 0
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))
      have h_w :
          0 + eblockWeight (.b10101 :: add_b10101 k []) = 5 * k + 6 := by
        simp only [eblockWeight, eblockWeight_add_b10101]
        omega
      rw [h_w] at h2
      exact h1.trans h2
    · have h_a : 2 * (n' + 3) + 1 = 2 * n' + 7 := by omega
      have h_mod : (2 * n' + 7) % 2 = 1 := by omega
      have h_ne1 : 2 * n' + 7 ≠ 1 := by omega
      have h_ne3 : 2 * n' + 7 ≠ 3 := by omega
      have h_ne5 : 2 * n' + 7 ≠ 5 := by omega
      have h_sub : 2 * n' + 7 - 6 = 2 * n' + 1 := by omega
      rw [h_a]
      simp only [next, h_mod, h_ne1, h_ne3, h_ne5, h_sub, Nat.reduceEqDiff, ↓reduceIte]
      have h1 := step_C_odd_ge7 n'
        (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default) b
      rw [append_10101_pow k] at h1
      exact h1

private theorem step_C (k a b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C k a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have h := step_state k a b
  rcases h_next : next (.C k a b) with _ | ⟨k', a', b'⟩
  · rw [h_next] at h
    obtain ⟨cfg', h_plus, h_none⟩ := h
    exact ⟨cfg', h_plus, Or.inr h_none⟩
  · rw [h_next] at h
    exact ⟨cfg_C k' a' b', h, Or.inl (in_ps_C k' a' b')⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 0 2 0) := by
  have h_init : ReachesPlus target (init []) (cfg_C 0 2 0) := by
    unfold cfg_C
    simp only [list_pow_zero, list_pow_succ]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 0 2 0, init_reaches_start, in_ps_C 0 2 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_C]
  exact step_C (vars 0) (vars 1) (vars 2)

/-- `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨k, a, b⟩ s' hnext
    have h := step_state k a b
    rwa [hnext] at h
  step_none := by
    rintro ⟨k, a, b⟩ hnext
    have h := step_state k a b
    rw [hnext] at h
    obtain ⟨cfg', hp, hh⟩ := h
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC
