/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`
(see <https://wiki.bbchallenge.org/wiki/1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE>)
(**cryptid_15**, holdout #105, suspect_87).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(a, f, g, d) :=
  0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^3\,(01111)^d\,011\,0^\infty$$
at $C(2, 0, 0, 0)$ in 118 steps, and every $C(a, f, g, d)$ advances in `ReachesPlus` either to
another $C(a', f', g', d')$ or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
C(a, f, g, d) = 0^inf 1^{a+1} C> 00 1^{f+4} (01)^g 1^3 (01111)^d 011 0^inf

C(a+2, f, g, d)  -> C(a, f+3, g, d)
C(0, f, g+2, d)  -> C(f+3, 3, g, d)
C(1, f, g+2, d)  -> C(f+4, 3, g, d)
C(0, 2k, 0, d)   -> C(2, 0, k+2, d)
C(0, 2k+1, 0, d) -> C(5, 0, k+1, d)
C(0, 0, 1, d)    -> C(2, 0, 0, d+2)
C(0, 2k+2, 1, d) -> C(5, 0, k, d+1)
C(0, 2k+1, 1, d) -> C(2, 0, k+1, d+1)
C(1, 2k, 0, d)   -> C(0, 0, k+3, d)
C(1, 2k+1, 0, d) -> Halt
C(1, 2k, 1, d)   -> Halt
C(1, 2k+1, 1, d) -> C(0, 0, k+2, d+1)

Start: C(2, 0, 0, 0), reached after 118 raw TM steps
```

## High-Level Collatz-like Acceleration

Eliminating $a$ and $f$ reduces the 4-counter dynamics $C(a, f, g, d)$ to the 2-counter family
$\{C_0(g, d), C_2(g, d), C_5(g, d)\}$ corresponding to $C(a_0, 0, g, d)$ with
$a_0 \in \{0, 2, 5\}$, starting at $C_2(0, 0)$:
- Every configuration drains $a$ modulo $2$ via
  $C(a, f, g, d) \to^* C(a \bmod 2, f + 3\lfloor a / 2 \rfloor, g, d)$.
- `scanG` collapses the entire $g \mapsto g - 2$ scan together with the interleaved parity drains
  on $a$ until $g \in \{0, 1\}$, exiting directly to $C_0$, $C_2$, $C_5$, or halting (`none`).
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Helper Lemmas for Block Repetition and Shifts -/

private theorem append_pow_split (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : ℕ) :
    ListBlank.append (u ^ (m + n)) s =
      ListBlank.append (u ^ n) (ListBlank.append (u ^ m) s) := by
  rw [Nat.add_comm m n, ListBlank.append_pow_add]

private theorem append_one_pow_add (s : ListBlank (Fin 2)) (a n : ℕ) :
    ListBlank.append (([1] : List (Fin 2)) ^ n)
      (ListBlank.append (([1] : List (Fin 2)) ^ a) s) =
      ListBlank.append (([1] : List (Fin 2)) ^ (a + n)) s := by
  rw [← ListBlank.append_pow_add, Nat.add_comm]

/-- Leftward shift across `1^k` in state `E`. -/
private theorem shift_E_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight E l
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight E
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k)
          (ListBlank.append [1] (ListBlank.append [1] r)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward sweep across `0 1^k` in state `E`. -/
private theorem sweep_E_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight E l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h1 := shift_E_left k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [0] l)
          (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight E l
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) := by
      rw [ListBlank.append_append, ← list_pow_succ', ListBlank.append_pow_succ]
    have h_pow2 :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [← ListBlank.append_pow_succ]
    rw [h_pow, ← h_pow2]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward shift across `1^k` with prefix `[0, 1, 1]` in state `E`. -/
private theorem shift_E_right_011 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l
        (ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0, 1, 1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E l
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight E (ListBlank.append [1] l)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) k r]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward sweep across `0 1^{k+2}` in state `E`. -/
private theorem sweep_E_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight E
        (ListBlank.append [1]
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l)))
        r) := by
  have h_split :
      ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r) =
        ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) := by
    have h_eq : k + 2 = 2 + k := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 k r]
    rfl
  rw [h_split]
  have h1 := shift_E_right_011 k l r
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [0, 1, 1] r))
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l)))
          r) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l =
          ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) := by
      rw [← ListBlank.append_pow_succ]
    rw [h_l]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward sweep across `0 1^{k+2}` from `l0 <+ [0] <+ [1]` in state `E`. -/
private theorem sweep_E_right_01 (k : ℕ) (l0 r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1] (ListBlank.append [0] l0))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight E
        (ListBlank.append [1]
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2))
              (ListBlank.append [0] l0))))
        r) := by
  have h1 := sweep_E_right k (ListBlank.append [1] (ListBlank.append [0] l0)) r
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1] (ListBlank.append [0] l0)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 2))
          (ListBlank.append [0] l0) := by
    change ListBlank.append (([1] : List (Fin 2)) ^ (k + 1))
      (ListBlank.append (([1] : List (Fin 2)) ^ 1) (ListBlank.append [0] l0)) = _
    rw [append_one_pow_add (ListBlank.append [0] l0) 1 (k + 1)]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) _) (by omega)
  rwa [h_l] at h1

/-- Leftward shift across `1^{2k}` in state `C`, converting pairs of `1`s into `(01)^k`. -/
private theorem shift_C_left_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l =
          ListBlank.append [1]
            (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)) := by
      have h_eq : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [h_eq, append_pow_split l ([1] : List (Fin 2)) (2 * k + 1) 1,
        append_pow_split l ([1] : List (Fin 2)) (2 * k) 1]
      rfl
    rw [h_l]
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1]
              (ListBlank.append [1]
                (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)))
            (ListBlank.append [1] r))
          (Cfg.headRight C
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
            (ListBlank.append [1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_r] at h3

/-- Bounce in state `C` reading `00` across `1^{c+3}` and `0 1^m`. -/
private theorem sweep_C_bounce (m c : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
        (ListBlank.append [0, 0] r))
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1] r)) := by
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1]
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))) := by
    have h_eq : c + 3 = (c + 1) + 1 + 1 := by omega
    rw [h_eq, append_pow_split _ ([1] : List (Fin 2)) (c + 1 + 1) 1,
      append_pow_split _ ([1] : List (Fin 2)) (c + 1) 1]
    rfl
  rw [h_l]
  have h1 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))))
          (ListBlank.append [0, 0] r))
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
          (ListBlank.append [1] (ListBlank.append [0, 1, 0] r))) := by
    bb_steps
  have h2 := sweep_E_left (c + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [0, 1, 0] r)
  have h12 := h1.trans h2
  have h3 := sweep_E_right c
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [0, 1, 0] r)
  have h123 := h12.trans h3
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default := by
    rw [append_one_pow_add default m (c + 1)]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) default) (by omega)
  rw [h_comb] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)))
          (ListBlank.append [0, 1, 0] r))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)
          (ListBlank.append [0, 0, 1, 1, 1] r)) := by
    bb_steps
  exact h123.trans h4

/-- Rightward shift across `(01111)^d` in state `E`. -/
private theorem shift_E_right_01111 (d : ℕ) (l0 r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E (ListBlank.append [1] (ListBlank.append [0] l0))
        (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d) r))
      (Cfg.headRight E
        (ListBlank.append [1]
          (ListBlank.append [0]
            (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l0)))
        r) := by
  induction d generalizing l0 r with
  | zero => exact ReachesStar.refl _ _
  | succ d ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E (ListBlank.append [1] (ListBlank.append [0] l0))
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ (d + 1)) r))
          (Cfg.headRight E
            (ListBlank.append [1]
              (ListBlank.append [0] (ListBlank.append [1, 1, 1, 1, 0] l0)))
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d) r)) := by
      rw [ListBlank.append_pow_succ ([0, 1, 1, 1, 1] : List (Fin 2)) d r]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1, 1, 1, 0] l0) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d)
          (ListBlank.append [1, 1, 1, 1, 0] l0) =
          ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ (d + 1)) l0 := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `(11110)^d` in state `C`. -/
private theorem shift_C_left_11110 (d : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l)
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ 3) r)))
      (Cfg.headRight C l
        (ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d) r)))) := by
  induction d generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ d ih =>
    have h_l :
        ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ (d + 1)) l =
          ListBlank.append [1, 1, 1, 1, 0]
            (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l) := by
      rw [append_pow_split l ([1, 1, 1, 1, 0] : List (Fin 2)) d 1]
      rfl
    rw [h_l]
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1, 1, 1, 1, 0]
              (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l))
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ 3) r)))
          (Cfg.headRight C
            (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l)
            (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append [0, 1, 1, 1, 1] r)))) := by
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1, 1, 1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_r :
        ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
          (ListBlank.append [0, 1, 1, 1, 1] r) =
          ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ (d + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_r] at h3

/-- Full right-and-left bounce across `(01111)^d 011` from state `E` to state `C`. -/
private theorem bounce_E_to_C_d (d : ℕ) (l0 : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1] (ListBlank.append [0] l0))
        (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
          (ListBlank.append [0, 1, 1] default)))
      (Cfg.headRight C l0
        (ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
              (ListBlank.append [0, 1, 1] default))))) := by
  have h1 := shift_E_right_01111 d l0 (ListBlank.append [0, 1, 1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l0)))
          (ListBlank.append [0, 1, 1] default))
        (Cfg.headRight C
          (ListBlank.append (([1, 1, 1, 1, 0] : List (Fin 2)) ^ d) l0)
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  have h3 := shift_C_left_11110 d l0 (ListBlank.append [0, 1, 1] default)
  exact h1.trans_plus (h2.trans_star h3)

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$C(a, f, g, d) :=
  0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^3\,(01111)^d\,011\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
              (.rep [1] 1 (.rep [0, 1] 2
                (.sym 1 (.sym 1 (.sym 1
                  (.rep [0, 1, 1, 1, 1] 3
                    (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))) }

/-- Closed pattern set for `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Configuration $C(a, f, g, d)$. -/
private def cfg_C (a f g d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0, 0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
              (ListBlank.append [0, 1, 1] default))))))

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) (vars 3) := by
  dsimp only [pat_C, evalTapePattern, evalTapeExpr]
  unfold cfg_C
  have h_l :
      ListBlank.cons (1 : Fin 2)
        (ListBlank.append (([1] : List (Fin 2)) ^ vars 0) default) =
        ListBlank.append (([1] : List (Fin 2)) ^ (vars 0 + 1)) default := by
    rw [Nat.add_comm (vars 0) 1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (vars 0) default]
    rfl
  have h_f :
      ListBlank.append (([1] : List (Fin 2)) ^ (vars 1 + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ vars 2)
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ vars 3)
              (ListBlank.append [0, 1, 1] default)))) =
        ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
          (ListBlank.append (([1] : List (Fin 2)) ^ vars 1)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ vars 2)
              (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
                (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ vars 3)
                  (ListBlank.cons 0 (ListBlank.cons 1
                    (ListBlank.cons 1 default)))))))))))) := by
    rw [Nat.add_comm (vars 1) 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (vars 1)]
    rfl
  rw [h_l, h_f]
  rfl

private theorem in_ps_C (a f g d : ℕ) : IsInPatternSet ps (cfg_C a f g d) := by
  refine ⟨(pat_C, .true), List.Mem.head _,
    fun | 0 => a | 1 => f | 2 => g | 3 => d | _ => 0, ?_, trivial⟩
  rw [eval_pat_C]
  rfl

/-! ## Intermediate Configurations and Accelerated Rules -/

/-- Drain rule: $C(a + 2, f, g, d) \to C(a, f + 3, g, d)$. -/
private theorem rule_dec_a (a f g d : ℕ) :
    ReachesPlus target (cfg_C (a + 2) f g d) (cfg_C a (f + 3) g d) := by
  unfold cfg_C
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)) := by
    simp
  have h_r2 :
      ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 3 + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default))))) =
        ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                  (ListBlank.append [0, 1, 1] default))))) := by
    have h_f : f + 3 + 4 = 3 + (f + 4) := by omega
    rw [h_f, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 4)]
    rfl
  rw [h_l, h_r2]
  have h_step := sweep_C_bounce 0 a
    (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default)))))
  have h_add : 0 + a + 1 = a + 1 := by omega
  rwa [h_add] at h_step

/-- Intermediate configuration $M(a, f, g, d)$ after leaving $C(a, f, g, d)$ for
$a \in \{0, 1\}$. -/
private def cfg_M (a f g d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append [1]
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
    (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
              (ListBlank.append [0, 1, 1] default))))))

private theorem step_C_a0_to_M (f g d : ℕ) :
    ReachesPlus target (cfg_C 0 f g d) (cfg_M 0 f g d) := by
  unfold cfg_C cfg_M
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  bb_steps

private theorem step_C_a1_to_M (f g d : ℕ) :
    ReachesPlus target (cfg_C 1 f g d) (cfg_M 1 f g d) := by
  unfold cfg_C cfg_M
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  bb_steps

private theorem step_M_g2 (a f g d : ℕ) :
    ReachesPlus target (cfg_M a f (g + 2) d) (cfg_C (f + 3 + a) 3 g d) := by
  unfold cfg_M
  have h1 := sweep_E_right_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
      (ListBlank.append (([1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
          (ListBlank.append [0, 1, 1] default))))
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default)))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1 + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 4)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                    (ListBlank.append [0, 1, 1] default))))))) := by
    have h_g :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
              (ListBlank.append [0, 1, 1] default))) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                  (ListBlank.append [0, 1, 1] default)))) := by
      have h_eq : g + 2 = 2 + g := by omega
      rw [h_eq, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 g]
      rfl
    have h_f : f + 4 = f + 1 + 3 := by omega
    rw [h_g, h_f]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_C_bounce (a + 2) (f + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 4)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default)))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 + (f + 1) + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 4)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                  (ListBlank.append [0, 1, 1] default)))))) =
        cfg_C (f + 3 + a) 3 g d := by
    unfold cfg_C
    have h_a : a + 2 + (f + 1) + 1 = f + 3 + a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

/-- Intermediate configuration $L(a, m, d)$ after the rightward-and-leftward sweep across
$(01111)^d$. -/
private def cfg_L (a m d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1] : List (Fin 2)) ^ (m + 4))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
    (ListBlank.append [1]
      (ListBlank.append (([1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
          (ListBlank.append [0, 1, 1] default))))

private theorem step_M_g0 (a f d : ℕ) :
    ReachesPlus target (cfg_M a f 0 d) (cfg_L a (f + 3) d) := by
  have h_eq :
      cfg_M a f 0 d =
        Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default)))) := by
    unfold cfg_M
    simp only [list_pow_zero, ListBlank.append_nil]
    have h_f : f + 5 + 2 = (f + 4) + 3 := by omega
    rw [h_f, ListBlank.append_pow_add ([1] : List (Fin 2)) (f + 4) 3]
  rw [h_eq]
  have h1 := sweep_E_right_01 (f + 5)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
    (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
      (ListBlank.append [0, 1, 1] default))
  have h_f2 : f + 5 + 2 = f + 3 + 4 := by omega
  rw [h_f2] at h1
  have h2 := bounce_E_to_C_d d
    (ListBlank.append (([1] : List (Fin 2)) ^ (f + 3 + 4))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
  exact h1.trans h2

private theorem step_M_g1 (a f d : ℕ) :
    ReachesPlus target (cfg_M a f 1 d) (cfg_L a f (d + 1)) := by
  have h_eq :
      cfg_M a f 1 d =
        Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 2 + 2))
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ (d + 1))
                (ListBlank.append [0, 1, 1] default)))) := by
    unfold cfg_M
    rw [ListBlank.append_pow_succ ([0, 1, 1, 1, 1] : List (Fin 2)) d]
    rfl
  rw [h_eq]
  have h1 := sweep_E_right_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
    (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ (d + 1))
      (ListBlank.append [0, 1, 1] default))
  have h2 := bounce_E_to_C_d (d + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
  exact h1.trans h2

private theorem step_L_a1_odd (k d : ℕ) :
    ReachesPlus target (cfg_L 1 (2 * k + 1) d) (cfg_C 0 0 (k + 2) d) := by
  unfold cfg_L
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1 + 4))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (1 + 2))
            (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 2)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))) := by
    have h_eq : 2 * k + 1 + 4 = 1 + 2 * (k + 2) := by omega
    rw [h_eq, append_pow_split _ ([1] : List (Fin 2)) 1 (2 * (k + 2))]
  rw [h_l]
  have h1 := shift_C_left_even (k + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)))
    (ListBlank.append (([1] : List (Fin 2)) ^ 3)
      (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                  (ListBlank.append [0, 1, 1] default))))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (0 + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                    (ListBlank.append [0, 1, 1] default))))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := sweep_C_bounce 0 0
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default)))))
  exact h12.trans h3

private theorem step_L_a1_even_halt (k d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_L 1 (2 * k) d) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_L
  have h_eq : 2 * k + 4 = 2 * (k + 2) := by omega
  rw [h_eq]
  have h1 := shift_C_left_even (k + 2)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ 3)
      (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
        (ListBlank.append [0, 1, 1] default)))
  have h_k :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default))) =
        ListBlank.append [0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default)))) := by
    have h_add : k + 2 = 2 + k := by omega
    rw [h_add, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 k]
    rfl
  rw [h_k] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                    (ListBlank.append [0, 1, 1] default)))))))
        (Cfg.headRight F default
          (ListBlank.append [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  refine ⟨_, h1.trans_plus h2, ?_⟩
  bb_halt

private theorem step_L_a0_odd (k d : ℕ) :
    ReachesPlus target (cfg_L 0 (2 * k + 1) d) (cfg_C 2 0 (k + 1) d) := by
  unfold cfg_L
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1 + 4))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (0 + 2))
            (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 2)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))) := by
    have h_eq : 2 * k + 1 + 4 = 1 + 2 * (k + 2) := by omega
    rw [h_eq, append_pow_split _ ([1] : List (Fin 2)) 1 (2 * (k + 2))]
  rw [h_l]
  have h1 := shift_C_left_even (k + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)))
    (ListBlank.append (([1] : List (Fin 2)) ^ 3)
      (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
        (ListBlank.append [0, 1, 1] default)))
  have h_k :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default))) =
        ListBlank.append [0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default)))) := by
    have h_add : k + 2 = 1 + (k + 1) := by omega
    rw [h_add, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 1 (k + 1)]
    rfl
  rw [h_k] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)))
          (ListBlank.append [1]
            (ListBlank.append [0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                    (ListBlank.append [0, 1, 1] default)))))))
        (cfg_C 2 0 (k + 1) d) := by
    unfold cfg_C
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  exact h1.trans_plus h2

private theorem step_L_a0_even_succ (j d : ℕ) :
    ReachesPlus target (cfg_L 0 (2 * (j + 1)) d) (cfg_C 5 0 j d) := by
  unfold cfg_L
  have h_eq : 2 * (j + 1) + 4 = 2 * (j + 3) := by omega
  rw [h_eq]
  have h1 := shift_C_left_even (j + 3)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ 3)
      (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
        (ListBlank.append [0, 1, 1] default)))
  have h_j :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 3))
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default)))) := by
    have h_add : j + 3 = 3 + j := by omega
    rw [h_add, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 3 j]
  rw [h_j] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                    (ListBlank.append [0, 1, 1] default)))))))
        (cfg_C 5 0 j d) := by
    unfold cfg_C
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  exact h1.trans_plus h2

private theorem step_L_a0_zero (d : ℕ) :
    ReachesPlus target (cfg_L 0 0 d) (cfg_C 2 0 0 (d + 1)) := by
  have h1 :
      ReachesPlus target (cfg_L 0 0 d)
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append [1, 1, 1, 1, 0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 6) default))))
          (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1, 1] default))) := by
    unfold cfg_L
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  have h2 := bounce_E_to_C_d d
    (ListBlank.append [1, 1, 1, 1, 0]
      (ListBlank.append (([1] : List (Fin 2)) ^ 6) default))
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1, 1, 1, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 6) default))
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default)))))
        (cfg_C 2 0 0 (d + 1)) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([0, 1, 1, 1, 1] : List (Fin 2)) d]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  exact h1.trans (h2.trans h3)

/-! ## Composed Canonical Transitions -/

private theorem step_C_a0_g0_even (k d : ℕ) :
    ReachesPlus target (cfg_C 0 (2 * k) 0 d) (cfg_C 2 0 (k + 2) d) := by
  have h1 := (step_C_a0_to_M (2 * k) 0 d).trans (step_M_g0 0 (2 * k) d)
  have h_eq : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rw [h_eq] at h1
  exact h1.trans (step_L_a0_odd (k + 1) d)

private theorem step_C_a0_g0_odd (k d : ℕ) :
    ReachesPlus target (cfg_C 0 (2 * k + 1) 0 d) (cfg_C 5 0 (k + 1) d) := by
  have h1 := (step_C_a0_to_M (2 * k + 1) 0 d).trans (step_M_g0 0 (2 * k + 1) d)
  have h_eq : 2 * k + 1 + 3 = 2 * ((k + 1) + 1) := by omega
  rw [h_eq] at h1
  exact h1.trans (step_L_a0_even_succ (k + 1) d)

private theorem step_C_a0_g1_zero (d : ℕ) :
    ReachesPlus target (cfg_C 0 0 1 d) (cfg_C 2 0 0 (d + 2)) :=
  ((step_C_a0_to_M 0 1 d).trans (step_M_g1 0 0 d)).trans (step_L_a0_zero (d + 1))

private theorem step_C_a0_g1_even_succ (j d : ℕ) :
    ReachesPlus target (cfg_C 0 (2 * (j + 1)) 1 d) (cfg_C 5 0 j (d + 1)) :=
  ((step_C_a0_to_M (2 * (j + 1)) 1 d).trans
    (step_M_g1 0 (2 * (j + 1)) d)).trans (step_L_a0_even_succ j (d + 1))

private theorem step_C_a0_g1_odd (k d : ℕ) :
    ReachesPlus target (cfg_C 0 (2 * k + 1) 1 d) (cfg_C 2 0 (k + 1) (d + 1)) :=
  ((step_C_a0_to_M (2 * k + 1) 1 d).trans
    (step_M_g1 0 (2 * k + 1) d)).trans (step_L_a0_odd k (d + 1))

private theorem step_C_a0_g2 (f g d : ℕ) :
    ReachesPlus target (cfg_C 0 f (g + 2) d) (cfg_C (f + 3) 3 g d) :=
  (step_C_a0_to_M f (g + 2) d).trans (step_M_g2 0 f g d)

private theorem step_C_a1_g0_even (k d : ℕ) :
    ReachesPlus target (cfg_C 1 (2 * k) 0 d) (cfg_C 0 0 (k + 3) d) := by
  have h1 := (step_C_a1_to_M (2 * k) 0 d).trans (step_M_g0 1 (2 * k) d)
  have h_eq : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rw [h_eq] at h1
  exact h1.trans (step_L_a1_odd (k + 1) d)

private theorem step_C_a1_g0_odd_halt (k d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C 1 (2 * k + 1) 0 d) cfg' ∧ (step target cfg').isNone := by
  have h1 := (step_C_a1_to_M (2 * k + 1) 0 d).trans (step_M_g0 1 (2 * k + 1) d)
  have h_eq : 2 * k + 1 + 3 = 2 * (k + 2) := by omega
  rw [h_eq] at h1
  obtain ⟨cfg', h2, h_halt⟩ := step_L_a1_even_halt (k + 2) d
  exact ⟨cfg', h1.trans h2, h_halt⟩

private theorem step_C_a1_g1_even_halt (k d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C 1 (2 * k) 1 d) cfg' ∧ (step target cfg').isNone := by
  have h1 := (step_C_a1_to_M (2 * k) 1 d).trans (step_M_g1 1 (2 * k) d)
  obtain ⟨cfg', h2, h_halt⟩ := step_L_a1_even_halt k (d + 1)
  exact ⟨cfg', h1.trans h2, h_halt⟩

private theorem step_C_a1_g1_odd (k d : ℕ) :
    ReachesPlus target (cfg_C 1 (2 * k + 1) 1 d) (cfg_C 0 0 (k + 2) (d + 1)) :=
  ((step_C_a1_to_M (2 * k + 1) 1 d).trans
    (step_M_g1 1 (2 * k + 1) d)).trans (step_L_a1_odd k (d + 1))

private theorem step_C_a1_g2 (f g d : ℕ) :
    ReachesPlus target (cfg_C 1 f (g + 2) d) (cfg_C (f + 4) 3 g d) :=
  (step_C_a1_to_M f (g + 2) d).trans (step_M_g2 1 f g d)

private theorem step_C (a f g d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C a f g d) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a'
  · rcases g with _ | _ | g'
    · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨cfg_C 2 0 (k + 2) d, step_C_a0_g0_even k d, Or.inl (in_ps_C 2 0 (k + 2) d)⟩
      · exact ⟨cfg_C 5 0 (k + 1) d, step_C_a0_g0_odd k d, Or.inl (in_ps_C 5 0 (k + 1) d)⟩
    · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rcases k with _ | j
        · exact ⟨cfg_C 2 0 0 (d + 2), step_C_a0_g1_zero d, Or.inl (in_ps_C 2 0 0 (d + 2))⟩
        · exact ⟨cfg_C 5 0 j (d + 1), step_C_a0_g1_even_succ j d,
            Or.inl (in_ps_C 5 0 j (d + 1))⟩
      · exact ⟨cfg_C 2 0 (k + 1) (d + 1), step_C_a0_g1_odd k d,
          Or.inl (in_ps_C 2 0 (k + 1) (d + 1))⟩
    · exact ⟨cfg_C (f + 3) 3 g' d, step_C_a0_g2 f g' d, Or.inl (in_ps_C (f + 3) 3 g' d)⟩
  · rcases g with _ | _ | g'
    · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨cfg_C 0 0 (k + 3) d, step_C_a1_g0_even k d, Or.inl (in_ps_C 0 0 (k + 3) d)⟩
      · obtain ⟨cfg', h_step, h_halt⟩ := step_C_a1_g0_odd_halt k d
        exact ⟨cfg', h_step, Or.inr h_halt⟩
    · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨cfg', h_step, h_halt⟩ := step_C_a1_g1_even_halt k d
        exact ⟨cfg', h_step, Or.inr h_halt⟩
      · exact ⟨cfg_C 0 0 (k + 2) (d + 1), step_C_a1_g1_odd k d,
          Or.inl (in_ps_C 0 0 (k + 2) (d + 1))⟩
    · exact ⟨cfg_C (f + 4) 3 g' d, step_C_a1_g2 f g' d, Or.inl (in_ps_C (f + 4) 3 g' d)⟩
  · exact ⟨cfg_C a' (f + 3) g d, rule_dec_a a' f g d, Or.inl (in_ps_C a' (f + 3) g d)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 2 0 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_C 2 0 0 0) := by
    unfold cfg_C
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 2 0 0 0, init_reaches_start, in_ps_C 2 0 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_pat_C]
  exact step_C (vars 0) (vars 1) (vars 2) (vars 3)

/-- `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`. -/
inductive State where
  /-- $C(a, f, g, d) :=
    0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^3\,(01111)^d\,011\,0^\infty$. -/
  | C (a f g d : ℕ)

/-- Initial symbolic state $C(2, 0, 0, 0)$, reached after 118 raw TM steps. -/
def start : State := .C 2 0 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a f g d =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default))))))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C 0 f 0 d =>
    if f % 2 = 0 then some (.C 2 0 (f / 2 + 2) d)
    else some (.C 5 0 (f / 2 + 1) d)
  | .C 0 f 1 d =>
    if f = 0 then some (.C 2 0 0 (d + 2))
    else if f % 2 = 0 then some (.C 5 0 (f / 2 - 1) (d + 1))
    else some (.C 2 0 (f / 2 + 1) (d + 1))
  | .C 0 f (g + 2) d => some (.C (f + 3) 3 g d)
  | .C 1 f 0 d =>
    if f % 2 = 0 then some (.C 0 0 (f / 2 + 3) d)
    else none
  | .C 1 f 1 d =>
    if f % 2 = 0 then none
    else some (.C 0 0 (f / 2 + 2) (d + 1))
  | .C 1 f (g + 2) d => some (.C (f + 4) 3 g d)
  | .C (a + 2) f g d => some (.C a (f + 3) g d)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, f, g, d⟩ s' hnext
    rcases a with _ | _ | a'
    · rcases g with _ | _ | g'
      · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · have hmod : (2 * k) % 2 = 0 := by omega
          have hdiv : (2 * k) / 2 = k := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a0_g0_even k d
        · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * k + 1) / 2 = k := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a0_g0_odd k d
      · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · rcases k with _ | j
          · simp only [next, Nat.mul_zero, ↓reduceIte, Option.some.injEq] at hnext
            subst hnext
            exact step_C_a0_g1_zero d
          · have hne0 : 2 * (j + 1) ≠ 0 := by omega
            have hmod : (2 * (j + 1)) % 2 = 0 := by omega
            have hdiv : (2 * (j + 1)) / 2 - 1 = j := by omega
            simp only [next, hne0, ↓reduceIte, hmod, hdiv, Option.some.injEq] at hnext
            subst hnext
            exact step_C_a0_g1_even_succ j d
        · have hne0 : 2 * k + 1 ≠ 0 := by omega
          have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * k + 1) / 2 = k := by omega
          simp only [next, hne0, ↓reduceIte, hmod, hdiv, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a0_g1_odd k d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_a0_g2 f g' d
    · rcases g with _ | _ | g'
      · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · have hmod : (2 * k) % 2 = 0 := by omega
          have hdiv : (2 * k) / 2 = k := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a1_g0_even k d
        · simp [next] at hnext
      · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · simp [next] at hnext
        · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * k + 1) / 2 = k := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a1_g1_odd k d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_a1_g2 f g' d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_dec_a a' f g d
  step_none := by
    rintro ⟨a, f, g, d⟩ hnext
    rcases a with _ | _ | a'
    · rcases g with _ | _ | g'
      · simp only [next] at hnext
        split_ifs at hnext
      · simp only [next] at hnext
        split_ifs at hnext
      · simp [next] at hnext
    · rcases g with _ | _ | g'
      · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · simp [next] at hnext
        · obtain ⟨cfg', hp, hh⟩ := step_C_a1_g0_odd_halt k d
          exact ⟨cfg', hp.to_star, hh⟩
      · rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · obtain ⟨cfg', hp, hh⟩ := step_C_a1_g1_even_halt k d
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
      · simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- Two-counter symbolic state space for the high-level Collatz-like acceleration of
`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`, corresponding to $C(a_0, 0, g, d)$ with
$a_0 \in \{0, 2, 5\}$. -/
inductive HighLevelState where
  /-- $C_0(g, d) := C(0, 0, g, d)$. -/
  | C0 (g d : ℕ)
  /-- $C_2(g, d) := C(2, 0, g, d)$. -/
  | C2 (g d : ℕ)
  /-- $C_5(g, d) := C(5, 0, g, d)$. -/
  | C5 (g d : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $C_2(0, 0) = C(2, 0, 0, 0)$. -/
def highLevelStart : HighLevelState := .C2 0 0

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C0 g d => .C 0 0 g d
  | .C2 g d => .C 2 0 g d
  | .C5 g d => .C 5 0 g d

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Scan the counter $g$ from $C(\text{if } r \text{ then } 1 \text{ else } 0, f, g, d)$,
collapsing each $g \mapsto g - 2$ step together with the subsequent parity drain of $a$ until
$g \in \{0, 1\}$. -/
def scanG (r : Bool) (f g d : ℕ) : Option HighLevelState :=
  if g = 0 then
    if !r then
      if f % 2 = 0 then some (.C2 (f / 2 + 2) d)
      else some (.C5 (f / 2 + 1) d)
    else
      if f % 2 = 0 then some (.C0 (f / 2 + 3) d)
      else none
  else if g = 1 then
    if !r then
      if f = 0 then some (.C2 0 (d + 2))
      else if f % 2 = 0 then some (.C5 (f / 2 - 1) (d + 1))
      else some (.C2 (f / 2 + 1) (d + 1))
    else
      if f % 2 = 0 then none
      else some (.C0 (f / 2 + 2) (d + 1))
  else
    let s := f + 3 + if r then 1 else 0
    scanG (decide (s % 2 = 1)) (3 * (s / 2) + 3) (g - 2) d
termination_by g
decreasing_by omega

/-- High-level accelerated Collatz-like transition function on $C_0(g, d)$, $C_2(g, d)$, and
$C_5(g, d)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C0 g d => scanG false 0 g d
  | .C2 g d => scanG false 3 g d
  | .C5 g d => scanG true 6 g d

private theorem reaches_drain_a (k : ℕ) : ∀ (r f g d : ℕ),
    CollatzReachesStar next (.C (2 * k + r) f g d) (.C r (f + 3 * k) g d) := by
  induction k with
  | zero =>
    intro r f g d
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    intro r f g d
    have hstep : next (.C (2 * (k + 1) + r) f g d) = some (.C (2 * k + r) (f + 3) g d) := by
      rw [show 2 * (k + 1) + r = (2 * k + r) + 2 by omega]
      rfl
    have ih' := ih r (f + 3) g d
    rw [show f + 3 + 3 * k = f + 3 * (k + 1) by omega] at ih'
    exact CollatzReachesStar.head hstep ih'

private theorem stepsTo_scanG (g : ℕ) : ∀ (r : Bool) (f d : ℕ),
    CollatzStepsTo next (.C (if r then 1 else 0) f g d) ((scanG r f g d).map toState) := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro r f d
    rw [scanG]
    rcases eq_or_ne g 0 with rfl | hg0
    · simp only [↓reduceIte]
      cases r
      · by_cases hf : f % 2 = 0 <;>
          exact CollatzStepsTo.of_eq (by simp [next, hf, toState])
      · by_cases hf : f % 2 = 0 <;>
          exact CollatzStepsTo.of_eq (by simp [next, hf, toState])
    · rcases eq_or_ne g 1 with rfl | hg1
      · simp only [hg0, ↓reduceIte]
        cases r
        · by_cases hf0 : f = 0
          · subst hf0
            exact CollatzStepsTo.of_eq rfl
          · by_cases hf : f % 2 = 0 <;>
              exact CollatzStepsTo.of_eq (by simp [next, hf0, hf, toState])
        · by_cases hf : f % 2 = 0 <;>
            exact CollatzStepsTo.of_eq (by simp [next, hf, toState])
      · simp only [hg0, hg1, ↓reduceIte]
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
        simp only [Nat.add_sub_cancel]
        set s := f + 3 + if r then 1 else 0
        have hstep : next (.C (if r then 1 else 0) f (g' + 2) d) = some (.C s 3 g' d) := by
          cases r <;> rfl
        have hd := reaches_drain_a (s / 2) (s % 2) 3 g' d
        rw [Nat.div_add_mod] at hd
        have h_rem : s % 2 = if decide (s % 2 = 1) then 1 else 0 := by
          rcases Nat.mod_two_eq_zero_or_one s with hs | hs <;> simp [hs]
        have h_div : 3 + 3 * (s / 2) = 3 * (s / 2) + 3 := by omega
        rw [h_rem, h_div] at hd
        exact CollatzStepsTo.head hstep
          (CollatzStepsTo.of_reachesStar hd
            (ih g' (by omega) (decide (s % 2 = 1)) (3 * (s / 2) + 3) d))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) (CollatzReachesStar.refl next start) ?_
  rintro (⟨g, d⟩ | ⟨g, d⟩ | ⟨g, d⟩)
  · exact stepsTo_scanG g false 0 d
  · exact CollatzStepsTo.head rfl (stepsTo_scanG g false 3 d)
  · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (stepsTo_scanG g true 6 d))

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

end BusyBeaver.M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE
