/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB2RA1LC_2LC1RB2RB_---2LA1LA` (Bigfoot, Holdout #829)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
3-state, 3-symbol Busy Beaver holdout `1RB2RA1LC_2LC1RB2RB_---2LA1LA` (**Bigfoot**, Holdout #829;
discovered and analyzed by Shawn Ligocki and savask in October 2023, see
<https://wiki.bbchallenge.org/wiki/Bigfoot> and
<https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html>).

Starting from the blank tape (`init []`), the trajectory reaches the single canonical family
$$A(a, b, c) = 0^\infty\,(12)^a\,1^{2b+2}\,{<}\mathrm{A}\;1^{2(c+2)}\,0^\infty
  \quad (a, b, c \in \mathbb{N})$$
at $A(2, 0, 0)$ in 69 raw Turing machine steps. Every configuration $A(a, b, c)$ advances in
`ReachesPlus` according to $b \bmod 6 = 6q + r$:

## Collatz-like Acceleration Rules

```text
Configuration family:
  A(a, b, c) = 0^inf (12)^a 1^(2b+2) <A 1^(2(c+2)) 0^inf

Mod-6 transition rules (b = 6q + r):
  A(a,   6q,   c) -> A(a+1, 8q+c,   1)
  A(0,   6q+1, c) -> Halt (C0)
  A(a+1, 6q+1, c) -> A(a,   8q+c+4, 0)
  A(a,   6q+2, c) -> A(a,   8q+c+2, 3)
  A(a,   6q+3, c) -> A(a+1, 8q+c+4, 0)
  A(a,   6q+4, c) -> A(a,   8q+c+6, 1)
  A(a,   6q+5, c) -> A(a,   8q+c+8, 0)

Start: A(2, 0, 0) at step 69
Orbit: (2,0,0) -> (3,0,1) -> (4,1,1) -> (3,5,0) -> (3,8,0) -> (3,10,3) -> (3,17,1)
    -> (3,25,0) -> (2,36,0) -> ...
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA

open ThreeState Turing

/-- The `(3, 3)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2RA1LC_2LC1RB2RB_---2LA1LA"

/-- The `(3, 3)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

/-! ## Level B: Collatz-like Acceleration (`State`, `start`, `encode`, `next`) -/

/-- Canonical configuration family
$A(a, b, c) = 0^\infty\,(12)^a\,1^{2b+2}\,{<}\mathrm{A}\;1^{2(c+2)}\,0^\infty$. -/
inductive State where
  | A (a b c : ℕ)
  deriving DecidableEq, Repr

/-- Initial accelerated state $A(2, 0, 0)$, reached from `init []` in 69 steps. -/
def start : State := .A 2 0 0

/-- Decode an accelerated `State` into its concrete Turing machine configuration. -/
@[simp]
def encode : State → Cfg (Fin 3) (Fin 3)
  | .A a b c =>
      Cfg.headLeft A
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * b + 2)))
        (([1] : List (Fin 3)) ^ (2 * (c + 2)) +> default)

/-- Ligocki and savask's 7-rule mod-6 Collatz-like map for Bigfoot (`none` indicates halting at
$a = 0, b \equiv 1 \pmod 6$). -/
def next : State → Option State
  | .A a b c =>
      let q := b / 6
      let r := b % 6
      if r = 0 then
        some (.A (a + 1) (8 * q + c) 1)
      else if r = 1 then
        match a with
        | 0 => none
        | a' + 1 => some (.A a' (8 * q + c + 4) 0)
      else if r = 2 then
        some (.A a (8 * q + c + 2) 3)
      else if r = 3 then
        some (.A (a + 1) (8 * q + c + 4) 0)
      else if r = 4 then
        some (.A a (8 * q + c + 6) 1)
      else
        some (.A a (8 * q + c + 8) 0)

/-! ## Elementary Shift Rules and Tape Block Identities -/

@[simp]
private theorem pair_one_pow (k : ℕ) :
    ([1, 1] : List (Fin 3)) ^ k = ([1] : List (Fin 3)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 1 k

@[simp]
private theorem pair_two_pow (k : ℕ) :
    ([2, 2] : List (Fin 3)) ^ k = ([2] : List (Fin 3)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 2 k

private theorem flip_12_21 (a : ℕ) :
    ((default <+ ([1] : List (Fin 3))) <+ ([1, 2] : List (Fin 3)) ^ a) =
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3))) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have h1 : ([1, 2] : List (Fin 3)) ^ (a + 1) =
        ([1, 2] : List (Fin 3)) ++ ([1, 2] : List (Fin 3)) ^ a := rfl
    rw [h1, ← ListBlank.append_append, ih, ListBlank.append_append]
    have h12 : ([1, 2] : List (Fin 3)) ++ ([1] : List (Fin 3)) =
        ([1] : List (Fin 3)) ++ ([2, 1] : List (Fin 3)) := rfl
    rw [h12, ← ListBlank.append_append, ListBlank.append_append]
    rfl

private theorem shift_A_1 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{A}}> (([1] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([2] : List (Fin 3)) ^ k) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([2] : List (Fin 3))) {{A}}> (([1] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([2] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([2] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ k) =
        (l <+ ([2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_C_22 (k : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([2, 2] : List (Fin 3)) ^ k) <{{C}} r) [target]⊢*
      (l <{{C}} (([1, 1] : List (Fin 3)) ^ k +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (((l <+ ([2, 2] : List (Fin 3)) ^ k) <+ ([2, 2] : List (Fin 3))) <{{C}} r)
        [target]⊢⁺ ((l <+ ([2, 2] : List (Fin 3)) ^ k) <{{C}} (([1, 1] : List (Fin 3)) +> r)) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 3)) +> r)
    have h3 := (h1.trans_star h2).to_star
    have h_l : ((l <+ ([2, 2] : List (Fin 3)) ^ k) <+ ([2, 2] : List (Fin 3))) =
        (l <+ ([2, 2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append]; rfl
    have h_r : (([1, 1] : List (Fin 3)) ^ k +> (([1, 1] : List (Fin 3)) +> r)) =
        (([1, 1] : List (Fin 3)) ^ (k + 1) +> r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_l, h_r] at h3

private theorem shift_A_21 (k : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([2, 1] : List (Fin 3)) ^ k) <{{A}} r) [target]⊢*
      (l <{{A}} (([2, 1] : List (Fin 3)) ^ k +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (((l <+ ([2, 1] : List (Fin 3)) ^ k) <+ ([2, 1] : List (Fin 3))) <{{A}} r)
        [target]⊢⁺ ((l <+ ([2, 1] : List (Fin 3)) ^ k) <{{A}} (([2, 1] : List (Fin 3)) +> r)) := by
      bb_steps
    have h2 := ih l (([2, 1] : List (Fin 3)) +> r)
    have h3 := (h1.trans_star h2).to_star
    have h_l : ((l <+ ([2, 1] : List (Fin 3)) ^ k) <+ ([2, 1] : List (Fin 3))) =
        (l <+ ([2, 1] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append]; rfl
    have h_r : (([2, 1] : List (Fin 3)) ^ k +> (([2, 1] : List (Fin 3)) +> r)) =
        (([2, 1] : List (Fin 3)) ^ (k + 1) +> r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_l, h_r] at h3

private theorem shift_B_21 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{B}}> (([2, 1] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([1, 2] : List (Fin 3)) ^ k) {{B}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{B}}> (([2, 1] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 2] : List (Fin 3))) {{B}}> (([2, 1] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([1, 2] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([1, 2] : List (Fin 3))) <+ ([1, 2] : List (Fin 3)) ^ k) =
        (l <+ ([1, 2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_B_1 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{B}}> (([1] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([1] : List (Fin 3)) ^ k) {{B}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{B}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1] : List (Fin 3))) {{B}}> (([1] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([1] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([1] : List (Fin 3))) <+ ([1] : List (Fin 3)) ^ k) =
        (l <+ ([1] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-! ## Bounce and Drain Combinators -/

private theorem bounce_A0 (l : ListBlank (Fin 3)) (k : ℕ) :
    (l {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> default)) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1, 2, 2] : List (Fin 3)) +> default)) := by
  have h1 := shift_A_1 (k + 1) l default
  have h_l : (l <+ ([2] : List (Fin 3)) ^ (k + 1)) = ((l <+ ([2] : List (Fin 3)) ^ k) <+ [2]) := by
    rw [ListBlank.append_append]; rfl
  rw [h_l] at h1
  have h2 : (((l <+ ([2] : List (Fin 3)) ^ k) <+ [2]) {{A}}> default) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1, 2, 2] : List (Fin 3)) +> default)) := by
    bb_steps
  exact h1.trans_plus h2

private theorem bounce_A2 (l r : ListBlank (Fin 3)) (k : ℕ) :
    (l {{A}}> (([1] : List (Fin 3)) ^ k +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1] : List (Fin 3)) +> r)) := by
  have h1 := shift_A_1 k l (([2] : List (Fin 3)) +> r)
  have h2 : ((l <+ ([2] : List (Fin 3)) ^ k) {{A}}> (([2] : List (Fin 3)) +> r)) [target]⊢⁺
      ((l <+ ([2] : List (Fin 3)) ^ k) <{{C}} (([1] : List (Fin 3)) +> r)) := by
    bb_steps
  exact h1.trans_plus h2

private theorem eat_even (l r : ListBlank (Fin 3)) (k : ℕ) :
    (((l <+ ([1, 1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ (2 * k)) <{{C}} r) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * k + 2) +> r)) := by
  rw [← pair_two_pow]
  have h1 := shift_C_22 k (l <+ ([1, 1] : List (Fin 3))) r
  rw [pair_one_pow] at h1
  have h2 : ((l <+ ([1, 1] : List (Fin 3))) <{{C}} (([1] : List (Fin 3)) ^ (2 * k) +> r))
      [target]⊢⁺
      (l <{{A}} (([1, 1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_r : (([1, 1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r)) =
      (([1] : List (Fin 3)) ^ (2 * k + 2) +> r) := by
    have h11 : ([1, 1] : List (Fin 3)) = ([1] : List (Fin 3)) ^ 2 := rfl
    rw [h11, ← ListBlank.append_pow_add]
    exact congrArg (fun m => ([1] : List (Fin 3)) ^ m +> r) (by omega)
  rwa [h_r] at h3

private theorem eat_odd (l r : ListBlank (Fin 3)) (k : ℕ) :
    ((l <+ ([2] : List (Fin 3)) ^ (2 * k + 1)) <{{C}} r) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * k + 1) +> r)) := by
  have h_l : (l <+ ([2] : List (Fin 3)) ^ (2 * k + 1)) =
      ((l <+ [2]) <+ ([2, 2] : List (Fin 3)) ^ k) := by
    rw [pair_two_pow, ListBlank.append_append, ← list_pow_succ']
  rw [h_l]
  have h1 := shift_C_22 k (l <+ [2]) r
  rw [pair_one_pow] at h1
  have h2 : ((l <+ [2]) <{{C}} (([1] : List (Fin 3)) ^ (2 * k) +> r)) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_r : (([1] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * k) +> r)) =
      (([1] : List (Fin 3)) ^ (2 * k + 1) +> r) := rfl
  rwa [h_r] at h3

private theorem bounce_left_21 (a : ℕ) (r : ListBlank (Fin 3)) :
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{A}} r) [target]⊢⁺
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3))) {{B}}> r) := by
  have h1 := shift_A_21 a default r
  have h2 : (default <{{A}} (([2, 1] : List (Fin 3)) ^ a +> r)) [target]⊢⁺
      ((default <+ ([1] : List (Fin 3))) {{B}}> (([2, 1] : List (Fin 3)) ^ a +> r)) := by
    bb_steps
  have h3 := shift_B_21 a (default <+ ([1] : List (Fin 3))) r
  have h4 := (h1.trans_plus h2).trans_star h3
  rwa [flip_12_21 a] at h4

private theorem bounce_B_0 (l : ListBlank (Fin 3)) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) {{B}}> default) [target]⊢⁺
      (l <{{A}} (([1, 1, 1, 1] : List (Fin 3)) +> default)) := by
  bb_steps

private theorem bounce_B_22 (l : ListBlank (Fin 3)) :
    (((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([2, 2] : List (Fin 3))) {{B}}> default) [target]⊢⁺
      (l <{{A}} (([1, 1, 1, 1, 1, 1] : List (Fin 3)) +> default)) := by
  bb_steps

private theorem bounce_B_2 (l : ListBlank (Fin 3)) :
    (((l <+ ([1, 1, 1, 1, 1, 1] : List (Fin 3))) <+ ([2] : List (Fin 3))) {{B}}> default)
        [target]⊢⁺
      (l <{{A}} (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Fin 3)) +> default)) := by
  bb_steps

private theorem append_one_pow_succ (k : ℕ) (r : ListBlank (Fin 3)) :
    (([1] : List (Fin 3)) ^ k +> (([1] : List (Fin 3)) +> r)) =
      (([1] : List (Fin 3)) ^ (k + 1) +> r) :=
  ListBlank.append_pow_succ' [1] k r

private theorem flip_A_head (l r : ListBlank (Fin 3)) (k : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ k +> r)) =
      (l {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) := by
  rw [ListBlank.append_pow_succ]
  exact Cfg.headLeft_cons A 1 l _

private theorem flip_A_head3 (l r : ListBlank (Fin 3)) (k : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ k +> r)) =
      ((l <+ ([1, 1] : List (Fin 3))) {{A}}> (([1] : List (Fin 3)) ^ (k + 1) +> r)) :=
  flip_A_head (l <+ ([1, 1] : List (Fin 3))) r k

private theorem step_even_0 (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 3) +> (([2, 2] : List (Fin 3)) +> default))) := by
  rw [flip_A_head3 l default (2 * m)]
  have h1 := bounce_A0 (l <+ ([1, 1] : List (Fin 3))) (2 * m)
  have hr2 : (([1, 2, 2] : List (Fin 3)) +> default) =
      (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) := rfl
  rw [hr2] at h1
  have h2 := eat_even l (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) m
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * m + 2)] at h3

private theorem step_even_2 (l r : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}}
        (([1] : List (Fin 3)) ^ (2 * m + 1) +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 5) +> r)) := by
  rw [flip_A_head3 l (([2] : List (Fin 3)) +> r) (2 * m + 1)]
  have h1 := bounce_A2 (l <+ ([1, 1] : List (Fin 3))) r (2 * m + 2)
  have hr2 : (2 * m + 2) = 2 * (m + 1) := by omega
  rw [hr2] at h1
  have h2 := eat_even l (([1] : List (Fin 3)) +> r) (m + 1)
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * (m + 1) + 2)] at h3

private theorem step_odd_0 (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 1) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 2) +> (([2, 2] : List (Fin 3)) +> default))) := by
  rw [flip_A_head l default (2 * m + 1)]
  have h1 := bounce_A0 l (2 * m + 1)
  have hr2 : (([1, 2, 2] : List (Fin 3)) +> default) =
      (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) := rfl
  rw [hr2] at h1
  have h2 := eat_odd l (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) m
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * m + 1)] at h3

private theorem step_odd_2 (l r : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}}
        (([1] : List (Fin 3)) ^ (2 * m) +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 2) +> r)) := by
  rw [flip_A_head l (([2] : List (Fin 3)) +> r) (2 * m)]
  have h1 := bounce_A2 l r (2 * m + 1)
  have h2 := eat_odd l (([1] : List (Fin 3)) +> r) m
  have h3 := h1.trans h2
  rwa [append_one_pow_succ (2 * m + 1)] at h3

private theorem half_even_0 (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default)) [target]⊢⁺
      (l <{{C}} (([1] : List (Fin 3)) ^ (2 * m + 1) +> (([2, 2] : List (Fin 3)) +> default))) := by
  rw [flip_A_head l default (2 * m)]
  have h1 := bounce_A0 l (2 * m)
  rw [← pair_two_pow] at h1
  have h2 := shift_C_22 m l (([1, 2, 2] : List (Fin 3)) +> default)
  rw [pair_one_pow] at h2
  have h3 := h1.trans_star h2
  have hr2 : (([1, 2, 2] : List (Fin 3)) +> default) =
      (([1] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> default)) := rfl
  rw [hr2] at h3
  rwa [append_one_pow_succ (2 * m)] at h3

private theorem half_even_2 (l r : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <{{A}}
        (([1] : List (Fin 3)) ^ (2 * m + 1) +> (([2] : List (Fin 3)) +> r))) [target]⊢⁺
      (l <{{C}} (([1] : List (Fin 3)) ^ (2 * m + 3) +> r)) := by
  rw [flip_A_head l (([2] : List (Fin 3)) +> r) (2 * m + 1)]
  have h1 := bounce_A2 l r (2 * (m + 1))
  rw [← pair_two_pow] at h1
  have h2 := shift_C_22 (m + 1) l (([1] : List (Fin 3)) +> r)
  rw [pair_one_pow] at h2
  have h3 := h1.trans_star h2
  rwa [append_one_pow_succ (2 * (m + 1))] at h3

private theorem pass_even (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3)) ^ 9) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 11) +> default)) := by
  have hl : (l <+ ([1] : List (Fin 3)) ^ 9) =
      (((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0 ((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([1, 1, 1] : List (Fin 3))) m
  have hr1 : 2 * m + 3 = 2 * (m + 1) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_even_2 (l <+ ([1, 1, 1] : List (Fin 3))) (([2] : List (Fin 3)) +> default) (m + 1)
  have hr2 : 2 * (m + 1) + 5 = 2 * (m + 3) + 1 := by omega
  rw [hr2] at h2
  have h3 := step_even_2 l default (m + 3)
  have hr3 : 2 * (m + 3) + 5 = 2 * m + 11 := by omega
  rw [hr3] at h3
  exact (h1.trans h2).trans h3

private theorem pass_odd (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1, 1, 1] : List (Fin 3))) <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 1) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * m + 6) +> default)) := by
  have hl : (l <+ ([1, 1, 1] : List (Fin 3))) = (((l <+ [1]) <+ [1]) <+ [1]) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_odd_0 ((l <+ [1]) <+ [1]) m
  have hr1 : 2 * m + 2 = 2 * (m + 1) := by omega
  rw [hr1] at h1
  have h2 := step_odd_2 (l <+ [1]) (([2] : List (Fin 3)) +> default) (m + 1)
  have hr2 : 2 * (m + 1) + 2 = 2 * (m + 2) := by omega
  rw [hr2] at h2
  have h3 := step_odd_2 l default (m + 2)
  have hr3 : 2 * (m + 2) + 2 = 2 * m + 6 := by omega
  rw [hr3] at h3
  exact (h1.trans h2).trans h3

private theorem drain_step (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3)) ^ 12) <{{A}} (([1] : List (Fin 3)) ^ (2 * m) +> default))
        [target]⊢⁺
      (l <{{A}} (([1] : List (Fin 3)) ^ (2 * (m + 8)) +> default)) := by
  have hl : (l <+ ([1] : List (Fin 3)) ^ 12) =
      ((l <+ ([1, 1, 1] : List (Fin 3))) <+ ([1] : List (Fin 3)) ^ 9) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := pass_even (l <+ ([1, 1, 1] : List (Fin 3))) m
  have hr1 : 2 * m + 11 = 2 * (m + 5) + 1 := by omega
  rw [hr1] at h1
  have h2 := pass_odd l (m + 5)
  have hr2 : 2 * (m + 5) + 6 = 2 * (m + 8) := by omega
  rw [hr2] at h2
  exact h1.trans h2

/-! ## Canonical Configuration Family and Mod-6 Macro Rules -/

private def cfg_mid (a b n : ℕ) : Cfg (Fin 3) (Fin 3) :=
  (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * b + 2)) <{{A}}
    (([1] : List (Fin 3)) ^ (2 * n) +> default))

private def cfg_A (a b c : ℕ) : Cfg (Fin 3) (Fin 3) :=
  cfg_mid a b (c + 2)

private theorem drain_mod6 (a q r n : ℕ) :
    (cfg_mid a (6 * q + r) n) [target]⊢* (cfg_mid a r (8 * q + n)) := by
  induction q generalizing n with
  | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add]
  | succ q ih =>
    have hl : 2 * (6 * (q + 1) + r) + 2 = 12 + (2 * (6 * q + r) + 2) := by omega
    unfold cfg_mid
    rw [hl, list_pow_add, ← ListBlank.append_append]
    have h1 := drain_step
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (6 * q + r) + 2)) n
    have h2 := ih (n + 8)
    have hr : 8 * q + (n + 8) = 8 * (q + 1) + n := by omega
    rw [hr] at h2
    exact (h1.trans_star h2).to_star

private theorem combine_B_ones (l : ListBlank (Fin 3)) (m : ℕ) :
    ((l <+ ([1] : List (Fin 3))) <+ ([1] : List (Fin 3)) ^ m) =
      (l <+ ([1] : List (Fin 3)) ^ (m + 1)) := by
  rw [ListBlank.append_append, ← list_pow_succ']

private theorem split_ones_left (l : ListBlank (Fin 3)) (m c k : ℕ) (h : m = c + k) :
    (l <+ ([1] : List (Fin 3)) ^ m) =
      ((l <+ ([1] : List (Fin 3)) ^ k) <+ ([1] : List (Fin 3)) ^ c) := by
  rw [ListBlank.append_append, h, list_pow_add]

private theorem base_0 (a n : ℕ) :
    (cfg_mid a 0 (n + 2)) [target]⊢⁺ (cfg_A (a + 1) n 1) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 2) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1]) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := half_even_0 ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (n + 2)
  have h2 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default)))
      [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{A}}
      (([2] : List (Fin 3)) +>
        (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default)))) := by
    bb_steps
  have h3 := bounce_left_21 a
    (([2] : List (Fin 3)) +>
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default)))
  have h4 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) {{B}}>
      (([2] : List (Fin 3)) +>
        (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default))))
      [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) {{B}}>
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 1) +> (([2, 2] : List (Fin 3)) +> default))) := by
    have h21 : (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) =
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [2]) := by
      simp only [ListBlank.append_append]; rfl
    rw [h21]
    bb_steps
  have h5 := shift_B_1 (2 * (n + 2) + 1) (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1))
    (([2, 2] : List (Fin 3)) +> default)
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1))
      (2 * (n + 2) + 1) 3 (2 * n + 2) (by omega)] at h5
  have h6 : ((((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+
        ([1] : List (Fin 3)) ^ (2 * n + 2)) <+ ([1, 1, 1] : List (Fin 3))) {{B}}>
      (([2, 2] : List (Fin 3)) +> default)) [target]⊢⁺
      (((((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+
        ([1] : List (Fin 3)) ^ (2 * n + 2)) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([2, 2] : List (Fin 3))) {{B}}> default) := by
    bb_steps
  have h7 := bounce_B_22
    ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+ ([1] : List (Fin 3)) ^ (2 * n + 2))
  exact ((h1.trans h2).trans (h3.trans h4)).trans (h5.trans_plus (h6.trans h7))

private theorem base_1_pre (a n : ℕ) :
    (cfg_mid a 1 (n + 2)) [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{C}}
        (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default))) := by
  unfold cfg_mid
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 4) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0 ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (n + 2)
  have hr1 : 2 * (n + 2) + 3 = 2 * (n + 3) + 1 := by omega
  rw [hr1] at h1
  have h2 := half_even_2 (default <+ ([2, 1] : List (Fin 3)) ^ a)
    (([2] : List (Fin 3)) +> default) (n + 3)
  have hr2 : 2 * (n + 3) + 3 = 2 * (n + 2) + 5 := by omega
  rw [hr2] at h2
  exact h1.trans h2

private theorem base_1_halt (n : ℕ) :
    ∃ cfg', ((cfg_mid 0 1 (n + 2)) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(default <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default))),
    base_1_pre 0 n, by bb_halt⟩

private theorem base_1_step (a n : ℕ) :
    (cfg_mid (a + 1) 1 (n + 2)) [target]⊢⁺ (cfg_A a (n + 4) 0) := by
  have h1 := base_1_pre (a + 1) n
  have h2 : ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default)))
      [target]⊢⁺
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <{{A}}
      (([1] : List (Fin 3)) ^ (2 * (n + 5)) +> (([2] : List (Fin 3)) +> default))) := by
    have hl : (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) =
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [2]) := by
      simp only [ListBlank.append_append]; rfl
    have hr : (([1] : List (Fin 3)) ^ (2 * (n + 5)) +> (([2] : List (Fin 3)) +> default)) =
        (([1] : List (Fin 3)) +>
          (([1] : List (Fin 3)) ^ (2 * (n + 2) + 5) +> (([2] : List (Fin 3)) +> default))) := by
      have he : 2 * (n + 5) = 1 + (2 * (n + 2) + 5) := by omega
      rw [he, ListBlank.append_pow_add]; rfl
    rw [hl, hr]
    bb_steps
  have h3 := step_odd_2 (default <+ ([2, 1] : List (Fin 3)) ^ a) default (n + 5)
  have h4 := bounce_left_21 a (([1] : List (Fin 3)) ^ (2 * (n + 5) + 2) +> default)
  have h5 := shift_B_1 (2 * (n + 5) + 2)
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) default
  rw [combine_B_ones] at h5
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      ((2 * (n + 5) + 2) + 1) 3 (2 * (n + 4) + 2) (by omega)] at h5
  have h6 := bounce_B_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 4) + 2))
  exact (h1.trans h2).trans (h3.trans (h4.trans (h5.trans_plus h6)))

private theorem base_2 (a n : ℕ) :
    (cfg_mid a 2 (n + 2)) [target]⊢⁺ (cfg_A a (n + 2) 3) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 6) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1, 1, 1] : List (Fin 3))) (n + 2)
  have hr1 : 2 * (n + 2) + 3 = 2 * (n + 3) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_even_2 (default <+ ([2, 1] : List (Fin 3)) ^ a)
    (([2] : List (Fin 3)) +> default) (n + 3)
  have h3 := bounce_left_21 a
    (([1] : List (Fin 3)) ^ (2 * (n + 3) + 5) +> (([2] : List (Fin 3)) +> default))
  have h4 := shift_B_1 (2 * (n + 3) + 5)
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (([2] : List (Fin 3)) +> default)
  rw [combine_B_ones] at h4
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      ((2 * (n + 3) + 5) + 1) 6 (2 * (n + 2) + 2) (by omega)] at h4
  have h5 : ((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 2) + 2)) <+ ([1, 1, 1, 1, 1, 1] : List (Fin 3))) {{B}}>
      (([2] : List (Fin 3)) +> default)) [target]⊢⁺
      (((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 2) + 2)) <+ ([1, 1, 1, 1, 1, 1] : List (Fin 3))) <+
        [2]) {{B}}> default) := by
    bb_steps
  have h6 := bounce_B_2
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 2) + 2))
  exact (h1.trans h2).trans (h3.trans (h4.trans_plus (h5.trans h6)))

private theorem base_3 (a n : ℕ) :
    (cfg_mid a 3 (n + 2)) [target]⊢⁺ (cfg_A (a + 1) (n + 4) 0) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 8) =
      (((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1]) <+
        ([1, 1, 1] : List (Fin 3))) <+ ([1, 1, 1] : List (Fin 3))) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := step_even_0
    ((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1]) <+ ([1, 1, 1] : List (Fin 3)))
    (n + 2)
  have hr1 : 2 * (n + 2) + 3 = 2 * (n + 3) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_even_2 (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [1])
    (([2] : List (Fin 3)) +> default) (n + 3)
  have hr2 : 2 * (n + 3) + 5 = 2 * (n + 5) + 1 := by omega
  rw [hr2] at h2
  have h3 := half_even_2 ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) default (n + 5)
  have h4 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <{{C}}
      (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default)) [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ a) <{{A}}
      (([2] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default))) := by
    bb_steps
  have h5 := bounce_left_21 a
    (([2] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default))
  have h6 : (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) {{B}}>
      (([2] : List (Fin 3)) +> (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default)))
      [target]⊢⁺
      ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) {{B}}>
      (([1] : List (Fin 3)) ^ (2 * (n + 5) + 3) +> default)) := by
    have h21 : (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) =
        (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ [2]) := by
      simp only [ListBlank.append_append]; rfl
    rw [h21]
    bb_steps
  have h7 := shift_B_1 (2 * (n + 5) + 3)
    (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) default
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ (a + 1))
      (2 * (n + 5) + 3) 3 (2 * (n + 4) + 2) (by omega)] at h7
  have h8 := bounce_B_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ (a + 1)) <+ ([1] : List (Fin 3)) ^ (2 * (n + 4) + 2))
  exact ((h1.trans h2).trans (h3.trans h4)).trans ((h5.trans h6).trans (h7.trans_plus h8))

private theorem base_4 (a n : ℕ) :
    (cfg_mid a 4 (n + 2)) [target]⊢⁺ (cfg_A a (n + 6) 1) := by
  unfold cfg_mid cfg_A
  have hl : ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ 10) =
      (((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) <+ ([1] : List (Fin 3)) ^ 9) := by
    simp only [ListBlank.append_append]; rfl
  rw [hl]
  have h1 := pass_even ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (n + 2)
  have hr1 : 2 * (n + 2) + 11 = 2 * (n + 7) + 1 := by omega
  rw [hr1] at h1
  have h2 := step_odd_0 (default <+ ([2, 1] : List (Fin 3)) ^ a) (n + 7)
  have h3 := bounce_left_21 a
    (([1] : List (Fin 3)) ^ (2 * (n + 7) + 2) +> (([2, 2] : List (Fin 3)) +> default))
  have h4 := shift_B_1 (2 * (n + 7) + 2)
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) (([2, 2] : List (Fin 3)) +> default)
  rw [combine_B_ones] at h4
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      ((2 * (n + 7) + 2) + 1) 3 (2 * (n + 6) + 2) (by omega)] at h4
  have h5 : ((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 6) + 2)) <+ ([1, 1, 1] : List (Fin 3))) {{B}}>
      (([2, 2] : List (Fin 3)) +> default)) [target]⊢⁺
      (((((default <+ ([2, 1] : List (Fin 3)) ^ a) <+
        ([1] : List (Fin 3)) ^ (2 * (n + 6) + 2)) <+ ([1, 1, 1] : List (Fin 3))) <+
        ([2, 2] : List (Fin 3))) {{B}}> default) := by
    bb_steps
  have h6 := bounce_B_22
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 6) + 2))
  exact (h1.trans h2).trans (h3.trans (h4.trans_plus (h5.trans h6)))

private theorem base_5 (a n : ℕ) :
    (cfg_mid a 5 (n + 2)) [target]⊢⁺ (cfg_A a (n + 8) 0) := by
  unfold cfg_mid cfg_A
  have h1 := drain_step (default <+ ([2, 1] : List (Fin 3)) ^ a) (n + 2)
  have h2 := bounce_left_21 a (([1] : List (Fin 3)) ^ (2 * ((n + 2) + 8)) +> default)
  have h3 := shift_B_1 (2 * ((n + 2) + 8))
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ [1]) default
  rw [combine_B_ones] at h3
  rw [split_ones_left (default <+ ([2, 1] : List (Fin 3)) ^ a)
      (2 * ((n + 2) + 8) + 1) 3 (2 * (n + 8) + 2) (by omega)] at h3
  have h4 := bounce_B_0
    ((default <+ ([2, 1] : List (Fin 3)) ^ a) <+ ([1] : List (Fin 3)) ^ (2 * (n + 8) + 2))
  exact h1.trans (h2.trans (h3.trans_plus h4))

private theorem rule_mod6_0 (a q c : ℕ) :
    (cfg_A a (6 * q + 0) c) [target]⊢⁺ (cfg_A (a + 1) (8 * q + c) 1) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 0 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_0 a (8 * q + c))

private theorem rule_mod6_1_halt (q c : ℕ) :
    ∃ cfg', ((cfg_A 0 (6 * q + 1) c) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  unfold cfg_A
  have h1 := drain_mod6 0 q 1 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  obtain ⟨cfg', h2, hnone⟩ := base_1_halt (8 * q + c)
  exact ⟨cfg', h1.trans_plus h2, hnone⟩

private theorem rule_mod6_1_step (a q c : ℕ) :
    (cfg_A (a + 1) (6 * q + 1) c) [target]⊢⁺ (cfg_A a (8 * q + c + 4) 0) := by
  unfold cfg_A
  have h1 := drain_mod6 (a + 1) q 1 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_1_step a (8 * q + c))

private theorem rule_mod6_2 (a q c : ℕ) :
    (cfg_A a (6 * q + 2) c) [target]⊢⁺ (cfg_A a (8 * q + c + 2) 3) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 2 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_2 a (8 * q + c))

private theorem rule_mod6_3 (a q c : ℕ) :
    (cfg_A a (6 * q + 3) c) [target]⊢⁺ (cfg_A (a + 1) (8 * q + c + 4) 0) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 3 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_3 a (8 * q + c))

private theorem rule_mod6_4 (a q c : ℕ) :
    (cfg_A a (6 * q + 4) c) [target]⊢⁺ (cfg_A a (8 * q + c + 6) 1) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 4 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_4 a (8 * q + c))

private theorem rule_mod6_5 (a q c : ℕ) :
    (cfg_A a (6 * q + 5) c) [target]⊢⁺ (cfg_A a (8 * q + c + 8) 0) := by
  unfold cfg_A
  have h1 := drain_mod6 a q 5 (c + 2)
  have hr : 8 * q + (c + 2) = (8 * q + c) + 2 := by omega
  rw [hr] at h1
  exact h1.trans_plus (base_5 a (8 * q + c))

private theorem mod6_cases (b : ℕ) :
    (b = 6 * (b / 6) + 0) ∨ (b = 6 * (b / 6) + 1) ∨ (b = 6 * (b / 6) + 2) ∨
    (b = 6 * (b / 6) + 3) ∨ (b = 6 * (b / 6) + 4) ∨ (b = 6 * (b / 6) + 5) := by
  omega

private theorem init_to_cfg_A : (init []) [target]⊢⁺ (cfg_A 2 0 0) := by
  unfold cfg_A cfg_mid
  bb_steps

private theorem step_state_plus (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨a, b, c⟩
  dsimp only [next]
  rcases mod6_cases b with h0 | h1 | h2 | h3 | h4 | h5
  · have hr : b % 6 = 0 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A (a + 1) (8 * (b / 6) + c) 1)
    set q := b / 6
    rw [h0]
    exact rule_mod6_0 a q c
  · have hr : b % 6 = 1 := by omega
    rw [hr]
    rcases a with _ | a'
    · change ∃ cfg', ((cfg_A 0 b c) [target]⊢⁺ cfg') ∧ (step target cfg').isNone
      set q := b / 6
      rw [h1]
      exact rule_mod6_1_halt q c
    · change (cfg_A (a' + 1) b c) [target]⊢⁺ (cfg_A a' (8 * (b / 6) + c + 4) 0)
      set q := b / 6
      rw [h1]
      exact rule_mod6_1_step a' q c
  · have hr : b % 6 = 2 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A a (8 * (b / 6) + c + 2) 3)
    set q := b / 6
    rw [h2]
    exact rule_mod6_2 a q c
  · have hr : b % 6 = 3 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A (a + 1) (8 * (b / 6) + c + 4) 0)
    set q := b / 6
    rw [h3]
    exact rule_mod6_3 a q c
  · have hr : b % 6 = 4 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A a (8 * (b / 6) + c + 6) 1)
    set q := b / 6
    rw [h4]
    exact rule_mod6_4 a q c
  · have hr : b % 6 = 5 := by omega
    rw [hr]
    change (cfg_A a b c) [target]⊢⁺ (cfg_A a (8 * (b / 6) + c + 8) 0)
    set q := b / 6
    rw [h5]
    exact rule_mod6_5 a q c

/-- `next` is a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_to_cfg_A.to_star (fun s => ?_)
  have hs := step_state_plus s
  rcases hnext : next s with _ | s'
  · rw [hnext] at hs
    obtain ⟨cfg', hplus, hnone⟩ := hs
    exact ⟨cfg', hplus.to_star, hnone⟩
  · rw [hnext] at hs
    exact hs

/-- `target` halts iff the accelerated transition function `next` halts from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## Level A: Closed `TapePatternSet` (`HasCollatzReduction`) -/

/-- Tape pattern for
$A(a, b, c) = 0^\infty\,(12)^a\,1^{2b+2}\,{<}\mathrm{A}\;1^{2(c+2)}\,0^\infty$. -/
def pat_A : TapePattern (Fin 3) (Fin 3) :=
  { left := .sym 1 (.rep [1, 1] 1 (.rep [2, 1] 0 .default))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 2 .default))))) }

/-- Full `TapePatternSet` for `1RB2RA1LC_2LC1RB2RB_---2LA1LA`. -/
def ps : TapePatternSet (Fin 3) (Fin 3) :=
  [(pat_A, .true)]

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = encode (.A (vars 0) (vars 1) (vars 2)) := by
  dsimp only [pat_A, evalTapePattern, evalTapeExpr, encode, Cfg.headRight, Cfg.headLeft]
  have hl : ([1] : List (Fin 3)) ^ (2 * vars 1 + 2) =
      1 :: 1 :: ([1, 1] : List (Fin 3)) ^ (vars 1) := by
    rw [pair_one_pow]
    have h2 : 2 * vars 1 + 2 = 2 + 2 * vars 1 := by omega
    rw [h2, list_pow_add]; rfl
  have hr : ([1] : List (Fin 3)) ^ (2 * (vars 2 + 2)) =
      1 :: 1 :: 1 :: 1 :: ([1, 1] : List (Fin 3)) ^ (vars 2) := by
    rw [pair_one_pow]
    have h4 : 2 * (vars 2 + 2) = 4 + 2 * vars 2 := by omega
    rw [h4, list_pow_add]; rfl
  rw [hl, hr]
  simp only [ListBlank.append_cons, ListBlank.head_cons, ListBlank.tail_cons]

private theorem mem_encode (s : State) : IsInPatternSet ps (encode s) := by
  rcases s with ⟨a, b, c⟩
  let vars : ℕ → ℕ := fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0
  refine ⟨(pat_A, .true), List.Mem.head _, vars, ?_, trivial⟩
  exact (eval_pat_A vars).symm

private theorem encode_of_mem (cfg : Cfg (Fin 3) (Fin 3))
    (h : IsInPatternSet ps cfg) : ∃ s : State, cfg = encode s := by
  rcases h with ⟨entry, hentry, vars, rfl, _⟩
  rcases List.mem_singleton.mp hentry with rfl
  exact ⟨.A (vars 0) (vars 1) (vars 2), eval_pat_A vars⟩

/-- `ps` is a closed pattern set for `target`. -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine is_valid_acceleration.isClosedPatternSet mem_encode encode_of_mem (fun s hnext => ?_)
  have hs := step_state_plus s
  rw [hnext] at hs
  exact hs

/-- `target` has a Collatz-like reduction via `ps`. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA
