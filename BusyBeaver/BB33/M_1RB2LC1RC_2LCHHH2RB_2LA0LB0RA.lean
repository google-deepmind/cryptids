/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

@[expose] public section

/-!
# Cryptid `1RB2LC1RC_2LC---2RB_2LA0LB0RA` (BB(3, 3) See-Saw Counter Machine)

This file formalizes the Collatz-like reduction for the 3-state, 3-symbol Busy Beaver holdout
Turing machine `1RB2LC1RC_2LC---2RB_2LA0LB0RA` (one of the two See-Saw holdout machines analyzed
by `@dyuan01` and `@LegionMammal978`).

## Canonical Configuration (`State`)

Every macro configuration is parameterized by two natural numbers `(a, c) : ℕ²`:
$$A(a, c) := 0^\infty\, 1\, 2^a\, {<}\mathrm{C}\; (20)^c\, 0^\infty$$
The machine enters $A(0, 1)$ from the blank tape after 2 steps.

## Accelerated Transition Function (`next`)

Contracting `@dyuan01`'s 11-rule 3-counter system on $A_1(a, b, c)$, $A_2(a, b, c)$, and $B(a, b)$
back to $A(a, c) = A_1(a, 0, c)$ yields `@LegionMammal978`'s 10-rule 2-counter map on
$\mathbb{N}^2$:

| Regime | Parities / Condition | Next State |
| :--- | :--- | :--- |
| $a \le c$ | $a \equiv 0 \pmod 2,\; c \equiv 0 \pmod 2$ | **Halt** (`none`) |
| $a \le c$ | $a \equiv 0 \pmod 2,\; c \equiv 1 \pmod 2$ | $A(1,\; a/2 + c + 2)$ |
| $a \le c$ | $a \equiv 1 \pmod 2,\; c \equiv 0 \pmod 2$ | $A(3a,\; c - a + 4)$ |
| $a \le c$ | $a \equiv 1 \pmod 2,\; c \equiv 1 \pmod 2$ | $A(3a + 2,\; c - a + 1)$ |
| $a > c$ | $c \equiv 0, 2 \pmod 4$ | $A(a - c - 1,\; 3\lfloor c/2 \rfloor + 2)$ |
| $a > c$ | $c \equiv 1 \pmod 4,\; a = c + 1$ | **Halt** (`none`) |
| $a > c$ | $c \equiv 1 \pmod 4,\; a \ge c + 2$ | $A(a - c - 2,\; 3\lfloor c/2 \rfloor + 5)$ |
| $a > c$ | $c \equiv 3 \pmod 4,\; a = c + 1 \text{ or } c + 3$ | **Halt** (`none`) |
| $a > c$ | $c \equiv 3 \pmod 4,\; a = c + 2$ | $A(3c + 8,\; 1)$ |
| $a > c$ | $c \equiv 3 \pmod 4,\; a \ge c + 4$ | $A(a - c - 4,\; 3\lfloor c/2 \rfloor + 8)$ |

## References

* <https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA>
* <https://wiki.bbchallenge.org/wiki/BB(3,3)>
-/

namespace BusyBeaver.M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA

open Turing ThreeState

/-- The `(3, 3)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2LC1RC_2LC---2RB_2LA0LB0RA"

/-- The `(3, 3)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

/-- Canonical two-counter configuration `A(a, c)` representing `0^∞ 1 2^a <C (20)^c 0^∞`. -/
inductive State where
  | A (a c : ℕ)
  deriving DecidableEq, Repr

/-- The initial accelerated state `A(0, 1)`, reached after 2 steps from the blank tape. -/
def start : State := .A 0 1

/-- Encoding of `State` into Turing machine configurations. -/
def encode : State → Cfg (Fin 3) (Fin 3)
  | .A a c =>
    Cfg.headLeft C
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ a))
      (([2, 0] : List (Fin 3)) ^ c +> default)

/-- Accelerated transition function on `State` (`none` indicates halting). -/
def next : State → Option State
  | .A a c =>
    if a ≤ c then
      if a % 2 = 0 then
        if c % 2 = 0 then none
        else some (.A 1 (a / 2 + c + 2))
      else if c % 2 = 0 then
        some (.A (3 * a) (c - a + 4))
      else
        some (.A (3 * a + 2) (c - a + 1))
    else if c % 4 = 0 ∨ c % 4 = 2 then
      some (.A (a - c - 1) (3 * (c / 2) + 2))
    else if c % 4 = 1 then
      if a = c + 1 then none
      else some (.A (a - c - 2) (3 * (c / 2) + 5))
    else if a = c + 1 then
      none
    else if a = c + 2 then
      some (.A (3 * c + 8) 1)
    else if a = c + 3 then
      none
    else
      some (.A (a - c - 4) (3 * (c / 2) + 8))

/-! ## Intermediate Configurations and Elementary Walk Lemmas -/

private def cfgA1 (a b c : ℕ) : Cfg (Fin 3) (Fin 3) :=
  (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ a) <{{C}}
    ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ c) +> default)))

private def cfgA2 (a b c : ℕ) : Cfg (Fin 3) (Fin 3) :=
  (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ a) <{{A}}
    (([2] : List (Fin 3)) +>
      ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ c) +> default))))

private def cfgB (a b : ℕ) : Cfg (Fin 3) (Fin 3) :=
  (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ a) <{{B}}
    (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ b) +> default)))

@[simp]
private theorem pair_two_pow (k : ℕ) :
    ([2, 2] : List (Fin 3)) ^ k = ([2] : List (Fin 3)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 2 k

private theorem headLeft_two_succ (q : Fin 3) (m : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([2] : List (Fin 3)) ^ (m + 1)) <{{q}} r) =
      ((l <+ ([2] : List (Fin 3)) ^ m) {{q}}> (([2] : List (Fin 3)) +> r)) := by
  rw [ListBlank.append_pow_succ]
  exact Cfg.headLeft_cons q 2 _ r

private theorem two_append_22_pow_two (b : ℕ) (r : ListBlank (Fin 3)) :
    (([2] : List (Fin 3)) +>
      ((([2, 2] : List (Fin 3)) ^ b) +> (([2] : List (Fin 3)) +> r))) =
      ((([2, 2] : List (Fin 3)) ^ (b + 1)) +> r) := by
  rw [← swap_single_pair_pow 2 b (([2] : List (Fin 3)) +> r)]
  change (([2, 2] : List (Fin 3)) ^ b +> (([2, 2] : List (Fin 3)) +> r)) = _
  exact ListBlank.append_pow_succ' [2, 2] b r

private theorem walkR_B_2 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{B}}> (([2] : List (Fin 3)) ^ k +> r)) [target]⊢*
      ((l <+ ([2] : List (Fin 3)) ^ k) {{B}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (l {{B}}> (([2] : List (Fin 3)) ^ (k + 1) +> r)) [target]⊢⁺
        ((l <+ ([2] : List (Fin 3))) {{B}}> (([2] : List (Fin 3)) ^ k +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([2] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([2] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ k) =
        (l <+ ([2] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem walkR_C_22 (b : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{C}}> (([2, 2] : List (Fin 3)) ^ b +> r)) [target]⊢*
      ((l <+ ([1, 0] : List (Fin 3)) ^ b) {{C}}> r) := by
  induction b generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    have h1 : (l {{C}}> (([2, 2] : List (Fin 3)) ^ (b + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 3))) {{C}}> (([2, 2] : List (Fin 3)) ^ b +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (l <+ ([1, 0] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([1, 0] : List (Fin 3))) <+ ([1, 0] : List (Fin 3)) ^ b) =
        (l <+ ([1, 0] : List (Fin 3)) ^ (b + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem walkR_C_2020 (n : ℕ) (l r : ListBlank (Fin 3)) :
    (l {{C}}> (([2, 0] : List (Fin 3)) ^ (2 * n) +> r)) [target]⊢*
      ((l <+ ([1, 0] : List (Fin 3)) ^ (2 * n)) {{C}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h2n : ([2, 0] : List (Fin 3)) ^ (2 * (n + 1)) =
        ([2, 0, 2, 0] : List (Fin 3)) ++ ([2, 0] : List (Fin 3)) ^ (2 * n) := by
      rw [Nat.mul_succ, Nat.add_comm, list_pow_add]; rfl
    rw [h2n, ← ListBlank.append_append]
    have h1 : (l {{C}}> (([2, 0, 2, 0] : List (Fin 3)) +>
        ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> r))) [target]⊢⁺
        ((l <+ ([1, 0, 1, 0] : List (Fin 3))) {{C}}>
          ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> r)) := by
      bb_steps
    have h2 := ih (l <+ ([1, 0, 1, 0] : List (Fin 3))) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow : ((l <+ ([1, 0, 1, 0] : List (Fin 3))) <+ ([1, 0] : List (Fin 3)) ^ (2 * n)) =
        (l <+ ([1, 0] : List (Fin 3)) ^ (2 * (n + 1))) := by
      have h10 : ([1, 0, 1, 0] : List (Fin 3)) = ([1, 0] : List (Fin 3)) ^ 2 := rfl
      rw [h10, ListBlank.append_append, ← list_pow_add, ← Nat.mul_succ]
    rwa [h_pow] at h3

private theorem walkL_C0_10 (k : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([1, 0] : List (Fin 3)) ^ k) {{C}}> (([0] : List (Fin 3)) +> r)) [target]⊢*
      (l {{C}}> (([0] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([1, 0] : List (Fin 3))) {{C}}>
        (([0] : List (Fin 3)) +> r)) [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 3)) ^ k) {{C}}>
          (([0] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) +> r))) := by
      bb_steps
    have h2 := ih l (([2, 2] : List (Fin 3)) +> r)
    have h3 := (h1.trans_star h2).to_star
    have h_l : ((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([1, 0] : List (Fin 3))) =
        (l <+ ([1, 0] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append]; rfl
    have h_r : (([2, 2] : List (Fin 3)) ^ k +> (([2, 2] : List (Fin 3)) +> r)) =
        (([2, 2] : List (Fin 3)) ^ (k + 1) +> r) :=
      ListBlank.append_pow_succ' [2, 2] k r
    rwa [h_l, h_r] at h3

private theorem walkL_C1_010 (k : ℕ) (l r : ListBlank (Fin 3)) :
    (((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([0] : List (Fin 3))) {{C}}>
        (([1] : List (Fin 3)) +> r)) [target]⊢*
      ((l <+ ([0] : List (Fin 3))) {{C}}>
        (([1] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : ((((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([1, 0] : List (Fin 3))) <+
        ([0] : List (Fin 3))) {{C}}> (([1] : List (Fin 3)) +> r)) [target]⊢⁺
        (((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([0] : List (Fin 3))) {{C}}>
          (([1] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) +> r))) := by
      bb_steps
    have h2 := ih l (([2, 0] : List (Fin 3)) +> r)
    have h3 := (h1.trans_star h2).to_star
    have h_l : ((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([1, 0] : List (Fin 3))) =
        (l <+ ([1, 0] : List (Fin 3)) ^ (k + 1)) := by
      rw [ListBlank.append_append]; rfl
    have h_r : (([2, 0] : List (Fin 3)) ^ k +> (([2, 0] : List (Fin 3)) +> r)) =
        (([2, 0] : List (Fin 3)) ^ (k + 1) +> r) :=
      ListBlank.append_pow_succ' [2, 0] k r
    rwa [h_l, h_r] at h3

private theorem bounce_C_0 (k : ℕ) (l r : ListBlank (Fin 3)) :
    ((l <+ ([1, 0] : List (Fin 3)) ^ k) {{C}}> (([0] : List (Fin 3)) +> r)) [target]⊢⁺
      (l <{{A}} (([2] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ k +> r))) := by
  have h1 := walkL_C0_10 k l r
  have h2 : (l {{C}}> (([0] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ k +> r))) [target]⊢⁺
      (l <{{A}} (([2] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ k +> r))) := by
    bb_steps
  exact h1.trans_plus h2

private theorem bounce_C_default (k : ℕ) (l : ListBlank (Fin 3)) :
    ((l <+ ([1, 0] : List (Fin 3)) ^ k) {{C}}> default) [target]⊢⁺
      (l <{{A}} (([2] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ k +> default))) := by
  have h := bounce_C_0 k l default
  simpa using h

private theorem bounce_C_2 (k : ℕ) (l : ListBlank (Fin 3)) :
    ((l <+ ([1, 0] : List (Fin 3)) ^ k) {{C}}> (([2] : List (Fin 3)) +> default)) [target]⊢⁺
      (l <{{C}} (([2, 0] : List (Fin 3)) ^ (k + 2) +> default)) := by
  have h1 : ((l <+ ([1, 0] : List (Fin 3)) ^ k) {{C}}> (([2] : List (Fin 3)) +> default))
      [target]⊢⁺
      (((l <+ ([1, 0] : List (Fin 3)) ^ k) <+ ([0] : List (Fin 3))) {{C}}>
        (([1] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) +> default))) := by
    bb_steps
  have h2 := walkL_C1_010 k l (([2, 0] : List (Fin 3)) +> default)
  rw [ListBlank.append_pow_succ'] at h2
  have h3 : ((l <+ ([0] : List (Fin 3))) {{C}}>
      (([1] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ (k + 1) +> default))) [target]⊢⁺
      (l <{{C}} (([2, 0] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ (k + 1) +> default))) := by
    bb_steps
  have h4 := (h1.trans_star h2).trans h3
  rwa [← ListBlank.append_pow_succ] at h4

/-! ## Macro Transition Rules R1–R11 -/

private theorem walk_A1_zero (b n : ℕ) (r : ListBlank (Fin 3)) :
    (((default <+ ([1] : List (Fin 3))) <{{C}}
      ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> r)))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
        ([1, 0] : List (Fin 3)) ^ (b + 2 * n + 1)) {{C}}> r) := by
  have h1 : (((default <+ ([1] : List (Fin 3))) <{{C}}
      ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> r)))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
        ([1, 0] : List (Fin 3)) ^ 1) {{C}}>
        ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> r))) := by
    bb_steps
  have h2 := walkR_C_22 b
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
      ([1, 0] : List (Fin 3)) ^ 1)
    ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> r)
  have h3 := walkR_C_2020 n
    ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
      ([1, 0] : List (Fin 3)) ^ 1) <+ ([1, 0] : List (Fin 3)) ^ b) r
  have h4 := (h1.trans_star h2).trans_star h3
  have hl : (((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
      ([1, 0] : List (Fin 3)) ^ 1) <+ ([1, 0] : List (Fin 3)) ^ b) <+
      ([1, 0] : List (Fin 3)) ^ (2 * n)) =
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
        ([1, 0] : List (Fin 3)) ^ (b + 2 * n + 1)) := by
    rw [ListBlank.append_append, ListBlank.append_append, ← list_pow_add, ← list_pow_add]
    exact congrArg
      (fun k => ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1) <+
        ([1, 0] : List (Fin 3)) ^ k)
      (by omega)
  rwa [hl] at h4

private theorem rule_R1 (b n : ℕ) :
    (cfgA1 0 b (2 * n)) [target]⊢⁺ (cfgA2 1 (b + 2 * n + 1) 0) := by
  unfold cfgA1 cfgA2
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := walk_A1_zero b n default
  have h2 := bounce_C_default (b + 2 * n + 1)
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1)
  exact h1.trans h2

private theorem rule_R2 (b n : ℕ) :
    (cfgA1 0 b (2 * n + 1)) [target]⊢⁺ (cfgA1 1 0 (b + 2 * n + 3)) := by
  unfold cfgA1
  simp only [list_pow_zero, ListBlank.append_nil]
  have hr : (([2, 0] : List (Fin 3)) ^ (2 * n + 1) +> default) =
      (([2, 0] : List (Fin 3)) ^ (2 * n) +> (([2] : List (Fin 3)) +> default)) := by
    rw [list_pow_succ', ← ListBlank.append_append]
    simp
  rw [hr]
  have h1 := walk_A1_zero b n (([2] : List (Fin 3)) +> default)
  have h2 := bounce_C_2 (b + 2 * n + 1)
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ 1)
  exact h1.trans h2

private theorem rule_R3 (m b : ℕ) :
    (cfgA1 (m + 1) b 0) [target]⊢⁺ (cfgA1 m 0 (b + 2)) := by
  unfold cfgA1
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [headLeft_two_succ]
  have hr : (([2] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ b +> default)) =
      (([2, 2] : List (Fin 3)) ^ b +> (([2] : List (Fin 3)) +> default)) :=
    (swap_single_pair_pow 2 b default).symm
  rw [hr]
  have h1 := walkR_C_22 b
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m)
    (([2] : List (Fin 3)) +> default)
  have h2 := bounce_C_2 b ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m)
  exact h1.trans_plus h2

private theorem rule_R4 (m b n : ℕ) :
    (cfgA1 (m + 1) b (n + 1)) [target]⊢⁺ (cfgA2 m (b + 1) n) := by
  unfold cfgA1 cfgA2
  rw [headLeft_two_succ]
  have hr : (([2] : List (Fin 3)) +>
      ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ (n + 1)) +> default))) =
      ((([2, 2] : List (Fin 3)) ^ (b + 1)) +>
        (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ n) +> default))) := by
    rw [ListBlank.append_pow_succ]
    exact two_append_22_pow_two b (([0] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ n +> default))
  rw [hr]
  have h1 := walkR_C_22 (b + 1)
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m)
    (([0] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ n +> default))
  have h2 := bounce_C_0 (b + 1)
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m)
    ((([2, 0] : List (Fin 3)) ^ n) +> default)
  exact h1.trans_plus h2

private theorem rule_R10 (m n : ℕ) :
    (cfgB (m + 1) (2 * n)) [target]⊢⁺ (cfgA2 m (2 * n + 1) 0) := by
  unfold cfgB cfgA2
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [headLeft_two_succ]
  have h1 : (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) {{B}}>
      (([2] : List (Fin 3)) +>
        (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> default)))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
        ([1, 0] : List (Fin 3)) ^ 1) {{C}}>
        ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> default)) := by
    bb_steps
  have h2 := walkR_C_2020 n
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
      ([1, 0] : List (Fin 3)) ^ 1) default
  have h3 := h1.trans_star h2
  have hl : ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
      ([1, 0] : List (Fin 3)) ^ 1) <+ ([1, 0] : List (Fin 3)) ^ (2 * n)) =
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
        ([1, 0] : List (Fin 3)) ^ (2 * n + 1)) := by
    rw [ListBlank.append_append, ← list_pow_add, Nat.add_comm]
  rw [hl] at h3
  have h4 := bounce_C_default (2 * n + 1)
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m)
  exact h3.trans h4

private theorem rule_R11 (m n : ℕ) :
    (cfgB (m + 1) (2 * n + 1)) [target]⊢⁺ (cfgA1 m 0 (2 * n + 3)) := by
  unfold cfgB cfgA1
  rw [headLeft_two_succ]
  have hr : (([2, 0] : List (Fin 3)) ^ (2 * n + 1) +> default) =
      (([2, 0] : List (Fin 3)) ^ (2 * n) +> (([2] : List (Fin 3)) +> default)) := by
    rw [list_pow_succ', ← ListBlank.append_append]
    simp
  rw [hr]
  have h1 : (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) {{B}}>
      (([2] : List (Fin 3)) +>
        (([0] : List (Fin 3)) +>
          ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> (([2] : List (Fin 3)) +> default))))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
        ([1, 0] : List (Fin 3)) ^ 1) {{C}}>
        ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> (([2] : List (Fin 3)) +> default))) := by
    bb_steps
  have h2 := walkR_C_2020 n
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
      ([1, 0] : List (Fin 3)) ^ 1)
    (([2] : List (Fin 3)) +> default)
  have h3 := h1.trans_star h2
  have hl : ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
      ([1, 0] : List (Fin 3)) ^ 1) <+ ([1, 0] : List (Fin 3)) ^ (2 * n)) =
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
        ([1, 0] : List (Fin 3)) ^ (2 * n + 1)) := by
    rw [ListBlank.append_append, ← list_pow_add, Nat.add_comm]
  rw [hl] at h3
  have h4 := bounce_C_2 (2 * n + 1)
    ((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m)
  exact h3.trans h4

private theorem walk_A2_zero (b c : ℕ) :
    (cfgA2 0 b c) [target]⊢⁺
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ (2 * b + 3)) {{B}}>
        ((([2, 0] : List (Fin 3)) ^ c) +> default)) := by
  unfold cfgA2
  have h1 : (((default <+ ([1] : List (Fin 3))) <{{A}}
      (([2] : List (Fin 3)) +>
        ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ c) +> default))))) [target]⊢⁺
      ((default <+ ([1] : List (Fin 3))) {{B}}>
        (([2, 2, 2] : List (Fin 3)) +>
          ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ c) +> default)))) := by
    bb_steps
  have hr : (([2, 2, 2] : List (Fin 3)) +>
      ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ c) +> default))) =
      (([2] : List (Fin 3)) ^ (2 * b + 3) +> ((([2, 0] : List (Fin 3)) ^ c) +> default)) := by
    rw [pair_two_pow]
    have h222 : ([2, 2, 2] : List (Fin 3)) = ([2] : List (Fin 3)) ^ 3 := rfl
    rw [h222, ← ListBlank.append_pow_add, Nat.add_comm]
  rw [hr] at h1
  have h2 := walkR_B_2 (2 * b + 3) (default <+ ([1] : List (Fin 3)))
    ((([2, 0] : List (Fin 3)) ^ c) +> default)
  exact h1.trans_star h2

private theorem rule_R5 (b n : ℕ) :
    (cfgA2 0 b (2 * n)) [target]⊢⁺ (cfgA1 (2 * b + 3) 0 (2 * n + 1)) := by
  have h1 := walk_A2_zero b (2 * n)
  cases n with
  | zero =>
    have h2 : (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ (2 * b + 3)) {{B}}>
        default) [target]⊢⁺ (cfgA1 (2 * b + 3) 0 1) := by
      unfold cfgA1
      simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
      bb_steps
    exact h1.trans h2
  | succ k =>
    have hc : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hc, ListBlank.append_pow_succ] at h1
    change _ [target]⊢⁺
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ (2 * b + 3)) {{B}}>
        (([2] : List (Fin 3)) +>
          (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ (2 * k + 1)) +> default)))) at h1
    rw [← headLeft_two_succ B (2 * b + 3)] at h1
    have h2 := rule_R11 (2 * b + 3) k
    have h2k : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
    rw [h2k] at h2
    exact h1.trans h2

private theorem rule_R6 (b n : ℕ) :
    (cfgA2 0 b (2 * n + 1)) [target]⊢⁺ (cfgA2 (2 * b + 3) (2 * n + 1) 0) := by
  have h1 := walk_A2_zero b (2 * n + 1)
  rw [ListBlank.append_pow_succ] at h1
  change _ [target]⊢⁺
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ (2 * b + 3)) {{B}}>
      (([2] : List (Fin 3)) +>
        (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ (2 * n)) +> default)))) at h1
  rw [← headLeft_two_succ B (2 * b + 3)] at h1
  exact h1.trans (rule_R10 (2 * b + 3) n)

private theorem rule_R7 (m b : ℕ) :
    (cfgA2 (m + 1) b 0) [target]⊢⁺ (cfgB m (b + 2)) := by
  unfold cfgA2 cfgB
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [headLeft_two_succ]
  have hr : (([2] : List (Fin 3)) +> (([2, 2] : List (Fin 3)) ^ b +> default)) =
      (([2, 2] : List (Fin 3)) ^ b +> (([2] : List (Fin 3)) +> default)) :=
    (swap_single_pair_pow 2 b default).symm
  rw [hr]
  have h1 : (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) {{A}}>
      (([2] : List (Fin 3)) +>
        ((([2, 2] : List (Fin 3)) ^ b) +> (([2] : List (Fin 3)) +> default)))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
        ([1] : List (Fin 3))) {{C}}>
        ((([2, 2] : List (Fin 3)) ^ b) +> (([2] : List (Fin 3)) +> default))) := by
    bb_steps
  have h2 := walkR_C_22 b
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+ ([1] : List (Fin 3)))
    (([2] : List (Fin 3)) +> default)
  have h3 := bounce_C_2 b
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+ ([1] : List (Fin 3)))
  have h4 : ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
      ([1] : List (Fin 3))) <{{C}} (([2, 0] : List (Fin 3)) ^ (b + 2) +> default)) [target]⊢⁺
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <{{B}}
        (([0] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ (b + 2) +> default))) := by
    bb_steps
  exact ((h1.trans_star h2).trans h3).trans h4

private theorem rule_R8 (m b n : ℕ) :
    (cfgA2 (m + 1) b (n + 1)) [target]⊢⁺ (cfgA1 m (b + 2) n) := by
  unfold cfgA2 cfgA1
  rw [headLeft_two_succ]
  have hr : (([2] : List (Fin 3)) +>
      ((([2, 2] : List (Fin 3)) ^ b) +> ((([2, 0] : List (Fin 3)) ^ (n + 1)) +> default))) =
      ((([2, 2] : List (Fin 3)) ^ (b + 1)) +>
        (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ n) +> default))) := by
    rw [ListBlank.append_pow_succ]
    exact two_append_22_pow_two b (([0] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ n +> default))
  rw [hr]
  have h1 : (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) {{A}}>
      (([2] : List (Fin 3)) +>
        ((([2, 2] : List (Fin 3)) ^ (b + 1)) +>
          (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ n) +> default))))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
        ([1] : List (Fin 3))) {{C}}>
        ((([2, 2] : List (Fin 3)) ^ (b + 1)) +>
          (([0] : List (Fin 3)) +> ((([2, 0] : List (Fin 3)) ^ n) +> default)))) := by
    bb_steps
  have h2 := walkR_C_22 (b + 1)
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+ ([1] : List (Fin 3)))
    (([0] : List (Fin 3)) +> (([2, 0] : List (Fin 3)) ^ n +> default))
  have h3 := bounce_C_0 (b + 1)
    (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+ ([1] : List (Fin 3)))
    ((([2, 0] : List (Fin 3)) ^ n) +> default)
  have h4 : ((((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <+
      ([1] : List (Fin 3))) <{{A}}
      (([2] : List (Fin 3)) +>
        ((([2, 2] : List (Fin 3)) ^ (b + 1)) +> ((([2, 0] : List (Fin 3)) ^ n) +> default))))
      [target]⊢⁺
      (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m) <{{C}}
        ((([2, 2] : List (Fin 3)) ^ (b + 2)) +> ((([2, 0] : List (Fin 3)) ^ n) +> default))) := by
    rw [ListBlank.append_pow_succ [2, 2] (b + 1)]
    bb_steps
  exact ((h1.trans_star h2).trans h3).trans h4

private theorem rule_R9_halt (b : ℕ) : (step target (cfgB 0 b)).isNone := by
  unfold cfgB
  bb_halt

private theorem drain_pair (k a b c : ℕ) :
    (cfgA1 (a + 2 * k) b (c + 2 * k)) [target]⊢* (cfgA1 a (b + 3 * k) c) := by
  induction k generalizing b with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have ha : a + 2 * (k + 1) = (a + 2 * k + 1) + 1 := by omega
    have hc : c + 2 * (k + 1) = (c + 2 * k + 1) + 1 := by omega
    rw [ha, hc]
    have h1 := (rule_R4 (a + 2 * k + 1) b (c + 2 * k + 1)).trans
      (rule_R8 (a + 2 * k) (b + 1) (c + 2 * k))
    have h2 := ih (b + 3)
    have hb : (b + 3) + 3 * k = b + 3 * (k + 1) := by omega
    rw [hb] at h2
    exact (h1.trans_star h2).to_star

private theorem init_reaches_start : (init []) [target]⊢⁺ (encode start) := by
  unfold start encode
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  bb_steps

private theorem step_state_plus (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨a, c⟩
  dsimp only [next]
  by_cases hac : a ≤ c
  · simp only [hac, ↓reduceIte]
    rcases nat_even_or_odd_two_mul a with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hma : (2 * m) % 2 = 0 := by omega
      simp only [hma, ↓reduceIte]
      rcases nat_even_or_odd_two_mul (c - 2 * m) with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hc : c = 2 * r + 2 * m := by omega
        have hmc : c % 2 = 0 := by omega
        simp only [hmc, ↓reduceIte]
        change ∃ cfg', ((cfgA1 (2 * m) 0 c) [target]⊢⁺ cfg') ∧ (step target cfg').isNone
        rw [hc]
        have hdr := drain_pair m 0 0 (2 * r)
        simp only [Nat.zero_add] at hdr
        have hstep := (hdr.trans_plus (rule_R1 (3 * m) r)).trans (rule_R7 0 (3 * m + 2 * r + 1))
        exact ⟨cfgB 0 (3 * m + 2 * r + 3), hstep, rule_R9_halt _⟩
      · have hc : c = (2 * r + 1) + 2 * m := by omega
        have hmc : c % 2 = 1 := by omega
        simp only [hmc, Nat.one_ne_zero, ↓reduceIte]
        change (cfgA1 (2 * m) 0 c) [target]⊢⁺ (cfgA1 1 0 (2 * m / 2 + c + 2))
        have htarget : 2 * m / 2 + c + 2 = 3 * m + 2 * r + 3 := by omega
        rw [htarget, hc]
        have hdr := drain_pair m 0 0 (2 * r + 1)
        simp only [Nat.zero_add] at hdr
        exact hdr.trans_plus (rule_R2 (3 * m) r)
    · have hma : (2 * m + 1) % 2 = 1 := by omega
      simp only [hma, Nat.one_ne_zero, ↓reduceIte]
      rcases nat_even_or_odd_two_mul (c - (2 * m + 1)) with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hc : c = (2 * r + 1) + 2 * m := by omega
        have h1m : 2 * m + 1 = 1 + 2 * m := by omega
        have hmc : c % 2 = 1 := by omega
        simp only [hmc, Nat.one_ne_zero, ↓reduceIte]
        change (cfgA1 (2 * m + 1) 0 c) [target]⊢⁺
          (cfgA1 (3 * (2 * m + 1) + 2) 0 (c - (2 * m + 1) + 1))
        have ha' : 3 * (2 * m + 1) + 2 = 2 * (3 * m + 1) + 3 := by omega
        have hc' : c - (2 * m + 1) + 1 = 2 * r + 1 := by omega
        rw [ha', hc', hc, h1m]
        have hdr := drain_pair m 1 0 (2 * r + 1)
        simp only [Nat.zero_add] at hdr
        exact (hdr.trans_plus (rule_R4 0 (3 * m) (2 * r))).trans (rule_R5 (3 * m + 1) r)
      · have hc : c = (2 * r + 2) + 2 * m := by omega
        have h1m : 2 * m + 1 = 1 + 2 * m := by omega
        have hmc : c % 2 = 0 := by omega
        simp only [hmc, ↓reduceIte]
        change (cfgA1 (2 * m + 1) 0 c) [target]⊢⁺
          (cfgA1 (3 * (2 * m + 1)) 0 (c - (2 * m + 1) + 4))
        have ha' : 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 := by omega
        have hc' : c - (2 * m + 1) + 4 = 2 * (r + 1) + 3 := by omega
        rw [ha', hc', hc, h1m]
        have hdr := drain_pair m 1 0 (2 * r + 2)
        simp only [Nat.zero_add] at hdr
        have hstep1 := (hdr.trans_plus (rule_R4 0 (3 * m) (2 * r + 1))).trans
          (rule_R6 (3 * m + 1) r)
        have h6 : 2 * (3 * m + 1) + 3 = (2 * (3 * m + 1) + 2) + 1 := by omega
        rw [h6] at hstep1
        have hstep2 := hstep1.trans (rule_R7 (2 * (3 * m + 1) + 2) (2 * r + 1))
        have h2r : 2 * r + 1 + 2 = 2 * (r + 1) + 1 := by omega
        rw [h2r] at hstep2
        exact hstep2.trans (rule_R11 (2 * (3 * m + 1) + 1) (r + 1))
  · simp only [hac, ↓reduceIte]
    rcases nat_even_or_odd_two_mul c with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm4 : (2 * m) % 4 = 0 ∨ (2 * m) % 4 = 2 := by omega
      simp only [hm4, ↓reduceIte]
      change (cfgA1 a 0 (2 * m)) [target]⊢⁺ (cfgA1 (a - 2 * m - 1) 0 (3 * (2 * m / 2) + 2))
      have ha' : a = (a - 2 * m - 1 + 1) + 2 * m := by omega
      have hc' : 3 * (2 * m / 2) + 2 = 3 * m + 2 := by omega
      rw [hc']
      conv_lhs => rw [ha']
      have hdr := drain_pair m (a - 2 * m - 1 + 1) 0 0
      simp only [Nat.zero_add] at hdr
      exact hdr.trans_plus (rule_R3 (a - 2 * m - 1) (3 * m))
    · have hnot02 : ¬ ((2 * m + 1) % 4 = 0 ∨ (2 * m + 1) % 4 = 2) := by omega
      simp only [hnot02, ↓reduceIte]
      rcases hd : a - (2 * m + 1) - 1 with _ | d1
      · have ha_eq : a = 2 * m + 1 + 1 := by omega
        have ha2 : 2 * m + 1 + 1 = 2 + 2 * m := by omega
        have hc1 : 2 * m + 1 = 1 + 2 * m := by omega
        have hdr := drain_pair m 2 0 1
        simp only [Nat.zero_add] at hdr
        have hstep : (cfgA1 (2 * m + 1 + 1) 0 (2 * m + 1)) [target]⊢⁺ cfgB 0 (3 * m + 3) := by
          rw [ha2]
          conv_lhs => rw [hc1]
          exact (hdr.trans_plus (rule_R4 1 (3 * m) 0)).trans (rule_R7 0 (3 * m + 1))
        have hhalt : ∃ cfg', ((cfgA1 (2 * m + 1 + 1) 0 (2 * m + 1)) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone :=
          ⟨cfgB 0 (3 * m + 3), hstep, rule_R9_halt _⟩
        by_cases hm1 : (2 * m + 1) % 4 = 1
        · simp only [hm1, ha_eq, ↓reduceIte]
          exact hhalt
        · simp only [hm1, ha_eq, ↓reduceIte]
          exact hhalt
      · have ha_eq : a = (2 * m + 1) + d1 + 2 := by omega
        rcases nat_even_or_odd_two_mul m with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · have hm4 : (2 * (2 * k) + 1) % 4 = 1 := by omega
          have ha1 : a ≠ 2 * (2 * k) + 1 + 1 := by omega
          simp only [hm4, ha1, ↓reduceIte]
          change (cfgA1 a 0 (2 * (2 * k) + 1)) [target]⊢⁺
            (cfgA1 (a - (2 * (2 * k) + 1) - 2) 0 (3 * ((2 * (2 * k) + 1) / 2) + 5))
          have ha' : a = (d1 + 3) + 2 * (2 * k) := by omega
          have hc1 : 2 * (2 * k) + 1 = 1 + 2 * (2 * k) := by omega
          have ha_out : a - (2 * (2 * k) + 1) - 2 = d1 := by omega
          have hc_out : 3 * ((2 * (2 * k) + 1) / 2) + 5 = 2 * (3 * k + 1) + 3 := by omega
          rw [ha_out, hc_out, ha', hc1]
          have hdr := drain_pair (2 * k) (d1 + 3) 0 1
          simp only [Nat.zero_add] at hdr
          have hstep1 := (hdr.trans_plus (rule_R4 (d1 + 2) (3 * (2 * k)) 0)).trans
            (rule_R7 (d1 + 1) (3 * (2 * k) + 1))
          have hb : 3 * (2 * k) + 1 + 2 = 2 * (3 * k + 1) + 1 := by omega
          rw [hb] at hstep1
          exact hstep1.trans (rule_R11 d1 (3 * k + 1))
        · have hnot1 : (2 * (2 * k + 1) + 1) % 4 ≠ 1 := by omega
          have ha1 : a ≠ 2 * (2 * k + 1) + 1 + 1 := by omega
          simp only [hnot1, ha1, ↓reduceIte]
          have hc1 : 2 * (2 * k + 1) + 1 = 1 + 2 * (2 * k + 1) := by omega
          rcases d1 with _ | d2
          · have ha2 : a = 2 * (2 * k + 1) + 1 + 2 := by omega
            simp only [ha2, ↓reduceIte]
            change (cfgA1 (2 * (2 * k + 1) + 1 + 2) 0 (2 * (2 * k + 1) + 1)) [target]⊢⁺
              (cfgA1 (3 * (2 * (2 * k + 1) + 1) + 8) 0 1)
            have ha3 : 2 * (2 * k + 1) + 1 + 2 = 3 + 2 * (2 * k + 1) := by omega
            have ha_out : 3 * (2 * (2 * k + 1) + 1) + 8 = 2 * (6 * k + 7) + 3 := by omega
            rw [ha_out, ha3, hc1]
            have hdr := drain_pair (2 * k + 1) 3 0 1
            simp only [Nat.zero_add] at hdr
            have hstep1 := (hdr.trans_plus (rule_R4 2 (3 * (2 * k + 1)) 0)).trans
              (rule_R7 1 (3 * (2 * k + 1) + 1))
            have hb : 3 * (2 * k + 1) + 1 + 2 = 2 * (3 * k + 3) := by omega
            rw [hb] at hstep1
            have hstep2 := hstep1.trans (rule_R10 0 (3 * k + 3))
            have hb2 : 2 * (3 * k + 3) + 1 = 6 * k + 7 := by omega
            rw [hb2] at hstep2
            exact hstep2.trans (rule_R5 (6 * k + 7) 0)
          · have ha2 : a ≠ 2 * (2 * k + 1) + 1 + 2 := by omega
            simp only [ha2, ↓reduceIte]
            rcases d2 with _ | r
            · have ha3 : a = 2 * (2 * k + 1) + 1 + 3 := by omega
              simp only [ha3, ↓reduceIte]
              change ∃ cfg', ((cfgA1 (2 * (2 * k + 1) + 1 + 3) 0 (2 * (2 * k + 1) + 1))
                [target]⊢⁺ cfg') ∧ (step target cfg').isNone
              have ha4 : 2 * (2 * k + 1) + 1 + 3 = 4 + 2 * (2 * k + 1) := by omega
              rw [ha4, hc1]
              have hdr := drain_pair (2 * k + 1) 4 0 1
              simp only [Nat.zero_add] at hdr
              have hstep1 := (hdr.trans_plus (rule_R4 3 (3 * (2 * k + 1)) 0)).trans
                (rule_R7 2 (3 * (2 * k + 1) + 1))
              have hb : 3 * (2 * k + 1) + 1 + 2 = 2 * (3 * k + 3) := by omega
              rw [hb] at hstep1
              have hstep2 := (hstep1.trans (rule_R10 1 (3 * k + 3))).trans
                (rule_R7 0 (2 * (3 * k + 3) + 1))
              exact ⟨cfgB 0 (2 * (3 * k + 3) + 3), hstep2, rule_R9_halt _⟩
            · have ha3 : a ≠ 2 * (2 * k + 1) + 1 + 3 := by omega
              simp only [ha3, ↓reduceIte]
              change (cfgA1 a 0 (2 * (2 * k + 1) + 1)) [target]⊢⁺
                (cfgA1 (a - (2 * (2 * k + 1) + 1) - 4) 0 (3 * ((2 * (2 * k + 1) + 1) / 2) + 8))
              have ha' : a = (r + 5) + 2 * (2 * k + 1) := by omega
              have ha_out : a - (2 * (2 * k + 1) + 1) - 4 = r := by omega
              have hc_out : 3 * ((2 * (2 * k + 1) + 1) / 2) + 8 = 2 * (3 * k + 4) + 3 := by omega
              rw [ha_out, hc_out, ha', hc1]
              have hdr := drain_pair (2 * k + 1) (r + 5) 0 1
              simp only [Nat.zero_add] at hdr
              have hstep1 := (hdr.trans_plus (rule_R4 (r + 4) (3 * (2 * k + 1)) 0)).trans
                (rule_R7 (r + 3) (3 * (2 * k + 1) + 1))
              have hb1 : 3 * (2 * k + 1) + 1 + 2 = 2 * (3 * k + 3) := by omega
              rw [hb1] at hstep1
              have hstep2 := (hstep1.trans (rule_R10 (r + 2) (3 * k + 3))).trans
                (rule_R7 (r + 1) (2 * (3 * k + 3) + 1))
              have hb2 : 2 * (3 * k + 3) + 1 + 2 = 2 * (3 * k + 4) + 1 := by omega
              rw [hb2] at hstep2
              exact hstep2.trans (rule_R11 r (3 * k + 4))

/-- `next` is a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start.to_star (fun s => ?_)
  have hs := step_state_plus s
  rcases hnext : next s with _ | s'
  · rw [hnext] at hs
    obtain ⟨cfg', hplus, hnone⟩ := hs
    exact ⟨cfg', hplus.to_star, hnone⟩
  · rw [hnext] at hs
    exact hs

/-- `target` halts if and only if the accelerated map `next` reaches `none` from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-- Pattern for `encode (.A 0 c)`: `0^∞ C> 1 (20)^c 0^∞`. -/
def pat_A0 : TapePattern (Fin 3) (Fin 3) :=
  { left := .default
    head := some C
    right := .sym 1 (.rep [2, 0] 1 .default) }

/-- Pattern for `encode (.A (m + 1) c)`: `0^∞ 1 2^m C> 2 (20)^c 0^∞`. -/
def pat_AS : TapePattern (Fin 3) (Fin 3) :=
  { left := .rep [2] 0 (.sym 1 .default)
    head := some C
    right := .sym 2 (.rep [2, 0] 1 .default) }

/-- Two-pattern Collatz-like family covering `{ encode s | s : State }`. -/
def ps : TapePatternSet (Fin 3) (Fin 3) :=
  [(pat_A0, .true), (pat_AS, .true)]

private theorem encode_A_zero (c : ℕ) :
    encode (.A 0 c) =
      Cfg.headRight C default ((1 : Fin 3) >> (([2, 0] : List (Fin 3)) ^ c +> default)) := by
  unfold encode
  exact Cfg.headLeft_cons C 1 default _

private theorem encode_A_succ (m c : ℕ) :
    encode (.A (m + 1) c) =
      Cfg.headRight C (((default <+ ([1] : List (Fin 3))) <+ ([2] : List (Fin 3)) ^ m))
        ((2 : Fin 3) >> (([2, 0] : List (Fin 3)) ^ c +> default)) := by
  unfold encode
  exact Cfg.headLeft_cons C 2 _ _

private theorem mem_encode (s : State) : IsInPatternSet ps (encode s) := by
  rcases s with ⟨a, c⟩
  cases a with
  | zero =>
    refine ⟨(pat_A0, .true), .head _, fun i => if i = 1 then c else 0, ?_, trivial⟩
    rw [encode_A_zero]
    rfl
  | succ m =>
    refine ⟨(pat_AS, .true), .tail _ (.head _), fun i => if i = 0 then m else c, ?_, trivial⟩
    rw [encode_A_succ]
    rfl

private theorem encode_of_mem (cfg : Cfg (Fin 3) (Fin 3))
    (h : IsInPatternSet ps cfg) : ∃ s : State, cfg = encode s := by
  rcases h with ⟨entry, hentry, vars, rfl, -⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl
  · refine ⟨.A 0 (vars 1), ?_⟩
    rw [encode_A_zero]
    rfl
  · refine ⟨.A (vars 0 + 1) (vars 1), ?_⟩
    rw [encode_A_succ]
    rfl

/-- `ps` is a closed Collatz-like pattern set for `target`. -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine is_valid_acceleration.isClosedPatternSet mem_encode encode_of_mem (fun s hnext => ?_)
  have hs := step_state_plus s
  rw [hnext] at hs
  exact hs

/-- `target` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA
