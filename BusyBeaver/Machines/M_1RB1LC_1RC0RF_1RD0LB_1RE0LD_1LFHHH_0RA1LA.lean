/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Collatz Reduction for `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`

We analyze canonical configurations in state `A` facing the blank right half-tape `default`, with
left half-tape consisting of `n` blocks of `U4 = [0, 0, 1, 1]` (`LA n := default <+ U4^n`) followed
by one of five canonical suffixes:
- `R1 (n)`: `(LA n <+ [0, 0, 1]) {{A}}> default`
- `R2 (n)`: `(LA n <+ [0, 0, 1, 0, 0, 1]) {{A}}> default`
- `Q (n)`:  `(LA n <+ [0, 0, 1, 1, 1, 1]) {{A}}> default`
- `S4 (n)`: `(LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1]) {{A}}> default`
- `S6 (n)`: `(LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default`

Starting from the blank tape `init []`, the machine reaches `S6 1` in 66 steps.
The accelerated Collatz-like map `next : State → Option State` evolves the five canonical families
as follows:
- **`R1 (n)`**:
  - `R1 0 ↦ R1 4`
  - `R1 1 ↦ R1 6`
  - `R1 (n' + 2) ↦ R1 (n' + 7)`
- **`R2 (n)`**:
  - `R2 0 ↦ R1 4`
  - `R2 (n' + 1)` drains `n'` blocks of `U4` in pairs (`w = ⌊n'/2⌋`) into
    `W8 = [1, 0, 1, 1, 0, 1, 1, 0]` blocks (`HubTail 7 w r_R2`), which consumes `W8` blocks in
    groups of 5 (`w ↦ w - 5`, `k ↦ k + 31`)
    and branches on `w mod 5` into `R1`, `R2`, `Q`, or `R3 ↦ T1 ↦ R1`.
- **`Q (n)`, `S4 (n)`, `S6 (n)`**:
  - Small values of `n` (`n = 0, 1`) transition directly to `R1`, `R2`, or `HubTail`.
  - General values `n ≥ 1` (`Q`, `S4`) or `n ≥ 2` (`S6`) sweep left in state `D`, converting each
    `U4` block into `B4 = [1, 1, 1, 0]` on the right tape (`Scan 6 b p0010110 rend`), then scan
    across `B4^b` via the 7-prefix finite transducer (`ScanBundle`) interleaved with `D`-drains
    (`HubW8` and `HubTail`), halting on two specific remainder prefixes (`rem_halt_1`, `rem_halt_2`)
    or returning to `{R1, R2, Q, S4, S6}`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

private theorem zero1_append_default : (([0] : List (Fin 2)) +> default) = default := by
  simp only [ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default]

private abbrev B4 : List (Fin 2) := [1, 1, 1, 0]

/-- Left stack block `[0, 0, 1, 1]` (representing `1100` from left to right on the tape). -/
abbrev U4 : List (Fin 2) := [0, 0, 1, 1]

/-- Right sweep block `[0, 1, 1, 0]`. -/
private abbrev V4 : List (Fin 2) := [0, 1, 1, 0]

/-- Canonical 8-bit `D`-drain block `[1, 0, 1, 1, 0, 1, 1, 0]`. -/
private abbrev W8 : List (Fin 2) := [1, 0, 1, 1, 0, 1, 1, 0]

/-- Canonical left tape `LA a := default <+ ([0, 0, 1, 1])^a`. -/
def LA (a : Nat) : ListBlank (Fin 2) := default <+ (U4 ^ a)

private theorem LA_succ (a : Nat) : LA (a + 1) = LA a <+ U4 := by
  unfold LA
  rw [ListBlank.append_pow_add_rev default U4 a 1]
  rfl

private theorem LA_add (a k : Nat) : LA (a + k) = LA a <+ (U4 ^ k) := by
  unfold LA
  exact ListBlank.append_pow_add_rev default U4 a k

-- ============================================================================
-- Section 2: Universal One-Bit & Multi-Bit `LA` Consumption Laws
-- ============================================================================

/-- 8-step trigger from `((l <+ U4) {{A}}> ((1 : Fin 2) >> r))` to `(l {{C}}> ([1, 1, 1, 1,
  0] +> r))`. -/
private theorem step_trigger_1_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> ((1 : Fin 2) >> r)) [target]⊢⁺
    (l {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- 10-step left `{{C}}>` step across one `U4 = [0, 0, 1, 1]` block. -/
private theorem step_C_left_U4_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢⁺
    (l {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> (V4 +> r))) := by
  simp only [U4, V4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Inductive left `{{C}}>` sweep across `U4 ^ k` (`10k` steps). -/
private theorem shift_C_left_U4_0349 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (U4 ^ k)) {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢*
    (l {{C}}> (([1, 1, 1, 1, 0] : List (Fin 2)) +> ((V4 ^ k) +> r))) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_l : (l <+ (U4 ^ (k + 1))) = ((l <+ (U4 ^ k)) <+ U4) := by
      exact ListBlank.append_pow_add_rev l U4 k 1
    rw [h_l]
    have h1 := ReachesPlus.to_star (step_C_left_U4_0349 (l <+ (U4 ^ k)) r)
    have h2 := ih l (V4 +> r)
    have h_r : (V4 ^ k) +> (V4 +> r) = (V4 ^ (k + 1)) +> r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_r] at h2
    exact ReachesStar.trans h1 h2

/-- 9-step left-boundary bounce from `default {{C}}> ([1, 1, 1, 1,
  0] +> r)` to `default {{A}}> (V4 +> (V4 +> r))`. -/
private theorem step_C_bounce_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{C}}> (([1, 1, 1, 1,
      0] : List (Fin 2)) +> r)) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{A}}> (V4 +> (V4 +> r))) := by
  simp only [V4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- 6-step right `{{A}}>` step across one `V4 = [0, 1, 1, 0]` block. -/
private theorem step_A_right_V4_0349 (l r : ListBlank (Fin 2)) :
    (l {{A}}> (V4 +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> r) := by
  simp only [U4, V4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Inductive right `{{A}}>` sweep across `V4 ^ k` (`6k` steps). -/
private theorem shift_A_right_V4_0349 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((V4 ^ k) +> r)) [target]⊢*
    ((l <+ (U4 ^ k)) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [ListBlank.append_pow_succ V4 k r]
    have h1 := ReachesPlus.to_star (step_A_right_V4_0349 l ((V4 ^ k) +> r))
    have h2 := ih (l <+ U4) r
    have h_l : (l <+ U4) <+ (U4 ^ k) = l <+ (U4 ^ (k + 1)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_l] at h2
    exact ReachesStar.trans h1 h2

/-- Universal One-Bit Consumption Theorem (`16a + 29` micro-steps):
    For all `a : Nat` and `r : ListBlank (Fin 2)`,
    `LA (a + 1) {{A}}> ((1 : Fin 2) >> r) ⊢⁺ LA (a + 2) {{A}}> r`. -/
private theorem consume_1_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> ((1 : Fin 2) >> r)) [target]⊢⁺
    (LA (a + 2) {{A}}> r) := by
  rw [LA_succ a]
  have h1 := step_trigger_1_0349 (LA a) r
  have h2 := shift_C_left_U4_0349 a default r
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 := step_C_bounce_0349 ((V4 ^ a) +> r)
  have h4 := step_A_right_V4_0349 default (V4 +> ((V4 ^ a) +> r))
  have h5 := step_A_right_V4_0349 (LA 1) ((V4 ^ a) +> r)
  have h13 := ReachesPlus.trans h12 h3
  have h14 := ReachesPlus.trans h13 h4
  have h_l1 : (default <+ U4) = LA 1 := rfl
  rw [h_l1] at h14
  have h15 := ReachesPlus.trans h14 h5
  have h_l2 : (LA 1 <+ U4) = LA 2 := rfl
  rw [h_l2] at h15
  have h6 := shift_A_right_V4_0349 a (LA 2) r
  have h16 := ReachesPlus.trans_star h15 h6
  have h_la : (LA 2 <+ (U4 ^ a)) = LA (a + 2) := by
    rw [← LA_add 2 a, Nat.add_comm 2 a]
  rw [h_la] at h16
  exact h16

/-- Two-bit consumption on `LA (a + 1)`:
    `LA (a + 1) {{A}}> ([1, 1] +> r) ⊢⁺ LA (a + 3) {{A}}> r`. -/
private theorem consume_2_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 3) {{A}}> r) := by
  have h1 := consume_1_LA_0349 a ((1 : Fin 2) >> r)
  have h2 := consume_1_LA_0349 (a + 1) r
  exact ReachesPlus.trans h1 h2

/-- Three-bit consumption on `LA (a + 1)` (`48a + 135` micro-steps):
    `LA (a + 1) {{A}}> ([1, 1, 1] +> r) ⊢⁺ LA (a + 4) {{A}}> r`. -/
private theorem consume_3_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1, 1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> r) := by
  have h1 := consume_2_LA_0349 a ((1 : Fin 2) >> r)
  have h2 := consume_1_LA_0349 (a + 2) r
  exact ReachesPlus.trans h1 h2

-- ============================================================================
-- Section 3: Local In-Place Rewrites & Combined `LA` Block Consumers
-- ============================================================================

/-- 10-step local rewrite `((l <+ U4) {{A}}> ([0, 1, 0, 1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1,
  0] +> r))`. -/
private theorem rewrite_10_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Combined `[0, 1, 0, 1]` consumer: `LA (a + 1) {{A}}> ([0, 1, 0,
  1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0] +> r)`. -/
private theorem consume_0101_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_10_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans h1 h2

/-- 12-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1,
  0] +> r))`. -/
private theorem rewrite_12_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Combined `[0, 0, 1, 1]` consumer: `LA (a + 1) {{A}}> ([0, 0, 1,
  1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0] +> r)`. -/
private theorem consume_0011_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_12_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans h1 h2

/-- 28-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 0, 1, 1, 0,
  1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1, 0, 0, 1, 1, 0] +> r))`. -/
private theorem rewrite_28_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Combined `[0, 0, 1, 0, 1, 1, 0, 1]` consumer:
    `LA (a + 1) {{A}}> ([0, 0, 1, 0, 1, 1, 0, 1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0, 0, 1, 1,
      0] +> r)`. -/
private theorem consume_00101101_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_28_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0, 0, 1, 1, 0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans h1 h2

/-- 22-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 0, 1, 0,
  1] +> r)) ⊢⁺ ((l <+ U4) {{A}}> ([1, 1, 1, 0, 1, 1, 0] +> r))`. -/
private theorem rewrite_22_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Combined `[0, 0, 1, 0, 1, 0, 1]` consumer:
    `LA (a + 1) {{A}}> ([0, 0, 1, 0, 1, 0, 1] +> r) ⊢⁺ LA (a + 4) {{A}}> ([0, 1, 1, 0] +> r)`. -/
private theorem consume_0010101_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h1 := rewrite_22_0349 (LA a) r
  rw [← LA_succ a] at h1
  have h2 := consume_3_LA_0349 a (([0, 1, 1, 0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans h1 h2

/-- 92-step local rewrite `((l <+ U4) {{A}}> ([0, 0, 1, 0, 1, 1, 1, 0,
  1] +> r)) ⊢⁺ (l {{A}}> ([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] +> r))`. -/
private theorem rewrite_92_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

-- ============================================================================
-- Section 4: Universal Halting Suffix Theorem (`halt_LA_S6_0349`) & `S6(2)`
-- ============================================================================

/-- 4-step prefix step to halting configuration `E(1)` (`1LF---`):
    `l {{A}}> ([0, 0, 0, 0, 1] +> r) ⊢⁺ ((l <+ [1, 1, 1, 1]) {{E}}> ((1 : Fin 2) >> r))`. -/
private theorem step_halt_00001_0349 (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([0, 0, 0, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ [1, 1, 1, 1]) {{E}}> ((1 : Fin 2) >> r)) := by
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

-- ============================================================================
-- Section 5: Universal `D`-Drain Parity-Absorption Laws (`drain_LA_odd/even`)
-- ============================================================================

/-- 48-step entry from `(l <+ U4) {{A}}> ([0, 1, 1, 1, 0, 1, 1, 1, 0] +> r)` to
    `l {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] +> ([1, 0] +> r))`. -/
private theorem step_drain_entry_48_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (([1,
      0] : List (Fin 2)) +> r))) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- 98-step `D`-drain step across two `U4` blocks (`U4 ^ 2 = [0, 0, 1, 1, 0, 0, 1, 1]`):
    `(((l <+ U4) <+ U4) {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] +> r)) ⊢⁺ (l {{D}}> ([1, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 1] +> (W8 +> r)))`. -/
private theorem step_drain_2U4_98_0349 (l r : ListBlank (Fin 2)) :
    (((l <+ U4) <+ U4) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (W8 +> r))) := by
  simp only [U4, W8, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- Inductive `D`-drain across `2 * m` blocks of `U4` (`98m` micro-steps). -/
private theorem shift_drain_2m_0349 (m : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (U4 ^ (2 * m))) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [target]⊢*
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> ((W8 ^ m) +> r))) := by
  induction m generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have h_l : (l <+ (U4 ^ (2 * (m + 1)))) = (((l <+ (U4 ^ (2 * m))) <+ U4) <+ U4) := by
      have h_eq : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h_eq, ListBlank.append_pow_add_rev l U4 (2 * m + 1) 1,
        ListBlank.append_pow_add_rev l U4 (2 * m) 1]
      rfl
    rw [h_l]
    have h1 := ReachesPlus.to_star (step_drain_2U4_98_0349 (l <+ (U4 ^ (2 * m))) r)
    have h2 := ih l (W8 +> r)
    have h_r : (W8 ^ m) +> (W8 +> r) = (W8 ^ (m + 1)) +> r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_r] at h2
    exact ReachesStar.trans h1 h2

/-- 66-step odd left-boundary turnaround from `default {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
  1] +> r)`. -/
private theorem step_drain_odd_end_66_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0] : List (Fin 2)) +> r)) := by
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

/-- 70-step even left-boundary turnaround from `(default <+ U4) {{D}}> ([1, 0, 0, 0, 0, 1, 1, 0,
  1, 0, 1] +> r)`. -/
private theorem step_drain_even_end_70_0349 (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ U4) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem consume_1_LA_zero_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{A}}> ((1 : Fin 2) >> r)) [target]⊢⁺
    (LA 1 {{A}}> r) := by
  simp only [LA, U4, HPow.hPow, 
      ]
  bb_steps

/-- 269-step universal post-drain prefix transition to `LA 7 {{A}}> r`. -/
private theorem step_drain_prefix_269_0349 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0] : List (Fin 2)) +> r))
    [target]⊢⁺ (LA 7 {{A}}> r) := by
  have h1 := consume_1_LA_zero_0349 (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_2_LA_0349 0 (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h3 := step_A_right_V4_0349 (LA 3) (([1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  rw [← LA_succ 3] at h3
  have h4 := consume_2_LA_0349 3 (([0, 1, 1, 0] : List (Fin 2)) +> r)
  have h5 := step_A_right_V4_0349 (LA 6) r
  rw [← LA_succ 6] at h5
  exact ReachesPlus.trans (ReachesPlus.trans (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4) h5

/-- Universal Odd `D`-Drain + Prefix Law (`98m + 383` micro-steps):
    For all `m : Nat` and `r : ListBlank (Fin 2)`,
    `LA (2 * m + 1) {{A}}> ([0, 1, 1, 1, 0, 1, 1, 1, 0] +> r) ⊢⁺ LA 7 {{A}}> ((W8 ^ m) +> ([1,
      0] +> r))`. -/
private theorem drain_LA_odd_to_LA7_0349 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m + 1) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))) := by
  rw [LA_succ (2 * m)]
  have h1 := step_drain_entry_48_0349 (LA (2 * m)) r
  have h2 := shift_drain_2m_0349 m default (([1, 0] : List (Fin 2)) +> r)
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 := step_drain_odd_end_66_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  exact ReachesPlus.trans (ReachesPlus.trans h12 h3) h4

/-- Universal Even `D`-Drain + Prefix Law (`98m + 387` micro-steps, exact +4 step parity offset):
    For all `m : Nat` and `r : ListBlank (Fin 2)`,
    `LA (2 * m + 2) {{A}}> ([0, 1, 1, 1, 0, 1, 1, 1, 0] +> r) ⊢⁺ LA 7 {{A}}> ((W8 ^ m) +> ([1,
      0] +> r))`. -/
private theorem drain_LA_even_to_LA7_0349 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m + 2) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))) := by
  have h_la : LA (2 * m + 2) = ((default <+ U4) <+ (U4 ^ (2 * m))) <+ U4 := by
    rw [LA_succ (2 * m + 1)]
    have h_eq : 2 * m + 1 = 1 + 2 * m := by omega
    unfold LA
    rw [h_eq, ListBlank.append_pow_add_rev default U4 1 (2 * m)]
    rfl
  rw [h_la]
  have h1 := step_drain_entry_48_0349 ((default <+ U4) <+ (U4 ^ (2 * m))) r
  have h2 := shift_drain_2m_0349 m (default <+ U4) (([1, 0] : List (Fin 2)) +> r)
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 := step_drain_even_end_70_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> (([1, 0] : List (Fin 2)) +> r))
  exact ReachesPlus.trans (ReachesPlus.trans h12 h3) h4

-- ============================================================================
-- Section 6: Shared `W8` Segment Consumers & Universal 5-Block `W8` (+31) Law
-- ============================================================================

/-- Shared 17-bit `W8^2 ++ [1]` prefix consumer (`192a + 1616` micro-steps):
    `LA (a + 1) {{A}}> ([1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
      1] +> r) ⊢⁺ LA (a + 14) {{A}}> ([0] +> r)`. -/
private theorem consume_W8_prefix_13_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r))
    [target]⊢⁺ (LA (a + 14) {{A}}> (([0] : List (Fin 2)) +> r)) := by
  have h1 := consume_1_LA_0349 a (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1] : List (Fin 2)) +> r)
  have h2 := step_A_right_V4_0349 (LA (a + 2)) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1] : List (Fin 2)) +> r)
  rw [← LA_succ (a + 2)] at h2
  have h3 := consume_2_LA_0349 (a + 2) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)
  have h4 := consume_0101_LA_0349 (a + 4) (([1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)
  have h5 := consume_0101_LA_0349 (a + 7) (([1, 0, 1] : List (Fin 2)) +> r)
  have h6 := consume_0101_LA_0349 (a + 10) r
  exact ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6

/-- Shared 8-bit `[0, 0, 1, 1, 0, 1, 1, 0]` mid-segment consumer (`96a + 438` micro-steps):
    `LA (a + 1) {{A}}> ([0, 0, 1, 1, 0, 1, 1, 0] +> r) ⊢⁺ LA (a + 7) {{A}}> ([0, 0] +> r)`. -/
private theorem consume_W8_mid_6_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r))
    [target]⊢⁺ (LA (a + 7) {{A}}> (([0, 0] : List (Fin 2)) +> r)) := by
  have h1 := consume_0011_LA_0349 a (([0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_0011_LA_0349 (a + 3) (([0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans h1 h2

/-- Shared 3-block `W8^3` consumer (`288a + 3302` micro-steps):
    `LA (a + 1) {{A}}> ((W8 ^ 3) +> r) ⊢⁺ LA (a + 20) {{A}}> ([0, 0] +> r)`. -/
private theorem consume_W8_3_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> ((W8 ^ 3) +> r))
    [target]⊢⁺ (LA (a + 20) {{A}}> (([0, 0] : List (Fin 2)) +> r)) := by
  have h1 := consume_W8_prefix_13_0349 a (([0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_W8_mid_6_0349 (a + 13) r
  exact ReachesPlus.trans h1 h2

/-- Remaining 2-block `[0, 0] +> (W8^2 +> r)` consumer (`160a + 1898` micro-steps):
    `LA (a + 1) {{A}}> ([0, 0] +> ((W8 ^ 2) +> r)) ⊢⁺ LA (a + 13) {{A}}> r`. -/
private theorem consume_W8_2_tail_12_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0] : List (Fin 2)) +> ((W8 ^ 2) +> r)))
    [target]⊢⁺ (LA (a + 13) {{A}}> r) := by
  have h1 := consume_00101101_LA_0349 a (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h2 := consume_0011_LA_0349 (a + 3) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h3 := consume_0010101_LA_0349 (a + 6) (([1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  have h4 := step_A_right_V4_0349 (LA (a + 10)) (([1, 0, 1, 1, 0] : List (Fin 2)) +> r)
  rw [← LA_succ (a + 10)] at h4
  have h5 := consume_1_LA_0349 (a + 10) (([0, 1, 1, 0] : List (Fin 2)) +> r)
  have h6 := step_A_right_V4_0349 (LA (a + 12)) r
  rw [← LA_succ (a + 12)] at h6
  exact ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6

/-- Universal 5-Block `W8` (+31) Consumption Theorem (`448a + 7442` micro-steps):
    For all `a : Nat` and `r : ListBlank (Fin 2)`,
    `LA (a + 1) {{A}}> ((W8 ^ 5) +> r) ⊢⁺ LA (a + 32) {{A}}> r`. -/
private theorem consume_5_W8_LA_0349 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> ((W8 ^ 5) +> r)) [target]⊢⁺
    (LA (a + 32) {{A}}> r) := by
  have h_w8 : (W8 ^ 5) +> r = (W8 ^ 3) +> ((W8 ^ 2) +> r) := by
    exact ListBlank.append_pow_add W8 3 2 r
  rw [h_w8]
  have h1 := consume_W8_3_0349 a ((W8 ^ 2) +> r)
  have h2 := consume_W8_2_tail_12_0349 (a + 19) r
  exact ReachesPlus.trans h1 h2

private theorem consume_1_LA_zero (r : ListBlank (Fin 2)) :
    (LA 0 {{A}}> (([1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 1 {{A}}> r) := by
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil, 
      ]
  bb_steps

private theorem consume_V4_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA a {{A}}> (([0, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 1) {{A}}> r) := by
  have h := step_A_right_V4_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem consume_1_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 2) {{A}}> r) := consume_1_LA_0349 a r

private theorem consume_0101_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := consume_0101_LA_0349 a r

private theorem consume_0011_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0] : List (Fin 2)) +> r)) := consume_0011_LA_0349 a r

private theorem consume_00101101_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := consume_00101101_LA_0349 a r

private theorem consume_0010101_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 4) {{A}}> (([0, 1, 1, 0] : List (Fin 2)) +> r)) := consume_0010101_LA_0349 a r

private theorem consume_rewrite92_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA a {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_92_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem rewrite_24_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rewrite_24_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_24_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem rewrite_20_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rewrite_20_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_20_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem rewrite_38a_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rewrite_38a_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_38a_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem rewrite_38b_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rewrite_38b_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_38b_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem rewrite_26_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    ((l <+ U4) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rewrite_26_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA (a + 1) {{A}}> (([1, 1, 1, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_26_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem rewrite_56_0349 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rewrite_56_LA (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 1) {{A}}> (([0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA a {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : List (Fin 2)) +> r)) := by
  have h := rewrite_56_0349 (LA a) r
  rwa [← LA_succ a] at h

private theorem drain_D_even_to_LA7 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> r)) := by
  have h2 := shift_drain_2m_0349 m default r
  have h3 := step_drain_odd_end_66_0349 ((W8 ^ m) +> r)
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> r)
  exact ReachesPlus.trans (ReachesStar.trans_plus h2 h3) h4

private theorem drain_D_odd_to_LA7 (m : Nat) (r : ListBlank (Fin 2)) :
    (LA (2 * m + 1) {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 7 {{A}}> ((W8 ^ m) +> r)) := by
  have h_la : LA (2 * m + 1) = (default <+ U4) <+ (U4 ^ (2 * m)) := by
    have h_eq : 2 * m + 1 = 1 + 2 * m := by omega
    unfold LA
    rw [h_eq, ListBlank.append_pow_add_rev default U4 1 (2 * m)]
    rfl
  rw [h_la]
  have h2 := shift_drain_2m_0349 m (default <+ U4) r
  have h3 := step_drain_even_end_70_0349 ((W8 ^ m) +> r)
  have h4 := step_drain_prefix_269_0349 ((W8 ^ m) +> r)
  exact ReachesPlus.trans (ReachesStar.trans_plus h2 h3) h4

private theorem drain_D_any_to_LA7 (k : Nat) (r : ListBlank (Fin 2)) :
    (LA k {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> r)) [target]⊢⁺
      (LA 7 {{A}}> ((W8 ^ (k / 2)) +> r)) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv]
    exact drain_D_even_to_LA7 m r
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    exact drain_D_odd_to_LA7 m r

private theorem drain_A_any_to_LA7 (k : Nat) (r : ListBlank (Fin 2)) :
    (LA (k + 1) {{A}}> (([0, 1, 1, 1, 0, 1, 1, 1,
      0] : List (Fin 2)) +> r)) [target]⊢⁺
      (LA 7 {{A}}> ((W8 ^ (k / 2)) +> (([1, 0] : List (Fin 2)) +> r))) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv]
    exact drain_LA_odd_to_LA7_0349 m r
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    exact drain_LA_even_to_LA7_0349 m r

-- ============================================================================
-- Section 7: Pattern Families & Remainder Lemmas
-- ============================================================================

private def P_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n) {{A}}> default
def R1_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1]) {{A}}> default
def R2_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1]) {{A}}> default
private def R3_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  (LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1]) {{A}}> default
private def T1_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 1, 0, 0,
  1]) {{A}}> default
def Q_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 1, 1, 1]) {{A}}> default
def S4_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1,
  1]) {{A}}> default
def S6_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) := (LA n <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1,
  1]) {{A}}> default

private abbrev r_R2 : List (Fin 2) := [1, 0, 0, 1]
private abbrev r_3 : List (Fin 2) := [1, 0, 1, 1, 0, 1, 0, 0, 1]
private abbrev r_4 : List (Fin 2) := [1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
private abbrev r_5 : List (Fin 2) := [1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1]

private abbrev r_Q : List (Fin 2) := [1]
private abbrev r_S6 : List (Fin 2) := [1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
private abbrev r_S4 : List (Fin 2) := [1, 0, 1, 1, 0, 0, 1]

private def HubTail (k w : Nat) (rt : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (LA k) {{A}}> ((W8 ^ w) +> (rt +> default))

private def HubW8 (k w b : Nat) (rend : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (LA k) {{A}}> ((W8 ^ w) +> (([1, 0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default))))

private def Scan (k b : Nat) (pfx rend : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (LA k) {{A}}> (pfx +> ((B4 ^ b) +> (rend +> default)))

-- B4 Left-Sweep Lemmas
private theorem Q_entry_40 (l : ListBlank (Fin 2)) :
    ((l <+ ([0, 0, 1, 1, 1, 1] : List (Fin 2))) {{A}}> default) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (r_Q +> default))) := by
  simp only [r_Q, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem S4_entry_100 (l : ListBlank (Fin 2)) :
    ((l <+ ([0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1] : List (Fin 2))) {{A}}> default) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (r_S4 +> default))) := by
  simp only [r_S4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem S6_entry_152 (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ ([0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1,
      1] : List (Fin 2))) {{A}}> default) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (r_S6 +> default))) := by
  simp only [U4, r_S6, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem step_D_B4_50 (l r : ListBlank (Fin 2)) :
    ((l <+ U4) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> r)) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> (B4 +> r))) := by
  simp only [U4, B4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem shift_D_B4 (n : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (U4 ^ n)) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> r)) [target]⊢*
    (l {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1, 0] : List (Fin 2)) +> ((B4 ^ n) +> r))) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h_l : (l <+ (U4 ^ (n + 1))) = ((l <+ (U4 ^ n)) <+ U4) :=
      ListBlank.append_pow_add_rev l U4 n 1
    rw [h_l]
    have h1 := ReachesPlus.to_star (step_D_B4_50 (l <+ (U4 ^ n)) r)
    have h2 := ih l (B4 +> r)
    have h_r : (B4 ^ n) +> (B4 +> r) = (B4 ^ (n + 1)) +> r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_r] at h2
    exact ReachesStar.trans h1 h2

private theorem step_D_B4_bounce_58 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 1 {{A}}> (([0, 0, 0, 1, 1, 0, 1, 1, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil, 
      ]
  bb_steps

private theorem step_D_B4_bounce_125 (r : ListBlank (Fin 2)) :
    (LA 1 {{A}}> (([0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1] : List (Fin 2)) +> r)) [target]⊢⁺
    (LA 1 {{A}}> (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil, 
      ]
  bb_steps

private theorem step_D_B4_bounce_to_LA6 (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> (([1] : List (Fin 2)) +> r))) [target]⊢⁺
    (LA 6 {{A}}> (([0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have h1 := step_D_B4_bounce_58 (([1] : List (Fin 2)) +> r)
  have h2 := step_D_B4_bounce_125 r
  have h3 := consume_2_LA_0349 0 (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)
  have h4 := consume_V4_LA 3 (([1, 1, 0, 0, 1, 0] : List (Fin 2)) +> r)
  have h5 := consume_2_LA_0349 3 (([0, 0, 1, 0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans (ReachesPlus.trans (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4) h5

private theorem sweep_D_B4_to_Scan (n : Nat) (rend : List (Fin 2)) :
    (LA (n + 1) {{D}}> (([1, 0, 0, 0, 0, 0, 0, 1, 1,
      0] : List (Fin 2)) +> (rend +> default))) [target]⊢⁺
    (Scan 6 n [0, 0, 1, 0, 1, 1, 0] rend) := by
  have h1 := shift_D_B4 (n + 1) default (rend +> default)
  have h2 := step_D_B4_bounce_to_LA6 (([1, 1, 0] : List (Fin 2)) +> ((B4 ^ n) +> (rend +> default)))
  exact ReachesStar.trans_plus h1 h2

-- Remainder Lemmas
private theorem rem_halt_1 (k : Nat) :
    ∃ cfg', ((LA k {{A}}> (([0, 0, 0, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺ cfg') ∧
      (step target cfg').isNone := by
  have h := step_halt_00001_0349 (LA k) default
  refine ⟨_, h, ?_⟩
  simp only [step, E, target]
  rfl

private theorem rem_halt_2 (k : Nat) :
    ∃ cfg', ((LA k {{A}}> (([0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ cfg') ∧
      (step target cfg').isNone := by
  have h := step_halt_00001_0349 (LA k) (([1, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
  refine ⟨_, h, ?_⟩
  simp only [step, E, target]
  rfl

private theorem rem_to_Q_0001_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺
    ((l <+ [0, 0, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_Q_0001 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (Q_cfg k) := by
  rw [LA_succ k]; exact rem_to_Q_0001_raw (LA k)

private theorem rem_to_S6_0001011001_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_S6_0001011001 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (S6_cfg k) := by
  rw [LA_succ k]; exact rem_to_S6_0001011001_raw (LA k)

private theorem rem_to_S4_00011001_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_S4_00011001 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (S4_cfg k) := by
  rw [LA_succ k]; exact rem_to_S4_00011001_raw (LA k)

private theorem rem_to_R1_001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺ (R1_cfg k) := by
  unfold R1_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_R1_0010 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0] : List (Fin 2)) +> default)) [target]⊢⁺ (R1_cfg k) := by
  unfold R1_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_R1_01 (k : Nat) :
    (LA k {{A}}> (([0, 1] : List (Fin 2)) +> default)) [target]⊢⁺ (R1_cfg k) := by
  unfold R1_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_R2_001001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (R2_cfg k) := by
  unfold R2_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_R2_00101 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺ (R2_cfg k) := by
  unfold R2_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_R2_01001 (k : Nat) :
    (LA k {{A}}> (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺ (R2_cfg k) := by
  unfold R2_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_R3_00101001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (R3_cfg k) := by
  unfold R3_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_T1_001011001 (k : Nat) :
    (LA k {{A}}> (([0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (T1_cfg k) := by
  unfold T1_cfg
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_S6_011101_raw (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1] : List (Fin 2)) +> default)) [target]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_to_S6_011101 (k : Nat) :
    (LA (k + 2) {{A}}> (([0, 1, 1, 1, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺ (S6_cfg k) := by
  rw [LA_succ (k + 1), LA_succ k]
  exact rem_to_S6_011101_raw (LA k)

private theorem rem_ddrain_82_raw (l : ListBlank (Fin 2)) :
    ((l <+ U4) {{A}}> (([0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (r_3 +> default))) := by
  simp only [U4, r_3, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_ddrain_82 (k : Nat) :
    (LA (k + 1) {{A}}> (([0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
      (HubTail 7 (k / 2) r_3) := by
  rw [LA_succ k]
  have h1 := rem_ddrain_82_raw (LA k)
  have h2 := drain_D_any_to_LA7 k (r_3 +> default)
  exact ReachesPlus.trans h1 h2

private theorem rem_ddrain_158_raw (l : ListBlank (Fin 2)) :
    ((((l <+ U4) <+ U4) <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> (W8 +> (r_4 +> default)))) := by
  simp only [U4, W8, r_4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_ddrain_158 (k : Nat) :
    (LA (k + 3) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
      (HubTail 7 (k / 2 + 1) r_4) := by
  rw [LA_succ (k + 2), LA_succ (k + 1), LA_succ k]
  have h1 := rem_ddrain_158_raw (LA k)
  have h2 := drain_D_any_to_LA7 k (W8 +> (r_4 +> default))
  have h_w8 : (W8 ^ (k / 2)) +> (W8 +> (r_4 +> default)) =
      (W8 ^ (k / 2 + 1)) +> (r_4 +> default) := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_w8] at h2
  exact ReachesPlus.trans h1 h2

private theorem rem_ddrain_232_raw (l : ListBlank (Fin 2)) :
    ((((l <+ U4) <+ U4) <+ U4) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1] : List (Fin 2)) +> (W8 +> (r_5 +> default)))) := by
  simp only [U4, W8, r_5, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem rem_ddrain_232 (k : Nat) :
    (LA (k + 3) {{A}}> (([0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) [target]⊢⁺
      (HubTail 7 (k / 2 + 1) r_5) := by
  rw [LA_succ (k + 2), LA_succ (k + 1), LA_succ k]
  have h1 := rem_ddrain_232_raw (LA k)
  have h2 := drain_D_any_to_LA7 k (W8 +> (r_5 +> default))
  have h_w8 : (W8 ^ (k / 2)) +> (W8 +> (r_5 +> default)) =
      (W8 ^ (k / 2 + 1)) +> (r_5 +> default) := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_w8] at h2
  exact ReachesPlus.trans h1 h2

-- ============================================================================
-- Section 8: TapePatternSet & Membership Lemmas (36 Patterns)
-- ============================================================================

private abbrev p0 : List (Fin 2) := [0]
private abbrev p001010 : List (Fin 2) := [0, 0, 1, 0, 1, 0]
private abbrev p0010 : List (Fin 2) := [0, 0, 1, 0]
private abbrev p0010110 : List (Fin 2) := [0, 0, 1, 0, 1, 1, 0]
private abbrev p00 : List (Fin 2) := [0, 0]
private abbrev p010 : List (Fin 2) := [0, 1, 0]
private abbrev pnil : List (Fin 2) := []

def pat_Master : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [0, 0, 1] 1 (.rep [1] 2 (.rep [0, 0, 1, 1] 0 .default))
    head  := some A
    right := .default }

def cond_Master : VarCond :=
  .or (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2)) (.not (.ge_const 2 1))))
    (.or (.and (.ge_const 1 2) (.and (.not (.ge_const 1 3)) (.not (.ge_const 2 1))))
      (.or (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2)) (.and (.ge_const 2 3) (.not
        (.ge_const 2 4)))))
        (.or (.and (.ge_const 1 3) (.and (.not (.ge_const 1 4)) (.and (.ge_const 2 3) (.not
          (.ge_const 2 4)))))
             (.and (.ge_const 1 3) (.and (.not (.ge_const 1 4)) (.and (.ge_const 2 5) (.not
               (.ge_const 2 6))))))))

def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_Master, cond_Master)]

private theorem eval_pat_R1 (vars : Nat -> Nat) (h1 : vars 1 = 1) (h2 : vars 2 = 0) :
    evalTapePattern pat_Master vars = R1_cfg (vars 0) := by
  simp only [pat_Master, R1_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

private theorem eval_pat_R2 (vars : Nat -> Nat) (h1 : vars 1 = 2) (h2 : vars 2 = 0) :
    evalTapePattern pat_Master vars = R2_cfg (vars 0) := by
  simp only [pat_Master, R2_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

private theorem eval_pat_Q (vars : Nat -> Nat) (h1 : vars 1 = 1) (h2 : vars 2 = 3) :
    evalTapePattern pat_Master vars = Q_cfg (vars 0) := by
  simp only [pat_Master, Q_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

private theorem eval_pat_S4 (vars : Nat -> Nat) (h1 : vars 1 = 3) (h2 : vars 2 = 3) :
    evalTapePattern pat_Master vars = S4_cfg (vars 0) := by
  simp only [pat_Master, S4_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

private theorem eval_pat_S6 (vars : Nat -> Nat) (h1 : vars 1 = 3) (h2 : vars 2 = 5) :
    evalTapePattern pat_Master vars = S6_cfg (vars 0) := by
  simp only [pat_Master, S6_cfg, LA, evalTapePattern, evalTapeExpr, h1, h2]
  rfl

private theorem in_R1 (n : Nat) : IsInPatternSet ps (R1_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 1 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_R1 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
private theorem in_R2 (n : Nat) : IsInPatternSet ps (R2_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 2 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_R2 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
private theorem in_Q (n : Nat) : IsInPatternSet ps (Q_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 1 | 2 => 3 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_Q vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
private theorem in_S4 (n : Nat) : IsInPatternSet ps (S4_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 3 | 2 => 3 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_S4 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
private theorem in_S6 (n : Nat) : IsInPatternSet ps (S6_cfg n) := by
  let vars : Nat -> Nat := fun i => match i with | 0 => n | 1 => 3 | 2 => 5 | _ => 0
  refine ⟨(pat_Master, cond_Master), List.Mem.head _, vars, (eval_pat_S6 vars rfl rfl).symm, ?_⟩
  simp only [cond_Master, evalVarCond, vars]
  (try omega)
inductive State where
  | R1 (n : ℕ)
  | R2 (n : ℕ)
  | Q (n : ℕ)
  | S4 (n : ℕ)
  | S6 (n : ℕ)

def start : State := .S6 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .R1 n => R1_cfg n
  | .R2 n => R2_cfg n
  | .Q n => Q_cfg n
  | .S4 n => S4_cfg n
  | .S6 n => S6_cfg n

private theorem encode_in_ps (s : State) : IsInPatternSet ps (encode s) := by
  cases s with
  | R1 n => exact in_R1 n
  | R2 n => exact in_R2 n
  | Q n => exact in_Q n
  | S4 n => exact in_S4 n
  | S6 n => exact in_S6 n

/-! ### Accelerated transition function `next`

The accelerated map is assembled from pure arithmetic helpers. Throughout, `HubTail`/`HubW8`
helpers take the *offset* `a` of the left stack `LA (a + 7)`, and `ScanBundle` helpers take the
offset `a` of `LA (a + 4)`; every helper returns the next core state (or `none` on halting). -/

/-- `P_cfg n` (`LA n {{A}}> default`): `P 0 ↦ S6 1`, `P 1 ↦ S4 0`, `P (n + 2) ↦ S6 n`. -/
def next_P (n : ℕ) : Option State :=
  Nat.casesOn n (some (.S6 1)) fun n =>
  Nat.casesOn n (some (.S4 0)) fun n' =>
  some (.S6 n')

/-- `R1 0 ↦ R1 4`, `R1 1 ↦ R1 6`, `R1 (n + 2) ↦ R1 (n + 7)`. -/
def next_R1 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 4)) fun n =>
  Nat.casesOn n (some (.R1 6)) fun n' =>
  some (.R1 (n' + 7))

/-- `T1_cfg n`: `T1 0 ↦ R1 7`, `T1 (n + 1) ↦ R1 (n + 8)`. -/
def next_T1 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 7)) fun n' =>
  some (.R1 (n' + 8))

/-- `R3_cfg n`: `R3 0 ↦ T1 4`, `R3 1 ↦ T1 6`, `R3 (n + 2) ↦ T1 (n + 7)`. -/
def next_R3 (n : ℕ) : Option State :=
  Nat.casesOn n (next_T1 4) fun n =>
  Nat.casesOn n (next_T1 6) fun n' =>
  next_T1 (n' + 7)

/-- `HubTail (a + 7) w r_R2`: consume `W8` blocks five at a time (`a ↦ a + 31`), branching on the
remainder `w mod 5`. -/
def next_HubTail_r_R2 : ℕ → ℕ → Option State
  | a, 0 => some (.R1 (a + 8))
  | a, 1 => some (.R2 (a + 11))
  | a, 2 => some (.Q (a + 19))
  | a, 3 => some (.R2 (a + 26))
  | a, 4 => next_R3 (a + 32)
  | a, w' + 5 => next_HubTail_r_R2 (a + 31) w'

/-- `HubTail (a + 7) w r_3`; the remainder `w = 3` halts. -/
def next_HubTail_r_3 : ℕ → ℕ → Option State
  | a, 0 => some (.R1 (a + 10))
  | a, 1 => some (.Q (a + 16))
  | a, 2 => some (.R2 (a + 23))
  | _, 3 => none
  | a, 4 => some (.R2 (a + 37))
  | a, w' + 5 => next_HubTail_r_3 (a + 31) w'

/-- `HubTail (a + 7) w r_4`. -/
def next_HubTail_r_4 : ℕ → ℕ → Option State
  | a, 0 => next_T1 (a + 9)
  | a, 1 => some (.R2 (a + 15))
  | a, 2 => some (.R1 (a + 25))
  | a, 3 => some (.S6 (a + 28))
  | a, 4 => some (.R2 (a + 41))
  | a, w' + 5 => next_HubTail_r_4 (a + 31) w'

/-- `HubTail (a + 7) w r_5`. -/
def next_HubTail_r_5 : ℕ → ℕ → Option State
  | a, 0 => some (.R1 (a + 12))
  | a, 1 => some (.R1 (a + 15))
  | a, 2 => some (.R2 (a + 26))
  | a, 3 => some (.Q (a + 34))
  | a, 4 => next_T1 (a + 38)
  | a, w' + 5 => next_HubTail_r_5 (a + 31) w'

/-- Successor maps of the seven `Scan` prefixes `p0`, `p001010`, `p0010`, `p0010110`, `p00`,
`p010`, `pnil`, each as a function of the offset `a` of `LA (a + 4)`, together with the two carry
components `p0_next`/`p0010_next` giving the `p0`/`p0010` successor maps one `B4` block further
(these let the bundles be defined by plain structural recursion on the block count). -/
structure NextScanBundle where
  p0 : ℕ → Option State
  p001010 : ℕ → Option State
  p0010 : ℕ → Option State
  p0010110 : ℕ → Option State
  p00 : ℕ → Option State
  p010 : ℕ → Option State
  pnil : ℕ → Option State
  p0_next : ℕ → Option State
  p0010_next : ℕ → Option State

/-- `HubW8 (a + 7) w b rend`: consume `W8` blocks five at a time, then hand over to the `Scan`
prefix selected by the remainder `w mod 5`. -/
def next_HubW8 (nb : NextScanBundle) : ℕ → ℕ → Option State
  | a, 0 => nb.p0 (a + 4)
  | a, 1 => nb.p010 (a + 7)
  | a, 2 => nb.p00 (a + 16)
  | a, 3 => nb.p0010 (a + 22)
  | a, 4 => nb.p001010 (a + 28)
  | a, w' + 5 => next_HubW8 nb (a + 31) w'

/-- `Scan (a + 4) b pfx r_Q` successor maps, by recursion on the number `b` of `B4` blocks. -/
def next_ScanBundle_r_Q (b : ℕ) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.R1 (a + 4))
      p001010 := fun a => next_P (a + 8)
      p0010 := fun a => some (.R2 (a + 4))
      p0010110 := fun a => next_P (a + 10)
      p00 := fun a => some (.R1 (a + 4))
      p010 := fun a => next_P (a + 7)
      pnil := fun a => next_P (a + 5)
      p0_next := fun a => some (.S6 (a + 2))
      p0010_next := fun a => some (.R1 (a + 9)) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

/-- `Scan (a + 4) b pfx r_S6` successor maps; the prefix `p0010110` with `b = 0` halts. -/
def next_ScanBundle_r_S6 (b : ℕ) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.S4 (a + 9))
      p001010 := fun a => next_T1 (a + 11)
      p0010 := fun a => some (.R1 (a + 10))
      p0010110 := fun _ => none
      p00 := fun a => some (.R2 (a + 11))
      p010 := fun a => some (.R1 (a + 14))
      pnil := fun a => next_T1 (a + 8)
      p0_next := fun a => next_HubTail_r_4 0 ((a + 1) / 2 + 1)
      p0010_next := fun a => next_HubTail_r_3 0 ((a + 8) / 2) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

/-- `Scan (a + 4) b pfx r_S4` successor maps. -/
def next_ScanBundle_r_S4 (b : ℕ) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.R2 (a + 7))
      p001010 := fun a => some (.R1 (a + 9))
      p0010 := fun a => some (.R1 (a + 9))
      p0010110 := fun a => some (.S4 (a + 9))
      p00 := fun a => next_T1 (a + 4)
      p010 := fun a => some (.Q (a + 9))
      pnil := fun a => some (.R1 (a + 6))
      p0_next := fun a => next_HubTail_r_5 0 ((a + 1) / 2 + 1)
      p0010_next := fun a => some (.R1 (a + 13)) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

/-- `R2 0 ↦ R1 4`; `R2 (n + 1)` drains `n` stack blocks in pairs into `HubTail 7 (n / 2) r_R2`. -/
def next_R2 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 4)) fun n' =>
  next_HubTail_r_R2 0 (n' / 2)

/-- `Q 0 ↦ R1 6`; `Q (n + 1)` sweeps into `Scan 6 n p0010110 r_Q`. -/
def next_Q (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 6)) fun n' =>
  (next_ScanBundle_r_Q n').p0010110 2

/-- `S4 0 ↦ R1 10`; `S4 (n + 1)` sweeps into `Scan 6 n p0010110 r_S4`. -/
def next_S4 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 10)) fun n' =>
  (next_ScanBundle_r_S4 n').p0010110 2

/-- `S6 0 ↦ R1 9`; `S6 1` drains into `HubTail 7 2 r_3`; `S6 (n + 2)` sweeps into
`Scan 6 n p0010110 r_S6`. -/
def next_S6 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 9)) fun n =>
  Nat.casesOn n (next_HubTail_r_3 0 2) fun n' =>
  (next_ScanBundle_r_S6 n').p0010110 2

/-- The accelerated Collatz-like transition function on the five core families. -/
def next : State → Option State
  | .R1 n => next_R1 n
  | .R2 n => next_R2 n
  | .Q n => next_Q n
  | .S4 n => next_S4 n
  | .S6 n => next_S6 n

/-- `c` advances in `ReachesPlus` to `encode s` (if `o = some s`) or to a halting configuration (if
`o = none`). -/
private def StepsTo (c : Cfg (Fin 2) (Fin 6)) : Option State → Prop
  | some s => c [target]⊢⁺ encode s
  | none => ∃ cfg', (c [target]⊢⁺ cfg') ∧ (step target cfg').isNone

private theorem StepsTo.toProp {c : Cfg (Fin 2) (Fin 6)} {o : Option State} (h : StepsTo c o) :
    ∃ cfg', (c [target]⊢⁺ cfg') ∧ (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  cases o with
  | some s => exact ⟨encode s, h, Or.inl (encode_in_ps s)⟩
  | none =>
    rcases h with ⟨cfg', hs, hnone⟩
    exact ⟨cfg', hs, Or.inr hnone⟩

private theorem reaches_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {o : Option State}
    (h₁ : c₁ [target]⊢⁺ c₂) (h₂ : StepsTo c₂ o) : StepsTo c₁ o := by
  cases o with
  | some s => exact h₁.trans h₂
  | none =>
    rcases h₂ with ⟨cfg', h_plus, h_none⟩
    exact ⟨cfg', h₁.trans h_plus, h_none⟩

/-- The seven `Scan (a + 4) b pfx rend` families all advance to the states given by `nb`. -/
private def ScanBundle (b : Nat) (rend : List (Fin 2)) (nb : NextScanBundle) : Prop :=
  (∀ a, StepsTo (Scan (a + 4) b p0 rend) (nb.p0 a)) ∧
  (∀ a, StepsTo (Scan (a + 4) b p001010 rend) (nb.p001010 a)) ∧
  (∀ a, StepsTo (Scan (a + 4) b p0010 rend) (nb.p0010 a)) ∧
  (∀ a, StepsTo (Scan (a + 4) b p0010110 rend) (nb.p0010110 a)) ∧
  (∀ a, StepsTo (Scan (a + 4) b p00 rend) (nb.p00 a)) ∧
  (∀ a, StepsTo (Scan (a + 4) b p010 rend) (nb.p010 a)) ∧
  (∀ a, StepsTo (Scan (a + 4) b pnil rend) (nb.pnil a))

-- Section 9: Closure Lemmas (Inductively Folded to 5 Core Patterns)

private theorem step_P_0 : (P_cfg 0) [target]⊢⁺ (P_cfg 3) := by
  unfold P_cfg
  simp only [LA, U4, HPow.hPow]
  bb_steps

private theorem step_P_1 : (P_cfg 1) [target]⊢⁺ (S4_cfg 0) := by
  unfold P_cfg S4_cfg
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_P_2plus_raw (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ U4) {{A}}> default) [target]⊢⁺
    ((l <+ [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]) {{A}}> default) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_P (n : Nat) : StepsTo (P_cfg n) (next_P n) := by
  rcases n with _ | _ | n'
  · have h3 : (P_cfg 3) [target]⊢⁺ (S6_cfg 1) := by
      unfold P_cfg; rw [LA_succ 2, LA_succ 1]; exact step_P_2plus_raw (LA 1)
    exact ReachesPlus.trans step_P_0 h3
  · exact step_P_1
  · unfold P_cfg
    rw [LA_succ (n' + 1), LA_succ n']
    exact step_P_2plus_raw (LA n')

private theorem step_R1_0 : (R1_cfg 0) [target]⊢⁺ (R1_cfg 4) := by
  unfold R1_cfg
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem R1_entry_77 (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ [0, 0, 1]) {{A}}> default) [target]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem step_R1 (n : Nat) : StepsTo (R1_cfg n) (next_R1 n) := by
  rcases n with _ | _ | n'
  · exact step_R1_0
  · have h1 := R1_entry_77 default
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have h12 := ReachesPlus.trans h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have h_rem := rem_to_R1_001 6
    exact ReachesPlus.trans hc_4 h_rem
  · unfold R1_cfg
    rw [LA_succ (n' + 1)]
    have h1 := R1_entry_77 (LA (n' + 1))
    have hs_0 := consume_1_LA n' (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h1 hs_0
    have hs_1 := consume_1_LA (n' + 1) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_1_LA (n' + 2) (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_V4_LA (n' + 4) (([1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA (n' + 4) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (n' + 5) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have h_rem := rem_to_R1_001 (n' + 7)
    exact ReachesPlus.trans hc_5 h_rem

private theorem T1_entry_84 (l : ListBlank (Fin 2)) :
    ((l <+ [0, 0, 1, 0, 0, 1, 1, 0, 0, 1]) {{A}}> default) [target]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)) := by
  simp only [ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem step_T1 (n : Nat) : StepsTo (T1_cfg n) (next_T1 n) := by
  rcases n with _ | n'
  · have h1 := T1_entry_84 default
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have h12 := ReachesPlus.trans h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_V4_LA 6 (([0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have h_rem := rem_to_R1_01 7
    exact ReachesPlus.trans hc_5 h_rem
  · have h1 := T1_entry_84 (LA (n' + 1))
    have hs_0 := consume_1_LA n' (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h1 hs_0
    have hs_1 := consume_1_LA (n' + 1) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_1_LA (n' + 2) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_V4_LA (n' + 4) (([1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA (n' + 4) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (n' + 5) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_V4_LA (n' + 7) (([0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have h_rem := rem_to_R1_01 (n' + 8)
    exact ReachesPlus.trans hc_6 h_rem

private theorem step_R3_0 : (R3_cfg 0) [target]⊢⁺ (T1_cfg 4) := by
  unfold R3_cfg T1_cfg
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem R3_entry_137 (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ [0, 0, 1, 0, 0, 1, 0, 0, 1]) {{A}}> default) [target]⊢⁺
    (l {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) := by
  simp only [U4, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem step_R3 (n : Nat) : StepsTo (R3_cfg n) (next_R3 n) := by
  rcases n with _ | _ | n'
  · exact reaches_trans (step_R3_0) (step_T1 4)
  · have h1 := R3_entry_137 default
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have h12 := ReachesPlus.trans h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have h_rem := rem_to_T1_001011001 6
    exact reaches_trans (ReachesPlus.trans hc_4 h_rem) (step_T1 6)
  · unfold R3_cfg
    rw [LA_succ (n' + 1)]
    have h1 := R3_entry_137 (LA (n' + 1))
    have hs_0 := consume_1_LA n' (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h1 hs_0
    have hs_1 := consume_1_LA (n' + 1) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_1_LA (n' + 2) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_V4_LA (n' + 4) (([1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA (n' + 4) (([1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (n' + 5) (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have h_rem := rem_to_T1_001011001 (n' + 7)
    exact reaches_trans (ReachesPlus.trans hc_5 h_rem) (step_T1 (n' + 7))

private theorem step_HubTail_r_R2 (a w : Nat) :
    StepsTo (HubTail (a + 7) w r_R2) (next_HubTail_r_R2 a w) := by
  revert a
  refine Nat.strong_induction_on w ?_
  intro w ih a
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 0, 1] : List (Fin 2)) +> default)
    have h_rem := rem_to_R1_001 (a + 8)
    exact ReachesPlus.trans hs_0 h_rem
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have h_rem := rem_to_R2_01001 (a + 11)
    exact ReachesPlus.trans hc_3 h_rem
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have h_rem := rem_to_Q_0001 (a + 19)
    exact ReachesPlus.trans hc_6 h_rem
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have h_rem := rem_to_R2_001001 (a + 26)
    exact ReachesPlus.trans hc_8 h_rem
  · unfold HubTail r_R2
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have h_rem := rem_to_R3_00101001 (a + 32)
    exact reaches_trans (ReachesPlus.trans hc_10 h_rem) (step_R3 (a + 32))
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_R2 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_R2
      +> default)) := by
      rw [Nat.add_comm w' 5, ListBlank.append_pow_add W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_R2 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 31))

private theorem step_HubTail_r_3 (a w : Nat) :
    StepsTo (HubTail (a + 7) w r_3) (next_HubTail_r_3 a w) := by
  revert a
  refine Nat.strong_induction_on w ?_
  intro w ih a
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have h_rem := rem_to_R1_001 (a + 10)
    exact ReachesPlus.trans hc_2 h_rem
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have h_rem := rem_to_Q_0001 (a + 16)
    exact ReachesPlus.trans hc_5 h_rem
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have h_rem := rem_to_R2_001001 (a + 23)
    exact ReachesPlus.trans hc_7 h_rem
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    rcases rem_halt_1 (a + 32) with ⟨cfg', h_rem, h_halt⟩
    exact ⟨cfg', ReachesPlus.trans hc_10 h_rem, h_halt⟩
  · unfold HubTail r_3
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have hs_11 := consume_0010101_LA (a + 31) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := ReachesPlus.trans hc_10 hs_11
    have hs_12 := consume_V4_LA (a + 35) (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_12 := ReachesPlus.trans hc_11 hs_12
    have hs_13 := consume_1_LA (a + 35) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_13 := ReachesPlus.trans hc_12 hs_13
    have h_rem := rem_to_R2_01001 (a + 37)
    exact ReachesPlus.trans hc_13 h_rem
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_3 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_3
      +> default)) := by
      rw [Nat.add_comm w' 5, ListBlank.append_pow_add W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_3 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 31))

private theorem step_HubTail_r_4 (a w : Nat) :
    StepsTo (HubTail (a + 7) w r_4) (next_HubTail_r_4 a w) := by
  revert a
  refine Nat.strong_induction_on w ?_
  intro w ih a
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have h_rem := rem_to_T1_001011001 (a + 9)
    exact reaches_trans (ReachesPlus.trans hc_1 h_rem) (step_T1 (a + 9))
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 11) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 11) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have h_rem := rem_to_R2_01001 (a + 15)
    exact ReachesPlus.trans hc_5 h_rem
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := rewrite_20_LA (a + 19) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_1_LA (a + 19) (([1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_1_LA (a + 20) (([1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_1_LA (a + 21) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have hs_11 := consume_V4_LA (a + 23) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := ReachesPlus.trans hc_10 hs_11
    have hs_12 := consume_1_LA (a + 23) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_12 := ReachesPlus.trans hc_11 hs_12
    have h_rem := rem_to_R1_001 (a + 25)
    exact ReachesPlus.trans hc_12 h_rem
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_0011_LA (a + 25) (([0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have h_rem := rem_to_S6_0001011001 (a + 28)
    exact ReachesPlus.trans hc_9 h_rem
  · unfold HubTail r_4
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1,
      0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have hs_11 := rewrite_38a_LA (a + 31) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := ReachesPlus.trans hc_10 hs_11
    have hs_12 := consume_1_LA (a + 31) (([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_12 := ReachesPlus.trans hc_11 hs_12
    have hs_13 := consume_1_LA (a + 32) (([1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_13 := ReachesPlus.trans hc_12 hs_13
    have hs_14 := consume_1_LA (a + 33) (([0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_14 := ReachesPlus.trans hc_13 hs_14
    have hs_15 := consume_0011_LA (a + 34) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_15 := ReachesPlus.trans hc_14 hs_15
    have hs_16 := consume_0011_LA (a + 37) (([0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_16 := ReachesPlus.trans hc_15 hs_16
    have h_rem := rem_to_R2_001001 (a + 41)
    exact ReachesPlus.trans hc_16 h_rem
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_4 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_4
      +> default)) := by
      rw [Nat.add_comm w' 5, ListBlank.append_pow_add W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_4 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 31))

private theorem step_HubTail_r_5 (a w : Nat) :
    StepsTo (HubTail (a + 7) w r_5) (next_HubTail_r_5 a w) := by
  revert a
  refine Nat.strong_induction_on w ?_
  intro w ih a
  rcases w with _ | _ | _ | _ | _ | w'
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 7) (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_V4_LA (a + 9) (([1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA (a + 10) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have h_rem := rem_to_R1_001 (a + 12)
    exact ReachesPlus.trans hc_4 h_rem
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 11) (([1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 11) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 12) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_V4_LA (a + 14) (([0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have h_rem := rem_to_R1_01 (a + 15)
    exact ReachesPlus.trans hc_7 h_rem
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0101_LA (a + 19) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0101_LA (a + 22) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have h_rem := rem_to_R2_01001 (a + 26)
    exact ReachesPlus.trans hc_8 h_rem
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_0011_LA (a + 25) (([0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have hs_11 := consume_0011_LA (a + 31) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := ReachesPlus.trans hc_10 hs_11
    have h_rem := rem_to_Q_0001 (a + 34)
    exact ReachesPlus.trans hc_11 h_rem
  · unfold HubTail r_5
    have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have hs_11 := consume_00101101_LA (a + 31) (([1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := ReachesPlus.trans hc_10 hs_11
    have hs_12 := consume_0011_LA (a + 34) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_12 := ReachesPlus.trans hc_11 hs_12
    have h_rem := rem_to_T1_001011001 (a + 38)
    exact reaches_trans (ReachesPlus.trans hc_12 h_rem) (step_T1 (a + 38))
  · unfold HubTail
    have h_w8 : (W8 ^ (w' + 5)) +> (r_5 +> default) = (W8 ^ 5) +> ((W8 ^ w') +> (r_5
      +> default)) := by
      rw [Nat.add_comm w' 5, ListBlank.append_pow_add W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (r_5 +> default))
    exact reaches_trans h1 (ih w' (by omega) (a + 31))

private theorem step_R2_0 : (R2_cfg 0) [target]⊢⁺ (R1_cfg 4) := by
  unfold R2_cfg R1_cfg
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_R2_succ_raw (l : ListBlank (Fin 2)) :
    (((l <+ U4) <+ [0, 0, 1, 0, 0, 1]) {{A}}> default) [target]⊢⁺
    (l {{D}}> (([1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2)) +> (r_R2 +> default))) := by
  simp only [U4, r_R2, ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem step_R2 (n : Nat) : StepsTo (R2_cfg n) (next_R2 n) := by
  rcases n with _ | n'
  · exact step_R2_0
  · unfold R2_cfg
    rw [LA_succ n']
    have h1 := step_R2_succ_raw (LA n')
    have h2 := drain_D_any_to_LA7 n' (r_R2 +> default)
    exact reaches_trans (ReachesPlus.trans h1 h2) (step_HubTail_r_R2 0 (n' / 2))

private theorem hub_w0_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 0) +> (([1, 0] : List (Fin 2)) +> r))) [target]⊢⁺
    (LA (a + 8) {{A}}> (([0] : List (Fin 2)) +> r)) :=
  consume_1_LA (a + 6) (([0] : List (Fin 2)) +> r)

private theorem hub_w1_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 1) +> (([1, 0] : List (Fin 2)) +> r))) [target]⊢⁺
    (LA (a + 11) {{A}}> (([0, 1, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_1 := ReachesPlus.trans hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_2 := ReachesPlus.trans hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans hc_2 hs_3

private theorem hub_w2_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 2) +> (([1, 0] : List (Fin 2)) +> r))) [target]⊢⁺
    (LA (a + 20) {{A}}> (([0, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_1 := ReachesPlus.trans hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_2 := ReachesPlus.trans hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_3 := ReachesPlus.trans hc_2 hs_3
  have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_4 := ReachesPlus.trans hc_3 hs_4
  have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_5 := ReachesPlus.trans hc_4 hs_5
  have hs_6 := consume_0101_LA (a + 16) (([0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans hc_5 hs_6

private theorem hub_w3_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 3) +> (([1, 0] : List (Fin 2)) +> r))) [target]⊢⁺
    (LA (a + 26) {{A}}> (([0, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
    0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0] : List (Fin 2)) +> r)
  have hc_1 := ReachesPlus.trans hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_2 := ReachesPlus.trans hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_3 := ReachesPlus.trans hc_2 hs_3
  have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_4 := ReachesPlus.trans hc_3 hs_4
  have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_5 := ReachesPlus.trans hc_4 hs_5
  have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_6 := ReachesPlus.trans hc_5 hs_6
  have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_7 := ReachesPlus.trans hc_6 hs_7
  have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans hc_7 hs_8

private theorem hub_w4_10 (a : Nat) (r : ListBlank (Fin 2)) :
    (LA (a + 7) {{A}}> ((W8 ^ 4) +> (([1, 0] : List (Fin 2)) +> r))) [target]⊢⁺
    (LA (a + 32) {{A}}> (([0, 0, 1, 0, 1, 0] : List (Fin 2)) +> r)) := by
  have hs_0 := consume_1_LA (a + 6) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
    0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hs_1 := consume_V4_LA (a + 8) (([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_1 := ReachesPlus.trans hs_0 hs_1
  have hs_2 := consume_1_LA (a + 8) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_2 := ReachesPlus.trans hc_1 hs_2
  have hs_3 := consume_1_LA (a + 9) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
    1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_3 := ReachesPlus.trans hc_2 hs_3
  have hs_4 := consume_0101_LA (a + 10) (([1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_4 := ReachesPlus.trans hc_3 hs_4
  have hs_5 := consume_0101_LA (a + 13) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0] : List (Fin 2)) +> r)
  have hc_5 := ReachesPlus.trans hc_4 hs_5
  have hs_6 := consume_0101_LA (a + 16) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_6 := ReachesPlus.trans hc_5 hs_6
  have hs_7 := consume_0011_LA (a + 19) (([0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0] : List (Fin 2)) +> r)
  have hc_7 := ReachesPlus.trans hc_6 hs_7
  have hs_8 := consume_0011_LA (a + 22) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_8 := ReachesPlus.trans hc_7 hs_8
  have hs_9 := consume_00101101_LA (a + 25) (([1, 0, 1, 0] : List (Fin 2)) +> r)
  have hc_9 := ReachesPlus.trans hc_8 hs_9
  have hs_10 := consume_0011_LA (a + 28) (([0, 1, 0, 1, 0] : List (Fin 2)) +> r)
  exact ReachesPlus.trans hc_9 hs_10

private theorem step_HubW8 (rend : List (Fin 2)) (nb : NextScanBundle) (a w b : Nat)
    (hb : ScanBundle b rend nb) :
    StepsTo (HubW8 (a + 7) w b rend) (next_HubW8 nb a w) := by
  revert a
  refine Nat.strong_induction_on w ?_
  intro w ih a
  rcases w with _ | _ | _ | _ | _ | w'
  · exact reaches_trans (hub_w0_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.1 (a + 4))
  · exact reaches_trans (hub_w1_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.2.2.2.2.1 (a + 7))
  · exact reaches_trans (hub_w2_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.2.2.2.1 (a + 16))
  · exact reaches_trans (hub_w3_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.2.1 (a + 22))
  · exact reaches_trans (hub_w4_10 a ((B4 ^ b) +> (rend
    +> default))) (hb.2.1 (a + 28))
  · unfold HubW8
    have h_w8 : (W8 ^ (w' + 5)) +> (([1, 0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default))) =
        (W8 ^ 5) +> ((W8 ^ w') +> (([1,
          0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default)))) := by
      rw [Nat.add_comm w' 5, ListBlank.append_pow_add W8 5 w']
    rw [h_w8]
    have h1 := consume_5_W8_LA_0349 (a + 6) ((W8 ^ w') +> (([1,
      0] : List (Fin 2)) +> ((B4 ^ b) +> (rend +> default))))
    exact reaches_trans h1 (ih w' (by omega) (a + 31))

private theorem step_Scan_p0_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b p0 r_Q) ((next_ScanBundle_r_Q b).p0 a) := by
  rcases b with _ | _ | b'
  · unfold Scan p0 r_Q
    have h_rem := rem_to_R1_01 (a + 4)
    exact h_rem
  · unfold Scan p0 r_Q
    have h_rem := rem_to_S6_011101 (a + 2)
    exact h_rem
  · unfold Scan p0
    have h_b4 : (B4 ^ (b' + 2)) +> (r_Q +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_Q
      +> default)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add B4 2 b']
    rw [h_b4]
    have h1 := drain_A_any_to_LA7 (a + 3) ((B4 ^ b') +> (r_Q +> default))
    exact reaches_trans h1 (step_HubW8 r_Q (next_ScanBundle_r_Q b') 0 ((a + 3) / 2) b'
      (ih b' (by omega)))

private theorem step_Scan_p0_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b p0 r_S6) ((next_ScanBundle_r_S6 b).p0 a) := by
  rcases b with _ | _ | b'
  · unfold Scan p0 r_S6
    have hs_0 := rewrite_26_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 3) (([1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 4) (([1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 5) (([0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_0011_LA (a + 6) (([0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have h_rem := rem_to_S4_00011001 (a + 9)
    exact ReachesPlus.trans hc_4 h_rem
  · unfold Scan p0 r_S6
    have h_rem := rem_ddrain_158 (a + 1)
    exact reaches_trans h_rem (step_HubTail_r_4 0 ((a + 1) / 2 + 1))
  · unfold Scan p0
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S6 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S6
      +> default)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add B4 2 b']
    rw [h_b4]
    have h1 := drain_A_any_to_LA7 (a + 3) ((B4 ^ b') +> (r_S6 +> default))
    exact reaches_trans h1 (step_HubW8 r_S6 (next_ScanBundle_r_S6 b') 0 ((a + 3) / 2) b'
      (ih b' (by omega)))

private theorem step_Scan_p0_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b p0 r_S4) ((next_ScanBundle_r_S4 b).p0 a) := by
  rcases b with _ | _ | b'
  · unfold Scan p0 r_S4
    have hs_0 := consume_0101_LA (a + 3) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have h_rem := rem_to_R2_01001 (a + 7)
    exact ReachesPlus.trans hs_0 h_rem
  · unfold Scan p0 r_S4
    have h_rem := rem_ddrain_232 (a + 1)
    exact reaches_trans h_rem (step_HubTail_r_5 0 ((a + 1) / 2 + 1))
  · unfold Scan p0
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S4 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S4
      +> default)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add B4 2 b']
    rw [h_b4]
    have h1 := drain_A_any_to_LA7 (a + 3) ((B4 ^ b') +> (r_S4 +> default))
    exact reaches_trans h1 (step_HubW8 r_S4 (next_ScanBundle_r_S4 b') 0 ((a + 3) / 2) b'
      (ih b' (by omega)))

private theorem step_Scan_p001010_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b p001010 r_Q) ((next_ScanBundle_r_Q b).p001010 a) := by
  rcases b with _ | b'
  · unfold Scan p001010 r_Q
    have hs_0 := consume_0010101_LA (a + 3) default
    have hs_1 := consume_V4_LA (a + 7) default
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    exact reaches_trans (hc_1) (step_P (a + 8))
  · unfold Scan p001010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_0010101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_V4_LA (a + 7) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 8) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    exact reaches_trans (hc_3) ((ih b' (Nat.lt_succ_self b')).1 (a + 6))

private theorem step_Scan_p001010_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b p001010 r_S6) ((next_ScanBundle_r_S6 b).p001010 a) := by
  rcases b with _ | b'
  · unfold Scan p001010 r_S6
    have hs_0 := consume_0010101_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 7) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 7) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have h_rem := rem_to_T1_001011001 (a + 11)
    exact reaches_trans (ReachesPlus.trans hc_2 h_rem) (step_T1 (a + 11))
  · unfold Scan p001010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_0010101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_V4_LA (a + 7) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 8) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    exact reaches_trans (hc_3) ((ih b' (Nat.lt_succ_self b')).1 (a + 6))

private theorem step_Scan_p001010_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b p001010 r_S4) ((next_ScanBundle_r_S4 b).p001010 a) := by
  rcases b with _ | b'
  · unfold Scan p001010 r_S4
    have hs_0 := consume_0010101_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 7) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_V4_LA (a + 8) (([0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have h_rem := rem_to_R1_01 (a + 9)
    exact ReachesPlus.trans hc_2 h_rem
  · unfold Scan p001010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_0010101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_V4_LA (a + 7) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 8) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    exact reaches_trans (hc_3) ((ih b' (Nat.lt_succ_self b')).1 (a + 6))

private theorem step_Scan_p0010_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b p0010 r_Q) ((next_ScanBundle_r_Q b).p0010 a) := by
  rcases b with _ | _ | b'
  · unfold Scan p0010 r_Q
    have h_rem := rem_to_R2_00101 (a + 4)
    exact h_rem
  · unfold Scan p0010 r_Q
    have hs_0 := consume_rewrite92_LA (a + 3) default
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1,
      0] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1,
      0] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have h_rem := rem_to_R1_0010 (a + 9)
    exact ReachesPlus.trans hc_6 h_rem
  · unfold Scan p0010
    have h_b4 : (B4 ^ (b' + 2)) +> (r_Q +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_Q
      +> default)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add B4 2 b']
    rw [h_b4]
    have hs_0 := consume_rewrite92_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    exact reaches_trans (hc_6) ((ih b' (Nat.lt_trans (Nat.lt_succ_self b') (Nat.lt_succ_self (b' +
      1)))).2.2.2.1 (a + 5))

private theorem step_Scan_p0010_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b p0010 r_S6) ((next_ScanBundle_r_S6 b).p0010 a) := by
  rcases b with _ | _ | b'
  · unfold Scan p0010 r_S6
    have hs_0 := rewrite_38b_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 3) (([1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 4) (([1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 5) (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 7) (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_V4_LA (a + 8) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_V4_LA (a + 9) (([0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have h_rem := rem_to_R1_01 (a + 10)
    exact ReachesPlus.trans hc_6 h_rem
  · unfold Scan p0010 r_S6
    have hs_0 := consume_rewrite92_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1,
      1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have h_rem := rem_ddrain_82 (a + 8)
    exact reaches_trans (ReachesPlus.trans hc_6 h_rem) (step_HubTail_r_3 0 ((a + 8) / 2))
  · unfold Scan p0010
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S6 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S6
      +> default)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add B4 2 b']
    rw [h_b4]
    have hs_0 := consume_rewrite92_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    exact reaches_trans (hc_6) ((ih b' (Nat.lt_trans (Nat.lt_succ_self b') (Nat.lt_succ_self (b' +
      1)))).2.2.2.1 (a + 5))

private theorem step_Scan_p0010_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b p0010 r_S4) ((next_ScanBundle_r_S4 b).p0010 a) := by
  rcases b with _ | _ | b'
  · unfold Scan p0010 r_S4
    have hs_0 := consume_0010101_LA (a + 3) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 7) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 7) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have h_rem := rem_to_R1_001 (a + 9)
    exact ReachesPlus.trans hc_2 h_rem
  · unfold Scan p0010 r_S4
    have hs_0 := consume_rewrite92_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := rewrite_24_LA (a + 8) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_1_LA (a + 8) (([1, 1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_1_LA (a + 9) (([1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have hs_10 := consume_1_LA (a + 10) (([0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_10 := ReachesPlus.trans hc_9 hs_10
    have hs_11 := consume_V4_LA (a + 12) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_11 := ReachesPlus.trans hc_10 hs_11
    have h_rem := rem_to_R1_001 (a + 13)
    exact ReachesPlus.trans hc_11 h_rem
  · unfold Scan p0010
    have h_b4 : (B4 ^ (b' + 2)) +> (r_S4 +> default) = (B4 ^ 2) +> ((B4 ^ b') +> (r_S4
      +> default)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add B4 2 b']
    rw [h_b4]
    have hs_0 := consume_rewrite92_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_1_LA (a + 2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 3) (([1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 4) (([0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 6) (([1, 1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_1_LA (a + 6) (([1, 0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 7) (([0, 0, 1, 0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    exact reaches_trans (hc_6) ((ih b' (Nat.lt_trans (Nat.lt_succ_self b') (Nat.lt_succ_self (b' +
      1)))).2.2.2.1 (a + 5))

private theorem step_Scan_p0010110_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b p0010110 r_Q) ((next_ScanBundle_r_Q b).p0010110 a) := by
  rcases b with _ | b'
  · unfold Scan p0010110 r_Q
    have hs_0 := consume_00101101_LA (a + 3) default
    have hs_1 := consume_0011_LA (a + 6) (([0] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    repeat rw [zero1_append_default] at hc_1
    exact reaches_trans (hc_1) (step_P (a + 10))
  · unfold Scan p0010110
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_00101101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_0011_LA (a + 6) (([0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 9) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.1 (a + 9))

private theorem step_Scan_p0010110_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b p0010110 r_S6) ((next_ScanBundle_r_S6 b).p0010110 a) := by
  rcases b with _ | b'
  · unfold Scan p0010110 r_S6
    have hs_0 := consume_00101101_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 6) (([0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    rcases rem_halt_2 (a + 10) with ⟨cfg', h_rem, h_halt⟩
    exact ⟨cfg', ReachesPlus.trans hc_1 h_rem, h_halt⟩
  · unfold Scan p0010110
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_00101101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_0011_LA (a + 6) (([0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 9) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.1 (a + 9))

private theorem step_Scan_p0010110_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b p0010110 r_S4) ((next_ScanBundle_r_S4 b).p0010110 a) := by
  rcases b with _ | b'
  · unfold Scan p0010110 r_S4
    have hs_0 := consume_00101101_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 6) (([0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have h_rem := rem_to_S4_00011001 (a + 9)
    exact ReachesPlus.trans hc_1 h_rem
  · unfold Scan p0010110
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_00101101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_0011_LA (a + 6) (([0, 1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_0011_LA (a + 9) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.1 (a + 9))

private theorem step_Scan_p00_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b p00 r_Q) ((next_ScanBundle_r_Q b).p00 a) := by
  rcases b with _ | b'
  · unfold Scan p00 r_Q
    have h_rem := rem_to_R1_001 (a + 4)
    exact h_rem
  · unfold Scan p00
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_0011_LA (a + 3) (([1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    exact reaches_trans (hs_0) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.1 (a + 3))

private theorem step_Scan_p00_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b p00 r_S6) ((next_ScanBundle_r_S6 b).p00 a) := by
  rcases b with _ | b'
  · unfold Scan p00 r_S6
    have hs_0 := rewrite_24_LA (a + 3) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_1_LA (a + 3) (([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 4) (([1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 5) (([0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA (a + 7) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_0101_LA (a + 7) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have h_rem := rem_to_R2_01001 (a + 11)
    exact ReachesPlus.trans hc_5 h_rem
  · unfold Scan p00
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_0011_LA (a + 3) (([1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    exact reaches_trans (hs_0) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.1 (a + 3))

private theorem step_Scan_p00_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b p00 r_S4) ((next_ScanBundle_r_S4 b).p00 a) := by
  rcases b with _ | b'
  · unfold Scan p00 r_S4
    have h_rem := rem_to_T1_001011001 (a + 4)
    exact reaches_trans (h_rem) (step_T1 (a + 4))
  · unfold Scan p00
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_0011_LA (a + 3) (([1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    exact reaches_trans (hs_0) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.1 (a + 3))

private theorem step_Scan_p010_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b p010 r_Q) ((next_ScanBundle_r_Q b).p010 a) := by
  rcases b with _ | b'
  · unfold Scan p010 r_Q
    have hs_0 := consume_0101_LA (a + 3) default
    rw [zero1_append_default] at hs_0
    exact reaches_trans (hs_0) (step_P (a + 7))
  · unfold Scan p010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_0101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_V4_LA (a + 7) ((B4 ^ b') +> (r_Q +> default))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    exact reaches_trans (hc_1) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.2 (a + 4))

private theorem step_Scan_p010_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b p010 r_S6) ((next_ScanBundle_r_S6 b).p010 a) := by
  rcases b with _ | b'
  · unfold Scan p010 r_S6
    have hs_0 := consume_0101_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := rewrite_56_LA (a + 6) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA (a + 6) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA (a + 7) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_V4_LA (a + 9) (([1, 1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_1_LA (a + 9) (([1, 0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_1_LA (a + 10) (([0, 1, 1, 0, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have hs_8 := consume_V4_LA (a + 12) (([1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_8 := ReachesPlus.trans hc_7 hs_8
    have hs_9 := consume_1_LA (a + 12) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_9 := ReachesPlus.trans hc_8 hs_9
    have h_rem := rem_to_R1_001 (a + 14)
    exact ReachesPlus.trans hc_9 h_rem
  · unfold Scan p010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_0101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_V4_LA (a + 7) ((B4 ^ b') +> (r_S6 +> default))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    exact reaches_trans (hc_1) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.2 (a + 4))

private theorem step_Scan_p010_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b p010 r_S4) ((next_ScanBundle_r_S4 b).p010 a) := by
  rcases b with _ | b'
  · unfold Scan p010 r_S4
    have hs_0 := consume_0101_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 6) (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have h_rem := rem_to_Q_0001 (a + 9)
    exact ReachesPlus.trans hc_1 h_rem
  · unfold Scan p010
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_0101_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_V4_LA (a + 7) ((B4 ^ b') +> (r_S4 +> default))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    exact reaches_trans (hc_1) ((ih b' (Nat.lt_succ_self b')).2.2.2.2.2.2 (a + 4))

private theorem step_Scan_pnil_r_Q (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_Q (next_ScanBundle_r_Q b')) :
    StepsTo (Scan (a + 4) b pnil r_Q) ((next_ScanBundle_r_Q b).pnil a) := by
  rcases b with _ | b'
  · unfold Scan pnil r_Q
    have hs_0 := consume_1_LA (a + 3) default
    exact reaches_trans (hs_0) (step_P (a + 5))
  · unfold Scan pnil
    have h_b4 : (B4 ^ (b' + 1)) +> (r_Q +> default) = B4 +> ((B4 ^ b') +> (r_Q +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_Q +> default)
    rw [h_b4]
    have hs_0 := consume_1_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hs_1 := consume_1_LA (a + 4) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_Q +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).1 (a + 3))

private theorem step_Scan_pnil_r_S6 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S6 (next_ScanBundle_r_S6 b')) :
    StepsTo (Scan (a + 4) b pnil r_S6) ((next_ScanBundle_r_S6 b).pnil a) := by
  rcases b with _ | b'
  · unfold Scan pnil r_S6
    have hs_0 := consume_1_LA (a + 3) (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hs_1 := consume_0011_LA (a + 4) (([0, 1, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have h_rem := rem_to_T1_001011001 (a + 8)
    exact reaches_trans (ReachesPlus.trans hc_1 h_rem) (step_T1 (a + 8))
  · unfold Scan pnil
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S6 +> default) = B4 +> ((B4 ^ b') +> (r_S6 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S6 +> default)
    rw [h_b4]
    have hs_0 := consume_1_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hs_1 := consume_1_LA (a + 4) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S6 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).1 (a + 3))

private theorem step_Scan_pnil_r_S4 (a b : Nat)
    (ih : ∀ b' < b, ScanBundle b' r_S4 (next_ScanBundle_r_S4 b')) :
    StepsTo (Scan (a + 4) b pnil r_S4) ((next_ScanBundle_r_S4 b).pnil a) := by
  rcases b with _ | b'
  · unfold Scan pnil r_S4
    have hs_0 := consume_1_LA (a + 3) (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hs_1 := consume_V4_LA (a + 5) (([0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have h_rem := rem_to_R1_01 (a + 6)
    exact ReachesPlus.trans hc_1 h_rem
  · unfold Scan pnil
    have h_b4 : (B4 ^ (b' + 1)) +> (r_S4 +> default) = B4 +> ((B4 ^ b') +> (r_S4 +> default)) :=
      ListBlank.append_pow_succ B4 b' (r_S4 +> default)
    rw [h_b4]
    have hs_0 := consume_1_LA (a + 3) (([1, 1,
      0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hs_1 := consume_1_LA (a + 4) (([1, 0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_1 := ReachesPlus.trans hs_0 hs_1
    have hs_2 := consume_1_LA (a + 5) (([0] : List (Fin 2)) +> ((B4 ^ b') +> (r_S4 +> default)))
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    exact reaches_trans (hc_2) ((ih b' (Nat.lt_succ_self b')).1 (a + 3))

private theorem scanBundle_all_r_Q (b : Nat) : ScanBundle b r_Q (next_ScanBundle_r_Q b) := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  exact ⟨fun a => step_Scan_p0_r_Q a b ih,
         fun a => step_Scan_p001010_r_Q a b ih,
         fun a => step_Scan_p0010_r_Q a b ih,
         fun a => step_Scan_p0010110_r_Q a b ih,
         fun a => step_Scan_p00_r_Q a b ih,
         fun a => step_Scan_p010_r_Q a b ih,
         fun a => step_Scan_pnil_r_Q a b ih⟩

private theorem scanBundle_all_r_S6 (b : Nat) : ScanBundle b r_S6 (next_ScanBundle_r_S6 b) := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  exact ⟨fun a => step_Scan_p0_r_S6 a b ih,
         fun a => step_Scan_p001010_r_S6 a b ih,
         fun a => step_Scan_p0010_r_S6 a b ih,
         fun a => step_Scan_p0010110_r_S6 a b ih,
         fun a => step_Scan_p00_r_S6 a b ih,
         fun a => step_Scan_p010_r_S6 a b ih,
         fun a => step_Scan_pnil_r_S6 a b ih⟩

private theorem scanBundle_all_r_S4 (b : Nat) : ScanBundle b r_S4 (next_ScanBundle_r_S4 b) := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  exact ⟨fun a => step_Scan_p0_r_S4 a b ih,
         fun a => step_Scan_p001010_r_S4 a b ih,
         fun a => step_Scan_p0010_r_S4 a b ih,
         fun a => step_Scan_p0010110_r_S4 a b ih,
         fun a => step_Scan_p00_r_S4 a b ih,
         fun a => step_Scan_p010_r_S4 a b ih,
         fun a => step_Scan_pnil_r_S4 a b ih⟩

private theorem step_Q (n : Nat) : StepsTo (Q_cfg n) (next_Q n) := by
  rcases n with _ | n'
  · have h1 := Q_entry_40 default
    have h2 := step_D_B4_bounce_to_LA6 default
    have h3 := rem_to_R1_0010 6
    exact ReachesPlus.trans (ReachesPlus.trans h1 h2) h3
  · have h1 := Q_entry_40 (LA (n' + 1))
    have h2 := sweep_D_B4_to_Scan n' r_Q
    exact reaches_trans (ReachesPlus.trans h1 h2) ((scanBundle_all_r_Q n').2.2.2.1 2)

private theorem step_S4 (n : Nat) : StepsTo (S4_cfg n) (next_S4 n) := by
  rcases n with _ | n'
  · have h1 := S4_entry_100 default
    have h2 := step_D_B4_bounce_to_LA6 (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have h12 := ReachesPlus.trans h1 h2
    have hs_0 := rewrite_24_LA 5 (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h12 hs_0
    have hs_1 := consume_1_LA 5 (([1, 1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_1_LA 6 (([1, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA 7 (([0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_V4_LA 9 (([0, 0, 1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have h_rem := rem_to_R1_001 10
    exact ReachesPlus.trans hc_4 h_rem
  · have h1 := S4_entry_100 (LA (n' + 1))
    have h2 := sweep_D_B4_to_Scan n' r_S4
    exact reaches_trans (ReachesPlus.trans h1 h2) ((scanBundle_all_r_S4 n').2.2.2.1 2)

private theorem S6_0_entry_232 :
    (S6_cfg 0) [target]⊢⁺
    (LA 0 {{A}}> (([1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)) := by
  unfold S6_cfg
  simp only [LA, U4, HPow.hPow,
    ListBlank.append_cons, ListBlank.append_nil,
    ]
  bb_steps

private theorem step_S6 (n : Nat) : StepsTo (S6_cfg n) (next_S6 n) := by
  rcases n with _ | _ | n'
  · have h1 := S6_0_entry_232
    have h2 := consume_1_LA_zero (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0,
      0, 1] : List (Fin 2)) +> default)
    have h12 := ReachesPlus.trans h1 h2
    have hs_0 := consume_1_LA 0 (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_0 := ReachesPlus.trans h12 hs_0
    have hs_1 := consume_1_LA 1 (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_1 := ReachesPlus.trans hc_0 hs_1
    have hs_2 := consume_V4_LA 3 (([1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_2 := ReachesPlus.trans hc_1 hs_2
    have hs_3 := consume_1_LA 3 (([1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_3 := ReachesPlus.trans hc_2 hs_3
    have hs_4 := consume_1_LA 4 (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have hc_4 := ReachesPlus.trans hc_3 hs_4
    have hs_5 := consume_V4_LA 6 (([0, 1, 1, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_5 := ReachesPlus.trans hc_4 hs_5
    have hs_6 := consume_V4_LA 7 (([0, 1, 1, 0, 0, 1] : List (Fin 2)) +> default)
    have hc_6 := ReachesPlus.trans hc_5 hs_6
    have hs_7 := consume_V4_LA 8 (([0, 1] : List (Fin 2)) +> default)
    have hc_7 := ReachesPlus.trans hc_6 hs_7
    have h_rem := rem_to_R1_01 9
    exact ReachesPlus.trans hc_7 h_rem
  · have h1 := S6_entry_152 default
    have h2 := step_D_B4_bounce_to_LA6 (([0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0,
      1] : List (Fin 2)) +> default)
    have h12 := ReachesPlus.trans h1 h2
    have h3 := rem_ddrain_82 5
    exact reaches_trans (ReachesPlus.trans h12 h3) (step_HubTail_r_3 0 2)
  · unfold S6_cfg
    rw [LA_succ (n' + 1)]
    have h1 := S6_entry_152 (LA (n' + 1))
    have h2 := sweep_D_B4_to_Scan n' r_S6
    exact reaches_trans (ReachesPlus.trans h1 h2) ((scanBundle_all_r_S6 n').2.2.2.1 2)

-- ============================================================================
-- Section 10: Initial Reachability & Main Cryptid Theorem (5 Core Patterns)
-- ============================================================================

private theorem init_to_S6_1 : (init []) [target]⊢* (S6_cfg 1) := by
  have h1 : (init []) [target]⊢* (P_cfg 3) := ReachesPlus.to_star step_P_0
  have h2 : (P_cfg 3) [target]⊢⁺ (S6_cfg 1) := by
    unfold P_cfg; rw [LA_succ 2, LA_succ 1]; exact step_P_2plus_raw (LA 1)
  exact ReachesStar.trans h1 (ReachesPlus.to_star h2)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨S6_cfg 1, init_to_S6_1, in_S6 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  cases h_mem with
  | head =>
    simp only [cond_Master, evalVarCond] at h_cond
    rcases h_cond with ⟨h1a, h1b, h2a⟩ | ⟨h1a, h1b, h2a⟩ | ⟨h1a, h1b, h2a, h2b⟩ | ⟨h1a, h1b, h2a,
      h2b⟩ | ⟨h1a, h1b, h2a, h2b⟩
    · have h1 : vars 1 = 1 := by omega
      have h2 : vars 2 = 0 := by omega
      rw [eval_pat_R1 vars h1 h2]; exact (step_R1 (vars 0)).toProp
    · have h1 : vars 1 = 2 := by omega
      have h2 : vars 2 = 0 := by omega
      rw [eval_pat_R2 vars h1 h2]; exact (step_R2 (vars 0)).toProp
    · have h1 : vars 1 = 1 := by omega
      have h2 : vars 2 = 3 := by omega
      rw [eval_pat_Q vars h1 h2]; exact (step_Q (vars 0)).toProp
    · have h1 : vars 1 = 3 := by omega
      have h2 : vars 2 = 3 := by omega
      rw [eval_pat_S4 vars h1 h2]; exact (step_S4 (vars 0)).toProp
    · have h1 : vars 1 = 3 := by omega
      have h2 : vars 2 = 5 := by omega
      rw [eval_pat_S6 vars h1 h2]; exact (step_S6 (vars 0)).toProp
  | tail _ h_mem =>
    nomatch h_mem

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_to_S6_1 ?_
  intro s
  have hs : StepsTo (encode s) (next s) := by
    cases s with
    | R1 n => exact step_R1 n
    | R2 n => exact step_R2 n
    | Q n => exact step_Q n
    | S4 n => exact step_S4 n
    | S6 n => exact step_S6 n
  cases h : next s with
  | some s' =>
    rw [h] at hs
    exact hs
  | none =>
    rw [h] at hs
    rcases hs with ⟨cfg', h_plus, h_none⟩
    exact ⟨cfg', ReachesPlus.to_star h_plus, h_none⟩

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA
