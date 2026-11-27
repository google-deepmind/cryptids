/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
import Mathlib.Tactic.Linarith

/-!
# Shared `(BigF, BigD1)` Mutual Excursion & `StrongWall` Closure Bridge (Pair-Stack)

Pure machine-independent symbolic engine shared across the pair-stack non-halting family,
including the 6-mode pair-stack equivalence class:
1. 4-mode pair-stack macro system (`Mode581`, `Cfg581`, `step581`, `run581`).
2. Depth-indexed mutual big-step excursion relation `(BigF, BigD1)`, halting inversion
   (`halts_inversion`), and turnkey wall bridge (`wall_no_halt_of_bigF_inv`).
3. Complete 28-predicate strong induction (`InvAt`, `invAt_all`) closing `StrongWall`
   (`strongWall_step`, `strongWall_no_halt`).
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.Calculi.PairStackA

abbrev Seg := Nat × Bool

inductive Mode581
  | FR0
  | BL0
  | DR0
  | DL0

structure Cfg581 where
  mode : Mode581
  L : List Nat
  R : List Seg

def bumpL : List Nat → List Nat
  | [] => [0]
  | a :: L => (a + 1) :: L

def bumpR : List Seg → List Seg
  | [] => [(0, false)]
  | (d, b) :: R => (d + 1, b) :: R

def ones : Nat → List Seg
  | 0 => []
  | n + 1 => (1, false) :: ones n

theorem bumpR_nonempty (R : List Seg) : bumpR R ≠ [] := by
  cases R with
  | nil => simp [bumpR]
  | cons x xs =>
    cases x
    simp [bumpR]

theorem append_nonempty_of_right {α : Type} (l1 l2 : List α) (h : l2 ≠ []) : l1 ++ l2 ≠ [] := by
  intro heq
  cases l1 with
  | nil => exact h heq
  | cons _ _ => simp at heq

/-- Bit-exact 1-macro-step transition function of the 4-mode pair-stack system. -/
def step581 : Cfg581 → Option Cfg581
  | ⟨.FR0, L, []⟩ => some ⟨.BL0, L, [(0, false)]⟩
  | ⟨.FR0, L, (0, false) :: R⟩ => some ⟨.BL0, L, bumpR (bumpR R)⟩
  | ⟨.FR0, L, (0, true) :: R⟩ => some ⟨.BL0, L, (1, false) :: R⟩
  | ⟨.FR0, L, (1, false) :: R⟩ => some ⟨.FR0, 1 :: L, R⟩
  | ⟨.FR0, L, (1, true) :: R⟩ => some ⟨.BL0, 1 :: L, bumpR R⟩
  | ⟨.FR0, L, (2, b) :: R⟩ => some ⟨.DR0, 0 :: L, (0, b) :: R⟩
  | ⟨.FR0, L, (d + 3, b) :: R⟩ => some ⟨.DL0, 1 :: L, (d, b) :: R⟩
  | ⟨.BL0, [], _⟩ => none
  | ⟨.BL0, 0 :: L', R⟩ => some ⟨.DL0, bumpL (bumpL L'), R⟩
  | ⟨.BL0, 1 :: L', R⟩ => some ⟨.BL0, L', (0, true) :: R⟩
  | ⟨.BL0, 2 :: [], _⟩ => none
  | ⟨.BL0, 2 :: a' :: L', R⟩ => some ⟨.DL0, (a' + 1) :: L', (1, false) :: R⟩
  | ⟨.BL0, (a + 3) :: L', R⟩ => some ⟨.FR0, a :: L', (0, true) :: R⟩
  | ⟨.DR0, L, []⟩ => some ⟨.FR0, bumpL L, []⟩
  | ⟨.DR0, L, (0, false) :: R⟩ => some ⟨.FR0, L, bumpR (bumpR R)⟩
  | ⟨.DR0, L, (0, true) :: R⟩ => some ⟨.FR0, L, (1, false) :: R⟩
  | ⟨.DR0, L, (1, false) :: R⟩ => some ⟨.FR0, bumpL (bumpL (bumpL L)), R⟩
  | ⟨.DR0, L, (1, true) :: R⟩ => some ⟨.BL0, bumpL (bumpL (bumpL L)), bumpR R⟩
  | ⟨.DR0, L, (2, b) :: R⟩ => some ⟨.DR0, bumpL (bumpL L), (0, b) :: R⟩
  | ⟨.DR0, L, (d + 3, b) :: R⟩ => some ⟨.DL0, bumpL (bumpL (bumpL L)), (d, b) :: R⟩
  | ⟨.DL0, [], R⟩ => some ⟨.FR0, [0], R⟩
  | ⟨.DL0, 0 :: [], []⟩ => none
  | ⟨.DL0, 0 :: a' :: L', []⟩ => some ⟨.DL0, (a' + 1) :: L', [(0, true), (0, false)]⟩
  | ⟨.DL0, (a + 1) :: L', []⟩ => some ⟨.FR0, a :: L', [(1, false)]⟩
  | ⟨.DL0, a :: L', (0, false) :: R⟩ => some ⟨.FR0, (a + 2) :: L', R⟩
  | ⟨.DL0, a :: L', (0, true) :: R⟩ => some ⟨.BL0, (a + 2) :: L', bumpR R⟩
  | ⟨.DL0, a :: L', (1, b) :: R⟩ => some ⟨.DR0, (a + 1) :: L', (0, b) :: R⟩
  | ⟨.DL0, a :: L', (d + 2, b) :: R⟩ => some ⟨.DL0, (a + 2) :: L', (d, b) :: R⟩

def run581 : Nat → Cfg581 → Option Cfg581
  | 0, c => some c
  | n + 1, c =>
    match step581 c with
    | none => none
    | some c' => run581 n c'

theorem run581_add (m n : Nat) (c c' : Cfg581) (h : run581 m c = some c') :
    run581 (m + n) c = run581 n c' := by
  induction m generalizing c with
  | zero =>
    simp only [run581, Option.some.injEq] at h
    subst h
    simp only [Nat.zero_add]
  | succ k ih =>
    simp only [Nat.succ_add, run581] at h ⊢
    cases hs : step581 c with
    | none => simp [hs] at h
    | some c1 =>
      simp only [hs] at h
      exact ih c1 h

theorem halts_after_run {m n : Nat} {c c' : Cfg581}
    (hrun : run581 m c = some c') (hhalt : run581 n c = none) :
    m ≤ n ∧ run581 (n - m) c' = none := by
  induction m generalizing n c with
  | zero =>
    simp only [run581, Option.some.injEq] at hrun
    subst hrun
    exact ⟨Nat.zero_le n, hhalt⟩
  | succ k ih =>
    cases n with
    | zero => simp [run581] at hhalt
    | succ n' =>
      simp only [run581] at hrun hhalt
      cases hs : step581 c with
      | none => simp [hs] at hrun
      | some c1 =>
        simp only [hs] at hrun hhalt
        obtain ⟨hle, hrem⟩ := ih hrun hhalt
        exact ⟨Nat.succ_le_succ hle, by simpa [Nat.succ_sub_succ] using hrem⟩

theorem halts_after_step {n : Nat} {c c' : Cfg581}
    (hs : step581 c = some c') (hhalt : run581 n c = none) :
    1 ≤ n ∧ run581 (n - 1) c' = none :=
  halts_after_run (m := 1) (by simp [run581, hs]) hhalt

/-! ## Exact Unconditional Wall Reflections on [1, 3, 2] -/

theorem wall_9 (R : List Seg) :
    run581 9 ⟨.BL0, [1, 3, 2], R⟩ = some ⟨.FR0, [1, 0, 5], R⟩ := rfl

theorem wall_15 (R : List Seg) :
    run581 15 ⟨.BL0, [1, 0, 5], R⟩ = some ⟨.FR0, [1, 3, 2], bumpR R⟩ := rfl

theorem wall_27 (tail : List Seg) :
    run581 27 ⟨.BL0, [1, 3, 2], (0, true) :: tail⟩ =
      some ⟨.FR0, [0, 1, 3, 2], bumpR (bumpR tail)⟩ := by
  have h1 : run581 9 ⟨.BL0, [1, 3, 2], (0, true) :: tail⟩ =
      some ⟨.FR0, [1, 0, 5], (0, true) :: tail⟩ := wall_9 ((0, true) :: tail)
  have h10 : run581 10 ⟨.BL0, [1, 3, 2], (0, true) :: tail⟩ =
      some ⟨.BL0, [1, 0, 5], (1, false) :: tail⟩ := run581_add 9 1 _ _ h1
  have h25 : run581 25 ⟨.BL0, [1, 3, 2], (0, true) :: tail⟩ =
      some ⟨.FR0, [1, 3, 2], (2, false) :: tail⟩ := by
    rw [show (25 : Nat) = 10 + 15 from rfl, run581_add 10 15 _ _ h10]
    exact wall_15 ((1, false) :: tail)
  rw [show (27 : Nat) = 25 + 2 from rfl, run581_add 25 2 _ _ h25]
  rfl

/-! ## BL0 (+3q) Shift Reduction -/

theorem bl0_shift_3 (a : Nat) (L : List Nat) (R : List Seg) :
    run581 2 ⟨.BL0, (a + 3) :: L, R⟩ = some ⟨.BL0, a :: L, (1, false) :: R⟩ := rfl

theorem bl0_shift_3q (q rem : Nat) (L : List Nat) (R : List Seg) :
    run581 (2 * q) ⟨.BL0, (3 * q + rem) :: L, R⟩ = some ⟨.BL0, rem :: L, ones q ++ R⟩ := by
  induction q generalizing R with
  | zero => simp [run581, ones]
  | succ k ih =>
    have hstep : run581 2 ⟨.BL0, (3 * (k + 1) + rem) :: L, R⟩ =
        some ⟨.BL0, (3 * k + rem) :: L, (1, false) :: R⟩ := by
      have heq : 3 * (k + 1) + rem = (3 * k + rem) + 3 := by omega
      rw [heq]
      exact bl0_shift_3 (3 * k + rem) L R
    have hmul : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [hmul]
    rw [run581_add 2 (2 * k) _ _ hstep]
    rw [ih ((1, false) :: R)]
    have hones : ones k ++ (1, false) :: R = ones (k + 1) ++ R := by
      clear ih hstep hmul
      induction k with
      | zero => rfl
      | succ j ihj =>
        simp only [ones, List.cons_append] at ihj ⊢
        rw [ihj]
    rw [hones]

/-! ## Depth-Indexed Pure-Nat Mutual Big-Step System (BigF, BigD1) -/

mutual
  /-- `BigF k R Δ R_fin`: `FR0 (a :: L) R` reaches `BL0 ((a + Δ) :: L) R_fin` with derivation size
      `k`. -/
  inductive BigF : Nat → List Seg → Nat → List Seg → Prop
    | nil : BigF 0 [] 0 [(0, false)]
    | zeroF (Y : List Seg) : BigF 0 ((0, false) :: Y) 0 (bumpR (bumpR Y))
    | zeroT (Y : List Seg) : BigF 0 ((0, true) :: Y) 0 ((1, false) :: Y)
    | oneT (Y : List Seg) : BigF 0 ((1, true) :: Y) 0 ((0, true) :: bumpR Y)
    | oneF_rem1 {k1 : Nat} {Y R1 : List Seg} {Δ1 : Nat}
        (h1 : BigF k1 Y Δ1 R1) (hrem : (1 + Δ1) % 3 = 1) :
        BigF (k1 + 1) ((1, false) :: Y) 0 ((0, true) :: ones ((1 + Δ1) / 3) ++ R1)
    | oneF_rem2 {k1 k2 : Nat} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigF k1 Y Δ1 R1) (hrem : (1 + Δ1) % 3 = 2)
        (h2 : BigD1 k2 (ones ((1 + Δ1) / 3 + 1) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((1, false) :: Y) Δ2 R2
    | oneF_rem0 {k1 k2 : Nat} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigF k1 Y Δ1 R1) (hrem : (1 + Δ1) % 3 = 0)
        (h2 : BigD1 k2 (ones ((1 + Δ1) / 3) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((1, false) :: Y) (Δ2 + 1) R2
    | twoF_rem1 {k1 : Nat} {Y R1 : List Seg} {Δ1 : Nat}
        (h1 : BigF k1 (bumpR (bumpR Y)) Δ1 R1) (hrem : Δ1 % 3 = 1) :
        BigF (k1 + 1) ((2, false) :: Y) 0 ((0, true) :: ones (Δ1 / 3) ++ R1)
    | twoF_rem2 {k1 k2 : Nat} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigF k1 (bumpR (bumpR Y)) Δ1 R1) (hrem : Δ1 % 3 = 2)
        (h2 : BigD1 k2 (ones (Δ1 / 3 + 1) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((2, false) :: Y) Δ2 R2
    | twoF_rem0 {k1 k2 : Nat} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigF k1 (bumpR (bumpR Y)) Δ1 R1) (hrem : Δ1 % 3 = 0)
        (h2 : BigD1 k2 (ones (Δ1 / 3) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((2, false) :: Y) (Δ2 + 1) R2
    | twoT_rem1 {k1 : Nat} {Y R1 : List Seg} {Δ1 : Nat}
        (h1 : BigF k1 ((1, false) :: Y) Δ1 R1) (hrem : Δ1 % 3 = 1) :
        BigF (k1 + 1) ((2, true) :: Y) 0 ((0, true) :: ones (Δ1 / 3) ++ R1)
    | twoT_rem2 {k1 k2 : Nat} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigF k1 ((1, false) :: Y) Δ1 R1) (hrem : Δ1 % 3 = 2)
        (h2 : BigD1 k2 (ones (Δ1 / 3 + 1) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((2, true) :: Y) Δ2 R2
    | twoT_rem0 {k1 k2 : Nat} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigF k1 ((1, false) :: Y) Δ1 R1) (hrem : Δ1 % 3 = 0)
        (h2 : BigD1 k2 (ones (Δ1 / 3) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((2, true) :: Y) (Δ2 + 1) R2
    | ge3_rem1 {k1 d : Nat} {b : Bool} {Y R1 : List Seg} {Δ1 : Nat}
        (h1 : BigD1 k1 ((d, b) :: Y) Δ1 R1) (hrem : Δ1 % 3 = 1) :
        BigF (k1 + 1) ((d + 3, b) :: Y) 0 ((0, true) :: ones (Δ1 / 3) ++ R1)
    | ge3_rem2 {k1 k2 d : Nat} {b : Bool} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigD1 k1 ((d, b) :: Y) Δ1 R1) (hrem : Δ1 % 3 = 2)
        (h2 : BigD1 k2 (ones (Δ1 / 3 + 1) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((d + 3, b) :: Y) Δ2 R2
    | ge3_rem0 {k1 k2 d : Nat} {b : Bool} {Y R1 R2 : List Seg} {Δ1 Δ2 : Nat}
        (h1 : BigD1 k1 ((d, b) :: Y) Δ1 R1) (hrem : Δ1 % 3 = 0)
        (h2 : BigD1 k2 (ones (Δ1 / 3) ++ R1) Δ2 R2) :
        BigF (k1 + k2 + 1) ((d + 3, b) :: Y) (Δ2 + 1) R2

  /-- `BigD1 k R Δ' R_fin`: `DL0 ((a + 1) :: L) R` reaches `BL0 ((a + Δ') :: L) R_fin` with
      derivation size `k`. -/
  inductive BigD1 : Nat → List Seg → Nat → List Seg → Prop
    | nil : BigD1 0 [] 0 [(0, true), (0, false)]
    | zeroF {k : Nat} {Y R_fin : List Seg} {Δ : Nat}
        (h : BigF k Y Δ R_fin) : BigD1 (k + 1) ((0, false) :: Y) (Δ + 3) R_fin
    | zeroT (Y : List Seg) : BigD1 0 ((0, true) :: Y) 3 (bumpR Y)
    | oneF {k : Nat} {Y R_fin : List Seg} {Δ : Nat}
        (h : BigF k (bumpR (bumpR Y)) Δ R_fin) : BigD1 (k + 1) ((1, false) :: Y) (Δ + 2) R_fin
    | oneT {k : Nat} {Y R_fin : List Seg} {Δ : Nat}
        (h : BigF k ((1, false) :: Y) Δ R_fin) : BigD1 (k + 1) ((1, true) :: Y) (Δ + 2) R_fin
    | ge2 {k d : Nat} {b : Bool} {Y R_fin : List Seg} {Δ' : Nat}
        (h : BigD1 k ((d, b) :: Y) Δ' R_fin) : BigD1 (k + 1) ((d + 2, b) :: Y) (Δ' + 2) R_fin
end

/-! ## Master Inversion Theorem (Theorem 2: step581 -> BigF / BigD1) -/

private theorem dispatch_halts {n val a : Nat} {L : List Nat} {R1 : List Seg}
    (hhalt : run581 n ⟨.BL0, val :: a :: L, R1⟩ = none)
    (ihD : ∀ k < n, ∀ a' L' R', run581 k ⟨.DL0, (a' + 1) :: L', R'⟩ = none →
      ∃ k' < k, ∃ s Δ' R_fin, BigD1 s R' Δ' R_fin ∧ run581 k' ⟨.BL0, (a' + Δ') :: L',
          R_fin⟩ = none) :
    (val % 3 = 1 ∧ ∃ k' < n, run581 k' ⟨.BL0, a :: L, (0, true) :: ones (val / 3) ++ R1⟩ = none) ∨
    (val % 3 = 2 ∧ ∃ k' < n, ∃ s Δ2 R2,
      BigD1 s (ones (val / 3 + 1) ++ R1) Δ2 R2 ∧ run581 k' ⟨.BL0, (a + Δ2) :: L, R2⟩ = none) ∨
    (val % 3 = 0 ∧ ∃ k' < n, ∃ s Δ2 R2,
      BigD1 s (ones (val / 3) ++ R1) Δ2 R2 ∧ run581 k' ⟨.BL0, (a + (Δ2 + 1)) :: L, R2⟩ = none) := by
  have hdiv : 3 * (val / 3) + val % 3 = val := by omega
  have hsh : run581 (2 * (val / 3)) ⟨.BL0, val :: a :: L, R1⟩ =
      some ⟨.BL0, (val % 3) :: a :: L, ones (val / 3) ++ R1⟩ := by
    have h0 := bl0_shift_3q (val / 3) (val % 3) (a :: L) R1
    rwa [hdiv] at h0
  obtain ⟨hle, hrem⟩ := halts_after_run hsh hhalt
  have hmod : val % 3 = 0 ∨ val % 3 = 1 ∨ val % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · rw [h0] at hrem
    have hs : step581 ⟨.BL0, 0 :: a :: L, ones (val / 3) ++ R1⟩ =
        some ⟨.DL0, ((a + 1) + 1) :: L, ones (val / 3) ++ R1⟩ := rfl
    obtain ⟨h1le, hdl⟩ := halts_after_step hs hrem
    have hlt : n - 2 * (val / 3) - 1 < n := by omega
    obtain ⟨k', hk', s, Δ2, R2, hD, hfin⟩ := ihD _ hlt (a + 1) L (ones (val / 3) ++ R1) hdl
    refine Or.inr (Or.inr ⟨h0, k', by omega, s, Δ2, R2, hD, ?_⟩)
    have haeq : a + 1 + Δ2 = a + (Δ2 + 1) := by omega
    rwa [haeq] at hfin
  · rw [h1] at hrem
    have hs : step581 ⟨.BL0, 1 :: a :: L, ones (val / 3) ++ R1⟩ =
        some ⟨.BL0, a :: L, (0, true) :: ones (val / 3) ++ R1⟩ := rfl
    obtain ⟨h1le, hbl⟩ := halts_after_step hs hrem
    exact Or.inl ⟨h1, n - 2 * (val / 3) - 1, by omega, hbl⟩
  · rw [h2] at hrem
    have hs : step581 ⟨.BL0, 2 :: a :: L, ones (val / 3) ++ R1⟩ =
        some ⟨.DL0, (a + 1) :: L, ones (val / 3 + 1) ++ R1⟩ := by
      have hcons : (1, false) :: (ones (val / 3) ++ R1) = ones (val / 3 + 1) ++ R1 := rfl
      simp [step581, hcons]
    obtain ⟨h1le, hdl⟩ := halts_after_step hs hrem
    have hlt : n - 2 * (val / 3) - 1 < n := by omega
    obtain ⟨k', hk', s, Δ2, R2, hD, hfin⟩ := ihD _ hlt a L (ones (val / 3 + 1) ++ R1) hdl
    exact Or.inr (Or.inl ⟨h2, k', by omega, s, Δ2, R2, hD, hfin⟩)

/-- Combined Master Inversion Theorem by strong induction on `n`. -/
theorem halts_inversion (n : Nat) :
    (∀ a L R, run581 n ⟨.FR0, a :: L, R⟩ = none →
      ∃ k < n, ∃ s Δ R_fin, BigF s R Δ R_fin ∧ run581 k ⟨.BL0, (a + Δ) :: L, R_fin⟩ = none) ∧
    (∀ a L R, run581 n ⟨.DL0, (a + 1) :: L, R⟩ = none →
      ∃ k < n, ∃ s Δ' R_fin, BigD1 s R Δ' R_fin ∧ run581 k ⟨.BL0, (a + Δ') :: L, R_fin⟩ = none) :=
          by
  refine Nat.strongRecOn (motive := fun m =>
    (∀ a L R, run581 m ⟨.FR0, a :: L, R⟩ = none →
      ∃ k < m, ∃ s Δ R_fin, BigF s R Δ R_fin ∧ run581 k ⟨.BL0, (a + Δ) :: L, R_fin⟩ = none) ∧
    (∀ a L R, run581 m ⟨.DL0, (a + 1) :: L, R⟩ = none →
      ∃ k < m, ∃ s Δ' R_fin, BigD1 s R Δ' R_fin ∧ run581 k ⟨.BL0, (a + Δ') :: L,
          R_fin⟩ = none)) n ?_
  intro m ih
  have ihF : ∀ k < m, ∀ a' L' R', run581 k ⟨.FR0, a' :: L', R'⟩ = none →
      ∃ k' < k, ∃ s Δ R_fin, BigF s R' Δ R_fin ∧ run581 k' ⟨.BL0, (a' + Δ) :: L', R_fin⟩ = none :=
    fun k hk => (ih k hk).1
  have ihD : ∀ k < m, ∀ a' L' R', run581 k ⟨.DL0, (a' + 1) :: L', R'⟩ = none →
      ∃ k' < k, ∃ s Δ' R_fin, BigD1 s R' Δ' R_fin ∧ run581 k' ⟨.BL0, (a' + Δ') :: L',
          R_fin⟩ = none :=
    fun k hk => (ih k hk).2
  constructor
  · intro a L R hhalt
    match R with
    | [] =>
      obtain ⟨h1, hr⟩ := halts_after_step (c' := ⟨.BL0, a :: L, [(0, false)]⟩) rfl hhalt
      exact ⟨m - 1, by omega, 0, 0, [(0, false)], BigF.nil, hr⟩
    | (0, false) :: Y =>
      obtain ⟨h1, hr⟩ := halts_after_step (c' := ⟨.BL0, a :: L, bumpR (bumpR Y)⟩) rfl hhalt
      exact ⟨m - 1, by omega, 0, 0, bumpR (bumpR Y), BigF.zeroF Y, hr⟩
    | (0, true) :: Y =>
      obtain ⟨h1, hr⟩ := halts_after_step (c' := ⟨.BL0, a :: L, (1, false) :: Y⟩) rfl hhalt
      exact ⟨m - 1, by omega, 0, 0, (1, false) :: Y, BigF.zeroT Y, hr⟩
    | (1, true) :: Y =>
      have h2 : run581 2 ⟨.FR0, a :: L, (1, true) :: Y⟩ =
          some ⟨.BL0, a :: L, (0, true) :: bumpR Y⟩ := rfl
      obtain ⟨hle, hr⟩ := halts_after_run h2 hhalt
      exact ⟨m - 2, by omega, 0, 0, (0, true) :: bumpR Y, BigF.oneT Y, hr⟩
    | (1, false) :: Y =>
      obtain ⟨h1, hr1⟩ := halts_after_step (c' := ⟨.FR0, 1 :: a :: L, Y⟩) rfl hhalt
      obtain ⟨k1, hk1, s1, Δ1, R1, hF1, hbl1⟩ := ihF (m - 1) (by omega) 1 (a :: L) Y hr1
      have hdisp := dispatch_halts hbl1 (fun k hk => ihD k (by omega))
      rcases hdisp with ⟨hrem, k', hk', hfin⟩ | ⟨hrem, k', hk', s2, Δ2, R2, hD2, hfin⟩ | ⟨hrem, k',
          hk', s2, Δ2, R2, hD2, hfin⟩
      · exact ⟨k', by omega, s1 + 1, 0, (0, true) :: ones ((1 + Δ1) / 3) ++ R1,
                    BigF.oneF_rem1 hF1 hrem, hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2, R2, BigF.oneF_rem2 hF1 hrem hD2, hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2 + 1, R2, BigF.oneF_rem0 hF1 hrem hD2, hfin⟩
    | (2, false) :: Y =>
      have h2 : run581 2 ⟨.FR0, a :: L, (2, false) :: Y⟩ =
          some ⟨.FR0, 0 :: a :: L, bumpR (bumpR Y)⟩ := rfl
      obtain ⟨hle, hr1⟩ := halts_after_run h2 hhalt
      obtain ⟨k1, hk1, s1, Δ1, R1, hF1, hbl1⟩ :=
          ihF (m - 2) (by omega) 0 (a :: L) (bumpR (bumpR Y)) hr1
      rw [Nat.zero_add] at hbl1
      have hdisp := dispatch_halts hbl1 (fun k hk => ihD k (by omega))
      rcases hdisp with ⟨hrem, k', hk', hfin⟩ | ⟨hrem, k', hk', s2, Δ2, R2, hD2, hfin⟩ | ⟨hrem, k',
          hk', s2, Δ2, R2, hD2, hfin⟩
      · exact ⟨k', by omega, s1 + 1, 0, (0, true) :: ones (Δ1 / 3) ++ R1, BigF.twoF_rem1 hF1 hrem,
                    hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2, R2, BigF.twoF_rem2 hF1 hrem hD2, hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2 + 1, R2, BigF.twoF_rem0 hF1 hrem hD2, hfin⟩
    | (2, true) :: Y =>
      have h2 : run581 2 ⟨.FR0, a :: L, (2, true) :: Y⟩ =
          some ⟨.FR0, 0 :: a :: L, (1, false) :: Y⟩ := rfl
      obtain ⟨hle, hr1⟩ := halts_after_run h2 hhalt
      obtain ⟨k1, hk1, s1, Δ1, R1, hF1, hbl1⟩ :=
          ihF (m - 2) (by omega) 0 (a :: L) ((1, false) :: Y) hr1
      rw [Nat.zero_add] at hbl1
      have hdisp := dispatch_halts hbl1 (fun k hk => ihD k (by omega))
      rcases hdisp with ⟨hrem, k', hk', hfin⟩ | ⟨hrem, k', hk', s2, Δ2, R2, hD2, hfin⟩ | ⟨hrem, k',
          hk', s2, Δ2, R2, hD2, hfin⟩
      · exact ⟨k', by omega, s1 + 1, 0, (0, true) :: ones (Δ1 / 3) ++ R1, BigF.twoT_rem1 hF1 hrem,
                    hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2, R2, BigF.twoT_rem2 hF1 hrem hD2, hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2 + 1, R2, BigF.twoT_rem0 hF1 hrem hD2, hfin⟩
    | (d + 3, b) :: Y =>
      obtain ⟨h1, hr1⟩ := halts_after_step (c' := ⟨.DL0, 1 :: a :: L, (d, b) :: Y⟩) rfl hhalt
      obtain ⟨k1, hk1, s1, Δ1, R1, hD1, hbl1⟩ := ihD (m - 1) (by omega) 0 (a :: L) ((d, b) :: Y) hr1
      rw [Nat.zero_add] at hbl1
      have hdisp := dispatch_halts hbl1 (fun k hk => ihD k (by omega))
      rcases hdisp with ⟨hrem, k', hk', hfin⟩ | ⟨hrem, k', hk', s2, Δ2, R2, hD2, hfin⟩ | ⟨hrem, k',
          hk', s2, Δ2, R2, hD2, hfin⟩
      · exact ⟨k', by omega, s1 + 1, 0, (0, true) :: ones (Δ1 / 3) ++ R1, BigF.ge3_rem1 hD1 hrem,
                    hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2, R2, BigF.ge3_rem2 hD1 hrem hD2, hfin⟩
      · exact ⟨k', by omega, s1 + s2 + 1, Δ2 + 1, R2, BigF.ge3_rem0 hD1 hrem hD2, hfin⟩
  · intro a L R hhalt
    match R with
    | [] =>
      have h4 : run581 4 ⟨.DL0, (a + 1) :: L, []⟩ =
          some ⟨.BL0, a :: L, [(0, true), (0, false)]⟩ := rfl
      obtain ⟨hle, hr⟩ := halts_after_run h4 hhalt
      exact ⟨m - 4, by omega, 0, 0, [(0, true), (0, false)], BigD1.nil, hr⟩
    | (0, false) :: Y =>
      obtain ⟨h1, hr1⟩ := halts_after_step (c' := ⟨.FR0, (a + 3) :: L, Y⟩) rfl hhalt
      obtain ⟨k1, hk1, s, Δ, R_fin, hF, hfin⟩ := ihF (m - 1) (by omega) (a + 3) L Y hr1
      refine ⟨k1, by omega, s + 1, Δ + 3, R_fin, BigD1.zeroF hF, ?_⟩
      have heq : a + 3 + Δ = a + (Δ + 3) := by omega
      rwa [heq] at hfin
    | (0, true) :: Y =>
      obtain ⟨h1, hr1⟩ := halts_after_step (c' := ⟨.BL0, (a + 3) :: L, bumpR Y⟩) rfl hhalt
      exact ⟨m - 1, by omega, 0, 3, bumpR Y, BigD1.zeroT Y, hr1⟩
    | (1, false) :: Y =>
      have h2 : run581 2 ⟨.DL0, (a + 1) :: L, (1, false) :: Y⟩ =
          some ⟨.FR0, (a + 2) :: L, bumpR (bumpR Y)⟩ := rfl
      obtain ⟨hle, hr1⟩ := halts_after_run h2 hhalt
      obtain ⟨k1, hk1, s, Δ, R_fin, hF, hfin⟩ :=
          ihF (m - 2) (by omega) (a + 2) L (bumpR (bumpR Y)) hr1
      refine ⟨k1, by omega, s + 1, Δ + 2, R_fin, BigD1.oneF hF, ?_⟩
      have heq : a + 2 + Δ = a + (Δ + 2) := by omega
      rwa [heq] at hfin
    | (1, true) :: Y =>
      have h2 : run581 2 ⟨.DL0, (a + 1) :: L, (1, true) :: Y⟩ =
          some ⟨.FR0, (a + 2) :: L, (1, false) :: Y⟩ := rfl
      obtain ⟨hle, hr1⟩ := halts_after_run h2 hhalt
      obtain ⟨k1, hk1, s, Δ, R_fin, hF, hfin⟩ :=
          ihF (m - 2) (by omega) (a + 2) L ((1, false) :: Y) hr1
      refine ⟨k1, by omega, s + 1, Δ + 2, R_fin, BigD1.oneT hF, ?_⟩
      have heq : a + 2 + Δ = a + (Δ + 2) := by omega
      rwa [heq] at hfin
    | (d + 2, b) :: Y =>
      obtain ⟨h1, hr1⟩ := halts_after_step (c' := ⟨.DL0, ((a + 2) + 1) :: L, (d, b) :: Y⟩) rfl hhalt
      obtain ⟨k1, hk1, s, Δ', R_fin, hD, hfin⟩ := ihD (m - 1) (by omega) (a + 2) L ((d, b) :: Y) hr1
      refine ⟨k1, by omega, s + 1, Δ' + 2, R_fin, BigD1.ge2 hD, ?_⟩
      have heq : a + 2 + Δ' = a + (Δ' + 2) := by omega
      rwa [heq] at hfin

/-! ## Turnkey WallReturnSafe Non-Halting Bridge -/

/-- Any wall invariant `W` closed under `BigF` proves `BL0 [1, 3, 2] R` NEVER halts! -/
theorem wall_no_halt_of_bigF_inv (W : List Seg → Prop)
    (hW : ∀ R, W R → ∃ tail, R = (0, true) :: tail ∧
      ∀ s Δ R_fin, BigF s (bumpR (bumpR tail)) Δ R_fin →
        Δ % 3 = 1 ∧ W ((0, true) :: ones (Δ / 3) ++ R_fin)) :
    ∀ n R, W R → run581 n ⟨.BL0, [1, 3, 2], R⟩ ≠ none := by
  intro n
  refine Nat.strongRecOn (motive := fun m => ∀ R, W R → run581 m ⟨.BL0, [1, 3, 2], R⟩ ≠ none) n ?_
  intro m ih R hWR hhalt
  obtain ⟨tail, rfl, hstep⟩ := hW R hWR
  obtain ⟨hle27, hfr⟩ := halts_after_run (wall_27 tail) hhalt
  obtain ⟨k1, hk1, s, Δ, R_fin, hF, hbl⟩ :=
      (halts_inversion (m - 27)).1 0 [1, 3, 2] (bumpR (bumpR tail)) hfr
  rw [Nat.zero_add] at hbl
  obtain ⟨hrem1, hW'⟩ := hstep s Δ R_fin hF
  have hdiv : 3 * (Δ / 3) + 1 = Δ := by omega
  have hsh : run581 (2 * (Δ / 3)) ⟨.BL0, Δ :: [1, 3, 2], R_fin⟩ =
      some ⟨.BL0, 1 :: [1, 3, 2], ones (Δ / 3) ++ R_fin⟩ := by
    have h0 := bl0_shift_3q (Δ / 3) 1 [1, 3, 2] R_fin
    rwa [hdiv] at h0
  obtain ⟨hle2, hbl1⟩ := halts_after_run hsh hbl
  obtain ⟨h1le, hnext⟩ := halts_after_step
    (c' := ⟨.BL0, [1, 3, 2], (0, true) :: ones (Δ / 3) ++ R_fin⟩) rfl hbl1
  exact ih (k1 - 2 * (Δ / 3) - 1) (by omega) ((0, true) :: ones (Δ / 3) ++ R_fin) hW' hnext

/-! ## Structural Properties of (BigF, BigD1): Bounds, Determinism, NoNonlast0F -/

theorem bigFD_bounds (s : Nat) :
    (∀ R Δ R_fin, BigF s R Δ R_fin → Δ ≠ 1 ∧ R_fin ≠ []) ∧
    (∀ R Δ' R_fin, BigD1 s R Δ' R_fin → (R ≠ [] → 2 ≤ Δ') ∧ R_fin ≠ []) := by
  refine Nat.strongRecOn (motive := fun m =>
    (∀ R Δ R_fin, BigF m R Δ R_fin → Δ ≠ 1 ∧ R_fin ≠ []) ∧
    (∀ R Δ' R_fin, BigD1 m R Δ' R_fin → (R ≠ [] → 2 ≤ Δ') ∧ R_fin ≠ [])) s ?_
  intro m ih
  constructor
  · intro R Δ R_fin hF
    cases hF with
    | nil => exact ⟨by omega, by simp⟩
    | zeroF Y => exact ⟨by omega, bumpR_nonempty (bumpR Y)⟩
    | zeroT _ => exact ⟨by omega, by simp⟩
    | oneT _ => exact ⟨by omega, by simp⟩
    | oneF_rem1 _ _ => exact ⟨by omega, by simp⟩
    | oneF_rem2 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).1 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | oneF_rem0 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).1 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | twoF_rem1 _ _ => exact ⟨by omega, by simp⟩
    | twoF_rem2 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).1 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | twoF_rem0 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).1 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | twoT_rem1 _ _ => exact ⟨by omega, by simp⟩
    | twoT_rem2 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).1 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | twoT_rem0 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).1 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | ge3_rem1 _ _ => exact ⟨by omega, by simp⟩
    | ge3_rem2 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).2 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
    | ge3_rem0 h1 _ h2 =>
      obtain ⟨_, hne1⟩ := (ih _ (by omega)).2 _ _ _ h1
      obtain ⟨hge2, hne2⟩ := (ih _ (by omega)).2 _ _ _ h2
      exact ⟨by have := hge2 (append_nonempty_of_right _ _ hne1); omega, hne2⟩
  · intro R Δ' R_fin hD
    cases hD with
    | nil => exact ⟨fun h => absurd rfl h, by simp⟩
    | zeroF h => exact ⟨fun _ => by omega, ((ih _ (by omega)).1 _ _ _ h).2⟩
    | zeroT Y => exact ⟨fun _ => by omega, bumpR_nonempty Y⟩
    | oneF h => exact ⟨fun _ => by omega, ((ih _ (by omega)).1 _ _ _ h).2⟩
    | oneT h => exact ⟨fun _ => by omega, ((ih _ (by omega)).1 _ _ _ h).2⟩
    | ge2 h => exact ⟨fun _ => by omega, ((ih _ (by omega)).2 _ _ _ h).2⟩

theorem bigFD_det (s1 : Nat) :
    (∀ s2 R Δ1 Δ2 R1 R2, BigF s1 R Δ1 R1 → BigF s2 R Δ2 R2 → Δ1 = Δ2 ∧ R1 = R2) ∧
    (∀ s2 R Δ1 Δ2 R1 R2, BigD1 s1 R Δ1 R1 → BigD1 s2 R Δ2 R2 → Δ1 = Δ2 ∧ R1 = R2) := by
  refine Nat.strongRecOn (motive := fun m =>
    (∀ s2 R Δ1 Δ2 R1 R2, BigF m R Δ1 R1 → BigF s2 R Δ2 R2 → Δ1 = Δ2 ∧ R1 = R2) ∧
    (∀ s2 R Δ1 Δ2 R1 R2, BigD1 m R Δ1 R1 → BigD1 s2 R Δ2 R2 → Δ1 = Δ2 ∧ R1 = R2)) s1 ?_
  intro m ih
  constructor
  · intro s2 R Δ1 Δ2 R1 R2 h1 h2
    cases h1 with
    | nil => cases h2; exact ⟨rfl, rfl⟩
    | zeroF Y => cases h2; exact ⟨rfl, rfl⟩
    | zeroT Y => cases h2; exact ⟨rfl, rfl⟩
    | oneT Y => cases h2; exact ⟨rfl, rfl⟩
    | oneF_rem1 ha hr =>
      cases h2 with
      | oneF_rem1 hb _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
      | oneF_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | oneF_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
    | oneF_rem2 ha hr hd =>
      cases h2 with
      | oneF_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | oneF_rem2 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb
        exact (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
      | oneF_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
    | oneF_rem0 ha hr hd =>
      cases h2 with
      | oneF_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | oneF_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | oneF_rem0 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
        exact ⟨rfl, rfl⟩
    | twoF_rem1 ha hr =>
      cases h2 with
      | twoF_rem1 hb _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
      | twoF_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoF_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
    | twoF_rem2 ha hr hd =>
      cases h2 with
      | twoF_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoF_rem2 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb
        exact (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
      | twoF_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
    | twoF_rem0 ha hr hd =>
      cases h2 with
      | twoF_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoF_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoF_rem0 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
        exact ⟨rfl, rfl⟩
    | twoT_rem1 ha hr =>
      cases h2 with
      | twoT_rem1 hb _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
      | twoT_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoT_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
    | twoT_rem2 ha hr hd =>
      cases h2 with
      | twoT_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoT_rem2 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb
        exact (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
      | twoT_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
    | twoT_rem0 ha hr hd =>
      cases h2 with
      | twoT_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoT_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; omega
      | twoT_rem0 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
        exact ⟨rfl, rfl⟩
    | ge3_rem1 ha hr =>
      cases h2 with
      | ge3_rem1 hb _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
      | ge3_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; omega
      | ge3_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; omega
    | ge3_rem2 ha hr hd =>
      cases h2 with
      | ge3_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; omega
      | ge3_rem2 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb
        exact (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
      | ge3_rem0 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; omega
    | ge3_rem0 ha hr hd =>
      cases h2 with
      | ge3_rem1 hb hr2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; omega
      | ge3_rem2 hb hr2 _ =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; omega
      | ge3_rem0 hb _ hd2 =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ hd hd2
        exact ⟨rfl, rfl⟩
  · intro s2 R Δ1 Δ2 R1 R2 h1 h2
    cases h1 with
    | nil => cases h2; exact ⟨rfl, rfl⟩
    | zeroF ha =>
      cases h2 with | zeroF hb =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
    | zeroT Y => cases h2; exact ⟨rfl, rfl⟩
    | oneF ha =>
      cases h2 with | oneF hb =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
    | oneT ha =>
      cases h2 with | oneT hb =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩
    | ge2 ha =>
      cases h2 with | ge2 hb =>
        obtain ⟨rfl, rfl⟩ := (ih _ (by omega)).2 _ _ _ _ _ _ ha hb; exact ⟨rfl, rfl⟩

/-- `NoNonlast0F R`: `(0, false)` occurs only at the last element of `R`. -/
def NoNonlast0F : List Seg → Prop
  | [] => True
  | [_] => True
  | (0, false) :: _ :: _ => False
  | _ :: x :: xs => NoNonlast0F (x :: xs)

/-- `NoInterior0F R`: `(0, false)` occurs only at `R.head` or `R.last`. -/
def NoInterior0F : List Seg → Prop
  | [] => True
  | _ :: xs => NoNonlast0F xs

theorem noNonlast0F_tail {x : Seg} {xs : List Seg} (h : NoNonlast0F (x :: xs)) : NoNonlast0F xs :=
    by
  cases xs with
  | nil => trivial
  | cons y ys =>
    cases x with
    | mk d b =>
      cases d with
      | zero =>
        cases b with
        | false => exact False.elim h
        | true => exact h
      | succ _ => exact h

theorem noNonlast0F_cons_ne0F {x : Seg} {xs : List Seg} (hne : x ≠ (0,
    false)) (h : NoNonlast0F xs) :
    NoNonlast0F (x :: xs) := by
  cases xs with
  | nil => trivial
  | cons y ys =>
    cases x with
    | mk d b =>
      cases d with
      | zero =>
        cases b with
        | false => exact absurd rfl hne
        | true => exact h
      | succ _ => exact h

theorem noNonlast0F_bumpR {R : List Seg} (h : NoNonlast0F R) : NoNonlast0F (bumpR R) := by
  cases R with
  | nil => trivial
  | cons x xs =>
    cases x with
    | mk d b =>
      exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_tail h)

theorem noNonlast0F_ones_append (q : Nat) {R : List Seg} (h : NoNonlast0F R) :
    NoNonlast0F (ones q ++ R) := by
  induction q with
  | zero => exact h
  | succ k ih => exact noNonlast0F_cons_ne0F (by simp) ih

theorem noNonlast0F_imp_noInterior0F {R : List Seg} (h : NoNonlast0F R) : NoInterior0F R := by
  cases R with
  | nil => trivial
  | cons x xs => exact noNonlast0F_tail h

/-- Exact `NoNonlast0F` / `NoInterior0F` preservation on `(BigF, BigD1)`. -/
theorem bigFD_noNonlast0F (s : Nat) :
    (∀ R Δ R_fin, BigF s R Δ R_fin → NoNonlast0F R → NoNonlast0F R_fin) ∧
    (∀ R Δ' R_fin, BigD1 s R Δ' R_fin → NoInterior0F R → NoNonlast0F R_fin) := by
  refine Nat.strongRecOn (motive := fun m =>
    (∀ R Δ R_fin, BigF m R Δ R_fin → NoNonlast0F R → NoNonlast0F R_fin) ∧
    (∀ R Δ' R_fin, BigD1 m R Δ' R_fin → NoInterior0F R → NoNonlast0F R_fin)) s ?_
  intro m ih
  constructor
  · intro R Δ R_fin hF hN
    cases hF with
    | nil => trivial
    | zeroF Y =>
      cases Y with
      | nil => trivial
      | cons _ _ => exact False.elim hN
    | zeroT Y => exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_tail hN)
    | oneT Y => exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_bumpR (noNonlast0F_tail hN))
    | oneF_rem1 h1 _ =>
      have h1N := (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_tail hN)
      exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_ones_append _ h1N)
    | oneF_rem2 h1 _ h2 =>
      have h1N := (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_tail hN)
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | oneF_rem0 h1 _ h2 =>
      have h1N := (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_tail hN)
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | twoF_rem1 h1 _ =>
      have h1N :=
          (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN)))
      exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_ones_append _ h1N)
    | twoF_rem2 h1 _ h2 =>
      have h1N :=
          (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN)))
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | twoF_rem0 h1 _ h2 =>
      have h1N :=
          (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN)))
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | twoT_rem1 h1 _ =>
      have h1N :=
          (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_cons_ne0F (by simp) (noNonlast0F_tail hN))
      exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_ones_append _ h1N)
    | twoT_rem2 h1 _ h2 =>
      have h1N :=
          (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_cons_ne0F (by simp) (noNonlast0F_tail hN))
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | twoT_rem0 h1 _ h2 =>
      have h1N :=
          (ih _ (by omega)).1 _ _ _ h1 (noNonlast0F_cons_ne0F (by simp) (noNonlast0F_tail hN))
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | ge3_rem1 h1 _ =>
      have h1N := (ih _ (by omega)).2 _ _ _ h1 (noNonlast0F_tail hN)
      exact noNonlast0F_cons_ne0F (by simp) (noNonlast0F_ones_append _ h1N)
    | ge3_rem2 h1 _ h2 =>
      have h1N := (ih _ (by omega)).2 _ _ _ h1 (noNonlast0F_tail hN)
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
    | ge3_rem0 h1 _ h2 =>
      have h1N := (ih _ (by omega)).2 _ _ _ h1 (noNonlast0F_tail hN)
      exact (ih _ (by omega)).2 _ _ _ h2
          (noNonlast0F_imp_noInterior0F (noNonlast0F_ones_append _ h1N))
  · intro R Δ' R_fin hD hI
    cases hD with
    | nil => trivial
    | zeroF h => exact (ih _ (by omega)).1 _ _ _ h hI
    | zeroT Y => exact noNonlast0F_bumpR hI
    | oneF h => exact (ih _ (by omega)).1 _ _ _ h (noNonlast0F_bumpR (noNonlast0F_bumpR hI))
    | oneT h => exact (ih _ (by omega)).1 _ _ _ h (noNonlast0F_cons_ne0F (by simp) hI)
    | ge2 h => exact (ih _ (by omega)).2 _ _ _ h hI

/-! ## Exact Algebraic Identities (yaronika / steverin / zephyrus / kalbaugh) -/

/-- Exact `D(1, 1 :: X) = 2 + F(3 :: X)` (`zephyrus`). -/
theorem bigD1_1_1_inv {s Δ' : Nat} {X R_fin : List Seg}
    (h : BigD1 s ((1, false) :: (1, false) :: X) Δ' R_fin) :
    ∃ s' < s, ∃ Δ0, Δ' = Δ0 + 2 ∧ BigF s' ((3, false) :: X) Δ0 R_fin := by
  cases h with
  | oneF hF => exact ⟨_, by omega, _, rfl, hF⟩

/-- Exact `0*`-peeling identity `F(3 :: 0* :: X) = 3 + F(3 :: X)` (`zephyrus`), strictly decreasing
    `s`! -/
theorem bigF_3_0s_inv {s Δ : Nat} {X R_fin : List Seg}
    (h : BigF s ((3, false) :: (0, true) :: X) Δ R_fin) :
    ∃ s' < s, ∃ Δ0, Δ = Δ0 + 3 ∧ BigF s' ((3, false) :: X) Δ0 R_fin := by
  have hD0 : BigD1 1 ((0, false) :: (0, true) :: X) 3 ((1, false) :: X) :=
    BigD1.zeroF (BigF.zeroT X)
  cases h with
  | ge3_rem1 h1 hrem =>
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).2 _ _ _ _ _ _ h1 hD0
    omega
  | ge3_rem2 h1 hrem _ =>
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).2 _ _ _ _ _ _ h1 hD0
    omega
  | ge3_rem0 h1 _ h2 =>
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).2 _ _ _ _ _ _ h1 hD0
    obtain ⟨s', hs', Δ0, rfl, hF⟩ := bigD1_1_1_inv h2
    exact ⟨s', by omega, Δ0, by omega, hF⟩

/-- Exact `F(3 :: 1* :: X) = 3 + F(2* :: bump X)` (`zephyrus`), strictly decreasing `s`! -/
theorem bigF_3_1s_inv {s Δ : Nat} {X R_fin : List Seg}
    (h : BigF s ((3, false) :: (1, true) :: X) Δ R_fin) :
    ∃ s' < s, ∃ Δ0, Δ = Δ0 + 3 ∧ BigF s' ((2, true) :: bumpR X) Δ0 R_fin := by
  have hD0 : BigD1 1 ((0, false) :: (1, true) :: X) 3 ((0, true) :: bumpR X) :=
    BigD1.zeroF (BigF.oneT X)
  cases h with
  | ge3_rem1 h1 hrem =>
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).2 _ _ _ _ _ _ h1 hD0; omega
  | ge3_rem2 h1 hrem _ =>
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).2 _ _ _ _ _ _ h1 hD0; omega
  | ge3_rem0 h1 _ h2 =>
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).2 _ _ _ _ _ _ h1 hD0
    cases h2 with
    | oneF hF => exact ⟨_, by omega, _, by omega, hF⟩

/-- `F(2* :: 0* :: X) = (4, 2 :: X)` (`zephyrus`). -/
theorem bigF_2s_0s_exists (X : List Seg) :
    BigF 2 ((2, true) :: (0, true) :: X) 4 ((2, false) :: X) :=
  BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.zeroT X) rfl) rfl (BigD1.zeroT ((1, false) :: X))

/-- `F(3 :: 1 :: 1 :: 1* :: X) = (7, 2 :: 0* :: bump X)`. Covers `W₁₆`! -/
theorem bigF_3_1_1_1s_exists (X : List Seg) :
    BigF 7 ((3, false) :: (1, false) :: (1, false) :: (1, true) :: X) 7
      ((2, false) :: (0, true) :: bumpR X) := by
  have h1 : BigD1 3 ((0, false) :: (1, false) :: (1, false) :: (1, true) :: X) 3
      ((0, true) :: (0, true) :: (0, true) :: bumpR X) :=
    BigD1.zeroF (BigF.oneF_rem1 (BigF.oneF_rem1 (BigF.oneT X) rfl) rfl)
  exact BigF.ge3_rem0 h1 rfl (BigD1.oneF (bigF_2s_0s_exists ((0, true) :: bumpR X)))

/-- `NoNonlast0F` Head Constraint: whenever `BigF s R 0 R_fin` under `NoNonlast0F R`, `R_fin`
starts strictly in `{(0, F), (0, T), (1, F)}`. -/
theorem bigF_zero_head_nnf {s : Nat} {R R_fin : List Seg}
    (hF : BigF s R 0 R_fin) (hN : NoNonlast0F R) :
    ∃ x xs, R_fin = x :: xs ∧ (x = (0, false) ∨ x = (0, true) ∨ x = (1, false)) := by
  cases hF with
  | nil => exact ⟨(0, false), [], rfl, Or.inl rfl⟩
  | zeroF Y =>
    cases Y with
    | nil => exact ⟨(1, false), [], rfl, Or.inr (Or.inr rfl)⟩
    | cons _ _ => exact False.elim hN
  | zeroT Y => exact ⟨(1, false), Y, rfl, Or.inr (Or.inr rfl)⟩
  | oneT Y => exact ⟨(0, true), bumpR Y, rfl, Or.inr (Or.inl rfl)⟩
  | oneF_rem1 _ _ => exact ⟨(0, true), _, rfl, Or.inr (Or.inl rfl)⟩
  | twoF_rem1 _ _ => exact ⟨(0, true), _, rfl, Or.inr (Or.inl rfl)⟩
  | twoT_rem1 _ _ => exact ⟨(0, true), _, rfl, Or.inr (Or.inl rfl)⟩
  | ge3_rem1 _ _ => exact ⟨(0, true), _, rfl, Or.inr (Or.inl rfl)⟩
  | oneF_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega
  | twoF_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega
  | twoT_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega
  | ge3_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).2 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega

theorem bumpR_bumpR_ge2 {R : List Seg} (hne : R ≠ []) :
    ∃ d b Y, bumpR (bumpR R) = (d + 2, b) :: Y := by
  cases R with
  | nil => exact absurd rfl hne
  | cons x xs =>
    cases x with
    | mk d b => exact ⟨d, b, xs, rfl⟩

theorem ones_pos_cons {q : Nat} (hq : 1 ≤ q) (R : List Seg) :
    ∃ Z, ones q ++ R = (1, false) :: Z := by
  cases q with
  | zero => omega
  | succ k => exact ⟨ones k ++ R, rfl⟩

/-- Unconditional (even without `NoNonlast0F`!): any `BigF s ((d + 2, b) :: Y) 0 R_fin`
    returns `R_fin = (0, true) :: (1, false) :: Z`! -/
theorem bigF_ge2_zero_head {s d : Nat} {b : Bool} {Y R_fin : List Seg}
    (hF : BigF s ((d + 2, b) :: Y) 0 R_fin) :
    ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
  cases hF with
  | @twoF_rem1 _ _ R1 Δ1 h1 hrem =>
    have hne1 := ((bigFD_bounds _).1 _ _ _ h1).1
    obtain ⟨Z, hZ⟩ := ones_pos_cons (q := Δ1 / 3) (by omega) R1
    exact ⟨Z, by rw [List.cons_append, hZ]⟩
  | @twoT_rem1 _ _ R1 Δ1 h1 hrem =>
    have hne1 := ((bigFD_bounds _).1 _ _ _ h1).1
    obtain ⟨Z, hZ⟩ := ones_pos_cons (q := Δ1 / 3) (by omega) R1
    exact ⟨Z, by rw [List.cons_append, hZ]⟩
  | @ge3_rem1 _ _ _ _ R1 Δ1 h1 hrem =>
    have hge2 := ((bigFD_bounds _).2 _ _ _ h1).1 (by simp)
    obtain ⟨Z, hZ⟩ := ones_pos_cons (q := Δ1 / 3) (by omega) R1
    exact ⟨Z, by rw [List.cons_append, hZ]⟩
  | twoF_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega
  | twoT_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega
  | ge3_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).2 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega

/-- Unconditional: any `BigF s ((1, false) :: Y) 0 R_fin` starts with `(0, true)`. -/
theorem bigF_oneF_zero_head {s : Nat} {Y R_fin : List Seg}
    (hF : BigF s ((1, false) :: Y) 0 R_fin) :
    ∃ Z, R_fin = (0, true) :: Z := by
  cases hF with
  | oneF_rem1 _ _ => exact ⟨_, rfl⟩
  | oneF_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega

/-- Helper: `BigD1 s ((1, false) :: tail) 2 R_fin` (with `tail ≠ []`) forces `0* :: 1 :: Z`. -/
theorem bigD1_oneF_two_head {s : Nat} {tail R_fin : List Seg}
    (hne : tail ≠ []) (hD : BigD1 s ((1, false) :: tail) 2 R_fin) :
    ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
  cases hD with
  | oneF hF =>
    obtain ⟨d, b, Y, hEq⟩ := bumpR_bumpR_ge2 hne
    rw [hEq] at hF
    exact bigF_ge2_zero_head hF

/-- Unconditional: `BigF s R 2 R_fin` ALWAYS has `R_fin = (0, true) :: (1, false) :: Z`! -/
theorem bigF_two_head {s : Nat} {R R_fin : List Seg} (hF : BigF s R 2 R_fin) :
    ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
  cases hF with
  | oneF_rem2 h1 _ h2 =>
    exact bigD1_oneF_two_head (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ h1).2) h2
  | twoF_rem2 h1 _ h2 =>
    exact bigD1_oneF_two_head (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ h1).2) h2
  | twoT_rem2 h1 _ h2 =>
    exact bigD1_oneF_two_head (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ h1).2) h2
  | ge3_rem2 h1 _ h2 =>
    exact bigD1_oneF_two_head (append_nonempty_of_right _ _ ((bigFD_bounds _).2 _ _ _ h1).2) h2
  | oneF_rem0 h1 _ h2 =>
    have hge :=
        ((bigFD_bounds _).2 _ _ _ h2).1
        (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ h1).2)
    omega
  | twoF_rem0 h1 _ h2 =>
    have hge :=
        ((bigFD_bounds _).2 _ _ _ h2).1
        (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ h1).2)
    omega
  | twoT_rem0 h1 _ h2 =>
    have hge :=
        ((bigFD_bounds _).2 _ _ _ h2).1
        (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ h1).2)
    omega
  | ge3_rem0 h1 _ h2 =>
    have hge :=
        ((bigFD_bounds _).2 _ _ _ h2).1
        (append_nonempty_of_right _ _ ((bigFD_bounds _).2 _ _ _ h1).2)
    omega

/-- Unconditional: `BigF s R 3 R_fin` ALWAYS has `R_fin = (0, true) :: (1, false) :: Z`! -/
theorem bigF_three_head {s : Nat} {R R_fin : List Seg} (hF : BigF s R 3 R_fin) :
    ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
  cases hF with
  | oneF_rem2 _ _ h2 =>
    cases h2 with | oneF h3 => exact absurd rfl ((bigFD_bounds _).1 _ _ _ h3).1
  | twoF_rem2 _ _ h2 =>
    cases h2 with | oneF h3 => exact absurd rfl ((bigFD_bounds _).1 _ _ _ h3).1
  | twoT_rem2 _ _ h2 =>
    cases h2 with | oneF h3 => exact absurd rfl ((bigFD_bounds _).1 _ _ _ h3).1
  | ge3_rem2 _ _ h2 =>
    cases h2 with | oneF h3 => exact absurd rfl ((bigFD_bounds _).1 _ _ _ h3).1
  | @oneF_rem0 _ _ _ R1 _ Δ1 _ h1 hrem h2 =>
    have hne := ((bigFD_bounds _).1 _ _ _ h1).2
    cases hqq : (1 + Δ1) / 3 with
    | zero => omega
    | succ k =>
      rw [hqq] at h2
      exact bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2
  | @ge3_rem0 _ _ _ _ _ R1 _ Δ1 _ h1 hrem h2 =>
    have hge := ((bigFD_bounds _).2 _ _ _ h1).1 (by simp)
    have hne := ((bigFD_bounds _).2 _ _ _ h1).2
    cases hqq : Δ1 / 3 with
    | zero => omega
    | succ k =>
      rw [hqq] at h2
      exact bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2
  | @twoF_rem0 _ _ Y R1 _ Δ1 _ h1 hrem h2 =>
    cases hΔ : Δ1 with
    | zero =>
      subst hΔ
      simp only [Nat.zero_div, ones, List.nil_append] at h2
      have h0t : ∃ Z, R1 = (0, true) :: Z := by
        cases Y with
        | nil => exact bigF_oneF_zero_head h1
        | cons x xs =>
          cases x with | mk d b =>
            obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head h1
            exact ⟨(1, false) :: Z, hZ⟩
      obtain ⟨Z, rfl⟩ := h0t
      cases h2
    | succ k =>
      subst hΔ
      have hne := ((bigFD_bounds _).1 _ _ _ h1).2
      cases hqq : (k + 1) / 3 with
      | zero => omega
      | succ m =>
        rw [hqq] at h2
        exact bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2
  | @twoT_rem0 _ _ Y R1 _ Δ1 _ h1 hrem h2 =>
    cases hΔ : Δ1 with
    | zero =>
      subst hΔ
      simp only [Nat.zero_div, ones, List.nil_append] at h2
      obtain ⟨Z, rfl⟩ := bigF_oneF_zero_head h1
      cases h2
    | succ k =>
      subst hΔ
      have hne := ((bigFD_bounds _).1 _ _ _ h1).2
      cases hqq : (k + 1) / 3 with
      | zero => omega
      | succ m =>
        rw [hqq] at h2
        exact bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2

/-- Global `NoNonlast0F` Head Constraint: `ValidHead R` iff `R.head ∈ {0, 0*, 1, 1*, 2}`. -/
def ValidHead : List Seg → Prop
  | (0, false) :: _ => True
  | (0, true)  :: _ => True
  | (1, false) :: _ => True
  | (1, true)  :: _ => True
  | (2, false) :: _ => True
  | _ => False

/-- Global `NoNonlast0F` Head Theorem (ALL `Δ : ℕ`!):
    Under `NoNonlast0F R`, `BigF s R Δ R_fin` ALWAYS returns `ValidHead R_fin`
    (NEVER `(2, true)` and NEVER `(d ≥ 3, _)`!). -/
theorem bigF_head_nnf (s : Nat) :
    ∀ R Δ R_fin, BigF s R Δ R_fin → NoNonlast0F R → ValidHead R_fin := by
  refine Nat.strongRecOn (motive := fun m =>
    ∀ R Δ R_fin, BigF m R Δ R_fin → NoNonlast0F R → ValidHead R_fin) s ?_
  intro m ih R Δ R_fin hF hN
  cases hF with
  | nil => trivial
  | zeroF Y =>
    cases Y with
    | nil => trivial
    | cons _ _ => exact False.elim hN
  | zeroT _ => trivial
  | oneT _ => trivial
  | oneF_rem1 _ _ => trivial
  | twoF_rem1 _ _ => trivial
  | twoT_rem1 _ _ => trivial
  | ge3_rem1 _ _ => trivial
  | oneF_rem2 h1 _ h2 =>
    have h1N := (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_tail hN)
    cases h2 with | oneF h3 =>
      exact ih _ (by omega) _ _ _ h3
          (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | twoF_rem2 h1 _ h2 =>
    have h1N :=
        (bigFD_noNonlast0F _).1 _ _ _ h1
        (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN)))
    cases h2 with | oneF h3 =>
      exact ih _ (by omega) _ _ _ h3
          (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | twoT_rem2 h1 _ h2 =>
    have h1N :=
        (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (by simp) (noNonlast0F_tail hN))
    cases h2 with | oneF h3 =>
      exact ih _ (by omega) _ _ _ h3
          (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | ge3_rem2 h1 _ h2 =>
    have h1N := (bigFD_noNonlast0F _).2 _ _ _ h1 (noNonlast0F_tail hN)
    cases h2 with | oneF h3 =>
      exact ih _ (by omega) _ _ _ h3
          (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | @oneF_rem0 _ _ _ _ _ Δ1 _ h1 hrem h2 =>
    have h1N := (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_tail hN)
    cases hq : (1 + Δ1) / 3 with
    | zero => omega
    | succ k =>
      rw [hq] at h2
      cases h2 with | oneF h3 =>
        exact ih _ (by omega) _ _ _ h3
            (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | @ge3_rem0 _ _ _ _ _ _ _ Δ1 _ h1 hrem h2 =>
    have hge := ((bigFD_bounds _).2 _ _ _ h1).1 (by simp)
    have h1N := (bigFD_noNonlast0F _).2 _ _ _ h1 (noNonlast0F_tail hN)
    cases hq : Δ1 / 3 with
    | zero => omega
    | succ k =>
      rw [hq] at h2
      cases h2 with | oneF h3 =>
        exact ih _ (by omega) _ _ _ h3
            (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | @twoF_rem0 _ _ Y R1 _ Δ1 _ h1 hrem h2 =>
    have hYN := noNonlast0F_tail hN
    have h1N := (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_bumpR (noNonlast0F_bumpR hYN))
    cases hΔ : Δ1 with
    | zero =>
      subst hΔ
      simp only [Nat.zero_div, ones, List.nil_append] at h2
      cases Y with
      | nil =>
        cases h1 with
        | @oneF_rem1 _ _ R0 Δ0 h0 h0rem =>
          cases h2 with | zeroT _ =>
            cases hΔ0 : Δ0 with
            | zero =>
              subst hΔ0
              obtain ⟨x, xs, hEq, hx⟩ := bigF_zero_head_nnf h0 trivial
              rw [hEq]
              rcases hx with rfl | rfl | rfl <;> trivial
            | succ k0 =>
              cases hq0 : (1 + (k0 + 1)) / 3 with
              | zero => omega
              | succ j0 => trivial
        | oneF_rem2 ha _ hb =>
          have hge :=
              ((bigFD_bounds _).2 _ _ _ hb).1
              (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ ha).2)
          omega
      | cons x xs =>
        cases x with | mk d b =>
          obtain ⟨Z, rfl⟩ := bigF_ge2_zero_head h1
          cases h2 with | zeroT _ => trivial
    | succ k =>
      subst hΔ
      cases hq : (k + 1) / 3 with
      | zero => omega
      | succ j =>
        rw [hq] at h2
        cases h2 with | oneF h3 =>
          exact ih _ (by omega) _ _ _ h3
              (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))
  | @twoT_rem0 _ _ Y R1 _ Δ1 _ h1 hrem h2 =>
    have hYN := noNonlast0F_tail hN
    have h1N := (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (by simp) hYN)
    cases hΔ : Δ1 with
    | zero =>
      subst hΔ
      simp only [Nat.zero_div, ones, List.nil_append] at h2
      cases h1 with
      | @oneF_rem1 _ _ R0 Δ0 h0 h0rem =>
        cases h2 with | zeroT _ =>
          cases hΔ0 : Δ0 with
          | zero =>
            subst hΔ0
            obtain ⟨x, xs, hEq, hx⟩ := bigF_zero_head_nnf h0 hYN
            rw [hEq]
            rcases hx with rfl | rfl | rfl <;> trivial
          | succ k0 =>
            cases hq0 : (1 + (k0 + 1)) / 3 with
            | zero => omega
            | succ j0 => trivial
      | oneF_rem2 ha _ hb =>
        have hge :=
            ((bigFD_bounds _).2 _ _ _ hb).1
            (append_nonempty_of_right _ _ ((bigFD_bounds _).1 _ _ _ ha).2)
        omega
    | succ k =>
      subst hΔ
      cases hq : (k + 1) / 3 with
      | zero => omega
      | succ j =>
        rw [hq] at h2
        cases h2 with | oneF h3 =>
          exact ih _ (by omega) _ _ _ h3
              (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N)))



/-! ## Unconditional Algebraic & Master Inversion Lemmas (Zero Induction) -/

theorem bigD1_oneF_inv {s Δ' : Nat} {Y R_fin : List Seg}
    (h : BigD1 s ((1, false) :: Y) Δ' R_fin) :
    ∃ s' < s, ∃ Δ0, Δ' = Δ0 + 2 ∧ BigF s' (bumpR (bumpR Y)) Δ0 R_fin := by
  cases h with
  | oneF h0 => exact ⟨_, by omega, _, rfl, h0⟩

theorem bigD1_zeroF_inv {s Δ' : Nat} {Y R_fin : List Seg}
    (h : BigD1 s ((0, false) :: Y) Δ' R_fin) :
    ∃ s' < s, ∃ Δ0, Δ' = Δ0 + 3 ∧ BigF s' Y Δ0 R_fin := by
  cases h with
  | zeroF h0 => exact ⟨_, by omega, _, rfl, h0⟩

theorem bigD1_zeroT_inv {s Δ' : Nat} {Y R_fin : List Seg}
    (h : BigD1 s ((0, true) :: Y) Δ' R_fin) :
    Δ' = 3 ∧ R_fin = bumpR Y := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Master Inversion for `BigF s ((3, false) :: Y) Δ R_fin`. -/
theorem bigF_3_inv {s Δ : Nat} {Y R_fin : List Seg}
    (h : BigF s ((3, false) :: Y) Δ R_fin) :
    ∃ s1 < s, ∃ Δ0 R1, BigF s1 Y Δ0 R1 ∧
      ( (Δ0 % 3 = 1 ∧ 4 ≤ Δ0 ∧ Δ = 0 ∧
          R_fin = (0, true) :: (1, false) :: (1, false) :: ones (Δ0 / 3 - 1) ++ R1) ∨
        (Δ0 % 3 = 2 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧
          BigF s2 ((3, false) :: ones (Δ0 / 3) ++ R1) Δ3 R_fin) ∨
        (Δ0 = 0 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧
          BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
        (Δ0 % 3 = 0 ∧ 3 ≤ Δ0 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧
          BigF s2 ((3, false) :: ones (Δ0 / 3 - 1) ++ R1) Δ3 R_fin) ) := by
  cases h with
  | @ge3_rem1 k1 _ _ _ R1 Δ1 h1 hrem =>
    obtain ⟨s0, hs0, Δ0, hΔ1, h0⟩ := bigD1_zeroF_inv h1
    have hne1 := ((bigFD_bounds _).1 _ _ _ h0).1
    have hge4 : 4 ≤ Δ0 := by omega
    have hdiv : Δ1 / 3 = (Δ0 / 3 - 1) + 2 := by omega
    refine ⟨s0, by omega, Δ0, R1, h0, Or.inl ⟨by omega, hge4, rfl, ?_⟩⟩
    rw [hdiv]
    rfl
  | @ge3_rem2 k1 k2 _ _ _ R1 _ Δ1 _ h1 hrem h2 =>
    obtain ⟨s0, hs0, Δ0, hΔ1, h0⟩ := bigD1_zeroF_inv h1
    have hdiv : Δ1 / 3 + 1 = Δ0 / 3 + 2 := by omega
    rw [hdiv] at h2
    obtain ⟨s2, hs2, Δ3, hΔ3, hF2⟩ := bigD1_1_1_inv h2
    exact ⟨s0, by omega, Δ0, R1, h0, Or.inr (Or.inl ⟨by omega, s2, by omega, Δ3, hΔ3, hF2⟩)⟩
  | @ge3_rem0 k1 k2 _ _ _ R1 _ Δ1 Δ2 h1 hrem h2 =>
    obtain ⟨s0, hs0, Δ0, hΔ1, h0⟩ := bigD1_zeroF_inv h1
    cases hΔ0 : Δ0 with
    | zero =>
      subst hΔ0
      have hdiv : Δ1 / 3 = 1 := by omega
      rw [hdiv] at h2
      obtain ⟨s2, hs2, Δ3, hΔ3, hF2⟩ := bigD1_oneF_inv h2
      exact ⟨s0, by omega, 0, R1, h0, Or.inr (Or.inr (Or.inl ⟨rfl, s2, by omega, Δ3, by omega,
          hF2⟩))⟩
    | succ m =>
      subst hΔ0
      have hge3 : 3 ≤ m + 1 := by omega
      have hdiv : Δ1 / 3 = ((m + 1) / 3 - 1) + 2 := by omega
      rw [hdiv] at h2
      obtain ⟨s2, hs2, Δ3, hΔ3, hF2⟩ := bigD1_1_1_inv h2
      exact ⟨s0, by omega, m + 1, R1, h0, Or.inr (Or.inr (Or.inr ⟨by omega, hge3, s2, by omega, Δ3,
          by omega, hF2⟩))⟩

/-- Master Inversion for `BigF s ((1, false) :: Y) Δ R_fin`. -/
theorem bigF_1_inv {s Δ : Nat} {Y R_fin : List Seg}
    (h : BigF s ((1, false) :: Y) Δ R_fin) :
    ∃ s1 < s, ∃ Δ1 R1, BigF s1 Y Δ1 R1 ∧
      ( (Δ1 % 3 = 0 ∧ Δ = 0 ∧ R_fin = (0, true) :: ones (Δ1 / 3) ++ R1) ∨
        (Δ1 % 3 = 1 ∧ 4 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧
          BigF s2 ((3, false) :: ones (Δ1 / 3 - 1) ++ R1) Δ3 R_fin) ∨
        (Δ1 = 2 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧
          BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
        (Δ1 % 3 = 2 ∧ 5 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧
          BigF s2 ((3, false) :: ones (Δ1 / 3 - 1) ++ R1) Δ3 R_fin) ) := by
  cases h with
  | @oneF_rem1 k1 _ R1 Δ1 h1 hrem =>
    have hdiv : (1 + Δ1) / 3 = Δ1 / 3 := by omega
    refine ⟨k1, by omega, Δ1, R1, h1, Or.inl ⟨by omega, rfl, ?_⟩⟩
    rw [hdiv]
  | @oneF_rem2 k1 k2 _ R1 _ Δ1 _ h1 hrem h2 =>
    have hne1 := ((bigFD_bounds _).1 _ _ _ h1).1
    have hge4 : 4 ≤ Δ1 := by omega
    have hdiv : (1 + Δ1) / 3 + 1 = (Δ1 / 3 - 1) + 2 := by omega
    rw [hdiv] at h2
    obtain ⟨s2, hs2, Δ3, hΔ3, hF2⟩ := bigD1_1_1_inv h2
    exact ⟨k1, by omega, Δ1, R1, h1, Or.inr (Or.inl ⟨by omega, hge4, s2, by omega, Δ3, hΔ3, hF2⟩)⟩
  | @oneF_rem0 k1 k2 _ R1 _ Δ1 Δ2 h1 hrem h2 =>
    by_cases h2eq : Δ1 = 2
    · subst h2eq
      have hdiv : (1 + 2) / 3 = 1 := rfl
      rw [hdiv] at h2
      obtain ⟨s2, hs2, Δ3, hΔ3, hF2⟩ := bigD1_oneF_inv h2
      exact ⟨k1, by omega, 2, R1, h1, Or.inr (Or.inr (Or.inl ⟨rfl, s2, by omega, Δ3, by omega,
          hF2⟩))⟩
    · have hge5 : 5 ≤ Δ1 := by omega
      have hdiv : (1 + Δ1) / 3 = (Δ1 / 3 - 1) + 2 := by omega
      rw [hdiv] at h2
      obtain ⟨s2, hs2, Δ3, hΔ3, hF2⟩ := bigD1_1_1_inv h2
      exact ⟨k1, by omega, Δ1, R1, h1, Or.inr (Or.inr (Or.inr ⟨by omega, hge5, s2, by omega, Δ3,
          by omega, hF2⟩))⟩

private theorem disp_of_bigF_aux {s2 Δ1 Δ2 : Nat} {R1 R_fin : List Seg}
    (hrem0 : Δ1 % 3 = 0)
    (h2 : BigD1 s2 (ones (Δ1 / 3) ++ R1) Δ2 R_fin) :
    (Δ1 = 0 ∧ BigD1 s2 R1 Δ2 R_fin) ∨
    (Δ1 = 3 ∧ ∃ s' < s2, ∃ Δ3, Δ2 = Δ3 + 2 ∧ BigF s' (bumpR (bumpR R1)) Δ3 R_fin) ∨
    (Δ1 % 3 = 0 ∧ 6 ≤ Δ1 ∧ ∃ s' < s2, ∃ Δ3, Δ2 = Δ3 + 2 ∧ BigF s' ((3,
        false) :: ones (Δ1 / 3 - 2) ++ R1) Δ3 R_fin) := by
  by_cases h0 : Δ1 = 0
  · subst h0
    simp only [Nat.zero_div, ones, List.nil_append] at h2
    exact Or.inl ⟨rfl, h2⟩
  · by_cases h3 : Δ1 = 3
    · subst h3
      have hdiv : 3 / 3 = 1 := rfl
      rw [hdiv] at h2
      obtain ⟨s', hs', Δ3, hΔ3, hF'⟩ := bigD1_oneF_inv h2
      exact Or.inr (Or.inl ⟨rfl, s', hs', Δ3, hΔ3, hF'⟩)
    · have hge6 : 6 ≤ Δ1 := by omega
      have hdiv : Δ1 / 3 = (Δ1 / 3 - 2) + 2 := by omega
      rw [hdiv] at h2
      obtain ⟨s', hs', Δ3, hΔ3, hF'⟩ := bigD1_1_1_inv h2
      exact Or.inr (Or.inr ⟨hrem0, hge6, s', hs', Δ3, hΔ3, hF'⟩)

private theorem disp_rem2_of_bigF_aux {s2 Δ1 Δ2 : Nat} {R1 R_fin : List Seg}
    (hrem2 : Δ1 % 3 = 2)
    (h2 : BigD1 s2 (ones (Δ1 / 3 + 1) ++ R1) Δ2 R_fin) :
    (Δ1 = 2 ∧ ∃ s' < s2, ∃ Δ3, Δ2 = Δ3 + 2 ∧ BigF s' (bumpR (bumpR R1)) Δ3 R_fin) ∨
    (Δ1 % 3 = 2 ∧ 5 ≤ Δ1 ∧ ∃ s' < s2, ∃ Δ3, Δ2 = Δ3 + 2 ∧ BigF s' ((3,
        false) :: ones (Δ1 / 3 - 1) ++ R1) Δ3 R_fin) := by
  by_cases h2eq : Δ1 = 2
  · subst h2eq
    have hdiv : 2 / 3 + 1 = 1 := rfl
    rw [hdiv] at h2
    obtain ⟨s', hs', Δ3, hΔ3, hF'⟩ := bigD1_oneF_inv h2
    exact Or.inl ⟨rfl, s', hs', Δ3, hΔ3, hF'⟩
  · have hge5 : 5 ≤ Δ1 := by omega
    have hdiv : Δ1 / 3 + 1 = (Δ1 / 3 - 1) + 2 := by omega
    rw [hdiv] at h2
    obtain ⟨s', hs', Δ3, hΔ3, hF'⟩ := bigD1_1_1_inv h2
    exact Or.inr ⟨hrem2, hge5, s', hs', Δ3, hΔ3, hF'⟩

/-- Master Inversion for `BigF s ((2, false) :: Y) Δ R_fin`. -/
theorem bigF_2_inv {s Δ : Nat} {Y R_fin : List Seg}
    (h : BigF s ((2, false) :: Y) Δ R_fin) :
    ∃ s1 < s, ∃ Δ1 R1, BigF s1 (bumpR (bumpR Y)) Δ1 R1 ∧
      ( (Δ1 % 3 = 1 ∧ 4 ≤ Δ1 ∧ Δ = 0 ∧ R_fin = (0, true) :: ones (Δ1 / 3) ++ R1) ∨
        (Δ1 = 2 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧ BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
        (Δ1 % 3 = 2 ∧ 5 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧ BigF s2 ((3,
            false) :: ones (Δ1 / 3 - 1) ++ R1) Δ3 R_fin) ∨
        (Δ1 = 0 ∧ ∃ s2 < s, ∃ Δ2, Δ = Δ2 + 1 ∧ BigD1 s2 R1 Δ2 R_fin) ∨
        (Δ1 = 3 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧ BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
        (Δ1 % 3 = 0 ∧ 6 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧ BigF s2 ((3,
            false) :: ones (Δ1 / 3 - 2) ++ R1) Δ3 R_fin) ) := by
  cases h with
  | @twoF_rem1 k1 _ R1 Δ1 h1 hrem =>
    have hne1 := ((bigFD_bounds _).1 _ _ _ h1).1
    exact ⟨k1, by omega, Δ1, R1, h1, Or.inl ⟨hrem, by omega, rfl, rfl⟩⟩
  | @twoF_rem2 k1 k2 _ R1 _ Δ1 _ h1 hrem h2 =>
    rcases disp_rem2_of_bigF_aux hrem h2 with ⟨rfl, s', hs', Δ3, rfl, hF'⟩ | ⟨hr, hg, s', hs', Δ3,
        rfl, hF'⟩
    · exact ⟨k1, by omega, 2, R1, h1, Or.inr (Or.inl ⟨rfl, s', by omega, Δ3, rfl, hF'⟩)⟩
    · exact ⟨k1, by omega, Δ1, R1, h1, Or.inr (Or.inr (Or.inl ⟨hr, hg, s', by omega, Δ3, rfl,
                                                                            hF'⟩))⟩
  | @twoF_rem0 k1 k2 _ R1 _ Δ1 Δ2 h1 hrem h2 =>
    rcases disp_of_bigF_aux hrem h2 with ⟨rfl, hD⟩ | ⟨rfl, s', hs', Δ3, hΔ3, hF'⟩ | ⟨hr, hg, s',
        hs', Δ3, hΔ3, hF'⟩
    · exact ⟨k1, by omega, 0, R1, h1, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k2, by omega, Δ2, rfl,
          hD⟩)))⟩
    · exact ⟨k1, by omega, 3, R1, h1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, s', by omega, Δ3,
          by omega, hF'⟩))))⟩
    · exact ⟨k1, by omega, Δ1, R1, h1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, hg, s', by omega,
          Δ3, by omega, hF'⟩))))⟩

/-- Master Inversion for `BigF s ((2, true) :: Y) Δ R_fin`. -/
theorem bigF_2s_inv {s Δ : Nat} {Y R_fin : List Seg}
    (h : BigF s ((2, true) :: Y) Δ R_fin) :
    ∃ s1 < s, ∃ Δ1 R1, BigF s1 ((1, false) :: Y) Δ1 R1 ∧
      ( (Δ1 % 3 = 1 ∧ 4 ≤ Δ1 ∧ Δ = 0 ∧ R_fin = (0, true) :: ones (Δ1 / 3) ++ R1) ∨
        (Δ1 = 2 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧ BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
        (Δ1 % 3 = 2 ∧ 5 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧ BigF s2 ((3,
            false) :: ones (Δ1 / 3 - 1) ++ R1) Δ3 R_fin) ∨
        (Δ1 = 0 ∧ ∃ s2 < s, ∃ Δ2, Δ = Δ2 + 1 ∧ BigD1 s2 R1 Δ2 R_fin) ∨
        (Δ1 = 3 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧ BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
        (Δ1 % 3 = 0 ∧ 6 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧ BigF s2 ((3,
            false) :: ones (Δ1 / 3 - 2) ++ R1) Δ3 R_fin) ) := by
  cases h with
  | @twoT_rem1 k1 _ R1 Δ1 h1 hrem =>
    have hne1 := ((bigFD_bounds _).1 _ _ _ h1).1
    exact ⟨k1, by omega, Δ1, R1, h1, Or.inl ⟨hrem, by omega, rfl, rfl⟩⟩
  | @twoT_rem2 k1 k2 _ R1 _ Δ1 _ h1 hrem h2 =>
    rcases disp_rem2_of_bigF_aux hrem h2 with ⟨rfl, s', hs', Δ3, rfl, hF'⟩ | ⟨hr, hg, s', hs', Δ3,
        rfl, hF'⟩
    · exact ⟨k1, by omega, 2, R1, h1, Or.inr (Or.inl ⟨rfl, s', by omega, Δ3, rfl, hF'⟩)⟩
    · exact ⟨k1, by omega, Δ1, R1, h1, Or.inr (Or.inr (Or.inl ⟨hr, hg, s', by omega, Δ3, rfl,
                                                                            hF'⟩))⟩
  | @twoT_rem0 k1 k2 _ R1 _ Δ1 Δ2 h1 hrem h2 =>
    rcases disp_of_bigF_aux hrem h2 with ⟨rfl, hD⟩ | ⟨rfl, s', hs', Δ3, hΔ3, hF'⟩ | ⟨hr, hg, s',
        hs', Δ3, hΔ3, hF'⟩
    · exact ⟨k1, by omega, 0, R1, h1, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k2, by omega, Δ2, rfl,
          hD⟩)))⟩
    · exact ⟨k1, by omega, 3, R1, h1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, s', by omega, Δ3,
          by omega, hF'⟩))))⟩
    · exact ⟨k1, by omega, Δ1, R1, h1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, hg, s', by omega,
          Δ3, by omega, hF'⟩))))⟩

/-- Exact `F(3* :: Y) = 3 + F(bump^3 Y)`, strictly decreasing `s`! -/
theorem bigF_3s_inv {s Δ : Nat} {Y R_fin : List Seg}
    (h : BigF s ((3, true) :: Y) Δ R_fin) :
    ∃ s' < s, ∃ Δ0, Δ = Δ0 + 3 ∧ BigF s' (bumpR (bumpR (bumpR Y))) Δ0 R_fin := by
  cases h with
  | ge3_rem1 h1 hrem =>
    obtain ⟨rfl, rfl⟩ := bigD1_zeroT_inv h1; omega
  | ge3_rem2 h1 hrem _ =>
    obtain ⟨rfl, rfl⟩ := bigD1_zeroT_inv h1; omega
  | ge3_rem0 h1 _ h2 =>
    obtain ⟨rfl, rfl⟩ := bigD1_zeroT_inv h1
    obtain ⟨s', hs', Δ0, rfl, hF'⟩ := bigD1_oneF_inv h2
    exact ⟨s', by omega, Δ0, by omega, hF'⟩

/-- Exact `F(3, 1, 0* :: Y) = 3 + F(2*, 1 :: Y)`, strictly decreasing `s`! -/
theorem bigF_3_1_0s_inv {s Δ : Nat} {Y R_fin : List Seg}
    (h : BigF s ((3, false) :: (1, false) :: (0, true) :: Y) Δ R_fin) :
    ∃ s' < s, ∃ Δ0, Δ = Δ0 + 3 ∧ BigF s' ((2, true) :: (1, false) :: Y) Δ0 R_fin := by
  have h10 : BigF 1 ((1, false) :: (0, true) :: Y) 0 ((0, true) :: (1, false) :: Y) :=
    BigF.oneF_rem1 (BigF.zeroT Y) rfl
  obtain ⟨s1, hs1, Δ0, R1, hF1, hcases⟩ := bigF_3_inv h
  obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF1 h10
  rcases hcases with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, _, _, _, _,
      _⟩
  · omega
  · omega
  · exact ⟨s2, hs2, Δ3, rfl, hF2⟩
  · omega

/-- Unconditional `F(3, 1, 1, 0* :: Y) = (7, [2, 1 :: Y])`. -/
theorem bigF_3_1_1_0s_exists (Y : List Seg) :
    BigF 7 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: Y) 7 ((2, false) :: (1,
        false) :: Y) := by
  have h1 : BigD1 3 ((0, false) :: (1, false) :: (1, false) :: (0, true) :: Y) 3
      ((0, true) :: (0, true) :: (1, false) :: Y) :=
    BigD1.zeroF (BigF.oneF_rem1 (BigF.oneF_rem1 (BigF.zeroT Y) rfl) rfl)
  exact BigF.ge3_rem0 h1 rfl (BigD1.oneF (bigF_2s_0s_exists ((1, false) :: Y)))

/-- Unconditional `F(2*, 1, 0* :: Y) = (4, [1*, 1 :: Y])`. -/
theorem bigF_2s_1_0s_exists (Y : List Seg) :
    BigF 3 ((2, true) :: (1, false) :: (0, true) :: Y) 4 ((1, true) :: (1, false) :: Y) :=
  BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneF_rem1 (BigF.zeroT Y) rfl) rfl) rfl
    (BigD1.zeroT ((0, true) :: (1, false) :: Y))

/-- Unconditional `F(2*, 0) = (4, [2])`. -/
theorem bigF_2s_0_exists :
    BigF 2 ((2, true) :: [(0, false)]) 4 [(2, false)] :=
  BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.zeroF []) rfl) rfl (BigD1.zeroT [(1, false)])

/-- Unconditional `F([2]) = (4, [1])`. Wait: `bump^2 [] = [1]`, `F([1]) = (0, [0*, 0])`, `D1([0*,
    0]) = (3, [1])`, so `F([2]) = (4, [1])`! -/
theorem bigF_2_nil_exists :
    ∃ s, BigF s [(2, false)] 4 [(1, false)] :=
  ⟨_, BigF.twoF_rem0 (BigF.oneF_rem1 BigF.nil rfl) rfl (BigD1.zeroT [(0, false)])⟩

/-- Unconditional `F([3]) = (7, [1])`. -/
theorem bigF_3_nil_exists :
    ∃ s, BigF s [(3, false)] 7 [(1, false)] := by
  obtain ⟨s2, h2⟩ := bigF_2_nil_exists
  exact ⟨_, BigF.ge3_rem0 (BigD1.zeroF BigF.nil) rfl (BigD1.oneF h2)⟩

/-- Unconditional `F([2, 1*, 0]) = (0, [0*, 1, 1, 1, 1])`. -/
theorem bigF_2_1s_0_exists :
    ∃ s, BigF s [(2, false), (1, true), (0, false)] 0 [(0, true), (1, false), (1, false), (1,
        false), (1, false)] := by
  obtain ⟨s3, h3⟩ := bigF_3_nil_exists
  have h3s : BigF (0 + (s3 + 1) + 1) (bumpR (bumpR [(1, true), (0, false)])) 10 [(1, false)] :=
    BigF.ge3_rem0 (BigD1.zeroT [(0, false)]) rfl (BigD1.oneF h3)
  exact ⟨_, BigF.twoF_rem1 h3s rfl⟩

/-- Unconditional: `BigF s ((3, false) :: Y) 0 R_fin` ALWAYS returns `[0*, 1, 1 :: Z]`. -/
theorem bigF_3_zero_prefix {s : Nat} {Y R_fin : List Seg}
    (h : BigF s ((3, false) :: Y) 0 R_fin) :
    ∃ Z, R_fin = (0, true) :: (1, false) :: (1, false) :: Z := by
  obtain ⟨_, _, _, _, _, hcases⟩ := bigF_3_inv h
  rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, hΔ, _⟩ | ⟨_, _, _, _, hΔ, _⟩ | ⟨_, _, _, _, _,
      hΔ, _⟩
  · exact ⟨_, rfl⟩
  · omega
  · omega
  · omega

/-- Unconditional: `BigD1 s ((d, b) :: Y) 4 R_fin` ALWAYS has `R_fin = (0, true) :: Z`! -/
theorem bigD1_four_head {s d : Nat} {b : Bool} {Y R_fin : List Seg}
    (h : BigD1 s ((d, b) :: Y) 4 R_fin) :
    ∃ Z, R_fin = (0, true) :: Z := by
  cases h with
  | zeroF h0 => exact absurd rfl ((bigFD_bounds _).1 _ _ _ h0).1
  | oneF h0 =>
    obtain ⟨Z, hZ⟩ := bigF_two_head h0
    exact ⟨(1, false) :: Z, hZ⟩
  | oneT h0 =>
    obtain ⟨Z, hZ⟩ := bigF_two_head h0
    exact ⟨(1, false) :: Z, hZ⟩
  | @ge2 _ d' _ _ _ Δ0 h0 =>
    cases h0 with
    | oneF ha =>
      cases Y with
      | nil => exact bigF_oneF_zero_head ha
      | cons x xs =>
        cases x
        obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head ha
        exact ⟨(1, false) :: Z, hZ⟩
    | oneT ha => exact bigF_oneF_zero_head ha
    | ge2 ha =>
      have hge := ((bigFD_bounds _).2 _ _ _ ha).1 (by simp)
      omega

/-- Unconditional: `BigF s ((d + 3, b) :: Y) 0 R_fin` ALWAYS returns `[0*, 1, 1 :: Z] ∨ [0*, 1, 0*
    :: Z]`! -/
theorem bigF_ge3_zero_prefix {s d : Nat} {b : Bool} {Y R_fin : List Seg}
    (h : BigF s ((d + 3, b) :: Y) 0 R_fin) :
    (∃ Z, R_fin = (0, true) :: (1, false) :: (1, false) :: Z) ∨
    (∃ Z, R_fin = (0, true) :: (1, false) :: (0, true) :: Z) := by
  cases h with
  | @ge3_rem1 _ _ _ _ R1 Δ1 h1 hrem =>
    have hge2 := ((bigFD_bounds _).2 _ _ _ h1).1 (by simp)
    by_cases h4 : Δ1 = 4
    · subst h4
      obtain ⟨Z, rfl⟩ := bigD1_four_head h1
      exact Or.inr ⟨Z, rfl⟩
    · have hge7 : 7 ≤ Δ1 := by omega
      have hdiv : Δ1 / 3 = (Δ1 / 3 - 2) + 2 := by omega
      rw [hdiv]
      exact Or.inl ⟨ones (Δ1 / 3 - 2) ++ R1, rfl⟩
  | ge3_rem2 h1 _ h2 =>
    have hne := ((bigFD_bounds _).2 _ _ _ h1).2
    have hge := ((bigFD_bounds _).2 _ _ _ h2).1 (append_nonempty_of_right _ _ hne)
    omega

/-- Unconditional: `BigF` never returns `Δ = 1`. -/
theorem bigF_ne_one {s : Nat} {R R_fin : List Seg} (h : BigF s R 1 R_fin) : False :=
  ((bigFD_bounds s).1 R 1 R_fin h).1 rfl

/-- Unconditional: `BigD1` on a nonempty tape returns `Δ ≥ 2`. -/
theorem bigD1_ge2_of_ne_nil {s : Nat} {R R_fin : List Seg} {Δ : Nat}
    (h : BigD1 s R Δ R_fin) (hne : R ≠ []) : 2 ≤ Δ :=
  ((bigFD_bounds s).2 R Δ R_fin h).1 hne

/-- Unconditional: `BigF` always outputs a nonempty tape. -/
theorem bigF_out_ne_nil {s : Nat} {R R_fin : List Seg} {Δ : Nat}
    (h : BigF s R Δ R_fin) : R_fin ≠ [] :=
  ((bigFD_bounds s).1 R Δ R_fin h).2

/-- Unconditional: `BigD1` always outputs a nonempty tape. -/
theorem bigD1_out_ne_nil {s : Nat} {R R_fin : List Seg} {Δ : Nat}
    (h : BigD1 s R Δ R_fin) : R_fin ≠ [] :=
  ((bigFD_bounds s).2 R Δ R_fin h).2

/-- Unconditional: `bumpR R` never starts with `(0, true)`. -/
theorem bumpR_head_ne_zeroT (R : List Seg) (Z : List Seg) :
    bumpR R ≠ (0, true) :: Z := by
  cases R with
  | nil => simp [bumpR]
  | cons x xs =>
    cases x with
    | mk d b => simp [bumpR]

/-- Unconditional: `F(Y) = (0, [1 :: Z])` with `NoNonlast0F Y` forces `Y = [(0, false)] ∧ Z = []` or
    `Y = [0* :: Z]`. -/
theorem bigF_zero_oneF_head {s : Nat} {Y Z : List Seg}
    (h : BigF s Y 0 ((1, false) :: Z)) (hnnf : NoNonlast0F Y) :
    (Y = [(0, false)] ∧ Z = []) ∨ Y = (0, true) :: Z := by
  generalize hΔ : (0 : Nat) = Δ at h
  generalize hR : ((1, false) :: Z) = R_fin at h
  cases h with
  | nil => simp at hR
  | @zeroF Y0 =>
    cases Y0 with
    | nil =>
      simp only [bumpR, List.cons.injEq, true_and] at hR
      exact Or.inl ⟨rfl, hR⟩
    | cons x xs =>
      simp [NoNonlast0F] at hnnf
  | zeroT =>
    cases hR
    exact Or.inr rfl
  | oneT => simp at hR
  | oneF_rem1 => simp at hR
  | twoF_rem1 => simp at hR
  | twoT_rem1 => simp at hR
  | ge3_rem1 => simp at hR
  | oneF_rem0 => omega
  | twoF_rem0 => omega
  | twoT_rem0 => omega
  | ge3_rem0 => omega
  | oneF_rem2 h1 _ h2 =>
    have hge := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))
    omega
  | twoF_rem2 h1 _ h2 =>
    have hge := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))
    omega
  | twoT_rem2 h1 _ h2 =>
    have hge := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))
    omega
  | ge3_rem2 h1 _ h2 =>
    have hge := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigD1_out_ne_nil h1))
    omega

/-- Unconditional: `F(2*, 0* :: W) = (4, [2 :: W])`. -/
theorem bigF_2s_0s_full_exists (W : List Seg) :
    BigF 2 ((2, true) :: (0, true) :: W) 4 ((2, false) :: W) := by
  have h1 : BigF 1 ((1, false) :: (0, true) :: W) 0 ((0, true) :: (1, false) :: W) :=
    BigF.oneF_rem1 (BigF.zeroT W) rfl
  exact BigF.twoT_rem0 h1 rfl (BigD1.zeroT ((1, false) :: W))


/-! ## Syntactic Predicates, InvAt (m : Nat), and Groups 1 & 2 Step Lemmas -/


/-- Unconditional: `F(2*, 1, 1, 0* :: U) = (4, [1*, 0*, 1 :: U])`. -/
theorem bigF_2s_1_1_0s_exists (U : List Seg) :
    BigF 4 ((2, true) :: (1, false) :: (1, false) :: (0, true) :: U) 4
      ((1, true) :: (0, true) :: (1, false) :: U) := by
  have h0 : BigF 0 ((0, true) :: U) 0 ((1, false) :: U) := BigF.zeroT U
  have h1 : BigF 1 ((1, false) :: (0, true) :: U) 0 ((0, true) :: (1, false) :: U) :=
    BigF.oneF_rem1 h0 rfl
  have h2 : BigF 2 ((1, false) :: (1, false) :: (0, true) :: U) 0
      ((0, true) :: (0, true) :: (1, false) :: U) :=
    BigF.oneF_rem1 h1 rfl
  have h3 : BigF 3 ((1, false) :: (1, false) :: (1, false) :: (0, true) :: U) 0
      ((0, true) :: (0, true) :: (0, true) :: (1, false) :: U) :=
    BigF.oneF_rem1 h2 rfl
  exact BigF.twoT_rem0 h3 rfl (BigD1.zeroT ((0, true) :: (0, true) :: (1, false) :: U))

/-- Clean 3-way `BigF s Y 0 R1` head classification under `NoNonlast0F Y`. -/
theorem bigF_zero_head_3 {s : Nat} {Y R1 : List Seg}
    (h : BigF s Y 0 R1) (hN : NoNonlast0F Y) :
    R1 = [(0, false)] ∨
    (∃ Z, R1 = (0, true) :: Z) ∨
    (∃ Z, R1 = (1, false) :: Z) := by
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h hN
  obtain ⟨x, xs, rfl, hx⟩ := bigF_zero_head_nnf h hN
  rcases hx with rfl | rfl | rfl
  · cases xs with
    | nil => exact Or.inl rfl
    | cons y ys => exact False.elim hN1
  · exact Or.inr (Or.inl ⟨xs, rfl⟩)
  · exact Or.inr (Or.inr ⟨xs, rfl⟩)

/-- Unconditional: `BigD1 s ((d, b) :: Y) 2 R1` under `NoNonlast0F Y` has
    `R1 = [0*, 0] ∨ [0*, 0* :: Z] ∨ [0*, 1 :: Z]`. -/
theorem bigD1_two_head_nnf {s d : Nat} {b : Bool} {Y R1 : List Seg}
    (h : BigD1 s ((d, b) :: Y) 2 R1) (hNY : NoNonlast0F Y) :
    R1 = [(0, true), (0, false)] ∨
    (∃ Z, R1 = (0, true) :: (0, true) :: Z) ∨
    (∃ Z, R1 = (0, true) :: (1, false) :: Z) := by
  cases h with
  | oneF h0 =>
    cases Y with
    | nil =>
      cases h0 with
      | oneF_rem1 h1 _ =>
        cases h1
        exact Or.inl rfl
      | oneF_rem2 h1 _ h2 =>
        have hge := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))
        omega
    | cons x xs =>
      cases x with
      | mk d' b' =>
        obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head h0
        exact Or.inr (Or.inr ⟨Z, hZ⟩)
  | oneT h0 =>
    cases h0 with
    | oneF_rem1 h1 hrem =>
      rename_i s0 R0 Δ0
      by_cases h0z : Δ0 = 0
      · subst h0z
        rcases bigF_zero_head_3 h1 hNY with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨Z, rfl⟩)
        · exact Or.inr (Or.inr ⟨Z, rfl⟩)
      · have hq : 1 ≤ (1 + Δ0) / 3 := by omega
        obtain ⟨Z, hZ⟩ := ones_pos_cons hq R0
        exact Or.inr (Or.inr ⟨Z, congrArg ((0, true) :: ·) hZ⟩)
    | oneF_rem2 h1 _ h2 =>
      have hge := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))
      omega
  | ge2 h0 =>
    have hge := bigD1_ge2_of_ne_nil h0 (by simp)
    omega

/-! ## Syntactic Predicates (Sealed: derdenye + kalbaugh + texstapa U_bomb) -/

def Head0s11 (R : List Seg) : Prop :=
  ∃ Z, R = (0, true) :: (1, false) :: (1, false) :: Z

def Head0s111 (R : List Seg) : Prop :=
  ∃ Z, R = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z

def GoodZero111Head (Y : List Seg) : Prop :=
  (∀ Z, Y ≠ (0, true) :: Z) ∨ (∃ Z, Y = (0, true) :: (1, false) :: Z)

def GoodF2U (U : List Seg) : Prop :=
  (∃ W, U = (1, false) :: W) ∨
  (∃ W, U = (1, true) :: W) ∨
  (∃ W, U = (2, false) :: W) ∨
  Head0s11 U

theorem goodF2U_to_goodZero111Head {U : List Seg} (h : GoodF2U U) : GoodZero111Head U := by
  rcases h with ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨Z, rfl⟩
  · exact Or.inl (fun _ hEq => by cases hEq)
  · exact Or.inl (fun _ hEq => by cases hEq)
  · exact Or.inl (fun _ hEq => by cases hEq)
  · exact Or.inr ⟨(1, false) :: Z, rfl⟩

def Good1 (R : List Seg) : Prop :=
  R = [(1, true), (0, true), (0, false)] ∨
  (∃ Z, R = (1, true) :: (0, true) :: (0, true) :: Z) ∨
  R = [(1, true), (0, true), (1, false)] ∨
  R = [(1, true), (0, true), (1, false), (0, false)] ∨
  (∃ Z, R = (1, true) :: (0, true) :: (1, false) :: (0, true) :: Z) ∨
  (∃ Z, R = (1, true) :: (0, true) :: (1, false) :: (1, false) :: Z) ∨
  (∃ Z, R = (1, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z) ∨
  (∃ Z, R = (1, true) :: (1, false) :: (1, false) :: (1, false) :: Z ∧ GoodF2U Z) ∨
  (∃ Z, R = (2, false) :: (1, false) :: (1, false) :: Z)

inductive Good2 : List Seg → Prop
  | of_good1 {R : List Seg} : Good1 R → Good2 R
  | c_2_0 : Good2 [(2, false), (0, false)]
  | c_2_1 : Good2 [(2, false), (1, false)]
  | c_2_1_2 : Good2 [(2, false), (1, false), (2, false)]
  | c_2_0s (Z : List Seg) : Good2 ((2, false) :: (0, true) :: Z)
  | c_2_1s_0 : Good2 [(2, false), (1, true), (0, false)]
  | c_2_1s_0s (Z : List Seg) : Good2 ((2, false) :: (1, true) :: (0, true) :: Z)
  | c_2_1s_1 : Good2 [(2, false), (1, true), (1, false)]
  | c_2_1s_1_0 : Good2 [(2, false), (1, true), (1, false), (0, false)]
  | c_2_1s_1_0s (Z : List Seg) : Good2 ((2, false) :: (1, true) :: (1, false) :: (0, true) :: Z)
  | c_2_1s_1_1 (Z : List Seg) : Good2 ((2, false) :: (1, true) :: (1, false) :: (1, false) :: Z)
  | c_2_1_0s (Z : List Seg) : Good2 ((2, false) :: (1, false) :: (0, true) :: Z)
  | c_2_1_1 (Z : List Seg) : Good2 ((2, false) :: (1, false) :: (1, false) :: Z)
  | c_2_1_1s (Z : List Seg) : Good2 ((2, false) :: (1, false) :: (1, true) :: Z)
  | c_2_2_0s_1_1 (Z : List Seg) : Good2 ((2, false) :: (2, false) :: (0, true) :: (1, false) :: (1,
      false) :: Z)
  | c_2_2_1_0s_1_1 (Z : List Seg) : Good2 ((2, false) :: (2, false) :: (1, false) :: (0,
      true) :: (1, false) :: (1, false) :: Z)
  | c_2_2_1_1_gf {Z : List Seg} : GoodF2U Z → Good2 ((2, false) :: (2, false) :: (1, false) :: (1,
      false) :: Z)
  | step_21 {G : List Seg} : Good2 G → Good2 ((2, false) :: (1, false) :: G)

def GoodStrongHead (U : List Seg) : Prop :=
  U = [] ∨
  U = [(0, false)] ∨
  (∃ W, U = (0, true) :: W ∧ (W = [] ∨ Good2 ((2, false) :: W))) ∨
  (∃ W, U = (1, false) :: W) ∨
  (∃ W, U = (1, true) :: W) ∨
  Good2 U

def Strong2 (G : List Seg) : Prop :=
  Good2 G ∧ (∀ U, G = (2, false) :: (0, true) :: U → GoodStrongHead U)

def GoodTail (Z : List Seg) : Prop :=
  Good2 Z ∨ Head0s11 Z ∨
  (∃ W, Z = (1, false) :: W ∧ (Good2 W ∨ Head0s11 W)) ∨
  (∃ W, Z = (1, false) :: (1, false) :: W)

def Good1Safe (R : List Seg) : Prop :=
  Good1 R ∧ (∀ Z, R = (2, false) :: (1, false) :: (1, false) :: Z → GoodTail Z)

def SafeU (U : List Seg) : Prop :=
  (∃ Z, U = (1, false) :: (1, false) :: (1, false) :: Z) ∨
  (∃ Z, U = (1, false) :: (1, false) :: Z ∧ (Good2 Z ∨ Head0s11 Z)) ∨
  (∃ Z, U = (1, false) :: Z ∧ (Good2 Z ∨ Head0s11 Z)) ∨
  Head0s111 U ∨
  Good1Safe U

def Safe0s (R : List Seg) : Prop :=
  ∃ U, R = (0, true) :: (1, false) :: (1, false) :: U ∧ SafeU U

inductive Good4Out : List Seg → Prop
  | two_one_one : Good4Out [(2, false), (1, false), (1, false)]
  | of_1_1_1s (Z : List Seg) : Good4Out ((2, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
      true) :: Z)
  | of_safeU {U : List Seg} : SafeU U → Good4Out ((2, false) :: (1, false) :: U)
  | step_21 {Z : List Seg} : Good4Out Z → Good4Out ((2, false) :: (1, false) :: Z)

def Zero111 (R : List Seg) : Prop :=
  R = [(0, true), (0, true), (0, true), (0, false)] ∨
  (∃ Z, R = (0, true) :: (0, true) :: (0, true) :: (0, true) :: Z) ∨
  (∃ Z, R = (0, true) :: (0, true) :: (0, true) :: (1, false) :: Z) ∨
  (∃ Z, R = (0, true) :: (0, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
      false) :: Z) ∨
  (∃ Z, R = (0, true) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z ∧ GoodF2U Z) ∨
  (∃ Z, R = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z ∧ GoodTail Z)

def TightZero111 (R : List Seg) : Prop :=
  Zero111 R ∧
  (∀ Z, R = (0, true) :: (0, true) :: (0, true) :: (1, false) :: Z →
    Z = [] ∨ (∃ W, Z = (0, true) :: W) ∨ (∃ W, Z = (1, false) :: W))

theorem head0s111_to_head0s11 {R : List Seg} (h : Head0s111 R) : Head0s11 R := by
  obtain ⟨Z, rfl⟩ := h; exact ⟨(1, false) :: Z, rfl⟩

theorem safe0s_to_head0s11 {R : List Seg} (h : Safe0s R) : Head0s11 R := by
  obtain ⟨U, rfl, _⟩ := h; exact ⟨U, rfl⟩

theorem safeU_to_goodF2U {U : List Seg} (h : SafeU U) : GoodF2U U := by
  rcases h with ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl⟩ | ⟨hG1, _⟩
  · exact Or.inl ⟨(1, false) :: (1, false) :: Z, rfl⟩
  · exact Or.inl ⟨(1, false) :: Z, rfl⟩
  · exact Or.inl ⟨Z, rfl⟩
  · exact Or.inr (Or.inr (Or.inr ⟨(1, false) :: Z, rfl⟩))
  · rcases hG1 with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z,
        rfl⟩
    · exact Or.inr (Or.inl ⟨[(0, true), (0, false)], rfl⟩)
    · exact Or.inr (Or.inl ⟨(0, true) :: (0, true) :: Z, rfl⟩)
    · exact Or.inr (Or.inl ⟨[(0, true), (1, false)], rfl⟩)
    · exact Or.inr (Or.inl ⟨[(0, true), (1, false), (0, false)], rfl⟩)
    · exact Or.inr (Or.inl ⟨(0, true) :: (1, false) :: (0, true) :: Z, rfl⟩)
    · exact Or.inr (Or.inl ⟨(0, true) :: (1, false) :: (1, false) :: Z, rfl⟩)
    · exact Or.inr (Or.inl ⟨(1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z,
          rfl⟩)
    · exact Or.inr (Or.inl ⟨(1, false) :: (1, false) :: (1, false) :: Z, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1, false) :: Z, rfl⟩))

theorem good1_to_good2 {R : List Seg} (h : Good1 R) : Good2 R := Good2.of_good1 h

theorem good1_to_strong2 {R : List Seg} (h : Good1 R) : Strong2 R := by
  refine ⟨Good2.of_good1 h, fun W hEq => ?_⟩
  rcases h with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z,
      rfl⟩ <;> cases hEq

theorem good1Safe_to_good2 {R : List Seg} (h : Good1Safe R) : Good2 R := Good2.of_good1 h.1

theorem good1Safe_to_strong2 {R : List Seg} (h : Good1Safe R) : Strong2 R := good1_to_strong2 h.1

theorem good2_of_2_0s (Z : List Seg) : Good2 ((2, false) :: (0, true) :: Z) := Good2.c_2_0s Z

theorem good2_of_2_1_1 (Z : List Seg) : Good2 ((2, false) :: (1, false) :: (1, false) :: Z) :=
    Good2.c_2_1_1 Z

theorem strong2_of_2_1_1 (Z : List Seg) : Strong2 ((2, false) :: (1, false) :: (1, false) :: Z) :=
  ⟨Good2.c_2_1_1 Z, fun _ hEq => by cases hEq⟩

theorem good2_of_2_1_0s (Z : List Seg) : Good2 ((2, false) :: (1, false) :: (0, true) :: Z) :=
    Good2.c_2_1_0s Z

theorem good2_to_goodF2U {G : List Seg} (hG : Good2 G) : GoodF2U G := by
  cases hG with
  | of_good1 h1 =>
    rcases h1 with rfl | ⟨_, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ | ⟨_,
        rfl⟩
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  | _ => exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))

theorem goodTail_to_goodF2U {Z : List Seg} (hT : GoodTail Z) : GoodF2U Z := by
  rcases hT with hG | hH | ⟨W, rfl, _⟩ | ⟨W, rfl⟩
  · exact good2_to_goodF2U hG
  · exact Or.inr (Or.inr (Or.inr hH))
  · exact Or.inl ⟨W, rfl⟩
  · exact Or.inl ⟨(1, false) :: W, rfl⟩

theorem strong2_of_2_0s {U : List Seg} (hU : GoodStrongHead U) :
    Strong2 ((2, false) :: (0, true) :: U) :=
  ⟨Good2.c_2_0s U, fun _ hEq => by cases hEq; exact hU⟩

theorem strong2_of_2_1_0s (Z : List Seg) : Strong2 ((2, false) :: (1, false) :: (0, true) :: Z) :=
  ⟨Good2.c_2_1_0s Z, fun _ hEq => by cases hEq⟩

theorem strong2_of_step_21 {G : List Seg} (hG : Good2 G) :
    Strong2 ((2, false) :: (1, false) :: G) :=
  ⟨Good2.step_21 hG, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_1s_0 : Strong2 [(2, false), (1, true), (0, false)] :=
  ⟨Good2.c_2_1s_0, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_1s_0s (Z : List Seg) : Strong2 ((2, false) :: (1, true) :: (0, true) :: Z) :=
  ⟨Good2.c_2_1s_0s Z, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_1s_1 : Strong2 [(2, false), (1, true), (1, false)] :=
  ⟨Good2.c_2_1s_1, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_1s_1_0 : Strong2 [(2, false), (1, true), (1, false), (0, false)] :=
  ⟨Good2.c_2_1s_1_0, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_1s_1_0s (Z : List Seg) :
    Strong2 ((2, false) :: (1, true) :: (1, false) :: (0, true) :: Z) :=
  ⟨Good2.c_2_1s_1_0s Z, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_1s_1_1 (Z : List Seg) :
    Strong2 ((2, false) :: (1, true) :: (1, false) :: (1, false) :: Z) :=
  ⟨Good2.c_2_1s_1_1 Z, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_2_1_0s_1_1 (Z : List Seg) :
    Strong2 ((2, false) :: (2, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
        false) :: Z) :=
  ⟨Good2.c_2_2_1_0s_1_1 Z, fun _ hEq => by cases hEq⟩

theorem strong2_of_2_2_1_1_gf {Z : List Seg} (hZ : GoodF2U Z) :
    Strong2 ((2, false) :: (2, false) :: (1, false) :: (1, false) :: Z) :=
  ⟨Good2.c_2_2_1_1_gf hZ, fun _ hEq => by cases hEq⟩

theorem good2_ne_zeroT {G : List Seg} (h : Good2 G) (Z : List Seg) : G ≠ (0, true) :: Z := by
  cases h with
  | of_good1 h1 =>
    rcases h1 with rfl | ⟨_, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ | ⟨_,
        rfl⟩ <;> simp
  | _ => simp

theorem goodTail_ones_append (k : Nat) {R : List Seg} (h : Good2 R ∨ Head0s11 R) :
    GoodTail (ones k ++ R) := by
  cases k with
  | zero =>
    rcases h with hG | hH
    · exact Or.inl hG
    · exact Or.inr (Or.inl hH)
  | succ k' =>
    cases k' with
    | zero => exact Or.inr (Or.inr (Or.inl ⟨R, rfl, h⟩))
    | succ k'' => exact Or.inr (Or.inr (Or.inr ⟨ones k'' ++ R, rfl⟩))

theorem good1Safe_of_1s_0s_0 : Good1Safe [(1, true), (0, true), (0, false)] :=
  ⟨Or.inl rfl, fun _ h => by cases h⟩
theorem good1Safe_of_1s_0s_0s (Z : List Seg) : Good1Safe ((1, true) :: (0, true) :: (0,
    true) :: Z) :=
  ⟨Or.inr (Or.inl ⟨Z, rfl⟩), fun _ h => by cases h⟩
theorem good1Safe_of_1s_0s_1_nil : Good1Safe [(1, true), (0, true), (1, false)] :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), fun _ h => by cases h⟩
theorem good1Safe_of_1s_0s_1_0s (Z : List Seg) :
    Good1Safe ((1, true) :: (0, true) :: (1, false) :: (0, true) :: Z) :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, rfl⟩)))), fun _ h => by cases h⟩
theorem good1Safe_of_1s_0s_1_1 (Z : List Seg) :
    Good1Safe ((1, true) :: (0, true) :: (1, false) :: (1, false) :: Z) :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, rfl⟩))))), fun _ h => by cases h⟩
theorem good1Safe_of_1s_1_1_0s_1_1 (Z : List Seg) :
    Good1Safe ((1, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
        false) :: Z) :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, rfl⟩)))))), fun _ h => by cases h⟩
theorem good1Safe_of_1s_1_1_1 {Z : List Seg} (hZ : GoodF2U Z) :
    Good1Safe ((1, true) :: (1, false) :: (1, false) :: (1, false) :: Z) :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, rfl, hZ⟩))))))),
      fun _ h => by cases h⟩
theorem good1Safe_of_2_1_1 {Z : List Seg} (hT : GoodTail Z) :
    Good1Safe ((2, false) :: (1, false) :: (1, false) :: Z) :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Z, rfl⟩))))))),
    fun _ h => by cases h; exact hT⟩

/-! ## Master Strong-Induction Invariant `InvAt (m : Nat)` (Sealed) -/

structure InvAt (m : Nat) : Prop where
  -- Group 1: General F(R)
  f_258 : ∀ {R Δ R_fin}, BigF m R Δ R_fin → NoNonlast0F R → (Δ = 2 ∨ Δ = 5 ∨ Δ = 8) → Head0s11 R_fin
  f_25_goodF2U : ∀ {R Δ R_fin}, BigF m R Δ R_fin → NoNonlast0F R → (Δ = 2 ∨ Δ = 5) →
    ∃ U, R_fin = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U
  f_pos_0s : ∀ {R Δ R_fin W}, BigF m R Δ R_fin → NoNonlast0F R → 0 < Δ →
    R_fin = (0, true) :: W → ∃ Z, R_fin = (0, true) :: (1, false) :: Z
  f_4_head : ∀ {R R_fin}, BigF m R 4 R_fin → NoNonlast0F R →
    R_fin = [(1, false)] ∨ (∃ W, R_fin = (1, true) :: W) ∨ (∃ W, R_fin = (2, false) :: W)
  f_11 : ∀ {R R_fin}, BigF m R 11 R_fin → NoNonlast0F R → Head0s11 R_fin ∨ Strong2 R_fin

  -- Group 2: F(3 :: Y) family
  f3_ne24 : ∀ {Y Δ R_fin}, BigF m ((3, false) :: Y) Δ R_fin → NoNonlast0F Y → Δ ≠ 2 ∧ Δ ≠ 4
  f3_36 : ∀ {Y Δ R_fin}, BigF m ((3,
      false) :: Y) Δ R_fin → NoNonlast0F Y → (Δ = 3 ∨ Δ = 6) → Head0s11 R_fin
  f3_3_non0s : ∀ {Y R_fin}, BigF m ((3, false) :: Y) 3 R_fin → NoNonlast0F Y →
    (∀ Z, Y ≠ (0, true) :: Z) → Safe0s R_fin
  f3_5_0111 : ∀ {Y R_fin}, BigF m ((3, false) :: Y) 5 R_fin → NoNonlast0F Y → Head0s111 R_fin
  f3_9 : ∀ {Y R_fin}, BigF m ((3,
      false) :: Y) 9 R_fin → NoNonlast0F Y → Head0s11 R_fin ∨ Strong2 R_fin
  f3_1_ne6 : ∀ {Y R_fin}, BigF m ((3, false) :: (1, false) :: Y) 6 R_fin → NoNonlast0F Y → False
  f3_11 : ∀ {Y Δ R_fin}, BigF m ((3, false) :: (1, false) :: (1,
      false) :: Y) Δ R_fin → NoNonlast0F Y →
    Δ = 0 ∨ Δ = 7 ∨ (Δ = 10 ∧ Good2 R_fin)
  f3_111 : ∀ {Y Δ R_fin}, BigF m ((3, false) :: (1, false) :: (1, false) :: (1,
      false) :: Y) Δ R_fin →
    NoNonlast0F Y → (Δ = 7 ∨ Δ = 10) ∧ Good2 R_fin ∧ (Δ = 10 → Strong2 R_fin)
  f3_1111 : ∀ {Y Δ R_fin}, BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
      false) :: Y) Δ R_fin →
    NoNonlast0F Y → Δ = 7 ∧ Good2 R_fin ∧ (GoodZero111Head Y → Strong2 R_fin)

  -- Group 3: F(1 :: Y) family
  f1 : ∀ {Y Δ R_fin}, BigF m ((1, false) :: Y) Δ R_fin → NoNonlast0F Y →
    Δ ≠ 3 ∧ Δ ≠ 4 ∧
    (Δ = 5 → Safe0s R_fin) ∧
    (Δ = 6 → Head0s11 R_fin) ∧
    (Δ = 7 → Head0s111 R_fin ∨ Good1Safe R_fin) ∧
    (Δ = 10 → Head0s11 R_fin ∨ Good2 R_fin) ∧
    (Δ = 13 → Head0s11 R_fin ∨ Good2 R_fin) ∧
    (Δ = 14 → Head0s11 R_fin ∨ Strong2 R_fin)
  f11 : ∀ {Y Δ R_fin}, BigF m ((1, false) :: (1, false) :: Y) Δ R_fin → NoNonlast0F Y →
    Δ % 3 ≠ 2 ∧ Δ ≠ 3 ∧ Δ ≠ 6 ∧
    (Δ = 7 → Good1Safe R_fin) ∧
    (((Δ % 3 = 0 ∧ 9 ≤ Δ) ∨ Δ = 10) → Good2 R_fin) ∧
    (Δ = 13 → GoodF2U Y → Strong2 R_fin) ∧
    (Δ = 10 → Strong2 R_fin)
  f111 : ∀ {Y Δ R_fin}, BigF m ((1, false) :: (1, false) :: (1,
      false) :: Y) Δ R_fin → NoNonlast0F Y →
    (Δ = 0 ∧ Zero111 R_fin ∧ (GoodZero111Head Y → TightZero111 R_fin)) ∨
    (Δ % 3 = 0 ∧ 9 ≤ Δ ∧ Good2 R_fin ∧ (Δ = 9 → GoodF2U Y → Strong2 R_fin) ∧
        (Δ = 12 → Strong2 R_fin))

  -- Group 4: F(2* :: Y) family
  f2s : ∀ {Y Δ R_fin}, BigF m ((2, true) :: Y) Δ R_fin → NoNonlast0F Y →
    Δ ≠ 2 ∧ Δ ≠ 5 ∧
    (Δ = 0 → Safe0s R_fin) ∧
    (Δ = 3 → Head0s11 R_fin) ∧
    (Δ = 6 → Head0s11 R_fin ∨ Good1Safe R_fin) ∧
    (Δ = 9 → Head0s11 R_fin ∨ Strong2 R_fin) ∧
    (Δ = 12 → Head0s11 R_fin ∨ Good2 R_fin)
  f2s_1 : ∀ {Y Δ R_fin}, BigF m ((2, true) :: (1, false) :: Y) Δ R_fin → NoNonlast0F Y →
    Δ = 0 ∨ Δ = 4 ∨ Δ = 10 ∨ Δ = 13
  f2s_11 : ∀ {Y Δ R_fin}, BigF m ((2, true) :: (1, false) :: (1,
      false) :: Y) Δ R_fin → NoNonlast0F Y →
    (Δ = 4 ∧ (GoodZero111Head Y → Good1Safe R_fin)) ∨
    (Δ = 10 ∧ (GoodF2U Y → Strong2 R_fin)) ∨
    Δ = 13
  f2s_111 : ∀ {Y Δ R_fin}, BigF m ((2, true) :: (1, false) :: (1, false) :: (1,
      false) :: Y) Δ R_fin →
    NoNonlast0F Y → Δ = 4 ∧ Good1Safe R_fin

  -- Group 5: Good2 closure
  good2_f : ∀ {G Δ R_fin}, Good2 G → BigF m G Δ R_fin → NoNonlast0F G →
    Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
    (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
    (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W))
  good2_f1 : ∀ {G Δ R_fin}, Good2 G → BigF m ((1, false) :: G) Δ R_fin → NoNonlast0F G →
    Δ = 0 ∨ (Δ = 9 ∧ Good2 R_fin) ∨ (Δ = 12 ∧ Strong2 R_fin) ∨ (Δ % 3 = 0 ∧ 15 ≤ Δ)
  good2_f11 : ∀ {G Δ R_fin}, Good2 G → BigF m ((1, false) :: (1,
      false) :: G) Δ R_fin → NoNonlast0F G →
    Δ = 0
  good2_f31 : ∀ {G Δ R_fin}, Good2 G → BigF m ((3, false) :: (1,
      false) :: G) Δ R_fin → NoNonlast0F G →
    (Δ = 7 ∨ (Δ = 10 ∧ Good2 R_fin)) ∧ (Strong2 G → Strong2 R_fin)
  good2_f311 : ∀ {G Δ R_fin}, Good2 G → BigF m ((3, false) :: (1, false) :: (1,
      false) :: G) Δ R_fin →
    NoNonlast0F G → Δ = 7 ∧ Strong2 R_fin
  good2_f3111 : ∀ {G Δ R_fin}, Good2 G → BigF m ((3, false) :: (1, false) :: (1, false) :: (1,
      false) :: G) Δ R_fin →
    NoNonlast0F G → Δ = 7 ∧ Good2 R_fin ∧ (Strong2 G → Strong2 R_fin)
  good1_f3121 : ∀ {G Δ R_fin}, Good1 G →
    BigF m ((3, false) :: (1, false) :: (2, false) :: (1, false) :: G) Δ R_fin →
    NoNonlast0F G → (Δ = 7 ∨ Δ = 10) ∧ Good2 R_fin

theorem InvAt.f_4_ne0s {m : Nat} (hInv : InvAt m) {R R_fin Z : List Seg}
    (h : BigF m R 4 R_fin) (hN : NoNonlast0F R) : R_fin ≠ (0, true) :: Z := by
  rcases hInv.f_4_head h hN with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

def InvLt (m : Nat) : Prop := ∀ k, k < m → InvAt k

/-! ## Helper: `F(bumpR (bumpR R1))` for `rem2` with `q = 0` -/

theorem bigF_bump2_of_d1_two {m s1 s3 d Δ3 : Nat} {b : Bool} {Y R1 R_fin : List Seg}
    (ih : InvLt m) (hs3 : s3 < m)
    (h1 : BigD1 s1 ((d, b) :: Y) 2 R1) (hNY : NoNonlast0F Y)
    (hF : BigF s3 (bumpR (bumpR R1)) Δ3 R_fin) :
    (Δ3 = 0 ∧ Safe0s R_fin) ∨ Δ3 = 4 ∨ Δ3 = 10 ∨ Δ3 = 13 := by
  have hN1 : NoNonlast0F R1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
  rcases bigD1_two_head_nnf h1 hNY with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
  · have hF' : BigF s3 [(2, true), (0, false)] Δ3 R_fin := by simpa [bumpR] using hF
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' bigF_2s_0_exists
    exact Or.inr (Or.inl rfl)
  · have hF' : BigF s3 ((2, true) :: (0, true) :: Z) Δ3 R_fin := by simpa [bumpR] using hF
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_2s_0s_exists Z)
    exact Or.inr (Or.inl rfl)
  · have hN_Z := noNonlast0F_tail (noNonlast0F_tail hN1)
    have hF' : BigF s3 ((2, true) :: (1, false) :: Z) Δ3 R_fin := by simpa [bumpR] using hF
    rcases (ih s3 hs3).f2s_1 hF' hN_Z with rfl | rfl | rfl | rfl
    · have hS :=
          ((ih s3 hs3).f2s hF' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN_Z)).2.2.1 rfl
      exact Or.inl ⟨rfl, hS⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem d1_rem2_258 {m s2 q Δ : Nat} {R1 R_fin : List Seg}
    (ih : InvLt m) (hs2 : s2 < m)
    (h2 : BigD1 s2 (ones (q + 1) ++ R1) Δ R_fin)
    (hN1 : NoNonlast0F R1)
    (hΔ : Δ = 2 ∨ Δ = 5 ∨ Δ = 8)
    (hq0 : q = 0 → ∀ s3 Δ3, s3 < s2 → BigF s3 (bumpR (bumpR R1)) Δ3 R_fin →
      (Δ3 = 0 ∧ Safe0s R_fin) ∨ Δ3 = 4 ∨ Δ3 = 10 ∨ Δ3 = 13) :
    Head0s11 R_fin := by
  cases h2 with
  | oneF hF =>
    rename_i s3 Δ3
    cases q with
    | zero =>
      have hF' : BigF s3 (bumpR (bumpR R1)) Δ3 R_fin := by simpa [ones] using hF
      rcases hq0 rfl s3 Δ3 (by omega) hF' with ⟨_, hS⟩ | h4 | h10 | h13
      · exact safe0s_to_head0s11 hS
      · omega
      · omega
      · omega
    | succ q' =>
      have hF' : BigF s3 ((3, false) :: ones q' ++ R1) Δ3 R_fin := by simpa [ones, bumpR] using hF
      rcases hΔ with h2e | h5e | h8e
      · have h0 : Δ3 = 0 := by omega
        subst h0
        exact bigF_3_zero_prefix hF'
      · exact (ih s3 (by omega)).f3_36 hF' (noNonlast0F_ones_append q' hN1) (Or.inl (by omega))
      · exact (ih s3 (by omega)).f3_36 hF' (noNonlast0F_ones_append q' hN1) (Or.inr (by omega))

theorem d1_rem0_258 {m s2 q Δ2 : Nat} {R1 R_fin : List Seg}
    (ih : InvLt m) (hs2 : s2 < m)
    (h2 : BigD1 s2 (ones q ++ R1) Δ2 R_fin)
    (hN1 : NoNonlast0F R1) (hne1 : R1 ≠ [])
    (hΔ : Δ2 + 1 = 2 ∨ Δ2 + 1 = 5 ∨ Δ2 + 1 = 8)
    (hq0 : q = 0 → ∃ Z, R1 = (0, true) :: Z) :
    Head0s11 R_fin := by
  have hge2 := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ hne1)
  cases q with
  | zero =>
    obtain ⟨Z, rfl⟩ := hq0 rfl
    simp only [ones, List.nil_append] at h2
    cases h2
    omega
  | succ q' =>
    cases h2 with
    | oneF hF =>
      rename_i s3 Δ3
      have hF' : BigF s3 (bumpR (bumpR (ones q' ++ R1))) Δ3 R_fin := by simpa [ones] using hF
      have hN' : NoNonlast0F (bumpR (bumpR (ones q' ++ R1))) :=
        noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append q' hN1))
      exact (ih s3 (by omega)).f_258 hF' hN' (by omega)

/-! ## Group 1 Step Lemmas (under `ih : InvLt m`) -/

theorem step_f_258 {m : Nat} (ih : InvLt m)
    {R : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m R Δ R_fin) (hN : NoNonlast0F R)
    (hΔ : Δ = 2 ∨ Δ = 5 ∨ Δ = 8) : Head0s11 R_fin := by
  cases h with
  | nil => omega
  | zeroF => omega
  | zeroT => omega
  | oneT => omega
  | oneF_rem1 => omega
  | twoF_rem1 => omega
  | twoT_rem1 => omega
  | ge3_rem1 => omega
  | oneF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    refine d1_rem2_258 ih (by omega) h2 hN1 hΔ (fun hq0 _ _ _ _ => ?_)
    have hΔ1 : Δ1 = 1 := by omega
    subst hΔ1
    exact False.elim (bigF_ne_one h1)
  | twoF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine d1_rem2_258 ih (by omega) h2 hN1 hΔ (fun hq0 s3 Δ3 hs3 hF => ?_)
    have hΔ1 : Δ1 = 2 := by omega
    subst hΔ1
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | twoT_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine d1_rem2_258 ih (by omega) h2 hN1 hΔ (fun hq0 s3 Δ3 hs3 hF => ?_)
    have hΔ1 : Δ1 = 2 := by omega
    subst hΔ1
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_1Y (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | ge3_rem2 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    refine d1_rem2_258 ih (by omega) h2 hN1 hΔ (fun hq0 s3 Δ3 hs3 hF => ?_)
    have hΔ1 : Δ1 = 2 := by omega
    subst hΔ1
    exact bigF_bump2_of_d1_two ih (by omega) h1 hNY hF
  | oneF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    refine d1_rem0_258 ih (by omega) h2 hN1 (bigF_out_ne_nil h1) hΔ (fun hq0 => ?_)
    omega
  | twoF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine d1_rem0_258 ih (by omega) h2 hN1 (bigF_out_ne_nil h1) hΔ (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    cases Y with
    | nil => exact bigF_oneF_zero_head h1
    | cons x xs =>
      cases x
      obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head h1
      exact ⟨(1, false) :: Z, hZ⟩
  | twoT_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine d1_rem0_258 ih (by omega) h2 hN1 (bigF_out_ne_nil h1) hΔ (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    exact bigF_oneF_zero_head h1
  | ge3_rem0 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1 Δ2
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    have hge2 := bigD1_ge2_of_ne_nil h1 (by simp)
    refine d1_rem0_258 ih (by omega) h2 hN1 (bigD1_out_ne_nil h1) hΔ (fun hq0 => ?_)
    omega

theorem bigF_3_zero_goodF2U {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Y R_fin : List Seg} (h : BigF s ((3, false) :: Y) 0 R_fin) (hN : NoNonlast0F Y) :
    ∃ U, R_fin = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
  obtain ⟨s4, hs4, Δ4, R4, h4, hc4⟩ := bigF_3_inv h
  rcases hc4 with ⟨hrem4, hge4, _, rfl⟩ | ⟨_, _, _, _, hadd4, _⟩ |
      ⟨_, _, _, _, hadd4, _⟩ | ⟨_, _, _, _, _, hadd4, _⟩
  · by_cases h4e : Δ4 = 4
    · subst h4e
      rcases (ih s4 (by omega)).f_4_head h4 hN with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
      · exact ⟨[(1, false)], by simp [ones], Or.inl ⟨[], rfl⟩⟩
      · exact ⟨(1, true) :: W, by simp [ones], Or.inr (Or.inl ⟨W, rfl⟩)⟩
      · exact ⟨(2, false) :: W, by simp [ones], Or.inr (Or.inr (Or.inl ⟨W, rfl⟩))⟩
    · have hge7 : 7 ≤ Δ4 := by omega
      have hsp : Δ4 / 3 - 1 = (Δ4 / 3 - 2) + 1 := by omega
      rw [hsp]
      exact ⟨(1, false) :: ones (Δ4 / 3 - 2) ++ R4, rfl, Or.inl ⟨ones (Δ4 / 3 - 2) ++ R4, rfl⟩⟩
  · omega
  · omega
  · omega

theorem step_f_25_goodF2U {m : Nat} (ih : InvLt m)
    {R : List Seg} {Δ : Nat} {R_fin : List Seg} (h : BigF m R Δ R_fin) (hN : NoNonlast0F R)
    (hΔ : Δ = 2 ∨ Δ = 5) :
    ∃ U, R_fin = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
  have hrem2 : ∀ {s2 q : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones (q + 1) ++ R1) Δ R_fin → NoNonlast0F R1 →
      (q = 0 → ∀ s3 Δ3, s3 < s2 → BigF s3 (bumpR (bumpR R1)) Δ3 R_fin →
        (Δ3 = 0 ∧ Safe0s R_fin) ∨ Δ3 = 4 ∨ Δ3 = 10 ∨ Δ3 = 13) →
      ∃ U, R_fin = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
    intro s2 q R1 hs2 h2 hN1 hq0
    cases h2 with
    | oneF hF =>
      rename_i s3 Δ3
      cases q with
      | zero =>
        have hF' : BigF s3 (bumpR (bumpR R1)) Δ3 R_fin := by simpa [ones] using hF
        rcases hq0 rfl s3 Δ3 (by omega) hF' with ⟨_, ⟨U, rfl, hSU⟩⟩ | h4 | h10 | h13
        · exact ⟨U, rfl, safeU_to_goodF2U hSU⟩
        · omega
        · omega
        · omega
      | succ q' =>
        have hF' : BigF s3 ((3, false) :: (ones q' ++ R1)) Δ3 R_fin := by
            simpa [ones, bumpR] using hF
        have hN_in := noNonlast0F_ones_append q' hN1
        rcases hΔ with h2e | h5e
        · have h0 : Δ3 = 0 := by omega
          subst h0
          exact bigF_3_zero_goodF2U ih (by omega) hF' hN_in
        · have h3e : Δ3 = 3 := by omega
          subst h3e
          cases hq' : ones q' ++ R1 with
          | nil =>
            rw [hq'] at hF'
            obtain ⟨U, rfl, hSU⟩ :=
                (ih s3 (by omega)).f3_3_non0s hF' trivial (fun _ hEq => by cases hEq)
            exact ⟨U, rfl, safeU_to_goodF2U hSU⟩
          | cons x xs =>
            rw [hq'] at hF' hN_in
            cases x with
            | mk dx bx =>
              by_cases h0s : dx = 0 ∧ bx = true
              · obtain ⟨rfl, rfl⟩ := h0s
                obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv hF'
                have h0e : Δ4 = 0 := by omega
                subst h0e
                exact bigF_3_zero_goodF2U ih (by omega) hF4 (noNonlast0F_tail hN_in)
              · obtain ⟨U, rfl, hSU⟩ := (ih s3 (by omega)).f3_3_non0s hF' hN_in (fun Z hEq => by
                  cases hEq; exact h0s ⟨rfl, rfl⟩)
                exact ⟨U, rfl, safeU_to_goodF2U hSU⟩
  have hrem0 : ∀ {s2 q Δ2 : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones q ++ R1) Δ2 R_fin → NoNonlast0F R1 → R1 ≠ [] →
      Δ2 + 1 = Δ →
      (q = 0 → ∃ Z, R1 = (0, true) :: Z) →
      ∃ U, R_fin = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
    intro s2 q Δ2 R1 hs2 h2 hN1 hne1 hEqΔ hq0
    have hge2 := bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ hne1)
    cases q with
    | zero =>
      obtain ⟨Z, rfl⟩ := hq0 rfl
      simp only [ones, List.nil_append] at h2
      cases h2; omega
    | succ q' =>
      cases h2 with
      | oneF hF =>
        rename_i s3 Δ3
        have hF' : BigF s3 (bumpR (bumpR (ones q' ++ R1))) Δ3 R_fin := by simpa [ones] using hF
        have hN' : NoNonlast0F (bumpR (bumpR (ones q' ++ R1))) :=
          noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append q' hN1))
        exact (ih s3 (by omega)).f_25_goodF2U hF' hN' (Or.inl (by omega))
  cases h with
  | nil => omega
  | zeroF => omega
  | zeroT => omega
  | oneT => omega
  | oneF_rem1 => omega
  | twoF_rem1 => omega
  | twoT_rem1 => omega
  | ge3_rem1 => omega
  | oneF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    refine hrem2 (by omega) h2 hN1 (fun hq0 _ _ _ _ => ?_)
    have : Δ1 = 1 := by omega
    subst this; exact False.elim (bigF_ne_one h1)
  | twoF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | twoT_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_1Y (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | ge3_rem2 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    exact bigF_bump2_of_d1_two ih (by omega) h1 hNY hF
  | oneF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    exact hrem0 (by omega) h2 hN1 (bigF_out_ne_nil h1) rfl (fun hq0 => by omega)
  | twoF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine hrem0 (by omega) h2 hN1 (bigF_out_ne_nil h1) rfl (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    cases Y with
    | nil => exact bigF_oneF_zero_head h1
    | cons x xs =>
      cases x
      obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head h1
      exact ⟨(1, false) :: Z, hZ⟩
  | twoT_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine hrem0 (by omega) h2 hN1 (bigF_out_ne_nil h1) rfl (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    exact bigF_oneF_zero_head h1
  | ge3_rem0 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1 Δ2
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    have hge2 := bigD1_ge2_of_ne_nil h1 (by simp)
    exact hrem0 (by omega) h2 hN1 (bigD1_out_ne_nil h1) rfl (fun hq0 => by omega)

theorem head0s11_to_head0s1 {R : List Seg} (h : Head0s11 R) :
    ∃ Z, R = (0, true) :: (1, false) :: Z := by
  obtain ⟨Z, rfl⟩ := h; exact ⟨(1, false) :: Z, rfl⟩

theorem step_f_pos_0s {m : Nat} (ih : InvLt m)
    {R : List Seg} {Δ : Nat} {R_fin W : List Seg}
    (h : BigF m R Δ R_fin) (hN : NoNonlast0F R) (hpos : 0 < Δ)
    (h0s : R_fin = (0, true) :: W) : ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
  have hrem2 : ∀ {s2 q : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones (q + 1) ++ R1) Δ R_fin → NoNonlast0F R1 →
      (q = 0 → ∀ s3 Δ3, s3 < s2 → BigF s3 (bumpR (bumpR R1)) Δ3 R_fin →
        (Δ3 = 0 ∧ Safe0s R_fin) ∨ Δ3 = 4 ∨ Δ3 = 10 ∨ Δ3 = 13) →
      ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
    intro s2 q R1 hs2 h2 hN1 hq0
    cases h2 with
    | oneF hF =>
      rename_i s3 Δ3
      cases q with
      | zero =>
        have hF' : BigF s3 (bumpR (bumpR R1)) Δ3 R_fin := by simpa [ones] using hF
        rcases hq0 rfl s3 Δ3 (by omega) hF' with ⟨_, hS⟩ | rfl | rfl | rfl
        · exact head0s11_to_head0s1 (safe0s_to_head0s11 hS)
        · exact (ih s3 (by omega)).f_pos_0s hF' (noNonlast0F_bumpR (noNonlast0F_bumpR hN1))
              (by omega) h0s
        · exact (ih s3 (by omega)).f_pos_0s hF' (noNonlast0F_bumpR (noNonlast0F_bumpR hN1))
              (by omega) h0s
        · exact (ih s3 (by omega)).f_pos_0s hF' (noNonlast0F_bumpR (noNonlast0F_bumpR hN1))
              (by omega) h0s
      | succ q' =>
        have hF' : BigF s3 ((3, false) :: (ones q' ++ R1)) Δ3 R_fin := by
            simpa [ones, bumpR] using hF
        by_cases h0 : Δ3 = 0
        · subst h0; exact head0s11_to_head0s1 (bigF_3_zero_prefix hF')
        · exact (ih s3 (by omega)).f_pos_0s hF'
            (noNonlast0F_cons_ne0F (x := (3, false)) (by simp) (noNonlast0F_ones_append q' hN1))
            (by omega) h0s
  have hrem0 : ∀ {s2 q Δ2 : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones q ++ R1) Δ2 R_fin → NoNonlast0F R1 →
      (q = 0 → ∃ U, R1 = (0, true) :: U) →
      (q = 1 → ∀ s3, s3 < s2 → BigF s3 (bumpR (bumpR R1)) 0 R_fin → ∃ Z, R_fin = (0, true) :: (1,
          false) :: Z) →
      ∃ Z, R_fin = (0, true) :: (1, false) :: Z := by
    intro s2 q Δ2 R1 hs2 h2 hN1 hq0 hq1
    cases q with
    | zero =>
      obtain ⟨U, rfl⟩ := hq0 rfl
      simp only [ones, List.nil_append] at h2
      cases h2 with
      | zeroT => exact False.elim (bumpR_head_ne_zeroT U W h0s)
    | succ q' =>
      cases h2 with
      | oneF hF =>
        rename_i s3 Δ3
        have hF' : BigF s3 (bumpR (bumpR (ones q' ++ R1))) Δ3 R_fin := by simpa [ones] using hF
        have hN' : NoNonlast0F (bumpR (bumpR (ones q' ++ R1))) :=
          noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append q' hN1))
        by_cases h0 : Δ3 = 0
        · subst h0
          cases q' with
          | zero =>
            have hF'' : BigF s3 (bumpR (bumpR R1)) 0 R_fin := by simpa [ones] using hF'
            exact hq1 rfl s3 (by omega) hF''
          | succ q'' =>
            have hF'' : BigF s3 ((3, false) :: ones q'' ++ R1) 0 R_fin := by
                simpa [ones, bumpR] using hF'
            exact head0s11_to_head0s1 (bigF_3_zero_prefix hF'')
        · exact (ih s3 (by omega)).f_pos_0s hF' hN' (by omega) h0s
  cases h with
  | nil => omega
  | zeroF => omega
  | zeroT => omega
  | oneT => omega
  | oneF_rem1 => omega
  | twoF_rem1 => omega
  | twoT_rem1 => omega
  | ge3_rem1 => omega
  | oneF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    refine hrem2 (by omega) h2 hN1 (fun hq0 _ _ _ _ => ?_)
    have : Δ1 = 1 := by omega
    subst this; exact False.elim (bigF_ne_one h1)
  | twoF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | twoT_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_1Y (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | ge3_rem2 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    exact bigF_bump2_of_d1_two ih (by omega) h1 hNY hF
  | oneF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    refine hrem0 (by omega) h2 hN1 (fun hq0 => by omega) (fun hq1 s3 hs3 hF => ?_)
    have h2e : Δ1 = 2 := by omega
    subst h2e
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hNY (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) 0 R_fin := by
        simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
  | twoF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine hrem0 (by omega) h2 hN1 (fun hq0 => ?_) (fun hq1 s3 hs3 hF => ?_)
    · have h0 : Δ1 = 0 := by omega
      subst h0
      cases Y with
      | nil => exact bigF_oneF_zero_head h1
      | cons x xs =>
        cases x
        obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head h1
        exact ⟨(1, false) :: Z, hZ⟩
    · have h3e : Δ1 = 3 := by omega
      subst h3e
      obtain ⟨Z, rfl⟩ := bigF_three_head h1
      have hF' : BigF s3 ((2, true) :: (1, false) :: Z) 0 R_fin := by simpa [bumpR] using hF
      exact head0s11_to_head0s1
          (safe0s_to_head0s11 (((ih s3 (by omega)).f2s hF' (noNonlast0F_tail hN1)).2.2.1 rfl))
  | twoT_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1 Δ2
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine hrem0 (by omega) h2 hN1 (fun hq0 => ?_) (fun hq1 s3 hs3 hF => ?_)
    · have h0 : Δ1 = 0 := by omega
      subst h0
      exact bigF_oneF_zero_head h1
    · have h3e : Δ1 = 3 := by omega
      subst h3e
      exact False.elim (((ih s1 (by omega)).f1 h1 (noNonlast0F_tail hN)).1 rfl)
  | ge3_rem0 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1 Δ2
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    have hge2 := bigD1_ge2_of_ne_nil h1 (by simp)
    refine hrem0 (by omega) h2 hN1 (fun hq0 => by omega) (fun hq1 s3 hs3 hF => ?_)
    have h3e : Δ1 = 3 := by omega
    subst h3e
    cases h1 with
    | zeroF h0f =>
      rcases bigF_zero_head_3 h0f hNY with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
      · have hF' : BigF s3 [(2, false)] 0 R_fin := by simpa [bumpR] using hF
        obtain ⟨_, hEx⟩ := bigF_2_nil_exists
        obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
        omega
      · have hF' : BigF s3 ((2, true) :: Z) 0 R_fin := by simpa [bumpR] using hF
        exact head0s11_to_head0s1
            (safe0s_to_head0s11 (((ih s3 (by omega)).f2s hF' (noNonlast0F_tail hN1)).2.2.1 rfl))
      · have hF' : BigF s3 ((3, false) :: Z) 0 R_fin := by simpa [bumpR] using hF
        exact head0s11_to_head0s1 (bigF_3_zero_prefix hF')
    | zeroT =>
      cases Y with
      | nil =>
        have hF' : BigF s3 [(2, false)] 0 R_fin := by simpa [bumpR] using hF
        obtain ⟨_, hEx⟩ := bigF_2_nil_exists
        obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
        omega
      | cons x xs =>
        cases x with
        | mk d' b' =>
          have hF' : BigF s3 ((d' + 3, b') :: xs) 0 R_fin := by simpa [bumpR] using hF
          rcases bigF_ge3_zero_prefix hF' with ⟨Z, rfl⟩ | ⟨Z, rfl⟩
          · exact ⟨(1, false) :: Z, rfl⟩
          · exact ⟨(0, true) :: Z, rfl⟩
    | oneF h0f => exact False.elim (bigF_ne_one h0f)
    | oneT h0f => exact False.elim (bigF_ne_one h0f)
    | ge2 h0d =>
      have hge := bigD1_ge2_of_ne_nil h0d (by simp)
      omega

theorem step_f_4_head {m : Nat} (ih : InvLt m)
    {R R_fin : List Seg} (h : BigF m R 4 R_fin) (hN : NoNonlast0F R) :
    R_fin = [(1, false)] ∨ (∃ W, R_fin = (1, true) :: W) ∨ (∃ W, R_fin = (2, false) :: W) := by
  have hrem2_imp : ∀ {s2 q : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones (q + 1) ++ R1) 4 R_fin → NoNonlast0F R1 →
      (q = 0 → ∀ s3 Δ3, s3 < s2 → BigF s3 (bumpR (bumpR R1)) Δ3 R_fin →
        (Δ3 = 0 ∧ Safe0s R_fin) ∨ Δ3 = 4 ∨ Δ3 = 10 ∨ Δ3 = 13) →
      False := by
    intro s2 q R1 hs2 h2 hN1 hq0
    cases h2 with
    | oneF hF =>
      rename_i s3
      cases q with
      | zero =>
        have hF' : BigF s3 (bumpR (bumpR R1)) 2 R_fin := by simpa [ones] using hF
        rcases hq0 rfl s3 2 (by omega) hF' with ⟨h0, _⟩ | h4 | h10 | h13 <;> omega
      | succ q' =>
        have hF' : BigF s3 ((3, false) :: ones q' ++ R1) 2 R_fin := by simpa [ones, bumpR] using hF
        exact ((ih s3 (by omega)).f3_ne24 hF' (noNonlast0F_ones_append q' hN1)).1 rfl
  have hrem0_ok : ∀ {s2 q : Nat} {R1 : List Seg},
      BigD1 s2 (ones q ++ R1) 3 R_fin →
      (q = 0 → R1 = [(0, true), (0, false)] ∨ (∃ W, R1 = (0, true) :: (0, true) :: W) ∨
        (∃ W, R1 = (0, true) :: (1, false) :: W)) →
      R_fin = [(1, false)] ∨ (∃ W, R_fin = (1, true) :: W) ∨ (∃ W, R_fin = (2, false) :: W) := by
    intro s2 q R1 h2 hq0
    cases q with
    | zero =>
      simp only [ones, List.nil_append] at h2
      rcases hq0 rfl with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
      · cases h2; exact Or.inl rfl
      · cases h2; exact Or.inr (Or.inl ⟨W, rfl⟩)
      · cases h2; exact Or.inr (Or.inr ⟨W, rfl⟩)
    | succ q' =>
      cases h2 with
      | oneF hF => exact False.elim (bigF_ne_one hF)
  cases h with
  | oneF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    exact False.elim (hrem2_imp (by omega) h2 hN1 (fun hq0 _ _ _ _ => by
      have : Δ1 = 1 := by omega
      subst this; exact False.elim (bigF_ne_one h1)))
  | twoF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    exact False.elim (hrem2_imp (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => by
      have : Δ1 = 2 := by omega
      subst this
      obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [bumpR] using hF
      rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr (Or.inl h10))
      · exact Or.inr (Or.inr (Or.inr h13))))
  | twoT_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    exact False.elim (hrem2_imp (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => by
      have : Δ1 = 2 := by omega
      subst this
      obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_1Y (Or.inl rfl)
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [bumpR] using hF
      rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr (Or.inl h10))
      · exact Or.inr (Or.inr (Or.inr h13))))
  | ge3_rem2 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    exact False.elim (hrem2_imp (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => by
      have : Δ1 = 2 := by omega
      subst this
      exact bigF_bump2_of_d1_two ih (by omega) h1 hNY hF))
  | oneF_rem0 h1 hrem h2 =>
    exact hrem0_ok h2 (fun hq0 => by omega)
  | twoF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    refine hrem0_ok h2 (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    cases Y with
    | nil =>
      cases h1 with
      | oneF_rem1 h0f _ => cases h0f; exact Or.inl rfl
      | oneF_rem2 h0f _ h02 =>
        have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))
        omega
    | cons x xs =>
      cases x
      obtain ⟨W, hW⟩ := bigF_ge2_zero_head h1
      exact Or.inr (Or.inr ⟨W, hW⟩)
  | twoT_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    refine hrem0_ok h2 (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    cases h1 with
    | oneF_rem1 h0f hrem0 =>
      rename_i s0 R0 Δ0
      by_cases h0z : Δ0 = 0
      · subst h0z
        rcases bigF_zero_head_3 h0f hNY with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨W, rfl⟩)
        · exact Or.inr (Or.inr ⟨W, rfl⟩)
      · have hq0' : 1 ≤ (1 + Δ0) / 3 := by omega
        obtain ⟨W, hW⟩ := ones_pos_cons hq0' R0
        exact Or.inr (Or.inr ⟨W, congrArg ((0, true) :: ·) hW⟩)
    | oneF_rem2 h0f _ h02 =>
      have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))
      omega
  | ge3_rem0 h1 hrem h2 =>
    have hge2 := bigD1_ge2_of_ne_nil h1 (by simp)
    exact hrem0_ok h2 (fun hq0 => by omega)

theorem step_f_11 {m : Nat} (ih : InvLt m)
    {R R_fin : List Seg} (h : BigF m R 11 R_fin) (hN : NoNonlast0F R) :
    Head0s11 R_fin ∨ Strong2 R_fin := by
  have hrem2 : ∀ {s2 q : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones (q + 1) ++ R1) 11 R_fin → NoNonlast0F R1 →
      (q = 0 → ∀ s3 Δ3, s3 < s2 → BigF s3 (bumpR (bumpR R1)) Δ3 R_fin →
        (Δ3 = 0 ∧ Safe0s R_fin) ∨ Δ3 = 4 ∨ Δ3 = 10 ∨ Δ3 = 13) →
      Head0s11 R_fin ∨ Strong2 R_fin := by
    intro s2 q R1 hs2 h2 hN1 hq0
    cases h2 with
    | oneF hF =>
      rename_i s3
      cases q with
      | zero =>
        have hF' : BigF s3 (bumpR (bumpR R1)) 9 R_fin := by simpa [ones] using hF
        rcases hq0 rfl s3 9 (by omega) hF' with ⟨h0, _⟩ | h4 | h10 | h13 <;> omega
      | succ q' =>
        have hF' : BigF s3 ((3, false) :: ones q' ++ R1) 9 R_fin := by simpa [ones, bumpR] using hF
        exact (ih s3 (by omega)).f3_9 hF' (noNonlast0F_ones_append q' hN1)
  have hrem0 : ∀ {s2 q : Nat} {R1 : List Seg}, s2 < m →
      BigD1 s2 (ones q ++ R1) 10 R_fin → NoNonlast0F R1 →
      (q = 0 → ∃ W, R1 = (0, true) :: W) →
      Head0s11 R_fin ∨ Strong2 R_fin := by
    intro s2 q R1 hs2 h2 hN1 hq0
    cases q with
    | zero =>
      obtain ⟨W, rfl⟩ := hq0 rfl
      simp only [ones, List.nil_append] at h2
      cases h2
    | succ q' =>
      cases h2 with
      | oneF hF =>
        rename_i s3
        have hF' : BigF s3 (bumpR (bumpR (ones q' ++ R1))) 8 R_fin := by simpa [ones] using hF
        have hN' : NoNonlast0F (bumpR (bumpR (ones q' ++ R1))) :=
          noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append q' hN1))
        exact Or.inl ((ih s3 (by omega)).f_258 hF' hN' (Or.inr (Or.inr rfl)))
  cases h with
  | oneF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hNY
    refine hrem2 (by omega) h2 hN1 (fun hq0 _ _ _ _ => ?_)
    have : Δ1 = 1 := by omega
    subst this; exact False.elim (bigF_ne_one h1)
  | twoF_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | twoT_rem2 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_1Y (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF' : BigF s3 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF
    rcases (ih s3 (by omega)).f2s_11 hF' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h10))
    · exact Or.inr (Or.inr (Or.inr h13))
  | ge3_rem2 h1 hrem h2 =>
    rename_i s1 s2 d b Y R1 Δ1
    have hNY := noNonlast0F_tail hN
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hNY
    refine hrem2 (by omega) h2 hN1 (fun hq0 s3 Δ3 hs3 hF => ?_)
    have : Δ1 = 2 := by omega
    subst this
    exact bigF_bump2_of_d1_two ih (by omega) h1 hNY hF
  | oneF_rem0 h1 hrem h2 =>
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_tail hN)
    exact hrem0 (by omega) h2 hN1 (fun hq0 => by omega)
  | twoF_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    refine hrem0 (by omega) h2 hN1 (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    cases Y with
    | nil => exact bigF_oneF_zero_head h1
    | cons x xs =>
      cases x
      obtain ⟨W, hW⟩ := bigF_ge2_zero_head h1
      exact ⟨(1, false) :: W, hW⟩
  | twoT_rem0 h1 hrem h2 =>
    rename_i s1 s2 Y R1 Δ1
    have hN_1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_tail hN)
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_1Y
    refine hrem0 (by omega) h2 hN1 (fun hq0 => ?_)
    have h0 : Δ1 = 0 := by omega
    subst h0
    exact bigF_oneF_zero_head h1
  | ge3_rem0 h1 hrem h2 =>
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 (noNonlast0F_tail hN)
    have hge2 := bigD1_ge2_of_ne_nil h1 (by simp)
    exact hrem0 (by omega) h2 hN1 (fun hq0 => by omega)

/-! ## Group 2 Step Lemmas (F(3 :: Y) family, under `ih : InvLt m`) -/

theorem step_f3_ne24 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((3, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    Δ ≠ 2 ∧ Δ ≠ 4 := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, _, rfl, _⟩ | ⟨hrem, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ | ⟨hrem, hge3, s2, hs2, Δ3, rfl, hF2⟩
  · omega
  · have hne := (ih s2 hs2).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)
    constructor
    · intro h2e
      have h0 : Δ3 = 0 := by omega
      subst h0
      by_cases hΔ0_2 : Δ0 = 2
      · subst hΔ0_2
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inl rfl)
        have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 0 R_fin := by
          simpa [ones] using hF2
        obtain ⟨_, _, _, hadd, _⟩ := bigF_3_0s_inv hF2'
        omega
      · by_cases hΔ0_5 : Δ0 = 5
        · subst hΔ0_5
          obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inl rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
              false) :: U) 0 R_fin := by
            simpa [ones] using hF2
          obtain ⟨_, _, _, hadd, _⟩ := bigF_3_1_0s_inv hF2'
          omega
        · by_cases hΔ0_8 : Δ0 = 8
          · subst hΔ0_8
            obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inr rfl))
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                false) :: (1, false) :: U) 0 R_fin := by
              simpa [ones] using hF2
            obtain ⟨h7, _⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            omega
          · have hq3 : Δ0 / 3 = (Δ0 / 3 - 3) + 3 := by omega
            rw [hq3] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                (ones (Δ0 / 3 - 3) ++ R1)) 0 R_fin := by simpa [ones] using hF2
            have ⟨h710, _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
            omega
    · omega
  · constructor
    · omega
    · intro h4
      have h1e : Δ3 = 1 := by omega
      subst h1e
      exact bigF_ne_one hF2
  · constructor
    · omega
    · intro h4
      have h1e : Δ3 = 1 := by omega
      subst h1e
      exact bigF_ne_one hF2

theorem step_f3_36 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((3, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y)
    (hΔ : Δ = 3 ∨ Δ = 6) : Head0s11 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, _, rfl, _⟩ | ⟨_, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, _, s2, hs2, Δ3, rfl, hF2⟩
  · omega
  · rcases hΔ with h3 | h6
    · have h1e : Δ3 = 1 := by omega
      subst h1e; exact False.elim (bigF_ne_one hF2)
    · exact False.elim (((ih s2 hs2).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).2 (by omega))
  · rcases hΔ with h3 | h6
    · have h0e : Δ3 = 0 := by omega
      subst h0e
      rcases bigF_zero_head_3 h1 hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
      · have hF' : BigF s2 [(2, false)] 0 R_fin := by simpa [bumpR] using hF2
        obtain ⟨_, hEx⟩ := bigF_2_nil_exists
        obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
        omega
      · have hF' : BigF s2 ((2, true) :: Z) 0 R_fin := by simpa [bumpR] using hF2
        exact safe0s_to_head0s11 (((ih s2 hs2).f2s hF' (noNonlast0F_tail hN1)).2.2.1 rfl)
      · have hF' : BigF s2 ((3, false) :: Z) 0 R_fin := by simpa [bumpR] using hF2
        exact bigF_3_zero_prefix hF'
    · have h3e : Δ3 = 3 := by omega
      subst h3e
      rcases bigF_zero_head_3 h1 hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
      · have hF' : BigF s2 [(2, false)] 3 R_fin := by simpa [bumpR] using hF2
        obtain ⟨_, hEx⟩ := bigF_2_nil_exists
        obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
        omega
      · have hF' : BigF s2 ((2, true) :: Z) 3 R_fin := by simpa [bumpR] using hF2
        exact ((ih s2 hs2).f2s hF' (noNonlast0F_tail hN1)).2.2.2.1 rfl
      · have hF' : BigF s2 ((3, false) :: Z) 3 R_fin := by simpa [bumpR] using hF2
        exact (ih s2 hs2).f3_36 hF' (noNonlast0F_tail hN1) (Or.inl rfl)
  · rcases hΔ with h3 | h6
    · have h0e : Δ3 = 0 := by omega
      subst h0e
      exact bigF_3_zero_prefix hF2
    · have h3e : Δ3 = 3 := by omega
      subst h3e
      exact (ih s2 hs2).f3_36 hF2 (noNonlast0F_ones_append _ hN1) (Or.inl rfl)

theorem step_f3_3_non0s {m : Nat} (ih : InvLt m)
    {Y R_fin : List Seg}
    (h : BigF m ((3, false) :: Y) 3 R_fin) (hN : NoNonlast0F Y)
    (hnon0s : ∀ Z, Y ≠ (0, true) :: Z) : Safe0s R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ | ⟨_, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ | ⟨hrem, hge3, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)
  · have h0e : Δ3 = 0 := by omega
    subst h0e
    rcases bigF_zero_head_3 h1 hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
    · have hF' : BigF s2 [(2, false)] 0 R_fin := by simpa [bumpR] using hF2
      obtain ⟨_, hEx⟩ := bigF_2_nil_exists
      obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
      omega
    · have hF' : BigF s2 ((2, true) :: Z) 0 R_fin := by simpa [bumpR] using hF2
      exact ((ih s2 hs2).f2s hF' (noNonlast0F_tail hN1)).2.2.1 rfl
    · rcases bigF_zero_oneF_head h1 hN with ⟨rfl, rfl⟩ | rfl
      · have hF' : BigF s2 [(3, false)] 0 R_fin := by simpa [bumpR] using hF2
        obtain ⟨_, hEx⟩ := bigF_3_nil_exists
        obtain ⟨h6, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
        omega
      · exact False.elim (hnon0s Z rfl)
  · have h0e : Δ3 = 0 := by omega
    subst h0e
    obtain ⟨s4, hs4, Δ4, R4, h4, hc4⟩ := bigF_3_inv hF2
    rcases hc4 with ⟨hrem4, hge4, _, rfl⟩ | ⟨_, _, _, _, hadd4, _⟩ |
        ⟨_, _, _, _, hadd4, _⟩ | ⟨_, _, _, _, _, hadd4, _⟩
    · by_cases hge13 : 13 ≤ Δ4
      · have hsplit4 : Δ4 / 3 - 1 = (Δ4 / 3 - 4) + 3 := by omega
        rw [hsplit4]
        exact ⟨(1, false) :: (1, false) :: (1, false) :: ones (Δ4 / 3 - 4) ++ R4, rfl,
          Or.inl ⟨ones (Δ4 / 3 - 4) ++ R4, rfl⟩⟩
      · by_cases h10 : Δ4 = 10
        · subst h10
          have hGH : Good2 R4 ∨ Head0s11 R4 := by
            cases hq : Δ0 / 3 - 1 with
            | zero =>
              have hΔ0_3 : Δ0 = 3 := by omega
              subst hΔ0_3
              rw [hq] at h4; simp only [ones] at h4
              obtain ⟨W, rfl⟩ := bigF_three_head h1
              cases h4
            | succ k =>
              cases k with
              | zero =>
                rw [hq] at h4
                have h4' : BigF s4 ((1, false) :: R1) 10 R4 := by simpa [ones] using h4
                rcases ((ih s4 (by omega)).f1 h4' hN1).2.2.2.2.2.1 rfl with hH | hG2
                · exact Or.inr hH
                · exact Or.inl hG2
              | succ k' =>
                cases k' with
                | zero =>
                  rw [hq] at h4
                  have h4' : BigF s4 ((1, false) :: (1, false) :: R1) 10 R4 := by
                      simpa [ones] using h4
                  exact Or.inl (((ih s4 (by omega)).f11 h4' hN1).2.2.2.2.1 (Or.inr rfl))
                | succ k'' =>
                  rw [hq] at h4
                  have h4' : BigF s4 ((1, false) :: (1, false) :: (1,
                      false) :: (ones k'' ++ R1)) 10 R4 := by
                    simpa [ones] using h4
                  rcases (ih s4 (by omega)).f111 h4' (noNonlast0F_ones_append k'' hN1) with ⟨h0, _,
                      _⟩ | ⟨hm, _, _, _⟩ <;> omega
          exact ⟨(1, false) :: (1, false) :: R4, by simp [ones], Or.inr (Or.inl ⟨R4, rfl, hGH⟩)⟩
        · by_cases h7 : Δ4 = 7
          · subst h7
            have hGH : Good2 R4 ∨ Head0s11 R4 := by
              cases hq : Δ0 / 3 - 1 with
              | zero =>
                have hΔ0_3 : Δ0 = 3 := by omega
                subst hΔ0_3
                rw [hq] at h4; simp only [ones] at h4
                obtain ⟨W, rfl⟩ := bigF_three_head h1
                cases h4
              | succ k =>
                cases k with
                | zero =>
                  rw [hq] at h4
                  have h4' : BigF s4 ((1, false) :: R1) 7 R4 := by simpa [ones] using h4
                  rcases ((ih s4 (by omega)).f1 h4' hN1).2.2.2.2.1 rfl with hH | hG1
                  · exact Or.inr (head0s111_to_head0s11 hH)
                  · exact Or.inl (good1Safe_to_good2 hG1)
                | succ k' =>
                  cases k' with
                  | zero =>
                    rw [hq] at h4
                    have h4' : BigF s4 ((1, false) :: (1, false) :: R1) 7 R4 := by
                        simpa [ones] using h4
                    exact Or.inl (good1Safe_to_good2 (((ih s4 (by omega)).f11 h4' hN1).2.2.2.1 rfl))
                  | succ k'' =>
                    rw [hq] at h4
                    have h4' : BigF s4 ((1, false) :: (1, false) :: (1,
                        false) :: (ones k'' ++ R1)) 7 R4 := by
                      simpa [ones] using h4
                    rcases (ih s4 (by omega)).f111 h4' (noNonlast0F_ones_append k'' hN1) with ⟨h0,
                        _, _⟩ | ⟨hm, _, _, _⟩ <;> omega
            exact ⟨(1, false) :: R4, by simp [ones], Or.inr (Or.inr (Or.inl ⟨R4, rfl, hGH⟩))⟩
          · have h4e : Δ4 = 4 := by omega
            subst h4e
            cases hq : Δ0 / 3 - 1 with
            | zero =>
              have hΔ0_3 : Δ0 = 3 := by omega
              subst hΔ0_3
              rw [hq] at h4
              simp only [ones] at h4
              obtain ⟨W, rfl⟩ := bigF_three_head h1
              cases h4
            | succ k =>
              rw [hq] at h4
              have h4' : BigF s4 ((1, false) :: (ones k ++ R1)) 4 R4 := by simpa [ones] using h4
              exact False.elim (((ih s4 (by omega)).f1 h4' (noNonlast0F_ones_append k hN1)).2.1 rfl)
    · omega
    · omega
    · omega

theorem step_f3_5_0111 {m : Nat} (ih : InvLt m)
    {Y R_fin : List Seg}
    (h : BigF m ((3, false) :: Y) 5 R_fin) (hN : NoNonlast0F Y) :
    Head0s111 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ | ⟨hrem, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ | ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h3e : Δ3 = 3 := by omega
    subst h3e
    by_cases h2e : Δ0 = 2
    · subst h2e
      obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inl rfl)
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv hF2'
      have h0e : Δ4 = 0 := by omega
      subst h0e
      obtain ⟨s5, hs5, Δ5, R5, h5, hc5⟩ := bigF_3_inv hF4
      rcases hc5 with ⟨hrem5, hge5, _, rfl⟩ | ⟨_, _, _, _, hadd5, _⟩ |
          ⟨_, _, _, _, hadd5, _⟩ | ⟨_, _, _, _, _, hadd5, _⟩
      · have hne4 : Δ5 ≠ 4 :=
            ((ih s5 (by omega)).f1 h5 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNU)).2.1
        have hge7 : 7 ≤ Δ5 := by omega
        have hsp : Δ5 / 3 - 1 = (Δ5 / 3 - 2) + 1 := by omega
        rw [hsp]
        exact ⟨ones (Δ5 / 3 - 2) ++ R5, rfl⟩
      · omega
      · omega
      · omega
    · by_cases h5e : Δ0 = 5
      · subst h5e
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inl rfl))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) 3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        obtain ⟨h4, _⟩ := (ih s4 (by omega)).f2s_111 hF4 hNU
        omega
      · by_cases h8e : Δ0 = 8
        · subst h8e
          obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) 3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h7, _⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          omega
        · have hq3 : Δ0 / 3 = (Δ0 / 3 - 3) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ0 / 3 - 3) ++ R1)) 3 R_fin := by simpa [ones] using hF2
          obtain ⟨h710, _, _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          omega
  · have h2e : Δ3 = 2 := by omega
    subst h2e
    rcases bigF_zero_head_3 h1 hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
    · have hF' : BigF s2 [(2, false)] 2 R_fin := by simpa [bumpR] using hF2
      obtain ⟨_, hEx⟩ := bigF_2_nil_exists
      obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
      omega
    · have hF' : BigF s2 ((2, true) :: Z) 2 R_fin := by simpa [bumpR] using hF2
      exact False.elim (((ih s2 hs2).f2s hF' (noNonlast0F_tail hN1)).1 rfl)
    · have hF' : BigF s2 ((3, false) :: Z) 2 R_fin := by simpa [bumpR] using hF2
      exact False.elim (((ih s2 hs2).f3_ne24 hF' (noNonlast0F_tail hN1)).1 rfl)
  · exact False.elim (((ih s2 hs2).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).1 (by omega))

theorem step_f3_9 {m : Nat} (ih : InvLt m)
    {Y R_fin : List Seg}
    (h : BigF m ((3, false) :: Y) 9 R_fin) (hN : NoNonlast0F Y) :
    Head0s11 R_fin ∨ Strong2 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ | ⟨hrem, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ | ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h7e : Δ3 = 7 := by omega
    subst h7e
    by_cases h2e : Δ0 = 2
    · subst h2e
      obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inl rfl)
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 7 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv hF2'
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      exact False.elim (((ih s4 (by omega)).f3_ne24 hF4
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
          (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNU))).2 (by omega))
    · by_cases h5e : Δ0 = 5
      · subst h5e
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inl rfl))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) 7 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        exact Or.inr (good1Safe_to_strong2 ((ih s4 (by omega)).f2s_111 hF4 hNU).2)
      · by_cases h8e : Δ0 = 8
        · subst h8e
          obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) 7 R_fin := by
            simpa [ones] using hF2
          obtain ⟨_, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          exact Or.inr (strong2_of_2_1_1 ((1, false) :: U))
        · by_cases h11e : Δ0 = 11
          · subst h11e
            rcases (ih s1 hs1).f_11 h1 hN with ⟨U, rfl⟩ | hG2
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0,
                  true) :: (1, false) :: (1, false) :: U) 7 R_fin := by
                simpa [ones] using hF2
              -- 3,1,1,1,0*,1,1::U = (7, 2::0*::1::1::1::U)
              have hEx : BigF 8 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0,
                  true) :: (1, false) :: (1, false) :: U) 7
                  ((2, false) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U) := by
                have h0 : BigF 0 ((0, true) :: (1, false) :: (1, false) :: U) 0 ((1, false) :: (1,
                    false) :: (1, false) :: U) := BigF.zeroT _
                have h1' := BigF.oneF_rem1 h0 rfl
                have h2' := BigF.oneF_rem1 h1' rfl
                have h3' := BigF.oneF_rem1 h2' rfl
                have h4' : BigF 2 ((2, true) :: (0, true) :: (0, true) :: (1, false) :: (1,
                    false) :: (1, false) :: U) 4
                    ((2, false) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U) :=
                  bigF_2s_0s_full_exists ((0, true) :: (1, false) :: (1, false) :: (1, false) :: U)
                exact BigF.ge3_rem0 (BigD1.zeroF h3') rfl (BigD1.oneF h4')
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' hEx
              exact Or.inr (strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1,
                  false) :: U, rfl⟩)))))
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
                  false) :: R1) 7 R_fin := by
                simpa [ones] using hF2
              exact Or.inr (((ih s2 hs2).good2_f3111 hG2.1 hF2' hN1).2.2 hG2)
          · have hge14 : 14 ≤ Δ0 := by omega
            have hq4 : Δ0 / 3 = (Δ0 / 3 - 4) + 4 := by omega
            rw [hq4] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δ0 / 3 - 4) ++ R1)) 7 R_fin := by simpa [ones] using hF2
            have hGZ : GoodZero111Head (ones (Δ0 / 3 - 4) ++ R1) := by
              cases hq : Δ0 / 3 - 4 with
              | zero =>
                simp only [ones, List.nil_append]
                by_cases h0s : ∃ W, R1 = (0, true) :: W
                · obtain ⟨W, hW⟩ := h0s
                  exact Or.inr ((ih s1 hs1).f_pos_0s h1 hN (by omega) hW)
                · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
              | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
            exact Or.inr (((ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)).2.2 hGZ)
  · have h6e : Δ3 = 6 := by omega
    subst h6e
    rcases bigF_zero_head_3 h1 hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
    · have hF' : BigF s2 [(2, false)] 6 R_fin := by simpa [bumpR] using hF2
      obtain ⟨_, hEx⟩ := bigF_2_nil_exists
      obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' hEx
      omega
    · have hF' : BigF s2 ((2, true) :: Z) 6 R_fin := by simpa [bumpR] using hF2
      rcases ((ih s2 hs2).f2s hF' (noNonlast0F_tail hN1)).2.2.2.2.1 rfl with hH | hG1
      · exact Or.inl hH
      · exact Or.inr (good1Safe_to_strong2 hG1)
    · have hF' : BigF s2 ((3, false) :: Z) 6 R_fin := by simpa [bumpR] using hF2
      exact Or.inl ((ih s2 hs2).f3_36 hF' (noNonlast0F_tail hN1) (Or.inr rfl))
  · have h6e : Δ3 = 6 := by omega
    subst h6e
    exact Or.inl ((ih s2 hs2).f3_36 hF2 (noNonlast0F_ones_append _ hN1) (Or.inr rfl))

theorem step_f3_1_ne6 {m : Nat} (ih : InvLt m)
    {Y R_fin : List Seg}
    (h : BigF m ((3, false) :: (1, false) :: Y) 6 R_fin) (hN : NoNonlast0F Y) : False := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 :=
      (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  rcases hcases with ⟨_, _, h0, _⟩ | ⟨_, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ | ⟨hrem, hge3, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · exact ((ih s2 hs2).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).2 (by omega)
  · have h3e : Δ3 = 3 := by omega
    subst h3e
    cases h1 with
    | oneF_rem1 h0f hrem0 =>
      rename_i s0 R0 Δ0'
      have hN0 := (bigFD_noNonlast0F _).1 _ _ _ h0f hN
      by_cases h0z : Δ0' = 0
      · subst h0z
        rcases bigF_zero_head_3 h0f hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
        · have hF' : BigF s2 [(2, true), (0, false)] 3 R_fin := by simpa [ones, bumpR] using hF2
          obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' bigF_2s_0_exists
          omega
        · have hF' : BigF s2 ((2, true) :: (0, true) :: Z) 3 R_fin := by
              simpa [ones, bumpR] using hF2
          obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_2s_0s_exists Z)
          omega
        · have hF' : BigF s2 ((2, true) :: (1, false) :: Z) 3 R_fin := by
              simpa [ones, bumpR] using hF2
          rcases (ih s2 hs2).f2s_1 hF' (noNonlast0F_tail hN0) with h | h | h | h <;> omega
      · have hq0 : 1 ≤ (1 + Δ0') / 3 := by omega
        obtain ⟨Z, hZ⟩ := ones_pos_cons hq0 R0
        have hNZ : NoNonlast0F Z := by
          have := noNonlast0F_ones_append ((1 + Δ0') / 3) hN0
          rw [hZ] at this
          exact noNonlast0F_tail this
        have hF' : BigF s2 ((2, true) :: (1, false) :: Z) 3 R_fin := by simpa [hZ, bumpR] using hF2
        rcases (ih s2 hs2).f2s_1 hF' hNZ with h | h | h | h <;> omega
    | oneF_rem2 h0f _ h02 =>
      have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))
      omega
  · have h3e : Δ3 = 3 := by omega
    subst h3e
    have hne3 := ((ih s1 hs1).f1 h1 hN).1
    by_cases h6 : Δ0 = 6
    · subst h6
      obtain ⟨U, rfl⟩ := ((ih s1 hs1).f1 h1 hN).2.2.2.1 rfl
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
          false) :: U) 3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have h4 := ((ih s4 (by omega)).f2s_111 hF4 hNU).1
      omega
    · have hge9 : 9 ≤ Δ0 := by omega
      have hq2 : Δ0 / 3 - 1 = (Δ0 / 3 - 3) + 2 := by omega
      rw [hq2] at hF2
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (1,
          false) :: (ones (Δ0 / 3 - 3) ++ R1)) 3 R_fin := by
        simpa [ones] using hF2
      rcases (ih s2 hs2).f3_11 hF2' (noNonlast0F_ones_append _ hN1) with h0 | h7 | ⟨h10,
          _⟩ <;> omega

theorem f_bump2_of_f11_zero {m s1 s2 Δ3 : Nat} {Y R1 R_fin : List Seg}
    (ih : InvLt m) (hs1 : s1 < m) (hs2 : s2 < m)
    (h1 : BigF s1 ((1, false) :: (1, false) :: Y) 0 R1) (hN : NoNonlast0F Y)
    (hF2 : BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) :
    Δ3 = 4 := by
  cases h1 with
  | oneF_rem1 h0 hrem0 =>
    rename_i s0 R0 Δ0
    have hN0 :=
        (bigFD_noNonlast0F _).1 _ _ _ h0 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
    have hne3 := ((ih s0 (by omega)).f1 h0 hN).1
    by_cases h0z : Δ0 = 0
    · subst h0z
      obtain ⟨W, rfl⟩ := bigF_oneF_zero_head h0
      have hF2' : BigF s2 ((2, true) :: (0, true) :: W) Δ3 R_fin := by simpa [ones, bumpR] using hF2
      exact ((bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_exists W)).1
    · by_cases h6 : Δ0 = 6
      · subst h6
        obtain ⟨U, rfl⟩ := ((ih s0 (by omega)).f1 h0 hN).2.2.2.1 rfl
        have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
        exact ((bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_1_1_0s_exists ((1, false) :: (1,
            false) :: U))).1
      · have hge9 : 9 ≤ Δ0 := by omega
        have hq3 : (1 + Δ0) / 3 = ((1 + Δ0) / 3 - 3) + 3 := by omega
        rw [hq3] at hF2
        have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) ::
            (ones ((1 + Δ0) / 3 - 3) ++ R0)) Δ3 R_fin := by simpa [ones, bumpR] using hF2
        exact ((ih s2 hs2).f2s_111 hF2' (noNonlast0F_ones_append _ hN0)).1
  | oneF_rem2 h0 _ h02 =>
    have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0))
    omega

theorem step_f3_11 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((3, false) :: (1, false) :: (1, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    Δ = 0 ∨ Δ = 7 ∨ (Δ = 10 ∧ Good2 R_fin) := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN))
  have hf11 := (ih s1 hs1).f11 h1 hN
  rcases hcases with ⟨_, _, rfl, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ | ⟨hrem, hge3, s2, hs2, Δ3, rfl, hF2⟩
  · exact Or.inl rfl
  · exact False.elim (hf11.1 hrem)
  · have h4 := f_bump2_of_f11_zero ih hs1 hs2 h1 hN hF2
    exact Or.inr (Or.inl (by omega))
  · have hge9 : 9 ≤ Δ0 := by omega
    have hG2 : Good2 R1 := hf11.2.2.2.2.1 (Or.inl ⟨hrem, hge9⟩)
    by_cases h9 : Δ0 = 9
    · subst h9
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨rfl, hS⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
      exact Or.inr (Or.inr ⟨rfl, hS.1⟩)
    · by_cases h12 : Δ0 = 12
      · subst h12
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin :=
            by
          simpa [ones] using hF2
        obtain ⟨rfl, hG, _⟩ := (ih s2 hs2).good2_f3111 hG2 hF2' hN1
        exact Or.inr (Or.inr ⟨rfl, hG⟩)
      · have hge15 : 15 ≤ Δ0 := by omega
        have hq4 : Δ0 / 3 - 1 = (Δ0 / 3 - 5) + 4 := by omega
        rw [hq4] at hF2
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) ::
            (ones (Δ0 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
        obtain ⟨rfl, hG, _⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
        exact Or.inr (Or.inr ⟨rfl, hG⟩)

theorem step_f3_111 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((3, false) :: (1, false) :: (1, false) :: (1,
        false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    (Δ = 7 ∨ Δ = 10) ∧ Good2 R_fin ∧ (Δ = 10 → Strong2 R_fin) := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)))
  have hf111 := (ih s1 hs1).f111 h1 hN
  rcases hcases with ⟨hrem, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ | ⟨hrem, hge3, s2, hs2, Δ3, rfl, hF2⟩
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  · rcases hf111 with ⟨_, hZ, _⟩ | ⟨_, hge, _, _, _⟩
    · rcases hZ with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl, _⟩
      · have hF2' : BigF s2 [(2, true), (0, true), (0, true), (0, false)] Δ3 R_fin := by
          simpa [bumpR] using hF2
        obtain ⟨rfl, rfl⟩ :=
            (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_exists [(0, true), (0, false)])
        exact ⟨Or.inl rfl, good2_of_2_0s [(0, false)], by omega⟩
      · have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (0, true) :: Z) Δ3 R_fin := by
          simpa [bumpR] using hF2
        obtain ⟨rfl, rfl⟩ :=
            (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_exists ((0, true) :: (0, true) :: Z))
        exact ⟨Or.inl rfl, good2_of_2_0s ((0, true) :: Z), by omega⟩
      · have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1, false) :: Z) Δ3 R_fin := by
          simpa [bumpR] using hF2
        obtain ⟨rfl, rfl⟩ :=
            (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_exists ((0, true) :: (1, false) :: Z))
        exact ⟨Or.inl rfl, good2_of_2_0s ((1, false) :: Z), by omega⟩
      · have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1, false) :: (0, true) :: (1,
            false) :: (1, false) :: Z) Δ3 R_fin := by
          simpa [bumpR] using hF2
        obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
          (bigF_2s_0s_exists ((1, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
              false) :: Z))
        exact ⟨Or.inl rfl, good2_of_2_1_1 ((0, true) :: (1, false) :: (1, false) :: Z), by omega⟩
      · have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1, false) :: (1,
            false) :: Z) Δ3 R_fin := by
          simpa [bumpR] using hF2
        obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
          (bigF_2s_0s_exists ((1, false) :: (1, false) :: (1, false) :: Z))
        exact ⟨Or.inl rfl, good2_of_2_1_1 ((1, false) :: Z), by omega⟩
      · have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) :: Z) Δ3 R_fin :=
            by
          simpa [bumpR] using hF2
        have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
        obtain ⟨rfl, hG1⟩ := (ih s2 hs2).f2s_111 hF2' hNZ
        exact ⟨Or.inl rfl, good1Safe_to_good2 hG1, by omega⟩
    · omega
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨_, hge9, hG2, _, hS12⟩
    · omega
    · by_cases h9 : Δ0 = 9
      · subst h9
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨rfl, hS⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
        exact ⟨Or.inr rfl, hS.1, fun _ => hS⟩
      · by_cases h12 : Δ0 = 12
        · subst h12
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
              false) :: R1) Δ3 R_fin := by
            simpa [ones] using hF2
          have hS1 := hS12 rfl
          obtain ⟨rfl, hG, hS⟩ := (ih s2 hs2).good2_f3111 hG2 hF2' hN1
          exact ⟨Or.inr rfl, hG, fun _ => hS hS1⟩
        · have hge15 : 15 ≤ Δ0 := by omega
          have hq4 : Δ0 / 3 - 1 = (Δ0 / 3 - 5) + 4 := by omega
          rw [hq4] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ0 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
          have hGZ : GoodZero111Head (ones (Δ0 / 3 - 5) ++ R1) := by
            cases hq : Δ0 / 3 - 5 with
            | zero =>
              simp only [ones, List.nil_append]
              exact Or.inl (good2_ne_zeroT hG2)
            | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
          obtain ⟨rfl, hG, hS⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
          exact ⟨Or.inr rfl, hG, fun _ => hS hGZ⟩

theorem step_f3_1111 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) :: Y) Δ R_fin)
    (hN : NoNonlast0F Y) :
    Δ = 7 ∧ Good2 R_fin ∧ (GoodZero111Head Y → Strong2 R_fin) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_3_inv h
  have h1_zero : Δ1 = 0 ∧
      ((∃ Z, R1 = (0, true) :: (0, true) :: (0, true) :: Z ∧
          (GoodZero111Head Y → GoodStrongHead Z)) ∨
       (∃ Z, R1 = (0, true) :: (0, true) :: (1, false) :: (1, false) :: Z) ∨
       (∃ Z, R1 = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z)) := by
    cases h1 with
    | oneF_rem1 h0 hrem0 =>
      rename_i s0 R0 Δ0
      rcases (ih s0 (by omega)).f111 h0 hN with ⟨rfl, hZ, hTZ⟩ | ⟨hm, hge9, _, _, _⟩
      · refine ⟨rfl, ?_⟩
        rcases hZ with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl, _⟩
        · exact Or.inl ⟨[(0, true), (0, false)], rfl, fun _ =>
            Or.inr (Or.inr (Or.inl ⟨[(0, false)], rfl, Or.inr Good2.c_2_0⟩))⟩
        · exact Or.inl ⟨(0, true) :: (0, true) :: Z, rfl, fun _ =>
            Or.inr (Or.inr (Or.inl ⟨(0, true) :: Z, rfl, Or.inr (Good2.c_2_0s Z)⟩))⟩
        · refine Or.inl ⟨(0, true) :: (1, false) :: Z, rfl, fun hGZ =>
            Or.inr (Or.inr (Or.inl ⟨(1, false) :: Z, rfl, Or.inr ?_⟩))⟩
          rcases (hTZ hGZ).2 Z rfl with rfl | ⟨W', rfl⟩ | ⟨W', rfl⟩
          · exact Good2.c_2_1
          · exact Good2.c_2_1_0s W'
          · exact Good2.c_2_1_1 W'
        · exact Or.inl ⟨(1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z, rfl,
            fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (0, true) :: (1, false) :: (1,
                false) :: Z, rfl⟩)))⟩
        · exact Or.inl ⟨(1, false) :: (1, false) :: (1, false) :: Z, rfl,
            fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1, false) :: Z, rfl⟩)))⟩
        · exact Or.inr (Or.inl ⟨(1, false) :: Z, rfl⟩)
      · refine ⟨rfl, Or.inr (Or.inr ?_)⟩
        have hq3 : (1 + Δ0) / 3 = ((1 + Δ0) / 3 - 3) + 3 := by omega
        rw [hq3]
        exact ⟨ones ((1 + Δ0) / 3 - 3) ++ R0, rfl⟩
    | oneF_rem2 h0 hrem0 _ =>
      rename_i s0 _ R0 _ Δ0
      rcases (ih s0 (by omega)).f111 h0 hN with ⟨h0e, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
    | oneF_rem0 h0 hrem0 _ =>
      rename_i s0 _ R0 _ Δ0 _
      rcases (ih s0 (by omega)).f111 h0 hN with ⟨h0e, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  obtain ⟨rfl, hR1⟩ := h1_zero
  rcases hcases with ⟨hrem, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨_, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, hge3, _, _, _, _, _⟩
  · omega
  · omega
  · have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1
      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
          (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
            (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN))))
    rcases hR1 with ⟨Z, rfl, hZS⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
    · have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: Z) Δ3 R_fin := by
          simpa [bumpR] using hF2
      obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_exists ((0, true) :: Z))
      exact ⟨rfl, good2_of_2_0s Z, fun hGZ => strong2_of_2_0s (hZS hGZ)⟩
    · have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1, false) :: Z) Δ3 R_fin := by
        simpa [bumpR] using hF2
      obtain ⟨rfl, rfl⟩ :=
          (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_exists ((1, false) :: (1, false) :: Z))
      exact ⟨rfl, good2_of_2_1_1 Z, fun _ => strong2_of_2_1_1 Z⟩
    · have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) :: Z) Δ3 R_fin := by
        simpa [bumpR] using hF2
      have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      obtain ⟨rfl, hG1⟩ := (ih s2 hs2).f2s_111 hF2' hNZ
      exact ⟨rfl, good1Safe_to_good2 hG1, fun _ => good1Safe_to_strong2 hG1⟩
  · omega


/-! ## Helpers for Groups 3 & 4 -/

/-- `BigF s ((2, false) :: V) 2 R_fin` is impossible under `ih : InvLt m`. -/
theorem bigF_2_ne2 {m s : Nat} (ih : InvLt m) (hs : s < m)
    {V R_fin : List Seg} (h : BigF s ((2, false) :: V) 2 R_fin) (hN : NoNonlast0F V) : False := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
  have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR hN)
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, hadd, hD2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h0 : Δ3 = 0 := by omega
    subst h0
    obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) 0 R_fin := by
        simpa [bumpR] using hF2
    rcases (ih s2 (by omega)).f2s_11 hF2' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
  · have h0 : Δ3 = 0 := by omega
    subst h0
    by_cases h5 : Δ1 = 5
    · subst h5
      obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inr (Or.inl rfl))
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 0 R_fin := by
        simpa [ones] using hF2
      obtain ⟨_, _, _, hadd4, _⟩ := bigF_3_0s_inv hF2'
      omega
    · by_cases h8 : Δ1 = 8
      · subst h8
        obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inr (Or.inr rfl))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) 0 R_fin := by
          simpa [ones] using hF2
        obtain ⟨_, _, _, hadd4, _⟩ := bigF_3_1_0s_inv hF2'
        omega
      · by_cases h11 : Δ1 = 11
        · subst h11
          rcases (ih s1 (by omega)).f_11 h1 hN_b2 with ⟨U, rfl⟩ | hS
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                false) :: (1, false) :: U) 0 R_fin := by
              simpa [ones] using hF2
            obtain ⟨h7, _⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            omega
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 0 R_fin := by
              simpa [ones] using hF2
            have h7 := ((ih s2 (by omega)).good2_f311 hS.1 hF2' hN1).1
            omega
        · have hge14 : 14 ≤ Δ1 := by omega
          have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ1 / 3 - 4) ++ R1)) 0 R_fin := by simpa [ones] using hF2
          obtain ⟨h710, _, _⟩ := (ih s2 (by omega)).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          omega
  · have hge := bigD1_ge2_of_ne_nil hD2 (bigF_out_ne_nil h1)
    omega
  · omega
  · omega

/-- Unconditional: `F([2, 0]) = (0, [0*, 1, 1])`. -/
theorem bigF_2_0_exists :
    ∃ s, BigF s [(2, false), (0, false)] 0 [(0, true), (1, false), (1, false)] := by
  obtain ⟨s1, h1⟩ := bigF_2_nil_exists
  exact ⟨_, BigF.twoF_rem1 (Y := [(0, false)]) h1 rfl⟩

/-- Unconditional: `F([3, 1]) = (7, [2])`. -/
theorem bigF_3_1_nil_exists :
    BigF 6 [(3, false), (1, false)] 7 [(2, false)] := by
  have h1 : BigD1 2 [(0, false), (1, false)] 3 [(0, true), (0, false)] :=
    BigD1.zeroF (BigF.oneF_rem1 BigF.nil rfl)
  exact BigF.ge3_rem0 h1 rfl (BigD1.oneF bigF_2s_0_exists)

/-- Unconditional: `F(3, 1, 1, 1) = (7, [2, 0*, 0])`. -/
theorem bigF_3_1_1_1_nil_exists :
    BigF 8 [(3, false), (1, false), (1, false), (1, false)] 7
      [(2, false), (0, true), (0, false)] := by
  have h0 : BigF 0 [] 0 [(0, false)] := BigF.nil
  have h1 := BigF.oneF_rem1 h0 rfl
  have h2 := BigF.oneF_rem1 h1 rfl
  have h3 := BigF.oneF_rem1 h2 rfl
  have h4 := bigF_2s_0s_full_exists [(0, true), (0, false)]
  exact BigF.ge3_rem0 (BigD1.zeroF h3) rfl (BigD1.oneF h4)

/-- Unconditional: `F(3, 1, 1, 1, 0* :: 1 :: 1 :: U) = (7, 2 :: 0* :: 1 :: 1 :: 1 :: U)`. -/
theorem bigF_3_1_1_1_0s_1_1_exists (U : List Seg) :
    BigF 8 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
        false) :: U) 7
      ((2, false) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U) := by
  have h0 : BigF 0 ((0, true) :: (1, false) :: (1, false) :: U) 0
      ((1, false) :: (1, false) :: (1, false) :: U) := BigF.zeroT _
  have h1 := BigF.oneF_rem1 h0 rfl
  have h2 := BigF.oneF_rem1 h1 rfl
  have h3 := BigF.oneF_rem1 h2 rfl
  have h4 := bigF_2s_0s_full_exists ((0, true) :: (1, false) :: (1, false) :: (1, false) :: U)
  exact BigF.ge3_rem0 (BigD1.zeroF h3) rfl (BigD1.oneF h4)

/-- `F(3, 1, 1, 2 :: W) = (7, R_fin)` always yields `Strong2 R_fin`. -/
theorem bigF_3_1_1_2_seven_strong {m s : Nat} (ih : InvLt m) (hs : s < m)
    {W R_fin : List Seg} (h : BigF s ((3, false) :: (1, false) :: (1, false) :: (2,
        false) :: W) 7 R_fin)
    (hN : NoNonlast0F W) : Strong2 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN2W : NoNonlast0F ((2, false) :: W) := noNonlast0F_cons_ne0F (x := (2, false)) (by simp) hN
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN2W))
  have hf11 := (ih s1 (by omega)).f11 h1 hN2W
  rcases hcases with ⟨_, _, h0, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ | ⟨hrem, hge3, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · exact False.elim (hf11.1 hrem)
  · have h4e : Δ3 = 4 := by omega
    subst h4e
    cases h1 with
    | oneF_rem1 h0f hrem0f =>
      rename_i s0 R0 Δ0'
      have hN0 := (bigFD_noNonlast0F _).1 _ _ _ h0f
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN2W)
      by_cases h0z : Δ0' = 0
      · subst h0z
        cases h0f with
        | oneF_rem1 hy hremy =>
          rename_i sy Ry Δy
          by_cases hyz : Δy = 0
          · subst hyz
            cases W with
            | nil =>
              obtain ⟨_, hEx⟩ := bigF_2_nil_exists
              obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hy hEx
              omega
            | cons x xs =>
              cases x with
              | mk dx bx =>
                obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head hy
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1,
                    false) :: Z) 4 R_fin := by
                  simpa [hZ, ones, bumpR] using hF2
                obtain ⟨_, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                    false) :: Z))
                exact strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, rfl⟩))))
          · by_cases h3y : Δy = 3
            · subst h3y
              obtain ⟨Z, rfl⟩ := bigF_three_head hy
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (0, true) :: (1,
                  false) :: Z) 4 R_fin := by
                simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((1, false) :: (0,
                  true) :: (1, false) :: Z))
              exact strong2_of_2_1_0s ((1, false) :: Z)
            · have hge6 : 6 ≤ Δy := by omega
              have hq2 : (1 + Δy) / 3 = ((1 + Δy) / 3 - 2) + 2 := by omega
              rw [hq2] at hF2
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1,
                  false) :: (ones ((1 + Δy) / 3 - 2) ++ Ry)) 4 R_fin := by
                simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
                (bigF_2s_0s_full_exists ((1, false) :: (1,
                    false) :: (ones ((1 + Δy) / 3 - 2) ++ Ry)))
              exact strong2_of_2_1_1 (ones ((1 + Δy) / 3 - 2) ++ Ry)
        | oneF_rem2 hy _ hy2 =>
          have hge := bigD1_ge2_of_ne_nil hy2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hy))
          omega
      · have hne3 := ((ih s0 (by omega)).f1 h0f hN2W).1
        by_cases h6 : Δ0' = 6
        · subst h6
          obtain ⟨U, rfl⟩ := ((ih s0 (by omega)).f1 h0f hN2W).2.2.2.1 rfl
          have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) 4 R_fin := by
            simpa [ones, bumpR] using hF2
          obtain ⟨_, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          exact good1Safe_to_strong2 (good1Safe_of_1s_0s_1_1 ((1, false) :: U))
        · have hge9 : 9 ≤ Δ0' := by omega
          have hq3 : (1 + Δ0') / 3 = ((1 + Δ0') / 3 - 3) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) ::
              (ones ((1 + Δ0') / 3 - 3) ++ R0)) 4 R_fin := by simpa [ones, bumpR] using hF2
          exact good1Safe_to_strong2
              ((ih s2 (by omega)).f2s_111 hF2' (noNonlast0F_ones_append _ hN0)).2
    | oneF_rem2 h0f _ h02 =>
      have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))
      omega
  · have h4e : Δ3 = 4 := by omega
    subst h4e
    have hge9 : 9 ≤ Δ0 := by omega
    have hG2 : Good2 R1 := hf11.2.2.2.2.1 (Or.inl ⟨hrem, hge9⟩)
    by_cases h9 : Δ0 = 9
    · subst h9
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 4 R_fin := by
          simpa [ones] using hF2
      have h7 := ((ih s2 (by omega)).good2_f311 hG2 hF2' hN1).1
      omega
    · by_cases h12 : Δ0 = 12
      · subst h12
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: R1) 4 R_fin :=
            by
          simpa [ones] using hF2
        have h7 := ((ih s2 (by omega)).good2_f3111 hG2 hF2' hN1).1
        omega
      · have hge15 : 15 ≤ Δ0 := by omega
        have hq4 : Δ0 / 3 - 1 = (Δ0 / 3 - 5) + 4 := by omega
        rw [hq4] at hF2
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) ::
            (ones (Δ0 / 3 - 5) ++ R1)) 4 R_fin := by simpa [ones] using hF2
        have h7 := ((ih s2 (by omega)).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)).1
        omega

/-- `F(3, 1, 1 :: U) = (7, R_fin)` with `GoodF2U U` yields `Good2 R_fin`. -/
theorem bigF_3_1_1_goodF2U_7 {m s : Nat} (ih : InvLt m) (hs : s < m)
    {U R_fin : List Seg} (hU : GoodF2U U)
    (h : BigF s ((3, false) :: (1, false) :: (1, false) :: U) 7 R_fin) (hN : NoNonlast0F U) :
    Good2 R_fin := by
  rcases hU with ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩
  · exact ((ih s hs).f3_111 h (noNonlast0F_tail hN)).2.1
  · obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ h (bigF_3_1_1_1s_exists W)
    exact good2_of_2_0s (bumpR W)
  · exact (bigF_3_1_1_2_seven_strong ih hs h (noNonlast0F_tail hN)).1
  · obtain ⟨_, rfl⟩ :=
        (bigFD_det _).1 _ _ _ _ _ _ h (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: W))
    exact good2_of_2_1_1 ((1, false) :: W)

/-- `F(3, 2 :: W) = (12, R_fin)` yields `Head0s11 R_fin ∨ Strong2 R_fin`. -/
theorem bigF_3_2_12_strong {m s : Nat} (ih : InvLt m) (hs : s < m)
    {W R_fin : List Seg} (h : BigF s ((3, false) :: (2, false) :: W) 12 R_fin)
    (hN : NoNonlast0F W) : Head0s11 R_fin ∨ Strong2 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN2W : NoNonlast0F ((2, false) :: W) := noNonlast0F_cons_ne0F (x := (2, false)) (by simp) hN
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN2W
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨hrem2, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem0, hge3, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h10e : Δ3 = 10 := by omega
    subst h10e
    by_cases h2e : Δ0 = 2
    · subst h2e
      exact False.elim (bigF_2_ne2 ih (by omega) h1 hN)
    · by_cases h5e : Δ0 = 5
      · subst h5e
        obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN2W (Or.inr (Or.inl rfl))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) 10 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        have h4 := ((ih s4 (by omega)).f2s_111 hF4 hNU).1
        omega
      · by_cases h8e : Δ0 = 8
        · subst h8e
          obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN2W (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) 10 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h7, _⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          omega
        · by_cases h11e : Δ0 = 11
          · subst h11e
            rcases (ih s1 (by omega)).f_11 h1 hN2W with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0,
                  true) :: (1, false) :: (1, false) :: U) 10 R_fin := by
                simpa [ones] using hF2
              obtain ⟨h7, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_1_0s_1_1_exists U)
              omega
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
                  false) :: R1) 10 R_fin := by
                simpa [ones] using hF2
              have h7 := ((ih s2 (by omega)).good2_f3111 hS.1 hF2' hN1).1
              omega
          · have hge14 : 14 ≤ Δ0 := by omega
            have hq4 : Δ0 / 3 = (Δ0 / 3 - 4) + 4 := by omega
            rw [hq4] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δ0 / 3 - 4) ++ R1)) 10 R_fin := by simpa [ones] using hF2
            have h7 := ((ih s2 (by omega)).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)).1
            omega
  · have h9e : Δ3 = 9 := by omega
    subst h9e
    cases W with
    | nil =>
      obtain ⟨_, hEx⟩ := bigF_2_nil_exists
      obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h1 hEx
      omega
    | cons x xs =>
      cases x with
      | mk dx bx =>
        obtain ⟨Z, rfl⟩ := bigF_ge2_zero_head h1
        have hF2' : BigF s2 ((2, true) :: (1, false) :: Z) 9 R_fin := by simpa [bumpR] using hF2
        have hNZ := noNonlast0F_tail (noNonlast0F_tail hN1)
        rcases (ih s2 (by omega)).f2s_1 hF2' hNZ with h0 | h4 | h10 | h13 <;> omega
  · have h9e : Δ3 = 9 := by omega
    subst h9e
    by_cases h3e : Δ0 = 3
    · subst h3e
      have hF2' : BigF s2 ((3, false) :: R1) 9 R_fin := by simpa [ones] using hF2
      exact (ih s2 (by omega)).f3_9 hF2' hN1
    · by_cases h6e : Δ0 = 6
      · subst h6e
        have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) 9 R_fin := by simpa [ones] using hF2
        exact (ih s2 (by omega)).f3_9 hF2' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN1)
      · by_cases h9d : Δ0 = 9
        · subst h9d
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 9 R_fin := by
              simpa [ones] using hF2
          rcases (ih s2 (by omega)).f3_11 hF2' hN1 with h0 | h7 | ⟨h10, _⟩ <;> omega
        · have hge12 : 12 ≤ Δ0 := by omega
          have hq3 : Δ0 / 3 - 1 = (Δ0 / 3 - 4) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ0 / 3 - 4) ++ R1)) 9 R_fin := by simpa [ones] using hF2
          obtain ⟨h710, _, _⟩ := (ih s2 (by omega)).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          omega

/-- `F(2 :: Z) = (4, R0)` classification: `[1]`, `2 :: 0* :: (0 | 0*::_ | 1::_)`, or `2 :: 1 :: _`.
-/
theorem bigF_2_4_head {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Z R0 : List Seg} (h : BigF s ((2, false) :: Z) 4 R0) (hN : NoNonlast0F Z) :
    R0 = [(1, false)] ∨
    (∃ W, R0 = (2, false) :: (0, true) :: W ∧
      (W = [(0, false)] ∨ (∃ U, W = (0, true) :: U) ∨ (∃ U, W = (1, false) :: U))) ∨
    (∃ W, R0 = (2, false) :: (1, false) :: W) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
  have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR hN)
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, hadd, hD2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R0 := by
        simpa [bumpR] using hF2
    rcases (ih s2 (by omega)).f2s_11 hF2' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
  · exact False.elim (((ih s2 (by omega)).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).1 (by omega))
  · have h3e : Δ2 = 3 := by omega
    subst h3e
    cases Z with
    | nil =>
      obtain ⟨_, hEx⟩ := bigF_2_nil_exists
      obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
      exact Or.inl rfl
    | cons x xs =>
      cases x with
      | mk dx bx =>
        cases dx with
        | zero =>
          cases bx with
          | false =>
            cases xs with
            | nil =>
              obtain ⟨_, hEx⟩ := bigF_2_0_exists
              obtain ⟨h0, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
              omega
            | cons _ _ => simp [NoNonlast0F] at hN
          | true =>
            have h1' : BigF s1 ((2, true) :: xs) 0 R1 := by simpa [bumpR] using h1
            obtain ⟨U, rfl, _⟩ := ((ih s1 (by omega)).f2s h1' (noNonlast0F_tail hN)).2.2.1 rfl
            cases hD2
            exact Or.inr (Or.inr ⟨U, rfl⟩)
        | succ dx' =>
          have h1' : BigF s1 ((dx' + 3, bx) :: xs) 0 R1 := by simpa [bumpR] using h1
          cases h1' with
          | ge3_rem1 hd1 hremd1 =>
            rename_i sd1 Rd1 Δd1
            have hge2 := bigD1_ge2_of_ne_nil hd1 (by simp)
            have hge4 : 4 ≤ Δd1 := by omega
            cases hD2
            by_cases h4d : Δd1 = 4
            · subst h4d
              have hNxs := noNonlast0F_tail hN
              cases hd1 with
              | zeroF h0f => exact False.elim (bigF_ne_one h0f)
              | oneF h0f =>
                obtain ⟨U, rfl⟩ :=
                    (ih _ (by omega)).f_258 h0f (noNonlast0F_bumpR (noNonlast0F_bumpR hNxs))
                    (Or.inl rfl)
                exact Or.inr (Or.inl ⟨(1, false) :: (1, false) :: U, by simp [ones, bumpR],
                                                                      Or.inr (Or.inr ⟨(1,
                                                                      false) :: U, rfl⟩)⟩)
              | oneT h0f =>
                obtain ⟨U, rfl⟩ :=
                    (ih _ (by omega)).f_258 h0f (noNonlast0F_cons_ne0F (x := (1,
                    false)) (by simp) hNxs) (Or.inl rfl)
                exact Or.inr (Or.inl ⟨(1, false) :: (1, false) :: U, by simp [ones, bumpR],
                                                                      Or.inr (Or.inr ⟨(1,
                                                                      false) :: U, rfl⟩)⟩)
              | ge2 hd2 =>
                rcases bigD1_two_head_nnf hd2 hNxs with rfl | ⟨U, rfl⟩ | ⟨U, rfl⟩
                · exact Or.inr (Or.inl ⟨[(0, false)], by simp [ones, bumpR], Or.inl rfl⟩)
                · exact Or.inr (Or.inl ⟨(0, true) :: U, by simp [ones, bumpR], Or.inr (Or.inl ⟨U,
                                                         rfl⟩)⟩)
                · exact Or.inr (Or.inl ⟨(1, false) :: U, by simp [ones, bumpR], Or.inr (Or.inr ⟨U,
                                                          rfl⟩)⟩)
            · have hge7 : 7 ≤ Δd1 := by omega
              have hq2 : Δd1 / 3 = (Δd1 / 3 - 2) + 2 := by omega
              rw [hq2]
              exact Or.inr (Or.inr ⟨ones (Δd1 / 3 - 2) ++ Rd1, by simp [ones, bumpR]⟩)
          | ge3_rem2 hd1 _ hd2 =>
            have hge :=
                bigD1_ge2_of_ne_nil hd2 (append_nonempty_of_right _ _ (bigD1_out_ne_nil hd1))
            omega
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)

/-- `F(2, 1 :: W) = (7, Rx)` always yields `Head0s111 Rx ∨ Good1Safe Rx`. -/
theorem bigF_2_1_7_head {m s : Nat} (ih : InvLt m) (hs : s < m)
    {W Rx : List Seg} (h : BigF s ((2, false) :: (1, false) :: W) 7 Rx) (hN : NoNonlast0F W) :
    Head0s111 Rx ∨ Good1Safe Rx := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
  have h1' : BigF s1 ((3, false) :: W) Δ1 R1 := by simpa [bumpR] using h1
  have hN1 :=
      (bigFD_noNonlast0F _).1 _ _ _ h1' (noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN)
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, hadd, hD2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · exact False.elim (((ih s1 (by omega)).f3_ne24 h1' hN).1 rfl)
  · have h5e : Δ3 = 5 := by omega
    subst h5e
    exact Or.inl ((ih s2 (by omega)).f3_5_0111 hF2 (noNonlast0F_ones_append _ hN1))
  · obtain ⟨U, rfl⟩ := bigF_3_zero_prefix h1'
    cases hD2; omega
  · have h4e : Δ3 = 4 := by omega
    subst h4e
    have hGF : ∃ U, R1 = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
      cases W with
      | nil =>
        obtain ⟨U, rfl, hSU⟩ :=
            (ih s1 (by omega)).f3_3_non0s h1' trivial (fun _ hEq => by cases hEq)
        exact ⟨U, rfl, safeU_to_goodF2U hSU⟩
      | cons x xs =>
        cases x with
        | mk dx bx =>
          by_cases h0s : dx = 0 ∧ bx = true
          · obtain ⟨rfl, rfl⟩ := h0s
            obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv h1'
            have h0e : Δ4 = 0 := by omega
            subst h0e
            exact bigF_3_zero_goodF2U ih (by omega) hF4 (noNonlast0F_tail hN)
          · obtain ⟨U, rfl, hSU⟩ := (ih s1 (by omega)).f3_3_non0s h1' hN (fun Z hEq => by
              cases hEq; exact h0s ⟨rfl, rfl⟩)
            exact ⟨U, rfl, safeU_to_goodF2U hSU⟩
    obtain ⟨U, rfl, hGFU⟩ := hGF
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) 4 Rx := by
        simpa [bumpR] using hF2
    rcases (ih s2 (by omega)).f2s_11 hF2' hNU with ⟨_, hG1⟩ | ⟨h10, _⟩ | h13
    · exact Or.inr (hG1 (goodF2U_to_goodZero111Head hGFU))
    · omega
    · omega
  · exact False.elim (((ih s2 (by omega)).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).2 (by omega))

/-- `F(3, 1 :: R1) = (12, R_fin)` when `R1` has valid `BigF` output head yields `Head0s11 R_fin ∨
    Strong2 R_fin`. -/
theorem bigF_3_1_12_of_validHead {m s : Nat} (ih : InvLt m) (hs : s < m)
    {R1 R_fin : List Seg} (h : BigF s ((3, false) :: (1, false) :: R1) 12 R_fin)
    (hN1 : NoNonlast0F R1)
    (hHead : R1 = [(0, false)] ∨ (∃ Z, R1 = (0, true) :: Z) ∨ (∃ Z, R1 = (1, false) :: Z) ∨
      (∃ Z, R1 = (1, true) :: Z) ∨ (∃ Z, R1 = (2, false) :: Z)) :
    Head0s11 R_fin ∨ Strong2 R_fin := by
  obtain ⟨s1, hs1, Δ0, R0, h1, hcases⟩ := bigF_3_inv h
  have hN11 := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN1
  have hN0 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN11
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨hrem2, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem0, hge3, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h10e : Δ3 = 10 := by omega
    subst h10e
    by_cases h2e : Δ0 = 2
    · subst h2e
      obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN11 (Or.inl rfl)
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN0))
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 10 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv hF2'
      have h7e : Δ4 = 7 := by omega
      subst h7e
      -- Inspect h1 : BigF s1 (1 :: R1) 2 (0* :: 1 :: 1 :: U)
      obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_1_inv h1
      have hNa := (bigFD_noNonlast0F _).1 _ _ _ ha hN1
      rcases hca with ⟨_, h0, _⟩ |
          ⟨hrema, hgea, sb, hsb, Δb, haddb, hFb⟩ |
          ⟨rfl, _, _, _, haddb, _⟩ |
          ⟨_, _, _, _, _, haddb, _⟩
      · omega
      · have h0b : Δb = 0 := by omega
        subst h0b
        have hNX := noNonlast0F_ones_append (Δa / 3 - 1) hNa
        obtain ⟨sc, hsc, Δc, Rc, hc, hcc⟩ := bigF_3_inv hFb
        have hNc := (bigFD_noNonlast0F _).1 _ _ _ hc hNX
        rcases hcc with ⟨hremc, hgec, _, hEqU⟩ | ⟨_, _, _, _, haddc, _⟩ | ⟨_, _, _, _, haddc,
            _⟩ | ⟨_, _, _, _, _, haddc, _⟩
        · cases hEqU
          by_cases h4c : Δc = 4
          · subst h4c
            have hF4' : BigF s4 ((3, false) :: (1, false) :: (1, false) :: Rc) 7 R_fin := by
                simpa [ones] using hF4
            rcases (ih sc (by omega)).f_4_head hc hNX with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
            · obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' bigF_3_1_1_1_nil_exists
              exact Or.inr (strong2_of_2_0s (Or.inr (Or.inl rfl)))
            · exfalso
              by_cases h4a : Δa = 4
              · subst h4a
                have hc' : BigF sc Ra 4 ((1, true) :: W) := by simpa [ones] using hc
                rcases hHead with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
                · cases ha
                · cases ha
                · exact ((ih sa (by omega)).f1 ha (noNonlast0F_tail hN1)).2.1 rfl
                · cases ha
                · rcases bigF_2_4_head ih (by omega) ha (noNonlast0F_tail hN1) with rfl | ⟨W', rfl,
                      _⟩ | ⟨W', rfl⟩
                  · cases hc' with
                    | oneF_rem2 h0 hrem _ => cases h0; omega
                    | oneF_rem0 h0 hrem _ => cases h0; omega
                  · rcases bigF_2_4_head ih (by omega) hc' (noNonlast0F_tail hNa) with hE | ⟨_, hE,
                        _⟩ | ⟨_, hE⟩ <;> cases hE
                  · rcases bigF_2_4_head ih (by omega) hc' (noNonlast0F_tail hNa) with hE | ⟨_, hE,
                        _⟩ | ⟨_, hE⟩ <;> cases hE
              · have hq1 : 1 ≤ Δa / 3 - 1 := by omega
                obtain ⟨W', hW'⟩ := ones_pos_cons hq1 Ra
                have hc' : BigF sc ((1, false) :: W') 4 ((1, true) :: W) := by
                  have htmp :=
                      hc; change BigF sc (ones (Δa / 3 - 1) ++ Ra) 4 ((1, true) :: W) at htmp
                  rw [hW'] at htmp; exact htmp
                have hNW' : NoNonlast0F W' := by
                    have htmp := hNX; rw [hW'] at htmp; exact noNonlast0F_tail htmp
                exact ((ih sc (by omega)).f1 hc' hNW').2.1 rfl
            · exact Or.inr (bigF_3_1_1_2_seven_strong ih (by omega) hF4' (noNonlast0F_tail hNc))
          · by_cases h7c : Δc = 7
            · subst h7c
              have hF4' : BigF s4 ((3, false) :: (1, false) :: (1, false) :: (1,
                  false) :: Rc) 7 R_fin := by
                simpa [ones] using hF4
              have hRc_good : Head0s111 Rc ∨ Good1Safe Rc := by
                by_cases h4a : Δa = 4
                · subst h4a
                  have hc' : BigF sc Ra 7 Rc := by simpa [ones] using hc
                  rcases hHead with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
                  · cases ha
                  · cases ha
                  · exact False.elim (((ih sa (by omega)).f1 ha (noNonlast0F_tail hN1)).2.1 rfl)
                  · cases ha
                  · rcases bigF_2_4_head ih (by omega) ha (noNonlast0F_tail hN1) with
                        rfl | ⟨W, rfl, hW⟩ | ⟨W, rfl⟩
                    · cases hc' with
                      | oneF_rem2 h0 hrem _ => cases h0; omega
                      | oneF_rem0 h0 hrem _ => cases h0; omega
                    · rcases hW with rfl | ⟨V, rfl⟩ | ⟨V, rfl⟩
                      · obtain ⟨s2a, _, Δ2a, R2a, h2a, hc2a⟩ := bigF_2_inv hc'
                        have h2a' : BigF s2a [(2, true), (0, false)] Δ2a R2a := by
                            simpa [bumpR] using h2a
                        obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h2a' bigF_2s_0_exists
                        rcases hc2a with ⟨_, _, h0, _⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                            _⟩ |
                            ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                                _⟩ <;> omega
                      · obtain ⟨s2a, _, Δ2a, R2a, h2a, hc2a⟩ := bigF_2_inv hc'
                        have h2a' : BigF s2a ((2, true) :: (0, true) :: V) Δ2a R2a := by
                            simpa [bumpR] using h2a
                        obtain ⟨rfl, _⟩ :=
                            (bigFD_det _).1 _ _ _ _ _ _ h2a' (bigF_2s_0s_full_exists V)
                        rcases hc2a with ⟨_, _, h0, _⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                            _⟩ |
                            ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                                _⟩ <;> omega
                      · obtain ⟨s2a, _, Δ2a, R2a, h2a, hc2a⟩ := bigF_2_inv hc'
                        have h2a' : BigF s2a ((2, true) :: (1, false) :: V) Δ2a R2a := by
                            simpa [bumpR] using h2a
                        have hNV := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNa))
                        have hN2a := (bigFD_noNonlast0F _).1 _ _ _ h2a'
                          (noNonlast0F_cons_ne0F (x := (2, true)) (by simp)
                            (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNV))
                        rcases (ih s2a (by omega)).f2s_1 h2a' hNV with rfl | rfl | rfl | rfl
                        · rcases hc2a with ⟨hrem, _, _, _⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _,
                              _, _⟩ |
                              ⟨_, sd, _, Δd, haddd, hDd⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨_, hge6, _, _, _,
                                  _⟩
                          · omega
                          · omega
                          · omega
                          · obtain ⟨U2, rfl, _⟩ := ((ih s2a (by omega)).f2s h2a'
                              (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNV)).2.2.1 rfl
                            cases hDd; omega
                          · omega
                          · omega
                        · rcases hc2a with ⟨_, _, h0, _⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                              _⟩ |
                              ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                                  _⟩ <;> omega
                        · rcases hc2a with ⟨_, _, h0, _⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                              _⟩ |
                              ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                                  _⟩ <;> omega
                        · rcases hc2a with ⟨_, _, h0, _⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                              _⟩ |
                              ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _,
                                  _⟩ <;> omega
                    · exact bigF_2_1_7_head ih (by omega) hc'
                          (noNonlast0F_tail (noNonlast0F_tail hNa))
                · by_cases h7a : Δa = 7
                  · subst h7a
                    have hc' : BigF sc ((1, false) :: Ra) 7 Rc := by simpa [ones] using hc
                    exact ((ih sc (by omega)).f1 hc' hNa).2.2.2.2.1 rfl
                  · by_cases h10a : Δa = 10
                    · subst h10a
                      have hc' : BigF sc ((1, false) :: (1, false) :: Ra) 7 Rc := by
                          simpa [ones] using hc
                      exact Or.inr (((ih sc (by omega)).f11 hc' hNa).2.2.2.1 rfl)
                    · have hge13 : 13 ≤ Δa := by omega
                      have hq3 : Δa / 3 - 1 = (Δa / 3 - 4) + 3 := by omega
                      rw [hq3] at hc
                      have hc' : BigF sc ((1, false) :: (1, false) :: (1,
                          false) :: (ones (Δa / 3 - 4) ++ Ra)) 7 Rc := by
                        simpa [ones] using hc
                      rcases (ih sc (by omega)).f111 hc' (noNonlast0F_ones_append _ hNa) with ⟨h0,
                          _, _⟩ | ⟨hm, _, _, _⟩ <;> omega
              rcases hRc_good with ⟨V, rfl⟩ | hG1
              · obtain ⟨_, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF4' (bigF_3_1_1_1_0s_1_1_exists ((1, false) :: V))
                exact Or.inr (strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1,
                    false) :: (1, false) :: V, rfl⟩)))))
              · exact Or.inr
                    (((ih s4 (by omega)).good2_f3111 (good1Safe_to_good2 hG1) hF4' hNc).2.2
                    (good1Safe_to_strong2 hG1))
            · have hge10 : 10 ≤ Δc := by omega
              have hq2 : Δc / 3 - 1 = (Δc / 3 - 3) + 2 := by omega
              rw [hq2] at hF4
              have hF4' : BigF s4 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                  false) ::
                  (ones (Δc / 3 - 3) ++ Rc)) 7 R_fin := by simpa [ones] using hF4
              have hGZ : GoodZero111Head (ones (Δc / 3 - 3) ++ Rc) := by
                cases hq : Δc / 3 - 3 with
                | zero =>
                  simp only [ones, List.nil_append]
                  by_cases h0s : ∃ W, Rc = (0, true) :: W
                  · obtain ⟨W, hW⟩ := h0s
                    exact Or.inr ((ih sc (by omega)).f_pos_0s hc hNX (by omega) hW)
                  · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
                | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
              exact Or.inr
                  (((ih s4 (by omega)).f3_1111 hF4' (noNonlast0F_ones_append _ hNc)).2.2 hGZ)
        · omega
        · omega
        · omega
      · omega
      · omega
    · by_cases h5e : Δ0 = 5
      · subst h5e
        obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN11 (Or.inr (Or.inl rfl))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) 10 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN0))
        have h4 := ((ih s4 (by omega)).f2s_111 hF4 hNU).1
        omega
      · by_cases h8e : Δ0 = 8
        · subst h8e
          obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN11 (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) 10 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h7, _⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          omega
        · by_cases h11e : Δ0 = 11
          · subst h11e
            rcases (ih s1 (by omega)).f_11 h1 hN11 with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0,
                  true) :: (1, false) :: (1, false) :: U) 10 R_fin := by
                simpa [ones] using hF2
              obtain ⟨h7, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_1_0s_1_1_exists U)
              omega
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
                  false) :: R0) 10 R_fin := by
                simpa [ones] using hF2
              have h7 := ((ih s2 (by omega)).good2_f3111 hS.1 hF2' hN0).1
              omega
          · have hge14 : 14 ≤ Δ0 := by omega
            have hq4 : Δ0 / 3 = (Δ0 / 3 - 4) + 4 := by omega
            rw [hq4] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δ0 / 3 - 4) ++ R0)) 10 R_fin := by simpa [ones] using hF2
            have h7 := ((ih s2 (by omega)).f3_1111 hF2' (noNonlast0F_ones_append _ hN0)).1
            omega
  · have h9e : Δ3 = 9 := by omega
    subst h9e
    obtain ⟨W, rfl⟩ := bigF_oneF_zero_head h1
    have hF2' : BigF s2 ((2, true) :: W) 9 R_fin := by simpa [bumpR] using hF2
    exact ((ih s2 (by omega)).f2s hF2' (noNonlast0F_tail hN0)).2.2.2.2.2.1 rfl
  · have h9e : Δ3 = 9 := by omega
    subst h9e
    have hne3 := ((ih s1 (by omega)).f1 h1 hN1).1
    by_cases h6e : Δ0 = 6
    · subst h6e
      have hF2' : BigF s2 ((3, false) :: (1, false) :: R0) 9 R_fin := by simpa [ones] using hF2
      exact (ih s2 (by omega)).f3_9 hF2' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN0)
    · by_cases h9d : Δ0 = 9
      · subst h9d
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R0) 9 R_fin := by
            simpa [ones] using hF2
        rcases (ih s2 (by omega)).f3_11 hF2' hN0 with h0 | h7 | ⟨h10, _⟩ <;> omega
      · have hge12 : 12 ≤ Δ0 := by omega
        have hq3 : Δ0 / 3 - 1 = (Δ0 / 3 - 4) + 3 := by omega
        rw [hq3] at hF2
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
            (ones (Δ0 / 3 - 4) ++ R0)) 9 R_fin := by simpa [ones] using hF2
        obtain ⟨h710, _, _⟩ := (ih s2 (by omega)).f3_111 hF2' (noNonlast0F_ones_append _ hN0)
        omega

/-! ## Group 3: F(1 :: Y), F(1, 1 :: Y), F(1, 1, 1 :: Y) -/

theorem step_f1 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((1, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    Δ ≠ 3 ∧ Δ ≠ 4 ∧
    (Δ = 5 → Safe0s R_fin) ∧
    (Δ = 6 → Head0s11 R_fin) ∧
    (Δ = 7 → Head0s111 R_fin ∨ Good1Safe R_fin) ∧
    (Δ = 10 → Head0s11 R_fin ∨ Good2 R_fin) ∧
    (Δ = 13 → Head0s11 R_fin ∨ Good2 R_fin) ∧
    (Δ = 14 → Head0s11 R_fin ∨ Strong2 R_fin) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_1_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, rfl, _⟩ |
      ⟨hrem1, hge4, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, rfl, hF2⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- Δ1 = 3q + 1 (≥ 4): Δ = Δ3 + 2, hF2 : BigF s2 (3 :: ones (Δ1/3 - 1) ++ R1) Δ3 R_fin
    have hN_in := noNonlast0F_ones_append (Δ1 / 3 - 1) hN1
    have hne24 := (ih s2 hs2).f3_ne24 hF2 hN_in
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h3
      have h1e : Δ3 = 1 := by omega
      subst h1e; exact bigF_ne_one hF2
    · omega
    · intro h5
      have h3e : Δ3 = 3 := by omega
      subst h3e
      refine (ih s2 hs2).f3_3_non0s hF2 hN_in (fun Z hZ => ?_)
      by_cases h4e : Δ1 = 4
      · subst h4e
        change R1 = (0, true) :: Z at hZ
        exact (ih s1 hs1).f_4_ne0s h1 hN hZ
      · have hq1 : 1 ≤ Δ1 / 3 - 1 := by omega
        obtain ⟨W, hW⟩ := ones_pos_cons hq1 R1
        change ones (Δ1 / 3 - 1) ++ R1 = (0, true) :: Z at hZ
        rw [hW] at hZ
        cases hZ
    · omega
    · intro h7
      have h5e : Δ3 = 5 := by omega
      subst h5e
      exact Or.inl ((ih s2 hs2).f3_5_0111 hF2 hN_in)
    · intro h10
      have h8e : Δ3 = 8 := by omega
      subst h8e
      exact Or.inl ((ih s2 hs2).f_258 hF2 (noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN_in)
        (Or.inr (Or.inr rfl)))
    · intro h13
      have h11e : Δ3 = 11 := by omega
      subst h11e
      rcases (ih s2 hs2).f_11 hF2 (noNonlast0F_cons_ne0F (x := (3,
          false)) (by simp) hN_in) with hH | hS
      · exact Or.inl hH
      · exact Or.inr hS.1
    · intro h14
      have h12e : Δ3 = 12 := by omega
      subst h12e
      by_cases h4e : Δ1 = 4
      · subst h4e
        have hF2' : BigF s2 ((3, false) :: R1) 12 R_fin := by simpa [ones] using hF2
        rcases (ih s1 hs1).f_4_head h1 hN with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
        · obtain ⟨h7, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' bigF_3_1_nil_exists
          omega
        · obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1s_inv hF2'
          have h9e : Δ4 = 9 := by omega
          subst h9e
          exact ((ih s4 (by omega)).f2s hF4
              (noNonlast0F_bumpR (noNonlast0F_tail hN1))).2.2.2.2.2.1 rfl
        · exact bigF_3_2_12_strong ih hs2 hF2' (noNonlast0F_tail hN1)
      · by_cases h7e : Δ1 = 7
        · subst h7e
          have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) 12 R_fin := by simpa [ones] using hF2
          have hHead : R1 = [(0, false)] ∨ (∃ Z, R1 = (0, true) :: Z) ∨ (∃ Z, R1 = (1,
              false) :: Z) ∨
              (∃ Z, R1 = (1, true) :: Z) ∨ (∃ Z, R1 = (2, false) :: Z) := by
            have hh := bigF_head_nnf _ _ _ _ h1 hN
            cases R1 with
            | nil => exact False.elim hh
            | cons x xs =>
              cases x with
              | mk dx bx =>
                cases dx with
                | zero =>
                  cases bx with
                  | false =>
                    cases xs with
                    | nil => exact Or.inl rfl
                    | cons _ _ => exact False.elim hN1
                  | true => exact Or.inr (Or.inl ⟨xs, rfl⟩)
                | succ dx' =>
                  cases dx' with
                  | zero =>
                    cases bx with
                    | false => exact Or.inr (Or.inr (Or.inl ⟨xs, rfl⟩))
                    | true => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨xs, rfl⟩)))
                  | succ dx'' =>
                    cases dx'' with
                    | zero =>
                      cases bx with
                      | false => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨xs, rfl⟩)))
                      | true => exact False.elim hh
                    | succ _ => exact False.elim hh
          exact bigF_3_1_12_of_validHead ih hs2 hF2' hN1 hHead
        · by_cases h10e : Δ1 = 10
          · subst h10e
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 12 R_fin := by
                simpa [ones] using hF2
            rcases (ih s2 hs2).f3_11 hF2' hN1 with h0 | h7 | ⟨h10, _⟩ <;> omega
          · have hge13 : 13 ≤ Δ1 := by omega
            have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
            rw [hq3] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                (ones (Δ1 / 3 - 4) ++ R1)) 12 R_fin := by simpa [ones] using hF2
            obtain ⟨h710, _, _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
            omega
  · -- Δ1 = 2: R1 = 0*::1::1::U with GoodF2U U, bumpR^2 R1 = [2*, 1, 1 :: U], Δ = Δ3 + 3
    obtain ⟨U, rfl, hGFU⟩ := (ih s1 hs1).f_25_goodF2U h1 hN (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF2
    rcases (ih s2 hs2).f2s_11 hF2' hNU with ⟨rfl, hG1⟩ | ⟨rfl, hS⟩ | rfl
    · exact ⟨by omega, by omega, by omega, by omega,
        fun _ => Or.inr (hG1 (goodF2U_to_goodZero111Head hGFU)), by omega, by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
        fun _ => Or.inr (hS hGFU).1, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- Δ1 = 3q + 2 (≥ 5): Δ = Δ3 + 3, hF2 : BigF s2 (3 :: ones (Δ1/3 - 1) ++ R1) Δ3 R_fin
    have hN_in := noNonlast0F_ones_append (Δ1 / 3 - 1) hN1
    have hne24 := (ih s2 hs2).f3_ne24 hF2 hN_in
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h3
      have h0e : Δ3 = 0 := by omega
      subst h0e
      by_cases h5 : Δ1 = 5
      · subst h5
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inl rfl))
        have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 0 R_fin := by
          simpa [ones] using hF2
        obtain ⟨_, _, _, hadd, _⟩ := bigF_3_0s_inv hF2'
        omega
      · by_cases h8 : Δ1 = 8
        · subst h8
          obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
              false) :: U) 0 R_fin := by
            simpa [ones] using hF2
          obtain ⟨_, _, _, hadd, _⟩ := bigF_3_1_0s_inv hF2'
          omega
        · by_cases h11 : Δ1 = 11
          · subst h11
            rcases (ih s1 hs1).f_11 h1 hN with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                  false) :: (1, false) :: U) 0 R_fin := by
                simpa [ones] using hF2
              obtain ⟨h7, _⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                  false) :: U))
              omega
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 0 R_fin := by
                simpa [ones] using hF2
              have h7 := ((ih s2 hs2).good2_f311 hS.1 hF2' hN1).1
              omega
          · have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
            rw [hq3] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                (ones (Δ1 / 3 - 4) ++ R1)) 0 R_fin := by simpa [ones] using hF2
            obtain ⟨h710, _, _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
            omega
    · intro h4
      have h1e : Δ3 = 1 := by omega
      subst h1e; exact bigF_ne_one hF2
    · omega
    · intro h6
      have h3e : Δ3 = 3 := by omega
      subst h3e
      exact (ih s2 hs2).f3_36 hF2 hN_in (Or.inl rfl)
    · omega
    · intro h10
      have h7e : Δ3 = 7 := by omega
      subst h7e
      by_cases h5 : Δ1 = 5
      · subst h5
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inl rfl))
        have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 7 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv hF2'
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        exact False.elim (((ih s4 (by omega)).f3_ne24 hF4
          (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
            (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNU))).2 (by omega))
      · by_cases h8 : Δ1 = 8
        · subst h8
          obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
              false) :: U) 7 R_fin := by
            simpa [ones] using hF2
          obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
          have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
          exact Or.inr (good1Safe_to_good2 ((ih s4 (by omega)).f2s_111 hF4 hNU).2)
        · by_cases h11 : Δ1 = 11
          · subst h11
            rcases (ih s1 hs1).f_11 h1 hN with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                  false) :: (1, false) :: U) 7 R_fin := by
                simpa [ones] using hF2
              obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                  false) :: U))
              exact Or.inr (good2_of_2_1_1 ((1, false) :: U))
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 7 R_fin := by
                simpa [ones] using hF2
              exact Or.inr ((ih s2 hs2).good2_f311 hS.1 hF2' hN1).2.1
          · have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
            rw [hq3] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                (ones (Δ1 / 3 - 4) ++ R1)) 7 R_fin := by simpa [ones] using hF2
            exact Or.inr ((ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)).2.1
    · intro h13
      have h10e : Δ3 = 10 := by omega
      subst h10e
      by_cases h5 : Δ1 = 5
      · subst h5
        obtain ⟨U, rfl, hGFU⟩ := (ih s1 hs1).f_25_goodF2U h1 hN (Or.inr rfl)
        have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) 10 R_fin :=
            by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_0s_inv hF2'
        have h7e : Δ4 = 7 := by omega
        subst h7e
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        exact Or.inr (bigF_3_1_1_goodF2U_7 ih (by omega) hGFU hF4 hNU)
      · by_cases h8 : Δ1 = 8
        · subst h8
          obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN (Or.inr (Or.inr rfl))
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
              false) :: U) 10 R_fin := by
            simpa [ones] using hF2
          obtain ⟨s4, hs4, Δ4, hadd4, hF4⟩ := bigF_3_1_0s_inv hF2'
          have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
          have h4 := ((ih s4 (by omega)).f2s_111 hF4 hNU).1
          omega
        · by_cases h11 : Δ1 = 11
          · subst h11
            rcases (ih s1 hs1).f_11 h1 hN with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                  false) :: (1, false) :: U) 10 R_fin := by
                simpa [ones] using hF2
              obtain ⟨h7, _⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                  false) :: U))
              omega
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 10 R_fin := by
                simpa [ones] using hF2
              have h7 := ((ih s2 hs2).good2_f311 hS.1 hF2' hN1).1
              omega
          · have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
            rw [hq3] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                (ones (Δ1 / 3 - 4) ++ R1)) 10 R_fin := by simpa [ones] using hF2
            exact Or.inr ((ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)).2.1
    · intro h14
      have h11e : Δ3 = 11 := by omega
      subst h11e
      exact (ih s2 hs2).f_11 hF2 (noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN_in)

/-- Helper for `step_f11` (Δ=13 with `GoodF2U Y`):
    when `GoodF2U Y`, `BigF s1 (1 :: Y) 5 (0*::1::1::U)`, and `BigF s4 (3::1::1::U) 7 R_fin`,
    `Strong2 R_fin` holds. -/
theorem bigF_1_5_311_strong {m s1 s4 : Nat} (ih : InvLt m) (hs1 : s1 < m) (hs4 : s4 < m)
    {Y U R_fin : List Seg} (hGF : GoodF2U Y)
    (h1 : BigF s1 ((1, false) :: Y) 5 ((0, true) :: (1, false) :: (1, false) :: U))
    (hF4 : BigF s4 ((3, false) :: (1, false) :: (1, false) :: U) 7 R_fin)
    (hN : NoNonlast0F Y) : Strong2 R_fin := by
  have hN_out :=
      (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN_out))
  obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_1_inv h1
  have hNa := (bigFD_noNonlast0F _).1 _ _ _ ha hN
  rcases hca with ⟨_, h0, _⟩ |
      ⟨hrema, hgea, sb, hsb, Δb, haddb, hFb⟩ |
      ⟨rfl, sb, hsb, Δb, haddb, hFb⟩ |
      ⟨hrema, hgea, sb, hsb, Δb, haddb, hFb⟩
  · omega
  · have h3b : Δb = 3 := by omega
    subst h3b
    have hNX := noNonlast0F_ones_append (Δa / 3 - 1) hNa
    -- hFb : BigF sb (3 :: X) 3 (0* :: 1 :: 1 :: U), where X = ones (Δa/3 - 1) ++ Ra
    obtain ⟨sc, hsc, Δc, Rc, hc, hcc⟩ := bigF_3_inv hFb
    have hNc := (bigFD_noNonlast0F _).1 _ _ _ hc hNX
    rcases hcc with ⟨_, _, h0, _⟩ |
        ⟨_, sd, hsd, Δd, haddd, hFd⟩ |
        ⟨rfl, sd, hsd, Δd, haddd, hFd⟩ |
        ⟨hremc, hge3c, sd, hsd, Δd, haddd, hFd⟩
    · omega
    · have h1d : Δd = 1 := by omega
      subst h1d; exact False.elim (bigF_ne_one hFd)
    · have h0d : Δd = 0 := by omega
      subst h0d
      -- Show Rc = 0* :: 1 :: Zc so bumpR^2 Rc = 2* :: 1 :: Zc, then f2s(0) -> f11(7/10/>=13)!
      have hRc1 : ∃ Zc, Rc = (0, true) :: (1, false) :: Zc := by
        by_cases h4a : Δa = 4
        · subst h4a
          have hc' : BigF sc Ra 0 Rc := by simpa [ones] using hc
          rcases hGF with ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩
          · exact False.elim (((ih sa (by omega)).f1 ha (noNonlast0F_tail hN)).2.1 rfl)
          · cases ha
          · rcases bigF_2_4_head ih (by omega) ha (noNonlast0F_tail hN) with rfl | ⟨W', rfl,
                _⟩ | ⟨W', rfl⟩
            · cases hc' with
              | oneF_rem1 h0 _ => cases h0; exact False.elim (by
                  have hFd' : BigF sd [(2, true), (0, false)] 0 ((0, true) :: (1, false) :: (1,
                      false) :: U) := by
                    simpa [ones, bumpR] using hFd
                  obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hFd' bigF_2s_0_exists
                  omega)
              | oneF_rem2 h0 _ h2 =>
                have hge :=
                    bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0))
                omega
            · exact bigF_ge2_zero_head hc'
            · exact bigF_ge2_zero_head hc'
          · cases ha
        · have hq1 : 1 ≤ Δa / 3 - 1 := by omega
          obtain ⟨W, hW⟩ := ones_pos_cons hq1 Ra
          have hc' : BigF sc ((1, false) :: W) 0 Rc := by
            have htmp := hc; change BigF sc (ones (Δa / 3 - 1) ++ Ra) 0 Rc at htmp
            rw [hW] at htmp; exact htmp
          cases hc' with
          | oneF_rem1 hW0 hremW0 =>
            rename_i sW RW ΔW
            by_cases h0W : ΔW = 0
            · subst h0W
              have hNW : NoNonlast0F W := by
                have := hNX; rw [hW] at this; exact noNonlast0F_tail this
              rcases bigF_zero_head_3 hW0 hNW with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
              · -- Rc = [0*, 0] -> bumpR^2 Rc = [2*, 0], Δd = 4 ≠ 0
                have hFd' : BigF sd [(2, true), (0, false)] 0 ((0, true) :: (1, false) :: (1,
                    false) :: U) := by
                  simpa [ones, bumpR] using hFd
                obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hFd' bigF_2s_0_exists
                omega
              · have hFd' : BigF sd ((2, true) :: (0, true) :: Z) 0 ((0, true) :: (1, false) :: (1,
                    false) :: U) := by
                  simpa [ones, bumpR] using hFd
                obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hFd' (bigF_2s_0s_full_exists Z)
                omega
              · exact ⟨Z, by simp [ones]⟩
            · have hqW : 1 ≤ (1 + ΔW) / 3 := by omega
              obtain ⟨Z, hZ⟩ := ones_pos_cons hqW RW
              exact ⟨Z, congrArg ((0, true) :: ·) hZ⟩
          | oneF_rem2 hW0 _ hW2 =>
            have hge := bigD1_ge2_of_ne_nil hW2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hW0))
            omega
      obtain ⟨Zc, rfl⟩ := hRc1
      have hNZc := noNonlast0F_tail (noNonlast0F_tail hNc)
      have hFd' : BigF sd ((2, true) :: (1, false) :: Zc) 0 ((0, true) :: (1, false) :: (1,
          false) :: U) := by
        simpa [bumpR] using hFd
      obtain ⟨se, hse, Δe, Re, he, hce⟩ := bigF_2s_inv hFd'
      have hNe := (bigFD_noNonlast0F _).1 _ _ _ he
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
          (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZc))
      rcases hce with ⟨hreme, hgee, _, hEq⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
          ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
      · have hf11e := (ih se (by omega)).f11 he hNZc
        have hne4 : Δe ≠ 4 :=
            ((ih se (by omega)).f1 he (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZc)).2.1
        by_cases h7e : Δe = 7
        · subst h7e
          have hEq' : U = Re := by simpa [ones] using hEq
          subst hEq'
          have hG1 := hf11e.2.2.2.1 rfl
          exact ((ih s4 hs4).good2_f311 (good1Safe_to_good2 hG1) hF4 hNe).2
        · by_cases h10e : Δe = 10
          · subst h10e
            have hEq' : U = (1, false) :: Re := by simpa [ones] using hEq
            subst hEq'
            have hS := hf11e.2.2.2.2.2.2 rfl
            exact ((ih s4 hs4).good2_f3111 hS.1 hF4 hNe).2.2 hS
          · have hge13 : 13 ≤ Δe := by omega
            have hq2 : Δe / 3 = (Δe / 3 - 4) + 4 := by omega
            rw [hq2] at hEq
            have hEq' : U = (1, false) :: (1, false) :: (ones (Δe / 3 - 4) ++ Re) := by
              simpa [ones] using hEq
            subst hEq'
            have hGZ : GoodZero111Head (ones (Δe / 3 - 4) ++ Re) := by
              cases hq : Δe / 3 - 4 with
              | zero =>
                simp only [ones, List.nil_append]
                by_cases h0s : ∃ W, Re = (0, true) :: W
                · obtain ⟨W, hW⟩ := h0s
                  exact Or.inr ((ih se (by omega)).f_pos_0s he
                    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
                      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZc)) (by omega) hW)
                · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
              | succ k => exact Or.inl (fun _ hEq2 => by simp [ones] at hEq2)
            exact ((ih s4 hs4).f3_1111 hF4 (noNonlast0F_ones_append _ hNe)).2.2 hGZ
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h0d : Δd = 0 := by omega
      subst h0d
      -- hFd : BigF sd (3 :: ones (Δc/3 - 1) ++ Rc) 0 (0*::1::1::U)
      obtain ⟨se, hse, Δe, Re, he, hce⟩ := bigF_3_inv hFd
      have hNYe := noNonlast0F_ones_append (Δc / 3 - 1) hNc
      have hNe := (bigFD_noNonlast0F _).1 _ _ _ he hNYe
      rcases hce with ⟨hreme, hgee, _, hEq⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _,
          _, _, _, hadd, _⟩
      · cases hEq
        by_cases h4e : Δe = 4
        · subst h4e
          have hF4' : BigF s4 ((3, false) :: (1, false) :: (1, false) :: Re) 7 R_fin := by
              simpa [ones] using hF4
          rcases (ih se (by omega)).f_4_head he hNYe with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
          · obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' bigF_3_1_1_1_nil_exists
            exact strong2_of_2_0s (Or.inr (Or.inl rfl))
          · exfalso
            by_cases h3c : Δc = 3
            · subst h3c
              have he' : BigF se Rc 4 ((1, true) :: W) := by simpa [ones] using he
              obtain ⟨W', rfl⟩ := bigF_three_head hc
              cases he'
            · have hq1 : 1 ≤ Δc / 3 - 1 := by omega
              obtain ⟨W', hW'⟩ := ones_pos_cons hq1 Rc
              have he' : BigF se ((1, false) :: W') 4 ((1, true) :: W) := by
                have htmp := he; change BigF se (ones (Δc / 3 - 1) ++ Rc) 4 ((1, true) :: W) at htmp
                rw [hW'] at htmp; exact htmp
              have hNW' : NoNonlast0F W' := by
                  have htmp := hNYe; rw [hW'] at htmp; exact noNonlast0F_tail htmp
              exact ((ih se (by omega)).f1 he' hNW').2.1 rfl
          · exact bigF_3_1_1_2_seven_strong ih hs4 hF4' (noNonlast0F_tail hNe)
        · by_cases h7e : Δe = 7
          · subst h7e
            have hF4' : BigF s4 ((3, false) :: (1, false) :: (1, false) :: (1,
                false) :: Re) 7 R_fin := by
              simpa [ones] using hF4
            have hRe_good : Head0s111 Re ∨ Good1Safe Re := by
              by_cases h3c : Δc = 3
              · subst h3c
                have he' : BigF se Rc 7 Re := by simpa [ones] using he
                obtain ⟨W, rfl⟩ := bigF_three_head hc
                cases he'
              · by_cases h6c : Δc = 6
                · subst h6c
                  have he' : BigF se ((1, false) :: Rc) 7 Re := by simpa [ones] using he
                  exact ((ih se (by omega)).f1 he' hNc).2.2.2.2.1 rfl
                · by_cases h9c : Δc = 9
                  · subst h9c
                    have he' : BigF se ((1, false) :: (1, false) :: Rc) 7 Re := by
                        simpa [ones] using he
                    exact Or.inr (((ih se (by omega)).f11 he' hNc).2.2.2.1 rfl)
                  · have hge12 : 12 ≤ Δc := by omega
                    have hq3 : Δc / 3 - 1 = (Δc / 3 - 4) + 3 := by omega
                    rw [hq3] at he
                    have he' : BigF se ((1, false) :: (1, false) :: (1,
                        false) :: (ones (Δc / 3 - 4) ++ Rc)) 7 Re := by
                      simpa [ones] using he
                    rcases (ih se (by omega)).f111 he' (noNonlast0F_ones_append _ hNc) with ⟨h0, _,
                        _⟩ | ⟨hm, _, _, _⟩ <;> omega
            rcases hRe_good with ⟨V, rfl⟩ | hG1
            · obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF4' (bigF_3_1_1_1_0s_1_1_exists ((1, false) :: V))
              exact strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1, false) :: (1,
                  false) :: V, rfl⟩))))
            · exact ((ih s4 hs4).good2_f3111 (good1Safe_to_good2 hG1) hF4' hNe).2.2
                  (good1Safe_to_strong2 hG1)
          · have hge10 : 10 ≤ Δe := by omega
            have hq2 : Δe / 3 - 1 = (Δe / 3 - 3) + 2 := by omega
            rw [hq2] at hF4
            have hF4' : BigF s4 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δe / 3 - 3) ++ Re)) 7 R_fin := by simpa [ones] using hF4
            have hGZ : GoodZero111Head (ones (Δe / 3 - 3) ++ Re) := by
              cases hq : Δe / 3 - 3 with
              | zero =>
                simp only [ones, List.nil_append]
                by_cases h0s : ∃ W, Re = (0, true) :: W
                · obtain ⟨W, hW⟩ := h0s
                  exact Or.inr ((ih se (by omega)).f_pos_0s he hNYe (by omega) hW)
                · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
              | succ k => exact Or.inl (fun _ hEq2 => by simp [ones] at hEq2)
            exact ((ih s4 hs4).f3_1111 hF4' (noNonlast0F_ones_append _ hNe)).2.2 hGZ
      · omega
      · omega
      · omega
  · obtain ⟨U1, rfl⟩ := (ih sa (by omega)).f_258 ha hN (Or.inl rfl)
    have hNU1 := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNa))
    have hFb' : BigF sb ((2, true) :: (1, false) :: (1, false) :: U1) Δb ((0, true) :: (1,
        false) :: (1, false) :: U) := by
      simpa [bumpR] using hFb
    rcases (ih sb (by omega)).f2s_11 hFb' hNU1 with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
  · exact False.elim (((ih sb (by omega)).f3_ne24 hFb (noNonlast0F_ones_append _ hNa)).1 (by omega))

theorem step_f11 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((1, false) :: (1, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    Δ % 3 ≠ 2 ∧ Δ ≠ 3 ∧ Δ ≠ 6 ∧
    (Δ = 7 → Good1Safe R_fin) ∧
    (((Δ % 3 = 0 ∧ 9 ≤ Δ) ∨ Δ = 10) → Good2 R_fin) ∧
    (Δ = 13 → GoodF2U Y → Strong2 R_fin) ∧
    (Δ = 10 → Strong2 R_fin) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_1_inv h
  have hN1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN1Y
  have hf1 := (ih s1 hs1).f1 h1 hN
  rcases hcases with ⟨_, rfl, _⟩ |
      ⟨hrem1, hge4, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, rfl, hF2⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- Δ1 ≡ 1 (mod 3), ≥ 4; hf1 gives Δ1 ≠ 4 so Δ1 ≥ 7
    by_cases h7 : Δ1 = 7
    · subst h7
      rcases hf1.2.2.2.2.1 rfl with ⟨U, rfl⟩ | hG1
      · have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: (1, false) :: U) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2'
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        obtain ⟨rfl, hG1'⟩ := (ih s4 (by omega)).f2s_111 hF4 hNU
        exact ⟨by omega, by omega, by omega, by omega, fun _ => good1Safe_to_good2 hG1', by omega,
            by omega⟩
      · have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
        have ⟨h710, hSf⟩ := (ih s2 hs2).good2_f31 (good1Safe_to_good2 hG1) hF2' hN1
        have hS := hSf (good1Safe_to_strong2 hG1)
        rcases h710 with rfl | ⟨rfl, _⟩
        · exact ⟨by omega, by omega, by omega, by omega, fun _ => hS.1, by omega, by omega⟩
        · exact ⟨by omega, by omega, by omega, by omega, fun _ => hS.1, by omega, by omega⟩
    · by_cases h10 : Δ1 = 10
      · subst h10
        rcases hf1.2.2.2.2.2.1 rfl with ⟨U, rfl⟩ | hG2
        · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨rfl, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          exact ⟨by omega, by omega, by omega, by omega, fun _ => good2_of_2_1_1 ((1, false) :: U),
                                                by omega, by omega⟩
        · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
          exact ⟨by omega, by omega, by omega, by omega, fun _ => hS'.1, by omega, by omega⟩
      · have hge13 : 13 ≤ Δ1 := by omega
        have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
        rw [hq3] at hF2
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
            (ones (Δ1 / 3 - 4) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
        obtain ⟨h710, hG2', _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
        rcases h710 with rfl | rfl
        · exact ⟨by omega, by omega, by omega, by omega, fun _ => hG2', by omega, by omega⟩
        · exact ⟨by omega, by omega, by omega, by omega, fun _ => hG2', by omega, by omega⟩
  · -- Δ1 = 2: R1 = 0*::1::1::U with GoodF2U U, bumpR^2 R1 = [2*, 1, 1 :: U], Δ = Δ3 + 3
    obtain ⟨U, rfl, hGFU⟩ := (ih s1 hs1).f_25_goodF2U h1 hN1Y (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF2
    rcases (ih s2 hs2).f2s_11 hF2' hNU with ⟨rfl, hG1⟩ | ⟨rfl, hS⟩ | rfl
    · exact ⟨by omega, by omega, by omega, fun _ => hG1 (goodF2U_to_goodZero111Head hGFU), by omega,
          by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, fun _ _ => hS hGFU, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- Δ1 ≡ 2 (mod 3), ≥ 5: Δ = Δ3 + 3
    by_cases h5 : Δ1 = 5
    · subst h5
      obtain ⟨U, rfl, hSU⟩ := hf1.2.2.1 rfl
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2'
      have hΔ4 : Δ4 = 7 ∨ Δ4 = 10 := by
        rcases hSU with ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl⟩ | ⟨hG1, _⟩
        · exact Or.inl ((ih s4 (by omega)).f3_1111 hF4 (noNonlast0F_tail (noNonlast0F_tail hNU))).1
        · exact Or.inl ((ih s4 (by omega)).f3_1111 hF4 (noNonlast0F_tail (noNonlast0F_tail hNU))).1
        · exact ((ih s4 (by omega)).f3_111 hF4 (noNonlast0F_tail hNU)).1
        · obtain ⟨rfl, _⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF4 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: (1,
              false) :: Z))
          exact Or.inl rfl
        · exact Or.inl ((ih s4 (by omega)).good2_f311 (good1_to_good2 hG1) hF4 hNU).1
      rcases hΔ4 with rfl | rfl
      · exact ⟨by omega, by omega, by omega, by omega, by omega,
          fun _ hGF => bigF_1_5_311_strong ih hs1 (by omega) hGF h1 hF4 hN, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases h8 : Δ1 = 8
      · subst h8
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN1Y (Or.inr (Or.inr rfl))
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2'
        obtain ⟨rfl, hG1'⟩ := (ih s4 (by omega)).f2s_111 hF4 hNU
        exact ⟨by omega, by omega, by omega, by omega, fun _ => good1Safe_to_good2 hG1',
          by omega, fun _ => good1Safe_to_strong2 hG1'⟩
      · by_cases h11 : Δ1 = 11
        · subst h11
          rcases (ih s1 hs1).f_11 h1 hN1Y with ⟨U, rfl⟩ | hS
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                false) :: (1, false) :: U) Δ3 R_fin := by
              simpa [ones] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            exact ⟨by omega, by omega, by omega, by omega, fun _ => good2_of_2_1_1 ((1,
                                                  false) :: U),
              by omega, fun _ => strong2_of_2_1_1 ((1, false) :: U)⟩
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
            obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hS.1 hF2' hN1
            exact ⟨by omega, by omega, by omega, by omega, fun _ => hS'.1, by omega, fun _ => hS'⟩
        · by_cases h14 : Δ1 = 14
          · subst h14
            rcases hf1.2.2.2.2.2.2.2 rfl with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0,
                  true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
                simpa [ones] using hF2
              obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_1_0s_1_1_exists U)
              exact ⟨by omega, by omega, by omega, by omega,
                fun _ => good2_of_2_0s ((1, false) :: (1, false) :: (1, false) :: U), by omega,
                fun _ => strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1,
                    false) :: U, rfl⟩))))⟩
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
                  false) :: R1) Δ3 R_fin := by
                simpa [ones] using hF2
              obtain ⟨rfl, hG2', hSf⟩ := (ih s2 hs2).good2_f3111 hS.1 hF2' hN1
              exact ⟨by omega, by omega, by omega, by omega, fun _ => hG2', by omega,
                                                                             fun _ => hSf hS⟩
          · have hge17 : 17 ≤ Δ1 := by omega
            have hq4 : Δ1 / 3 - 1 = (Δ1 / 3 - 5) + 4 := by omega
            rw [hq4] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
            have hGZ : GoodZero111Head (ones (Δ1 / 3 - 5) ++ R1) := by
              cases hq : Δ1 / 3 - 5 with
              | zero =>
                simp only [ones, List.nil_append]
                by_cases h0s : ∃ W, R1 = (0, true) :: W
                · obtain ⟨W, hW⟩ := h0s
                  exact Or.inr ((ih s1 hs1).f_pos_0s h1 hN1Y (by omega) hW)
                · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
              | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
            obtain ⟨rfl, hG2', hSf⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
            exact ⟨by omega, by omega, by omega, by omega, fun _ => hG2', by omega,
                                                                           fun _ => hSf hGZ⟩

/-- `BigF s ((3, false) :: X) 7 R0` always yields `GoodF2U R0`. -/
theorem bigF_3_7_goodF2U {m s : Nat} (ih : InvLt m) (hs : s < m)
    {X R0 : List Seg} (h : BigF s ((3, false) :: X) 7 R0) (hN : NoNonlast0F X) :
    GoodF2U R0 := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨_, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h5e : Δ3 = 5 := by omega
    subst h5e
    exact Or.inr
        (Or.inr (Or.inr
        (head0s111_to_head0s11 ((ih s2 (by omega)).f3_5_0111 hF2 (noNonlast0F_ones_append _ hN1)))))
  · have h4e : Δ3 = 4 := by omega
    subst h4e
    rcases (ih s2 (by omega)).f_4_head hF2
        (noNonlast0F_bumpR (noNonlast0F_bumpR hN1)) with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
    · exact Or.inl ⟨[], rfl⟩
    · exact Or.inr (Or.inl ⟨W, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨W, rfl⟩))
  · exact False.elim (((ih s2 (by omega)).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).2 (by omega))

/-- `BigF s ((1, false) :: Y) 9 R0` always yields `GoodF2U R0`. -/
theorem bigF_1_9_goodF2U {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Y R0 : List Seg} (h : BigF s ((1, false) :: Y) 9 R0) (hN : NoNonlast0F Y) :
    GoodF2U R0 := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_1_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  rcases hcases with ⟨_, h0, _⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h7e : Δ3 = 7 := by omega
    subst h7e
    exact bigF_3_7_goodF2U ih (by omega) hF2 (noNonlast0F_ones_append _ hN1)
  · obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R0 := by
        simpa [bumpR] using hF2
    rcases (ih s2 (by omega)).f2s_11 hF2' hNU with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
  · have h6e : Δ3 = 6 := by omega
    subst h6e
    exact Or.inr
        (Or.inr (Or.inr
        ((ih s2 (by omega)).f3_36 hF2 (noNonlast0F_ones_append _ hN1) (Or.inr rfl))))

theorem step_f111 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((1, false) :: (1, false) :: (1, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    (Δ = 0 ∧ Zero111 R_fin ∧ (GoodZero111Head Y → TightZero111 R_fin)) ∨
    (Δ % 3 = 0 ∧ 9 ≤ Δ ∧ Good2 R_fin ∧ (Δ = 9 → GoodF2U Y → Strong2 R_fin) ∧
        (Δ = 12 → Strong2 R_fin)) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_1_inv h
  have hN11 := noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN11
  have hf11 := (ih s1 hs1).f11 h1 hN
  rcases hcases with ⟨hrem0, rfl, rfl⟩ |
      ⟨hrem1, hge4, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, _, _, _, _, _, _⟩
  · -- Δ1 ≡ 0 (mod 3): Δ = 0, R_fin = 0* :: ones (Δ1 / 3) ++ R1
    by_cases h0 : Δ1 = 0
    · subst h0
      refine Or.inl ⟨rfl, ?_⟩
      cases h1 with
      | oneF_rem1 h0f hrem0f =>
        rename_i s0 R0 Δ0
        have hf1 := (ih s0 (by omega)).f1 h0f hN
        by_cases h0z : Δ0 = 0
        · subst h0z
          cases h0f with
          | oneF_rem1 hy hremy =>
            rename_i sy Ry Δy
            by_cases hyz : Δy = 0
            · subst hyz
              rcases bigF_zero_head_3 hy hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
              · exact ⟨Or.inl rfl, fun _ => ⟨Or.inl rfl, fun _ hEq => by cases hEq⟩⟩
              · exact ⟨Or.inr (Or.inl ⟨Z, rfl⟩), fun _ => ⟨Or.inr (Or.inl ⟨Z, rfl⟩),
                    fun _ hEq => by cases hEq⟩⟩
              · refine ⟨Or.inr (Or.inr (Or.inl ⟨Z, rfl⟩)), fun hGZ => ⟨Or.inr (Or.inr (Or.inl ⟨Z,
                    rfl⟩)), fun Z' hEq => ?_⟩⟩
                cases hEq
                rcases bigF_zero_oneF_head hy hN with ⟨_, rfl⟩ | rfl
                · exact Or.inl rfl
                · rcases hGZ with hne0 | ⟨W, hW⟩
                  · exact False.elim (hne0 Z rfl)
                  · cases hW; exact Or.inr (Or.inr ⟨W, rfl⟩)
            · have hqy : 1 ≤ (1 + Δy) / 3 := by omega
              obtain ⟨Z, hZ⟩ := ones_pos_cons hqy Ry
              have hEqR : (0, true) :: ones (0 / 3) ++ ((0, true) :: ones ((1 + 0) / 3) ++ ((0,
                  true) :: ones ((1 + Δy) / 3) ++ Ry)) =
                  (0, true) :: (0, true) :: (0, true) :: (1, false) :: Z := by
                simpa [ones] using congrArg ((0, true) :: (0, true) :: (0, true) :: ·) hZ
              refine ⟨Or.inr (Or.inr (Or.inl ⟨Z, hEqR⟩)), fun _ => ⟨Or.inr (Or.inr (Or.inl ⟨Z,
                  hEqR⟩)), fun Z' hEq => ?_⟩⟩
              rw [hEqR] at hEq; cases hEq
              by_cases h3y : Δy = 3
              · subst h3y
                have hZ' : Z = Ry := by simpa [ones] using hZ.symm
                subst hZ'
                obtain ⟨W, rfl⟩ := bigF_three_head hy
                exact Or.inr (Or.inl ⟨(1, false) :: W, rfl⟩)
              · have hge6 : 6 ≤ Δy := by omega
                have hq2 : (1 + Δy) / 3 = ((1 + Δy) / 3 - 2) + 2 := by omega
                rw [hq2] at hZ
                have hZ' : Z = (1, false) :: (ones ((1 + Δy) / 3 - 2) ++ Ry) := by
                  simpa [ones] using hZ.symm
                exact Or.inr (Or.inr ⟨ones ((1 + Δy) / 3 - 2) ++ Ry, hZ'⟩)
          | oneF_rem2 hy _ hy2 =>
            have hge := bigD1_ge2_of_ne_nil hy2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hy))
            omega
        · by_cases h6 : Δ0 = 6
          · subst h6
            obtain ⟨U, rfl⟩ := hf1.2.2.2.1 rfl
            exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨U, rfl⟩))),
              fun _ => ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨U, rfl⟩))), fun _ hEq => by cases hEq⟩⟩
          · have hge9 : 9 ≤ Δ0 := by omega
            have hq3 : (1 + Δ0) / 3 = ((1 + Δ0) / 3 - 3) + 3 := by omega
            rw [hq3]
            have hGF0 : GoodF2U (ones ((1 + Δ0) / 3 - 3) ++ R0) := by
              by_cases h9 : Δ0 = 9
              · subst h9
                simpa [ones] using bigF_1_9_goodF2U ih (by omega) h0f hN
              · have hq1 : 1 ≤ (1 + Δ0) / 3 - 3 := by omega
                obtain ⟨W, hW⟩ := ones_pos_cons hq1 R0
                exact Or.inl ⟨W, hW⟩
            exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ones ((1 + Δ0) / 3 - 3) ++ R0, rfl,
                hGF0⟩)))),
              fun _ => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ones ((1 + Δ0) / 3 - 3) ++ R0, rfl,
                  hGF0⟩)))),
                fun _ hEq => by cases hEq⟩⟩
      | oneF_rem2 h0f _ h02 =>
        have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))
        omega
    · have hge9 : 9 ≤ Δ1 := by omega
      have hG2 : Good2 R1 := hf11.2.2.2.2.1 (Or.inl ⟨hrem0, hge9⟩)
      have hq3 : Δ1 / 3 = (Δ1 / 3 - 3) + 3 := by omega
      rw [hq3]
      have hT : GoodTail (ones (Δ1 / 3 - 3) ++ R1) := goodTail_ones_append (Δ1 / 3 - 3) (Or.inl hG2)
      exact Or.inl ⟨rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ones (Δ1 / 3 - 3) ++ R1, rfl, hT⟩)))),
        fun _ => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ones (Δ1 / 3 - 3) ++ R1, rfl, hT⟩)))),
          fun _ hEq => by cases hEq⟩⟩
  · -- Δ1 ≡ 1 (mod 3), ≥ 4: hf1 gives Δ1 ≠ 4
    by_cases h7 : Δ1 = 7
    · subst h7
      have hG1 := hf11.2.2.2.1 rfl
      have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
      have ⟨h710, hSf⟩ := (ih s2 hs2).good2_f31 (good1Safe_to_good2 hG1) hF2' hN1
      have hS := hSf (good1Safe_to_strong2 hG1)
      rcases h710 with rfl | ⟨rfl, _⟩
      · exact Or.inr ⟨rfl, by omega, hS.1, fun _ _ => hS, by omega⟩
      · exact Or.inr ⟨rfl, by omega, hS.1, by omega, fun _ => hS⟩
    · by_cases h10 : Δ1 = 10
      · subst h10
        have hG2 := hf11.2.2.2.2.1 (Or.inr rfl)
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
        exact Or.inr ⟨rfl, by omega, hS'.1, fun _ _ => hS', by omega⟩
      · by_cases h13 : Δ1 = 13
        · subst h13
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
              false) :: R1) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h710, hG2', hS10⟩ := (ih s2 hs2).f3_111 hF2' hN1
          rcases h710 with rfl | rfl
          · refine Or.inr ⟨rfl, by omega, hG2', fun _ hGF => ?_, by omega⟩
            have hS1 := hf11.2.2.2.2.2.1 rfl hGF
            exact ((ih s2 hs2).good2_f3111 hS1.1 hF2' hN1).2.2 hS1
          · exact Or.inr ⟨rfl, by omega, hG2', by omega, fun _ => hS10 rfl⟩
        · have hne4 : Δ1 ≠ 4 :=
              ((ih s1 hs1).f1 h1 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)).2.1
          have hge16 : 16 ≤ Δ1 := by omega
          have hq4 : Δ1 / 3 - 1 = (Δ1 / 3 - 5) + 4 := by omega
          rw [hq4] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
          have hGZ : GoodZero111Head (ones (Δ1 / 3 - 5) ++ R1) := by
            cases hq : Δ1 / 3 - 5 with
            | zero =>
              simp only [ones, List.nil_append]
              by_cases h0s : ∃ W, R1 = (0, true) :: W
              · obtain ⟨W, hW⟩ := h0s
                exact Or.inr ((ih s1 hs1).f_pos_0s h1 hN11 (by omega) hW)
              · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
            | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
          obtain ⟨rfl, hG2', hSf⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
          exact Or.inr ⟨rfl, by omega, hG2', fun _ _ => hSf hGZ, by omega⟩
  · exact False.elim (hf11.1 (by omega))
  · exact False.elim (hf11.1 hrem2)

/-! ## Group 4: F(2* :: Y), F(2*, 1 :: Y), F(2*, 1, 1 :: Y), F(2*, 1, 1, 1 :: Y) -/

theorem bigD1_of_tightZero111 {s Δ2 : Nat} {R1 R_fin : List Seg}
    (hTZ : TightZero111 R1) (hD : BigD1 s R1 Δ2 R_fin) :
    Δ2 = 3 ∧ Good1Safe R_fin := by
  rcases hTZ.1 with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, hGF⟩ | ⟨Z, rfl, hT⟩
  · cases hD; exact ⟨rfl, good1Safe_of_1s_0s_0⟩
  · cases hD; exact ⟨rfl, good1Safe_of_1s_0s_0s Z⟩
  · cases hD
    rcases hTZ.2 Z rfl with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩
    · exact ⟨rfl, good1Safe_of_1s_0s_1_nil⟩
    · exact ⟨rfl, good1Safe_of_1s_0s_1_0s W⟩
    · exact ⟨rfl, good1Safe_of_1s_0s_1_1 W⟩
  · cases hD; exact ⟨rfl, good1Safe_of_1s_1_1_0s_1_1 Z⟩
  · cases hD; exact ⟨rfl, good1Safe_of_1s_1_1_1 hGF⟩
  · cases hD; exact ⟨rfl, good1Safe_of_2_1_1 hT⟩

theorem step_f2s {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((2, true) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    Δ ≠ 2 ∧ Δ ≠ 5 ∧
    (Δ = 0 → Safe0s R_fin) ∧
    (Δ = 3 → Head0s11 R_fin) ∧
    (Δ = 6 → Head0s11 R_fin ∨ Good1Safe R_fin) ∧
    (Δ = 9 → Head0s11 R_fin ∨ Strong2 R_fin) ∧
    (Δ = 12 → Head0s11 R_fin ∨ Good2 R_fin) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2s_inv h
  have hN1Y := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN1Y
  have hf1 := (ih s1 hs1).f1 h1 hN
  rcases hcases with ⟨hrem1, hge4, rfl, rfl⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, rfl, hD2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, rfl, hF2⟩
  · -- Δ1 ≡ 1 (mod 3), ≥ 4; hf1 gives Δ1 ≠ 4 so Δ1 ≥ 7
    refine ⟨by omega, by omega, ?_, by omega, by omega, by omega, by omega⟩
    intro _
    by_cases h7 : Δ1 = 7
    · subst h7
      rcases hf1.2.2.2.2.1 rfl with hH | hG1
      · exact ⟨R1, rfl, Or.inr (Or.inr (Or.inr (Or.inl hH)))⟩
      · exact ⟨R1, rfl, Or.inr (Or.inr (Or.inr (Or.inr hG1)))⟩
    · by_cases h10 : Δ1 = 10
      · subst h10
        have hGH : Good2 R1 ∨ Head0s11 R1 := by
          rcases hf1.2.2.2.2.2.1 rfl with hH | hG2
          · exact Or.inr hH
          · exact Or.inl hG2
        exact ⟨(1, false) :: R1, by simp [ones], Or.inr (Or.inr (Or.inl ⟨R1, rfl, hGH⟩))⟩
      · by_cases h13 : Δ1 = 13
        · subst h13
          have hGH : Good2 R1 ∨ Head0s11 R1 := by
            rcases hf1.2.2.2.2.2.2.1 rfl with hH | hG2
            · exact Or.inr hH
            · exact Or.inl hG2
          exact ⟨(1, false) :: (1, false) :: R1, by simp [ones], Or.inr (Or.inl ⟨R1, rfl, hGH⟩)⟩
        · have hge16 : 16 ≤ Δ1 := by omega
          have hq5 : Δ1 / 3 = (Δ1 / 3 - 5) + 5 := by omega
          rw [hq5]
          exact ⟨(1, false) :: (1, false) :: (1, false) :: (ones (Δ1 / 3 - 5) ++ R1),
              by simp [ones],
            Or.inl ⟨ones (Δ1 / 3 - 5) ++ R1, rfl⟩⟩
  · -- Δ1 = 2: R1 = 0*::1::1::U with GoodF2U U, bumpR^2 R1 = [2*, 1, 1 :: U], Δ = Δ3 + 2
    obtain ⟨U, rfl, hGFU⟩ := (ih s1 hs1).f_25_goodF2U h1 hN1Y (Or.inl rfl)
    have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF2
    rcases (ih s2 hs2).f2s_11 hF2' hNU with ⟨rfl, hG1⟩ | ⟨rfl, hS⟩ | rfl
    · exact ⟨by omega, by omega, by omega, by omega,
        fun _ => Or.inr (hG1 (goodF2U_to_goodZero111Head hGFU)), by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
                                                                fun _ => Or.inr (hS hGFU).1⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- Δ1 ≡ 2 (mod 3), ≥ 5: Δ = Δ3 + 2, hF2 : BigF s2 (3 :: ones (Δ1/3 - 1) ++ R1) Δ3 R_fin
    by_cases h5 : Δ1 = 5
    · subst h5
      obtain ⟨U, rfl, hSU⟩ := hf1.2.2.1 rfl
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2'
      rcases hSU with ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl⟩ | ⟨hG1, _⟩
      · obtain ⟨rfl, hG2', _⟩ :=
            (ih s4 (by omega)).f3_1111 hF4 (noNonlast0F_tail (noNonlast0F_tail hNU))
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr hG2'⟩
      · obtain ⟨rfl, hG2', _⟩ :=
            (ih s4 (by omega)).f3_1111 hF4 (noNonlast0F_tail (noNonlast0F_tail hNU))
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr hG2'⟩
      · obtain ⟨h710, hG2', _⟩ := (ih s4 (by omega)).f3_111 hF4 (noNonlast0F_tail hNU)
        rcases h710 with rfl | rfl
        · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr hG2'⟩
        · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · obtain ⟨rfl, rfl⟩ :=
            (bigFD_det _).1 _ _ _ _ _ _ hF4 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: (1,
            false) :: Z))
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
                                                                  fun _ =>
                                                                  Or.inr (good2_of_2_1_1 ((1,
                                                                  false) :: (1, false) :: Z))⟩
      · obtain ⟨rfl, hS'⟩ := (ih s4 (by omega)).good2_f311 (good1_to_good2 hG1) hF4 hNU
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr hS'.1⟩
    · by_cases h8 : Δ1 = 8
      · subst h8
        obtain ⟨U, rfl⟩ := (ih s1 hs1).f_258 h1 hN1Y (Or.inr (Or.inr rfl))
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2'
        obtain ⟨rfl, hG1'⟩ := (ih s4 (by omega)).f2s_111 hF4 hNU
        exact ⟨by omega, by omega, by omega, by omega, by omega,
          fun _ => Or.inr (good1Safe_to_strong2 hG1'), by omega⟩
      · by_cases h11 : Δ1 = 11
        · subst h11
          rcases (ih s1 hs1).f_11 h1 hN1Y with ⟨U, rfl⟩ | hS
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                false) :: (1, false) :: U) Δ3 R_fin := by
              simpa [ones] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            exact ⟨by omega, by omega, by omega, by omega, by omega,
              fun _ => Or.inr (strong2_of_2_1_1 ((1, false) :: U)), by omega⟩
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
            obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hS.1 hF2' hN1
            exact ⟨by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr hS', by omega⟩
        · by_cases h14 : Δ1 = 14
          · subst h14
            rcases hf1.2.2.2.2.2.2.2 rfl with ⟨U, rfl⟩ | hS
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0,
                  true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
                simpa [ones] using hF2
              obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_1_0s_1_1_exists U)
              exact ⟨by omega, by omega, by omega, by omega, by omega,
                fun _ => Or.inr (strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1,
                    false) :: U, rfl⟩))))),
                by omega⟩
            · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
                  false) :: R1) Δ3 R_fin := by
                simpa [ones] using hF2
              obtain ⟨rfl, _, hSf⟩ := (ih s2 hs2).good2_f3111 hS.1 hF2' hN1
              exact ⟨by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr (hSf hS),
                                                              by omega⟩
          · have hge17 : 17 ≤ Δ1 := by omega
            have hq4 : Δ1 / 3 - 1 = (Δ1 / 3 - 5) + 4 := by omega
            rw [hq4] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
            have hGZ : GoodZero111Head (ones (Δ1 / 3 - 5) ++ R1) := by
              cases hq : Δ1 / 3 - 5 with
              | zero =>
                simp only [ones, List.nil_append]
                by_cases h0s : ∃ W, R1 = (0, true) :: W
                · obtain ⟨W, hW⟩ := h0s
                  exact Or.inr ((ih s1 hs1).f_pos_0s h1 hN1Y (by omega) hW)
                · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
              | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
            obtain ⟨rfl, _, hSf⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
            exact ⟨by omega, by omega, by omega, by omega, by omega, fun _ => Or.inr (hSf hGZ),
                                                            by omega⟩
  · -- Δ1 = 0: R1 = 0* :: W -> BigD1 s2 (0* :: W) Δ2 R_fin gives Δ2 = 3, Δ = 4
    obtain ⟨W, rfl⟩ := bigF_oneF_zero_head h1
    cases hD2
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- Δ1 = 3: impossible by hf1.1
    exact False.elim (hf1.1 rfl)
  · -- Δ1 ≡ 0 (mod 3), ≥ 6: Δ = Δ3 + 3, hF2 : BigF s2 (3 :: ones (Δ1/3 - 2) ++ R1) Δ3 R_fin
    by_cases h6 : Δ1 = 6
    · subst h6
      obtain ⟨U, rfl⟩ := hf1.2.2.2.1 rfl
      have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
      have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2'
      rcases (ih s4 (by omega)).f3_11 hF4 hNU with rfl | rfl | ⟨rfl, _⟩
      · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inl (bigF_3_zero_prefix hF4),
                                              by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases h9 : Δ1 = 9
      · subst h9
        have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
        have hN_1R1 := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN1
        refine ⟨by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
        · intro h5; exact ((ih s2 hs2).f3_ne24 hF2' hN_1R1).1 (by omega)
        · intro h3
          have h0 : Δ3 = 0 := by omega
          subst h0; exact bigF_3_zero_prefix hF2'
        · intro h6
          have h3e : Δ3 = 3 := by omega
          subst h3e; exact Or.inl ((ih s2 hs2).f3_36 hF2' hN_1R1 (Or.inl rfl))
        · intro h9e
          have h6e : Δ3 = 6 := by omega
          subst h6e; exact False.elim ((ih s2 hs2).f3_1_ne6 hF2' hN1)
        · intro h12e
          have h9d : Δ3 = 9 := by omega
          subst h9d
          rcases (ih s2 hs2).f3_9 hF2' hN_1R1 with hH | hS
          · exact Or.inl hH
          · exact Or.inr hS.1
      · by_cases h12 : Δ1 = 12
        · subst h12
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
            simpa [ones] using hF2
          rcases (ih s2 hs2).f3_11 hF2' hN1 with rfl | rfl | ⟨rfl, _⟩
          · exact ⟨by omega, by omega, by omega, fun _ => bigF_3_zero_prefix hF2', by omega,
                by omega, by omega⟩
          · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
          · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
        · have hge15 : 15 ≤ Δ1 := by omega
          have hq3 : Δ1 / 3 - 2 = (Δ1 / 3 - 5) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
          obtain ⟨h710, _, _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          rcases h710 with rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega, by omega,
              by omega, by omega⟩

theorem step_f2s_1 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((2, true) :: (1, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    Δ = 0 ∨ Δ = 4 ∨ Δ = 10 ∨ Δ = 13 := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2s_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN))
  have hf11 := (ih s1 hs1).f11 h1 hN
  rcases hcases with ⟨_, _, rfl, _⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, _, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ2, rfl, hD2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, rfl, hF2⟩
  · exact Or.inl rfl
  · exact False.elim (hf11.1 (by omega))
  · exact False.elim (hf11.1 hrem2)
  · obtain ⟨W, rfl⟩ := bigF_oneF_zero_head h1
    cases hD2
    exact Or.inr (Or.inl rfl)
  · exact False.elim (hf11.2.1 rfl)
  · by_cases h6 : Δ1 = 6
    · exact False.elim (hf11.2.2.1 h6)
    · by_cases h9 : Δ1 = 9
      · subst h9
        have hG2 := hf11.2.2.2.2.1 (Or.inl ⟨rfl, by omega⟩)
        have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
        rcases ((ih s2 hs2).good2_f31 hG2 hF2' hN1).1 with rfl | ⟨rfl, _⟩
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · by_cases h12 : Δ1 = 12
        · subst h12
          have hG2 := hf11.2.2.2.2.1 (Or.inl ⟨rfl, by omega⟩)
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
          obtain ⟨rfl, _⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
          exact Or.inr (Or.inr (Or.inl rfl))
        · have hge15 : 15 ≤ Δ1 := by omega
          have hq3 : Δ1 / 3 - 2 = (Δ1 / 3 - 5) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
              (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
          obtain ⟨h710, _, _⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          rcases h710 with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))

theorem step_f2s_11 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((2, true) :: (1, false) :: (1, false) :: Y) Δ R_fin) (hN : NoNonlast0F Y) :
    (Δ = 4 ∧ (GoodZero111Head Y → Good1Safe R_fin)) ∨
    (Δ = 10 ∧ (GoodF2U Y → Strong2 R_fin)) ∨
    Δ = 13 := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2s_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)))
  have hf111 := (ih s1 hs1).f111 h1 hN
  rcases hcases with ⟨hrem1, _, _, _⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, _, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ2, rfl, hD2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, rfl, hF2⟩
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  · rcases hf111 with ⟨_, hZ, hTZ⟩ | ⟨_, hge, _, _, _⟩
    · have h0s : ∃ W, R1 = (0, true) :: W := by
        rcases hZ with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl,
            _⟩ <;> exact ⟨_, rfl⟩
      obtain ⟨W, rfl⟩ := h0s
      cases hD2
      exact Or.inl ⟨rfl, fun hGZ => (bigD1_of_tightZero111 (hTZ hGZ) (BigD1.zeroT W)).2⟩
    · omega
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨_, hge, _, _, _⟩ <;> omega
  · rcases hf111 with ⟨h0, _, _⟩ | ⟨_, hge9, hG2, hS9, hS12⟩
    · omega
    · by_cases h9 : Δ1 = 9
      · subst h9
        have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
        have ⟨h710, hSf⟩ := (ih s2 hs2).good2_f31 hG2 hF2' hN1
        rcases h710 with rfl | ⟨rfl, _⟩
        · exact Or.inr (Or.inl ⟨rfl, fun hGF => hSf (hS9 rfl hGF)⟩)
        · exact Or.inr (Or.inr rfl)
      · by_cases h12 : Δ1 = 12
        · subst h12
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
          obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
          exact Or.inr (Or.inl ⟨rfl, fun _ => hS'⟩)
        · by_cases h15 : Δ1 = 15
          · subst h15
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
                false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
            obtain ⟨rfl, _, _⟩ := (ih s2 hs2).good2_f3111 hG2 hF2' hN1
            -- Wait: Δ1 = 15 -> R1 is Good2, not necessarily Strong2! Check if f111(15) gives
            -- Strong2 or wait:
            -- In f111(15): Δ3 = 7, does 3,1,1,1::R1 give Strong2? YES! Look at f111(15): Δ1 = 15 in
            -- f111 came from Δ1' = 13 -> Δ3 = 10 -> f3_111(10) -> Strong2!!
            -- Wait: f111 has (Δ = 12 → Strong2), NOT 15! Check: Δ1 = 15 in f111 is IMPOSSIBLE?
            -- Let's check: in step_f111, rem1 gives Δ = Δ3 + 2 where Δ3 ∈ {7, 10}! So Δ ∈ {9, 12}
            -- ONLY!!
            exact Or.inr (Or.inl ⟨rfl, fun _ => by
              have hS15 : Strong2 R1 := by
                obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_1_inv h1
                rcases hca with ⟨_, h0, _⟩ | ⟨_, _, sb, hsb, Δb, haddb, hFb⟩ | ⟨rfl, _, _, _, _,
                    _⟩ | ⟨hrem2, _, _, _, _, _, _⟩
                · omega
                · have h13b : Δb = 13 := by omega
                  subst h13b
                  have hNa := (bigFD_noNonlast0F _).1 _ _ _ ha
                    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
                      (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN))
                  have hf11a := (ih sa (by omega)).f11 ha hN
                  by_cases h7a : Δa = 7
                  · subst h7a
                    have hG1a := hf11a.2.2.2.1 rfl
                    have hFb' : BigF sb ((3, false) :: (1, false) :: Ra) 13 R1 := by
                        simpa [ones] using hFb
                    rcases ((ih sb (by omega)).good2_f31 (good1Safe_to_good2 hG1a) hFb'
                        hNa).1 with h7 | ⟨h10, _⟩ <;> omega
                  · by_cases h10a : Δa = 10
                    · subst h10a
                      have hG2a := hf11a.2.2.2.2.1 (Or.inr rfl)
                      have hFb' : BigF sb ((3, false) :: (1, false) :: (1, false) :: Ra) 13 R1 := by
                          simpa [ones] using hFb
                      have h7 := ((ih sb (by omega)).good2_f311 hG2a hFb' hNa).1
                      omega
                    · have hne4 : Δa ≠ 4 :=
                          ((ih sa (by omega)).f1 ha (noNonlast0F_cons_ne0F (x := (1,
                          false)) (by simp) hN)).2.1
                      have hq3 : Δa / 3 - 1 = (Δa / 3 - 4) + 3 := by omega
                      rw [hq3] at hFb
                      have hFb' : BigF sb ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                          (ones (Δa / 3 - 4) ++ Ra)) 13 R1 := by simpa [ones] using hFb
                      obtain ⟨h710, _, _⟩ :=
                          (ih sb (by omega)).f3_111 hFb' (noNonlast0F_ones_append _ hNa)
                      omega
                · exact False.elim (((ih sa (by omega)).f11 ha hN).1 (by omega))
                · exact False.elim (((ih sa (by omega)).f11 ha hN).1 hrem2)
              exact ((ih s2 hs2).good2_f3111 hG2 hF2' hN1).2.2 hS15⟩)
          · have hge18 : 18 ≤ Δ1 := by omega
            have hq4 : Δ1 / 3 - 2 = (Δ1 / 3 - 6) + 4 := by omega
            rw [hq4] at hF2
            have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                false) ::
                (ones (Δ1 / 3 - 6) ++ R1)) Δ3 R_fin := by simpa [ones] using hF2
            have hGZ : GoodZero111Head (ones (Δ1 / 3 - 6) ++ R1) := by
              cases hq : Δ1 / 3 - 6 with
              | zero =>
                simp only [ones, List.nil_append]
                exact Or.inl (good2_ne_zeroT hG2)
              | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
            obtain ⟨rfl, _, hSf⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
            exact Or.inr (Or.inl ⟨rfl, fun _ => hSf hGZ⟩)

theorem step_f2s_111 {m : Nat} (ih : InvLt m)
    {Y : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF m ((2, true) :: (1, false) :: (1, false) :: (1, false) :: Y) Δ R_fin)
    (hN : NoNonlast0F Y) :
    Δ = 4 ∧ Good1Safe R_fin := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2s_inv h
  have h1_zero : Δ1 = 0 ∧ TightZero111 R1 := by
    cases h1 with
    | oneF_rem1 h0 hrem0 =>
      rename_i s0 R0 Δ0
      rcases (ih s0 (by omega)).f111 h0 hN with ⟨rfl, hZ, _⟩ | ⟨hm, hge9, hG2, _, _⟩
      · refine ⟨rfl, ?_⟩
        rcases hZ with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z, rfl, hT⟩
        · exact ⟨Or.inr (Or.inl ⟨[(0, false)], rfl⟩), fun _ hEq => by cases hEq⟩
        · exact ⟨Or.inr (Or.inl ⟨(0, true) :: Z, rfl⟩), fun _ hEq => by cases hEq⟩
        · exact ⟨Or.inr (Or.inl ⟨(1, false) :: Z, rfl⟩), fun _ hEq => by cases hEq⟩
        · exact ⟨Or.inr (Or.inr (Or.inl ⟨(1, false) :: (0, true) :: (1, false) :: (1, false) :: Z,
              rfl⟩)),
            fun _ hEq => by cases hEq; exact Or.inr (Or.inr ⟨(0, true) :: (1, false) :: (1,
                          false) :: Z, rfl⟩)⟩
        · exact ⟨Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1, false) :: Z, rfl⟩)),
            fun _ hEq => by cases hEq; exact Or.inr (Or.inr ⟨(1, false) :: Z, rfl⟩)⟩
        · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, rfl, goodTail_to_goodF2U hT⟩)))),
              fun _ hEq => by cases hEq⟩
      · refine ⟨rfl, ?_⟩
        have hq3 : (1 + Δ0) / 3 = ((1 + Δ0) / 3 - 3) + 3 := by omega
        rw [hq3]
        have hT := goodTail_ones_append ((1 + Δ0) / 3 - 3) (Or.inl hG2)
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ones ((1 + Δ0) / 3 - 3) ++ R0, rfl, hT⟩)))),
          fun _ hEq => by cases hEq⟩
    | oneF_rem2 h0 hrem0 _ =>
      rename_i s0 _ R0 _ Δ0
      rcases (ih s0 (by omega)).f111 h0 hN with ⟨h0e, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
    | oneF_rem0 h0 hrem0 _ =>
      rename_i s0 _ R0 _ Δ0 _
      rcases (ih s0 (by omega)).f111 h0 hN with ⟨h0e, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
  obtain ⟨rfl, hTZ⟩ := h1_zero
  rcases hcases with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _, _⟩ |
      ⟨_, s2, hs2, Δ2, rfl, hD2⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _, _⟩
  · omega
  · omega
  · omega
  · obtain ⟨rfl, hG1⟩ := bigD1_of_tightZero111 hTZ hD2
    exact ⟨rfl, hG1⟩
  · omega
  · omega


/-! ## Group 5 Helpers, Step Lemmas, and `invAt_all` -/


/-! ## Group 5 Helpers -/

/-- Unconditional under `ih`: `BigF s ((2, false) :: Y) 3 R_fin` always yields `0*::1::1::U` with
    `GoodF2U U`. -/
theorem bigF_2_3_goodF2U {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Y R_fin : List Seg} (h : BigF s ((2, false) :: Y) 3 R_fin) (hN : NoNonlast0F Y) :
    ∃ U, R_fin = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
  have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR hN)
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨rfl, _, _, Δ3, hadd, hF2⟩ |
      ⟨_, _, _, _, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, hadd, hD2⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)
  · have h2e : Δ2 = 2 := by omega
    subst h2e
    cases Y with
    | nil =>
      obtain ⟨_, hEx⟩ := bigF_2_nil_exists
      obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
      omega
    | cons x xs =>
      cases x with
      | mk dx bx =>
        obtain ⟨Z, rfl⟩ := bigF_ge2_zero_head h1
        cases hD2
  · have h0e : Δ3 = 0 := by omega
    subst h0e
    obtain ⟨Z, rfl⟩ := bigF_three_head h1
    have hF2' : BigF s2 ((2, true) :: (1, false) :: Z) 0 R_fin := by simpa [bumpR] using hF2
    obtain ⟨U, rfl, hSU⟩ := ((ih s2 (by omega)).f2s hF2' (noNonlast0F_tail hN1)).2.2.1 rfl
    exact ⟨U, rfl, safeU_to_goodF2U hSU⟩
  · have h0e : Δ3 = 0 := by omega
    subst h0e
    exact bigF_3_zero_goodF2U ih (by omega) hF2 (noNonlast0F_ones_append _ hN1)

/-- Unconditional under `ih`: `BigF s ((2, false) :: Y) 3 R_fin` always yields `Head0s11 R_fin`. -/
theorem bigF_2_3_head0s11 {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Y R_fin : List Seg} (h : BigF s ((2, false) :: Y) 3 R_fin) (hN : NoNonlast0F Y) :
    Head0s11 R_fin := by
  obtain ⟨U, rfl, _⟩ := bigF_2_3_goodF2U ih hs h hN
  exact ⟨U, rfl⟩

/-- `BigF s ((2, true) :: Z) 3 R1` always yields `0*::1::1::U` with `GoodF2U U`. -/
theorem bigF_2s_3_goodF2U {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Z R1 : List Seg} (h : BigF s ((2, true) :: Z) 3 R1) (hN : NoNonlast0F Z) :
    ∃ U, R1 = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
  obtain ⟨s1, hs1, Δ1, Ra, h1, hcases⟩ := bigF_2s_inv h
  have hN1 :=
      (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  have hf1 := (ih s1 (by omega)).f1 h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, hadd, hD2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)
  · obtain ⟨W, rfl⟩ := bigF_oneF_zero_head h1
    cases hD2; omega
  · exact False.elim (hf1.1 rfl)
  · have h0e : Δ3 = 0 := by omega
    subst h0e
    exact bigF_3_zero_goodF2U ih (by omega) hF2 (noNonlast0F_ones_append _ hN1)

/-- `GoodZero111Head X → BigF s (3 :: 1 :: 1 :: X) 7 R_fin → Good2 R_fin`. -/
theorem bigF_3_1_1_7_good2_of_gz {m s : Nat} (ih : InvLt m) (hs : s < m)
    {X R_fin : List Seg} (hGZ : GoodZero111Head X)
    (h : BigF s ((3, false) :: (1, false) :: (1, false) :: X) 7 R_fin) (hN : NoNonlast0F X) :
    Good2 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN11 := noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
    (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN11
  have hf11 := (ih s1 (by omega)).f11 h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨hrem2, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨hrem0, hge3, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · exact False.elim (hf11.1 hrem2)
  · have h4e : Δ3 = 4 := by omega
    subst h4e
    cases h1 with
    | oneF_rem1 h0f hrem0f =>
      rename_i s0 R0 Δ0'
      have hN0 :=
          (bigFD_noNonlast0F _).1 _ _ _ h0f (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
      by_cases h0z : Δ0' = 0
      · subst h0z
        cases h0f with
        | oneF_rem1 hx hremx =>
          rename_i sx Rx Δx
          by_cases hxz : Δx = 0
          · subst hxz
            rcases bigF_zero_head_3 hx hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
            · have hF2' : BigF s2 [(2, true), (0, true), (0, false)] 4 R_fin := by
                  simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(0, false)])
              exact Good2.c_2_0
            · have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: Z) 4 R_fin := by
                  simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: Z))
              exact good2_of_2_0s Z
            · have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: Z) 4 R_fin := by
                  simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((1, false) :: Z))
              rcases bigF_zero_oneF_head hx hN with ⟨_, rfl⟩ | rfl
              · exact Good2.c_2_1
              · rcases hGZ with hne0 | ⟨W, hW⟩
                · exact False.elim (hne0 Z rfl)
                · cases hW; exact good2_of_2_1_1 W
          · by_cases h3x : Δx = 3
            · subst h3x
              obtain ⟨W, rfl⟩ := bigF_three_head hx
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (0, true) :: (1,
                  false) :: W) 4 R_fin := by
                simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((1, false) :: (0,
                  true) :: (1, false) :: W))
              exact good2_of_2_1_0s ((1, false) :: W)
            · have hge6 : 6 ≤ Δx := by omega
              have hq2 : (1 + Δx) / 3 = ((1 + Δx) / 3 - 2) + 2 := by omega
              rw [hq2] at hF2
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1,
                  false) :: (ones ((1 + Δx) / 3 - 2) ++ Rx)) 4 R_fin := by
                simpa [ones, bumpR] using hF2
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
                (bigF_2s_0s_full_exists ((1, false) :: (1,
                    false) :: (ones ((1 + Δx) / 3 - 2) ++ Rx)))
              exact good2_of_2_1_1 (ones ((1 + Δx) / 3 - 2) ++ Rx)
        | oneF_rem2 hx _ hx2 =>
          have hge := bigD1_ge2_of_ne_nil hx2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hx))
          omega
      · have hne3 := ((ih s0 (by omega)).f1 h0f hN).1
        by_cases h6 : Δ0' = 6
        · subst h6
          obtain ⟨U, rfl⟩ := ((ih s0 (by omega)).f1 h0f hN).2.2.2.1 rfl
          have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (0, true) :: (1,
              false) :: (1, false) :: U) 4 R_fin := by
            simpa [ones, bumpR] using hF2
          obtain ⟨_, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_1_1_0s_exists ((1, false) :: (1,
              false) :: U))
          exact good1Safe_to_good2 (good1Safe_of_1s_0s_1_1 ((1, false) :: U))
        · have hge9 : 9 ≤ Δ0' := by omega
          have hq3 : (1 + Δ0') / 3 = ((1 + Δ0') / 3 - 3) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1,
              false) :: (ones ((1 + Δ0') / 3 - 3) ++ R0)) 4 R_fin := by
            simpa [ones, bumpR] using hF2
          exact good1Safe_to_good2
              ((ih s2 (by omega)).f2s_111 hF2' (noNonlast0F_ones_append _ hN0)).2
    | oneF_rem2 h0f _ h02 =>
      have hge := bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))
      omega
  · have h4e : Δ3 = 4 := by omega
    subst h4e
    have hge9 : 9 ≤ Δ0 := by omega
    have hG2 := hf11.2.2.2.2.1 (Or.inl ⟨hrem0, hge9⟩)
    by_cases h9 : Δ0 = 9
    · subst h9
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) 4 R_fin := by
          simpa [ones] using hF2
      have h7 := ((ih s2 (by omega)).good2_f311 hG2 hF2' hN1).1
      omega
    · by_cases h12 : Δ0 = 12
      · subst h12
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: R1) 4 R_fin :=
            by simpa [ones] using hF2
        have h7 := ((ih s2 (by omega)).good2_f3111 hG2 hF2' hN1).1
        omega
      · have hge15 : 15 ≤ Δ0 := by omega
        have hq4 : Δ0 / 3 - 1 = (Δ0 / 3 - 5) + 4 := by omega
        rw [hq4] at hF2
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) ::
            (ones (Δ0 / 3 - 5) ++ R1)) 4 R_fin := by simpa [ones] using hF2
        have h7 := ((ih s2 (by omega)).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)).1
        omega

/-- `Good2 G → BigF s ((2, true) :: G) Δ R_fin` returns `(Δ = 4 ∧ (Good2 ∨ 1*::_)) ∨ Δ = 10 ∨ Δ =
    13`. -/
theorem bigF_2s_good2 {m s : Nat} (ih : InvLt m) (hs : s < m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF s ((2, true) :: G) Δ R_fin) (hN : NoNonlast0F G) :
    (Δ = 4 ∧ (Good2 R_fin ∨ ∃ W, R_fin = (1, true) :: W)) ∨ Δ = 10 ∨ Δ = 13 := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2s_inv h
  have hN1 :=
      (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  have hf1 := (ih s1 (by omega)).good2_f1 hG h1 hN
  rcases hcases with ⟨hrem1, _, _, _⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, _, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ2, rfl, hD2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, rfl, hF2⟩
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · cases h1 with
    | oneF_rem1 hg hremg =>
      rename_i sg Rg Δg
      cases hD2
      by_cases h0g : Δg = 0
      · subst h0g
        have hRg0s : ∃ W, Rg = (0, true) :: W := by
          cases hG with
          | of_good1 h1g =>
            rcases h1g with rfl | ⟨_, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl,
                _⟩ | ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · cases hg; exact ⟨_, rfl⟩
            · obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head hg; exact ⟨_, hZ⟩
          | _ => obtain ⟨Z, hZ⟩ := bigF_ge2_zero_head hg; exact ⟨_, hZ⟩
        obtain ⟨W, rfl⟩ := hRg0s
        exact Or.inl ⟨rfl, Or.inr ⟨W, by simp [ones, bumpR]⟩⟩
      · by_cases h3g : Δg = 3
        · subst h3g
          obtain ⟨W, rfl⟩ := bigF_three_head hg
          exact Or.inl ⟨rfl, Or.inl (good2_of_2_0s ((1, false) :: W))⟩
        · by_cases h6g : Δg = 6
          · subst h6g
            obtain ⟨U, rfl⟩ := ((ih sg (by omega)).good2_f hG hg hN).2.2.1 rfl
            exact Or.inl ⟨rfl, Or.inl (good2_of_2_1_0s ((1, false) :: (1, false) :: U))⟩
          · have hge9 : 9 ≤ Δg := by omega
            have hq3 : (1 + Δg) / 3 = ((1 + Δg) / 3 - 3) + 3 := by omega
            rw [hq3]
            exact Or.inl ⟨rfl, Or.inl (good2_of_2_1_1 (ones ((1 + Δg) / 3 - 3) ++ Rg))⟩
    | oneF_rem2 hg _ hg2 =>
      have hge := bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))
      omega
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · rcases hf1 with h0 | ⟨rfl, hG2⟩ | ⟨rfl, hS2⟩ | ⟨_, hge15⟩
    · omega
    · have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
      rcases ((ih s2 (by omega)).good2_f31 hG2 hF2' hN1).1 with rfl | ⟨rfl, _⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
          simpa [ones] using hF2
      obtain ⟨rfl, _⟩ := (ih s2 (by omega)).good2_f311 hS2.1 hF2' hN1
      exact Or.inr (Or.inl rfl)
    · have hq3 : Δ1 / 3 - 2 = (Δ1 / 3 - 5) + 3 := by omega
      rw [hq3] at hF2
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
          false) :: (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by
        simpa [ones] using hF2
      obtain ⟨h710, _, _⟩ := (ih s2 (by omega)).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
      rcases h710 with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- `Good1Safe R → BigF s ((3, false) :: R) Δ R_fin` returns `(Δ = 7 ∧ (Good2 ∨ 1*::_)) ∨ (Δ % 3 = 1
    ∧ 13 ≤ Δ)`. -/
theorem bigF_3_good1Safe {m s : Nat} (ih : InvLt m) (hs : s < m)
    {R : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG1 : Good1Safe R) (h : BigF s ((3, false) :: R) Δ R_fin) (hN : NoNonlast0F R) :
    (Δ = 7 ∧ (Good2 R_fin ∨ ∃ W, R_fin = (1, true) :: W)) ∨ (Δ % 3 = 1 ∧ 13 ≤ Δ) := by
  rcases hG1.1 with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl,
      hGF⟩ | ⟨Z, rfl⟩
  · -- [1*, 0*, 0]
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 [(2, true), (1, true), (0, false)] Δ4 R_fin := by simpa [bumpR] using hF4
    have hEx : BigF 2 [(2, true), (1, true), (0, false)] 4 [(1, true), (1, false)] :=
      BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT [(0, false)]) rfl) rfl (BigD1.zeroT [(0, true), (1,
          false)])
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' hEx
    exact Or.inl ⟨rfl, Or.inr ⟨[(1, false)], rfl⟩⟩
  · -- 1*, 0*, 0* :: Z
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 ((2, true) :: (1, true) :: (0, true) :: Z) Δ4 R_fin := by
        simpa [bumpR] using hF4
    have hEx : BigF 2 ((2, true) :: (1, true) :: (0, true) :: Z) 4 ((1, true) :: (1, true) :: Z) :=
      BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT ((0, true) :: Z)) rfl) rfl (BigD1.zeroT ((0,
          true) :: (1, true) :: Z))
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' hEx
    exact Or.inl ⟨rfl, Or.inr ⟨(1, true) :: Z, rfl⟩⟩
  · -- [1*, 0*, 1]
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 [(2, true), (1, true), (1, false)] Δ4 R_fin := by simpa [bumpR] using hF4
    have hEx : BigF 2 [(2, true), (1, true), (1, false)] 4 [(1, true), (2, false)] :=
      BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT [(1, false)]) rfl) rfl (BigD1.zeroT [(0, true), (2,
          false)])
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' hEx
    exact Or.inl ⟨rfl, Or.inr ⟨[(2, false)], rfl⟩⟩
  · -- [1*, 0*, 1, 0]
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 [(2, true), (1, true), (1, false), (0, false)] Δ4 R_fin := by
        simpa [bumpR] using hF4
    have hEx : BigF 2 [(2, true), (1, true), (1, false), (0, false)] 4 [(1, true), (2, false), (0,
        false)] :=
      BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT [(1, false), (0, false)]) rfl) rfl (BigD1.zeroT [(0,
          true), (2, false), (0, false)])
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' hEx
    exact Or.inl ⟨rfl, Or.inr ⟨[(2, false), (0, false)], rfl⟩⟩
  · -- 1*, 0*, 1, 0* :: Z
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 ((2, true) :: (1, true) :: (1, false) :: (0, true) :: Z) Δ4 R_fin := by
        simpa [bumpR] using hF4
    have hEx : BigF 2 ((2, true) :: (1, true) :: (1, false) :: (0, true) :: Z) 4 ((1, true) :: (2,
        false) :: (0, true) :: Z) :=
      BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT ((1, false) :: (0, true) :: Z)) rfl) rfl
        (BigD1.zeroT ((0, true) :: (2, false) :: (0, true) :: Z))
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' hEx
    exact Or.inl ⟨rfl, Or.inr ⟨(2, false) :: (0, true) :: Z, rfl⟩⟩
  · -- 1*, 0*, 1, 1 :: Z
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 ((2, true) :: (1, true) :: (1, false) :: (1, false) :: Z) Δ4 R_fin := by
        simpa [bumpR] using hF4
    have hEx : BigF 2 ((2, true) :: (1, true) :: (1, false) :: (1, false) :: Z) 4 ((1, true) :: (2,
        false) :: (1, false) :: Z) :=
      BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT ((1, false) :: (1, false) :: Z)) rfl) rfl
        (BigD1.zeroT ((0, true) :: (2, false) :: (1, false) :: Z))
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4' hEx
    exact Or.inl ⟨rfl, Or.inr ⟨(2, false) :: (1, false) :: Z, rfl⟩⟩
  · -- 1*, 1, 1, 0*, 1, 1 :: Z -> bumpR = 2, 1, 0*, 1, 1 :: Z ∈ Good2!
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 ((2, true) :: (2, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
        false) :: Z) Δ4 R_fin := by
      simpa [bumpR] using hF4
    rcases bigF_2s_good2 ih (by omega) (good2_of_2_1_0s ((1, false) :: (1, false) :: Z)) hF4'
        (noNonlast0F_bumpR (noNonlast0F_tail hN)) with ⟨rfl, hO⟩ | rfl | rfl
    · exact Or.inl ⟨rfl, hO⟩
    · exact Or.inr ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
  · -- 1*, 1, 1, 1 :: Z -> bumpR = 2, 1, 1 :: Z ∈ Good2!
    obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1s_inv h
    have hF4' : BigF s4 ((2, true) :: (2, false) :: (1, false) :: (1, false) :: Z) Δ4 R_fin := by
      simpa [bumpR] using hF4
    rcases bigF_2s_good2 ih (by omega) (good2_of_2_1_1 Z) hF4'
        (noNonlast0F_bumpR (noNonlast0F_tail hN)) with ⟨rfl, hO⟩ | rfl | rfl
    · exact Or.inl ⟨rfl, hO⟩
    · exact Or.inr ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
  · -- 2, 1, 1 :: Z with GoodTail Z
    have hT : GoodTail Z := hG1.2 Z rfl
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))
    obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
    -- Compute BigF s1 (2, 1, 1 :: Z) Δ0 R1 via bigF_2_inv -> BigF (3, 1 :: Z)
    obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv h1
    have ha' : BigF sa ((3, false) :: (1, false) :: Z) Δa Ra := by simpa [bumpR] using ha
    have hNa := (bigFD_noNonlast0F _).1 _ _ _ ha'
      (noNonlast0F_cons_ne0F (x := (3, false)) (by simp)
        (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ))
    have hΔa : Δa = 7 ∨ Δa = 10 := by
      rcases hT with hG | ⟨U, rfl⟩ | ⟨W, rfl, hW⟩ | ⟨W, rfl⟩
      · rcases ((ih sa (by omega)).good2_f31 hG ha' hNZ).1 with rfl | ⟨rfl, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv ha'
        obtain ⟨rfl, _⟩ :=
            (ih s4 (by omega)).f2s_111 hF4
            (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNZ)))
        exact Or.inl rfl
      · rcases hW with hG | ⟨U, rfl⟩
        · exact Or.inl ((ih sa (by omega)).good2_f311 hG ha' (noNonlast0F_tail hNZ)).1
        · obtain ⟨rfl, _⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ ha' (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))
          exact Or.inl rfl
      · exact ((ih sa (by omega)).f3_111 ha' (noNonlast0F_tail (noNonlast0F_tail hNZ))).1
    have hΔ0 : Δ0 = 0 ∧ ((Δa = 7 ∧ R1 = (0, true) :: (1, false) :: (1, false) :: Ra) ∨
        (Δa = 10 ∧ R1 = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Ra)) := by
      rcases hca with ⟨_, _, rfl, rfl⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
          ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩
      · rcases hΔa with rfl | rfl
        · exact ⟨rfl, Or.inl ⟨rfl, by simp [ones]⟩⟩
        · exact ⟨rfl, Or.inr ⟨rfl, by simp [ones]⟩⟩
      · rcases hΔa with rfl | rfl <;> omega
      · rcases hΔa with rfl | rfl <;> omega
      · rcases hΔa with rfl | rfl <;> omega
      · rcases hΔa with rfl | rfl <;> omega
      · rcases hΔa with rfl | rfl <;> omega
    obtain ⟨rfl, hR1⟩ := hΔ0
    rcases hcases with ⟨hrem, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
        ⟨_, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, hge, _, _, _, _, _⟩
    · omega
    · omega
    · rcases hR1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: Ra) Δ3 R_fin := by
            simpa [bumpR] using hF2
        have hGZ : GoodZero111Head Ra := by
          by_cases h0s : ∃ W, Ra = (0, true) :: W
          · obtain ⟨W, hW⟩ := h0s
            exact Or.inr ((ih sa (by omega)).f_pos_0s ha'
              (noNonlast0F_cons_ne0F (x := (3, false)) (by simp)
                (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)) (by omega) hW)
          · exact Or.inl (fun Z' hZ' => h0s ⟨Z', hZ'⟩)
        rcases (ih s2 (by omega)).f2s_11 hF2' hNa with ⟨rfl, hG1f⟩ | ⟨rfl, _⟩ | rfl
        · exact Or.inl ⟨rfl, Or.inl (good1Safe_to_good2 (hG1f hGZ))⟩
        · exact Or.inr ⟨rfl, by omega⟩
        · exact Or.inr ⟨rfl, by omega⟩
      · have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) :: Ra) Δ3 R_fin :=
            by
          simpa [bumpR] using hF2
        obtain ⟨rfl, hG1f⟩ := (ih s2 (by omega)).f2s_111 hF2' hNa
        exact Or.inl ⟨rfl, Or.inl (good1Safe_to_good2 hG1f)⟩
    · omega

/-- `SafeU U → BigF s ((3, false) :: U) Δ R_fin` always has `Δ % 3 = 1 ∧ 7 ≤ Δ`. -/
theorem bigF_3_safeU {m s : Nat} (ih : InvLt m) (hs : s < m)
    {U : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hSU : SafeU U) (h : BigF s ((3, false) :: U) Δ R_fin) (hN : NoNonlast0F U) :
    Δ % 3 = 1 ∧ 7 ≤ Δ := by
  rcases hSU with ⟨Z, rfl⟩ | ⟨Z, rfl, hZ⟩ | ⟨Z, rfl, hZ⟩ | ⟨Z, rfl⟩ | hG1
  · obtain ⟨h710, _, _⟩ :=
        (ih s hs).f3_111 h (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))
    rcases h710 with rfl | rfl <;> exact ⟨rfl, by omega⟩
  · rcases hZ with hG | ⟨W, rfl⟩
    · obtain ⟨rfl, _⟩ := (ih s hs).good2_f311 hG h (noNonlast0F_tail (noNonlast0F_tail hN))
      exact ⟨rfl, by omega⟩
    · obtain ⟨rfl, _⟩ :=
          (bigFD_det _).1 _ _ _ _ _ _ h (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: W))
      exact ⟨rfl, by omega⟩
  · rcases hZ with hG | ⟨W, rfl⟩
    · rcases ((ih s hs).good2_f31 hG h (noNonlast0F_tail hN)).1 with rfl | ⟨rfl, _⟩ <;> exact ⟨rfl,
          by omega⟩
    · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv h
      obtain ⟨rfl, _⟩ :=
          (ih s4 (by omega)).f2s_111 hF4
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))
      exact ⟨rfl, by omega⟩
  · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv h
    obtain ⟨h710, _, _⟩ :=
        (ih s4 (by omega)).f3_111 hF4
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))
    rcases h710 with rfl | rfl <;> exact ⟨rfl, by omega⟩
  · rcases bigF_3_good1Safe ih hs hG1 h hN with ⟨rfl, _⟩ | ⟨hm, hge⟩
    · exact ⟨rfl, by omega⟩
    · exact ⟨hm, by omega⟩

/-- `BigF s ((3, false) :: (2, false) :: (1, false) :: U) Δ R_fin` given `BigF (3 :: U)` has `Δ1 % 3
    = 1 ∧ 7 ≤ Δ1`. -/
theorem bigF_3_2_1_of_3_mod1_ge7 {m s : Nat} (ih : InvLt m) (hs : s < m)
    {U : List Seg} {Δ : Nat} {R_fin : List Seg}
    (h : BigF s ((3, false) :: (2, false) :: (1, false) :: U) Δ R_fin)
    (hN : NoNonlast0F U)
    (h3U : ∀ {sa Δa Ra}, sa < s → BigF sa ((3, false) :: U) Δa Ra → Δa % 3 = 1 ∧ 7 ≤ Δa) :
    (Δ = 7 ∧ Good2 R_fin) ∨ (Δ % 3 = 1 ∧ 13 ≤ Δ) := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv h1
  have ha' : BigF sa ((3, false) :: U) Δa Ra := by simpa [bumpR] using ha
  have hNa :=
      (bigFD_noNonlast0F _).1 _ _ _ ha' (noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN)
  obtain ⟨hrema, hge7a⟩ := h3U (by omega) ha'
  have hΔ0 : Δ0 = 0 ∧ R1 = (0, true) :: ones (Δa / 3) ++ Ra := by
    rcases hca with ⟨_, _, rfl, rfl⟩ | ⟨h2, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
        ⟨h0, _, _, _, _, _⟩ | ⟨h3, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩
    · exact ⟨rfl, rfl⟩
    · omega
    · omega
    · omega
    · omega
    · omega
  obtain ⟨rfl, rfl⟩ := hΔ0
  rcases hcases with ⟨hrem, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨_, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, hge, _, _, _, _, _⟩
  · omega
  · omega
  · by_cases h7a : Δa = 7
    · subst h7a
      have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: Ra) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
      have hGZ : GoodZero111Head Ra := by
        by_cases h0s : ∃ W, Ra = (0, true) :: W
        · obtain ⟨W, hW⟩ := h0s
          exact Or.inr ((ih sa (by omega)).f_pos_0s ha' (noNonlast0F_cons_ne0F (x := (3,
              false)) (by simp) hN) (by omega) hW)
        · exact Or.inl (fun Z' hZ' => h0s ⟨Z', hZ'⟩)
      rcases (ih s2 (by omega)).f2s_11 hF2' hNa with ⟨rfl, hG1⟩ | ⟨rfl, _⟩ | rfl
      · exact Or.inl ⟨rfl, good1Safe_to_good2 (hG1 hGZ)⟩
      · exact Or.inr ⟨rfl, by omega⟩
      · exact Or.inr ⟨rfl, by omega⟩
    · have hge10 : 10 ≤ Δa := by omega
      have hq3 : Δa / 3 = (Δa / 3 - 3) + 3 := by omega
      rw [hq3] at hF2
      have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1,
          false) :: (ones (Δa / 3 - 3) ++ Ra)) Δ3 R_fin := by
        simpa [ones, bumpR] using hF2
      obtain ⟨rfl, hG1⟩ := (ih s2 (by omega)).f2s_111 hF2' (noNonlast0F_ones_append _ hNa)
      exact Or.inl ⟨rfl, good1Safe_to_good2 hG1⟩
  · omega

/-- `Good4Out Z → BigF s ((3, false) :: Z) Δ R_fin` returns `(Δ = 7 ∧ Good2 R_fin) ∨ (Δ % 3 = 1 ∧ 13
    ≤ Δ)`. -/
theorem bigF_3_good4Out {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Z : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hZ : Good4Out Z) (h : BigF s ((3, false) :: Z) Δ R_fin) (hN : NoNonlast0F Z) :
    (Δ = 7 ∧ Good2 R_fin) ∨ (Δ % 3 = 1 ∧ 13 ≤ Δ) := by
  induction hZ generalizing s Δ R_fin with
  | two_one_one =>
    refine bigF_3_2_1_of_3_mod1_ge7 ih hs h trivial (fun hlt ha => ?_)
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ ha bigF_3_1_nil_exists
    exact ⟨rfl, by omega⟩
  | of_1_1_1s W =>
    have hNW :=
        noNonlast0F_tail
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))
    refine bigF_3_2_1_of_3_mod1_ge7 ih hs h (noNonlast0F_tail (noNonlast0F_tail hN)) (fun hlt ha =>
        ?_)
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ ha (bigF_3_1_1_1s_exists W)
    exact ⟨rfl, by omega⟩
  | of_safeU hSU =>
    have hNU := noNonlast0F_tail (noNonlast0F_tail hN)
    exact bigF_3_2_1_of_3_mod1_ge7 ih hs h hNU (fun hlt ha => bigF_3_safeU ih (by omega) hSU ha hNU)
  | step_21 hZ' ihZ =>
    have hNZ' := noNonlast0F_tail (noNonlast0F_tail hN)
    refine bigF_3_2_1_of_3_mod1_ge7 ih hs h hNZ' (fun hlt ha => ?_)
    rcases ihZ (by omega) ha hNZ' with ⟨rfl, _⟩ | ⟨hm, hge⟩
    · exact ⟨rfl, by omega⟩
    · exact ⟨hm, by omega⟩

/-- `GoodStrongHead U → BigF s ((2, true) :: U) 4 R_2s → Good2 (2 :: 1 :: R_2s)`. -/
theorem bigF_2s_4_good2_of_strongHead {m s : Nat} (ih : InvLt m) (hs : s < m)
    {U R_2s : List Seg} (hU : GoodStrongHead U)
    (h : BigF s ((2, true) :: U) 4 R_2s) (hN : NoNonlast0F U) :
    Good2 ((2, false) :: (1, false) :: R_2s) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2s_inv h
  have hN1 :=
      (bigFD_noNonlast0F _).1 _ _ _ h1 (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
  have hf1 := (ih s1 (by omega)).f1 h1 hN
  rcases hcases with ⟨_, _, h0, _⟩ |
      ⟨rfl, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, hadd, hD2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨_, _, s2, hs2, Δ3, hadd, hF2⟩
  · omega
  · obtain ⟨U', rfl⟩ :=
        (ih s1 (by omega)).f_258 h1 (noNonlast0F_cons_ne0F (x := (1,
        false)) (by simp) hN) (Or.inl rfl)
    have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U') Δ3 R_2s := by
        simpa [bumpR] using hF2
    rcases (ih s2 (by omega)).f2s_11 hF2'
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) with ⟨h4, _⟩ | ⟨h10,
        _⟩ | h13 <;> omega
  · exact False.elim (((ih s2 (by omega)).f3_ne24 hF2 (noNonlast0F_ones_append _ hN1)).1 (by omega))
  · cases h1 with
    | oneF_rem1 hu hremu =>
      rename_i su Ru Δu
      cases hD2
      by_cases h0u : Δu = 0
      · subst h0u
        rcases bigF_zero_head_3 hu hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
        · simpa [ones, bumpR] using Good2.c_2_1_1 []
        · simpa [ones, bumpR] using Good2.c_2_1_1s Z
        · rcases bigF_zero_oneF_head hu hN with ⟨_, rfl⟩ | rfl
          · simpa [ones, bumpR] using Good2.c_2_1_2
          · rcases hU with hE | hE | ⟨W, hE, hW⟩ | ⟨_, hE⟩ | ⟨_, hE⟩ | hG
            · cases hE
            · cases hE
            · cases hE
              rcases hW with rfl | hG2
              · simpa [ones, bumpR] using Good2.c_2_1_2
              · simpa [ones, bumpR] using Good2.step_21 hG2
            · cases hE
            · cases hE
            · exact False.elim (good2_ne_zeroT hG Z rfl)
      · by_cases h3u : Δu = 3
        · subst h3u
          obtain ⟨Z, rfl⟩ := bigF_three_head hu
          simpa [ones, bumpR] using Good2.step_21 (Good2.c_2_0s ((1, false) :: Z))
        · by_cases h6u : Δu = 6
          · subst h6u
            have hRu : Good2 Ru ∨ Head0s11 Ru := by
              rcases hU with rfl | rfl | ⟨W, rfl, _⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩ | hG
              · cases hu
              · cases hu
              · cases hu
              · exact Or.inr (((ih su (by omega)).f1 hu (noNonlast0F_tail hN)).2.2.2.1 rfl)
              · cases hu
              · exact Or.inr (((ih su (by omega)).good2_f hG hu hN).2.2.1 rfl)
            rcases hRu with hG2 | ⟨V, rfl⟩
            · simpa [ones, bumpR] using Good2.step_21 (Good2.step_21 hG2)
            · simpa [ones, bumpR] using Good2.step_21 (Good2.c_2_1_0s ((1, false) :: (1,
                  false) :: V))
          · have hge9 : 9 ≤ Δu := by omega
            have hq3 : (1 + Δu) / 3 = ((1 + Δu) / 3 - 3) + 3 := by omega
            rw [hq3]
            simpa [ones, bumpR] using Good2.step_21 (Good2.c_2_1_1 (ones ((1 + Δu) / 3 - 3) ++ Ru))
    | oneF_rem2 hu _ hu2 =>
      have hge := bigD1_ge2_of_ne_nil hu2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hu))
      omega
  · exact False.elim (hf1.1 rfl)
  · have h1e : Δ3 = 1 := by omega
    subst h1e; exact False.elim (bigF_ne_one hF2)

/-- `BigF s ((4, false) :: Y) 4 R_fin` is impossible under `ih : InvLt m`. -/
theorem bigF_4_ne4 {m s : Nat} (ih : InvLt m) (hs : s < m)
    {Y R_fin : List Seg} (h : BigF s ((4, false) :: Y) 4 R_fin) (hN : NoNonlast0F Y) : False := by
  cases h with
  | ge3_rem2 h1 hrem h2 =>
    rename_i s1 s2 R1 Δ1
    have hN1 := (bigFD_noNonlast0F _).2 _ _ _ h1 hN
    cases h2 with
    | oneF hF =>
      rename_i s3
      cases hq : Δ1 / 3 with
      | zero =>
        have h2e : Δ1 = 2 := by omega
        subst h2e
        rcases bigD1_two_head_nnf h1 hN with rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩
        · have hF' : BigF s3 [(2, true), (0, false)] 2 R_fin := by simpa [hq, ones, bumpR] using hF
          obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' bigF_2s_0_exists
          omega
        · have hF' : BigF s3 ((2, true) :: (0, true) :: Z) 2 R_fin := by
              simpa [hq, ones, bumpR] using hF
          obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_2s_0s_full_exists Z)
          omega
        · have hF' : BigF s3 ((2, true) :: (1, false) :: Z) 2 R_fin := by
              simpa [hq, ones, bumpR] using hF
          rcases (ih s3 (by omega)).f2s_1 hF'
              (noNonlast0F_tail (noNonlast0F_tail hN1)) with h0 | h4 | h10 | h13 <;> omega
      | succ q' =>
        have hF' : BigF s3 ((3, false) :: (ones q' ++ R1)) 2 R_fin := by
            simpa [hq, ones, bumpR] using hF
        exact ((ih s3 (by omega)).f3_ne24 hF' (noNonlast0F_ones_append q' hN1)).1 rfl
  | ge3_rem0 h1 hrem h2 =>
    rename_i s1 s2 R1 Δ1
    have hge2 := bigD1_ge2_of_ne_nil h1 (by simp)
    have hq1 : 1 ≤ Δ1 / 3 := by omega
    obtain ⟨q', hq⟩ : ∃ q', Δ1 / 3 = q' + 1 := ⟨Δ1 / 3 - 1, by omega⟩
    rw [hq] at h2
    cases h2 with
    | oneF hF =>
      exact bigF_ne_one hF


/-! ## Group 5 Step Lemmas (`step_good2_*`, `step_good1_f3121`) + `invAt_all` -/


-- Concrete finite boundary witnesses for `Good2`
theorem bigF_2_1_nil_exists :
    ∃ s, BigF s [(2, false), (1, false)] 0 [(0, true), (1, false), (1, false), (1, false)] := by
  obtain ⟨s3, h3⟩ := bigF_3_nil_exists
  exact ⟨_, BigF.twoF_rem1 (Y := [(1, false)]) h3 rfl⟩

theorem bigF_3_2_nil_exists :
    ∃ s, BigF s [(3, false), (2, false)] 0 [(0, true), (1, false), (1, false), (1, false)] := by
  obtain ⟨s2, h2⟩ := bigF_2_nil_exists
  exact ⟨_, BigF.ge3_rem1 (d := 0) (b := false) (Y := [(2, false)]) (BigD1.zeroF h2) rfl⟩

theorem bigF_2_1_2_exists :
    ∃ s, BigF s [(2, false), (1, false), (2, false)] 4 [(2, false), (1, false), (1, false)] := by
  obtain ⟨s32, h32⟩ := bigF_3_2_nil_exists
  exact ⟨_, BigF.twoF_rem0 (Y := [(1, false), (2, false)]) h32 rfl
    (BigD1.zeroT [(1, false), (1, false), (1, false)])⟩

theorem bigF_4_nil_exists :
    ∃ s, BigF s [(4, false)] 6 [(2, false)] := by
  have h1 : BigD1 2 [(1, false)] 2 [(0, true), (0, false)] :=
    BigD1.oneF (BigF.oneF_rem1 BigF.nil rfl)
  exact ⟨_, BigF.ge3_rem2 (d := 1) (b := false) (Y := []) h1 rfl (BigD1.oneF bigF_2s_0_exists)⟩

theorem bigF_2_1s_1_exists :
    ∃ s, ∃ R, BigF s [(2, false), (1, true), (1, false)] 13 R := by
  obtain ⟨s4, h4⟩ := bigF_4_nil_exists
  have h3s1 : BigF (0 + (s4 + 1) + 1) [(3, true), (1, false)] 9 [(2, false)] :=
    BigF.ge3_rem0 (d := 0) (b := true) (Y := [(1, false)]) (BigD1.zeroT [(1,
        false)]) rfl (BigD1.oneF h4)
  -- BigF [3, 1, 2]: BigF [1, 2] = 2 + BigF [3, 1] = 9, so BigF [3, 1, 2] = 3 + BigF [3, 1, 1, 2] =
  -- 10!
  obtain ⟨s2, h2⟩ := bigF_2_nil_exists
  have h12 : BigF (s2 + (6 + 1) + 1) [(1, false), (2, false)] 9 [(2, false)] :=
    BigF.oneF_rem2 h2 rfl (BigD1.oneF bigF_3_1_nil_exists)
  have h112 : BigF ((s2 + (6 + 1) + 1) + 1) [(1, false), (1, false), (2, false)] 0
      [(0, true), (1, false), (1, false), (1, false), (2, false)] :=
    BigF.oneF_rem1 h12 rfl
  -- BigF [3, 1, 1, 2] = 3 + BigF [2*, 1, 1, 1, 2] = 7
  have h1112 : BigF (((s2 + (6 + 1) + 1) + 1) + 1) [(1, false), (1, false), (1, false), (2,
      false)] 0
      [(0, true), (0, true), (1, false), (1, false), (1, false), (2, false)] :=
    BigF.oneF_rem1 h112 rfl
  have h11112 : BigF ((((s2 + (6 + 1) + 1) + 1) + 1) + 1) [(1, false), (1, false), (1, false), (1,
      false), (2, false)] 0
      [(0, true), (0, true), (0, true), (1, false), (1, false), (1, false), (2, false)] :=
    BigF.oneF_rem1 h1112 rfl
  have h2s1112 : BigF _ [(2, true), (1, false), (1, false), (1, false), (2, false)] 4
      [(1, true), (0, true), (1, false), (1, false), (1, false), (2, false)] :=
    BigF.twoT_rem0 h11112 rfl (BigD1.zeroT [(0, true), (0, true), (1, false), (1, false), (1,
        false), (2, false)])
  have h3112 : BigF _ [(3, false), (1, false), (1, false), (2, false)] 7
      [(1, true), (0, true), (1, false), (1, false), (1, false), (2, false)] :=
    BigF.ge3_rem0 (BigD1.zeroF h112) rfl (BigD1.oneF h2s1112)
  have h312 : BigF _ [(3, false), (1, false), (2, false)] 10
      [(1, true), (0, true), (1, false), (1, false), (1, false), (2, false)] :=
    BigF.ge3_rem0 (BigD1.zeroF h12) rfl
        (BigD1.oneF (BigF.ge3_rem0 (BigD1.zeroF h112) rfl (BigD1.oneF h2s1112)))
  exact ⟨_, _, BigF.twoF_rem0 (Y := [(1, true), (1, false)]) h3s1 rfl (BigD1.oneF h312)⟩

theorem bigF_2_1s_1_0_exists :
    ∃ s, BigF s [(2, false), (1, true), (1, false), (0, false)] 0
      [(0, true), (1, false), (1, false), (1, false), (1, false), (2, false)] := by
  obtain ⟨s2, h2⟩ := bigF_2_nil_exists
  have h40 : BigF _ [(4, false), (0, false)] 10 [(2, false)] :=
    BigF.ge3_rem0 (d := 1) (b := false) (Y := [(0,
        false)]) (BigD1.oneF h2) rfl (BigD1.oneF bigF_3_1_nil_exists)
  have h3s10 : BigF _ [(3, true), (1, false), (0, false)] 13 [(2, false)] :=
    BigF.ge3_rem0 (d := 0) (b := true) (Y := [(1, false), (0, false)]) (BigD1.zeroT [(1, false), (0,
        false)]) rfl
      (BigD1.oneF h40)
  exact ⟨_, BigF.twoF_rem1 (Y := [(1, true), (1, false), (0, false)]) h3s10 rfl⟩

/-- Shared dispatch for `BigF s ((2, false) :: Y) Δ R_fin` given `BigF s1 (bumpR (bumpR Y)) Δ1 R1`:
    handles all `Δ1` branches when `Δ1` is NOT `0`, `2`, `3`, `5`, `6`, or `9` (and handles `8, 11,
    ≥14, 12, ≥15`). -/
private theorem good2_f_dispatch_high {m s s1 Δ Δ1 : Nat} {Y R1 R_fin : List Seg}
    (ih : InvLt m) (hs : s ≤ m) (hs1 : s1 < s)
    (h1 : BigF s1 (bumpR (bumpR Y)) Δ1 R1) (hN_b2 : NoNonlast0F (bumpR (bumpR Y)))
    (hcases :
      (Δ1 % 3 = 1 ∧ 4 ≤ Δ1 ∧ Δ = 0 ∧ R_fin = (0, true) :: ones (Δ1 / 3) ++ R1) ∨
      (Δ1 = 2 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧ BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
      (Δ1 % 3 = 2 ∧ 5 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 2 ∧ BigF s2 ((3,
          false) :: ones (Δ1 / 3 - 1) ++ R1) Δ3 R_fin) ∨
      (Δ1 = 0 ∧ ∃ s2 < s, ∃ Δ2, Δ = Δ2 + 1 ∧ BigD1 s2 R1 Δ2 R_fin) ∨
      (Δ1 = 3 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧ BigF s2 (bumpR (bumpR R1)) Δ3 R_fin) ∨
      (Δ1 % 3 = 0 ∧ 6 ≤ Δ1 ∧ ∃ s2 < s, ∃ Δ3, Δ = Δ3 + 3 ∧ BigF s2 ((3,
          false) :: ones (Δ1 / 3 - 2) ++ R1) Δ3 R_fin))
    (hne2 : Δ1 ≠ 2)
    (h5 : Δ1 = 5 → Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
      (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
      (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)))
    (h0 : Δ1 = 0 → ∀ s2 Δ2, s2 < s → Δ = Δ2 + 1 → BigD1 s2 R1 Δ2 R_fin →
      Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
      (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
      (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)))
    (h3 : Δ1 = 3 → ∀ s2 Δ3, s2 < s → Δ = Δ3 + 3 → BigF s2 (bumpR (bumpR R1)) Δ3 R_fin →
      Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
      (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
      (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)))
    (h6 : Δ1 = 6 → ∀ s2 Δ3, s2 < s → Δ = Δ3 + 3 → BigF s2 ((3, false) :: R1) Δ3 R_fin →
      Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
      (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
      (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)))
    (h9 : Δ1 = 9 → ∀ s2 Δ3, s2 < s → Δ = Δ3 + 3 → BigF s2 ((3, false) :: (1,
        false) :: R1) Δ3 R_fin →
      Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
      (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
      (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W))) :
    Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
    (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
    (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)) := by
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
  rcases hcases with ⟨_, _, rfl, _⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, hge5, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, s2, hs2, Δ2, rfl, hD2⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨hrem0, hge6, s2, hs2, Δ3, rfl, hF2⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · exact False.elim (hne2 rfl)
  · by_cases h5e : Δ1 = 5
    · exact h5 h5e
    · by_cases h8e : Δ1 = 8
      · subst h8e
        obtain ⟨U, rfl⟩ := (ih s1 (by omega)).f_258 h1 hN_b2 (Or.inr (Or.inr rfl))
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
        have hF2' : BigF s2 ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
            false) :: U) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2'
        obtain ⟨rfl, _⟩ := (ih s4 (by omega)).f2s_111 hF4 hNU
        exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · by_cases h11e : Δ1 = 11
        · subst h11e
          rcases (ih s1 (by omega)).f_11 h1 hN_b2 with ⟨U, rfl⟩ | hS
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: (1,
                false) :: (1, false) :: U) Δ3 R_fin := by
              simpa [ones] using hF2
            obtain ⟨rfl, _⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            exact ⟨by omega, by omega, by omega, by omega, by omega⟩
          · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
                simpa [ones] using hF2
            obtain ⟨rfl, _⟩ := (ih s2 (by omega)).good2_f311 hS.1 hF2' hN1
            exact ⟨by omega, by omega, by omega, by omega, by omega⟩
        · have hge14 : 14 ≤ Δ1 := by omega
          have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
              false) :: (ones (Δ1 / 3 - 4) ++ R1)) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h710, _, _⟩ := (ih s2 (by omega)).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          rcases h710 with rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · exact h0 rfl s2 Δ2 hs2 rfl hD2
  · exact h3 rfl s2 Δ3 hs2 rfl hF2
  · by_cases h6e : Δ1 = 6
    · subst h6e
      have hF2' : BigF s2 ((3, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
      exact h6 rfl s2 Δ3 hs2 rfl hF2'
    · by_cases h9e : Δ1 = 9
      · subst h9e
        have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
        exact h9 rfl s2 Δ3 hs2 rfl hF2'
      · by_cases h12e : Δ1 = 12
        · subst h12e
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
          rcases (ih s2 (by omega)).f3_11 hF2' hN1 with rfl | rfl | ⟨rfl, _⟩
          · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
          · have hGZ : GoodZero111Head R1 := by
              by_cases h0s : ∃ W, R1 = (0, true) :: W
              · obtain ⟨W, hW⟩ := h0s
                exact Or.inr ((ih s1 (by omega)).f_pos_0s h1 hN_b2 (by omega) hW)
              · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
            exact ⟨by omega, by omega, by omega, by omega,
              fun _ => Or.inl (bigF_3_1_1_7_good2_of_gz ih (by omega) hGZ hF2' hN1)⟩
          · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
        · have hge15 : 15 ≤ Δ1 := by omega
          have hq3 : Δ1 / 3 - 2 = (Δ1 / 3 - 5) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
              false) :: (ones (Δ1 / 3 - 5) ++ R1)) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h710, hG2', _⟩ := (ih s2 (by omega)).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          rcases h710 with rfl | rfl
          · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inl hG2'⟩
          · exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Helper: `BigF s2 (bumpR (bumpR (0*::1::1::U))) Δ3 R_fin` with `GoodZero111Head U` closes `Δ = Δ3
    + 3`. -/
private theorem good2_f_from_3_0s11 {m s2 Δ3 : Nat} {U R_fin : List Seg}
    (ih : InvLt m) (hs2 : s2 < m) (hGZ : GoodZero111Head U)
    (hF2 : BigF s2 (bumpR (bumpR ((0, true) :: (1, false) :: (1, false) :: U))) Δ3 R_fin)
    (hNU : NoNonlast0F U) :
    (Δ3 + 3) % 3 ≠ 2 ∧ (Δ3 + 3 = 4 → Good4Out R_fin) ∧ (Δ3 + 3 = 6 → Head0s11 R_fin) ∧
    (Δ3 + 3 = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
    (Δ3 + 3 = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)) := by
  have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin := by
      simpa [bumpR] using hF2
  rcases (ih s2 hs2).f2s_11 hF2' hNU with ⟨rfl, hG1⟩ | ⟨rfl, _⟩ | rfl
  · exact ⟨by omega, by omega, by omega, fun _ => Or.inl (good1Safe_to_strong2 (hG1 hGZ)), by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Helper: `BigF s2 (3 :: 0* :: 1 :: 1 :: U) Δ3 R_fin` closes `Δ = Δ3 + 3`. -/
private theorem good2_f_from_6_0s11 {m s2 Δ3 : Nat} {U R_fin : List Seg}
    (ih : InvLt m) (hs2 : s2 < m)
    (hF2 : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δ3 R_fin)
    (hNU : NoNonlast0F U) :
    (Δ3 + 3) % 3 ≠ 2 ∧ (Δ3 + 3 = 4 → Good4Out R_fin) ∧ (Δ3 + 3 = 6 → Head0s11 R_fin) ∧
    (Δ3 + 3 = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
    (Δ3 + 3 = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)) := by
  obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2
  rcases (ih s4 (by omega)).f3_11 hF4 hNU with rfl | rfl | ⟨rfl, _⟩
  · exact ⟨by omega, by omega, fun _ => bigF_3_zero_prefix hF4, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Helper: `BigF s2 (3 :: 1 :: R1) Δ3 R_fin` with `Head0s11 R1 ∨ Strong2 R1` closes `Δ = Δ3 + 3`.
-/
private theorem good2_f_from_9_hs {m s2 Δ3 : Nat} {R1 R_fin : List Seg}
    (ih : InvLt m) (hs2 : s2 < m) (hR1 : Head0s11 R1 ∨ Strong2 R1)
    (hF2 : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin) (hN1 : NoNonlast0F R1) :
    (Δ3 + 3) % 3 ≠ 2 ∧ (Δ3 + 3 = 4 → Good4Out R_fin) ∧ (Δ3 + 3 = 6 → Head0s11 R_fin) ∧
    (Δ3 + 3 = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
    (Δ3 + 3 = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)) := by
  rcases hR1 with ⟨U, rfl⟩ | hS
  · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2
    obtain ⟨rfl, hG1⟩ :=
        (ih s4 (by omega)).f2s_111 hF4 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inl (good1Safe_to_good2 hG1)⟩
  · have ⟨h710, hSf⟩ := (ih s2 hs2).good2_f31 hS.1 hF2 hN1
    have hS' := hSf hS
    rcases h710 with rfl | ⟨rfl, _⟩
    · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inl hS'.1⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Helper for `BigF s1 ((4, false) :: X) Δ1 R1`: handles `BigF s ((2, false) :: (2, false) :: X) Δ
R_fin`
    for `c_2_2_0s_1_1`, `c_2_2_1_0s_1_1`, `c_2_2_1_1_gf` and `c_2_1s_1_0s`, `c_2_1s_1_1`. -/
theorem step_good2_f {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF m G Δ R_fin) (hN : NoNonlast0F G) :
    Δ % 3 ≠ 2 ∧ (Δ = 4 → Good4Out R_fin) ∧ (Δ = 6 → Head0s11 R_fin) ∧
    (Δ = 7 → Strong2 R_fin ∨ Head0s11 R_fin) ∧
    (Δ = 10 → Good2 R_fin ∨ Head0s11 R_fin ∨ (∃ W, R_fin = (1, true) :: W)) := by
  induction hG generalizing m Δ R_fin with
  | of_good1 h1g =>
    rcases h1g with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl, _⟩ | ⟨Z,
        rfl⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases h; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · -- 2 :: 1 :: 1 :: Z
      obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
      have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))
      have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
      have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
      have h1' : BigF s1 ((3, false) :: (1, false) :: Z) Δ1 R1 := by simpa [bumpR] using h1
      refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
        (fun h2 => ((ih s1 hs1).f3_ne24 h1' (noNonlast0F_cons_ne0F (x := (1,
            false)) (by simp) hNZ)).1 h2)
        (fun h5 => ?_) (fun h0 s2 Δ2 hs2 hadd hD2 => ?_) (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
        (fun h6 _ _ _ _ _ => False.elim ((ih s1 hs1).f3_1_ne6 (h6 ▸ h1') hNZ))
        (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
      · -- Δ1 = 5
        subst h5
        rcases hcases with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, s2, hs2, Δ3, rfl, hF2⟩ |
            ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _⟩
        · omega
        · omega
        · obtain ⟨U, rfl⟩ :=
              (ih s1 hs1).f3_5_0111 h1' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)
          have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
          have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: (1,
              false) :: U) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2'
          obtain ⟨h710, _, _⟩ := (ih s4 (by omega)).f3_111 hF4 hNU
          rcases h710 with rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩
        · omega
        · omega
        · omega
      · -- Δ1 = 0 -> BigF s1 (3, 1 :: Z) 0 R1 -> Good4Out.of_safeU
        subst h0; subst hadd
        obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_3_inv h1'
        have hNa :=
            (bigFD_noNonlast0F _).1 _ _ _ ha (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)
        rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_, _, _, _, hadd0,
            _⟩ | ⟨_, _, _, _, _, hadd0, _⟩
        · cases hD2
          have hf1a := (ih sa (by omega)).f1 ha hNZ
          have hne4 := hf1a.2.1
          have hSU : SafeU (ones (Δa / 3 - 1) ++ Ra) := by
            by_cases h7a : Δa = 7
            · subst h7a
              rcases hf1a.2.2.2.2.1 rfl with hH | hG1a
              · exact Or.inr (Or.inr (Or.inl ⟨Ra, by simp [ones],
                                                   Or.inr (head0s111_to_head0s11 hH)⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨Ra, by simp [ones],
                                                   Or.inl (good1Safe_to_good2 hG1a)⟩))
            · by_cases h10a : Δa = 10
              · subst h10a
                rcases hf1a.2.2.2.2.2.1 rfl with hH | hG2a
                · exact Or.inr (Or.inl ⟨Ra, by simp [ones], Or.inr hH⟩)
                · exact Or.inr (Or.inl ⟨Ra, by simp [ones], Or.inl hG2a⟩)
              · have hge13 : 13 ≤ Δa := by omega
                have hq3 : Δa / 3 - 1 = (Δa / 3 - 4) + 3 := by omega
                rw [hq3]
                exact Or.inl ⟨ones (Δa / 3 - 4) ++ Ra, by simp [ones]⟩
          exact ⟨by omega, fun _ => Good4Out.of_safeU hSU, by omega, by omega, by omega⟩
        · omega
        · omega
        · omega
      · -- Δ1 = 3 -> f3_3_non0s -> Safe0s
        subst h3; subst hadd
        obtain ⟨U, rfl, hSU⟩ :=
            (ih s1 hs1).f3_3_non0s h1' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)
          (fun _ hEq => by cases hEq)
        exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · -- Δ1 = 9 -> f3_9 -> Head0s11 ∨ Strong2
        subst h9; subst hadd
        exact good2_f_from_9_hs ih hs2 ((ih s1 hs1).f3_9 h1' (noNonlast0F_cons_ne0F (x := (1,
            false)) (by simp) hNZ)) hF2 hN1
  | c_2_0 =>
    obtain ⟨_, hEx⟩ := bigF_2_0_exists
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | c_2_1 =>
    obtain ⟨_, hEx⟩ := bigF_2_1_nil_exists
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | c_2_1_2 =>
    obtain ⟨_, hEx⟩ := bigF_2_1_2_exists
    obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
    exact ⟨by omega, fun _ => Good4Out.two_one_one, by omega, by omega, by omega⟩
  | c_2_0s Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail hN)
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((2, true) :: Z) Δ1 R1 := by simpa [bumpR] using h1
    have hf2s := (ih s1 hs1).f2s h1' hNZ
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases hf2s.1
      (fun h5 => False.elim (hf2s.2.1 h5))
      (fun h0 s2 Δ2 hs2 hadd hD2 => ?_) (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
      (fun h6 s2 Δ3 hs2 hadd hF2 => ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h0; subst hadd
      obtain ⟨U, rfl, hSU⟩ := hf2s.2.2.1 rfl
      cases hD2
      exact ⟨by omega, fun _ => Good4Out.of_safeU hSU, by omega, by omega, by omega⟩
    · subst h3; subst hadd
      obtain ⟨U, rfl, hGFU⟩ := bigF_2s_3_goodF2U ih hs1 h1' hNZ
      exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head hGFU) hF2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · subst h6; subst hadd
      rcases hf2s.2.2.2.2.1 rfl with ⟨U, rfl⟩ | hG1
      · exact good2_f_from_6_0s11 ih hs2 hF2
            (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · rcases bigF_3_good1Safe ih hs2 hG1 hF2 hN1 with ⟨rfl, hO⟩ | ⟨hm, hge⟩
        · rcases hO with hG2 | ⟨W, rfl⟩
          · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inl hG2⟩
          · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inr (Or.inr ⟨W, rfl⟩)⟩
        · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · subst h9; subst hadd
      exact good2_f_from_9_hs ih hs2 (hf2s.2.2.2.2.2.1 rfl) hF2 hN1
  | c_2_1s_0 =>
    obtain ⟨_, hEx⟩ := bigF_2_1s_0_exists
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | c_2_1s_0s Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, true) :: (0, true) :: Z) Δ1 R1 := by simpa [bumpR] using h1
    obtain ⟨sa, hsa, Δa, hadd1, ha⟩ := bigF_3s_inv h1'
    have ha' : BigF sa ((3, true) :: Z) Δa R1 := by simpa [bumpR] using ha
    obtain ⟨sb, hsb, Δb, hadda, hb⟩ := bigF_3s_inv ha'
    have hN_b3 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_bumpR hNZ))
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by omega) (by omega) (fun h0 => by omega) (fun h3 => by omega)
      (fun h6 s2 Δ3 hs2 hadd hF2 => ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h6; subst hadd
      have h0b : Δb = 0 := by omega
      subst h0b
      cases Z with
      | nil =>
        obtain ⟨_, hEx⟩ := bigF_2_nil_exists
        have hb' : BigF sb [(2, false)] 0 R1 := by simpa [bumpR] using hb
        obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hb' hEx
        omega
      | cons x xs =>
        cases x with
        | mk dx bx =>
          have hb' : BigF sb ((dx + 3, bx) :: xs) 0 R1 := by simpa [bumpR] using hb
          rcases bigF_ge3_zero_prefix hb' with ⟨U, rfl⟩ | ⟨U, rfl⟩
          · exact good2_f_from_6_0s11 ih hs2 hF2
                (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
          · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2
            obtain ⟨s5, hs5, Δ5, rfl, hF5⟩ := bigF_3_1_0s_inv hF4
            have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))
            rcases (ih s5 (by omega)).f2s_1 hF5 hNU with rfl | rfl | rfl | rfl <;>
              exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · subst h9; subst hadd
      have h3b : Δb = 3 := by omega
      subst h3b
      obtain ⟨U, rfl⟩ := bigF_three_head hb
      have hNU := noNonlast0F_tail (noNonlast0F_tail hN1)
      obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2
      rcases (ih s4 (by omega)).f2s_11 hF4 hNU with ⟨rfl, hG1⟩ | ⟨rfl, _⟩ | rfl
      · refine ⟨by omega, by omega, by omega, by omega, fun _ => ?_⟩
        by_cases h0s : ∃ W, U = (0, true) :: W
        · obtain ⟨W, rfl⟩ := h0s
          obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF4 (bigF_2s_1_1_0s_exists W)
          exact Or.inr (Or.inr ⟨(0, true) :: (1, false) :: W, rfl⟩)
        · exact Or.inl (good1Safe_to_good2 (hG1 (Or.inl (fun W hW => h0s ⟨W, hW⟩))))
      · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | c_2_1s_1 =>
    obtain ⟨_, _, hEx⟩ := bigF_2_1s_1_exists
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | c_2_1s_1_0 =>
    obtain ⟨_, hEx⟩ := bigF_2_1s_1_0_exists
    obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ h hEx
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | c_2_1s_1_0s Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, true) :: (1, false) :: (0, true) :: Z) Δ1 R1 := by
        simpa [bumpR] using h1
    obtain ⟨sa, hsa, Δa, hadd1, ha⟩ := bigF_3s_inv h1'
    have ha' : BigF sa ((4, false) :: (0, true) :: Z) Δa R1 := by simpa [bumpR] using ha
    -- Analyze BigF sa (4 :: 0* :: Z) Δa R1 via cases ha'
    have h4_info : (Δa = 0 ∧ Head0s111 R1) ∨
        (Δa = 3 ∧ Head0s11 R1) ∨
        (Δa = 5 ∧ Head0s11 R1) ∨
        (Δa = 6 ∧ (Head0s11 R1 ∨ Good1Safe R1)) ∨
        Δa = 8 ∨ Δa % 3 = 1 ∨ 9 ≤ Δa := by
      cases ha' with
      | ge3_rem1 hd1 hremd1 =>
        rename_i sd1 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((2, true) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hf2s := (ih sb (by omega)).f2s hb' hNZ
        have hne2 := hf2s.1
        have hne5 := hf2s.2.1
        have hge8 : 8 ≤ Δb := by omega
        have hq3 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 3) + 3 := by omega
        rw [hq3]
        exact Or.inl ⟨rfl, ⟨ones ((Δb + 2) / 3 - 3) ++ Rd1, by simp [ones]⟩⟩
      | ge3_rem2 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((2, true) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hNb :=
            (bigFD_noNonlast0F _).1 _ _ _ hb' (noNonlast0F_cons_ne0F (x := (2, true)) (by simp) hNZ)
        have hf2s := (ih sb (by omega)).f2s hb' hNZ
        cases hd2 with
        | oneF hF =>
          rename_i sc Δc
          by_cases h0b : Δb = 0
          · subst h0b
            obtain ⟨U, rfl, hSU⟩ := hf2s.2.2.1 rfl
            have hF' : BigF sc ((2, true) :: (1, false) :: (1, false) :: U) Δc R1 := by
                simpa [ones, bumpR] using hF
            rcases (ih sc (by omega)).f2s_11 hF'
                (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb))) with
                ⟨rfl, hG1⟩ | ⟨rfl, _⟩ | rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
                  Or.inr (hG1 (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)))⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
          · by_cases h3b : Δb = 3
            · subst h3b
              obtain ⟨U, rfl⟩ := hf2s.2.2.2.1 rfl
              have hF' : BigF sc ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δc R1 :=
                  by
                simpa [ones, bumpR] using hF
              obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF'
              rcases (ih s4 (by omega)).f3_11 hF4
                  (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb))) with
                  rfl | rfl | ⟨rfl, _⟩
              · exact Or.inr (Or.inr (Or.inl ⟨rfl, bigF_3_zero_prefix hF4⟩))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
            · by_cases h6b : Δb = 6
              · subst h6b
                have hF' : BigF sc ((3, false) :: (1, false) :: Rd1) Δc R1 := by
                    simpa [ones, bumpR] using hF
                rcases hf2s.2.2.2.2.1 rfl with ⟨U, rfl⟩ | hG1
                · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF'
                  obtain ⟨rfl, _⟩ :=
                      (ih s4 (by omega)).f2s_111 hF4
                      (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb)))
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
                · rcases ((ih sc (by omega)).good2_f31 (good1Safe_to_good2 hG1) hF'
                      hNb).1 with rfl | ⟨rfl, _⟩ <;>
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
              · by_cases h9b : Δb = 9
                · subst h9b
                  have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: Rd1) Δc R1 := by
                      simpa [ones, bumpR] using hF
                  rcases hf2s.2.2.2.2.2.1 rfl with ⟨U, rfl⟩ | hS
                  · obtain ⟨rfl, _⟩ :=
                        (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                        false) :: U))
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
                  · obtain ⟨rfl, _⟩ := (ih sc (by omega)).good2_f311 hS.1 hF' hNb
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
                · have hge12 : 12 ≤ Δb := by omega
                  have hq3 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 4) + 4 := by omega
                  rw [hq3] at hF
                  have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                      (ones ((Δb + 2) / 3 - 4) ++ Rd1)) Δc R1 := by simpa [ones, bumpR] using hF
                  obtain ⟨h710, _, _⟩ :=
                      (ih sc (by omega)).f3_111 hF' (noNonlast0F_ones_append _ hNb)
                  rcases h710 with rfl | rfl <;>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
      | ge3_rem0 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1 Δd2
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((2, true) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hNb :=
            (bigFD_noNonlast0F _).1 _ _ _ hb' (noNonlast0F_cons_ne0F (x := (2, true)) (by simp) hNZ)
        have hge4 : 4 ≤ Δb := by have := ((bigFD_bounds _).1 _ _ _ hb').1; omega
        have hq2 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 2) + 2 := by omega
        rw [hq2] at hd2
        obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
        have hN_in := noNonlast0F_ones_append ((Δb + 2) / 3 - 2) hNb
        have hne24 := (ih sc (by omega)).f3_ne24 hF hN_in
        by_cases h0c : Δc = 0
        · subst h0c; exact Or.inr (Or.inl ⟨by omega, bigF_3_zero_prefix hF⟩)
        · by_cases h3c : Δc = 3
          · subst h3c; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
                Or.inl ((ih sc (by omega)).f3_36 hF hN_in (Or.inl rfl))⟩)))
          · by_cases h5c : Δc = 5
            · subst h5c; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
            · by_cases h1c : Δc = 1
              · subst h1c; exact False.elim (bigF_ne_one hF)
              · by_cases hm1 : Δc % 3 = 1
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by omega) (fun h5 => by omega) (fun h0 => by omega)
      (fun h3 s2 Δ3 hs2 hadd hF2 => ?_) (fun h6 s2 Δ3 hs2 hadd hF2 =>
          ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h3; subst hadd
      have h0a : Δa = 0 := by omega
      rcases h4_info with ⟨_, ⟨U, rfl⟩⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | h8 | hm | h9
      · exact good2_f_from_3_0s11 ih hs2 (Or.inl (fun _ hEq => by cases hEq)) hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h6; subst hadd
      have h3a : Δa = 3 := by omega
      rcases h4_info with ⟨h0, _⟩ | ⟨_, ⟨U, rfl⟩⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | h8 | hm | h9
      · omega
      · exact good2_f_from_6_0s11 ih hs2 hF2
            (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h9; subst hadd
      have h6a : Δa = 6 := by omega
      rcases h4_info with ⟨h0, _⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨_, hO⟩ | h8 | hm | h9
      · omega
      · omega
      · omega
      · rcases hO with hH | hG1
        · exact good2_f_from_9_hs ih hs2 (Or.inl hH) hF2 hN1
        · exact good2_f_from_9_hs ih hs2 (Or.inr (good1Safe_to_strong2 hG1)) hF2 hN1
      · omega
      · omega
      · omega
  | c_2_1s_1_1 Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, true) :: (1, false) :: (1, false) :: Z) Δ1 R1 := by
        simpa [bumpR] using h1
    obtain ⟨sa, hsa, Δa, hadd1, ha⟩ := bigF_3s_inv h1'
    have ha' : BigF sa ((4, false) :: (1, false) :: Z) Δa R1 := by simpa [bumpR] using ha
    have h4_info : (Δa = 0 ∧ ∃ U, R1 = (0, true) :: (1, false) :: (1,
        false) :: U ∧ GoodZero111Head U) ∨
        (Δa = 3 ∧ Head0s11 R1) ∨
        (Δa = 5 ∧ Head0s11 R1) ∨
        (Δa = 6 ∧ (Head0s11 R1 ∨ Good1Safe R1)) ∨
        Δa = 8 ∨ Δa % 3 = 1 ∨ 9 ≤ Δa := by
      cases ha' with
      | ge3_rem1 hd1 hremd1 =>
        rename_i sd1 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hne24 := (ih sb (by omega)).f3_ne24 hb' hNZ
        by_cases h5b : Δb = 5
        · subst h5b
          obtain ⟨U, rfl⟩ := (ih sb (by omega)).f3_5_0111 hb' hNZ
          exact Or.inl ⟨rfl, ⟨(0, true) :: (1, false) :: (1, false) :: (1, false) :: U,
              by simp [ones], Or.inr ⟨(1, false) :: (1, false) :: U, rfl⟩⟩⟩
        · have hge8 : 8 ≤ Δb := by omega
          have hq3 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 3) + 3 := by omega
          rw [hq3]
          exact Or.inl ⟨rfl, ⟨(1, false) :: (ones ((Δb + 2) / 3 - 3) ++ Rd1), by simp [ones],
              Or.inl (fun _ hEq => by cases hEq)⟩⟩
      | ge3_rem2 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hNb :=
            (bigFD_noNonlast0F _).1 _ _ _ hb' (noNonlast0F_cons_ne0F (x := (3,
            false)) (by simp) hNZ)
        cases hd2 with
        | oneF hF =>
          rename_i sc Δc
          by_cases h0b : Δb = 0
          · subst h0b
            obtain ⟨U, rfl, hGFU⟩ := bigF_3_zero_goodF2U ih (by omega) hb' hNZ
            have hF' : BigF sc ((2, true) :: (1, false) :: (1, false) :: U) Δc R1 := by
                simpa [ones, bumpR] using hF
            rcases (ih sc (by omega)).f2s_11 hF'
                (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb))) with
                ⟨rfl, hG1⟩ | ⟨rfl, _⟩ | rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
                  Or.inr (hG1 (goodF2U_to_goodZero111Head hGFU))⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
          · by_cases h3b : Δb = 3
            · subst h3b
              obtain ⟨U, rfl⟩ := (ih sb (by omega)).f3_36 hb' hNZ (Or.inl rfl)
              have hF' : BigF sc ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δc R1 :=
                  by
                simpa [ones, bumpR] using hF
              obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF'
              rcases (ih s4 (by omega)).f3_11 hF4
                  (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb))) with
                  rfl | rfl | ⟨rfl, _⟩
              · exact Or.inr (Or.inr (Or.inl ⟨rfl, bigF_3_zero_prefix hF4⟩))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
            · by_cases h6b : Δb = 6
              · subst h6b
                obtain ⟨U, rfl⟩ := (ih sb (by omega)).f3_36 hb' hNZ (Or.inr rfl)
                have hF' : BigF sc ((3, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
                    false) :: U) Δc R1 := by
                  simpa [ones, bumpR] using hF
                obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF'
                obtain ⟨rfl, _⟩ :=
                    (ih s4 (by omega)).f2s_111 hF4
                    (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb)))
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
              · by_cases h9b : Δb = 9
                · subst h9b
                  have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: Rd1) Δc R1 := by
                      simpa [ones, bumpR] using hF
                  rcases (ih sb (by omega)).f3_9 hb' hNZ with ⟨U, rfl⟩ | hS
                  · obtain ⟨rfl, _⟩ :=
                        (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                        false) :: U))
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
                  · obtain ⟨rfl, _⟩ := (ih sc (by omega)).good2_f311 hS.1 hF' hNb
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
                · have hge12 : 12 ≤ Δb := by omega
                  have hq3 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 4) + 4 := by omega
                  rw [hq3] at hF
                  have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                      (ones ((Δb + 2) / 3 - 4) ++ Rd1)) Δc R1 := by simpa [ones, bumpR] using hF
                  obtain ⟨h710, _, _⟩ :=
                      (ih sc (by omega)).f3_111 hF' (noNonlast0F_ones_append _ hNb)
                  rcases h710 with rfl | rfl <;>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
      | ge3_rem0 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1 Δd2
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hNb :=
            (bigFD_noNonlast0F _).1 _ _ _ hb' (noNonlast0F_cons_ne0F (x := (3,
            false)) (by simp) hNZ)
        have hne24 := (ih sb (by omega)).f3_ne24 hb' hNZ
        have hge7 : 7 ≤ Δb := by have := ((bigFD_bounds _).1 _ _ _ hb').1; omega
        have hq3 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 2) + 2 := by omega
        rw [hq3] at hd2
        obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
        have hN_in := noNonlast0F_ones_append ((Δb + 2) / 3 - 2) hNb
        have hne24c := (ih sc (by omega)).f3_ne24 hF hN_in
        by_cases h0c : Δc = 0
        · subst h0c; exact Or.inr (Or.inl ⟨by omega, bigF_3_zero_prefix hF⟩)
        · by_cases h3c : Δc = 3
          · subst h3c; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
                Or.inl ((ih sc (by omega)).f3_36 hF hN_in (Or.inl rfl))⟩)))
          · by_cases h5c : Δc = 5
            · subst h5c; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
            · by_cases h1c : Δc = 1
              · subst h1c; exact False.elim (bigF_ne_one hF)
              · by_cases hm1 : Δc % 3 = 1
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by omega) (fun h5 => by omega) (fun h0 => by omega)
      (fun h3 s2 Δ3 hs2 hadd hF2 => ?_) (fun h6 s2 Δ3 hs2 hadd hF2 =>
          ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h3; subst hadd
      have h0a : Δa = 0 := by omega
      rcases h4_info with ⟨_, ⟨U, rfl, hGZ⟩⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | h8 | hm | h9
      · exact good2_f_from_3_0s11 ih hs2 hGZ hF2
            (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h6; subst hadd
      have h3a : Δa = 3 := by omega
      rcases h4_info with ⟨h0, _⟩ | ⟨_, ⟨U, rfl⟩⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | h8 | hm | h9
      · omega
      · exact good2_f_from_6_0s11 ih hs2 hF2
            (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h9; subst hadd
      have h6a : Δa = 6 := by omega
      rcases h4_info with ⟨h0, _⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨_, hO⟩ | h8 | hm | h9
      · omega
      · omega
      · omega
      · rcases hO with hH | hG1
        · exact good2_f_from_9_hs ih hs2 (Or.inl hH) hF2 hN1
        · exact good2_f_from_9_hs ih hs2 (Or.inr (good1Safe_to_strong2 hG1)) hF2 hN1
      · omega
      · omega
      · omega
  | c_2_1_0s Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, false) :: (0, true) :: Z) Δ1 R1 := by simpa [bumpR] using h1
    obtain ⟨sa, hsa, Δa, hadd1, ha⟩ := bigF_3_0s_inv h1'
    have hne24 := (ih sa (by omega)).f3_ne24 ha hNZ
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by omega) (fun h5 => by omega) (fun h0 => by omega)
      (fun h3 s2 Δ3 hs2 hadd hF2 => ?_) (fun h6 s2 Δ3 hs2 hadd hF2 =>
          ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h3; subst hadd
      have h0a : Δa = 0 := by omega
      subst h0a
      obtain ⟨U, rfl, hGFU⟩ := bigF_3_zero_goodF2U ih (by omega) ha hNZ
      exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head hGFU) hF2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · subst h6; subst hadd
      have h3a : Δa = 3 := by omega
      subst h3a
      obtain ⟨U, rfl⟩ := (ih sa (by omega)).f3_36 ha hNZ (Or.inl rfl)
      exact good2_f_from_6_0s11 ih hs2 hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · subst h9; subst hadd
      have h6a : Δa = 6 := by omega
      subst h6a
      exact good2_f_from_9_hs ih hs2 (Or.inl ((ih sa (by omega)).f3_36 ha hNZ (Or.inr rfl))) hF2 hN1
  | c_2_1_1 Z =>
    -- Identical to of_good1's 2::1::1::Z! Just delegate via Good2.of_good1!
    -- Wait: we can't call ihG directly, just repeat 1-line delegation? Actually Good2.of_good1
    -- (2::1::1::Z) IS in Good1!
    -- Reuse the exact proof cleanly:
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, false) :: (1, false) :: Z) Δ1 R1 := by simpa [bumpR] using h1
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (fun h2 => ((ih s1 hs1).f3_ne24 h1' (noNonlast0F_cons_ne0F (x := (1,
          false)) (by simp) hNZ)).1 h2)
      (fun h5 => ?_) (fun h0 s2 Δ2 hs2 hadd hD2 => ?_) (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
      (fun h6 _ _ _ _ _ => False.elim ((ih s1 hs1).f3_1_ne6 (h6 ▸ h1') hNZ))
      (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h5
      rcases hcases with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, s2, hs2, Δ3, rfl, hF2⟩ |
          ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _⟩
      · omega
      · omega
      · obtain ⟨U, rfl⟩ :=
            (ih s1 hs1).f3_5_0111 h1' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)
        have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
        have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: (1,
            false) :: U) Δ3 R_fin := by
          simpa [ones] using hF2
        obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2'
        obtain ⟨h710, _, _⟩ := (ih s4 (by omega)).f3_111 hF4 hNU
        rcases h710 with rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · omega
      · omega
      · omega
    · subst h0; subst hadd
      obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_3_inv h1'
      rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_,
          _, _, _, _, hadd0, _⟩
      · cases hD2
        have hf1a := (ih sa (by omega)).f1 ha hNZ
        have hne4 := hf1a.2.1
        have hSU : SafeU (ones (Δa / 3 - 1) ++ Ra) := by
          by_cases h7a : Δa = 7
          · subst h7a
            rcases hf1a.2.2.2.2.1 rfl with hH | hG1a
            · exact Or.inr (Or.inr (Or.inl ⟨Ra, by simp [ones], Or.inr (head0s111_to_head0s11 hH)⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨Ra, by simp [ones], Or.inl (good1Safe_to_good2 hG1a)⟩))
          · by_cases h10a : Δa = 10
            · subst h10a
              rcases hf1a.2.2.2.2.2.1 rfl with hH | hG2a
              · exact Or.inr (Or.inl ⟨Ra, by simp [ones], Or.inr hH⟩)
              · exact Or.inr (Or.inl ⟨Ra, by simp [ones], Or.inl hG2a⟩)
            · have hge13 : 13 ≤ Δa := by omega
              have hq3 : Δa / 3 - 1 = (Δa / 3 - 4) + 3 := by omega
              rw [hq3]
              exact Or.inl ⟨ones (Δa / 3 - 4) ++ Ra, by simp [ones]⟩
        exact ⟨by omega, fun _ => Good4Out.of_safeU hSU, by omega, by omega, by omega⟩
      · omega
      · omega
      · omega
    · subst h3; subst hadd
      obtain ⟨U, rfl, hSU⟩ :=
          (ih s1 hs1).f3_3_non0s h1' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)
        (fun _ hEq => by cases hEq)
      exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · subst h9; subst hadd
      exact good2_f_from_9_hs ih hs2 ((ih s1 hs1).f3_9 h1' (noNonlast0F_cons_ne0F (x := (1,
          false)) (by simp) hNZ)) hF2 hN1
  | c_2_1_1s Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, false) :: (1, true) :: Z) Δ1 R1 := by simpa [bumpR] using h1
    obtain ⟨sa, hsa, Δa, hadd1, ha⟩ := bigF_3_1s_inv h1'
    have hNbZ := noNonlast0F_bumpR hNZ
    have hf2s := (ih sa (by omega)).f2s ha hNbZ
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by omega) (fun h5 => by omega) (fun h0 => by omega)
      (fun h3 s2 Δ3 hs2 hadd hF2 => ?_) (fun h6 s2 Δ3 hs2 hadd hF2 =>
          ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h3; subst hadd
      have h0a : Δa = 0 := by omega
      subst h0a
      obtain ⟨U, rfl, hSU⟩ := hf2s.2.2.1 rfl
      exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · subst h6; subst hadd
      have h3a : Δa = 3 := by omega
      subst h3a
      obtain ⟨U, rfl⟩ := hf2s.2.2.2.1 rfl
      exact good2_f_from_6_0s11 ih hs2 hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · subst h9; subst hadd
      have h6a : Δa = 6 := by omega
      subst h6a
      rcases hf2s.2.2.2.2.1 rfl with hH | hG1
      · exact good2_f_from_9_hs ih hs2 (Or.inl hH) hF2 hN1
      · exact good2_f_from_9_hs ih hs2 (Or.inr (good1Safe_to_strong2 hG1)) hF2 hN1
  | c_2_2_0s_1_1 Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ :=
        noNonlast0F_tail
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((4, false) :: (0, true) :: (1, false) :: (1, false) :: Z) Δ1 R1 := by
        simpa [bumpR] using h1
    have h4_out : (Δ1 = 3 ∧ ∃ U, R1 = (0, true) :: (1, false) :: (1,
        false) :: U ∧ GoodF2U U) ∨ Δ1 % 3 = 1 := by
      cases h1' with
      | ge3_rem1 hd1 hremd1 =>
        rename_i sd1 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        have hb' : BigF sb ((2, true) :: (1, false) :: (1, false) :: Z) Δb Rd1 := by
            simpa [bumpR] using hb
        rcases (ih sb (by omega)).f2s_11 hb' hNZ with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
      | @ge3_rem2 sd1 _ _ _ _ Rd1 _ Δd1 _ hd1 hremd1 _ =>
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        have hb' : BigF sb ((2, true) :: (1, false) :: (1, false) :: Z) Δb Rd1 := by
            simpa [bumpR] using hb
        rcases (ih sb (by omega)).f2s_11 hb' hNZ with ⟨h4, _⟩ | ⟨h10, _⟩ | h13 <;> omega
      | ge3_rem0 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1 Δd2
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((2, true) :: (1, false) :: (1, false) :: Z) Δb Rd1 := by
            simpa [bumpR] using hb
        have hNb := (bigFD_noNonlast0F _).1 _ _ _ hb'
          (noNonlast0F_cons_ne0F (x := (2, true)) (by simp)
            (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
              (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ)))
        rcases (ih sb (by omega)).f2s_11 hb' hNZ with ⟨rfl, _⟩ | ⟨rfl, _⟩ | rfl
        · -- Δb = 4 -> Rd1 = bumpR of Zero111 -> 3 :: Rd1 has Δc % 3 = 1 -> Δ1 % 3 = 1!
          obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
          have hF' : BigF sc ((3, false) :: Rd1) Δc R1 := by simpa [ones] using hF
          -- Extract Zero111 from hb' : BigF sb (2*, 1, 1 :: Z) 4 Rd1
          obtain ⟨se, hse, Δe, Re, he, hce⟩ := bigF_2s_inv hb'
          have hf111e := (ih se (by omega)).f111 he hNZ
          have hRd1 : (∃ W, Rd1 = (1, true) :: (0, true) :: W) ∨
              (∃ W, Rd1 = (1, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
                  false) :: W) ∨
              (∃ W, Rd1 = (1, true) :: (1, false) :: (1, false) :: (1, false) :: W ∧ GoodF2U W) ∨
              (∃ W, Rd1 = (2, false) :: (1, false) :: (1, false) :: W ∧ GoodTail W) := by
            rcases hce with ⟨hrem, _, _, _⟩ | ⟨rfl, _, _, _, _, _⟩ | ⟨hrem, _, _, _, _, _, _⟩ |
                ⟨rfl, sf, hsf, Δf, haddf, hDf⟩ | ⟨rfl, _, _, _, _, _⟩ | ⟨_, hge6, sf, _, Δf, haddf,
                    hFf⟩
            · rcases hf111e with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
            · rcases hf111e with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
            · rcases hf111e with ⟨h0, _, _⟩ | ⟨hm, _, _, _, _⟩ <;> omega
            · rcases hf111e with ⟨_, hZ111, _⟩ | ⟨_, hge9, _, _, _⟩
              · rcases hZ111 with rfl | ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl, hGF⟩ | ⟨W, rfl,
                    hT⟩
                · cases hDf; exact Or.inl ⟨[(0, false)], rfl⟩
                · cases hDf; exact Or.inl ⟨(0, true) :: W, rfl⟩
                · cases hDf; exact Or.inl ⟨(1, false) :: W, rfl⟩
                · cases hDf; exact Or.inr (Or.inl ⟨W, rfl⟩)
                · cases hDf; exact Or.inr (Or.inr (Or.inl ⟨W, rfl, hGF⟩))
                · cases hDf; exact Or.inr (Or.inr (Or.inr ⟨W, rfl, hT⟩))
              · omega
            · rcases hf111e with ⟨h0, _, _⟩ | ⟨_, hge9, _, _, _⟩ <;> omega
            · have h1f : Δf = 1 := by omega
              subst h1f; exact False.elim (bigF_ne_one hFf)
          rcases hRd1 with ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl, hGF⟩ | ⟨W, rfl, hT⟩
          · obtain ⟨sf, hsf, Δf, haddf, hFf⟩ := bigF_3_1s_inv hF'
            have hFf' : BigF sf ((2, true) :: (1, true) :: W) Δf R1 := by simpa [bumpR] using hFf
            have hEx : BigF 2 ((2, true) :: (1, true) :: W) 4 ((1, true) :: bumpR W) :=
              BigF.twoT_rem0 (BigF.oneF_rem1 (BigF.oneT W) rfl) rfl (BigD1.zeroT ((0,
                  true) :: bumpR W))
            obtain ⟨rfl, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hFf' hEx
            exact Or.inr (by omega)
          · rcases bigF_3_good1Safe ih (by omega) (good1Safe_of_1s_1_1_0s_1_1 W) hF' hNb with ⟨rfl,
                _⟩ | ⟨hm, _⟩ <;>
              exact Or.inr (by omega)
          · rcases bigF_3_good1Safe ih (by omega) (good1Safe_of_1s_1_1_1 hGF) hF' hNb with ⟨rfl,
                _⟩ | ⟨hm, _⟩ <;>
              exact Or.inr (by omega)
          · rcases bigF_3_good1Safe ih (by omega) (good1Safe_of_2_1_1 hT) hF' hNb with ⟨rfl,
                _⟩ | ⟨hm, _⟩ <;>
              exact Or.inr (by omega)
        · -- Δb = 10 -> BigD1 = 12 -> 3 :: 1 :: 1 :: Rd1 (f3_11: 0, 7, 10)
          obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
          have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: Rd1) Δc R1 := by
              simpa [ones] using hF
          rcases (ih sc (by omega)).f3_11 hF' hNb with rfl | rfl | ⟨rfl, _⟩
          · exact Or.inl ⟨by omega, bigF_3_zero_goodF2U ih (by omega) hF'
              (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
                  false)) (by simp) hNb))⟩
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
        · -- Δb = 13 -> BigD1 = 15 -> 3 :: 1 :: 1 :: 1 :: Rd1 (f3_111: 7, 10)
          obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
          have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: (1, false) :: Rd1) Δc R1 :=
              by simpa [ones] using hF
          obtain ⟨h710, _, _⟩ := (ih sc (by omega)).f3_111 hF' hNb
          rcases h710 with rfl | rfl <;> exact Or.inr (by omega)
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by rcases h4_out with ⟨h3, _⟩ | hm <;> omega)
      (fun h5 => by rcases h4_out with ⟨h3, _⟩ | hm <;> omega)
      (fun h0 => by rcases h4_out with ⟨h3, _⟩ | hm <;> omega)
      (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
      (fun h6 => by rcases h4_out with ⟨h3, _⟩ | hm <;> omega)
      (fun h9 => by rcases h4_out with ⟨h3, _⟩ | hm <;> omega)
    · subst h3; subst hadd
      rcases h4_out with ⟨_, ⟨U, rfl, hGFU⟩⟩ | hm
      · exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head hGFU) hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
  | c_2_2_1_0s_1_1 Z =>
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ :=
        noNonlast0F_tail
        (noNonlast0F_tail
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((4, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
        false) :: Z) Δ1 R1 := by simpa [bumpR] using h1
    have h4_out : (Δ1 = 3 ∧ ∃ U, R1 = (0, true) :: (1, false) :: (1,
        false) :: U ∧ GoodF2U U) ∨ Δ1 % 3 = 1 ∨ Δ1 = 12 ∨ Δ1 = 15 := by
      cases h1' with
      | ge3_rem1 hd1 hremd1 =>
        rename_i sd1 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        have hb' : BigF sb ((3, false) :: (0, true) :: (1, false) :: (1, false) :: Z) Δb Rd1 := by
            simpa [bumpR] using hb
        obtain ⟨sc, hsc, Δc, haddc, hc⟩ := bigF_3_0s_inv hb'
        rcases (ih sc (by omega)).f3_11 hc hNZ with rfl | rfl | ⟨rfl, _⟩ <;> omega
      | ge3_rem2 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: (0, true) :: (1, false) :: (1, false) :: Z) Δb Rd1 := by
            simpa [bumpR] using hb
        obtain ⟨sc, hsc, Δc, haddc, hc⟩ := bigF_3_0s_inv hb'
        subst haddc
        rcases (ih sc (by omega)).f3_11 hc hNZ with rfl | rfl | ⟨rfl, _⟩
        · -- Δc = 0, Δb = 3, Δd1 = 5 -> hd2 on (1::1::Rd1)
          -- -> 3 :: Rd1 = 3 :: 0* :: 1 :: 1 :: U where U = 1 :: _!
          obtain ⟨sd, hsd, Δd, haddd, hFd⟩ := bigD1_1_1_inv hd2
          -- Extract U = 1 :: _ from hc : BigF sc (3, 1, 1 :: Z) 0 Rd1
          obtain ⟨se, hse, Δe, Re, he, hce⟩ := bigF_3_inv hc
          have hNe := (bigFD_noNonlast0F _).1 _ _ _ he
            (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
                false)) (by simp) hNZ))
          rcases hce with ⟨hreme, hgee, _, rfl⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_, _, _, _, hadd0,
              _⟩ | ⟨_, _, _, _, _, hadd0, _⟩
          · have hne4 : Δe ≠ 4 :=
                ((ih se (by omega)).f1 he (noNonlast0F_cons_ne0F (x := (1,
                false)) (by simp) hNZ)).2.1
            have hq1 : 1 ≤ Δe / 3 - 1 := by omega
            obtain ⟨W, hW⟩ := ones_pos_cons hq1 Re
            have hFd' : BigF sd ((3, false) :: (0, true) :: (1, false) :: (1, false) :: (1,
                false) :: W) Δd R1 := by
              rw [← hW]; simpa [ones] using hFd
            obtain ⟨sf, hsf, Δf, rfl, hFf⟩ := bigF_3_0s_inv hFd'
            have hNW : NoNonlast0F W := by
              have htmp :=
                  noNonlast0F_ones_append (Δe / 3 - 1) hNe; rw
                  [hW] at htmp; exact noNonlast0F_tail htmp
            obtain ⟨h710, _, _⟩ := (ih sf (by omega)).f3_111 hFf hNW
            rcases h710 with rfl | rfl
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inr (by omega)))
          · omega
          · omega
          · omega
        · omega
        · omega
      | ge3_rem0 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1 Δd2
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: (0, true) :: (1, false) :: (1, false) :: Z) Δb Rd1 := by
            simpa [bumpR] using hb
        have hNb := (bigFD_noNonlast0F _).1 _ _ _ hb'
          (noNonlast0F_cons_ne0F (x := (3, false)) (by simp)
            (noNonlast0F_cons_ne0F (x := (0, true)) (by simp)
              (noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
                (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ))))
        obtain ⟨sc, hsc, Δc, haddc, hc⟩ := bigF_3_0s_inv hb'
        subst haddc
        rcases (ih sc (by omega)).f3_11 hc hNZ with rfl | rfl | ⟨rfl, _⟩
        · omega
        · obtain ⟨sd, hsd, Δd, haddd, hFd⟩ := bigD1_1_1_inv hd2
          have hFd' : BigF sd ((3, false) :: (1, false) :: (1, false) :: Rd1) Δd R1 := by
              simpa [ones] using hFd
          rcases (ih sd (by omega)).f3_11 hFd' hNb with rfl | rfl | ⟨rfl, _⟩
          · exact Or.inl ⟨by omega, bigF_3_zero_goodF2U ih (by omega) hFd'
              (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
                  false)) (by simp) hNb))⟩
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inr (Or.inl (by omega))
        · obtain ⟨sd, hsd, Δd, haddd, hFd⟩ := bigD1_1_1_inv hd2
          have hFd' : BigF sd ((3, false) :: (1, false) :: (1, false) :: (1, false) :: Rd1) Δd R1 :=
              by simpa [ones] using hFd
          obtain ⟨h710, _, _⟩ := (ih sd (by omega)).f3_111 hFd' hNb
          rcases h710 with rfl | rfl <;> exact Or.inr (Or.inl (by omega))
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by rcases h4_out with ⟨h3, _⟩ | hm | h12 | h15 <;> omega)
      (fun h5 => by rcases h4_out with ⟨h3, _⟩ | hm | h12 | h15 <;> omega)
      (fun h0 => by rcases h4_out with ⟨h3, _⟩ | hm | h12 | h15 <;> omega)
      (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
      (fun h6 => by rcases h4_out with ⟨h3, _⟩ | hm | h12 | h15 <;> omega)
      (fun h9 => by rcases h4_out with ⟨h3, _⟩ | hm | h12 | h15 <;> omega)
    · subst h3; subst hadd
      rcases h4_out with ⟨_, ⟨U, rfl, hGFU⟩⟩ | hm | h12 | h15
      · exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head hGFU) hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
      · omega
      · omega
  | c_2_2_1_1_gf hGF =>
    rename_i Z
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNZ := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((4, false) :: (1, false) :: (1, false) :: Z) Δ1 R1 := by
        simpa [bumpR] using h1
    have h4_out :
        (Δ1 = 0 ∧ Safe0s R1) ∨
        (Δ1 = 3 ∧ ∃ U, R1 = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U) ∨
        (Δ1 = 5 ∧ Head0s111 R1) ∨
        (Δ1 = 6 ∧ (Head0s11 R1 ∨ Good1Safe R1)) ∨
        (Δ1 = 9 ∧ Strong2 R1) ∨
        Δ1 = 8 ∨ Δ1 % 3 = 1 ∨ 11 ≤ Δ1 := by
      have hN1Z := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNZ
      cases h1' with
      | ge3_rem1 hd1 hremd1 =>
        rename_i sd1 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: (1, false) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hN31Z := noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN1Z
        have hne24 := (ih sb (by omega)).f3_ne24 hb' hN1Z
        by_cases h5b : Δb = 5
        · subst h5b
          obtain ⟨U, rfl⟩ := (ih sb (by omega)).f3_5_0111 hb' hN1Z
          exact Or.inl ⟨rfl, ⟨(0, true) :: (1, false) :: (1, false) :: (1, false) :: U,
              by simp [ones],
            Or.inr (Or.inr (Or.inr (Or.inl ⟨U, rfl⟩)))⟩⟩
        · by_cases h8b : Δb = 8
          · subst h8b
            obtain ⟨U, rfl⟩ := (ih sb (by omega)).f_258 hb' hN31Z (Or.inr (Or.inr rfl))
            exact Or.inl ⟨rfl, ⟨(1, false) :: (0, true) :: (1, false) :: (1, false) :: U,
                by simp [ones],
              Or.inr (Or.inr (Or.inl ⟨_, rfl, Or.inr ⟨U, rfl⟩⟩))⟩⟩
          · by_cases h11b : Δb = 11
            · subst h11b
              rcases (ih sb (by omega)).f_11 hb' hN31Z with hH | hS
              · exact Or.inl ⟨rfl, ⟨(1, false) :: (1, false) :: Rd1, by simp [ones],
                  Or.inr (Or.inl ⟨Rd1, rfl, Or.inr hH⟩)⟩⟩
              · exact Or.inl ⟨rfl, ⟨(1, false) :: (1, false) :: Rd1, by simp [ones],
                  Or.inr (Or.inl ⟨Rd1, rfl, Or.inl hS.1⟩)⟩⟩
            · have hge14 : 14 ≤ Δb := by omega
              have hq5 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 5) + 5 := by omega
              rw [hq5]
              exact Or.inl ⟨rfl, ⟨(1, false) :: (1, false) :: (1,
                  false) :: (ones ((Δb + 2) / 3 - 5) ++ Rd1),
                by simp [ones], Or.inl ⟨ones ((Δb + 2) / 3 - 5) ++ Rd1, rfl⟩⟩⟩
      | ge3_rem2 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: (1, false) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hN31Z := noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN1Z
        have hNb := (bigFD_noNonlast0F _).1 _ _ _ hb' hN31Z
        by_cases h0b : Δb = 0
        · subst h0b
          obtain ⟨se, hse, Δe, Re, he, hce⟩ := bigF_3_inv hb'
          have hNe := (bigFD_noNonlast0F _).1 _ _ _ he hN1Z
          rcases hce with ⟨hreme, hgee, _, rfl⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_, _, _, _, hadd0,
              _⟩ | ⟨_, _, _, _, _, hadd0, _⟩
          · have hne4 : Δe ≠ 4 := ((ih se (by omega)).f1 he hNZ).2.1
            have hq1 : 1 ≤ Δe / 3 - 1 := by omega
            obtain ⟨W, hW⟩ := ones_pos_cons hq1 Re
            cases hd2 with
            | @oneF sc _ _ Δc hF =>
              have hF' : BigF sc ((2, true) :: (1, false) :: (1, false) :: (1, false) :: W) Δc R1 :=
                  by
                rw [← hW]; simpa [ones, bumpR] using hF
              have hNW : NoNonlast0F W := by
                have htmp :=
                    noNonlast0F_ones_append (Δe / 3 - 1) hNe; rw
                    [hW] at htmp; exact noNonlast0F_tail htmp
              obtain ⟨rfl, hG1⟩ := (ih sc (by omega)).f2s_111 hF' hNW
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr hG1⟩)))
          · omega
          · omega
          · omega
        · by_cases h3b : Δb = 3
          · subst h3b
            obtain ⟨U, rfl⟩ := (ih sb (by omega)).f3_36 hb' hN1Z (Or.inl rfl)
            have hNU := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb))
            obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
            have hF' : BigF sc ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) Δc R1 :=
                by simpa [ones] using hF
            obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF'
            rcases (ih s4 (by omega)).f3_11 hF4 hNU with rfl | rfl | ⟨rfl, _⟩
            · obtain ⟨se, hse, Δe, Re, he, hce⟩ := bigF_3_inv hF4
              rcases hce with ⟨hreme, hgee, _, rfl⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_, _, _, _, hadd0,
                  _⟩ | ⟨_, _, _, _, _, hadd0, _⟩
              · have hne4 : Δe ≠ 4 :=
                    ((ih se (by omega)).f1 he (noNonlast0F_cons_ne0F (x := (1,
                    false)) (by simp) hNU)).2.1
                have hq1 : 1 ≤ Δe / 3 - 1 := by omega
                obtain ⟨W, hW⟩ := ones_pos_cons hq1 Re
                exact Or.inr (Or.inr (Or.inl ⟨by omega, ⟨W, by simp [hW]⟩⟩))
              · omega
              · omega
              · omega
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))
          · by_cases h6b : Δb = 6
            · subst h6b; exact False.elim ((ih sb (by omega)).f3_1_ne6 hb' hNZ)
            · by_cases h9b : Δb = 9
              · subst h9b
                obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
                have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: Rd1) Δc R1 := by
                    simpa [ones] using hF
                rcases (ih sb (by omega)).f3_9 hb' hN1Z with ⟨U, rfl⟩ | hS
                · obtain ⟨rfl, rfl⟩ :=
                      (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                      false) :: U))
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, strong2_of_2_1_1 ((1,
                      false) :: U)⟩))))
                · obtain ⟨rfl, hS'⟩ := (ih sc (by omega)).good2_f311 hS.1 hF' hNb
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hS'⟩))))
              · by_cases h12b : Δb = 12
                · subst h12b
                  have hHead : Z = [(0, false)] ∨ (∃ W, Z = (0, true) :: W) ∨ (∃ W, Z = (1,
                      false) :: W) ∨
                      (∃ W, Z = (1, true) :: W) ∨ (∃ W, Z = (2, false) :: W) := by
                    rcases hGF with ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩ | ⟨W, rfl⟩
                    · exact Or.inr (Or.inr (Or.inl ⟨W, rfl⟩))
                    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl⟩)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨W, rfl⟩)))
                    · exact Or.inr (Or.inl ⟨(1, false) :: (1, false) :: W, rfl⟩)
                  obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
                  have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: (1,
                      false) :: Rd1) Δc R1 := by simpa [ones] using hF
                  rcases bigF_3_1_12_of_validHead ih (by omega) hb' hNZ hHead with ⟨U, rfl⟩ | hS
                  · obtain ⟨rfl, rfl⟩ :=
                        (bigFD_det _).1 _ _ _ _ _ _ hF' (bigF_3_1_1_1_0s_1_1_exists U)
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
                      strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1, false) :: (1,
                          false) :: U, rfl⟩))))⟩))))
                  · obtain ⟨rfl, _, hSf⟩ := (ih sc (by omega)).good2_f3111 hS.1 hF' hNb
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hSf hS⟩))))
                · have hge15 : 15 ≤ Δb := by omega
                  have hq6 : (Δb + 2) / 3 + 1 = ((Δb + 2) / 3 - 5) + 6 := by omega
                  rw [hq6] at hd2
                  obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
                  have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
                      false) ::
                      (ones ((Δb + 2) / 3 - 5) ++ Rd1)) Δc R1 := by simpa [ones] using hF
                  have hGZ : GoodZero111Head (ones ((Δb + 2) / 3 - 5) ++ Rd1) := by
                    cases hq : (Δb + 2) / 3 - 5 with
                    | zero =>
                      simp only [ones, List.nil_append]
                      by_cases h0s : ∃ W, Rd1 = (0, true) :: W
                      · obtain ⟨W, hW⟩ := h0s
                        exact Or.inr ((ih sb (by omega)).f_pos_0s hb' hN31Z (by omega) hW)
                      · exact Or.inl (fun W hW => h0s ⟨W, hW⟩)
                    | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
                  obtain ⟨rfl, _, hSf⟩ :=
                      (ih sc (by omega)).f3_1111 hF' (noNonlast0F_ones_append _ hNb)
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hSf hGZ⟩))))
      | ge3_rem0 hd1 hremd1 hd2 =>
        rename_i sd1 sd2 Rd1 Δd1 Δd2
        obtain ⟨sb, hsb, Δb, haddb, hb⟩ := bigD1_oneF_inv hd1
        subst haddb
        have hb' : BigF sb ((3, false) :: (1, false) :: Z) Δb Rd1 := by simpa [bumpR] using hb
        have hN31Z := noNonlast0F_cons_ne0F (x := (3, false)) (by simp) hN1Z
        have hNb := (bigFD_noNonlast0F _).1 _ _ _ hb' hN31Z
        have hne24 := (ih sb (by omega)).f3_ne24 hb' hN1Z
        have hge7 : 7 ≤ Δb := by have := ((bigFD_bounds _).1 _ _ _ hb').1; omega
        by_cases h7b : Δb = 7
        · subst h7b
          obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
          have hF' : BigF sc ((3, false) :: (1, false) :: Rd1) Δc R1 := by simpa [ones] using hF
          have hne24c :=
              (ih sc (by omega)).f3_ne24 hF' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNb)
          by_cases h0c : Δc = 0
          · subst h0c
            exact Or.inr (Or.inl ⟨by omega, bigF_3_zero_goodF2U ih (by omega) hF'
              (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNb)⟩)
          · by_cases h3c : Δc = 3
            · subst h3c
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl ((ih sc (by omega)).f3_36 hF'
                (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hNb) (Or.inl rfl))⟩)))
            · by_cases h6c : Δc = 6
              · subst h6c; exact False.elim ((ih sc (by omega)).f3_1_ne6 hF' hNb)
              · by_cases h5c : Δc = 5
                · subst h5c; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
                · by_cases h1c : Δc = 1
                  · subst h1c; exact False.elim (bigF_ne_one hF')
                  · by_cases hm1 : Δc % 3 = 1
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))
        · by_cases h10b : Δb = 10
          · subst h10b
            obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
            have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: Rd1) Δc R1 := by
                simpa [ones] using hF
            rcases (ih sc (by omega)).f3_11 hF' hNb with rfl | rfl | ⟨rfl, _⟩
            · exact Or.inr (Or.inl ⟨by omega, bigF_3_zero_goodF2U ih (by omega) hF'
                (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
                    false)) (by simp) hNb))⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
          · have hge13 : 13 ≤ Δb := by omega
            have hq5 : (Δb + 2) / 3 = ((Δb + 2) / 3 - 5) + 5 := by omega
            rw [hq5] at hd2
            obtain ⟨sc, hsc, Δc, haddc, hF⟩ := bigD1_1_1_inv hd2
            have hF' : BigF sc ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                (ones ((Δb + 2) / 3 - 5) ++ Rd1)) Δc R1 := by simpa [ones] using hF
            obtain ⟨h710, _, _⟩ := (ih sc (by omega)).f3_111 hF' (noNonlast0F_ones_append _ hNb)
            rcases h710 with rfl | rfl <;>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (by rcases h4_out with ⟨h0, _⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | ⟨h9,
          _⟩ | h8 | hm | h11 <;> omega)
      (fun h5 => ?_) (fun h0 s2 Δ2 hs2 hadd hD2 => ?_) (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
      (fun h6 s2 Δ3 hs2 hadd hF2 => ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · subst h5
      rcases h4_out with ⟨h0, _⟩ | ⟨h3, _⟩ | ⟨_, ⟨W, rfl⟩⟩ | ⟨h6, _⟩ | ⟨h9, _⟩ | h8 | hm | h11
      · omega
      · omega
      · rcases hcases with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, s2, hs2, Δ3, rfl, hF2⟩ |
            ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _⟩ | ⟨_, _, _, _, _, _, _⟩
        · omega
        · omega
        · have hF2' : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: (1,
              false) :: W) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_0s_inv hF2'
          obtain ⟨h710, _, _⟩ := (ih s4 (by omega)).f3_111 hF4
            (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))))
          rcases h710 with rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h0; subst hadd
      rcases h4_out with ⟨_, ⟨U, rfl, hSU⟩⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | ⟨h9, _⟩ | h8 | hm | h11
      · cases hD2
        exact ⟨by omega, fun _ => Good4Out.of_safeU hSU, by omega, by omega, by omega⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h3; subst hadd
      rcases h4_out with ⟨h0, _⟩ | ⟨_, ⟨U, rfl, hGFU⟩⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | ⟨h9, _⟩ | h8 | hm | h11
      · omega
      · exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head hGFU) hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · subst h6; subst hadd
      rcases h4_out with ⟨h0, _⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨_, hO⟩ | ⟨h9, _⟩ | h8 | hm | h11
      · omega
      · omega
      · omega
      · rcases hO with ⟨U, rfl⟩ | hG1
        · exact good2_f_from_6_0s11 ih hs2 hF2
              (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
        · rcases bigF_3_good1Safe ih hs2 hG1 hF2 hN1 with ⟨rfl, hO'⟩ | ⟨hm2, hge⟩
          · rcases hO' with hG2 | ⟨W, rfl⟩
            · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inl hG2⟩
            · exact ⟨by omega, by omega, by omega, by omega, fun _ => Or.inr (Or.inr ⟨W, rfl⟩)⟩
          · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · omega
      · omega
      · omega
      · omega
    · subst h9; subst hadd
      rcases h4_out with ⟨h0, _⟩ | ⟨h3, _⟩ | ⟨h5, _⟩ | ⟨h6, _⟩ | ⟨_, hS⟩ | h8 | hm | h11
      · omega
      · omega
      · omega
      · omega
      · exact good2_f_from_9_hs ih hs2 (Or.inr hS) hF2 hN1
      · omega
      · omega
      · omega
  | step_21 hG' ihG' =>
    rename_i G'
    obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_2_inv h
    have hNG' := noNonlast0F_tail (noNonlast0F_tail hN)
    have hN_b2 := noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))
    have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN_b2
    have h1' : BigF s1 ((3, false) :: G') Δ1 R1 := by simpa [bumpR] using h1
    -- Analyze BigF s1 (3 :: G') Δ1 R1 via bigF_3_inv + good2_f on G'!
    obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_3_inv h1'
    have hNa := (bigFD_noNonlast0F _).1 _ _ _ ha hNG'
    have hfg := (ih sa (by omega)).good2_f hG' ha hNG'
    refine good2_f_dispatch_high ih (le_refl m) hs1 h1 hN_b2 hcases
      (fun h2 => ((ih s1 hs1).f3_ne24 h1' hNG').1 h2)
      (fun h5 => ?_) (fun h0 s2 Δ2 hs2 hadd hD2 => ?_) (fun h3 s2 Δ3 hs2 hadd hF2 => ?_)
      (fun h6 s2 Δ3 hs2 hadd hF2 => ?_) (fun h9 s2 Δ3 hs2 hadd hF2 => ?_)
    · -- Δ1 = 5 impossible for 3 :: Good2!
      rcases hca with ⟨_, _, h0, _⟩ | ⟨hrem2, _, _, _, _, _⟩ |
          ⟨rfl, sb, hsb, Δb, haddb, hFb⟩ | ⟨hrem0, hge3, sb, hsb, Δb, haddb, hFb⟩
      · omega
      · exact False.elim (hfg.1 hrem2)
      · have h2b : Δb = 2 := by omega
        subst h2b
        cases hG' with
        | of_good1 h1g =>
          rcases h1g with rfl | ⟨_, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl,
              _⟩ | ⟨_, rfl⟩
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb) (by trivial)).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb)
                (noNonlast0F_bumpR (noNonlast0F_tail hNG'))).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb) (by trivial)).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb) (by trivial)).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb)
                (noNonlast0F_bumpR (noNonlast0F_tail hNG'))).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb)
                (noNonlast0F_bumpR (noNonlast0F_tail hNG'))).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb)
                (noNonlast0F_bumpR (noNonlast0F_tail hNG'))).1 rfl)
          · cases ha; exact False.elim
                (((ih sb (by omega)).f2s (by simpa [bumpR] using hFb)
                (noNonlast0F_bumpR (noNonlast0F_tail hNG'))).1 rfl)
          · obtain ⟨Z, rfl⟩ := bigF_ge2_zero_head ha
            have hFb' : BigF sb ((2, true) :: (1, false) :: Z) 2 R1 := by simpa [bumpR] using hFb
            rcases (ih sb (by omega)).f2s_1 hFb'
                (noNonlast0F_tail (noNonlast0F_tail hNa)) with h0 | h4 | h10 | h13 <;> omega
        | _ =>
          obtain ⟨Z, rfl⟩ := bigF_ge2_zero_head ha
          have hFb' : BigF sb ((2, true) :: (1, false) :: Z) 2 R1 := by simpa [bumpR] using hFb
          rcases (ih sb (by omega)).f2s_1 hFb'
              (noNonlast0F_tail (noNonlast0F_tail hNa)) with h0 | h4 | h10 | h13 <;> omega
      · exact False.elim
            (((ih sb (by omega)).f3_ne24 hFb (noNonlast0F_ones_append _ hNa)).1 (by omega))
    · -- Δ1 = 0 -> Good4Out!
      subst h0; subst hadd
      rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨hrem2, _, _, _, _, _⟩ | ⟨_, _, _, _, hadd0, _⟩ | ⟨_,
          _, _, _, _, hadd0, _⟩
      · cases hD2
        by_cases h4a : Δa = 4
        · subst h4a
          exact ⟨by omega, fun _ => Good4Out.step_21 (hfg.2.1 rfl), by omega, by omega, by omega⟩
        · by_cases h7a : Δa = 7
          · subst h7a
            have hSU : SafeU ((1, false) :: Ra) := by
              rcases hfg.2.2.2.1 rfl with hS | hH
              · exact Or.inr (Or.inr (Or.inl ⟨Ra, rfl, Or.inl hS.1⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨Ra, rfl, Or.inr hH⟩))
            exact ⟨by omega, fun _ => by simpa [ones, bumpR] using Good4Out.of_safeU hSU, by omega,
                by omega, by omega⟩
          · by_cases h10a : Δa = 10
            · subst h10a
              rcases hfg.2.2.2.2 rfl with hG2 | hH | ⟨W, rfl⟩
              · exact ⟨by omega, fun _ => by simpa [ones,
                                           bumpR] using Good4Out.of_safeU (Or.inr (Or.inl ⟨Ra, rfl,
                                           Or.inl hG2⟩)), by omega, by omega, by omega⟩
              · exact ⟨by omega, fun _ => by
                    simpa [ones, bumpR] using
                      Good4Out.of_safeU (Or.inr (Or.inl ⟨Ra, rfl, Or.inr hH⟩)),
                  by omega, by omega, by omega⟩
              · exact ⟨by omega, fun _ => by
                    simpa [ones, bumpR] using Good4Out.of_1_1_1s W,
                  by omega, by omega, by omega⟩
            · have hge13 : 13 ≤ Δa := by omega
              have hq3 : Δa / 3 - 1 = (Δa / 3 - 4) + 3 := by omega
              rw [hq3]
              exact ⟨by omega, fun _ => by
                    simpa [ones, bumpR] using
                      Good4Out.of_safeU (Or.inl ⟨ones (Δa / 3 - 4) ++ Ra, rfl⟩),
                  by omega, by omega, by omega⟩
      · omega
      · omega
      · omega
    · -- Δ1 = 3 -> f3_3_non0s -> Safe0s!
      subst h3; subst hadd
      obtain ⟨U, rfl, hSU⟩ := (ih s1 hs1).f3_3_non0s h1' hNG' (good2_ne_zeroT hG')
      exact good2_f_from_3_0s11 ih hs2 (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · -- Δ1 = 6 -> f3_36 -> Head0s11!
      subst h6; subst hadd
      obtain ⟨U, rfl⟩ := (ih s1 hs1).f3_36 h1' hNG' (Or.inr rfl)
      exact good2_f_from_6_0s11 ih hs2 hF2
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
    · -- Δ1 = 9 -> f3_9 -> Head0s11 ∨ Strong2!
      subst h9; subst hadd
      exact good2_f_from_9_hs ih hs2 ((ih s1 hs1).f3_9 h1' hNG') hF2 hN1

theorem step_good2_f1 {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF m ((1, false) :: G) Δ R_fin) (hN : NoNonlast0F G) :
    Δ = 0 ∨ (Δ = 9 ∧ Good2 R_fin) ∨ (Δ = 12 ∧ Strong2 R_fin) ∨ (Δ % 3 = 0 ∧ 15 ≤ Δ) := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_1_inv h
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN
  have hfg := (ih s1 hs1).good2_f hG h1 hN
  rcases hcases with ⟨_, rfl, _⟩ |
      ⟨hrem1, hge4, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨rfl, _, _, _, _, _⟩ |
      ⟨hrem2, _, _, _, _, _, _⟩
  · exact Or.inl rfl
  · by_cases h4e : Δ1 = 4
    · subst h4e
      have hF2' : BigF s2 ((3, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
      rcases bigF_3_good4Out ih hs2 (hfg.2.1 rfl) hF2' hN1 with ⟨rfl, hG2⟩ | ⟨hm, hge13⟩
      · exact Or.inr (Or.inl ⟨rfl, hG2⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · by_cases h7e : Δ1 = 7
      · subst h7e
        have hF2' : BigF s2 ((3, false) :: (1, false) :: R1) Δ3 R_fin := by simpa [ones] using hF2
        rcases hfg.2.2.2.1 rfl with hS | ⟨U, rfl⟩
        · have ⟨h710, hSf⟩ := (ih s2 hs2).good2_f31 hS.1 hF2' hN1
          have hS' := hSf hS
          rcases h710 with rfl | ⟨rfl, _⟩
          · exact Or.inr (Or.inl ⟨rfl, hS'.1⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, hS'⟩))
        · obtain ⟨s4, hs4, Δ4, rfl, hF4⟩ := bigF_3_1_0s_inv hF2'
          obtain ⟨rfl, hG1⟩ :=
              (ih s4 (by omega)).f2s_111 hF4
              (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))
          exact Or.inr (Or.inl ⟨rfl, good1Safe_to_good2 hG1⟩)
      · by_cases h10e : Δ1 = 10
        · subst h10e
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
              simpa [ones] using hF2
          rcases hfg.2.2.2.2 rfl with hG2 | ⟨U, rfl⟩ | ⟨W, rfl⟩
          · obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
            exact Or.inr (Or.inl ⟨rfl, hS'.1⟩)
          · obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            exact Or.inr (Or.inl ⟨rfl, good2_of_2_1_1 ((1, false) :: U)⟩)
          · obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_3_1_1_1s_exists W)
            exact Or.inr (Or.inl ⟨rfl, good2_of_2_0s (bumpR W)⟩)
        · have hge13 : 13 ≤ Δ1 := by omega
          have hq3 : Δ1 / 3 - 1 = (Δ1 / 3 - 4) + 3 := by omega
          rw [hq3] at hF2
          have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1,
              false) :: (ones (Δ1 / 3 - 4) ++ R1)) Δ3 R_fin := by
            simpa [ones] using hF2
          obtain ⟨h710, hG2', hS10⟩ := (ih s2 hs2).f3_111 hF2' (noNonlast0F_ones_append _ hN1)
          rcases h710 with rfl | rfl
          · exact Or.inr (Or.inl ⟨rfl, hG2'⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, hS10 rfl⟩))
  · exact False.elim (hfg.1 (by omega))
  · exact False.elim (hfg.1 hrem2)

theorem step_good2_f11 {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF m ((1, false) :: (1, false) :: G) Δ R_fin) (hN : NoNonlast0F G) :
    Δ = 0 := by
  obtain ⟨s1, hs1, Δ1, R1, h1, hcases⟩ := bigF_1_inv h
  have hf1 := (ih s1 hs1).good2_f1 hG h1 hN
  rcases hcases with ⟨_, rfl, _⟩ | ⟨hrem1, _, _, _, _, _, _⟩ | ⟨rfl, _, _, _, _, _⟩ | ⟨hrem2, _, _,
      _, _, _, _⟩
  · rfl
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega

theorem step_good2_f31 {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF m ((3, false) :: (1, false) :: G) Δ R_fin) (hN : NoNonlast0F G) :
    (Δ = 7 ∨ (Δ = 10 ∧ Good2 R_fin)) ∧ (Strong2 G → Strong2 R_fin) := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have hN1G := noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN
  have hN1 := (bigFD_noNonlast0F _).1 _ _ _ h1 hN1G
  have hf1 := (ih s1 hs1).good2_f1 hG h1 hN
  rcases hcases with ⟨hrem1, _, _, _⟩ |
      ⟨hrem2, _, _, _, _, _⟩ |
      ⟨rfl, s2, hs2, Δ3, rfl, hF2⟩ |
      ⟨hrem0, hge3, s2, hs2, Δ3, rfl, hF2⟩
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · rcases hf1 with h0 | ⟨h9, _⟩ | ⟨h12, _⟩ | ⟨hm, _⟩ <;> omega
  · -- Δ0 = 0: inspect h1 : BigF s1 (1 :: G) 0 R1
    cases h1 with
    | oneF_rem1 hg hremg =>
      rename_i sg Rg Δg
      have hNg := (bigFD_noNonlast0F _).1 _ _ _ hg hN
      by_cases h0g : Δg = 0
      · subst h0g
        cases hG with
        | of_good1 h1g =>
          rcases h1g with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl,
              hGF⟩ | ⟨Z, rfl⟩
          · cases hg
            have hF2' : BigF s2 [(2, true), (0, true), (1, true), (0, false)] Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(1, true), (0, false)])
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1s_0⟩
          · cases hg
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, true) :: (0, true) :: Z) Δ3 R_fin :=
                by simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((1, true) :: (0,
                true) :: Z))
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1s_0s Z⟩
          · cases hg
            have hF2' : BigF s2 [(2, true), (0, true), (1, true), (1, false)] Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(1, true), (1, false)])
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1s_1⟩
          · cases hg
            have hF2' : BigF s2 [(2, true), (0, true), (1, true), (1, false), (0,
                false)] Δ3 R_fin := by simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(1, true), (1, false), (0,
                false)])
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1s_1_0⟩
          · cases hg
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, true) :: (1, false) :: (0,
                true) :: Z) Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((1, true) :: (1,
                false) :: (0, true) :: Z))
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1s_1_0s Z⟩
          · cases hg
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, true) :: (1, false) :: (1,
                false) :: Z) Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((1, true) :: (1,
                false) :: (1, false) :: Z))
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1s_1_1 Z⟩
          · cases hg
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (2, false) :: (1, false) :: (0,
                true) :: (1, false) :: (1, false) :: Z) Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
              (bigF_2s_0s_full_exists ((2, false) :: (1, false) :: (0, true) :: (1, false) :: (1,
                  false) :: Z))
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_2_1_0s_1_1 Z⟩
          · cases hg
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (2, false) :: (1, false) :: (1,
                false) :: Z) Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
              (bigF_2s_0s_full_exists ((2, false) :: (1, false) :: (1, false) :: Z))
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_2_1_1_gf hGF⟩
          · -- 2 :: 1 :: 1 :: Z
            obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
            rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                _⟩ |
                ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
            · have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                  simpa [ones, bumpR] using hF2
              obtain ⟨rfl, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
              have hne4 : Δa ≠ 4 := ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
                (noNonlast0F_cons_ne0F (x := (1,
                    false)) (by simp)
                    (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))).2
              have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
              rw [hq2]
              exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
            · omega
            · omega
            · omega
            · omega
            · omega
        | c_2_0s U =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          have hNU := noNonlast0F_tail (noNonlast0F_tail hN)
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            refine ⟨Or.inl rfl, fun hS => ?_⟩
            by_cases h4a : Δa = 4
            · subst h4a
              have ha' : BigF sa ((2, true) :: U) 4 Ra := by simpa [bumpR] using ha
              have hG2 := bigF_2s_4_good2_of_strongHead ih (by omega) (hS.2 U rfl) ha' hNU
              exact ⟨by simpa [ones] using hG2, fun _ hEq => by simp [ones] at hEq⟩
            · have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
              rw [hq2]
              exact strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_0 =>
          obtain ⟨_, hEx⟩ := bigF_2_0_exists
          obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
          have hF2' : BigF s2 [(2, true), (0, true), (1, false), (1, false)] Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
          obtain ⟨rfl, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(1, false), (1, false)])
          exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 []⟩
        | c_2_1 =>
          obtain ⟨_, hEx⟩ := bigF_2_1_nil_exists
          obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
          have hF2' : BigF s2 [(2, true), (0, true), (1, false), (1, false), (1, false)] Δ3 R_fin :=
              by simpa [ones, bumpR] using hF2
          obtain ⟨rfl, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(1, false), (1, false), (1,
              false)])
          exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 [(1, false)]⟩
        | c_2_1_2 =>
          obtain ⟨_, hEx⟩ := bigF_2_1_2_exists
          obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
          omega
        | c_2_1s_0 =>
          obtain ⟨_, hEx⟩ := bigF_2_1s_0_exists
          obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
          have hF2' : BigF s2 [(2, true), (0, true), (1, false), (1, false), (1, false), (1,
              false)] Δ3 R_fin := by
            simpa [ones, bumpR] using hF2
          obtain ⟨rfl, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(1, false), (1, false), (1,
              false), (1, false)])
          exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 [(1, false), (1, false)]⟩
        | c_2_1s_0s Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · obtain ⟨sb, _, Δb, haddb, hb⟩ :=
                bigF_3s_inv (by simpa [bumpR] using ha : BigF sa ((3, true) :: (0,
                true) :: Z) Δa Ra)
            have hne4 : Δa ≠ 4 := by
              intro h4
              have h1b : Δb = 1 := by omega
              rw [h1b] at hb
              exact bigF_ne_one hb
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_1s_1 =>
          obtain ⟨_, _, hEx⟩ := bigF_2_1s_1_exists
          obtain ⟨h13, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
          omega
        | c_2_1s_1_0 =>
          obtain ⟨_, hEx⟩ := bigF_2_1s_1_0_exists
          obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
          have hF2' : BigF s2 [(2, true), (0, true), (1, false), (1, false), (1, false), (1, false),
              (2, false)] Δ3 R_fin := by
            simpa [ones, bumpR] using hF2
          obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
            (bigF_2s_0s_full_exists [(1, false), (1, false), (1, false), (1, false), (2, false)])
          exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 [(1, false), (1, false), (2, false)]⟩
        | c_2_1s_1_0s Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · obtain ⟨sb, _, Δb, haddb, hb⟩ :=
                bigF_3s_inv (by simpa [bumpR] using ha : BigF sa ((3, true) :: (1, false) :: (0,
                true) :: Z) Δa Ra)
            have hne4 : Δa ≠ 4 := by
              intro h4
              have h1b : Δb = 1 := by omega
              rw [h1b] at hb
              exact bigF_ne_one hb
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_1s_1_1 Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · obtain ⟨sb, _, Δb, haddb, hb⟩ :=
                bigF_3s_inv (by simpa [bumpR] using ha : BigF sa ((3, true) :: (1, false) :: (1,
                false) :: Z) Δa Ra)
            have hne4 : Δa ≠ 4 := by
              intro h4
              have h1b : Δb = 1 := by omega
              rw [h1b] at hb
              exact bigF_ne_one hb
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_1_0s Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
              (noNonlast0F_tail (noNonlast0F_tail hN))).2
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_1_1 Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
              (noNonlast0F_tail (noNonlast0F_tail hN))).2
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_1_1s Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
              (noNonlast0F_tail (noNonlast0F_tail hN))).2
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_2_0s_1_1 Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := fun h4 =>
              bigF_4_ne4 ih (s := sa) (by omega)
                (by subst h4; simpa [bumpR] using ha)
                (noNonlast0F_tail (noNonlast0F_tail hN))
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_2_1_0s_1_1 Z =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := fun h4 =>
              bigF_4_ne4 ih (s := sa) (by omega)
                (by subst h4; simpa [bumpR] using ha)
                (noNonlast0F_tail (noNonlast0F_tail hN))
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | c_2_2_1_1_gf hGF =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := fun h4 =>
              bigF_4_ne4 ih (s := sa) (by omega)
                (by subst h4; simpa [bumpR] using ha)
                (noNonlast0F_tail (noNonlast0F_tail hN))
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
        | step_21 hG' =>
          obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
          rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩ |
              ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
          · have hne4 : Δa ≠ 4 := ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
              (noNonlast0F_tail (noNonlast0F_tail hN))).2
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (ones (Δa / 3) ++ Ra)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists (ones (Δa / 3) ++ Ra))
            have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
            rw [hq2]
            exact ⟨Or.inl rfl, fun _ => strong2_of_2_1_1 (ones (Δa / 3 - 2) ++ Ra)⟩
          · omega
          · omega
          · omega
          · omega
          · omega
      · by_cases h3g : Δg = 3
        · subst h3g
          have hRg : ∃ U, Rg = (0, true) :: (1, false) :: (1, false) :: U ∧ GoodF2U U := by
            cases hG with
            | of_good1 h1g =>
              rcases h1g with rfl | ⟨_, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl,
                  _⟩ | ⟨_, rfl⟩
              · cases hg
              · cases hg
              · cases hg
              · cases hg
              · cases hg
              · cases hg
              · cases hg
              · cases hg
              · exact bigF_2_3_goodF2U ih (by omega) hg (noNonlast0F_tail hN)
            | _ => exact bigF_2_3_goodF2U ih (by omega) hg (noNonlast0F_tail hN)
          obtain ⟨U, rfl, hGFU⟩ := hRg
          have hF2' : BigF s2 ((2, true) :: (1, false) :: (0, true) :: (1, false) :: (1,
              false) :: U) Δ3 R_fin := by
            simpa [ones, bumpR] using hF2
          obtain ⟨rfl, rfl⟩ :=
              (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_1_0s_exists ((1, false) :: (1, false) :: U))
          exact ⟨Or.inl rfl, fun _ => good1Safe_to_strong2 (good1Safe_of_1s_1_1_1 hGFU)⟩
        · by_cases h6g : Δg = 6
          · subst h6g
            obtain ⟨U, rfl⟩ := ((ih sg (by omega)).good2_f hG hg hN).2.2.1 rfl
            have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (0, true) :: (1,
                false) :: (1, false) :: U) Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_1_1_0s_exists ((1, false) :: (1,
                false) :: U))
            exact ⟨Or.inl rfl, fun _ => good1Safe_to_strong2 (good1Safe_of_1s_0s_1_1 ((1,
                false) :: U))⟩
          · have hge9 : 9 ≤ Δg := by omega
            have hq3 : (1 + Δg) / 3 = ((1 + Δg) / 3 - 3) + 3 := by omega
            rw [hq3] at hF2
            have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1,
                false) :: (ones ((1 + Δg) / 3 - 3) ++ Rg)) Δ3 R_fin := by
              simpa [ones, bumpR] using hF2
            obtain ⟨rfl, hG1⟩ := (ih s2 hs2).f2s_111 hF2' (noNonlast0F_ones_append _ hNg)
            exact ⟨Or.inl rfl, fun _ => good1Safe_to_strong2 hG1⟩
    | oneF_rem2 hg _ hg2 =>
      have hge := bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))
      omega
  · -- Δ0 % 3 = 0, ≥ 3 -> Δ0 ∈ {9, 12, ≥15}
    rcases hf1 with h0 | ⟨rfl, hG2⟩ | ⟨rfl, hS2⟩ | ⟨_, hge15⟩
    · omega
    · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin := by
          simpa [ones] using hF2
      obtain ⟨rfl, hS'⟩ := (ih s2 hs2).good2_f311 hG2 hF2' hN1
      exact ⟨Or.inr ⟨rfl, hS'.1⟩, fun _ => hS'⟩
    · have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: R1) Δ3 R_fin :=
          by simpa [ones] using hF2
      obtain ⟨rfl, hG', hSf⟩ := (ih s2 hs2).good2_f3111 hS2.1 hF2' hN1
      have hS' := hSf hS2
      exact ⟨Or.inr ⟨rfl, hG'⟩, fun _ => hS'⟩
    · have hq4 : Δ0 / 3 - 1 = (Δ0 / 3 - 5) + 4 := by omega
      rw [hq4] at hF2
      have hF2' : BigF s2 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1,
          false) :: (ones (Δ0 / 3 - 5) ++ R1)) Δ3 R_fin := by
        simpa [ones] using hF2
      have hGZ : GoodZero111Head (ones (Δ0 / 3 - 5) ++ R1) := by
        cases hq : Δ0 / 3 - 5 with
        | zero =>
          simp only [ones, List.nil_append]
          by_cases h0s : ∃ W, R1 = (0, true) :: W
          · obtain ⟨W, hW⟩ := h0s
            exact Or.inr ((ih s1 hs1).f_pos_0s h1 hN1G (by omega) hW)
          · exact Or.inl (fun Z hZ => h0s ⟨Z, hZ⟩)
        | succ k => exact Or.inl (fun _ hEq => by simp [ones] at hEq)
      obtain ⟨rfl, hG', hSf⟩ := (ih s2 hs2).f3_1111 hF2' (noNonlast0F_ones_append _ hN1)
      exact ⟨Or.inr ⟨rfl, hG'⟩, fun _ => hSf hGZ⟩

theorem step_good2_f311 {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF m ((3, false) :: (1, false) :: (1,
        false) :: G) Δ R_fin) (hN : NoNonlast0F G) :
    Δ = 7 ∧ Strong2 R_fin := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have h0 : Δ0 = 0 := (ih s1 hs1).good2_f11 hG h1 hN
  subst h0
  rcases hcases with ⟨hrem, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨_, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, hge, _, _, _, _, _⟩
  · omega
  · omega
  · cases h1 with
    | @oneF_rem1 s1f _ R1f Δ1f h1f _ =>
      have hN1f :=
          (bigFD_noNonlast0F _).1 _ _ _ h1f (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN)
      rcases (ih s1f (by omega)).good2_f1 hG h1f hN with rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, hge15⟩
      · cases h1f with
        | @oneF_rem1 sg _ Rg Δg hg _ =>
          by_cases h0g : Δg = 0
          · subst h0g
            cases hG with
            | of_good1 h1g =>
              rcases h1g with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl,
                  _⟩ | ⟨Z, rfl⟩
              · cases hg
                have hF2' : BigF s2 [(2, true), (0, true), (0, true), (1, true), (0,
                    false)] Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(0, true), (1, true),
                    (0, false)])
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨[(0, false)],
                    rfl⟩)))))⟩
              · cases hg
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1, true) :: (0,
                    true) :: Z) Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                    true) :: (0, true) :: Z))
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(0, true) :: Z,
                    rfl⟩)))))⟩
              · cases hg
                have hF2' : BigF s2 [(2, true), (0, true), (0, true), (1, true), (1,
                    false)] Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(0, true), (1, true),
                    (1, false)])
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨[(1, false)],
                    rfl⟩)))))⟩
              · cases hg
                have hF2' : BigF s2 [(2, true), (0, true), (0, true), (1, true), (1, false), (0,
                    false)] Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists [(0, true), (1, true),
                    (1, false), (0, false)])
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨[(1, false),
                    (0, false)], rfl⟩)))))⟩
              · cases hg
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1, true) :: (1,
                    false) :: (0, true) :: Z) Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                    true) :: (1, false) :: (0, true) :: Z))
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1,
                    false) :: (0, true) :: Z, rfl⟩)))))⟩
              · cases hg
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1, true) :: (1,
                    false) :: (1, false) :: Z) Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                    true) :: (1, false) :: (1, false) :: Z))
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(1,
                    false) :: (1, false) :: Z, rfl⟩)))))⟩
              · cases hg
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (2, false) :: (1,
                    false) :: (0, true) :: (1, false) :: (1, false) :: Z) Δ3 R_fin := by
                  simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
                  (bigF_2s_0s_full_exists ((0, true) :: (2, false) :: (1, false) :: (0, true) :: (1,
                      false) :: (1, false) :: Z))
                exact ⟨rfl,
                    strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (good2_of_2_1_0s ((1,
                    false) :: (1, false) :: Z)))))))⟩
              · cases hg
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (2, false) :: (1,
                    false) :: (1, false) :: Z) Δ3 R_fin := by
                  simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
                  (bigF_2s_0s_full_exists ((0, true) :: (2, false) :: (1, false) :: (1,
                      false) :: Z))
                exact ⟨rfl,
                    strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (good2_of_2_1_1 Z))))))⟩
              · obtain ⟨Z', rfl⟩ := bigF_ge2_zero_head hg
                have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1,
                    false) :: Z') Δ3 R_fin := by simpa [ones, bumpR] using hF2
                obtain ⟨rfl, rfl⟩ :=
                    (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                    false) :: Z'))
                exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z', rfl⟩))))⟩
            | _ =>
              obtain ⟨Z', rfl⟩ := bigF_ge2_zero_head hg
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1,
                  false) :: Z') Δ3 R_fin := by simpa [ones, bumpR] using hF2
              obtain ⟨rfl, rfl⟩ :=
                  (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                  false) :: Z'))
              exact ⟨rfl, strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z', rfl⟩))))⟩
          · by_cases h3g : Δg = 3
            · subst h3g
              have hRg : Head0s11 Rg := by
                cases hG with
                | of_good1 h1g =>
                  rcases h1g with rfl | ⟨_, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_,
                      rfl, _⟩ | ⟨_, rfl⟩
                  · cases hg
                  · cases hg
                  · cases hg
                  · cases hg
                  · cases hg
                  · cases hg
                  · cases hg
                  · cases hg
                  · exact bigF_2_3_head0s11 ih (by omega) hg (noNonlast0F_tail hN)
                | _ => exact bigF_2_3_head0s11 ih (by omega) hg (noNonlast0F_tail hN)
              obtain ⟨U, rfl⟩ := hRg
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (0, true) :: (1,
                  false) :: (1, false) :: U) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
              obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
                (bigF_2s_0s_full_exists ((1, false) :: (0, true) :: (1, false) :: (1, false) :: U))
              exact ⟨rfl, strong2_of_2_1_0s ((1, false) :: (1, false) :: U)⟩
            · have hge6 : 6 ≤ Δg := by omega
              have hq2 : (1 + Δg) / 3 = ((1 + Δg) / 3 - 2) + 2 := by omega
              rw [hq2] at hF2
              have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1,
                  false) :: (ones ((1 + Δg) / 3 - 2) ++ Rg)) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
              obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
                (bigF_2s_0s_full_exists ((1, false) :: (1,
                    false) :: (ones ((1 + Δg) / 3 - 2) ++ Rg)))
              exact ⟨rfl, strong2_of_2_1_1 (ones ((1 + Δg) / 3 - 2) ++ Rg)⟩
        | oneF_rem2 hg _ hg2 =>
          have hge := bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))
          omega
      · have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) :: R1f) Δ3 R_fin :=
            by
          simpa [ones, bumpR] using hF2
        obtain ⟨rfl, hG1⟩ := (ih s2 hs2).f2s_111 hF2' hN1f
        exact ⟨rfl, good1Safe_to_strong2 hG1⟩
      · have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1, false) :: (1,
            false) :: R1f) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
        obtain ⟨rfl, hG1⟩ :=
            (ih s2 hs2).f2s_111 hF2' (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) hN1f)
        exact ⟨rfl, good1Safe_to_strong2 hG1⟩
      · have hq3 : (1 + Δ1f) / 3 = ((1 + Δ1f) / 3 - 3) + 3 := by omega
        rw [hq3] at hF2
        have hF2' : BigF s2 ((2, true) :: (1, false) :: (1, false) :: (1,
            false) :: (ones ((1 + Δ1f) / 3 - 3) ++ R1f)) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
        obtain ⟨rfl, hG1⟩ := (ih s2 hs2).f2s_111 hF2' (noNonlast0F_ones_append _ hN1f)
        exact ⟨rfl, good1Safe_to_strong2 hG1⟩
    | oneF_rem2 h1f _ h12 =>
      have hge := bigD1_ge2_of_ne_nil h12 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1f))
      omega
  · omega

theorem step_good2_f3111 {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good2 G) (h : BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: G) Δ R_fin)
    (hN : NoNonlast0F G) :
    Δ = 7 ∧ Good2 R_fin ∧ (Strong2 G → Strong2 R_fin) := by
  obtain ⟨s1, hs1, Δ0, R1, h1, hcases⟩ := bigF_3_inv h
  have h1_zero : Δ0 = 0 ∧ ∃ s11 < s1, ∃ R11, R1 = (0, true) :: R11 ∧
      BigF s11 ((1, false) :: (1, false) :: G) 0 R11 := by
    cases h1 with
    | oneF_rem1 h11 _ =>
      have h0 := (ih _ (by omega)).good2_f11 hG h11 hN
      subst h0; exact ⟨rfl, _, by omega, _, by simp [ones], h11⟩
    | oneF_rem2 h11 _ _ =>
      have h0 := (ih _ (by omega)).good2_f11 hG h11 hN; omega
    | oneF_rem0 h11 _ _ =>
      have h0 := (ih _ (by omega)).good2_f11 hG h11 hN; omega
  obtain ⟨rfl, s11, hs11, R11, rfl, h11⟩ := h1_zero
  rcases hcases with ⟨hrem, _, _, _⟩ | ⟨hrem, _, _, _, _, _⟩ |
      ⟨_, s2, hs2, Δ3, rfl, hF2⟩ | ⟨_, hge, _, _, _, _, _⟩
  · omega
  · omega
  · cases h11 with
    | @oneF_rem1 s1f _ R1f Δ1f h1f _ =>
      rcases (ih s1f (by omega)).good2_f1 hG h1f hN with rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, hge15⟩
      · cases h1f with
        | @oneF_rem1 sg _ Rg Δg hg _ =>
          by_cases h0g : Δg = 0
          · subst h0g
            -- R1 = 0* :: 0* :: 0* :: Rg -> bump2 R1 = 2* :: 0* :: 0* :: Rg -> R_fin = 2 :: 0* ::
            -- Rg!
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: Rg) Δ3 R_fin := by
                simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: Rg))
            refine ⟨rfl, good2_of_2_0s Rg, fun hS => strong2_of_2_0s ?_⟩
            cases hG with
            | of_good1 h1g =>
              rcases h1g with rfl | ⟨Z, rfl⟩ | rfl | rfl | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl⟩ | ⟨Z, rfl,
                  hGF⟩ | ⟨Z, rfl⟩
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨[(1, true), (0, false)], rfl,
                    Or.inr Good2.c_2_1s_0⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨(1, true) :: (0, true) :: Z, rfl,
                    Or.inr (Good2.c_2_1s_0s Z)⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨[(1, true), (1, false)], rfl,
                    Or.inr Good2.c_2_1s_1⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨[(1, true), (1, false), (0, false)], rfl,
                    Or.inr Good2.c_2_1s_1_0⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨(1, true) :: (1, false) :: (0, true) :: Z,
                    rfl, Or.inr (Good2.c_2_1s_1_0s Z)⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨(1, true) :: (1, false) :: (1, false) :: Z,
                    rfl, Or.inr (Good2.c_2_1s_1_1 Z)⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨(2, false) :: (1, false) :: (0, true) :: (1,
                    false) :: (1, false) :: Z, rfl,
                  Or.inr (Good2.c_2_2_1_0s_1_1 Z)⟩))
              · cases hg; exact Or.inr (Or.inr (Or.inl ⟨(2, false) :: (1, false) :: (1, false) :: Z,
                    rfl,
                  Or.inr (Good2.c_2_2_1_1_gf hGF)⟩))
              · obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
                rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _,
                    hadd, _⟩ |
                    ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
                · have hne4 : Δa ≠ 4 := ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))).2
                  have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                  rw [hq2]
                  exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                      Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
                · omega
                · omega
                · omega
                · omega
                · omega
            | c_2_0s U =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              have hNU := noNonlast0F_tail (noNonlast0F_tail hN)
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · by_cases h4a : Δa = 4
                · subst h4a
                  have ha' : BigF sa ((2, true) :: U) 4 Ra := by simpa [bumpR] using ha
                  have hG2 := bigF_2s_4_good2_of_strongHead ih (by omega) (hS.2 U rfl) ha' hNU
                  exact Or.inr (Or.inr (Or.inl ⟨ones (4 / 3) ++ Ra, rfl,
                      Or.inr (by simpa [ones] using hG2)⟩))
                · have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                  rw [hq2]
                  exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                      Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_0 =>
              obtain ⟨_, hEx⟩ := bigF_2_0_exists
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
              exact Or.inr (Or.inr (Or.inl ⟨[(1, false), (1, false)], rfl,
                  Or.inr (Good2.c_2_1_1 [])⟩))
            | c_2_1 =>
              obtain ⟨_, hEx⟩ := bigF_2_1_nil_exists
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
              exact Or.inr (Or.inr (Or.inl ⟨[(1, false), (1, false), (1, false)], rfl,
                  Or.inr (Good2.c_2_1_1 [(1, false)])⟩))
            | c_2_1_2 =>
              obtain ⟨_, hEx⟩ := bigF_2_1_2_exists
              obtain ⟨h4, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx; omega
            | c_2_1s_0 =>
              obtain ⟨_, hEx⟩ := bigF_2_1s_0_exists
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
              exact Or.inr (Or.inr (Or.inl ⟨_, rfl, Or.inr (Good2.c_2_1_1 [(1, false), (1,
                  false)])⟩))
            | c_2_1s_0s Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · obtain ⟨sb, _, Δb, haddb, hb⟩ :=
                    bigF_3s_inv (by simpa [bumpR] using ha : BigF sa ((3, true) :: (0,
                    true) :: Z) Δa Ra)
                have hne4 : Δa ≠ 4 := by
                  intro h4
                  have h1b : Δb = 1 := by omega
                  rw [h1b] at hb
                  exact bigF_ne_one hb
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_1s_1 =>
              obtain ⟨_, _, hEx⟩ := bigF_2_1s_1_exists
              obtain ⟨h13, _⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx; omega
            | c_2_1s_1_0 =>
              obtain ⟨_, hEx⟩ := bigF_2_1s_1_0_exists
              obtain ⟨_, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hg hEx
              exact Or.inr (Or.inr (Or.inl ⟨_, rfl, Or.inr (Good2.c_2_1_1 [(1, false), (1, false),
                  (2, false)])⟩))
            | c_2_1s_1_0s Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · obtain ⟨sb, _, Δb, haddb, hb⟩ :=
                    bigF_3s_inv (by simpa [bumpR] using ha : BigF sa ((3, true) :: (1, false) :: (0,
                    true) :: Z) Δa Ra)
                have hne4 : Δa ≠ 4 := by
                  intro h4
                  have h1b : Δb = 1 := by omega
                  rw [h1b] at hb
                  exact bigF_ne_one hb
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_1s_1_1 Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · obtain ⟨sb, _, Δb, haddb, hb⟩ :=
                    bigF_3s_inv (by simpa [bumpR] using ha : BigF sa ((3, true) :: (1, false) :: (1,
                    false) :: Z) Δa Ra)
                have hne4 : Δa ≠ 4 := by
                  intro h4
                  have h1b : Δb = 1 := by omega
                  rw [h1b] at hb
                  exact bigF_ne_one hb
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_1_0s Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 :=
                    ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))).2
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_1_1 Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 :=
                    ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))).2
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_1_1s Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 :=
                    ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))).2
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_2_0s_1_1 Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 := fun h4 =>
                  bigF_4_ne4 ih (s := sa) (by omega)
                    (by subst h4; simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_2_1_0s_1_1 Z =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 := fun h4 =>
                  bigF_4_ne4 ih (s := sa) (by omega)
                    (by subst h4; simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | c_2_2_1_1_gf hGF =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 := fun h4 =>
                  bigF_4_ne4 ih (s := sa) (by omega)
                    (by subst h4; simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
            | step_21 hG' =>
              obtain ⟨sa, hsa, Δa, Ra, ha, hca⟩ := bigF_2_inv hg
              rcases hca with ⟨hrema, hgea, _, rfl⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd,
                  _⟩ |
                  ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, hadd, _⟩ | ⟨_, _, _, _, _, hadd, _⟩
              · have hne4 : Δa ≠ 4 :=
                    ((ih sa (by omega)).f3_ne24 (by simpa [bumpR] using ha)
                    (noNonlast0F_tail (noNonlast0F_tail hN))).2
                have hq2 : Δa / 3 = (Δa / 3 - 2) + 2 := by omega
                rw [hq2]
                exact Or.inr (Or.inr (Or.inl ⟨_, rfl,
                    Or.inr (Good2.c_2_1_1 (ones (Δa / 3 - 2) ++ Ra))⟩))
              · omega
              · omega
              · omega
              · omega
              · omega
          · have hq1 : 1 ≤ (1 + Δg) / 3 := by omega
            obtain ⟨W, hW⟩ := ones_pos_cons hq1 Rg
            have hF2' : BigF s2 ((2, true) :: (0, true) :: (0, true) :: (1, false) :: W) Δ3 R_fin :=
                by
              rw [← hW]; simpa [ones, bumpR] using hF2
            obtain ⟨rfl, rfl⟩ :=
                (bigFD_det _).1 _ _ _ _ _ _ hF2' (bigF_2s_0s_full_exists ((0, true) :: (1,
                false) :: W))
            exact ⟨rfl, good2_of_2_0s ((1, false) :: W),
                fun _ => strong2_of_2_0s (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl⟩))))⟩
        | oneF_rem2 hg _ hg2 =>
          have hge := bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))
          omega
      · have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1, false) :: (1,
            false) :: R1f) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
        obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
          (bigF_2s_0s_full_exists ((1, false) :: (1, false) :: (1, false) :: R1f))
        exact ⟨rfl, good2_of_2_1_1 ((1, false) :: R1f), fun _ => strong2_of_2_1_1 ((1,
            false) :: R1f)⟩
      · have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: (1,
            false) :: R1f) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
        obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
          (bigF_2s_0s_full_exists ((1, false) :: (1, false) :: (1, false) :: (1, false) :: R1f))
        exact ⟨rfl, good2_of_2_1_1 ((1, false) :: (1, false) :: R1f), fun _ => strong2_of_2_1_1 ((1,
            false) :: (1, false) :: R1f)⟩
      · have hq3 : (1 + Δ1f) / 3 = ((1 + Δ1f) / 3 - 3) + 3 := by omega
        rw [hq3] at hF2
        have hF2' : BigF s2 ((2, true) :: (0, true) :: (1, false) :: (1, false) :: (1,
            false) :: (ones ((1 + Δ1f) / 3 - 3) ++ R1f)) Δ3 R_fin := by
          simpa [ones, bumpR] using hF2
        obtain ⟨rfl, rfl⟩ := (bigFD_det _).1 _ _ _ _ _ _ hF2'
          (bigF_2s_0s_full_exists ((1, false) :: (1, false) :: (1,
              false) :: (ones ((1 + Δ1f) / 3 - 3) ++ R1f)))
        exact ⟨rfl, good2_of_2_1_1 ((1, false) :: (ones ((1 + Δ1f) / 3 - 3) ++ R1f)),
          fun _ => strong2_of_2_1_1 ((1, false) :: (ones ((1 + Δ1f) / 3 - 3) ++ R1f))⟩
    | oneF_rem2 h1f _ h12 =>
      have hge := bigD1_ge2_of_ne_nil h12 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1f))
      omega
  · omega

theorem step_good1_f3121 {m : Nat} (ih : InvLt m)
    {G : List Seg} {Δ : Nat} {R_fin : List Seg}
    (hG : Good1 G) (h : BigF m ((3, false) :: (1, false) :: (2, false) :: (1, false) :: G) Δ R_fin)
    (hN : NoNonlast0F G) :
    (Δ = 7 ∨ Δ = 10) ∧ Good2 R_fin := by
  have h21 : Good2 ((2, false) :: (1, false) :: G) := Good2.step_21 (Good2.of_good1 hG)
  have hS21 : Strong2 ((2, false) :: (1, false) :: G) := strong2_of_step_21 (Good2.of_good1 hG)
  have hN21 : NoNonlast0F ((2, false) :: (1, false) :: G) :=
    noNonlast0F_cons_ne0F (x := (2, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
        false)) (by simp) hN)
  have ⟨h710, hSf⟩ := step_good2_f31 ih h21 h hN21
  have hS' := hSf hS21
  rcases h710 with rfl | ⟨rfl, _⟩
  · exact ⟨Or.inl rfl, hS'.1⟩
  · exact ⟨Or.inr rfl, hS'.1⟩

/-! ## Master Strong Induction Closure: `invAt_all (m : Nat) : InvAt m` -/

theorem invAt_all (m : Nat) : InvAt m :=
  Nat.strongRecOn m fun _ ih =>
    { f_258 := fun h hN hΔ => step_f_258 ih h hN hΔ
      f_25_goodF2U := fun h hN hΔ => step_f_25_goodF2U ih h hN hΔ
      f_pos_0s := fun h hN hpos h0s => step_f_pos_0s ih h hN hpos h0s
      f_4_head := fun h hN => step_f_4_head ih h hN
      f_11 := fun h hN => step_f_11 ih h hN
      f3_ne24 := fun h hN => step_f3_ne24 ih h hN
      f3_36 := fun h hN hΔ => step_f3_36 ih h hN hΔ
      f3_3_non0s := fun h hN hne => step_f3_3_non0s ih h hN hne
      f3_5_0111 := fun h hN => step_f3_5_0111 ih h hN
      f3_9 := fun h hN => step_f3_9 ih h hN
      f3_1_ne6 := fun h hN => step_f3_1_ne6 ih h hN
      f3_11 := fun h hN => step_f3_11 ih h hN
      f3_111 := fun h hN => step_f3_111 ih h hN
      f3_1111 := fun h hN => step_f3_1111 ih h hN
      f1 := fun h hN => step_f1 ih h hN
      f11 := fun h hN => step_f11 ih h hN
      f111 := fun h hN => step_f111 ih h hN
      f2s := fun h hN => step_f2s ih h hN
      f2s_1 := fun h hN => step_f2s_1 ih h hN
      f2s_11 := fun h hN => step_f2s_11 ih h hN
      f2s_111 := fun h hN => step_f2s_111 ih h hN
      good2_f := fun hG h hN => step_good2_f ih hG h hN
      good2_f1 := fun hG h hN => step_good2_f1 ih hG h hN
      good2_f11 := fun hG h hN => step_good2_f11 ih hG h hN
      good2_f31 := fun hG h hN => step_good2_f31 ih hG h hN
      good2_f311 := fun hG h hN => step_good2_f311 ih hG h hN
      good2_f3111 := fun hG h hN => step_good2_f3111 ih hG h hN
      good1_f3121 := fun hG h hN => step_good1_f3121 ih hG h hN }

/-! ## Direct StrongWall Closure of `run581 n ⟨.BL0, [1, 3, 2], R⟩ ≠ none` -/

def StrongWall (R : List Seg) : Prop :=
  ∃ tail, R = (0, true) :: tail ∧ NoNonlast0F tail ∧
    ((∃ G, bumpR (bumpR tail) = (3, false) :: (1, false) :: G ∧ Strong2 G) ∨
     (∃ G, bumpR (bumpR tail) = (3, false) :: (1, false) :: (1, false) :: G ∧ Good2 G))

theorem strongWall_step (R : List Seg) (hW : StrongWall R) :
    ∃ tail, R = (0, true) :: tail ∧
      ∀ s Δ R_fin, BigF s (bumpR (bumpR tail)) Δ R_fin →
        Δ % 3 = 1 ∧ StrongWall ((0, true) :: ones (Δ / 3) ++ R_fin) := by
  obtain ⟨tail, rfl, hN, hC⟩ := hW
  refine ⟨tail, rfl, fun s Δ R_fin hF => ?_⟩
  have hNb2 := noNonlast0F_bumpR (noNonlast0F_bumpR hN)
  have hNf := (bigFD_noNonlast0F _).1 _ _ _ hF hNb2
  rcases hC with ⟨G, hEq, hS⟩ | ⟨G, hEq, hG⟩
  · rw [hEq] at hF hNb2
    have hNG := noNonlast0F_tail (noNonlast0F_tail hNb2)
    have ⟨h710, hSf⟩ := (invAt_all s).good2_f31 hS.1 hF hNG
    have hS' := hSf hS
    rcases h710 with rfl | ⟨rfl, _⟩
    · exact ⟨rfl, ⟨(1, false) :: (1, false) :: R_fin, rfl,
        noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
            false)) (by simp) hNf),
        Or.inl ⟨R_fin, by simp [bumpR], hS'⟩⟩⟩
    · exact ⟨rfl, ⟨(1, false) :: (1, false) :: (1, false) :: R_fin, rfl,
        noNonlast0F_cons_ne0F (x := (1, false)) (by simp)
          (noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
              false)) (by simp) hNf)),
        Or.inr ⟨R_fin, by simp [bumpR], hS'.1⟩⟩⟩
  · rw [hEq] at hF hNb2
    have hNG := noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb2))
    obtain ⟨rfl, hS'⟩ := (invAt_all s).good2_f311 hG hF hNG
    exact ⟨rfl, ⟨(1, false) :: (1, false) :: R_fin, rfl,
      noNonlast0F_cons_ne0F (x := (1, false)) (by simp) (noNonlast0F_cons_ne0F (x := (1,
          false)) (by simp) hNf),
      Or.inl ⟨R_fin, by simp [bumpR], hS'⟩⟩⟩

theorem strongWall_no_halt (R : List Seg) (hW : StrongWall R) :
    ∀ n, run581 n ⟨.BL0, [1, 3, 2], R⟩ ≠ none :=
  fun n => wall_no_halt_of_bigF_inv StrongWall strongWall_step n R hW


end BusyBeaver.Calculi.PairStackA
