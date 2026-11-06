/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Calculi.WordCalculusA
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word Calculus Engine B (`BusyBeaver.Calculi.WordCalculusB`)

Formal word-rewriting calculus for structured tape transformations,
providing verified macro-step reductions and tile segment chains for family B.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordCalculus
set_option quotPrecheck false
set_option maxRecDepth 4000000

variable {α β γ : Type*}
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
private abbrev t : BitWord := [1, 1, 0, 0]
private abbrev d0 : BitWord := [0, 0]
private abbrev d1 : BitWord := [1, 0]
open Word
local notation "WordList" => List Word
inductive PhaseScan : Nat -> WordList -> Nat -> WordList -> Rat -> Rat -> Prop where
  | nil (k : Nat) : PhaseScan k [] k [] 0 0
  | T {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (2 + n * 2) u k v a b ->
        PhaseScan (3 + n) (V :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair0 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (n * 2) u k v a b ->
        PhaseScan (1 + n) (Q :: K :: u) k (V :: v) (a * (1 / 2)) ((1 + b) * (1 / 2))
  | pair1 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (1 + n * 2) u k v a b ->
        PhaseScan (1 + n) (Q :: Q :: u) k (V :: v) (a * (1 / 2)) ((3 / 4) + b * (1 / 2))
  | short00 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (n * 2) u k v a b -> PhaseScan (2 + n * 4) (K :: u) k (K :: v) (3 + a * 2) (b * 2)
  | short01 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (1 + n * 2) u k v a b ->
        PhaseScan (2 + n * 4) (Q :: u) k (K :: v) (2 + a * 2) (b * 2)
  | short10 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (n * 2) u k v a b -> PhaseScan (4 + n * 4) (K :: u) k (Q :: v) (4 + a * 2) (b * 2)
  | short11 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      PhaseScan (1 + n * 2) u k v a b ->
        PhaseScan (4 + n * 4) (Q :: u) k (Q :: v) (3 + a * 2) (b * 2)
theorem phaseScan_pos_of_out_pos {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : PhaseScan k u k' v a b) (hk' : 0 < k') : 0 < k := by
  cases h <;> omega
theorem phaseScan_budget_eq {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : PhaseScan k u k' v a b) :
    (k : Rat) - 4 = ((k' : Rat) - 4) * wordScale v + 2 * (a - b) := by
  induction h with
  | nil k => simp [wordScale]
  | T _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
theorem phaseScan_loss_bounds {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : PhaseScan k u k' v a b) :
    wordMass v <= wordMass u /\ 0 <= a /\ a <= 4 * wordMass u /\ 0 <= b /\
      b <= wordMass u * (1 / 4) := by
  induction h with
  | nil _ => simp [wordMass]
  | @T n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | @pair0 n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | @pair1 n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | @short00 n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | @short01 n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | @short10 n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | @short11 n u k v a b _ ih =>
    have hw := wordMass_nonneg u
    dsimp [wordMass]; refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
theorem phaseScan_append {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h1 : PhaseScan k u k' v a b) :
    ∀ {w : WordList} {k'' : Nat} {x : WordList} {c d : Rat},
      PhaseScan k' w k'' x c d ->
      ∃ a' b', PhaseScan k (u ++ w) k'' (v ++ x) a' b' /\
        a' = a + wordScale v * c /\ b' = b + wordScale v * d := by
  induction h1 with
  | nil _ =>
    intro w k'' x c d h2
    exact ⟨c, d, h2, by simp [wordScale], by simp [wordScale]⟩
  | T _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨a' * (1 / 2), b' * (1 / 2), PhaseScan.T hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
  | pair0 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨a' * (1 / 2), (1 + b') * (1 / 2), PhaseScan.pair0 hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
  | pair1 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨a' * (1 / 2), (3 / 4) + b' * (1 / 2), PhaseScan.pair1 hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
  | short00 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨3 + a' * 2, b' * 2, PhaseScan.short00 hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
  | short01 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨2 + a' * 2, b' * 2, PhaseScan.short01 hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
  | short10 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨4 + a' * 2, b' * 2, PhaseScan.short10 hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
  | short11 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    exact ⟨3 + a' * 2, b' * 2, PhaseScan.short11 hK,
      by dsimp [wordScale]; linarith, by dsimp [wordScale]; linarith⟩
theorem exists_phaseScan_of_wordPrefix {e : Bool} {u : WordList} (hI : WordPrefix e u) :
    ∀ (k : Nat), (e = true -> ∃ n, k = n * 2) ->
      8 * wordMass u < (k : Rat) - 4 ->
      ∃ b v lp lm, PhaseScan k u b v lp lm /\ 4 < b := by
  induction hI with
  | nil e =>
    intro k _ hk
    dsimp [wordMass] at hk
    have hk_gt : (4 : Rat) < (k : Rat) := by linarith
    have hk_nat : 4 < k := by exact_mod_cast hk_gt
    exact ⟨k, [], 0, 0, PhaseScan.nil k, hk_nat⟩
  | @T e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    rcases k with _ | _ | _ | k
    · push_cast at hk; linarith
    · push_cast at hk; linarith
    · push_cast at hk; linarith
    · have h3k : k + 3 = 3 + k := by omega
      rw [h3k] at hk ⊢
      rcases ih (2 + k * 2) (fun _ => ⟨1 + k, by omega⟩)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
      exact ⟨b, V :: v, lp * (1 / 2), lm * (1 / 2), PhaseScan.T hS, hB⟩
  | @short0 u _ ih =>
    intro k hEk hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    rcases hEk rfl with ⟨n, rfl⟩
    rcases even_or_odd_mul_two n with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (a * 2) (fun _ => ⟨a, rfl⟩)
          (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
        refine ⟨b, Q :: v, 4 + lp * 2, lm * 2, ?_, hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact PhaseScan.short10 hS
    · rcases ih (a * 2) (fun _ => ⟨a, rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
      refine ⟨b, K :: v, 3 + lp * 2, lm * 2, ?_, hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact PhaseScan.short00 hS
  | @short1 u _ ih =>
    intro k hEk hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    rcases hEk rfl with ⟨n, rfl⟩
    rcases even_or_odd_mul_two n with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (1 + a * 2) (fun h => by contradiction)
          (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
        refine ⟨b, Q :: v, 3 + lp * 2, lm * 2, ?_, hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact PhaseScan.short11 hS
    · rcases ih (1 + a * 2) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
      refine ⟨b, K :: v, 2 + lp * 2, lm * 2, ?_, hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact PhaseScan.short01 hS
  | @pair0 e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k, rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
      exact ⟨b, V :: v, lp * (1 / 2), (1 + lm) * (1 / 2), PhaseScan.pair0 hS, hB⟩
  | @pair1 e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (1 + k * 2) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, lp, lm, hS, hB⟩
      exact ⟨b, V :: v, lp * (1 / 2), (3 / 4) + lm * (1 / 2), PhaseScan.pair1 hS, hB⟩
theorem exists_phaseScan_of_mass_lt (u : WordList) (k : Nat) (h : 8 * wordMass u <
    ((k * 2 : Nat) : Rat) - 4) :
    ∃ b v lp lm, PhaseScan (k * 2) u b v lp lm /\ 4 < b :=
  exists_phaseScan_of_wordPrefix (wordPrefix_true_and_cases u).1 (k * 2) (fun _ => ⟨k, rfl⟩) h
theorem scan_digitVal_loss_bound {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {l : Rat}
    (hI : Scan k u k' v l) :
    ∀ {A H : Nat}, DigitVal A H u ->
      ∃ a b, PhaseScan k u k' v a b /\ a <= 3 * wordMass v + l /\ b <= 3 * l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0, 0, PhaseScan.nil k, by simp [wordMass], by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | pair0 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2, H2, hD2, _, _⟩
    rcases ih hD2 with ⟨a, b, hJ, hP, hM⟩
    exact ⟨a * (1 / 2), (1 + b) * (1 / 2), PhaseScan.pair0 hJ,
      by dsimp [wordMass]; linarith, by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases digitVal_cons_Q_inv hD1 with ⟨A2, H2, hD2, _, _⟩
    rcases ih hD2 with ⟨a, b, hJ, hP, hM⟩
    exact ⟨a * (1 / 2), (3 / 4) + b * (1 / 2), PhaseScan.pair1 hJ,
      by dsimp [wordMass]; linarith, by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨a, b, hJ, hP, hM⟩
    exact ⟨3 + a * 2, b * 2, PhaseScan.short00 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨a, b, hJ, hP, hM⟩
    exact ⟨2 + a * 2, b * 2, PhaseScan.short01 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨a, b, hJ, hP, hM⟩
    exact ⟨4 + a * 2, b * 2, PhaseScan.short10 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨a, b, hJ, hP, hM⟩
    exact ⟨3 + a * 2, b * 2, PhaseScan.short11 hJ, by dsimp [wordMass]; linarith, by linarith⟩
theorem phaseScan_digitVal_loss_bound {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) :
    ∀ {A H : Nat}, DigitVal A H u ->
      ∃ l, Scan k u k' v l /\ a <= 3 * wordMass v + l /\ b <= 3 * l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0, Scan.nil k, by simp [wordMass], by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | pair0 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2, H2, hD2, _, _⟩
    rcases ih hD2 with ⟨l, hJ, hP, hM⟩
    exact ⟨(1 + l) * (1 / 2), Scan.pair0 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases digitVal_cons_Q_inv hD1 with ⟨A2, H2, hD2, _, _⟩
    rcases ih hD2 with ⟨l, hJ, hP, hM⟩
    exact ⟨(1 / 4) + l * (1 / 2), Scan.pair1 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hP, hM⟩
    exact ⟨1 + l * 2, Scan.short00 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hP, hM⟩
    exact ⟨l * 2, Scan.short01 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hP, hM⟩
    exact ⟨1 + l * 2, Scan.short10 hJ, by dsimp [wordMass]; linarith, by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hP, hM⟩
    exact ⟨l * 2, Scan.short11 hJ, by dsimp [wordMass]; linarith, by linarith⟩
theorem phaseScan_tailDefect_bound {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) {z : Rat} (hD : TailDefect u z) :
    wordMass v <= 1 + 2 * z /\ a <= 4 * (1 + 2 * z) /\ b <= 3 * (1 + 2 * z) := by
  rcases exists_digitVal_of_tailDefect hD with ⟨A, H, hB⟩
  rcases phaseScan_digitVal_loss_bound hI hB with ⟨l, hJ, hP, hM⟩
  rcases scan_tailDefect_bound hJ hD with ⟨hMv, hLv, _⟩
  refine ⟨by linarith, by linarith, by linarith⟩
theorem phaseScan_scale_le {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : PhaseScan k u k' v a b) : wordScale v <= wordScale u := by
  induction h with
  | nil _ => simp [wordScale]
  | T _ ih => dsimp [wordScale]; linarith
  | @pair0 _ u _ _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | @pair1 _ u _ _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | short00 _ ih => dsimp [wordScale]; linarith
  | short01 _ ih => dsimp [wordScale]; linarith
  | short10 _ ih => dsimp [wordScale]; linarith
  | short11 _ ih => dsimp [wordScale]; linarith
theorem scan_tailDefect_step_bound (u : WordList) (z : Rat) (k : Nat)
    (hD : TailDefect u z)
    (hBudget : 2 * (wordMass u + wordMassK u) < ((k * 2 : Nat) : Rat))
    (hLoss : 8 * (1 + 2 * z) < ((k * 2 : Nat) : Rat) - 4) :
    ∃ k' v a b, PhaseScan (k * 2) u k' v a b /\ 4 < k' := by
  have hEx : (wordMass u + wordMassK u) * 2 < ((k * 2 : Nat) : Rat) := by linarith
  rcases exists_scan_of_mass_lt u k hEx with ⟨k', v, l, hI, _⟩
  rcases exists_digitVal_of_tailDefect hD with ⟨A, H, hB⟩
  rcases scan_digitVal_loss_bound hI hB with ⟨a, b, hJ, _, _⟩
  refine ⟨k', v, a, b, hJ, ?_⟩
  have hTB := phaseScan_tailDefect_bound hJ hD
  have hBud := phaseScan_budget_eq hJ
  have hBnd := phaseScan_loss_bounds hJ
  have hSv := wordScale_pos v
  have hk'_gt : (4 : Rat) < (k' : Rat) := by
    have h1 : 2 * (a - b) <= 8 * (1 + 2 * z) := by linarith
    have h2 : 0 < ((k' : Rat) - 4) * wordScale v := by linarith
    nlinarith
  exact_mod_cast hk'_gt
theorem phaseScan_even_out_of_notEndsWithQ {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b
    : Rat}
    (hI : PhaseScan k u k' v a b) :
    notEndsWithQ u = true -> u ≠ [] -> ∃ n, k' = n * 2 := by
  induction hI with
  | nil _ => intro _ hNe; exact False.elim (hNe rfl)
  | @T n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : 2 + n * 2 = k0 at hSub; cases hSub; exact ⟨1 + n, by omega⟩
    | cons x u' => exact ih (notEndsWithQ_of_cons V (x :: u') hC) (by simp)
  | @pair0 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : n * 2 = k0 at hSub; cases hSub; exact ⟨n, by omega⟩
    | cons x u' =>
      have hC1 := notEndsWithQ_of_cons Q (K :: x :: u') hC
      have hC2 := notEndsWithQ_of_cons K (x :: u') hC1
      exact ih hC2 (by simp)
  | @pair1 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => contradiction
    | cons x u' =>
      have hC1 := notEndsWithQ_of_cons Q (Q :: x :: u') hC
      have hC2 := notEndsWithQ_of_cons Q (x :: u') hC1
      exact ih hC2 (by simp)
  | @short00 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : n * 2 = k0 at hSub; cases hSub; exact ⟨n, by omega⟩
    | cons x u' => exact ih (notEndsWithQ_of_cons K (x :: u') hC) (by simp)
  | @short01 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => contradiction
    | cons x u' => exact ih (notEndsWithQ_of_cons Q (x :: u') hC) (by simp)
  | @short10 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : n * 2 = k0 at hSub; cases hSub; exact ⟨n, by omega⟩
    | cons x u' => exact ih (notEndsWithQ_of_cons K (x :: u') hC) (by simp)
  | @short11 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => contradiction
    | cons x u' => exact ih (notEndsWithQ_of_cons Q (x :: u') hC) (by simp)
theorem phaseScan_split_of_splitCond {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : PhaseScan k u k' v a b) :
    ∀ (p q : WordList), u = p ++ q -> SplitCond p q ->
      ∃ m x y a1 b1 a2 b2, PhaseScan k p m x a1 b1 /\ PhaseScan m q k' y a2 b2 /\
        v = x ++ y /\ a = a1 + wordScale x * a2 /\ b = b1 + wordScale x * b2 := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨k, [], [], 0, 0, 0, 0, PhaseScan.nil k, PhaseScan.nil k, rfl, by simp [wordScale],
        by simp [wordScale]⟩
    | cons s p => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.T hI, rfl, by simp [wordScale],
        by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons V p q hP) with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl,
        hA, hB⟩
      exact ⟨m, V :: x, y, a1 * (1 / 2), b1 * (1 / 2), a2, b2, PhaseScan.T hJ, hK, rfl,
        by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.pair0 hI, rfl, by simp [wordScale],
        by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      cases p with
      | nil =>
        dsimp at hE; subst hE
        rcases hP with hP | ⟨r, hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
        have hP' := splitCond_of_cons K p q (splitCond_of_cons Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl, hA, hB⟩
        exact ⟨m, V :: x, y, a1 * (1 / 2), (1 + b1) * (1 / 2), a2, b2, PhaseScan.pair0 hJ, hK, rfl,
          by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.pair1 hI, rfl, by simp [wordScale],
        by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      cases p with
      | nil =>
        dsimp at hE; subst hE
        rcases hP with hP | ⟨r, hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
        have hP' := splitCond_of_cons Q p q (splitCond_of_cons Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl, hA, hB⟩
        exact ⟨m, V :: x, y, a1 * (1 / 2), (3 / 4) + b1 * (1 / 2), a2, b2, PhaseScan.pair1 hJ, hK,
          rfl,
          by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.short00 hI, rfl,
        by simp [wordScale], by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl,
        hA, hB⟩
      exact ⟨m, K :: x, y, 3 + a1 * 2, b1 * 2, a2, b2, PhaseScan.short00 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.short01 hI, rfl,
        by simp [wordScale], by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl,
        hA, hB⟩
      exact ⟨m, K :: x, y, 2 + a1 * 2, b1 * 2, a2, b2, PhaseScan.short01 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.short10 hI, rfl,
        by simp [wordScale], by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl,
        hA, hB⟩
      exact ⟨m, Q :: x, y, 4 + a1 * 2, b1 * 2, a2, b2, PhaseScan.short10 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, 0, _, _, PhaseScan.nil _, PhaseScan.short11 hI, rfl,
        by simp [wordScale], by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨m, x, y, a1, b1, a2, b2, hJ, hK, rfl,
        hA, hB⟩
      exact ⟨m, Q :: x, y, 3 + a1 * 2, b1 * 2, a2, b2, PhaseScan.short11 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hA]; ring, by dsimp [wordScale]; rw [hB]; ring⟩
theorem phaseScan_append_odd_Q_K_inv (r k : Nat) (u : WordList) (k' : Nat) (v : WordList) (a b :
    Rat)
    (hI : PhaseScan k (u ++ List.replicate (1 + r * 2) Q ++ [K]) k' v a b) :
    ∃ w n, v = w ++ List.replicate (1 + r) V /\ k' = n * 2 ^ (1 + r) := by
  rcases split_trailing_Q u with ⟨p, n, rfl, hP⟩
  have hE : (p ++ List.replicate n Q) ++ List.replicate (1 + r * 2) Q ++ [K] =
      p ++ (List.replicate (1 + r * 2 + n) Q ++ [K]) := by
    have heq : 1 + r * 2 + n = n + (1 + r * 2) := by omega
    rw [heq, List.replicate_add n (1 + r * 2)]; simp only [List.append_assoc]
  rw [hE] at hI
  rcases phaseScan_split_of_splitCond hI p (List.replicate (1 + r * 2 + n) Q ++ [K]) rfl (Or.inl hP)
    with ⟨m, x, y, _, _, _, _, _, hK, rfl, _, _⟩
  have hD : DigitVal ((2 ^ (1 + r * 2 + n) - 1) + 0 * 2 ^ (1 + r * 2 + n)) ((1 + r * 2 + n) + 1)
      (List.replicate (1 + r * 2 + n) Q ++ [K]) :=
    digitVal_append (digitVal_replicate_Q (1 + r * 2 + n)) (DigitVal.zero DigitVal.nil)
  rcases phaseScan_digitVal_loss_bound hK hD with ⟨l, hL, _, _⟩
  rcases scan_add_Q_K_inv n r m k' y l hL with ⟨w, q, rfl, rfl⟩
  exact ⟨x ++ w, q, by rw [List.append_assoc], rfl⟩
theorem phaseScan_replicate_V_inv (p : Nat) :
    ∀ (k k' : Nat) (v : WordList) (a b : Rat),
      PhaseScan k (List.replicate p V) k' v a b ->
      v = List.replicate p V /\ k' + 4 * 2 ^ p = k * 2 ^ p + 4 /\ a = 0 /\ b = 0 := by
  induction p with
  | zero =>
    intro k k' v a b hI
    cases hI
    exact ⟨rfl, by simp, rfl, rfl⟩
  | succ p ih =>
    intro k k' v a b hI
    cases hI with
    | @T n _ _ v0 a0 b0 hJ =>
      rcases ih (2 + n * 2) k' v0 a0 b0 hJ with ⟨rfl, hEq, rfl, rfl⟩
      refine ⟨rfl, ?_, by ring, by ring⟩
      rw [Nat.pow_succ]; ring_nf at hEq ⊢; omega
theorem digitVal_high_ones_suffix (n t0 B : Nat) (ds : WordList)
    (hD : DigitVal B (n + t0) ds) (hL : 2 ^ (n + t0) <= B + 2 ^ n) :
    ∃ u, ds = u ++ List.replicate t0 Q := by
  have hBound := lt_pow_of_digitVal hD
  have hPos := pow_two_pos t0
  rw [Nat.pow_add] at hL hBound
  let a := B - (2 ^ t0 - 1) * 2 ^ n
  have hSum : a + (2 ^ t0 - 1) * 2 ^ n = B := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    omega
  have ha_lt : a < 2 ^ n := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    omega
  rcases exists_digitVal_of_lt_pow n a ha_lt with ⟨u, hU⟩
  refine ⟨u, digitVal_unique hD ?_⟩
  rw [<- hSum]
  exact digitVal_append hU (digitVal_replicate_Q t0)
def stripWordPrefix : WordList -> WordList -> Option (WordList)
  | [], u => some u
  | V :: p, V :: u => stripWordPrefix p u
  | K :: p, K :: u => stripWordPrefix p u
  | Q :: p, Q :: u => stripWordPrefix p u
  | _, _ => none
theorem stripWordPrefix_sound (p : WordList) :
    ∀ (u v : WordList), stripWordPrefix p u = some v -> u = p ++ v := by
  induction p with
  | nil => intro u v h; injection h
  | cons w p ih =>
    intro u v h
    cases u with
    | nil => cases w <;> contradiction
    | cons x u =>
      cases w <;> cases x <;> try contradiction
      all_goals
        dsimp [stripWordPrefix] at h
        rw [ih u v h]; rfl
def isWordK : Word -> Bool
  | K => true
  | _ => false
theorem evalWords_default_of_all_K (u : WordList) (h : u.all isWordK = true) :
    evalWords u default = default := by
  induction u with
  | nil => rfl
  | cons w u ih =>
    cases w <;> try contradiction
    dsimp [List.all, isWordK] at h
    change d0 +> evalWords u default = default
    rw [ih h]
    have h0 : (0 : Fin 2) >> (default : HalfTape) = default := ListBlank.cons_head_tail default
    simp [h0]
def isDigitWord : Word -> Bool
  | V => false
  | _ => true
theorem exists_digitVal_of_all_isDigitWord (ds : WordList) (h : ds.all isDigitWord = true) :
    ∃ A, DigitVal A ds.length ds := by
  induction ds with
  | nil => exact ⟨0, DigitVal.nil⟩
  | cons w ds ih =>
    cases w
    · contradiction
    · dsimp [List.all, isDigitWord] at h
      rcases ih h with ⟨A, hI⟩
      have heq : (K :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨A * 2, DigitVal.zero hI⟩
    · dsimp [List.all, isDigitWord] at h
      rcases ih h with ⟨A, hI⟩
      have heq : (Q :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨1 + A * 2, DigitVal.one hI⟩
def bitStepNat (e : Bool) (n : Nat) : Nat := if e then 1 + n * 2 else n * 2
def halfCeil (n : Nat) : Nat := (n + 1) / 2
theorem le_halfCeil_mul_two (n : Nat) : n <= (halfCeil n) * 2 := by
  unfold halfCeil; omega
theorem rat_le_two_mul_halfCeil (n : Nat) : (n : Rat) <= 2 * ((halfCeil n : Nat) : Rat) := by
  have h := le_halfCeil_mul_two n
  have hq : (n : Rat) <= (((halfCeil n) * 2 : Nat) : Rat) := by exact_mod_cast h
  push_cast at hq
  linarith
def massUpperBound (c0 c1 : Nat) : WordList -> Nat -> Nat
  | [], n => n
  | V :: u, n => forceNat (halfCeil n) (fun m => massUpperBound c0 c1 u m)
  | K :: u, n => forceNat (n * 2 + c0) (fun m => massUpperBound c0 c1 u m)
  | Q :: u, n => forceNat (n * 2 + c1) (fun m => massUpperBound c0 c1 u m)
theorem massUpperBound_reverse_le (c0 c1 : Nat) (u : WordList) :
    ∀ (n : Nat),
      (c0 : Rat) * wordMassK u.reverse + (c1 : Rat) * wordMassQ u.reverse +
        wordScale u.reverse * (n : Rat) <=
        ((massUpperBound c0 c1 u n : Nat) : Rat) := by
  induction u with
  | nil =>
    intro n
    simp [wordMassK, wordMassQ, wordScale, massUpperBound]
  | cons w u ih =>
    intro n
    have hsp := wordScale_pos u.reverse
    cases w
    · dsimp [massUpperBound, forceNat_eq]
      rw [List.reverse_cons, wordMassK_append, wordMassQ_append, wordScale_append]
      dsimp [wordMassK, wordMassQ, wordScale]
      have hhu := rat_le_two_mul_halfCeil n
      have hih := ih (halfCeil n)
      nlinarith
    · dsimp [massUpperBound, forceNat_eq]
      rw [List.reverse_cons, wordMassK_append, wordMassQ_append, wordScale_append]
      dsimp [wordMassK, wordMassQ, wordScale]
      have hih := ih (n * 2 + c0)
      push_cast at hih
      nlinarith
    · dsimp [massUpperBound, forceNat_eq]
      rw [List.reverse_cons, wordMassK_append, wordMassQ_append, wordScale_append]
      dsimp [wordMassK, wordMassQ, wordScale]
      have hih := ih (n * 2 + c1)
      push_cast at hih
      nlinarith
theorem massUpperBound_le (c0 c1 : Nat) (u : WordList) (n : Nat) :
    (c0 : Rat) * wordMassK u + (c1 : Rat) * wordMassQ u + wordScale u * (n : Rat) <=
      ((massUpperBound c0 c1 u.reverse n : Nat) : Rat) := by
  have h := massUpperBound_reverse_le c0 c1 u.reverse n
  simpa [List.reverse_reverse] using h
def heightShift : WordList -> Nat -> Option Nat
  | [], h => some h
  | V :: u, h => heightShift u (h + 1)
  | _ :: _, 0 => none
  | _ :: u, h + 1 => heightShift u h
theorem heightShift_sound (u : WordList) :
    ∀ (h H : Nat), heightShift u h = some H ->
      wordScale u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE
    simp [wordScale]
  | cons w u ih =>
    intro h H hE
    cases w
    · dsimp [heightShift, wordScale] at hE ⊢
      have hih := ih (h + 1) H hE
      rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hih
      linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [heightShift, wordScale] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
        linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [heightShift, wordScale] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
        linarith
def splitLastVRev : WordList -> WordList -> Option (WordList × WordList)
  | [], _ => none
  | V :: u, ds => some (u.reverseAux [V], ds)
  | w :: u, ds => splitLastVRev u (w :: ds)
theorem splitLastVRev_sound (u : WordList) :
    ∀ (ds p tail : WordList), splitLastVRev u ds = some (p, tail) ->
      ds.all isDigitWord = true ->
      u.reverseAux ds = p ++ tail /\ tail.all isDigitWord = true := by
  induction u with
  | nil => intro ds p tail hE _; contradiction
  | cons w u ih =>
    intro ds p tail hE hD
    cases w
    · dsimp [splitLastVRev] at hE
      injection hE with h1; injection h1 with h1 h2; subst h1; subst h2
      refine ⟨?_, hD⟩
      simp [List.reverseAux_eq]
    · dsimp [splitLastVRev] at hE
      have hD' : (K :: ds).all isDigitWord = true := by simp [isDigitWord, hD]
      exact ih (K :: ds) p tail hE hD'
    · dsimp [splitLastVRev] at hE
      have hD' : (Q :: ds).all isDigitWord = true := by simp [isDigitWord, hD]
      exact ih (Q :: ds) p tail hE hD'
def splitPrefixDigits (u : WordList) : Option (WordList × WordList) :=
  splitLastVRev u.reverse []
theorem splitPrefixDigits_sound (u p ds : WordList) (hE : splitPrefixDigits u = some (p, ds)) :
    u = p ++ ds /\ ds.all isDigitWord = true := by
  rcases splitLastVRev_sound u.reverse [] p ds hE rfl with ⟨hU, hD⟩
  simp only [List.reverseAux_eq, List.append_nil, List.reverse_reverse] at hU
  exact ⟨hU, hD⟩
theorem replicate_reverse (n : Nat) (w : Word) : (List.replicate n w).reverse =
    List.replicate n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv_lhs => rw [replicate_succ_append, List.reverse_append, ih]
    rfl
def startsWithKOrNil : WordList -> Bool
  | [] => true
  | K :: _ => true
  | V :: _ => false
  | Q :: u => !startsWithKOrNil u
def modFourDigit (k : Nat) : Word :=
  if (k - 2) % 4 == 0 then K else Q
def evalPhaseScan : Nat -> WordList -> Nat -> Option (Nat × WordList)
  | 0, _, _ => none
  | _ + 1, [], k => some (k, [])
  | fuel + 1, V :: u, k =>
    if k < 3 then none
    else forceNat (2 + (k - 3) * 2) (fun m => match evalPhaseScan fuel u m with
    | none => none
    | some (k', v) => some (k', V :: v))
  | fuel + 1, K :: u, k =>
    if k < 2 || k % 2 != 0 then none
    else
      forceNat (((k - 2) / 4) * 2) (fun m => match evalPhaseScan fuel u m with
      | none => none
      | some (k', v) => forceWord (modFourDigit k) (fun w => some (k', w :: v)))
  | fuel + 1, Q :: u, k =>
    if k == 0 then none
    else if k % 2 == 0 && startsWithKOrNil (Q :: u) then
      forceNat (1 + ((k - 2) / 4) * 2) (fun m => match evalPhaseScan fuel u m with
      | none => none
      | some (k', v) => forceWord (modFourDigit k) (fun w => some (k', w :: v)))
    else match u with
    | K :: u' =>
      forceNat ((k - 1) * 2) (fun m => match evalPhaseScan fuel u' m with
      | none => none
      | some (k', v) => some (k', V :: v))
    | Q :: u' =>
      forceNat (1 + (k - 1) * 2) (fun m => match evalPhaseScan fuel u' m with
      | none => none
      | some (k', v) => some (k', V :: v))
    | _ => none
theorem evalPhaseScan_sound (fuel : Nat) :
    ∀ (u : WordList) (k k' : Nat) (v : WordList),
      evalPhaseScan fuel u k = some (k', v) ->
      ∃ a b, PhaseScan k u k' v a b := by
  induction fuel with
  | zero => intro u k k' v h; contradiction
  | succ fuel ih =>
    intro u k k' v h
    cases u with
    | nil =>
      dsimp [evalPhaseScan, forceNat_eq] at h
      injection h with h; injection h with hk hv; subst hk; subst hv
      exact ⟨0, 0, PhaseScan.nil k⟩
    | cons w u =>
      cases w with
      | V =>
        dsimp [evalPhaseScan, forceNat_eq] at h
        split_ifs at h with hk
        cases hrec : evalPhaseScan fuel u (2 + (k - 3) * 2) with
        | none => rw [hrec] at h; contradiction
        | some kv =>
          rw [hrec] at h
          rcases kv with ⟨k0, v0⟩
          injection h with h; injection h with hk' hv'; subst hk'; subst hv'
          rcases ih u (2 + (k - 3) * 2) k0 v0 hrec with ⟨a, b, hSub⟩
          have heq : k = 3 + (k - 3) := by omega
          rw [heq]; exact ⟨a * (1 / 2), b * (1 / 2), PhaseScan.T hSub⟩
      | K =>
        dsimp [evalPhaseScan, forceNat_eq] at h
        split_ifs at h with hk
        have hk2 : 2 <= k /\ k % 2 = 0 := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, not_lt,
            not_not] at hk
          exact hk
        cases hrec : evalPhaseScan fuel u (((k - 2) / 4) * 2) with
        | none => rw [hrec] at h; contradiction
        | some kv =>
          rw [hrec] at h
          rcases kv with ⟨k0, v0⟩
          simp only [forceWord_eq] at h
          injection h with h; injection h with hk' hv'; subst hk'; subst hv'
          rcases ih u (((k - 2) / 4) * 2) k0 v0 hrec with ⟨a, b, hSub⟩
          unfold modFourDigit
          have hmod4 : (k - 2) % 4 = 0 \/ (k - 2) % 4 = 2 := by omega
          rcases hmod4 with hm | hm
          · have hc : ((k - 2) % 4 == 0) = true := beq_iff_eq.mpr hm
            rw [hc]
            have heq : k = 2 + ((k - 2) / 4) * 4 := by omega
            rw [heq]; exact ⟨3 + a * 2, b * 2, PhaseScan.short00 hSub⟩
          · have hc : ((k - 2) % 4 == 0) = false := beq_false_of_ne (by omega)
            rw [hc]
            have heq : k = 4 + ((k - 2) / 4) * 4 := by omega
            rw [heq]; exact ⟨4 + a * 2, b * 2, PhaseScan.short10 hSub⟩
      | Q =>
        dsimp [evalPhaseScan, forceNat_eq] at h
        split_ifs at h with hk0 hks
        · have hk2 : 2 <= k /\ k % 2 = 0 := by
            simp only [beq_iff_eq] at hk0
            simp only [Bool.and_eq_true, beq_iff_eq] at hks
            omega
          cases hrec : evalPhaseScan fuel u (1 + ((k - 2) / 4) * 2) with
          | none => rw [hrec] at h; contradiction
          | some kv =>
            rw [hrec] at h
            rcases kv with ⟨k0, v0⟩
            simp only [forceWord_eq] at h
            injection h with h; injection h with hk' hv'; subst hk'; subst hv'
            rcases ih u (1 + ((k - 2) / 4) * 2) k0 v0 hrec with ⟨a, b, hSub⟩
            unfold modFourDigit
            have hmod4 : (k - 2) % 4 = 0 \/ (k - 2) % 4 = 2 := by omega
            rcases hmod4 with hm | hm
            · have hc : ((k - 2) % 4 == 0) = true := beq_iff_eq.mpr hm
              rw [hc]
              have heq : k = 2 + ((k - 2) / 4) * 4 := by omega
              rw [heq]; exact ⟨2 + a * 2, b * 2, PhaseScan.short01 hSub⟩
            · have hc : ((k - 2) % 4 == 0) = false := beq_false_of_ne (by omega)
              rw [hc]
              have heq : k = 4 + ((k - 2) / 4) * 4 := by omega
              rw [heq]; exact ⟨3 + a * 2, b * 2, PhaseScan.short11 hSub⟩
        · have hk_pos : 1 <= k := by simp only [beq_iff_eq] at hk0; omega
          cases u with
          | nil => contradiction
          | cons w2 u' =>
            cases w2 with
            | V => contradiction
            | K =>
              dsimp [forceNat_eq] at h
              cases hrec : evalPhaseScan fuel u' ((k - 1) * 2) with
              | none => rw [hrec] at h; contradiction
              | some kv =>
                rw [hrec] at h
                rcases kv with ⟨k0, v0⟩
                injection h with h; injection h with hk' hv'; subst hk'; subst hv'
                rcases ih u' ((k - 1) * 2) k0 v0 hrec with ⟨a, b, hSub⟩
                have heq : k = 1 + (k - 1) := by omega
                rw [heq]; exact ⟨a * (1 / 2), (1 + b) * (1 / 2), PhaseScan.pair0 hSub⟩
            | Q =>
              dsimp [forceNat_eq] at h
              cases hrec : evalPhaseScan fuel u' (1 + (k - 1) * 2) with
              | none => rw [hrec] at h; contradiction
              | some kv =>
                rw [hrec] at h
                rcases kv with ⟨k0, v0⟩
                injection h with h; injection h with hk' hv'; subst hk'; subst hv'
                rcases ih u' (1 + (k - 1) * 2) k0 v0 hrec with ⟨a, b, hSub⟩
                have heq : k = 1 + (k - 1) := by omega
                rw [heq]; exact ⟨a * (1 / 2), (3 / 4) + b * (1 / 2), PhaseScan.pair1 hSub⟩
theorem splitLastVRev_ends_with_V (u : WordList) :
    ∀ (ds p tail : WordList), splitLastVRev u ds = some (p, tail) ->
      ∃ v, p = v ++ [V] := by
  induction u with
  | nil => intro ds p tail hE; contradiction
  | cons w u ih =>
    intro ds p tail hE
    cases w
    · dsimp [splitLastVRev] at hE
      injection hE with h1; injection h1 with h1 h2; subst h1
      exact ⟨u.reverse, by simp [List.reverseAux_eq]⟩
    · exact ih (K :: ds) p tail hE
    · exact ih (Q :: ds) p tail hE
theorem splitPrefixDigits_ends_with_V (u p ds : WordList) (hE : splitPrefixDigits u = some (p,
    ds)) :
    ∃ v, p = v ++ [V] :=
  splitLastVRev_ends_with_V u.reverse [] p ds hE
theorem all_isDigitWord_of_digitVal {A H : Nat} {u : WordList} (h : DigitVal A H u) :
    u.all isDigitWord = true := by
  induction h with
  | nil => rfl
  | zero _ ih => simp [isDigitWord, ih]
  | one _ ih => simp [isDigitWord, ih]
theorem rat_pow_two_pos (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) := by
  exact_mod_cast pow_two_pos n
theorem wordMass_and_scale_replicate_V (n : Nat) :
    wordMass (List.replicate n V) = 0 /\
    wordScale (List.replicate n V) * ((2 ^ n : Nat) : Rat) = 1 := by
  induction n with
  | zero => simp [wordMass, wordScale]
  | succ n ih =>
    rw [List.replicate_succ, Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [wordMass, wordScale]
    refine ⟨by linarith [ih.1], ?_⟩
    calc wordScale (List.replicate n V) * (1 / 2) * (((2 ^ n : Nat) : Rat) * 2)
      _ = wordScale (List.replicate n V) * ((2 ^ n : Nat) : Rat) := by ring
      _ = 1 := ih.2
theorem wordScale_replicate_V_mul_pow (n : Nat) (x : Rat) :
    wordScale (List.replicate n V) * x * ((2 ^ n : Nat) : Rat) = x := by
  calc wordScale (List.replicate n V) * x * ((2 ^ n : Nat) : Rat)
    _ = (wordScale (List.replicate n V) * ((2 ^ n : Nat) : Rat)) * x := by ring
    _ = 1 * x := by rw [(wordMass_and_scale_replicate_V n).2]
    _ = x := by ring
theorem wordMassQ_replicate_V (q : Nat) : wordMassQ (List.replicate q V) = 0 := by
  induction q with
  | zero => simp [wordMassQ]
  | succ q ih => rw [List.replicate_succ]; dsimp [wordMassQ]; linarith
theorem exists_phaseScan_twelve (u : WordList) (A H : Nat) (ds : WordList)
    (hD : DigitVal A H ds)
    (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hCut : notEndsWithQ u = true) (hNe : u ≠ [])
    (hBound : wordMass u + wordScale u * (1 + wordMassK ds) <= 1 / 128) :
    ∃ k v a b, PhaseScan 12 (u ++ ds ++ [K]) k v a b /\ 4 < k := by
  have hWu := wordMass_nonneg u
  have hWd := wordMass_nonneg ds
  have hSu := wordScale_pos u
  have hMu : wordMass u <= 1 / 128 := by nlinarith
  rcases exists_phaseScan_of_mass_lt u 6 (by push_cast; linarith) with ⟨k0, v, a, b, hI, hK0⟩
  rcases phaseScan_even_out_of_notEndsWithQ hI hCut hNe with ⟨n, rfl⟩
  have hBudget := phaseScan_budget_eq hI
  have hLoss := phaseScan_loss_bounds hI
  have hSv := phaseScan_scale_le hI
  have hPv := wordScale_pos v
  have hCarry : 7 < (((n * 2 : Nat) : Rat) - 4) * wordScale v := by
    push_cast at hBudget ⊢; linarith
  rcases digitVal_scale_and_mass hD with ⟨hSd, hMd, hOd⟩
  have hRest : 2 * (wordMass (ds ++ [K]) + wordMassK (ds ++ [K])) * wordScale v < 7 := by
    rw [wordMass_append, wordMassK_append]
    dsimp [wordMass, wordMassK]
    have h1 : wordScale u * wordMassK ds <= 1 / 128 := by nlinarith
    have h2 : wordScale u * (3 * wordScale ds - 1 + wordMassK ds) < 4 := by nlinarith
    have h3 : 0 <= 3 * wordScale ds - 1 + wordMassK ds := by linarith
    nlinarith
  have hLoss2 : 8 * (1 + 2 * wordMassK ds) * wordScale v < 1 := by
    have h1 : wordScale u * wordMassK ds <= 1 / 128 := by nlinarith
    have h2 : wordScale u <= 1 / 128 := by nlinarith
    nlinarith
  rcases scan_tailDefect_step_bound (ds ++
    [K]) (wordMassK ds) n (tailDefect_append_K_of_digitVal hD)
      (by nlinarith) (by nlinarith) with ⟨k, w, c, d, hJ, hK'⟩
  rcases phaseScan_append hI hJ with ⟨a', b', hS, _, _⟩
  rw [<- List.append_assoc] at hS
  exact ⟨k, v ++ w, a', b', hS, hK'⟩
theorem scan_odd_Q_K_tailDefect (r a b : Nat) (v : WordList) (l : Rat) (u : WordList) (z : Rat)
    (hI : Scan a ((List.replicate (1 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : TailDefect u z) :
    wordMass v * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1 / 2) * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : SplitCond (List.replicate (1 + r * 2) Q ++ [K]) u := by
    left; rw [notEndsWithQ_append_singleton]; rfl
  rcases scan_split_of_splitCond hI (List.replicate (1 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c, x, y, s, t0, hJ, hK, rfl, hL⟩
  rcases scan_odd_Q_K_inv r a c x s hJ with ⟨rfl, _, rfl⟩
  have hTB := scan_tailDefect_bound hK hZ
  have hRT := wordMass_and_scale_replicate_V (1 + r)
  have hRF1 := wordScale_replicate_V_mul_pow (1 + r) (wordMass y)
  have hRF2 := wordScale_replicate_V_mul_pow (1 + r) t0
  have hPos := rat_pow_two_pos (1 + r)
  rw [wordMass_append]
  constructor <;> nlinarith
theorem scan_even_Q_K_tailDefect (r a b : Nat) (v : WordList) (l : Rat) (u : WordList) (z : Rat)
    (hI : Scan a ((List.replicate (2 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : TailDefect u z) :
    (wordMass v - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : SplitCond (List.replicate (2 + r * 2) Q ++ [K]) u := by
    left; rw [notEndsWithQ_append_singleton]; rfl
  rcases scan_split_of_splitCond hI (List.replicate (2 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c, x, y, s, t0, hJ, hK, rfl, hL⟩
  rcases scan_even_Q_K_inv r a c x s hJ with ⟨d, n, rfl, _, rfl⟩
  have hTB := scan_tailDefect_bound hK hZ
  have hSB := scan_mass_bounds hK
  have hGe1 : (1 : Rat) <= ((2 ^ r : Nat) : Rat) := by exact_mod_cast pow_two_pos r
  have hWy := wordMass_nonneg y
  set sc := wordScale (List.replicate (1 + r) V)
  have hMrep : wordMass (List.replicate (1 + r) V ++ y) = sc * wordMass y := by
    rw [wordMass_append, (wordMass_and_scale_replicate_V (1 + r)).1, zero_add]
  have hRF1 := wordScale_replicate_V_mul_pow (1 + r) (wordMass y)
  have hRF2 := wordScale_replicate_V_mul_pow (1 + r) t0
  have hpow : ((2 ^ (1 + r) : Nat) : Rat) = ((2 ^ r : Nat) : Rat) * 2 := by
    rw [pow_two_one_add]; push_cast; ring
  rw [hpow] at hRF1 hRF2
  have hRF1' : sc * wordMass y * ((2 ^ r : Nat) : Rat) = wordMass y * (1 / 2) := by
    change wordScale (List.replicate (1 + r) V) * wordMass y * ((2 ^ r : Nat) : Rat) =
      wordMass y * (1 / 2)
    linarith [hRF1]
  have hRF2' : sc * t0 * ((2 ^ r : Nat) : Rat) = t0 * (1 / 2) := by
    change wordScale (List.replicate (1 + r) V) * t0 * ((2 ^ r : Nat) : Rat) = t0 * (1 / 2)
    linarith [hRF2]
  simp only [List.cons_append]
  cases d with
  | V =>
    change l = 1 + (sc * (1 / 2)) * t0 at hL
    have hM : wordMass (V :: (List.replicate (1 + r) V ++ y)) = (sc * wordMass y) * (1 / 2) := by
      dsimp [wordMass]; rw [hMrep]
    rw [hM, hL]
    have h1 : ((sc * wordMass y) * (1 / 2) - 1) * ((2 ^ r : Nat) : Rat) =
      (sc * wordMass y * ((2 ^ r : Nat) : Rat)) * (1 / 2) - ((2 ^ r : Nat) : Rat) := by ring
    have h2 : (1 + (sc * (1 / 2)) * t0 - 1) * ((2 ^ r : Nat) : Rat) =
      (sc * t0 * ((2 ^ r : Nat) : Rat)) * (1 / 2) := by ring
    rw [h1, h2, hRF1', hRF2']
    constructor <;> linarith [hWy.1, hSB.1, hGe1, hTB.1, hTB.2.1]
  | K =>
    change l = 1 + (sc * 2) * t0 at hL
    have hM : wordMass (K :: (List.replicate (1 + r) V ++ y)) = 1 + (sc * wordMass y) * 2 := by
      dsimp [wordMass]; rw [hMrep]
    rw [hM, hL]
    have h1 : (1 + (sc * wordMass y) * 2 - 1) * ((2 ^ r : Nat) : Rat) =
      (sc * wordMass y * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    have h2 : (1 + (sc * 2) * t0 - 1) * ((2 ^ r : Nat) : Rat) =
      (sc * t0 * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    rw [h1, h2, hRF1', hRF2']
    constructor <;> linarith [hWy.1, hSB.1, hGe1, hTB.1, hTB.2.1]
  | Q =>
    change l = 1 + (sc * 2) * t0 at hL
    have hM : wordMass (Q :: (List.replicate (1 + r) V ++ y)) = 1 + (sc * wordMass y) * 2 := by
      dsimp [wordMass]; rw [hMrep]
    rw [hM, hL]
    have h1 : (1 + (sc * wordMass y) * 2 - 1) * ((2 ^ r : Nat) : Rat) =
      (sc * wordMass y * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    have h2 : (1 + (sc * 2) * t0 - 1) * ((2 ^ r : Nat) : Rat) =
      (sc * t0 * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    rw [h1, h2, hRF1', hRF2']
    constructor <;> linarith [hWy.1, hSB.1, hGe1, hTB.1, hTB.2.1]
theorem scan_replicate_Q_K_tailDefect (c a b : Nat) (v : WordList) (l : Rat) (u : WordList) (z :
    Rat)
    (hI : Scan a ((List.replicate c Q ++ [K]) ++ u) b v l)
    (hZ : TailDefect u z) (hC : 0 < c) :
    wordMass v * ((2 ^ (c + c / 2) : Nat) : Rat) <=
      ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) /\
    l * ((2 ^ (c + c / 2) : Nat) : Rat) <=
      ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) := by
  have hZn := tailDefect_nonneg hZ
  rcases even_or_odd_mul_two c with ⟨a0, rfl⟩ | ⟨a0, rfl⟩
  · cases a0 with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI ⊢
      have hEven := scan_even_Q_K_tailDefect r a b v l u z hI hZ
      have hP : 2 + r * 2 + (2 + r * 2) / 2 = (2 + r * 2) + r + 1 := by omega
      have hPow : ((2 ^ (2 + r * 2 + (2 + r * 2) / 2) : Nat) : Rat) =
          ((2 ^ (2 + r * 2) : Nat) : Rat) * ((2 ^ r : Nat) : Rat) * 2 := by
        rw [hP, Nat.pow_add, Nat.pow_add]; push_cast; ring
      have hPos1 := rat_pow_two_pos (2 + r * 2)
      have hPos2 := rat_pow_two_pos r
      rw [hPow]
      constructor <;> nlinarith
  · have hOdd := scan_odd_Q_K_tailDefect a0 a b v l u z hI hZ
    have hP : 1 + a0 * 2 + (1 + a0 * 2) / 2 = (1 + a0 * 2) + a0 := by omega
    have hPow : ((2 ^ (1 + a0 * 2 + (1 + a0 * 2) / 2) : Nat) : Rat) =
        ((2 ^ (1 + a0 * 2) : Nat) : Rat) * ((2 ^ a0 : Nat) : Rat) := by
      rw [hP, Nat.pow_add]; push_cast; ring
    have hPow1 : ((2 ^ (1 + a0) : Nat) : Rat) = ((2 ^ a0 : Nat) : Rat) * 2 := by
      rw [pow_two_one_add]; push_cast; ring
    rw [hPow1] at hOdd
    have hPos1 := rat_pow_two_pos (1 + a0 * 2)
    have hPos2 := rat_pow_two_pos a0
    rw [hPow]
    constructor <;> nlinarith
theorem tailDefect_replicate_Q_append_inv (c : Nat) :
    ∀ (u : WordList) (z : Rat), TailDefect (List.replicate c Q ++ u) z ->
      ∃ z', TailDefect u z' /\ z = ((2 ^ c : Nat) : Rat) * z' := by
  induction c with
  | zero =>
    intro u z hI
    exact ⟨z, hI, by simp⟩
  | succ c ih =>
    intro u z hI
    rw [List.replicate_succ, List.cons_append] at hI
    rcases tailDefect_cons_Q_inv hI with ⟨y, hJ, rfl⟩
    rcases ih u y hJ with ⟨x, hK, rfl⟩
    refine ⟨x, hK, ?_⟩
    rw [Nat.pow_succ]; push_cast; ring
theorem mul_le_add_of_le (x z p q : Rat) (hp : 0 < p) (hpq : p <= q) (hz : 0 <= z)
    (h : x * q <= q + 2 * z) : x * p <= p + 2 * z := by
  by_cases hx : x <= 1
  · nlinarith
  · nlinarith
theorem scan_digitVal_carry_bound (s c : Nat) (u : WordList) (A H a b : Nat) (v : WordList) (l :
    Rat)
    (hD : DigitVal A H (List.replicate c Q ++ K :: u))
    (hI : Scan a ((List.replicate c Q ++ K :: u) ++ [K]) b v l)
    (hC : 0 < c) (hSC : s <= c) :
    wordMass v * ((2 ^ (s + s / 2) : Nat) : Rat) <=
      ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK (List.replicate c Q ++ K :: u) /\
    l * ((2 ^ (s + s / 2) : Nat) : Rat) <=
      ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK (List.replicate c Q ++ K :: u) := by
  have hZ := tailDefect_append_K_of_digitVal hD
  rw [List.append_assoc] at hZ
  rcases tailDefect_replicate_Q_append_inv c (K :: u ++ [K]) (wordMassK (List.replicate c Q ++
    K :: u)) hZ with ⟨x, hU, hX⟩
  rcases tailDefect_cons_K_inv hU with ⟨hNil, _⟩ | ⟨z, hV, rfl⟩
  · simp at hNil
  · have hE : (List.replicate c Q ++ K :: u) ++ [K] =
        (List.replicate c Q ++ [K]) ++ (u ++ [K]) := by simp [List.append_assoc]
    rw [hE] at hI
    rcases scan_replicate_Q_K_tailDefect c a b v l (u ++ [K]) z hI hV hC with ⟨hM, hL⟩
    have hPos := rat_pow_two_pos (s + s / 2)
    have hMono : ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
    have hW := wordMass_nonneg (List.replicate c Q ++ K :: u)
    constructor
    · exact mul_le_add_of_le (wordMass v) (wordMassK (List.replicate c Q ++
      K :: u)) _ _ hPos hMono hW.2.1 (by nlinarith)
    · exact mul_le_add_of_le l (wordMassK (List.replicate c Q ++
      K :: u)) _ _ hPos hMono hW.2.1 (by nlinarith)
theorem phaseScan_digitVal_carry_bound (s : Nat) (ds : WordList) (A H k k' : Nat) (v : WordList) (a
    b : Rat)
    (hD : DigitVal A H ds) (hI : PhaseScan k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u, (0 < c /\ s <= c) /\ ds = List.replicate c Q ++ K :: u) :
    wordMass v * ((2 ^ (s + s / 2) : Nat) : Rat) <=
      ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds /\
    a * ((2 ^ (s + s / 2) : Nat) : Rat) <=
      4 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) /\
    b * ((2 ^ (s + s / 2) : Nat) : Rat) <=
      3 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) := by
  rcases hLow with ⟨c, u, ⟨hC, hSC⟩, rfl⟩
  have hFull := digitVal_append hD (DigitVal.zero DigitVal.nil)
  rcases phaseScan_digitVal_loss_bound hI hFull with ⟨l, hJ, hP, hN⟩
  have hCore := scan_digitVal_carry_bound s c u A H k k' v l hD hJ hC hSC
  have hPos := rat_pow_two_pos (s + s / 2)
  refine ⟨hCore.1, by nlinarith, by nlinarith⟩
theorem divisibility_carry_step (r J k b A B : Nat) (hR : r <= J)
    (hK : ∃ n, k = n * 2 ^ r) (hB0 : ∃ n, 1 + b = n * 2 ^ r)
    (hAsum : A + 2 ^ J = k) (hBsum : B + 2 ^ J = A + b) :
    ∃ n, 1 + B = n * 2 ^ r := by
  rcases hK with ⟨n, rfl⟩
  rcases hB0 with ⟨m, hM⟩
  have hP : 2 ^ J = 2 ^ (J - r) * 2 ^ r := by
    rw [<- Nat.pow_add, Nat.sub_add_cancel hR]
  refine ⟨n + m - 2 * 2 ^ (J - r), ?_⟩
  have hpos := pow_two_pos r
  have hle : 2 * 2 ^ (J - r) <= n + m := by
    have h1 : (2 * 2 ^ (J - r)) * 2 ^ r <= (n + m) * 2 ^ r := by
      calc (2 * 2 ^ (J - r)) * 2 ^ r = 2 ^ J + 2 ^ J := by rw [hP]; ring
        _ <= n * 2 ^ r + (1 + b) := by omega
        _ = (n + m) * 2 ^ r := by rw [hM]; ring
    exact Nat.le_of_mul_le_mul_right h1 hpos
  rw [Nat.sub_mul]
  have h2 : 2 * 2 ^ (J - r) * 2 ^ r = 2 ^ J + 2 ^ J := by rw [hP]; ring
  have h3 : (n + m) * 2 ^ r = n * 2 ^ r + (1 + b) := by rw [hM]; ring
  omega
theorem digitVal_low_ones_prefix (s : Nat) :
    ∀ (B H : Nat) (ds : WordList), DigitVal B H ds -> s <= H ->
      (∃ n, 1 + B = n * 2 ^ s) -> ∃ u, ds = List.replicate s Q ++ u := by
  induction s with
  | zero =>
    intro B H ds _ _ _
    exact ⟨ds, rfl⟩
  | succ s ih =>
    intro B H ds hD hSH ⟨n, hN⟩
    have hpow : 2 ^ (s + 1) = 2 ^ s * 2 := Nat.pow_succ 2 s
    cases hD with
    | nil => omega
    | @zero A H' u hSub =>
      rw [hpow] at hN
      have hN2 : 1 + A * 2 = (n * 2 ^ s) * 2 := by rw [hN]; ring
      omega
    | @one A H' u hSub =>
      rw [hpow] at hN
      have hN2 : 1 + (1 + A * 2) = (n * 2 ^ s) * 2 := by rw [hN]; ring
      have hN' : 1 + A = n * 2 ^ s := by omega
      rcases ih A H' u hSub (by omega) ⟨n, hN'⟩ with ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      rw [List.replicate_succ, List.cons_append]
theorem phaseScan_effect_split (r k : Nat) (u : WordList) (k' : Nat) (v : WordList) (a b : Rat)
    (carry : Nat) (eff : WordList) (A B J : Nat) (ds : WordList)
    (hI : PhaseScan k (u ++ List.replicate (1 + r * 2) Q ++ [K]) k' v a b)
    (hE : WordEffect 0 (V :: (v ++ [V])) carry eff)
    (hD : DigitVal B J ds) (hR : 1 + r <= J)
    (hAsum : A + 2 ^ J = k') (hBsum : B + 2 ^ J = A + carry) :
    ∃ w, ds = List.replicate (1 + r) Q ++ w := by
  rcases phaseScan_append_odd_Q_K_inv r k u k' v a b hI with ⟨w, n, rfl, hK⟩
  have hEq : V :: ((w ++ List.replicate (1 + r) V) ++ [V]) =
      (V :: w) ++ List.replicate (2 + r) V := by
    have h2 : 2 + r = (1 + r) + 1 := by omega
    rw [h2, replicate_succ_append]
    simp only [List.cons_append, List.append_assoc]
  rw [hEq] at hE
  rcases wordEffect_append_replicate_V_inv (V :: w) (2 + r) 0 carry eff hE with ⟨x, m, _, hC⟩
  have hCarry : ∃ n0, 1 + carry = n0 * 2 ^ (1 + r) := by
    refine ⟨m * 2, ?_⟩
    have hpow : 2 ^ (2 + r) = 2 * 2 ^ (1 + r) := by
      have h2 : 2 + r = 1 + (1 + r) := by omega
      rw [h2, pow_two_one_add]; ring
    rw [hpow] at hC
    calc 1 + carry = m * (2 * 2 ^ (1 + r)) := hC
      _ = (m * 2) * 2 ^ (1 + r) := by ring
  exact digitVal_low_ones_prefix (1 + r) B J ds hD hR (divisibility_carry_step (1 +
    r) J k' carry A B hR ⟨n, hK⟩ hCarry hAsum hBsum)
theorem mul_le_of_CrossMul_le (x p q s f : Rat) (hp : 0 < p) (hs : 0 <= s)
    (hxp : x * p <= q) (hsq : s * q <= f * p) : s * x <= f := by
  have h1 : (s * x) * p <= f * p := by
    calc (s * x) * p = s * (x * p) := by ring
      _ <= s * q := mul_le_mul_of_nonneg_left hxp hs
      _ <= f * p := hsq
  exact le_of_mul_le_mul_right h1 hp
theorem phaseScan_digitVal_weighted_bound (s : Nat) (ds : WordList) (A H k k' : Nat) (v : WordList)
    (a b sigma f : Rat)
    (hD : DigitVal A H ds) (hI : PhaseScan k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u, (0 < c /\ s <= c) /\ ds = List.replicate c Q ++ K :: u)
    (hSig : 0 <= sigma)
    (hBound : sigma * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    sigma * wordMass v <= f /\ sigma * a <= 4 * f /\ sigma * b <= 3 * f := by
  rcases phaseScan_digitVal_carry_bound s ds A H k k' v a b hD hI hLow with ⟨hM, hP, hN⟩
  have hPos := rat_pow_two_pos (s + s / 2)
  refine ⟨?_, ?_, ?_⟩
  · exact mul_le_of_CrossMul_le (wordMass v) _ _ sigma f hPos hSig hM hBound
  · exact mul_le_of_CrossMul_le a _ _ sigma (4 * f) hPos hSig hP (by linarith)
  · exact mul_le_of_CrossMul_le b _ _ sigma (3 * f) hPos hSig hN (by linarith)
theorem phaseScan_twelve_scale_eq (u : WordList) (k : Nat) (v : WordList) (a b : Rat)
    (hI : PhaseScan 12 u k v a b) :
    (k : Rat) * wordScale (V :: (v ++ [V])) = 2 + 4 * wordScale (V :: (v ++
      [V])) - (a - b) * (1 / 2) := by
  have hEq := phaseScan_budget_eq hI
  dsimp [wordScale]
  rw [wordScale_append]
  dsimp [wordScale]
  push_cast at hEq ⊢
  linarith
theorem phaseScan_twelve_height_sum (u : WordList) (k : Nat) (v : WordList) (a b : Rat) (J A B
    carry : Nat)
    (hI : PhaseScan 12 u k v a b)
    (hHeight : wordScale (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1)
    (hAsum : A + 2 ^ J = k) (hBsum : B + 2 ^ J = A + carry) :
    1 - ((1 + B : Nat) : Rat) * wordScale (V :: (v ++ [V])) =
      (a - b) * (1 / 2) - 4 * wordScale (V :: (v ++ [V])) -
      (((1 + carry : Nat) : Rat) * wordScale (V :: (v ++ [V])) - 1) := by
  have hBudget := phaseScan_twelve_scale_eq u k v a b hI
  have hSum : B + 2 ^ J + 2 ^ J = k + carry := by omega
  have hQsum : (B : Rat) + ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat) =
    (k : Rat) + (carry : Rat) := by
    exact_mod_cast hSum
  set s := wordScale (V :: (v ++ [V]))
  have hMul : (B : Rat) * s + 1 + 1 = (k : Rat) * s + (carry : Rat) * s := by
    calc (B : Rat) * s + 1 + 1
      _ = (B : Rat) * s + (s * ((2 ^ J : Nat) : Rat)) + (s * ((2 ^ J : Nat) : Rat)) := by
        rw [hHeight]
      _ = ((B : Rat) + ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat)) * s := by ring
      _ = ((k : Rat) + (carry : Rat)) * s := by rw [hQsum]
      _ = (k : Rat) * s + (carry : Rat) * s := by ring
  push_cast
  calc 1 - (1 + (B : Rat)) * s
    _ = 3 - ((B : Rat) * s + 1 + 1) - s := by ring
    _ = 3 - ((k : Rat) * s + (carry : Rat) * s) - s := by rw [hMul]
    _ = 3 - ((2 + 4 * s - (a - b) * (1 / 2)) + (carry : Rat) * s) - s := by rw [hBudget]
    _ = (a - b) * (1 / 2) - 4 * s - ((1 + (carry : Rat)) * s - 1) := by ring

end BusyBeaver.WordCalculus
