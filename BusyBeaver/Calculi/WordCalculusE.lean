/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Calculi.WordCalculusB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
theorem phaseScan_scale_le_of_hasQKSubword {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b
    : Rat}
    (hI : PhaseScan k u k' v a b) :
    hasQKSubword u = true -> wordScale v * 8 <= wordScale u := by
  induction hI with
  | nil _ => intro h; contradiction
  | T _ ih => intro h; have h1 := ih h; dsimp [wordScale]; linarith
  | @pair0 _ u _ v _ _ hSub _ =>
    intro _
    have h1 := phaseScan_scale_le hSub
    dsimp [wordScale]; linarith
  | @pair1 _ u _ v _ _ hSub _ =>
    intro _
    have h1 := phaseScan_scale_le hSub
    dsimp [wordScale]; linarith
  | short00 _ ih => intro h; have h1 := ih h; dsimp [wordScale]; linarith
  | @short01 n u _ _ _ _ hSub ih =>
    intro h
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => have h1 := ih h; dsimp [wordScale] at h1 ⊢; linarith
      | K =>
        generalize hk : 1 + n * 2 = k0 at hSub
        cases hSub <;> omega
      | Q => have h1 := ih h; dsimp [wordScale] at h1 ⊢; linarith
  | short10 _ ih => intro h; have h1 := ih h; dsimp [wordScale]; linarith
  | @short11 n u _ _ _ _ hSub ih =>
    intro h
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => have h1 := ih h; dsimp [wordScale] at h1 ⊢; linarith
      | K =>
        generalize hk : 1 + n * 2 = k0 at hSub
        cases hSub <;> omega
      | Q => have h1 := ih h; dsimp [wordScale] at h1 ⊢; linarith
theorem phaseScan_net_loss_le_three_mass {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b :
    Rat}
    (hI : PhaseScan k u k' v a b) :
    a - b - wordMassQ v <= 3 * wordMass u := by
  induction hI with
  | nil _ => simp [wordMassQ, wordMass]
  | @T _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
  | @pair0 _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
  | @pair1 _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
  | @short00 _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
  | @short01 _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
  | @short10 _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
  | @short11 _ u _ _ _ _ _ ih => have hw := wordMass_nonneg u; dsimp [wordMassQ, wordMass]; linarith
theorem phaseScan_digitVal_net_loss_bound {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b :
    Rat}
    (hI : PhaseScan k u k' v a b) :
    ∀ {A H : Nat}, DigitVal A H u ->
      ∃ l, Scan k u k' v l /\ a - b - wordMassQ v <= 2 * wordMass v + l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0, Scan.nil k, by simp [wordMass, wordMassQ]⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | pair0 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2, H2, hD2, _, _⟩
    rcases ih hD2 with ⟨l, hJ, hL⟩
    exact ⟨(1 + l) * (1 / 2), Scan.pair0 hJ, by dsimp [wordMass, wordMassQ]; linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases digitVal_cons_Q_inv hD1 with ⟨A2, H2, hD2, _, _⟩
    rcases ih hD2 with ⟨l, hJ, hL⟩
    exact ⟨(1 / 4) + l * (1 / 2), Scan.pair1 hJ, by dsimp [wordMass, wordMassQ]; linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hL⟩
    exact ⟨1 + l * 2, Scan.short00 hJ, by dsimp [wordMass, wordMassQ]; linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hL⟩
    exact ⟨l * 2, Scan.short01 hJ, by dsimp [wordMass, wordMassQ]; linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hL⟩
    exact ⟨1 + l * 2, Scan.short10 hJ, by dsimp [wordMass, wordMassQ]; linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1, H1, hD1, _, _⟩
    rcases ih hD1 with ⟨l, hJ, hL⟩
    exact ⟨l * 2, Scan.short11 hJ, by dsimp [wordMass, wordMassQ]; linarith⟩
theorem phaseScan_tailDefect_net_loss_bound {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b
    z : Rat}
    (hI : PhaseScan k u k' v a b) (hT : TailDefect u z) :
    a - b - wordMassQ v <= 3 * (1 + 2 * z) := by
  rcases exists_digitVal_of_tailDefect hT with ⟨A, H, hD⟩
  rcases phaseScan_digitVal_net_loss_bound hI hD with ⟨l, hJ, hL⟩
  rcases scan_tailDefect_bound hJ hT with ⟨hMv, hLv, _⟩
  linarith
set_option maxHeartbeats 2000000 in
-- Bound the sigma-weighted mass and net loss across the phase scan.
theorem phaseScan_digitVal_sigma_bound (h : Nat) (u : WordList) (B H : Nat) (ds : WordList) (sigma
    : Rat)
    (hDig : DigitVal B H ds)
    (hUnit : sigma * ((2 ^ h : Nat) : Rat) = 1)
    (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat))
    (hPair : hasQKSubword u = true)
    (hCut : notEndsWithQ u = true)
    (hNe : u ≠ [])
    (hZ : 7 <= wordMassK ds)
    (hPhi : 4 * sigma * wordMass u + sigma * wordScale u * wordMassK ds + 2 * sigma <= 1 / 256) :
    ∃ k v a b,
      PhaseScan (4 * 2 ^ h) (u ++ ds ++ [K]) k v a b /\ 4 < k /\
      sigma * wordMass v <= sigma * wordMass u + (15 / 56) * (sigma * wordScale u * wordMassK ds) /\
      sigma * (a - b - wordMassQ v) <=
        3 * sigma * wordMass u + (45 / 56) * (sigma * wordScale u * wordMassK ds) := by
  have hPh : (0 : Rat) < ((2 ^ h : Nat) : Rat) := by exact_mod_cast pow_two_pos h
  have hPH : (0 : Rat) < ((2 ^ H : Nat) : Rat) := by exact_mod_cast pow_two_pos H
  have hS : 0 < sigma := by nlinarith
  have hSu := wordScale_pos u
  have hMu := wordMass_nonneg u
  have hMd := wordMass_nonneg ds
  have hDpos : 0 <= sigma * wordScale u * wordMassK ds := by positivity
  have hSmall : 4 * sigma * wordMass u + 2 * sigma <= 1 / 256 := by linarith
  have hDefSmall : sigma * wordScale u * wordMassK ds <= 1 / 256 := by nlinarith
  have hBound : 8 * wordMass u < (((2 * 2 ^ h) * 2 : Nat) : Rat) - 4 := by
    have hc : (((2 * 2 ^ h) * 2 : Nat) : Rat) = 4 * ((2 ^ h : Nat) : Rat) := by push_cast; ring
    rw [hc]; nlinarith
  rcases exists_phaseScan_of_mass_lt u (2 * 2 ^ h) hBound with ⟨m, x, a1, b1, hI0, _⟩
  have hI : PhaseScan (4 * 2 ^ h) u m x a1 b1 := by
    have heq : (2 * 2 ^ h) * 2 = 4 * 2 ^ h := by ring
    rwa [heq] at hI0
  rcases phaseScan_even_out_of_notEndsWithQ hI hCut hNe with ⟨n, rfl⟩
  have hGain := phaseScan_scale_le_of_hasQKSubword hI hPair
  have hBudget := phaseScan_budget_eq hI
  have hBounds := phaseScan_loss_bounds hI
  have hSx := wordScale_pos x
  let s := sigma * wordScale x
  have hSp : 0 < s := by positivity
  have hUnitTail : sigma * wordScale u * ((2 ^ H : Nat) : Rat) = 1 := by
    calc sigma * wordScale u * ((2 ^ H : Nat) : Rat)
      _ = sigma * (wordScale u * ((2 ^ H : Nat) : Rat)) := by ring
      _ = sigma * ((2 ^ h : Nat) : Rat) := by rw [hHeight]
      _ = 1 := hUnit
  have hGs : 8 * s <= sigma * wordScale u := by
    change 8 * (sigma * wordScale x) <= sigma * wordScale u
    nlinarith
  have hHt : s * ((2 ^ H : Nat) : Rat) <= 1 / 8 := by
    have h1 : 8 * s * ((2 ^ H : Nat) : Rat) <= sigma * wordScale u * ((2 ^ H : Nat) : Rat) :=
      by nlinarith
    linarith
  have hF : s * (1 + 2 * wordMassK ds) <= (15 / 56) * (sigma * wordScale u * wordMassK ds) := by
    have h1 : 7 * s <= s * wordMassK ds := by nlinarith
    have h2 : 8 * s * wordMassK ds <= sigma * wordScale u * wordMassK ds := by nlinarith
    linarith
  have hBudget' : (((n * 2 : Nat) : Rat) - 4) * s = 4 - 4 * sigma - 2 * sigma * (a1 - b1) := by
    change (((n * 2 : Nat) : Rat) - 4) * (sigma * wordScale x) =
      4 - 4 * sigma - 2 * sigma * (a1 - b1)
    have hc : ((4 * 2 ^ h : Nat) : Rat) = 4 * ((2 ^ h : Nat) : Rat) := by push_cast; ring
    rw [hc] at hBudget
    nlinarith
  have hCarry : 3 < (((n * 2 : Nat) : Rat) - 4) * s := by
    nlinarith
  rcases digitVal_scale_and_mass hDig with ⟨hSd, hMassD, _⟩
  have hTail : 2 * (wordMass (ds ++ [K]) + wordMassK (ds ++ [K])) * s < 3 := by
    rw [wordMass_append, wordMassK_append]
    dsimp [wordMass, wordMassK]
    have h1 : s * wordScale ds <= 1 / 8 := by rwa [hSd]
    have h2 : s * wordMass ds <= 1 / 8 := by nlinarith
    have h3 : s * wordMassK ds <= 1 / 256 := by nlinarith
    linarith
  have hTail1 : 2 * (wordMass (ds ++ [K]) + wordMassK (ds ++ [K])) < ((n * 2 : Nat) : Rat) := by
    nlinarith
  have hTail2 : 8 * (1 + 2 * wordMassK ds) < ((n * 2 : Nat) : Rat) - 4 := by
    nlinarith
  rcases scan_tailDefect_step_bound (ds ++
    [K]) (wordMassK ds) n (tailDefect_append_K_of_digitVal hDig) hTail1 hTail2
    with ⟨k, y, a2, b2, hJ, hK⟩
  rcases phaseScan_append hI hJ with ⟨a, b, hIJ, hA, hB⟩
  have hIJ' : PhaseScan (4 * 2 ^ h) (u ++ ds ++ [K]) k (x ++ y) a b := by
    simpa [List.append_assoc] using! hIJ
  have hTB := phaseScan_tailDefect_bound hJ (tailDefect_append_K_of_digitVal hDig)
  have hE1 := phaseScan_net_loss_le_three_mass hI
  have hE2 := phaseScan_tailDefect_net_loss_bound hJ (tailDefect_append_K_of_digitVal hDig)
  refine ⟨k, x ++ y, a, b, hIJ', hK, ?_, ?_⟩
  · rw [wordMass_append]
    have h1 : sigma * (wordScale x * wordMass y) = s * wordMass y := by ring
    have h2 : s * wordMass y <= s * (1 + 2 * wordMassK ds) := by nlinarith
    nlinarith
  · rw [wordMassQ_append, hA, hB]
    have h1 : sigma * (a - b - wordMassQ (x ++
      y)) = sigma * (a1 - b1 - wordMassQ x) + s * (a2 - b2 - wordMassQ y) := by
      rw [wordMassQ_append, hA, hB]; change _ = _ + (sigma * wordScale x) * _; ring
    have h2 : s * (a2 - b2 - wordMassQ y) <= 3 * s * (1 + 2 * wordMassK ds) := by nlinarith
    nlinarith
def heightShiftE : WordList -> Nat -> Option Nat
  | [], h => some h
  | V :: u, h => heightShiftE u (h + 1)
  | _ :: _u, 0 => none
  | _ :: u, h + 1 => heightShiftE u h
theorem heightShiftE_sound (u : WordList) :
    ∀ (h H : Nat), heightShiftE u h = some H ->
      wordScale u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE
    simp [wordScale]
  | cons w u ih =>
    intro h H hE
    cases w with
    | V =>
      dsimp [heightShiftE, wordScale] at hE ⊢
      have hIH := ih (h + 1) H hE
      rw [Nat.pow_succ] at hIH
      push_cast at hIH ⊢; linarith
    | K =>
      cases h with
      | zero => contradiction
      | succ h =>
        dsimp [heightShiftE, wordScale] at hE ⊢
        have hIH := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hIH ⊢; linarith
    | Q =>
      cases h with
      | zero => contradiction
      | succ h =>
        dsimp [heightShiftE, wordScale] at hE ⊢
        have hIH := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hIH ⊢; linarith
theorem heightShiftE_append_inv (u : WordList) :
    ∀ (v : WordList) (h H : Nat), heightShiftE (u ++ v) h = some H ->
      ∃ j, heightShiftE u h = some j /\ heightShiftE v j = some H := by
  induction u with
  | nil =>
    intro v h H hE
    exact ⟨h, rfl, hE⟩
  | cons w u ih =>
    intro v h H hE
    cases w with
    | V => exact ih v (h + 1) H hE
    | K =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE
    | Q =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE
theorem heightShiftE_replicate_V (n : Nat) :
    ∀ (h : Nat), heightShiftE (List.replicate n V) h = some (h + n) := by
  induction n with
  | zero => intro h; simp [heightShiftE]
  | succ n ih =>
    intro h
    dsimp [List.replicate, heightShiftE]
    rw [ih (h + 1)]
    congr 1; omega
theorem le_of_heightShiftE_append_replicate_V (u : WordList) (n h H : Nat)
    (hE : heightShiftE (u ++ List.replicate n V) h = some H) : n <= H := by
  rcases heightShiftE_append_inv u (List.replicate n V) h H hE with ⟨j, _, hJ⟩
  rw [heightShiftE_replicate_V] at hJ
  injection hJ with hJ
  (try omega)
theorem exists_heightShiftE_of_mass_lt (u : WordList) :
    ∀ (h : Nat), wordMass u < ((2 ^ h : Nat) : Rat) -> ∃ H, heightShiftE u h = some H := by
  induction u with
  | nil => intro h _; exact ⟨h, rfl⟩
  | cons w u ih =>
    intro h hM
    cases w with
    | V =>
      dsimp [wordMass, heightShiftE] at hM ⊢
      apply ih (h + 1)
      rw [Nat.pow_succ]; push_cast at hM ⊢; linarith
    | K =>
      cases h with
      | zero =>
        have hw := (wordMass_nonneg u).1
        dsimp [wordMass] at hM; linarith
      | succ h =>
        dsimp [wordMass, heightShiftE] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
    | Q =>
      cases h with
      | zero =>
        have hw := (wordMass_nonneg u).1
        dsimp [wordMass] at hM; linarith
      | succ h =>
        dsimp [wordMass, heightShiftE] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
theorem heightShiftE_succ (u : WordList) :
    ∀ (h H : Nat), heightShiftE u h = some H -> heightShiftE u (h + 1) = some (H + 1) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE; rfl
  | cons w u ih =>
    intro h H hE
    cases w with
    | V => exact ih (h + 1) H hE
    | K =>
      cases h with
      | zero => contradiction
      | succ h => exact ih h H hE
    | Q =>
      cases h with
      | zero => contradiction
      | succ h => exact ih h H hE
theorem phaseScan_effect_heightShiftE {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) :
    ∀ (h H n n' : Nat) (eff : WordList),
      heightShiftE v h = some H -> WordEffect n v n' eff ->
      k + n * 2 + 3 <= 4 * 2 ^ h -> k' + n' * 2 + 3 <= 4 * 2 ^ H := by
  induction hI with
  | nil k =>
    intro h H n n' eff hHeight hEff hBound
    injection hHeight with hEq; subst hEq
    cases hEff
    exact hBound
  | T _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases hEff with
    | T hSub =>
      apply ih (h + 1) H (1 + n * 2) n' _ hHeight hSub
      rw [Nat.pow_succ]; omega
  | pair0 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases hEff with
    | T hSub =>
      apply ih (h + 1) H (1 + n * 2) n' _ hHeight hSub
      rw [Nat.pow_succ]; omega
  | pair1 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases hEff with
    | T hSub =>
      apply ih (h + 1) H (1 + n * 2) n' _ hHeight hSub
      rw [Nat.pow_succ]; omega
  | short00 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d00 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d01 hSub => apply ih h H _ n' _ hHeight hSub; omega
  | short01 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d00 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d01 hSub => apply ih h H _ n' _ hHeight hSub; omega
  | short10 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d10 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d11 hSub => apply ih h H _ n' _ hHeight hSub; omega
  | short11 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d10 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d11 hSub => apply ih h H _ n' _ hHeight hSub; omega
theorem wordEffect_replicate_Q_V (n : Nat) :
    WordEffect 1 (List.replicate n Q ++ [V]) 3 (List.replicate n K ++ [V]) := by
  induction n with
  | zero => exact WordEffect.T (WordEffect.nil 3)
  | succ n ih => exact @WordEffect.d11 0 _ _ _ ih
theorem phaseScan_replicate_K_V_inv (n : Nat) :
    ∀ (h k k' : Nat) (v : WordList) (a b : Rat),
      PhaseScan k (List.replicate n K ++ [V]) k' v a b ->
      k + 4 = 4 * 2 ^ h ->
      ∃ H, v = List.replicate n Q ++ [V] /\ heightShiftE v h = some H /\ k' + 12 = 4 * 2 ^ H := by
  induction n with
  | zero =>
    intro h k k' v a b hI hEq
    generalize hk : k = k0 at hI
    cases hI with
    | @T m _ _ v0 a0 b0 hSub =>
      generalize hkSub : 2 + m * 2 = kSub at hSub
      cases hSub
      refine ⟨h + 1, rfl, rfl, ?_⟩
      rw [Nat.pow_succ]; omega
  | succ n ih =>
    intro h k k' v a b hI hEq
    have hpos := pow_two_pos h
    cases h with
    | zero =>
      dsimp at hEq
      cases hI <;> omega
    | succ h =>
      rw [Nat.pow_succ] at hEq
      cases hI with
      | short00 _ => omega
      | @short10 m _ _ v0 a0 b0 hSub =>
        rcases ih h (m * 2) k' v0 a0 b0 hSub (by omega) with ⟨H, rfl, hHt, hK⟩
        exact ⟨H, rfl, hHt, hK⟩
inductive EGuard : WordList -> Prop where
  | T (n : Nat) (w : WordList) : EGuard (V :: (List.replicate n Q ++ V :: w))
  | D (w : WordList) : EGuard (Q :: V :: w)
theorem eGuard_append {u v : WordList} (hG : EGuard u) : EGuard (u ++ v) := by
  cases hG with
  | T n w =>
    have heq : (V :: (List.replicate n Q ++ V :: w)) ++ v =
        V :: (List.replicate n Q ++ V :: (w ++ v)) := by
      simp [List.append_assoc]
    rw [heq]; exact EGuard.T n (w ++ v)
  | D w =>
    exact EGuard.D (w ++ v)
theorem eGuard_effect_phaseScan_split (h : Nat) (orig eff : WordList) (carry k : Nat) (v :
    WordList) (a b : Rat)
    (hG : EGuard orig) (hE : WordEffect 0 orig carry eff)
    (hI : PhaseScan (4 * 2 ^ h) eff k v a b) (_hPos : 0 < k) :
    ∃ pre rest j m x a' b' c H,
      v = pre ++ rest /\ EGuard (pre ++ rest) /\
      heightShiftE pre h = some H /\ WordEffect 0 pre c x /\
      PhaseScan j m k rest a' b' /\ j + c * 2 + 3 <= 4 * 2 ^ H := by
  cases hG with
  | T n w =>
    have hEq : V :: (List.replicate n Q ++ V :: w) =
        (V :: (List.replicate n Q ++ [V])) ++ w := by
      simp [List.append_assoc]
    rw [hEq] at hE
    rcases wordEffect_split_input (V :: (List.replicate n Q ++ [V])) hE
      with ⟨c, pre, tail, rfl, hEP, hET⟩
    have hEG : WordEffect 0 (V :: (List.replicate n Q ++ [V])) 3 (V :: (List.replicate n K ++
      [V])) :=
      WordEffect.T (wordEffect_replicate_Q_V n)
    rcases wordEffect_unique hEP hEG with ⟨rfl, rfl⟩
    have hCut : SplitCond (V :: (List.replicate n K ++ [V])) tail := by
      left
      have heq_cut : (V :: (List.replicate n K ++ [V])) = (V :: List.replicate n K) ++ [V] := by
        simp
      rw [heq_cut, notEndsWithQ_append_singleton]; rfl
    rcases phaseScan_split_of_splitCond hI (V :: (List.replicate n K ++ [V])) tail rfl hCut
      with ⟨j, x, y, a1, b1, a2, b2, hSX, hSY, rfl, _, _⟩
    generalize hkSX : 4 * 2 ^ h = kSX at hSX
    cases hSX with
    | @T m _ _ v0 a0 b0 hJ =>
      have hEq_m : (2 + m * 2) + 4 = 4 * 2 ^ (h + 1) := by
        rw [Nat.pow_succ]; omega
      rcases phaseScan_replicate_K_V_inv n (h + 1) (2 + m * 2) j v0 a0 b0 hJ hEq_m
        with ⟨hh, rfl, hHt, hK⟩
      refine ⟨V :: (List.replicate n Q ++ [V]), y, j, tail, V :: (List.replicate n K ++ [V]), a2,
        b2, 3, hh, rfl, ?_, hHt, hEG, hSY, by omega⟩
      have heq_g : (V :: (List.replicate n Q ++ [V])) ++ y = V :: (List.replicate n Q ++
        V :: y) := by
        simp [List.append_assoc]
      rw [heq_g]; exact EGuard.T n y
  | D w =>
    generalize hk0 : (0 : Nat) = k0 at hE
    cases hE with
    | @d10 m _ _ _ hE1 =>
      have hm0 : m = 0 := by omega
      subst hm0
      generalize hk1 : (0 : Nat) = k1 at hE1
      cases hE1 with
      | T hE2 =>
        subst hk1
        have hpos_h := pow_two_pos h
        cases h with
        | zero =>
          dsimp at hI
          generalize hkI : (4 : Nat) = kI at hI
          cases hI with
          | @short01 m' _ _ _ _ _ _ => omega
          | @short11 m' _ _ _ _ _ hSub =>
            have hm'0 : m' = 0 := by omega
            subst hm'0
            dsimp at hSub
            generalize hkS : (1 : Nat) = kS at hSub
            cases hSub with
            | T _ => omega
        | succ h =>
          have hpow : 4 * 2 ^ (h + 1) = 4 + (2 * 2 ^ h - 1) * 4 := by
            have hp := pow_two_pos h
            rw [Nat.pow_succ]; omega
          rw [hpow] at hI
          generalize hkI : 4 + (2 * 2 ^ h - 1) * 4 = kI at hI
          cases hI with
          | @short01 m' _ _ _ _ _ _ => omega
          | @short11 m' _ _ _ _ _ hSub =>
            have hm' : m' = 2 * 2 ^ h - 1 := by omega
            subst hm'
            have h1 : 1 + (2 * 2 ^ h - 1) * 2 = 3 + (4 * 2 ^ h - 4) := by
              have hp := pow_two_pos h; omega
            rw [h1] at hSub
            generalize hkS : 3 + (4 * 2 ^ h - 4) = kS at hSub
            cases hSub with
            | @T m'' _ _ v0 a0 b0 hSub2 =>
              have hm'' : m'' = 4 * 2 ^ h - 4 := by omega
              subst hm''
              refine ⟨[Q, V], v0, 2 + (4 * 2 ^ h - 4) * 2, _, [Q, V], a0, b0, 1, h + 1, rfl,
                EGuard.D v0, rfl, ?_, hSub2, ?_⟩
              · exact WordEffect.d10 (WordEffect.T (WordEffect.nil 1))
              · have hp := pow_two_pos h
                rw [Nat.pow_succ]; omega
    | d11 _ => omega
theorem eStep_of_eGuard_phaseScan {h : Nat} {orig eff : WordList} {carry k : Nat} {v : WordList} {a
    b : Rat}
    {H n : Nat} {out : WordList}
    (hG : EGuard orig) (hE : WordEffect 0 orig carry eff)
    (hI : PhaseScan (4 * 2 ^ h) eff k v a b) (hPos : 0 < k)
    (hHeight : heightShiftE v h = some H) (hEff : WordEffect 0 v n out) :
    EGuard v /\ k + n * 2 + 3 <= 4 * 2 ^ H := by
  rcases eGuard_effect_phaseScan_split h orig eff carry k v a b hG hE hI hPos
    with ⟨pre, rest, j, m, x, a', b', c, H', rfl, hG', hHt, hEp, hJ, hBound⟩
  rcases heightShiftE_append_inv pre rest h H hHeight with ⟨hh, hHp, hHr⟩
  rw [hHt] at hHp
  injection hHp with hEq; subst hEq
  rcases wordEffect_split_input pre hEff with ⟨c', pre', out', _, hEp', hEr⟩
  rcases wordEffect_unique hEp hEp' with ⟨rfl, _⟩
  exact ⟨hG', phaseScan_effect_heightShiftE hJ H' H c n out' hHr hEr hBound⟩
theorem digitVal_low_zeros_prefix (s : Nat) :
    ∀ (B H : Nat) (ds : WordList),
      DigitVal B H ds -> s <= H -> (∃ n, B = n * 2 ^ s) ->
      ∃ rest, ds = List.replicate s K ++ rest := by
  induction s with
  | zero =>
    intro B H ds _ _ _
    exact ⟨ds, rfl⟩
  | succ s ih =>
    intro B H ds hD hSH ⟨n, hN⟩
    have hN2 : B = (n * 2 ^ s) * 2 := by
      rw [Nat.pow_succ] at hN
      linarith
    cases hD with
    | nil => omega
    | @zero A' H' u' hSub =>
      rcases ih A' H' u' hSub (by omega) ⟨n, by omega⟩ with ⟨rest, rfl⟩
      exact ⟨rest, rfl⟩
    | one _ => omega
theorem phaseScan_three_K_div_eight {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k (K :: K :: K :: u) k' v a b)
    (hN : ∃ n, k + 12 = n * 16) :
    ∃ w, v = Q :: Q :: K :: w := by
  rcases hN with ⟨n, hEq⟩
  generalize hk0 : k = k0 at hI
  cases hI with
  | short00 _ => omega
  | @short10 m1 _ _ _ _ _ hI1 =>
    generalize hk1 : m1 * 2 = k1 at hI1
    cases hI1 with
    | short00 _ => omega
    | @short10 m2 _ _ _ _ _ hI2 =>
      generalize hk2 : m2 * 2 = k2 at hI2
      cases hI2 with
      | @short00 m3 _ _ w0 _ _ _ => exact ⟨w0, rfl⟩
      | short10 _ => omega
theorem phaseScan_four_V_three_K_div_eight {k : Nat} {u rest : WordList} {k' : Nat} {v : WordList}
    {a b : Rat}
    (hI : PhaseScan k ((u ++ List.replicate 4 V) ++ K :: K :: K :: rest) k' v a b) :
    ∃ x y, v = (x ++ List.replicate 4 V) ++ Q :: Q :: K :: y := by
  have hE1 : (u ++ List.replicate 4 V) ++ K :: K :: K :: rest =
      u ++ (List.replicate 4 V ++ K :: K :: K :: rest) := by
    simp [List.append_assoc]
  rw [hE1] at hI
  rcases phaseScan_split_of_splitCond hI u (List.replicate 4 V ++
    K :: K :: K :: rest) rfl (Or.inr ⟨_, rfl⟩)
    with ⟨m, x, y, _, _, _, _, _, hB, rfl, _, _⟩
  rcases phaseScan_split_of_splitCond hB (List.replicate 4 V) (K :: K :: K :: rest) rfl (Or.inl
    (notEndsWithQ_replicate_V 4))
    with ⟨j, x', y', _, _, _, _, hC, hD, rfl, _, _⟩
  rcases phaseScan_replicate_V_inv 4 m j x' _ _ hC with ⟨rfl, hN, _, _⟩
  have hMod : ∃ q, j + 12 = q * 16 := ⟨m - 3, by omega⟩
  rcases phaseScan_three_K_div_eight hD hMod with ⟨w, rfl⟩
  exact ⟨x, w, by simp [List.append_assoc]⟩
theorem hasQKSubword_append_right (u v : WordList) (h : hasQKSubword v =
    true) : hasQKSubword (u ++ v) = true := by
  induction u with
  | nil => exact h
  | cons w u ih =>
    cases w with
    | V => exact ih
    | K => exact ih
    | Q =>
      cases u with
      | nil =>
        cases v with
        | nil => contradiction
        | cons w2 v' => cases w2 <;> first | rfl | exact h
      | cons w2 u' =>
        cases w2 with
        | V => exact ih
        | K => rfl
        | Q => exact ih
theorem wordEffect_four_V_QQK_hasQKSubword {u rest : WordList} {n : Nat} {eff : WordList}
    (hE : WordEffect 0 ((u ++ List.replicate 4 V) ++ Q :: Q :: K :: rest) n eff) :
    hasQKSubword eff = true := by
  rcases wordEffect_split_input (u ++ List.replicate 4 V) hE with ⟨c, x, y, rfl, hA, hB⟩
  rcases wordEffect_append_replicate_V_inv u 4 0 c x hA with ⟨z, m, _, hC⟩
  have h4 : (2 : Nat) ^ 4 = 16 := rfl
  rw [h4] at hC
  generalize hk0 : c = k0 at hB
  cases hB with
  | d10 _ => omega
  | @d11 c1 _ _ _ hB1 =>
    generalize hk1 : 1 + c1 = k1 at hB1
    cases hB1 with
    | @d10 c2 _ _ _ hB2 =>
      generalize hk2 : c2 = k2 at hB2
      cases hB2 with
      | @d00 c3 _ _ w0 _ =>
        exact hasQKSubword_append_right x (K :: Q :: K :: w0) rfl
      | d01 _ => omega
    | d11 _ => omega
theorem phaseScan_effect_sigma_contraction (h : Nat) (u : WordList) (n : Nat) (v : WordList) (a b :
    Rat) (c : Nat) (eff : WordList) (sigma : Rat)
    (hI : PhaseScan (4 * 2 ^ h) u (n * 2) v a b)
    (hE : WordEffect 0 v c eff)
    (hS : 0 < sigma)
    (hUnit : sigma * ((2 ^ h : Nat) : Rat) = 1) :
    1 - ((n + c + 2 : Nat) : Rat) * (sigma * wordScale v * (1 / 2)) <=
      (sigma + sigma * (a - b - wordMassQ v)) * (1 / 2) - 3 * (sigma * wordScale v * (1 / 2)) := by
  have hBudget := phaseScan_budget_eq hI
  have hCarry := wordEffect_budget_eq hE
  have hMass := (wordEffect_preserves_scale_and_mass hE).2
  have hSplit := wordMass_eq_add eff
  have hWeff := wordMass_nonneg eff
  have hO : wordMassQ eff <= wordMass v := by linarith
  have hSv := wordScale_pos v
  have hc4 : ((4 * 2 ^ h : Nat) : Rat) = 4 * ((2 ^ h : Nat) : Rat) := by push_cast; ring
  have hn2 : ((n * 2 : Nat) : Rat) = 2 * (n : Rat) := by push_cast; ring
  have hc1 : ((1 + c : Nat) : Rat) = 1 + (c : Rat) := by push_cast; ring
  have hc0 : ((1 + 0 : Nat) : Rat) = 1 := rfl
  have hnc : ((n + c + 2 : Nat) : Rat) = (n : Rat) + (c : Rat) + 2 := by push_cast; ring
  rw [hc4, hn2] at hBudget
  rw [hc1, hc0] at hCarry
  rw [hnc]
  have hB0 : (4 * ((2 ^ h : Nat) : Rat) - 4) - ((2 * (n : Rat) - 4) * wordScale v +
    2 * (a - b)) = 0 := by linarith
  have hC0 : (1 + (c : Rat)) * wordScale v - (1 + wordMass v + wordMassQ v - wordMassQ eff) =
    0 := by linarith
  have hU0 : sigma * ((2 ^ h : Nat) : Rat) - 1 = 0 := by linarith
  have h_id :
    (sigma + sigma * (a - b - wordMassQ v)) * (1 / 2) - 3 * (sigma * wordScale v * (1 / 2)) -
      (1 - ((n : Rat) + (c : Rat) + 2) * (sigma * wordScale v * (1 / 2))) =
    (sigma * ((2 ^ h : Nat) : Rat) - 1) -
      (1 / 4) * sigma * ((4 * ((2 ^ h : Nat) : Rat) - 4) - ((2 * (n : Rat) - 4) * wordScale v +
        2 * (a - b))) +
      (1 / 2) * sigma * ((1 + (c : Rat)) * wordScale v - (1 + wordMass v +
        wordMassQ v - wordMassQ eff)) +
      (1 / 2) * sigma * (wordMass v - wordMassQ eff) := by ring
  rw [hU0, hB0, hC0] at h_id
  have h_nonneg : 0 <= (1 / 2) * sigma * (wordMass v - wordMassQ eff) := by nlinarith
  linarith
theorem eGood_contraction_ineq (M D sigma M' D' : Rat)
    (_ : 0 <= M) (_ : 0 <= sigma)
    (hM' : M' <= (M + (15 / 56) * D) * (1 / 2))
    (hD' : D' <= (sigma + 3 * M + (45 / 56) * D) * (1 / 2)) :
    4 * M' + D' + sigma <= (15 / 16) * (4 * M + D + 2 * sigma) := by
  linarith
theorem digitVal_high_ones_suffix_E (n t0 B : Nat) (ds : WordList)
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
    (try omega)
  have ha_lt : a < 2 ^ n := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    (try omega)
  rcases exists_digitVal_of_lt_pow n a ha_lt with ⟨u, hU⟩
  refine ⟨u, digitVal_unique hD ?_⟩
  rw [<- hSum]
  exact digitVal_append hU (digitVal_replicate_Q t0)
theorem digitVal_unit_massK_bound {B H : Nat} {ds : WordList} {unit : Rat}
    (hD : DigitVal B H ds) (hU : 0 < unit)
    (hHeight : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hZ : 7 <= wordMassK ds)
    (hSmall : unit * wordMassK ds <= 1 / 256) :
    ∃ rest, ds = rest ++ List.replicate 7 Q := by
  have hH7 : 7 <= H := by
    by_contra hlt
    have hle : H <= 6 := by omega
    have hpow_le : 2 ^ H <= 64 := by
      calc 2 ^ H <= 2 ^ 6 := Nat.pow_le_pow_right (by decide) hle
      _ = 64 := by decide
    have hpow_q : ((2 ^ H : Nat) : Rat) <= 64 := by exact_mod_cast hpow_le
    nlinarith
  have hShift : unit * ((2 ^ (H - 7) : Nat) : Rat) = 1 / 128 := by
    have heq : H = (H - 7) + 7 := by omega
    have hpow : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - 7) : Nat) : Rat) * 128 := by
      have hp : 2 ^ H = 2 ^ (H - 7) * 128 := by rw [heq, Nat.pow_add]; rfl
      rw [hp]; push_cast; ring
    rw [hpow] at hHeight
    linarith
  have hEq := digitVal_wordMassK_eq hD
  have hH_split : (H - 7) + 7 = H := by omega
  have hD' : DigitVal B ((H - 7) + 7) ds := by rwa [hH_split]
  apply digitVal_high_ones_suffix_E (H - 7) 7 B ds hD'
  have hL_q : ((2 ^ ((H - 7) + 7) : Nat) : Rat) <= ((B + 2 ^ (H - 7) : Nat) : Rat) := by
    rw [hH_split]
    push_cast at hEq hShift ⊢
    nlinarith
  exact_mod_cast hL_q
inductive EGood : Nat -> WordList -> Prop where
  | intro (h H : Nat) (u : WordList) (A : Nat) (da : WordList) (carry : Nat) (eff : WordList)
      (B : Nat) (db : WordList) (sigma : Rat) :
      heightShiftE u h = some H ->
      EGuard u ->
      (∃ w, u = w ++ List.replicate 4 V) ->
      DigitVal A H da ->
      WordEffect 0 u carry eff ->
      A + carry = B ->
      DigitVal B H db ->
      hasQKSubword eff = true ->
      (∃ w, db = K :: K :: K :: w) ->
      (∃ w, db = w ++ List.replicate 7 Q) ->
      sigma * ((2 ^ h : Nat) : Rat) = 1 ->
      4 * sigma * wordMass u + sigma * wordScale u * wordMassK db + 2 * sigma <= 1 / 256 ->
      EGood h (u ++ da)
inductive EStep : Nat -> WordList -> WordList -> Prop where
  | intro (h : Nat) (orig eff : WordList) (n : Nat) (v : WordList) (a b : Rat) (J : Nat) (da :
    WordList) :
      WordEffect 0 (orig ++ [K]) 0 eff ->
      PhaseScan (4 * 2 ^ h) eff (n * 2) v a b ->
      0 < n ->
      DigitVal (1 + n) J da ->
      EStep h orig (v ++ da)
set_option maxHeartbeats 2000000 in
-- Combine the phase-scan sigma bound with the word-effect contraction.
theorem eGood_progress {h : Nat} {orig : WordList} (hG : EGood h orig) :
    ∃ out, EStep h orig out /\ EGood (h + 1) out := by
  rcases hG with ⟨H, u, A, da, carry, eff, B, db, sigma,
    hHeight, hGuardU, hEnd, hDA, hE, hSum, hDB, hPair, hLow, hHigh, hUnit, hPhi⟩
  have hHt := heightShiftE_sound u h H hHeight
  rcases wordEffect_preserves_scale_and_mass hE with ⟨hSe, hMe⟩
  have hPh : (0 : Rat) < ((2 ^ h : Nat) : Rat) := by exact_mod_cast pow_two_pos h
  have hSig : 0 < sigma := by nlinarith
  have hWu := wordMass_nonneg u
  have hWdb := wordMass_nonneg db
  have hSu := wordScale_pos u
  have hDpos : 0 <= sigma * wordScale u * wordMassK db :=
    mul_nonneg (mul_nonneg (le_of_lt hSig) (le_of_lt hSu)) hWdb.2.1
  have hMu : 0 <= sigma * wordMass u :=
    mul_nonneg (le_of_lt hSig) hWu.1
  have hZ : 7 <= wordMassK db := by
    rcases hLow with ⟨w, rfl⟩
    have hw := wordMass_nonneg w
    dsimp [wordMassK]; linarith
  have hEe : ∃ p, eff = p ++ List.replicate 4 V := by
    rcases hEnd with ⟨p, rfl⟩
    rcases wordEffect_append_replicate_V_inv p 4 0 carry eff hE with ⟨w, q, hV, _⟩
    exact ⟨w, hV⟩
  have hCut : notEndsWithQ eff = true := by
    rcases hEe with ⟨p, rfl⟩
    have heq : p ++ List.replicate 4 V = (p ++ [V, V, V]) ++ [V] := by
      simp [List.append_assoc]
    rw [heq, notEndsWithQ_append_singleton]; rfl
  have hNe : eff ≠ [] := by
    rcases hEe with ⟨p, rfl⟩
    simp
  have hHt_eff : wordScale eff * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by rwa [hSe]
  have hPhi_eff : 4 * sigma * wordMass eff + sigma * wordScale eff * wordMassK db + 2 * sigma <=
    1 / 256 := by
    rwa [hSe, hMe]
  rcases phaseScan_digitVal_sigma_bound h eff B H db sigma hDB hUnit hHt_eff hPair hCut hNe hZ
    hPhi_eff
    with ⟨k, v, a, b, hI, hPos, hMass, hEnergy⟩
  rw [hSe, hMe] at hMass hEnergy
  rcases hHigh with ⟨hi, hHi⟩
  have hIH : PhaseScan (4 * 2 ^ h) ((eff ++ hi) ++ List.replicate (1 + 3 * 2) Q ++
    [K]) k v a b := by
    have h7 : List.replicate 7 Q = List.replicate (1 + 3 * 2) Q := rfl
    rw [hHi, h7] at hI
    simpa [List.append_assoc] using! hI
  rcases phaseScan_append_odd_Q_K_inv 3 (4 * 2 ^ h) (eff ++ hi) k v a b hIH with ⟨p, n, hV, rfl⟩
  have h16 : 2 ^ (1 + 3) = 16 := rfl
  rw [h16] at hI hPos
  have hI' : PhaseScan (4 * 2 ^ h) (eff ++ db ++ [K]) ((n * 8) * 2) v a b := by
    have heq : (n * 8) * 2 = n * 16 := by ring
    rwa [heq]
  have hMv : sigma * wordMass v <= 1 / 256 := by linarith
  have hMv_pow : wordMass v < ((2 ^ h : Nat) : Rat) := by nlinarith
  rcases exists_heightShiftE_of_mass_lt v h hMv_pow with ⟨Hv, hHeightV⟩
  rcases exists_wordEffect v 0 with ⟨carry', eff', hE'⟩
  rcases exists_wordEffect_of_digitVal_add hDA hSum (lt_pow_of_digitVal hDB) with ⟨db0, hDB0, hED⟩
  have hdb_eq : db0 = db := digitVal_unique hDB0 hDB
  rw [hdb_eq] at hED
  have hFull : WordEffect 0 ((u ++ da) ++ [K]) 0 (eff ++ db ++ [K]) := by
    simpa only [List.append_assoc] using!
      wordEffect_append hE (wordEffect_append hED (WordEffect.d00 (WordEffect.nil 0)))
  have hGuardFull : EGuard ((u ++ da) ++ [K]) := eGuard_append (eGuard_append hGuardU)
  rcases eStep_of_eGuard_phaseScan hGuardFull hFull hI (by omega) hHeightV hE' with ⟨hGuardV,
    hBarrier⟩
  let J := Hv + 1
  let A' := 1 + n * 8
  let B' := A' + carry'
  have hUpper : B' < 2 ^ J := by
    change 1 + n * 8 + carry' < 2 ^ (Hv + 1)
    rw [Nat.pow_succ]; omega
  rcases exists_digitVal_of_lt_pow J A' (by omega) with ⟨da', hDA'⟩
  rcases exists_digitVal_of_lt_pow J B' hUpper with ⟨db', hDB'⟩
  have hHeightNew : heightShiftE v (h + 1) = some J := heightShiftE_succ v h Hv hHeightV
  let unit := sigma * wordScale v * (1 / 2)
  have hUp : 0 < unit := by
    have hSv := wordScale_pos v
    positivity
  have hUH : unit * ((2 ^ J : Nat) : Rat) = 1 := by
    have hHV := heightShiftE_sound v (h + 1) J hHeightNew
    have hp : ((2 ^ (h + 1) : Nat) : Rat) = ((2 ^ h : Nat) : Rat) * 2 := by
      rw [Nat.pow_succ]; push_cast; ring
    rw [hp] at hHV
    change (sigma * wordScale v * (1 / 2)) * ((2 ^ J : Nat) : Rat) = 1
    calc (sigma * wordScale v * (1 / 2)) * ((2 ^ J : Nat) : Rat)
      _ = sigma * (wordScale v * ((2 ^ J : Nat) : Rat)) * (1 / 2) := by ring
      _ = sigma * (((2 ^ h : Nat) : Rat) * 2) * (1 / 2) := by rw [hHV]
      _ = sigma * ((2 ^ h : Nat) : Rat) := by ring
      _ = 1 := hUnit
  have hDnew : unit * wordMassK db' <=
    (sigma + 3 * sigma * wordMass u +
    (45 / 56) * (sigma * wordScale u * wordMassK db)) * (1 / 2) := by
    have hDef := phaseScan_effect_sigma_contraction h (eff ++ db ++
      [K]) (n * 8) v a b carry' eff' sigma hI' hE' hSig hUnit
    have hZeros := digitVal_wordMassK_eq hDB'
    have hEq_cast : ((n * 8 + carry' + 2 : Nat) : Rat) = (B' : Rat) + 1 := by
      change ((n * 8 + carry' + 2 : Nat) : Rat) = ((1 + n * 8 + carry' : Nat) : Rat) + 1
      push_cast; ring
    rw [hEq_cast] at hDef
    change 1 - ((B' : Rat) + 1) * unit <=
      (sigma + sigma * (a - b - wordMassQ v)) * (1 / 2) - 3 * unit at hDef
    nlinarith
  have hPhiNew : 4 * (sigma * (1 / 2)) * wordMass v +
    (sigma * (1 / 2)) * wordScale v * wordMassK db' + 2 * (sigma * (1 / 2)) <= 1 / 256 := by
    have hDnew' : unit * wordMassK db' <=
      (sigma + 3 * (sigma * wordMass u) +
      (45 / 56) * (sigma * wordScale u * wordMassK db)) * (1 / 2) := by
      linarith
    have hBound :=
      eGood_contraction_ineq (sigma * wordMass u) (sigma * wordScale u * wordMassK db) sigma
      (sigma * wordMass v * (1 / 2)) (unit * wordMassK db') hMu (by linarith) (by linarith) hDnew'
    dsimp [unit] at hBound
    linarith
  have hPairNew : hasQKSubword eff' = true := by
    rcases hEe with ⟨ue, rfl⟩
    rcases hLow with ⟨lo, rfl⟩
    have hI_shape : PhaseScan (4 * 2 ^ h) ((ue ++ List.replicate 4 V) ++ K :: K :: K :: (lo ++
      [K])) (n * 16) v a b := by
      simpa [List.append_assoc] using! hI
    rcases phaseScan_four_V_three_K_div_eight hI_shape with ⟨x, y, hVy⟩
    rw [hVy] at hE'
    exact wordEffect_four_V_QQK_hasQKSubword hE'
  have hJ4 : 4 <= J := by
    have hHv3 : 4 <= Hv := by
      apply le_of_heightShiftE_append_replicate_V p 4 h Hv
      rw [<- hV]; exact hHeightV
    (try omega)
  have hLowNew : ∃ w, db' = K :: K :: K :: w := by
    have hE'_v : WordEffect 0 (p ++ List.replicate 4 V) carry' eff' := by rwa [<- hV]
    rcases wordEffect_append_replicate_V_inv p 4 0 carry' eff' hE'_v with ⟨w, m, _, hCm⟩
    have h4 : (2 : Nat) ^ 4 = 16 := rfl
    rw [h4] at hCm
    have hDiv8 : ∃ q, B' = q * 2 ^ 3 :=
      ⟨n + m * 2, by change 1 + n * 8 + carry' = (n + m * 2) * 8; omega⟩
    rcases digitVal_low_zeros_prefix 3 B' J db' hDB' (by omega) hDiv8 with ⟨rest, hRest⟩
    exact ⟨rest, hRest⟩
  have hHighNew : ∃ w, db' = w ++ List.replicate 7 Q := by
    refine digitVal_unit_massK_bound hDB' hUp hUH ?_ ?_
    · rcases hLowNew with ⟨w, rfl⟩
      have hw := wordMass_nonneg w
      dsimp [wordMassK]; linarith
    · have hWv := wordMass_nonneg v
      have hSuv : 0 <= (sigma * (1 / 2)) * wordMass v := mul_nonneg (by linarith) hWv.1
      dsimp [unit]
      linarith
  refine ⟨v ++ da', ?_, ?_⟩
  · exact EStep.intro h (u ++ da) (eff ++ db ++ [K]) (n * 8) v a b J da' hFull hI' (by omega) hDA'
  · refine EGood.intro (h + 1) J v A' da' carry' eff' B' db' (sigma * (1 / 2))
      hHeightNew hGuardV ⟨p, hV⟩ hDA' hE' rfl hDB' hPairNew hLowNew hHighNew ?_ hPhiNew
    have hUnit' := hUnit
    rw [Nat.pow_succ]; push_cast at hUnit' ⊢; linarith
def decodeDigitsE : Nat -> Nat -> Option (WordList)
  | 0, _ => none
  | _ + 1, 0 => none
  | _ + 1, 1 => some [Q]
  | fuel + 1, m + 2 =>
    forceNat ((m + 2) / 2) (fun q =>
      match decodeDigitsE fuel q with
      | none => none
      | some ws => forceWord (if (m + 2) % 2 == 0 then K else Q) (fun w => some (w :: ws)))
theorem decodeDigitsE_sound (fuel : Nat) :
    ∀ (m : Nat) (ws : WordList), decodeDigitsE fuel m = some ws ->
      ∃ H, DigitVal m H ws := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1, DigitVal.one DigitVal.nil⟩
    · dsimp [decodeDigitsE, forceNat] at h
      simp only [forceWord_eq] at h
      cases hrec : decodeDigitsE fuel ((m + 2) / 2) with
      | none => rw [hrec] at h; contradiction
      | some ws' =>
        rw [hrec] at h
        injection h with h; subst h
        rcases ih ((m + 2) / 2) ws' hrec with ⟨H, hD⟩
        rcases Nat.mod_two_eq_zero_or_one (m + 2) with hmod | hmod
        · have hcond : ((m + 2) % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [hcond]
          refine ⟨1 + H, ?_⟩
          have heq : m + 2 = ((m + 2) / 2) * 2 := by omega
          rw [heq]; exact DigitVal.zero hD
        · have hcond : ((m + 2) % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [hcond]
          refine ⟨1 + H, ?_⟩
          have heq : m + 2 = 1 + ((m + 2) / 2) * 2 := by omega
          rw [heq]; exact DigitVal.one hD
def stripWordPrefixE : WordList -> WordList -> Option (WordList)
  | [], u => some u
  | V :: p, V :: u => stripWordPrefixE p u
  | K :: p, K :: u => stripWordPrefixE p u
  | Q :: p, Q :: u => stripWordPrefixE p u
  | _, _ => none
theorem stripWordPrefixE_sound (p : WordList) :
    ∀ (u v : WordList), stripWordPrefixE p u = some v -> u = p ++ v := by
  induction p with
  | nil => intro u v h; injection h
  | cons w p ih =>
    intro u v h
    cases u with
    | nil => cases w <;> contradiction
    | cons x u =>
      cases w <;> cases x <;> try contradiction
      all_goals
        dsimp [stripWordPrefixE] at h
        rw [ih u v h]; rfl
inductive ChoiceE where
  | CT | CP0 | CP1 | CS00 | CS01 | CS10 | CS11
deriving DecidableEq
open ChoiceE
inductive CodeE where
  | Stop (n : Nat)
  | More (ch : ChoiceE) (n : Nat) (next : CodeE)
def choiceInCoeffE : ChoiceE -> Nat -> Nat
  | CT, n => 3 + n
  | CP0, n | CP1, n => 1 + n
  | CS00, n | CS01, n => 2 + n * 4
  | CS10, n | CS11, n => 4 + n * 4
def choiceOutCoeffE : ChoiceE -> Nat -> Nat
  | CT, n => 2 + n * 2
  | CP0, n | CS00, n | CS10, n => n * 2
  | CP1, n | CS01, n | CS11, n => 1 + n * 2
def choiceInWordsE : ChoiceE -> WordList
  | CT => [V]
  | CP0 => [Q, K]
  | CP1 => [Q, Q]
  | CS00 | CS10 => [K]
  | CS01 | CS11 => [Q]
def choiceOutWordE : ChoiceE -> Word
  | CT | CP0 | CP1 => V
  | CS00 | CS01 => K
  | CS10 | CS11 => Q
def evalCodeScanE : CodeE -> Nat -> WordList -> Option (Nat × WordList)
  | .Stop n, k, [] =>
    if k == n * 2 && 0 < n then some (n, []) else none
  | .Stop _, _, _ :: _ => none
  | .More ch m c, k, u =>
    if k == choiceInCoeffE ch m then
      match stripWordPrefixE (choiceInWordsE ch) u with
      | none => none
      | some w =>
        forceNat (choiceOutCoeffE ch m) (fun k' =>
          match evalCodeScanE c k' w with
          | none => none
          | some (n, v) => forceWord (choiceOutWordE ch) (fun wj => some (n, wj :: v)))
    else none
theorem evalCodeScanE_sound (c : CodeE) :
    ∀ (k : Nat) (u : WordList) (n : Nat) (v : WordList),
      evalCodeScanE c k u = some (n, v) ->
      ∃ a b, PhaseScan k u (n * 2) v a b /\ 0 < n := by
  induction c with
  | Stop m =>
    intro k u n v hE
    cases u with
    | cons _ _ => contradiction
    | nil =>
      dsimp [evalCodeScanE, forceNat] at hE
      cases hcond : (k == m * 2 && decide (0 < m)) with
      | false => rw [hcond] at hE; contradiction
      | true =>
        rw [hcond] at hE
        injection hE with hE
        injection hE with hm hv; subst hm hv
        rcases Bool.and_eq_true_iff.mp hcond with ⟨hk, hpos⟩
        have rfl_k : k = m * 2 := beq_iff_eq.mp hk
        subst rfl_k
        exact ⟨0, 0, PhaseScan.nil (m * 2), of_decide_eq_true hpos⟩
  | More ch m c ih =>
    intro k u n v hE
    dsimp [evalCodeScanE] at hE
    cases hk : (k == choiceInCoeffE ch m) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE; dsimp at hE
      have rfl_k : k = choiceInCoeffE ch m := beq_iff_eq.mp hk
      subst rfl_k
      cases hU : stripWordPrefixE (choiceInWordsE ch) u with
      | none => rw [hU] at hE; contradiction
      | some w =>
        rw [hU] at hE; dsimp at hE
        cases hC : evalCodeScanE c (choiceOutCoeffE ch m) w with
        | none => rw [hC] at hE; contradiction
        | some nv =>
          rw [hC] at hE
          rcases nv with ⟨n', x⟩
          dsimp [forceNat] at hE
          rw [forceWord_eq] at hE
          injection hE with hE
          injection hE with hn hv; subst hn hv
          have rfl_u := stripWordPrefixE_sound (choiceInWordsE ch) u w hU
          subst rfl_u
          rcases ih (choiceOutCoeffE ch m) w n' x hC with ⟨a, b, hS, hPos⟩
          cases ch
          · exact ⟨a * (1 / 2), b * (1 / 2), PhaseScan.T hS, hPos⟩
          · exact ⟨a * (1 / 2), (1 + b) * (1 / 2), PhaseScan.pair0 hS, hPos⟩
          · exact ⟨a * (1 / 2), (3 / 4) + b * (1 / 2), PhaseScan.pair1 hS, hPos⟩
          · exact ⟨3 + a * 2, b * 2, PhaseScan.short00 hS, hPos⟩
          · exact ⟨2 + a * 2, b * 2, PhaseScan.short01 hS, hPos⟩
          · exact ⟨4 + a * 2, b * 2, PhaseScan.short10 hS, hPos⟩
          · exact ⟨3 + a * 2, b * 2, PhaseScan.short11 hS, hPos⟩
def evalEStep (h : Nat) (c : CodeE) (orig : WordList) : Option (WordList) :=
  let (carry, eff) := evalEffect 0 (orig ++ [K])
  if carry == 0 then
    forceNat (4 * 2 ^ h) (fun k =>
      match evalCodeScanE c k eff with
      | none => none
      | some (n, v) =>
        forceNat (1 + n) (fun m =>
          match decodeDigitsE 64 m with
          | none => none
          | some da => some (v ++ da)))
  else none
theorem evalEStep_sound (h : Nat) (c : CodeE) (orig out : WordList)
    (hR : evalEStep h c orig = some out) :
    EStep h orig out := by
  dsimp [evalEStep, forceNat] at hR
  have hE := evalEffect_sound (orig ++ [K]) 0
  generalize h_ev : evalEffect 0 (orig ++ [K]) = ce at hR hE
  rcases ce with ⟨carry, eff⟩
  dsimp at hE hR
  cases hc : (carry == 0) with
  | false => rw [hc] at hR; contradiction
  | true =>
    rw [hc] at hR; dsimp at hR
    have rfl_c : carry = 0 := beq_iff_eq.mp hc
    subst rfl_c
    cases hP : evalCodeScanE c (4 * 2 ^ h) eff with
    | none => rw [hP] at hR; contradiction
    | some nv =>
      rw [hP] at hR
      rcases nv with ⟨n, v⟩
      dsimp at hR
      cases hD : decodeDigitsE 64 (1 + n) with
      | none => rw [hD] at hR; contradiction
      | some da =>
        rw [hD] at hR
        injection hR with hR; subst hR
        rcases evalCodeScanE_sound c (4 * 2 ^ h) eff n v hP with ⟨a, b, hS, hPos⟩
        rcases decodeDigitsE_sound 64 (1 + n) da hD with ⟨J, hDig⟩
        exact EStep.intro h orig eff n v a b J da hE hS hPos hDig
inductive ERounds : Nat -> WordList -> Nat -> WordList -> Prop where
  | refl (h : Nat) (u : WordList) : ERounds h u h u
  | next {h : Nat} {u v : WordList} {j : Nat} {w : WordList} :
      EStep h u v -> ERounds (h + 1) v j w -> ERounds h u j w
def evalERounds : Nat -> List CodeE -> WordList -> Option (WordList)
  | _, [], u => some u
  | h, c :: cs, u =>
    match evalEStep h c u with
    | none => none
    | some v => forceNat (h + 1) (fun h' => evalERounds h' cs v)
theorem evalERounds_sound (cs : List CodeE) :
    ∀ (h : Nat) (u v : WordList),
      evalERounds h cs u = some v ->
      ERounds h u (h + cs.length) v := by
  induction cs with
  | nil =>
    intro h u v hR
    injection hR with hR; subst hR
    simpa using! ERounds.refl h u
  | cons c cs ih =>
    intro h u v hR
    dsimp [evalERounds, forceNat] at hR
    cases hW : evalEStep h c u with
    | none => rw [hW] at hR; contradiction
    | some w =>
      rw [hW] at hR
      have hStep := evalEStep_sound h c u w hW
      have hSub := ih (h + 1) w v hR
      have heq : (h + 1) + cs.length = h + (c :: cs).length := by simp; omega
      rw [heq] at hSub
      exact ERounds.next hStep hSub
def isDigitWordE : Word -> Bool
  | V => false
  | _ => true
theorem exists_digitVal_of_all_isDigitWordE (ds : WordList) (h : ds.all isDigitWordE = true) :
    ∃ A, DigitVal A ds.length ds := by
  induction ds with
  | nil => exact ⟨0, DigitVal.nil⟩
  | cons w ds ih =>
    cases w
    · contradiction
    · dsimp [List.all, isDigitWordE] at h
      rcases ih h with ⟨A, hI⟩
      have heq : (K :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨A * 2, DigitVal.zero hI⟩
    · dsimp [List.all, isDigitWordE] at h
      rcases ih h with ⟨A, hI⟩
      have heq : (Q :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨1 + A * 2, DigitVal.one hI⟩
theorem eGood_of_check (h : Nat) (u da db : WordList)
    (hHt : heightShiftE u h = some da.length)
    (hGu : EGuard u)
    (hEnd : u = u.take (u.length - 4) ++ List.replicate 4 V)
    (hDig : da.all isDigitWordE = true)
    (hLast : (evalEffect (evalEffect 0 u).1 da).1 = 0)
    (hDB_eq : (evalEffect (evalEffect 0 u).1 da).2 = db)
    (hPair : hasQKSubword (evalEffect 0 u).2 = true)
    (hLo : db = K :: K :: K :: db.drop 3)
    (hHi : db = db.take (db.length - 7) ++ List.replicate 7 Q)
    (hPhi : 4 * (1 / ((2 ^ h : Nat) : Rat)) * wordMass u +
      (1 / ((2 ^ h : Nat) : Rat)) * wordScale u * wordMassK db +
      2 * (1 / ((2 ^ h : Nat) : Rat)) <= 1 / 256) :
    EGood h (u ++ da) := by
  rcases exists_digitVal_of_all_isDigitWordE da hDig with ⟨A, hDA⟩
  have hEU := evalEffect_sound u 0
  let carry := (evalEffect 0 u).1
  let eff := (evalEffect 0 u).2
  have hED := evalEffect_sound da carry
  rw [hLast, hDB_eq] at hED
  rcases wordEffect_digitVal hED hDA with ⟨B, hDB, hSum⟩
  simp only [Nat.zero_mul, Nat.add_zero] at hSum
  refine EGood.intro h da.length u A da carry eff B db (1 / ((2 ^ h : Nat) : Rat))
    hHt hGu ⟨u.take (u.length - 4), hEnd⟩ hDA hEU hSum hDB hPair
    ⟨db.drop 3, hLo⟩ ⟨db.take (db.length - 7), hHi⟩ ?_ hPhi
  have hpos : ((2 ^ h : Nat) : Rat) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (pow_two_pos h)
  exact one_div_mul_cancel hpos

end BusyBeaver.WordCalculus
