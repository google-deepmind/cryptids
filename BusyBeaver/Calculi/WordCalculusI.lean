/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Calculi.WordCalculusH
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver Counter

namespace BusyBeaver.WordCanonBR
set_option quotPrecheck false
set_option maxRecDepth 4000000

variable {Γ₀ Λ₀ α β γ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
open WordCalculus Word BRIncs
local notation "WordList" => List Word

def modeScaleWeight : Bool -> Rat
  | false => 1
  | true => 1 / 4

theorem bScan_scale_le {s : Bool} {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : BScan s k u k' v a b) :
    wordScale v <= modeScaleWeight s * wordScale u := by
  induction h with
  | nil _ => simp [wordScale, modeScaleWeight]
  | T _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | @pair0 _ u _ _ _ _ _ ih =>
    have hp := wordScale_pos u
    dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | @pair1 _ u _ _ _ _ _ ih =>
    have hp := wordScale_pos u
    dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | short00 _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | short01 _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | short10 _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | short11 _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | @odd_chain0 r m u k v a b _ ih =>
    dsimp [wordScale, modeScaleWeight] at ih ⊢;
      rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
    have hp := wordScale_pos u
    rcases powHalf_and_powFour_bounds r with ⟨hiv1, hiv2, hp4, _⟩
    nlinarith
  | @odd_chain1 r m u k v a b _ ih =>
    dsimp [wordScale, modeScaleWeight] at ih ⊢;
      rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
    have hp := wordScale_pos u
    rcases powHalf_and_powFour_bounds r with ⟨hiv1, hiv2, hp4, _⟩
    nlinarith
  | @even_chain r m u k v a b _ ih =>
    have h1r : List.replicate (1 + r) V ++ v = V :: (List.replicate r V ++ v) := by
      rw [Nat.add_comm 1 r, List.replicate_succ, List.cons_append]
    rw [h1r]; dsimp [wordScale, modeScaleWeight] at ih ⊢;
      rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
    have hp := wordScale_pos u
    rcases powHalf_and_powFour_bounds r with ⟨hiv1, hiv2, hp4, _⟩
    nlinarith
  | shift_pair0 _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | shift_pair1 _ ih => dsimp [wordScale, modeScaleWeight] at ih ⊢; linarith
  | @shift_chain0 r m u k v a b _ ih =>
    have h1r : List.replicate (1 + r) V ++ v = V :: (List.replicate r V ++ v) := by
      rw [Nat.add_comm 1 r, List.replicate_succ, List.cons_append]
    dsimp [wordScale, modeScaleWeight] at ih ⊢; rw [h1r]; dsimp [wordScale];
      rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
    have hp := wordScale_pos u
    rcases powHalf_and_powFour_bounds r with ⟨hiv1, hiv2, hp4, _⟩
    nlinarith
  | @shift_chain1 r m u k v a b _ ih =>
    have h1r : List.replicate (1 + r) V ++ v = V :: (List.replicate r V ++ v) := by
      rw [Nat.add_comm 1 r, List.replicate_succ, List.cons_append]
    dsimp [wordScale, modeScaleWeight] at ih ⊢; rw [h1r]; dsimp [wordScale];
      rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
    have hp := wordScale_pos u
    rcases powHalf_and_powFour_bounds r with ⟨hiv1, hiv2, hp4, _⟩
    nlinarith

theorem not_bScan_odd_cons_K (n : Nat) (u : WordList) (k' : Nat) (v : WordList) (a b : Rat) :
    ¬ BScan false (1 + n * 2) (K :: u) k' v a b := by
  intro h
  generalize hs : false = s at h
  generalize hk : 1 + n * 2 = k at h
  generalize hu : K :: u = w at h
  cases h with
  | short00 _ => omega
  | short10 _ => omega
  | odd_chain0 r _ => cases r <;> simp [zQK] at hu
  | odd_chain1 r _ => cases r <;> simp [zQK] at hu
  | even_chain _ _ => omega
  | _ => simp at hs hu

theorem not_bScan_odd_of_startsWithQKOrQQ {n : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b :
    Rat}
    (h : BScan false (1 + n * 2) u k' v a b)
    (hL : startsWithQKOrQQ (Q :: u) = true) :
    startsWithQKOrQQ u = true := by
  cases u with
  | nil => contradiction
  | cons t0 u' =>
    cases t0 with
    | V => exact hL
    | K => exact False.elim (not_bScan_odd_cons_K n u' k' v a b h)
    | Q =>
      generalize hs : false = s at h
      generalize hk : 1 + n * 2 = k at h
      generalize hu : Q :: u' = w at h
      cases h with
      | pair0 _ => simp [startsWithQKOrQQ, z0L] at hu ⊢
      | pair1 _ => simp [startsWithQKOrQQ, z0L] at hu ⊢
      | short01 _ => omega
      | short11 _ => omega
      | odd_chain0 r _ =>
        cases r with
        | zero => simp [zQK] at hu
        | succ r' => simp [zQK, startsWithQKOrQQ, z0L] at hu ⊢
      | odd_chain1 r _ =>
        cases r with
        | zero => simp [zQK] at hu
        | succ r' => simp [zQK, startsWithQKOrQQ, z0L] at hu ⊢
      | _ => simp at hs hu

theorem bScan_scale_le_of_startsWithQKOrQQ {s : Bool} {k : Nat} {u : WordList} {k' : Nat} {v :
    WordList} {a b : Rat}
    (h : BScan s k u k' v a b)
    (hL : startsWithQKOrQQ u = true) :
    wordScale v <= (1 / 8) * modeScaleWeight s * wordScale u := by
  induction h with
  | nil _ => contradiction
  | T _ ih =>
    have hIH := ih hL
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | pair0 hSub _ =>
    have hUp := bScan_scale_le hSub
    dsimp [wordScale, modeScaleWeight] at hUp ⊢; linarith
  | pair1 hSub _ =>
    have hUp := bScan_scale_le hSub
    dsimp [wordScale, modeScaleWeight] at hUp ⊢; linarith
  | short00 _ ih =>
    have hIH := ih hL
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | short01 hSub ih =>
    have hIH := ih (not_bScan_odd_of_startsWithQKOrQQ hSub hL)
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | short10 _ ih =>
    have hIH := ih hL
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | short11 hSub ih =>
    have hIH := ih (not_bScan_odd_of_startsWithQKOrQQ hSub hL)
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | @odd_chain0 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [prependQK, zQK, List.replicate, wordScale, modeScaleWeight, powHalf] at hIH ⊢; linarith
    | succ r' =>
      have hUp := bScan_scale_le hSub
      dsimp [wordScale, modeScaleWeight] at hUp ⊢;
        rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
      have hp := wordScale_pos u
      rcases powHalf_and_powFour_bounds (r' + 1) with ⟨hiv1, hiv2, hp4, hge1⟩
      rcases hge1 (by omega) with ⟨_, h8⟩
      nlinarith
  | @odd_chain1 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [prependQK, zQK, List.replicate, wordScale, modeScaleWeight, powHalf] at hIH ⊢; linarith
    | succ r' =>
      have hUp := bScan_scale_le hSub
      dsimp [wordScale, modeScaleWeight] at hUp ⊢;
        rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
      have hp := wordScale_pos u
      rcases powHalf_and_powFour_bounds (r' + 1) with ⟨hiv1, hiv2, hp4, hge1⟩
      rcases hge1 (by omega) with ⟨_, h8⟩
      nlinarith
  | @even_chain r m u k v a b hSub _ =>
    have hUp := bScan_scale_le hSub
    have h1r : List.replicate (1 + r) V ++ v = V :: (List.replicate r V ++ v) := by
      rw [Nat.add_comm 1 r, List.replicate_succ, List.cons_append]
    rw [h1r]; dsimp [wordScale, modeScaleWeight] at hUp ⊢;
      rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
    have hp := wordScale_pos u
    rcases powHalf_and_powFour_bounds r with ⟨hiv1, hiv2, hp4, _⟩
    nlinarith
  | shift_pair0 _ ih =>
    have hIH := ih hL
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | shift_pair1 hSub ih =>
    have hIH := ih (not_bScan_odd_of_startsWithQKOrQQ hSub hL)
    dsimp [wordScale, modeScaleWeight] at hIH ⊢; linarith
  | @shift_chain0 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [prependQK, zQK, List.replicate, wordScale, modeScaleWeight, powHalf] at hIH ⊢; linarith
    | succ r' =>
      have hUp := bScan_scale_le hSub
      have h1r : List.replicate (1 + (r' + 1)) V ++ v = V :: (List.replicate (r' + 1) V ++ v) := by
        rw [Nat.add_comm 1 (r' + 1), List.replicate_succ, List.cons_append]
      dsimp [wordScale, modeScaleWeight] at hUp ⊢; rw [h1r]; dsimp [wordScale];
        rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
      have hp := wordScale_pos u
      rcases powHalf_and_powFour_bounds (r' + 1) with ⟨hiv1, hiv2, hp4, hge1⟩
      rcases hge1 (by omega) with ⟨_, h8⟩
      nlinarith
  | @shift_chain1 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [prependQK, zQK, List.replicate, wordScale, modeScaleWeight, powHalf] at hIH ⊢; linarith
    | succ r' =>
      have hUp := bScan_scale_le hSub
      have h1r : List.replicate (1 + (r' + 1)) V ++ v = V :: (List.replicate (r' + 1) V ++ v) := by
        rw [Nat.add_comm 1 (r' + 1), List.replicate_succ, List.cons_append]
      dsimp [wordScale, modeScaleWeight] at hUp ⊢; rw [h1r]; dsimp [wordScale];
        rw [wordScale_replicate_V_append, wordScale_prependQK]; dsimp [wordScale]
      have hp := wordScale_pos u
      rcases powHalf_and_powFour_bounds (r' + 1) with ⟨hiv1, hiv2, hp4, hge1⟩
      rcases hge1 (by omega) with ⟨_, h8⟩
      nlinarith

-- ModeU and WordPrefixMode (downward BScan existence on u)
inductive ModeU where
  | ME
  | MO
  | MS
deriving DecidableEq

open ModeU

inductive WordPrefixMode : ModeU -> WordList -> Prop where
  | base_E : WordPrefixMode ME [V]
  | base_O : WordPrefixMode MO [V]
  | T_E {u : WordList} : WordPrefixMode MO u -> WordPrefixMode ME (V :: u)
  | T_O {u : WordList} : WordPrefixMode MO u -> WordPrefixMode MO (V :: u)
  | odd_c (r : Nat) {u : WordList} : WordPrefixMode MS u -> WordPrefixMode MO (prependQK r (V :: u))
  | short_K {u : WordList} : WordPrefixMode ME u -> WordPrefixMode ME (K :: u)
  | even_c (r : Nat) {u : WordList} : WordPrefixMode MS u ->
    WordPrefixMode ME (K :: prependQK r (V :: u))
  | shift_K {u : WordList} : WordPrefixMode ME u -> WordPrefixMode MS (K :: u)
  | shift_c (r : Nat) {u : WordList} : WordPrefixMode MS u ->
    WordPrefixMode MS (K :: prependQK r (V :: u))
  | short_Q {u : WordList} : WordPrefixMode MO u -> WordPrefixMode ME (Q :: u)
  | shift_Q {u : WordList} : WordPrefixMode MO u -> WordPrefixMode MS (Q :: u)
  | pair0_E {u : WordList} : WordPrefixMode ME u -> WordPrefixMode ME (Q :: K :: u)
  | pair0_O {u : WordList} : WordPrefixMode ME u -> WordPrefixMode MO (Q :: K :: u)
  | pair1_E {u : WordList} : WordPrefixMode MO u -> WordPrefixMode ME (Q :: Q :: u)
  | pair1_O {u : WordList} : WordPrefixMode MO u -> WordPrefixMode MO (Q :: Q :: u)

def WordPrefixChain (w : WordList) : Prop := ∃ r u, w = prependQK r (V :: u) /\ WordPrefixMode MS u

theorem wordPrefixMode_all (u_pre : WordList) :
    let w := u_pre ++ [V]
    (WordPrefixMode ME w \/ WordPrefixChain w) /\
    (WordPrefixMode MO w \/ (WordPrefixMode MS w /\
      (WordPrefixMode ME (Q :: w) \/ WordPrefixChain (Q :: w)) /\ WordPrefixMode MO (Q :: w))) := by
  induction u_pre with
  | nil =>
    exact ⟨Or.inl WordPrefixMode.base_E, Or.inl WordPrefixMode.base_O⟩
  | cons a u ih =>
    rcases ih with ⟨hEC, hOS⟩
    cases a with
    | V =>
      rcases hOS with hO | ⟨hS, _, _⟩
      · exact ⟨Or.inl (WordPrefixMode.T_E hO), Or.inl (WordPrefixMode.T_O hO)⟩
      · exact ⟨Or.inr ⟨0, u ++ [V], rfl, hS⟩, Or.inl (WordPrefixMode.odd_c 0 hS)⟩
    | K =>
      rcases hEC with hE | ⟨r, u0, hw, hS⟩
      · exact ⟨Or.inl (WordPrefixMode.short_K hE),
          Or.inr ⟨WordPrefixMode.shift_K hE, Or.inl (WordPrefixMode.pair0_E hE),
            WordPrefixMode.pair0_O hE⟩⟩
      · dsimp at hw ⊢; rw [hw]
        exact ⟨Or.inl (WordPrefixMode.even_c r hS),
          Or.inr ⟨WordPrefixMode.shift_c r hS, Or.inr ⟨r + 1, u0, rfl, hS⟩,
            WordPrefixMode.odd_c (r + 1) hS⟩⟩
    | Q =>
      rcases hOS with hO | ⟨_, hQ_EC, hQ_O⟩
      · exact ⟨Or.inl (WordPrefixMode.short_Q hO),
          Or.inr ⟨WordPrefixMode.shift_Q hO, Or.inl (WordPrefixMode.pair1_E hO),
            WordPrefixMode.pair1_O hO⟩⟩
      · exact ⟨hQ_EC, Or.inl hQ_O⟩

theorem wordPrefixMode_MO_cons_V (w : WordList) : WordPrefixMode MO (V :: (w ++ [V])) := by
  rcases (wordPrefixMode_all w).2 with hO | ⟨hS, _, _⟩
  · exact WordPrefixMode.T_O hO
  · exact WordPrefixMode.odd_c 0 hS

theorem wordPrefixMode_ME_cons_V_V (w : WordList) : WordPrefixMode ME (V :: V :: (w ++ [V])) :=
  WordPrefixMode.T_E (wordPrefixMode_MO_cons_V w)

theorem one_le_wordWeightCanon_of_MS {u : WordList} (h : WordPrefixMode MS u) : 1 <=
    wordWeightCanon u := by
  generalize hm : MS = m at h
  cases h with
  | @shift_K u0 _ => have := (wordWeightCanon_nonneg u0).2.2.2; dsimp [wordWeightCanon]; linarith
  | @shift_c r u0 _ =>
    have := (wordWeightCanon_nonneg u0).2.2.2
    dsimp [wordWeightCanon]; rw [loc_z0W_prependQK]; dsimp [wordWeightCanon]
    rcases powHalf_and_powFour_bounds r with ⟨_, _, hp4, _⟩
    nlinarith
  | @shift_Q u0 _ => have := (wordWeightCanon_nonneg u0).2.2.2; dsimp [wordWeightCanon]; linarith
  | _ => contradiction

theorem exists_bScan_of_wordPrefixMode {m : ModeU} {w : WordList} (hI : WordPrefixMode m w) :
    ((m = ME \/ m = MO) ->
      ∀ (k : Nat),
        (m = ME -> ∃ n, k = n * 2) ->
        (m = MO -> ∃ n, k = 1 + n * 2) ->
        16 * wordWeightCanon w < (k : Rat) - 3 ->
        ∃ m' v a b, BScan false k w (1 + m') v a b /\ 0 < m') /\
    (m = MS ->
      ∀ (k : Nat),
        (∃ n, k = 1 + n * 2) ->
        4 * wordWeightCanon w - 4 < (k : Rat) - 3 ->
        ∃ m' v a b, BScan true k w (1 + m') v a b /\ 0 < m') := by
  induction hI with
  | base_E =>
    refine ⟨fun _ k hE _ hk => ?_, fun h => by contradiction⟩
    rcases hE rfl with ⟨n, rfl⟩
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    refine ⟨(2 * n - 2) * 2, [V], 0, 0, ?_ , by omega⟩
    have heq1 : n * 2 = 2 + (n - 1) * 2 := by omega
    have heq2 : 1 + (2 * n - 2) * 2 = 1 + ((n - 1) * 2) * 2 := by omega
    rw [heq1, heq2]
    simpa using! BScan.T (BScan.nil _)
  | base_O =>
    refine ⟨fun _ k _ hO hk => ?_, fun h => by contradiction⟩
    rcases hO rfl with ⟨n, rfl⟩
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    refine ⟨(2 * n - 1) * 2, [V], 0, 0, ?_ , by omega⟩
    have heq1 : 1 + n * 2 = 2 + (n * 2 - 1) := by omega
    have heq2 : 1 + (2 * n - 1) * 2 = 1 + (n * 2 - 1) * 2 := by omega
    rw [heq1, heq2]
    simpa using! BScan.T (BScan.nil _)
  | @T_E u hO ih =>
    refine ⟨fun _ k hE _ hk => ?_, fun h => by contradiction⟩
    rcases hE rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hn_q : (n : Rat) * 2 = 2 + ((n * 2 - 2 : Nat) : Rat) := by
      exact_mod_cast (by omega : n * 2 = 2 + (n * 2 - 2))
    rcases ih.1 (Or.inr rfl) (1 +
      (n * 2 - 2) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2 - 2, rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hS, hm'⟩
    have heq : n * 2 = 2 + (n * 2 - 2) := by omega
    rw [heq]
    exact ⟨m', V :: v, a * (1 / 2), b * (1 / 2), BScan.T hS, hm'⟩
  | @T_O u hO ih =>
    refine ⟨fun _ k _ hO_k hk => ?_, fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hn_q : 1 + (n : Rat) * 2 = 2 + ((n * 2 - 1 : Nat) : Rat) := by
      exact_mod_cast (by omega : 1 + n * 2 = 2 + (n * 2 - 1))
    rcases ih.1 (Or.inr rfl) (1 +
      (n * 2 - 1) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2 - 1, rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hS, hm'⟩
    have heq : 1 + n * 2 = 2 + (n * 2 - 1) := by omega
    rw [heq]
    exact ⟨m', V :: v, a * (1 / 2), b * (1 / 2), BScan.T hS, hm'⟩
  | @odd_c r u hS ih =>
    refine ⟨fun _ k _ hO_k hk => ?_, fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n, rfl⟩
    have hWu := one_le_wordWeightCanon_of_MS hS
    rw [wordWeightCanon_prependQK] at hk; dsimp [wordWeightCanon] at hk
    rcases powHalf_and_powFour_bounds r with ⟨_, _, hp4, _⟩
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; nlinarith
    have hpow_ge : 2 <= 2 ^ (1 + r) := by
      rw [pow_two_one_add r]; have := pow_two_pos r; omega
    rcases even_or_odd_mul_two (n - 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hk_eq : 1 + n * 2 = 3 + m * 4 := by omega
      have hm_pow : m * 2 <= m * 2 ^ (1 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : (m : Rat) * 2 <= ((m * 2 ^ (1 + r) : Nat) : Rat) := by exact_mod_cast hm_pow
      have hm_q : (n : Rat) = 1 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 1 + m * 2)
      rcases ih.2 rfl (1 + m * 2 ^ (1 + r)) ⟨m * 2 ^ r, by rw [pow_two_one_add r]; ring⟩
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', K :: (List.replicate r V ++ v), (2 + a * 2) * powHalf r, b * 2 * powHalf r,
        BScan.odd_chain0 r hSub, hm'⟩
    · have hk_eq : 1 + n * 2 = 5 + m * 4 := by omega
      have hm_pow : m * 2 <= m * 2 ^ (1 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : (m : Rat) * 2 <= ((m * 2 ^ (1 + r) : Nat) : Rat) := by exact_mod_cast hm_pow
      have hm_q : (n : Rat) = 2 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 2 + m * 2)
      rcases ih.2 rfl (1 + m * 2 ^ (1 + r)) ⟨m * 2 ^ r, by rw [pow_two_one_add r]; ring⟩
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', Q :: (List.replicate r V ++ v), 1 + (2 + a * 2) * powHalf r, b * 2 * powHalf r,
        BScan.odd_chain1 r hSub, hm'⟩
  | @short_K u hE ih =>
    refine ⟨fun _ k hE_k _ hk => ?_, fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    rcases even_or_odd_mul_two n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm1 : 1 <= m := by omega
      have hk_eq : m * 2 * 2 = 4 + (m - 1) * 4 := by omega
      have hm_q : (m : Rat) = 1 + ((m - 1 : Nat) : Rat) := by
        exact_mod_cast (by omega : m = 1 + (m - 1))
      rcases ih.1 (Or.inl rfl) ((m - 1) * 2) (fun _ => ⟨m - 1, rfl⟩) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', Q :: v, (7 / 2) + a * 2, b * 2, BScan.short10 hSub, hm'⟩
    · have hk_eq : (1 + m * 2) * 2 = 2 + m * 4 := by omega
      rcases ih.1 (Or.inl rfl) (m * 2) (fun _ => ⟨m, rfl⟩) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', K :: v, (5 / 2) + a * 2, b * 2, BScan.short00 hSub, hm'⟩
  | @even_c r u hS ih =>
    refine ⟨fun _ k hE_k _ hk => ?_, fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n, rfl⟩
    have hWu := one_le_wordWeightCanon_of_MS hS
    dsimp [wordWeightCanon] at hk; rw [loc_z0W_prependQK] at hk;
      dsimp [wordWeightCanon] at hk
    rcases powHalf_and_powFour_bounds r with ⟨_, _, hp4, _⟩
    have hn3 : 3 <= n := by
      by_contra hlt; have : n <= 2 := by omega
      have hq : (n : Rat) <= 2 := by exact_mod_cast this
      push_cast at hk; nlinarith
    have hk_eq : n * 2 = 6 + (n - 3) * 2 := by omega
    have hn_q : (n : Rat) = 3 + ((n - 3 : Nat) : Rat) := by
      exact_mod_cast (by omega : n = 3 + (n - 3))
    have hpow_ge : 2 <= 2 ^ (1 + r) := by
      rw [pow_two_one_add r]; have := pow_two_pos r; omega
    have hm_pow : (1 + (n - 3) * 2) * 2 <= (1 + (n - 3) * 2) * 2 ^ (1 + r) :=
      Nat.mul_le_mul_left (1 + (n - 3) * 2) hpow_ge
    have hm_pow_q : (((1 + (n - 3) * 2) * 2 : Nat) : Rat) <=
      (((1 + (n - 3) * 2) * 2 ^ (1 + r) : Nat) : Rat) := by
      exact_mod_cast hm_pow
    rcases ih.2 rfl (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r)) ⟨(1 + (n - 3) * 2) * 2 ^ r,
      by rw [pow_two_one_add r]; ring⟩
      (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m', v, a, b, hSub, hm'⟩
    rw [hk_eq]
    exact ⟨m', List.replicate (1 + r) V ++ v, 1 + (1 + a) * (1 / 2) * powHalf r,
      b * (1 / 2) * powHalf r, BScan.even_chain r hSub, hm'⟩
  | @shift_K u hE ih =>
    refine ⟨fun h => by rcases h with h | h <;> contradiction, fun _ k hO_k hk => ?_⟩
    rcases hO_k with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    rcases ih.1 (Or.inl rfl) ((n * 2) * 2) (fun _ => ⟨n * 2, rfl⟩) (fun h => by contradiction)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
    exact ⟨m', V :: v, a * (1 / 2), (1 / 4) + b * (1 / 2), BScan.shift_pair0 hSub, hm'⟩
  | @shift_c r u hS ih =>
    refine ⟨fun h => by rcases h with h | h <;> contradiction, fun _ k hO_k hk => ?_⟩
    rcases hO_k with ⟨n, rfl⟩
    have hWu := one_le_wordWeightCanon_of_MS hS
    dsimp [wordWeightCanon] at hk; rw [loc_z0W_prependQK] at hk;
      dsimp [wordWeightCanon] at hk
    rcases powHalf_and_powFour_bounds r with ⟨_, _, hp4, _⟩
    have hn4 : 4 <= n := by
      by_contra hlt; have : n <= 3 := by omega
      have hq : (n : Rat) <= 3 := by exact_mod_cast this
      push_cast at hk; nlinarith
    have hpow_ge : 4 <= 2 ^ (2 + r) := by
      have h2r : 2 + r = 1 + (1 + r) := by omega
      rw [h2r, pow_two_one_add (1 + r), pow_two_one_add r]; have := pow_two_pos r; omega
    rcases even_or_odd_mul_two (n - 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hk_eq : 1 + n * 2 = 3 + m * 4 := by omega
      have hm_q : (n : Rat) = 1 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 1 + m * 2)
      have h_even_sub : ∃ n', 1 + m * 2 ^ (2 + r) = 1 + n' * 2 := by
        refine ⟨m * 2 ^ (1 + r), ?_⟩
        have h2r : 2 + r = (1 + r) + 1 := by omega
        rw [h2r, Nat.pow_succ]; ring
      have hm_pow : m * 4 <= m * 2 ^ (2 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : ((m * 4 : Nat) : Rat) <= ((m * 2 ^ (2 + r) : Nat) : Rat) := by
        exact_mod_cast hm_pow
      rcases ih.2 rfl (1 + m * 2 ^ (2 + r)) h_even_sub
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', K :: (List.replicate (1 + r) V ++ v), (1 + a) * powHalf r, b * powHalf r,
        BScan.shift_chain0 r hSub, hm'⟩
    · have hk_eq : 1 + n * 2 = 5 + m * 4 := by omega
      have hm_q : (n : Rat) = 2 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 2 + m * 2)
      have h_even_sub : ∃ n', 1 + m * 2 ^ (2 + r) = 1 + n' * 2 := by
        refine ⟨m * 2 ^ (1 + r), ?_⟩
        have h2r : 2 + r = (1 + r) + 1 := by omega
        rw [h2r, Nat.pow_succ]; ring
      have hm_pow : m * 4 <= m * 2 ^ (2 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : ((m * 4 : Nat) : Rat) <= ((m * 2 ^ (2 + r) : Nat) : Rat) := by
        exact_mod_cast hm_pow
      rcases ih.2 rfl (1 + m * 2 ^ (2 + r)) h_even_sub
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', Q :: (List.replicate (1 + r) V ++ v), 1 + (1 + a) * powHalf r, b * powHalf r,
        BScan.shift_chain1 r hSub, hm'⟩
  | @short_Q u hO ih =>
    refine ⟨fun _ k hE_k _ hk => ?_, fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    rcases even_or_odd_mul_two n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm1 : 1 <= m := by omega
      have hk_eq : m * 2 * 2 = 4 + (m - 1) * 4 := by omega
      have hm_q : (m : Rat) = 1 + ((m - 1 : Nat) : Rat) := by
        exact_mod_cast (by omega : m = 1 + (m - 1))
      rcases ih.1 (Or.inr rfl) (1 + (m - 1) * 2) (fun h => by contradiction) (fun _ => ⟨m - 1, rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', Q :: v, (5 / 2) + a * 2, b * 2, BScan.short11 hSub, hm'⟩
    · have hk_eq : (1 + m * 2) * 2 = 2 + m * 4 := by omega
      rcases ih.1 (Or.inr rfl) (1 + m * 2) (fun h => by contradiction) (fun _ => ⟨m, rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
      rw [hk_eq]
      exact ⟨m', K :: v, (3 / 2) + a * 2, b * 2, BScan.short01 hSub, hm'⟩
  | @shift_Q u hO ih =>
    refine ⟨fun h => by rcases h with h | h <;> contradiction, fun _ k hO_k hk => ?_⟩
    rcases hO_k with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    rcases ih.1 (Or.inr rfl) (1 + (n * 2) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2, rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
    exact ⟨m', V :: v, a * (1 / 2), (1 / 2) + b * (1 / 2), BScan.shift_pair1 hSub, hm'⟩
  | @pair0_E u hE ih =>
    refine ⟨fun _ k hE_k _ hk => ?_, fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hk_eq : n * 2 = 1 + (n * 2 - 1) := by omega
    have hn_q : (n : Rat) * 2 = 1 + ((n * 2 - 1 : Nat) : Rat) := by exact_mod_cast hk_eq
    rcases ih.1 (Or.inl rfl) ((n * 2 - 1) * 2) (fun _ => ⟨n * 2 - 1,
      rfl⟩) (fun h => by contradiction)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
    rw [hk_eq]
    exact ⟨m', V :: v, a * (1 / 2), (1 / 4) + b * (1 / 2), BScan.pair0 hSub, hm'⟩
  | @pair0_O u hE ih =>
    refine ⟨fun _ k _ hO_k hk => ?_, fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    rcases ih.1 (Or.inl rfl) ((n * 2) * 2) (fun _ => ⟨n * 2, rfl⟩) (fun h => by contradiction)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
    exact ⟨m', V :: v, a * (1 / 2), (1 / 4) + b * (1 / 2), BScan.pair0 hSub, hm'⟩
  | @pair1_E u hO ih =>
    refine ⟨fun _ k hE_k _ hk => ?_, fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hk_eq : n * 2 = 1 + (n * 2 - 1) := by omega
    have hn_q : (n : Rat) * 2 = 1 + ((n * 2 - 1 : Nat) : Rat) := by exact_mod_cast hk_eq
    rcases ih.1 (Or.inr rfl) (1 +
      (n * 2 - 1) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2 - 1, rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
    rw [hk_eq]
    exact ⟨m', V :: v, a * (1 / 2), (1 / 2) + b * (1 / 2), BScan.pair1 hSub, hm'⟩
  | @pair1_O u hO ih =>
    refine ⟨fun _ k _ hO_k hk => ?_, fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n, rfl⟩
    have hw := (wordWeightCanon_nonneg u).2.2.2
    dsimp [wordWeightCanon] at hk
    rcases ih.1 (Or.inr rfl) (1 + (n * 2) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2, rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m', v, a, b, hSub, hm'⟩
    exact ⟨m', V :: v, a * (1 / 2), (1 / 2) + b * (1 / 2), BScan.pair1 hSub, hm'⟩

theorem wordMassK_of_digitVal_zero {A H : Nat} {w : WordList} (h : DigitVal A H w) (h0 : A = 0) :
    wordMassK w = ((2 ^ H : Nat) : Rat) - 1 := by
  induction h with
  | nil => simp [wordMassK]
  | @zero A1 H1 u1 _ ih =>
    have hA1 : A1 = 0 := by omega
    rw [pow_two_one_add]; dsimp [wordMassK]; rw [ih hA1]; push_cast; ring
  | one _ => omega

theorem exists_bScan_piece3 {n_mid : Nat} (hn : 2 <= n_mid) :
    ∃ m_end d1 a_t b_t,
      BScan false (n_mid * 4) [K, Q, Q, Q, Q, K] (m_end * 8) [Q, d1, V, V] a_t b_t /\
      wordScale [Q, d1, V, V] = 1 /\
      wordWeightCanon [Q, d1, V, V] <= 15 / 4 /\
      startsWithQKOrQQ [Q, d1, V, V] = true /\
      a_t - b_t <= 6 /\
      b_t - a_t <= 0 := by
  have hm0 : 1 <= n_mid - 1 := by omega
  rcases even_or_odd_mul_two (n_mid - 1) with ⟨m1, hm1⟩ | ⟨m1, hm1⟩
  · have hm1_pos : 1 <= m1 := by omega
    have hk0 : n_mid * 4 = 4 + ((m1 - 1) * 2 + 2) * 4 := by omega
    have hk1 : ((m1 - 1) * 2 + 2) * 2 = 4 + (m1 - 1) * 4 := by omega
    have hB0 : BScan false (1 + ((m1 - 1) * 2) * 2) [Q,
      K] ((m1 - 1) * 8) [V] (0 * (1 / 2)) ((1 / 4) + 0 * (1 / 2)) := by
      have h := BScan.pair0 (BScan.nil (((m1 - 1) * 2) * 2 * 2))
      have heq : ((m1 - 1) * 2) * 2 * 2 = (m1 - 1) * 8 := by ring
      rw [heq] at h
      exact h
    have hB1 := BScan.pair1 hB0
    have hB2 := BScan.short11 hB1
    rw [<- hk1] at hB2
    have hB3 := BScan.short10 hB2
    rw [<- hk0] at hB3
    refine ⟨m1 - 1, Q, _, _, hB3, ?_⟩
    refine ⟨by norm_num [wordScale], by dsimp [wordWeightCanon, loc_z0W]; norm_num,
      rfl, by norm_num, by norm_num⟩
  · have hk0 : n_mid * 4 = 4 + (1 + m1 * 2) * 4 := by omega
    have hk1 : (1 + m1 * 2) * 2 = 2 + m1 * 4 := by omega
    have hB0 : BScan false (1 + (m1 * 2) * 2) [Q,
      K] (m1 * 8) [V] (0 * (1 / 2)) ((1 / 4) + 0 * (1 / 2)) := by
      have h := BScan.pair0 (BScan.nil ((m1 * 2) * 2 * 2))
      have heq : (m1 * 2) * 2 * 2 = m1 * 8 := by ring
      rw [heq] at h
      exact h
    have hB1 := BScan.pair1 hB0
    have hB2 := BScan.short01 hB1
    rw [<- hk1] at hB2
    have hB3 := BScan.short10 hB2
    rw [<- hk0] at hB3
    refine ⟨m1, K, _, _, hB3, ?_⟩
    refine ⟨by norm_num [wordScale], by dsimp [wordWeightCanon, loc_z0W]; norm_num,
      rfl, by norm_num, by norm_num⟩

theorem brIncs_of_bScan {s : Bool} {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h1 : BScan s k u k' v a b) :
    ∀ {r r' : HalfTape}, BRIncs false k' r r' -> BRIncs s k (evalWords u r) (evalWords v r') := by
  induction h1 with
  | nil _ => intro r r' h2; exact h2
  | T _ ih => intro r r' h2; exact BRIncs.T (ih h2)
  | pair0 _ ih => intro r r' h2; exact BRIncs.pair0 (ih h2)
  | pair1 _ ih => intro r r' h2; exact BRIncs.pair1 (ih h2)
  | short00 _ ih => intro r r' h2; exact BRIncs.short00 (ih h2)
  | short01 _ ih => intro r r' h2; exact BRIncs.short01 (ih h2)
  | short10 _ ih => intro r r' h2; exact BRIncs.short10 (ih h2)
  | short11 _ ih => intro r r' h2; exact BRIncs.short11 (ih h2)
  | @odd_chain0 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : evalWords (prependQK r_ch (V :: u)) r =
      evalWords (prependQK r_ch [V]) (evalWords u r) := by
      rw [<- evalWords_append, <- prependQK_append]; rfl
    have h_out : evalWords (K :: (List.replicate r_ch V ++
      v)) r' = d0 +> evalWords (List.replicate r_ch V) (evalWords v r') := by
      dsimp [evalWords]; rw [evalWords_append]
    rw [h_in, h_out]
    exact BRIncs.odd_chain0 r_ch (ih h2)
  | @odd_chain1 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : evalWords (prependQK r_ch (V :: u)) r =
      evalWords (prependQK r_ch [V]) (evalWords u r) := by
      rw [<- evalWords_append, <- prependQK_append]; rfl
    have h_out : evalWords (Q :: (List.replicate r_ch V ++
      v)) r' = d1 +> evalWords (List.replicate r_ch V) (evalWords v r') := by
      dsimp [evalWords]; rw [evalWords_append]
    rw [h_in, h_out]
    exact BRIncs.odd_chain1 r_ch (ih h2)
  | @even_chain r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : evalWords (K :: prependQK r_ch (V :: u)) r =
      d0 +> evalWords (prependQK r_ch [V]) (evalWords u r) := by
      dsimp [evalWords]; rw [<- evalWords_append, <- prependQK_append]; rfl
    have h_out : evalWords (List.replicate (1 + r_ch) V ++
      v) r' = evalWords (List.replicate (1 + r_ch) V) (evalWords v r') := by
      rw [evalWords_append]
    rw [h_in, h_out]
    exact BRIncs.even_chain r_ch (ih h2)
  | shift_pair0 _ ih => intro r r' h2; exact BRIncs.shift_pair0 (ih h2)
  | shift_pair1 _ ih => intro r r' h2; exact BRIncs.shift_pair1 (ih h2)
  | @shift_chain0 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : evalWords (K :: prependQK r_ch (V :: u)) r =
      d0 +> evalWords (prependQK r_ch [V]) (evalWords u r) := by
      dsimp [evalWords]; rw [<- evalWords_append, <- prependQK_append]; rfl
    have h_out : evalWords (K :: (List.replicate (1 + r_ch) V ++
      v)) r' = d0 +> evalWords (List.replicate (1 + r_ch) V) (evalWords v r') := by
      dsimp [evalWords]; rw [evalWords_append]
    rw [h_in, h_out]
    exact BRIncs.shift_chain0 r_ch (ih h2)
  | @shift_chain1 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : evalWords (K :: prependQK r_ch (V :: u)) r =
      d0 +> evalWords (prependQK r_ch [V]) (evalWords u r) := by
      dsimp [evalWords]; rw [<- evalWords_append, <- prependQK_append]; rfl
    have h_out : evalWords (Q :: (List.replicate (1 + r_ch) V ++
      v)) r' = d1 +> evalWords (List.replicate (1 + r_ch) V) (evalWords v r') := by
      dsimp [evalWords]; rw [evalWords_append]
    rw [h_in, h_out]
    exact BRIncs.shift_chain1 r_ch (ih h2)

theorem binary_of_digitVal {A H : Nat} {ds : WordList} (hD : DigitVal A H ds) :
    ∀ (n : Nat), A = 1 + n -> 2 ^ (H - 1) <= 1 + n -> Binary (1 + n) H (evalWords ds default) := by
  induction hD with
  | nil => intro n hA _; omega
  | @zero A' H' u hD' ih =>
    intro n hA hPow
    have hA'_pos : 1 <= A' := by omega
    cases H' with
    | zero =>
      have hlt := lt_pow_of_digitVal hD'
      omega
    | succ H'' =>
      have hpow_sub : 2 ^ ((1 + (H'' + 1)) - 1) = 2 ^ ((H'' + 1) - 1) * 2 := by
        simp [Nat.pow_succ]
      have hIH := ih (A' - 1) (by omega) (by omega)
      have hB := Binary.zero hIH
      have heq1 : 2 + (A' - 1) * 2 = 1 + n := by omega
      rw [heq1] at hB
      exact hB
  | @one A' H' u hD' ih =>
    intro n hA hPow
    cases H' with
    | zero =>
      have hlt := lt_pow_of_digitVal hD'
      have hA'0 : A' = 0 := by omega
      subst hA'0
      have hu : u = [] := (digitVal_unique_canon DigitVal.nil hD').symm
      subst hu
      have hn0 : n = 0 := by omega
      subst hn0
      exact Binary.one
    | succ H'' =>
      have hpow_sub : 2 ^ ((1 + (H'' + 1)) - 1) = 2 ^ ((H'' + 1) - 1) * 2 := by
        simp [Nat.pow_succ]
      have h_ge1 : 1 <= 2 ^ ((H'' + 1) - 1) := by
        have := pow_two_pos ((H'' + 1) - 1); omega
      have hA'_pos : 1 <= A' := by omega
      have hIH := ih (A' - 1) (by omega) (by omega)
      have hB := Binary.two hIH
      have heq1 : 3 + (A' - 1) * 2 = 1 + n := by omega
      rw [heq1] at hB
      exact hB

-- Section 7D: P33 prefix, BGood, BStep, phaseScan_budget_eq, finite rounds executor,
-- and machine glue

def prefix33Words : WordList :=
    ([V, V, Q, V, V, Q, V, V, K, V, V, K, V, V, Q, V, V, Q, V, V, K, V, V, K, V, V, Q, V, V, Q, V,
    V] ++ [K])

def out33Words : WordList :=
    ([V, Q, V, V, K, V, V, K, V, V, Q, V, V, Q, V, V, K, V, V, K, V, V, Q, V, V, Q, V, V, K, V, V,
    K] ++ [V])

def tail8Words : WordList := [Q, Q, K, K, Q, Q, Q, Q]

theorem digitVal_tail8Words : DigitVal 243 8 tail8Words :=
  DigitVal.one (DigitVal.one (DigitVal.zero (DigitVal.zero (DigitVal.one (DigitVal.one
    (DigitVal.one (DigitVal.one DigitVal.nil)))))))

theorem brIncs_step_11 (m : Nat) {k_in k_out : Nat} {r r' : HalfTape}
    (h1 : k_in = 4 + m * 2) (h2 : k_out = 1 + m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d1 +> r))) (t +> (d1 +> (t +> r'))) := by
  have h_in : k_in = 2 + (2 + m * 2) := by omega
  have h_out : k_out = 1 + (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair1 h
  have h_oc := BRIncs.odd_chain1 0 h_sp
  have h_mid : 5 + m * 4 = 1 + (2 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

theorem brIncs_step_01 (m : Nat) {k_in k_out : Nat} {r r' : HalfTape}
    (h1 : k_in = 3 + m * 2) (h2 : k_out = 1 + m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d1 +> r))) (t +> (d0 +> (t +> r'))) := by
  have h_in : k_in = 2 + (1 + m * 2) := by omega
  have h_out : k_out = 1 + (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair1 h
  have h_oc := BRIncs.odd_chain0 0 h_sp
  have h_mid : 3 + m * 4 = 1 + (1 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

theorem brIncs_step_00 (m : Nat) {k_in k_out : Nat} {r r' : HalfTape}
    (h1 : k_in = 3 + m * 2) (h2 : k_out = m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d0 +> r))) (t +> (d0 +> (t +> r'))) := by
  have h_in : k_in = 2 + (1 + m * 2) := by omega
  have h_out : k_out = (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair0 h
  have h_oc := BRIncs.odd_chain0 0 h_sp
  have h_mid : 3 + m * 4 = 1 + (1 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

theorem brIncs_step_10 (m : Nat) {k_in k_out : Nat} {r r' : HalfTape}
    (h1 : k_in = 4 + m * 2) (h2 : k_out = m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d0 +> r))) (t +> (d1 +> (t +> r'))) := by
  have h_in : k_in = 2 + (2 + m * 2) := by omega
  have h_out : k_out = (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair0 h
  have h_oc := BRIncs.odd_chain1 0 h_sp
  have h_mid : 5 + m * 4 = 1 + (2 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

theorem brIncs_prefix33Words {r r' : HalfTape} (h : BRIncs false 249044 r r') :
    BRIncs false 128 (evalWords prefix33Words r) (evalWords out33Words r') := by
  exact
    brIncs_step_11 62 rfl rfl (
    brIncs_step_01 123 rfl rfl (
    brIncs_step_00 245 rfl rfl (
    brIncs_step_10 488 rfl rfl (
    brIncs_step_11 974 rfl rfl (
    brIncs_step_01 1947 rfl rfl (
    brIncs_step_00 3893 rfl rfl (
    brIncs_step_10 7784 rfl rfl (
    brIncs_step_11 15566 rfl rfl (
    brIncs_step_01 31131 rfl rfl (
    brIncs_step_00 62261 rfl rfl h))))))))))

inductive BGood : WordList -> Prop where
  | intro (H : Nat) (u : WordList) (A : Nat) (hi8 : WordList) :
      DigitVal A H hi8 ->
      wordScale u * ((2 ^ H : Nat) : Rat) = 128 ->
      wordScale u <= 1 / 16 ->
      (∃ w, u = V :: V :: (w ++ [V])) ->
      startsWithQKOrQQ u = true ->
      (∃ w, hi8 = Q :: K :: w) ->
      wordWeightCanon u <= 74 / 5 ->
      wordScale u * wordMassK hi8 <= 1273 / 10 ->
      BGood (u ++ (hi8 ++ tail8Words))

inductive BStep : WordList -> WordList -> Prop where
  | intro (orig : WordList) (n : Nat) (v : WordList) (a b : Rat) (J : Nat) (ds : WordList) :
      BScan false 249044 (orig ++ [K]) (n * 2) v a b ->
      DigitVal (1 + n) J ds ->
      BStep orig ([V, V, K, V] ++ v ++ ds)

theorem bGood_progress {orig : WordList} (hG : BGood orig) :
    ∃ out, BStep orig out /\ BGood out := by
  rcases hG with ⟨H, u, A, hi8, hDig, hHeight, hU11, ⟨wu, hwu⟩, hLu, ⟨w0, hw0⟩, hWu_max, hZ_max⟩
  have hWu_nonneg := (wordWeightCanon_nonneg u).2.2.2
  have hSu := wordScale_pos u
  have hPrU : WordPrefixMode ME u := by rw [hwu]; exact wordPrefixMode_ME_cons_V_V wu
  have hk_in : 16 * wordWeightCanon u < (249044 : Rat) - 3 := by linarith only [hWu_max]
  rcases (exists_bScan_of_wordPrefixMode hPrU).1 (Or.inl rfl) 249044 (fun _ => ⟨124522,
    rfl⟩) (fun h => by contradiction) hk_in with ⟨m1, v1, a1, b1, hB1, hm1⟩
  have hSv1 := wordScale_pos v1
  have hWv1_nonneg := (wordWeightCanon_nonneg v1).2.2.2
  have h11_v1 : wordScale v1 <= (1 / 8) * wordScale u := by
    have := bScan_scale_le_of_startsWithQKOrQQ hB1 hLu; dsimp [modeScaleWeight] at this;
      linarith only [this]
  rcases (bScan_loss_bounds hB1).1 rfl with ⟨hW_v1, hAB_1, hBA_1⟩
  have hBud1 := bScan_budget_eq hB1
  subst hw0
  rcases digitVal_cons_Q_inv hDig with ⟨A1, H1, hD1, hA1, hH1⟩
  rcases digitVal_cons_K_inv hD1 with ⟨A0, H0, hD0, hA0, hH0⟩
  have hDw0 := digitVal_scale_and_mass hD0
  have hSw0 := wordScale_pos w0
  have hZw0_nonneg := (wordWeightCanon_nonneg w0).2.1
  have hPowH : ((2 ^ H : Nat) : Rat) = 4 * wordScale w0 := by
    have h1 : 2 ^ H = 4 * 2 ^ H0 := by
      rw [hH1, hH0, pow_two_one_add (1 + H0), pow_two_one_add H0]; ring
    have h2 : ((2 ^ H : Nat) : Rat) = ((4 * 2 ^ H0 : Nat) : Rat) := by exact_mod_cast h1
    rw [Nat.cast_mul] at h2
    change ((2 ^ H : Nat) : Rat) = 4 * ((2 ^ H0 : Nat) : Rat) at h2
    linarith only [h2, hDw0.1]
  have hZ_hi8 : wordMassK (Q :: K :: w0) = 2 + 4 * wordMassK w0 := by dsimp [wordMassK]; ring
  have hA0_pos : 0 < A0 := by
    by_contra hle; have hA0_0 : A0 = 0 := by omega
    have hZw0_0 := wordMassK_of_digitVal_zero hD0 hA0_0
    rw [<- hDw0.1] at hZw0_0
    have h_prod : wordScale u * wordMassK (Q :: K :: w0) + 2 * wordScale u =
      wordScale u * (4 * wordScale w0) := by
      rw [hZ_hi8, hZw0_0]; ring
    have h_pow_u : wordScale u * ((2 ^ H : Nat) : Rat) = wordScale u * (4 * wordScale w0) :=
      by rw [hPowH]
    linarith only [h_prod, h_pow_u, hHeight, hU11, hZ_max]
  have hLw0 : startsWithQKOrQQ (w0 ++ [K]) = true := startsWithQKOrQQ_of_digitVal_pos hD0 hA0_pos
  have hY_w0qqk : wordMass (w0 ++ [Q, Q, K]) = wordMass w0 + 7 * wordScale w0 := by
    rw [wordMass_append]; dsimp [wordMass]; ring
  have hZ_w0qqk : wordMassK (w0 ++ [Q, Q, K]) = wordMassK w0 + 4 * wordScale w0 := by
    rw [wordMassK_append]; dsimp [wordMassK]; ring
  have hScan_cond : (wordMass (w0 ++ [Q, Q, K]) + wordMassK (w0 ++ [Q, Q,
    K])) * 2 < ((m1 * 2 : Nat) : Rat) := by
    have h_yw0 : wordMass w0 = wordScale w0 - 1 := by linarith only [hDw0.1, hDw0.2.1]
    push_cast at hBud1 ⊢
    have hm1_nn : (0 : Rat) <= (m1 : Rat) := Nat.cast_nonneg m1
    have hm1_ub : ((m1 : Rat) * 2) * wordScale v1 <=
      ((m1 : Rat) * 2) * ((1 / 8) * wordScale u) := by
      nlinarith only [hm1_nn, h11_v1]
    have h_bud1_exp : (1 + (m1 : Rat) - 3) * wordScale v1 =
      (1 / 2) * (((m1 : Rat) * 2) * wordScale v1) - 2 * wordScale v1 := by ring
    have h_lhs_u : wordScale u * ((wordMass (w0 ++ [Q, Q, K]) + wordMassK (w0 ++ [Q, Q, K])) * 2) =
        6 * (wordScale u * (4 * wordScale w0)) +
          (1 / 2) * (wordScale u * wordMassK (Q :: K :: w0)) - 3 * wordScale u := by
      rw [hY_w0qqk, hZ_w0qqk, h_yw0, hZ_hi8]; ring
    have h_pow_u : wordScale u * ((2 ^ H : Nat) : Rat) = wordScale u * (4 * wordScale w0) :=
      by rw [hPowH]
    have h_rhs_u : ((m1 : Rat) * 2) * ((1 / 8) * wordScale u) =
      (1 / 8) * (wordScale u * ((m1 : Rat) * 2)) := by ring
    have h_lt_u : wordScale u * ((wordMass (w0 ++ [Q, Q, K]) + wordMassK (w0 ++ [Q, Q,
      K])) * 2) < wordScale u * ((m1 : Rat) * 2) := by
      linarith only [h_lhs_u, h_pow_u, hHeight, hZ_max, hSu, hBud1, h_bud1_exp, hm1_ub, h_rhs_u,
        hAB_1, hWu_max, hSv1]
    nlinarith only [hSu, h_lt_u]
  rcases exists_scan_of_mass_lt (w0 ++ [Q, Q, K]) m1 hScan_cond with ⟨b2, y, l2, hS2, _⟩
  rcases scan_qqk_inv hS2 w0 rfl with ⟨_, h11_y_fn, ⟨n_mid, hb2_eq⟩, ⟨y0, hy0⟩⟩
  subst hb2_eq
  have h11_y : wordScale (V :: y) <= (1 / 64) * ((2 ^ H : Nat) : Rat) := by
    have hy := h11_y_fn hLw0
    have h11_qqk : wordScale (w0 ++ [Q, Q, K]) = 8 * wordScale w0 := by
      rw [wordScale_append]
      norm_num [wordScale]
      ring
    have h_vy : wordScale (V :: y) = wordScale y * (1 / 2) := rfl
    linarith only [h_vy, hy, h11_qqk, hPowH]
  rcases bScan_high_digits hS2 hD0 with ⟨a2, b2_r, hB2, hY_vy, hAB_2, hBA_2⟩
  have hW_vy : wordWeightCanon (V :: y) <= (11 / 32) * wordMassK (Q :: K :: w0) := by
    have := (wordWeightCanon_bounds (V :: y)).2; linarith only [this, hY_vy]
  rcases bScan_append hB1 hB2 with ⟨a12, b12, hB12, ha12, hb12⟩
  have h11_v12 : wordScale (v1 ++ (V :: y)) <= 1 / 4 := by
    rw [wordScale_append]; have hS_vy := wordScale_pos (V :: y)
    have h_prod : wordScale v1 * wordScale (V :: y) <=
      ((1 / 8) * wordScale u) * ((1 / 64) * ((2 ^ H : Nat) : Rat)) := by
      nlinarith only [h11_v1, h11_y, hSv1, hS_vy]
    have h_eq : ((1 / 8) * wordScale u) * ((1 / 64) * ((2 ^ H : Nat) : Rat)) =
      (1 / 512) * (wordScale u * ((2 ^ H : Nat) : Rat)) := by ring
    linarith only [h_prod, h_eq, hHeight]
  have hSv12 := wordScale_pos (v1 ++ (V :: y))
  have hBud12 := bScan_budget_eq hB12
  have hZ_hi8_nn : 0 <= wordMassK (Q :: K :: w0) := (wordMass_nonneg (Q :: K :: w0)).2.1
  have hp1_ab : wordScale v1 * (a2 - b2_r) <=
    (7 / 64) * (wordScale u * wordMassK (Q :: K :: w0)) := by
    have hp : wordScale v1 * (a2 - b2_r) <=
      ((1 / 8) * wordScale u) * ((7 / 8) * wordMassK (Q :: K :: w0)) := by
      nlinarith only [h11_v1, hAB_2, hSv1, hZ_hi8_nn]
    have heq : ((1 / 8) * wordScale u) * ((7 / 8) * wordMassK (Q :: K :: w0)) =
      (7 / 64) * (wordScale u * wordMassK (Q :: K :: w0)) := by ring
    linarith only [hp, heq]
  have h_ab12 : a12 - b12 <=
    (64 / 11) * wordWeightCanon u + (7 / 64) * (wordScale u * wordMassK (Q :: K :: w0)) := by
    have h_diff : a12 - b12 = (a1 - b1) + wordScale v1 * (a2 - b2_r) := by rw [ha12, hb12]; ring
    linarith only [h_diff, hAB_1, hp1_ab]
  have hn_mid2 : 2 <= n_mid := by
    by_contra hlt; have : n_mid <= 1 := by omega
    have hq : (n_mid : Rat) <= 1 := by exact_mod_cast this
    push_cast at hBud12
    have h_ub : ((n_mid : Rat) * 4 - 3) * wordScale (v1 ++ (V :: y)) <= 1 := by
      nlinarith only [hq, h11_v12, hSv12]
    linarith only [hBud12, h_ub, h_ab12, hWu_max, hZ_max]
  rcases exists_bScan_piece3 hn_mid2 with ⟨m_end, d1_tok, a3, b3, hB3, h11_p3, hW_p3, hL_p3,
    hAB_3, hBA_3⟩
  rcases bScan_append hB12 hB3 with ⟨a, b, hB_all, ha_all, hb_all⟩
  let v := (v1 ++ (V :: y)) ++ [Q, d1_tok, V, V]
  have h11_v : wordScale v = wordScale (v1 ++ (V :: y)) := by
    dsimp [v]
    rw [wordScale_append, h11_p3]
    ring
  have hSv : 0 < wordScale v := wordScale_pos v
  have h11_v_le : wordScale v <= 1 / 4 := by linarith only [h11_v, h11_v12]
  have hW_v : wordWeightCanon v <=
    (66 / 19) * wordWeightCanon u + (11 / 256) * (wordScale u * wordMassK (Q :: K :: w0)) +
    15 / 16 := by
    dsimp [v]; rw [wordWeightCanon_append, wordWeightCanon_append]
    have hW_p3_nn := (wordWeightCanon_nonneg [Q, d1_tok, V, V]).2.2.2
    have hW_vy_nn := (wordWeightCanon_nonneg (V :: y)).2.2.2
    have hp1 : wordScale v1 * wordWeightCanon (V :: y) <=
      ((1 / 8) * wordScale u) * ((11 / 32) * wordMassK (Q :: K :: w0)) := by
      nlinarith only [h11_v1, hW_vy, hSv1, hW_vy_nn]
    have hp2 : wordScale (v1 ++ (V :: y)) * wordWeightCanon [Q, d1_tok, V,
      V] <= (1 / 4) * (15 / 4) := by
      nlinarith only [h11_v12, hW_p3, hSv12, hW_p3_nn]
    have hp1_eq : ((1 / 8) * wordScale u) * ((11 / 32) * wordMassK (Q :: K :: w0)) =
      (11 / 256) * (wordScale u * wordMassK (Q :: K :: w0)) := by ring
    linarith only [hW_v1, hp1, hp1_eq, hp2]
  have hAB : a - b <= 508 / 5 := by
    have hp2 : wordScale (v1 ++ (V :: y)) * (a3 - b3) <= (1 / 4) * 6 := by
      nlinarith only [h11_v12, hAB_3, hSv12]
    have h_diff : a - b = (a12 - b12) + wordScale (v1 ++ (V :: y)) * (a3 - b3) := by
      rw [ha_all, hb_all]; ring
    linarith only [h_diff, h_ab12, hp2, hWu_max, hZ_max]
  have hBA : b - a <= 8 := by
    have hp1 : wordScale v1 * (b2_r - a2) <= wordScale v1 := by nlinarith only [hSv1, hBA_2]
    have hp2 : wordScale (v1 ++ (V :: y)) * (b3 - a3) <= 0 := by nlinarith only [hSv12, hBA_3]
    have h_diff : b - a = (b1 - a1) + wordScale v1 * (b2_r - a2) + wordScale (v1 ++
      (V :: y)) * (b3 - a3) := by
      rw [ha_all, hb_all, ha12, hb12]; ring
    linarith only [h_diff, hBA_1, hp1, hp2, h11_v1, hU11, hWu_max]
  have hY_v_lt : wordMass v < ((2 ^ 17 : Nat) : Rat) := by
    have := (wordWeightCanon_bounds v).1; push_cast; linarith only [this, hW_v, hWu_max, hZ_max]
  rcases exists_heightShift_canon v 17 hY_v_lt with ⟨J, hHn⟩
  have hUnit := heightShift_sound v 17 J hHn
  have hJ10 : 10 <= J := by
    by_contra hlt; have hJ9 : J <= 9 := by omega
    have hpow9 : 2 ^ J <= 2 ^ 9 := Nat.pow_le_pow_right (by decide) hJ9
    have hpow9_q : ((2 ^ J : Nat) : Rat) <= ((2 ^ 9 : Nat) : Rat) := by exact_mod_cast hpow9
    push_cast at hpow9_q hUnit
    nlinarith only [hpow9_q, hUnit, h11_v_le, hSv]
  let H8' := J - 8
  have hH8'_2 : 2 <= H8' := by omega
  have hJ_eq : J = H8' + 8 := by omega
  have hUnit_H8' : wordScale v * ((2 ^ H8' : Nat) : Rat) = 512 := by
    have hpow : 2 ^ J = 2 ^ H8' * 256 := by rw [hJ_eq, Nat.pow_add]
    have hpow_q : ((2 ^ J : Nat) : Rat) = ((2 ^ H8' : Nat) : Rat) * 256 := by
      exact_mod_cast hpow
    have h_eq : wordScale v * (((2 ^ H8' : Nat) : Rat) * 256) =
      256 * (wordScale v * ((2 ^ H8' : Nat) : Rat)) := by ring
    have h17 : ((2 ^ 17 : Nat) : Rat) = 131072 := by norm_num
    rw [hpow_q, h_eq, h17] at hUnit
    linarith only [hUnit]
  have hBud := bScan_budget_eq hB_all
  have hBud_v : ((m_end : Rat) * 8) * wordScale v = 249041 + 3 * wordScale v - 2 * (a - b) := by
    have h1 : wordScale ((v1 ++ (V :: y)) ++ [Q, d1_tok, V, V]) = wordScale v := rfl
    rw [h1] at hBud
    push_cast at hBud
    have h2 : ((m_end : Rat) * 8 - 3) * wordScale v =
      ((m_end : Rat) * 8) * wordScale v - 3 * wordScale v := by ring
    linarith only [hBud, h2]
  let B := 1 + m_end * 4
  have hB_cast : (B : Rat) = 1 + (m_end : Rat) * 4 := by dsimp [B]; push_cast; rfl
  have hB_lo : 243 * 2 ^ H8' <= B := by
    have h243_cast : ((243 * 2 ^ H8' : Nat) : Rat) = 243 * ((2 ^ H8' : Nat) : Rat) := by
      rw [Nat.cast_mul]; rfl
    have h_b_v : ((B : Rat) - ((243 * 2 ^ H8' : Nat) : Rat)) * wordScale v =
        wordScale v +
          (1 / 2) * (((m_end : Rat) * 8) * wordScale v) - 243 * (wordScale v * ((2 ^ H8' : Nat) :
          Rat)) := by
      rw [hB_cast, h243_cast]; ring
    have h_pos_v : 0 < ((B : Rat) - ((243 * 2 ^ H8' : Nat) : Rat)) * wordScale v := by
      linarith only [h_b_v, hBud_v, hUnit_H8', hAB, hSv]
    have hq : ((243 * 2 ^ H8' : Nat) : Rat) <= (B : Rat) := by
      nlinarith only [h_pos_v, hSv]
    exact_mod_cast hq
  have hB_hi : B < 244 * 2 ^ H8' := by
    have h244_cast : ((244 * 2 ^ H8' : Nat) : Rat) = 244 * ((2 ^ H8' : Nat) : Rat) := by
      rw [Nat.cast_mul]; rfl
    have h_b_v : (((244 * 2 ^ H8' : Nat) : Rat) - (B : Rat)) * wordScale v =
        244 * (wordScale v * ((2 ^ H8' : Nat) : Rat)) - wordScale v - (1 / 2) * (((m_end : Rat) *
          8) * wordScale v) := by
      rw [hB_cast, h244_cast]; ring
    have h_pos_v : 0 < (((244 * 2 ^ H8' : Nat) : Rat) - (B : Rat)) * wordScale v := by
      linarith only [h_b_v, hBud_v, hUnit_H8', hBA, h11_v_le]
    have hq : (B : Rat) < ((244 * 2 ^ H8' : Nat) : Rat) := by
      nlinarith only [h_pos_v, hSv]
    exact_mod_cast hq
  let A8' := B - 243 * 2 ^ H8'
  have hA8'_lt : A8' < 2 ^ H8' := by omega
  rcases exists_digitVal_of_lt_pow H8' A8' hA8'_lt with ⟨hi8', hD_hi8'⟩
  have hA8'_mod : ∃ m', A8' = 1 + m' * 4 := by
    have hpow4 : 2 ^ H8' = 2 ^ (H8' - 2) * 4 := by
      have heq : H8' = (H8' - 2) + 2 := by omega
      conv_lhs => rw [heq, Nat.pow_add]
    refine ⟨m_end - 243 * 2 ^ (H8' - 2), ?_⟩
    dsimp [A8', B]; omega
  rcases hA8'_mod with ⟨m_a8, hm_a8⟩
  have hLow' : ∃ w, hi8' = Q :: K :: w := by
    rw [hm_a8] at hD_hi8'; exact digitVal_mod_four_one_prefix hD_hi8' hH8'_2
  have hD_ds' : DigitVal (1 + m_end * 4) J (hi8' ++ tail8Words) := by
    have hU := digitVal_append hD_hi8' digitVal_tail8Words
    have heqA : A8' + 243 * 2 ^ H8' = 1 + m_end * 4 := by dsimp [A8', B]; omega
    rw [heqA, <- hJ_eq] at hU; exact hU
  let u' := [V, V, K, V] ++ v
  have h11_u' : wordScale u' = (1 / 4) * wordScale v := by dsimp [u', wordScale]; ring
  have hW_u' : wordWeightCanon u' = (11 / 32) + (1 / 4) * wordWeightCanon v := by
    dsimp [u', wordWeightCanon]; ring
  have hDef' := digitVal_wordMassK_eq hD_hi8'
  have hA8'_q : (A8' : Rat) + 243 * ((2 ^ H8' : Nat) : Rat) = 1 + (m_end : Rat) * 4 := by
    have heq : A8' + 243 * 2 ^ H8' = 1 + m_end * 4 := by dsimp [A8', B]; omega
    exact_mod_cast heq
  have hZ_new : wordScale u' * wordMassK hi8' <= 1273 / 10 := by
    have h1 : wordMassK hi8' = ((2 ^ H8' : Nat) : Rat) - 1 - (A8' : Rat) := by linarith only [hDef']
    have h2 : (A8' : Rat) = 1 + (m_end : Rat) * 4 - 243 * ((2 ^ H8' : Nat) : Rat) := by
      linarith only [hA8'_q]
    have h_z_prod : wordScale u' * wordMassK hi8' =
        (244 / 4) * (wordScale v * ((2 ^ H8' : Nat) : Rat)) - (1 / 2) * wordScale v -
        (1 / 8) * (((m_end : Rat) * 8) * wordScale v) := by
      rw [h11_u', h1, h2]; ring
    linarith only [h_z_prod, hUnit_H8', hBud_v, hAB, hSv]
  have hHeight' : wordScale u' * ((2 ^ H8' : Nat) : Rat) = 128 := by
    have h_eq : wordScale u' * ((2 ^ H8' : Nat) : Rat) =
      (1 / 4) * (wordScale v * ((2 ^ H8' : Nat) : Rat)) := by
      rw [h11_u']; ring
    linarith only [h_eq, hUnit_H8']
  refine ⟨u' ++ (hi8' ++ tail8Words), ?_, ?_⟩
  · have h_in_eq : (u ++ ((Q :: K :: w0) ++ tail8Words)) ++ [K] =
        (u ++ ((Q :: K :: w0) ++ [Q, Q, K])) ++ [K, Q, Q, Q, Q, K] := by
      dsimp [tail8Words]; simp [List.append_assoc]
    have h_out_eq : u' ++ (hi8' ++ tail8Words) = [V, V, K, V] ++ v ++ (hi8' ++ tail8Words) := by
      simp [u']
    rw [h_out_eq]
    refine BStep.intro _ (m_end * 4) v a b J (hi8' ++ tail8Words) ?_ hD_ds'
    have hk_out_eq : (m_end * 4) * 2 = m_end * 8 := by ring
    rw [hk_out_eq, h_in_eq]; exact hB_all
  · refine BGood.intro H8' u' A8' hi8' hD_hi8' hHeight' (by linarith only [h11_u',
    h11_v_le]) ?_ ?_ hLow' (by linarith only [hW_u', hW_v, hWu_max, hZ_max]) hZ_new
    · refine ⟨[K, V] ++ v1 ++ (V :: y) ++ [Q, d1_tok, V], ?_⟩
      simp [u', v, List.append_assoc]
    · have heq_u' : u' = ([V, V, K, V] ++ (v1 ++ (V :: y))) ++ [Q, d1_tok, V, V] := by
        simp [u', v, List.append_assoc]
      rw [heq_u']; exact startsWithQKOrQQ_append_right _ _ hL_p3

theorem evalWords_default_of_digitVal_zero {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hZ :
    A = 0) :
    evalWords da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    change d0 +> evalWords u default = default
    rw [ih hA0, d0_append_default]
  | one _ => omega

theorem brIncs_of_digitVal_pos {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hPos : 0 < A) :
    BRIncs false ((A - 1) * 2) default (evalWords da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := BRIncs.short00 hIH
    rw [d0_append_default] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [evalWords]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change BRIncs false 0 default (d1 +> evalWords u default)
      rw [evalWords_default_of_digitVal_zero hDu rfl]
      have h0 := BRIncs.zero (default : HalfTape)
      have hd : d1 +> (default : HalfTape) = one +> default := by
        change (1 : Fin 2) >> (0 >> default) = 1 >> default
        rw [ListBlank.cons_zero_default]
      rw [hd]; exact h0
    | succ A =>
      have hA_pos : 0 < A + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A + 1 - 1) * 2 = A * 2 := by omega
      rw [heq_in] at hIH
      have hs := BRIncs.short10 hIH
      rw [d0_append_default] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2 = 4 + A * 4 := by omega
      dsimp [evalWords]
      rwa [heq]

theorem exists_brIncs_of_bStep {orig out : WordList} (hS : BStep orig out) :
    ∃ r, BRIncs false 128 (evalWords (prefix33Words ++ orig) default) r /\
      evalWords (prefix33Words ++ out) default = evalWords [V, V, Q, V] r := by
  rcases hS with ⟨n, v, a, b, J, ds, hI, hD⟩
  have hB : BRIncs false (n * 2) default (evalWords ds default) := by
    have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
    rw [heq]; exact brIncs_of_digitVal_pos hD (by omega)
  have hR_orig : BRIncs false 249044 (evalWords orig default) (evalWords (v ++ ds) default) := by
    have hR := brIncs_of_bScan hI hB
    simpa [evalWords_append, evalWords, d0_append_default] using! hR
  have hR_p33 := brIncs_prefix33Words hR_orig
  refine ⟨evalWords (out33Words ++ (v ++ ds)) default, ?_ , ?_⟩
  · rw [evalWords_append, evalWords_append]; exact hR_p33
  · have h_eq : prefix33Words ++ ([V, V, K, V] ++ v ++ ds) = [V, V, Q,
    V] ++ (out33Words ++ (v ++ ds)) := by
      simp [prefix33Words, out33Words]
    rw [h_eq, evalWords_append]

def decodeBinaryWords : Nat -> Nat -> Option WordList
  | 0, _ => none
  | _ + 1, 0 => none
  | _ + 1, 1 => some [Q]
  | fuel + 1, m + 2 =>
    match decodeBinaryWords fuel ((m + 2) / 2) with
    | none => none
    | some ws => some ((if (m + 2) % 2 == 0 then K else Q) :: ws)

theorem decodeBinaryWords_sound (fuel : Nat) :
    ∀ (m : Nat) (ws : WordList), decodeBinaryWords fuel m = some ws ->
      ∃ H, Binary m H (evalWords ws default) := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1, Binary.one⟩
    · dsimp [decodeBinaryWords] at h
      cases hrec : decodeBinaryWords fuel ((m + 2) / 2) with
      | none => rw [hrec] at h; contradiction
      | some ws' =>
        rw [hrec] at h
        injection h with h; subst h
        rcases ih ((m + 2) / 2) ws' hrec with ⟨H, hB⟩
        have hq : (m + 2) / 2 = 1 + ((m + 2) / 2 - 1) := by omega
        rw [hq] at hB
        rcases Nat.mod_two_eq_zero_or_one (m + 2) with hmod | hmod
        · have hcond : ((m + 2) % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [hcond]; dsimp [evalWords]
          refine ⟨1 + H, ?_⟩
          have heq : m + 2 = 2 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.zero hB
        · have hcond : ((m + 2) % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [hcond]; dsimp [evalWords]
          refine ⟨1 + H, ?_⟩
          have heq : m + 2 = 3 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.two hB

inductive Choice where
  | CT | CP0 | CP1 | CS00 | CS01 | CS10 | CS11
  | COC0 (r : Nat) | COC1 (r : Nat) | CEC (r : Nat)
  | CSP0 | CSP1 | CSC0 (r : Nat) | CSC1 (r : Nat)
deriving DecidableEq

open Choice

def choiceInMode : Choice -> Bool
  | CSP0 | CSP1 | CSC0 _ | CSC1 _ => true
  | _ => false

def choiceOutMode : Choice -> Bool
  | COC0 _ | COC1 _ | CEC _ | CSC0 _ | CSC1 _ => true
  | _ => false

def choiceNextParam : Choice -> Nat -> Nat
  | CT, k => k - 2
  | CP0, k | CP1, k | CSP0, k | CSP1, k => k - 1
  | CS00, k | CS01, k => (k - 2) / 4
  | CS10, k | CS11, k => (k - 4) / 4
  | COC0 _, k | CSC0 _, k => (k - 3) / 4
  | COC1 _, k | CSC1 _, k => (k - 5) / 4
  | CEC _, k => (k - 6) / 2

def choiceInMult : Choice -> Nat -> Nat
  | CT, n => 2 + n
  | CP0, n | CP1, n | CSP0, n | CSP1, n => 1 + n
  | CS00, n | CS01, n => 2 + n * 4
  | CS10, n | CS11, n => 4 + n * 4
  | COC0 _, n | CSC0 _, n => 3 + n * 4
  | COC1 _, n | CSC1 _, n => 5 + n * 4
  | CEC _, n => 6 + n * 2

def choiceOutMult : Choice -> Nat -> Nat
  | CT, n | CP1, n | CS01, n | CS11, n | CSP1, n => 1 + n * 2
  | CP0, n | CS00, n | CS10, n | CSP0, n => n * 2
  | COC0 r, n | COC1 r, n => 1 + n * 2 ^ (1 + r)
  | CEC r, n => 1 + (1 + n * 2) * 2 ^ (1 + r)
  | CSC0 r, n | CSC1 r, n => 1 + n * 2 ^ (2 + r)

def choiceInWords : Choice -> WordList
  | CT => [V]
  | CP0 => [Q, K]
  | CP1 => [Q, Q]
  | CS00 | CS10 | CSP0 => [K]
  | CS01 | CS11 | CSP1 => [Q]
  | COC0 r | COC1 r => prependQK r [V]
  | CEC r | CSC0 r | CSC1 r => K :: prependQK r [V]

def choiceOutWords : Choice -> WordList
  | CT | CP0 | CP1 | CSP0 | CSP1 => [V]
  | CS00 | CS01 => [K]
  | CS10 | CS11 => [Q]
  | COC0 r => K :: List.replicate r V
  | COC1 r => Q :: List.replicate r V
  | CEC r => List.replicate (1 + r) V
  | CSC0 r => K :: List.replicate (1 + r) V
  | CSC1 r => Q :: List.replicate (1 + r) V

def evalChoiceList : List Choice -> Bool -> Nat -> WordList -> Option WordList
  | [], s, k, u =>
    forceNat (k / 2) (fun n =>
    if s == false then
      if k == n * 2 then
        if u.all isWordK then decodeBinaryWords 600 (1 + n) else none
      else none
    else none)
  | ch :: cs, s, k, u =>
    forceNat (choiceNextParam ch k) (fun n =>
    if s == choiceInMode ch then
      if k == choiceInMult ch n then
        match stripWordPrefix (choiceInWords ch) u with
        | none => none
        | some w =>
          forceNat (choiceOutMult ch n) (fun k' =>
          match evalChoiceList cs (choiceOutMode ch) k' w with
          | none => none
          | some x => some (choiceOutWords ch ++ x))
      else none
    else none)

theorem evalChoiceList_sound (cs : List Choice) :
    ∀ (s : Bool) (k : Nat) (u v : WordList), evalChoiceList cs s k u = some v ->
      BRIncs s k (evalWords u default) (evalWords v default) := by
  induction cs with
  | nil =>
    intro s k u v hE
    dsimp [evalChoiceList, forceNat_eq] at hE
    cases hs : (s == false) with
    | false => rw [hs] at hE; contradiction
    | true =>
      rw [hs] at hE
      have rfl_s : s = false := beq_iff_eq.mp hs
      subst rfl_s
      cases hk : (k == (k / 2) * 2) with
      | false => rw [hk] at hE; contradiction
      | true =>
        rw [hk] at hE
        have rfl_k : k = (k / 2) * 2 := beq_iff_eq.mp hk
        cases hu : u.all isWordK with
        | false => rw [hu] at hE; contradiction
        | true =>
          rw [hu] at hE
          dsimp at hE
          rw [evalWords_default_of_all_K u hu]
          rcases decodeBinaryWords_sound 600 (1 + k / 2) v hE with ⟨H, hB⟩
          have hR := brIncs_of_binary hB
          have heq : ((1 + k / 2) - 1) * 2 = k := by omega
          rwa [heq] at hR
  | cons ch cs ih =>
    intro s k u v hE
    dsimp [evalChoiceList, forceNat_eq] at hE
    cases hs : (s == choiceInMode ch) with
    | false => rw [hs] at hE; contradiction
    | true =>
      rw [hs] at hE
      have rfl_s : s = choiceInMode ch := beq_iff_eq.mp hs
      subst rfl_s
      cases hk : (k == choiceInMult ch (choiceNextParam ch k)) with
      | false => rw [hk] at hE; contradiction
      | true =>
        rw [hk] at hE
        dsimp at hE
        have rfl_k : k = choiceInMult ch (choiceNextParam ch k) := beq_iff_eq.mp hk
        cases hU : stripWordPrefix (choiceInWords ch) u with
        | none => rw [hU] at hE; contradiction
        | some w =>
          rw [hU] at hE
          dsimp at hE
          cases hC : evalChoiceList cs (choiceOutMode ch) (choiceOutMult ch (choiceNextParam ch k))
            w with
          | none => rw [hC] at hE; contradiction
          | some x =>
            rw [hC] at hE
            injection hE with hE; subst hE
            have rfl_u := stripWordPrefix_sound (choiceInWords ch) u w hU
            subst rfl_u
            have hIH := ih (choiceOutMode ch) (choiceOutMult ch (choiceNextParam ch k)) w x hC
            rw [rfl_k]
            cases ch with
            | CT => exact BRIncs.T hIH
            | CP0 => exact BRIncs.pair0 hIH
            | CP1 => exact BRIncs.pair1 hIH
            | CS00 => exact BRIncs.short00 hIH
            | CS01 => exact BRIncs.short01 hIH
            | CS10 => exact BRIncs.short10 hIH
            | CS11 => exact BRIncs.short11 hIH
            | COC0 r =>
              dsimp [choiceInWords, choiceOutWords, choiceInMode, choiceOutMode, choiceInMult,
                choiceOutMult] at hIH ⊢
              rw [evalWords_append (prependQK r [V]) w]; dsimp [evalWords];
                rw [evalWords_append (List.replicate r V) x]
              exact BRIncs.odd_chain0 r hIH
            | COC1 r =>
              dsimp [choiceInWords, choiceOutWords, choiceInMode, choiceOutMode, choiceInMult,
                choiceOutMult] at hIH ⊢
              rw [evalWords_append (prependQK r [V]) w]; dsimp [evalWords];
                rw [evalWords_append (List.replicate r V) x]
              exact BRIncs.odd_chain1 r hIH
            | CEC r =>
              dsimp [choiceInWords, choiceOutWords, choiceInMode, choiceOutMode, choiceInMult,
                choiceOutMult] at hIH ⊢
              dsimp [evalWords];
                rw [evalWords_append (prependQK r [V]) w,
                evalWords_append (List.replicate (1 + r) V) x]
              exact BRIncs.even_chain r hIH
            | CSP0 => exact BRIncs.shift_pair0 hIH
            | CSP1 => exact BRIncs.shift_pair1 hIH
            | CSC0 r =>
              dsimp [choiceInWords, choiceOutWords, choiceInMode, choiceOutMode, choiceInMult,
                choiceOutMult] at hIH ⊢
              dsimp [evalWords];
                rw [evalWords_append (prependQK r [V]) w,
                evalWords_append (List.replicate (1 + r) V) x]
              exact BRIncs.shift_chain0 r hIH
            | CSC1 r =>
              dsimp [choiceInWords, choiceOutWords, choiceInMode, choiceOutMode, choiceInMult,
                choiceOutMult] at hIH ⊢
              dsimp [evalWords];
                rw [evalWords_append (prependQK r [V]) w,
                evalWords_append (List.replicate (1 + r) V) x]
              exact BRIncs.shift_chain1 r hIH

def evalCanonStep (cs : List Choice) (u : WordList) : Option WordList :=
  match evalChoiceList cs false 128 (u ++ [K]) with
  | some v => some ([V, V, Q, V] ++ v)
  | none => none

theorem evalCanonStep_sound (cs : List Choice) (u v : WordList) (h : evalCanonStep cs u = some v) :
    ∃ r, BRIncs false 128 (evalWords u default) r /\
      evalWords v default = evalWords [V, V, Q, V] r := by
  dsimp [evalCanonStep] at h
  cases hE : evalChoiceList cs false 128 (u ++ [K]) with
  | none => rw [hE] at h; contradiction
  | some w =>
    rw [hE] at h
    injection h with h; subst h
    refine ⟨evalWords w default, ?_, rfl⟩
    have hR := evalChoiceList_sound cs false 128 (u ++ [K]) w hE
    simpa [evalWords_append, evalWords, d0_append_default] using! hR

inductive CanonRounds : HalfTape -> HalfTape -> Prop where
  | refl (r : HalfTape) : CanonRounds r r
  | next {r s t0 : HalfTape} :
      BRIncs false 128 r s -> CanonRounds (evalWords [V, V, Q, V] s) t0 -> CanonRounds r t0

def evalCanonRounds : List (List Choice) -> WordList -> Option WordList
  | [], u => some u
  | c :: cs, u =>
    match evalCanonStep c u with
    | none => none
    | some v => evalCanonRounds cs v

theorem evalCanonRounds_sound (cs : List (List Choice)) :
    ∀ (u v : WordList), evalCanonRounds cs u = some v ->
      CanonRounds (evalWords u default) (evalWords v default) := by
  induction cs with
  | nil =>
    intro u v h
    injection h with h; subst h
    exact CanonRounds.refl _
  | cons c cs ih =>
    intro u v h
    dsimp [evalCanonRounds] at h
    cases hW : evalCanonStep c u with
    | none => rw [hW] at h; contradiction
    | some w =>
      rw [hW] at h
      rcases evalCanonStep_sound c u w hW with ⟨r, hR, hEq⟩
      refine CanonRounds.next hR ?_
      rw [<- hEq]
      exact ih w v h

def vWordCount : WordList -> Nat
  | [] => 0
  | V :: u => 1 + vWordCount u
  | K :: u => vWordCount u
  | Q :: u => vWordCount u

def pairWordCount : WordList -> Nat
  | [] => 0
  | V :: u => pairWordCount u
  | K :: u => 1 + pairWordCount u
  | Q :: u => 1 + pairWordCount u

theorem wordScale_mul_pow_vWordCount (u : WordList) :
    wordScale u * ((2 ^ vWordCount u : Nat) : Rat) = ((2 ^ pairWordCount u : Nat) : Rat) := by
  induction u with
  | nil => simp [wordScale, vWordCount, pairWordCount]
  | cons w u ih =>
    cases w with
    | V =>
      dsimp [wordScale, vWordCount, pairWordCount]
      rw [pow_two_one_add (vWordCount u), Nat.cast_add]
      have h_eq : wordScale u * (1 / 2) * (((2 ^ vWordCount u : Nat) : Rat) +
        ((2 ^ vWordCount u : Nat) : Rat)) =
          wordScale u * ((2 ^ vWordCount u : Nat) : Rat) := by ring
      linarith only [h_eq, ih]
    | K =>
      dsimp [wordScale, vWordCount, pairWordCount]
      rw [pow_two_one_add (pairWordCount u), Nat.cast_add]
      have h_eq : wordScale u * 2 * ((2 ^ vWordCount u : Nat) : Rat) =
          2 * (wordScale u * ((2 ^ vWordCount u : Nat) : Rat)) := by ring
      linarith only [h_eq, ih]
    | Q =>
      dsimp [wordScale, vWordCount, pairWordCount]
      rw [pow_two_one_add (pairWordCount u), Nat.cast_add]
      have h_eq : wordScale u * 2 * ((2 ^ vWordCount u : Nat) : Rat) =
          2 * (wordScale u * ((2 ^ vWordCount u : Nat) : Rat)) := by ring
      linarith only [h_eq, ih]

def scaledWeightUpper : WordList -> Nat
  | [] => 0
  | V :: u => (scaledWeightUpper u + 1) / 2
  | K :: u => 90112 + 2 * scaledWeightUpper u
  | Q :: u => 65536 + 2 * scaledWeightUpper u

theorem scaledWeightUpper_ge (u : WordList) :
    65536 * wordWeightCanon u <= ((scaledWeightUpper u : Nat) : Rat) := by
  induction u with
  | nil => simp [wordWeightCanon, loc_z0W, scaledWeightUpper]
  | cons w u ih =>
    cases w with
    | V =>
      dsimp [wordWeightCanon, loc_z0W, scaledWeightUpper]
      have hdiv : scaledWeightUpper u <= 2 * ((scaledWeightUpper u + 1) / 2) := by omega
      have hdiv_q : ((scaledWeightUpper u : Nat) : Rat) <=
        ((2 * ((scaledWeightUpper u + 1) / 2) : Nat) : Rat) := by exact_mod_cast hdiv
      push_cast at hdiv_q
      linarith only [ih, hdiv_q]
    | K =>
      dsimp [wordWeightCanon, loc_z0W, scaledWeightUpper]; push_cast; linarith only [ih]
    | Q =>
      dsimp [wordWeightCanon, loc_z0W, scaledWeightUpper]; push_cast; linarith only [ih]

def natOfDigitWords : WordList -> Nat
  | [] => 0
  | V :: u => natOfDigitWords u
  | K :: u => 1 + 2 * natOfDigitWords u
  | Q :: u => 2 * natOfDigitWords u

theorem wordMassK_eq_natOfDigitWords (u : WordList) (h : u.all isDigitWord = true) :
    wordMassK u = ((natOfDigitWords u : Nat) : Rat) := by
  induction u with
  | nil => simp [wordMassK, natOfDigitWords]
  | cons w u ih =>
    cases w with
    | V => contradiction
    | K =>
      dsimp [List.all, isDigitWord] at h
      dsimp [wordMassK, natOfDigitWords]; rw [ih h]; push_cast; ring
    | Q =>
      dsimp [List.all, isDigitWord] at h
      dsimp [wordMassK, natOfDigitWords]; rw [ih h]; push_cast; ring

def endsWithV : WordList -> Bool
  | [] => false
  | [x] => x == V
  | _ :: y :: ys => endsWithV (y :: ys)

theorem endsWithV_eq (u : WordList) (h : endsWithV u = true) : ∃ w, u = w ++ [V] := by
  induction u with
  | nil => contradiction
  | cons x u ih =>
    cases u with
    | nil =>
      cases x <;> try contradiction
      exact ⟨[], rfl⟩
    | cons y ys =>
      change endsWithV (y :: ys) = true at h
      rcases ih h with ⟨w, hw⟩
      exact ⟨x :: w, by rw [hw]; rfl⟩

def startsWithVVAndEndsWithV : WordList -> Bool
  | V :: V :: u => endsWithV u
  | _ => false

theorem startsWithVVAndEndsWithV_eq (u : WordList) (h : startsWithVVAndEndsWithV u = true) : ∃ w,
    u = V :: V :: (w ++ [V]) := by
  rcases u with _ | ⟨_ | _ | _, _ | ⟨_ | _ | _, u'⟩⟩ <;> try contradiction
  change endsWithV u' = true at h
  rcases endsWithV_eq u' h with ⟨w, hw⟩
  exact ⟨w, by rw [hw]⟩

def startsWithQK : WordList -> Bool
  | Q :: K :: _ => true
  | _ => false

theorem startsWithQK_eq (u v : WordList) (h : startsWithQK u = true) : ∃ w,
    u ++ v = Q :: K :: w := by
  rcases u with _ | ⟨_ | _ | _, _ | ⟨_ | _ | _, u'⟩⟩ <;> try contradiction
  exact ⟨u' ++ v, rfl⟩

theorem bGood_of_check (u hi_low hi_top : WordList)
    (hD_low : hi_low.all isDigitWord = true)
    (hD_top : hi_top.all isDigitWord = true)
    (hTopLen : hi_top.length = 16)
    (hPow : pairWordCount u + (hi_low.length + 16) = 7 + vWordCount u)
    (hU11_nat : 4 + pairWordCount u <= vWordCount u)
    (hEnd : startsWithVVAndEndsWithV u = true)
    (hLu : startsWithQKOrQQ u = true)
    (hLo : startsWithQK hi_low = true)
    (hW_nat : scaledWeightUpper u <= 969932)
    (hZ_nat : 10 * (1 + natOfDigitWords hi_top) <= 651776) :
    BGood (u ++ ((hi_low ++ hi_top) ++ tail8Words)) := by
  let hi8 := hi_low ++ hi_top
  have hD : hi8.all isDigitWord = true := by dsimp [hi8]; rw [List.all_append, hD_low, hD_top]; rfl
  rcases exists_digitVal_of_all_isDigitWord hi8 hD with ⟨A, hI⟩
  have hLen : hi8.length = hi_low.length + 16 := by dsimp [hi8]; rw [List.length_append, hTopLen]
  have h11_u := wordScale_mul_pow_vWordCount u
  have hPow2 : 2 ^ pairWordCount u * 2 ^ hi8.length = 128 * 2 ^ vWordCount u := by
    rw [<- Nat.pow_add, hLen, hPow, Nat.pow_add]
  have hPow2_q : ((2 ^ pairWordCount u : Nat) : Rat) * ((2 ^ hi8.length : Nat) : Rat) =
    128 * ((2 ^ vWordCount u : Nat) : Rat) := by
    exact_mod_cast hPow2
  have hPos : 0 < ((2 ^ vWordCount u : Nat) : Rat) := by exact_mod_cast pow_two_pos (vWordCount u)
  have hHeight : wordScale u * ((2 ^ hi8.length : Nat) : Rat) = 128 := by
    nlinarith only [h11_u, hPow2_q, hPos]
  have hLe2 : 16 * 2 ^ pairWordCount u <= 2 ^ vWordCount u := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hU11_nat
    rw [Nat.pow_add] at this; omega
  have hLe2_q : 16 * ((2 ^ pairWordCount u : Nat) : Rat) <= ((2 ^ vWordCount u : Nat) : Rat) := by
    exact_mod_cast hLe2
  have hU11 : wordScale u <= 1 / 16 := by
    nlinarith only [h11_u, hLe2_q, hPos]
  have hW_q : ((scaledWeightUpper u : Nat) : Rat) <= 969932 := by exact_mod_cast hW_nat
  have hW_ge := scaledWeightUpper_ge u
  have hW : wordWeightCanon u <= 74 / 5 := by linarith only [hW_q, hW_ge]
  rcases exists_digitVal_of_all_isDigitWord hi_low hD_low with ⟨A_low, hI_low⟩
  rcases exists_digitVal_of_all_isDigitWord hi_top hD_top with ⟨A_top, hI_top⟩
  have hDw_low := digitVal_scale_and_mass hI_low
  have hDw_top := digitVal_scale_and_mass hI_top
  have hZ_low_le : wordMassK hi_low <= wordScale hi_low := by
    have h1 := wordMass_eq_add hi_low
    have h2 : 0 <= wordMassQ hi_low := by rw [hDw_low.2.2]; exact Nat.cast_nonneg A_low
    linarith only [h1, h2, hDw_low.1, hDw_low.2.1]
  have h11_top : wordScale hi_top = 65536 := by
    have h1 := hDw_top.1; rw [hTopLen] at h1
    have h2 : ((2 ^ 16 : Nat) : Rat) = 65536 := by norm_num
    linarith only [h1, h2]
  have h11_hi8 : wordScale hi8 = ((2 ^ hi8.length : Nat) : Rat) := (digitVal_scale_and_mass hI).1
  have h11_split : wordScale hi8 = wordScale hi_low * wordScale hi_top := by
    dsimp [hi8]
    exact wordScale_append hi_low hi_top
  have h_u_low : wordScale u * wordScale hi_low = 1 / 512 := by
    have h_eq : wordScale u * ((2 ^ hi8.length : Nat) : Rat) =
      65536 * (wordScale u * wordScale hi_low) := by
      rw [<- h11_hi8, h11_split, h11_top]; ring
    linarith only [hHeight, h_eq]
  have hZ_split : wordMassK hi8 = wordMassK hi_low + wordScale hi_low * wordMassK hi_top := by
    dsimp [hi8]; exact wordMassK_append hi_low hi_top
  have hZ_top_eq := wordMassK_eq_natOfDigitWords hi_top hD_top
  have hZ_top_q : 10 * (1 + ((natOfDigitWords hi_top : Nat) : Rat)) <= 651776 := by
    exact_mod_cast hZ_nat
  have hSu := wordScale_pos u
  have hZ : wordScale u * wordMassK hi8 <= 1273 / 10 := by
    have h_uz_split : wordScale u * wordMassK hi8 =
      wordScale u * wordMassK hi_low + (wordScale u * wordScale hi_low) * wordMassK hi_top := by
      rw [hZ_split]; ring
    have h_uz_low : wordScale u * wordMassK hi_low <= wordScale u * wordScale hi_low := by
      nlinarith only [hSu, hZ_low_le]
    have h_uz_top : (wordScale u * wordScale hi_low) * wordMassK hi_top =
      (1 / 512) * ((natOfDigitWords hi_top : Nat) : Rat) := by
      rw [h_u_low, hZ_top_eq]
    linarith only [h_uz_split, h_uz_low, h_u_low, h_uz_top, hZ_top_q]
  exact BGood.intro hi8.length u A hi8 hI hHeight hU11
    (startsWithVVAndEndsWithV_eq u hEnd) hLu (startsWithQK_eq hi_low hi_top hLo) hW hZ

theorem seg_ch_odd_d1 (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [list_pow_one_add_canon, List.cons_append,
    List.nil_append] using! seg_append_calls seg_ch_d1 (seg_ch_double_pow seg_ch_two_d0 n)

def evalChPow : Nat -> WordList -> Option WordList
  | 0, u => some u
  | _, [] => none
  | k + 1, V :: u =>
    match evalChPow ((k + 1) * 2) u with
    | some v => some (V :: v)
    | none => none
  | k + 1, K :: u =>
    let m := (k + 1) / 2
    if k + 1 == m * 2 then
      match evalChPow m u with
      | some v => some (K :: v)
      | none => none
    else
      match evalChPow m u with
      | some v => some (Q :: v)
      | none => none
  | k + 1, Q :: u =>
    let m := (k + 1) / 2
    if k + 1 == m * 2 then
      match evalChPow m u with
      | some v => some (Q :: v)
      | none => none
    else
      match evalChPow (1 + m) u with
      | some v => some (K :: v)
      | none => none

theorem evalChPow_sound (u : WordList) :
    ∀ (k : Nat) (v : WordList), evalChPow k u = some v ->
      Side ([Call.ch] ^ k) (evalWords u default) (evalWords v default) := by
  induction u with
  | nil =>
    intro k v h
    cases k with
    | zero =>
      injection h with h; subst h
      exact Side.nil _
    | succ k => contradiction
  | cons w u ih =>
    intro k v h
    cases k with
    | zero =>
      injection h with h; subst h
      exact Side.nil _
    | succ k =>
      cases w with
      | V =>
        dsimp [evalChPow] at h
        cases hE : evalChPow ((k + 1) * 2) u with
        | none => rw [hE] at h; contradiction
        | some v' =>
          rw [hE] at h
          injection h with h; subst h
          exact side_of_seg (seg_ch_pow_t (k + 1)) (ih _ _ hE)
      | K =>
        dsimp [evalChPow] at h
        cases hk : (k + 1 == ((k + 1) / 2) * 2) with
        | true =>
          rw [hk] at h; dsimp at h
          cases hE : evalChPow ((k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have heq : k + 1 = ((k + 1) / 2) * 2 := beq_iff_eq.mp hk
            rw [heq]
            exact side_of_seg (seg_ch_even_d0 ((k + 1) / 2)) (ih _ _ hE)
        | false =>
          rw [hk] at h; dsimp at h
          cases hE : evalChPow ((k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have hne : k + 1 ≠ ((k + 1) / 2) * 2 := by
              intro hc; have := beq_iff_eq.mpr hc; rw [this] at hk; contradiction
            have heq : k + 1 = 1 + ((k + 1) / 2) * 2 := by omega
            rw [heq]
            exact side_of_seg (seg_ch_odd_d0 ((k + 1) / 2)) (ih _ _ hE)
      | Q =>
        dsimp [evalChPow] at h
        cases hk : (k + 1 == ((k + 1) / 2) * 2) with
        | true =>
          rw [hk] at h; dsimp at h
          cases hE : evalChPow ((k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have heq : k + 1 = ((k + 1) / 2) * 2 := beq_iff_eq.mp hk
            rw [heq]
            exact side_of_seg (seg_ch_even_d1 ((k + 1) / 2)) (ih _ _ hE)
        | false =>
          rw [hk] at h; dsimp at h
          cases hE : evalChPow (1 + (k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have hne : k + 1 ≠ ((k + 1) / 2) * 2 := by
              intro hc; have := beq_iff_eq.mpr hc; rw [this] at hk; contradiction
            have heq : k + 1 = 1 + ((k + 1) / 2) * 2 := by omega
            rw [heq]
            exact side_of_seg (seg_ch_odd_d1 ((k + 1) / 2)) (ih _ _ hE)

abbrev w_pre3_rest : BitWord := t ++ t ++ (t ++ d1)

abbrev w_pre3 : BitWord := w_word ++ w_pre3_rest

abbrev w_pre5_rest : BitWord := w_pre3_rest ++ t ++ (t ++ d0)

abbrev w_pre5 : BitWord := w_word ++ w_pre5_rest

abbrev w_pre_rest : BitWord := w_pre5_rest ++ t ++ (t ++ d0)

abbrev w_pre : BitWord := w_word ++ w_pre_rest

theorem seg_word_pre3 :
    Seg [.ch, .cj, .ch] ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 2) w_pre3_rest
      (t ++ t ++ (d0 ++ t)) := by
  unfold w_pre3_rest
  exact seg_comp_words (seg_comp_words seg_word_s1 seg_word_s2) seg_word_s3

theorem seg_word_pre5 :
    Seg [.ch, .cj, .ch] ([.ch] ^ 8 ++ [.cj, .ch]) w_pre5_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)) := by
  unfold w_pre5_rest
  exact seg_comp_words (seg_comp_words seg_word_pre3 seg_word_s4) seg_word_s5

theorem seg_word_pre :
    Seg [.ch, .cj, .ch] ([.ch] ^ 16) w_pre_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))) := by
  unfold w_pre_rest
  exact seg_comp_words (seg_comp_words seg_word_pre5 seg_word_s6) seg_word_s7

theorem stepPlus_word_pre3_full {r r' : HalfTape} (h : Side ([.ch] ^ 4 ++ [.cp] ++
    [.ch] ^ 2) r r') :
    (cfgLeft lh (w_pre3 +> r)) [canon_tm]⊢⁺ (cfgLeft lh (w_pre5 +> (t +> r'))) := by
  have h_side := seg_word_pre3 r r' h
  have h_turn := stepPlus_word_turn h_side
  have h_in : w_word +> (w_pre3_rest +> r) = w_pre3 +> r := by
    unfold w_pre3 w_pre3_rest; simp only [List.append_assoc, append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t)) +> r') =
      w_pre5 +> (t +> r') := by
    unfold w_pre5 w_pre5_rest w_pre3_rest w_word t d0 d1
    simp only [List.cons_append, List.nil_append, append_cons, append_nil]
  rwa [h_in, h_out] at h_turn

theorem stepPlus_word_pre5_full {r r' : HalfTape} (h : Side ([.ch] ^ 8 ++ [.cj, .ch]) r r') :
    (cfgLeft lh (w_pre5 +> r)) [canon_tm]⊢⁺ (cfgLeft lh (w_pre +> (t +> r'))) := by
  have h_side := seg_word_pre5 r r' h
  have h_turn := stepPlus_word_turn h_side
  have h_in : w_word +> (w_pre5_rest +> r) = w_pre5 +> r := by
    unfold w_pre5 w_pre5_rest; simp only [List.append_assoc, append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)) +> r') =
      w_pre +> (t +> r') := by
    unfold w_pre w_pre_rest w_pre5_rest w_pre3_rest w_word t d0 d1
    simp only [List.cons_append, List.nil_append, append_cons, append_nil]
  rwa [h_in, h_out] at h_turn

theorem stepPlus_word_pre_full {r r' : HalfTape} (h : Side ([.ch] ^ 16) r r') :
    (cfgLeft lh (w_pre +> r)) [canon_tm]⊢⁺ (cfgCanon r') := by
  have h_side := seg_word_pre r r' h
  have h_turn := stepPlus_word_turn h_side
  have h_in : w_word +> (w_pre_rest +> r) = w_pre +> r := by
    unfold w_pre w_pre_rest; simp only [List.append_assoc, append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))) +> r') =
      w_base +> r' := by
    unfold w_base w_word w_rest t d0 d1 one
    simp only [List.cons_append, List.nil_append, append_cons, append_nil]
  unfold cfgCanon
  rwa [h_in, h_out] at h_turn

theorem seg_ch_16_to_31 :
    Seg ([.ch] ^ 16) ([.cj] ++ [.ch] ^ 31) (d0 ++ t ++ (t ++ one)) (d0 ++ t ++ t) := by
  have h1 : Seg ([.ch] ^ 16) ([.ch] ^ 8) d0 d0 := seg_ch_even_d0 8
  have h2 : Seg ([.ch] ^ 8) ([.ch] ^ 16) t t := seg_ch_pow_t 8
  have h3 : Seg ([.ch] ^ 16) ([.cj] ++ [.ch] ^ 31) (t ++ one) t := by
    have ha := seg_append_calls seg_ch_t_one (seg_ch_pow_t 15)
    have heq_in : ([Call.ch] : List Call) ++ [Call.ch] ^ 15 = [Call.ch] ^ 16 := rfl
    have heq_out : ([Call.cj,
      Call.ch] : List Call) ++ [Call.ch] ^ (15 * 2) = [Call.cj] ++ [Call.ch] ^ 31 := rfl
    rwa [heq_in, heq_out] at ha
  exact seg_comp_words (seg_comp_words h1 h2) h3

abbrev canonBMultiStepFast (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep canon_tm n c

theorem canonBMultiStepFast_sound {c1 c2 : CCfg} {n : Nat} (hn : 0 <
    n) (h : canonBMultiStepFast c1 n = some c2) :
    (c_to_cfg c1) [canon_tm]⊢⁺ (c_to_cfg c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

theorem stepPlus_of_bStep {orig out : WordList} (hS : BStep orig out) :
    (cfgCanon (evalWords (prefix33Words ++
      orig) default)) [canon_tm]⊢⁺ (cfgCanon (evalWords (prefix33Words ++ out) default)) := by
  rcases exists_brIncs_of_bStep hS with ⟨r, hI, hEq⟩
  rw [hEq]
  exact stepPlus_of_brIncs_128 hI

theorem stepStar_of_canonRounds {r r' : HalfTape} (h : CanonRounds r r') :
    (cfgCanon r) [canon_tm]⊢* (cfgCanon r') := by
  induction h with
  | refl _ => exact ⟨0, rfl⟩
  | next hR _ ih =>
    rcases stepPlus_of_brIncs_128 hR with ⟨n, _, hn⟩
    rcases ih with ⟨m, hm⟩
    exact ⟨n + m, multiStep_trans_canon canon_tm _ _ _ n m hn hm⟩

theorem multiStep_add_Intermediate {M : Machine (Fin 2) (Fin 6)} {c c' : Cfg (Fin 2) (Fin 6)} {j d
    : Nat}
    (h : multiStep M c (j + d) = some c') :
    (multiStep M c j).isSome := by
  rw [BusyBeaver.multiStep_add] at h
  cases h_j : multiStep M c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl


end BusyBeaver.WordCanonBR
