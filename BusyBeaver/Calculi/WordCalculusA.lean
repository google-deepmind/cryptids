/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Word Calculus Engine A (`BusyBeaver.Calculi.WordCalculusA`)

Formal word-rewriting calculus for structured tape transformations,
providing verified macro-step reductions and tile segment chains for family A.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordCalculus
set_option quotPrecheck false
set_option maxRecDepth 4000000

variable {α β γ : Type*}
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
local notation "t" => ([1, 1, 0, 0] : BitWord)
local notation "d0" => ([0, 0] : BitWord)
local notation "d1" => ([1, 0] : BitWord)
theorem pow_two_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega
theorem pow_two_one_add (n : Nat) : 2 ^ (1 + n) = 2 ^ n + 2 ^ n := by
  rw [Nat.add_comm 1 n, Nat.pow_succ]; omega
theorem even_or_odd_mul_two (n : Nat) : (∃ a, n = a * 2) \/ (∃ a, n = 1 + a * 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; exact ⟨n / 2, by omega⟩
  · right; exact ⟨n / 2, by omega⟩
inductive Word where
  | V
  | K
  | Q
deriving DecidableEq
open Word
local notation "WordList" => List Word
inductive WordPrefix : Bool -> WordList -> Prop where
  | nil (e : Bool) : WordPrefix e []
  | T (e : Bool) {u : WordList} : WordPrefix true u -> WordPrefix e (V :: u)
  | short0 {u : WordList} : WordPrefix true u -> WordPrefix true (K :: u)
  | short1 {u : WordList} : WordPrefix false u -> WordPrefix true (Q :: u)
  | pair0 (e : Bool) {u : WordList} : WordPrefix true u -> WordPrefix e (Q :: K :: u)
  | pair1 (e : Bool) {u : WordList} : WordPrefix false u -> WordPrefix e (Q :: Q :: u)
theorem wordPrefix_true_of_false {u : WordList} (h : WordPrefix false u) : WordPrefix true u := by
  cases h with
  | nil _ => exact WordPrefix.nil true
  | T _ hu => exact WordPrefix.T true hu
  | pair0 _ hu => exact WordPrefix.pair0 true hu
  | pair1 _ hu => exact WordPrefix.pair1 true hu
theorem wordPrefix_true_and_cases (u : WordList) :
    WordPrefix true u /\ (WordPrefix false u \/ WordPrefix false (Q :: u)) := by
  induction u with
  | nil => exact ⟨WordPrefix.nil true, Or.inl (WordPrefix.nil false)⟩
  | cons w u ih =>
    rcases ih with ⟨hI, hJ⟩
    cases w with
    | V => exact ⟨WordPrefix.T true hI, Or.inl (WordPrefix.T false hI)⟩
    | K => exact ⟨WordPrefix.short0 hI, Or.inr (WordPrefix.pair0 false hI)⟩
    | Q =>
      rcases hJ with hJ | hJ
      · exact ⟨WordPrefix.short1 hJ, Or.inr (WordPrefix.pair1 false hJ)⟩
      · exact ⟨wordPrefix_true_of_false hJ, Or.inl hJ⟩
inductive DigitVal : Nat -> Nat -> WordList -> Prop where
  | nil : DigitVal 0 0 []
  | zero {A H : Nat} {u : WordList} : DigitVal A H u -> DigitVal (A * 2) (1 + H) (K :: u)
  | one {A H : Nat} {u : WordList} : DigitVal A H u -> DigitVal (1 + A * 2) (1 + H) (Q :: u)
theorem digitVal_not_cons_V {A H : Nat} {u : WordList} (h : DigitVal A H (V :: u)) : False := by
  cases h
theorem digitVal_cons_K_inv {A H : Nat} {u : WordList} (h : DigitVal A H (K :: u)) :
    ∃ A' H', DigitVal A' H' u /\ A = A' * 2 /\ H = 1 + H' := by
  cases h with
  | zero hD => exact ⟨_, _, hD, rfl, rfl⟩
theorem digitVal_cons_Q_inv {A H : Nat} {u : WordList} (h : DigitVal A H (Q :: u)) :
    ∃ A' H', DigitVal A' H' u /\ A = 1 + A' * 2 /\ H = 1 + H' := by
  cases h with
  | one hD => exact ⟨_, _, hD, rfl, rfl⟩
def hasQKSubword : WordList -> Bool
  | Q :: K :: _ => true
  | _ :: v => hasQKSubword v
  | [] => false
def notEndsWithQ : WordList -> Bool
  | [] => true
  | [Q] => false
  | _ :: v => notEndsWithQ v
theorem notEndsWithQ_of_cons (w : Word) (u : WordList) (h : notEndsWithQ (w :: u) = true) :
    notEndsWithQ u = true := by
  cases u with
  | nil => rfl
  | cons x xs => cases w <;> exact h
def SplitCond (p q : WordList) : Prop :=
  notEndsWithQ p = true \/ ∃ r, q = V :: r
theorem splitCond_of_cons (w : Word) (p q : WordList) (h : SplitCond (w :: p) q) :
    SplitCond p q := by
  rcases h with h | h
  · left; exact notEndsWithQ_of_cons w p h
  · right; exact h
theorem notEndsWithQ_append_singleton (u : WordList) (w : Word) :
    notEndsWithQ (u ++ [w]) = notEndsWithQ [w] := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases u with
    | nil => cases a <;> rfl
    | cons b u' => cases a <;> exact ih
theorem notEndsWithQ_replicate_V (p : Nat) : notEndsWithQ (List.replicate p V) = true := by
  induction p with
  | zero => rfl
  | succ p ih =>
    cases p with
    | zero => rfl
    | succ p' => exact ih
theorem replicate_succ_append (w : Word) (n : Nat) :
    List.replicate (n + 1) w = List.replicate n w ++ [w] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv_lhs => rw [List.replicate_succ, ih]
    rfl
theorem split_trailing_Q (u : WordList) :
    ∃ p n, u = p ++ List.replicate n Q /\ notEndsWithQ p = true := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨[], 0, rfl, rfl⟩
  | append_singleton u x ih =>
    rcases ih with ⟨p, n, rfl, hP⟩
    cases x with
    | V =>
      exact ⟨(p ++ List.replicate n Q) ++ [V], 0, by simp,
        by rw [notEndsWithQ_append_singleton]; rfl⟩
    | K =>
      exact ⟨(p ++ List.replicate n Q) ++ [K], 0, by simp,
        by rw [notEndsWithQ_append_singleton]; rfl⟩
    | Q =>
      refine ⟨p, n + 1, ?_, hP⟩
      rw [replicate_succ_append, List.append_assoc]
def evalWords : WordList -> HalfTape -> HalfTape
  | [], r => r
  | V :: u, r => t +> evalWords u r
  | K :: u, r => d0 +> evalWords u r
  | Q :: u, r => d1 +> evalWords u r
theorem evalWords_append (u v : WordList) (r : HalfTape) :
    evalWords (u ++ v) r = evalWords u (evalWords v r) := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [evalWords, ih]
def wordsToBits : WordList -> BitWord
  | [] => []
  | V :: u => t ++ wordsToBits u
  | K :: u => d0 ++ wordsToBits u
  | Q :: u => d1 ++ wordsToBits u
theorem wordsToBits_append_tape (u : WordList) (r : HalfTape) :
    wordsToBits u +> r = evalWords u r := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases a <;> (dsimp [wordsToBits, evalWords]; rw [ih])
theorem wordsToBits_append (u v : WordList) :
    wordsToBits (u ++ v) = wordsToBits u ++ wordsToBits v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases a <;> (dsimp [wordsToBits]; rw [ih])
theorem exists_digitVal_of_lt_pow (H : Nat) : ∀ A, A < 2 ^ H -> ∃ u, DigitVal A H u := by
  induction H with
  | zero =>
    intro A hA
    have h0 : A = 0 := by simpa using hA
    subst h0; exact ⟨[], DigitVal.nil⟩
  | succ H ih =>
    intro A hA
    have hpow : 2 ^ (H + 1) = 2 ^ H * 2 := Nat.pow_succ 2 H
    have h1H : H + 1 = 1 + H := by omega
    rcases even_or_odd_mul_two A with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases ih a (by omega) with ⟨u, hI⟩
      rw [h1H]; exact ⟨K :: u, DigitVal.zero hI⟩
    · rcases ih a (by omega) with ⟨u, hI⟩
      rw [h1H]; exact ⟨Q :: u, DigitVal.one hI⟩
theorem digitVal_append {A H : Nat} {u : WordList} (h1 : DigitVal A H u) :
    ∀ {B J : Nat} {v : WordList}, DigitVal B J v -> DigitVal (A + B * 2 ^ H) (H + J) (u ++ v) := by
  induction h1 with
  | nil =>
    intro B J v h2
    simpa using h2
  | @zero A H u _ ih =>
    intro B J v h2
    have h3 := DigitVal.zero (ih h2)
    have heq1 : (A + B * 2 ^ H) * 2 = A * 2 + B * 2 ^ (1 + H) := by
      rw [pow_two_one_add]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1, heq2] at h3
  | @one A H u _ ih =>
    intro B J v h2
    have h3 := DigitVal.one (ih h2)
    have heq1 : 1 + (A + B * 2 ^ H) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by
      rw [pow_two_one_add]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1, heq2] at h3
theorem digitVal_replicate_Q (n : Nat) : DigitVal (2 ^ n - 1) n (List.replicate n Q) := by
  induction n with
  | zero => exact DigitVal.nil
  | succ n ih =>
    have hpos := pow_two_pos n
    have h1 := DigitVal.one ih
    have heq1 : 1 + (2 ^ n - 1) * 2 = 2 ^ (n + 1) - 1 := by
      rw [Nat.pow_succ]; omega
    have heq2 : 1 + n = n + 1 := by omega
    simpa [List.replicate, heq1, heq2] using h1
theorem lt_pow_of_digitVal {A H : Nat} {u : WordList} (h : DigitVal A H u) : A < 2 ^ H := by
  induction h with
  | nil => decide
  | @zero A H u _ ih => rw [pow_two_one_add]; omega
  | @one A H u _ ih => rw [pow_two_one_add]; omega
theorem digitVal_unique_aux {A1 H1 : Nat} {u : WordList} (h1 : DigitVal A1 H1 u) :
    ∀ {A2 H2 : Nat} {v : WordList}, DigitVal A2 H2 v -> A1 = A2 -> H1 = H2 -> u = v := by
  induction h1 with
  | nil =>
    intro A2 H2 v h2 hA hH
    cases h2 with
    | nil => rfl
    | zero _ => omega
    | one _ => omega
  | @zero A1 H1 u _ ih =>
    intro A2 H2 v h2 hA hH
    cases h2 with
    | nil => omega
    | @zero A2' H2' v' hD =>
      rw [ih hD (by omega) (by omega)]
    | one _ => omega
  | @one A1 H1 u _ ih =>
    intro A2 H2 v h2 hA hH
    cases h2 with
    | nil => omega
    | zero _ => omega
    | @one A2' H2' v' hD =>
      rw [ih hD (by omega) (by omega)]
theorem digitVal_unique {A H : Nat} {u v : WordList} (h1 : DigitVal A H u) (h2 : DigitVal A H v) :
    u = v :=
  digitVal_unique_aux h1 h2 rfl rfl
def wordMass : WordList -> Rat
  | [] => 0
  | V :: v => wordMass v * (1 / 2)
  | _ :: v => 1 + wordMass v * 2
def wordMassK : WordList -> Rat
  | [] => 0
  | V :: v => wordMassK v * (1 / 2)
  | K :: v => 1 + wordMassK v * 2
  | Q :: v => wordMassK v * 2
def wordMassQ : WordList -> Rat
  | [] => 0
  | V :: v => wordMassQ v * (1 / 2)
  | K :: v => wordMassQ v * 2
  | Q :: v => 1 + wordMassQ v * 2
def wordScale : WordList -> Rat
  | [] => 1
  | V :: v => wordScale v * (1 / 2)
  | _ :: v => wordScale v * 2
theorem wordMass_nonneg (u : WordList) : 0 <= wordMass u /\ 0 <= wordMassK u /\
    0 <= wordMassQ u := by
  induction u with
  | nil => simp [wordMass, wordMassK, wordMassQ]
  | cons a u ih =>
    cases a <;>
      (dsimp [wordMass, wordMassK, wordMassQ]; refine ⟨by linarith, by linarith, by linarith⟩)
theorem wordMass_eq_add (u : WordList) : wordMass u = wordMassK u + wordMassQ u := by
  induction u with
  | nil => simp [wordMass, wordMassK, wordMassQ]
  | cons a u ih => cases a <;> (dsimp [wordMass, wordMassK, wordMassQ]; rw [ih]; ring)
theorem wordScale_pos (u : WordList) : 0 < wordScale u := by
  induction u with
  | nil => simp [wordScale]
  | cons a u ih => cases a <;> (dsimp [wordScale]; linarith)
theorem wordMass_append (u v : WordList) : wordMass (u ++
    v) = wordMass u + wordScale u * wordMass v := by
  induction u with
  | nil => simp [wordMass, wordScale]
  | cons a u ih => cases a <;> (dsimp [wordMass, wordScale]; rw [ih]; ring)
theorem wordMassK_append (u v : WordList) : wordMassK (u ++
    v) = wordMassK u + wordScale u * wordMassK v := by
  induction u with
  | nil => simp [wordMassK, wordScale]
  | cons a u ih => cases a <;> (dsimp [wordMassK, wordScale]; rw [ih]; ring)
theorem wordMassQ_append (u v : WordList) : wordMassQ (u ++
    v) = wordMassQ u + wordScale u * wordMassQ v := by
  induction u with
  | nil => simp [wordMassQ, wordScale]
  | cons a u ih => cases a <;> (dsimp [wordMassQ, wordScale]; rw [ih]; ring)
theorem wordScale_append (u v : WordList) : wordScale (u ++ v) = wordScale u * wordScale v := by
  induction u with
  | nil => simp [wordScale]
  | cons a u ih => cases a <;> (dsimp [wordScale]; rw [ih]; ring)
theorem digitVal_scale_and_mass {A H : Nat} {u : WordList} (h : DigitVal A H u) :
    wordScale u = ((2 ^ H : Nat) : Rat) /\ wordMass u + 1 = ((2 ^ H : Nat) : Rat) /\
      wordMassQ u = (A : Rat) := by
  induction h with
  | nil => simp [wordScale, wordMass, wordMassQ]
  | @zero A H u _ ih =>
    rw [pow_two_one_add H]; dsimp [wordScale, wordMass, wordMassQ]
    push_cast at ih ⊢; refine ⟨by linarith, by linarith, by linarith⟩
  | @one A H u _ ih =>
    rw [pow_two_one_add H]; dsimp [wordScale, wordMass, wordMassQ]
    push_cast at ih ⊢; refine ⟨by linarith, by linarith, by linarith⟩
theorem digitVal_wordMassK_eq {A H : Nat} {u : WordList} (h : DigitVal A H u) :
    wordMassK u + (A : Rat) + 1 = ((2 ^ H : Nat) : Rat) := by
  have hd := digitVal_scale_and_mass h
  have hm := wordMass_eq_add u
  linarith
inductive Scan : Nat -> WordList -> Nat -> WordList -> Rat -> Prop where
  | nil (k : Nat) : Scan k [] k [] 0
  | T {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan ((1 + n) * 2) u k v l -> Scan (1 + n) (V :: u) k (V :: v) (l * (1 / 2))
  | pair0 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (1 + n) (Q :: K :: u) k (V :: v) ((1 + l) * (1 / 2))
  | pair1 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (1 + n) (Q :: Q :: u) k (V :: v) ((1 / 4) + l * (1 / 2))
  | short00 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (2 + n * 4) (K :: u) k (K :: v) (1 + l * 2)
  | short01 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (2 + n * 4) (Q :: u) k (K :: v) (l * 2)
  | short10 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (4 + n * 4) (K :: u) k (Q :: v) (1 + l * 2)
  | short11 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (4 + n * 4) (Q :: u) k (Q :: v) (l * 2)
theorem scan_mass_bounds {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    0 <= l /\ wordMass v <= wordMass u /\ wordMass v + l <= wordMass u + wordMassK u := by
  induction h with
  | nil _ => simp [wordMass, wordMassK]
  | T _ ih =>
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
  | @pair0 n u k v l _ ih =>
    have hw := wordMass_nonneg v
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
  | @pair1 n u k v l _ ih =>
    have hw := wordMass_nonneg v
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
  | short00 _ ih =>
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
  | short01 _ ih =>
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
  | short10 _ ih =>
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
  | short11 _ ih =>
    dsimp [wordMass, wordMassK]; refine ⟨by linarith, by linarith, by linarith⟩
theorem exists_scan_of_wordPrefix {e : Bool} {u : WordList} (hI : WordPrefix e u) :
    ∀ (k : Nat), (e = true -> ∃ n, k = n * 2) ->
      (wordMass u + wordMassK u) * 2 < (k : Rat) ->
      ∃ b v l, Scan k u b v l /\ 0 < b := by
  induction hI with
  | nil e =>
    intro k _ hk
    dsimp [wordMass, wordMassK] at hk
    have hk_pos : (0 : Rat) < (k : Rat) := by linarith
    have hk_nat : 0 < k := Nat.cast_pos.mp hk_pos
    exact ⟨k, [], 0, Scan.nil k, hk_nat⟩
  | @T e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass, wordMassK] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih ((1 + k) * 2) (fun _ => ⟨1 + k, rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
      exact ⟨b, V :: v, l * (1 / 2), Scan.T hS, hB⟩
  | @short0 u _ ih =>
    intro k hEk hk
    have hw := wordMass_nonneg u
    dsimp [wordMass, wordMassK] at hk
    rcases hEk rfl with ⟨n, rfl⟩
    rcases even_or_odd_mul_two n with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (a * 2) (fun _ => ⟨a, rfl⟩)
          (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
        refine ⟨b, Q :: v, 1 + l * 2, ?_, hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact Scan.short10 hS
    · rcases ih (a * 2) (fun _ => ⟨a, rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
      refine ⟨b, K :: v, 1 + l * 2, ?_, hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact Scan.short00 hS
  | @short1 u _ ih =>
    intro k hEk hk
    have hw := wordMass_nonneg u
    dsimp [wordMass, wordMassK] at hk
    rcases hEk rfl with ⟨n, rfl⟩
    rcases even_or_odd_mul_two n with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (1 + a * 2) (fun h => by contradiction)
          (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
        refine ⟨b, Q :: v, l * 2, ?_, hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact Scan.short11 hS
    · rcases ih (1 + a * 2) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
      refine ⟨b, K :: v, l * 2, ?_, hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact Scan.short01 hS
  | @pair0 e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass, wordMassK] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k, rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
      exact ⟨b, V :: v, (1 + l) * (1 / 2), Scan.pair0 hS, hB⟩
  | @pair1 e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass, wordMassK] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (1 + k * 2) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨b, v, l, hS, hB⟩
      exact ⟨b, V :: v, (1 / 4) + l * (1 / 2), Scan.pair1 hS, hB⟩
theorem exists_scan_of_mass_lt (u : WordList) (k : Nat) (h : (wordMass u + wordMassK u) * 2 <
    ((k * 2 : Nat) : Rat)) :
    ∃ b v l, Scan (k * 2) u b v l /\ 0 < b :=
  exists_scan_of_wordPrefix (wordPrefix_true_and_cases u).1 (k * 2) (fun _ => ⟨k, rfl⟩) h
theorem not_scan_odd_cons_K (n : Nat) (u : WordList) (b : Nat) (v : WordList) (l : Rat) :
    ¬ Scan (1 + n * 2) (K :: u) b v l := by
  intro h; generalize ha : 1 + n * 2 = a at h; cases h <;> omega
theorem not_scan_odd_even_Q_K (r : Nat) :
    ∀ (n b : Nat) (v : WordList) (l : Rat),
      ¬ Scan (1 + n * 2) (List.replicate (r * 2) Q ++ [K]) b v l := by
  induction r with
  | zero =>
    intro n b v l hI
    exact not_scan_odd_cons_K n [] b v l hI
  | succ r ih =>
    intro n b v l hI
    have heq : (r + 1) * 2 = r * 2 + 2 := by omega
    rw [heq] at hI
    change Scan (1 + n * 2) (Q :: Q :: (List.replicate (r * 2) Q ++ [K])) b v l at hI
    generalize ha : 1 + n * 2 = a at hI
    cases hI with
    | @pair1 m _ _ _ _ hJ =>
      exact ih m _ _ _ hJ
    | short01 _ => omega
    | short11 _ => omega
theorem scan_odd_Q_K_inv (r : Nat) :
    ∀ (a b : Nat) (v : WordList) (l : Rat),
      Scan a (List.replicate (1 + r * 2) Q ++ [K]) b v l ->
      v = List.replicate (1 + r) V /\ b = (a - 1) * 2 ^ (1 + r) /\ l = 1 / 2 := by
  induction r with
  | zero =>
    intro a b v l hI
    change Scan a [Q, K] b v l at hI
    cases hI with
    | @pair0 m _ _ _ _ hJ =>
      generalize hk : m * 2 = k at hJ
      cases hJ
      exact ⟨rfl, by simp; omega, by ring⟩
    | short01 hJ => exact False.elim (not_scan_odd_cons_K _ [] _ _ _ hJ)
    | short11 hJ => exact False.elim (not_scan_odd_cons_K _ [] _ _ _ hJ)
  | succ r ih =>
    intro a b v l hI
    have heq : 1 + (r + 1) * 2 = (1 + r * 2) + 2 := by omega
    rw [heq] at hI
    change Scan a (Q :: Q :: (List.replicate (1 + r * 2) Q ++ [K])) b v l at hI
    cases hI with
    | @pair1 n _ _ v0 l0 hJ =>
      rcases ih (1 + n * 2) b v0 l0 hJ with ⟨rfl, rfl, rfl⟩
      refine ⟨rfl, ?_, by ring⟩
      have heq2 : 1 + (r + 1) = (1 + r) + 1 := by omega
      rw [heq2, Nat.pow_succ]; simp; ring
    | @short01 n _ _ _ _ hJ =>
      have heq2 : (1 + r * 2) + 1 = (r + 1) * 2 := by omega
      change Scan (1 + n * 2) (List.replicate ((1 + r * 2) + 1) Q ++ [K]) _ _ _ at hJ
      rw [heq2] at hJ
      exact False.elim (not_scan_odd_even_Q_K (r + 1) n _ _ _ hJ)
    | @short11 n _ _ _ _ hJ =>
      have heq2 : (1 + r * 2) + 1 = (r + 1) * 2 := by omega
      change Scan (1 + n * 2) (List.replicate ((1 + r * 2) + 1) Q ++ [K]) _ _ _ at hJ
      rw [heq2] at hJ
      exact False.elim (not_scan_odd_even_Q_K (r + 1) n _ _ _ hJ)
theorem scan_even_Q_K_inv (r a b : Nat) (v : WordList) (l : Rat)
    (hI : Scan a (List.replicate (2 + r * 2) Q ++ [K]) b v l) :
    ∃ d n, v = d :: List.replicate (1 + r) V /\ b = n * 2 ^ (2 + r) /\ l = 1 := by
  have heq0 : 2 + r * 2 = (r * 2) + 2 := by omega
  rw [heq0] at hI
  change Scan a (Q :: Q :: (List.replicate (r * 2) Q ++ [K])) b v l at hI
  cases hI with
  | @pair1 n _ _ _ _ hJ =>
    exact False.elim (not_scan_odd_even_Q_K r n _ _ _ hJ)
  | @short01 n _ _ v0 l0 hJ =>
    have heq1 : 1 + r * 2 = (r * 2) + 1 := by omega
    have hJ' : Scan (1 + n * 2) (List.replicate (1 + r * 2) Q ++ [K]) b v0 l0 := by
      rw [heq1]; exact hJ
    rcases scan_odd_Q_K_inv r (1 + n * 2) b v0 l0 hJ' with ⟨rfl, rfl, rfl⟩
    refine ⟨K, n, rfl, ?_, by ring⟩
    have heq : 2 + r = (1 + r) + 1 := by omega
    rw [heq, Nat.pow_succ]; simp; ring
  | @short11 n _ _ v0 l0 hJ =>
    have heq1 : 1 + r * 2 = (r * 2) + 1 := by omega
    have hJ' : Scan (1 + n * 2) (List.replicate (1 + r * 2) Q ++ [K]) b v0 l0 := by
      rw [heq1]; exact hJ
    rcases scan_odd_Q_K_inv r (1 + n * 2) b v0 l0 hJ' with ⟨rfl, rfl, rfl⟩
    refine ⟨Q, n, rfl, ?_, by ring⟩
    have heq : 2 + r = (1 + r) + 1 := by omega
    rw [heq, Nat.pow_succ]; simp; ring
theorem scan_add_Q_K_inv (n r a b : Nat) (v : WordList) (l : Rat)
    (hI : Scan a (List.replicate (1 + r * 2 + n) Q ++ [K]) b v l) :
    ∃ w k, v = w ++ List.replicate (1 + r) V /\ b = k * 2 ^ (1 + r) := by
  rcases even_or_odd_mul_two n with ⟨a0, rfl⟩ | ⟨a0, rfl⟩
  · have heq : 1 + r * 2 + a0 * 2 = 1 + (r + a0) * 2 := by omega
    rw [heq] at hI
    rcases scan_odd_Q_K_inv (r + a0) a b v l hI with ⟨rfl, rfl, _⟩
    refine ⟨List.replicate a0 V, (a - 1) * 2 ^ a0, ?_, ?_⟩
    · have heq2 : 1 + (r + a0) = a0 + (1 + r) := by omega
      rw [heq2, List.replicate_add]
    · have heq2 : 1 + (r + a0) = a0 + (1 + r) := by omega
      rw [heq2, Nat.pow_add]; ring
  · have heq : 1 + r * 2 + (1 + a0 * 2) = 2 + (r + a0) * 2 := by omega
    rw [heq] at hI
    rcases scan_even_Q_K_inv (r + a0) a b v l hI with ⟨d, k, rfl, rfl, _⟩
    refine ⟨d :: List.replicate a0 V, k * 2 ^ (1 + a0), ?_, ?_⟩
    · have heq2 : 1 + (r + a0) = a0 + (1 + r) := by omega
      rw [heq2, List.replicate_add]; rfl
    · have heq2 : 2 + (r + a0) = (1 + a0) + (1 + r) := by omega
      rw [heq2, Nat.pow_add]; ring
inductive TailDefect : WordList -> Rat -> Prop where
  | tail_end : TailDefect [K] 0
  | tail_zero {u : WordList} {z : Rat} : TailDefect u z -> TailDefect (K :: u) (1 + z * 2)
  | tail_one {u : WordList} {z : Rat} : TailDefect u z -> TailDefect (Q :: u) (z * 2)
theorem tailDefect_nonneg {u : WordList} {z : Rat} (h : TailDefect u z) : 0 <= z := by
  induction h with
  | tail_end => linarith
  | tail_zero _ ih => linarith
  | tail_one _ ih => linarith
theorem tailDefect_cons_K_inv {u : WordList} {z : Rat} (h : TailDefect (K :: u) z) :
    (u = [] /\ z = 0) \/ ∃ y, TailDefect u y /\ z = 1 + y * 2 := by
  cases h with
  | tail_end => left; exact ⟨rfl, rfl⟩
  | tail_zero hJ => right; exact ⟨_, hJ, rfl⟩
theorem tailDefect_cons_Q_inv {u : WordList} {z : Rat} (h : TailDefect (Q :: u) z) :
    ∃ y, TailDefect u y /\ z = y * 2 := by
  cases h with
  | tail_one hJ => exact ⟨_, hJ, rfl⟩
theorem tailDefect_append_K_of_digitVal {A H : Nat} {u : WordList} (h : DigitVal A H u) :
    TailDefect (u ++ [K]) (wordMassK u) := by
  induction h with
  | nil => exact TailDefect.tail_end
  | zero _ ih => exact TailDefect.tail_zero ih
  | one _ ih => exact TailDefect.tail_one ih
theorem exists_digitVal_of_tailDefect {u : WordList} {z : Rat} (h : TailDefect u z) :
    ∃ A H, DigitVal A H u := by
  induction h with
  | tail_end => exact ⟨0, 1, DigitVal.zero DigitVal.nil⟩
  | tail_zero _ ih =>
    rcases ih with ⟨A, H, hD⟩
    exact ⟨A * 2, 1 + H, DigitVal.zero hD⟩
  | tail_one _ ih =>
    rcases ih with ⟨A, H, hD⟩
    exact ⟨1 + A * 2, 1 + H, DigitVal.one hD⟩
theorem scan_tailDefect_bound {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    ∀ {z : Rat}, TailDefect u z ->
      wordMass v <= 1 + z * 2 /\ l <= 1 + z * 2 /\
      (∀ n, a = 1 + n * 2 -> wordMass v <= z * 2 /\ l <= (1 / 2) + z * 2) := by
  induction h with
  | nil _ => intro z hZ; cases hZ
  | T _ _ => intro z hZ; cases hZ
  | @pair0 m _ _ _ _ hI ih =>
    intro z hZ
    rcases tailDefect_cons_Q_inv hZ with ⟨y, hJ, rfl⟩
    rcases tailDefect_cons_K_inv hJ with ⟨rfl, rfl⟩ | ⟨x, hJ', rfl⟩
    · generalize hk : m * 2 = k at hI
      cases hI
      dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ _ => ⟨by linarith, by linarith⟩⟩
    · rcases ih hJ' with ⟨hM, hL, _⟩
      have hx := tailDefect_nonneg hJ'
      dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ _ => ⟨by linarith, by linarith⟩⟩
  | @pair1 m _ _ _ _ hI ih =>
    intro z hZ
    rcases tailDefect_cons_Q_inv hZ with ⟨y, hJ, rfl⟩
    rcases tailDefect_cons_Q_inv hJ with ⟨x, hJ', rfl⟩
    rcases (ih hJ').2.2 m rfl with ⟨hM, hL⟩
    have hx := tailDefect_nonneg hJ'
    dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ _ => ⟨by linarith, by linarith⟩⟩
  | @short00 m _ _ _ _ hI ih =>
    intro z hZ
    rcases tailDefect_cons_K_inv hZ with ⟨rfl, rfl⟩ | ⟨x, hJ, rfl⟩
    · generalize hk : m * 2 = k at hI
      cases hI
      dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ h => by omega⟩
    · rcases ih hJ with ⟨hM, hL, _⟩
      dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ h => by omega⟩
  | @short01 m _ _ _ _ _ ih =>
    intro z hZ
    rcases tailDefect_cons_Q_inv hZ with ⟨x, hJ, rfl⟩
    rcases (ih hJ).2.2 m rfl with ⟨hM, hL⟩
    dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ h => by omega⟩
  | @short10 m _ _ _ _ hI ih =>
    intro z hZ
    rcases tailDefect_cons_K_inv hZ with ⟨rfl, rfl⟩ | ⟨x, hJ, rfl⟩
    · generalize hk : m * 2 = k at hI
      cases hI
      dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ h => by omega⟩
    · rcases ih hJ with ⟨hM, hL, _⟩
      dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ h => by omega⟩
  | @short11 m _ _ _ _ _ ih =>
    intro z hZ
    rcases tailDefect_cons_Q_inv hZ with ⟨x, hJ, rfl⟩
    rcases (ih hJ).2.2 m rfl with ⟨hM, hL⟩
    dsimp [wordMass]; refine ⟨by linarith, by linarith, fun _ h => by omega⟩
theorem scan_append {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h1 : Scan a u b v l) :
    ∀ {w : WordList} {c : Nat} {x : WordList} {m : Rat},
      Scan b w c x m -> ∃ p, Scan a (u ++ w) c (v ++ x) p /\ p = l + wordScale v * m := by
  induction h1 with
  | nil _ =>
    intro w c x m h2
    exact ⟨m, h2, by simp [wordScale]⟩
  | T _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨p * (1 / 2), Scan.T hK, by dsimp [wordScale]; rw [hE]; ring⟩
  | pair0 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨(1 + p) * (1 / 2), Scan.pair0 hK, by dsimp [wordScale]; rw [hE]; ring⟩
  | pair1 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨(1 / 4) + p * (1 / 2), Scan.pair1 hK, by dsimp [wordScale]; rw [hE]; ring⟩
  | short00 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨1 + p * 2, Scan.short00 hK, by dsimp [wordScale]; rw [hE]; ring⟩
  | short01 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨p * 2, Scan.short01 hK, by dsimp [wordScale]; rw [hE]; ring⟩
  | short10 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨1 + p * 2, Scan.short10 hK, by dsimp [wordScale]; rw [hE]; ring⟩
  | short11 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p, hK, hE⟩
    exact ⟨p * 2, Scan.short11 hK, by dsimp [wordScale]; rw [hE]; ring⟩
theorem scan_split_of_splitCond {a : Nat} {u : WordList} {c : Nat} {z : WordList} {l : Rat}
    (h : Scan a u c z l) :
    ∀ (p q : WordList), u = p ++ q -> SplitCond p q ->
      ∃ b v w x y, Scan a p b v x /\ Scan b q c w y /\ z = v ++ w /\ l = x + wordScale v * y := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨k, [], [], 0, 0, Scan.nil k, Scan.nil k, rfl, by simp [wordScale]⟩
    | cons s p => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.T hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons V p q hP) with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
      exact ⟨b, V :: v0, w, x * (1 / 2), y, Scan.T hJ, hK, rfl,
        by dsimp [wordScale]; rw [hL]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.pair0 hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      cases p with
      | nil =>
        dsimp at hE; subst hE
        rcases hP with hP | ⟨r, hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
        have hP' := splitCond_of_cons K p q (splitCond_of_cons Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
        exact ⟨b, V :: v0, w, (1 + x) * (1 / 2), y, Scan.pair0 hJ, hK, rfl,
          by dsimp [wordScale]; rw [hL]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.pair1 hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      cases p with
      | nil =>
        dsimp at hE; subst hE
        rcases hP with hP | ⟨r, hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
        have hP' := splitCond_of_cons Q p q (splitCond_of_cons Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
        exact ⟨b, V :: v0, w, (1 / 4) + x * (1 / 2), y, Scan.pair1 hJ, hK, rfl,
          by dsimp [wordScale]; rw [hL]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.short00 hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
      exact ⟨b, K :: v0, w, 1 + x * 2, y, Scan.short00 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hL]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.short01 hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
      exact ⟨b, K :: v0, w, x * 2, y, Scan.short01 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hL]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.short10 hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
      exact ⟨b, Q :: v0, w, 1 + x * 2, y, Scan.short10 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hL]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      dsimp at hE; subst hE
      exact ⟨_, [], _, 0, _, Scan.nil _, Scan.short11 hI, rfl, by simp [wordScale]⟩
    | cons s p =>
      simp only [List.cons_append, List.cons.injEq] at hE; rcases hE with ⟨rfl, hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨b, v0, w, x, y, hJ, hK, rfl, hL⟩
      exact ⟨b, Q :: v0, w, x * 2, y, Scan.short11 hJ, hK, rfl,
        by dsimp [wordScale]; rw [hL]; ring⟩
theorem scan_scale_pow_eight {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    ∃ g : Nat, wordScale u = wordScale v * ((8 ^ g : Nat) : Rat) := by
  induction h with
  | nil _ => exact ⟨0, by simp [wordScale]⟩
  | T _ ih =>
    rcases ih with ⟨g, hE⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring⟩
  | pair0 _ ih =>
    rcases ih with ⟨g, hE⟩
    refine ⟨g + 1, ?_⟩
    rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; dsimp [wordScale]; rw [hE]; ring
  | pair1 _ ih =>
    rcases ih with ⟨g, hE⟩
    refine ⟨g + 1, ?_⟩
    rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; dsimp [wordScale]; rw [hE]; ring
  | short00 _ ih =>
    rcases ih with ⟨g, hE⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring⟩
  | short01 _ ih =>
    rcases ih with ⟨g, hE⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring⟩
  | short10 _ ih =>
    rcases ih with ⟨g, hE⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring⟩
  | short11 _ ih =>
    rcases ih with ⟨g, hE⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring⟩
inductive WordEffect : Nat -> WordList -> Nat -> WordList -> Prop where
  | nil (n : Nat) : WordEffect n [] n []
  | T {n : Nat} {u : WordList} {b : Nat} {v : WordList} :
      WordEffect (1 + n * 2) u b v -> WordEffect n (V :: u) b (V :: v)
  | d00 {n : Nat} {u : WordList} {b : Nat} {v : WordList} :
      WordEffect n u b v -> WordEffect (n * 2) (K :: u) b (K :: v)
  | d01 {n : Nat} {u : WordList} {b : Nat} {v : WordList} :
      WordEffect n u b v -> WordEffect (1 + n * 2) (K :: u) b (Q :: v)
  | d10 {n : Nat} {u : WordList} {b : Nat} {v : WordList} :
      WordEffect n u b v -> WordEffect (n * 2) (Q :: u) b (Q :: v)
  | d11 {n : Nat} {u : WordList} {b : Nat} {v : WordList} :
      WordEffect (1 + n) u b v -> WordEffect (1 + n * 2) (Q :: u) b (K :: v)
def forceNat (e : Nat) (f : Nat -> α) : α :=
  Nat.casesOn (e + 1) (f 0) (fun n => f n)

@[scoped simp] theorem forceNat_eq (e : Nat) (f : Nat -> α) : forceNat e f = f e := rfl

def forceWord (w : Word) (f : Word -> α) : α :=
  Word.casesOn w (f V) (f K) (f Q)

@[scoped simp] theorem forceWord_eq (w : Word) (f : Word -> α) : forceWord w f = f w := by
  cases w <;> rfl

def forceProd (p : α × β) (f : α -> β -> γ) : γ :=
  Prod.casesOn p f

@[scoped simp] theorem forceProd_eq (p : α × β) (f : α -> β -> γ) : forceProd p f = f p.1 p.2 := by
  cases p; rfl

def withNatWordList (u : WordList) (f : WordList -> α) : α :=
  match u with
  | [] => f []
  | w :: ws => forceWord w (fun w' => withNatWordList ws (fun ws' => f (w' :: ws')))

@[scoped simp] theorem withNatWordList_eq (u : WordList) (f : WordList ->
  α) : withNatWordList u f = f u := by
  induction u generalizing f with
  | nil => rfl
  | cons w ws ih => simp [withNatWordList, ih]

def evalEffect : Nat -> WordList -> Nat × WordList
  | n, [] => (n, [])
  | n, V :: u =>
    forceNat (1 + n * 2) (fun m =>
      forceProd (evalEffect m u) (fun r1 r2 => (r1, V :: r2)))
  | n, K :: u =>
    forceNat (n / 2) (fun m =>
      forceWord (if n % 2 == 0 then K else Q) (fun w =>
        forceProd (evalEffect m u) (fun r1 r2 => (r1, w :: r2))))
  | n, Q :: u =>
    forceNat (if n % 2 == 0 then n / 2 else 1 + n / 2) (fun m =>
      forceWord (if n % 2 == 0 then Q else K) (fun w =>
        forceProd (evalEffect m u) (fun r1 r2 => (r1, w :: r2))))
theorem evalEffect_sound (u : WordList) :
    ∀ (n : Nat), WordEffect n u (evalEffect n u).1 (evalEffect n u).2 := by
  induction u with
  | nil => intro n; exact WordEffect.nil n
  | cons w u ih =>
    intro n
    cases w with
    | V =>
      dsimp [evalEffect]
      exact WordEffect.T (ih (1 + n * 2))
    | K =>
      dsimp [evalEffect]
      rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · have hcond : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
        rw [hcond]; dsimp
        have h1 := WordEffect.d00 (ih (n / 2))
        have heq : (n / 2) * 2 = n := by omega
        rwa [heq] at h1
      · have hcond : (n % 2 == 0) = false := beq_false_of_ne (by omega)
        rw [hcond]; dsimp
        have h1 := WordEffect.d01 (ih (n / 2))
        have heq : 1 + (n / 2) * 2 = n := by omega
        rwa [heq] at h1
    | Q =>
      dsimp [evalEffect]
      rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · have hcond : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
        rw [hcond]; dsimp
        have h1 := WordEffect.d10 (ih (n / 2))
        have heq : (n / 2) * 2 = n := by omega
        rwa [heq] at h1
      · have hcond : (n % 2 == 0) = false := beq_false_of_ne (by omega)
        rw [hcond]; dsimp
        have h1 := WordEffect.d11 (ih (1 + n / 2))
        have heq : 1 + (n / 2) * 2 = n := by omega
        rwa [heq] at h1
theorem exists_wordEffect (u : WordList) (n : Nat) : ∃ b v, WordEffect n u b v :=
  ⟨(evalEffect n u).1, (evalEffect n u).2, evalEffect_sound u n⟩
theorem wordEffect_unique {n : Nat} {u : WordList} {b1 : Nat} {v1 : WordList}
    (h1 : WordEffect n u b1 v1) :
    ∀ {b2 : Nat} {v2 : WordList}, WordEffect n u b2 v2 -> b1 = b2 /\ v1 = v2 := by
  induction h1 with
  | nil n =>
    intro b2 v2 h2; cases h2; exact ⟨rfl, rfl⟩
  | T _ ih =>
    intro b2 v2 h2
    cases h2 with
    | T h2' =>
      rcases ih h2' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | @d00 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : n * 2 = k at h2
    cases h2 with
    | @d00 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | d01 _ => omega
  | @d01 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : 1 + n * 2 = k at h2
    cases h2 with
    | d00 _ => omega
    | @d01 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | @d10 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : n * 2 = k at h2
    cases h2 with
    | @d10 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | d11 _ => omega
  | @d11 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : 1 + n * 2 = k at h2
    cases h2 with
    | d10 _ => omega
    | @d11 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
theorem wordEffect_append {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (h1 : WordEffect n u b v) :
    ∀ {w : WordList} {c : Nat} {x : WordList},
      WordEffect b w c x -> WordEffect n (u ++ w) c (v ++ x) := by
  induction h1 with
  | nil _ => intro w c x h2; exact h2
  | T _ ih => intro w c x h2; exact WordEffect.T (ih h2)
  | d00 _ ih => intro w c x h2; exact WordEffect.d00 (ih h2)
  | d01 _ ih => intro w c x h2; exact WordEffect.d01 (ih h2)
  | d10 _ ih => intro w c x h2; exact WordEffect.d10 (ih h2)
  | d11 _ ih => intro w c x h2; exact WordEffect.d11 (ih h2)
theorem wordEffect_split_input (u : WordList) :
    ∀ {n : Nat} {w : WordList} {b : Nat} {out : WordList},
      WordEffect n (u ++ w) b out ->
      ∃ m v x, out = v ++ x /\ WordEffect n u m v /\ WordEffect m w b x := by
  induction u with
  | nil =>
    intro n w b out hE
    exact ⟨n, [], out, rfl, WordEffect.nil n, hE⟩
  | cons s u ih =>
    intro n w b out hE
    cases hE with
    | T hSub =>
      rcases ih hSub with ⟨m, v1, x, rfl, hA, hB⟩
      exact ⟨m, V :: v1, x, rfl, WordEffect.T hA, hB⟩
    | d00 hSub =>
      rcases ih hSub with ⟨m, v1, x, rfl, hA, hB⟩
      exact ⟨m, K :: v1, x, rfl, WordEffect.d00 hA, hB⟩
    | d01 hSub =>
      rcases ih hSub with ⟨m, v1, x, rfl, hA, hB⟩
      exact ⟨m, Q :: v1, x, rfl, WordEffect.d01 hA, hB⟩
    | d10 hSub =>
      rcases ih hSub with ⟨m, v1, x, rfl, hA, hB⟩
      exact ⟨m, Q :: v1, x, rfl, WordEffect.d10 hA, hB⟩
    | d11 hSub =>
      rcases ih hSub with ⟨m, v1, x, rfl, hA, hB⟩
      exact ⟨m, K :: v1, x, rfl, WordEffect.d11 hA, hB⟩
theorem wordEffect_split_output (v : WordList) :
    ∀ {n : Nat} {u : WordList} {c : Nat} {w : WordList},
      WordEffect n u c (v ++ w) ->
      ∃ u1 u2 b, u = u1 ++ u2 /\ WordEffect n u1 b v /\ WordEffect b u2 c w := by
  induction v with
  | nil =>
    intro n u c w hE
    exact ⟨[], u, n, rfl, WordEffect.nil n, hE⟩
  | cons x v ih =>
    intro n u c w hE
    cases hE with
    | T hSub =>
      rcases ih hSub with ⟨u1, u2, b, rfl, hL, hR⟩
      exact ⟨V :: u1, u2, b, rfl, WordEffect.T hL, hR⟩
    | d00 hSub =>
      rcases ih hSub with ⟨u1, u2, b, rfl, hL, hR⟩
      exact ⟨K :: u1, u2, b, rfl, WordEffect.d00 hL, hR⟩
    | d01 hSub =>
      rcases ih hSub with ⟨u1, u2, b, rfl, hL, hR⟩
      exact ⟨K :: u1, u2, b, rfl, WordEffect.d01 hL, hR⟩
    | d10 hSub =>
      rcases ih hSub with ⟨u1, u2, b, rfl, hL, hR⟩
      exact ⟨Q :: u1, u2, b, rfl, WordEffect.d10 hL, hR⟩
    | d11 hSub =>
      rcases ih hSub with ⟨u1, u2, b, rfl, hL, hR⟩
      exact ⟨Q :: u1, u2, b, rfl, WordEffect.d11 hL, hR⟩
theorem wordEffect_digitVal {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ∀ {A H : Nat}, DigitVal A H u -> ∃ B, DigitVal B H v /\ A + n = B + b * 2 ^ H := by
  induction hI with
  | nil n =>
    intro A H hD; cases hD
    exact ⟨0, DigitVal.nil, by simp⟩
  | T _ _ =>
    intro A H hD; exact False.elim (digitVal_not_cons_V hD)
  | @d00 n _ b _ _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A', H', hD', rfl, rfl⟩
    rcases ih hD' with ⟨B, hBv, hEq⟩
    refine ⟨B * 2, DigitVal.zero hBv, ?_⟩
    rw [pow_two_one_add, Nat.mul_add]; omega
  | @d01 n _ b _ _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A', H', hD', rfl, rfl⟩
    rcases ih hD' with ⟨B, hBv, hEq⟩
    refine ⟨1 + B * 2, DigitVal.one hBv, ?_⟩
    rw [pow_two_one_add, Nat.mul_add]; omega
  | @d10 n _ b _ _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A', H', hD', rfl, rfl⟩
    rcases ih hD' with ⟨B, hBv, hEq⟩
    refine ⟨1 + B * 2, DigitVal.one hBv, ?_⟩
    rw [pow_two_one_add, Nat.mul_add]; omega
  | @d11 n _ b _ _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A', H', hD', rfl, rfl⟩
    rcases ih hD' with ⟨B, hBv, hEq⟩
    refine ⟨B * 2, DigitVal.zero hBv, ?_⟩
    rw [pow_two_one_add, Nat.mul_add]; omega
theorem exists_wordEffect_of_digitVal_add {n : Nat} {ds : WordList} {A H B : Nat}
    (hD : DigitVal A H ds) (hSum : A + n = B) (hBound : B < 2 ^ H) :
    ∃ v, DigitVal B H v /\ WordEffect n ds 0 v := by
  rcases exists_wordEffect ds n with ⟨b, v, hE⟩
  rcases wordEffect_digitVal hE hD with ⟨C, hV, hEq⟩
  have hCb := lt_pow_of_digitVal hV
  have hb0 : b = 0 := by
    cases b with
    | zero => rfl
    | succ b' =>
      have : 1 * 2 ^ H <= (b' + 1) * 2 ^ H := Nat.mul_le_mul_right (2 ^ H) (by omega)
      omega
  subst hb0
  have hCB : C = B := by omega
  subst hCB
  exact ⟨v, hV, hE⟩
theorem wordEffect_preserves_scale_and_mass {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    wordScale v = wordScale u /\ wordMass v = wordMass u := by
  induction hI with
  | nil _ => simp [wordScale, wordMass]
  | T _ ih => dsimp [wordScale, wordMass]; constructor <;> linarith
  | d00 _ ih => dsimp [wordScale, wordMass]; constructor <;> linarith
  | d01 _ ih => dsimp [wordScale, wordMass]; constructor <;> linarith
  | d10 _ ih => dsimp [wordScale, wordMass]; constructor <;> linarith
  | d11 _ ih => dsimp [wordScale, wordMass]; constructor <;> linarith
theorem wordEffect_budget_eq {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ((1 + b : Nat) : Rat) * wordScale u =
      ((1 + n : Nat) : Rat) + wordMass u + wordMassQ u - wordMassQ v := by
  induction hI with
  | nil _ => simp [wordScale, wordMass, wordMassQ]
  | T _ ih => dsimp [wordScale, wordMass, wordMassQ]; push_cast at ih ⊢; linarith
  | d00 _ ih => dsimp [wordScale, wordMass, wordMassQ]; push_cast at ih ⊢; linarith
  | d01 _ ih => dsimp [wordScale, wordMass, wordMassQ]; push_cast at ih ⊢; linarith
  | d10 _ ih => dsimp [wordScale, wordMass, wordMassQ]; push_cast at ih ⊢; linarith
  | d11 _ ih => dsimp [wordScale, wordMass, wordMassQ]; push_cast at ih ⊢; linarith
theorem wordEffect_replicate_V_inv (p : Nat) :
    ∀ (n b : Nat) (v : WordList),
      WordEffect n (List.replicate p V) b v ->
      v = List.replicate p V /\ 1 + b = (1 + n) * 2 ^ p := by
  induction p with
  | zero =>
    intro n b v hI
    cases hI
    exact ⟨rfl, by simp⟩
  | succ p ih =>
    intro n b v hI
    cases hI with
    | T hSub =>
      rcases ih (1 + n * 2) b _ hSub with ⟨rfl, hEq⟩
      refine ⟨rfl, ?_⟩
      rw [Nat.pow_succ]; ring_nf at hEq ⊢; omega
theorem wordEffect_append_replicate_V_inv (u : WordList) :
    ∀ (p n b : Nat) (v : WordList),
      WordEffect n (u ++ List.replicate p V) b v ->
      ∃ w q, v = w ++ List.replicate p V /\ 1 + b = q * 2 ^ p := by
  induction u with
  | nil =>
    intro p n b v hI
    rcases wordEffect_replicate_V_inv p n b v hI with ⟨rfl, hEq⟩
    exact ⟨[], 1 + n, rfl, hEq⟩
  | cons x u ih =>
    intro p n b v hI
    cases hI with
    | T hSub =>
      rcases ih p (1 + n * 2) b _ hSub with ⟨w, q, rfl, hEq⟩
      exact ⟨V :: w, q, rfl, hEq⟩
    | d00 hSub =>
      rcases ih p _ b _ hSub with ⟨w, q, rfl, hEq⟩
      exact ⟨K :: w, q, rfl, hEq⟩
    | d01 hSub =>
      rcases ih p _ b _ hSub with ⟨w, q, rfl, hEq⟩
      exact ⟨Q :: w, q, rfl, hEq⟩
    | d10 hSub =>
      rcases ih p _ b _ hSub with ⟨w, q, rfl, hEq⟩
      exact ⟨Q :: w, q, rfl, hEq⟩
    | d11 hSub =>
      rcases ih p _ b _ hSub with ⟨w, q, rfl, hEq⟩
      exact ⟨K :: w, q, rfl, hEq⟩

end BusyBeaver.WordCalculus
