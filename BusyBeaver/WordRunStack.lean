/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Calculi.Counter
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordRunStack

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {Γ : Type*} [Inhabited Γ]

theorem append_assoc_blank (u v : List Γ) (lb : ListBlank Γ) :
    (u ++ v) +> lb = u +> (v +> lb) := by
  induction u with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

theorem nth_cons_zero (x : Γ) (t : ListBlank Γ) : (x >> t).nth 0 = x := by
  rw [ListBlank.nth_zero, ListBlank.head_cons]

theorem nth_cons_succ (x : Γ) (t : ListBlank Γ) (i : ℕ) : (x >> t).nth (i + 1) = t.nth i := by
  rw [ListBlank.nth_succ, ListBlank.tail_cons]

theorem nth_cons_one (x : Γ) (t : ListBlank Γ) : (x >> t).nth 1 = t.nth 0 :=
  nth_cons_succ x t 0

theorem nth_cons_two (x : Γ) (t : ListBlank Γ) : (x >> t).nth 2 = t.nth 1 :=
  nth_cons_succ x t 1

theorem nth_cons_three (x : Γ) (t : ListBlank Γ) : (x >> t).nth 3 = t.nth 2 :=
  nth_cons_succ x t 2

theorem nth_default : ∀ i : ℕ, (default : ListBlank Γ).nth i = default
  | 0 => by
      rw [ListBlank.nth_zero]
      exact ListBlank.head_mk []
  | i + 1 => by
      rw [ListBlank.nth_succ]
      have htail : (default : ListBlank Γ).tail = default := ListBlank.tail_mk []
      rw [htail]
      exact nth_default i

/-- Extracts the first `n` symbols of a `ListBlank Γ`. -/
def takeBlank {Γ : Type*} [Inhabited Γ] : ℕ → ListBlank Γ → List Γ
  | 0, _ => []
  | n + 1, lb => lb.head :: takeBlank n lb.tail

theorem takeBlank_length : ∀ (n : ℕ) (lb : ListBlank Γ), (takeBlank n lb).length = n
  | 0, _ => rfl
  | n + 1, lb => by
      simp only [takeBlank, List.length_cons, takeBlank_length n lb.tail]

theorem nth_takeBlank_append_of_lt :
    ∀ (n : ℕ) (lb : ListBlank Γ) (v : List Γ) (t : ListBlank Γ) (i : ℕ), i < n →
      ((takeBlank n lb ++ v) +> t).nth i = lb.nth i
  | 0, _, _, _, _, h => nomatch h
  | n + 1, lb, v, t, 0, _ => by
      simp only [takeBlank, List.cons_append, ListBlank.append]
      rw [nth_cons_zero, ListBlank.nth_zero]
  | n + 1, lb, v, t, i + 1, h => by
      simp only [takeBlank, List.cons_append, ListBlank.append]
      rw [nth_cons_succ, ListBlank.nth_succ]
      exact nth_takeBlank_append_of_lt n lb.tail v t i (Nat.lt_of_succ_lt_succ h)

theorem nth_takeBlank_append_add :
    ∀ (n : ℕ) (lb : ListBlank Γ) (v : List Γ) (t : ListBlank Γ) (j : ℕ),
      ((takeBlank n lb ++ v) +> t).nth (n + j) = (v +> t).nth j
  | 0, _, _, _, _ => by simp only [takeBlank, List.nil_append, Nat.zero_add]
  | n + 1, lb, v, t, j => by
      simp only [takeBlank, List.cons_append, ListBlank.append]
      rw [Nat.succ_add, nth_cons_succ]
      exact nth_takeBlank_append_add n lb.tail v t j

theorem nth_append_of_lt :
    ∀ (v : List Γ) (t : ListBlank Γ) (j : ℕ), j < v.length → (v +> t).nth j = v.getD j default
  | [], _, _, h => nomatch h
  | x :: v, t, 0, _ => by
      simp only [ListBlank.append, List.getD_cons_zero]
      exact nth_cons_zero x (v +> t)
  | x :: v, t, j + 1, h => by
      simp only [ListBlank.append, List.getD_cons_succ]
      rw [nth_cons_succ]
      exact nth_append_of_lt v t j (Nat.lt_of_succ_lt_succ h)

def NoFactor (pat : List Γ) (t : ListBlank Γ) : Prop :=
  ∀ i : ℕ, ¬ ∀ j : ℕ, j < pat.length → t.nth (i + j) = pat.getD j default

theorem noFactor_default (pat : List Γ) (j : ℕ) (hj : j < pat.length)
    (hne : pat.getD j default ≠ default) : NoFactor pat (default : ListBlank Γ) := by
  intro i h
  exact hne ((h j hj).symm.trans (nth_default (i + j)))

theorem noFactor_cons_of_nth_ne (pat : List Γ) (x : Γ) (t : ListBlank Γ) (ht : NoFactor pat t)
    (j : ℕ) (hj : j < pat.length) (hne : (x >> t).nth j ≠ pat.getD j default) :
    NoFactor pat (x >> t) := by
  intro i h
  cases i with
  | zero => exact hne (by simpa using h j hj)
  | succ i =>
      apply ht i
      intro j' hj'
      have := h j' hj'
      rwa [Nat.succ_add, nth_cons_succ] at this

theorem isNowhereDenseFamily_of_noFactor {S : Type*} (Valid : S → Prop) (enc : S → ListBlank Γ)
    (pat : List Γ) (hforb : ∀ s, Valid s → NoFactor pat (enc s)) :
    IsNowhereDenseFamily Valid enc := by
  intro s hs n
  refine ⟨(takeBlank n (enc s) ++ pat) +> default, ?_, ?_⟩
  · intro i hi
    exact nth_takeBlank_append_of_lt n _ pat default i hi
  · intro s' hs' heq
    apply hforb s' hs' n
    intro j hj
    rw [heq, nth_takeBlank_append_add, nth_append_of_lt pat default j hj]

theorem isNowhereDenseHalf_of_noFactor {S : Type*} (Valid : S → Prop)
    (segs : S → List (SegRegionKind Γ)) (pat : List Γ)
    (hforb : ∀ s, Valid s → NoFactor pat (evalSegmentedHalf (segs s))) :
    IsNowhereDenseHalf Valid segs :=
  isNowhereDenseFamily_of_noFactor Valid (fun s => evalSegmentedHalf (segs s)) pat hforb

end BusyBeaver.WordRunStack
