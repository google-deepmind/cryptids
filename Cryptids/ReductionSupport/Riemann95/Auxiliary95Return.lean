/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95
public import Cryptids.ReductionSupport.Riemann.WordGuard

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary.Return

open Turing ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1
  (append_replicate_cons append_cons_snoc append_replicate_zero_default
   default_cons_zero fin2_cases Tape.mkL)
open ConjectureMachines.Riemann120 (rootLeftOf stackLeftOf)
open ConjectureMachines.Riemann104.OnePassGuard (NoThreeZeros)

@[simp] theorem nSteps_zero (c : Cfg 98 2) : nSteps 0 c = some c := rfl
@[simp] theorem nSteps_succ (n : Nat) (c : Cfg 98 2) :
    nSteps (n + 1) c = (step machine c).bind (nSteps n) := rfl

theorem nSteps_add (m n : Nat) (c : Cfg 98 2) :
    nSteps (m + n) c = (nSteps m c).bind (nSteps n) := by
  induction m generalizing c with
  | zero => simp only [Nat.zero_add, nSteps_zero, Option.bind_some]
  | succ m ih =>
    simp only [Nat.succ_add, nSteps_succ, ih, Option.bind_assoc]

theorem nSteps_bind_eq {m n : Nat} {c c' c'' : Cfg 98 2}
    (h : nSteps m c = some c') (h' : nSteps n c' = some c'') :
    nSteps (m + n) c = some c'' := by rw [nSteps_add, h]; exact h'

theorem step_one {c c' : Cfg 98 2} (h : step machine c = some c') :
    nSteps 1 c = some c' := by simp only [nSteps_succ, h, Option.bind_some, nSteps_zero]

theorem step_nSteps {n : Nat} {c c' c'' : Cfg 98 2}
    (h : step machine c = some c') (h' : nSteps n c' = some c'') :
    nSteps (n + 1) c = some c'' := by simp only [nSteps_succ, h, Option.bind_some, h']

theorem step_mkL_left {q q' : Fin 98} {a b : Fin 2}
    (h : machine.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step machine ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 98} {a b : Fin 2}
    (h : machine.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step machine ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 98} {a b : Fin 2}
    (h : machine.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step machine ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem right_scan {q : Fin 98} {a b : Fin 2}
    (h : machine.transition q a = some (b, .right, q)) (k : Nat)
    (L R : ListBlank (Fin 2)) :
    nSteps k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

def scanState : Nat → Fin 98
  | 0 => 5
  | 1 => 7
  | _ => 10

theorem scan_rev (rev : List (Fin 2)) (z : Nat) (hz : z ≤ 2)
    (hok : NoThreeZeros (List.replicate z 0 ++ rev) = true) (R : ListBlank (Fin 2)) :
    ∃ z', z' ≤ 2 ∧
      nSteps rev.length ⟨scanState z, Tape.mkL (ListBlank.append rev default) R⟩ =
        some ⟨scanState z', Tape.mkL default (ListBlank.append rev.reverse R)⟩ := by
  induction rev generalizing z R with
  | nil => exact ⟨z, hz, rfl⟩
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · match z, hz with
      | 0, _ =>
        have hs : step machine ⟨5, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨7, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by decide) _ _
        obtain ⟨z', hz', ht⟩ := ih 1 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at ht
        exact ⟨z', hz', step_nSteps hs ht⟩
      | 1, _ =>
        have hs : step machine ⟨7, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨10, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by decide) _ _
        obtain ⟨z', hz', ht⟩ := ih 2 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at ht
        exact ⟨z', hz', step_nSteps hs ht⟩
      | 2, _ => cases hok
    · have ht : ∀ z₀, z₀ ≤ 2 →
          machine.transition (scanState z₀) 1 = some (1, .left, 5) := by decide
      have hs : step machine
          ⟨scanState z, Tape.mkL ((ListBlank.append xs default).cons 1) R⟩ =
            some ⟨5, Tape.mkL (ListBlank.append xs default) (R.cons 1)⟩ :=
        step_mkL_left (ht z hz) _ _
      have hok' : NoThreeZeros (List.replicate 0 0 ++ xs) = true := by
        match z, hz with
        | 0, _ => exact hok
        | 1, _ => exact hok
        | 2, _ => exact hok
      obtain ⟨z', hz', hrest⟩ := ih 0 (by decide) hok' (R.cons 1)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', step_nSteps hs hrest⟩

theorem scan_bounce_default (z : Nat) (hz : z ≤ 2) (R : ListBlank (Fin 2)) :
    nSteps (2 * (2 - z) + 1) ⟨scanState z, Tape.mkL default R⟩ =
      some ⟨12, Tape.mk' default R⟩ := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
    default_cons_zero.symm
  have hb : ∀ R' : ListBlank (Fin 2),
      nSteps 1 ⟨10, Tape.mkL default R'⟩ = some ⟨12, Tape.mk' default R'⟩ := by
    intro R'
    apply step_one
    conv_lhs => rw [hdef]
    rw [step_mkL_right (q := 10) (q' := 12) (a := 0) (b := 0) (by decide),
      default_cons_zero]
  match z, hz with
  | 2, _ => exact hb R
  | 1, _ =>
    have h1 : step machine ⟨7, Tape.mkL default R⟩ =
        some ⟨10, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by decide) default R
    have h2 := hb (R.cons 0)
    have h3 := right_scan (q := 12) (a := 0) (b := 0) (by decide) 1 default R
    rw [append_replicate_zero_default] at h3
    exact step_nSteps h1 (nSteps_bind_eq (m := 1) (n := 1) h2 h3)
  | 0, _ =>
    have h1 : step machine ⟨5, Tape.mkL default R⟩ =
        some ⟨7, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by decide) default R
    have h2 : step machine ⟨7, Tape.mkL default (R.cons 0)⟩ =
        some ⟨10, Tape.mkL default ((R.cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by decide) default _
    have h3 := hb ((R.cons 0).cons 0)
    have h4 := right_scan (q := 12) (a := 0) (b := 0) (by decide) 2 default R
    rw [append_replicate_zero_default] at h4
    exact step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq (m := 1) (n := 2) h3 h4))

theorem scan_root_marker (R : ListBlank (Fin 2)) :
    nSteps 1 ⟨12, Tape.mk' default (R.cons 1)⟩ =
      some ⟨15, Tape.mk' (ListBlank.cons 1 default) R⟩ :=
  step_one (step_mk'_right (by decide) _ _)


/-- The complete edited caller word, including its single-one root sentinel. -/
theorem stackLeft_word (word : List (Fin 2)) :
    stackLeftOf true word = ListBlank.append (1 :: word).reverse default := by
  simp [stackLeftOf, rootLeftOf, List.reverse_cons, ListBlank.append_assoc, ListBlank.append]

/-- Universal NoThree scanner for the exact98 table, with no leading gap. -/
theorem run_return98 (word : List (Fin 2))
    (hok : NoThreeZeros (1 :: word).reverse = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps s
      ⟨5, Tape.mkL (stackLeftOf true word) R⟩ =
        some ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append word R)⟩ := by
  obtain ⟨z, hz, hs⟩ := scan_rev (1 :: word).reverse 0 (by decide) hok R
  rw [List.reverse_reverse] at hs
  have hb := scan_bounce_default z hz (ListBlank.append (1 :: word) R)
  have hr := scan_root_marker (ListBlank.append word R)
  have htotal := nSteps_bind_eq hs (nSteps_bind_eq hb hr)
  refine ⟨(1 :: word).reverse.length + (2 * (2 - z) + 1 + 1), by omega, ?_⟩
  rw [stackLeft_word]
  exact htotal

/-- Peel the first state5/ONE self-step; root15 proves a positive remaining run. -/
theorem run_return98_after_one (word : List (Fin 2))
    (hok : NoThreeZeros (1 :: word).reverse = true)
    (hhead : (stackLeftOf true word).head = 1) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps s
      ⟨5, Tape.mkL (stackLeftOf true word).tail (R.cons 1)⟩ =
        some ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append word R)⟩ := by
  have hleft : ((stackLeftOf true word).tail).cons 1 = stackLeftOf true word := by
    rw [← hhead]
    exact ListBlank.cons_head_tail _
  have hfirst : step machine ⟨5, Tape.mkL (stackLeftOf true word) R⟩ =
      some ⟨5, Tape.mkL (stackLeftOf true word).tail (R.cons 1)⟩ := by
    simpa only [hleft] using
      step_mkL_left (q := 5) (q' := 5) (a := 1) (b := 1) (by decide)
        (stackLeftOf true word).tail R
  obtain ⟨s, hpos, hs⟩ := run_return98 word hok R
  cases s with
  | zero => omega
  | succ s =>
    rw [nSteps_succ, hfirst, Option.bind_some] at hs
    have hnonzero : s ≠ 0 := by
      intro hz
      rw [hz, nSteps_zero] at hs
      have heq := Option.some.inj hs
      have hbad : (5 : Fin 98) = 15 := congrArg Cfg.state heq
      norm_num at hbad
    exact ⟨s, by omega, hs⟩

end ConjectureMachines.Riemann95Auxiliary.Return
