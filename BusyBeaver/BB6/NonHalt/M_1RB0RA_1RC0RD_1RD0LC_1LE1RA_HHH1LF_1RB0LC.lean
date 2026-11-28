/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.ProofKit


/-!
# Busy Beaver Machine `1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.ProofKit`
and defines `target_tm` for `1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 2, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxRecDepth 4000

/-- Canonical E1 donor machine `#762` (`1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF`). -/
def tm762 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

/-- State bijection `σ : q_762 ↦ q_347` (`0↦2, 1↦3, 2↦4, 3↦5, 4↦1, 5↦0`, unmirrored `f = false`). -/
def isoPerm : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0

theorem tm347_iso_tm762 :
    ∀ (q : Fin 6) (a : Fin 2),
      target_tm (isoPerm q) a = (tm762 q a).map (Counter.conjOut isoPerm false)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 3, 0 => rfl
  | 3, 1 => rfl
  | 4, 0 => rfl
  | 4, 1 => rfl
  | 5, 0 => rfl
  | 5, 1 => rfl


-- ============================================================================
-- Section 1: Token Words, Hub Configurations, Events & Parametric Micro-Rules
-- ============================================================================

def w0 : List (Fin 2) := [0, 0, 0, 0]
def w1 : List (Fin 2) := [0, 1, 1]
def w2 : List (Fin 2) := [0, 0, 1, 1]
def w3 : List (Fin 2) := [0, 0, 0, 1]
def w4 : List (Fin 2) := [0, 0, 1]
def wE : List (Fin 2) := [1, 1]
def w5 : List (Fin 2) := [0, 0, 0, 1, 1]

def l00 : List (Fin 2) := [0, 0]
def l101 : List (Fin 2) := [1, 0, 1]
def l1111 : List (Fin 2) := [1, 1, 1, 1]
def l01111 : List (Fin 2) := [0, 1, 1, 1, 1]

/-- Right-moving hub configuration in state `F` (`5`). -/
def hF (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l {{5}}> r

/-- Left-moving hub configuration in state `A` (`0`). -/
def hA (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l <{{0}} r

theorem multiStep_trans_local {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)} {n m : ℕ}
    (h₁ : c₁ [tm762]⊢^{n} c₂) (h₂ : c₂ [tm762]⊢^{m} c₃) :
    c₁ [tm762]⊢^{n + m} c₃ :=
  Counter.multiStep_trans tm762 c₁ c₂ c₃ n m h₁ h₂

theorem stepPlus_trans_local {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [tm762]⊢⁺ c₂) (h₂ : c₂ [tm762]⊢⁺ c₃) :
    c₁ [tm762]⊢⁺ c₃ :=
  Counter.stepPlus_trans h₁ h₂

theorem w0_append_default : w0 +> (default : ListBlank (Fin 2)) = default := by
  simp only [w0, Counter.listblank_append_cons, Counter.listblank_append_nil,
    Counter.zero_cons_default]

local macro "run_micro" : tactic =>
  `(tactic| simp only [hF, hA, w0, w1, w2, w3, w4, wE, w5, l00, l101, l1111, l01111,
    Counter.listblank_append_cons, Counter.listblank_append_nil,
    BusyBeaver.multiStep_succ, BusyBeaver.multiStep_zero,
    Option.bind, step, tm762, Option.map,
    Tape.write, Turing.Tape.move, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, Counter.default_head, Counter.default_tail,
    Counter.zero_cons_default])

theorem micro_R1 (l r : ListBlank (Fin 2)) :
    (hF l (wE +> r)) [tm762]⊢⁺ hF (l00 +> l) r :=
  ⟨2, by decide, by run_micro⟩

theorem micro_R2 (l r : ListBlank (Fin 2)) :
    (hF l (w1 +> r)) [tm762]⊢⁺ hF (l101 +> l) r :=
  ⟨3, by decide, by run_micro⟩

theorem micro_R3 (l r : ListBlank (Fin 2)) :
    (hF l (w3 +> r)) [tm762]⊢⁺ hF (l1111 +> l) r :=
  ⟨4, by decide, by run_micro⟩

theorem micro_R4 (l r : ListBlank (Fin 2)) :
    (hF l (w2 +> r)) [tm762]⊢⁺ hA l (w3 +> r) :=
  ⟨5, by decide, by run_micro⟩

theorem micro_R5 (l r : ListBlank (Fin 2)) :
    (hF l (w4 +> ((0 : Fin 2) >> r))) [tm762]⊢⁺ hA l (w0 +> r) :=
  ⟨5, by decide, by run_micro⟩

theorem micro_R5_fuse (l r : ListBlank (Fin 2)) :
    (hF l (w4 +> (wE +> r))) [tm762]⊢⁺ hA l (w5 +> r) :=
  ⟨5, by decide, by run_micro⟩

theorem micro_R6 (l r : ListBlank (Fin 2)) :
    (hF l (w0 +> r)) [tm762]⊢⁺ hA l (w2 +> r) :=
  ⟨7, by decide, by run_micro⟩

theorem micro_R7 (l r : ListBlank (Fin 2)) :
    (hA (l101 +> l) r) [tm762]⊢⁺ hA l (w1 +> r) :=
  ⟨5, by decide, by run_micro⟩

theorem micro_R8 (l r : ListBlank (Fin 2)) :
    (hA (l1111 +> l) r) [tm762]⊢⁺ hA l (w0 +> r) :=
  ⟨4, by decide, by run_micro⟩

theorem micro_R9 (l r : ListBlank (Fin 2)) :
    (hA (l00 +> l) ((0 : Fin 2) >> r)) [tm762]⊢⁺ hF (l101 +> l) r :=
  ⟨6, by decide, by run_micro⟩

theorem micro_R10 (r : ListBlank (Fin 2)) :
    (hA default ((0 : Fin 2) >> r)) [tm762]⊢⁺ hF (l101 +> default) r :=
  ⟨6, by decide, by run_micro⟩

theorem micro_5_fwd (l r : ListBlank (Fin 2)) :
    (hF l (w5 +> r)) [tm762]⊢⁺ hF (l01111 +> l) r :=
  ⟨5, by decide, by run_micro⟩

theorem micro_5_ret (l r : ListBlank (Fin 2)) :
    (hA (l01111 +> l) ((0 : Fin 2) >> r)) [tm762]⊢⁺ hA l (w0 +> (wE +> r)) :=
  ⟨7, by decide, by run_micro⟩

/-- Right-tape event alphabet: `B` (parametric `hF -> hA` bounce) and `S` (leading `0` strip). -/
inductive Ev where
  | B
  | S

def StepEv : Ev → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | Ev.B, r, r' => ∀ l : ListBlank (Fin 2), (hF l r) [tm762]⊢⁺ hA l r'
  | Ev.S, r, r' => r = (0 : Fin 2) >> r'

inductive RunEv : List Ev → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | nil (r : ListBlank (Fin 2)) : RunEv [] r r
  | cons {e : Ev} {es : List Ev} {r₁ r₂ r₃ : ListBlank (Fin 2)} :
      StepEv e r₁ r₂ → RunEv es r₂ r₃ → RunEv (e :: es) r₁ r₃

theorem runEv_single {e : Ev} {r₁ r₂ : ListBlank (Fin 2)} (h : StepEv e r₁ r₂) :
    RunEv [e] r₁ r₂ :=
  RunEv.cons h (RunEv.nil r₂)

theorem runEv_append {xs ys : List Ev} {r₁ r₂ r₃ : ListBlank (Fin 2)}
    (hx : RunEv xs r₁ r₂) (hy : RunEv ys r₂ r₃) : RunEv (xs ++ ys) r₁ r₃ := by
  induction hx with
  | nil _ => exact hy
  | cons hstep _ ih => exact RunEv.cons hstep (ih hy)

theorem runEv_prefix {xs ys : List Ev} {r₁ r₃ : ListBlank (Fin 2)}
    (h : RunEv (xs ++ ys) r₁ r₃) : ∃ r₂, RunEv xs r₁ r₂ ∧ RunEv ys r₂ r₃ := by
  induction xs generalizing r₁ with
  | nil => exact ⟨r₁, RunEv.nil r₁, h⟩
  | cons e es ih =>
    cases h with
    | cons hstep hrest =>
      rcases ih hrest with ⟨r₂, hes, hys⟩
      exact ⟨r₂, RunEv.cons hstep hes, hys⟩

theorem stepEv_default_S : StepEv Ev.S (default : ListBlank (Fin 2)) default :=
  Counter.zero_cons_default.symm

-- Single-token `StepEv` lemmas (all parametric in arbitrary `r : ListBlank (Fin 2)`).
theorem stepEv_w0_B (r : ListBlank (Fin 2)) : StepEv Ev.B (w0 +> r) (w2 +> r) :=
  fun l => micro_R6 l r

theorem stepEv_w2_B (r : ListBlank (Fin 2)) : StepEv Ev.B (w2 +> r) (w3 +> r) :=
  fun l => micro_R4 l r

theorem stepEv_w3_B {r r' : ListBlank (Fin 2)} (h : StepEv Ev.B r r') :
    StepEv Ev.B (w3 +> r) (w0 +> r') :=
  fun l => stepPlus_trans_local (micro_R3 l r)
    (stepPlus_trans_local (h (l1111 +> l)) (micro_R8 l r'))

theorem stepEv_w1_B {r r' : ListBlank (Fin 2)} (h : StepEv Ev.B r r') :
    StepEv Ev.B (w1 +> r) (w1 +> r') :=
  fun l => stepPlus_trans_local (micro_R2 l r)
    (stepPlus_trans_local (h (l101 +> l)) (micro_R7 l r'))

theorem stepEv_w4_B {r r' : ListBlank (Fin 2)} (h : StepEv Ev.S r r') :
    StepEv Ev.B (w4 +> r) (w0 +> r') := by
  intro l
  rw [h]
  exact micro_R5 l r'

theorem stepEv_w4_wE_B (r : ListBlank (Fin 2)) :
    StepEv Ev.B (w4 +> (wE +> r)) (w5 +> r) :=
  fun l => micro_R5_fuse l r

theorem stepEv_wE_B {r r₁ r₂ r₃ : ListBlank (Fin 2)}
    (h1 : StepEv Ev.B r r₁) (h2 : StepEv Ev.S r₁ r₂) (h3 : StepEv Ev.B r₂ r₃) :
    StepEv Ev.B (wE +> r) (w1 +> r₃) := by
  intro l
  have s1 := micro_R1 l r
  have s2 := h1 (l00 +> l)
  rw [h2] at s2
  have s3 := micro_R9 l r₂
  have s4 := h3 (l101 +> l)
  have s5 := micro_R7 l r₃
  exact stepPlus_trans_local s1 (stepPlus_trans_local s2
    (stepPlus_trans_local s3 (stepPlus_trans_local s4 s5)))

theorem stepEv_w5_B {r r₁ r₂ : ListBlank (Fin 2)}
    (h1 : StepEv Ev.B r r₁) (h2 : StepEv Ev.S r₁ r₂) :
    StepEv Ev.B (w5 +> r) (w0 +> (wE +> r₂)) := by
  intro l
  have s1 := micro_5_fwd l r
  have s2 := h1 (l01111 +> l)
  rw [h2] at s2
  have s3 := micro_5_ret l r₂
  exact stepPlus_trans_local s1 (stepPlus_trans_local s2 s3)

theorem stepEv_w0_S {r r' : ListBlank (Fin 2)} (h : StepEv Ev.S r r') :
    StepEv Ev.S (w0 +> r) (w0 +> r') := by
  change w0 +> r = (0 : Fin 2) >> (w0 +> r')
  rw [h]
  rfl

theorem stepEv_w1_S (r : ListBlank (Fin 2)) : StepEv Ev.S (w1 +> r) (wE +> r) := rfl
theorem stepEv_w2_S (r : ListBlank (Fin 2)) : StepEv Ev.S (w2 +> r) (w1 +> r) := rfl
theorem stepEv_w3_S (r : ListBlank (Fin 2)) : StepEv Ev.S (w3 +> r) (w4 +> r) := rfl
theorem stepEv_w0_wE_S (r : ListBlank (Fin 2)) :
    StepEv Ev.S (w0 +> (wE +> r)) (w5 +> r) := rfl

--

-- ============================================================================
-- Section 3: Era Loop (`era_step`: `1^k ++ x_k ++ !` → `1^{k+1} ++ x_{k+1} ++ !`)
-- ============================================================================

def xk (k : ℕ) : List (Fin 2) := if k % 3 == 1 then w2 else w0

def eraCfg (k : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  hA default (w1 ^ k +> (xk k +> (wE +> r)))

theorem sweep_R2 (n : ℕ) (l r : ListBlank (Fin 2)) :
    (hF l (w1 ^ n +> r)) [tm762]⊢* hF (l101 ^ n +> l) r := by
  induction n generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 : (hF l (w1 ^ (n + 1) +> r)) [tm762]⊢⁺ hF (l101 +> l) (w1 ^ n +> r) := by
      rw [Counter.right_pow_succ]
      exact micro_R2 l (w1 ^ n +> r)
    have h2 := ih (l101 +> l)
    have heq : l101 ^ n +> (l101 +> l) = l101 ^ (n + 1) +> l := by
      rw [← Counter.listblank_append_assoc, ← Counter.pow_succ_right]
    rw [heq] at h2
    exact Counter.stepStar_trans (Counter.stepPlus_stepStar h1) h2

theorem sweep_R7 (n : ℕ) (l r : ListBlank (Fin 2)) :
    (hA (l101 ^ n +> l) r) [tm762]⊢* hA l (w1 ^ n +> r) := by
  induction n generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 : (hA (l101 ^ (n + 1) +> l) r) [tm762]⊢⁺ hA (l101 ^ n +> l) (w1 +> r) := by
      rw [Counter.right_pow_succ]
      exact micro_R7 (l101 ^ n +> l) r
    have h2 := ih (w1 +> r)
    have heq : w1 ^ n +> (w1 +> r) = w1 ^ (n + 1) +> r := by
      rw [← Counter.listblank_append_assoc, ← Counter.pow_succ_right]
    rw [heq] at h2
    exact Counter.stepStar_trans (Counter.stepPlus_stepStar h1) h2

theorem launch_era (k : ℕ) (t : ListBlank (Fin 2)) :
    (hA default (w1 ^ (k + 1) +> t)) [tm762]⊢⁺
      hF (l101 ^ k +> (l00 +> (l101 +> default))) t := by
  rw [Counter.right_pow_succ]
  have s1 : (hA default (w1 +> (w1 ^ k +> t))) [tm762]⊢⁺
      hF (l101 +> default) (wE +> (w1 ^ k +> t)) :=
    micro_R10 (wE +> (w1 ^ k +> t))
  have s2 := micro_R1 (l101 +> default) (w1 ^ k +> t)
  have s3 := sweep_R2 k (l00 +> (l101 +> default)) t
  exact Counter.stepPlus_stepStar_stepPlus (stepPlus_trans_local s1 s2) s3

theorem bounce_advance (a b : ℕ) (t : ListBlank (Fin 2)) :
    (hA (l101 ^ (b + 1) +> (l00 +> (l101 ^ a +> default))) t) [tm762]⊢⁺
      hF (l101 ^ b +> (l00 +> (l101 ^ (a + 1) +> default))) t := by
  have s1 := sweep_R7 (b + 1) (l00 +> (l101 ^ a +> default)) t
  have s2 : (hA (l00 +> (l101 ^ a +> default)) (w1 ^ (b + 1) +> t)) [tm762]⊢⁺
      hF (l101 +> (l101 ^ a +> default)) (wE +> (w1 ^ b +> t)) := by
    rw [Counter.right_pow_succ]
    exact micro_R9 (l101 ^ a +> default) (wE +> (w1 ^ b +> t))
  have heq : l101 +> (l101 ^ a +> default) = l101 ^ (a + 1) +> default :=
    (Counter.right_pow_succ l101 a default).symm
  rw [heq] at s2
  have s3 := micro_R1 (l101 ^ (a + 1) +> default) (w1 ^ b +> t)
  have s4 := sweep_R2 b (l00 +> (l101 ^ (a + 1) +> default)) t
  exact Counter.stepStar_stepPlus_stepPlus s1
    (Counter.stepPlus_stepStar_stepPlus (stepPlus_trans_local s2 s3) s4)

theorem loop_3b_one (a b : ℕ) {r r' : ListBlank (Fin 2)} (hB : StepEv Ev.B r r') :
    (hA (l101 ^ (b + 3) +> (l00 +> (l101 ^ a +> default))) (w0 +> (w1 +> r))) [tm762]⊢⁺
      hA (l101 ^ b +> (l00 +> (l101 ^ (a + 3) +> default))) (w0 +> (w1 +> r')) := by
  have s1 := bounce_advance a (b + 2) (w0 +> (w1 +> r))
  have s2 := micro_R6 (l101 ^ (b + 2) +> (l00 +> (l101 ^ (a + 1) +> default))) (w1 +> r)
  have s3 := bounce_advance (a + 1) (b + 1) (w2 +> (w1 +> r))
  have s4 := micro_R4 (l101 ^ (b + 1) +> (l00 +> (l101 ^ (a + 2) +> default))) (w1 +> r)
  have s5 := bounce_advance (a + 2) b (w3 +> (w1 +> r))
  have s6 : StepEv Ev.B (w3 +> (w1 +> r)) (w0 +> (w1 +> r')) :=
    stepEv_w3_B (stepEv_w1_B hB)
  have s6' := s6 (l101 ^ b +> (l00 +> (l101 ^ (a + 3) +> default)))
  exact stepPlus_trans_local s1 (stepPlus_trans_local s2
    (stepPlus_trans_local s3 (stepPlus_trans_local s4 (stepPlus_trans_local s5 s6'))))

theorem loop_3b (m a b : ℕ) {r r' : ListBlank (Fin 2)}
    (hBs : RunEv (List.replicate m Ev.B) r r') :
    (hA (l101 ^ (b + 3 * m) +> (l00 +> (l101 ^ a +> default))) (w0 +> (w1 +> r))) [tm762]⊢*
      hA (l101 ^ b +> (l00 +> (l101 ^ (a + 3 * m) +> default))) (w0 +> (w1 +> r')) := by
  induction m generalizing a r with
  | zero =>
    cases hBs
    simp
  | succ m ih =>
    rw [List.replicate_succ] at hBs
    cases hBs with
    | cons hB hrest =>
      rename_i r_mid
      have s1 : (hA (l101 ^ ((b + 3 * m) + 3) +> (l00 +> (l101 ^ a +> default))) (w0 +> (w1 +> r)))
          [tm762]⊢⁺
          hA (l101 ^ (b + 3 * m) +> (l00 +> (l101 ^ (a + 3) +> default))) (w0 +> (w1 +> r_mid)) :=
        loop_3b_one a (b + 3 * m) hB
      have s2 := ih (a + 3) hrest
      have hb : b + 3 * (m + 1) = (b + 3 * m) + 3 := by omega
      have ha : a + 3 * (m + 1) = (a + 3) + 3 * m := by omega
      rw [hb, ha]
      exact Counter.stepStar_trans (Counter.stepPlus_stepStar s1) s2

theorem finish_b0 (a : ℕ) (r : ListBlank (Fin 2)) :
    (hA (l00 +> (l101 ^ a +> default)) (w0 +> (w1 +> r))) [tm762]⊢⁺
      hA default (w1 ^ (a + 1) +> (w2 +> (wE +> r))) := by
  have hstrip : w0 +> (w1 +> r) = (0 : Fin 2) >> (w0 +> (wE +> r)) := rfl
  rw [hstrip]
  have s1 := micro_R9 (l101 ^ a +> default) (w0 +> (wE +> r))
  have heq : l101 +> (l101 ^ a +> default) = l101 ^ (a + 1) +> default :=
    (Counter.right_pow_succ l101 a default).symm
  rw [heq] at s1
  have s2 := micro_R6 (l101 ^ (a + 1) +> default) (wE +> r)
  have s3 := sweep_R7 (a + 1) default (w2 +> (wE +> r))
  exact Counter.stepPlus_stepStar_stepPlus (stepPlus_trans_local s1 s2) s3

theorem finish_b2 (a : ℕ) (r : ListBlank (Fin 2)) :
    (hA (l101 ^ 2 +> (l00 +> (l101 ^ a +> default))) (w0 +> (w1 +> r))) [tm762]⊢⁺
      hA default (w1 ^ (a + 3) +> (w0 +> (wE +> r))) := by
  have s1 := bounce_advance a 1 (w0 +> (w1 +> r))
  have s2 := micro_R6 (l101 ^ 1 +> (l00 +> (l101 ^ (a + 1) +> default))) (w1 +> r)
  have s3 := bounce_advance (a + 1) 0 (w2 +> (w1 +> r))
  have s4 := micro_R4 (l101 ^ 0 +> (l00 +> (l101 ^ (a + 2) +> default))) (w1 +> r)
  have s5 : (hA (l00 +> (l101 ^ (a + 2) +> default)) (w3 +> (w1 +> r))) [tm762]⊢⁺
      hF (l101 ^ (a + 3) +> default) (w4 +> (w1 +> r)) := by
    have hs := micro_R9 (l101 ^ (a + 2) +> default) (w4 +> (w1 +> r))
    have heq : l101 +> (l101 ^ (a + 2) +> default) = l101 ^ (a + 3) +> default :=
      (Counter.right_pow_succ l101 (a + 2) default).symm
    rw [heq] at hs
    exact hs
  have s6 : (hF (l101 ^ (a + 3) +> default) (w4 +> (w1 +> r))) [tm762]⊢⁺
      hA (l101 ^ (a + 3) +> default) (w0 +> (wE +> r)) :=
    micro_R5 (l101 ^ (a + 3) +> default) (wE +> r)
  have s7 := sweep_R7 (a + 3) default (w0 +> (wE +> r))
  exact Counter.stepPlus_stepStar_stepPlus
    (stepPlus_trans_local s1 (stepPlus_trans_local s2
      (stepPlus_trans_local s3 (stepPlus_trans_local s4 (stepPlus_trans_local s5 s6)))))
    s7

def eraEvents (k : ℕ) : List Ev := [Ev.B, Ev.S] ++ List.replicate (k / 3) Ev.B

theorem era_step (k : ℕ) (hk : 3 ≤ k) {r r' : ListBlank (Fin 2)}
    (hev : RunEv (eraEvents k) r r') :
    (eraCfg k r) [tm762]⊢⁺ eraCfg (k + 1) r' := by
  have hm_pos : 1 ≤ k / 3 := by omega
  set m := k / 3 - 1
  have hm : k / 3 = m + 1 := by omega
  have hev' : RunEv ([Ev.B, Ev.S, Ev.B] ++ List.replicate m Ev.B) r r' := by
    simpa [eraEvents, hm, List.replicate_succ] using hev
  rcases runEv_prefix hev' with ⟨r3, hbsb, hbm⟩
  cases hbsb with
  | cons hB1 hrest1 =>
    rename_i r1
    cases hrest1 with
    | cons hS hrest2 =>
      rename_i r2
      cases hrest2 with
      | cons hB2 hnil =>
        cases hnil
        have hrem : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases hrem with hr0 | hr1 | hr2
        · have hkeq : k = 3 * m + 3 := by omega
          have hxk : xk k = w0 := by simp [xk, hr0]
          have hxk1 : xk (k + 1) = w2 := by
            have : (k + 1) % 3 = 1 := by omega
            simp [xk, this]
          unfold eraCfg
          rw [hxk, hxk1, hkeq]
          have s1 := launch_era (3 * m + 2) (w0 +> (wE +> r))
          have s2 := micro_R6 (l101 ^ (3 * m + 2) +> (l00 +> (l101 +> default))) (wE +> r)
          have s3 := bounce_advance 1 (3 * m + 1) (w2 +> (wE +> r))
          have s4 := micro_R4 (l101 ^ (3 * m + 1) +> (l00 +> (l101 ^ 2 +> default))) (wE +> r)
          have s5 := bounce_advance 2 (3 * m) (w3 +> (wE +> r))
          have s6 := (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))
            (l101 ^ (3 * m) +> (l00 +> (l101 ^ 3 +> default)))
          have s7 := loop_3b m 3 0 hbm
          have s8 := finish_b0 (3 * m + 3) r'
          have h7_eq : 3 + 3 * m = 3 * m + 3 := by omega
          have hb_eq : 0 + 3 * m = 3 * m := by omega
          rw [hb_eq, h7_eq] at s7
          have h_l1 : l101 ^ 1 +> default = l101 +> default := by
            simp [Counter.pow_succ_list]
          rw [← h_l1] at s1 s2
          exact stepPlus_trans_local s1 (stepPlus_trans_local s2
            (stepPlus_trans_local s3 (stepPlus_trans_local s4
              (stepPlus_trans_local s5 (Counter.stepPlus_stepStar_stepPlus s6
                (Counter.stepStar_trans s7 (Counter.stepPlus_stepStar s8)))))))
        · have hkeq : k = 3 * m + 4 := by omega
          have hxk : xk k = w2 := by simp [xk, hr1]
          have hxk1 : xk (k + 1) = w0 := by
            have : (k + 1) % 3 = 2 := by omega
            simp [xk, this]
          unfold eraCfg
          rw [hxk, hxk1, hkeq]
          have s1 := launch_era (3 * m + 3) (w2 +> (wE +> r))
          have s2 := micro_R4 (l101 ^ (3 * m + 3) +> (l00 +> (l101 +> default))) (wE +> r)
          have s3 := bounce_advance 1 (3 * m + 2) (w3 +> (wE +> r))
          have s4 := (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))
            (l101 ^ (3 * m + 2) +> (l00 +> (l101 ^ 2 +> default)))
          have s5 := loop_3b m 2 2 hbm
          have s6 := finish_b2 (3 * m + 2) r'
          have h5_b : 2 + 3 * m = 3 * m + 2 := by omega
          rw [h5_b] at s5
          have h_l1 : l101 ^ 1 +> default = l101 +> default := by
            simp [Counter.pow_succ_list]
          rw [← h_l1] at s1 s2
          have hf_eq : 3 * m + 2 + 3 = 3 * m + 4 + 1 := by omega
          rw [hf_eq] at s6
          exact stepPlus_trans_local s1 (stepPlus_trans_local s2
            (stepPlus_trans_local s3 (Counter.stepPlus_stepStar_stepPlus s4
              (Counter.stepStar_trans s5 (Counter.stepPlus_stepStar s6)))))
        · have hkeq : k = 3 * m + 5 := by omega
          have hxk : xk k = w0 := by simp [xk, hr2]
          have hxk1 : xk (k + 1) = w0 := by
            have : (k + 1) % 3 = 0 := by omega
            simp [xk, this]
          unfold eraCfg
          rw [hxk, hxk1, hkeq]
          have s1 := launch_era (3 * m + 4) (w0 +> (wE +> r))
          have s2 := micro_R6 (l101 ^ (3 * m + 4) +> (l00 +> (l101 +> default))) (wE +> r)
          have s3 := bounce_advance 1 (3 * m + 3) (w2 +> (wE +> r))
          have s4 := micro_R4 (l101 ^ (3 * m + 3) +> (l00 +> (l101 ^ 2 +> default))) (wE +> r)
          have s5 := bounce_advance 2 (3 * m + 2) (w3 +> (wE +> r))
          have s6 := (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))
            (l101 ^ (3 * m + 2) +> (l00 +> (l101 ^ 3 +> default)))
          have s7 := loop_3b m 3 2 hbm
          have s8 := finish_b2 (3 * m + 3) r'
          have h7_b : 2 + 3 * m = 3 * m + 2 := by omega
          have h7_a : 3 + 3 * m = 3 * m + 3 := by omega
          rw [h7_b, h7_a] at s7
          have h_l1 : l101 ^ 1 +> default = l101 +> default := by
            simp [Counter.pow_succ_list]
          rw [← h_l1] at s1 s2
          have hf_eq : 3 * m + 3 + 3 = 3 * m + 5 + 1 := by omega
          rw [hf_eq] at s8
          exact stepPlus_trans_local s1 (stepPlus_trans_local s2
            (stepPlus_trans_local s3 (stepPlus_trans_local s4
              (stepPlus_trans_local s5 (Counter.stepPlus_stepStar_stepPlus s6
                (Counter.stepStar_trans s7 (Counter.stepPlus_stepStar s8)))))))

-- ============================================================================
-- Section 4: Pure Rational `AdjGoodFrom`, Discreteness Lemma & Gap Events
-- ============================================================================

def nextP (p : ℚ) (g : ℕ) : ℚ := (g : ℚ) + p / 3

def endP (p : ℚ) : List ℕ → ℚ
  | [] => p
  | g :: gs => endP (nextP p g) gs

def AdjGoodFrom (p : ℚ) : List ℕ → Prop
  | [] => True
  | g :: gs => 2 * p ≤ 3 * (g : ℚ) + 3 ∧ AdjGoodFrom (nextP p g) gs

def Good (gs : List ℕ) : Prop := AdjGoodFrom 0 gs

theorem endP_append (p : ℚ) (xs ys : List ℕ) :
    endP p (xs ++ ys) = endP (endP p xs) ys := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => exact ih (nextP p x)

theorem adjGood_append {p : ℚ} {xs ys : List ℕ}
    (hx : AdjGoodFrom p xs) (hy : AdjGoodFrom (endP p xs) ys) :
    AdjGoodFrom p (xs ++ ys) := by
  induction xs generalizing p with
  | nil => exact hy
  | cons x xs ih =>
    rcases hx with ⟨h1, hrest⟩
    exact ⟨h1, ih hrest hy⟩

theorem adjGood_implies_bound {p : ℚ} {gs : List ℕ} (h : AdjGoodFrom p gs) :
    ∀ x ∈ gs, 2 * p ≤ 3 * (x : ℚ) + 3 := by
  induction gs generalizing p with
  | nil => intro x hx; cases hx
  | cons g rest ih =>
    rcases h with ⟨h1, hrest⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact h1
    · have hih := ih hrest x hmem
      unfold nextP at hih
      rcases Nat.lt_or_ge g (x + 1) with hle | hge
      · have hle' : (g : ℚ) ≤ (x : ℚ) := by exact_mod_cast (Nat.lt_succ_iff.mp hle)
        linarith
      · have hge' : (x : ℚ) + 1 ≤ (g : ℚ) := by exact_mod_cast hge
        linarith

theorem adjGood_no_zero_of_gt {p : ℚ} {gs : List ℕ} (h : AdjGoodFrom p gs) (hp : 3 < 2 * p) :
    ∀ x ∈ gs, 1 ≤ x := by
  intro x hx
  have hb := adjGood_implies_bound h x hx
  cases x with
  | zero => simp at hb; linarith
  | succ _ => omega

def gapEv (g : ℕ) : List Ev := List.replicate g Ev.B ++ [Ev.S]

def gapsEv : List ℕ → List Ev
  | [] => []
  | g :: gs => gapEv g ++ gapsEv gs

theorem gapsEv_append (xs ys : List ℕ) : gapsEv (xs ++ ys) = gapsEv xs ++ gapsEv ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [gapsEv, ih, List.append_assoc]

def isAllPos : List ℕ → Bool
  | [] => true
  | 0 :: _ => false
  | (_ + 1) :: gs => isAllPos gs

theorem isAllPos_eq_true_iff {gs : List ℕ} :
    isAllPos gs = true ↔ ∀ x ∈ gs, 1 ≤ x := by
  induction gs with
  | nil => simp [isAllPos]
  | cons g rest ih =>
    cases g with
    | zero => simp [isAllPos]
    | succ n => simp [isAllPos, ih]

def stripLZ : List ℕ → List ℕ
  | [] => []
  | 0 :: gs => stripLZ gs
  | (n + 1) :: gs => (n + 1) :: gs

theorem stripLZ_zeros_append (zs gs : List ℕ) (hz : ∀ x ∈ zs, x = 0) :
    stripLZ (zs ++ gs) = stripLZ gs := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have h0 : z = 0 := hz z (by simp)
    subst h0
    exact ih (fun x hx => hz x (by simp [hx]))

def isSafeZero (gs : List ℕ) : Bool :=
  match stripLZ gs with
  | [] => true
  | 1 :: 0 :: rest => isAllPos rest
  | rest => isAllPos rest

theorem isSafeZero_of_allPos {gs : List ℕ} (h : ∀ x ∈ gs, 1 ≤ x) :
    isSafeZero gs = true := by
  cases gs with
  | nil => rfl
  | cons g rest =>
    cases g with
    | zero => exact absurd (h 0 (by simp)) (by decide)
    | succ n =>
      have hpos : isAllPos rest = true :=
        isAllPos_eq_true_iff.mpr (fun x hx => h x (by simp [hx]))
      cases n with
      | zero =>
        cases rest with
        | nil => rfl
        | cons r rs =>
          cases r with
          | zero => exact absurd (h 0 (by simp)) (by decide)
          | succ m =>
            simp only [isSafeZero, stripLZ, isAllPos]
            exact isAllPos_eq_true_iff.mpr (fun x hx => h x (by simp [hx]))
      | succ n' =>
        simp [isSafeZero, stripLZ, isAllPos, hpos]

theorem isSafeZero_zeros_append {zs gs : List ℕ} (hz : ∀ x ∈ zs, x = 0)
    (h : isSafeZero gs = true) : isSafeZero (zs ++ gs) = true := by
  unfold isSafeZero
  rw [stripLZ_zeros_append zs gs hz]
  exact h

-- Multi-`B` lift helpers on single tokens.
theorem runEv_w0_B3 {r r' : ListBlank (Fin 2)} (h : StepEv Ev.B r r') :
    RunEv [Ev.B, Ev.B, Ev.B] (w0 +> r) (w0 +> r') :=
  RunEv.cons (stepEv_w0_B r)
    (RunEv.cons (stepEv_w2_B r)
      (RunEv.cons (stepEv_w3_B h) (RunEv.nil _)))

theorem runEv_w0_B3q (q : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (List.replicate q Ev.B) r r') :
    RunEv (List.replicate (3 * q) Ev.B) (w0 +> r) (w0 +> r') := by
  induction q generalizing r with
  | zero =>
    cases h
    exact RunEv.nil _
  | succ q ih =>
    rw [List.replicate_succ] at h
    cases h with
    | cons hB hrest =>
      have heq : List.replicate (3 * (q + 1)) Ev.B = [Ev.B, Ev.B, Ev.B] ++ List.replicate (3 * q)
        Ev.B := by
        have : 3 * (q + 1) = 3 + 3 * q := by omega
        (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
      rw [heq]
      exact runEv_append (runEv_w0_B3 hB) (ih hrest)

theorem runEv_w1_Bk (k : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (List.replicate k Ev.B) r r') :
    RunEv (List.replicate k Ev.B) (w1 +> r) (w1 +> r') := by
  induction k generalizing r with
  | zero =>
    cases h
    exact RunEv.nil _
  | succ k ih =>
    rw [List.replicate_succ] at h
    cases h with
    | cons hB hrest =>
      rw [List.replicate_succ]
      exact RunEv.cons (stepEv_w1_B hB) (ih hrest)

theorem run_B_only : ∀ t : ℕ, ∃ r', RunEv (List.replicate t Ev.B) default r' := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => exact ⟨default, RunEv.nil default⟩
    | succ t' =>
      set n := t' + 1
      have hq_lt : n / 3 < n := by omega
      rcases ih (n / 3) hq_lt with ⟨r1, hr1⟩
      have hmain := runEv_w0_B3q (n / 3) hr1
      rw [w0_append_default] at hmain
      have hrem : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hn : n = 3 * (n / 3) := by omega
        rw [hn]; exact ⟨w0 +> r1, hmain⟩
      · have hn : List.replicate n Ev.B = List.replicate (3 * (n / 3)) Ev.B ++ [Ev.B] := by
          have : n = 3 * (n / 3) + 1 := by omega
          (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
        rw [hn]
        exact ⟨w2 +> r1, runEv_append hmain (runEv_single (stepEv_w0_B r1))⟩
      · have hn : List.replicate n Ev.B = List.replicate (3 * (n / 3)) Ev.B ++ [Ev.B, Ev.B] := by
          have : n = 3 * (n / 3) + 2 := by omega
          (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
        rw [hn]
        exact ⟨w3 +> r1, runEv_append hmain
          (RunEv.cons (stepEv_w0_B r1) (runEv_single (stepEv_w2_B r1)))⟩

-- ============================================================================
-- Section 5: 1-Cell Peeling Transducer (`peel1`)
-- ============================================================================

inductive St1 where
  | s0
  | s4
  | s1
  | sE

def tok1 : St1 → List (Fin 2)
  | .s0 => w0
  | .s4 => w4
  | .s1 => w1
  | .sE => wE

def def1 : St1 → ℕ
  | .s0 => 0
  | .s4 => 1
  | .s1 => 1
  | .sE => 2

def step1 (st : St1) (c g : ℕ) : St1 × ℕ × List ℕ :=
  match st with
  | .s0 =>
    if g % 3 == 0 then (.s0, 0, [c + g / 3])
    else if g % 3 == 1 then (.s1, c + g / 3, [])
    else (.s4, c + g / 3, [])
  | .s4 =>
    match g with
    | 0 => (.s4, c, [])
    | g' + 1 =>
      if g' % 3 == 0 then (.s0, 0, [c, g' / 3])
      else if g' % 3 == 1 then (.s1, g' / 3, [c])
      else (.s4, g' / 3, [c])
  | .s1 => (.sE, c + g, [])
  | .sE =>
    match g with
    | 0 => (.sE, c, [])
    | g' + 1 => (.sE, g' + 1, [c + 1])

def run1Aux : St1 → ℕ → List ℕ → St1 × ℕ × List ℕ
  | st, c, [] => (st, c, [])
  | st, c, g :: gs =>
    let r1 := step1 st c g
    let r2 := run1Aux r1.1 r1.2.1 gs
    (r2.1, r2.2.1, r1.2.2 ++ r2.2.2)

def step1Tail (st : St1) (c t : ℕ) : List ℕ × ℕ :=
  match st with
  | .s0 => ([], c + t / 3)
  | .s4 => match t with | 0 => ([], c) | t' + 1 => ([c], t' / 3)
  | .s1 => ([], c + t)
  | .sE => match t with | 0 => ([], c) | t' + 1 => ([c + 1], t' + 1)

def run1Full (st : St1) (c : ℕ) (gs : List ℕ) (t : ℕ) : List ℕ × ℕ :=
  let r := run1Aux st c gs
  let rt := step1Tail r.1 r.2.1 t
  (r.2.2 ++ rt.1, rt.2)

def step1Ev (st : St1) (g : ℕ) : List Ev :=
  match st with
  | .s0 =>
    if g % 3 == 0 then List.replicate (g / 3) Ev.B ++ [Ev.S]
    else List.replicate (g / 3) Ev.B
  | .s4 =>
    match g with
    | 0 => []
    | g' + 1 =>
      Ev.S :: (if g' % 3 == 0 then List.replicate (g' / 3) Ev.B ++ [Ev.S]
             else List.replicate (g' / 3) Ev.B)
  | .s1 => List.replicate g Ev.B
  | .sE =>
    match g with
    | 0 => []
    | g' + 1 => Ev.B :: Ev.S :: List.replicate (g' + 1) Ev.B

def step1TailEv (st : St1) (t : ℕ) : List Ev :=
  match st with
  | .s0 => List.replicate (t / 3) Ev.B
  | .s4 => match t with | 0 => [] | t' + 1 => Ev.S :: List.replicate (t' / 3) Ev.B
  | .s1 => List.replicate t Ev.B
  | .sE => match t with | 0 => [] | t' + 1 => Ev.B :: Ev.S :: List.replicate (t' + 1) Ev.B

def run1Evs : St1 → List ℕ → ℕ → List Ev
  | st, [], t => step1TailEv st t
  | st, g :: gs, t => step1Ev st g ++ run1Evs (step1 st 0 g).1 gs t

theorem step1_next_indep_c (st : St1) (c g : ℕ) : (step1 st c g).1 = (step1 st 0 g).1 := by
  cases st with
  | s0 =>
    simp only [step1]; split <;> [rfl; split <;> rfl]
  | s4 =>
    cases g with
    | zero => rfl
    | succ g' => simp only [step1]; split <;> [rfl; split <;> rfl]
  | s1 => rfl
  | sE => cases g <;> rfl

theorem rep_B_step1Ev (st : St1) (c g : ℕ) (hg : (st = .s4 ∨ st = .sE) → 1 ≤ g) :
    List.replicate c Ev.B ++ step1Ev st g =
      gapsEv (step1 st c g).2.2 ++ List.replicate (step1 st c g).2.1 Ev.B := by
  cases st with
  | s0 =>
    simp only [step1Ev, step1]
    have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
    rcases hrem with h0 | h1 | h2
    · simp only [h0, beq_self_eq_true, ↓reduceIte, gapsEv, gapEv, List.replicate_zero,
        List.append_nil, List.replicate_add, List.append_assoc]
    · have hne0 : (1 == 0) = false := rfl
      simp only [h1, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, gapsEv,
        List.nil_append, List.replicate_add]
    · have hne0 : (2 == 0) = false := rfl
      have hne1 : (2 == 1) = false := rfl
      simp only [h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte, gapsEv, List.nil_append,
        List.replicate_add]
  | s4 =>
    cases g with
    | zero => exact absurd (hg (Or.inl rfl)) (by decide)
    | succ g' =>
      simp only [step1Ev, step1]
      have hrem : g' % 3 = 0 ∨ g' % 3 = 1 ∨ g' % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · simp only [h0, beq_self_eq_true, ↓reduceIte, gapsEv, gapEv, List.replicate_zero,
          List.nil_append, List.append_nil, List.cons_append, List.append_assoc]
      · have hne0 : (1 == 0) = false := rfl
        simp only [h1, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, gapsEv, gapEv,
          List.nil_append, List.append_nil, List.cons_append, List.append_assoc]
      · have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte, gapsEv, gapEv, List.nil_append,
          List.append_nil, List.cons_append, List.append_assoc]
  | s1 =>
    simp only [step1Ev, step1, gapsEv, List.nil_append, List.replicate_add]
  | sE =>
    cases g with
    | zero => exact absurd (hg (Or.inr rfl)) (by decide)
    | succ g' =>
      simp only [step1Ev, step1, gapsEv, gapEv, List.append_nil]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem rep_B_step1TailEv (st : St1) (c t : ℕ) :
    List.replicate c Ev.B ++ step1TailEv st t =
      gapsEv (step1Tail st c t).1 ++ List.replicate (step1Tail st c t).2 Ev.B := by
  cases st with
  | s0 => simp only [step1TailEv, step1Tail, gapsEv, List.nil_append, List.replicate_add]
  | s4 =>
    cases t with
    | zero => simp [step1TailEv, step1Tail, gapsEv]
    | succ t' => simp [step1TailEv, step1Tail, gapsEv, gapEv, List.append_assoc]
  | s1 => simp only [step1TailEv, step1Tail, gapsEv, List.nil_append, List.replicate_add]
  | sE =>
    cases t with
    | zero => simp [step1TailEv, step1Tail, gapsEv]
    | succ t' =>
      simp only [step1TailEv, step1Tail, gapsEv, gapEv, List.append_nil]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]

def Safe1 : St1 → List ℕ → Prop
  | _, [] => True
  | st, g :: gs =>
    ((st = .s4 ∨ st = .sE) → 1 ≤ g) ∧ Safe1 (step1 st 0 g).1 gs

theorem safe1_of_allPos (st : St1) (gs : List ℕ) (h : ∀ x ∈ gs, 1 ≤ x) : Safe1 st gs := by
  induction gs generalizing st with
  | nil => trivial
  | cons g rest ih =>
    exact ⟨fun _ => h g (by simp), ih _ (fun x hx => h x (by simp [hx]))⟩

theorem rep_B_run1Evs (st : St1) (c : ℕ) (gs : List ℕ) (t : ℕ) (hs : Safe1 st gs) :
    List.replicate c Ev.B ++ run1Evs st gs t =
      gapsEv (run1Full st c gs t).1 ++ List.replicate (run1Full st c gs t).2 Ev.B := by
  induction gs generalizing st c with
  | nil =>
    simp only [run1Evs, run1Full, run1Aux, List.nil_append]
    exact rep_B_step1TailEv st c t
  | cons g rest ih =>
    rcases hs with ⟨hg, hrest⟩
    simp only [run1Evs, run1Full, run1Aux]
    rw [← List.append_assoc, rep_B_step1Ev st c g hg, List.append_assoc]
    rw [← step1_next_indep_c st c g] at hrest
    rw [← step1_next_indep_c st c g]
    have hih := ih (step1 st c g).1 (step1 st c g).2.1 hrest
    simp only [run1Full] at hih
    rw [hih]; simp only [gapsEv_append, List.append_assoc]

theorem lift1_s0_step (g : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (step1Ev .s0 g) r r') :
    RunEv (gapEv g) (w0 +> r) (tok1 (step1 .s0 0 g).1 +> r') := by
  have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
  rcases hrem with h0 | h1 | h2
  · have hq : g = 3 * (g / 3) := by omega
    simp only [step1Ev, h0, beq_self_eq_true, ↓reduceIte] at h
    simp only [step1, h0, beq_self_eq_true, ↓reduceIte, tok1]
    rcases runEv_prefix h with ⟨r1, hB, hS⟩
    cases hS with
    | cons hs hnil =>
      cases hnil
      have hge : gapEv g = List.replicate (3 * (g / 3)) Ev.B ++ [Ev.S] := by
        unfold gapEv; (conv_lhs => rw [hq])
      rw [hge]
      exact runEv_append (runEv_w0_B3q (g / 3) hB) (runEv_single (stepEv_w0_S hs))
  · have hq : g = 3 * (g / 3) + 1 := by omega
    simp only [step1Ev, h1] at h
    have hne : (1 == 0) = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    simp only [step1, h1, tok1]
    have hge : gapEv g = List.replicate (3 * (g / 3)) Ev.B ++ [Ev.B, Ev.S] := by
      unfold gapEv; (conv_lhs => rw [hq]); rw [List.replicate_add, List.append_assoc]; rfl
    rw [hge]
    exact runEv_append (runEv_w0_B3q (g / 3) h)
      (RunEv.cons (stepEv_w0_B r') (runEv_single (stepEv_w2_S r')))
  · have hq : g = 3 * (g / 3) + 2 := by omega
    simp only [step1Ev, h2] at h
    have hne : (2 == 0) = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    simp only [step1, h2, tok1]
    have hge : gapEv g = List.replicate (3 * (g / 3)) Ev.B ++ [Ev.B, Ev.B, Ev.S] := by
      unfold gapEv; (conv_lhs => rw [hq]); rw [List.replicate_add, List.append_assoc]; rfl
    rw [hge]
    exact runEv_append (runEv_w0_B3q (g / 3) h)
      (RunEv.cons (stepEv_w0_B r')
        (RunEv.cons (stepEv_w2_B r') (runEv_single (stepEv_w3_S r'))))

theorem lift1_step (st : St1) (g : ℕ) (hg : (st = .s4 ∨ st = .sE) → 1 ≤ g)
    {r r' : ListBlank (Fin 2)} (h : RunEv (step1Ev st g) r r') :
    RunEv (gapEv g) (tok1 st +> r) (tok1 (step1 st 0 g).1 +> r') := by
  cases st with
  | s0 => exact lift1_s0_step g h
  | s4 =>
    cases g with
    | zero => exact absurd (hg (Or.inl rfl)) (by decide)
    | succ g' =>
      simp only [step1Ev] at h
      cases h with
      | cons hS hrest =>
        rename_i r1
        have hs1 : StepEv Ev.B (w4 +> r) (w0 +> r1) := stepEv_w4_B hS
        have hgap : gapEv (g' + 1) = Ev.B :: gapEv g' := by
          simp [gapEv, List.replicate_succ]
        rw [hgap]
        have hlift : RunEv (gapEv g') (w0 +> r1) (tok1 (step1 .s0 0 g').1 +> r') :=
          lift1_s0_step g' hrest
        have heq_st : (step1 .s4 0 (g' + 1)).1 = (step1 .s0 0 g').1 := by
          simp only [step1]; split <;> [rfl; split <;> rfl]
        rw [heq_st]
        exact RunEv.cons hs1 hlift
  | s1 =>
    simp only [step1Ev] at h
    simp only [step1, tok1, gapEv]
    exact runEv_append (runEv_w1_Bk g h) (runEv_single (stepEv_w1_S r'))
  | sE =>
    cases g with
    | zero => exact absurd (hg (Or.inr rfl)) (by decide)
    | succ g' =>
      simp only [step1Ev] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS h2 =>
          rw [List.replicate_succ] at h2
          cases h2 with
          | cons hB2 hrest =>
            have hs1 : StepEv Ev.B (wE +> r) (w1 +> _) := stepEv_wE_B hB1 hS hB2
            have hgap : gapEv (g' + 1) = Ev.B :: (List.replicate g' Ev.B ++ [Ev.S]) := by
              simp [gapEv, List.replicate_succ]
            rw [hgap]
            exact RunEv.cons hs1
              (runEv_append (runEv_w1_Bk g' hrest) (runEv_single (stepEv_w1_S r')))

theorem lift1_tail (st : St1) (t : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (step1TailEv st t) r r') :
    ∃ r_out, RunEv (List.replicate t Ev.B) (tok1 st +> r) r_out := by
  cases st with
  | s0 =>
    simp only [step1TailEv] at h
    have hrem : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases hrem with h0 | h1 | h2
    · have ht : t = 3 * (t / 3) := by omega
      rw [ht]; exact ⟨w0 +> r', runEv_w0_B3q (t / 3) h⟩
    · have ht : List.replicate t Ev.B = List.replicate (3 * (t / 3)) Ev.B ++ [Ev.B] := by
        have : t = 3 * (t / 3) + 1 := by omega
        (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
      rw [ht]; exact ⟨w2 +> r', runEv_append (runEv_w0_B3q (t / 3) h) (runEv_single (stepEv_w0_B
        r'))⟩
    · have ht : List.replicate t Ev.B = List.replicate (3 * (t / 3)) Ev.B ++ [Ev.B, Ev.B] := by
        have : t = 3 * (t / 3) + 2 := by omega
        (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
      rw [ht]; exact ⟨w3 +> r', runEv_append (runEv_w0_B3q (t / 3) h)
        (RunEv.cons (stepEv_w0_B r') (runEv_single (stepEv_w2_B r')))⟩
  | s4 =>
    cases t with
    | zero => exact ⟨w4 +> r, RunEv.nil _⟩
    | succ t' =>
      simp only [step1TailEv] at h
      cases h with
      | cons hS hrest =>
        have hrem : t' % 3 = 0 ∨ t' % 3 = 1 ∨ t' % 3 = 2 := by omega
        rw [List.replicate_succ]
        rcases hrem with h0 | h1 | h2
        · have ht : t' = 3 * (t' / 3) := by omega
          rw [ht]
          exact ⟨w0 +> r', RunEv.cons (stepEv_w4_B hS) (runEv_w0_B3q (t' / 3) hrest)⟩
        · have ht : List.replicate t' Ev.B = List.replicate (3 * (t' / 3)) Ev.B ++ [Ev.B] := by
            have : t' = 3 * (t' / 3) + 1 := by omega
            (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
          rw [ht]
          exact ⟨w2 +> r', RunEv.cons (stepEv_w4_B hS)
            (runEv_append (runEv_w0_B3q (t' / 3) hrest) (runEv_single (stepEv_w0_B r')))⟩
        · have ht : List.replicate t' Ev.B = List.replicate (3 * (t' / 3)) Ev.B ++ [Ev.B, Ev.B] :=
            by
            have : t' = 3 * (t' / 3) + 2 := by omega
            (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
          rw [ht]
          exact ⟨w3 +> r', RunEv.cons (stepEv_w4_B hS)
            (runEv_append (runEv_w0_B3q (t' / 3) hrest)
              (RunEv.cons (stepEv_w0_B r') (runEv_single (stepEv_w2_B r'))))⟩
  | s1 =>
    simp only [step1TailEv] at h
    exact ⟨w1 +> r', runEv_w1_Bk t h⟩
  | sE =>
    cases t with
    | zero => exact ⟨wE +> r, RunEv.nil _⟩
    | succ t' =>
      simp only [step1TailEv] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS h2 =>
          rw [List.replicate_succ] at h2
          cases h2 with
          | cons hB2 hrest =>
            rw [List.replicate_succ]
            exact ⟨w1 +> r', RunEv.cons (stepEv_wE_B hB1 hS hB2) (runEv_w1_Bk t' hrest)⟩

theorem lift1_run (st : St1) (gs : List ℕ) (t : ℕ) (hs : Safe1 st gs)
    {r r' : ListBlank (Fin 2)} (h : RunEv (run1Evs st gs t) r r') :
    ∃ r_out, RunEv (gapsEv gs ++ List.replicate t Ev.B) (tok1 st +> r) r_out := by
  induction gs generalizing st r with
  | nil =>
    simp only [gapsEv, List.nil_append]
    exact lift1_tail st t h
  | cons g rest ih =>
    rcases hs with ⟨hg, hrest⟩
    simp only [run1Evs] at h
    rcases runEv_prefix h with ⟨r1, hstep, htail⟩
    have hl := lift1_step st g hg hstep
    rcases ih (step1 st 0 g).1 hrest htail with ⟨r_out, hrest_run⟩
    exact ⟨r_out, by
      simp only [gapsEv, List.append_assoc]
      exact runEv_append hl hrest_run⟩

-- Invariant `Inv1` proving `AdjGoodFrom` for `peel1` in one pass!
def Inv1 (st : St1) (c : ℕ) (po pi : ℚ) : Prop :=
  0 ≤ po ∧ 0 ≤ pi ∧
  match st with
  | .s0 => c = 0 ∧ 3 * po ≤ pi
  | .s4 => 2 ≤ pi ∧ 3 * (c : ℚ) + po ≤ pi - 2 ∧ 2 * po ≤ 3 * (c : ℚ) + 3
  | .s1 => 1 ≤ pi ∧ 3 * (c : ℚ) + po ≤ pi - 1
  | .sE => 3 * (c : ℚ) + po ≤ 3 * pi + 3 / 2 ∧ 2 * po ≤ 3 * (c : ℚ) + 6

theorem inv1_step (st : St1) (c g : ℕ) (po pi : ℚ)
    (hinv : Inv1 st c po pi) (hgood : 2 * pi ≤ 3 * (g : ℚ) + 3)
    (hgE : st = .sE → 1 ≤ g) :
    ((st = .s4 ∨ st = .sE) → 1 ≤ g) ∧
    AdjGoodFrom po (step1 st c g).2.2 ∧
    Inv1 (step1 st c g).1 (step1 st c g).2.1
      (endP po (step1 st c g).2.2) (nextP pi g) := by
  rcases hinv with ⟨hpo0, hpi0, hst⟩
  cases st with
  | s0 =>
    rcases hst with ⟨rfl, hle⟩
    have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
    rcases hrem with h0 | h1 | h2
    · have hq : g = 3 * (g / 3) := by omega
      have hqQ : (g : ℚ) = 3 * ((g / 3 : ℕ) : ℚ) := by exact_mod_cast hq
      simp only [step1, h0, beq_self_eq_true, ↓reduceIte, Nat.zero_add, endP, nextP, Inv1,
        AdjGoodFrom]
      refine ⟨(fun h => by rcases h with h | h <;> cases h),
        ⟨by linarith, trivial⟩, ?_, ?_, trivial, ?_⟩
      · have : (0 : ℚ) ≤ ((g / 3 : ℕ) : ℚ) := Nat.cast_nonneg _; linarith
      · have : (0 : ℚ) ≤ (g : ℚ) := Nat.cast_nonneg _; linarith
      · linarith
    · have hq : g = 3 * (g / 3) + 1 := by omega
      have hqQ : (g : ℚ) = 3 * ((g / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
      have hne0 : (1 == 0) = false := rfl
      simp only [step1, h1, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Nat.zero_add,
        endP, nextP, Inv1, AdjGoodFrom]
      have hg1 : (1 : ℚ) ≤ (g : ℚ) := by
        have : 1 ≤ g := by omega
        exact_mod_cast this
      exact ⟨(fun h => by rcases h with h | h <;> cases h), trivial,
        hpo0, by linarith, by linarith, by linarith⟩
    · have hq : g = 3 * (g / 3) + 2 := by omega
      have hqQ : (g : ℚ) = 3 * ((g / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
      have hne0 : (2 == 0) = false := rfl
      have hne1 : (2 == 1) = false := rfl
      simp only [step1, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
        endP, nextP, Inv1, AdjGoodFrom]
      have hg2 : (2 : ℚ) ≤ (g : ℚ) := by
        have : 2 ≤ g := by omega
        exact_mod_cast this
      exact ⟨(fun h => by rcases h with h | h <;> cases h), trivial,
        hpo0, by linarith, by linarith, by linarith, by linarith⟩
  | s4 =>
    rcases hst with ⟨hpi2, hcp, hpo_adj⟩
    cases g with
    | zero => simp at hgood; linarith
    | succ g' =>
      have hgQ : ((g' + 1 : ℕ) : ℚ) = (g' : ℚ) + 1 := by push_cast; ring
      have hrem : g' % 3 = 0 ∨ g' % 3 = 1 ∨ g' % 3 = 2 := by omega
      have hc0 : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg c
      rcases hrem with h0 | h1 | h2
      · have hq : g' = 3 * (g' / 3) := by omega
        have hqQ : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) := by exact_mod_cast hq
        simp only [step1, h0, beq_self_eq_true, ↓reduceIte, endP, nextP, Inv1, AdjGoodFrom]
        have hq0 : (0 : ℚ) ≤ ((g' / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
        refine ⟨fun _ => by omega, ⟨hpo_adj, by linarith, trivial⟩,
          by linarith, by linarith, trivial, by linarith⟩
      · have hq : g' = 3 * (g' / 3) + 1 := by omega
        have hqQ : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
        have hne0 : (1 == 0) = false := rfl
        simp only [step1, h1, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
          endP, nextP, Inv1, AdjGoodFrom]
        have hq0 : (0 : ℚ) ≤ ((g' / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
        exact ⟨fun _ => by omega, ⟨hpo_adj, trivial⟩,
          by linarith, by linarith, by linarith, by linarith⟩
      · have hq : g' = 3 * (g' / 3) + 2 := by omega
        have hqQ : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [step1, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          endP, nextP, Inv1, AdjGoodFrom]
        have hq0 : (0 : ℚ) ≤ ((g' / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
        exact ⟨fun _ => by omega, ⟨hpo_adj, trivial⟩,
          by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | s1 =>
    rcases hst with ⟨hpi1, hcp⟩
    simp only [step1, endP, nextP, Inv1, AdjGoodFrom]
    have hg0 : (0 : ℚ) ≤ (g : ℚ) := Nat.cast_nonneg g
    have hc0 : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg c
    have hcg : ((c + g : ℕ) : ℚ) = (c : ℚ) + (g : ℚ) := by push_cast; ring
    refine ⟨(fun h => by rcases h with h | h <;> cases h), trivial,
      hpo0, by linarith, by linarith, by linarith⟩
  | sE =>
    rcases hst with ⟨hcp, hpo_adj⟩
    cases g with
    | zero => exact absurd (hgE rfl) (by decide)
    | succ g' =>
      simp only [step1, endP, nextP, Inv1, AdjGoodFrom]
      have hgQ : ((g' + 1 : ℕ) : ℚ) = (g' : ℚ) + 1 := by push_cast; ring
      have hc0 : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg c
      have hc1 : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
      have hg'0 : (0 : ℚ) ≤ (g' : ℚ) := Nat.cast_nonneg g'
      exact ⟨fun _ => by omega, ⟨by linarith, trivial⟩,
        by linarith, by linarith, by linarith, by linarith⟩

theorem inv1_run (st : St1) (c : ℕ) (gs : List ℕ) (po pi : ℚ)
    (hinv : Inv1 st c po pi) (hgood : AdjGoodFrom pi gs)
    (hsafeE : Safe1 st gs) :
    AdjGoodFrom po (run1Aux st c gs).2.2 ∧
    Inv1 (run1Aux st c gs).1 (run1Aux st c gs).2.1
      (endP po (run1Aux st c gs).2.2) (endP pi gs) := by
  induction gs generalizing st c po pi with
  | nil =>
    simp only [run1Aux, endP, AdjGoodFrom]
    exact ⟨trivial, hinv⟩
  | cons g rest ih =>
    rcases hgood with ⟨h1, hrest_g⟩
    rcases hsafeE with ⟨hg_s, hrest_s⟩
    have hstep := inv1_step st c g po pi hinv h1 (fun heq => hg_s (Or.inr heq))
    rcases hstep with ⟨_, h_ag_em, h_inv1⟩
    simp only [run1Aux]
    rw [← step1_next_indep_c st c g] at hrest_s
    rcases ih (step1 st c g).1 (step1 st c g).2.1
      (endP po (step1 st c g).2.2) (nextP pi g) h_inv1 hrest_g hrest_s with ⟨h_ag_r, h_inv_r⟩
    refine ⟨adjGood_append h_ag_em h_ag_r, ?_⟩
    rw [endP_append]
    exact h_inv_r

theorem inv1_tail (st : St1) (c t : ℕ) (po pi : ℚ) (hinv : Inv1 st c po pi) :
    AdjGoodFrom po (step1Tail st c t).1 := by
  rcases hinv with ⟨_, _, hst⟩
  cases st with
  | s0 => simp [step1Tail, AdjGoodFrom]
  | s4 =>
    cases t with
    | zero => simp [step1Tail, AdjGoodFrom]
    | succ t' =>
      rcases hst with ⟨_, _, h_adj⟩
      exact ⟨h_adj, trivial⟩
  | s1 => simp [step1Tail, AdjGoodFrom]
  | sE =>
    cases t with
    | zero => simp [step1Tail, AdjGoodFrom]
    | succ t' =>
      rcases hst with ⟨_, h_adj⟩
      simp only [step1Tail, AdjGoodFrom]
      have hc1 : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
      exact ⟨by linarith, trivial⟩

theorem inv1_full (st : St1) (c : ℕ) (gs : List ℕ) (t : ℕ) (po pi : ℚ)
    (hinv : Inv1 st c po pi) (hgood : AdjGoodFrom pi gs) (hsafe : Safe1 st gs) :
    AdjGoodFrom po (run1Full st c gs t).1 := by
  rcases inv1_run st c gs po pi hinv hgood hsafe with ⟨hag, hinv'⟩
  exact adjGood_append hag (inv1_tail _ _ t _ _ hinv')

theorem run1Aux_def_eq (st : St1) (c : ℕ) (gs : List ℕ) (hs : Safe1 st gs) :
    (run1Aux st c gs).2.2.length + def1 (run1Aux st c gs).1 = gs.length + def1 st := by
  induction gs generalizing st c with
  | nil => simp [run1Aux]
  | cons g rest ih =>
    rcases hs with ⟨hg, hrest⟩
    rw [← step1_next_indep_c st c g] at hrest
    have hih := ih (step1 st c g).1 (step1 st c g).2.1 hrest
    simp only [run1Aux, List.length_append, List.length_cons]
    have hstep : (step1 st c g).2.2.length + def1 (step1 st c g).1 = 1 + def1 st := by
      cases st with
      | s0 =>
        simp only [step1, def1]
        have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
        rcases hrem with h0 | h1 | h2
        · simp [h0]
        · simp [h1]
        · simp [h2]
      | s4 =>
        cases g with
        | zero => exact absurd (hg (Or.inl rfl)) (by decide)
        | succ g' =>
          simp only [step1, def1]
          have hrem : g' % 3 = 0 ∨ g' % 3 = 1 ∨ g' % 3 = 2 := by omega
          rcases hrem with h0 | h1 | h2
          · simp [h0]
          · simp [h1]
          · simp [h2]
      | s1 => simp [step1, def1]
      | sE =>
        cases g with
        | zero => exact absurd (hg (Or.inr rfl)) (by decide)
        | succ g' => simp [step1, def1]
    omega

theorem run1Aux_stay_base3_budget (st : St1) (c : ℕ) (gs : List ℕ) (hs : Safe1 st gs)
    (h_end : (run1Aux st c gs).1 = .s0 ∨ (run1Aux st c gs).1 = .s4) :
    (st = .s0 ∨ st = .s4) →
    3 * ((run1Aux st c gs).2.2.sum + (run1Aux st c gs).2.1) ≤ gs.sum + 3 * c := by
  induction gs generalizing st c with
  | nil => intro _; simp [run1Aux]
  | cons g rest ih =>
    intro hst0
    rcases hs with ⟨hg, hrest⟩
    rw [← step1_next_indep_c st c g] at hrest
    have hnext_not_imm : ∀ st_cur c1, (st_cur = .s1 ∨ st_cur = .sE) →
        (run1Aux st_cur c1 rest).1 = .s1 ∨ (run1Aux st_cur c1 rest).1 = .sE := by
      intro st_cur c1 hs1
      clear h_end ih hst0 hrest
      induction rest generalizing st_cur c1 with
      | nil => exact hs1
      | cons g2 rs2 ihr =>
        simp only [run1Aux]
        apply ihr
        rcases hs1 with rfl | rfl
        · exact Or.inr rfl
        · cases g2 <;> exact Or.inr rfl
    have hst1 : (step1 st c g).1 = .s0 ∨ (step1 st c g).1 = .s4 := by
      cases hcase : (step1 st c g).1 with
      | s0 => exact Or.inl rfl
      | s4 => exact Or.inr rfl
      | s1 =>
        have hbad := hnext_not_imm .s1 (step1 st c g).2.1 (Or.inl rfl)
        simp only [run1Aux, hcase] at h_end
        rcases h_end with he | he <;> rcases hbad with hb | hb <;> rw [he] at hb <;> cases hb
      | sE =>
        have hbad := hnext_not_imm .sE (step1 st c g).2.1 (Or.inr rfl)
        simp only [run1Aux, hcase] at h_end
        rcases h_end with he | he <;> rcases hbad with hb | hb <;> rw [he] at hb <;> cases hb
    have hih := ih (step1 st c g).1 (step1 st c g).2.1 hrest (by simpa [run1Aux] using h_end) hst1
    simp only [run1Aux, List.sum_append, List.sum_cons]
    have hstep_b : 3 * ((step1 st c g).2.2.sum + (step1 st c g).2.1) ≤ g + 3 * c := by
      rcases hst0 with rfl | rfl
      · simp only [step1]
        have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
        rcases hrem with h0 | h1 | h2
        · simp [h0]; omega
        · simp [h1]; omega
        · simp [h2]; omega
      · cases g with
        | zero => exact absurd (hg (Or.inl rfl)) (by decide)
        | succ g' =>
          simp only [step1]
          have hrem : g' % 3 = 0 ∨ g' % 3 = 1 ∨ g' % 3 = 2 := by omega
          rcases hrem with h0 | h1 | h2
          · simp [h0]; omega
          · simp [h1]; omega
          · simp [h2]; omega
    omega

theorem run1Full_from_s1_allPos (st : St1) (c : ℕ) (gs : List ℕ) (t : ℕ)
    (hst : st = .s1 ∨ st = .sE) (hpos : ∀ x ∈ gs, 1 ≤ x) :
    ∀ x ∈ (run1Full st c gs t).1, 1 ≤ x := by
  induction gs generalizing st c with
  | nil =>
    simp only [run1Full, run1Aux, List.nil_append]
    rcases hst with rfl | rfl
    · simp [step1Tail]
    · cases t <;> simp [step1Tail]
  | cons g rest ih =>
    have hg : 1 ≤ g := hpos g (by simp)
    have hrest_pos : ∀ x ∈ rest, 1 ≤ x := fun x hx => hpos x (by simp [hx])
    simp only [run1Full, run1Aux, List.append_assoc]
    rcases hst with rfl | rfl
    · simp only [step1, List.nil_append]
      exact ih .sE (c + g) (Or.inr rfl) hrest_pos
    · cases g with
      | zero => omega
      | succ g' =>
        simp only [step1, List.cons_append, List.nil_append]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact ih .sE (g' + 1) (Or.inr rfl) hrest_pos x hx'

theorem run1Full_from_s0_1_0_allPos (rest : List ℕ) (t : ℕ) (hpos : ∀ x ∈ rest, 1 ≤ x) :
    ∀ x ∈ (run1Full .s0 0 (1 :: 0 :: rest) t).1, 1 ≤ x := by
  have heq : run1Full .s0 0 (1 :: 0 :: rest) t = run1Full .sE 0 rest t := by
    simp [run1Full, run1Aux, step1]
  rw [heq]
  exact run1Full_from_s1_allPos .sE 0 rest t (Or.inr rfl) hpos

-- ============================================================================
-- Section 6: 2-Cell Post-Entry Peeling Transducer (`peel2`)
-- ============================================================================

/-- 10 post-entry 2-cell states after `col 1` switches to `1` (or `2` pending `S` in `p42`). -/
inductive St2 where
  | p01
  | p42
  | p0E
  | p41z
  | p41p
  | p5
  | p4E
  | p11
  | p1E
  | pE1

def tok2 : St2 → List (Fin 2)
  | .p01 => w0 ++ w1
  | .p42 => w4 ++ w2
  | .p0E => w0 ++ wE
  | .p41z => w4 ++ w1
  | .p41p => w4 ++ w1
  | .p5 => w5
  | .p4E => w4 ++ wE
  | .p11 => w1 ++ w1
  | .p1E => w1 ++ wE
  | .pE1 => wE ++ w1

def def2 : St2 → ℕ
  | .p01 => 1
  | .p42 => 1
  | .p0E => 2
  | .p41z => 2
  | .p41p => 2
  | .p5 => 3
  | .p4E => 3
  | .p11 => 2
  | .p1E => 3
  | .pE1 => 3

/-- Helper transition from state `0!` (`w0 ++ wE`) on gap `g'`. -/
def step2From0E (c g' : ℕ) : St2 × ℕ × List ℕ :=
  match g' with
  | 0 => (.p5, c, [])
  | 1 => (.p1E, c, [])
  | 2 => (.p4E, c, [])
  | _ =>
    if g' % 3 == 0 then (.p0E, g' / 3, [c + 1])
    else if g' % 3 == 1 then (.p11, g' / 3, [c + 1])
    else (.p41p, g' / 3, [c + 1])

/-- Helper transition from state `01` (`w0 ++ w1`) on gap `g'`. -/
def step2From01 (c g' : ℕ) : St2 × ℕ × List ℕ :=
  if g' % 3 == 0 then (.p0E, c + g' / 3, [])
  else if g' % 3 == 1 then (.p11, c + g' / 3, [])
  else (.p41z, c + g' / 3, [])

def step2 (st : St2) (c g : ℕ) : St2 × ℕ × List ℕ :=
  match st with
  | .p01 => step2From01 c g
  | .p42 =>
    match g with
    | 0 => (.p42, c, [])
    | g' + 1 => step2From01 c g'
  | .p0E => step2From0E c g
  | .p41z =>
    match g with
    | 0 => (.p41z, c, [])
    | g' + 1 => step2From0E c g'
  | .p41p =>
    match g with
    | 0 => (.p41p, c, [])
    | g' + 1 => step2From0E c g'
  | .p5 =>
    match g with
    | 0 => (.p5, c, [])
    | g' + 1 =>
      let res := step2From0E 0 g'
      (res.1, res.2.1, (c + 1) :: res.2.2)
  | .p4E =>
    match g with
    | 0 => (.p4E, c, [])
    | 1 => (.p4E, c, [])
    | g' + 2 =>
      let res := step2From0E 0 g'
      (res.1, res.2.1, (c + 1) :: res.2.2)
  | .p11 => (.pE1, c + g, [])
  | .p1E =>
    match g with
    | 0 => (.p1E, c, [])
    | g' + 1 => (.pE1, g' + 1, [c + 1])
  | .pE1 =>
    match g with
    | 0 => (.pE1, c, [])
    | g' + 1 => (.pE1, g' + 1, [c + 2])

def run2Aux : St2 → ℕ → List ℕ → St2 × ℕ × List ℕ
  | st, c, [] => (st, c, [])
  | st, c, g :: gs =>
    let r1 := step2 st c g
    let r2 := run2Aux r1.1 r1.2.1 gs
    (r2.1, r2.2.1, r1.2.2 ++ r2.2.2)

def step2Tail0E (c t : ℕ) : List ℕ × ℕ :=
  match t with
  | 0 => ([], c)
  | 1 => ([], c)
  | 2 => ([], c)
  | t' + 3 => ([c + 1], (t' + 3) / 3)

def step2Tail (st : St2) (c t : ℕ) : List ℕ × ℕ :=
  match st with
  | .p01 => ([], c + t / 3)
  | .p42 => match t with | 0 => ([], c) | t' + 1 => ([], c + t' / 3)
  | .p0E => step2Tail0E c t
  | .p41z => match t with | 0 => ([], c) | t' + 1 => step2Tail0E c t'
  | .p41p => match t with | 0 => ([], c) | t' + 1 => step2Tail0E c t'
  | .p5 =>
    match t with
    | 0 => ([], c)
    | t' + 1 =>
      let rt := step2Tail0E 0 t'
      ((c + 1) :: rt.1, rt.2)
  | .p4E =>
    match t with
    | 0 => ([], c)
    | 1 => ([], c)
    | t' + 2 =>
      let rt := step2Tail0E 0 t'
      ((c + 1) :: rt.1, rt.2)
  | .p11 => ([], c + t)
  | .p1E => match t with | 0 => ([], c) | t' + 1 => ([c + 1], t' + 1)
  | .pE1 => match t with | 0 => ([], c) | t' + 1 => ([c + 2], t' + 1)

def run2Full (st : St2) (c : ℕ) (gs : List ℕ) (t : ℕ) : List ℕ × ℕ :=
  let r := run2Aux st c gs
  let rt := step2Tail r.1 r.2.1 t
  (r.2.2 ++ rt.1, rt.2)

def step2From0EEv (g' : ℕ) : List Ev :=
  match g' with
  | 0 => []
  | 1 => []
  | 2 => []
  | _ => Ev.B :: Ev.S :: List.replicate (g' / 3) Ev.B

def step2Ev (st : St2) (g : ℕ) : List Ev :=
  match st with
  | .p01 => List.replicate (g / 3) Ev.B
  | .p42 => match g with | 0 => [] | g' + 1 => List.replicate (g' / 3) Ev.B
  | .p0E => step2From0EEv g
  | .p41z => match g with | 0 => [] | g' + 1 => step2From0EEv g'
  | .p41p => match g with | 0 => [] | g' + 1 => step2From0EEv g'
  | .p5 => match g with | 0 => [] | g' + 1 => Ev.B :: Ev.S :: step2From0EEv g'
  | .p4E => match g with | 0 => [] | 1 => [] | g' + 2 => Ev.B :: Ev.S :: step2From0EEv g'
  | .p11 => List.replicate g Ev.B
  | .p1E => match g with | 0 => [] | g' + 1 => Ev.B :: Ev.S :: List.replicate (g' + 1) Ev.B
  | .pE1 => match g with | 0 => [] | g' + 1 => Ev.B :: Ev.B :: Ev.S :: List.replicate (g' + 1) Ev.B

def step2Tail0EEv (t : ℕ) : List Ev :=
  match t with
  | 0 => []
  | 1 => []
  | 2 => []
  | t' + 3 => Ev.B :: Ev.S :: List.replicate ((t' + 3) / 3) Ev.B

def step2TailEv (st : St2) (t : ℕ) : List Ev :=
  match st with
  | .p01 => List.replicate (t / 3) Ev.B
  | .p42 => match t with | 0 => [] | t' + 1 => List.replicate (t' / 3) Ev.B
  | .p0E => step2Tail0EEv t
  | .p41z => match t with | 0 => [] | t' + 1 => step2Tail0EEv t'
  | .p41p => match t with | 0 => [] | t' + 1 => step2Tail0EEv t'
  | .p5 => match t with | 0 => [] | t' + 1 => Ev.B :: Ev.S :: step2Tail0EEv t'
  | .p4E => match t with | 0 => [] | 1 => [] | t' + 2 => Ev.B :: Ev.S :: step2Tail0EEv t'
  | .p11 => List.replicate t Ev.B
  | .p1E => match t with | 0 => [] | t' + 1 => Ev.B :: Ev.S :: List.replicate (t' + 1) Ev.B
  | .pE1 => match t with | 0 => [] | t' + 1 => Ev.B :: Ev.B :: Ev.S :: List.replicate (t' + 1) Ev.B

def run2Evs : St2 → List ℕ → ℕ → List Ev
  | st, [], t => step2TailEv st t
  | st, g :: gs, t => step2Ev st g ++ run2Evs (step2 st 0 g).1 gs t

theorem step2From01_next_indep (c g : ℕ) : (step2From01 c g).1 = (step2From01 0 g).1 := by
  simp only [step2From01]; split <;> [rfl; split <;> rfl]

theorem step2From0E_next_indep (c g : ℕ) : (step2From0E c g).1 = (step2From0E 0 g).1 := by
  cases g with
  | zero => rfl
  | succ g1 =>
    cases g1 with
    | zero => rfl
    | succ g2 =>
      cases g2 with
      | zero => rfl
      | succ g3 =>
        simp only [step2From0E]; split <;> [rfl; split <;> rfl]

theorem step2_next_indep_c (st : St2) (c g : ℕ) : (step2 st c g).1 = (step2 st 0 g).1 := by
  cases st with
  | p01 => exact step2From01_next_indep c g
  | p42 => cases g with | zero => rfl | succ g' => exact step2From01_next_indep c g'
  | p0E => exact step2From0E_next_indep c g
  | p41z => cases g with | zero => rfl | succ g' => exact step2From0E_next_indep c g'
  | p41p => cases g with | zero => rfl | succ g' => exact step2From0E_next_indep c g'
  | p5 => cases g <;> rfl
  | p4E => cases g with | zero => rfl | succ g1 => cases g1 <;> rfl
  | p11 => rfl
  | p1E => cases g <;> rfl
  | pE1 => cases g <;> rfl

theorem rep_B_step2From0E (c g' : ℕ) :
    List.replicate c Ev.B ++ step2From0EEv g' =
      gapsEv (step2From0E c g').2.2 ++ List.replicate (step2From0E c g').2.1 Ev.B := by
  match g' with
  | 0 => simp [step2From0EEv, step2From0E, gapsEv]
  | 1 => simp [step2From0EEv, step2From0E, gapsEv]
  | 2 => simp [step2From0EEv, step2From0E, gapsEv]
  | g'' + 3 =>
    simp only [step2From0EEv, step2From0E]
    have hrem : (g'' + 3) % 3 = 0 ∨ (g'' + 3) % 3 = 1 ∨ (g'' + 3) % 3 = 2 := by omega
    have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
      rw [List.replicate_add]; rfl
    rcases hrem with h0 | h1m | h2m
    · simp only [h0, beq_self_eq_true, ↓reduceIte, gapsEv, gapEv, List.append_nil]
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]
    · have hne0 : (1 == 0) = false := rfl
      simp only [h1m, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, gapsEv, gapEv,
        List.append_nil]
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]
    · have hne0 : (2 == 0) = false := rfl
      have hne1 : (2 == 1) = false := rfl
      simp only [h2m, hne0, hne1, Bool.false_eq_true, ↓reduceIte, gapsEv, gapEv, List.append_nil]
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem rep_B_step2From01 (c g' : ℕ) :
    List.replicate c Ev.B ++ List.replicate (g' / 3) Ev.B =
      gapsEv (step2From01 c g').2.2 ++ List.replicate (step2From01 c g').2.1 Ev.B := by
  simp only [step2From01]
  have hrem : g' % 3 = 0 ∨ g' % 3 = 1 ∨ g' % 3 = 2 := by omega
  rcases hrem with h0 | h1 | h2
  · simp only [h0, beq_self_eq_true, ↓reduceIte, gapsEv, List.nil_append, List.replicate_add]
  · have hne0 : (1 == 0) = false := rfl
    simp only [h1, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, gapsEv,
      List.nil_append, List.replicate_add]
  · have hne0 : (2 == 0) = false := rfl
    have hne1 : (2 == 1) = false := rfl
    simp only [h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte, gapsEv, List.nil_append,
      List.replicate_add]

theorem rep_B_step2Tail0E (c t : ℕ) :
    List.replicate c Ev.B ++ step2Tail0EEv t =
      gapsEv (step2Tail0E c t).1 ++ List.replicate (step2Tail0E c t).2 Ev.B := by
  match t with
  | 0 => simp [step2Tail0EEv, step2Tail0E, gapsEv]
  | 1 => simp [step2Tail0EEv, step2Tail0E, gapsEv]
  | 2 => simp [step2Tail0EEv, step2Tail0E, gapsEv]
  | t' + 3 =>
    simp only [step2Tail0EEv, step2Tail0E, gapsEv, gapEv, List.append_nil]
    have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
      rw [List.replicate_add]; rfl
    rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Minimum gap requirement for a valid `St2` transition (guaranteed by `AllPos` + `Inv2`). -/
def minGap2 : St2 → ℕ
  | .p01 => 1
  | .p42 => 3
  | .p0E => 2
  | .p41z => 1
  | .p41p => 4
  | .p5 => 1
  | .p4E => 2
  | .p11 => 1
  | .p1E => 1
  | .pE1 => 1

theorem rep_B_step2Ev (st : St2) (c g : ℕ) (hg : minGap2 st ≤ g) :
    List.replicate c Ev.B ++ step2Ev st g =
      gapsEv (step2 st c g).2.2 ++ List.replicate (step2 st c g).2.1 Ev.B := by
  cases st with
  | p01 => exact rep_B_step2From01 c g
  | p42 =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' => exact rep_B_step2From01 c g'
  | p0E => exact rep_B_step2From0E c g
  | p41z =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' => exact rep_B_step2From0E c g'
  | p41p =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' => exact rep_B_step2From0E c g'
  | p5 =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [step2Ev, step2, gapsEv, gapEv]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      have h0 := rep_B_step2From0E 0 g'
      simp only [List.replicate_zero, List.nil_append] at h0
      rw [h1, h0]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | p4E =>
    match g with
    | 0 => simp [minGap2] at hg
    | 1 => simp [minGap2] at hg
    | g' + 2 =>
      simp only [step2Ev, step2, gapsEv, gapEv]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      have h0 := rep_B_step2From0E 0 g'
      simp only [List.replicate_zero, List.nil_append] at h0
      rw [h1, h0]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | p11 => simp only [step2Ev, step2, gapsEv, List.nil_append, List.replicate_add]
  | p1E =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [step2Ev, step2, gapsEv, gapEv, List.append_nil]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | pE1 =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [step2Ev, step2, gapsEv, gapEv, List.append_nil]
      have h2 : List.replicate (c + 2) Ev.B = List.replicate c Ev.B ++ [Ev.B, Ev.B] := by
        rw [List.replicate_add]; rfl
      rw [h2]; simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem rep_B_step2TailEv (st : St2) (c t : ℕ) :
    List.replicate c Ev.B ++ step2TailEv st t =
      gapsEv (step2Tail st c t).1 ++ List.replicate (step2Tail st c t).2 Ev.B := by
  cases st with
  | p01 => simp only [step2TailEv, step2Tail, gapsEv, List.nil_append, List.replicate_add]
  | p42 => cases t <;> simp only [step2TailEv, step2Tail, gapsEv, List.nil_append,
    List.append_nil, List.replicate_add]
  | p0E => exact rep_B_step2Tail0E c t
  | p41z =>
    cases t with
    | zero => simp [step2TailEv, step2Tail, gapsEv]
    | succ t' => exact rep_B_step2Tail0E c t'
  | p41p =>
    cases t with
    | zero => simp [step2TailEv, step2Tail, gapsEv]
    | succ t' => exact rep_B_step2Tail0E c t'
  | p5 =>
    cases t with
    | zero => simp [step2TailEv, step2Tail, gapsEv]
    | succ t' =>
      simp only [step2TailEv, step2Tail, gapsEv, gapEv]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      have h0 := rep_B_step2Tail0E 0 t'
      simp only [List.replicate_zero, List.nil_append] at h0
      rw [h1, h0]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | p4E =>
    match t with
    | 0 => simp [step2TailEv, step2Tail, gapsEv]
    | 1 => simp [step2TailEv, step2Tail, gapsEv]
    | t' + 2 =>
      simp only [step2TailEv, step2Tail, gapsEv, gapEv]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      have h0 := rep_B_step2Tail0E 0 t'
      simp only [List.replicate_zero, List.nil_append] at h0
      rw [h1, h0]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | p11 => simp only [step2TailEv, step2Tail, gapsEv, List.nil_append, List.replicate_add]
  | p1E =>
    cases t with
    | zero => simp [step2TailEv, step2Tail, gapsEv]
    | succ t' =>
      simp only [step2TailEv, step2Tail, gapsEv, gapEv, List.append_nil]
      have h1 : List.replicate (c + 1) Ev.B = List.replicate c Ev.B ++ [Ev.B] := by
        rw [List.replicate_add]; rfl
      rw [h1]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | pE1 =>
    cases t with
    | zero => simp [step2TailEv, step2Tail, gapsEv]
    | succ t' =>
      simp only [step2TailEv, step2Tail, gapsEv, gapEv, List.append_nil]
      have h2 : List.replicate (c + 2) Ev.B = List.replicate c Ev.B ++ [Ev.B, Ev.B] := by
        rw [List.replicate_add]; rfl
      rw [h2]; simp only [List.append_assoc, List.cons_append, List.nil_append]

def Safe2 : St2 → List ℕ → Prop
  | _, [] => True
  | st, g :: gs => minGap2 st ≤ g ∧ Safe2 (step2 st 0 g).1 gs

theorem rep_B_run2Evs (st : St2) (c : ℕ) (gs : List ℕ) (t : ℕ) (hs : Safe2 st gs) :
    List.replicate c Ev.B ++ run2Evs st gs t =
      gapsEv (run2Full st c gs t).1 ++ List.replicate (run2Full st c gs t).2 Ev.B := by
  induction gs generalizing st c with
  | nil =>
    simp only [run2Evs, run2Full, run2Aux, List.nil_append]
    exact rep_B_step2TailEv st c t
  | cons g rest ih =>
    rcases hs with ⟨hg, hrest⟩
    simp only [run2Evs, run2Full, run2Aux]
    rw [← List.append_assoc, rep_B_step2Ev st c g hg, List.append_assoc]
    rw [← step2_next_indep_c st c g] at hrest
    rw [← step2_next_indep_c st c g]
    have hih := ih (step2 st c g).1 (step2 st c g).2.1 hrest
    simp only [run2Full] at hih
    rw [hih]; simp only [gapsEv_append, List.append_assoc]

-- 2-cell `RunEv` compositional lift helpers!
theorem lift2_01_step (g : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (List.replicate (g / 3) Ev.B) r r') :
    RunEv (gapEv g) (w0 +> (w1 +> r)) (tok2 (step2From01 0 g).1 +> r') := by
  have hb3 : RunEv (List.replicate (3 * (g / 3)) Ev.B) (w0 +> (w1 +> r)) (w0 +> (w1 +> r')) :=
    runEv_w0_B3q (g / 3) (runEv_w1_Bk (g / 3) h)
  have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
  rcases hrem with h0 | h1 | h2
  · have hq : g = 3 * (g / 3) := by omega
    simp only [step2From01, h0, beq_self_eq_true, ↓reduceIte, tok2,
      Counter.listblank_append_assoc]
    have hge : gapEv g = List.replicate (3 * (g / 3)) Ev.B ++ [Ev.S] := by
      unfold gapEv; (conv_lhs => rw [hq])
    rw [hge]
    exact runEv_append hb3 (runEv_single (stepEv_w0_S (stepEv_w1_S r')))
  · have hq : g = 3 * (g / 3) + 1 := by omega
    have hne0 : (1 == 0) = false := rfl
    simp only [step2From01, h1, hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, tok2,
      Counter.listblank_append_assoc]
    have hge : gapEv g = List.replicate (3 * (g / 3)) Ev.B ++ [Ev.B, Ev.S] := by
      unfold gapEv; (conv_lhs => rw [hq]); rw [List.replicate_add, List.append_assoc]; rfl
    rw [hge]
    exact runEv_append hb3 (RunEv.cons (stepEv_w0_B (w1 +> r'))
      (runEv_single (stepEv_w2_S (w1 +> r'))))
  · have hq : g = 3 * (g / 3) + 2 := by omega
    have hne0 : (2 == 0) = false := rfl
    have hne1 : (2 == 1) = false := rfl
    simp only [step2From01, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte, tok2,
      Counter.listblank_append_assoc]
    have hge : gapEv g = List.replicate (3 * (g / 3)) Ev.B ++ [Ev.B, Ev.B, Ev.S] := by
      unfold gapEv; (conv_lhs => rw [hq]); rw [List.replicate_add, List.append_assoc]; rfl
    rw [hge]
    exact runEv_append hb3
      (RunEv.cons (stepEv_w0_B (w1 +> r'))
        (RunEv.cons (stepEv_w2_B (w1 +> r')) (runEv_single (stepEv_w3_S (w1 +> r')))))

theorem lift2_01_step_p (g : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (List.replicate (g / 3) Ev.B) r r') :
    RunEv (gapEv g) (w0 +> (w1 +> r))
      (tok2 (if g % 3 == 0 then .p0E else if g % 3 == 1 then .p11 else .p41p) +> r') := by
  have hb := lift2_01_step g h
  have htok : tok2 (step2From01 0 g).1 =
      tok2 (if g % 3 == 0 then .p0E else if g % 3 == 1 then .p11 else .p41p) := by
    simp only [step2From01]
    split
    · rfl
    · split <;> rfl
  rwa [htok] at hb

theorem lift2_0E_step (g : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (step2From0EEv g) r r') :
    RunEv (gapEv g) (w0 +> (wE +> r)) (tok2 (step2From0E 0 g).1 +> r') := by
  match g with
  | 0 =>
    cases h
    exact runEv_single (stepEv_w0_wE_S r)
  | 1 =>
    cases h
    simp only [gapEv, step2From0E, tok2, Counter.listblank_append_assoc]
    exact RunEv.cons (stepEv_w0_B (wE +> r)) (runEv_single (stepEv_w2_S (wE +> r)))
  | 2 =>
    cases h
    simp only [gapEv, step2From0E, tok2, Counter.listblank_append_assoc]
    exact RunEv.cons (stepEv_w0_B (wE +> r))
      (RunEv.cons (stepEv_w2_B (wE +> r)) (runEv_single (stepEv_w3_S (wE +> r))))
  | g' + 3 =>
    simp only [step2From0EEv] at h
    have hq : (g' + 3) / 3 = g' / 3 + 1 := by omega
    rw [hq, List.replicate_succ] at h
    cases h with
    | cons hB1 h1 =>
      cases h1 with
      | cons hS h2 =>
        cases h2 with
        | cons hB2 hrest =>
          rename_i r1 r2 r3
          have hb3 : RunEv [Ev.B, Ev.B, Ev.B] (w0 +> (wE +> r)) (w0 +> (w1 +> r3)) :=
            RunEv.cons (stepEv_w0_B (wE +> r))
              (RunEv.cons (stepEv_w2_B (wE +> r))
                (runEv_single (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))))
          have hge : gapEv (g' + 3) = [Ev.B, Ev.B, Ev.B] ++ gapEv g' := by
            simp [gapEv, List.replicate_succ]
          rw [hge]
          have hlift := lift2_01_step_p g' hrest
          have hmod : (g' + 3) % 3 = g' % 3 := by omega
          have hst_eq : (step2From0E 0 (g' + 3)).1 =
              (if g' % 3 == 0 then .p0E else if g' % 3 == 1 then .p11 else .p41p) := by
            simp only [step2From0E, hmod]
            split <;> [rfl; split <;> rfl]
          rw [hst_eq]
          exact runEv_append hb3 hlift

theorem lift2_step (st : St2) (g : ℕ) (hg : minGap2 st ≤ g)
    {r r' : ListBlank (Fin 2)} (h : RunEv (step2Ev st g) r r') :
    RunEv (gapEv g) (tok2 st +> r) (tok2 (step2 st 0 g).1 +> r') := by
  cases st with
  | p01 =>
    simp only [tok2, Counter.listblank_append_assoc]
    exact lift2_01_step g h
  | p42 =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [tok2, Counter.listblank_append_assoc]
      have hge : gapEv (g' + 1) = Ev.B :: gapEv g' := by simp [gapEv, List.replicate_succ]
      rw [hge]
      exact RunEv.cons (stepEv_w4_B (stepEv_w2_S r)) (lift2_01_step g' h)
  | p0E =>
    simp only [tok2, Counter.listblank_append_assoc]
    exact lift2_0E_step g h
  | p41z =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [tok2, Counter.listblank_append_assoc]
      have hge : gapEv (g' + 1) = Ev.B :: gapEv g' := by simp [gapEv, List.replicate_succ]
      rw [hge]
      exact RunEv.cons (stepEv_w4_B (stepEv_w1_S r)) (lift2_0E_step g' h)
  | p41p =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [tok2, Counter.listblank_append_assoc]
      have hge : gapEv (g' + 1) = Ev.B :: gapEv g' := by simp [gapEv, List.replicate_succ]
      rw [hge]
      exact RunEv.cons (stepEv_w4_B (stepEv_w1_S r)) (lift2_0E_step g' h)
  | p5 =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [step2Ev] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS hrest =>
          have hge : gapEv (g' + 1) = Ev.B :: gapEv g' := by simp [gapEv, List.replicate_succ]
          rw [hge]
          exact RunEv.cons (stepEv_w5_B hB1 hS) (lift2_0E_step g' hrest)
  | p4E =>
    match g with
    | 0 => simp [minGap2] at hg
    | 1 => simp [minGap2] at hg
    | g' + 2 =>
      simp only [step2Ev] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS hrest =>
          simp only [tok2, Counter.listblank_append_assoc]
          have hge : gapEv (g' + 2) = Ev.B :: Ev.B :: gapEv g' := by
            simp [gapEv, List.replicate_succ]
          rw [hge]
          exact RunEv.cons (stepEv_w4_wE_B r)
            (RunEv.cons (stepEv_w5_B hB1 hS) (lift2_0E_step g' hrest))
  | p11 =>
    simp only [tok2, Counter.listblank_append_assoc, step2Ev, step2, gapEv] at *
    exact runEv_append (runEv_w1_Bk g (runEv_w1_Bk g h)) (runEv_single (stepEv_w1_S (w1 +> r')))
  | p1E =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [step2Ev] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS h2 =>
          rw [List.replicate_succ] at h2
          cases h2 with
          | cons hB2 hrest =>
            simp only [tok2, Counter.listblank_append_assoc, step2]
            have hge : gapEv (g' + 1) = Ev.B :: (List.replicate g' Ev.B ++ [Ev.S]) := by
              simp [gapEv, List.replicate_succ]
            rw [hge]
            exact RunEv.cons (stepEv_w1_B (stepEv_wE_B hB1 hS hB2))
              (runEv_append (runEv_w1_Bk g' (runEv_w1_Bk g' hrest))
                (runEv_single (stepEv_w1_S (w1 +> r'))))
  | pE1 =>
    cases g with
    | zero => simp [minGap2] at hg
    | succ g' =>
      simp only [step2Ev] at h
      cases h with
      | cons hB0 h0 =>
        cases h0 with
        | cons hB1 h1 =>
          cases h1 with
          | cons hS h2 =>
            rw [List.replicate_succ] at h2
            cases h2 with
            | cons hB2 hrest =>
              rename_i r1 r2 r3 r4
              simp only [tok2, Counter.listblank_append_assoc, step2]
              have hs1 : StepEv Ev.B (wE +> (w1 +> r)) (w1 +> (w1 +> r4)) :=
                stepEv_wE_B (stepEv_w1_B hB0) (stepEv_w1_S r1) (stepEv_wE_B hB1 hS hB2)
              have hge : gapEv (g' + 1) = Ev.B :: (List.replicate g' Ev.B ++ [Ev.S]) := by
                simp [gapEv, List.replicate_succ]
              rw [hge]
              exact RunEv.cons hs1
                (runEv_append (runEv_w1_Bk g' (runEv_w1_Bk g' hrest))
                  (runEv_single (stepEv_w1_S (w1 +> r'))))

theorem lift2_01_tail (t : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (List.replicate (t / 3) Ev.B) r r') :
    ∃ r_out, RunEv (List.replicate t Ev.B) (w0 +> (w1 +> r)) r_out := by
  have hb3 := runEv_w0_B3q (t / 3) (runEv_w1_Bk (t / 3) h)
  have hrem : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hrem with h0 | h1 | h2
  · have ht : t = 3 * (t / 3) := by omega
    rw [ht]; exact ⟨_, hb3⟩
  · have ht : List.replicate t Ev.B = List.replicate (3 * (t / 3)) Ev.B ++ [Ev.B] := by
      have : t = 3 * (t / 3) + 1 := by omega
      (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
    rw [ht]; exact ⟨_, runEv_append hb3 (runEv_single (stepEv_w0_B (w1 +> r')))⟩
  · have ht : List.replicate t Ev.B = List.replicate (3 * (t / 3)) Ev.B ++ [Ev.B, Ev.B] := by
      have : t = 3 * (t / 3) + 2 := by omega
      (conv_lhs => rw [this]); rw [List.replicate_add]; rfl
    rw [ht]; exact ⟨_, runEv_append hb3
      (RunEv.cons (stepEv_w0_B (w1 +> r')) (runEv_single (stepEv_w2_B (w1 +> r'))))⟩

theorem lift2_0E_tail (t : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (step2Tail0EEv t) r r') :
    ∃ r_out, RunEv (List.replicate t Ev.B) (w0 +> (wE +> r)) r_out := by
  match t with
  | 0 => exact ⟨_, RunEv.nil _⟩
  | 1 => exact ⟨_, runEv_single (stepEv_w0_B (wE +> r))⟩
  | 2 => exact ⟨_, RunEv.cons (stepEv_w0_B (wE +> r)) (runEv_single (stepEv_w2_B (wE +> r)))⟩
  | t' + 3 =>
    simp only [step2Tail0EEv] at h
    have hq : (t' + 3) / 3 = t' / 3 + 1 := by omega
    rw [hq, List.replicate_succ] at h
    cases h with
    | cons hB1 h1 =>
      cases h1 with
      | cons hS h2 =>
        cases h2 with
        | cons hB2 hrest =>
          rename_i r1 r2 r3
          have hb3 : RunEv [Ev.B, Ev.B, Ev.B] (w0 +> (wE +> r)) (w0 +> (w1 +> r3)) :=
            RunEv.cons (stepEv_w0_B (wE +> r))
              (RunEv.cons (stepEv_w2_B (wE +> r))
                (runEv_single (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))))
          rcases lift2_01_tail t' hrest with ⟨r_out, hr_out⟩
          have ht : List.replicate (t' + 3) Ev.B = [Ev.B, Ev.B, Ev.B] ++ List.replicate t' Ev.B :=
            by
            simp [List.replicate_succ]
          rw [ht]
          exact ⟨r_out, runEv_append hb3 hr_out⟩

theorem lift2_tail (st : St2) (t : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (step2TailEv st t) r r') :
    ∃ r_out, RunEv (List.replicate t Ev.B) (tok2 st +> r) r_out := by
  cases st with
  | p01 =>
    simp only [tok2, Counter.listblank_append_assoc]
    exact lift2_01_tail t h
  | p42 =>
    cases t with
    | zero => exact ⟨_, RunEv.nil _⟩
    | succ t' =>
      simp only [tok2, Counter.listblank_append_assoc]
      rcases lift2_01_tail t' h with ⟨r_out, hr_out⟩
      rw [List.replicate_succ]
      exact ⟨r_out, RunEv.cons (stepEv_w4_B (stepEv_w2_S r)) hr_out⟩
  | p0E =>
    simp only [tok2, Counter.listblank_append_assoc]
    exact lift2_0E_tail t h
  | p41z =>
    cases t with
    | zero => exact ⟨_, RunEv.nil _⟩
    | succ t' =>
      simp only [tok2, Counter.listblank_append_assoc]
      rcases lift2_0E_tail t' h with ⟨r_out, hr_out⟩
      rw [List.replicate_succ]
      exact ⟨r_out, RunEv.cons (stepEv_w4_B (stepEv_w1_S r)) hr_out⟩
  | p41p =>
    cases t with
    | zero => exact ⟨_, RunEv.nil _⟩
    | succ t' =>
      simp only [tok2, Counter.listblank_append_assoc]
      rcases lift2_0E_tail t' h with ⟨r_out, hr_out⟩
      rw [List.replicate_succ]
      exact ⟨r_out, RunEv.cons (stepEv_w4_B (stepEv_w1_S r)) hr_out⟩
  | p5 =>
    cases t with
    | zero => exact ⟨_, RunEv.nil _⟩
    | succ t' =>
      simp only [step2TailEv] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS hrest =>
          rcases lift2_0E_tail t' hrest with ⟨r_out, hr_out⟩
          rw [List.replicate_succ]
          exact ⟨r_out, RunEv.cons (stepEv_w5_B hB1 hS) hr_out⟩
  | p4E =>
    match t with
    | 0 => exact ⟨_, RunEv.nil _⟩
    | 1 =>
      simp only [tok2, Counter.listblank_append_assoc]
      exact ⟨_, runEv_single (stepEv_w4_wE_B r)⟩
    | t' + 2 =>
      simp only [step2TailEv] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS hrest =>
          simp only [tok2, Counter.listblank_append_assoc]
          rcases lift2_0E_tail t' hrest with ⟨r_out, hr_out⟩
          have ht : List.replicate (t' + 2) Ev.B = Ev.B :: Ev.B :: List.replicate t' Ev.B := by
            simp [List.replicate_succ]
          rw [ht]
          exact ⟨r_out, RunEv.cons (stepEv_w4_wE_B r)
            (RunEv.cons (stepEv_w5_B hB1 hS) hr_out)⟩
  | p11 =>
    simp only [tok2, Counter.listblank_append_assoc, step2TailEv] at *
    exact ⟨_, runEv_w1_Bk t (runEv_w1_Bk t h)⟩
  | p1E =>
    cases t with
    | zero => exact ⟨_, RunEv.nil _⟩
    | succ t' =>
      simp only [step2TailEv] at h
      cases h with
      | cons hB1 h1 =>
        cases h1 with
        | cons hS h2 =>
          rw [List.replicate_succ] at h2
          cases h2 with
          | cons hB2 hrest =>
            simp only [tok2, Counter.listblank_append_assoc]
            rw [List.replicate_succ]
            exact ⟨_, RunEv.cons (stepEv_w1_B (stepEv_wE_B hB1 hS hB2))
              (runEv_w1_Bk t' (runEv_w1_Bk t' hrest))⟩
  | pE1 =>
    cases t with
    | zero => exact ⟨_, RunEv.nil _⟩
    | succ t' =>
      simp only [step2TailEv] at h
      cases h with
      | cons hB0 h0 =>
        cases h0 with
        | cons hB1 h1 =>
          cases h1 with
          | cons hS h2 =>
            rw [List.replicate_succ] at h2
            cases h2 with
            | cons hB2 hrest =>
              rename_i r1 r2 r3 r4
              simp only [tok2, Counter.listblank_append_assoc]
              have hs1 : StepEv Ev.B (wE +> (w1 +> r)) (w1 +> (w1 +> r4)) :=
                stepEv_wE_B (stepEv_w1_B hB0) (stepEv_w1_S r1) (stepEv_wE_B hB1 hS hB2)
              rw [List.replicate_succ]
              exact ⟨_, RunEv.cons hs1 (runEv_w1_Bk t' (runEv_w1_Bk t' hrest))⟩

theorem lift2_run (st : St2) (gs : List ℕ) (t : ℕ) (hs : Safe2 st gs)
    {r r' : ListBlank (Fin 2)} (h : RunEv (run2Evs st gs t) r r') :
    ∃ r_out, RunEv (gapsEv gs ++ List.replicate t Ev.B) (tok2 st +> r) r_out := by
  induction gs generalizing st r with
  | nil =>
    simp only [gapsEv, List.nil_append]
    exact lift2_tail st t h
  | cons g rest ih =>
    rcases hs with ⟨hg, hrest⟩
    simp only [run2Evs] at h
    rcases runEv_prefix h with ⟨r1, hstep, htail⟩
    have hl := lift2_step st g hg hstep
    rcases ih (step2 st 0 g).1 hrest htail with ⟨r_out, hrest_run⟩
    exact ⟨r_out, by
      simp only [gapsEv, List.append_assoc]
      exact runEv_append hl hrest_run⟩

-- Invariant `Inv2` proving `AdjGoodFrom`, `Safe2`, `AllPos`, AND `length` decrease for `peel2`!
def Inv2 (st : St2) (c : ℕ) (po pi : ℚ) : Prop :=
  0 ≤ po ∧ 0 ≤ pi ∧
  match st with
  | .p01 => c = 0 ∧ po = 0 ∧ 3 ≤ pi
  | .p42 => c = 0 ∧ po = 0 ∧ 5 ≤ pi
  | .p0E => 1 ≤ c ∧ 3 * (c : ℚ) + po ≤ pi + 3 / 2 ∧
            3 * (c : ℚ) + 1 / 3 ≤ pi ∧ 2 * po ≤ 3 * (c : ℚ) + 6
  | .p41z => po = 0 ∧ 3 * (c : ℚ) + 3 ≤ pi
  | .p41p => 1 ≤ c ∧ 3 * (c : ℚ) + po ≤ pi - 1 / 2 ∧
             3 * (c : ℚ) + 28 / 9 ≤ pi ∧ 2 * po ≤ 3 * (c : ℚ) + 6
  | .p5 => c = 0 ∧ po ≤ 3 ∧ po ≤ pi ∧ 1 ≤ pi
  | .p4E => c ≤ 1 ∧ po ≤ 3 ∧ 3 * (c : ℚ) + po ≤ 6 ∧
            3 * (c : ℚ) + po ≤ pi + 5 / 2 ∧ 28 / 9 ≤ pi
  | .p11 => 3 * (c : ℚ) + po ≤ pi + 1 / 2
  | .p1E => c = 0 ∧ po ≤ 3 ∧ po ≤ pi - 1
  | .pE1 => 3 * (c : ℚ) + po ≤ 3 * pi + 3 ∧ 2 * po ≤ 3 * (c : ℚ) + 9

set_option maxHeartbeats 1600000 in
-- Large case split across `St2` and residues mod 3 requires extra heartbeats.
theorem inv2_step (st : St2) (c g : ℕ) (po pi : ℚ)
    (hinv : Inv2 st c po pi) (hgpos : 1 ≤ g) (hgood : 2 * pi ≤ 3 * (g : ℚ) + 3) :
    minGap2 st ≤ g ∧
    (∀ x ∈ (step2 st c g).2.2, 1 ≤ x) ∧
    (step2 st c g).2.2.length + def2 (step2 st c g).1 = 1 + def2 st ∧
    AdjGoodFrom po (step2 st c g).2.2 ∧
    Inv2 (step2 st c g).1 (step2 st c g).2.1
      (endP po (step2 st c g).2.2) (nextP pi g) := by
  rcases hinv with ⟨hpo0, hpi0, hst⟩
  have hgQ0 : (0 : ℚ) ≤ (g : ℚ) := Nat.cast_nonneg g
  have hcQ0 : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg c
  cases st with
  | p01 =>
    rcases hst with ⟨rfl, rfl, hpi3⟩
    have hrem : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
    rcases hrem with h0 | h1 | h2
    · have hq : g = 3 * (g / 3) := by omega
      have hq_pos : 1 ≤ g / 3 := by omega
      have hqQ : (g : ℚ) = 3 * ((g / 3 : ℕ) : ℚ) := by exact_mod_cast hq
      have hq0 : (0 : ℚ) ≤ ((g / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
      simp only [minGap2, step2, step2From01, h0, beq_self_eq_true, ↓reduceIte, Nat.zero_add,
        def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨hgpos, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith,
        hq_pos, by linarith, by linarith, by linarith⟩
    · have hq : g = 3 * (g / 3) + 1 := by omega
      have hqQ : (g : ℚ) = 3 * ((g / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
      have hne0 : (1 == 0) = false := rfl
      simp only [minGap2, step2, step2From01, h1, hne0, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, Nat.zero_add, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨hgpos, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith, by linarith⟩
    · have hq : g = 3 * (g / 3) + 2 := by omega
      have hqQ : (g : ℚ) = 3 * ((g / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
      have hne0 : (2 == 0) = false := rfl
      have hne1 : (2 == 1) = false := rfl
      simp only [minGap2, step2, step2From01, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨hgpos, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith, trivial, by
        linarith⟩
  | p42 =>
    rcases hst with ⟨rfl, rfl, hpi5⟩
    have hg3 : 3 ≤ g := by
      rcases Nat.lt_or_ge g 3 with hlt | hge
      · have : (g : ℚ) ≤ 2 := by exact_mod_cast (show g ≤ 2 by omega)
        linarith
      · exact hge
    cases g with
    | zero => omega
    | succ g' =>
      have hg'2 : 2 ≤ g' := by omega
      have hgQ : ((g' + 1 : ℕ) : ℚ) = (g' : ℚ) + 1 := by push_cast; ring
      have hrem : g' % 3 = 0 ∨ g' % 3 = 1 ∨ g' % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hq : g' = 3 * (g' / 3) := by omega
        have hq_pos : 1 ≤ g' / 3 := by omega
        have hqQ : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) := by exact_mod_cast hq
        have hq0 : (0 : ℚ) ≤ ((g' / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
        simp only [minGap2, step2, step2From01, h0, beq_self_eq_true, ↓reduceIte, Nat.zero_add,
          def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨hg3, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith,
          hq_pos, by linarith, by linarith, by linarith⟩
      · have hq : g' = 3 * (g' / 3) + 1 := by omega
        have hqQ : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
        have hne0 : (1 == 0) = false := rfl
        simp only [minGap2, step2, step2From01, h1, hne0, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Nat.zero_add, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨hg3, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith, by linarith⟩
      · have hq : g' = 3 * (g' / 3) + 2 := by omega
        have hqQ : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [minGap2, step2, step2From01, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          Nat.zero_add, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨hg3, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith, trivial, by
          linarith⟩
  | p0E =>
    rcases hst with ⟨hc1, hW, hpi_lb, hpo_adj⟩
    have hc1Q : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
    have hg2 : 2 ≤ g := by
      rcases Nat.lt_or_ge g 2 with hlt | hge
      · have : (g : ℚ) ≤ 1 := by exact_mod_cast (show g ≤ 1 by omega)
        linarith
      · exact hge
    match g with
    | 0 => omega
    | 1 => omega
    | 2 =>
      have hc_eq1 : c = 1 := by
        rcases Nat.lt_or_ge c 2 with hlt | hge
        · omega
        · have : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hge
          simp only [Nat.cast_ofNat] at hgood
          linarith
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      simp only [Nat.cast_ofNat] at hgood
      refine ⟨by omega, (fun _ hx => by cases hx), rfl, trivial, hpo0, by linarith,
        by omega, ?_, ?_, ?_, ?_⟩
      · have hc_q : (c : ℚ) = 1 := by exact_mod_cast hc_eq1
        linarith
      · linarith
      · linarith
      · linarith
    | g' + 3 =>
      have hgQ : ((g' + 3 : ℕ) : ℚ) = (g' : ℚ) + 3 := by push_cast; ring
      have hc1_eq : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
      have hq_pos : 1 ≤ (g' + 3) / 3 := by omega
      have hrem : (g' + 3) % 3 = 0 ∨ (g' + 3) % 3 = 1 ∨ (g' + 3) % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hq : g' + 3 = 3 * ((g' + 3) / 3) := by omega
        have hqQ : ((g' + 3 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) := by exact_mod_cast hq
        simp only [minGap2, step2, step2From0E, h0, beq_self_eq_true, ↓reduceIte, def2,
          endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, hq_pos, by linarith, by linarith, by linarith⟩
      · have hq : g' + 3 = 3 * ((g' + 3) / 3) + 1 := by omega
        have hqQ : ((g' + 3 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
        have hne0 : (1 == 0) = false := rfl
        simp only [minGap2, step2, step2From0E, h1, hne0, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, by linarith⟩
      · have hq : g' + 3 = 3 * ((g' + 3) / 3) + 2 := by omega
        have hqQ : ((g' + 3 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [minGap2, step2, step2From0E, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, hq_pos, by linarith, by linarith, by linarith⟩
  | p41z =>
    rcases hst with ⟨rfl, hpi_lb⟩
    match g with
    | 0 => omega
    | 1 =>
      have hc0 : c = 0 := by
        cases c with
        | zero => rfl
        | succ c' =>
          have : (1 : ℚ) ≤ ((c' + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ c' + 1 by omega)
          simp only [Nat.cast_one] at hgood
          linarith
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      simp only [Nat.cast_one] at hgood
      refine ⟨by omega, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith,
        hc0, by norm_num, by linarith, by linarith⟩
    | 2 =>
      have hc0 : c = 0 := by
        cases c with
        | zero => rfl
        | succ c' =>
          have : (1 : ℚ) ≤ ((c' + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ c' + 1 by omega)
          simp only [Nat.cast_ofNat] at hgood
          linarith
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      simp only [Nat.cast_ofNat] at hgood
      refine ⟨by omega, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith,
        hc0, by norm_num, by linarith⟩
    | 3 =>
      have hc_le1 : c ≤ 1 := by
        rcases Nat.lt_or_ge c 2 with hlt | hge
        · omega
        · have : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hge
          simp only [Nat.cast_ofNat] at hgood
          linarith
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      simp only [Nat.cast_ofNat] at hgood
      have hcQ1 : (c : ℚ) ≤ 1 := by exact_mod_cast hc_le1
      refine ⟨by omega, (fun _ hx => by cases hx), rfl, trivial, le_refl 0, by linarith,
        hc_le1, by norm_num, by linarith, by linarith, by linarith⟩
    | g' + 4 =>
      have hc1_eq : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
      have hq_pos : 1 ≤ (g' + 3) / 3 := by omega
      have hrem : (g' + 3) % 3 = 0 ∨ (g' + 3) % 3 = 1 ∨ (g' + 3) % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 1 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
        simp only [minGap2, step2, step2From0E, h0, beq_self_eq_true, ↓reduceIte, def2,
          endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, hq_pos, by linarith, by linarith, by linarith⟩
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 2 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hne0 : (1 == 0) = false := rfl
        simp only [minGap2, step2, step2From0E, h1, hne0, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, by linarith⟩
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 3 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 3 := by exact_mod_cast hq
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [minGap2, step2, step2From0E, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, hq_pos, by linarith, by linarith, by linarith⟩
  | p41p =>
    rcases hst with ⟨hc1, hW, hpi_lb, hpo_adj⟩
    have hc1Q : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
    have hg4 : 4 ≤ g := by
      rcases Nat.lt_or_ge g 4 with hlt | hge
      · have : (g : ℚ) ≤ 3 := by exact_mod_cast (show g ≤ 3 by omega)
        linarith
      · exact hge
    match g with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | g' + 4 =>
      have hc1_eq : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
      have hq_pos : 1 ≤ (g' + 3) / 3 := by omega
      have hrem : (g' + 3) % 3 = 0 ∨ (g' + 3) % 3 = 1 ∨ (g' + 3) % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 1 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
        simp only [minGap2, step2, step2From0E, h0, beq_self_eq_true, ↓reduceIte, def2,
          endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, hq_pos, by linarith, by linarith, by linarith⟩
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 2 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hne0 : (1 == 0) = false := rfl
        simp only [minGap2, step2, step2From0E, h1, hne0, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, by linarith⟩
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 3 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 3 := by exact_mod_cast hq
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [minGap2, step2, step2From0E, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
          by linarith, by linarith, hq_pos, by linarith, by linarith, by linarith⟩
  | p5 =>
    rcases hst with ⟨rfl, hpo3, hW, hpi1⟩
    match g with
    | 0 => omega
    | 1 =>
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by norm_num; linarith, trivial⟩,
        by norm_num; linarith, by norm_num; linarith, trivial, by norm_num; linarith,
        by norm_num; linarith, by norm_num; linarith⟩
    | 2 =>
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by norm_num; linarith, trivial⟩,
        by norm_num; linarith, by norm_num; linarith, trivial, by norm_num; linarith,
        by norm_num; linarith⟩
    | 3 =>
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by norm_num; linarith, trivial⟩,
        by norm_num; linarith, by norm_num; linarith, by omega, by norm_num; linarith,
        by norm_num; linarith, by norm_num; linarith, by norm_num; linarith⟩
    | g' + 4 =>
      have hq_pos : 1 ≤ (g' + 3) / 3 := by omega
      have hq1Q : (1 : ℚ) ≤ (((g' + 3) / 3 : ℕ) : ℚ) := by exact_mod_cast hq_pos
      have hrem : (g' + 3) % 3 = 0 ∨ (g' + 3) % 3 = 1 ∨ (g' + 3) % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 1 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 1 := by exact_mod_cast hq
        have hgp : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) := by
          exact_mod_cast (show g' = 3 * (g' / 3) by omega)
        simp only [minGap2, step2, step2From0E, h0, beq_self_eq_true, ↓reduceIte, def2,
          endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl,
          ⟨by norm_num; linarith, by norm_num; linarith, trivial⟩,
          by norm_num; linarith, by linarith, hq_pos, by norm_num; linarith,
          by linarith, by norm_num; linarith⟩
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 2 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hgp : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 1 := by
          exact_mod_cast (show g' = 3 * (g' / 3) + 1 by omega)
        have hne0 : (1 == 0) = false := rfl
        simp only [minGap2, step2, step2From0E, h1, hne0, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl,
          ⟨by norm_num; linarith, by norm_num; linarith, trivial⟩,
          by norm_num; linarith, by linarith, by norm_num; linarith⟩
      · have hq : g' + 4 = 3 * ((g' + 3) / 3) + 3 := by omega
        have hqQ : ((g' + 4 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 3 := by exact_mod_cast hq
        have hgp : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 2 := by
          exact_mod_cast (show g' = 3 * (g' / 3) + 2 by omega)
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [minGap2, step2, step2From0E, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl,
          ⟨by norm_num; linarith, by norm_num; linarith, trivial⟩,
          by norm_num; linarith, by linarith, hq_pos, by norm_num; linarith,
          by linarith, by norm_num; linarith⟩
  | p4E =>
    rcases hst with ⟨hc_le1, hpo3, h3c6, hW, hpi_lb⟩
    have hg2 : 2 ≤ g := by
      rcases Nat.lt_or_ge g 2 with hlt | hge
      · have : (g : ℚ) ≤ 1 := by exact_mod_cast (show g ≤ 1 by omega)
        linarith
      · exact hge
    have hc1_eq : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
    match g with
    | 0 => omega
    | 1 => omega
    | 2 =>
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
        by linarith, by linarith, trivial, by linarith, by linarith, by linarith⟩
    | 3 =>
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
        by linarith, by linarith, trivial, by linarith, by linarith⟩
    | 4 =>
      simp only [minGap2, step2, step2From0E, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
        by linarith, by linarith, by omega, by linarith, by linarith, by linarith, by linarith⟩
    | g' + 5 =>
      have hq_pos : 1 ≤ (g' + 3) / 3 := by omega
      have hq1Q : (1 : ℚ) ≤ (((g' + 3) / 3 : ℕ) : ℚ) := by exact_mod_cast hq_pos
      have hrem : (g' + 3) % 3 = 0 ∨ (g' + 3) % 3 = 1 ∨ (g' + 3) % 3 = 2 := by omega
      rcases hrem with h0 | h1 | h2
      · have hq : g' + 5 = 3 * ((g' + 3) / 3) + 2 := by omega
        have hqQ : ((g' + 5 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 2 := by exact_mod_cast hq
        have hgp : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) := by
          exact_mod_cast (show g' = 3 * (g' / 3) by omega)
        simp only [minGap2, step2, step2From0E, h0, beq_self_eq_true, ↓reduceIte, def2,
          endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · cases List.mem_singleton.mp hx; omega,
          rfl,
          ⟨by linarith, by norm_num; linarith, trivial⟩,
          by norm_num; linarith, by linarith, hq_pos, by norm_num; linarith,
          by linarith, by norm_num; linarith⟩
      · have hq : g' + 5 = 3 * ((g' + 3) / 3) + 3 := by omega
        have hqQ : ((g' + 5 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 3 := by exact_mod_cast hq
        have hgp : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 1 := by
          exact_mod_cast (show g' = 3 * (g' / 3) + 1 by omega)
        have hne0 : (1 == 0) = false := rfl
        simp only [minGap2, step2, step2From0E, h1, hne0, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · cases List.mem_singleton.mp hx; omega,
          rfl,
          ⟨by linarith, by norm_num; linarith, trivial⟩,
          by norm_num; linarith, by linarith, by norm_num; linarith⟩
      · have hq : g' + 5 = 3 * ((g' + 3) / 3) + 4 := by omega
        have hqQ : ((g' + 5 : ℕ) : ℚ) = 3 * (((g' + 3) / 3 : ℕ) : ℚ) + 4 := by exact_mod_cast hq
        have hgp : (g' : ℚ) = 3 * ((g' / 3 : ℕ) : ℚ) + 2 := by
          exact_mod_cast (show g' = 3 * (g' / 3) + 2 by omega)
        have hne0 : (2 == 0) = false := rfl
        have hne1 : (2 == 1) = false := rfl
        simp only [minGap2, step2, step2From0E, h2, hne0, hne1, Bool.false_eq_true, ↓reduceIte,
          def2, endP, nextP, Inv2, AdjGoodFrom]
        refine ⟨by omega, fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · cases List.mem_singleton.mp hx; omega,
          rfl,
          ⟨by linarith, by norm_num; linarith, trivial⟩,
          by norm_num; linarith, by linarith, hq_pos, by norm_num; linarith,
          by linarith, by norm_num; linarith⟩
  | p11 =>
    have hcg : ((c + g : ℕ) : ℚ) = (c : ℚ) + (g : ℚ) := by push_cast; ring
    simp only [minGap2, step2, def2, endP, nextP, Inv2, AdjGoodFrom]
    exact ⟨hgpos, (fun _ hx => by cases hx), rfl, trivial, hpo0, by linarith,
      by linarith, by linarith⟩
  | p1E =>
    rcases hst with ⟨rfl, hpo3, hW⟩
    cases g with
    | zero => omega
    | succ g' =>
      have hgQ : ((g' + 1 : ℕ) : ℚ) = (g' : ℚ) + 1 := by push_cast; ring
      have hg'0 : (0 : ℚ) ≤ (g' : ℚ) := Nat.cast_nonneg g'
      simp only [minGap2, step2, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by norm_num; linarith, trivial⟩,
        by norm_num; linarith, by linarith, by norm_num; linarith, by norm_num; linarith⟩
  | pE1 =>
    rcases hst with ⟨hW, hpo_adj⟩
    cases g with
    | zero => omega
    | succ g' =>
      have hgQ : ((g' + 1 : ℕ) : ℚ) = (g' : ℚ) + 1 := by push_cast; ring
      have hc2_eq : ((c + 2 : ℕ) : ℚ) = (c : ℚ) + 2 := by push_cast; ring
      have hg'0 : (0 : ℚ) ≤ (g' : ℚ) := Nat.cast_nonneg g'
      simp only [minGap2, step2, def2, endP, nextP, Inv2, AdjGoodFrom]
      refine ⟨by omega, (fun x hx => by simp at hx; omega), rfl, ⟨by linarith, trivial⟩,
        by linarith, by linarith, by linarith, by linarith⟩

theorem inv2_run (st : St2) (c : ℕ) (gs : List ℕ) (po pi : ℚ)
    (hinv : Inv2 st c po pi) (hpos : ∀ x ∈ gs, 1 ≤ x) (hgood : AdjGoodFrom pi gs) :
    Safe2 st gs ∧
    (∀ x ∈ (run2Aux st c gs).2.2, 1 ≤ x) ∧
    (run2Aux st c gs).2.2.length + def2 (run2Aux st c gs).1 = gs.length + def2 st ∧
    AdjGoodFrom po (run2Aux st c gs).2.2 ∧
    Inv2 (run2Aux st c gs).1 (run2Aux st c gs).2.1
      (endP po (run2Aux st c gs).2.2) (endP pi gs) := by
  induction gs generalizing st c po pi with
  | nil =>
    simp only [Safe2, run2Aux, List.length_nil, Nat.zero_add, endP, AdjGoodFrom]
    exact ⟨trivial, (fun _ hx => by cases hx), trivial, trivial, hinv⟩
  | cons g rest ih =>
    rcases hgood with ⟨h1, hrest_g⟩
    have hg : 1 ≤ g := hpos g (by simp)
    have hrest_pos : ∀ x ∈ rest, 1 ≤ x := fun x hx => hpos x (by simp [hx])
    rcases inv2_step st c g po pi hinv hg h1 with ⟨hmin, hall1, hlen1, hag1, hinv1⟩
    rcases ih (step2 st c g).1 (step2 st c g).2.1
      (endP po (step2 st c g).2.2) (nextP pi g) hinv1 hrest_pos hrest_g with
      ⟨hsafe2, hall2, hlen2, hag2, hinv2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [Safe2]
      rw [← step2_next_indep_c st c g]
      exact ⟨hmin, hsafe2⟩
    · simp only [run2Aux]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hall1 x h
      · exact hall2 x h
    · simp only [run2Aux, List.length_append, List.length_cons]
      omega
    · simp only [run2Aux]
      exact adjGood_append hag1 hag2
    · simp only [run2Aux]
      rw [endP_append]
      exact hinv2

theorem inv2_tail (st : St2) (c t : ℕ) (po pi : ℚ) (hinv : Inv2 st c po pi) :
    (∀ x ∈ (step2Tail st c t).1, 1 ≤ x) ∧
    (step2Tail st c t).1.length + 1 ≤ def2 st ∧
    AdjGoodFrom po (step2Tail st c t).1 := by
  rcases hinv with ⟨hpo0, hpi0, hst⟩
  have hc0 : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg c
  have hc1_eq : ((c + 1 : ℕ) : ℚ) = (c : ℚ) + 1 := by push_cast; ring
  have hc2_eq : ((c + 2 : ℕ) : ℚ) = (c : ℚ) + 2 := by push_cast; ring
  cases st with
  | p01 =>
    simp [step2Tail, def2, AdjGoodFrom]
  | p42 =>
    cases t <;> simp [step2Tail, def2, AdjGoodFrom]
  | p0E =>
    rcases hst with ⟨_, _, _, hpo_adj⟩
    match t with
    | 0 | 1 | 2 => simp [step2Tail, step2Tail0E, def2, AdjGoodFrom]
    | t' + 3 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by linarith, trivial⟩⟩
  | p41z =>
    rcases hst with ⟨rfl, _⟩
    match t with
    | 0 | 1 | 2 | 3 => simp [step2Tail, step2Tail0E, def2, AdjGoodFrom]
    | t' + 4 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by linarith, trivial⟩⟩
  | p41p =>
    rcases hst with ⟨_, _, _, hpo_adj⟩
    match t with
    | 0 | 1 | 2 | 3 => simp [step2Tail, step2Tail0E, def2, AdjGoodFrom]
    | t' + 4 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by linarith, trivial⟩⟩
  | p5 =>
    rcases hst with ⟨rfl, hpo3, _, _⟩
    match t with
    | 0 => simp [step2Tail, def2, AdjGoodFrom]
    | 1 | 2 | 3 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by norm_num; linarith, trivial⟩⟩
    | t' + 4 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_cons, List.length_nil]
      exact ⟨(fun x hx => by simp at hx; omega), by omega,
        ⟨by norm_num; linarith, by simp [nextP]; linarith, trivial⟩⟩
  | p4E =>
    rcases hst with ⟨_, hpo3, h3c6, _, _⟩
    match t with
    | 0 | 1 => simp [step2Tail, def2, AdjGoodFrom]
    | 2 | 3 | 4 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by linarith, trivial⟩⟩
    | t' + 5 =>
      simp only [step2Tail, step2Tail0E, def2, AdjGoodFrom, List.length_cons, List.length_nil]
      exact ⟨fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · cases List.mem_singleton.mp hx; omega,
        by omega,
        ⟨by linarith, by simp [nextP]; linarith, trivial⟩⟩
  | p11 => simp [step2Tail, def2, AdjGoodFrom]
  | p1E =>
    rcases hst with ⟨rfl, hpo3, _⟩
    cases t with
    | zero => simp [step2Tail, def2, AdjGoodFrom]
    | succ t' =>
      simp only [step2Tail, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by norm_num; linarith, trivial⟩⟩
  | pE1 =>
    rcases hst with ⟨_, hpo_adj⟩
    cases t with
    | zero => simp [step2Tail, def2, AdjGoodFrom]
    | succ t' =>
      simp only [step2Tail, def2, AdjGoodFrom, List.length_singleton]
      exact ⟨(fun x hx => by simp at hx; omega), by omega, ⟨by linarith, trivial⟩⟩

-- ============================================================================
-- Section 7: Phase-0 Split & Strong Induction (`main_stream`)
-- ============================================================================

-- Phase-0 single-step transitions on `(col0, col1)` with blank tail `default`:
-- `w0 +> w0 +> default` and `w4 +> w0 +> default` absorb `0`s directly into `default`!
theorem phase0_00_2 :
    RunEv (gapEv 2) (w0 +> (w0 +> default)) (w4 +> (w0 +> default)) :=
  RunEv.cons (stepEv_w0_B _)
    (RunEv.cons (stepEv_w2_B _) (runEv_single (stepEv_w3_S _)))

theorem phase0_00_3 :
    RunEv (gapEv 3) (w0 +> (w0 +> default)) (tok2 .p01 +> default) := by
  simp only [tok2, Counter.listblank_append_assoc]
  exact RunEv.cons (stepEv_w0_B _)
    (RunEv.cons (stepEv_w2_B _)
      (RunEv.cons (stepEv_w3_B (stepEv_w0_B default))
        (runEv_single (stepEv_w0_S (stepEv_w2_S default)))))

theorem phase0_00_5 :
    RunEv (gapEv 5) (w0 +> (w0 +> default)) (tok2 .p42 +> default) := by
  simp only [tok2, Counter.listblank_append_assoc]
  exact RunEv.cons (stepEv_w0_B _)
    (RunEv.cons (stepEv_w2_B _)
      (RunEv.cons (stepEv_w3_B (stepEv_w0_B default))
        (RunEv.cons (stepEv_w0_B _)
          (RunEv.cons (stepEv_w2_B _) (runEv_single (stepEv_w3_S _))))))

theorem phase0_40_1 :
    RunEv (gapEv 1) (w4 +> (w0 +> default)) (w0 +> (w0 +> default)) :=
  RunEv.cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S))
    (runEv_single (stepEv_w0_S (stepEv_w0_S stepEv_default_S)))

theorem phase0_40_3 :
    RunEv (gapEv 3) (w4 +> (w0 +> default)) (w4 +> (w0 +> default)) :=
  RunEv.cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S)) phase0_00_2

theorem phase0_40_4 :
    RunEv (gapEv 4) (w4 +> (w0 +> default)) (tok2 .p01 +> default) :=
  RunEv.cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S)) phase0_00_3

theorem phase0_40_6 :
    RunEv (gapEv 6) (w4 +> (w0 +> default)) (tok2 .p42 +> default) :=
  RunEv.cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S)) phase0_00_5

/-- Whenever `run1Full st 0 gs t` fails `isSafeZero` starting from `st ∈ {.s0, .s4}` (`c = 0`),
    Phase 0 (`w0 +> w0 +> default` / `w4 +> w0 +> default`) reaches `tok2 st_hit +> default`
    (`st_hit ∈ {.p01, .p42}`) with `Inv2 st_hit 0 0 pi_hit` and remaining suffix `suff` strictly
    shorter than `gs`! -/
theorem phase0_find_entry (st : St1) (gs : List ℕ) (t : ℕ) (pi : ℚ)
    (hst : st = .s0 ∨ st = .s4)
    (hpi : 0 ≤ pi ∧ (st = .s4 → 2 ≤ pi))
    (hpos : ∀ x ∈ gs, 1 ≤ x)
    (hgood : AdjGoodFrom pi gs)
    (hbad : isSafeZero (run1Full st 0 gs t).1 = false) :
    ∃ (pref suff : List ℕ) (st2 : St2) (pi2 : ℚ),
      gs = pref ++ suff ∧
      suff.length < gs.length ∧
      (st2 = .p01 ∨ st2 = .p42) ∧
      Inv2 st2 0 0 pi2 ∧
      AdjGoodFrom pi2 suff ∧
      RunEv (gapsEv pref) (tok1 st +> (w0 +> default)) (tok2 st2 +> default) := by
  induction gs generalizing st pi with
  | nil =>
    rcases hst with rfl | rfl
    · simp [run1Full, run1Aux, step1Tail, isSafeZero, stripLZ] at hbad
    · cases t <;> simp [run1Full, run1Aux, step1Tail, isSafeZero, stripLZ] at hbad
  | cons g rest ih =>
    rcases hgood with ⟨h1, hrest_g⟩
    have hg : 1 ≤ g := hpos g (by simp)
    have hrest_pos : ∀ x ∈ rest, 1 ≤ x := fun x hx => hpos x (by simp [hx])
    have hsafe_rest : ∀ s, Safe1 s rest := fun s => safe1_of_allPos s rest hrest_pos
    rcases hst with rfl | rfl
    · -- st = .s0 (`00`)
      match g with
      | 0 => omega
      | 1 =>
        have hall : ∀ x ∈ (run1Full .s1 0 rest t).1, 1 ≤ x :=
          run1Full_from_s1_allPos .s1 0 rest t (Or.inl rfl) hrest_pos
        have hok : isSafeZero (run1Full .s0 0 (1 :: rest) t).1 = true := by
          have : (run1Full .s0 0 (1 :: rest) t).1 = (run1Full .s1 0 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rw [this]; exact isSafeZero_of_allPos hall
        rw [hok] at hbad; cases hbad
      | 2 =>
        have hbad' : isSafeZero (run1Full .s4 0 rest t).1 = false := by
          have : (run1Full .s0 0 (2 :: rest) t).1 = (run1Full .s4 0 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rwa [this] at hbad
        have hpi' : 0 ≤ nextP pi 2 ∧ (St1.s4 = .s4 → 2 ≤ nextP pi 2) := by
          simp only [nextP, Nat.cast_ofNat]; exact ⟨by linarith, fun _ => by linarith⟩
        rcases ih .s4 (nextP pi 2) (Or.inr rfl) hpi' hrest_pos hrest_g hbad' with
          ⟨pref, suff, st2, pi2, heq, hlt, hst2, hinv2, hgsuff, hrun⟩
        exact ⟨2 :: pref, suff, st2, pi2, by rw [heq]; rfl, by simp; omega, hst2, hinv2, hgsuff,
          by simp only [gapsEv]; exact runEv_append phase0_00_2 hrun⟩
      | 3 =>
        refine ⟨[3], rest, .p01, nextP pi 3, rfl, by simp, Or.inl rfl, ?_, hrest_g, ?_⟩
        · refine ⟨le_refl 0, ?_, rfl, rfl, ?_⟩
          · simp only [nextP, Nat.cast_ofNat]; linarith
          · simp only [nextP, Nat.cast_ofNat]; linarith
        · simp only [gapsEv, List.append_nil]; exact phase0_00_3
      | 4 =>
        have hall : ∀ x ∈ (run1Full .s1 1 rest t).1, 1 ≤ x :=
          run1Full_from_s1_allPos .s1 1 rest t (Or.inl rfl) hrest_pos
        have hok : isSafeZero (run1Full .s0 0 (4 :: rest) t).1 = true := by
          have : (run1Full .s0 0 (4 :: rest) t).1 = (run1Full .s1 1 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rw [this]; exact isSafeZero_of_allPos hall
        rw [hok] at hbad; cases hbad
      | 5 =>
        refine ⟨[5], rest, .p42, nextP pi 5, rfl, by simp, Or.inr rfl, ?_, hrest_g, ?_⟩
        · refine ⟨le_refl 0, ?_, rfl, rfl, ?_⟩
          · simp only [nextP, Nat.cast_ofNat]; linarith
          · simp only [nextP, Nat.cast_ofNat]; linarith
        · simp only [gapsEv, List.append_nil]; exact phase0_00_5
      | g' + 6 =>
        have hg_ge6 : 6 ≤ g' + 6 := by omega
        have hq2 : 2 ≤ (g' + 6) / 3 := by omega
        have hinv0 : Inv1 .s0 0 0 pi := ⟨le_refl 0, hpi.1, rfl, by linarith⟩
        have hgood_all := inv1_full .s0 0 ((g' + 6) :: rest) t 0 pi hinv0
          ⟨h1, hrest_g⟩ (safe1_of_allPos .s0 ((g' + 6) :: rest) (by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · omega
            · exact hrest_pos x hx'))
        have hrem : (g' + 6) % 3 = 0 ∨ (g' + 6) % 3 = 1 ∨ (g' + 6) % 3 = 2 := by omega
        rcases hrem with h0 | h1m | h2m
        · -- emits q >= 2 immediately -> all subsequent elements >= 1!
          have heq_list : (run1Full .s0 0 ((g' + 6) :: rest) t).1 =
              ((g' + 6) / 3) :: (run1Full .s0 0 rest t).1 := by
            simp [run1Full, run1Aux, step1, h0]
          rw [heq_list] at hgood_all hbad
          rcases hgood_all with ⟨_, hrest_ag⟩
          have hp_gt : 3 < 2 * nextP 0 ((g' + 6) / 3) := by
            simp only [nextP]
            have : (2 : ℚ) ≤ (((g' + 6) / 3 : ℕ) : ℚ) := by exact_mod_cast hq2
            linarith
          have hall_rest := adjGood_no_zero_of_gt hrest_ag hp_gt
          have hok : isSafeZero (((g' + 6) / 3) :: (run1Full .s0 0 rest t).1) = true :=
            isSafeZero_of_allPos (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · omega
              · exact hall_rest x hx')
          rw [hok] at hbad; cases hbad
        · -- goes to s1 -> all subsequent elements >= 1!
          have hne0 : (1 == 0) = false := rfl
          have heq_list : (run1Full .s0 0 ((g' + 6) :: rest) t).1 =
              (run1Full .s1 ((g' + 6) / 3) rest t).1 := by
            simp [run1Full, run1Aux, step1, h1m, hne0]
          rw [heq_list] at hbad
          have hok := isSafeZero_of_allPos
            (run1Full_from_s1_allPos .s1 ((g' + 6) / 3) rest t (Or.inl rfl) hrest_pos)
          rw [hok] at hbad; cases hbad
        · -- goes to s4 with c = q >= 2!
          have hne0 : (2 == 0) = false := rfl
          have hne1 : (2 == 1) = false := rfl
          have heq_list : (run1Full .s0 0 ((g' + 6) :: rest) t).1 =
              (run1Full .s4 ((g' + 6) / 3) rest t).1 := by
            simp [run1Full, run1Aux, step1, h2m, hne0, hne1]
          rw [heq_list] at hgood_all hbad
          cases rest with
          | nil =>
            cases t with
            | zero => simp [run1Full, run1Aux, step1Tail, isSafeZero, stripLZ] at hbad
            | succ t' =>
              have hok : isSafeZero (run1Full .s4 ((g' + 6) / 3) [] (t' + 1)).1 = true := by
                simp only [run1Full, run1Aux, step1Tail, List.nil_append]
                exact isSafeZero_of_allPos (fun x hx => by simp at hx; omega)
              rw [hok] at hbad; cases hbad
          | cons g2 rest2 =>
            cases g2 with
            | zero => exact absurd (hrest_pos 0 (by simp)) (by decide)
            | succ g2' =>
              have hhead : ∃ tail_em, (run1Full .s4 ((g' + 6) / 3) ((g2' + 1) :: rest2) t).1 =
                  ((g' + 6) / 3) :: tail_em := by
                simp only [run1Full, run1Aux, step1]
                split
                · exact ⟨_, rfl⟩
                · split <;> exact ⟨_, rfl⟩
              rcases hhead with ⟨tail_em, hte⟩
              rw [hte] at hgood_all hbad
              rcases hgood_all with ⟨_, hrest_ag⟩
              have hp_gt : 3 < 2 * nextP 0 ((g' + 6) / 3) := by
                simp only [nextP]
                have : (2 : ℚ) ≤ (((g' + 6) / 3 : ℕ) : ℚ) := by exact_mod_cast hq2
                linarith
              have hall_rest := adjGood_no_zero_of_gt hrest_ag hp_gt
              have hok : isSafeZero (((g' + 6) / 3) :: tail_em) = true :=
                isSafeZero_of_allPos (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx'
                  · omega
                  · exact hall_rest x hx')
              rw [hok] at hbad; cases hbad
    · -- st = .s4 (`40`)
      have hpi2 : 2 ≤ pi := hpi.2 rfl
      match g with
      | 0 => omega
      | 1 =>
        have hbad' : isSafeZero (run1Full .s0 0 rest t).1 = false := by
          have : (run1Full .s4 0 (1 :: rest) t).1 = 0 :: 0 :: (run1Full .s0 0 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rw [this] at hbad
          simpa [isSafeZero, stripLZ] using hbad
        have hpi' : 0 ≤ nextP pi 1 ∧ (St1.s0 = .s4 → 2 ≤ nextP pi 1) := by
          simp only [nextP, Nat.cast_one]
          exact ⟨by linarith, fun h => by cases h⟩
        rcases ih .s0 (nextP pi 1) (Or.inl rfl) hpi' hrest_pos hrest_g hbad' with
          ⟨pref, suff, st2, pi2, heq, hlt, hst2, hinv2, hgsuff, hrun⟩
        exact ⟨1 :: pref, suff, st2, pi2, by rw [heq]; rfl, by simp; omega, hst2, hinv2, hgsuff,
          by simp only [gapsEv]; exact runEv_append phase0_40_1 hrun⟩
      | 2 =>
        have hall : ∀ x ∈ (run1Full .s1 0 rest t).1, 1 ≤ x :=
          run1Full_from_s1_allPos .s1 0 rest t (Or.inl rfl) hrest_pos
        have hok : isSafeZero (run1Full .s4 0 (2 :: rest) t).1 = true := by
          have : (run1Full .s4 0 (2 :: rest) t).1 = [0] ++ (run1Full .s1 0 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rw [this]
          exact isSafeZero_zeros_append (fun _ hx => List.mem_singleton.mp hx)
            (isSafeZero_of_allPos hall)
        rw [hok] at hbad; cases hbad
      | 3 =>
        have hbad' : isSafeZero (run1Full .s4 0 rest t).1 = false := by
          have : (run1Full .s4 0 (3 :: rest) t).1 = 0 :: (run1Full .s4 0 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rw [this] at hbad
          simpa [isSafeZero, stripLZ] using hbad
        have hpi' : 0 ≤ nextP pi 3 ∧ (St1.s4 = .s4 → 2 ≤ nextP pi 3) := by
          simp only [nextP, Nat.cast_ofNat]; exact ⟨by linarith, fun _ => by linarith⟩
        rcases ih .s4 (nextP pi 3) (Or.inr rfl) hpi' hrest_pos hrest_g hbad' with
          ⟨pref, suff, st2, pi2, heq, hlt, hst2, hinv2, hgsuff, hrun⟩
        exact ⟨3 :: pref, suff, st2, pi2, by rw [heq]; rfl, by simp; omega, hst2, hinv2, hgsuff,
          by simp only [gapsEv]; exact runEv_append phase0_40_3 hrun⟩
      | 4 =>
        refine ⟨[4], rest, .p01, nextP pi 4, rfl, by simp, Or.inl rfl, ?_, hrest_g, ?_⟩
        · refine ⟨le_refl 0, ?_, rfl, rfl, ?_⟩
          · simp only [nextP, Nat.cast_ofNat]; linarith
          · simp only [nextP, Nat.cast_ofNat]; linarith
        · simp only [gapsEv, List.append_nil]; exact phase0_40_4
      | 5 =>
        have hall : ∀ x ∈ (run1Full .s1 1 rest t).1, 1 ≤ x :=
          run1Full_from_s1_allPos .s1 1 rest t (Or.inl rfl) hrest_pos
        have hok : isSafeZero (run1Full .s4 0 (5 :: rest) t).1 = true := by
          have : (run1Full .s4 0 (5 :: rest) t).1 = [0] ++ (run1Full .s1 1 rest t).1 := by
            simp [run1Full, run1Aux, step1]
          rw [this]
          exact isSafeZero_zeros_append (fun _ hx => List.mem_singleton.mp hx)
            (isSafeZero_of_allPos hall)
        rw [hok] at hbad; cases hbad
      | 6 =>
        refine ⟨[6], rest, .p42, nextP pi 6, rfl, by simp, Or.inr rfl, ?_, hrest_g, ?_⟩
        · refine ⟨le_refl 0, ?_, rfl, rfl, ?_⟩
          · simp only [nextP, Nat.cast_ofNat]; linarith
          · simp only [nextP, Nat.cast_ofNat]; linarith
        · simp only [gapsEv, List.append_nil]; exact phase0_40_6
      | g' + 7 =>
        have hq2 : 2 ≤ (g' + 6) / 3 := by omega
        have hinv4 : Inv1 .s4 0 0 pi :=
          ⟨le_refl 0, hpi.1, hpi2, by norm_num; linarith, by norm_num⟩
        have hgood_all := inv1_full .s4 0 ((g' + 7) :: rest) t 0 pi hinv4
          ⟨h1, hrest_g⟩ (safe1_of_allPos .s4 ((g' + 7) :: rest) (by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · omega
            · exact hrest_pos x hx'))
        have hrem : (g' + 6) % 3 = 0 ∨ (g' + 6) % 3 = 1 ∨ (g' + 6) % 3 = 2 := by omega
        rcases hrem with h0 | h1m | h2m
        · have heq_list : (run1Full .s4 0 ((g' + 7) :: rest) t).1 =
              0 :: ((g' + 6) / 3) :: (run1Full .s0 0 rest t).1 := by
            simp [run1Full, run1Aux, step1, h0]
          rw [heq_list] at hgood_all hbad
          rcases hgood_all with ⟨_, _, hrest_ag⟩
          have hz : nextP 0 0 = 0 := by simp [nextP]
          rw [hz] at hrest_ag
          have hp_gt : 3 < 2 * nextP 0 ((g' + 6) / 3) := by
            simp only [nextP]
            have : (2 : ℚ) ≤ (((g' + 6) / 3 : ℕ) : ℚ) := by exact_mod_cast hq2
            linarith
          have hall_rest := adjGood_no_zero_of_gt hrest_ag hp_gt
          have hok : isSafeZero (0 :: ((g' + 6) / 3) :: (run1Full .s0 0 rest t).1) = true :=
            isSafeZero_zeros_append (zs := [0]) (fun _ hx => List.mem_singleton.mp hx)
              (isSafeZero_of_allPos (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx'
                · omega
                · exact hall_rest x hx'))
          rw [hok] at hbad; cases hbad
        · have hne0 : (1 == 0) = false := rfl
          have heq_list : (run1Full .s4 0 ((g' + 7) :: rest) t).1 =
              0 :: (run1Full .s1 ((g' + 6) / 3) rest t).1 := by
            simp [run1Full, run1Aux, step1, h1m, hne0]
          rw [heq_list] at hbad
          have hok : isSafeZero (0 :: (run1Full .s1 ((g' + 6) / 3) rest t).1) = true :=
            isSafeZero_zeros_append (zs := [0]) (fun _ hx => List.mem_singleton.mp hx)
              (isSafeZero_of_allPos
                (run1Full_from_s1_allPos .s1 ((g' + 6) / 3) rest t (Or.inl rfl) hrest_pos))
          rw [hok] at hbad; cases hbad
        · have hne0 : (2 == 0) = false := rfl
          have hne1 : (2 == 1) = false := rfl
          have heq_list : (run1Full .s4 0 ((g' + 7) :: rest) t).1 =
              0 :: (run1Full .s4 ((g' + 6) / 3) rest t).1 := by
            simp [run1Full, run1Aux, step1, h2m, hne0, hne1]
          rw [heq_list] at hgood_all hbad
          rcases hgood_all with ⟨_, hrest_ag0⟩
          have hz : nextP 0 0 = 0 := by simp [nextP]
          rw [hz] at hrest_ag0
          cases rest with
          | nil =>
            cases t with
            | zero => simp [run1Full, run1Aux, step1Tail, isSafeZero, stripLZ] at hbad
            | succ t' =>
              have hok : isSafeZero (0 :: (run1Full .s4 ((g' + 6) / 3) [] (t' + 1)).1) = true :=
                isSafeZero_zeros_append (zs := [0]) (fun _ hx => List.mem_singleton.mp hx) (by
                  simp only [run1Full, run1Aux, step1Tail, List.nil_append]
                  exact isSafeZero_of_allPos (fun x hx => by simp at hx; omega))
              rw [hok] at hbad; cases hbad
          | cons g2 rest2 =>
            cases g2 with
            | zero => exact absurd (hrest_pos 0 (by simp)) (by decide)
            | succ g2' =>
              have hhead : ∃ tail_em, (run1Full .s4 ((g' + 6) / 3) ((g2' + 1) :: rest2) t).1 =
                  ((g' + 6) / 3) :: tail_em := by
                simp only [run1Full, run1Aux, step1]
                split
                · exact ⟨_, rfl⟩
                · split <;> exact ⟨_, rfl⟩
              rcases hhead with ⟨tail_em, hte⟩
              rw [hte] at hrest_ag0 hbad
              rcases hrest_ag0 with ⟨_, hrest_ag⟩
              have hp_gt : 3 < 2 * nextP 0 ((g' + 6) / 3) := by
                simp only [nextP]
                have : (2 : ℚ) ≤ (((g' + 6) / 3 : ℕ) : ℚ) := by exact_mod_cast hq2
                linarith
              have hall_rest := adjGood_no_zero_of_gt hrest_ag hp_gt
              have hok : isSafeZero (0 :: ((g' + 6) / 3) :: tail_em) = true :=
                isSafeZero_zeros_append (zs := [0]) (fun _ hx => List.mem_singleton.mp hx)
                  (isSafeZero_of_allPos (fun x hx => by
                    rcases List.mem_cons.mp hx with rfl | hx'
                    · omega
                    · exact hall_rest x hx'))
              rw [hok] at hbad; cases hbad

/-- **Master Stream Execution Theorem** (strong induction on `(gs.length, gs.sum + t)`):
    Every `Good` and `isSafeZero` gap sequence `gs` followed by `t` trailing `B`s executes
    completely on the blank right half-tape `default` without halting or fusing out of invariant! -/
theorem main_stream : ∀ (n : ℕ) (m : ℕ) (gs : List ℕ) (t : ℕ),
    gs.length ≤ n → gs.sum + t ≤ m → Good gs → isSafeZero gs = true →
    ∃ r', RunEv (gapsEv gs ++ List.replicate t Ev.B) default r' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih_len =>
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih_sum =>
      intro gs t hlen hsum hgood hsafe
      cases gs with
      | nil =>
        simp only [gapsEv, List.nil_append]
        exact run_B_only t
      | cons g rest =>
        cases g with
        | zero =>
          -- Leading `0`: consume `S` directly on `default`!
          rcases hgood with ⟨_, hrest_g⟩
          have hz : nextP 0 0 = 0 := by simp [nextP]
          rw [hz] at hrest_g
          have hsafe' : isSafeZero rest = true := by simpa [isSafeZero, stripLZ] using hsafe
          have hlen' : rest.length ≤ n - 1 := by simp at hlen; omega
          have hlt_n : n - 1 < n := by simp at hlen; omega
          rcases ih_len (n - 1) hlt_n (rest.sum + t) rest t hlen' (le_refl _) hrest_g hsafe' with
            ⟨r', hr'⟩
          exact ⟨r', by
            simp only [gapsEv, gapEv, List.replicate_zero, List.nil_append, List.cons_append]
            exact RunEv.cons stepEv_default_S hr'⟩
        | succ g0 =>
          -- Non-empty, head `g0 + 1 >= 1`!
          set gs0 := (g0 + 1) :: rest
          have hgs_sum_pos : 1 ≤ gs0.sum := by simp [gs0]; omega
          -- Case split on whether `gs0` is `1 :: 0 :: rest'` or `AllPos gs0`!
          have hsplit : (∃ rest', gs0 = 1 :: 0 :: rest' ∧ ∀ x ∈ rest', 1 ≤ x) ∨
              (∀ x ∈ gs0, 1 ≤ x) := by
            cases g0 with
            | zero =>
              cases rest with
              | nil => exact Or.inr (fun x hx => by simp [gs0] at hx; omega)
              | cons r1 rs1 =>
                cases r1 with
                | zero =>
                  have hpos_rs : ∀ x ∈ rs1, 1 ≤ x := by
                    simp only [gs0, isSafeZero, stripLZ] at hsafe
                    exact isAllPos_eq_true_iff.mp hsafe
                  exact Or.inl ⟨rs1, rfl, hpos_rs⟩
                | succ r1' =>
                  have hpos_rest : ∀ x ∈ (r1' + 1) :: rs1, 1 ≤ x := by
                    simp only [gs0, isSafeZero, stripLZ, isAllPos] at hsafe
                    have htail := isAllPos_eq_true_iff.mp hsafe
                    intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx'
                    · omega
                    · exact htail x hx'
                  exact Or.inr (fun x hx => by
                    rcases List.mem_cons.mp hx with rfl | hx'
                    · omega
                    · exact hpos_rest x hx')
            | succ g0' =>
              have hpos_rest : ∀ x ∈ rest, 1 ≤ x := by
                simp only [gs0, isSafeZero, stripLZ, isAllPos] at hsafe
                exact isAllPos_eq_true_iff.mp hsafe
              exact Or.inr (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx'
                · omega
                · exact hpos_rest x hx')
          have hsafe1 : Safe1 .s0 gs0 := by
            rcases hsplit with ⟨rest', heq, hpos'⟩ | hpos
            · rw [heq]
              refine ⟨(fun h => by rcases h with h | h <;> cases h), ?_⟩
              simp only [step1]
              refine ⟨(fun h => by rcases h with h | h <;> cases h), ?_⟩
              exact safe1_of_allPos .sE rest' hpos'
            · exact safe1_of_allPos .s0 gs0 hpos
          set res1 := run1Full .s0 0 gs0 t
          have hinv0 : Inv1 .s0 0 0 0 := ⟨le_refl 0, le_refl 0, rfl, by norm_num⟩
          have hgood1 : Good res1.1 := inv1_full .s0 0 gs0 t 0 0 hinv0 hgood hsafe1
          cases hsf1 : isSafeZero res1.1 with
          | true =>
            -- PEEL 1 CELL!
            have hdef := run1Aux_def_eq .s0 0 gs0 hsafe1
            have hrun_child : ∃ r1', RunEv (gapsEv res1.1 ++ List.replicate res1.2 Ev.B) default
              r1' := by
              cases hst_end : (run1Aux .s0 0 gs0).1 with
              | s1 =>
                have hlt_len : res1.1.length < gs0.length := by
                  change ((run1Aux .s0 0 gs0).2.2 ++
                    (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 t).1).length <
                    gs0.length
                  rw [hst_end] at hdef ⊢
                  simp only [step1Tail, def1, List.append_nil] at hdef ⊢
                  omega
                have hlt_n : n - 1 < n := by simp [gs0] at hlen; omega
                exact ih_len (n - 1) hlt_n (res1.1.sum + res1.2) res1.1 res1.2
                  (by omega) (le_refl _) hgood1 hsf1
              | sE =>
                have hlt_len : res1.1.length < gs0.length := by
                  change ((run1Aux .s0 0 gs0).2.2 ++
                    (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 t).1).length <
                    gs0.length
                  rw [hst_end] at hdef ⊢
                  simp only [def1, List.length_append] at hdef ⊢
                  cases t <;> simp [step1Tail] <;> omega
                have hlt_n : n - 1 < n := by simp [gs0] at hlen; omega
                exact ih_len (n - 1) hlt_n (res1.1.sum + res1.2) res1.1 res1.2
                  (by omega) (le_refl _) hgood1 hsf1
              | s0 =>
                have hlen_le : res1.1.length ≤ n := by
                  change ((run1Aux .s0 0 gs0).2.2 ++
                    (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 t).1).length ≤ n
                  rw [hst_end] at hdef ⊢
                  simp only [step1Tail, def1, List.append_nil] at hdef ⊢
                  omega
                have hbud := run1Aux_stay_base3_budget .s0 0 gs0 hsafe1
                  (Or.inl hst_end) (Or.inl rfl)
                have hsum_lt : res1.1.sum + res1.2 < m := by
                  change ((run1Aux .s0 0 gs0).2.2 ++
                    (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 t).1).sum +
                    (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 t).2 < m
                  rw [hst_end]
                  simp only [step1Tail, List.append_nil]
                  omega
                exact ih_sum (res1.1.sum + res1.2) hsum_lt res1.1 res1.2
                  hlen_le (le_refl _) hgood1 hsf1
              | s4 =>
                cases t with
                | zero =>
                  have hlt_len : res1.1.length < gs0.length := by
                    change ((run1Aux .s0 0 gs0).2.2 ++
                      (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 0).1).length <
                      gs0.length
                    rw [hst_end] at hdef ⊢
                    simp only [step1Tail, def1, List.append_nil] at hdef ⊢
                    omega
                  have hlt_n : n - 1 < n := by simp [gs0] at hlen; omega
                  exact ih_len (n - 1) hlt_n (res1.1.sum + res1.2) res1.1 res1.2
                    (by omega) (le_refl _) hgood1 hsf1
                | succ t' =>
                  have hlen_le : res1.1.length ≤ n := by
                    change ((run1Aux .s0 0 gs0).2.2 ++
                      (step1Tail (run1Aux .s0 0 gs0).1
                        (run1Aux .s0 0 gs0).2.1 (t' + 1)).1).length ≤ n
                    rw [hst_end] at hdef ⊢
                    simp only [step1Tail, def1, List.length_append, List.length_singleton] at hdef ⊢
                    omega
                  have hbud := run1Aux_stay_base3_budget .s0 0 gs0 hsafe1
                    (Or.inr hst_end) (Or.inl rfl)
                  have hsum_lt : res1.1.sum + res1.2 < m := by
                    change ((run1Aux .s0 0 gs0).2.2 ++
                      (step1Tail (run1Aux .s0 0 gs0).1
                        (run1Aux .s0 0 gs0).2.1 (t' + 1)).1).sum +
                      (step1Tail (run1Aux .s0 0 gs0).1 (run1Aux .s0 0 gs0).2.1 (t' + 1)).2 < m
                    rw [hst_end]
                    simp only [step1Tail, List.sum_append, List.sum_singleton]
                    omega
                  exact ih_sum (res1.1.sum + res1.2) hsum_lt res1.1 res1.2
                    hlen_le (le_refl _) hgood1 hsf1
            rcases hrun_child with ⟨r1', hr1'⟩
            have hev_eq := rep_B_run1Evs .s0 0 gs0 t hsafe1
            simp only [List.replicate_zero, List.nil_append] at hev_eq
            rw [← hev_eq] at hr1'
            rcases lift1_run .s0 gs0 t hsafe1 hr1' with ⟨r_out, hrun_out⟩
            rw [tok1, w0_append_default] at hrun_out
            exact ⟨r_out, hrun_out⟩
          | false =>
            -- PEEL 2 CELLS!
            -- First rule out `gs0 = 1 :: 0 :: rest'`: its 1-cell output is all positive!
            have hpos_gs0 : ∀ x ∈ gs0, 1 ≤ x := by
              rcases hsplit with ⟨rest', heq, hpos'⟩ | hpos
              · exfalso
                have hall := run1Full_from_s0_1_0_allPos rest' t hpos'
                rw [← heq] at hall
                have hok := isSafeZero_of_allPos hall
                rw [hok] at hsf1; cases hsf1
              · exact hpos
            rcases phase0_find_entry .s0 gs0 t 0 (Or.inl rfl)
              ⟨le_refl 0, fun h => by cases h⟩ hpos_gs0 hgood hsf1 with
              ⟨pref, suff, st2, pi2, heq_gs, hlt_suff, hst2, hinv2, hgood_suff, hrun_pref⟩
            have hpos_suff : ∀ x ∈ suff, 1 ≤ x := fun x hx =>
              hpos_gs0 x (by rw [heq_gs]; exact List.mem_append_right pref hx)
            rcases inv2_run st2 0 suff 0 pi2 hinv2 hpos_suff hgood_suff with
              ⟨hsafe2, hall2_aux, hlen2_aux, hag2_aux, hinv2_end⟩
            rcases inv2_tail (run2Aux st2 0 suff).1 (run2Aux st2 0 suff).2.1 t
              (endP 0 (run2Aux st2 0 suff).2.2) (endP pi2 suff) hinv2_end with
              ⟨hall2_tail, hlen2_tail, hag2_tail⟩
            set res2 := run2Full st2 0 suff t
            have hgood2 : Good res2.1 := adjGood_append hag2_aux hag2_tail
            have hall2 : ∀ x ∈ res2.1, 1 ≤ x := by
              intro x hx
              rcases List.mem_append.mp hx with h | h
              · exact hall2_aux x h
              · exact hall2_tail x h
            have hsafe_res2 : isSafeZero res2.1 = true := isSafeZero_of_allPos hall2
            have hdef_st2 : def2 st2 = 1 := by rcases hst2 with rfl | rfl <;> rfl
            have hlen2_lt : res2.1.length < gs0.length := by
              simp only [res2, run2Full, List.length_append]
              omega
            have hlt_n : n - 1 < n := by simp [gs0] at hlen; omega
            rcases ih_len (n - 1) hlt_n (res2.1.sum + res2.2) res2.1 res2.2
              (by omega) (le_refl _) hgood2 hsafe_res2 with ⟨r2', hr2'⟩
            have hev2_eq := rep_B_run2Evs st2 0 suff t hsafe2
            simp only [List.replicate_zero, List.nil_append] at hev2_eq
            rw [← hev2_eq] at hr2'
            rcases lift2_run st2 suff t hsafe2 hr2' with ⟨r_out, hrun_suff⟩
            have hstart : tok1 .s0 +> (w0 +> default) = (default : ListBlank (Fin 2)) := by
              simp [tok1, w0_append_default]
            rw [hstart] at hrun_pref
            exact ⟨r_out, by
              rw [heq_gs, gapsEv_append, List.append_assoc]
              exact runEv_append hrun_pref hrun_suff⟩

--

-- ============================================================================
-- Section 8: Initial Reachability (`init [] ⊢^{6937} conjCfg (era 18 (w2 +> default))`)
-- ============================================================================

def c_0 : Counter.CCfg (Fin 2) (Fin 6) := ⟨0, 0, [], []⟩
def c_400 : Counter.CCfg (Fin 2) (Fin 6) := ⟨0, 0, [1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1,
  1, 0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 1]⟩
def c_800 : Counter.CCfg (Fin 2) (Fin 6) := ⟨3, 0, [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0, 0, 0, 1]⟩
def c_1200 : Counter.CCfg (Fin 2) (Fin 6) := ⟨4, 1, [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1]⟩
def c_1600 : Counter.CCfg (Fin 2) (Fin 6) := ⟨0, 1, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 0,
  1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]⟩
def c_2000 : Counter.CCfg (Fin 2) (Fin 6) := ⟨3, 1, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0,
  1, 1]⟩
def c_2400 : Counter.CCfg (Fin 2) (Fin 6) := ⟨2, 1, [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0, 0, 1, 1, 0, 0,
  0, 0, 0, 0, 1, 1]⟩
def c_2800 : Counter.CCfg (Fin 2) (Fin 6) := ⟨4, 1, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
  1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0,
  0, 0, 0, 0, 0, 1]⟩
def c_3200 : Counter.CCfg (Fin 2) (Fin 6) := ⟨3, 0, [1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0,
  1], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]⟩
def c_3600 : Counter.CCfg (Fin 2) (Fin 6) := ⟨3, 1, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
  0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1,
  0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩
def c_4000 : Counter.CCfg (Fin 2) (Fin 6) := ⟨4, 1, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
  1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1]⟩
def c_4400 : Counter.CCfg (Fin 2) (Fin 6) := ⟨2, 1, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1]⟩
def c_4800 : Counter.CCfg (Fin 2) (Fin 6) := ⟨2, 1, [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩
def c_5200 : Counter.CCfg (Fin 2) (Fin 6) := ⟨5, 0, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 1, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩
def c_5600 : Counter.CCfg (Fin 2) (Fin 6) := ⟨0, 0, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1], [1, 1,
  0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1]⟩
def c_6000 : Counter.CCfg (Fin 2) (Fin 6) := ⟨0, 0, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 1], [1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]⟩
def c_6400 : Counter.CCfg (Fin 2) (Fin 6) := ⟨1, 0, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
  1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
  1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1]⟩
def c_6800 : Counter.CCfg (Fin 2) (Fin 6) := ⟨2, 0, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
  1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
  [0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1]⟩
def c_6937 : Counter.CCfg (Fin 2) (Fin 6) := ⟨2, 0, [], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
  1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1]⟩
theorem bstep_0_400 : Counter.bmultiStep target_tm 400 c_0 = some c_400 := by decide +kernel
theorem bstep_400_800 : Counter.bmultiStep target_tm 400 c_400 = some c_800 := by decide +kernel
theorem bstep_800_1200 : Counter.bmultiStep target_tm 400 c_800 = some c_1200 := by decide +kernel
theorem bstep_1200_1600 : Counter.bmultiStep target_tm 400 c_1200 = some c_1600 := by decide +kernel
theorem bstep_1600_2000 : Counter.bmultiStep target_tm 400 c_1600 = some c_2000 := by decide +kernel
theorem bstep_2000_2400 : Counter.bmultiStep target_tm 400 c_2000 = some c_2400 := by decide +kernel
theorem bstep_2400_2800 : Counter.bmultiStep target_tm 400 c_2400 = some c_2800 := by decide +kernel
theorem bstep_2800_3200 : Counter.bmultiStep target_tm 400 c_2800 = some c_3200 := by decide +kernel
theorem bstep_3200_3600 : Counter.bmultiStep target_tm 400 c_3200 = some c_3600 := by decide +kernel
theorem bstep_3600_4000 : Counter.bmultiStep target_tm 400 c_3600 = some c_4000 := by decide +kernel
theorem bstep_4000_4400 : Counter.bmultiStep target_tm 400 c_4000 = some c_4400 := by decide +kernel
theorem bstep_4400_4800 : Counter.bmultiStep target_tm 400 c_4400 = some c_4800 := by decide +kernel
theorem bstep_4800_5200 : Counter.bmultiStep target_tm 400 c_4800 = some c_5200 := by decide +kernel
theorem bstep_5200_5600 : Counter.bmultiStep target_tm 400 c_5200 = some c_5600 := by decide +kernel
theorem bstep_5600_6000 : Counter.bmultiStep target_tm 400 c_5600 = some c_6000 := by decide +kernel
theorem bstep_6000_6400 : Counter.bmultiStep target_tm 400 c_6000 = some c_6400 := by decide +kernel
theorem bstep_6400_6800 : Counter.bmultiStep target_tm 400 c_6400 = some c_6800 := by decide +kernel
theorem bstep_6800_6937 : Counter.bmultiStep target_tm 137 c_6800 = some c_6937 := by decide +kernel

theorem evalBCfg_c6937_eq :
    Counter.evalBCfg c_6937 =
      Counter.conjCfg isoPerm false (eraCfg 18 (w2 +> default)) := by
  have hlist : c_6937.r = w1 ^ 18 ++ (w0 ++ (wE ++ w2)) := by decide
  have hr : c_6937.r +> (default : ListBlank (Fin 2)) =
      w1 ^ 18 +> (w0 +> (wE +> (w2 +> default))) := by
    rw [hlist, Counter.listblank_append_assoc, Counter.listblank_append_assoc,
      Counter.listblank_append_assoc]
  have hdef : Counter.evalBCfg c_6937 =
      (⟨some (2 : Fin 6), ⟨(0 : Fin 2), default, c_6937.r +> default⟩⟩ : Cfg (Fin 2) (Fin 6)) := rfl
  rw [hdef, hr]
  rfl

theorem init_reaches_era18 :
    (init []) [target_tm]⊢^{6937}
      Counter.conjCfg isoPerm false (eraCfg 18 (w2 +> default)) := by
  have h0 := Counter.bmultiStep_sound 400 c_0 c_400 bstep_0_400
  have h1 := Counter.bmultiStep_sound 400 c_400 c_800 bstep_400_800
  have h2 := Counter.bmultiStep_sound 400 c_800 c_1200 bstep_800_1200
  have h3 := Counter.bmultiStep_sound 400 c_1200 c_1600 bstep_1200_1600
  have h4 := Counter.bmultiStep_sound 400 c_1600 c_2000 bstep_1600_2000
  have h5 := Counter.bmultiStep_sound 400 c_2000 c_2400 bstep_2000_2400
  have h6 := Counter.bmultiStep_sound 400 c_2400 c_2800 bstep_2400_2800
  have h7 := Counter.bmultiStep_sound 400 c_2800 c_3200 bstep_2800_3200
  have h8 := Counter.bmultiStep_sound 400 c_3200 c_3600 bstep_3200_3600
  have h9 := Counter.bmultiStep_sound 400 c_3600 c_4000 bstep_3600_4000
  have h10 := Counter.bmultiStep_sound 400 c_4000 c_4400 bstep_4000_4400
  have h11 := Counter.bmultiStep_sound 400 c_4400 c_4800 bstep_4400_4800
  have h12 := Counter.bmultiStep_sound 400 c_4800 c_5200 bstep_4800_5200
  have h13 := Counter.bmultiStep_sound 400 c_5200 c_5600 bstep_5200_5600
  have h14 := Counter.bmultiStep_sound 400 c_5600 c_6000 bstep_5600_6000
  have h15 := Counter.bmultiStep_sound 400 c_6000 c_6400 bstep_6000_6400
  have h16 := Counter.bmultiStep_sound 400 c_6400 c_6800 bstep_6400_6800
  have h17 := Counter.bmultiStep_sound 137 c_6800 c_6937 bstep_6800_6937
  have h := Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _
    _ (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (Counter.multiStep_trans target_tm _ _ _ _ _
    (Counter.multiStep_trans target_tm _ _ _ _ _ (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10)
    h11) h12) h13) h14) h15) h16) h17
  rw [evalBCfg_c6937_eq] at h
  exact h

-- ============================================================================
-- Section 9: Peeling Initial `w2` Cell & Final E1-Transported `IsNotHalt` Proof
-- ============================================================================

def eraStream347 : ℕ → List Ev
  | 0 => []
  | N + 1 => eraStream347 N ++ eraEvents (18 + N)

def tailSeq347 : ℕ → List ℕ
  | 0 => []
  | N + 1 => tailSeq347 N ++ [(18 + N) / 3 + 1]

theorem eraStream347_eq_gapsEv (N : ℕ) :
    eraStream347 N ++ [Ev.B, Ev.S] = gapsEv (1 :: tailSeq347 N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [eraStream347, eraEvents]
    have hg : gapsEv (1 :: tailSeq347 (N + 1)) =
        gapsEv (1 :: tailSeq347 N) ++ gapEv ((18 + N) / 3 + 1) := by
      change gapsEv ((1 :: tailSeq347 N) ++ [(18 + N) / 3 + 1]) = _
      simp only [gapsEv_append, gapsEv, List.append_nil]
    rw [hg, ← ih]
    simp only [gapEv]
    have hrep : List.replicate ((18 + N) / 3 + 1) Ev.B =
        List.replicate ((18 + N) / 3) Ev.B ++ [Ev.B] := by
      rw [List.replicate_add]; rfl
    rw [hrep]
    simp only [List.append_assoc]
    rfl

theorem tailSeq347_allPos (N : ℕ) : ∀ x ∈ tailSeq347 N, 1 ≤ x := by
  induction N with
  | zero => intro x hx; cases hx
  | succ N ih =>
    intro x hx
    simp only [tailSeq347] at hx
    rcases List.mem_append.mp hx with h | h
    · exact ih x h
    · simp at h; omega

theorem tailSeq347_good_from_2 (N : ℕ) :
    AdjGoodFrom 2 (tailSeq347 N) ∧
      2 * endP 2 (tailSeq347 N) ≤ 3 * (((18 + N) / 3 + 1 : ℕ) : ℚ) := by
  induction N with
  | zero =>
    refine ⟨trivial, ?_⟩
    simp only [tailSeq347, endP]
    norm_num
  | succ N ih =>
    rcases ih with ⟨hgN, hendN⟩
    set x := (18 + N) / 3 + 1
    have hstep_ag : AdjGoodFrom (endP 2 (tailSeq347 N)) [x] := ⟨by linarith, trivial⟩
    have hgood_succ : AdjGoodFrom 2 (tailSeq347 (N + 1)) := adjGood_append hgN hstep_ag
    have hmono : x ≤ (18 + (N + 1)) / 3 + 1 := by omega
    have hmonoQ : (x : ℚ) ≤ (((18 + (N + 1)) / 3 + 1 : ℕ) : ℚ) := by exact_mod_cast hmono
    refine ⟨hgood_succ, ?_⟩
    simp only [tailSeq347]
    rw [endP_append]
    simp only [endP, nextP]
    linarith

theorem tailSeq347_cons_prefix (N : ℕ) :
    (N = 0 ∧ tailSeq347 N = []) ∨
    (N = 1 ∧ tailSeq347 N = [7]) ∨
    (∃ rest, tailSeq347 N = 7 :: 7 :: rest ∧ ∀ x ∈ rest, 1 ≤ x) := by
  match N with
  | 0 => exact Or.inl ⟨rfl, rfl⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, by simp [tailSeq347]⟩)
  | k + 2 =>
    refine Or.inr (Or.inr ?_)
    induction k with
    | zero => exact ⟨[], by simp [tailSeq347], fun _ hx => by cases hx⟩
    | succ k ih =>
      rcases ih with ⟨rest, hrest, hpos⟩
      refine ⟨rest ++ [(18 + (k + 2)) / 3 + 1], ?_, ?_⟩
      · change tailSeq347 (k + 2) ++ [(18 + (k + 2)) / 3 + 1] =
            7 :: 7 :: (rest ++ [(18 + (k + 2)) / 3 + 1])
        rw [hrest]
        rfl
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hpos x h
        · simp at h; omega

theorem run1_tailSeq347_safe (N : ℕ) :
    isSafeZero (run1Full .s4 0 (tailSeq347 N) 0).1 = true := by
  rcases tailSeq347_cons_prefix N with ⟨_, h0⟩ | ⟨_, h1⟩ | ⟨rest, hrest, hpos⟩
  · rw [h0]; rfl
  · rw [h1]; decide
  · rw [hrest]
    have heq : (run1Full .s4 0 (7 :: 7 :: rest) 0).1 =
        [0] ++ (2 :: (run1Full .s1 2 rest 0).1) := by
      simp [run1Full, run1Aux, step1]
    rw [heq]
    apply isSafeZero_zeros_append (fun _ hx => List.mem_singleton.mp hx)
    have hall := run1Full_from_s1_allPos .s1 2 rest 0 (Or.inl rfl) hpos
    exact isSafeZero_of_allPos (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · exact hall x hx')

theorem eraStream347_runs (N : ℕ) : ∃ r', RunEv (eraStream347 N) (w2 +> default) r' := by
  have hpos := tailSeq347_allPos N
  have hsafe1 : Safe1 .s4 (tailSeq347 N) := safe1_of_allPos .s4 (tailSeq347 N) hpos
  have hinv4 : Inv1 .s4 0 0 2 := ⟨le_refl 0, by norm_num, le_refl 2, by norm_num, by norm_num⟩
  have hgood1 : Good (run1Full .s4 0 (tailSeq347 N) 0).1 :=
    inv1_full .s4 0 (tailSeq347 N) 0 0 2 hinv4 (tailSeq347_good_from_2 N).1 hsafe1
  have hsf1 : isSafeZero (run1Full .s4 0 (tailSeq347 N) 0).1 = true :=
    run1_tailSeq347_safe N
  set res := run1Full .s4 0 (tailSeq347 N) 0
  rcases main_stream res.1.length (res.1.sum + res.2) res.1 res.2
    (le_refl _) (le_refl _) hgood1 hsf1 with ⟨r1, hr1⟩
  have hev_eq := rep_B_run1Evs .s4 0 (tailSeq347 N) 0 hsafe1
  simp only [List.replicate_zero, List.nil_append] at hev_eq
  rw [← hev_eq] at hr1
  rcases lift1_run .s4 (tailSeq347 N) 0 hsafe1 hr1 with ⟨r_end, hrun_tail⟩
  simp only [List.replicate_zero, List.append_nil, tok1] at hrun_tail
  have hstep1 : RunEv (gapEv 1) (w2 +> default) (w4 +> default) :=
    RunEv.cons (stepEv_w2_B default) (runEv_single (stepEv_w3_S default))
  have hfull : RunEv (gapsEv (1 :: tailSeq347 N)) (w2 +> default) r_end :=
    runEv_append hstep1 hrun_tail
  rw [← eraStream347_eq_gapsEv N] at hfull
  rcases runEv_prefix hfull with ⟨r', hr', _⟩
  exact ⟨r', hr'⟩

theorem multi_era347_reach (N : ℕ) {r r' : ListBlank (Fin 2)}
    (h : RunEv (eraStream347 N) r r') :
    ∃ M ≥ N, (eraCfg 18 r) [tm762]⊢^{M} eraCfg (18 + N) r' := by
  induction N generalizing r' with
  | zero =>
    cases h
    exact ⟨0, le_refl 0, rfl⟩
  | succ N ih =>
    simp only [eraStream347] at h
    rcases runEv_prefix h with ⟨r_mid, hpre, hlast⟩
    rcases ih hpre with ⟨M1, hM1, hms1⟩
    rcases era_step (18 + N) (by omega) hlast with ⟨k, hk_pos, hms2⟩
    refine ⟨M1 + k, by omega, ?_⟩
    have h_add : 18 + (N + 1) = (18 + N) + 1 := by omega
    rw [h_add]
    exact multiStep_trans_local hms1 hms2

theorem isSome_of_multiStep_add {c c' : Cfg (Fin 2) (Fin 6)} {j d : ℕ}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [BusyBeaver.multiStep_add] at h
  cases hj : multiStep target_tm c j with
  | none => rw [hj] at h; cases h
  | some _ => rfl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases eraStream347_runs (n + 1) with ⟨r', hr'⟩
  rcases multi_era347_reach (n + 1) hr' with ⟨M, hM, hmsM⟩
  have hconj : (Counter.conjCfg isoPerm false (eraCfg 18 (w2 +> default))) [target_tm]⊢^{M}
      Counter.conjCfg isoPerm false (eraCfg (18 + (n + 1)) r') := by
    rw [Counter.multiStep_conj_of_tableIso tm347_iso_tm762, hmsM, Option.map_some]
  have htot : (init []) [target_tm]⊢^{6937 + M}
      Counter.conjCfg isoPerm false (eraCfg (18 + (n + 1)) r') :=
    Counter.multiStep_trans target_tm _ _ _ 6937 M init_reaches_era18 hconj
  have hge : n + 1 ≤ 6937 + M := by omega
  have heq : (n + 1) + (6937 + M - (n + 1)) = 6937 + M := Nat.add_sub_of_le hge
  rw [← heq] at htot
  have hsome := isSome_of_multiStep_add htot
  rw [BusyBeaver.multiStep_add, hn] at hsome
  exact hsome


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC
