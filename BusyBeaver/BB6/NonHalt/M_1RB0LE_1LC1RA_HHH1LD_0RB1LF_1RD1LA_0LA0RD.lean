/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_0LA0RD` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_0LA0RD`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1LC1RA_HHH1LD_0RB1LF_1RD1LA_0LA0RD

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_0LA0RD`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 3, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

abbrev b0 : Fin 2 := 0
abbrev b1 : Fin 2 := 1

@[reducible] def c0 (l : ListBlank (Fin 2)) : ListBlank (Fin 2) := ListBlank.cons b0 l
@[reducible] def c1 (l : ListBlank (Fin 2)) : ListBlank (Fin 2) := ListBlank.cons b1 l

def cfg (q : Fin 6) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some q, ⟨r.head, l, r.tail⟩⟩

@[simp] lemma zero_cons_default : ListBlank.cons (0 : Fin 2) default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = b0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

lemma init_eq_cfg : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = cfg A default default := rfl

lemma multiStep_succ_of_step {c c' : Cfg (Fin 2) (Fin 6)} (n : ℕ)
    (h : step target_tm c = some c') :
    multiStep target_tm c (n + 1) = multiStep target_tm c' n := by
  unfold multiStep
  rw [Function.iterate_succ_apply]
  change (Option.bind · (step target_tm))^[n] (step target_tm c) = _
  rw [h]

@[simp] lemma multiStep_succ_end (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep target_tm c (n + 1) = Option.bind (multiStep target_tm c n) (step target_tm) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma multiStep_add (c₁ : Cfg (Fin 2) (Fin 6)) (n m : Nat) :
    multiStep target_tm c₁ (n + m) = (multiStep target_tm c₁ n).bind (fun c₂ => multiStep target_tm c₂ m) := by
  induction m with
  | zero => simp [multiStep]
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ_end, ih, Option.bind_assoc]
    simp_rw [multiStep_succ_end]

lemma multiStep_trans (c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)) (n m : Nat)
    (h₁ : multiStep target_tm c₁ n = some c₂) (h₂ : multiStep target_tm c₂ m = some c₃) :
    multiStep target_tm c₁ (n + m) = some c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : Nat}
    (h : multiStep target_tm c k = none) (d : Nat) :
    multiStep target_tm c (k + d) = none := by
  rw [multiStep_add, h]; rfl

inductive StepsStar : Cfg (Fin 2) (Fin 6) → Cfg (Fin 2) (Fin 6) → Prop
  | refl (c) : StepsStar c c
  | next {c c₁ c₂} : step target_tm c = some c₁ → StepsStar c₁ c₂ → StepsStar c c₂

def StepsPlus (c₁ c₂ : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ c', step target_tm c₁ = some c' ∧ StepsStar c' c₂

lemma StepsStar.trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : StepsStar c₁ c₂) (h₂ : StepsStar c₂ c₃) : StepsStar c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | next hs _ ih => exact StepsStar.next hs (ih h₂)

lemma StepsStar.to_multiStep {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : StepsStar c₁ c₂) : ∃ n, multiStep target_tm c₁ n = some c₂ := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | next hs _ ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, by rw [multiStep_succ_of_step n hs, hn]⟩

lemma StepsPlus.trans_star {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : StepsPlus c₁ c₂) (h₂ : StepsStar c₂ c₃) : StepsPlus c₁ c₃ := by
  rcases h₁ with ⟨c', hs, hstar⟩
  exact ⟨c', hs, StepsStar.trans hstar h₂⟩

lemma StepsStar.trans_plus {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : StepsStar c₁ c₂) (h₂ : StepsPlus c₂ c₃) : StepsPlus c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | next hs _ ih =>
    rcases ih h₂ with ⟨c', hs', hstar'⟩
    exact ⟨_, hs, StepsStar.next hs' hstar'⟩

lemma StepsPlus.trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : StepsPlus c₁ c₂) (h₂ : StepsPlus c₂ c₃) : StepsPlus c₁ c₃ := by
  rcases h₁ with ⟨c', hs, hstar⟩
  exact ⟨c', hs, StepsPlus.trans_star (StepsStar.trans_plus hstar h₂) (StepsStar.refl _) |> fun ⟨c'', hs'', hst⟩ => StepsStar.next hs'' hst⟩

lemma StepsPlus.to_multiStep {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : StepsPlus c₁ c₂) : ∃ n > 0, multiStep target_tm c₁ n = some c₂ := by
  rcases h with ⟨c', hs, hstar⟩
  rcases hstar.to_multiStep with ⟨n, hn⟩
  exact ⟨n + 1, by omega, by rw [multiStep_succ_of_step n hs, hn]⟩

-- ============================================================================
-- Canonical Tape Encodings `L1`, `R1`, `R01`, and `Hub`
-- ============================================================================

def L1 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, l => l
  | n + 1, l => c1 (L1 n l)

def R1 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | n + 1, r => c1 (R1 n r)

def R01 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | n + 1, r => c0 (c1 (R01 n r))

lemma step_cfg_right {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.right))
    (l r : ListBlank (Fin 2)) :
    step target_tm (cfg q l (ListBlank.cons b r)) = some (cfg q' (ListBlank.cons a l) r) := by
  simp [cfg, step, h, Turing.Tape.write, Turing.Tape.move]

lemma step_cfg_left {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    (c : Fin 2) (l r : ListBlank (Fin 2)) :
    step target_tm (cfg q (ListBlank.cons c l) (ListBlank.cons b r)) =
      some (cfg q' l (ListBlank.cons c (ListBlank.cons a r))) := by
  simp [cfg, step, h, Turing.Tape.write, Turing.Tape.move]

lemma step_cfg_right_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q (0 : Fin 2) = some (some q', Stmt.write a Dir.right))
    (l : ListBlank (Fin 2)) :
    step target_tm (cfg q l default) = some (cfg q' (ListBlank.cons a l) default) := by
  simpa using step_cfg_right h l default

lemma step_cfg_left_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q (0 : Fin 2) = some (some q', Stmt.write a Dir.left))
    (c : Fin 2) (l : ListBlank (Fin 2)) :
    step target_tm (cfg q (ListBlank.cons c l) default) =
      some (cfg q' l (ListBlank.cons c (ListBlank.cons a default))) := by
  simpa using step_cfg_left h c l default

lemma step_cfg_left_lnil {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    (r : ListBlank (Fin 2)) :
    step target_tm (cfg q default (ListBlank.cons b r)) =
      some (cfg q' default (ListBlank.cons (0 : Fin 2) (ListBlank.cons a r))) := by
  simpa using step_cfg_left h (0 : Fin 2) default r

lemma step_cfg_left_both_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q (0 : Fin 2) = some (some q', Stmt.write a Dir.left)) :
    step target_tm (cfg q default default) =
      some (cfg q' default (ListBlank.cons (0 : Fin 2) (ListBlank.cons a default))) := by
  simpa using step_cfg_left h (0 : Fin 2) default default

lemma star_right {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.right))
    {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' (ListBlank.cons a l) r) target) :
    StepsStar (cfg q l (ListBlank.cons b r)) target :=
  StepsStar.next (step_cfg_right h l r) hr

lemma star_left {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    {c : Fin 2} {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' l (ListBlank.cons c (ListBlank.cons a r))) target) :
    StepsStar (cfg q (ListBlank.cons c l) (ListBlank.cons b r)) target :=
  StepsStar.next (step_cfg_left h c l r) hr

lemma star_right_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q (0 : Fin 2) = some (some q', Stmt.write a Dir.right))
    {l : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' (ListBlank.cons a l) default) target) :
    StepsStar (cfg q l default) target :=
  StepsStar.next (step_cfg_right_nil h l) hr

lemma star_left_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q (0 : Fin 2) = some (some q', Stmt.write a Dir.left))
    {c : Fin 2} {l : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' l (ListBlank.cons c (ListBlank.cons a default))) target) :
    StepsStar (cfg q (ListBlank.cons c l) default) target :=
  StepsStar.next (step_cfg_left_nil h c l) hr

lemma star_left_lnil {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    {r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' default (ListBlank.cons (0 : Fin 2) (ListBlank.cons a r))) target) :
    StepsStar (cfg q default (ListBlank.cons b r)) target :=
  StepsStar.next (step_cfg_left_lnil h r) hr

lemma star_left_both_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q (0 : Fin 2) = some (some q', Stmt.write a Dir.left))
    {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' default (ListBlank.cons (0 : Fin 2) (ListBlank.cons a default))) target) :
    StepsStar (cfg q default default) target :=
  StepsStar.next (step_cfg_left_both_nil h) hr

lemma plus_right {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.right))
    {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : StepsStar (cfg q' (ListBlank.cons a l) r) target) :
    StepsPlus (cfg q l (ListBlank.cons b r)) target :=
  ⟨_, step_cfg_right h l r, hr⟩

macro "step_tm" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [c0, c1, b0, b1]
  try simp only [zero_cons_default]
  first
  | refine star_right rfl ?_
  | refine star_left rfl ?_
  | refine star_right_nil rfl ?_
  | refine star_left_nil rfl ?_
  | refine star_left_lnil rfl ?_
  | refine star_left_both_nil rfl ?_))

macro "plus_right_tm" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [c0, c1, b0, b1]
  try simp only [zero_cons_default]
  refine plus_right rfl ?_))

macro "exec_tm" n:num : tactic => `(tactic| (
  iterate $n step_tm
  dsimp -failIfUnchanged only [c0, c1, b0, b1]
  try simp only [zero_cons_default]
  exact StepsStar.refl _))

lemma L1_add (m n : Nat) (l : ListBlank (Fin 2)) : L1 (m + n) l = L1 m (L1 n l) := by
  induction m with
  | zero => simp [L1]
  | succ m ih => simp [L1, Nat.succ_add, ih]

lemma R1_add (m n : Nat) (r : ListBlank (Fin 2)) : R1 (m + n) r = R1 m (R1 n r) := by
  induction m with
  | zero => simp [R1]
  | succ m ih => simp [R1, Nat.succ_add, ih]

lemma R01_add (m n : Nat) (r : ListBlank (Fin 2)) : R01 (m + n) r = R01 m (R01 n r) := by
  induction m with
  | zero => simp [R01]
  | succ m ih => simp [R01, Nat.succ_add, ih]

lemma R01_snoc : ∀ (c : Nat) (r : ListBlank (Fin 2)), R01 c (c0 (c1 r)) = c0 (c1 (R01 c r))
  | 0, _ => rfl
  | c + 1, r => by simp [R01, R01_snoc c r]

def Hub (c : Nat) : Cfg (Fin 2) (Fin 6) :=
  cfg A default (c0 (c0 (R1 c default)))

lemma init_to_Hub3 : StepsStar (cfg A default default) (Hub 3) := by
  dsimp -failIfUnchanged only [Hub, R1]
  exec_tm 16

-- ============================================================================
-- The Only Two Primitive 2-Step Loops in the Entire Machine!
-- ============================================================================

lemma scan_right_01 : ∀ (k : Nat) (l r : ListBlank (Fin 2)),
    StepsStar (cfg A l (R01 k r)) (cfg A (L1 (2 * k) l) r)
  | 0, l, r => StepsStar.refl _
  | k + 1, l, r => by
    simp only [R01]
    step_tm
    step_tm
    have h2 : L1 (2 * (k + 1)) l = L1 (2 * k) (c1 (c1 l)) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, L1_add (2 * k) 2 l]; try rfl
    rw [h2]
    exact scan_right_01 k (c1 (c1 l)) r

lemma scan_left_E11 : ∀ (k : Nat) (l r : ListBlank (Fin 2)),
    StepsStar (cfg E (L1 (2 * k) l) (c1 r)) (cfg E l (c1 (R01 k r)))
  | 0, l, r => StepsStar.refl _
  | k + 1, l, r => by
    have h1 : L1 (2 * (k + 1)) l = c1 (c1 (L1 (2 * k) l)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, L1_add 2 (2 * k) l]; try rfl
    rw [h1]
    step_tm
    step_tm
    have h2 : R01 (k + 1) r = R01 k (c0 (c1 r)) := (R01_snoc k r).symm
    rw [h2]
    exact scan_left_E11 k l (c0 (c1 r))

-- ============================================================================
-- Right-End Drain Rules (`even_step`, `drain_even`, `odd_step`, `drain_odd`)
-- ============================================================================

lemma step_A4_00 (l r : ListBlank (Fin 2)) :
    StepsPlus (cfg A (c1 (c1 (c1 (c1 l)))) (c0 (c0 r)))
              (cfg E l (c1 (c0 (c0 (R1 3 r))))) := by
  dsimp -failIfUnchanged only [R1]
  plus_right_tm
  exec_tm 7

lemma even_step (k : Nat) (v r : ListBlank (Fin 2)) :
    StepsPlus (cfg A (L1 (2 * k + 4) (c0 v)) (c0 (c0 r)))
              (cfg A (L1 (2 * k + 2) v) (c0 (c0 (R1 3 r)))) := by
  have hl : L1 (2 * k + 4) (c0 v) = c1 (c1 (c1 (c1 (L1 (2 * k) (c0 v))))) := by
    rw [show 2 * k + 4 = 4 + 2 * k by omega, L1_add 4 (2 * k)]; try rfl
  rw [hl]
  refine StepsPlus.trans_star (step_A4_00 (L1 (2 * k) (c0 v)) r) ?_
  refine StepsStar.trans (scan_left_E11 k (c0 v) (c0 (c0 (R1 3 r)))) ?_
  step_tm
  have hl2 : 2 * k + 2 = 2 * (k + 1) := by omega
  rw [hl2]
  exact scan_right_01 (k + 1) v (c0 (c0 (R1 3 r)))

lemma even_base (r : ListBlank (Fin 2)) :
    StepsPlus (cfg A (L1 2 default) (c0 (c0 r)))
              (cfg A default (c0 (c0 (R1 3 r)))) := by
  dsimp -failIfUnchanged only [L1, R1]
  plus_right_tm
  exec_tm 6

lemma drain_even : ∀ (k c : Nat),
    StepsPlus (cfg A (L1 (2 * k + 2) default) (c0 (c0 (R1 c default))))
              (Hub (c + 3 * k + 3))
  | 0, c => by
    unfold Hub
    have hr : R1 3 (R1 c default) = R1 (c + 3) default := by
      rw [← R1_add 3 c default, show 3 + c = c + 3 by omega]
    simpa [hr] using even_base (R1 c default)
  | k + 1, c => by
    have hsplit : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    rw [hsplit]
    have h1 : L1 (2 * k + 4) default = L1 (2 * k + 4) (c0 default) := by simp
    rw [h1]
    have hs := even_step k default (R1 c default)
    have hr : R1 3 (R1 c default) = R1 (c + 3) default := by
      rw [← R1_add 3 c default, show 3 + c = c + 3 by omega]
    rw [hr] at hs
    refine StepsPlus.trans hs ?_
    simpa [show (c + 3) + 3 * k + 3 = c + 3 * (k + 1) + 3 by omega] using drain_even k (c + 3)

lemma odd_step (k : Nat) (v r : ListBlank (Fin 2)) :
    StepsPlus (cfg A (L1 (2 * k + 5) (c0 v)) (c0 (c0 r)))
              (cfg A (L1 (2 * k + 1) (c0 (c1 v))) (c0 (c0 (R1 3 r)))) := by
  have hl : L1 (2 * k + 5) (c0 v) = c1 (c1 (c1 (c1 (L1 (2 * k) (c1 (c0 v)))))) := by
    rw [show 2 * k + 5 = 4 + (2 * k + 1) by omega,
        L1_add 4 (2 * k + 1),
        L1_add (2 * k) 1]; try rfl
  rw [hl]
  refine StepsPlus.trans_star (step_A4_00 (L1 (2 * k) (c1 (c0 v))) r) ?_
  refine StepsStar.trans (scan_left_E11 k (c1 (c0 v)) (c0 (c0 (R1 3 r)))) ?_
  iterate 5 step_tm
  have hl2 : L1 (2 * k + 1) (c0 (c1 v)) = L1 (2 * k) (c1 (c0 (c1 v))) := by
    rw [L1_add (2 * k) 1]; try rfl
  rw [hl2]
  exact scan_right_01 k (c1 (c0 (c1 v))) (c0 (c0 (R1 3 r)))

lemma odd_base (k : Nat) (r : ListBlank (Fin 2)) :
    StepsPlus (cfg A (L1 1 (c0 (L1 (2 * k + 2) default))) (c0 (c0 r)))
              (cfg A (L1 (2 * k + 2) default) (c0 (c0 (R1 3 r)))) := by
  have hstart : L1 1 (c0 (L1 (2 * k + 2) default)) =
                c1 (c0 (c1 (c1 (L1 (2 * k) default)))) := by
    rw [show 2 * k + 2 = 2 + 2 * k by omega, L1_add 2 (2 * k)]; try rfl
  rw [hstart]
  plus_right_tm
  iterate 5 step_tm
  refine StepsStar.trans (scan_left_E11 k default (c0 (c0 (R1 3 r)))) ?_
  step_tm
  try simp only [zero_cons_default]
  have heq : 2 * k + 2 = 2 * (k + 1) := by omega
  rw [heq]
  exact scan_right_01 (k + 1) default (c0 (c0 (R1 3 r)))

lemma drain_odd_steps : ∀ (m e c : Nat),
    StepsStar (cfg A (L1 (4 * m + 1) (c0 (L1 e default))) (c0 (c0 (R1 c default))))
              (cfg A (L1 1 (c0 (L1 (e + m) default))) (c0 (c0 (R1 (c + 3 * m) default))))
  | 0, e, c => by simpa using StepsStar.refl _
  | m + 1, e, c => by
    have hsplit : 4 * (m + 1) + 1 = 2 * (2 * m) + 5 := by omega
    rw [hsplit]
    have hs := odd_step (2 * m) (L1 e default) (R1 c default)
    have hr : R1 3 (R1 c default) = R1 (c + 3) default := by
      rw [← R1_add 3 c default, show 3 + c = c + 3 by omega]
    rw [hr] at hs
    rcases hs with ⟨c', h1, hst⟩
    refine StepsStar.next h1 (StepsStar.trans hst ?_)
    have h4m : 2 * (2 * m) + 1 = 4 * m + 1 := by omega
    have he : c1 (L1 e default) = L1 (e + 1) default := rfl
    rw [h4m, he]
    simpa [show e + 1 + m = e + (m + 1) by omega,
           show c + 3 + 3 * m = c + 3 * (m + 1) by omega] using drain_odd_steps m (e + 1) (c + 3)

-- ============================================================================
-- Main Pumping Phase (`P_step6`, `P_drain6`, `branch_mod6_0`, `branch_mod6_3`)
-- ============================================================================

lemma P_step6 (k : Nat) (r : ListBlank (Fin 2)) :
    StepsStar (cfg A default (R01 (k + 1) (R1 6 r)))
              (cfg A default (R01 (k + 5) r)) := by
  refine StepsStar.trans (scan_right_01 (k + 1) default (R1 6 r)) ?_
  have hl1 : L1 (2 * (k + 1)) default = c1 (L1 (2 * k) (c1 default)) := by
    rw [show 2 * (k + 1) = 1 + (2 * k + 1) by omega, L1_add 1 (2 * k + 1), L1_add (2 * k) 1]; try rfl
  have hr1 : R1 6 r = c1 (R1 5 r) := rfl
  rw [hl1, hr1]
  step_tm
  refine StepsStar.trans (scan_left_E11 k (c1 default) (c0 (R1 5 r))) ?_
  iterate 5 step_tm
  try simp only [zero_cons_default]
  refine StepsStar.trans (scan_right_01 k (c1 (c0 (c1 default))) (c0 (R1 5 r))) ?_
  have hr2 : R1 5 r = c1 (c1 (R1 3 r)) := rfl
  rw [hr2]
  iterate 3 step_tm
  have hl2 : ListBlank.cons 1 (L1 (2 * k) (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 default)))) =
             L1 (2 * (k + 1)) (c0 (c1 default)) := by
    rw [show 2 * (k + 1) = 1 + (2 * k + 1) by omega, L1_add 1 (2 * k + 1), L1_add (2 * k) 1]; try rfl
  rw [hl2]
  refine StepsStar.trans (scan_left_E11 (k + 1) (c0 (c1 default)) (c0 (R1 3 r))) ?_
  step_tm
  refine StepsStar.trans (scan_right_01 (k + 2) (c1 default) (c0 (R1 3 r))) ?_
  have hr4 : R1 3 r = c1 (c1 (c1 r)) := rfl
  rw [hr4]
  iterate 3 step_tm
  have hl3 : ListBlank.cons 1 (L1 (2 * (k + 2)) (ListBlank.cons 1 default)) = L1 (2 * (k + 3)) default := by
    rw [show 2 * (k + 3) = 1 + (2 * (k + 2) + 1) by omega,
        L1_add 1 (2 * (k + 2) + 1), L1_add (2 * (k + 2)) 1]; try rfl
  rw [hl3]
  refine StepsStar.trans (scan_left_E11 (k + 3) default (c0 (c1 r))) ?_
  step_tm
  try simp only [zero_cons_default]
  have hfin : R01 (k + 5) r = c0 (c1 (R01 (k + 3) (c0 (c1 r)))) := by
    rw [show k + 5 = 1 + ((k + 3) + 1) by omega, R01_add 1 ((k + 3) + 1) r, R01_add (k + 3) 1 r]; try rfl
  rw [hfin]
  exact StepsStar.refl _

lemma P_drain6 : ∀ (j k : Nat) (r : ListBlank (Fin 2)),
    StepsStar (cfg A default (R01 (k + 1) (R1 (6 * j) r)))
              (cfg A default (R01 (4 * j + k + 1) r))
  | 0, k, r => by simpa [R1] using StepsStar.refl _
  | j + 1, k, r => by
    have hsplit : R1 (6 * (j + 1)) r = R1 6 (R1 (6 * j) r) := by
      rw [show 6 * (j + 1) = 6 + 6 * j by omega, R1_add 6 (6 * j) r]
    rw [hsplit]
    refine StepsStar.trans (P_step6 k (R1 (6 * j) r)) ?_
    simpa [show 4 * j + (k + 4) + 1 = 4 * (j + 1) + k + 1 by omega] using P_drain6 j (k + 4) r

lemma Hub_enter_P (c : Nat) :
    StepsStar (Hub (c + 1)) (cfg A default (R01 2 (R1 c default))) := by
  unfold Hub
  have hr : R1 (c + 1) default = c1 (R1 c default) := rfl
  rw [hr]
  dsimp -failIfUnchanged only [R01]
  exec_tm 7

lemma branch_mod6_0 (j : Nat) :
    StepsPlus (Hub (6 * j + 6)) (Hub (12 * j + 15)) := by
  have hs0 : StepsStar (Hub (6 * j + 6)) (cfg A default (R01 (4 * j + 2) (R1 5 default))) := by
    refine StepsStar.trans (by simpa [show 6 * j + 6 = (6 * j + 5) + 1 by omega] using Hub_enter_P (6 * j + 5)) ?_
    have hr : R1 (6 * j + 5) default = R1 (6 * j) (R1 5 default) := R1_add (6 * j) 5 default
    rw [hr]
    exact P_drain6 j 1 (R1 5 default)
  refine StepsStar.trans_plus hs0 ?_
  refine StepsStar.trans_plus (scan_right_01 (4 * j + 2) default (R1 5 default)) ?_
  have hl1 : L1 (2 * (4 * j + 2)) default = c1 (L1 (2 * (4 * j + 1)) (c1 default)) := by
    rw [show 2 * (4 * j + 2) = 1 + (2 * (4 * j + 1) + 1) by omega,
        L1_add 1 (2 * (4 * j + 1) + 1), L1_add (2 * (4 * j + 1)) 1]; try rfl
  rw [hl1]
  have hs1 : StepsStar (cfg A (c1 (L1 (2 * (4 * j + 1)) (c1 default))) (R1 5 default))
                       (cfg A (L1 (2 * (4 * j + 4) + 2) default) (c0 (c0 (R1 0 default)))) := by
    dsimp -failIfUnchanged only [R1]
    step_tm
    refine StepsStar.trans (scan_left_E11 (4 * j + 1) (c1 default) (c0 (c1 (c1 (c1 (c1 default)))))) ?_
    iterate 5 step_tm
    try simp only [zero_cons_default]
    refine StepsStar.trans (scan_right_01 (4 * j + 1) (c1 (c0 (c1 default))) (c0 (c1 (c1 (c1 (c1 default)))))) ?_
    iterate 3 step_tm
    have hl2 : ListBlank.cons 1 (L1 (2 * (4 * j + 1)) (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 default)))) =
               L1 (2 * (4 * j + 2)) (c0 (c1 default)) := by
      rw [show 2 * (4 * j + 2) = 1 + (2 * (4 * j + 1) + 1) by omega,
          L1_add 1 (2 * (4 * j + 1) + 1), L1_add (2 * (4 * j + 1)) 1]; try rfl
    rw [hl2]
    refine StepsStar.trans (scan_left_E11 (4 * j + 2) (c0 (c1 default)) (c0 (c1 (c1 default)))) ?_
    step_tm
    refine StepsStar.trans (scan_right_01 (4 * j + 3) (c1 default) (c0 (c1 (c1 default)))) ?_
    iterate 3 step_tm
    try simp only [zero_cons_default]
    have hl3 : ListBlank.cons 1 (L1 (2 * (4 * j + 3)) (ListBlank.cons 1 default)) = L1 (2 * (4 * j + 4)) default := by
      rw [show 2 * (4 * j + 4) = 1 + (2 * (4 * j + 3) + 1) by omega,
          L1_add 1 (2 * (4 * j + 3) + 1), L1_add (2 * (4 * j + 3)) 1]; try rfl
    rw [hl3]
    refine StepsStar.trans (scan_left_E11 (4 * j + 4) default default) ?_
    step_tm
    try simp only [zero_cons_default]
    have hl4 : L1 (2 * (4 * j + 5)) default = L1 (2 * (4 * j + 4) + 2) default := rfl
    rw [← hl4]
    exact scan_right_01 (4 * j + 5) default default
  refine StepsStar.trans_plus hs1 ?_
  have hd := drain_even (4 * j + 4) 0
  rwa [show 0 + 3 * (4 * j + 4) + 3 = 12 * j + 15 by omega] at hd

lemma branch_mod6_3 (j : Nat) :
    StepsPlus (Hub (6 * j + 3)) (Hub (9 * j + 9)) := by
  have hs0 : StepsStar (Hub (6 * j + 3)) (cfg A default (R01 (4 * j + 2) (R1 2 default))) := by
    refine StepsStar.trans (by simpa [show 6 * j + 3 = (6 * j + 2) + 1 by omega] using Hub_enter_P (6 * j + 2)) ?_
    have hr : R1 (6 * j + 2) default = R1 (6 * j) (R1 2 default) := R1_add (6 * j) 2 default
    rw [hr]
    exact P_drain6 j 1 (R1 2 default)
  refine StepsStar.trans_plus hs0 ?_
  refine StepsStar.trans_plus (scan_right_01 (4 * j + 2) default (R1 2 default)) ?_
  have hl1 : L1 (2 * (4 * j + 2)) default = c1 (L1 (2 * (4 * j + 1)) (c1 default)) := by
    rw [show 2 * (4 * j + 2) = 1 + (2 * (4 * j + 1) + 1) by omega,
        L1_add 1 (2 * (4 * j + 1) + 1), L1_add (2 * (4 * j + 1)) 1]; try rfl
  rw [hl1]
  have hs1 : StepsStar (cfg A (c1 (L1 (2 * (4 * j + 1)) (c1 default))) (R1 2 default))
                       (cfg A (L1 (4 * (2 * j + 1) + 1) (c0 (L1 1 default))) (c0 (c0 (R1 0 default)))) := by
    dsimp -failIfUnchanged only [R1]
    step_tm
    refine StepsStar.trans (scan_left_E11 (4 * j + 1) (c1 default) (c0 (c1 default))) ?_
    iterate 5 step_tm
    try simp only [zero_cons_default]
    have hr1 : R01 (4 * j + 1) (c0 (c1 default)) = R01 (4 * j + 2) default := by
      rw [show 4 * j + 2 = (4 * j + 1) + 1 by omega, R01_add (4 * j + 1) 1 default]; try rfl
    rw [hr1]
    have hl2 : L1 (2 * (4 * j + 2)) (c1 (c0 (c1 default))) =
               L1 (4 * (2 * j + 1) + 1) (ListBlank.cons 0 (L1 1 default)) := by
      rw [show 4 * (2 * j + 1) + 1 = 2 * (4 * j + 2) + 1 by omega, L1_add (2 * (4 * j + 2)) 1]; try rfl
    rw [← hl2]
    exact scan_right_01 (4 * j + 2) (c1 (c0 (c1 default))) default
  refine StepsStar.trans_plus hs1 ?_
  refine StepsStar.trans_plus (drain_odd_steps (2 * j + 1) 1 0) ?_
  have hob : StepsPlus (cfg A (L1 1 (c0 (L1 (1 + (2 * j + 1)) default))) (c0 (c0 (R1 (0 + 3 * (2 * j + 1)) default))))
                       (cfg A (L1 (2 * j + 2) default) (c0 (c0 (R1 (6 * j + 6) default)))) := by
    have heq1 : 1 + (2 * j + 1) = 2 * j + 2 := by omega
    have heq2 : R1 3 (R1 (0 + 3 * (2 * j + 1)) default) = R1 (6 * j + 6) default := by
      rw [← R1_add 3 (0 + 3 * (2 * j + 1)) default, show 3 + (0 + 3 * (2 * j + 1)) = 6 * j + 6 by omega]
    rw [heq1]
    have hop := odd_base j (R1 (0 + 3 * (2 * j + 1)) default)
    rwa [heq2] at hop
  refine StepsPlus.trans hob ?_
  have hd := drain_even j (6 * j + 6)
  rwa [show (6 * j + 6) + 3 * j + 3 = 9 * j + 9 by omega] at hd

-- ============================================================================
-- Closed Mod-3 Invariant and Main Non-Halting Theorem
-- ============================================================================

def Inv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m : Nat, c = Hub (3 * m + 3)

lemma Inv_step {c : Cfg (Fin 2) (Fin 6)} (h : Inv c) :
    ∃ c', Inv c' ∧ StepsPlus c c' := by
  rcases h with ⟨m, rfl⟩
  have hm := Nat.div_add_mod m 2
  have hlt := Nat.mod_lt m (by decide : 0 < 2)
  by_cases hpar : m % 2 = 0
  · refine ⟨Hub (9 * (m / 2) + 9), ⟨3 * (m / 2) + 2, by congr 1; omega⟩, ?_⟩
    simpa [show 3 * m + 3 = 6 * (m / 2) + 3 by omega] using branch_mod6_3 (m / 2)
  · refine ⟨Hub (12 * (m / 2) + 15), ⟨4 * (m / 2) + 4, by congr 1; omega⟩, ?_⟩
    simpa [show 3 * m + 3 = 6 * (m / 2) + 6 by omega] using branch_mod6_0 (m / 2)

theorem reach_arbitrarily_long :
    ∀ k : Nat, ∃ N c, k ≤ N ∧ Inv c ∧ multiStep target_tm (init []) N = some c
  | 0 => by
    rcases init_to_Hub3.to_multiStep with ⟨N₀, hN₀⟩
    exact ⟨N₀, Hub 3, Nat.zero_le N₀, ⟨0, rfl⟩, hN₀⟩
  | k + 1 => by
    rcases reach_arbitrarily_long k with ⟨N, c, hle, hc, hN⟩
    rcases Inv_step hc with ⟨c', hc', hplus⟩
    rcases hplus.to_multiStep with ⟨m, hm_pos, hm⟩
    exact ⟨N + m, c', by omega, hc', multiStep_trans _ _ _ N m hN hm⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨k, hk⟩
  cases h_step : step target_tm cfg with
  | some cfg' => rfl
  | none =>
    have h_none : multiStep target_tm (init []) (k + 1) = none := by
      rw [multiStep_succ_end, hk]; exact h_step
    rcases reach_arbitrarily_long (k + 1) with ⟨N, _, h_ge, _, hN⟩
    have h_split : N = (k + 1) + (N - (k + 1)) := by omega
    have h_none_N : multiStep target_tm (init []) N = none := by
      rw [h_split]
      exact multiStep_none_add h_none (N - (k + 1))
    rw [h_none_N] at hN
    nomatch hN

end BusyBeaver.M_1RB0LE_1LC1RA_HHH1LD_0RB1LF_1RD1LA_0LA0RD
