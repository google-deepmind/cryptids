/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LD_1RC0RF_1LC1LA_0LE---_1LF0RB_0RC0RE` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LD_1RC0RF_1LC1LA_0LE---_1LF0RB_0RC0RE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_1RC0RF_1LC1LA_0LEHHH_1LF0RB_0RC0RE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LD_1RC0RF_1LC1LA_0LE---_1LF0RB_0RC0RE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => none
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.right)

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

inductive ReachHalt : Cfg (Fin 2) (Fin 6) → Prop
  | done {c} : (step target_tm c).isNone → ReachHalt c
  | next {c c'} : step target_tm c = some c' → ReachHalt c' → ReachHalt c

def Reaches (c c' : Cfg (Fin 2) (Fin 6)) : Prop :=
  ReachHalt c' → ReachHalt c

lemma Reaches.refl (c : Cfg (Fin 2) (Fin 6)) : Reaches c c := id

lemma Reaches.trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)} (h₁ : Reaches c₁ c₂) (h₂ : Reaches c₂ c₃) :
    Reaches c₁ c₃ :=
  fun h => h₁ (h₂ h)

lemma multiStep_succ_of_step {c c' : Cfg (Fin 2) (Fin 6)} (n : ℕ)
    (h : step target_tm c = some c') :
    multiStep target_tm c (n + 1) = multiStep target_tm c' n := by
  unfold multiStep
  rw [Function.iterate_succ_apply]
  change (Option.bind · (step target_tm))^[n] (step target_tm c) = _
  rw [h]

lemma ReachHalt.to_isHalt {c : Cfg (Fin 2) (Fin 6)} (h : ReachHalt c) :
    ∃ cfg, (c [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone := by
  induction h with
  | done hnone => exact ⟨_, ⟨0, rfl⟩, hnone⟩
  | next hstep _ ih =>
    rcases ih with ⟨cfg, ⟨n, hn⟩, hnone⟩
    exact ⟨cfg, ⟨n + 1, by rw [multiStep_succ_of_step n hstep, hn]⟩, hnone⟩

@[reducible] def c0 (l : ListBlank (Fin 2)) : ListBlank (Fin 2) := ListBlank.cons b0 l
@[reducible] def c1 (l : ListBlank (Fin 2)) : ListBlank (Fin 2) := ListBlank.cons b1 l

def cfg (q : Fin 6) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some q, ⟨r.head, l, r.tail⟩⟩

@[simp] lemma zero_cons_default : ListBlank.cons b0 default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = b0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

lemma init_eq_cfg : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = cfg A default default := rfl

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
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.right))
    (l : ListBlank (Fin 2)) :
    step target_tm (cfg q l default) = some (cfg q' (ListBlank.cons a l) default) := by
  simpa using! step_cfg_right h l default

lemma step_cfg_left_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.left))
    (c : Fin 2) (l : ListBlank (Fin 2)) :
    step target_tm (cfg q (ListBlank.cons c l) default) =
      some (cfg q' l (ListBlank.cons c (ListBlank.cons a default))) := by
  simpa using! step_cfg_left h c l default

lemma step_cfg_left_lnil {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    (r : ListBlank (Fin 2)) :
    step target_tm (cfg q default (ListBlank.cons b r)) =
      some (cfg q' default (ListBlank.cons b0 (ListBlank.cons a r))) := by
  simpa using! step_cfg_left h b0 default r

lemma reach_right {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.right))
    {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' (ListBlank.cons a l) r) target) :
    Reaches (cfg q l (ListBlank.cons b r)) target :=
  fun ht => ReachHalt.next (step_cfg_right h l r) (hr ht)

lemma reach_left {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    {c : Fin 2} {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' l (ListBlank.cons c (ListBlank.cons a r))) target) :
    Reaches (cfg q (ListBlank.cons c l) (ListBlank.cons b r)) target :=
  fun ht => ReachHalt.next (step_cfg_left h c l r) (hr ht)

lemma reach_right_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.right))
    {l : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' (ListBlank.cons a l) default) target) :
    Reaches (cfg q l default) target :=
  fun ht => ReachHalt.next (step_cfg_right_nil h l) (hr ht)

lemma reach_left_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.left))
    {c : Fin 2} {l : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' l (ListBlank.cons c (ListBlank.cons a default))) target) :
    Reaches (cfg q (ListBlank.cons c l) default) target :=
  fun ht => ReachHalt.next (step_cfg_left_nil h c l) (hr ht)

lemma reach_left_lnil {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    {r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' default (ListBlank.cons b0 (ListBlank.cons a r))) target) :
    Reaches (cfg q default (ListBlank.cons b r)) target :=
  fun ht => ReachHalt.next (step_cfg_left_lnil h r) (hr ht)

macro "step_tm" : tactic => `(tactic|
  first
  | refine reach_right rfl ?_
  | refine reach_left rfl ?_
  | refine reach_right_nil rfl ?_
  | refine reach_left_nil rfl ?_
  | refine reach_left_lnil rfl ?_)

macro "exec_tm" n:num : tactic => `(tactic| (
  iterate $n step_tm
  try simp only [zero_cons_default]
  exact Reaches.refl _))

-- ============================================================================
-- Canonical Tape Encodings `L0`, `R1`, and `G(a, m)`
-- ============================================================================

def L0 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, l => l
  | n + 1, l => c0 (L0 n l)

def R1 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | n + 1, r => c1 (R1 n r)

lemma L0_add (m n : Nat) (l : ListBlank (Fin 2)) : L0 (m + n) l = L0 m (L0 n l) := by
  induction m with
  | zero => simp [L0]
  | succ m ih => simp [L0, Nat.succ_add, ih]

lemma R1_add (m n : Nat) (r : ListBlank (Fin 2)) : R1 (m + n) r = R1 m (R1 n r) := by
  induction m with
  | zero => simp [R1]
  | succ m ih => simp [R1, Nat.succ_add, ih]

lemma R1_snoc : ∀ (c : Nat) (r : ListBlank (Fin 2)), R1 c (c1 r) = c1 (R1 c r)
  | 0, _ => rfl
  | c + 1, r => by simp [R1, R1_snoc c r]

/-- Canonical hub `G(a, m) := 0^∞ 1 0^a 11 0^{3m + 5} C> 0^∞`. -/
def G (a m : Nat) : Cfg (Fin 2) (Fin 6) :=
  cfg C (L0 (3 * m + 5) (c1 (c1 (L0 a (c1 default))))) default

lemma init_to_G5 : Reaches (cfg A default default) (G 5 0) := by
  unfold G
  exec_tm 45

-- ============================================================================
-- Inner Sweep Lemmas (`sweep_C0`, `sweep_B111`, `pump_A`)
-- ============================================================================

lemma sweep_C0 : ∀ (c : Nat) (l r : ListBlank (Fin 2)),
    Reaches (cfg C (L0 c l) (c0 r)) (cfg C l (c0 (R1 c r)))
  | 0, l, r => Reaches.refl _
  | c + 1, l, r => by
    simp only [L0]
    refine reach_left rfl ?_
    have heq : c1 (R1 c r) = R1 (c + 1) r := rfl
    rw [← heq, ← R1_snoc c r]
    exact sweep_C0 c l (c1 r)

lemma exit_11_C0 (c : Nat) (l : ListBlank (Fin 2)) :
    Reaches (cfg C (L0 c (c1 (c1 l))) default) (cfg A l (R1 (c + 3) default)) := by
  have hs : Reaches (cfg C (L0 c (c1 (c1 l))) default) (cfg C (c1 (c1 l)) (c0 (R1 c default))) := by
    simpa using! sweep_C0 c (c1 (c1 l)) default
  refine Reaches.trans hs ?_
  step_tm
  step_tm
  have heq : c1 (c1 (c1 (R1 c default))) = R1 (c + 3) default := by
    rw [show c + 3 = 3 + c by omega, R1_add 3 c default]; rfl
  dsimp only [c0, c1, b0, b1] at heq ⊢
  rw [heq]
  exact Reaches.refl _

lemma sweep_B111 : ∀ (k : Nat) (l r : ListBlank (Fin 2)),
    Reaches (cfg B l (R1 (3 * k) r)) (cfg B (L0 (3 * k) l) r)
  | 0, l, r => Reaches.refl _
  | k + 1, l, r => by
    have h1 : R1 (3 * (k + 1)) r = c1 (c1 (c1 (R1 (3 * k) r))) := by
      rw [show 3 * (k + 1) = 3 + 3 * k by omega, R1_add 3 (3 * k) r]; rfl
    have h2 : L0 (3 * (k + 1)) l = L0 (3 * k) (c0 (c0 (c0 l))) := by
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, L0_add (3 * k) 3 l]; rfl
    rw [h1, h2]
    step_tm
    step_tm
    step_tm
    exact sweep_B111 k (c0 (c0 (c0 l))) r

lemma finish_A0_mod3 (k : Nat) (u : ListBlank (Fin 2)) :
    Reaches (cfg A u (c0 (R1 (3 * k + 9) default)))
            (cfg C (L0 5 (c1 (c1 (L0 (3 * k + 8) (c1 u))))) default) := by
  have hr : R1 (3 * k + 9) default = R1 (3 * (k + 3)) default := rfl
  rw [hr]
  step_tm
  refine Reaches.trans (sweep_B111 (k + 3) (c1 u) default) ?_
  have hl : L0 (3 * (k + 3)) (c1 u) = L0 1 (L0 (3 * k + 8) (c1 u)) := by
    rw [← L0_add 1 (3 * k + 8) (c1 u)]
    congr 1; omega
  rw [hl]
  simp only [L0]
  exec_tm 22

lemma pump_A : ∀ (c : Nat) (l : ListBlank (Fin 2)) (k : Nat),
    Reaches (cfg A (L0 c l) (c0 (R1 (3 * k + 1) default)))
            (cfg A l (c0 (R1 (3 * (k + c) + 1) default)))
  | 0, l, k => by simpa [L0] using! Reaches.refl _
  | c + 1, l, k => by
    simp only [L0]
    have hr : R1 (3 * k + 1) default = R1 (3 * k) (c1 default) := R1_add (3 * k) 1 default
    rw [hr]
    step_tm
    refine Reaches.trans (sweep_B111 k (c1 (c0 (L0 c l))) (c1 default)) ?_
    step_tm
    step_tm
    have hl : c0 (c0 (L0 (3 * k) (c1 (c0 (L0 c l))))) =
              L0 (3 * k + 2) (c1 (c0 (L0 c l))) := by
      rw [show 3 * k + 2 = 2 + 3 * k by omega, L0_add 2 (3 * k)]; rfl
    dsimp only [c0, c1, b0, b1] at hl ⊢
    rw [hl]
    refine Reaches.trans (by simpa using! sweep_C0 (3 * k + 2) (c1 (c0 (L0 c l))) default) ?_
    step_tm
    step_tm
    have hnext : c0 (c1 (c1 (R1 (3 * k + 2) default))) = c0 (R1 (3 * (k + 1) + 1) default) := by
      rw [show 3 * (k + 1) + 1 = 2 + (3 * k + 2) by omega, R1_add 2 (3 * k + 2) default]; rfl
    dsimp only [c0, c1, b0, b1] at hnext ⊢
    rw [hnext]
    simpa [Nat.add_assoc, Nat.add_comm 1 c] using! pump_A c l (k + 1)

-- ============================================================================
-- Exact Macro-Transition Rules on `G(a, m)`
-- ============================================================================

lemma G_halt (m : Nat) : ReachHalt (G 0 m) := by
  unfold G
  apply exit_11_C0 (3 * m + 5) (c1 default)
  have hr : R1 (3 * m + 5 + 3) default = c1 (R1 (3 * m + 7) default) := by
    rw [show 3 * m + 5 + 3 = 1 + (3 * m + 7) by omega, R1_add 1 (3 * m + 7) default]; rfl
  rw [hr]
  exact ReachHalt.next (step_cfg_left rfl b1 default (R1 (3 * m + 7) default))
    (ReachHalt.done (by simp [cfg, step, target_tm]))

lemma G_mod1 (m : Nat) : Reaches (G 1 m) (G (3 * m + 8) 0) := by
  unfold G
  refine Reaches.trans (exit_11_C0 (3 * m + 5) (L0 1 (c1 default))) ?_
  have hr : R1 (3 * m + 5 + 3) default = c1 (R1 (3 * m + 7) default) := by
    rw [show 3 * m + 5 + 3 = 1 + (3 * m + 7) by omega, R1_add 1 (3 * m + 7) default]; rfl
  rw [hr]
  simp only [L0]
  iterate 6 step_tm
  try simp only [zero_cons_default]
  have hr2 : c1 (c1 (R1 (3 * m + 7) default)) = R1 (3 * m + 9) default := by
    rw [show 3 * m + 9 = 2 + (3 * m + 7) by omega, R1_add 2 (3 * m + 7) default]; rfl
  dsimp only [c0, c1, b0, b1] at hr2 ⊢
  rw [hr2]
  exact finish_A0_mod3 m default

lemma G_mod2 (m : Nat) : Reaches (G 2 m) (G (3 * m + 8) 0) := by
  unfold G
  refine Reaches.trans (exit_11_C0 (3 * m + 5) (L0 2 (c1 default))) ?_
  have hr : R1 (3 * m + 5 + 3) default = c1 (c1 (R1 (3 * m + 6) default)) := by
    rw [show 3 * m + 5 + 3 = 2 + (3 * m + 6) by omega, R1_add 2 (3 * m + 6) default]; rfl
  rw [hr]
  simp only [L0]
  iterate 8 step_tm
  try simp only [zero_cons_default]
  have hr2 : c1 (c1 (c1 (R1 (3 * m + 6) default))) = R1 (3 * m + 9) default := by
    rw [show 3 * m + 9 = 3 + (3 * m + 6) by omega, R1_add 3 (3 * m + 6) default]; rfl
  dsimp only [c0, c1, b0, b1] at hr2 ⊢
  rw [hr2]
  exact finish_A0_mod3 m default

lemma G_mod3 (m : Nat) : Reaches (G 3 m) (G (3 * m + 14) 0) := by
  unfold G
  refine Reaches.trans (exit_11_C0 (3 * m + 5) (L0 3 (c1 default))) ?_
  have hr : R1 (3 * m + 5 + 3) default = c1 (c1 (c1 (c1 (R1 (3 * m + 4) default)))) := by
    rw [show 3 * m + 5 + 3 = 4 + (3 * m + 4) by omega, R1_add 4 (3 * m + 4) default]; rfl
  rw [hr]
  simp only [L0]
  iterate 24 step_tm
  try simp only [zero_cons_default]
  have hr2 : c1 (c1 (c1 (c1 (c1 (c1 (c1 (c1 (c1 (c1 (c1 (R1 (3 * m + 4) default))))))))))) =
             R1 (3 * (m + 2) + 9) default := by
    rw [show 3 * (m + 2) + 9 = 11 + (3 * m + 4) by omega, R1_add 11 (3 * m + 4) default]; rfl
  dsimp only [c0, c1, b0, b1] at hr2 ⊢
  rw [hr2]
  simpa [show 3 * (m + 2) + 8 = 3 * m + 14 by omega] using! finish_A0_mod3 (m + 2) default

lemma G_step4 (a m : Nat) : Reaches (G (a + 4) m) (G a (3 * m + 9)) := by
  unfold G
  have hl0 : L0 (a + 4) (c1 default) = L0 4 (L0 a (c1 default)) := by
    rw [← L0_add 4 a (c1 default)]
    congr 1; omega
  rw [hl0]
  refine Reaches.trans (exit_11_C0 (3 * m + 5) (L0 4 (L0 a (c1 default)))) ?_
  have hr : R1 (3 * m + 5 + 3) default = c1 (c1 (c1 (R1 (3 * m + 5) default))) := by
    rw [show 3 * m + 5 + 3 = 3 + (3 * m + 5) by omega, R1_add 3 (3 * m + 5) default]; rfl
  rw [hr]
  simp only [L0]
  iterate 13 step_tm
  have hr2 : c1 (c1 (c1 (c1 (c1 (c1 (R1 (3 * m + 5) default)))))) =
             R1 (3 * (m + 3)) (c1 (c1 default)) := by
    have h6 : c1 (c1 (c1 (c1 (c1 (c1 (R1 (3 * m + 5) default)))))) = R1 6 (R1 (3 * m + 5) default) := rfl
    rw [h6, ← R1_add 6 (3 * m + 5) default,
        show 6 + (3 * m + 5) = 3 * (m + 3) + 2 by omega,
        R1_add (3 * (m + 3)) 2 default]
    rfl
  dsimp only [c0, c1, b0, b1] at hr2 ⊢
  rw [hr2]
  refine Reaches.trans (sweep_B111 (m + 3) (c1 (L0 a (c1 default))) (c1 (c1 default))) ?_
  iterate 5 step_tm
  have hl2 : c0 (L0 (3 * (m + 3)) (c1 (L0 a (c1 default)))) =
             L0 (3 * m + 10) (c1 (L0 a (c1 default))) := by
    rw [show 3 * m + 10 = 1 + 3 * (m + 3) by omega, L0_add 1 (3 * (m + 3))]; rfl
  dsimp only [c0, c1, b0, b1] at hl2 ⊢
  rw [hl2]
  refine Reaches.trans (by simpa [R1] using! pump_A (3 * m + 10) (c1 (L0 a (c1 default))) 0) ?_
  step_tm
  have hr3 : c1 (R1 (3 * (3 * m + 10)) default) = R1 (3 * (3 * m + 10)) (c1 default) :=
    R1_add (3 * (3 * m + 10)) 1 default
  dsimp only [c0, c1, b0, b1] at hr3 ⊢
  rw [hr3]
  refine Reaches.trans (sweep_B111 (3 * m + 10) (c1 (c1 (L0 a (c1 default)))) (c1 default)) ?_
  step_tm
  step_tm
  have hfin : c0 (c0 (L0 (3 * (3 * m + 10)) (c1 (c1 (L0 a (c1 default)))))) =
              L0 (3 * (3 * m + 9) + 5) (c1 (c1 (L0 a (c1 default)))) := by
    rw [show 3 * (3 * m + 9) + 5 = 2 + 3 * (3 * m + 10) by omega,
        L0_add 2 (3 * (3 * m + 10))]; rfl
  dsimp only [c0, c1, b0, b1] at hfin ⊢
  rw [hfin]
  exact Reaches.refl _

-- ============================================================================
-- Euler Totient Modular Tower (`MSeq`, `pow3_mod_pow2`, `pow3ModBin`)
-- ============================================================================

def MSeq : Nat → Nat
  | 0 => 0
  | k + 1 => 3 * MSeq k + 9

lemma G_drain : ∀ (k r : Nat), Reaches (G (4 * k + r) 0) (G r (MSeq k))
  | 0, r => by simpa [MSeq] using! Reaches.refl _
  | k + 1, r => by
    have hsplit : 4 * (k + 1) + r = (4 * k + r) + 4 := by omega
    rw [hsplit]
    exact Reaches.trans (G_drain k (r + 4)) (by simpa [MSeq] using! G_step4 r (MSeq k))

lemma two_MSeq_add_nine : ∀ k : Nat, 2 * MSeq k + 9 = 3 ^ (k + 2)
  | 0 => rfl
  | k + 1 => by
    have ih := two_MSeq_add_nine k
    simp only [MSeq]
    rw [show 3 ^ (k + 1 + 2) = 3 * 3 ^ (k + 2) by ring]
    omega

lemma two_TSeq_add_one (k : Nat) : 2 * (3 * MSeq k + 13) + 1 = 3 ^ (k + 3) := by
  have ih := two_MSeq_add_nine k
  rw [show 3 ^ (k + 3) = 3 * 3 ^ (k + 2) by ring]
  omega

/-- Euler totient congruence `2^(e + 3) ∣ 3^(2^(e + 1)) - 1` for all `e : Nat`. -/
lemma pow2_dvd_pow3_sub1 : ∀ e : Nat, 2 ^ (e + 3) ∣ 3 ^ (2 ^ (e + 1)) - 1
  | 0 => by decide
  | e + 1 => by
    rcases pow2_dvd_pow3_sub1 e with ⟨q, hq⟩
    have hge1 : 1 ≤ 3 ^ (2 ^ (e + 1)) := Nat.one_le_pow _ _ (by decide)
    have h3 : 3 ^ (2 ^ (e + 1)) = 2 ^ (e + 3) * q + 1 := by omega
    have hsq : 3 ^ (2 ^ (e + 1 + 1)) =
        2 ^ (e + 1 + 3) * (q + 2 ^ (e + 2) * q * q) + 1 := by
      have hexp : 2 ^ (e + 1 + 1) = 2 ^ (e + 1) + 2 ^ (e + 1) := by ring
      rw [hexp, Nat.pow_add, h3]
      ring
    exact ⟨q + 2 ^ (e + 2) * q * q, by omega⟩

lemma pow3_add_period (e k : Nat) :
    3 ^ (k + 2 ^ (e + 1)) % 2 ^ (e + 3) = 3 ^ k % 2 ^ (e + 3) := by
  rcases pow2_dvd_pow3_sub1 e with ⟨q, hq⟩
  have hge1 : 1 ≤ 3 ^ (2 ^ (e + 1)) := Nat.one_le_pow _ _ (by decide)
  have h3 : 3 ^ (2 ^ (e + 1)) = 2 ^ (e + 3) * q + 1 := by omega
  have hrew : 3 ^ (k + 2 ^ (e + 1)) = 2 ^ (e + 3) * (3 ^ k * q) + 3 ^ k := by
    rw [Nat.pow_add, h3]; ring
  rw [hrew, Nat.mul_add_mod]

lemma pow3_mod_pow2 (e : Nat) : ∀ k : Nat,
    3 ^ k % 2 ^ (e + 3) = 3 ^ (k % 2 ^ (e + 1)) % 2 ^ (e + 3) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hlt : k < 2 ^ (e + 1)
    · rw [Nat.mod_eq_of_lt hlt]
    · have hge : k ≥ 2 ^ (e + 1) := by omega
      have hpos : 0 < 2 ^ (e + 1) := by positivity
      have hsub : k = (k - 2 ^ (e + 1)) + 2 ^ (e + 1) := by omega
      rw [hsub, pow3_add_period, ih (k - 2 ^ (e + 1)) (by omega), Nat.add_mod_right]

lemma two_mul_add_one_mod (x m : Nat) (hm : 0 < m) :
    (2 * x + 1) % (2 * m) = 2 * (x % m) + 1 := by
  have hx := Nat.div_add_mod x m
  have hrem : x % m < m := Nat.mod_lt x hm
  have hrew : 2 * x + 1 = 2 * m * (x / m) + (2 * (x % m) + 1) := by nlinarith
  have hlt : 2 * (x % m) + 1 < 2 * m := by omega
  rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma div4_mod (a m : Nat) (hm : 0 < m) :
    (a % (4 * m)) / 4 = (a / 4) % m := by
  have hdiv4 := Nat.div_add_mod a 4
  have hrem4 : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hdivm := Nat.div_add_mod (a / 4) m
  have hremm : (a / 4) % m < m := Nat.mod_lt (a / 4) hm
  have ha : a = 4 * m * ((a / 4) / m) + (4 * ((a / 4) % m) + a % 4) := by nlinarith
  have hlt : 4 * ((a / 4) % m) + a % 4 < 4 * m := by nlinarith
  nth_rw 1 [ha]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  omega

lemma mod_eq_of_add_one (X Y m : Nat) (h : (X + 1) % m = (Y + 1) % m) : X % m = Y % m := by
  by_cases hm : m = 0
  · subst hm; simpa using! h
  · have hx := Nat.div_add_mod X m
    have hy := Nat.div_add_mod Y m
    have hltX : X % m < m := Nat.mod_lt X (by omega)
    have hltY : Y % m < m := Nat.mod_lt Y (by omega)
    by_cases hx1 : X % m + 1 = m <;> by_cases hy1 : Y % m + 1 = m
    · omega
    · have hX : (X + 1) % m = 0 := by
        have : X + 1 = m * (X / m + 1) + 0 := by nlinarith
        rw [this, Nat.mul_add_mod]; simp
      have hY : (Y + 1) % m = Y % m + 1 := by
        have : Y + 1 = m * (Y / m) + (Y % m + 1) := by nlinarith
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hY : (Y + 1) % m = 0 := by
        have : Y + 1 = m * (Y / m + 1) + 0 := by nlinarith
        rw [this, Nat.mul_add_mod]; simp
      have hX : (X + 1) % m = X % m + 1 := by
        have : X + 1 = m * (X / m) + (X % m + 1) := by nlinarith
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hX : (X + 1) % m = X % m + 1 := by
        have : X + 1 = m * (X / m) + (X % m + 1) := by nlinarith
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hY : (Y + 1) % m = Y % m + 1 := by
        have : Y + 1 = m * (Y / m) + (Y % m + 1) := by nlinarith
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      omega

lemma mod_eq_of_add_five (X Y m : Nat) (h : (X + 5) % m = (Y + 5) % m) : X % m = Y % m := by
  apply mod_eq_of_add_one
  apply mod_eq_of_add_one
  apply mod_eq_of_add_one
  apply mod_eq_of_add_one
  apply mod_eq_of_add_one
  simpa [Nat.add_assoc] using! h

lemma TSeq_mod_half (k m : Nat) (hm : 0 < m) :
    (3 * MSeq k + 13) % m = (3 ^ (k + 3) % (2 * m)) / 2 := by
  have h1 := two_TSeq_add_one k
  have h2 := two_mul_add_one_mod (3 * MSeq k + 13) m hm
  rw [← h1, h2]
  omega

lemma TSeq_mod_congr (e a r_mod : Nat)
    (ha : a % 2 ^ (e + 3) = r_mod) :
    (3 * MSeq (a / 4) + 13) % 2 ^ (e + 2) = (3 * MSeq (r_mod / 4) + 13) % 2 ^ (e + 2) := by
  have hdiv_mod : (a / 4) % 2 ^ (e + 1) = r_mod / 4 := by
    have hsplit : 2 ^ (e + 3) = 4 * 2 ^ (e + 1) := by ring
    rw [hsplit] at ha
    rw [← div4_mod a (2 ^ (e + 1)) (by positivity), ha]
  have hp1 := pow3_mod_pow2 e (a / 4 + 3)
  have hp2 := pow3_mod_pow2 e (r_mod / 4 + 3)
  have hexp_eq : (a / 4 + 3) % 2 ^ (e + 1) = (r_mod / 4 + 3) % 2 ^ (e + 1) := by
    rw [← Nat.mod_add_mod (a / 4) (2 ^ (e + 1)) 3, hdiv_mod]
  rw [hexp_eq] at hp1
  have h3eq : 3 ^ (a / 4 + 3) % 2 ^ (e + 3) = 3 ^ (r_mod / 4 + 3) % 2 ^ (e + 3) :=
    hp1.trans hp2.symm
  have hpow : 2 ^ (e + 3) = 2 * 2 ^ (e + 2) := by ring
  rw [TSeq_mod_half (a / 4) (2 ^ (e + 2)) (by positivity),
      TSeq_mod_half (r_mod / 4) (2 ^ (e + 2)) (by positivity),
      ← hpow, h3eq]

lemma MSeq_mod_step (e a r_mod : Nat) (ha : a % 2 ^ (e + 3) = r_mod) :
    (3 * MSeq (a / 4) + 8) % 2 ^ (e + 2) = (3 * MSeq (r_mod / 4) + 8) % 2 ^ (e + 2) := by
  apply mod_eq_of_add_five
  simpa [show (3 * MSeq (a / 4) + 8) + 5 = 3 * MSeq (a / 4) + 13 by omega,
         show (3 * MSeq (r_mod / 4) + 8) + 5 = 3 * MSeq (r_mod / 4) + 13 by omega] using
    TSeq_mod_congr e a r_mod ha

lemma MSeq_mod_step3 (e a r_mod : Nat) (ha : a % 2 ^ (e + 3) = r_mod) :
    (3 * MSeq (a / 4) + 14) % 2 ^ (e + 2) = (3 * MSeq (r_mod / 4) + 14) % 2 ^ (e + 2) := by
  have h := TSeq_mod_congr e a r_mod ha
  rw [show 3 * MSeq (a / 4) + 14 = (3 * MSeq (a / 4) + 13) + 1 by omega,
      show 3 * MSeq (r_mod / 4) + 14 = (3 * MSeq (r_mod / 4) + 13) + 1 by omega,
      ← Nat.mod_add_mod (3 * MSeq (a / 4) + 13) (2 ^ (e + 2)) 1,
      h,
      Nat.mod_add_mod (3 * MSeq (r_mod / 4) + 13) (2 ^ (e + 2)) 1]

lemma a_mod4_eq (e a r_mod : Nat) (ha : a % 2 ^ (e + 3) = r_mod) :
    a % 4 = r_mod % 4 := by
  have h4dvd : 4 ∣ 2 ^ (e + 3) := ⟨2 ^ (e + 1), by ring⟩
  rw [← ha, Nat.mod_mod_of_dvd a h4dvd]

lemma step_mod1 (e a r_mod : Nat) (ha : a % 2 ^ (e + 3) = r_mod) (_ : r_mod < 2 ^ (e + 3))
    (hr4 : r_mod % 4 = 1) :
    ∃ a', Reaches (G a 0) (G a' 0) ∧ a' % 2 ^ (e + 2) = (3 * MSeq (r_mod / 4) + 8) % 2 ^ (e + 2) := by
  refine ⟨3 * MSeq (a / 4) + 8, ?_, MSeq_mod_step e a r_mod ha⟩
  have hm4 := a_mod4_eq e a r_mod ha
  have hd4 := Nat.div_add_mod a 4
  have ha4 : a = 4 * (a / 4) + 1 := by omega
  nth_rw 1 [ha4]
  exact Reaches.trans (G_drain (a / 4) 1) (G_mod1 (MSeq (a / 4)))

lemma step_mod2 (e a r_mod : Nat) (ha : a % 2 ^ (e + 3) = r_mod) (_ : r_mod < 2 ^ (e + 3))
    (hr4 : r_mod % 4 = 2) :
    ∃ a', Reaches (G a 0) (G a' 0) ∧ a' % 2 ^ (e + 2) = (3 * MSeq (r_mod / 4) + 8) % 2 ^ (e + 2) := by
  refine ⟨3 * MSeq (a / 4) + 8, ?_, MSeq_mod_step e a r_mod ha⟩
  have hm4 := a_mod4_eq e a r_mod ha
  have hd4 := Nat.div_add_mod a 4
  have ha4 : a = 4 * (a / 4) + 2 := by omega
  nth_rw 1 [ha4]
  exact Reaches.trans (G_drain (a / 4) 2) (G_mod2 (MSeq (a / 4)))

lemma step_mod3 (e a r_mod : Nat) (ha : a % 2 ^ (e + 3) = r_mod) (_ : r_mod < 2 ^ (e + 3))
    (hr4 : r_mod % 4 = 3) :
    ∃ a', Reaches (G a 0) (G a' 0) ∧ a' % 2 ^ (e + 2) = (3 * MSeq (r_mod / 4) + 14) % 2 ^ (e + 2) := by
  refine ⟨3 * MSeq (a / 4) + 14, ?_, MSeq_mod_step3 e a r_mod ha⟩
  have hm4 := a_mod4_eq e a r_mod ha
  have hd4 := Nat.div_add_mod a 4
  have ha4 : a = 4 * (a / 4) + 3 := by omega
  nth_rw 1 [ha4]
  exact Reaches.trans (G_drain (a / 4) 3) (G_mod3 (MSeq (a / 4)))

/-- Fast binary squaring `(3 ^ n) % m` in `fuel = 16` steps (depth <= 16, zero big ints!). -/
def pow3ModBin : Nat → Nat → Nat → Nat
  | 0, _, m => 1 % m
  | fuel + 1, n, m =>
    if n = 0 then 1 % m
    else
      let half := pow3ModBin fuel (n / 2) m
      let sq := (half * half) % m
      if n % 2 = 1 then (3 * sq) % m else sq

lemma pow3ModBin_eq : ∀ (fuel n m : Nat), n < 2 ^ fuel → pow3ModBin fuel n m = 3 ^ n % m
  | 0, n, m, hn => by
    have h0 : n = 0 := by omega
    subst h0; rfl
  | fuel + 1, n, m, hn => by
    simp only [pow3ModBin]
    split_ifs with h0 hodd
    · subst h0; rfl
    · have hlt : n / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      rw [pow3ModBin_eq fuel (n / 2) m hlt]
      have hsq : (3 ^ (n / 2) % m * (3 ^ (n / 2) % m)) % m = 3 ^ (2 * (n / 2)) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add, show n / 2 + n / 2 = 2 * (n / 2) by omega]
      rw [hsq]
      rw [Nat.mul_mod_mod, show 3 * 3 ^ (2 * (n / 2)) = 3 ^ (2 * (n / 2) + 1) by ring]
      rw [show 2 * (n / 2) + 1 = n by omega]
    · have hlt : n / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      rw [pow3ModBin_eq fuel (n / 2) m hlt]
      rw [← Nat.mul_mod, ← Nat.pow_add, show n / 2 + n / 2 = n by omega]

lemma MSeq_fast_step1 (e r_mod : Nat) (hlt : r_mod / 4 + 3 < 2 ^ 16) :
    (3 * MSeq (r_mod / 4) + 8) % 2 ^ (e + 2) =
    (pow3ModBin 16 (r_mod / 4 + 3) (2 ^ (e + 3)) / 2 + 5 * 2 ^ (e + 2) - 5) % 2 ^ (e + 2) := by
  apply mod_eq_of_add_five
  have h5 : 5 ≤ 5 * 2 ^ (e + 2) := by
    have : 1 ≤ 2 ^ (e + 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have hpow : 2 ^ (e + 3) = 2 * 2 ^ (e + 2) := by ring
  have h1 : (3 * MSeq (r_mod / 4) + 8) + 5 = 3 * MSeq (r_mod / 4) + 13 := by omega
  rw [h1, TSeq_mod_half (r_mod / 4) (2 ^ (e + 2)) (by positivity), ← hpow,
      ← pow3ModBin_eq 16 (r_mod / 4 + 3) (2 ^ (e + 3)) hlt]
  have hadd : (pow3ModBin 16 (r_mod / 4 + 3) (2 ^ (e + 3)) / 2 + 5 * 2 ^ (e + 2) - 5) + 5 =
              2 ^ (e + 2) * 5 + pow3ModBin 16 (r_mod / 4 + 3) (2 ^ (e + 3)) / 2 := by omega
  have hlt2 : pow3ModBin 16 (r_mod / 4 + 3) (2 ^ (e + 3)) / 2 < 2 ^ (e + 2) := by
    have hlt3 : 3 ^ (r_mod / 4 + 3) % 2 ^ (e + 3) < 2 ^ (e + 3) :=
      Nat.mod_lt _ (by positivity)
    rw [← pow3ModBin_eq 16 (r_mod / 4 + 3) (2 ^ (e + 3)) hlt] at hlt3
    omega
  rw [hadd, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt2]

lemma MSeq_fast_step3 (e r_mod : Nat) (hlt : r_mod / 4 + 3 < 2 ^ 16) :
    (3 * MSeq (r_mod / 4) + 14) % 2 ^ (e + 2) =
    (pow3ModBin 16 (r_mod / 4 + 3) (2 ^ (e + 3)) / 2 + 1) % 2 ^ (e + 2) := by
  have hpow : 2 ^ (e + 3) = 2 * 2 ^ (e + 2) := by ring
  rw [show 3 * MSeq (r_mod / 4) + 14 = (3 * MSeq (r_mod / 4) + 13) + 1 by omega,
      ← Nat.mod_add_mod (3 * MSeq (r_mod / 4) + 13) (2 ^ (e + 2)) 1,
      TSeq_mod_half (r_mod / 4) (2 ^ (e + 2)) (by positivity), ← hpow,
      ← pow3ModBin_eq 16 (r_mod / 4 + 3) (2 ^ (e + 3)) hlt]

theorem tower_halts : ReachHalt (G 5 0) := by
  have s0 : (5 : Nat) % 2 ^ 17 = 5 := by decide
  rcases step_mod1 14 5 5 s0 (by decide) (by decide) with ⟨a1, r1, h1⟩
  rw [MSeq_fast_step1 14 5 (by decide), show (pow3ModBin 16 (5 / 4 + 3) (2 ^ 17) / 2 + 5 * 2 ^ 16 - 5) % 2 ^ 16 = 35 by decide] at h1
  rcases step_mod3 13 a1 35 h1 (by decide) (by decide) with ⟨a2, r2, h2⟩
  rw [MSeq_fast_step3 13 35 (by decide), show (pow3ModBin 16 (35 / 4 + 3) (2 ^ 16) / 2 + 1) % 2 ^ 15 = 23038 by decide] at h2
  rcases step_mod2 12 a2 23038 h2 (by decide) (by decide) with ⟨a3, r3, h3⟩
  rw [MSeq_fast_step1 12 23038 (by decide), show (pow3ModBin 16 (23038 / 4 + 3) (2 ^ 15) / 2 + 5 * 2 ^ 14 - 5) % 2 ^ 14 = 255 by decide] at h3
  rcases step_mod3 11 a3 255 h3 (by decide) (by decide) with ⟨a4, r4, h4⟩
  rw [MSeq_fast_step3 11 255 (by decide), show (pow3ModBin 16 (255 / 4 + 3) (2 ^ 14) / 2 + 1) % 2 ^ 13 = 4741 by decide] at h4
  rcases step_mod1 10 a4 4741 h4 (by decide) (by decide) with ⟨a5, r5, h5⟩
  rw [MSeq_fast_step1 10 4741 (by decide), show (pow3ModBin 16 (4741 / 4 + 3) (2 ^ 13) / 2 + 5 * 2 ^ 12 - 5) % 2 ^ 12 = 2147 by decide] at h5
  rcases step_mod3 9 a5 2147 h5 (by decide) (by decide) with ⟨a6, r6, h6⟩
  rw [MSeq_fast_step3 9 2147 (by decide), show (pow3ModBin 16 (2147 / 4 + 3) (2 ^ 12) / 2 + 1) % 2 ^ 11 = 990 by decide] at h6
  rcases step_mod2 8 a6 990 h6 (by decide) (by decide) with ⟨a7, r7, h7⟩
  rw [MSeq_fast_step1 8 990 (by decide), show (pow3ModBin 16 (990 / 4 + 3) (2 ^ 11) / 2 + 5 * 2 ^ 10 - 5) % 2 ^ 10 = 175 by decide] at h7
  rcases step_mod3 7 a7 175 h7 (by decide) (by decide) with ⟨a8, r8, h8⟩
  rw [MSeq_fast_step3 7 175 (by decide), show (pow3ModBin 16 (175 / 4 + 3) (2 ^ 10) / 2 + 1) % 2 ^ 9 = 253 by decide] at h8
  rcases step_mod1 6 a8 253 h8 (by decide) (by decide) with ⟨a9, r9, h9⟩
  rw [MSeq_fast_step1 6 253 (by decide), show (pow3ModBin 16 (253 / 4 + 3) (2 ^ 9) / 2 + 5 * 2 ^ 8 - 5) % 2 ^ 8 = 127 by decide] at h9
  rcases step_mod3 5 a9 127 h9 (by decide) (by decide) with ⟨a10, r10, h10⟩
  rw [MSeq_fast_step3 5 127 (by decide), show (pow3ModBin 16 (127 / 4 + 3) (2 ^ 8) / 2 + 1) % 2 ^ 7 = 69 by decide] at h10
  rcases step_mod1 4 a10 69 h10 (by decide) (by decide) with ⟨a11, r11, h11⟩
  rw [MSeq_fast_step1 4 69 (by decide), show (pow3ModBin 16 (69 / 4 + 3) (2 ^ 7) / 2 + 5 * 2 ^ 6 - 5) % 2 ^ 6 = 3 by decide] at h11
  rcases step_mod3 3 a11 3 h11 (by decide) (by decide) with ⟨a12, r12, h12⟩
  rw [MSeq_fast_step3 3 3 (by decide), show (pow3ModBin 16 (3 / 4 + 3) (2 ^ 6) / 2 + 1) % 2 ^ 5 = 14 by decide] at h12
  rcases step_mod2 2 a12 14 h12 (by decide) (by decide) with ⟨a13, r13, h13⟩
  rw [MSeq_fast_step1 2 14 (by decide), show (pow3ModBin 16 (14 / 4 + 3) (2 ^ 5) / 2 + 5 * 2 ^ 4 - 5) % 2 ^ 4 = 7 by decide] at h13
  rcases step_mod3 1 a13 7 h13 (by decide) (by decide) with ⟨a14, r14, h14⟩
  rw [MSeq_fast_step3 1 7 (by decide), show (pow3ModBin 16 (7 / 4 + 3) (2 ^ 4) / 2 + 1) % 2 ^ 3 = 1 by decide] at h14
  rcases step_mod1 0 a14 1 h14 (by decide) (by decide) with ⟨a15, r15, h15⟩
  rw [MSeq_fast_step1 0 1 (by decide), show (pow3ModBin 16 (1 / 4 + 3) (2 ^ 3) / 2 + 5 * 2 ^ 2 - 5) % 2 ^ 2 = 0 by decide] at h15
  have ha15 : a15 = 4 * (a15 / 4) + 0 := by omega
  have hfin : ReachHalt (G a15 0) := by
    rw [ha15]
    exact G_drain (a15 / 4) 0 (G_halt (MSeq (a15 / 4)))
  exact r1 (r2 (r3 (r4 (r5 (r6 (r7 (r8 (r9 (r10 (r11 (r12 (r13 (r14 (r15 hfin))))))))))))))

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  rw [IsHalt, init_eq_cfg]
  exact ReachHalt.to_isHalt (init_to_G5 tower_halts)

end BusyBeaver.M_1RB0LD_1RC0RF_1LC1LA_0LEHHH_1LF0RB_0RC0RE
