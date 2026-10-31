/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RF_1LC0RA_---0LD_1RE1LD_0LF0LB_1RA1LE` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_1LC0RA_---0LD_1RE1LD_0LF0LB_1RA1LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_1LC0RA_HHH0LD_1RE1LD_0LF0LB_1RA1LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_1LC0RA_---0LD_1RE1LD_0LF0LB_1RA1LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 4, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5


-- ============================================================================
-- Backward Reachability & Fast Symbolic Execution Infrastructure
-- ============================================================================

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

def cfg (q : Fin 6) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some q, ⟨r.head, l, r.tail⟩⟩

@[simp] lemma zero_cons_default : b0 >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = b0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

lemma init_eq_cfg : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = cfg A default default := rfl

lemma step_cfg_right {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.right))
    (l r : ListBlank (Fin 2)) :
    step target_tm (cfg q l (b >> r)) = some (cfg q' (a >> l) r) := by
  simp [cfg, step, h, Turing.Tape.write, Turing.Tape.move]

lemma step_cfg_left {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    (c : Fin 2) (l r : ListBlank (Fin 2)) :
    step target_tm (cfg q (c >> l) (b >> r)) = some (cfg q' l (c >> a >> r)) := by
  simp [cfg, step, h, Turing.Tape.write, Turing.Tape.move]

lemma step_cfg_right_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.right))
    (l : ListBlank (Fin 2)) :
    step target_tm (cfg q l default) = some (cfg q' (a >> l) default) := by
  simpa using step_cfg_right h l default

lemma step_cfg_left_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.left))
    (c : Fin 2) (l : ListBlank (Fin 2)) :
    step target_tm (cfg q (c >> l) default) = some (cfg q' l (c >> a >> default)) := by
  simpa using step_cfg_left h c l default

lemma step_cfg_left_lnil {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    (r : ListBlank (Fin 2)) :
    step target_tm (cfg q default (b >> r)) = some (cfg q' default (b0 >> a >> r)) := by
  simpa using step_cfg_left h b0 default r

lemma reach_right {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.right))
    {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' (a >> l) r) target) :
    Reaches (cfg q l (b >> r)) target :=
  fun ht => ReachHalt.next (step_cfg_right h l r) (hr ht)

lemma reach_left {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    {c : Fin 2} {l r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' l (c >> a >> r)) target) :
    Reaches (cfg q (c >> l) (b >> r)) target :=
  fun ht => ReachHalt.next (step_cfg_left h c l r) (hr ht)

lemma reach_right_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.right))
    {l : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' (a >> l) default) target) :
    Reaches (cfg q l default) target :=
  fun ht => ReachHalt.next (step_cfg_right_nil h l) (hr ht)

lemma reach_left_nil {q q' : Fin 6} {a : Fin 2}
    (h : target_tm q b0 = some (some q', Stmt.write a Dir.left))
    {c : Fin 2} {l : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' l (c >> a >> default)) target) :
    Reaches (cfg q (c >> l) default) target :=
  fun ht => ReachHalt.next (step_cfg_left_nil h c l) (hr ht)

lemma reach_left_lnil {q q' : Fin 6} {b a : Fin 2}
    (h : target_tm q b = some (some q', Stmt.write a Dir.left))
    {r : ListBlank (Fin 2)} {target : Cfg (Fin 2) (Fin 6)}
    (hr : Reaches (cfg q' default (b0 >> a >> r)) target) :
    Reaches (cfg q default (b >> r)) target :=
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
-- Tape Encodings & Shift Lemmas
-- ============================================================================

def L01 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, l => l
  | k + 1, l => b0 >> b1 >> L01 k l

def L11 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, l => l
  | n + 1, l => b1 >> b1 >> L11 n l

def R1 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | c + 1, r => b1 >> R1 c r

def R01 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | d + 1, r => b0 >> b1 >> R01 d r

def L0 : ListBlank (Fin 2) := b0 >> b1 >> b0 >> b1 >> b1 >> default

@[simp] lemma L01_zero (l : ListBlank (Fin 2)) : L01 0 l = l := rfl
@[simp] lemma L01_succ (k : Nat) (l : ListBlank (Fin 2)) : L01 (k + 1) l = b0 >> b1 >> L01 k l := rfl
@[simp] lemma L11_zero (l : ListBlank (Fin 2)) : L11 0 l = l := rfl
@[simp] lemma L11_succ (n : Nat) (l : ListBlank (Fin 2)) : L11 (n + 1) l = b1 >> b1 >> L11 n l := rfl
@[simp] lemma R1_zero (r : ListBlank (Fin 2)) : R1 0 r = r := rfl
@[simp] lemma R1_succ (c : Nat) (r : ListBlank (Fin 2)) : R1 (c + 1) r = b1 >> R1 c r := rfl
@[simp] lemma R01_zero (r : ListBlank (Fin 2)) : R01 0 r = r := rfl
@[simp] lemma R01_succ (d : Nat) (r : ListBlank (Fin 2)) : R01 (d + 1) r = b0 >> b1 >> R01 d r := rfl

lemma L01_add (a b : Nat) (l : ListBlank (Fin 2)) : L01 (a + b) l = L01 a (L01 b l) := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]

lemma L11_add (a b : Nat) (l : ListBlank (Fin 2)) : L11 (a + b) l = L11 a (L11 b l) := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]

lemma R1_add (a b : Nat) (r : ListBlank (Fin 2)) : R1 (a + b) r = R1 a (R1 b r) := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]

lemma R01_add (a b : Nat) (r : ListBlank (Fin 2)) : R01 (a + b) r = R01 a (R01 b r) := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]

lemma L11_eq_R1 (n : Nat) (l : ListBlank (Fin 2)) : L11 n l = R1 (2 * n) l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [h, R1_add]
    simp [ih]

lemma cons1_L11_cons1 (m : Nat) (l : ListBlank (Fin 2)) :
    b1 >> L11 m (b1 >> l) = L11 (m + 1) l := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

lemma L0_eq_L01 : L0 = L01 2 (b1 >> default) := rfl

lemma shift_A_01 (d : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg A l (R01 d r)) (cfg A (L01 d l) r) := by
  induction d generalizing l with
  | zero => exact Reaches.refl _
  | succ d ih =>
    have h1 : Reaches (cfg A l (b0 >> b1 >> R01 d r)) (cfg A (b0 >> b1 >> l) (R01 d r)) := by
      exec_tm 2
    refine h1.trans ?_
    have h2 := ih (b0 >> b1 >> l)
    have h_eq : L01 d (b0 >> b1 >> l) = L01 (d + 1) l := by
      change L01 d (L01 1 l) = L01 (d + 1) l
      rw [← L01_add]
    rwa [h_eq] at h2

lemma shift_F_01 (d : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg F l (R01 d r)) (cfg F (L11 d l) r) := by
  induction d generalizing l with
  | zero => exact Reaches.refl _
  | succ d ih =>
    have h1 : Reaches (cfg F l (b0 >> b1 >> R01 d r)) (cfg F (b1 >> b1 >> l) (R01 d r)) := by
      exec_tm 2
    refine h1.trans ?_
    have h2 := ih (b1 >> b1 >> l)
    have h_eq : L11 d (b1 >> b1 >> l) = L11 (d + 1) l := by
      change L11 d (L11 1 l) = L11 (d + 1) l
      rw [← L11_add]
    rwa [h_eq] at h2

lemma shift_A_1_01 (d : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg A l (b1 >> R01 d r)) (cfg A (L11 d l) (b1 >> r)) := by
  induction d generalizing l with
  | zero => exact Reaches.refl _
  | succ d ih =>
    have h1 : Reaches (cfg A l (b1 >> b0 >> b1 >> R01 d r)) (cfg A (b1 >> b1 >> l) (b1 >> R01 d r)) := by
      exec_tm 2
    refine h1.trans ?_
    have h2 := ih (b1 >> b1 >> l)
    have h_eq : L11 d (b1 >> b1 >> l) = L11 (d + 1) l := by
      change L11 d (L11 1 l) = L11 (d + 1) l
      rw [← L11_add]
    rwa [h_eq] at h2

lemma shift_D_1 (m : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg D (R1 m l) (b1 >> r)) (cfg D l (R1 (m + 1) r)) := by
  induction m generalizing r with
  | zero => exact Reaches.refl _
  | succ m ih =>
    have h1 : Reaches (cfg D (b1 >> R1 m l) (b1 >> r)) (cfg D (R1 m l) (b1 >> (b1 >> r))) := by
      exec_tm 1
    refine h1.trans ?_
    have h2 := ih (b1 >> r)
    have h_eq : R1 (m + 1) (b1 >> r) = R1 (m + 2) r := by
      change R1 (m + 1) (R1 1 r) = R1 (m + 1 + 1) r
      rw [← R1_add]
    rwa [h_eq] at h2

lemma shift_E_01_pair (j : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg E (L01 (2 * j) l) (b1 >> b1 >> r)) (cfg E l (b1 >> b1 >> R01 (2 * j) r)) := by
  induction j generalizing r with
  | zero => exact Reaches.refl _
  | succ j ih =>
    have h_split : 2 * (j + 1) = 2 + 2 * j := by omega
    rw [h_split, L01_add]
    have h1 : Reaches (cfg E (b0 >> b1 >> b0 >> b1 >> L01 (2 * j) l) (b1 >> b1 >> r))
        (cfg E (L01 (2 * j) l) (b1 >> b1 >> (b0 >> b1 >> b0 >> b1 >> r))) := by
      exec_tm 6
    refine h1.trans ?_
    have h2 := ih (b0 >> b1 >> b0 >> b1 >> r)
    have h_eq : R01 (2 * j) (b0 >> b1 >> b0 >> b1 >> r) = R01 (2 + 2 * j) r := by
      change R01 (2 * j) (R01 2 r) = R01 (2 + 2 * j) r
      rw [← R01_add, Nat.add_comm]
    rwa [h_eq] at h2

lemma reach_C_from_even (j : Nat) (l : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j) l) default) (cfg C l (b1 >> b1 >> R01 (2 * j) default)) := by
  cases j with
  | zero =>
    simp only [Nat.mul_zero, L01_zero, R01_zero]
    exec_tm 2
  | succ j =>
    have h_split : 2 * (j + 1) = 1 + (2 * j + 1) := by omega
    have h_r2 : b0 >> b1 >> R01 (2 * j + 1) default = R01 (2 * (j + 1)) default := by
      have h_idx : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [h_idx]; rfl
    rw [← h_r2, h_split, L01_add, L01_add]
    change Reaches (cfg A (b0 >> b1 >> L01 (2 * j) (b0 >> b1 >> l)) default) _
    have h1 : Reaches (cfg A (b0 >> b1 >> L01 (2 * j) (b0 >> b1 >> l)) default)
        (cfg E (L01 (2 * j) (b0 >> b1 >> l)) (b1 >> b1 >> R01 1 default)) := by
      exec_tm 6
    refine h1.trans ?_
    refine (shift_E_01_pair j (b0 >> b1 >> l) (R01 1 default)).trans ?_
    have h_r : R01 (2 * j) (R01 1 default) = R01 (2 * j + 1) default := by
      rw [← R01_add]
    rw [h_r]
    exec_tm 2

lemma restore_L0 (m : Nat) :
    Reaches (cfg A (L01 (2 * (m + 1)) default) default) (cfg A (L01 (2 * (m + 1)) L0) default) := by
  have h1 := reach_C_from_even (m + 1) default
  refine h1.trans ?_
  have h2 : Reaches (cfg C default (b1 >> b1 >> R01 (2 * (m + 1)) default))
      (cfg A (b1 >> default) (R01 (2 * (m + 1) + 2) default)) := by
    exec_tm 6
  refine h2.trans ?_
  have h3 := shift_A_01 (2 * (m + 1) + 2) (b1 >> default) default
  have h_eq : L01 (2 * (m + 1) + 2) (b1 >> default) = L01 (2 * (m + 1)) L0 := by
    rw [L01_add]; rfl
  rwa [h_eq] at h3

lemma c_b1_bounce (r : ListBlank (Fin 2)) :
    Reaches (cfg C (b1 >> default) (b1 >> b1 >> r)) (cfg A L0 (b1 >> r)) := by
  exec_tm 17

lemma d_L0_bounce (r : ListBlank (Fin 2)) :
    Reaches (cfg D L0 (b1 >> b1 >> r)) (cfg A (L01 1 L0) r) := by
  exec_tm 6

lemma d_b01_shift (l' r' : ListBlank (Fin 2)) :
    Reaches (cfg D (b0 >> b1 >> l') (b1 >> b1 >> r'))
            (cfg A (b0 >> b1 >> b0 >> b1 >> l') r') := by
  exec_tm 6

lemma drain_C_L11 (m : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg C (L11 (m + 1) l) (b1 >> b1 >> r))
            (cfg D l (R1 (2 * m + 2) (b0 >> b1 >> r))) := by
  rw [L11_succ, L11_eq_R1]
  have h1 : Reaches (cfg C (b1 >> b1 >> R1 (2 * m) l) (b1 >> b1 >> r))
      (cfg D (R1 (2 * m + 1) l) (b1 >> (b0 >> b1 >> r))) := by
    have h_eq : b1 >> R1 (2 * m) l = R1 (2 * m + 1) l := by
      change R1 1 (R1 (2 * m) l) = R1 (2 * m + 1) l
      rw [← R1_add, Nat.add_comm]
    rw [← h_eq]
    exec_tm 1
  refine h1.trans ?_
  exact shift_D_1 (2 * m + 1) l (b0 >> b1 >> r)

-- ============================================================================
-- Canonical Configurations & Basic Macro-Step Rules
-- ============================================================================

inductive RBlocks where
  | nil : RBlocks
  | cons : Nat → Nat → RBlocks → RBlocks
deriving DecidableEq, Repr

def evalRBlocks : RBlocks → ListBlank (Fin 2)
  | .nil => default
  | .cons c d rest => R1 c (R01 d (evalRBlocks rest))

@[simp] lemma evalRBlocks_nil : evalRBlocks .nil = default := rfl
@[simp] lemma evalRBlocks_cons (c d : Nat) (rest : RBlocks) :
    evalRBlocks (.cons c d rest) = R1 c (R01 d (evalRBlocks rest)) := rfl

def toCfg (k n : Nat) (blks : RBlocks) : Cfg (Fin 2) (Fin 6) :=
  cfg A (L01 k (L11 n L0)) (evalRBlocks blks)

lemma rule_c0 (k n d : Nat) (rest : RBlocks) :
    Reaches (toCfg k n (.cons 0 d rest)) (toCfg (k + d) n rest) := by
  unfold toCfg
  rw [evalRBlocks_cons, R1_zero]
  have h := shift_A_01 d (L01 k (L11 n L0)) (evalRBlocks rest)
  have h_eq : L01 d (L01 k (L11 n L0)) = L01 (k + d) (L11 n L0) := by
    rw [← L01_add, Nat.add_comm]
  rwa [h_eq] at h

lemma step_even_nge1_one (j : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j) (b1 >> b1 >> l)) (b1 >> b1 >> r))
            (cfg A (L01 (2 * (j + 1)) l) r) := by
  have h1 : Reaches (cfg A (L01 (2 * j) (b1 >> b1 >> l)) (b1 >> b1 >> r))
      (cfg E (L01 (2 * j) (b1 >> b1 >> l)) (b1 >> b1 >> r)) := by
    exec_tm 2
  refine h1.trans ?_
  refine (shift_E_01_pair j (b1 >> b1 >> l) r).trans ?_
  have h2 : Reaches (cfg E (b1 >> b1 >> l) (b1 >> b1 >> R01 (2 * j) r))
      (cfg A (L01 1 l) (R01 (2 * j + 1) r)) := by
    have h_r : b0 >> b1 >> R01 (2 * j) r = R01 (2 * j + 1) r := rfl
    rw [← h_r]
    exec_tm 2
  refine h2.trans ?_
  have h3 := shift_A_01 (2 * j + 1) (L01 1 l) r
  have h_eq : L01 (2 * j + 1) (L01 1 l) = L01 (2 * (j + 1)) l := by
    rw [← L01_add]
    congr 1
  rwa [h_eq] at h3

lemma step_even_nge1 (m j : Nat) (l r : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j) (L11 m l)) (R1 (2 * m) r))
            (cfg A (L01 (2 * (j + m)) l) r) := by
  induction m generalizing j with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero, L11_zero, R1_zero]
    exact Reaches.refl _
  | succ m ih =>
    have h_r : 2 * (m + 1) = 2 + 2 * m := by omega
    rw [L11_succ, h_r, R1_add]
    change Reaches (cfg A (L01 (2 * j) (b1 >> b1 >> L11 m l)) (b1 >> b1 >> R1 (2 * m) r)) _
    refine (step_even_nge1_one j (L11 m l) (R1 (2 * m) r)).trans ?_
    have h2 := ih (j + 1)
    have h_eq : 2 * (j + 1 + m) = 2 * (j + (m + 1)) := by omega
    rwa [h_eq] at h2

lemma rule_even_nge1 (m j n c d : Nat) (rest : RBlocks) :
    Reaches (toCfg (2 * j) (m + n) (.cons (2 * m + c) d rest))
            (toCfg (2 * j + 2 * m) n (.cons c d rest)) := by
  unfold toCfg
  rw [evalRBlocks_cons, evalRBlocks_cons, L11_add, R1_add]
  have h := step_even_nge1 m j (L11 n L0) (R1 c (R01 d (evalRBlocks rest)))
  have h_eq : 2 * (j + m) = 2 * j + 2 * m := by omega
  rwa [h_eq] at h

lemma step_odd_n0 (j : Nat) (r : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j + 1) L0) (b1 >> b1 >> r))
            (cfg A (L11 (2 * j + 3) L0) (b1 >> r)) := by
  have h_l : L01 (2 * j + 1) L0 = L01 (2 * (j + 1)) (b0 >> b1 >> b1 >> default) := by
    rw [L0_eq_L01, ← L01_add]
    have h_idx : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
    rw [h_idx, L01_add]; rfl
  rw [h_l]
  have h1 : Reaches (cfg A (L01 (2 * (j + 1)) (b0 >> b1 >> b1 >> default)) (b1 >> b1 >> r))
      (cfg E (L01 (2 * (j + 1)) (b0 >> b1 >> b1 >> default)) (b1 >> b1 >> r)) := by
    exec_tm 2
  refine h1.trans ?_
  refine (shift_E_01_pair (j + 1) (b0 >> b1 >> b1 >> default) r).trans ?_
  have h2 : Reaches (cfg E (b0 >> b1 >> b1 >> default) (b1 >> b1 >> R01 (2 * (j + 1)) r))
      (cfg C (b1 >> default) (b1 >> b1 >> R01 (2 * j + 3) r)) := by
    have h_r : b0 >> b1 >> R01 (2 * (j + 1)) r = R01 (2 * j + 3) r := rfl
    rw [← h_r]
    exec_tm 2
  refine h2.trans ?_
  refine (c_b1_bounce (R01 (2 * j + 3) r)).trans ?_
  exact shift_A_1_01 (2 * j + 3) L0 r

lemma rule_odd_n0 (j c d : Nat) (rest : RBlocks) :
    Reaches (toCfg (2 * j + 1) 0 (.cons (c + 2) d rest))
            (toCfg 0 (3 + 2 * j) (.cons (c + 1) d rest)) := by
  unfold toCfg
  have h_c : c + 2 = 2 + c := by omega
  have h_c1 : c + 1 = 1 + c := by omega
  rw [evalRBlocks_cons, evalRBlocks_cons, L11_zero, L01_zero, h_c, R1_add, h_c1, R1_add]
  have h := step_odd_n0 j (R1 c (R01 d (evalRBlocks rest)))
  have h_n : 2 * j + 3 = 3 + 2 * j := by omega
  rwa [h_n] at h

lemma step_k1_to_k6 (c0 d : Nat) (rest : RBlocks) :
    Reaches (toCfg 1 0 (.cons (c0 + 7) d rest)) (toCfg 6 0 (.cons c0 d rest)) := by
  have h1 : toCfg 1 0 (.cons (c0 + 7) d rest) = toCfg (2 * 0 + 1) 0 (.cons ((c0 + 5) + 2) d rest) := by
    simp [Nat.add_assoc]
  rw [h1]
  refine (rule_odd_n0 0 (c0 + 5) d rest).trans ?_
  have h2 : toCfg 0 (3 + 2 * 0) (.cons ((c0 + 5) + 1) d rest) =
      toCfg (2 * 0) (3 + 0) (.cons (2 * 3 + c0) d rest) := by
    congr 2; omega
  rw [h2]
  exact rule_even_nge1 3 0 0 c0 d rest

lemma step_odd_nge1 (j m : Nat) (r : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j + 1) (L11 (m + 1) L0)) (b1 >> b1 >> r))
            (cfg A (L01 1 L0) (R1 (2 * m) (R01 (2 * j + 2) r))) := by
  have h_l : L01 (2 * j + 1) (L11 (m + 1) L0) = L01 (2 * j) (b0 >> b1 >> L11 (m + 1) L0) := by
    rw [L01_add]; rfl
  rw [h_l]
  have h1 : Reaches (cfg A (L01 (2 * j) (b0 >> b1 >> L11 (m + 1) L0)) (b1 >> b1 >> r))
      (cfg E (L01 (2 * j) (b0 >> b1 >> L11 (m + 1) L0)) (b1 >> b1 >> r)) := by
    exec_tm 2
  refine h1.trans ?_
  refine (shift_E_01_pair j (b0 >> b1 >> L11 (m + 1) L0) r).trans ?_
  have h2 : Reaches (cfg E (b0 >> b1 >> L11 (m + 1) L0) (b1 >> b1 >> R01 (2 * j) r))
      (cfg C (L11 (m + 1) L0) (b1 >> b1 >> R01 (2 * j + 1) r)) := by
    have h_r : b0 >> b1 >> R01 (2 * j) r = R01 (2 * j + 1) r := rfl
    rw [← h_r]
    exec_tm 2
  refine h2.trans ?_
  refine (drain_C_L11 m L0 (R01 (2 * j + 1) r)).trans ?_
  have h_r2 : R1 (2 * m + 2) (b0 >> b1 >> R01 (2 * j + 1) r) =
      b1 >> b1 >> R1 (2 * m) (R01 (2 * j + 2) r) := by
    have h_split : 2 * m + 2 = 2 + 2 * m := by omega
    rw [h_split, R1_add]; rfl
  rw [h_r2]
  exact d_L0_bounce (R1 (2 * m) (R01 (2 * j + 2) r))

lemma rule_odd_nge1 (j m c d : Nat) (rest : RBlocks) :
    Reaches (toCfg (2 * j + 1) (m + 1) (.cons (c + 2) d rest))
            (toCfg 1 0 (.cons (2 * m) (2 + 2 * j) (.cons c d rest))) := by
  unfold toCfg
  have h_c : c + 2 = 2 + c := by omega
  have h_j : 2 + 2 * j = 2 * j + 2 := by omega
  rw [evalRBlocks_cons, evalRBlocks_cons, evalRBlocks_cons, L11_zero, h_c, R1_add, h_j]
  exact step_odd_nge1 j m (R1 c (R01 d (evalRBlocks rest)))

lemma even_n0_boundary (j : Nat) (r : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j) L0) (b1 >> b1 >> r))
            (cfg A (L01 (2 * j + 3) default) r) := by
  have h1 : Reaches (cfg A (L01 (2 * j) L0) (b1 >> b1 >> r))
      (cfg E (L01 (2 * j) L0) (b1 >> b1 >> r)) := by
    exec_tm 2
  refine h1.trans ?_
  refine (shift_E_01_pair j L0 r).trans ?_
  have h2 : Reaches (cfg E L0 (b1 >> b1 >> R01 (2 * j) r))
      (cfg A default (R01 (2 * j + 3) r)) := by
    have h_r : b0 >> b1 >> b0 >> b1 >> b0 >> b1 >> R01 (2 * j) r = R01 (2 * j + 3) r := by
      have h_idx : 2 * j + 3 = 3 + 2 * j := by omega
      rw [h_idx, R01_add]; rfl
    rw [← h_r]
    exec_tm 8
  refine h2.trans ?_
  exact shift_A_01 (2 * j + 3) default r

lemma step_even_n0_c4 (j : Nat) (r_rem : ListBlank (Fin 2)) :
    Reaches (cfg A (L01 (2 * j) L0) (b1 >> b1 >> b1 >> b1 >> r_rem))
            (cfg A (L01 (2 * j + 3) L0) r_rem) := by
  refine (even_n0_boundary j (b1 >> b1 >> r_rem)).trans ?_
  have h_l : L01 (2 * j + 3) default = L01 (2 * (j + 1)) (b0 >> b1 >> default) := by
    have h_idx : 2 * j + 3 = 2 * (j + 1) + 1 := by omega
    rw [h_idx, L01_add]; rfl
  rw [h_l]
  have h1 : Reaches (cfg A (L01 (2 * (j + 1)) (b0 >> b1 >> default)) (b1 >> b1 >> r_rem))
      (cfg E (L01 (2 * (j + 1)) (b0 >> b1 >> default)) (b1 >> b1 >> r_rem)) := by
    exec_tm 2
  refine h1.trans ?_
  refine (shift_E_01_pair (j + 1) (b0 >> b1 >> default) r_rem).trans ?_
  have h2 : Reaches (cfg E (b0 >> b1 >> default) (b1 >> b1 >> R01 (2 * (j + 1)) r_rem))
      (cfg A (b1 >> default) (R01 (2 * j + 5) r_rem)) := by
    have h_r : b0 >> b1 >> b0 >> b1 >> b0 >> b1 >> R01 (2 * (j + 1)) r_rem = R01 (2 * j + 5) r_rem := by
      have h_idx : 2 * j + 5 = 3 + 2 * (j + 1) := by omega
      rw [h_idx, R01_add]; rfl
    rw [← h_r]
    exec_tm 8
  refine h2.trans ?_
  have h3 := shift_A_01 (2 * j + 5) (b1 >> default) r_rem
  have h_eq : L01 (2 * j + 5) (b1 >> default) = L01 (2 * j + 3) L0 := by
    have h_idx : 2 * j + 5 = (2 * j + 3) + 2 := by omega
    rw [h_idx, L01_add]; rfl
  rwa [h_eq] at h3

lemma rule_even_n0_c4 (j d : Nat) (rest : RBlocks) :
    Reaches (toCfg (2 * j) 0 (.cons 4 d rest))
            (toCfg (3 + 2 * j + d) 0 rest) := by
  unfold toCfg
  rw [evalRBlocks_cons, L11_zero]
  change Reaches (cfg A (L01 (2 * j) L0) (b1 >> b1 >> b1 >> b1 >> R01 d (evalRBlocks rest))) _
  refine (step_even_n0_c4 j (R01 d (evalRBlocks rest))).trans ?_
  have h := shift_A_01 d (L01 (2 * j + 3) L0) (evalRBlocks rest)
  have h_eq : L01 d (L01 (2 * j + 3) L0) = L01 (3 + 2 * j + d) L0 := by
    rw [← L01_add]; congr 1; omega
  rwa [h_eq] at h

lemma rule_even_n0_cge6 (j c d : Nat) (rest : RBlocks) :
    Reaches (toCfg (2 * j) 0 (.cons (c + 6) d rest))
            (toCfg 0 (5 + 2 * j) (.cons (c + 1) d rest)) := by
  have h_c : c + 6 = 4 + (c + 2) := by omega
  unfold toCfg
  rw [evalRBlocks_cons, L11_zero, h_c, R1_add]
  change Reaches (cfg A (L01 (2 * j) L0) (b1 >> b1 >> b1 >> b1 >> evalRBlocks (.cons (c + 2) d rest))) _
  refine (step_even_n0_c4 j (evalRBlocks (.cons (c + 2) d rest))).trans ?_
  have h1 : cfg A (L01 (2 * j + 3) L0) (evalRBlocks (.cons (c + 2) d rest)) =
      toCfg (2 * (j + 1) + 1) 0 (.cons (c + 2) d rest) := by
    unfold toCfg
    have h_idx : 2 * j + 3 = 2 * (j + 1) + 1 := by omega
    rw [L11_zero, h_idx]
  rw [h1]
  have h2 := rule_odd_n0 (j + 1) c d rest
  have h_n : 3 + 2 * (j + 1) = 5 + 2 * j := by omega
  rwa [h_n] at h2

lemma cons1_R1 (c : Nat) (r : ListBlank (Fin 2)) :
    b1 >> R1 c r = R1 c (b1 >> r) := by
  induction c with
  | zero => rfl
  | succ c ih => simp [ih]

lemma bounce_A_1_01_end (d : Nat) (l : ListBlank (Fin 2)) :
    Reaches (cfg A l (b1 >> R01 d default))
            (cfg D l (b1 >> b1 >> R1 (2 * d) (R01 1 default))) := by
  have h1 : Reaches (cfg A l (b1 >> R01 d default)) (cfg F (b1 >> l) (R01 d default)) := by
    exec_tm 1
  refine h1.trans ?_
  refine (shift_F_01 d (b1 >> l) default).trans ?_
  have h2 : Reaches (cfg F (L11 d (b1 >> l)) default)
      (cfg C (L11 (d + 1) l) (b1 >> b1 >> default)) := by
    rw [← cons1_L11_cons1]
    exec_tm 3
  refine h2.trans ?_
  have h3 := drain_C_L11 d l default
  have h_r : R1 (2 * d + 2) (b0 >> b1 >> default) = b1 >> b1 >> R1 (2 * d) (R01 1 default) := by
    have h_split : 2 * d + 2 = 2 + 2 * d := by omega
    rw [h_split, R1_add]; rfl
  rwa [h_r] at h3

lemma rule_c1_end (k n d : Nat) :
    Reaches (toCfg (k + 1) n (.cons 1 d .nil))
            (toCfg (1 + (k + 1)) n (.cons (2 * d) 1 .nil)) := by
  unfold toCfg
  rw [evalRBlocks_cons, evalRBlocks_nil, R1_succ, R1_zero]
  refine (bounce_A_1_01_end d (L01 (k + 1) (L11 n L0))).trans ?_
  rw [L01_succ]
  have h := d_b01_shift (L01 k (L11 n L0)) (R1 (2 * d) (R01 1 default))
  have h_l : b0 >> b1 >> b0 >> b1 >> L01 k (L11 n L0) = L01 (1 + (k + 1)) (L11 n L0) := by
    have h_idx : 1 + (k + 1) = k + 1 + 1 := by omega
    rw [h_idx]; rfl
  rwa [h_l] at h

lemma rule_c1_large_c2 (k n d c1 d2 : Nat) (rest2 : RBlocks) :
    Reaches (toCfg k n (.cons 1 (d + 1) (.cons (2 * (d + 1) + c1 - 1) d2 rest2)))
            (toCfg (k + 2 * (d + 1)) n (.cons c1 d2 rest2)) := by
  unfold toCfg
  rw [evalRBlocks_cons, evalRBlocks_cons, R1_succ, R1_zero]
  refine (shift_A_1_01 (d + 1) (L01 k (L11 n L0)) (R1 (2 * (d + 1) + c1 - 1) (R01 d2 (evalRBlocks rest2)))).trans ?_
  have h_r : b1 >> R1 (2 * (d + 1) + c1 - 1) (R01 d2 (evalRBlocks rest2)) =
      R1 (2 * (d + 1)) (R1 c1 (R01 d2 (evalRBlocks rest2))) := by
    have h_c2 : 2 * (d + 1) + c1 - 1 + 1 = 2 * (d + 1) + c1 := by omega
    rw [← R1_succ, h_c2, R1_add]
  rw [h_r]
  have h2 := step_even_nge1 (d + 1) 0 (L01 k (L11 n L0)) (R1 c1 (R01 d2 (evalRBlocks rest2)))
  simp only [Nat.mul_zero, L01_zero, Nat.zero_add] at h2
  have h_l : L01 (2 * (d + 1)) (L01 k (L11 n L0)) = L01 (k + 2 * (d + 1)) (L11 n L0) := by
    rw [← L01_add, Nat.add_comm]
  rwa [h_l] at h2

lemma L01_cons01 (k : Nat) (l : ListBlank (Fin 2)) :
    b0 >> b1 >> L01 k l = L01 k (b0 >> b1 >> l) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

lemma step_c1_small_c2_core (r m' d2' : Nat) (l : ListBlank (Fin 2)) :
    Reaches (cfg A l (b1 >> R01 ((m' + 1) + (r + 1)) (R1 (2 * (m' + 1)) (R01 (d2' + 1) default))))
            (cfg D l (b1 >> b1 >> R1 (2 * r) (R01 (2 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default))))) := by
  refine (shift_A_1_01 ((m' + 1) + (r + 1)) l (R1 (2 * (m' + 1)) (R01 (d2' + 1) default))).trans ?_
  rw [L11_add, cons1_R1]
  have h1 := step_even_nge1 (m' + 1) 0 (L11 (r + 1) l) (b1 >> R01 (d2' + 1) default)
  simp only [Nat.mul_zero, L01_zero, Nat.zero_add] at h1
  refine h1.trans ?_
  refine (bounce_A_1_01_end (d2' + 1) (L01 (2 * (m' + 1)) (L11 (r + 1) l))).trans ?_
  have h_split : 2 * (m' + 1) = (2 * m' + 1) + 1 := by omega
  rw [h_split, L01_succ]
  refine (d_b01_shift (L01 (2 * m' + 1) (L11 (r + 1) l)) (R1 (2 * (d2' + 1)) (R01 1 default))).trans ?_
  have h_l3 : b0 >> b1 >> b0 >> b1 >> L01 (2 * m' + 1) (L11 (r + 1) l) =
      L01 (2 * (m' + 1)) (b0 >> b1 >> L11 (r + 1) l) := by
    rw [L01_cons01, h_split]; rfl
  have h_r3 : R1 (2 * (d2' + 1)) (R01 1 default) = b1 >> b1 >> R1 (2 * d2') (R01 1 default) := by
    have h_s2 : 2 * (d2' + 1) = 2 + 2 * d2' := by omega
    rw [h_s2, R1_add]; rfl
  rw [h_l3, h_r3]
  have h3 : Reaches (cfg A (L01 (2 * (m' + 1)) (b0 >> b1 >> L11 (r + 1) l)) (b1 >> b1 >> R1 (2 * d2') (R01 1 default)))
      (cfg E (L01 (2 * (m' + 1)) (b0 >> b1 >> L11 (r + 1) l)) (b1 >> b1 >> R1 (2 * d2') (R01 1 default))) := by
    exec_tm 2
  refine h3.trans ?_
  refine (shift_E_01_pair (m' + 1) (b0 >> b1 >> L11 (r + 1) l) (R1 (2 * d2') (R01 1 default))).trans ?_
  have h4 : Reaches (cfg E (b0 >> b1 >> L11 (r + 1) l) (b1 >> b1 >> R01 (2 * (m' + 1)) (R1 (2 * d2') (R01 1 default))))
      (cfg C (L11 (r + 1) l) (b1 >> b1 >> R01 (1 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default)))) := by
    have h_r01 : b0 >> b1 >> R01 (2 * (m' + 1)) (R1 (2 * d2') (R01 1 default)) =
        R01 (1 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default)) := by
      have h_idx : 1 + 2 * (m' + 1) = 2 * (m' + 1) + 1 := by omega
      rw [h_idx]; rfl
    rw [← h_r01]
    exec_tm 2
  refine h4.trans ?_
  refine (drain_C_L11 r l (R01 (1 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default)))).trans ?_
  have h_r4 : R1 (2 * r + 2) (b0 >> b1 >> R01 (1 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default))) =
      b1 >> b1 >> R1 (2 * r) (R01 (2 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default))) := by
    have h_s3 : 2 * r + 2 = 2 + 2 * r := by omega
    have h_idx : 2 + 2 * (m' + 1) = (1 + 2 * (m' + 1)) + 1 := by omega
    rw [h_s3, R1_add, h_idx]; rfl
  rw [h_r4]
  exact Reaches.refl _

lemma step_c1_small_c2 (k n r' m' d2' : Nat) :
    Reaches (toCfg (k + 1) n (.cons 1 ((m' + 1) + (r' + 1)) (.cons (2 * (m' + 1)) (d2' + 1) .nil)))
            (cfg A (L01 (k + 2) (L11 n L0))
              (R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default))))) := by
  unfold toCfg
  rw [evalRBlocks_cons, evalRBlocks_cons, evalRBlocks_nil, R1_succ, R1_zero]
  refine (step_c1_small_c2_core r' m' d2' (L01 (k + 1) (L11 n L0))).trans ?_
  exact d_b01_shift (L01 k (L11 n L0)) (R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R1 (2 * d2') (R01 1 default))))

lemma rule_nil_even_nge2 (j m' : Nat) :
    Reaches (toCfg (2 * j) (m' + 2) .nil)
            (toCfg 1 0 (.cons (2 * m' + 2) (1 + 2 * j) .nil)) := by
  unfold toCfg
  rw [evalRBlocks_nil, evalRBlocks_cons, evalRBlocks_nil, L11_zero]
  refine (reach_C_from_even j (L11 (m' + 1 + 1) L0)).trans ?_
  refine (drain_C_L11 (m' + 1) L0 (R01 (2 * j) default)).trans ?_
  have h_r : R1 (2 * (m' + 1) + 2) (b0 >> b1 >> R01 (2 * j) default) =
      b1 >> b1 >> R1 (2 * m' + 2) (R01 (1 + 2 * j) default) := by
    have h_split : 2 * (m' + 1) + 2 = 2 + (2 * m' + 2) := by omega
    have h_idx : 1 + 2 * j = 2 * j + 1 := by omega
    rw [h_split, R1_add, h_idx]; rfl
  rw [h_r]
  exact d_L0_bounce (R1 (2 * m' + 2) (R01 (1 + 2 * j) default))

abbrev lb0 : ListBlank (Fin 2) := default

lemma rule_nil_even_n0 (j : Nat) :
    Reaches (toCfg (2 * j) 0 .nil)
            (toCfg 1 0 (.cons (4 + 4 * j) 1 .nil)) := by
  have h_start : toCfg (2 * j) 0 .nil = cfg A (L01 (2 * (j + 1)) (b1 >> lb0)) default := by
    unfold toCfg
    have h_idx : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [evalRBlocks_nil, L11_zero, L0_eq_L01, ← L01_add, h_idx]
  rw [h_start]
  refine (reach_C_from_even (j + 1) (b1 >> lb0)).trans ?_
  refine (c_b1_bounce (R01 (2 * (j + 1)) default)).trans ?_
  refine (shift_A_1_01 (2 * (j + 1)) L0 default).trans ?_
  have h1 : Reaches (cfg A (L11 (2 * (j + 1)) L0) (b1 >> lb0))
      (toCfg (2 * 0) ((2 * j + 1) + 2) .nil) := by
    unfold toCfg
    have h_n : (2 * j + 1) + 2 = 2 * (j + 1) + 1 := by omega
    rw [evalRBlocks_nil, Nat.mul_zero, L01_zero, h_n, L11_succ]
    exec_tm 2
  refine h1.trans ?_
  have h2 := rule_nil_even_nge2 0 (2 * j + 1)
  have h_c : 2 * (2 * j + 1) + 2 = 4 + 4 * j := by omega
  rwa [h_c] at h2

lemma step_nil_odd_ind (n j : Nat) :
    Reaches (toCfg (2 * j + 1) n .nil)
            (toCfg (2 * (j + n) + 1) 0 .nil) := by
  induction n generalizing j with
  | zero =>
    simp only [Nat.add_zero]
    exact Reaches.refl _
  | succ n ih =>
    unfold toCfg
    rw [evalRBlocks_nil]
    have h_l : L01 (2 * j + 1) (L11 (n + 1) L0) = L01 (2 * j) (b0 >> b1 >> L11 (n + 1) L0) := by
      rw [L01_add]; rfl
    rw [h_l]
    refine (reach_C_from_even j (b0 >> b1 >> L11 (n + 1) L0)).trans ?_
    have h1 : Reaches (cfg C (b0 >> b1 >> L11 (n + 1) L0) (b1 >> b1 >> R01 (2 * j) default))
        (cfg A (L01 1 (L11 n L0)) (R01 (2 * j + 2) default)) := by
      rw [L11_succ]
      have h_r : b0 >> b1 >> b0 >> b1 >> R01 (2 * j) default = R01 (2 * j + 2) default := by
        have h_idx : 2 * j + 2 = 2 + 2 * j := by omega
        rw [h_idx, R01_add]; rfl
      rw [← h_r]
      exec_tm 6
    refine h1.trans ?_
    refine (shift_A_01 (2 * j + 2) (L01 1 (L11 n L0)) default).trans ?_
    have h_l2 : cfg A (L01 (2 * j + 2) (L01 1 (L11 n L0))) default = toCfg (2 * (j + 1) + 1) n .nil := by
      unfold toCfg
      have h_idx : 2 * j + 2 + 1 = 2 * (j + 1) + 1 := by omega
      rw [evalRBlocks_nil, ← L01_add, h_idx]
    rw [h_l2]
    have h2 := ih (j + 1)
    have h_idx : j + 1 + n = j + (n + 1) := by omega
    rwa [h_idx] at h2

lemma rule_nil_odd (j n : Nat) :
    Reaches (toCfg (2 * j + 1) n .nil)
            (toCfg 1 0 (.cons (12 + 4 * j + 4 * n) 1 .nil)) := by
  refine (step_nil_odd_ind n j).trans ?_
  let J := j + n
  have h_l : toCfg (2 * J + 1) 0 .nil = cfg A (L01 (2 * (J + 1)) (b0 >> b1 >> b1 >> lb0)) default := by
    unfold toCfg
    rw [evalRBlocks_nil, L11_zero, L0_eq_L01, ← L01_add]
    have h_idx : 2 * J + 1 + 2 = 2 * (J + 1) + 1 := by omega
    rw [h_idx, L01_add]; rfl
  rw [h_l]
  refine (reach_C_from_even (J + 1) (b0 >> b1 >> b1 >> lb0)).trans ?_
  have h1 : Reaches (cfg C (b0 >> b1 >> b1 >> lb0) (b1 >> b1 >> R01 (2 * (J + 1)) default))
      (cfg A default (R01 (2 * (J + 2)) default)) := by
    have h_r : b0 >> b1 >> b0 >> b1 >> R01 (2 * (J + 1)) default = R01 (2 * (J + 2)) default := by
      have h_idx : 2 * (J + 2) = 2 + 2 * (J + 1) := by omega
      rw [h_idx, R01_add]; rfl
    rw [← h_r]
    exec_tm 6
  refine h1.trans ?_
  refine (shift_A_01 (2 * (J + 2)) default default).trans ?_
  refine (restore_L0 (J + 1)).trans ?_
  have h2 := rule_nil_even_n0 (J + 2)
  have h_c : 4 + 4 * (J + 2) = 12 + 4 * j + 4 * n := by omega
  rwa [h_c] at h2

lemma halt_from_E_default (r : ListBlank (Fin 2)) :
    ReachHalt (cfg E default (b1 >> b1 >> r)) := by
  refine ReachHalt.next (step_cfg_left_lnil rfl (b1 >> r)) ?_
  refine ReachHalt.next (step_cfg_left_lnil rfl (b0 >> b1 >> r)) ?_
  exact ReachHalt.done (by simp [cfg, step, target_tm])

lemma rule_even_n0_c2 (j m : Nat) :
    Reaches (toCfg (2 * j) 0 (.cons 2 (2 * m + 1) .nil))
            (toCfg (3 + 2 * j + (2 * m + 1)) 0 .nil) := by
  unfold toCfg
  rw [evalRBlocks_cons, evalRBlocks_nil, L11_zero]
  change Reaches (cfg A (L01 (2 * j) L0) (b1 >> b1 >> R01 (2 * m + 1) default)) _
  refine (even_n0_boundary j (R01 (2 * m + 1) default)).trans ?_
  refine (shift_A_01 (2 * m + 1) (L01 (2 * j + 3) default) default).trans ?_
  have h_eq : (2 * m + 1) + (2 * j + 3) = 2 * (j + m + 1 + 1) := by omega
  rw [← L01_add, h_eq]
  have h2 := restore_L0 (j + m + 1)
  have h_eq2 : 2 * (j + m + 1 + 1) = 3 + 2 * j + (2 * m + 1) := by omega
  rw [← h_eq2]
  exact h2

lemma rule_halt_c3 (j r' m' : Nat) :
    ReachHalt (toCfg (2 * j) 0 (.cons 3 ((m' + 1) + (r' + 2)) (.cons (2 * (m' + 1)) 1 .nil))) := by
  unfold toCfg
  rw [evalRBlocks_cons, evalRBlocks_cons, evalRBlocks_nil, L11_zero]
  change ReachHalt (cfg A (L01 (2 * j) L0) (b1 >> b1 >> b1 >> R01 ((m' + 1) + (r' + 2)) (R1 (2 * (m' + 1)) (R01 1 default))))
  refine even_n0_boundary j (b1 >> R01 ((m' + 1) + (r' + 2)) (R1 (2 * (m' + 1)) (R01 1 default))) ?_
  refine step_c1_small_c2_core (r' + 1) m' 0 (L01 (2 * j + 3) default) ?_
  have h_r : R1 (2 * (r' + 1)) (R01 (2 + 2 * (m' + 1)) (R1 (2 * 0) (R01 1 default))) =
      b1 >> b1 >> R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R01 1 default)) := by
    have h_split : 2 * (r' + 1) = 2 + 2 * r' := by omega
    rw [h_split, R1_add]; rfl
  rw [h_r]
  refine d_b01_shift (L01 (2 * j + 2) default) (b1 >> b1 >> R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R01 1 default))) ?_
  change ReachHalt (cfg A (L01 (2 * j + 4) default) (b1 >> b1 >> R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R01 1 default))))
  have h_l2 : 2 * j + 4 = 2 * (j + 2) := by omega
  rw [h_l2]
  have h_ae : Reaches (cfg A (L01 (2 * (j + 2)) default) (b1 >> b1 >> R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R01 1 default))))
      (cfg E (L01 (2 * (j + 2)) default) (b1 >> b1 >> R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R01 1 default)))) := by
    exec_tm 2
  refine h_ae ?_
  refine shift_E_01_pair (j + 2) default (R1 (2 * r') (R01 (2 + 2 * (m' + 1)) (R01 1 default))) ?_
  exact halt_from_E_default _

-- ============================================================================
-- Accelerated Era Loops: `step_withR_iter` and `step_outer_era_iter`
-- ============================================================================

lemma five_mul_le_pow2 (r : Nat) : 5 * r ≤ 20 * (2 ^ r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h_pow : 2 ^ (r + 1) = 2 * 2 ^ r := Nat.pow_succ'
    have h_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by decide)
    omega

lemma mul_pow2_sub_one_succ (m p : Nat) (hp : 1 ≤ p) :
    4 * (m + 5) * (2 * p - 1) = (4 * m + 20) + 4 * ((2 * m + 5) + 5) * (p - 1) := by
  have h_sub : 2 * p - 1 = 1 + 2 * (p - 1) := by omega
  have h_m : 4 * (m + 5) * 2 = 4 * ((2 * m + 5) + 5) := by omega
  have h_m1 : 4 * (m + 5) * 1 = 4 * m + 20 := by omega
  rw [h_sub, Nat.mul_add, h_m1, ← Nat.mul_assoc, h_m]

lemma step_withR_one (m c d : Nat) (rest : RBlocks) :
    Reaches (toCfg (2 * m) 0 (.cons (c + 1 + (4 * m + 15)) d rest))
            (toCfg (2 * (2 * m + 5)) 0 (.cons (c + 1) d rest)) := by
  have h1 : c + 1 + (4 * m + 15) = (c + (4 * m + 10)) + 6 := by omega
  rw [h1]
  refine (rule_even_n0_cge6 m (c + (4 * m + 10)) d rest).trans ?_
  have h2 : (c + (4 * m + 10)) + 1 = 2 * (5 + 2 * m) + (c + 1) := by omega
  rw [h2]
  have h3 := rule_even_nge1 (5 + 2 * m) 0 0 (c + 1) d rest
  have h4 : 2 * 0 + 2 * (5 + 2 * m) = 2 * (2 * m + 5) := by omega
  rwa [h4] at h3

lemma step_withR_iter (r m c_start c_end d : Nat) (rest : RBlocks)
    (h_c : 1 ≤ c_end)
    (h_eq : c_start + 5 * r = c_end + 4 * (m + 5) * (2 ^ r - 1)) :
    Reaches (toCfg (2 * m) 0 (.cons c_start d rest))
            (toCfg (2 * ((m + 5) * 2 ^ r - 5)) 0 (.cons c_end d rest)) := by
  induction r generalizing m c_start with
  | zero =>
    have h_c_eq : c_start = c_end := by
      simp only [Nat.pow_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at h_eq
      exact h_eq
    have h_k_eq : 2 * ((m + 5) * 2 ^ 0 - 5) = 2 * m := by simp
    rw [h_c_eq, h_k_eq]
    exact Reaches.refl _
  | succ r ih =>
    have h_pow : 2 ^ (r + 1) = 2 * 2 ^ r := Nat.pow_succ'
    have h_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by decide)
    have h_five := five_mul_le_pow2 r
    have h_mul : 20 * (2 ^ r - 1) ≤ 4 * ((2 * m + 5) + 5) * (2 ^ r - 1) :=
      Nat.mul_le_mul_right (2 ^ r - 1) (by omega)
    rw [h_pow, mul_pow2_sub_one_succ m (2 ^ r) h_pos] at h_eq
    let c_mid := c_start - (4 * m + 15)
    have h_cmid_ge : 1 ≤ c_mid := by omega
    have h_cstart : c_start = (c_mid - 1) + 1 + (4 * m + 15) := by omega
    rw [h_cstart]
    refine (step_withR_one m (c_mid - 1) d rest).trans ?_
    have h_cmid_eq : c_mid - 1 + 1 = c_mid := by omega
    rw [h_cmid_eq]
    have h_ih := ih (2 * m + 5) c_mid (by omega)
    have h_k : (2 * m + 5 + 5) * 2 ^ r = (m + 5) * 2 ^ (r + 1) := by
      have h_2m : 2 * m + 5 + 5 = (m + 5) * 2 := by omega
      rw [h_pow, h_2m, Nat.mul_assoc]
    rwa [h_k] at h_ih

lemma toCfg_cons_zero (k n c1 d1 d2 : Nat) (rest : RBlocks) :
    toCfg k n (.cons c1 d1 (.cons 0 d2 rest)) = toCfg k n (.cons c1 (d1 + d2) rest) := by
  unfold toCfg
  simp [R01_add]

lemma step_outer_era_pair (jc jr p jr2 p2 D_half limit h : Nat)
    (hp : p = 2 ^ (2 * jr + 1))
    (hp2 : p2 = 2 ^ (2 * jr2))
    (h_jc : 4 ≤ jc)
    (h_jr : 1 ≤ jr)
    (h_jr2 : 1 ≤ jr2)
    (h_b1 : 8 + 32 * p ≤ 30 + 2 * jc + 10 * jr)
    (h_b2 : 71 + 2 * jc + 10 * jr ≤ 64 * p)
    (h_b3 : 1 + 64 * p ≤ 44 + 2 * jc + 64 * p2 + 20 * jr)
    (h_D : 2 * D_half = 44 + 2 * jc + 64 * p2 + 20 * jr - 64 * p)
    (h_b4 : 30 + (64 * p - (36 + 2 * jc + 10 * jr)) + 10 * jr2 ≤ 64 * p2)
    (h_p2_lin : 26 + 10 * jr2 ≤ 32 * p2)
    (h_lim : limit = 18 + (64 * p - (36 + 2 * jc + 10 * jr)) + 2 * D_half + 10 * jr2 - 32 * p2)
    (h_le : 2 * h + 2 * D_half ≤ limit) :
    Reaches (toCfg 1 0 (.cons (2 * jc + 2 * h) 1 .nil))
            (toCfg 1 0 (.cons (2 * jc + 2 * D_half + 4 * h) 1 .nil)) := by
  have hp_ge : 8 ≤ p := by
    rw [hp]
    have : 2 ^ 3 ≤ 2 ^ (2 * jr + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hp2_ge : 4 ≤ p2 := by
    rw [hp2]
    have : 2 ^ 2 ≤ 2 ^ (2 * jr2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let m1 := (12 + jc + 5 * jr + h) - 16 * p
  let n_rem1' := 32 * p - (18 + jc + 5 * jr + h)
  let m2 := (10 + n_rem1' + 5 * jr2) - 16 * p2
  let n_rem2 := (16 * p2 - 5) - m2
  have hm1 : m1 = (12 + jc + 5 * jr + h) - 16 * p := rfl
  have hn1 : n_rem1' = 32 * p - (18 + jc + 5 * jr + h) := rfl
  have hm2 : m2 = (10 + n_rem1' + 5 * jr2) - 16 * p2 := rfl
  have hn2 : n_rem2 = (16 * p2 - 5) - m2 := rfl
  have h_e1_start : 2 * jc + 2 * h = (2 * jc + 2 * h - 7) + 7 := by omega
  rw [h_e1_start]
  refine (step_k1_to_k6 (2 * jc + 2 * h - 7) 1 .nil).trans ?_
  have h_r1 := step_withR_iter (2 * jr + 1) 3 (2 * jc + 2 * h - 7) (2 * m1 + 6) 1 .nil (by omega) (by rw [← hp]; omega)
  have h_k1 : 2 * ((3 + 5) * 2 ^ (2 * jr + 1) - 5) = 2 * (8 * p - 5) := by rw [← hp]
  rw [h_k1] at h_r1
  refine (show Reaches (toCfg (2 * 3) 0 _) _ from h_r1).trans ?_
  refine (rule_even_n0_cge6 (8 * p - 5) (2 * m1) 1 .nil).trans ?_
  have h_mid1 : 5 + 2 * (8 * p - 5) = m1 + (n_rem1' + 1) := by omega
  rw [h_mid1]
  refine (rule_even_nge1 m1 0 (n_rem1' + 1) 1 1 .nil).trans ?_
  have h_c1_in : 2 * 0 + 2 * m1 = (2 * m1 - 1) + 1 := by omega
  rw [h_c1_in]
  refine (rule_c1_end (2 * m1 - 1) (n_rem1' + 1) 1).trans ?_
  have h_odd1_in : 1 + ((2 * m1 - 1) + 1) = 2 * m1 + 1 := by omega
  rw [h_odd1_in]
  refine (rule_odd_nge1 m1 n_rem1' 0 1 .nil).trans ?_
  rw [toCfg_cons_zero]
  have h_e2_c : 2 * n_rem1' = (2 * n_rem1' - 7) + 7 := by omega
  have h_e2_d : 2 + 2 * m1 + 1 = 2 * m1 + 3 := by omega
  rw [h_e2_c, h_e2_d]
  refine (step_k1_to_k6 (2 * n_rem1' - 7) (2 * m1 + 3) .nil).trans ?_
  have h_r2 := step_withR_iter (2 * jr2) 3 (2 * n_rem1' - 7) (2 * m2 + 5) (2 * m1 + 3) .nil (by omega) (by rw [← hp2]; omega)
  have h_k2 : 2 * ((3 + 5) * 2 ^ (2 * jr2) - 5) = 2 * (8 * p2 - 5) := by rw [← hp2]
  rw [h_k2] at h_r2
  refine (show Reaches (toCfg (2 * 3) 0 _) _ from h_r2).trans ?_
  have h_cge6_in : 2 * m2 + 5 = (2 * m2 - 1) + 6 := by omega
  rw [h_cge6_in]
  refine (rule_even_n0_cge6 (8 * p2 - 5) (2 * m2 - 1) (2 * m1 + 3) .nil).trans ?_
  have h_mid2_n : 5 + 2 * (8 * p2 - 5) = m2 + n_rem2 := by omega
  have h_mid2_c : (2 * m2 - 1) + 1 = 2 * m2 + 0 := by omega
  rw [h_mid2_n, h_mid2_c]
  refine (rule_even_nge1 m2 0 n_rem2 0 (2 * m1 + 3) .nil).trans ?_
  refine (rule_c0 (2 * 0 + 2 * m2) n_rem2 (2 * m1 + 3) .nil).trans ?_
  have h_nil_in : 2 * 0 + 2 * m2 + (2 * m1 + 3) = 2 * (m2 + m1 + 1) + 1 := by omega
  rw [h_nil_in]
  have h_end := rule_nil_odd (m2 + m1 + 1) n_rem2
  have h_final : 12 + 4 * (m2 + m1 + 1) + 4 * n_rem2 = 2 * jc + 2 * D_half + 4 * h := by omega
  rwa [h_final] at h_end

lemma step_outer_era_iter (i : Nat) (jc jr p jr2 p2 D_half limit : Nat)
    (hp : p = 2 ^ (2 * jr + 1))
    (hp2 : p2 = 2 ^ (2 * jr2))
    (h_jc : 4 ≤ jc)
    (h_jr : 1 ≤ jr)
    (h_jr2 : 1 ≤ jr2)
    (h_b1 : 8 + 32 * p ≤ 30 + 2 * jc + 10 * jr)
    (h_b2 : 71 + 2 * jc + 10 * jr ≤ 64 * p)
    (h_b3 : 1 + 64 * p ≤ 44 + 2 * jc + 64 * p2 + 20 * jr)
    (h_D : 2 * D_half = 44 + 2 * jc + 64 * p2 + 20 * jr - 64 * p)
    (h_b4 : 30 + (64 * p - (36 + 2 * jc + 10 * jr)) + 10 * jr2 ≤ 64 * p2)
    (h_p2_lin : 26 + 10 * jr2 ≤ 32 * p2)
    (h_lim : limit = 18 + (64 * p - (36 + 2 * jc + 10 * jr)) + 2 * D_half + 10 * jr2 - 32 * p2)
    (h_le : 2 * D_half * 2 ^ i ≤ 2 * limit) :
    Reaches (toCfg 1 0 (.cons (2 * jc) 1 .nil))
            (toCfg 1 0 (.cons (2 * jc + 2 * D_half * (2 ^ i - 1)) 1 .nil)) := by
  induction i with
  | zero =>
    simp only [Nat.pow_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Reaches.refl _
  | succ i ih =>
    have h_pow : 2 ^ (i + 1) = 2 * 2 ^ i := Nat.pow_succ'
    have h_pos : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by decide)
    have h_2h : 2 * (D_half * (2 ^ i - 1)) = 2 * D_half * (2 ^ i - 1) := by
      rw [← Nat.mul_assoc]
    have h_4h : 4 * (D_half * (2 ^ i - 1)) = 2 * (2 * D_half * (2 ^ i - 1)) := by
      have : 4 = 2 * 2 := rfl
      rw [this, Nat.mul_assoc, h_2h]
    have h_sub : 2 * D_half * (2 ^ (i + 1) - 1) = 2 * D_half + 2 * (2 * D_half * (2 ^ i - 1)) := by
      have h1 : 2 ^ (i + 1) - 1 = 1 + 2 * (2 ^ i - 1) := by omega
      rw [h1, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
    have h_id : 2 * (D_half * (2 ^ i - 1)) + 2 * D_half = 2 * D_half * 2 ^ i := by
      have h1 : 1 + (2 ^ i - 1) = 2 ^ i := by omega
      calc 2 * (D_half * (2 ^ i - 1)) + 2 * D_half
        _ = 2 * D_half + 2 * D_half * (2 ^ i - 1) := by omega
        _ = 2 * D_half * (1 + (2 ^ i - 1)) := by rw [Nat.mul_add, Nat.mul_one]
        _ = 2 * D_half * 2 ^ i := by rw [h1]
    have h_dbl : 2 * D_half * 2 ^ (i + 1) = 2 * (2 * D_half * 2 ^ i) := by
      rw [h_pow, Nat.mul_left_comm]
    refine (ih (by omega)).trans ?_
    rw [← h_2h]
    have h_step := step_outer_era_pair jc jr p jr2 p2 D_half limit (D_half * (2 ^ i - 1))
      hp hp2 h_jc h_jr h_jr2 h_b1 h_b2 h_b3 h_D h_b4 h_p2_lin h_lim (by omega)
    have h_out : 2 * jc + 2 * D_half + 4 * (D_half * (2 ^ i - 1)) = 2 * jc + 2 * D_half * (2 ^ (i + 1) - 1) := by
      omega
    rwa [h_out] at h_step

-- ============================================================================
-- Executable Macro-Simulator & Soundness
-- ============================================================================

inductive HState where
  | active : Nat → Nat → RBlocks → HState
  | halted : HState
deriving DecidableEq, Repr

def bindNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  match Nat.add 1 n with
  | 0 => k 0
  | m + 1 => k m

def bindBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  match b with
  | true => k true
  | false => k false

@[simp] lemma bindNat_eq {α : Type} (n : Nat) (k : Nat → α) : bindNat n k = k n := by
  unfold bindNat
  rw [show Nat.add 1 n = n + 1 from Nat.add_comm 1 n]

@[simp] lemma bindBool_eq {α : Type} (b : Bool) (k : Bool → α) : bindBool b k = k b := by
  cases b <;> rfl

@[simp] lemma nat_ble_eq_true (a b : Nat) : (Nat.ble a b = true) ↔ a ≤ b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

@[simp] lemma nat_beq_eq_true (a b : Nat) : (Nat.beq a b = true) ↔ a = b := by
  simp [Nat.beq_eq]

def bindState (s : HState) (f : HState → HState) : HState :=
  match s with
  | .halted => .halted
  | .active k n blks => f (.active k n blks)

inductive ValidState : HState → Prop
  | halted : ValidState .halted
  | active {k n blks} : ReachHalt (toCfg k n blks) → ValidState (.active k n blks)

@[irreducible] def ValidFrom (k n : Nat) (blks : RBlocks) (s : HState) : Prop :=
  ValidState s → ReachHalt (toCfg k n blks)

lemma ValidFrom.self (k n : Nat) (blks : RBlocks) :
    ValidFrom k n blks (.active k n blks) := by
  unfold ValidFrom
  intro hs; cases hs with | active h => exact h

lemma ValidFrom.halted {k n : Nat} {blks : RBlocks} (h : ReachHalt (toCfg k n blks)) :
    ValidFrom k n blks .halted := by
  unfold ValidFrom
  exact fun _ => h

lemma ValidFrom.of_reaches {k n k' n' : Nat} {blks blks' : RBlocks} {s : HState}
    (h1 : Reaches (toCfg k n blks) (toCfg k' n' blks'))
    (h2 : ValidFrom k' n' blks' s) :
    ValidFrom k n blks s := by
  unfold ValidFrom at *
  exact fun hs => h1 (h2 hs)

lemma ValidState.of_validFrom {k n : Nat} {blks : RBlocks} {s : HState}
    (h : ValidFrom k n blks s) (hs : ValidState s) :
    ValidState (.active k n blks) := by
  unfold ValidFrom at h
  exact ValidState.active (h hs)

lemma min_le_left_sub (n c : Nat) : Nat.min n (c / 2) + (n - Nat.min n (c / 2)) = n := by
  change min n (c / 2) + (n - min n (c / 2)) = n
  omega

lemma min_le_right_sub (n c : Nat) : 2 * Nat.min n (c / 2) + (c - 2 * Nat.min n (c / 2)) = c := by
  change 2 * min n (c / 2) + (c - 2 * min n (c / 2)) = c
  omega

def mkActive0 (k n : Nat) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  HState.active k' n' .nil

def mkActiveRaw1 (k n c d : Nat) (rest : RBlocks) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  bindNat c fun c' =>
  bindNat d fun d' =>
  HState.active k' n' (.cons c' d' rest)

def mkActiveRaw2 (k n c1 d1 c2 d2 : Nat) (rest : RBlocks) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  bindNat c1 fun c1' =>
  bindNat d1 fun d1' =>
  bindNat c2 fun c2' =>
  bindNat d2 fun d2' =>
  HState.active k' n' (.cons c1' d1' (.cons c2' d2' rest))

def mkActiveRest0 (k n : Nat) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  if Nat.beq (k' % 2) 1 then
    bindNat ((k' - 1) / 2) fun j =>
    mkActiveRaw1 1 0 (12 + (4 * j + 4 * n')) 1 .nil
  else if Nat.beq n' 0 then
    bindNat (k' / 2) fun j =>
    mkActiveRaw1 1 0 (4 + 4 * j) 1 .nil
  else
    mkActive0 k' n'

lemma mkActiveRest0_sound (k n : Nat) :
    ValidFrom k n .nil (mkActiveRest0 k n) := by
  unfold mkActiveRest0 mkActiveRaw1 mkActive0
  simp only [bindNat_eq]
  split
  · next h_odd =>
    simp only [nat_beq_eq_true] at h_odd
    have hk : 2 * ((k - 1) / 2) + 1 = k := by omega
    have hc : 12 + 4 * ((k - 1) / 2) + 4 * n = 12 + (4 * ((k - 1) / 2) + 4 * n) := by omega
    have h_step := rule_nil_odd ((k - 1) / 2) n
    rw [hk, hc] at h_step
    exact ValidFrom.of_reaches h_step (ValidFrom.self _ _ _)
  · next h_even =>
    simp only [nat_beq_eq_true] at h_even
    split
    · next hn0 =>
      simp only [nat_beq_eq_true] at hn0
      have hk : 2 * (k / 2) = k := by omega
      have h_step := rule_nil_even_n0 (k / 2)
      rw [hk] at h_step
      rw [hn0]
      exact ValidFrom.of_reaches h_step (ValidFrom.self _ _ _)
    · exact ValidFrom.self _ _ _

lemma step_mk10_c1 (j m d : Nat) (hj : 1 ≤ j) (hd : 1 ≤ d) :
    Reaches (toCfg (2 * j) (m + 1) (.cons 1 d .nil))
            (toCfg 1 0 (.cons (2 * m) (2 + 2 * j) (.cons (2 * d - 2) 1 .nil))) := by
  have h1 := rule_c1_end (2 * j - 1) (m + 1) d
  have hk1 : (2 * j - 1) + 1 = 2 * j := by omega
  have hk2 : 1 + 2 * j = 2 * j + 1 := by omega
  rw [hk1, hk2] at h1
  have h2 := rule_odd_nge1 j m (2 * d - 2) 1 .nil
  have hd2 : (2 * d - 2) + 2 = 2 * d := by omega
  rw [hd2] at h2
  exact h1.trans h2

def mkActive10 (k n c d : Nat) (rest : RBlocks) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  bindNat c fun c' =>
  bindNat d fun d' =>
  match rest with
  | .nil =>
    if Nat.beq c' 0 then
      mkActiveRest0 (k' + d') n'
    else if Nat.beq c' 1 && Nat.ble 1 d' && Nat.ble 2 k' && Nat.beq (k' % 2) 0 && Nat.ble 1 n' then
      if Nat.beq d' 1 then
        if Nat.beq n' 1 then
          mkActiveRest0 (4 + k') 0
        else
          mkActiveRaw1 1 0 (2 * n' - 2) (3 + k') .nil
      else
        mkActiveRaw2 1 0 (2 * n' - 2) (2 + k') (2 * d' - 2) 1 .nil
    else if Nat.beq c' 2 && Nat.beq n' 0 && Nat.beq (k' % 2) 0 && Nat.beq (d' % 2) 1 then
      mkActiveRest0 (3 + (k' + d')) 0
    else
      mkActiveRaw1 k' n' c' d' .nil
  | .cons _ _ _ =>
    if Nat.beq c' 0 then
      HState.active (k' + d') n' rest
    else
      mkActiveRaw1 k' n' c' d' rest

lemma mkActive10_sound (k n c d : Nat) (rest : RBlocks) :
    ValidFrom k n (.cons c d rest) (mkActive10 k n c d rest) := by
  cases rest with
  | cons c2 d2 rest2 =>
    simp only [mkActive10, mkActiveRaw1, bindNat_eq]
    split
    · next hc0 =>
      simp only [nat_beq_eq_true] at hc0
      rw [hc0]
      exact ValidFrom.of_reaches (rule_c0 k n d (.cons c2 d2 rest2)) (ValidFrom.self _ _ _)
    · exact ValidFrom.self _ _ _
  | nil =>
    simp only [mkActive10, mkActiveRaw1, mkActiveRaw2, bindNat_eq]
    split
    · next hc0 =>
      simp only [nat_beq_eq_true] at hc0
      rw [hc0]
      exact ValidFrom.of_reaches (rule_c0 k n d .nil) (mkActiveRest0_sound (k + d) n)
    · next hnc0 =>
      split
      · next h_c1 =>
        simp only [Bool.and_eq_true, nat_beq_eq_true, nat_ble_eq_true] at h_c1
        have hc : c = 1 := by omega
        have hk : 2 * (k / 2) = k := by omega
        have hn : (n - 1) + 1 = n := by omega
        have hc_out : 2 * (n - 1) = 2 * n - 2 := by omega
        have h_step := step_mk10_c1 (k / 2) (n - 1) d (by omega) (by omega)
        rw [hk, hn, hc_out] at h_step
        rw [hc]
        split
        · next hd1 =>
          simp only [nat_beq_eq_true] at hd1
          have hd_z : 2 * d - 2 = 0 := by omega
          have hd_k : 2 + k + 1 = 3 + k := by omega
          rw [hd_z, toCfg_cons_zero, hd_k] at h_step
          split
          · next hn1 =>
            simp only [nat_beq_eq_true] at hn1
            have hn_z : 2 * n - 2 = 0 := by omega
            rw [hn_z] at h_step
            have h_c0 := rule_c0 1 0 (3 + k) .nil
            have hk4 : 1 + (3 + k) = 4 + k := by omega
            rw [hk4] at h_c0
            exact ValidFrom.of_reaches (h_step.trans h_c0) (mkActiveRest0_sound (4 + k) 0)
          · exact ValidFrom.of_reaches h_step (ValidFrom.self _ _ _)
        · exact ValidFrom.of_reaches h_step (ValidFrom.self _ _ _)
      · next h_nc1 =>
        split
        · next h_c2 =>
          simp only [Bool.and_eq_true, nat_beq_eq_true] at h_c2
          have hc : c = 2 := by omega
          have hn : n = 0 := by omega
          have hk : 2 * (k / 2) = k := by omega
          have hd : 2 * ((d - 1) / 2) + 1 = d := by omega
          have h_out : 3 + k + d = 3 + (k + d) := by omega
          have h_step := rule_even_n0_c2 (k / 2) ((d - 1) / 2)
          rw [hk, hd, h_out] at h_step
          rw [hc, hn]
          exact ValidFrom.of_reaches h_step (mkActiveRest0_sound (3 + (k + d)) 0)
        · exact ValidFrom.self _ _ _

def mkActiveRest (k n : Nat) (rest : RBlocks) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  match rest with
  | .nil => mkActiveRest0 k' n'
  | .cons c2 d2 rest2 =>
    if Nat.beq (k' % 2) 0 && Nat.ble 1 n' && Nat.ble 2 c2 then
      bindNat (Nat.min n' (c2 / 2)) fun m =>
      mkActive10 (k' + 2 * m) (n' - m) (c2 - 2 * m) d2 rest2
    else
      HState.active k' n' rest

lemma mkActiveRest_sound (k n : Nat) (rest : RBlocks) :
    ValidFrom k n rest (mkActiveRest k n rest) := by
  cases rest with
  | nil =>
    simp only [mkActiveRest, bindNat_eq]
    exact mkActiveRest0_sound k n
  | cons c2 d2 rest2 =>
    simp only [mkActiveRest, bindNat_eq]
    split
    · next h_cond =>
      simp only [Bool.and_eq_true, nat_beq_eq_true, nat_ble_eq_true] at h_cond
      have hk : 2 * (k / 2) = k := by omega
      have h_step := rule_even_nge1 (Nat.min n (c2 / 2)) (k / 2) (n - Nat.min n (c2 / 2)) (c2 - 2 * Nat.min n (c2 / 2)) d2 rest2
      rw [hk, min_le_left_sub, min_le_right_sub] at h_step
      exact ValidFrom.of_reaches h_step (mkActive10_sound _ _ _ d2 rest2)
    · exact ValidFrom.self _ _ _

def mkActive1 (k n c d : Nat) (rest : RBlocks) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  bindNat c fun c' =>
  bindNat d fun d' =>
  if Nat.beq c' 0 then
    mkActiveRest (k' + d') n' rest
  else
    mkActive10 k' n' c' d' rest

lemma mkActive1_sound (k n c d : Nat) (rest : RBlocks) :
    ValidFrom k n (.cons c d rest) (mkActive1 k n c d rest) := by
  unfold mkActive1
  simp only [bindNat_eq]
  split
  · next hc0 =>
    simp only [nat_beq_eq_true] at hc0
    rw [hc0]
    exact ValidFrom.of_reaches (rule_c0 k n d rest) (mkActiveRest_sound (k + d) n rest)
  · exact mkActive10_sound k n c d rest

def mkActive1Drain (k1 n c1 d2 : Nat) (rest2 : RBlocks) : HState :=
  bindNat k1 fun k1' =>
  bindNat n fun n' =>
  bindNat c1 fun c1' =>
  if Nat.beq (k1' % 2) 0 && Nat.ble 1 n' && Nat.ble 2 c1' then
    bindNat (Nat.min n' (c1' / 2)) fun m =>
    mkActive1 (k1' + 2 * m) (n' - m) (c1' - 2 * m) d2 rest2
  else
    mkActive1 k1' n' c1' d2 rest2

lemma mkActive1Drain_sound (k1 n c1 d2 : Nat) (rest2 : RBlocks) :
    ValidFrom k1 n (.cons c1 d2 rest2) (mkActive1Drain k1 n c1 d2 rest2) := by
  unfold mkActive1Drain
  simp only [bindNat_eq]
  split
  · next h_cond =>
    simp only [Bool.and_eq_true, nat_beq_eq_true, nat_ble_eq_true] at h_cond
    have hk : 2 * (k1 / 2) = k1 := by omega
    have h_step := rule_even_nge1 (Nat.min n (c1 / 2)) (k1 / 2) (n - Nat.min n (c1 / 2)) (c1 - 2 * Nat.min n (c1 / 2)) d2 rest2
    rw [hk, min_le_left_sub, min_le_right_sub] at h_step
    exact ValidFrom.of_reaches h_step (mkActive1_sound _ _ _ d2 rest2)
  · exact mkActive1_sound k1 n c1 d2 rest2

def mkActive2 (k n c1 d1 c2 d2 : Nat) (rest : RBlocks) : HState :=
  bindNat k fun k' =>
  bindNat n fun n' =>
  bindNat c1 fun c1' =>
  bindNat d1 fun d1' =>
  bindNat c2 fun c2' =>
  bindNat d2 fun d2' =>
  if Nat.beq c1' 0 then
    mkActive1 (k' + d1') n' c2' d2' rest
  else
    HState.active k' n' (.cons c1' d1' (.cons c2' d2' rest))

lemma mkActive2_sound (k n c1 d1 c2 d2 : Nat) (rest : RBlocks) :
    ValidFrom k n (.cons c1 d1 (.cons c2 d2 rest)) (mkActive2 k n c1 d1 c2 d2 rest) := by
  unfold mkActive2
  simp only [bindNat_eq]
  split
  · next hc0 =>
    have hc : c1 = 0 := Nat.eq_of_beq_eq_true hc0
    rw [hc]
    exact ValidFrom.of_reaches (rule_c0 k n d1 (.cons c2 d2 rest)) (mkActive1_sound (k + d1) n c2 d2 rest)
  · exact ValidFrom.self _ _ _

def pow2_256 : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
def pow2_128 : Nat := 340282366920938463463374607431768211456
def pow2_64  : Nat := 18446744073709551616
def pow2_32  : Nat := 4294967296
def pow2_16  : Nat := 65536

def stepBSearch (K c bit powBit r p : Nat) (cont : Nat → Nat → HState) : HState :=
  bindNat (bit + r) fun r' =>
  bindNat (p * powBit) fun p' =>
  bindBool (Nat.ble (1 + K * (2 * p' - 2)) (c + 5 * r')) fun ok =>
  bindNat (if ok then r' else r) fun r_next =>
  bindNat (if ok then p' else p) fun p_next =>
  cont r_next p_next

def withR (K c : Nat) (cont : Nat → Nat → HState) : HState :=
  stepBSearch K c 256 pow2_256 0 1 fun r p =>
  stepBSearch K c 128 pow2_128 r p fun r p =>
  stepBSearch K c 64  pow2_64  r p fun r p =>
  stepBSearch K c 32  pow2_32  r p fun r p =>
  stepBSearch K c 16  pow2_16  r p fun r p =>
  stepBSearch K c 8   256      r p fun r p =>
  stepBSearch K c 4   16       r p fun r p =>
  stepBSearch K c 2   4        r p fun r p =>
  stepBSearch K c 1   2        r p cont

lemma stepBSearch_spec (K c bit powBit r p : Nat) (cont : Nat → Nat → HState)
    (P : HState → Prop)
    (h_pow : powBit = 2 ^ bit)
    (h_p : p = 2 ^ r)
    (h_cont : ∀ r' p', p' = 2 ^ r' → P (cont r' p')) :
    P (stepBSearch K c bit powBit r p cont) := by
  unfold stepBSearch
  simp only [bindNat_eq, bindBool_eq]
  split
  · apply h_cont
    rw [h_p, h_pow, Nat.add_comm bit r, Nat.pow_add]
  · exact h_cont r p h_p

lemma withR_spec (K c : Nat) (cont : Nat → Nat → HState) (P : HState → Prop)
    (h_cont : ∀ r p, p = 2 ^ r → P (cont r p)) :
    P (withR K c cont) := by
  unfold withR
  refine stepBSearch_spec K c 256 pow2_256 0 1 _ P rfl rfl fun r p hp => ?_
  refine stepBSearch_spec K c 128 pow2_128 r p _ P rfl hp fun r p hp => ?_
  refine stepBSearch_spec K c 64  pow2_64  r p _ P rfl hp fun r p hp => ?_
  refine stepBSearch_spec K c 32  pow2_32  r p _ P rfl hp fun r p hp => ?_
  refine stepBSearch_spec K c 16  pow2_16  r p _ P rfl hp fun r p hp => ?_
  refine stepBSearch_spec K c 8   256      r p _ P rfl hp fun r p hp => ?_
  refine stepBSearch_spec K c 4   16       r p _ P rfl hp fun r p hp => ?_
  refine stepBSearch_spec K c 2   4        r p _ P rfl hp fun r p hp => ?_
  exact stepBSearch_spec K c 1   2        r p cont P rfl hp h_cont

def stepSSearch (D limit bit powBit q pq : Nat) (cont : Nat → Nat → HState) : HState :=
  bindNat (bit + q) fun q' =>
  bindNat (pq * powBit) fun pq' =>
  bindBool (Nat.ble (D * pq') limit) fun ok =>
  bindNat (if ok then q' else q) fun q_next =>
  bindNat (if ok then pq' else pq) fun pq_next =>
  cont q_next pq_next

def withS (D limit : Nat) (cont : Nat → Nat → HState) : HState :=
  stepSSearch D limit 256 pow2_256 0 1 fun q pq =>
  stepSSearch D limit 128 pow2_128 q pq fun q pq =>
  stepSSearch D limit 64  pow2_64  q pq fun q pq =>
  stepSSearch D limit 32  pow2_32  q pq fun q pq =>
  stepSSearch D limit 16  pow2_16  q pq fun q pq =>
  stepSSearch D limit 8   256      q pq fun q pq =>
  stepSSearch D limit 4   16       q pq fun q pq =>
  stepSSearch D limit 2   4        q pq fun q pq =>
  stepSSearch D limit 1   2        q pq fun q pq =>
  bindNat (1 + q) fun s_era =>
  bindNat (2 * pq) fun ps =>
  cont s_era ps

lemma stepSSearch_spec (D limit bit powBit q pq : Nat) (cont : Nat → Nat → HState)
    (P : HState → Prop)
    (h_pow : powBit = 2 ^ bit)
    (h_pq : pq = 2 ^ q)
    (h_le : D * pq ≤ limit)
    (h_cont : ∀ q' pq', pq' = 2 ^ q' → D * pq' ≤ limit → P (cont q' pq')) :
    P (stepSSearch D limit bit powBit q pq cont) := by
  unfold stepSSearch
  simp only [bindNat_eq, bindBool_eq]
  split
  · next h_ok =>
    apply h_cont
    · rw [h_pq, h_pow, Nat.add_comm bit q, Nat.pow_add]
    · exact Nat.le_of_ble_eq_true h_ok
  · exact h_cont q pq h_pq h_le

lemma withS_spec (D limit : Nat) (cont : Nat → Nat → HState) (P : HState → Prop)
    (h_D : D ≤ limit)
    (h_cont : ∀ s_era ps, ps = 2 ^ s_era → D * ps ≤ 2 * limit → P (cont s_era ps)) :
    P (withS D limit cont) := by
  unfold withS
  have h0 : D * 1 ≤ limit := by omega
  refine stepSSearch_spec D limit 256 pow2_256 0 1 _ P rfl rfl h0 fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 128 pow2_128 q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 64  pow2_64  q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 32  pow2_32  q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 16  pow2_16  q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 8   256      q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 4   16       q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 2   4        q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  refine stepSSearch_spec D limit 1   2        q pq _ P rfl hpq hle fun q pq hpq hle => ?_
  simp only [bindNat_eq]
  apply h_cont
  · rw [hpq, Nat.add_comm 1 q, Nat.pow_succ']
  · rw [Nat.mul_left_comm D 2 pq]; omega

def stepEvenN0Cge6 (k_even c_in d : Nat) (rest : RBlocks) : HState :=
  bindNat (5 + k_even) fun n_mid =>
  bindNat (c_in - 5) fun c_mid =>
  bindNat (Nat.min n_mid (c_mid / 2)) fun m =>
  mkActive1 (2 * m) (n_mid - m) (c_mid - 2 * m) d rest

lemma stepEvenN0Cge6_sound (k_even c_in d : Nat) (rest : RBlocks)
    (hk : k_even % 2 = 0) (hc : 6 ≤ c_in) :
    ValidFrom k_even 0 (.cons c_in d rest) (stepEvenN0Cge6 k_even c_in d rest) := by
  unfold stepEvenN0Cge6
  simp only [bindNat_eq]
  have hk_eq : 2 * (k_even / 2) = k_even := by omega
  have hc_eq : (c_in - 6) + 6 = c_in := by omega
  have hc_5 : (c_in - 6) + 1 = c_in - 5 := by omega
  have h1 := rule_even_n0_cge6 (k_even / 2) (c_in - 6) d rest
  rw [hk_eq, hc_eq, hc_5] at h1
  have h2 := rule_even_nge1 (Nat.min (5 + k_even) ((c_in - 5) / 2)) 0
    ((5 + k_even) - Nat.min (5 + k_even) ((c_in - 5) / 2))
    ((c_in - 5) - 2 * Nat.min (5 + k_even) ((c_in - 5) / 2)) d rest
  rw [min_le_left_sub, min_le_right_sub, Nat.mul_zero, Nat.zero_add] at h2
  exact ValidFrom.of_reaches (h1.trans h2) (mkActive1_sound _ _ _ d rest)

def stepOddWithRDefault (c0 r p d : Nat) (rest : RBlocks) : HState :=
  bindNat ((c0 + 5 * r) - 16 * (2 * p - 2)) fun c_new =>
  bindNat (16 * p - 10) fun k_new =>
  if Nat.ble 6 c_new then
    stepEvenN0Cge6 k_new c_new d rest
  else
    mkActive1 k_new 0 c_new d rest

lemma stepOddWithRDefault_sound (c c0 r p d : Nat) (rest : RBlocks)
    (hc : c0 + 7 = c) (hp : p = 2 ^ r) (hr : 1 ≤ r)
    (h_le : 1 + 16 * (2 * p - 2) ≤ c0 + 5 * r) :
    ValidFrom 1 0 (.cons c d rest) (stepOddWithRDefault c0 r p d rest) := by
  unfold stepOddWithRDefault
  simp only [bindNat_eq]
  let c_new := (c0 + 5 * r) - 16 * (2 * p - 2)
  let k_new := 16 * p - 10
  have h_pos : 2 ≤ p := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
    omega
  have h1 : Reaches (toCfg 1 0 (.cons c d rest)) (toCfg 6 0 (.cons c0 d rest)) := by
    rw [← hc]
    exact step_k1_to_k6 c0 d rest
  have h2 := step_withR_iter r 3 c0 c_new d rest (by omega) (by rw [← hp]; omega)
  have hk_eq : 2 * ((3 + 5) * 2 ^ r - 5) = k_new := by
    change 2 * ((3 + 5) * 2 ^ r - 5) = 16 * p - 10
    rw [← hp]; omega
  rw [hk_eq] at h2
  have h12 : Reaches (toCfg 1 0 (.cons c d rest)) (toCfg k_new 0 (.cons c_new d rest)) :=
    h1.trans h2
  split
  · next hc6 =>
    have hc_ge : 6 ≤ c_new := Nat.le_of_ble_eq_true hc6
    exact ValidFrom.of_reaches h12 (stepEvenN0Cge6_sound k_new c_new d rest (by omega) hc_ge)
  · exact ValidFrom.of_reaches h12 (mkActive1_sound k_new 0 c_new d rest)

lemma rule_c1_small_c2 (k n r' m' d2' : Nat) :
    Reaches (toCfg (k + 1) n (.cons 1 ((m' + 1) + (r' + 1)) (.cons (2 * (m' + 1)) (d2' + 1) .nil)))
            (toCfg (1 + (k + 1)) n (.cons (2 * r') (2 + 2 * (m' + 1)) (.cons (2 * d2') 1 .nil))) := by
  have h := step_c1_small_c2 k n r' m' d2'
  have hk : k + 2 = 1 + (k + 1) := by omega
  rw [hk] at h
  exact h

def stepHC1 (k n d : Nat) (rest : RBlocks) : HState :=
  if Nat.ble 1 k && Nat.ble 1 d then
    match rest with
    | .nil =>
      mkActiveRaw1 (1 + k) n (2 * d) 1 .nil
    | .cons c2 d2 rest2 =>
      if Nat.ble (2 * d) (1 + c2) then
        mkActive1Drain (k + 2 * d) n ((1 + c2) - 2 * d) d2 rest2
      else
        match rest2 with
        | .nil =>
          if Nat.ble 2 c2 && Nat.beq (c2 % 2) 0 && Nat.ble 1 d2 then
            bindNat (c2 / 2) fun m =>
            bindNat (d - m) fun r =>
            if Nat.beq d2 1 then
              mkActive1 (1 + k) n (2 * r - 2) (3 + 2 * m) .nil
            else
              mkActive2 (1 + k) n (2 * r - 2) (2 + 2 * m) (2 * d2 - 2) 1 .nil
          else .active k n (.cons 1 d (.cons c2 d2 .nil))
        | .cons _ _ _ => .active k n (.cons 1 d (.cons c2 d2 rest2))
  else .active k n (.cons 1 d rest)

lemma stepHC1_sound (k n d : Nat) (rest : RBlocks) :
    ValidFrom k n (.cons 1 d rest) (stepHC1 k n d rest) := by
  unfold stepHC1
  split
  · next hkd =>
    simp only [Bool.and_eq_true, nat_ble_eq_true] at hkd
    cases rest with
    | nil =>
      simp only [mkActiveRaw1, bindNat_eq]
      have hk : (k - 1) + 1 = k := by omega
      have h_step := rule_c1_end (k - 1) n d
      rw [hk] at h_step
      exact ValidFrom.of_reaches h_step (ValidFrom.self _ _ _)
    | cons c2 d2 rest2 =>
      dsimp only []
      split
      · next h_large =>
        simp only [nat_ble_eq_true] at h_large
        have hd : (d - 1) + 1 = d := by omega
        have hc2 : 2 * d + ((1 + c2) - 2 * d) - 1 = c2 := by omega
        have h_step := rule_c1_large_c2 k n (d - 1) ((1 + c2) - 2 * d) d2 rest2
        rw [hd, hc2] at h_step
        exact ValidFrom.of_reaches h_step (mkActive1Drain_sound (k + 2 * d) n ((1 + c2) - 2 * d) d2 rest2)
      · next h_small =>
        simp only [nat_ble_eq_true] at h_small
        cases rest2 with
        | cons _ _ _ =>
          dsimp only []
          exact ValidFrom.self _ _ _
        | nil =>
          dsimp only []
          split
          · next h_cond =>
            simp only [Bool.and_eq_true, nat_ble_eq_true, nat_beq_eq_true] at h_cond
            simp only [bindNat_eq]
            let m := c2 / 2
            let r := d - m
            have hk : (k - 1) + 1 = k := by omega
            have hm : 2 * ((m - 1) + 1) = c2 := by omega
            have hd_eq : ((m - 1) + 1) + ((r - 1) + 1) = d := by omega
            have hd2_eq : (d2 - 1) + 1 = d2 := by omega
            have hr_out : 2 * (r - 1) = 2 * r - 2 := by omega
            have hm_out : 2 + 2 * ((m - 1) + 1) = 2 + 2 * m := by omega
            have hd2_out : 2 * (d2 - 1) = 2 * d2 - 2 := by omega
            have h_step := rule_c1_small_c2 (k - 1) n (r - 1) (m - 1) (d2 - 1)
            rw [hk, hm_out, hm, hd_eq, hd2_eq, hr_out, hd2_out] at h_step
            split
            · next hd2_1 =>
              simp only [nat_beq_eq_true] at hd2_1
              have hd2_z : 2 * d2 - 2 = 0 := by omega
              have hm3 : 2 + 2 * m + 1 = 3 + 2 * m := by omega
              rw [hd2_z, toCfg_cons_zero, hm3] at h_step
              exact ValidFrom.of_reaches h_step (mkActive1_sound (1 + k) n (2 * r - 2) (3 + 2 * m) .nil)
            · exact ValidFrom.of_reaches h_step (mkActive2_sound (1 + k) n (2 * r - 2) (2 + 2 * m) (2 * d2 - 2) 1 .nil)
          · exact ValidFrom.self _ _ _
  · exact ValidFrom.self _ _ _

def stepHEvenSmall (k c d : Nat) (rest : RBlocks) : HState :=
  bindNat (k / 2) fun j =>
  if Nat.beq c 2 then
    match rest with
    | .nil =>
      if Nat.beq (d % 2) 1 then
        mkActiveRest0 (3 + (2 * j + d)) 0
      else .active k 0 (.cons c d .nil)
    | .cons c2 d2 rest2 => .active k 0 (.cons c d (.cons c2 d2 rest2))
  else if Nat.beq c 3 then
    match rest with
    | .nil => .active k 0 (.cons c d .nil)
    | .cons c2 d2 .nil =>
      if Nat.ble 2 c2 && Nat.ble (4 + c2) (2 * d) && Nat.beq (c2 % 2) 0 && Nat.beq d2 1 then
        .halted
      else .active k 0 (.cons c d (.cons c2 d2 .nil))
    | .cons c2 d2 (.cons c3 d3 rest3) => .active k 0 (.cons c d (.cons c2 d2 (.cons c3 d3 rest3)))
  else if Nat.beq c 4 then
    mkActiveRest (3 + (2 * j + d)) 0 rest
  else if Nat.ble 6 c then
    stepEvenN0Cge6 k c d rest
  else .active k 0 (.cons c d rest)

lemma stepHEvenSmall_sound (k c d : Nat) (rest : RBlocks) (hk_mod : k % 2 = 0) :
    ValidFrom k 0 (.cons c d rest) (stepHEvenSmall k c d rest) := by
  unfold stepHEvenSmall
  simp only [bindNat_eq]
  split
  · next hc2 =>
    simp only [nat_beq_eq_true] at hc2
    cases rest with
    | cons _ _ _ =>
      dsimp only []
      exact ValidFrom.self _ _ _
    | nil =>
      dsimp only []
      split
      · next hd_odd =>
        simp only [nat_beq_eq_true] at hd_odd
        have hk_eq : 2 * (k / 2) = k := by omega
        have hd_eq : 2 * ((d - 1) / 2) + 1 = d := by omega
        have h_out : 3 + k + d = 3 + (2 * (k / 2) + d) := by omega
        have h_step := rule_even_n0_c2 (k / 2) ((d - 1) / 2)
        rw [hk_eq, hd_eq, h_out] at h_step
        rw [hc2]
        exact ValidFrom.of_reaches h_step (mkActiveRest0_sound (3 + (2 * (k / 2) + d)) 0)
      · exact ValidFrom.self _ _ _
  · next hnc2 =>
    split
    · next hc3 =>
      simp only [nat_beq_eq_true] at hc3
      cases rest with
      | nil =>
        dsimp only []
        exact ValidFrom.self _ _ _
      | cons c2 d2 rest2 =>
        cases rest2 with
        | cons _ _ _ =>
          dsimp only []
          exact ValidFrom.self _ _ _
        | nil =>
          dsimp only []
          split
          · next h_halt =>
            simp only [Bool.and_eq_true, nat_ble_eq_true, nat_beq_eq_true] at h_halt
            have hk_eq : 2 * (k / 2) = k := by omega
            have hm_eq : 2 * ((c2 / 2 - 1) + 1) = c2 := by omega
            have hd_eq : ((c2 / 2 - 1) + 1) + ((d - c2 / 2 - 2) + 2) = d := by omega
            have hd2_eq : d2 = 1 := h_halt.2
            have h_step := rule_halt_c3 (k / 2) (d - c2 / 2 - 2) (c2 / 2 - 1)
            rw [hk_eq, hm_eq, hd_eq, ← hc3, ← hd2_eq] at h_step
            exact ValidFrom.halted h_step
          · exact ValidFrom.self _ _ _
    · next hnc3 =>
      split
      · next hc4 =>
        simp only [nat_beq_eq_true] at hc4
        have hk_eq : 2 * (k / 2) = k := by omega
        have h_out : 3 + k + d = 3 + (2 * (k / 2) + d) := by omega
        have h_step := rule_even_n0_c4 (k / 2) d rest
        rw [hk_eq, h_out] at h_step
        rw [hc4]
        exact ValidFrom.of_reaches h_step (mkActiveRest_sound (3 + (2 * (k / 2) + d)) 0 rest)
      · next hnc4 =>
        split
        · next hc6 =>
          simp only [nat_ble_eq_true] at hc6
          exact stepEvenN0Cge6_sound k c d rest hk_mod hc6
        · exact ValidFrom.self _ _ _

def stepHEven (k n c d : Nat) (rest : RBlocks) : HState :=
  if Nat.beq n 0 then
    if Nat.ble (16 + 2 * k) c then
      bindNat (10 + k) fun K =>
      withR K c fun r p =>
      if Nat.ble 1 r && Nat.ble (1 + K * (2 * p - 2)) (c + 5 * r) then
        bindNat ((c + 5 * r) - K * (2 * p - 2)) fun c_new =>
        bindNat (K * p - 10) fun k_new =>
        if Nat.ble 6 c_new then
          stepEvenN0Cge6 k_new c_new d rest
        else
          mkActive1 k_new 0 c_new d rest
      else .active k 0 (.cons c d rest)
    else
      stepHEvenSmall k c d rest
  else
    bindNat (Nat.min n (c / 2)) fun m =>
    mkActive1 (k + 2 * m) (n - m) (c - 2 * m) d rest

lemma stepHEven_sound (k n c d : Nat) (rest : RBlocks) (hk_mod : k % 2 = 0) :
    ValidFrom k n (.cons c d rest) (stepHEven k n c d rest) := by
  unfold stepHEven
  split
  · next hn0 =>
    simp only [nat_beq_eq_true] at hn0
    rw [hn0]
    split
    · next h_withR =>
      simp only [bindNat_eq]
      refine withR_spec (10 + k) c _ (ValidFrom k 0 (.cons c d rest)) fun r p hp => ?_
      split
      · next h_ok =>
        simp only [Bool.and_eq_true, nat_ble_eq_true] at h_ok
        let c_new := (c + 5 * r) - (10 + k) * (2 * p - 2)
        let k_new := (10 + k) * p - 10
        have h_pos : 2 ≤ p := by
          have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h_ok.1
          omega
        have hk_eq : 2 * (k / 2) = k := by omega
        have hK : 2 * (k / 2 + 5) = 10 + k := by omega
        have h_mul1 : 4 * (k / 2 + 5) * (p - 1) = (10 + k) * (2 * p - 2) := by
          have h1 : 4 * (k / 2 + 5) = (10 + k) * 2 := by omega
          have h2 : 2 * (p - 1) = 2 * p - 2 := by omega
          rw [h1, Nat.mul_assoc, h2]
        have h_mul2 : 2 * ((k / 2 + 5) * p) = (10 + k) * p := by
          rw [← Nat.mul_assoc, hK]
        have h_step := step_withR_iter r (k / 2) c c_new d rest (by omega) (by rw [← hp, h_mul1]; omega)
        have hk_out : 2 * ((k / 2 + 5) * 2 ^ r - 5) = k_new := by
          change 2 * ((k / 2 + 5) * 2 ^ r - 5) = (10 + k) * p - 10
          rw [← hp]; omega
        rw [hk_eq, hk_out] at h_step
        split
        · next hc6 =>
          simp only [nat_ble_eq_true] at hc6
          exact ValidFrom.of_reaches h_step (stepEvenN0Cge6_sound k_new c_new d rest (by omega) hc6)
        · exact ValidFrom.of_reaches h_step (mkActive1_sound k_new 0 c_new d rest)
      · exact ValidFrom.self _ _ _
    · exact stepHEvenSmall_sound k c d rest hk_mod
  · next hn_pos =>
    simp only [nat_beq_eq_true] at hn_pos
    simp only [bindNat_eq]
    have hk_eq : 2 * (k / 2) = k := by omega
    have h_step := rule_even_nge1 (Nat.min n (c / 2)) (k / 2) (n - Nat.min n (c / 2)) (c - 2 * Nat.min n (c / 2)) d rest
    rw [hk_eq, min_le_left_sub, min_le_right_sub] at h_step
    exact ValidFrom.of_reaches h_step (mkActive1_sound _ _ _ d rest)

def stepHOddK1 (c d : Nat) (rest : RBlocks) : HState :=
  bindNat (c - 7) fun c0 =>
  if Nat.ble 28 c0 then
    withR 16 c0 fun r p =>
    if Nat.ble 1 r && Nat.ble (1 + 16 * (2 * p - 2)) (c0 + 5 * r) then
      match rest with
      | .nil =>
        if Nat.beq d 1 && Nat.ble 3 r && Nat.beq (r % 2) 1 && Nat.beq (c % 2) 0 &&
           Nat.ble (8 + 32 * p) (25 + (c + 5 * r)) && Nat.ble (66 + (c + 5 * r)) (64 * p) then
          bindNat (64 * p - (31 + (c + 5 * r))) fun c_prime =>
          bindNat (c_prime - 7) fun c_prime0 =>
          withR 16 c_prime0 fun r2 p2 =>
          if Nat.ble 2 r2 && Nat.beq (r2 % 2) 0 &&
             Nat.ble (1 + 16 * (2 * p2 - 2)) (c_prime0 + 5 * r2) &&
             Nat.ble (30 + (c_prime + 5 * r2)) (64 * p2) &&
             Nat.ble (26 + 5 * r2) (32 * p2) &&
             Nat.ble (1 + 64 * p) (34 + (c + (64 * p2 + 10 * r))) then
            bindNat ((34 + (c + (64 * p2 + 10 * r))) - 64 * p) fun D =>
            if Nat.ble (32 * p2) (18 + (c_prime + (D + 5 * r2))) then
              bindNat ((18 + (c_prime + (D + 5 * r2))) - 32 * p2) fun limit =>
              if Nat.ble D limit then
                withS D limit fun _ ps =>
                mkActiveRaw1 1 0 (c + D * (ps - 1)) 1 .nil
              else
                stepOddWithRDefault c0 r p d .nil
            else
              stepOddWithRDefault c0 r p d .nil
          else
            stepOddWithRDefault c0 r p d .nil
        else
          stepOddWithRDefault c0 r p d .nil
      | .cons c2 d2 rest2 =>
        stepOddWithRDefault c0 r p d (.cons c2 d2 rest2)
    else .active 1 0 (.cons c d rest)
  else if Nat.ble 6 c0 then
    stepEvenN0Cge6 6 c0 d rest
  else
    mkActive1 6 0 c0 d rest

lemma stepHOddK1_sound (c d : Nat) (rest : RBlocks) (hc_ge : 7 ≤ c) :
    ValidFrom 1 0 (.cons c d rest) (stepHOddK1 c d rest) := by
  unfold stepHOddK1
  simp only [bindNat_eq]
  have hc0_eq : (c - 7) + 7 = c := by omega
  split
  · next hc0_28 =>
    refine withR_spec 16 (c - 7) _ (ValidFrom 1 0 (.cons c d rest)) fun r p hp => ?_
    split
    · next h_r_ok =>
      simp only [Bool.and_eq_true, nat_ble_eq_true] at h_r_ok
      cases rest with
      | cons c2 d2 rest2 =>
        dsimp only []
        exact stepOddWithRDefault_sound c (c - 7) r p d (.cons c2 d2 rest2) hc0_eq hp h_r_ok.1 h_r_ok.2
      | nil =>
        dsimp only []
        split
        · next h_era1 =>
          simp only [Bool.and_eq_true, nat_beq_eq_true, nat_ble_eq_true] at h_era1
          let c_prime := 64 * p - (31 + (c + 5 * r))
          refine withR_spec 16 (c_prime - 7) _ (ValidFrom 1 0 (.cons c d .nil)) fun r2 p2 hp2 => ?_
          split
          · next h_era2 =>
            simp only [Bool.and_eq_true, nat_beq_eq_true, nat_ble_eq_true] at h_era2
            let D := (34 + (c + (64 * p2 + 10 * r))) - 64 * p
            split
            · next h_era3 =>
              simp only [nat_ble_eq_true] at h_era3
              let limit := (18 + (c_prime + (D + 5 * r2))) - 32 * p2
              split
              · next h_D_lim =>
                simp only [nat_ble_eq_true] at h_D_lim
                refine withS_spec D limit _ (ValidFrom 1 0 (.cons c d .nil)) h_D_lim fun s_era ps hps h_ps_le => ?_
                unfold mkActiveRaw1; simp only [bindNat_eq]
                let jc := c / 2
                let jr := (r - 1) / 2
                let jr2 := r2 / 2
                let D_half := D / 2
                have hjc : jc = c / 2 := rfl
                have hjr : jr = (r - 1) / 2 := rfl
                have hjr2 : jr2 = r2 / 2 := rfl
                have hc_prime_def : c_prime = 64 * p - (31 + (c + 5 * r)) := rfl
                have hD_def : D = (34 + (c + (64 * p2 + 10 * r))) - 64 * p := rfl
                have hlim_def : limit = (18 + (c_prime + (D + 5 * r2))) - 32 * p2 := rfl
                have hD_half_def : D_half = D / 2 := rfl
                have hd1 : d = 1 := h_era1.1.1.1.1.1
                have hc_even : 2 * jc = c := by omega
                have hr_odd : 2 * jr + 1 = r := by omega
                have hr2_even : 2 * jr2 = r2 := by omega
                have hp_jr : p = 2 ^ (2 * jr + 1) := by rw [hr_odd, hp]
                have hp2_jr2 : p2 = 2 ^ (2 * jr2) := by rw [hr2_even, hp2]
                have h_D_even : 2 * D_half = 44 + 2 * jc + 64 * p2 + 20 * jr - 64 * p := by omega
                have h_2D : 2 * D_half = D := by omega
                have h_step := step_outer_era_iter s_era jc jr p jr2 p2 D_half limit
                  hp_jr hp2_jr2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  h_D_even (by omega) (by omega) (by omega)
                  (by
                    rw [h_2D, ← hps]
                    exact h_ps_le)
                have h_out : c + 2 * D_half * (2 ^ s_era - 1) = c + D * (ps - 1) := by
                  rw [h_2D, ← hps]
                rw [hc_even, h_out] at h_step
                rw [hd1]
                exact ValidFrom.of_reaches h_step (ValidFrom.self _ _ _)
              · exact stepOddWithRDefault_sound c (c - 7) r p d .nil hc0_eq hp h_r_ok.1 h_r_ok.2
            · exact stepOddWithRDefault_sound c (c - 7) r p d .nil hc0_eq hp h_r_ok.1 h_r_ok.2
          · exact stepOddWithRDefault_sound c (c - 7) r p d .nil hc0_eq hp h_r_ok.1 h_r_ok.2
        · exact stepOddWithRDefault_sound c (c - 7) r p d .nil hc0_eq hp h_r_ok.1 h_r_ok.2
    · exact ValidFrom.self _ _ _
  · next hc0_lt28 =>
    split
    · next hc0_6 =>
      simp only [nat_ble_eq_true] at hc0_6
      have h1 : Reaches (toCfg 1 0 (.cons c d rest)) (toCfg 6 0 (.cons (c - 7) d rest)) := by
        rw [← hc0_eq]
        exact step_k1_to_k6 (c - 7) d rest
      exact ValidFrom.of_reaches h1 (stepEvenN0Cge6_sound 6 (c - 7) d rest rfl hc0_6)
    · next hc0_lt6 =>
      have h1 : Reaches (toCfg 1 0 (.cons c d rest)) (toCfg 6 0 (.cons (c - 7) d rest)) := by
        rw [← hc0_eq]
        exact step_k1_to_k6 (c - 7) d rest
      exact ValidFrom.of_reaches h1 (mkActive1_sound 6 0 (c - 7) d rest)

def stepHOdd (k n c d : Nat) (rest : RBlocks) : HState :=
  bindNat ((k - 1) / 2) fun j =>
  if Nat.beq n 0 then
    if Nat.beq k 1 && Nat.ble 7 c then
      stepHOddK1 c d rest
    else if Nat.beq c 2 then .active k 0 (.cons c d rest)
    else if Nat.ble 2 c then
      mkActive1 0 (3 + 2 * j) (c - 1) d rest
    else .active k 0 (.cons c d rest)
  else
    if Nat.beq c 2 then
      mkActive1 1 0 (2 * n - 2) (2 + (2 * j + d)) rest
    else if Nat.ble 3 c then
      mkActive2 1 0 (2 * n - 2) (2 + 2 * j) (c - 2) d rest
    else .active k n (.cons c d rest)

lemma stepHOdd_sound (k n c d : Nat) (rest : RBlocks) (hk_odd : ¬ k % 2 = 0) :
    ValidFrom k n (.cons c d rest) (stepHOdd k n c d rest) := by
  unfold stepHOdd
  simp only [bindNat_eq]
  have hk_eq : 2 * ((k - 1) / 2) + 1 = k := by omega
  split
  · next hn0 =>
    simp only [nat_beq_eq_true] at hn0
    rw [hn0]
    split
    · next hk1_c7 =>
      simp only [Bool.and_eq_true, nat_beq_eq_true, nat_ble_eq_true] at hk1_c7
      rw [hk1_c7.1]
      exact stepHOddK1_sound c d rest hk1_c7.2
    · next h_not_k1_c7 =>
      split
      · exact ValidFrom.self _ _ _
      · split
        · next hc2_ge =>
          simp only [nat_ble_eq_true] at hc2_ge
          have hc_in : (c - 2) + 2 = c := by omega
          have hc_out : (c - 2) + 1 = c - 1 := by omega
          have h_step := rule_odd_n0 ((k - 1) / 2) (c - 2) d rest
          rw [hk_eq, hc_in, hc_out] at h_step
          exact ValidFrom.of_reaches h_step (mkActive1_sound 0 (3 + 2 * ((k - 1) / 2)) (c - 1) d rest)
        · exact ValidFrom.self _ _ _
  · next hn_pos =>
    simp only [nat_beq_eq_true] at hn_pos
    have hn_eq : (n - 1) + 1 = n := by omega
    have hn_out : 2 * (n - 1) = 2 * n - 2 := by omega
    split
    · next hc2 =>
      simp only [nat_beq_eq_true] at hc2
      have h_step := rule_odd_nge1 ((k - 1) / 2) (n - 1) 0 d rest
      have hd_out : 2 + 2 * ((k - 1) / 2) + d = 2 + (2 * ((k - 1) / 2) + d) := by omega
      rw [hk_eq, hn_eq, hn_out, toCfg_cons_zero, hd_out] at h_step
      rw [hc2]
      exact ValidFrom.of_reaches h_step (mkActive1_sound 1 0 (2 * n - 2) (2 + (2 * ((k - 1) / 2) + d)) rest)
    · next hnc2 =>
      split
      · next hc3 =>
        simp only [nat_ble_eq_true] at hc3
        have hc_eq : (c - 2) + 2 = c := by omega
        have h_step := rule_odd_nge1 ((k - 1) / 2) (n - 1) (c - 2) d rest
        rw [hk_eq, hn_eq, hn_out, hc_eq] at h_step
        exact ValidFrom.of_reaches h_step (mkActive2_sound 1 0 (2 * n - 2) (2 + 2 * ((k - 1) / 2)) (c - 2) d rest)
      · exact ValidFrom.self _ _ _

def stepH (s : HState) : HState :=
  match s with
  | .halted => .halted
  | .active k n blks =>
    match blks with
    | .nil => mkActiveRest0 k n
    | .cons c d rest =>
      if Nat.beq c 0 then
        mkActiveRest (k + d) n rest
      else if Nat.beq c 1 then
        stepHC1 k n d rest
      else if Nat.beq (k % 2) 0 then
        stepHEven k n c d rest
      else
        stepHOdd k n c d rest

lemma stepH_sound_aux (k n : Nat) (blks : RBlocks) :
    ValidFrom k n blks (stepH (.active k n blks)) := by
  cases blks with
  | nil =>
    dsimp only [stepH]
    exact mkActiveRest0_sound k n
  | cons c d rest =>
    dsimp only [stepH]
    split
    · next hc0 =>
      simp only [nat_beq_eq_true] at hc0
      rw [hc0]
      exact ValidFrom.of_reaches (rule_c0 k n d rest) (mkActiveRest_sound (k + d) n rest)
    · next hnc0 =>
      split
      · next hc1 =>
        simp only [nat_beq_eq_true] at hc1
        rw [hc1]
        exact stepHC1_sound k n d rest
      · next hnc1 =>
        split
        · next hk_even =>
          simp only [nat_beq_eq_true] at hk_even
          exact stepHEven_sound k n c d rest hk_even
        · next hk_odd =>
          simp only [nat_beq_eq_true] at hk_odd
          exact stepHOdd_sound k n c d rest hk_odd

lemma stepH_sound (s : HState) : ValidState (stepH s) → ValidState s := by
  cases s with
  | halted => exact id
  | active k n blks => exact ValidState.of_validFrom (stepH_sound_aux k n blks)

def runPow : Nat → HState → HState
  | 0, s => stepH s
  | k + 1, s => bindState (runPow k s) (runPow k)

lemma bindState_sound (s : HState) (f : HState → HState)
    (hf : ∀ x, ValidState (f x) → ValidState x) :
    ValidState (bindState s f) → ValidState s := by
  cases s with
  | halted => exact id
  | active k n blks => exact hf (.active k n blks)

lemma runPow_sound (k : Nat) : ∀ s, ValidState (runPow k s) → ValidState s := by
  induction k with
  | zero => exact stepH_sound
  | succ k ih =>
    intro s hs
    exact ih s (bindState_sound (runPow k s) (runPow k) ih hs)

def s0 : HState := HState.active 1 0 (RBlocks.cons 16 1 RBlocks.nil)

lemma reach_init_s0 : Reaches (init []) (toCfg 1 0 (.cons 16 1 .nil)) := by
  have h1 : Reaches (init []) (toCfg 0 0 .nil) := by
    unfold toCfg; rw [evalRBlocks_nil, L11_zero, L01_zero]; exec_tm 12
  refine h1.trans ?_
  refine (rule_nil_even_n0 0).trans ?_
  refine (show Reaches (toCfg (2 * 0 + 1) 0 (.cons (2 + 2) 1 .nil)) _ from
    rule_odd_n0 0 2 1 .nil).trans ?_
  refine (show Reaches (toCfg (2 * 0) (1 + 2) (.cons (2 * 1 + 1) 1 .nil)) _ from
    rule_even_nge1 1 0 2 1 1 .nil).trans ?_
  have h5 := step_mk10_c1 1 1 1 (by decide) (by decide)
  rw [show 2 * 1 - 2 = 0 from rfl, toCfg_cons_zero] at h5
  refine (show Reaches (toCfg 2 2 (.cons 1 1 .nil)) _ from h5).trans ?_
  refine (show Reaches (toCfg (2 * 0 + 1) 0 (.cons (0 + 2) 5 .nil)) _ from
    rule_odd_n0 0 0 5 .nil).trans ?_
  have h7 : Reaches (toCfg 0 3 (.cons 1 5 .nil)) (cfg A (L11 5 (L11 3 L0)) (b1 >> lb0)) := by
    unfold toCfg
    rw [evalRBlocks_cons, evalRBlocks_nil, R1_succ, R1_zero, L01_zero]
    exact shift_A_1_01 5 (L11 3 L0) default
  refine h7.trans ?_
  rw [← L11_add]
  have h8 : Reaches (cfg A (L11 8 L0) (b1 >> lb0)) (toCfg (2 * 0) (7 + 2) .nil) := by
    unfold toCfg
    rw [evalRBlocks_nil, L01_zero]
    exec_tm 2
  refine h8.trans ?_
  exact rule_nil_even_nge2 0 7

lemma holdout_halt_of_runPow (h_halt : runPow 13 s0 = HState.halted) : IsHalt target_tm := by
  have h_valid : ValidState (runPow 13 s0) := by
    rw [h_halt]; exact ValidState.halted
  have h_s0_valid : ValidState s0 :=
    runPow_sound 13 s0 h_valid
  have h_s0 : ReachHalt (toCfg 1 0 (.cons 16 1 .nil)) := by
    cases h_s0_valid with | active h => exact h
  exact ReachHalt.to_isHalt (reach_init_s0 h_s0)

set_option maxHeartbeats 10000000 in
theorem reaches_halt : runPow 13 s0 = HState.halted := by decide +kernel

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := holdout_halt_of_runPow reaches_halt

end BusyBeaver.M_1RB1RF_1LC0RA_HHH0LD_1RE1LD_0LF0LB_1RA1LE
