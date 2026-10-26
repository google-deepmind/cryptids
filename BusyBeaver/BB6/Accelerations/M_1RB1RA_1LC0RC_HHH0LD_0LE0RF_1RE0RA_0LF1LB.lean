/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB`
(https://wiki.bbchallenge.org/wiki/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB).
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Local Step Tactics and Pair-Stack Encodings -/

private theorem mod3_cases (b : ℕ) : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
  omega

private theorem ones_append_cons_one (n : ℕ) (T : ListBlank (Fin 2)) :
    (([1] : List (Fin 2)) ^ n) +> ((1 : Fin 2) >> T) =
      (1 : Fin 2) >> ((([1] : List (Fin 2)) ^ n) +> T) :=
  ListBlank.append_pow_comm ([1] : List (Fin 2)) n T

local macro "normalize" : tactic => `(tactic| (
  try simp only [ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, ones_append_cons_one, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "normalize_at" h:ident : tactic => `(tactic| (
  try simp only [ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, ones_append_cons_one, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one] at $h:ident))

private def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L => (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 1))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1))

private def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R => (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 3)) +>
      encRight R)

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl
@[simp] private theorem encLeft_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = (encLeft L <+ (([0] : List (Fin 2)) ^ (1 + b % 1))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1)) := rfl
@[simp] private theorem encRight_nil : encRight [] = default := rfl
@[simp] private theorem encRight_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((d, b) :: R) = (([1] : List (Fin 2)) ^ (1 * d + 1)) +>
      ((([0] : List (Fin 2)) ^ (1 + b % 3)) +> encRight R) := rfl

private theorem encLeft_mod1 (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, b) :: L) = encLeft ((a, b % 1) :: L) := by
  simp only [encLeft_cons, Nat.mod_mod]

private theorem encLeft_succ (a b : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a + 1, b) :: L) = (1 : Fin 2) >> encLeft ((a, b) :: L) := by
  simp only [encLeft_cons]
  rw [show 1 * (a + 1) + 1 = 1 + (1 * a + 1) by omega, list_pow_add, ListBlank.append_assoc]
  rfl

private theorem encLeft_d0_s0 (L : List (ℕ × ℕ)) :
    encLeft ((0, 0) :: L) = (1 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_d1_s0 (L : List (ℕ × ℕ)) :
    encLeft ((1, 0) :: L) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft L := rfl

private theorem encLeft_run_s0 (a : ℕ) (L : List (ℕ × ℕ)) :
    encLeft ((a, 0) :: L) = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >>
      encLeft L) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encLeft_succ, ih]; normalize

private theorem encRight_mod3 (a b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, b) :: R) = encRight ((a, b % 3) :: R) := by
  simp only [encRight_cons, Nat.mod_mod]

private theorem encRight_succ (a b : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a + 1, b) :: R) = (1 : Fin 2) >> encRight ((a, b) :: R) := by
  simp only [encRight_cons]
  rw [show 1 * (a + 1) + 1 = 1 + (1 * a + 1) by omega, list_pow_add, ListBlank.append_assoc]
  rfl

private theorem encRight_d0_s0 (R : List (ℕ × ℕ)) :
    encRight ((0, 0) :: R) = (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d0_s1 (R : List (ℕ × ℕ)) :
    encRight ((0, 1) :: R) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d0_s2 (R : List (ℕ × ℕ)) :
    encRight ((0, 2) :: R) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      encRight R := rfl

private theorem encRight_d1_s0 (R : List (ℕ × ℕ)) :
    encRight ((1, 0) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d1_s1 (R : List (ℕ × ℕ)) :
    encRight ((1, 1) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      encRight R := rfl

private theorem encRight_d1_s2 (R : List (ℕ × ℕ)) :
    encRight ((1, 2) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d2_s0 (R : List (ℕ × ℕ)) :
    encRight ((2, 0) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      encRight R := rfl

private theorem encRight_d2_s1 (R : List (ℕ × ℕ)) :
    encRight ((2, 1) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d2_s2 (R : List (ℕ × ℕ)) :
    encRight ((2, 2) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d3_s0 (R : List (ℕ × ℕ)) :
    encRight ((3, 0) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d3_s1 (R : List (ℕ × ℕ)) :
    encRight ((3, 1) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d3_s2 (R : List (ℕ × ℕ)) :
    encRight ((3, 2) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d4_s0 (R : List (ℕ × ℕ)) :
    encRight ((4, 0) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d4_s1 (R : List (ℕ × ℕ)) :
    encRight ((4, 1) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_d4_s2 (R : List (ℕ × ℕ)) :
    encRight ((4, 2) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R := rfl

private theorem encRight_run_s0 (a : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, 0) :: R) = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >>
      encRight R) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encRight_succ, ih]; normalize

private theorem encRight_run_s1 (a : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, 1) :: R) = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >>
      (0 : Fin 2) >> encRight R) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encRight_succ, ih]; normalize

private theorem encRight_run_s2 (a : ℕ) (R : List (ℕ × ℕ)) :
    encRight ((a, 2) :: R) = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> encRight R) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encRight_succ, ih]; normalize

@[simp] private theorem encLeft_cons_one (L : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encLeft L = encLeft (bumpPairHead L) := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · simp [bumpPairHead, encLeft]
  · exact (encLeft_succ a b L').symm

@[simp] private theorem encRight_cons_one (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encRight R = encRight (bumpPairHead R) := by
  rcases R with _ | ⟨⟨a, b⟩, R'⟩
  · simp [bumpPairHead, encRight]
  · exact (encRight_succ a b R').symm




local macro "walk" t:term : tactic => `(tactic| (
  (first | refine ReachesStar.trans $t ?_ | refine ReachesStar.trans_plus $t ?_)
  try simp only [Cfg.headRight, Cfg.headLeft, encLeft_nil, encRight_nil,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    ones_append_cons_one, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "step" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encLeft_nil, encRight_nil, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, ones_append_cons_one, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  refine ReachesPlus.head (by rfl) ?_
  simp only [Tape.move, Tape.write, encLeft_nil, encRight_nil,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    ones_append_cons_one, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encLeft_nil, encRight_nil, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, ones_append_cons_one, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  simp only [encLeft_cons_one, encRight_cons_one, multiStep_zero]
  try rfl))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

/-! ## Stack Modes and Walk Helpers -/

private def cfg_EB_n_00 (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encLeft L, [0, 0] +> encRight R⟩⟩

private def cfg_EL_n_00 (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) <{{E}} ([0, 0] +> encRight R)

private inductive StackMode
  | EB_n_00
  | EL_n_00
deriving DecidableEq

private def evalStackCfg : StackMode → List (ℕ × ℕ) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .EB_n_00, L, R => cfg_EB_n_00 L R
  | .EL_n_00, L, R => cfg_EL_n_00 L R

private def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

/-! ## Uniform Walk Theorem -/

private theorem cyc_R_A_1_11_11_1 (n : ℕ) : ∀ (T S : ListBlank (Fin 2)),
    (⟨some A, ⟨1, T, (([1] : List (Fin 2)) ^ n) +> S⟩⟩ : Cfg (Fin 2) (Fin 6)) [target]⊢*
      ⟨some A, ⟨1, (([1] : List (Fin 2)) ^ n) +> T, S⟩⟩ := by
  induction n with
  | zero =>
    intro T S
    normalize
    finish
  | succ j ih =>
    intro T S
    have h := ih ((1 : Fin 2) >> T) S
    normalize_at h
    normalize
    iterate 1 step
    exact h


/-! ## Mode Closure Theorems -/

private theorem mode_EB_sep0_d0 (b2 : ℕ) (hb4_0 : b2 % 3 = 0) (L R3 : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EB_n_00 L ((0, b2) :: R3)) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases R3 with _ | ⟨⟨a9, b10⟩, R11⟩
  · refine ⟨cfg_EL_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) [(0, 0)], ?_,
      Or.inl ⟨.EL_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), [(0, 0)], rfl⟩⟩
    unfold cfg_EB_n_00 cfg_EL_n_00
    rw [encRight_mod3 0 b2 [], hb4_0, encRight_d0_s0 [],
      ← encLeft_cons_one (bumpPairHead (bumpPairHead L)), ← encLeft_cons_one (bumpPairHead L),
      ← encLeft_cons_one L]
    iterate 8 step
    finish
  · rcases mod3_cases b10 with hb12_0 | hb12_1 | hb12_2
    · rcases a9 with _ | a16
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> encLeft L, encRight R11⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 0 b2 (((0), b10) :: R11), hb4_0, encRight_d0_s0 (((0), b10) :: R11),
          encRight_mod3 0 b10 R11, hb12_0, encRight_d0_s0 R11]
        iterate 6 step
        finish
      · rcases a16 with _ | a17
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) ((0, 0) :: R11), ?_,
            Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 0) :: R11, rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 0 b2 ((((0) + 1), b10) :: R11), hb4_0,
            encRight_d0_s0 ((((0) + 1), b10) :: R11), encRight_mod3 ((0) + 1) b10 R11, hb12_0,
            encRight_d1_s0 R11, ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s0 R11]
          iterate 13 step
          finish
        · refine ⟨cfg_EL_n_00 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a17,
            0) :: R11), ?_, Or.inl ⟨.EL_n_00, (0,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (a17, 0) :: R11, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 0 b2 ((((a17 + 1) + 1), b10) :: R11), hb4_0,
            encRight_d0_s0 ((((a17 + 1) + 1), b10) :: R11), encRight_mod3 ((a17 + 1) + 1) b10 R11,
            hb12_0, encRight_succ (a17 + 1) 0 R11, encRight_succ a17 0 R11,
            encRight_run_s0 a17 R11, encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 8 step
          finish
    · rcases a9 with _ | a18
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> encLeft L, (0 : Fin 2) >> encRight R11⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 0 b2 (((0), b10) :: R11), hb4_0, encRight_d0_s0 (((0), b10) :: R11),
          encRight_mod3 0 b10 R11, hb12_1, encRight_d0_s1 R11]
        iterate 6 step
        finish
      · rcases a18 with _ | a19
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) ((0, 1) :: R11), ?_,
            Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 1) :: R11, rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 0 b2 ((((0) + 1), b10) :: R11), hb4_0,
            encRight_d0_s0 ((((0) + 1), b10) :: R11), encRight_mod3 ((0) + 1) b10 R11, hb12_1,
            encRight_d1_s1 R11, ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s1 R11]
          iterate 13 step
          finish
        · refine ⟨cfg_EL_n_00 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a19,
            1) :: R11), ?_, Or.inl ⟨.EL_n_00, (0,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (a19, 1) :: R11, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 0 b2 ((((a19 + 1) + 1), b10) :: R11), hb4_0,
            encRight_d0_s0 ((((a19 + 1) + 1), b10) :: R11), encRight_mod3 ((a19 + 1) + 1) b10 R11,
            hb12_1, encRight_succ (a19 + 1) 1 R11, encRight_succ a19 1 R11,
            encRight_run_s1 a19 R11, encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 8 step
          finish
    · rcases a9 with _ | a20
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> encLeft L, (0 : Fin 2) >> (0 : Fin 2) >> encRight R11⟩⟩, ?_,
            Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 0 b2 (((0), b10) :: R11), hb4_0, encRight_d0_s0 (((0), b10) :: R11),
          encRight_mod3 0 b10 R11, hb12_2, encRight_d0_s2 R11]
        iterate 6 step
        finish
      · rcases a20 with _ | a21
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) ((0, 2) :: R11), ?_,
            Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 2) :: R11, rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 0 b2 ((((0) + 1), b10) :: R11), hb4_0,
            encRight_d0_s0 ((((0) + 1), b10) :: R11), encRight_mod3 ((0) + 1) b10 R11, hb12_2,
            encRight_d1_s2 R11, ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s2 R11]
          iterate 13 step
          finish
        · refine ⟨cfg_EL_n_00 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a21,
            2) :: R11), ?_, Or.inl ⟨.EL_n_00, (0,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (a21, 2) :: R11, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 0 b2 ((((a21 + 1) + 1), b10) :: R11), hb4_0,
            encRight_d0_s0 ((((a21 + 1) + 1), b10) :: R11), encRight_mod3 ((a21 + 1) + 1) b10 R11,
            hb12_2, encRight_succ (a21 + 1) 2 R11, encRight_succ a21 2 R11,
            encRight_run_s2 a21 R11, encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 8 step
          finish

private theorem mode_EB_sep0_d1 (b2 : ℕ) (hb4_0 : b2 % 3 = 0) (L R3 : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EB_n_00 L ((0 + 1, b2) :: R3)) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases R3 with _ | ⟨⟨a23, b24⟩, R25⟩
  · rcases L with _ | ⟨⟨a30, b31⟩, L32⟩
    · refine ⟨cfg_EB_n_00 [] [(0, 2), (0, 0)], ?_, Or.inl ⟨.EB_n_00, [], [(0, 2), (0, 0)], rfl⟩⟩
      unfold cfg_EB_n_00
      rw [encRight_mod3 ((0) + 1) b2 [], hb4_0, encRight_d1_s0 [], encRight_d0_s2 [(0, 0)],
        encRight_d0_s0 []]
      iterate 21 step
      finish
    · refine ⟨cfg_EL_n_00 ((a30, 0) :: L32) [(0, 2), (0, 0)], ?_, Or.inl ⟨.EL_n_00, (a30, 0) :: L32,
        [(0, 2), (0, 0)], rfl⟩⟩
      unfold cfg_EB_n_00 cfg_EL_n_00
      rw [encRight_mod3 ((0) + 1) b2 [], hb4_0, encRight_d1_s0 [], encLeft_mod1 a30 b31 L32,
        Nat.mod_one b31, encLeft_run_s0 a30 L32, encRight_d0_s2 [(0, 0)], encRight_d0_s0 []]
      iterate 21 step
      finish
  · rcases mod3_cases b24 with hb26_0 | hb26_1 | hb26_2
    · rcases a23 with _ | a34
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encLeft L, encRight R25⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((0) + 1) b2 (((0), b24) :: R25), hb4_0,
          encRight_d1_s0 (((0), b24) :: R25), encRight_mod3 0 b24 R25, hb26_0, encRight_d0_s0 R25]
        iterate 7 step
        finish
      · rcases a34 with _ | a35
        · refine ⟨cfg_EL_n_00 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
            0) :: R25), ?_, Or.inl ⟨.EL_n_00, (0,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 0) :: R25, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((0) + 1) b2 ((((0) + 1), b24) :: R25), hb4_0,
            encRight_d1_s0 ((((0) + 1), b24) :: R25), encRight_mod3 ((0) + 1) b24 R25, hb26_0,
            encRight_d1_s0 R25, encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s0 R25]
          iterate 14 step
          finish
        · refine ⟨cfg_EL_n_00 ((1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a35,
            0) :: R25), ?_, Or.inl ⟨.EL_n_00, (1,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (a35, 0) :: R25, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((0) + 1) b2 ((((a35 + 1) + 1), b24) :: R25), hb4_0,
            encRight_d1_s0 ((((a35 + 1) + 1), b24) :: R25), encRight_mod3 ((a35 + 1) + 1) b24 R25,
            hb26_0, encRight_succ (a35 + 1) 0 R25, encRight_succ a35 0 R25,
            encRight_run_s0 a35 R25, encLeft_d1_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 9 step
          finish
    · rcases a23 with _ | a36
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encLeft L, (0 : Fin 2) >> encRight R25⟩⟩, ?_,
            Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((0) + 1) b2 (((0), b24) :: R25), hb4_0,
          encRight_d1_s0 (((0), b24) :: R25), encRight_mod3 0 b24 R25, hb26_1, encRight_d0_s1 R25]
        iterate 7 step
        finish
      · rcases a36 with _ | a37
        · refine ⟨cfg_EL_n_00 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
            1) :: R25), ?_, Or.inl ⟨.EL_n_00, (0,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 1) :: R25, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((0) + 1) b2 ((((0) + 1), b24) :: R25), hb4_0,
            encRight_d1_s0 ((((0) + 1), b24) :: R25), encRight_mod3 ((0) + 1) b24 R25, hb26_1,
            encRight_d1_s1 R25, encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s1 R25]
          iterate 14 step
          finish
        · refine ⟨cfg_EL_n_00 ((1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a37,
            1) :: R25), ?_, Or.inl ⟨.EL_n_00, (1,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (a37, 1) :: R25, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((0) + 1) b2 ((((a37 + 1) + 1), b24) :: R25), hb4_0,
            encRight_d1_s0 ((((a37 + 1) + 1), b24) :: R25), encRight_mod3 ((a37 + 1) + 1) b24 R25,
            hb26_1, encRight_succ (a37 + 1) 1 R25, encRight_succ a37 1 R25,
            encRight_run_s1 a37 R25, encLeft_d1_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 9 step
          finish
    · rcases a23 with _ | a38
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encLeft L, (0 : Fin 2) >> (0 : Fin 2) >>
            encRight R25⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((0) + 1) b2 (((0), b24) :: R25), hb4_0,
          encRight_d1_s0 (((0), b24) :: R25), encRight_mod3 0 b24 R25, hb26_2, encRight_d0_s2 R25]
        iterate 7 step
        finish
      · rcases a38 with _ | a39
        · refine ⟨cfg_EL_n_00 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
            2) :: R25), ?_, Or.inl ⟨.EL_n_00, (0,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 2) :: R25, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((0) + 1) b2 ((((0) + 1), b24) :: R25), hb4_0,
            encRight_d1_s0 ((((0) + 1), b24) :: R25), encRight_mod3 ((0) + 1) b24 R25, hb26_2,
            encRight_d1_s2 R25, encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s2 R25]
          iterate 14 step
          finish
        · refine ⟨cfg_EL_n_00 ((1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a39,
            2) :: R25), ?_, Or.inl ⟨.EL_n_00, (1,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (a39, 2) :: R25, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((0) + 1) b2 ((((a39 + 1) + 1), b24) :: R25), hb4_0,
            encRight_d1_s0 ((((a39 + 1) + 1), b24) :: R25), encRight_mod3 ((a39 + 1) + 1) b24 R25,
            hb26_2, encRight_succ (a39 + 1) 2 R25, encRight_succ a39 2 R25,
            encRight_run_s2 a39 R25, encLeft_d1_s0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 9 step
          finish

private theorem mode_EB_sep0_ge2 (a22 b2 : ℕ) (hb4_0 : b2 % 3 = 0) (L R3 : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EB_n_00 L (((a22 + 1) + 1, b2) :: R3)) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases R3 with _ | ⟨⟨a41, b42⟩, R43⟩
  · rcases a22 with _ | a48
    · rcases L with _ | ⟨⟨a49, b50⟩, L51⟩
      · refine ⟨⟨some C, ⟨0, default, (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default⟩⟩, ?_,
            Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 (((0) + 1) + 1) b2 [], hb4_0, encRight_d2_s0 []]
        iterate 20 step
        finish
      · rcases a49 with _ | a53
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead L51)) [(1, 1), (0, 0)], ?_,
            Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead L51), [(1, 1), (0, 0)], rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 (((0) + 1) + 1) b2 [], hb4_0, encRight_d2_s0 [],
            encLeft_mod1 0 b50 L51, Nat.mod_one b50, encLeft_d0_s0 L51,
            ← encLeft_cons_one (bumpPairHead L51), ← encLeft_cons_one L51, encRight_d1_s1 [(0, 0)],
            encRight_d0_s0 []]
          iterate 24 step
          finish
        · rcases a53 with _ | a54
          · refine ⟨cfg_EB_n_00 L51 [(0, 1), (1, 1), (0, 0)], ?_, Or.inl ⟨.EB_n_00, L51, [(0, 1),
              (1, 1), (0, 0)], rfl⟩⟩
            unfold cfg_EB_n_00
            rw [encRight_mod3 (((0) + 1) + 1) b2 [], hb4_0, encRight_d2_s0 [],
              encLeft_mod1 ((0) + 1) b50 L51, Nat.mod_one b50, encLeft_d1_s0 L51,
              encRight_d0_s1 [(1, 1), (0, 0)], encRight_d1_s1 [(0, 0)], encRight_d0_s0 []]
            iterate 27 step
            finish
          · refine ⟨cfg_EL_n_00 ((a54, 0) :: L51) [(0, 1), (1, 1), (0, 0)], ?_, Or.inl ⟨.EL_n_00,
              (a54, 0) :: L51, [(0, 1), (1, 1), (0, 0)], rfl⟩⟩
            unfold cfg_EB_n_00 cfg_EL_n_00
            rw [encRight_mod3 (((0) + 1) + 1) b2 [], hb4_0, encRight_d2_s0 [],
              encLeft_mod1 ((a54 + 1) + 1) b50 L51, Nat.mod_one b50, encLeft_succ (a54 + 1) 0 L51,
              encLeft_succ a54 0 L51, encLeft_run_s0 a54 L51, encRight_d0_s1 [(1, 1), (0, 0)],
              encRight_d1_s1 [(0, 0)], encRight_d0_s0 []]
            iterate 27 step
            finish
    · rcases a48 with _ | a55
      · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead
          L))))) [(0, 0)], ?_, Or.inl ⟨.EB_n_00,
            bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead L)))), [(0, 0)],
              rfl⟩⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((((0) + 1) + 1) + 1) b2 [], hb4_0, encRight_d3_s0 [],
          ← encLeft_cons_one (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead L)))),
          ← encLeft_cons_one (bumpPairHead (bumpPairHead (bumpPairHead L))),
          ← encLeft_cons_one (bumpPairHead (bumpPairHead L)), ← encLeft_cons_one (bumpPairHead L),
          ← encLeft_cons_one L, encRight_d0_s0 []]
        iterate 19 step
        finish
      · rcases a55 with _ | a56
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) [(0, 1), (0, 0)], ?_,
            Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), [(0, 1), (0, 0)], rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 (((((0) + 1) + 1) + 1) + 1) b2 [], hb4_0, encRight_d4_s0 [],
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s1 [(0, 0)],
            encRight_d0_s0 []]
          iterate 23 step
          finish
        · refine ⟨cfg_EL_n_00 ((a56, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) [(0, 1),
            (0, 0)], ?_, Or.inl ⟨.EL_n_00, (a56, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L)),
              [(0, 1), (0, 0)], rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 (((((a56 + 1) + 1) + 1) + 1) + 1) b2 [], hb4_0,
            encRight_succ (a56 + 1 + 1 + 1 + 1) 0 [], encRight_succ (a56 + 1 + 1 + 1) 0 [],
            encRight_succ (a56 + 1 + 1) 0 [], encRight_succ (a56 + 1) 0 [], encRight_succ a56 0 [],
            encRight_run_s0 a56 [],
            encLeft_run_s0 a56 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s1 [(0, 0)],
            encRight_d0_s0 []]
          iterate 8 step
          walk (cyc_R_A_1_11_11_1 a56 _ _)
          iterate 16 step
          finish
  · rcases mod3_cases b42 with hb44_0 | hb44_1 | hb44_2
    · rcases a41 with _ | a57
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          (([1] : List (Fin 2)) ^ a22) +> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
            (1 : Fin 2) >> encLeft L), encRight R43⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((a22 + 1) + 1) b2 (((0), b42) :: R43), hb4_0,
          encRight_succ (a22 + 1) 0 (((0), b42) :: R43), encRight_succ a22 0 (((0), b42) :: R43),
          encRight_run_s0 a22 (((0), b42) :: R43), encRight_mod3 0 b42 R43, hb44_0,
          encRight_d0_s0 R43]
        iterate 5 step
        walk (cyc_R_A_1_11_11_1 a22 _ _)
        iterate 3 step
        finish
      · rcases a57 with _ | a58
        · refine ⟨cfg_EL_n_00 ((a22 + 1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
            0) :: R43), ?_, Or.inl ⟨.EL_n_00, (a22 + 1,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 0) :: R43, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((a22 + 1) + 1) b2 ((((0) + 1), b42) :: R43), hb4_0,
            encRight_succ (a22 + 1) 0 ((((0) + 1), b42) :: R43),
            encRight_succ a22 0 ((((0) + 1), b42) :: R43),
            encRight_run_s0 a22 ((((0) + 1), b42) :: R43), encRight_mod3 ((0) + 1) b42 R43, hb44_0,
            encRight_d1_s0 R43, encLeft_succ a22 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_run_s0 a22 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s0 R43]
          iterate 5 step
          walk (cyc_R_A_1_11_11_1 a22 _ _)
          iterate 10 step
          finish
        · refine ⟨cfg_EL_n_00 ((a22 + 1 + 1,
            0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a58, 0) :: R43), ?_,
              Or.inl ⟨.EL_n_00, (a22 + 1 + 1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L)),
                (a58, 0) :: R43, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((a22 + 1) + 1) b2 ((((a58 + 1) + 1), b42) :: R43), hb4_0,
            encRight_succ (a22 + 1) 0 ((((a58 + 1) + 1), b42) :: R43),
            encRight_succ a22 0 ((((a58 + 1) + 1), b42) :: R43),
            encRight_run_s0 a22 ((((a58 + 1) + 1), b42) :: R43),
            encRight_mod3 ((a58 + 1) + 1) b42 R43, hb44_0, encRight_succ (a58 + 1) 0 R43,
            encRight_succ a58 0 R43, encRight_run_s0 a58 R43,
            encLeft_succ (a22 + 1) 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_succ a22 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_run_s0 a22 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 5 step
          walk (cyc_R_A_1_11_11_1 a22 _ _)
          iterate 5 step
          finish
    · rcases a41 with _ | a59
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          (([1] : List (Fin 2)) ^ a22) +> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
            (1 : Fin 2) >> encLeft L), (0 : Fin 2) >> encRight R43⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((a22 + 1) + 1) b2 (((0), b42) :: R43), hb4_0,
          encRight_succ (a22 + 1) 0 (((0), b42) :: R43), encRight_succ a22 0 (((0), b42) :: R43),
          encRight_run_s0 a22 (((0), b42) :: R43), encRight_mod3 0 b42 R43, hb44_1,
          encRight_d0_s1 R43]
        iterate 5 step
        walk (cyc_R_A_1_11_11_1 a22 _ _)
        iterate 3 step
        finish
      · rcases a59 with _ | a60
        · refine ⟨cfg_EL_n_00 ((a22 + 1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
            1) :: R43), ?_, Or.inl ⟨.EL_n_00, (a22 + 1,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 1) :: R43, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((a22 + 1) + 1) b2 ((((0) + 1), b42) :: R43), hb4_0,
            encRight_succ (a22 + 1) 0 ((((0) + 1), b42) :: R43),
            encRight_succ a22 0 ((((0) + 1), b42) :: R43),
            encRight_run_s0 a22 ((((0) + 1), b42) :: R43), encRight_mod3 ((0) + 1) b42 R43, hb44_1,
            encRight_d1_s1 R43, encLeft_succ a22 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_run_s0 a22 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s1 R43]
          iterate 5 step
          walk (cyc_R_A_1_11_11_1 a22 _ _)
          iterate 10 step
          finish
        · refine ⟨cfg_EL_n_00 ((a22 + 1 + 1,
            0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a60, 1) :: R43), ?_,
              Or.inl ⟨.EL_n_00, (a22 + 1 + 1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L)),
                (a60, 1) :: R43, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((a22 + 1) + 1) b2 ((((a60 + 1) + 1), b42) :: R43), hb4_0,
            encRight_succ (a22 + 1) 0 ((((a60 + 1) + 1), b42) :: R43),
            encRight_succ a22 0 ((((a60 + 1) + 1), b42) :: R43),
            encRight_run_s0 a22 ((((a60 + 1) + 1), b42) :: R43),
            encRight_mod3 ((a60 + 1) + 1) b42 R43, hb44_1, encRight_succ (a60 + 1) 1 R43,
            encRight_succ a60 1 R43, encRight_run_s1 a60 R43,
            encLeft_succ (a22 + 1) 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_succ a22 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_run_s0 a22 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 5 step
          walk (cyc_R_A_1_11_11_1 a22 _ _)
          iterate 5 step
          finish
    · rcases a41 with _ | a61
      · refine ⟨⟨some C, ⟨0, (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          (([1] : List (Fin 2)) ^ a22) +> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
            (1 : Fin 2) >> encLeft L), (0 : Fin 2) >> (0 : Fin 2) >> encRight R43⟩⟩, ?_, Or.inr rfl⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((a22 + 1) + 1) b2 (((0), b42) :: R43), hb4_0,
          encRight_succ (a22 + 1) 0 (((0), b42) :: R43), encRight_succ a22 0 (((0), b42) :: R43),
          encRight_run_s0 a22 (((0), b42) :: R43), encRight_mod3 0 b42 R43, hb44_2,
          encRight_d0_s2 R43]
        iterate 5 step
        walk (cyc_R_A_1_11_11_1 a22 _ _)
        iterate 3 step
        finish
      · rcases a61 with _ | a62
        · refine ⟨cfg_EL_n_00 ((a22 + 1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
            2) :: R43), ?_, Or.inl ⟨.EL_n_00, (a22 + 1,
              0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 2) :: R43, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((a22 + 1) + 1) b2 ((((0) + 1), b42) :: R43), hb4_0,
            encRight_succ (a22 + 1) 0 ((((0) + 1), b42) :: R43),
            encRight_succ a22 0 ((((0) + 1), b42) :: R43),
            encRight_run_s0 a22 ((((0) + 1), b42) :: R43), encRight_mod3 ((0) + 1) b42 R43, hb44_2,
            encRight_d1_s2 R43, encLeft_succ a22 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_run_s0 a22 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s2 R43]
          iterate 5 step
          walk (cyc_R_A_1_11_11_1 a22 _ _)
          iterate 10 step
          finish
        · refine ⟨cfg_EL_n_00 ((a22 + 1 + 1,
            0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((a62, 2) :: R43), ?_,
              Or.inl ⟨.EL_n_00, (a22 + 1 + 1, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L)),
                (a62, 2) :: R43, rfl⟩⟩
          unfold cfg_EB_n_00 cfg_EL_n_00
          rw [encRight_mod3 ((a22 + 1) + 1) b2 ((((a62 + 1) + 1), b42) :: R43), hb4_0,
            encRight_succ (a22 + 1) 0 ((((a62 + 1) + 1), b42) :: R43),
            encRight_succ a22 0 ((((a62 + 1) + 1), b42) :: R43),
            encRight_run_s0 a22 ((((a62 + 1) + 1), b42) :: R43),
            encRight_mod3 ((a62 + 1) + 1) b42 R43, hb44_2, encRight_succ (a62 + 1) 2 R43,
            encRight_succ a62 2 R43, encRight_run_s2 a62 R43,
            encLeft_succ (a22 + 1) 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_succ a22 0 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            encLeft_run_s0 a22 (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
          iterate 5 step
          walk (cyc_R_A_1_11_11_1 a22 _ _)
          iterate 5 step
          finish

private theorem mode_EB_sep1 (a1 b2 : ℕ) (hb4_1 : b2 % 3 = 1) (L R3 : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EB_n_00 L ((a1, b2) :: R3)) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases a1 with _ | a63
  · refine ⟨cfg_EL_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) (bumpPairHead R3), ?_,
      Or.inl ⟨.EL_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), bumpPairHead R3, rfl⟩⟩
    unfold cfg_EB_n_00 cfg_EL_n_00
    rw [encRight_mod3 0 b2 R3, hb4_1, encRight_d0_s1 R3,
      ← encLeft_cons_one (bumpPairHead (bumpPairHead L)), ← encLeft_cons_one (bumpPairHead L),
      ← encLeft_cons_one L, ← encRight_cons_one R3]
    iterate 8 step
    finish
  · rcases a63 with _ | a64
    · rcases L with _ | ⟨⟨a65, b66⟩, L67⟩
      · refine ⟨cfg_EB_n_00 [] ((0, 2) :: bumpPairHead R3), ?_, Or.inl ⟨.EB_n_00, [], (0,
          2) :: bumpPairHead R3, rfl⟩⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((0) + 1) b2 R3, hb4_1, encRight_d1_s1 R3,
          encRight_d0_s2 (bumpPairHead R3), ← encRight_cons_one R3]
        iterate 21 step
        finish
      · refine ⟨cfg_EL_n_00 ((a65, 0) :: L67) ((0, 2) :: bumpPairHead R3), ?_, Or.inl ⟨.EL_n_00,
          (a65, 0) :: L67, (0, 2) :: bumpPairHead R3, rfl⟩⟩
        unfold cfg_EB_n_00 cfg_EL_n_00
        rw [encRight_mod3 ((0) + 1) b2 R3, hb4_1, encRight_d1_s1 R3, encLeft_mod1 a65 b66 L67,
          Nat.mod_one b66, encLeft_run_s0 a65 L67, encRight_d0_s2 (bumpPairHead R3),
          ← encRight_cons_one R3]
        iterate 21 step
        finish
    · rcases a64 with _ | a70
      · rcases L with _ | ⟨⟨a71, b72⟩, L73⟩
        · refine ⟨⟨some C, ⟨0, default, (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
              encRight R3⟩⟩, ?_, Or.inr rfl⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_1, encRight_d2_s1 R3]
          iterate 20 step
          finish
        · rcases a71 with _ | a75
          · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead L73)) ((1, 1) :: bumpPairHead R3), ?_,
              Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead L73), (1, 1) :: bumpPairHead R3, rfl⟩⟩
            unfold cfg_EB_n_00
            rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_1, encRight_d2_s1 R3,
              encLeft_mod1 0 b72 L73, Nat.mod_one b72, encLeft_d0_s0 L73,
              ← encLeft_cons_one (bumpPairHead L73), ← encLeft_cons_one L73,
              encRight_d1_s1 (bumpPairHead R3), ← encRight_cons_one R3]
            iterate 24 step
            finish
          · rcases a75 with _ | a76
            · refine ⟨cfg_EB_n_00 L73 ((0, 1) :: (1, 1) :: bumpPairHead R3), ?_, Or.inl ⟨.EB_n_00,
                L73, (0, 1) :: (1, 1) :: bumpPairHead R3, rfl⟩⟩
              unfold cfg_EB_n_00
              rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_1, encRight_d2_s1 R3,
                encLeft_mod1 ((0) + 1) b72 L73, Nat.mod_one b72, encLeft_d1_s0 L73,
                encRight_d0_s1 ((1, 1) :: bumpPairHead R3), encRight_d1_s1 (bumpPairHead R3),
                ← encRight_cons_one R3]
              iterate 27 step
              finish
            · refine ⟨cfg_EL_n_00 ((a76, 0) :: L73) ((0, 1) :: (1, 1) :: bumpPairHead R3), ?_,
                Or.inl ⟨.EL_n_00, (a76, 0) :: L73, (0, 1) :: (1, 1) :: bumpPairHead R3, rfl⟩⟩
              unfold cfg_EB_n_00 cfg_EL_n_00
              rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_1, encRight_d2_s1 R3,
                encLeft_mod1 ((a76 + 1) + 1) b72 L73, Nat.mod_one b72,
                encLeft_succ (a76 + 1) 0 L73, encLeft_succ a76 0 L73, encLeft_run_s0 a76 L73,
                encRight_d0_s1 ((1, 1) :: bumpPairHead R3), encRight_d1_s1 (bumpPairHead R3),
                ← encRight_cons_one R3]
              iterate 27 step
              finish
      · rcases a70 with _ | a77
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead
            L))))) (bumpPairHead R3), ?_, Or.inl ⟨.EB_n_00,
              bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead L)))),
                bumpPairHead R3, rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 ((((0) + 1) + 1) + 1) b2 R3, hb4_1, encRight_d3_s1 R3,
            ← encLeft_cons_one (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead L)))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, ← encRight_cons_one R3]
          iterate 19 step
          finish
        · rcases a77 with _ | a78
          · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
              1) :: bumpPairHead R3), ?_, Or.inl ⟨.EB_n_00,
                bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 1) :: bumpPairHead R3, rfl⟩⟩
            unfold cfg_EB_n_00
            rw [encRight_mod3 (((((0) + 1) + 1) + 1) + 1) b2 R3, hb4_1, encRight_d4_s1 R3,
              ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
              ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L,
              encRight_d0_s1 (bumpPairHead R3), ← encRight_cons_one R3]
            iterate 23 step
            finish
          · refine ⟨cfg_EL_n_00 ((a78, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
              1) :: bumpPairHead R3), ?_, Or.inl ⟨.EL_n_00, (a78,
                0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 1) :: bumpPairHead R3, rfl⟩⟩
            unfold cfg_EB_n_00 cfg_EL_n_00
            rw [encRight_mod3 (((((a78 + 1) + 1) + 1) + 1) + 1) b2 R3, hb4_1,
              encRight_succ (a78 + 1 + 1 + 1 + 1) 1 R3, encRight_succ (a78 + 1 + 1 + 1) 1 R3,
              encRight_succ (a78 + 1 + 1) 1 R3, encRight_succ (a78 + 1) 1 R3,
              encRight_succ a78 1 R3, encRight_run_s1 a78 R3,
              encLeft_run_s0 a78 (bumpPairHead (bumpPairHead (bumpPairHead L))),
              ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
              ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L,
              encRight_d0_s1 (bumpPairHead R3), ← encRight_cons_one R3]
            iterate 8 step
            walk (cyc_R_A_1_11_11_1 a78 _ _)
            iterate 16 step
            finish

private theorem mode_EB_sep2 (a1 b2 : ℕ) (hb4_2 : b2 % 3 = 2) (L R3 : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EB_n_00 L ((a1, b2) :: R3)) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases a1 with _ | a79
  · refine ⟨cfg_EL_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) ((0, 0) :: R3), ?_,
      Or.inl ⟨.EL_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 0) :: R3, rfl⟩⟩
    unfold cfg_EB_n_00 cfg_EL_n_00
    rw [encRight_mod3 0 b2 R3, hb4_2, encRight_d0_s2 R3,
      ← encLeft_cons_one (bumpPairHead (bumpPairHead L)), ← encLeft_cons_one (bumpPairHead L),
      ← encLeft_cons_one L, encRight_d0_s0 R3]
    iterate 8 step
    finish
  · rcases a79 with _ | a80
    · rcases L with _ | ⟨⟨a81, b82⟩, L83⟩
      · refine ⟨cfg_EB_n_00 [] ((0, 2) :: (0, 0) :: R3), ?_, Or.inl ⟨.EB_n_00, [], (0, 2) :: (0,
          0) :: R3, rfl⟩⟩
        unfold cfg_EB_n_00
        rw [encRight_mod3 ((0) + 1) b2 R3, hb4_2, encRight_d1_s2 R3, encRight_d0_s2 ((0, 0) :: R3),
          encRight_d0_s0 R3]
        iterate 21 step
        finish
      · refine ⟨cfg_EL_n_00 ((a81, 0) :: L83) ((0, 2) :: (0, 0) :: R3), ?_, Or.inl ⟨.EL_n_00, (a81,
          0) :: L83, (0, 2) :: (0, 0) :: R3, rfl⟩⟩
        unfold cfg_EB_n_00 cfg_EL_n_00
        rw [encRight_mod3 ((0) + 1) b2 R3, hb4_2, encRight_d1_s2 R3, encLeft_mod1 a81 b82 L83,
          Nat.mod_one b82, encLeft_run_s0 a81 L83, encRight_d0_s2 ((0, 0) :: R3),
          encRight_d0_s0 R3]
        iterate 21 step
        finish
    · rcases a80 with _ | a86
      · rcases L with _ | ⟨⟨a87, b88⟩, L89⟩
        · refine ⟨⟨some C, ⟨0, default, (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
              (0 : Fin 2) >> encRight R3⟩⟩, ?_, Or.inr rfl⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_2, encRight_d2_s2 R3]
          iterate 20 step
          finish
        · rcases a87 with _ | a91
          · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead L89)) ((1, 1) :: (0, 0) :: R3), ?_,
              Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead L89), (1, 1) :: (0, 0) :: R3, rfl⟩⟩
            unfold cfg_EB_n_00
            rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_2, encRight_d2_s2 R3,
              encLeft_mod1 0 b88 L89, Nat.mod_one b88, encLeft_d0_s0 L89,
              ← encLeft_cons_one (bumpPairHead L89), ← encLeft_cons_one L89,
              encRight_d1_s1 ((0, 0) :: R3), encRight_d0_s0 R3]
            iterate 24 step
            finish
          · rcases a91 with _ | a92
            · refine ⟨cfg_EB_n_00 L89 ((0, 1) :: (1, 1) :: (0, 0) :: R3), ?_, Or.inl ⟨.EB_n_00, L89,
                (0, 1) :: (1, 1) :: (0, 0) :: R3, rfl⟩⟩
              unfold cfg_EB_n_00
              rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_2, encRight_d2_s2 R3,
                encLeft_mod1 ((0) + 1) b88 L89, Nat.mod_one b88, encLeft_d1_s0 L89,
                encRight_d0_s1 ((1, 1) :: (0, 0) :: R3), encRight_d1_s1 ((0, 0) :: R3),
                encRight_d0_s0 R3]
              iterate 27 step
              finish
            · refine ⟨cfg_EL_n_00 ((a92, 0) :: L89) ((0, 1) :: (1, 1) :: (0, 0) :: R3), ?_,
                Or.inl ⟨.EL_n_00, (a92, 0) :: L89, (0, 1) :: (1, 1) :: (0, 0) :: R3, rfl⟩⟩
              unfold cfg_EB_n_00 cfg_EL_n_00
              rw [encRight_mod3 (((0) + 1) + 1) b2 R3, hb4_2, encRight_d2_s2 R3,
                encLeft_mod1 ((a92 + 1) + 1) b88 L89, Nat.mod_one b88,
                encLeft_succ (a92 + 1) 0 L89, encLeft_succ a92 0 L89, encLeft_run_s0 a92 L89,
                encRight_d0_s1 ((1, 1) :: (0, 0) :: R3), encRight_d1_s1 ((0, 0) :: R3),
                encRight_d0_s0 R3]
              iterate 27 step
              finish
      · rcases a86 with _ | a93
        · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead
            L))))) ((0, 0) :: R3), ?_, Or.inl ⟨.EB_n_00,
              bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead L)))), (0,
                0) :: R3, rfl⟩⟩
          unfold cfg_EB_n_00
          rw [encRight_mod3 ((((0) + 1) + 1) + 1) b2 R3, hb4_2, encRight_d3_s2 R3,
            ← encLeft_cons_one (bumpPairHead (bumpPairHead (bumpPairHead (bumpPairHead L)))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead (bumpPairHead L))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
            ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L, encRight_d0_s0 R3]
          iterate 19 step
          finish
        · rcases a93 with _ | a94
          · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) ((0, 1) :: (0,
              0) :: R3), ?_, Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), (0,
                1) :: (0, 0) :: R3, rfl⟩⟩
            unfold cfg_EB_n_00
            rw [encRight_mod3 (((((0) + 1) + 1) + 1) + 1) b2 R3, hb4_2, encRight_d4_s2 R3,
              ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
              ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L,
              encRight_d0_s1 ((0, 0) :: R3), encRight_d0_s0 R3]
            iterate 23 step
            finish
          · refine ⟨cfg_EL_n_00 ((a94, 0) :: bumpPairHead (bumpPairHead (bumpPairHead L))) ((0,
              1) :: (0, 0) :: R3), ?_, Or.inl ⟨.EL_n_00, (a94,
                0) :: bumpPairHead (bumpPairHead (bumpPairHead L)), (0, 1) :: (0, 0) :: R3, rfl⟩⟩
            unfold cfg_EB_n_00 cfg_EL_n_00
            rw [encRight_mod3 (((((a94 + 1) + 1) + 1) + 1) + 1) b2 R3, hb4_2,
              encRight_succ (a94 + 1 + 1 + 1 + 1) 2 R3, encRight_succ (a94 + 1 + 1 + 1) 2 R3,
              encRight_succ (a94 + 1 + 1) 2 R3, encRight_succ (a94 + 1) 2 R3,
              encRight_succ a94 2 R3, encRight_run_s2 a94 R3,
              encLeft_run_s0 a94 (bumpPairHead (bumpPairHead (bumpPairHead L))),
              ← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
              ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L,
              encRight_d0_s1 ((0, 0) :: R3), encRight_d0_s0 R3]
            iterate 8 step
            walk (cyc_R_A_1_11_11_1 a94 _ _)
            iterate 16 step
            finish

private theorem mode_EB_n_00_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EB_n_00 L R) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases R with _ | ⟨⟨a1, b2⟩, R3⟩
  · refine ⟨cfg_EB_n_00 (bumpPairHead (bumpPairHead (bumpPairHead L))) [], ?_,
      Or.inl ⟨.EB_n_00, bumpPairHead (bumpPairHead (bumpPairHead L)), [], rfl⟩⟩
    unfold cfg_EB_n_00
    rw [← encLeft_cons_one (bumpPairHead (bumpPairHead L)),
      ← encLeft_cons_one (bumpPairHead L), ← encLeft_cons_one L]
    iterate 3 step
    finish
  · rcases mod3_cases b2 with hb4_0 | hb4_1 | hb4_2
    · rcases a1 with _ | _ | a22
      · exact mode_EB_sep0_d0 b2 hb4_0 L R3
      · exact mode_EB_sep0_d1 b2 hb4_0 L R3
      · exact mode_EB_sep0_ge2 a22 b2 hb4_0 L R3
    · exact mode_EB_sep1 a1 b2 hb4_1 L R3
    · exact mode_EB_sep2 a1 b2 hb4_2 L R3

private theorem cfg_EL_n_00_nil_eq (R : List (ℕ × ℕ)) :
    cfg_EL_n_00 [] R = cfg_EB_n_00 [] R := by
  unfold cfg_EL_n_00 cfg_EB_n_00 Cfg.headLeft
  simp [encLeft_nil]

private theorem mode_EL_n_00_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg', ((cfg_EL_n_00 L R) [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
  · rw [cfg_EL_n_00_nil_eq]
    exact mode_EB_n_00_closed [] R
  · rcases a1 with _ | a69
    · refine ⟨cfg_EB_n_00 L3 (bumpPairHead R), ?_, Or.inl ⟨.EB_n_00, L3, bumpPairHead R, rfl⟩⟩
      unfold cfg_EL_n_00 cfg_EB_n_00
      rw [encLeft_mod1 0 b2 L3, Nat.mod_one b2, encLeft_d0_s0 L3, ← encRight_cons_one R]
      iterate 5 step
      finish
    · refine ⟨cfg_EL_n_00 ((a69, 0) :: L3) (bumpPairHead R), ?_,
        Or.inl ⟨.EL_n_00, (a69, 0) :: L3, bumpPairHead R, rfl⟩⟩
      unfold cfg_EL_n_00
      rw [encLeft_mod1 (a69 + 1) b2 L3, Nat.mod_one b2,
        encLeft_succ a69 0 L3, encLeft_run_s0 a69 L3, ← encRight_cons_one R]
      iterate 5 step
      finish

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
            (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | EB_n_00 => exact mode_EB_n_00_closed L R
  | EL_n_00 => exact mode_EL_n_00_closed L R

private theorem init_reaches_stack_system :
    ∃ cfg₀, ((init []) [target]⊢⁺ cfg₀) ∧ IsInStackSystem cfg₀ := by
  refine ⟨cfg_EB_n_00 [] [(0, 0)], ?_, ⟨.EB_n_00, [], [(0, 0)], rfl⟩⟩
  have hL : encLeft [] = default := rfl
  have hR : encRight [(0, 0)] = (1 : Fin 2) >> (0 : Fin 2) >> default := rfl
  unfold cfg_EB_n_00
  rw [hL, hR]
  execute 4


private theorem encLeft_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: L)).head = 1 := by
  rw [encLeft_cons, show 1 * a + 1 = (1 * a + 0) + 1 by omega, list_pow_succ, List.cons_append]
  simp only [ListBlank.append_cons, ListBlank.head_cons]

private theorem encLeft_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ L : List (ℕ × ℕ), encLeft L ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro L h
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rw [encLeft_mod1] at h
    have hb0 : b % 1 = 0 := Nat.mod_one b
    rw [hb0, encLeft_run_s0] at h
    rcases a with _ | a'
    · rcases L' with _ | ⟨⟨a', b'⟩, L''⟩
      · have h2 := congrArg (fun s => s.tail.tail.tail.head) h
        simp at h2
      · have h1 := congrArg (fun s => s.tail.tail.head) h
        normalize_at h1
        rw [encLeft_head a' b' L''] at h1; contradiction
    · have h1 := congrArg (fun s => s.tail.head) h
      normalize_at h1
      contradiction

private theorem encRight_head (a b : ℕ) (R : List (ℕ × ℕ)) :
    (encRight ((a, b) :: R)).head = 1 := by
  rw [encRight_cons, show 1 * a + 1 = (1 * a + 0) + 1 by omega, list_pow_succ, List.cons_append]
  simp only [ListBlank.append_cons, ListBlank.head_cons]

private theorem encRight_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ R : List (ℕ × ℕ), encRight R ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    default, rfl, ?_⟩
  intro R h
  rcases R with _ | ⟨⟨a, b⟩, R'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rw [encRight_mod3] at h
    rcases mod3_cases b with hb0 | hb1 | hb2
    · rw [hb0, encRight_run_s0] at h
      rcases a with _ | a'
      · rcases R' with _ | ⟨⟨a', b'⟩, R''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.head) h
          normalize_at h1
          rw [encRight_head a' b' R''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction
    · rw [hb1, encRight_run_s1] at h
      rcases a with _ | a'
      · rcases R' with _ | ⟨⟨a', b'⟩, R''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.tail.head) h
          normalize_at h1
          rw [encRight_head a' b' R''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction
    · rw [hb2, encRight_run_s2] at h
      rcases a with _ | a'
      · rcases R' with _ | ⟨⟨a', b'⟩, R''⟩
        · have h2 := congrArg (fun s => s.tail.tail.tail.tail.tail.head) h
          simp at h2
        · have h1 := congrArg (fun s => s.tail.tail.tail.tail.head) h
          normalize_at h1
          rw [encRight_head a' b' R''] at h1; contradiction
      · have h1 := congrArg (fun s => s.tail.head) h
        normalize_at h1
        contradiction

private theorem valid_stack_modes : IsValidStackModes encLeft encRight evalStackCfg := by
  intro m
  cases m with
  | EB_n_00 => exact ⟨E, .id [], .id [0, 0], Or.inl (fun _ _ => rfl)⟩
  | EL_n_00 => exact ⟨E, .id [], .id [0, 0], Or.inr (Or.inl (fun _ _ => rfl))⟩

/-! ## Stack Reduction Witness -/

/-- `target` reduces to a closed 2nd-order digit-stack transition system. -/
theorem has_stack_reduction : HasStackReduction target := by
  refine ⟨StackMode, 1, 0, encLeft, encRight, evalStackCfg, IsInStackSystem,
    Or.inl ⟨rfl, rfl⟩, rfl, rfl,
    encLeft_head, encRight_head, encLeft_not_surjective, encRight_not_surjective,
    ⟨1, 1, 1, 1, 1, 1, 1, 3, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    ⟨[.EB_n_00, .EL_n_00], by decide, by intro m; cases m <;> decide⟩,
    valid_stack_modes,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    init_reaches_stack_system,
    stack_system_closed⟩

end BusyBeaver.M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB
