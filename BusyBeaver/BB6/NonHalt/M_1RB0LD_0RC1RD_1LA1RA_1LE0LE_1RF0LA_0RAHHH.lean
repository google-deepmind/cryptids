/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.BB6.Accelerations.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.Accelerated
import BusyBeaver.Calculi.ProofKit


/-!
# Busy Beaver Machine `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.Accelerated`,
  `BusyBeaver.ProofKit`
and defines `target_tm` for `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH

namespace NonHaltProof

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-!
Holdout #510 (797:#510 / 608:#385, `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`).
derived_from:
  suspects/partial/accelerated/m_1rb0ld_0rc1rd_1la1ra_1le0le_1rf0la_0rahhh/has_queried_acceleration.lean

## Proof Overview

We prove `IsNotHalt target_tm` constructively (no excluded-middle bypass, no unverified native
evaluation, no incomplete goals; axioms strictly inside `{propext, Quot.sound, Classical.choice}`)
via **strong induction on step fuel** over a **topologically sorted 578-node tail-parametric
  abstract
fixed-point certificate**:

1. **Verified macro engine** (adapted from `has_queried_acceleration.lean`): encodes configurations
   via `evalSegCfg m L R` over `SegMode ∈ {.mAR, .mA0R, .mEL}`, plus accelerated `seg_desc_run`,
   `seg_W3_run`, `seg_T_run`, `seg_drain`, `seg_sea_enter`, `seg_era_mod0`, `seg_era_mod2`.
2. **Constructive fuel combinators (`SafeFrom`)**: a state is `SafeFrom P cfg fuel` if it either
   runs `fuel` raw steps without halting or reaches a state satisfying `P` in `1 ≤ m ≤ fuel` steps.
   Every `≥ 1`-step transition strictly decreases `fuel` (`Nat.strong_induction_on`), while every
   `0`-step structural decomposition strictly decreases the node index (`0..577`) along a verified
   topological order (`Nat.strong_induction_on`).
3. **Tail-parametric diode certificate (578 nodes, 174 deduplicated exit buckets)**:
   checked in 19 pure-kernel `decide +kernel` chunks (`cert_chunk_0..18`) over `noncomputable def`
   radix-8 lookup tables and pure-`Bool` equality. Soundness establishes:
   - `E(6, ANY)` (node 576): `mAR (0 :: 0 :: 1^6 ++ L) R` exits ONLY as `MZ 0`
     (`mA0R L (0 :: 1 :: _)`), draining `L = 1^m ++ [0]` directly to `mAR [] (2^(m + 2) ++ _)`.
   - `S1(7, ANY)` (node 577): `mAR (0 :: 1^7 ++ L) R` exits ONLY as `MZ 0` with tail
     `2^c ++ (h + 5) :: _` (`c ≥ 0`), draining `L = 1^m ++ [0]` directly to
     `mAR [] (2^(m + 2 + c) ++ (h + 5) :: _)`.
4. **Universal `h ≥ 4` sweep & exponential loop closure**:
   - Blank tape reaches `mAR [] (5 :: 1^2)` in 44 steps, then 8 deterministic Collatz eras
     (`2 → 6 → 12 → 20 → 30 → 44 → 62 → 86 → 118`) reach `mAR (E 78) [1, 1]`.
   - From any `mAR (E k) R` with `k ≥ 42` (`78 ≥ 42`): `E(6)` drains to `a = k - 4 ≥ 38` twos,
     `seg_desc_run` enters `S1(7)` above `a - 8` ones, `S1(7)` drains to `a' = k - 10 + c ≥ 32`
     twos before a digit `≥ 5`, `seg_sweep_ge4` + `seg_drain` + `seg_sea_enter` lift back to
     `mAR (E (2 * ((2 * a') / 3))) _`, where `2 * ((2 * a') / 3) ≥ 42` strictly closes the loop.
-/

/-! ## Section 1: Verified Macro Engine (from `has_queried_acceleration.lean`) -/


theorem reachesIn_cast {M : Machine (Fin 2) (Fin 6)} {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    {m k : ℕ} (h : ReachesIn M m c₁ c₂) (hk : m = k) :
    ReachesIn M k c₁ c₂ := by
  subst hk; exact h

local macro "finish_in" : tactic => `(tactic| (
  try simp only [zero_cons_default]
  exact ReachesIn.zero _ _))

local macro "step_in" : tactic => `(tactic| (
  refine ReachesIn.step_left (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))

inductive SegMode where
  | mAR
  | mA0R
  | mEL
deriving DecidableEq, Repr

@[simp]
def onesSep0 : ℕ → List (Fin 2)
  | 0 => [0]
  | d + 1 => 1 :: onesSep0 d

@[simp]
def lWord (d : ℕ) : List (Fin 2) := 1 :: onesSep0 d

@[simp]
def encLeft : List ℕ → ListBlank (Fin 2)
  | [] => default
  | d :: L => lWord d +> encLeft L

@[simp]
def rWord : ℕ → List (Fin 2)
  | 0 => [1]
  | z + 1 => 0 :: rWord z

@[simp]
def encRight : List ℕ → ListBlank (Fin 2)
  | [] => default
  | z :: R => rWord z +> encRight R

abbrev SegState := SegMode × List ℕ × List ℕ

@[simp]
def evalSegCfg : SegMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .mAR, L, R => (encLeft L) {{0}}> (encRight R)
  | .mA0R, L, R => ((0 : Fin 2) >> encLeft L) {{0}}> (encRight R)
  | .mEL, L, R => (encLeft L) <{{4}} (encRight R)

@[simp]
def bump1L : List ℕ → List ℕ
  | [] => [0]
  | d :: xs => (d + 1) :: xs

theorem one_cons_encLeft (xs : List ℕ) :
    (1 : Fin 2) >> encLeft xs = encLeft (bump1L xs) := by
  cases xs <;> simp [bump1L, encLeft, lWord, onesSep0, ListBlank.append, zero_cons_default]

@[simp]
def push0R : List ℕ → List ℕ
  | [] => []
  | z :: xs => (z + 1) :: xs

theorem zero_cons_encRight (xs : List ℕ) :
    (0 : Fin 2) >> encRight xs = encRight (push0R xs) := by
  cases xs <;> simp [push0R, encRight, rWord, ListBlank.append, zero_cons_default]

local macro "execute_in_1" : tactic => `(tactic| (
  iterate 1 step_in
  finish_in))

local macro "execute_in_2" : tactic => `(tactic| (
  iterate 2 step_in
  finish_in))

local macro "execute_in_3" : tactic => `(tactic| (
  iterate 3 step_in
  finish_in))

local macro "execute_in_4" : tactic => `(tactic| (
  iterate 4 step_in
  finish_in))

local macro "prep_seg" : tactic => `(tactic|
  simp only [evalSegCfg, ← one_cons_encLeft, ← zero_cons_encRight, encLeft, encRight,
    lWord, rWord, onesSep0, ListBlank.append, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, zero_cons_default, default_head, default_tail])

theorem step_mAR_1 (L : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mAR L []) (evalSegCfg .mAR (bump1L L) [1]) := by
  prep_seg; execute_in_3

theorem step_mAR_2 (Rt : List ℕ) :
    ReachesIn target_tm 2 (evalSegCfg .mAR [] (0 :: Rt)) (evalSegCfg .mEL [] (0 :: push0R Rt)) := by
  prep_seg; execute_in_2

theorem step_mAR_3 (lt2 Rt : List ℕ) :
    ReachesIn target_tm 4 (evalSegCfg .mAR (0 :: lt2) (0 :: Rt))
      (evalSegCfg .mA0R (bump1L lt2) (push0R Rt)) := by
  prep_seg; execute_in_4

theorem step_mAR_4 (lt2 Rt : List ℕ) :
    ReachesIn target_tm 2 (evalSegCfg .mAR (1 :: lt2) (0 :: Rt))
      (evalSegCfg .mEL (0 :: lt2) (push0R (push0R Rt))) := by
  prep_seg; execute_in_2

theorem step_mAR_5 (l3 : ℕ) (lt2 Rt : List ℕ) :
    ReachesIn target_tm 2 (evalSegCfg .mAR ((l3 + 2) :: lt2) (0 :: Rt))
      (evalSegCfg .mEL ((l3 + 1) :: lt2) (push0R (push0R Rt))) := by
  prep_seg; execute_in_2

theorem step_mAR_6 (L : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mAR L [1])
      (evalSegCfg .mEL (bump1L (bump1L L)) [0]) := by
  prep_seg; execute_in_3

theorem step_mAR_7 (L rt3 : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mAR L (1 :: 0 :: rt3))
      (evalSegCfg .mEL (bump1L (bump1L L)) (push0R rt3)) := by
  prep_seg; execute_in_3

theorem step_mAR_8 (L : List ℕ) (r3 : ℕ) (rt3 : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mAR L (1 :: (r3 + 1) :: rt3))
      (evalSegCfg .mEL (bump1L (bump1L L)) (0 :: r3 :: rt3)) := by
  prep_seg; execute_in_3

theorem step_mAR_2_loop (L Rt : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mAR L (2 :: Rt))
      (evalSegCfg .mAR (0 :: bump1L L) Rt) := by
  prep_seg; execute_in_3

theorem step_mAR_9 (L : List ℕ) (r3 : ℕ) (Rt : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mAR L ((r3 + 3) :: Rt))
      (evalSegCfg .mAR (bump1L L) (1 :: r3 :: Rt)) := by
  prep_seg; execute_in_3

theorem step_mA0R_10 (L : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mA0R L []) (evalSegCfg .mAR (0 :: L) [1]) := by
  prep_seg; execute_in_3

theorem step_mA0R_0 (L rt1 : List ℕ) :
    ReachesIn target_tm 2 (evalSegCfg .mA0R L (0 :: rt1))
      (evalSegCfg .mEL L (0 :: push0R rt1)) := by
  rcases L with _ | ⟨_ | l2, lt2⟩ <;> (prep_seg; execute_in_2)

theorem step_mA0R_14 (L : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mA0R L [1]) (evalSegCfg .mEL (1 :: L) [0]) := by
  prep_seg; execute_in_3

theorem step_mA0R_15 (L rt3 : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mA0R L (1 :: 0 :: rt3))
      (evalSegCfg .mEL (1 :: L) (push0R rt3)) := by
  prep_seg; execute_in_3

theorem step_mA0R_16 (L : List ℕ) (r3 : ℕ) (rt3 : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mA0R L (1 :: (r3 + 1) :: rt3))
      (evalSegCfg .mEL (1 :: L) (0 :: r3 :: rt3)) := by
  prep_seg; execute_in_3

theorem step_mA0R_2 (L rt1 : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mA0R L (2 :: rt1))
      (evalSegCfg .mAR (0 :: 0 :: L) rt1) := by
  rcases rt1 with _ | ⟨_ | r4, rt4⟩ <;> (prep_seg; execute_in_3)

theorem step_mA0R_20 (L : List ℕ) (r3 : ℕ) (rt1 : List ℕ) :
    ReachesIn target_tm 3 (evalSegCfg .mA0R L ((r3 + 3) :: rt1))
      (evalSegCfg .mAR (0 :: L) (1 :: r3 :: rt1)) := by
  prep_seg; execute_in_3

theorem step_mEL_21 :
    ReachesIn target_tm 2 (evalSegCfg .mEL [] []) (evalSegCfg .mA0R [0] []) := by
  prep_seg; execute_in_2

theorem step_mEL_pos (r2 : ℕ) (rt2 : List ℕ) :
    ReachesIn target_tm 2 (evalSegCfg .mEL [] ((r2 + 1) :: rt2))
      (evalSegCfg .mA0R [0] (r2 :: rt2)) := by
  rcases r2 with _ | r3 <;> (prep_seg; execute_in_2)

theorem step_mEL_25 (lt1 R : List ℕ) :
    ReachesIn target_tm 1 (evalSegCfg .mEL (0 :: lt1) R)
      (evalSegCfg .mAR lt1 (push0R (push0R R))) := by
  prep_seg; execute_in_1

theorem step_mEL_26 (lt1 R : List ℕ) :
    ReachesIn target_tm 1 (evalSegCfg .mEL (1 :: lt1) R)
      (evalSegCfg .mA0R lt1 (0 :: push0R R)) := by
  prep_seg; execute_in_1

theorem step_mEL_27 (l2 : ℕ) (lt1 R : List ℕ) :
    ReachesIn target_tm 1 (evalSegCfg .mEL ((l2 + 2) :: lt1) R)
      (evalSegCfg .mAR (l2 :: lt1) (0 :: push0R R)) := by
  prep_seg; execute_in_1

def stepMacroWithCost : SegMode → List ℕ → List ℕ → Option (SegState × ℕ)
  | .mAR, L, [] => some ((.mAR, bump1L L, [1]), 3)
  | .mAR, [], 0 :: Rt => some ((.mEL, [], 0 :: push0R Rt), 2)
  | .mAR, 0 :: lt2, 0 :: Rt => some ((.mA0R, bump1L lt2, push0R Rt), 4)
  | .mAR, 1 :: lt2, 0 :: Rt => some ((.mEL, 0 :: lt2, push0R (push0R Rt)), 2)
  | .mAR, (l3 + 2) :: lt2, 0 :: Rt => some ((.mEL, (l3 + 1) :: lt2, push0R (push0R Rt)), 2)
  | .mAR, L, [1] => some ((.mEL, bump1L (bump1L L), [0]), 3)
  | .mAR, L, 1 :: 0 :: rt3 => some ((.mEL, bump1L (bump1L L), push0R rt3), 3)
  | .mAR, L, 1 :: (r3 + 1) :: rt3 => some ((.mEL, bump1L (bump1L L), 0 :: r3 :: rt3), 3)
  | .mAR, L, 2 :: Rt => some ((.mAR, 0 :: bump1L L, Rt), 3)
  | .mAR, L, (r3 + 3) :: Rt => some ((.mAR, bump1L L, 1 :: r3 :: Rt), 3)
  | .mA0R, L, [] => some ((.mAR, 0 :: L, [1]), 3)
  | .mA0R, L, 0 :: rt1 => some ((.mEL, L, 0 :: push0R rt1), 2)
  | .mA0R, L, [1] => some ((.mEL, 1 :: L, [0]), 3)
  | .mA0R, L, 1 :: 0 :: rt3 => some ((.mEL, 1 :: L, push0R rt3), 3)
  | .mA0R, L, 1 :: (r3 + 1) :: rt3 => some ((.mEL, 1 :: L, 0 :: r3 :: rt3), 3)
  | .mA0R, L, 2 :: rt1 => some ((.mAR, 0 :: 0 :: L, rt1), 3)
  | .mA0R, L, (r3 + 3) :: rt1 => some ((.mAR, 0 :: L, 1 :: r3 :: rt1), 3)
  | .mEL, [], [] => some ((.mA0R, [0], []), 2)
  | .mEL, [], 0 :: _ => none
  | .mEL, [], (r2 + 1) :: rt2 => some ((.mA0R, [0], r2 :: rt2), 2)
  | .mEL, 0 :: lt1, R => some ((.mAR, lt1, push0R (push0R R)), 1)
  | .mEL, 1 :: lt1, R => some ((.mA0R, lt1, 0 :: push0R R), 1)
  | .mEL, (l2 + 2) :: lt1, R => some ((.mAR, l2 :: lt1, 0 :: push0R R), 1)

theorem stepMacro_sound (m : SegMode) (L R : List ℕ) (s' : SegState) (k : ℕ)
    (h : stepMacroWithCost m L R = some (s', k)) :
    0 < k ∧ ReachesIn target_tm k (evalSegCfg m L R) (evalSegCfg s'.1 s'.2.1 s'.2.2) := by
  cases m with
  | mAR =>
    rcases R with _ | ⟨_ | _ | _ | r3, Rt⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_1 L⟩
    · rcases L with _ | ⟨_ | _ | l3, lt2⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_2 Rt⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_3 lt2 Rt⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_4 lt2 Rt⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_5 l3 lt2 Rt⟩
    · rcases Rt with _ | ⟨_ | r3, rt3⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_6 L⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_7 L rt3⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_8 L r3 rt3⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_2_loop L Rt⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mAR_9 L r3 Rt⟩
  | mA0R =>
    rcases R with _ | ⟨_ | _ | _ | r3, rt1⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_10 L⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_0 L rt1⟩
    · rcases rt1 with _ | ⟨_ | r3, rt3⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_14 L⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_15 L rt3⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_16 L r3
          rt3⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_2 L rt1⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mA0R_20 L r3 rt1⟩
  | mEL =>
    rcases L with _ | ⟨_ | _ | l2, lt1⟩
    · rcases R with _ | ⟨_ | r2, rt2⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mEL_21⟩
      · cases h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mEL_pos r2 rt2⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mEL_25 lt1 R⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mEL_26 lt1 R⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by omega, step_mEL_27 l2 lt1 R⟩

def runMacro : ℕ → SegState → Option (SegState × ℕ)
  | 0, s => some (s, 0)
  | n + 1, (m, L, R) =>
    match stepMacroWithCost m L R with
    | none => none
    | some (s₁, c₁) =>
      match runMacro n s₁ with
      | none => none
      | some (s₂, c₂) => some (s₂, c₁ + c₂)

theorem runMacro_sound : ∀ (n : ℕ) (s s' : SegState) (k : ℕ),
    runMacro n s = some (s', k) →
    ReachesIn target_tm k (evalSegCfg s.1 s.2.1 s.2.2) (evalSegCfg s'.1 s'.2.1 s'.2.2)
  | 0, s, s', k, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ReachesIn.zero _ _
  | n + 1, (m, L, R), s', k, h => by
    unfold runMacro at h
    rcases h₁ : stepMacroWithCost m L R with _ | ⟨s₁, c₁⟩
    · rw [h₁] at h; cases h
    · rw [h₁] at h
      dsimp only at h
      rcases h₂ : runMacro n s₁ with _ | ⟨s₂, c₂⟩
      · rw [h₂] at h; cases h
      · rw [h₂] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ReachesIn.trans (stepMacro_sound m L R s₁ c₁ h₁).2 (runMacro_sound n s₁ s₂ c₂ h₂)

theorem rep_succ_append (n w : ℕ) (xs : List ℕ) :
    List.replicate (n + 1) w ++ xs = w :: (List.replicate n w ++ xs) := by
  rw [List.replicate_succ, List.cons_append]

theorem runMacro_to_tm (n : ℕ) {k : ℕ} {m₁ m₂ : SegMode} {L₁ R₁ L₂ R₂ : List ℕ}
    (h : runMacro n (m₁, L₁, R₁) = some ((m₂, L₂, R₂), k)) :
    ReachesIn target_tm k (evalSegCfg m₁ L₁ R₁) (evalSegCfg m₂ L₂ R₂) :=
  runMacro_sound n (m₁, L₁, R₁) (m₂, L₂, R₂) k h

def D (a : ℕ) : List ℕ := 0 :: (List.replicate a 1 ++ [0])
def E (i : ℕ) : List ℕ := 0 :: 0 :: (List.replicate i 1 ++ [0])

theorem seg_desc_run (a : ℕ) : ∀ (L R : List ℕ),
    ReachesIn target_tm (3 * (a + 1))
      (evalSegCfg .mAR L (List.replicate (a + 1) 2 ++ R))
      (evalSegCfg .mAR (0 :: (List.replicate a 1 ++ bump1L L)) R) := by
  induction a with
  | zero =>
    intro L R
    simp only [Nat.zero_add, Nat.mul_one, List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append]
    exact step_mAR_2_loop L R
  | succ a ih =>
    intro L R
    have hrep : List.replicate (a + 1 + 1) 2 ++ R = List.replicate (a + 1) 2 ++ (2 :: R) := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    rw [hrep]
    refine reachesIn_cast (m := 3 * (a + 1) + 3) ?_ (by omega)
    refine ReachesIn.trans (ih L (2 :: R)) ?_
    have hstep := step_mAR_2_loop (0 :: (List.replicate a 1 ++ bump1L L)) R
    simpa only [bump1L, List.replicate_succ, List.cons_append] using hstep

theorem seg_orbit_W3 (k : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 3
      (evalSegCfg .mA0R (1 :: L) (0 :: (k + 1) :: R))
      (evalSegCfg .mA0R L (0 :: 1 :: (k + 2) :: R)) := by
  apply runMacro_to_tm 2; rfl

theorem seg_W3_run (i : ℕ) : ∀ (kv : ℕ) (Lt Rt : List ℕ),
    ReachesIn target_tm (3 * (i + 1))
      (evalSegCfg .mA0R (List.replicate (i + 1) 1 ++ Lt) (0 :: (kv + 1) :: Rt))
      (evalSegCfg .mA0R Lt (0 :: 1 :: (List.replicate i 2 ++ (kv + 2) :: Rt))) := by
  induction i with
  | zero =>
    intro kv Lt Rt
    simp only [Nat.zero_add, Nat.mul_one, List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append]
    exact seg_orbit_W3 kv Lt Rt
  | succ i ih =>
    intro kv Lt Rt
    rw [List.replicate_succ, List.cons_append]
    refine reachesIn_cast (m := 3 + 3 * (i + 1)) ?_ (by omega)
    refine ReachesIn.trans (seg_orbit_W3 kv (List.replicate (i + 1) 1 ++ Lt) Rt) ?_
    have h2 := ih 0 Lt ((kv + 2) :: Rt)
    simp only [Nat.zero_add] at h2
    have hrep : List.replicate i 2 ++ 2 :: (kv + 2) :: Rt =
        List.replicate (i + 1) 2 ++ (kv + 2) :: Rt := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    rwa [hrep] at h2

theorem seg_orbit_T (i : ℕ) (Rt : List ℕ) :
    ReachesIn target_tm 18
      (evalSegCfg .mAR (E i) (1 :: 1 :: 1 :: Rt))
      (evalSegCfg .mAR (E (i + 2)) Rt) := by
  have h6 : ReachesIn target_tm 18
      (evalSegCfg .mAR (E i) (1 :: 1 :: 1 :: Rt))
      (evalSegCfg .mAR (0 :: 0 :: 1 :: 1 :: (List.replicate i 1 ++ [0])) Rt) := by
    unfold E
    apply runMacro_to_tm 6; rfl
  have hE : (0 : ℕ) :: 0 :: 1 :: 1 :: (List.replicate i 1 ++ [0]) = E (i + 2) := by
    unfold E
    have hi : i + 2 = 2 + i := by omega
    rw [hi, List.replicate_add]
    rfl
  rwa [hE] at h6

theorem seg_T_run (n : ℕ) : ∀ (i : ℕ) (Rt : List ℕ),
    ReachesIn target_tm (18 * n)
      (evalSegCfg .mAR (E i) (List.replicate (3 * n) 1 ++ Rt))
      (evalSegCfg .mAR (E (i + 2 * n)) Rt) := by
  induction n with
  | zero =>
    intro i Rt
    simp only [Nat.mul_zero, Nat.add_zero, List.replicate_zero, List.nil_append]
    exact ReachesIn.zero _ _
  | succ n ih =>
    intro i Rt
    have hrep : List.replicate (3 * (n + 1)) 1 ++ Rt =
        1 :: 1 :: 1 :: (List.replicate (3 * n) 1 ++ Rt) := by
      have h3 : 3 * (n + 1) = 3 + 3 * n := by omega
      rw [h3, List.replicate_add]
      rfl
    rw [hrep]
    refine reachesIn_cast (m := 18 + 18 * n) ?_ (by omega)
    refine ReachesIn.trans (seg_orbit_T i (List.replicate (3 * n) 1 ++ Rt)) ?_
    have h2 := ih (i + 2) Rt
    have hidx : i + 2 + 2 * n = i + 2 * (n + 1) := by omega
    rwa [hidx] at h2

theorem seg_orbit_W0 (R : List ℕ) :
    ReachesIn target_tm 20
      (evalSegCfg .mAR (D 0) (5 :: R))
      (evalSegCfg .mAR [] (5 :: 1 :: 1 :: R)) := by
  unfold D
  apply runMacro_to_tm 10; rfl

theorem seg_orbit_W1 (L R : List ℕ) :
    ReachesIn target_tm 10
      (evalSegCfg .mAR (0 :: 1 :: L) (5 :: R))
      (evalSegCfg .mAR (1 :: L) (5 :: 1 :: R)) := by
  apply runMacro_to_tm 5; rfl

theorem seg_orbit_W2 (L R : List ℕ) :
    ReachesIn target_tm 10
      (evalSegCfg .mAR (1 :: L) (5 :: R))
      (evalSegCfg .mA0R L (0 :: 4 :: 1 :: R)) := by
  apply runMacro_to_tm 5; rfl

theorem seg_orbit_W4 (k : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 3
      (evalSegCfg .mA0R (0 :: L) (0 :: (k + 1) :: R))
      (evalSegCfg .mAR L (2 :: (k + 2) :: R)) := by
  apply runMacro_to_tm 2; rfl

theorem seg_walk (a : ℕ) (R : List ℕ) :
    ReachesIn target_tm (3 * a + 20)
      (evalSegCfg .mAR (D a) (5 :: R))
      (evalSegCfg .mAR [] (List.replicate a 2 ++ 5 :: 1 :: 1 :: R)) := by
  rcases a with _ | _ | i
  · exact seg_orbit_W0 R
  · refine reachesIn_cast (m := 10 + (10 + 3)) ?_ (by omega)
    have hD : D 1 = [0, 1, 0] := rfl
    rw [hD]
    exact ReachesIn.trans (seg_orbit_W1 [0] R)
      (ReachesIn.trans (seg_orbit_W2 [0] (1 :: R))
        (seg_orbit_W4 3 [] (1 :: 1 :: R)))
  · refine reachesIn_cast (m := 10 + (10 + (3 * (i + 1) + 3))) ?_ (by omega)
    have hD : D (i + 2) = 0 :: 1 :: (List.replicate (i + 1) 1 ++ [0]) := by
      unfold D
      rw [List.replicate_succ, List.cons_append]
    rw [hD]
    refine ReachesIn.trans (seg_orbit_W1 (List.replicate (i + 1) 1 ++ [0]) R) ?_
    refine ReachesIn.trans (seg_orbit_W2 (List.replicate (i + 1) 1 ++ [0]) (1 :: R)) ?_
    refine ReachesIn.trans (seg_W3_run i 3 [0] (1 :: 1 :: R)) ?_
    have h4 := seg_orbit_W4 0 [] (List.replicate i 2 ++ 5 :: 1 :: 1 :: R)
    have hrep : (2 : ℕ) :: 2 :: (List.replicate i 2 ++ 5 :: 1 :: 1 :: R) =
        List.replicate (i + 2) 2 ++ 5 :: 1 :: 1 :: R := by
      have hi : i + 2 = 2 + i := by omega
      rw [hi, List.replicate_add]
      rfl
    rwa [hrep] at h4

theorem seg_sweep (a : ℕ) (R : List ℕ) :
    ReachesIn target_tm (6 * a + 23)
      (evalSegCfg .mAR [] (List.replicate (a + 1) 2 ++ 5 :: R))
      (evalSegCfg .mAR [] (List.replicate a 2 ++ 5 :: 1 :: 1 :: R)) := by
  refine reachesIn_cast (m := 3 * (a + 1) + (3 * a + 20)) ?_ (by omega)
  exact ReachesIn.trans (seg_desc_run a [] (5 :: R)) (seg_walk a R)

/-! ### Level-4 quadratic counter drain, sea entry, and closed-form Collatz era steps -/

theorem seg_drain (a : ℕ) : ∀ (R : List ℕ),
    ReachesIn target_tm (3 * a * a + 20 * a)
      (evalSegCfg .mAR [] (List.replicate a 2 ++ 5 :: R))
      (evalSegCfg .mAR [] (5 :: (List.replicate (2 * a) 1 ++ R))) := by
  induction a with
  | zero =>
    intro R
    simp only [Nat.mul_zero, Nat.add_zero, List.replicate_zero, List.nil_append]
    exact ReachesIn.zero _ _
  | succ a ih =>
    intro R
    refine reachesIn_cast (m := (6 * a + 23) + (3 * a * a + 20 * a)) ?_ ?_
    · refine ReachesIn.trans (seg_sweep a R) ?_
      have h2 := ih (1 :: 1 :: R)
      have hrep : List.replicate (2 * a) 1 ++ 1 :: 1 :: R =
          List.replicate (2 * (a + 1)) 1 ++ R := by
        have h2a : 2 * (a + 1) = 2 * a + 1 + 1 := by omega
        rw [h2a, List.replicate_succ', List.replicate_succ', List.append_assoc, List.append_assoc]
        rfl
      rwa [hrep] at h2
    · ring

theorem seg_orbit_I (R : List ℕ) :
    ReachesIn target_tm 14
      (evalSegCfg .mAR [] (5 :: 1 :: R))
      (evalSegCfg .mAR (E 0) (1 :: 1 :: R)) := by
  unfold E
  apply runMacro_to_tm 5; rfl

theorem seg_orbit_E0 (j : ℕ) :
    ReachesIn target_tm 10
      (evalSegCfg .mAR (E j) [])
      (evalSegCfg .mAR (D j) [5]) := by
  unfold E D
  apply runMacro_to_tm 5; rfl

theorem seg_orbit_E1 (j : ℕ) :
    ReachesIn target_tm 21
      (evalSegCfg .mAR (E j) [1])
      (evalSegCfg .mAR (D (j + 1)) [5]) := by
  refine reachesIn_cast (m := 11 + 10) ?_ (by omega)
  have h4 : ReachesIn target_tm 11
      (evalSegCfg .mAR (E j) [1])
      (evalSegCfg .mAR (E (j + 1)) []) := by
    unfold E
    rw [rep_succ_append j 1]
    apply runMacro_to_tm 4; rfl
  exact ReachesIn.trans h4 (seg_orbit_E0 (j + 1))

theorem seg_sea_enter (b0 : ℕ) (Rt : List ℕ) :
    ReachesIn target_tm (14 + 18 * ((b0 + 2) / 3))
      (evalSegCfg .mAR [] (5 :: (List.replicate (b0 + 1) 1 ++ Rt)))
      (evalSegCfg .mAR (E (2 * ((b0 + 2) / 3))) (List.replicate ((b0 + 2) % 3) 1 ++ Rt)) := by
  rw [List.replicate_succ, List.cons_append]
  refine ReachesIn.trans (seg_orbit_I (List.replicate b0 1 ++ Rt)) ?_
  have hsea : (1 : ℕ) :: 1 :: (List.replicate b0 1 ++ Rt) =
      List.replicate (3 * ((b0 + 2) / 3)) 1 ++ (List.replicate ((b0 + 2) % 3) 1 ++ Rt) := by
    change List.replicate 2 1 ++ (List.replicate b0 1 ++ Rt) = _
    rw [← List.append_assoc, ← List.replicate_add, ← List.append_assoc, ← List.replicate_add]
    exact congrArg (fun m => List.replicate m 1 ++ Rt) (by omega)
  rw [hsea]
  have hT := seg_T_run ((b0 + 2) / 3) 0 (List.replicate ((b0 + 2) % 3) 1 ++ Rt)
  rwa [Nat.zero_add] at hT

theorem seg_era_mod0 (k : ℕ) :
    ReachesIn target_tm (12 * k * k + 100 * k + 169)
      (evalSegCfg .mAR [] (5 :: List.replicate (3 * k + 3) 1))
      (evalSegCfg .mAR [] (5 :: List.replicate (4 * k + 8) 1)) := by
  have hlen : 3 * k + 3 = (3 * k + 2) + 1 := by omega
  rw [hlen, List.replicate_succ]
  refine reachesIn_cast
    (m := 14 + (18 * (k + 1) + (21 + ((3 * (2 * k + 3) + 20) +
      (3 * (2 * k + 3) * (2 * k + 3) + 20 * (2 * k + 3)))))) ?_ ?_
  · refine ReachesIn.trans (seg_orbit_I (List.replicate (3 * k + 2) 1)) ?_
    have hsea : (1 : ℕ) :: 1 :: List.replicate (3 * k + 2) 1 =
        List.replicate (3 * (k + 1)) 1 ++ [1] := by
      change List.replicate 2 1 ++ List.replicate (3 * k + 2) 1 =
        List.replicate (3 * (k + 1)) 1 ++ List.replicate 1 1
      rw [← List.replicate_add, ← List.replicate_add]
      have hk : 2 + (3 * k + 2) = 3 * (k + 1) + 1 := by omega
      rw [hk]
    rw [hsea]
    have hT := seg_T_run (k + 1) 0 [1]
    rw [Nat.zero_add] at hT
    refine ReachesIn.trans hT ?_
    have hE1 := seg_orbit_E1 (2 * (k + 1))
    have hj : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [hj] at hE1
    refine ReachesIn.trans hE1 ?_
    refine ReachesIn.trans (seg_walk (2 * k + 3) []) ?_
    have hd := seg_drain (2 * k + 3) [1, 1]
    have hfin : List.replicate (2 * (2 * k + 3)) 1 ++ [1, 1] =
        List.replicate (4 * k + 8) 1 := by
      change List.replicate (2 * (2 * k + 3)) 1 ++ List.replicate 2 1 = _
      rw [← List.replicate_add]
      have hidx : 2 * (2 * k + 3) + 2 = 4 * k + 8 := by omega
      rw [hidx]
    rwa [hfin] at hd
  · ring

theorem seg_era_mod2 (k : ℕ) :
    ReachesIn target_tm (12 * k * k + 88 * k + 120)
      (evalSegCfg .mAR [] (5 :: List.replicate (3 * k + 2) 1))
      (evalSegCfg .mAR [] (5 :: List.replicate (4 * k + 6) 1)) := by
  have hlen : 3 * k + 2 = (3 * k + 1) + 1 := by omega
  rw [hlen, List.replicate_succ]
  refine reachesIn_cast
    (m := 14 + (18 * (k + 1) + (10 + ((3 * (2 * k + 2) + 20) +
      (3 * (2 * k + 2) * (2 * k + 2) + 20 * (2 * k + 2)))))) ?_ ?_
  · refine ReachesIn.trans (seg_orbit_I (List.replicate (3 * k + 1) 1)) ?_
    have hsea : (1 : ℕ) :: 1 :: List.replicate (3 * k + 1) 1 =
        List.replicate (3 * (k + 1)) 1 ++ [] := by
      rw [List.append_nil]
      change List.replicate 2 1 ++ List.replicate (3 * k + 1) 1 = _
      rw [← List.replicate_add]
      have hk : 2 + (3 * k + 1) = 3 * (k + 1) := by omega
      rw [hk]
    rw [hsea]
    have hT := seg_T_run (k + 1) 0 []
    rw [Nat.zero_add] at hT
    refine ReachesIn.trans hT ?_
    have hj : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hj]
    refine ReachesIn.trans (seg_orbit_E0 (2 * k + 2)) ?_
    refine ReachesIn.trans (seg_walk (2 * k + 2) []) ?_
    have hd := seg_drain (2 * k + 2) [1, 1]
    have hfin : List.replicate (2 * (2 * k + 2)) 1 ++ [1, 1] =
        List.replicate (4 * k + 6) 1 := by
      change List.replicate (2 * (2 * k + 2)) 1 ++ List.replicate 2 1 = _
      rw [← List.replicate_add]
      have hidx : 2 * (2 * k + 2) + 2 = 4 * k + 6 := by omega
      rw [hidx]
    rwa [hfin] at hd
  · ring


/-! ## Section 2: Generalized Sweep, Drain, Entry, and Exact One-Shot Macro Lemmas -/

theorem entry_steps : ReachesIn target_tm 3 (init []) (evalSegCfg .mAR [0] [1]) := by
  have h_init : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
      ((default : ListBlank (Fin 2)) {{0}}> (default : ListBlank (Fin 2))) := rfl
  rw [h_init]
  simp only [evalSegCfg, encLeft, encRight, lWord, rWord, onesSep0,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute_in_3

theorem entry_to_b2 :
    ReachesIn target_tm 44 (init []) (evalSegCfg .mAR [] (5 :: List.replicate 2 1)) := by
  refine reachesIn_cast (m := 3 + 41) ?_ (by omega)
  refine ReachesIn.trans entry_steps ?_
  apply runMacro_to_tm 19
  rfl

theorem entry_to_E78 :
    ∃ K : ℕ, ReachesIn target_tm K (init []) (evalSegCfg .mAR (E 78) [1, 1]) := by
  have h1 : ReachesIn target_tm (44 + (12 * 0 * 0 + 88 * 0 + 120))
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 6 1)) :=
    ReachesIn.trans entry_to_b2 (seg_era_mod2 0)
  have h2 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 12 1)) :=
    ReachesIn.trans h1 (seg_era_mod0 1)
  have h3 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 20 1)) :=
    ReachesIn.trans h2 (seg_era_mod0 3)
  have h4 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 30 1)) :=
    ReachesIn.trans h3 (seg_era_mod2 6)
  have h5 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 44 1)) :=
    ReachesIn.trans h4 (seg_era_mod0 9)
  have h6 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 62 1)) :=
    ReachesIn.trans h5 (seg_era_mod2 14)
  have h7 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 86 1)) :=
    ReachesIn.trans h6 (seg_era_mod2 20)
  have h8 : ReachesIn target_tm _
      (init []) (evalSegCfg .mAR [] (5 :: List.replicate 118 1)) :=
    ReachesIn.trans h7 (seg_era_mod2 28)
  have hsea : ReachesIn target_tm (14 + 18 * ((117 + 2) / 3))
      (evalSegCfg .mAR [] (5 :: (List.replicate (117 + 1) 1 ++ [])))
      (evalSegCfg .mAR (E (2 * ((117 + 2) / 3))) (List.replicate ((117 + 2) % 3) 1 ++ [])) :=
    seg_sea_enter 117 []
  simp only [List.append_nil] at hsea
  exact ⟨_, ReachesIn.trans h8 hsea⟩

theorem seg_orbit_W0_gen (t : ℕ) (R : List ℕ) :
    ReachesIn target_tm 20
      (evalSegCfg .mAR (D 0) ((t + 4) :: R))
      (evalSegCfg .mAR [] (5 :: 1 :: t :: R)) := by
  unfold D
  apply runMacro_to_tm 10; rfl

theorem seg_orbit_W1_gen (t : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 10
      (evalSegCfg .mAR (0 :: 1 :: L) ((t + 4) :: R))
      (evalSegCfg .mAR (1 :: L) (5 :: t :: R)) := by
  apply runMacro_to_tm 5; rfl

theorem seg_walk_ge4 (a t : ℕ) (R : List ℕ) :
    ReachesIn target_tm (3 * a + 20)
      (evalSegCfg .mAR (D a) ((t + 4) :: R))
      (evalSegCfg .mAR [] (List.replicate a 2 ++ 5 :: 1 :: t :: R)) := by
  rcases a with _ | _ | i
  · exact seg_orbit_W0_gen t R
  · refine reachesIn_cast (m := 10 + (10 + 3)) ?_ (by omega)
    have hD : D 1 = [0, 1, 0] := rfl
    rw [hD]
    exact ReachesIn.trans (seg_orbit_W1_gen t [0] R)
      (ReachesIn.trans (seg_orbit_W2 [0] (t :: R))
        (seg_orbit_W4 3 [] (1 :: t :: R)))
  · refine reachesIn_cast (m := 10 + (10 + (3 * (i + 1) + 3))) ?_ (by omega)
    have hD : D (i + 2) = 0 :: 1 :: (List.replicate (i + 1) 1 ++ [0]) := by
      unfold D
      rw [List.replicate_succ, List.cons_append]
    rw [hD]
    refine ReachesIn.trans (seg_orbit_W1_gen t (List.replicate (i + 1) 1 ++ [0]) R) ?_
    refine ReachesIn.trans (seg_orbit_W2 (List.replicate (i + 1) 1 ++ [0]) (t :: R)) ?_
    refine ReachesIn.trans (seg_W3_run i 3 [0] (1 :: t :: R)) ?_
    have h4 := seg_orbit_W4 0 [] (List.replicate i 2 ++ 5 :: 1 :: t :: R)
    have hrep : (2 : ℕ) :: 2 :: (List.replicate i 2 ++ 5 :: 1 :: t :: R) =
        List.replicate (i + 2) 2 ++ 5 :: 1 :: t :: R := by
      have hi : i + 2 = 2 + i := by omega
      rw [hi, List.replicate_add]
      rfl
    rwa [hrep] at h4

theorem seg_sweep_ge4 (a t : ℕ) (R : List ℕ) :
    ReachesIn target_tm (6 * a + 23)
      (evalSegCfg .mAR [] (List.replicate (a + 1) 2 ++ (t + 4) :: R))
      (evalSegCfg .mAR [] (List.replicate a 2 ++ 5 :: 1 :: t :: R)) := by
  refine reachesIn_cast (m := 3 * (a + 1) + (3 * a + 20)) ?_ (by omega)
  exact ReachesIn.trans (seg_desc_run a [] ((t + 4) :: R)) (seg_walk_ge4 a t R)

theorem drain_ones_to_2 (m : ℕ) (rs : List ℕ) :
    ReachesIn target_tm (3 * (m + 1) + 3)
      (evalSegCfg .mA0R (List.replicate (m + 1) 1 ++ [0]) (0 :: 1 :: rs))
      (evalSegCfg .mAR [] (List.replicate (m + 3) 2 ++ rs)) := by
  refine ReachesIn.trans (seg_W3_run m 0 [0] rs) ?_
  have hrep1 : List.replicate m 2 ++ 2 :: rs = List.replicate (m + 1) 2 ++ rs := by
    rw [List.replicate_succ', List.append_assoc]; rfl
  rw [hrep1]
  have h4 := seg_orbit_W4 0 [] (List.replicate (m + 1) 2 ++ rs)
  have hrep2 : (2 : ℕ) :: 2 :: (List.replicate (m + 1) 2 ++ rs) =
      List.replicate (m + 3) 2 ++ rs := by
    have h2 : (2 : ℕ) :: 2 :: (List.replicate (m + 1) 2 ++ rs) =
        List.replicate 2 2 ++ (List.replicate (m + 1) 2 ++ rs) := rfl
    rw [h2, ← List.append_assoc, ← List.replicate_add]
    exact congrArg (fun n => List.replicate n 2 ++ rs) (by omega)
  rwa [hrep2] at h4

theorem mEL_shift (d r : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 3
      (evalSegCfg .mEL ((d + 3) :: L) (r :: R))
      (evalSegCfg .mEL (d :: L) ((r + 3) :: R)) := by
  rcases d with _ | d' <;> (apply runMacro_to_tm 2; rfl)

theorem mEL_shift_mul : ∀ (m r0 r : ℕ) (L R : List ℕ),
    ReachesIn target_tm (3 * m)
      (evalSegCfg .mEL ((3 * m + r0) :: L) (r :: R))
      (evalSegCfg .mEL (r0 :: L) ((3 * m + r) :: R))
  | 0, r0, r, L, R => by
    simp only [Nat.mul_zero, Nat.zero_add]
    exact ReachesIn.zero _ _
  | m + 1, r0, r, L, R => by
    have h1 : 3 * (m + 1) + r0 = (3 * m + r0) + 3 := by omega
    rw [h1]
    refine reachesIn_cast (m := 3 + 3 * m) ?_ (by omega)
    refine ReachesIn.trans (mEL_shift (3 * m + r0) r L R) ?_
    have ih := mEL_shift_mul m r0 (r + 3) L R
    have h2 : 3 * m + (r + 3) = 3 * (m + 1) + r := by omega
    rwa [h2] at ih

theorem mEL_d0 (r : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 1
      (evalSegCfg .mEL (0 :: L) (r :: R))
      (evalSegCfg .mAR L ((r + 2) :: R)) := by
  apply runMacro_to_tm 1; rfl

theorem mEL_d1 (r : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 1
      (evalSegCfg .mEL (1 :: L) (r :: R))
      (evalSegCfg .mA0R L (0 :: (r + 1) :: R)) := by
  apply runMacro_to_tm 1; rfl

theorem mEL_d2 (r : ℕ) (L R : List ℕ) :
    ReachesIn target_tm 5
      (evalSegCfg .mEL (2 :: L) (r :: R))
      (evalSegCfg .mA0R (bump1L L) ((r + 2) :: R)) := by
  apply runMacro_to_tm 2; rfl

theorem lem_A_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 40
      (evalSegCfg .mA0R (d :: L) [])
      (evalSegCfg .mEL ((d + 4) :: L) [0, 1, 1]) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 17; rfl)

theorem lem_A_1_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 6
      (evalSegCfg .mA0R (d :: L) [1])
      (evalSegCfg .mEL (d :: L) [0, 2]) := by
  apply runMacro_to_tm 3; rfl

theorem lem_A_1_0_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 6
      (evalSegCfg .mA0R (d :: L) [1, 0])
      (evalSegCfg .mEL (d :: L) [0]) := by
  apply runMacro_to_tm 3; rfl

theorem lem_A_1_0_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 6
      (evalSegCfg .mA0R (d :: L) (1 :: 0 :: x :: y))
      (evalSegCfg .mEL (d :: L) (0 :: (x + 3) :: y)) := by
  apply runMacro_to_tm 3; rfl

theorem lem_A_1_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 6
      (evalSegCfg .mA0R (d :: L) (1 :: (x + 1) :: y))
      (evalSegCfg .mEL (d :: L) (0 :: 2 :: x :: y)) := by
  apply runMacro_to_tm 3; rfl

theorem lem_A_3_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 11
      (evalSegCfg .mA0R (d :: L) [3])
      (evalSegCfg .mA0R ((d + 1) :: L) []) := by
  apply runMacro_to_tm 4; rfl

theorem lem_A_3_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 11
      (evalSegCfg .mA0R (d :: L) (3 :: x :: y))
      (evalSegCfg .mA0R ((d + 1) :: L) ((x + 3) :: y)) := by
  apply runMacro_to_tm 4; rfl

theorem lem_A_ge4 (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 14
      (evalSegCfg .mA0R (d :: L) ((x + 4) :: y))
      (evalSegCfg .mAR (0 :: 0 :: (d + 1) :: L) (x :: y)) := by
  apply runMacro_to_tm 5; rfl

theorem lem_A_7_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 40
      (evalSegCfg .mA0R (d :: L) [7])
      (evalSegCfg .mEL ((d + 4) :: L) [0, 1]) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 17; rfl)

theorem lem_A_7_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 40
      (evalSegCfg .mA0R (d :: L) (7 :: x :: y))
      (evalSegCfg .mEL ((d + 4) :: L) (0 :: 1 :: (x + 2) :: y)) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 17; rfl)

theorem lem_A_ge8 (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 40
      (evalSegCfg .mA0R (d :: L) ((x + 8) :: y))
      (evalSegCfg .mEL ((d + 4) :: L) (0 :: 1 :: 1 :: x :: y)) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 17; rfl)

theorem lem_S_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 16
      (evalSegCfg .mAR (0 :: d :: L) [])
      (evalSegCfg .mEL ((d + 3) :: L) [0, 1]) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 7; rfl)

theorem lem_S_1_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 37
      (evalSegCfg .mAR (0 :: d :: L) [1])
      (evalSegCfg .mEL ((d + 4) :: L) [0, 1, 1]) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 16; rfl)

theorem lem_S_1_0_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 8
      (evalSegCfg .mAR (0 :: d :: L) [1, 0])
      (evalSegCfg .mA0R ((d + 1) :: L) []) := by
  apply runMacro_to_tm 3; rfl

theorem lem_S_1_0_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 8
      (evalSegCfg .mAR (0 :: d :: L) (1 :: 0 :: x :: y))
      (evalSegCfg .mA0R ((d + 1) :: L) ((x + 3) :: y)) := by
  apply runMacro_to_tm 3; rfl

theorem lem_S_1_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 11
      (evalSegCfg .mAR (0 :: d :: L) (1 :: (x + 1) :: y))
      (evalSegCfg .mAR (0 :: 0 :: (d + 1) :: L) (x :: y)) := by
  apply runMacro_to_tm 4; rfl

theorem lem_S_1_1 (d : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 15
      (evalSegCfg .mAR (0 :: d :: L) (1 :: 1 :: y))
      (evalSegCfg .mA0R (1 :: (d + 1) :: L) (push0R y)) := by
  rcases y with _ | ⟨hd, tl⟩ <;> (apply runMacro_to_tm 5; rfl)

theorem lem_S_1_1_1 (d : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 18
      (evalSegCfg .mAR (0 :: d :: L) (1 :: 1 :: 1 :: y))
      (evalSegCfg .mAR (0 :: 0 :: 1 :: (d + 1) :: L) y) := by
  apply runMacro_to_tm 6; rfl

theorem lem_S_3_nil (d : ℕ) (L : List ℕ) :
    ReachesIn target_tm 16
      (evalSegCfg .mAR (0 :: d :: L) [3])
      (evalSegCfg .mEL ((d + 3) :: L) [0]) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 7; rfl)

theorem lem_S_3_pos (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 16
      (evalSegCfg .mAR (0 :: d :: L) (3 :: x :: y))
      (evalSegCfg .mEL ((d + 3) :: L) (0 :: (x + 2) :: y)) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 7; rfl)

theorem lem_S_ge4 (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 16
      (evalSegCfg .mAR (0 :: d :: L) ((x + 4) :: y))
      (evalSegCfg .mEL ((d + 3) :: L) (0 :: 1 :: x :: y)) := by
  rcases d with _ | _ | d' <;> (apply runMacro_to_tm 7; rfl)

theorem lem_MAR_ge5 (d x : ℕ) (L y : List ℕ) :
    ReachesIn target_tm 6
      (evalSegCfg .mAR (d :: L) ((x + 5) :: y))
      (evalSegCfg .mEL ((d + 3) :: L) (0 :: (x + 1) :: y)) := by
  apply runMacro_to_tm 2; rfl

theorem lem_BUMP_push2 (X y : List ℕ) :
    ReachesIn target_tm 11
      (evalSegCfg .mAR (0 :: 0 :: X) (1 :: 2 :: y))
      (evalSegCfg .mAR (0 :: 0 :: 1 :: X) (1 :: y)) := by
  apply runMacro_to_tm 4; rfl

theorem lem_BUMP_push2_run : ∀ (c : ℕ) (X y : List ℕ),
    ReachesIn target_tm (11 * c)
      (evalSegCfg .mAR (0 :: 0 :: X) (1 :: (List.replicate c 2 ++ y)))
      (evalSegCfg .mAR (0 :: 0 :: (List.replicate c 1 ++ X)) (1 :: y))
  | 0, X, y => by
    simp only [Nat.mul_zero, List.replicate_zero, List.nil_append]
    exact ReachesIn.zero _ _
  | c + 1, X, y => by
    rw [List.replicate_succ, List.cons_append]
    refine reachesIn_cast (m := 11 + 11 * c) ?_ (by omega)
    refine ReachesIn.trans (lem_BUMP_push2 X (List.replicate c 2 ++ y)) ?_
    have ih := lem_BUMP_push2_run c (1 :: X) y
    have hrep : List.replicate c 1 ++ 1 :: X = List.replicate (c + 1) 1 ++ X := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    rwa [hrep] at ih

/-! ## Section 3: Constructive Fuel-Induction Combinators (`SafeFrom`) -/

def SafeFrom (P : SegState → Prop) (cfg : Cfg (Fin 2) (Fin 6)) (fuel : ℕ) : Prop :=
  (∃ cfg', ReachesIn target_tm fuel cfg cfg') ∨
  (∃ m s', 1 ≤ m ∧ m ≤ fuel ∧ ReachesIn target_tm m cfg (evalSegCfg s'.1 s'.2.1 s'.2.2) ∧ P s')

theorem reachesIn_prefix {k n : ℕ} {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : n ≤ k) (hr : ReachesIn target_tm k c₁ c₂) :
    ∃ c', ReachesIn target_tm n c₁ c' := by
  have hk : k = n + (k - n) := by omega
  rw [ReachesIn, hk, multiStep_add] at hr
  rcases hmn : multiStep target_tm c₁ n with _ | c'
  · rw [hmn, Option.bind_none] at hr; cases hr
  · exact ⟨c', hmn⟩

theorem SafeFrom.of_done {P : SegState → Prop} {cfg : Cfg (Fin 2) (Fin 6)} {fuel m : ℕ} {s' :
  SegState}
    (hm1 : 1 ≤ m) (hreach : ReachesIn target_tm m cfg (evalSegCfg s'.1 s'.2.1 s'.2.2)) (hp : P s') :
    SafeFrom P cfg fuel := by
  rcases Nat.lt_or_ge fuel m with hlt | hge
  · exact Or.inl (reachesIn_prefix (by omega) hreach)
  · exact Or.inr ⟨m, s', hm1, hge, hreach, hp⟩

theorem SafeFrom.step_prefix {P : SegState → Prop} {cfg₁ cfg₂ : Cfg (Fin 2) (Fin 6)} {fuel k : ℕ}
    (hk : 1 ≤ k) (hreach : ReachesIn target_tm k cfg₁ cfg₂)
    (hnext : k ≤ fuel → SafeFrom P cfg₂ (fuel - k)) :
    SafeFrom P cfg₁ fuel := by
  rcases Nat.lt_or_ge fuel k with hlt | hge
  · exact Or.inl (reachesIn_prefix (by omega) hreach)
  · rcases hnext hge with ⟨c', hc'⟩ | ⟨m, s', hm1, hmle, hrm, hp⟩
    · exact Or.inl ⟨c', reachesIn_cast (ReachesIn.trans hreach hc') (by omega)⟩
    · exact Or.inr ⟨k + m, s', by omega, by omega, ReachesIn.trans hreach hrm, hp⟩

theorem SafeFrom.bind {P Q : SegState → Prop} {cfg : Cfg (Fin 2) (Fin 6)} {fuel : ℕ}
    (h1 : SafeFrom P cfg fuel)
    (h2 : ∀ m s', 1 ≤ m → m ≤ fuel → P s' → SafeFrom Q (evalSegCfg s'.1 s'.2.1 s'.2.2) (fuel - m)) :
    SafeFrom Q cfg fuel := by
  rcases h1 with hc | ⟨m, s', hm1, hmle, hrm, hp⟩
  · exact Or.inl hc
  · rcases h2 m s' hm1 hmle hp with ⟨c', hc'⟩ | ⟨m₂, s'', hm2, hm2le, hrm2, hq⟩
    · exact Or.inl ⟨c', reachesIn_cast (ReachesIn.trans hrm hc') (by omega)⟩
    · exact Or.inr ⟨m + m₂, s'', by omega, by omega, ReachesIn.trans hrm hrm2, hq⟩

theorem SafeFrom.weaken {P Q : SegState → Prop} {cfg : Cfg (Fin 2) (Fin 6)} {fuel : ℕ}
    (h : SafeFrom P cfg fuel) (himp : ∀ s, P s → Q s) :
    SafeFrom Q cfg fuel := by
  rcases h with hc | ⟨m, s', hm1, hmle, hrm, hp⟩
  · exact Or.inl hc
  · exact Or.inr ⟨m, s', hm1, hmle, hrm, himp s' hp⟩

theorem isNotHalt_of_reach_and_safe {K : ℕ} {cfg₀ : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachesIn target_tm K (init []) cfg₀)
    (hsafe : ∀ n : ℕ, ∃ c', ReachesIn target_tm n cfg₀ c') :
    IsNotHalt target_tm := by
  intro cfg ⟨n, hn⟩
  have hstep : ∃ c', ReachesIn target_tm (n + 1) (init []) c' := by
    rcases Nat.lt_or_ge (n + 1) K with hlt | hge
    · exact reachesIn_prefix (by omega) h0
    · obtain ⟨c', hc'⟩ := hsafe (n + 1 - K)
      exact ⟨c', reachesIn_cast (ReachesIn.trans h0 hc') (by omega)⟩
  obtain ⟨c', hc'⟩ := hstep
  rw [ReachesIn, multiStep_add target_tm (init []) n 1, hn, Option.bind_some, multiStep_one] at hc'
  rw [hc']
  rfl

/-! ## Section 4: Abstract Domain `RT`, Pure-Bool Equality, and 578-Node Certificate -/

inductive TailAtom : Type
  | nil | ge5 | ge3 | any

inductive RunLen : Type
  | c1 | c2 | c3 | c4

def RunLen.toNat : RunLen → Nat
  | .c1 => 1 | .c2 => 2 | .c3 => 3 | .c4 => 4

inductive RT : Type
  | nil | z | h3 | h4 | h5 | h6 | ge7 | ge5 | ge3 | ge2 | pos | any
  | r1 (c : RunLen) (b : TailAtom)
  | r1p (b : TailAtom)
  | r2 (c : RunLen) (b : TailAtom)
  | r2p (b : TailAtom)

def eqTail : TailAtom → TailAtom → Bool
  | .nil, .nil => true | .ge5, .ge5 => true | .ge3, .ge3 => true | .any, .any => true
  | _, _ => false

def eqLen : RunLen → RunLen → Bool
  | .c1, .c1 => true | .c2, .c2 => true | .c3, .c3 => true | .c4, .c4 => true
  | _, _ => false

def eqRT : RT → RT → Bool
  | .nil, .nil => true | .z, .z => true | .h3, .h3 => true | .h4, .h4 => true
  | .h5, .h5 => true | .h6, .h6 => true | .ge7, .ge7 => true | .ge5, .ge5 => true
  | .ge3, .ge3 => true | .ge2, .ge2 => true | .pos, .pos => true | .any, .any => true
  | .r1 ca b1, .r1 cb b2 => eqLen ca cb && eqTail b1 b2
  | .r1p b1, .r1p b2 => eqTail b1 b2
  | .r2 ca b1, .r2 cb b2 => eqLen ca cb && eqTail b1 b2
  | .r2p b1, .r2p b2 => eqTail b1 b2
  | _, _ => false

def tailToRT : TailAtom → RT
  | .nil => .nil | .ge5 => .ge5 | .ge3 => .ge3 | .any => .any

def toTail : RT → TailAtom
  | .nil => .nil
  | .h5 | .h6 | .ge7 | .ge5 => .ge5
  | .h3 | .h4 | .ge3 => .ge3
  | _ => .any

def cons1 : RT → RT
  | .r1 .c1 b => .r1 .c2 b
  | .r1 .c2 b => .r1 .c3 b
  | .r1 .c3 b => .r1 .c4 b
  | .r1 .c4 b => .r1p b
  | .r1p b => .r1p b
  | t => .r1 .c1 (toTail t)

def cons2 : RT → RT
  | .r2 .c1 b => .r2 .c2 b
  | .r2 .c2 b => .r2 .c3 b
  | .r2 .c3 b => .r2 .c4 b
  | .r2 .c4 b => .r2p b
  | .r2p b => .r2p b
  | t => .r2 .c1 (toTail t)

def subTail : TailAtom → TailAtom → Bool
  | _, .any => true
  | .nil, .nil => true
  | .ge5, .ge5 | .ge5, .ge3 => true
  | .ge3, .ge3 => true
  | _, _ => false

def clenGt : RunLen → RunLen → Bool
  | .c2, .c1 => true
  | .c3, .c1 | .c3, .c2 => true
  | .c4, .c1 | .c4, .c2 | .c4, .c3 => true
  | _, _ => false

def subRT : RT → RT → Bool
  | _, .any => true
  | .nil, .nil => true
  | .z, .z => true
  | .h3, .h3 | .h3, .ge3 | .h3, .ge2 | .h3, .pos => true
  | .h4, .h4 | .h4, .ge3 | .h4, .ge2 | .h4, .pos => true
  | .h5, .h5 | .h5, .ge5 | .h5, .ge3 | .h5, .ge2 | .h5, .pos => true
  | .h6, .h6 | .h6, .ge5 | .h6, .ge3 | .h6, .ge2 | .h6, .pos => true
  | .ge7, .ge7 | .ge7, .ge5 | .ge7, .ge3 | .ge7, .ge2 | .ge7, .pos => true
  | .ge5, .ge5 | .ge5, .ge3 | .ge5, .ge2 | .ge5, .pos => true
  | .ge3, .ge3 | .ge3, .ge2 | .ge3, .pos => true
  | .ge2, .ge2 | .ge2, .pos => true
  | .pos, .pos => true
  | .r1 _ _, .pos | .r1p _, .pos => true
  | .r2 _ _, .ge2 | .r2 _ _, .pos | .r2p _, .ge2 | .r2p _, .pos => true
  | .r1 ca ba, .r1 cb bb => (eqLen ca cb && subTail ba bb) || (clenGt ca cb && eqTail bb .any)
  | .r1 ca ba, .r1p bb => eqLen ca .c4 && subTail ba bb
  | .r1p _, .r1 _ bb => eqTail bb .any
  | .r1p ba, .r1p bb => subTail ba bb
  | .r2 ca ba, .r2 cb bb => (eqLen ca cb && subTail ba bb) || (clenGt ca cb && eqTail bb .any)
  | .r2 ca ba, .r2p bb => eqLen ca .c4 && subTail ba bb
  | .r2p _, .r2 _ bb => eqTail bb .any
  | .r2p ba, .r2p bb => subTail ba bb
  | _, _ => false

structure ExitBuckets where
  mar0 : List RT
  mar1 : List RT
  mar2 : List RT
  mz0 : List RT
  mz1 : List RT
  mz2 : List RT
  bump0 : List RT
  bump1 : List RT
  bump2 : List RT

def emptyBuckets : ExitBuckets := ⟨[], [], [], [], [], [], [], [], []⟩

inductive NodeSpec : Type
  | a (d : Nat) (rt : RT)
  | s (d : Nat) (rt : RT)
  | s1 (c : Nat) (rt : RT)
  | e (k : Nat) (rt : RT)
  | prop (d : Nat) (sub : Nat)

def eqSpec : NodeSpec → NodeSpec → Bool
  | .a d1 r1, .a d2 r2 => Nat.beq d1 d2 && eqRT r1 r2
  | .s d1 r1, .s d2 r2 => Nat.beq d1 d2 && eqRT r1 r2
  | .s1 c1 r1, .s1 c2 r2 => Nat.beq c1 c2 && eqRT r1 r2
  | .e k1 r1, .e k2 r2 => Nat.beq k1 k2 && eqRT r1 r2
  | .prop d1 s1, .prop d2 s2 => Nat.beq d1 d2 && Nat.beq s1 s2
  | _, _ => false

def capD (d : Nat) : Nat := if Nat.blt d 9 then d else 6 + d % 3
def qCap (q : Nat) : Nat := if Nat.ble 2 q then 2 else q

def memSub (t : RT) : List RT → Bool
  | [] => false
  | x :: xs => subRT t x || memSub t xs

def subList (xs ys : List RT) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => memSub x ys && subList xs' ys

def subsetBkt (src dst : ExitBuckets) : Bool :=
  subList src.mar0 dst.mar0 && subList src.mar1 dst.mar1 && subList src.mar2 dst.mar2 &&
  subList src.mz0 dst.mz0 && subList src.mz1 dst.mz1 && subList src.mz2 dst.mz2 &&
  subList src.bump0 dst.bump0 && subList src.bump1 dst.bump1 && subList src.bump2 dst.bump2

def memElPop (d : Nat) (t : RT) (dst : ExitBuckets) : Bool :=
  let q := qCap (d / 3)
  match d % 3, q with
  | 0, 0 => memSub t dst.mar0
  | 0, 1 => memSub t dst.mar1
  | 0, _ => memSub t dst.mar2
  | 1, 0 => memSub t dst.mz0
  | 1, 1 => memSub t dst.mz1
  | 1, _ => memSub t dst.mz2
  | _, 0 => memSub t dst.bump0
  | _, 1 => memSub t dst.bump1
  | _, _ => memSub t dst.bump2

def numNodes : Nat := 578

noncomputable def getBkt_0_0 : Nat → ExitBuckets
  | 0 => ⟨[], [], [], [], [], [], [], [(.r1 .c1 .any)], []⟩
  | 1 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2
    .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3],
    [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | 2 => ⟨[], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3],
    [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2
    .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3],
    [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any),
    (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2
    .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5),
    (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2
    .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2
    .nil), (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [], [], [], [], [], [], [(.r1 .c2 .nil)], []⟩
  | 6 => ⟨[], [], [], [(.r2 .c1 .any), .ge3, .nil], [], [], [], [], []⟩
  | 7 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2
    .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p
    .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_1 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r1 .c1 .any)], [], [], [], [], [], []⟩
  | 1 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [],
    [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3),
    (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | 2 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [.ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [.ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3],
    [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2
    .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2
    .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [], [(.r1 .c2 .nil)], [], [], [], [], [], []⟩
  | 6 => ⟨[], [], [], [], [], [], [(.r2 .c1 .any), .ge3, .nil], [], []⟩
  | 7 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge3), (.r2 .c1 .nil),
    (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_2 : Nat → ExitBuckets
  | 0 => ⟨[], [], [], [], [], [(.r1 .c1 .any)], [], [], []⟩
  | 1 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [],
    [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [(.r2 .c1 .ge3),
    (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil),
    (.r2 .c2 .any), .ge3]⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [.ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [.ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [], [], [], [], [(.r1 .c2 .nil)], [], [], []⟩
  | 6 => ⟨[], [], [], [], [], [], [], [], [(.r1 .c1 .any)]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [],
    [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [], [(.r1 .c1
    .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_3 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [], [], [], [], [], [], [], [(.r1 .c2 .nil)]⟩
  | 4 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [],
    [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_4 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r1 .c1 .any)], [], [], [], [], [], [], []⟩
  | 1 => ⟨[], [.ge2, .nil], [], [], [], [], [], [], []⟩
  | 2 => ⟨[], [(.r1 .c1 .nil)], [], [], [], [], [], [], []⟩
  | 3 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1 .any), .ge3, .nil], [(.r1 .c1
    .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3),
    (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r1 .c1 .any),
    (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | 4 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2
    .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3],
    [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1 .ge3), (.r2
    .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2
    .c2 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | 5 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2
    .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2
    .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3]⟩
  | 6 => ⟨[], [], [], [], [(.r1 .c2 .any)], [], [], [], []⟩
  | 7 => ⟨[], [], [], [], [(.r1 .c2 .nil)], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_5 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2
    .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5], [(.r1 .c1 .ge3), (.r1 .c2 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5],
    [(.r1 .c1 .ge3), (.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 2 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), .ge3],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [],
    [(.r1 .c1 .ge3), (.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3]⟩
  | 3 => ⟨[], [], [], [.h5], [], [], [], [], []⟩
  | 4 => ⟨[(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any),
    (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2
    .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2
    .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3]⟩
  | 5 => ⟨[.h5], [], [], [], [], [], [], [], []⟩
  | 6 => ⟨[(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r1 .c1 .ge3), (.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3]⟩
  | 7 => ⟨[(.r2 .c1 .ge5)], [], [], [], [], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_6 : Nat → ExitBuckets
  | 0 => ⟨[(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[(.r2 .c2 .ge5)], [], [], [], [], [], [], [], []⟩
  | 2 => ⟨[(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .h5], [(.r1 .c1 .any), .ge3], []⟩
  | 3 => ⟨[(.r2 .c3 .ge5)], [], [], [], [], [], [], [], []⟩
  | 4 => ⟨[(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any),
    .ge3], [], [], [], [], [], [], []⟩
  | 5 => ⟨[], [], [], [], [(.r1 .c1 .any)], [], [], [], []⟩
  | 6 => ⟨[], [], [], [], [.ge2, .nil], [], [], [], []⟩
  | 7 => ⟨[], [], [], [], [(.r1 .c1 .nil)], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_0_7 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2
    .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3],
    [(.r2 .c1 .any), .ge3, .nil], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any),
    .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3]⟩
  | 1 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2
    .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3],
    [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3),
    (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2
    .c2 .any), .ge3]⟩
  | 2 => ⟨[], [], [], [], [], [], [.h5], [], []⟩
  | 3 => ⟨[], [], [], [], [], [], [(.r2 .c1 .ge5)], [], []⟩
  | 4 => ⟨[], [], [], [], [], [], [(.r2 .c2 .ge5)], [], []⟩
  | 5 => ⟨[], [], [], [], [], [], [(.r2 .c3 .ge5)], [], []⟩
  | 6 => ⟨[], [], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5),
    .h5], [(.r1 .c1 .any), .ge3], []⟩
  | 7 => ⟨[], [.h5], [], [], [], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_0 (r : Nat) : ExitBuckets :=
  match r / 8 with
  | 0 => getBkt_0_0 (r % 8)
  | 1 => getBkt_0_1 (r % 8)
  | 2 => getBkt_0_2 (r % 8)
  | 3 => getBkt_0_3 (r % 8)
  | 4 => getBkt_0_4 (r % 8)
  | 5 => getBkt_0_5 (r % 8)
  | 6 => getBkt_0_6 (r % 8)
  | 7 => getBkt_0_7 (r % 8)
  | _ => emptyBuckets
noncomputable def getBkt_1_0 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r2 .c1 .ge5)], [], [], [], [], [], [], []⟩
  | 1 => ⟨[], [(.r2 .c2 .ge5)], [], [], [], [], [], [], []⟩
  | 2 => ⟨[], [(.r2 .c3 .ge5)], [], [], [], [], [], [], []⟩
  | 3 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any),
    .ge3], [], [], [], [], [], []⟩
  | 4 => ⟨[], [], [], [], [.h5], [], [], [], []⟩
  | 5 => ⟨[], [], [], [], [(.r2 .c1 .ge5)], [], [], [], []⟩
  | 6 => ⟨[], [], [], [], [(.r2 .c2 .ge5)], [], [], [], []⟩
  | 7 => ⟨[], [], [], [], [(.r2 .c3 .ge5)], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_1 : Nat → ExitBuckets
  | 0 => ⟨[], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5],
    [(.r1 .c1 .any), .ge3], [], [], []⟩
  | 1 => ⟨[], [], [], [], [], [], [], [.h5], []⟩
  | 2 => ⟨[], [], [], [], [], [], [], [(.r2 .c1 .ge5)], []⟩
  | 3 => ⟨[], [], [], [], [], [], [], [(.r2 .c2 .ge5)], []⟩
  | 4 => ⟨[], [], [], [], [], [], [], [(.r2 .c3 .ge5)], []⟩
  | 5 => ⟨[], [], [], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p
    .ge5), .h5], [(.r1 .c1 .any), .ge3]⟩
  | 6 => ⟨[], [], [.h5], [], [], [], [], [], []⟩
  | 7 => ⟨[], [], [(.r2 .c1 .ge5)], [], [], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_2 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r2 .c2 .ge5)], [], [], [], [], [], []⟩
  | 1 => ⟨[], [], [(.r2 .c3 .ge5)], [], [], [], [], [], []⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5),
    .ge3], [], [], [], [], [], []⟩
  | 3 => ⟨[], [], [], [], [], [.h5], [], [], []⟩
  | 4 => ⟨[], [], [], [], [], [(.r2 .c1 .ge5)], [], [], []⟩
  | 5 => ⟨[], [], [], [], [], [(.r2 .c2 .ge5)], [], [], []⟩
  | 6 => ⟨[], [], [], [], [], [(.r2 .c3 .ge5)], [], [], []⟩
  | 7 => ⟨[], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .ge5), .ge3], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_3 : Nat → ExitBuckets
  | 0 => ⟨[], [], [], [], [], [], [], [], [.h5]⟩
  | 1 => ⟨[], [], [], [], [], [], [], [], [(.r2 .c1 .ge5)]⟩
  | 2 => ⟨[], [], [], [], [], [], [], [], [(.r2 .c2 .ge5)]⟩
  | 3 => ⟨[], [], [], [], [], [], [], [], [(.r2 .c3 .ge5)]⟩
  | 4 => ⟨[], [], [], [], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2
    .c3 .ge5), (.r2p .ge5), .ge3]⟩
  | 5 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5], [(.r1 .c1 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], [], []⟩
  | 6 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5],
    [(.r1 .c1 .ge5), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5],
    [(.r1 .c1 .ge3), (.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 7 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2
    .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_4 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r1 .c1 .any), .ge2, .nil], [], [], [], [], [], [], []⟩
  | 1 => ⟨[(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge2, .nil], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3],
    [(.r2 .c1 .any), .ge3, .nil], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any),
    .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1
    .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1
    .nil), (.r2 .c2 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any),
    .ge3]⟩
  | 2 => ⟨[], [], [], [], [(.r1 .c1 .any), .ge2, .nil], [], [], [], []⟩
  | 3 => ⟨[], [(.r2 .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3
    .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), .ge2, .nil], [(.r1 .c1 .any), (.r2 .c1 .ge3),
    (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r2 .c1 .any), .ge3, .nil], [(.r1 .c1 .any), (.r2 .c1
    .ge3), (.r2 .c1 .nil), (.r2 .c2 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge3), (.r2 .c1 .nil),
    (.r2 .c2 .any), .ge3]⟩
  | 4 => ⟨[], [], [], [], [], [], [], [(.r1 .c2 .any)], []⟩
  | 5 => ⟨[], [], [(.r1 .c2 .any)], [], [], [], [], [], []⟩
  | 6 => ⟨[], [], [], [], [], [(.r1 .c2 .any)], [], [], []⟩
  | 7 => ⟨[], [], [], [], [], [], [], [], [(.r1 .c2 .any)]⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_5 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5], [(.r1 .c1 .ge3), (.r1 .c2
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any),
    (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), .ge3], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r1
    .c1 .ge3), (.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r2 .c1
    .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1 .any), .ge3], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2
    .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2
    .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 6 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [],
    [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7, .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_6 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), .ge7, .h5], [(.r1 .c1 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [(.r2 .c1 .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2
    .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3),
    (.r2 .c3 .nil), (.r2 .c4 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2
    .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3),
    (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2
    .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4
    .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4
    .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_1_7 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5], [(.r1 .c1 .ge3),
    (.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3],
    [], [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7,
    .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2
    .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any),
    (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5),
    (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [.ge7, .h5], [(.r1 .c1 .ge3), (.r1 .c2
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [(.r1 .c1 .any),
    (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 5 => ⟨[], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [],
    [(.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any),
    (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [.ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2
    .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_1 (r : Nat) : ExitBuckets :=
  match r / 8 with
  | 0 => getBkt_1_0 (r % 8)
  | 1 => getBkt_1_1 (r % 8)
  | 2 => getBkt_1_2 (r % 8)
  | 3 => getBkt_1_3 (r % 8)
  | 4 => getBkt_1_4 (r % 8)
  | 5 => getBkt_1_5 (r % 8)
  | 6 => getBkt_1_6 (r % 8)
  | 7 => getBkt_1_7 (r % 8)
  | _ => emptyBuckets
noncomputable def getBkt_2_0 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [], [], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5),
    (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any), .ge3], []⟩
  | 2 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any),
    .ge3], [], [], [], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)], []⟩
  | 3 => ⟨[], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3
    .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any), .ge3], [], [], []⟩
  | 4 => ⟨[], [], [], [], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)], [], [(.r2 .c1 .ge5), (.r2 .c2
    .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1 .c1 .any), .ge3]⟩
  | 5 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5),
    .ge3], [], [], [], [], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2
    .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge3], [], [], []⟩
  | 7 => ⟨[], [], [], [], [], [(.r1 .c1 .ge3), (.r1 .c2 .any)], [], [], [(.r1 .c1 .any), (.r2 .c1
    .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_2_1 : Nat → ExitBuckets
  | 0 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3], [], [(.r1 .c2 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 2 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 3 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2
    .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 4 => ⟨[], [], [], [(.r2 .c1 .ge5)], [], [], [], [], []⟩
  | 5 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3]⟩
  | 7 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [(.r2
    .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7, .h5], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_2_2 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3], [], [], [(.r1
    .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 1 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3
    .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5],
    [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any), .ge3]⟩
  | 2 => ⟨[], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5],
    [(.r1 .c1 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], []⟩
  | 3 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .h5], [(.r1 .c1 .any), .ge3]⟩
  | 4 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], []⟩
  | 5 => ⟨[], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .ge7,
    .h5], [(.r1 .c1 .any), .ge3]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5),
    .ge3], [], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5),
    .ge3], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_2_3 : Nat → ExitBuckets
  | 0 => ⟨[], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .ge5), .ge3]⟩
  | 1 => ⟨[], [], [], [(.r2 .c2 .ge5)], [], [], [], [], []⟩
  | 2 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any),
    .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil), (.r2 .c3 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil), (.r2 .c4 .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge3), (.r2 .c3 .nil),
    (.r2 .c4 .any), .ge7, .h5], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge3), (.r2 .c2 .nil),
    (.r2 .c3 .any), .ge3]⟩
  | 3 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5], [(.r1 .c1 .any),
    .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], [], []⟩
  | 4 => ⟨[], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5],
    [(.r1 .c1 .any), .ge3], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3], []⟩
  | 5 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .h5], [(.r1 .c1 .any), .ge3]⟩
  | 6 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7, .h5], [(.r1 .c1
    .any), .ge3], [], [], []⟩
  | 7 => ⟨[], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .ge7,
    .h5], [(.r1 .c1 .any), .ge3]⟩
  | _ => emptyBuckets
noncomputable def getBkt_2_4 : Nat → ExitBuckets
  | 0 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3]⟩
  | 1 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [], []⟩
  | 2 => ⟨[], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3]⟩
  | 3 => ⟨[], [], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .h5], [(.r1 .c1 .any), .ge3], []⟩
  | 4 => ⟨[], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5], [(.r1 .c1 .any),
    .ge3], [], [], [], [], [], []⟩
  | 5 => ⟨[], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5],
    [(.r1 .c1 .any), .ge3], [], [], []⟩
  | 6 => ⟨[], [], [], [], [], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p
    .any), .h5], [(.r1 .c1 .any), .ge3]⟩
  | 7 => ⟨[], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any),
    .ge3], [], [], [], [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_2_5 : Nat → ExitBuckets
  | 0 => ⟨[], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5),
    (.r2p .any), .ge3], [], [], []⟩
  | 1 => ⟨[], [], [], [], [], [], [], [], [(.r1 .c1 .any), (.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2
    .c3 .ge5), (.r2p .any), .ge3]⟩
  | 2 => ⟨[], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5], [(.r1
    .c1 .any), .ge3], [], [], [], []⟩
  | 3 => ⟨[], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [(.r1
    .c1 .any), .ge3], [], [], [], []⟩
  | 4 => ⟨[], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5], [], [],
    [], [], []⟩
  | 5 => ⟨[], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [], [],
    [], [], []⟩
  | _ => emptyBuckets
noncomputable def getBkt_2 (r : Nat) : ExitBuckets :=
  match r / 8 with
  | 0 => getBkt_2_0 (r % 8)
  | 1 => getBkt_2_1 (r % 8)
  | 2 => getBkt_2_2 (r % 8)
  | 3 => getBkt_2_3 (r % 8)
  | 4 => getBkt_2_4 (r % 8)
  | 5 => getBkt_2_5 (r % 8)
  | _ => emptyBuckets
noncomputable def getBkt (i : Nat) : ExitBuckets :=
  match i / 64 with
  | 0 => getBkt_0 (i % 64)
  | 1 => getBkt_1 (i % 64)
  | 2 => getBkt_2 (i % 64)
  | _ => emptyBuckets

structure NodeEntry where
  spec : NodeSpec
  bktId : Nat
  hints : List Nat

def defaultEntry : NodeEntry := ⟨.a 0 .nil, 0, []⟩

noncomputable def getEntry_0_0 : Nat → NodeEntry
  | 0 => ⟨.a 1 .ge7, 0, []⟩
  | 1 => ⟨.a 1 .h3, 1, [13, 148]⟩
  | 2 => ⟨.a 1 .h4, 2, [224]⟩
  | 3 => ⟨.a 1 .h5, 3, [232]⟩
  | 4 => ⟨.a 1 .h6, 4, [285]⟩
  | 5 => ⟨.a 1 .nil, 5, []⟩
  | 6 => ⟨.a 1 (.r1 .c1 .any), 6, []⟩
  | 7 => ⟨.a 1 (.r2 .c1 .any), 7, [405]⟩
  | _ => defaultEntry
noncomputable def getEntry_0_1 : Nat → NodeEntry
  | 0 => ⟨.a 2 .ge7, 8, []⟩
  | 1 => ⟨.a 2 .h3, 9, [21, 150]⟩
  | 2 => ⟨.a 2 .h4, 10, [225]⟩
  | 3 => ⟨.a 2 .h5, 11, [233]⟩
  | 4 => ⟨.a 2 .h6, 12, [286]⟩
  | 5 => ⟨.a 2 .nil, 13, []⟩
  | 6 => ⟨.a 2 (.r1 .c1 .any), 14, []⟩
  | 7 => ⟨.a 2 (.r2 .c1 .any), 15, [406]⟩
  | _ => defaultEntry
noncomputable def getEntry_0_2 : Nat → NodeEntry
  | 0 => ⟨.a 3 .ge7, 16, []⟩
  | 1 => ⟨.a 3 .h3, 17, [27, 151]⟩
  | 2 => ⟨.a 3 .h4, 18, [226]⟩
  | 3 => ⟨.a 3 .h5, 19, [234]⟩
  | 4 => ⟨.a 3 .h6, 20, [287]⟩
  | 5 => ⟨.a 3 .nil, 21, []⟩
  | 6 => ⟨.a 4 .ge7, 22, []⟩
  | 7 => ⟨.a 4 .h3, 23, [33, 152]⟩
  | _ => defaultEntry
noncomputable def getEntry_0_3 : Nat → NodeEntry
  | 0 => ⟨.a 4 .h4, 24, [227]⟩
  | 1 => ⟨.a 4 .h5, 25, [235]⟩
  | 2 => ⟨.a 4 .h6, 26, [288]⟩
  | 3 => ⟨.a 4 .nil, 27, []⟩
  | 4 => ⟨.a 5 .ge7, 8, []⟩
  | 5 => ⟨.a 5 .h3, 23, [39, 153]⟩
  | 6 => ⟨.a 5 .h4, 28, [228]⟩
  | 7 => ⟨.a 5 .h5, 29, [236]⟩
  | _ => defaultEntry
noncomputable def getEntry_0_4 : Nat → NodeEntry
  | 0 => ⟨.a 5 .h6, 29, [289]⟩
  | 1 => ⟨.a 5 .nil, 13, []⟩
  | 2 => ⟨.a 6 .ge7, 16, []⟩
  | 3 => ⟨.a 6 .h3, 23, [45, 154]⟩
  | 4 => ⟨.a 6 .h4, 30, [229]⟩
  | 5 => ⟨.a 6 .h5, 29, [237]⟩
  | 6 => ⟨.a 6 .h6, 29, [290]⟩
  | 7 => ⟨.a 6 .nil, 21, []⟩
  | _ => defaultEntry
noncomputable def getEntry_0_5 : Nat → NodeEntry
  | 0 => ⟨.a 7 .ge7, 22, []⟩
  | 1 => ⟨.a 7 .h3, 23, [51, 155]⟩
  | 2 => ⟨.a 7 .h4, 31, [230]⟩
  | 3 => ⟨.a 7 .h5, 29, [238]⟩
  | 4 => ⟨.a 7 .h6, 29, [291]⟩
  | 5 => ⟨.a 7 .nil, 27, []⟩
  | 6 => ⟨.a 8 .ge7, 8, []⟩
  | 7 => ⟨.a 8 .h3, 23, [39, 153]⟩
  | _ => defaultEntry
noncomputable def getEntry_0_6 : Nat → NodeEntry
  | 0 => ⟨.a 8 .h4, 28, [228]⟩
  | 1 => ⟨.a 8 .h5, 29, [236]⟩
  | 2 => ⟨.a 8 .h6, 29, [289]⟩
  | 3 => ⟨.a 8 .nil, 13, []⟩
  | 4 => ⟨.s 0 .ge7, 32, []⟩
  | 5 => ⟨.s 0 .h3, 33, []⟩
  | 6 => ⟨.s 0 .h4, 32, []⟩
  | 7 => ⟨.s 0 .h5, 32, []⟩
  | _ => defaultEntry
noncomputable def getEntry_0_7 : Nat → NodeEntry
  | 0 => ⟨.s 0 .h6, 32, []⟩
  | 1 => ⟨.s 0 .nil, 34, []⟩
  | 2 => ⟨.s 0 .z, 35, [5, 147]⟩
  | 3 => ⟨.s 0 (.r1 .c1 .any), 36, [5, 144, 405]⟩
  | 4 => ⟨.s 0 (.r1 .c1 .ge3), 37, [284, 397]⟩
  | 5 => ⟨.s 0 (.r1 .c1 .ge5), 38, [211, 399]⟩
  | 6 => ⟨.s 0 (.r1 .c1 .nil), 39, []⟩
  | 7 => ⟨.s 0 (.r1 .c2 .any), 40, [146, 202]⟩
  | _ => defaultEntry
noncomputable def getEntry_0 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_0_0 (r % 8)
  | 1 => getEntry_0_1 (r % 8)
  | 2 => getEntry_0_2 (r % 8)
  | 3 => getEntry_0_3 (r % 8)
  | 4 => getEntry_0_4 (r % 8)
  | 5 => getEntry_0_5 (r % 8)
  | 6 => getEntry_0_6 (r % 8)
  | 7 => getEntry_0_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_1_0 : Nat → NodeEntry
  | 0 => ⟨.s 0 (.r1 .c2 .ge3), 41, [143, 201]⟩
  | 1 => ⟨.s 0 (.r1 .c2 .ge5), 41, [201]⟩
  | 2 => ⟨.s 0 (.r1 .c3 .any), 42, [457]⟩
  | 3 => ⟨.s 0 (.r1 .c3 .nil), 43, [421]⟩
  | 4 => ⟨.s 0 (.r2 .c1 .any), 44, [419]⟩
  | 5 => ⟨.s 0 (.r2 .c1 .ge3), 45, [407]⟩
  | 6 => ⟨.s 0 (.r2 .c1 .ge5), 45, [409]⟩
  | 7 => ⟨.s 0 (.r2 .c1 .nil), 45, [394]⟩
  | _ => defaultEntry
noncomputable def getEntry_1_1 : Nat → NodeEntry
  | 0 => ⟨.s 0 (.r2 .c2 .any), 46, [470]⟩
  | 1 => ⟨.s 0 (.r2 .c2 .ge3), 47, [458]⟩
  | 2 => ⟨.s 0 (.r2 .c2 .ge5), 47, [460]⟩
  | 3 => ⟨.s 0 (.r2 .c2 .nil), 47, [450]⟩
  | 4 => ⟨.s 0 (.r2 .c3 .any), 48, [522]⟩
  | 5 => ⟨.s 0 (.r2 .c3 .ge3), 49, [512]⟩
  | 6 => ⟨.s 0 (.r2 .c3 .ge5), 49, [513]⟩
  | 7 => ⟨.s 0 (.r2 .c3 .nil), 49, [506]⟩
  | _ => defaultEntry
noncomputable def getEntry_1_2 : Nat → NodeEntry
  | 0 => ⟨.s 0 (.r2 .c4 .any), 50, [559]⟩
  | 1 => ⟨.s 0 (.r2 .c4 .ge5), 51, [551]⟩
  | 2 => ⟨.s 0 (.r2p .any), 50, [559, 193]⟩
  | 3 => ⟨.s 0 (.r2p .ge5), 52, [551, 193]⟩
  | 4 => ⟨.s 1 .ge7, 53, []⟩
  | 5 => ⟨.s 1 .h3, 54, []⟩
  | 6 => ⟨.s 1 .h4, 53, []⟩
  | 7 => ⟨.s 1 .h5, 53, []⟩
  | _ => defaultEntry
noncomputable def getEntry_1_3 : Nat → NodeEntry
  | 0 => ⟨.s 1 .h6, 53, []⟩
  | 1 => ⟨.s 1 .nil, 55, []⟩
  | 2 => ⟨.s 1 .z, 56, [13, 149]⟩
  | 3 => ⟨.s 1 (.r1 .c1 .any), 57, [13, 148, 406]⟩
  | 4 => ⟨.s 1 (.r2 .c1 .any), 37, [420]⟩
  | 5 => ⟨.s 2 .ge7, 0, []⟩
  | 6 => ⟨.s 2 .h5, 0, []⟩
  | 7 => ⟨.s 2 (.r2 .c1 .ge5), 58, [411]⟩
  | _ => defaultEntry
noncomputable def getEntry_1_4 : Nat → NodeEntry
  | 0 => ⟨.s 2 (.r2 .c2 .ge5), 59, [462]⟩
  | 1 => ⟨.s 2 (.r2 .c3 .ge5), 60, [515]⟩
  | 2 => ⟨.s 2 (.r2 .c4 .ge5), 61, [552]⟩
  | 3 => ⟨.s 2 (.r2p .ge5), 62, [552, 194]⟩
  | 4 => ⟨.s 3 .ge7, 8, []⟩
  | 5 => ⟨.s 3 .h5, 8, []⟩
  | 6 => ⟨.s 3 (.r2 .c1 .ge5), 63, [412]⟩
  | 7 => ⟨.s 3 (.r2 .c2 .ge5), 64, [463]⟩
  | _ => defaultEntry
noncomputable def getEntry_1_5 : Nat → NodeEntry
  | 0 => ⟨.s 3 (.r2 .c3 .ge5), 65, [516]⟩
  | 1 => ⟨.s 3 (.r2 .c4 .ge5), 66, [553]⟩
  | 2 => ⟨.s 3 (.r2p .ge5), 67, [553, 195]⟩
  | 3 => ⟨.s 4 .ge7, 16, []⟩
  | 4 => ⟨.s 4 .h5, 16, []⟩
  | 5 => ⟨.s 4 (.r2 .c1 .ge5), 68, [413]⟩
  | 6 => ⟨.s 4 (.r2 .c2 .ge5), 69, [464]⟩
  | 7 => ⟨.s 4 (.r2 .c3 .ge5), 70, [517]⟩
  | _ => defaultEntry
noncomputable def getEntry_1_6 : Nat → NodeEntry
  | 0 => ⟨.s 4 (.r2 .c4 .ge5), 71, [554]⟩
  | 1 => ⟨.s 4 (.r2p .ge5), 72, [554, 196]⟩
  | 2 => ⟨.s 5 .ge7, 22, []⟩
  | 3 => ⟨.s 5 .h5, 22, []⟩
  | 4 => ⟨.s 5 (.r2 .c1 .ge5), 73, [414]⟩
  | 5 => ⟨.s 5 (.r2 .c2 .ge5), 74, [465]⟩
  | 6 => ⟨.s 5 (.r2 .c3 .ge5), 75, [518]⟩
  | 7 => ⟨.s 5 (.r2 .c4 .ge5), 76, [555]⟩
  | _ => defaultEntry
noncomputable def getEntry_1_7 : Nat → NodeEntry
  | 0 => ⟨.s 5 (.r2p .ge5), 77, [555, 197]⟩
  | 1 => ⟨.s 6 .ge7, 8, []⟩
  | 2 => ⟨.s 6 .h5, 8, []⟩
  | 3 => ⟨.s 6 (.r2 .c1 .ge5), 78, [415]⟩
  | 4 => ⟨.s 6 (.r2 .c2 .ge5), 79, [466]⟩
  | 5 => ⟨.s 6 (.r2 .c3 .ge5), 80, [519]⟩
  | 6 => ⟨.s 6 (.r2 .c4 .ge5), 81, [556]⟩
  | 7 => ⟨.s 6 (.r2p .ge5), 82, [556, 198]⟩
  | _ => defaultEntry
noncomputable def getEntry_1 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_1_0 (r % 8)
  | 1 => getEntry_1_1 (r % 8)
  | 2 => getEntry_1_2 (r % 8)
  | 3 => getEntry_1_3 (r % 8)
  | 4 => getEntry_1_4 (r % 8)
  | 5 => getEntry_1_5 (r % 8)
  | 6 => getEntry_1_6 (r % 8)
  | 7 => getEntry_1_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_2_0 : Nat → NodeEntry
  | 0 => ⟨.s 7 .ge7, 16, []⟩
  | 1 => ⟨.s 7 .h5, 16, []⟩
  | 2 => ⟨.s 7 (.r2 .c1 .ge5), 83, [416]⟩
  | 3 => ⟨.s 7 (.r2 .c2 .ge5), 84, [467]⟩
  | 4 => ⟨.s 7 (.r2 .c3 .ge5), 85, [520]⟩
  | 5 => ⟨.s 7 (.r2 .c4 .ge5), 86, [557]⟩
  | 6 => ⟨.s 7 (.r2p .ge5), 87, [557, 199]⟩
  | 7 => ⟨.s 8 .ge7, 22, []⟩
  | _ => defaultEntry
noncomputable def getEntry_2_1 : Nat → NodeEntry
  | 0 => ⟨.s 8 .h5, 22, []⟩
  | 1 => ⟨.s 8 (.r2 .c1 .ge5), 88, [417]⟩
  | 2 => ⟨.s 8 (.r2 .c2 .ge5), 89, [468]⟩
  | 3 => ⟨.s 8 (.r2 .c3 .ge5), 90, [521]⟩
  | 4 => ⟨.s 8 (.r2 .c4 .ge5), 91, [558]⟩
  | 5 => ⟨.s 8 (.r2p .ge5), 92, [558, 200]⟩
  | 6 => ⟨.s1 4 (.r2 .c1 .any), 93, [569]⟩
  | 7 => ⟨.prop 1 2, 94, [293, 308, 315, 204, 213, 257, 433, 482, 497, 526, 241]⟩
  | _ => defaultEntry
noncomputable def getEntry_2_2 : Nat → NodeEntry
  | 0 => ⟨.a 1 .ge3, 57, [1, 2, 3, 4, 0]⟩
  | 1 => ⟨.a 1 .ge5, 95, [3, 4, 0]⟩
  | 2 => ⟨.prop 1 5, 64, [282]⟩
  | 3 => ⟨.a 1 .pos, 35, [6, 7, 1, 2, 3, 4, 0]⟩
  | 4 => ⟨.a 2 .ge3, 1, [9, 10, 11, 12, 8]⟩
  | 5 => ⟨.a 2 .pos, 56, [14, 15, 9, 10, 11, 12, 8]⟩
  | 6 => ⟨.a 3 .ge3, 9, [17, 18, 19, 20, 16]⟩
  | 7 => ⟨.a 4 .ge3, 17, [23, 24, 25, 26, 22]⟩
  | _ => defaultEntry
noncomputable def getEntry_2_3 : Nat → NodeEntry
  | 0 => ⟨.a 5 .ge3, 23, [29, 30, 31, 32, 28]⟩
  | 1 => ⟨.a 6 .ge3, 23, [35, 36, 37, 38, 34]⟩
  | 2 => ⟨.a 7 .ge3, 23, [41, 42, 43, 44, 40]⟩
  | 3 => ⟨.a 8 .ge3, 23, [47, 48, 49, 50, 46]⟩
  | 4 => ⟨.e 0 .ge7, 32, [52]⟩
  | 5 => ⟨.e 0 .h4, 32, [54]⟩
  | 6 => ⟨.e 0 .h5, 32, [55]⟩
  | 7 => ⟨.s 0 .ge3, 96, [53, 54, 55, 56, 52]⟩
  | _ => defaultEntry
noncomputable def getEntry_2_4 : Nat → NodeEntry
  | 0 => ⟨.s 0 .ge5, 32, [55, 56, 52]⟩
  | 1 => ⟨.e 0 .nil, 34, [57]⟩
  | 2 => ⟨.e 0 .z, 35, [58]⟩
  | 3 => ⟨.e 0 (.r1 .c1 .any), 36, [59]⟩
  | 4 => ⟨.e 0 (.r1 .c1 .ge3), 37, [60]⟩
  | 5 => ⟨.e 0 (.r1 .c1 .ge5), 38, [61]⟩
  | 6 => ⟨.e 0 (.r1 .c1 .nil), 39, [62]⟩
  | 7 => ⟨.e 0 (.r1 .c2 .any), 40, [63]⟩
  | _ => defaultEntry
noncomputable def getEntry_2_5 : Nat → NodeEntry
  | 0 => ⟨.e 0 (.r1 .c2 .ge3), 41, [64]⟩
  | 1 => ⟨.e 0 (.r1 .c2 .ge5), 41, [65]⟩
  | 2 => ⟨.e 0 (.r1 .c3 .any), 42, [66]⟩
  | 3 => ⟨.e 0 (.r1 .c3 .nil), 43, [67]⟩
  | 4 => ⟨.e 0 (.r2 .c1 .any), 44, [68]⟩
  | 5 => ⟨.s 0 .any, 97, [57, 58, 59, 68, 53, 54, 55, 56, 52]⟩
  | 6 => ⟨.e 0 (.r2 .c1 .ge3), 45, [69]⟩
  | 7 => ⟨.e 0 (.r2 .c1 .ge5), 45, [70]⟩
  | _ => defaultEntry
noncomputable def getEntry_2_6 : Nat → NodeEntry
  | 0 => ⟨.e 0 (.r2 .c1 .nil), 45, [71]⟩
  | 1 => ⟨.e 0 (.r2 .c2 .any), 46, [72]⟩
  | 2 => ⟨.e 0 (.r2 .c2 .ge3), 47, [73]⟩
  | 3 => ⟨.e 0 (.r2 .c2 .ge5), 47, [74]⟩
  | 4 => ⟨.e 0 (.r2 .c2 .nil), 47, [75]⟩
  | 5 => ⟨.e 0 (.r2 .c3 .any), 48, [76]⟩
  | 6 => ⟨.e 0 (.r2 .c3 .ge3), 49, [77]⟩
  | 7 => ⟨.e 0 (.r2 .c3 .ge5), 49, [78]⟩
  | _ => defaultEntry
noncomputable def getEntry_2_7 : Nat → NodeEntry
  | 0 => ⟨.e 0 (.r2 .c3 .nil), 49, [79]⟩
  | 1 => ⟨.e 0 (.r2 .c4 .any), 50, [80]⟩
  | 2 => ⟨.e 0 (.r2 .c4 .ge5), 51, [81]⟩
  | 3 => ⟨.e 0 (.r2p .any), 50, [82]⟩
  | 4 => ⟨.e 0 (.r2p .ge5), 52, [83]⟩
  | 5 => ⟨.s 1 .ge3, 98, [85, 86, 87, 88, 84]⟩
  | 6 => ⟨.s 1 .ge5, 53, [87, 88, 84]⟩
  | 7 => ⟨.s1 1 .nil, 55, [89]⟩
  | _ => defaultEntry
noncomputable def getEntry_2 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_2_0 (r % 8)
  | 1 => getEntry_2_1 (r % 8)
  | 2 => getEntry_2_2 (r % 8)
  | 3 => getEntry_2_3 (r % 8)
  | 4 => getEntry_2_4 (r % 8)
  | 5 => getEntry_2_5 (r % 8)
  | 6 => getEntry_2_6 (r % 8)
  | 7 => getEntry_2_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_3_0 : Nat → NodeEntry
  | 0 => ⟨.s 1 .any, 99, [89, 90, 91, 92, 85, 86, 87, 88, 84]⟩
  | 1 => ⟨.prop 0 142, 52, []⟩
  | 2 => ⟨.prop 2 142, 62, []⟩
  | 3 => ⟨.prop 3 142, 67, []⟩
  | 4 => ⟨.prop 4 142, 72, []⟩
  | 5 => ⟨.prop 5 142, 77, []⟩
  | 6 => ⟨.prop 6 142, 82, []⟩
  | 7 => ⟨.prop 7 142, 87, []⟩
  | _ => defaultEntry
noncomputable def getEntry_3_1 : Nat → NodeEntry
  | 0 => ⟨.prop 8 142, 92, []⟩
  | 1 => ⟨.prop 1 145, 41, [301, 322, 337, 344, 204, 213, 257, 433, 482, 497, 526, 241]⟩
  | 2 => ⟨.prop 1 147, 40, [293, 308, 315, 204, 213, 257, 425, 441, 474, 241]⟩
  | 3 => ⟨.prop 1 156, 38, []⟩
  | 4 => ⟨.prop 2 156, 100, []⟩
  | 5 => ⟨.prop 3 156, 101, []⟩
  | 6 => ⟨.prop 4 156, 102, []⟩
  | 7 => ⟨.prop 5 156, 103, []⟩
  | _ => defaultEntry
noncomputable def getEntry_3_2 : Nat → NodeEntry
  | 0 => ⟨.prop 6 156, 101, []⟩
  | 1 => ⟨.prop 7 156, 102, []⟩
  | 2 => ⟨.prop 8 156, 103, []⟩
  | 3 => ⟨.prop 1 157, 38, []⟩
  | 4 => ⟨.prop 1 158, 38, []⟩
  | 5 => ⟨.prop 2 158, 100, []⟩
  | 6 => ⟨.prop 3 158, 101, []⟩
  | 7 => ⟨.prop 4 158, 102, []⟩
  | _ => defaultEntry
noncomputable def getEntry_3_3 : Nat → NodeEntry
  | 0 => ⟨.prop 5 158, 103, []⟩
  | 1 => ⟨.prop 6 158, 101, []⟩
  | 2 => ⟨.prop 7 158, 102, []⟩
  | 3 => ⟨.prop 8 158, 103, []⟩
  | 4 => ⟨.e 0 .ge3, 96, [159]⟩
  | 5 => ⟨.e 0 .ge5, 32, [160]⟩
  | 6 => ⟨.prop 1 161, 39, []⟩
  | 7 => ⟨.prop 2 161, 5, []⟩
  | _ => defaultEntry
noncomputable def getEntry_3_4 : Nat → NodeEntry
  | 0 => ⟨.prop 2 162, 2, [294, 309, 316, 205, 214, 258, 426, 442, 475, 242]⟩
  | 1 => ⟨.prop 3 162, 10, [295, 310, 317, 206, 215, 259, 427, 443, 476, 243]⟩
  | 2 => ⟨.prop 4 162, 18, [296, 311, 318, 207, 216, 260, 428, 444, 477, 244]⟩
  | 3 => ⟨.prop 5 162, 24, [297, 312, 319, 208, 217, 261, 429, 445, 478, 245]⟩
  | 4 => ⟨.prop 6 162, 28, [298, 313, 320, 209, 218, 262, 430, 446, 479, 246]⟩
  | 5 => ⟨.prop 7 162, 30, [299, 314, 321, 210, 219, 260, 428, 444, 477, 244]⟩
  | 6 => ⟨.prop 8 162, 31, [297, 312, 319, 208, 217, 261, 429, 445, 478, 245]⟩
  | 7 => ⟨.prop 1 163, 104, [293, 308, 315, 204, 213, 257, 425, 441, 474, 241]⟩
  | _ => defaultEntry
noncomputable def getEntry_3_5 : Nat → NodeEntry
  | 0 => ⟨.prop 2 163, 3, [294, 309, 316, 205, 214, 258, 426, 442, 475, 242]⟩
  | 1 => ⟨.prop 3 163, 11, [295, 310, 317, 206, 215, 259, 427, 443, 476, 243]⟩
  | 2 => ⟨.prop 4 163, 19, [296, 311, 318, 207, 216, 260, 428, 444, 477, 244]⟩
  | 3 => ⟨.prop 5 163, 25, [297, 312, 319, 208, 217, 261, 429, 445, 478, 245]⟩
  | 4 => ⟨.prop 6 163, 29, [298, 313, 320, 209, 218, 262, 430, 446, 479, 246]⟩
  | 5 => ⟨.prop 7 163, 29, [299, 314, 321, 210, 219, 260, 428, 444, 477, 244]⟩
  | 6 => ⟨.prop 8 163, 29, [297, 312, 319, 208, 217, 261, 429, 445, 478, 245]⟩
  | 7 => ⟨.prop 1 164, 105, [301, 330, 358, 385, 204, 213, 257, 433, 482, 497, 526, 241]⟩
  | _ => defaultEntry
noncomputable def getEntry_3_6 : Nat → NodeEntry
  | 0 => ⟨.prop 2 164, 106, [302, 331, 359, 386, 205, 214, 258, 434, 483, 498, 527, 242]⟩
  | 1 => ⟨.prop 3 164, 107, [303, 332, 360, 387, 206, 215, 259, 435, 484, 499, 528, 243]⟩
  | 2 => ⟨.prop 4 164, 108, [304, 333, 361, 388, 207, 216, 260, 436, 485, 500, 529, 244]⟩
  | 3 => ⟨.prop 5 164, 26, [305, 334, 362, 389, 208, 217, 261, 437, 486, 501, 530, 245]⟩
  | 4 => ⟨.prop 6 164, 29, [306, 335, 363, 390, 209, 218, 262, 438, 487, 502, 531, 246]⟩
  | 5 => ⟨.prop 7 164, 29, [307, 336, 364, 391, 210, 219, 260, 436, 485, 500, 529, 244]⟩
  | 6 => ⟨.prop 8 164, 29, [305, 334, 362, 389, 208, 217, 261, 437, 486, 501, 530, 245]⟩
  | 7 => ⟨.prop 1 165, 43, []⟩
  | _ => defaultEntry
noncomputable def getEntry_3_7 : Nat → NodeEntry
  | 0 => ⟨.prop 2 165, 58, []⟩
  | 1 => ⟨.prop 3 165, 63, []⟩
  | 2 => ⟨.prop 4 165, 68, []⟩
  | 3 => ⟨.prop 5 165, 73, []⟩
  | 4 => ⟨.prop 6 165, 78, []⟩
  | 5 => ⟨.prop 7 165, 83, []⟩
  | 6 => ⟨.prop 8 165, 88, []⟩
  | 7 => ⟨.prop 1 166, 43, []⟩
  | _ => defaultEntry
noncomputable def getEntry_3 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_3_0 (r % 8)
  | 1 => getEntry_3_1 (r % 8)
  | 2 => getEntry_3_2 (r % 8)
  | 3 => getEntry_3_3 (r % 8)
  | 4 => getEntry_3_4 (r % 8)
  | 5 => getEntry_3_5 (r % 8)
  | 6 => getEntry_3_6 (r % 8)
  | 7 => getEntry_3_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_4_0 : Nat → NodeEntry
  | 0 => ⟨.prop 2 167, 109, [205, 214, 265, 276, 434, 483, 498, 527, 242]⟩
  | 1 => ⟨.prop 3 167, 110, [206, 215, 266, 277, 435, 484, 499, 528, 243]⟩
  | 2 => ⟨.prop 4 167, 111, [207, 216, 267, 278, 436, 485, 500, 529, 244]⟩
  | 3 => ⟨.prop 5 167, 25, [208, 217, 268, 279, 437, 486, 501, 530, 245]⟩
  | 4 => ⟨.prop 6 167, 29, [209, 218, 269, 280, 438, 487, 502, 531, 246]⟩
  | 5 => ⟨.prop 7 167, 29, [210, 219, 267, 278, 436, 485, 500, 529, 244]⟩
  | 6 => ⟨.prop 8 167, 29, [208, 217, 268, 279, 437, 486, 501, 530, 245]⟩
  | 7 => ⟨.prop 2 168, 112, [205, 214, 265, 276, 434, 483, 498, 527, 242]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_1 : Nat → NodeEntry
  | 0 => ⟨.prop 3 168, 113, [206, 215, 266, 277, 435, 484, 499, 528, 243]⟩
  | 1 => ⟨.prop 4 168, 114, [207, 216, 267, 278, 436, 485, 500, 529, 244]⟩
  | 2 => ⟨.prop 5 168, 115, [208, 217, 268, 279, 437, 486, 501, 530, 245]⟩
  | 3 => ⟨.prop 6 168, 29, [209, 218, 269, 280, 438, 487, 502, 531, 246]⟩
  | 4 => ⟨.prop 7 168, 29, [210, 219, 267, 278, 436, 485, 500, 529, 244]⟩
  | 5 => ⟨.prop 8 168, 29, [208, 217, 268, 279, 437, 486, 501, 530, 245]⟩
  | 6 => ⟨.prop 5 169, 115, [208, 217, 268, 279, 437, 486, 501, 530, 245]⟩
  | 7 => ⟨.prop 6 169, 29, [209, 218, 269, 280, 438, 487, 502, 531, 246]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_2 : Nat → NodeEntry
  | 0 => ⟨.prop 7 169, 29, [210, 219, 267, 278, 436, 485, 500, 529, 244]⟩
  | 1 => ⟨.prop 8 169, 29, [208, 217, 268, 279, 437, 486, 501, 530, 245]⟩
  | 2 => ⟨.prop 2 170, 116, [265, 276, 434, 483, 498, 527, 250, 250]⟩
  | 3 => ⟨.prop 3 170, 117, [266, 277, 435, 484, 499, 528, 251, 251]⟩
  | 4 => ⟨.prop 4 170, 118, [267, 278, 436, 485, 500, 529, 252, 252]⟩
  | 5 => ⟨.prop 5 170, 119, [268, 279, 437, 486, 501, 530, 253, 253]⟩
  | 6 => ⟨.prop 6 170, 29, [269, 280, 438, 487, 502, 531, 254, 254]⟩
  | 7 => ⟨.prop 7 170, 29, [267, 278, 436, 485, 500, 529, 252, 252]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_3 : Nat → NodeEntry
  | 0 => ⟨.prop 8 170, 29, [268, 279, 437, 486, 501, 530, 253, 253]⟩
  | 1 => ⟨.prop 2 171, 59, []⟩
  | 2 => ⟨.prop 3 171, 64, []⟩
  | 3 => ⟨.prop 4 171, 69, []⟩
  | 4 => ⟨.prop 1 172, 37, [95, 96, 97, 99, 93, 94, 301, 322, 337, 344, 204, 213, 257, 433, 482,
    497, 526, 241]⟩
  | 5 => ⟨.prop 2 172, 4, [102, 103, 104, 106, 100, 101, 302, 323, 338, 345, 205, 214, 258, 434,
    483, 498, 527, 242]⟩
  | 6 => ⟨.prop 3 172, 12, [109, 110, 111, 113, 107, 108, 303, 324, 339, 346, 206, 215, 259, 435,
    484, 499, 528, 243]⟩
  | 7 => ⟨.prop 4 172, 20, [116, 117, 118, 120, 114, 115, 304, 325, 340, 347, 207, 216, 260, 436,
    485, 500, 529, 244]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_4 : Nat → NodeEntry
  | 0 => ⟨.prop 5 172, 26, [123, 124, 125, 127, 121, 122, 305, 326, 341, 348, 208, 217, 261, 437,
    486, 501, 530, 245]⟩
  | 1 => ⟨.prop 6 172, 29, [130, 131, 132, 134, 128, 129, 306, 327, 342, 349, 209, 218, 262, 438,
    487, 502, 531, 246]⟩
  | 2 => ⟨.prop 7 172, 29, [137, 138, 139, 141, 135, 136, 307, 328, 343, 350, 210, 219, 260, 436,
    485, 500, 529, 244]⟩
  | 3 => ⟨.prop 8 172, 29, [123, 124, 125, 127, 121, 122, 305, 326, 341, 348, 208, 217, 261, 437,
    486, 501, 530, 245]⟩
  | 4 => ⟨.e 0 .any, 97, [173]⟩
  | 5 => ⟨.prop 2 174, 8, [101]⟩
  | 6 => ⟨.prop 3 174, 16, [108]⟩
  | 7 => ⟨.prop 4 174, 22, [115]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_5 : Nat → NodeEntry
  | 0 => ⟨.prop 5 174, 8, [122]⟩
  | 1 => ⟨.prop 6 174, 16, [129]⟩
  | 2 => ⟨.prop 7 174, 22, [136]⟩
  | 3 => ⟨.prop 8 174, 8, [122]⟩
  | 4 => ⟨.prop 1 175, 0, [94]⟩
  | 5 => ⟨.prop 2 175, 8, [101]⟩
  | 6 => ⟨.prop 3 175, 16, [108]⟩
  | 7 => ⟨.prop 4 175, 22, [115]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_6 : Nat → NodeEntry
  | 0 => ⟨.prop 5 175, 8, [122]⟩
  | 1 => ⟨.prop 6 175, 16, [129]⟩
  | 2 => ⟨.prop 7 175, 22, [136]⟩
  | 3 => ⟨.prop 8 175, 8, [122]⟩
  | 4 => ⟨.prop 2 176, 8, [101]⟩
  | 5 => ⟨.prop 3 176, 16, [108]⟩
  | 6 => ⟨.prop 4 176, 22, [115]⟩
  | 7 => ⟨.prop 5 176, 8, [122]⟩
  | _ => defaultEntry
noncomputable def getEntry_4_7 : Nat → NodeEntry
  | 0 => ⟨.prop 6 176, 16, [129]⟩
  | 1 => ⟨.prop 7 176, 22, [136]⟩
  | 2 => ⟨.prop 8 176, 8, [122]⟩
  | 3 => ⟨.prop 2 177, 120, [102, 103, 104, 106, 100, 101, 302, 323, 338, 345, 205, 214, 258, 242]⟩
  | 4 => ⟨.prop 3 177, 121, [109, 110, 111, 113, 107, 108, 303, 324, 339, 346, 206, 215, 259, 243]⟩
  | 5 => ⟨.prop 4 177, 122, [116, 117, 118, 120, 114, 115, 304, 325, 340, 347, 207, 216, 260, 244]⟩
  | 6 => ⟨.prop 5 177, 123, [123, 124, 125, 127, 121, 122, 305, 326, 341, 348, 208, 217, 261, 245]⟩
  | 7 => ⟨.prop 6 177, 29, [130, 131, 132, 134, 128, 129, 306, 327, 342, 349, 209, 218, 262, 246]⟩
  | _ => defaultEntry
noncomputable def getEntry_4 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_4_0 (r % 8)
  | 1 => getEntry_4_1 (r % 8)
  | 2 => getEntry_4_2 (r % 8)
  | 3 => getEntry_4_3 (r % 8)
  | 4 => getEntry_4_4 (r % 8)
  | 5 => getEntry_4_5 (r % 8)
  | 6 => getEntry_4_6 (r % 8)
  | 7 => getEntry_4_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_5_0 : Nat → NodeEntry
  | 0 => ⟨.prop 7 177, 29, [137, 138, 139, 141, 135, 136, 307, 328, 343, 350, 210, 219, 260, 244]⟩
  | 1 => ⟨.prop 8 177, 29, [123, 124, 125, 127, 121, 122, 305, 326, 341, 348, 208, 217, 261, 245]⟩
  | 2 => ⟨.prop 2 178, 63, [102]⟩
  | 3 => ⟨.prop 3 178, 68, [109]⟩
  | 4 => ⟨.prop 4 178, 73, [116]⟩
  | 5 => ⟨.prop 5 178, 78, [123]⟩
  | 6 => ⟨.prop 6 178, 83, [130]⟩
  | 7 => ⟨.prop 7 178, 88, [137]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_1 : Nat → NodeEntry
  | 0 => ⟨.prop 8 178, 78, [123]⟩
  | 1 => ⟨.prop 1 179, 58, [95]⟩
  | 2 => ⟨.prop 2 179, 63, [102]⟩
  | 3 => ⟨.prop 3 179, 68, [109]⟩
  | 4 => ⟨.prop 4 179, 73, [116]⟩
  | 5 => ⟨.prop 5 179, 78, [123]⟩
  | 6 => ⟨.prop 6 179, 83, [130]⟩
  | 7 => ⟨.prop 7 179, 88, [137]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_2 : Nat → NodeEntry
  | 0 => ⟨.prop 8 179, 78, [123]⟩
  | 1 => ⟨.prop 2 180, 63, [102]⟩
  | 2 => ⟨.prop 3 180, 68, [109]⟩
  | 3 => ⟨.prop 4 180, 73, [116]⟩
  | 4 => ⟨.prop 5 180, 78, [123]⟩
  | 5 => ⟨.prop 6 180, 83, [130]⟩
  | 6 => ⟨.prop 7 180, 88, [137]⟩
  | 7 => ⟨.prop 8 180, 78, [123]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_3 : Nat → NodeEntry
  | 0 => ⟨.prop 2 181, 124, [102, 103, 104, 106, 100, 101, 302, 331, 351, 365, 371, 205, 214, 258,
    242]⟩
  | 1 => ⟨.prop 3 181, 125, [109, 110, 111, 113, 107, 108, 303, 332, 352, 366, 372, 206, 215, 259,
    243]⟩
  | 2 => ⟨.prop 4 181, 126, [116, 117, 118, 120, 114, 115, 304, 333, 353, 367, 373, 207, 216, 260,
    244]⟩
  | 3 => ⟨.prop 5 181, 123, [123, 124, 125, 127, 121, 122, 305, 334, 354, 368, 374, 208, 217, 261,
    245]⟩
  | 4 => ⟨.prop 6 181, 29, [130, 131, 132, 134, 128, 129, 306, 335, 355, 369, 375, 209, 218, 262,
    246]⟩
  | 5 => ⟨.prop 7 181, 29, [137, 138, 139, 141, 135, 136, 307, 336, 356, 370, 376, 210, 219, 260,
    244]⟩
  | 6 => ⟨.prop 8 181, 29, [123, 124, 125, 127, 121, 122, 305, 334, 354, 368, 374, 208, 217, 261,
    245]⟩
  | 7 => ⟨.prop 3 182, 69, [110]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_4 : Nat → NodeEntry
  | 0 => ⟨.prop 4 182, 74, [117]⟩
  | 1 => ⟨.prop 5 182, 79, [124]⟩
  | 2 => ⟨.prop 6 182, 84, [131]⟩
  | 3 => ⟨.prop 7 182, 89, [138]⟩
  | 4 => ⟨.prop 8 182, 79, [124]⟩
  | 5 => ⟨.prop 1 183, 59, [96]⟩
  | 6 => ⟨.prop 2 183, 64, [103]⟩
  | 7 => ⟨.prop 3 183, 69, [110]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_5 : Nat → NodeEntry
  | 0 => ⟨.prop 4 183, 74, [117]⟩
  | 1 => ⟨.prop 5 183, 79, [124]⟩
  | 2 => ⟨.prop 6 183, 84, [131]⟩
  | 3 => ⟨.prop 7 183, 89, [138]⟩
  | 4 => ⟨.prop 8 183, 79, [124]⟩
  | 5 => ⟨.prop 3 184, 69, [110]⟩
  | 6 => ⟨.prop 4 184, 74, [117]⟩
  | 7 => ⟨.prop 5 184, 79, [124]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_6 : Nat → NodeEntry
  | 0 => ⟨.prop 6 184, 84, [131]⟩
  | 1 => ⟨.prop 7 184, 89, [138]⟩
  | 2 => ⟨.prop 8 184, 79, [124]⟩
  | 3 => ⟨.prop 3 185, 127, [109, 110, 111, 113, 107, 108, 303, 332, 360, 379, 215, 259, 243]⟩
  | 4 => ⟨.prop 4 185, 128, [116, 117, 118, 120, 114, 115, 304, 333, 361, 380, 216, 260, 244]⟩
  | 5 => ⟨.prop 5 185, 29, [123, 124, 125, 127, 121, 122, 305, 334, 362, 381, 217, 261, 245]⟩
  | 6 => ⟨.prop 6 185, 29, [130, 131, 132, 134, 128, 129, 306, 335, 363, 382, 218, 262, 246]⟩
  | 7 => ⟨.prop 7 185, 29, [137, 138, 139, 141, 135, 136, 307, 336, 364, 383, 219, 260, 244]⟩
  | _ => defaultEntry
noncomputable def getEntry_5_7 : Nat → NodeEntry
  | 0 => ⟨.prop 8 185, 29, [123, 124, 125, 127, 121, 122, 305, 334, 362, 381, 217, 261, 245]⟩
  | 1 => ⟨.prop 1 186, 60, [97]⟩
  | 2 => ⟨.prop 2 186, 65, [104]⟩
  | 3 => ⟨.prop 4 187, 128, [116, 117, 118, 120, 114, 115, 304, 333, 361, 380, 216, 260, 244]⟩
  | 4 => ⟨.prop 5 187, 29, [123, 124, 125, 127, 121, 122, 305, 334, 362, 381, 217, 261, 245]⟩
  | 5 => ⟨.prop 6 187, 29, [130, 131, 132, 134, 128, 129, 306, 335, 363, 382, 218, 262, 246]⟩
  | 6 => ⟨.prop 7 187, 29, [137, 138, 139, 141, 135, 136, 307, 336, 364, 383, 219, 260, 244]⟩
  | 7 => ⟨.prop 8 187, 29, [123, 124, 125, 127, 121, 122, 305, 334, 362, 381, 217, 261, 245]⟩
  | _ => defaultEntry
noncomputable def getEntry_5 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_5_0 (r % 8)
  | 1 => getEntry_5_1 (r % 8)
  | 2 => getEntry_5_2 (r % 8)
  | 3 => getEntry_5_3 (r % 8)
  | 4 => getEntry_5_4 (r % 8)
  | 5 => getEntry_5_5 (r % 8)
  | 6 => getEntry_5_6 (r % 8)
  | 7 => getEntry_5_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_6_0 : Nat → NodeEntry
  | 0 => ⟨.prop 1 188, 129, [95, 96, 97, 99, 94]⟩
  | 1 => ⟨.prop 2 188, 130, [102, 103, 104, 106, 101]⟩
  | 2 => ⟨.prop 3 188, 131, [109, 110, 111, 113, 108]⟩
  | 3 => ⟨.prop 4 188, 132, [116, 117, 118, 120, 115]⟩
  | 4 => ⟨.prop 5 188, 133, [123, 124, 125, 127, 122]⟩
  | 5 => ⟨.prop 6 188, 134, [130, 131, 132, 134, 129]⟩
  | 6 => ⟨.prop 7 188, 135, [137, 138, 139, 141, 136]⟩
  | 7 => ⟨.prop 8 188, 133, [123, 124, 125, 127, 122]⟩
  | _ => defaultEntry
noncomputable def getEntry_6_1 : Nat → NodeEntry
  | 0 => ⟨.s1 1 .ge3, 98, [189]⟩
  | 1 => ⟨.s1 1 .ge5, 53, [190]⟩
  | 2 => ⟨.prop 0 191, 45, []⟩
  | 3 => ⟨.prop 1 191, 43, []⟩
  | 4 => ⟨.s1 1 .any, 99, [192]⟩
  | 5 => ⟨.prop 1 220, 53, []⟩
  | 6 => ⟨.prop 2 220, 0, []⟩
  | 7 => ⟨.prop 1 221, 38, []⟩
  | _ => defaultEntry
noncomputable def getEntry_6_2 : Nat → NodeEntry
  | 0 => ⟨.e 1 .nil, 39, [222]⟩
  | 1 => ⟨.e 1 (.r1 .c1 .any), 104, [231]⟩
  | 2 => ⟨.e 1 (.r1 .c1 .ge3), 105, [239]⟩
  | 3 => ⟨.e 1 (.r1 .c1 .ge5), 43, [247]⟩
  | 4 => ⟨.e 1 (.r1 .c1 .nil), 43, [255]⟩
  | 5 => ⟨.prop 1 292, 7, [95, 96, 97, 99, 93, 94, 293, 308, 315, 204, 213, 257, 425, 441, 474,
    241]⟩
  | 6 => ⟨.prop 2 292, 15, [102, 103, 104, 106, 100, 101, 294, 309, 316, 205, 214, 258, 426, 442,
    475, 242]⟩
  | 7 => ⟨.prop 0 392, 45, []⟩
  | _ => defaultEntry
noncomputable def getEntry_6_3 : Nat → NodeEntry
  | 0 => ⟨.prop 1 392, 43, []⟩
  | 1 => ⟨.prop 0 393, 45, []⟩
  | 2 => ⟨.prop 1 393, 43, []⟩
  | 3 => ⟨.prop 2 393, 58, []⟩
  | 4 => ⟨.prop 3 393, 63, []⟩
  | 5 => ⟨.prop 4 393, 68, []⟩
  | 6 => ⟨.prop 5 393, 73, []⟩
  | 7 => ⟨.prop 6 393, 78, []⟩
  | _ => defaultEntry
noncomputable def getEntry_6_4 : Nat → NodeEntry
  | 0 => ⟨.prop 7 393, 83, []⟩
  | 1 => ⟨.prop 8 393, 88, []⟩
  | 2 => ⟨.s1 2 .nil, 43, [395]⟩
  | 3 => ⟨.prop 0 396, 44, [284, 397, 222, 256, 424, 440, 473, 240]⟩
  | 4 => ⟨.prop 1 396, 37, [285, 398, 223, 257, 425, 441, 474, 241]⟩
  | 5 => ⟨.prop 1 400, 43, []⟩
  | 6 => ⟨.prop 1 401, 136, [204, 213, 264, 275, 433, 482, 497, 526, 241]⟩
  | 7 => ⟨.prop 1 402, 137, [264, 275, 433, 482, 497, 526, 249, 249]⟩
  | _ => defaultEntry
noncomputable def getEntry_6_5 : Nat → NodeEntry
  | 0 => ⟨.prop 2 402, 138, [265, 276, 434, 483, 498, 527, 250, 250]⟩
  | 1 => ⟨.prop 3 402, 139, [266, 277, 435, 484, 499, 528, 251, 251]⟩
  | 2 => ⟨.prop 4 402, 108, [267, 278, 436, 485, 500, 529, 252, 252]⟩
  | 3 => ⟨.prop 5 402, 26, [268, 279, 437, 486, 501, 530, 253, 253]⟩
  | 4 => ⟨.prop 6 402, 29, [269, 280, 438, 487, 502, 531, 254, 254]⟩
  | 5 => ⟨.prop 7 402, 29, [267, 278, 436, 485, 500, 529, 252, 252]⟩
  | 6 => ⟨.prop 8 402, 29, [268, 279, 437, 486, 501, 530, 253, 253]⟩
  | 7 => ⟨.prop 1 403, 140, []⟩
  | _ => defaultEntry
noncomputable def getEntry_6_6 : Nat → NodeEntry
  | 0 => ⟨.prop 2 403, 59, []⟩
  | 1 => ⟨.prop 3 403, 64, []⟩
  | 2 => ⟨.prop 4 403, 69, []⟩
  | 3 => ⟨.prop 5 403, 74, []⟩
  | 4 => ⟨.prop 6 403, 79, []⟩
  | 5 => ⟨.prop 7 403, 84, []⟩
  | 6 => ⟨.prop 8 403, 89, []⟩
  | 7 => ⟨.prop 1 404, 140, []⟩
  | _ => defaultEntry
noncomputable def getEntry_6_7 : Nat → NodeEntry
  | 0 => ⟨.prop 2 404, 59, []⟩
  | 1 => ⟨.prop 3 404, 64, []⟩
  | 2 => ⟨.prop 4 404, 69, []⟩
  | 3 => ⟨.prop 5 404, 74, []⟩
  | 4 => ⟨.prop 6 404, 79, []⟩
  | 5 => ⟨.prop 7 404, 84, []⟩
  | 6 => ⟨.prop 8 404, 89, []⟩
  | 7 => ⟨.e 1 .any, 7, [405]⟩
  | _ => defaultEntry
noncomputable def getEntry_6 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_6_0 (r % 8)
  | 1 => getEntry_6_1 (r % 8)
  | 2 => getEntry_6_2 (r % 8)
  | 3 => getEntry_6_3 (r % 8)
  | 4 => getEntry_6_4 (r % 8)
  | 5 => getEntry_6_5 (r % 8)
  | 6 => getEntry_6_6 (r % 8)
  | 7 => getEntry_6_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_7_0 : Nat → NodeEntry
  | 0 => ⟨.s1 2 .ge3, 43, [408]⟩
  | 1 => ⟨.s1 2 .ge5, 43, [410]⟩
  | 2 => ⟨.prop 0 418, 47, []⟩
  | 3 => ⟨.prop 1 418, 140, []⟩
  | 4 => ⟨.s1 2 .any, 37, [420]⟩
  | 5 => ⟨.e 2 (.r1 .c1 .any), 136, [422]⟩
  | 6 => ⟨.e 2 (.r1 .c1 .ge3), 137, [423]⟩
  | 7 => ⟨.e 2 (.r1 .c1 .ge5), 140, [431]⟩
  | _ => defaultEntry
noncomputable def getEntry_7_1 : Nat → NodeEntry
  | 0 => ⟨.e 2 (.r1 .c1 .nil), 140, [439]⟩
  | 1 => ⟨.prop 1 447, 42, [301, 330, 358, 385, 204, 213, 257, 433, 482, 497, 526, 241]⟩
  | 2 => ⟨.prop 0 448, 47, []⟩
  | 3 => ⟨.prop 1 448, 140, []⟩
  | 4 => ⟨.prop 0 449, 47, []⟩
  | 5 => ⟨.prop 1 449, 140, []⟩
  | 6 => ⟨.prop 2 449, 59, []⟩
  | 7 => ⟨.prop 3 449, 64, []⟩
  | _ => defaultEntry
noncomputable def getEntry_7_2 : Nat → NodeEntry
  | 0 => ⟨.prop 4 449, 69, []⟩
  | 1 => ⟨.prop 5 449, 74, []⟩
  | 2 => ⟨.prop 6 449, 79, []⟩
  | 3 => ⟨.prop 7 449, 84, []⟩
  | 4 => ⟨.prop 8 449, 89, []⟩
  | 5 => ⟨.s1 3 .nil, 140, [451]⟩
  | 6 => ⟨.prop 0 452, 46, [300, 329, 357, 384, 203, 212, 256, 432, 481, 496, 525, 240]⟩
  | 7 => ⟨.prop 1 452, 105, [301, 330, 358, 385, 204, 213, 257, 433, 482, 497, 526, 241]⟩
  | _ => defaultEntry
noncomputable def getEntry_7_3 : Nat → NodeEntry
  | 0 => ⟨.prop 1 453, 141, [275, 433, 482, 497, 526, 249, 249]⟩
  | 1 => ⟨.prop 2 453, 142, [276, 434, 483, 498, 527, 250, 250]⟩
  | 2 => ⟨.prop 3 453, 143, [277, 435, 484, 499, 528, 251, 251]⟩
  | 3 => ⟨.prop 4 453, 144, [278, 436, 485, 500, 529, 252, 252]⟩
  | 4 => ⟨.prop 5 453, 145, [279, 437, 486, 501, 530, 253, 253]⟩
  | 5 => ⟨.prop 6 453, 29, [280, 438, 487, 502, 531, 254, 254]⟩
  | 6 => ⟨.prop 7 453, 29, [278, 436, 485, 500, 529, 252, 252]⟩
  | 7 => ⟨.prop 8 453, 29, [279, 437, 486, 501, 530, 253, 253]⟩
  | _ => defaultEntry
noncomputable def getEntry_7_4 : Nat → NodeEntry
  | 0 => ⟨.prop 1 454, 93, [433, 489, 533, 540, 562, 249, 249]⟩
  | 1 => ⟨.prop 2 454, 146, [434, 490, 534, 541, 563, 250, 250]⟩
  | 2 => ⟨.prop 3 454, 147, [435, 491, 535, 542, 564, 251, 251]⟩
  | 3 => ⟨.prop 4 454, 148, [436, 492, 536, 543, 565, 252, 252]⟩
  | 4 => ⟨.prop 5 454, 149, [437, 493, 537, 544, 566, 253, 253]⟩
  | 5 => ⟨.prop 6 454, 150, [438, 494, 538, 545, 567, 254, 254]⟩
  | 6 => ⟨.prop 7 454, 151, [436, 492, 536, 543, 565, 252, 252]⟩
  | 7 => ⟨.prop 8 454, 152, [437, 493, 537, 544, 566, 253, 253]⟩
  | _ => defaultEntry
noncomputable def getEntry_7_5 : Nat → NodeEntry
  | 0 => ⟨.prop 2 455, 60, []⟩
  | 1 => ⟨.prop 3 455, 65, []⟩
  | 2 => ⟨.prop 4 455, 70, []⟩
  | 3 => ⟨.prop 5 455, 75, []⟩
  | 4 => ⟨.prop 6 455, 80, []⟩
  | 5 => ⟨.prop 7 455, 85, []⟩
  | 6 => ⟨.prop 8 455, 90, []⟩
  | 7 => ⟨.prop 1 456, 153, []⟩
  | _ => defaultEntry
noncomputable def getEntry_7_6 : Nat → NodeEntry
  | 0 => ⟨.prop 2 456, 60, []⟩
  | 1 => ⟨.prop 3 456, 65, []⟩
  | 2 => ⟨.prop 4 456, 70, []⟩
  | 3 => ⟨.prop 5 456, 75, []⟩
  | 4 => ⟨.prop 6 456, 80, []⟩
  | 5 => ⟨.prop 7 456, 85, []⟩
  | 6 => ⟨.prop 8 456, 90, []⟩
  | 7 => ⟨.e 2 .any, 42, [457]⟩
  | _ => defaultEntry
noncomputable def getEntry_7_7 : Nat → NodeEntry
  | 0 => ⟨.s1 3 .ge3, 140, [459]⟩
  | 1 => ⟨.s1 3 .ge5, 140, [461]⟩
  | 2 => ⟨.prop 0 469, 49, []⟩
  | 3 => ⟨.s1 3 .any, 105, [471]⟩
  | 4 => ⟨.e 3 (.r1 .c1 .any), 141, [472]⟩
  | 5 => ⟨.e 3 (.r1 .c1 .ge3), 93, [480]⟩
  | 6 => ⟨.e 3 (.r1 .c1 .nil), 153, [495]⟩
  | 7 => ⟨.prop 1 503, 154, [264, 275, 433, 482, 497, 526, 249, 249]⟩
  | _ => defaultEntry
noncomputable def getEntry_7 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_7_0 (r % 8)
  | 1 => getEntry_7_1 (r % 8)
  | 2 => getEntry_7_2 (r % 8)
  | 3 => getEntry_7_3 (r % 8)
  | 4 => getEntry_7_4 (r % 8)
  | 5 => getEntry_7_5 (r % 8)
  | 6 => getEntry_7_6 (r % 8)
  | 7 => getEntry_7_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_8_0 : Nat → NodeEntry
  | 0 => ⟨.prop 0 504, 49, []⟩
  | 1 => ⟨.prop 0 505, 49, []⟩
  | 2 => ⟨.prop 1 505, 153, []⟩
  | 3 => ⟨.prop 2 505, 60, []⟩
  | 4 => ⟨.prop 3 505, 65, []⟩
  | 5 => ⟨.prop 4 505, 70, []⟩
  | 6 => ⟨.prop 5 505, 75, []⟩
  | 7 => ⟨.prop 6 505, 80, []⟩
  | _ => defaultEntry
noncomputable def getEntry_8_1 : Nat → NodeEntry
  | 0 => ⟨.prop 7 505, 85, []⟩
  | 1 => ⟨.prop 8 505, 90, []⟩
  | 2 => ⟨.prop 0 507, 48, [263, 274, 432, 481, 496, 525, 248, 248]⟩
  | 3 => ⟨.prop 1 507, 137, [264, 275, 433, 482, 497, 526, 249, 249]⟩
  | 4 => ⟨.prop 1 508, 155, [433, 489, 533, 540, 562, 249, 249]⟩
  | 5 => ⟨.prop 2 508, 156, [434, 490, 534, 541, 563, 250, 250]⟩
  | 6 => ⟨.prop 3 508, 157, [435, 491, 535, 542, 564, 251, 251]⟩
  | 7 => ⟨.prop 4 508, 158, [436, 492, 536, 543, 565, 252, 252]⟩
  | _ => defaultEntry
noncomputable def getEntry_8_2 : Nat → NodeEntry
  | 0 => ⟨.prop 5 508, 159, [437, 493, 537, 544, 566, 253, 253]⟩
  | 1 => ⟨.prop 6 508, 160, [438, 494, 538, 545, 567, 254, 254]⟩
  | 2 => ⟨.prop 7 508, 161, [436, 492, 536, 543, 565, 252, 252]⟩
  | 3 => ⟨.prop 8 508, 162, [437, 493, 537, 544, 566, 253, 253]⟩
  | 4 => ⟨.prop 2 509, 62, []⟩
  | 5 => ⟨.prop 3 509, 67, []⟩
  | 6 => ⟨.prop 4 509, 72, []⟩
  | 7 => ⟨.prop 5 509, 77, []⟩
  | _ => defaultEntry
noncomputable def getEntry_8_3 : Nat → NodeEntry
  | 0 => ⟨.prop 6 509, 82, []⟩
  | 1 => ⟨.prop 7 509, 87, []⟩
  | 2 => ⟨.prop 8 509, 92, []⟩
  | 3 => ⟨.prop 2 510, 61, []⟩
  | 4 => ⟨.prop 3 510, 66, []⟩
  | 5 => ⟨.prop 4 510, 71, []⟩
  | 6 => ⟨.prop 5 510, 76, []⟩
  | 7 => ⟨.prop 6 510, 81, []⟩
  | _ => defaultEntry
noncomputable def getEntry_8_4 : Nat → NodeEntry
  | 0 => ⟨.prop 7 510, 86, []⟩
  | 1 => ⟨.prop 8 510, 91, []⟩
  | 2 => ⟨.e 3 .any, 154, [511]⟩
  | 3 => ⟨.s1 4 .ge5, 153, [514]⟩
  | 4 => ⟨.s1 4 .any, 137, [523]⟩
  | 5 => ⟨.e 4 (.r1 .c1 .any), 155, [524]⟩
  | 6 => ⟨.prop 1 546, 155, [433, 489, 533, 540, 562, 249, 249]⟩
  | 7 => ⟨.prop 0 547, 51, []⟩
  | _ => defaultEntry
noncomputable def getEntry_8_5 : Nat → NodeEntry
  | 0 => ⟨.prop 2 547, 61, []⟩
  | 1 => ⟨.prop 3 547, 66, []⟩
  | 2 => ⟨.prop 4 547, 71, []⟩
  | 3 => ⟨.prop 5 547, 76, []⟩
  | 4 => ⟨.prop 6 547, 81, []⟩
  | 5 => ⟨.prop 7 547, 86, []⟩
  | 6 => ⟨.prop 8 547, 91, []⟩
  | 7 => ⟨.prop 0 548, 50, [432, 488, 532, 539, 561, 248, 248]⟩
  | _ => defaultEntry
noncomputable def getEntry_8_6 : Nat → NodeEntry
  | 0 => ⟨.prop 1 548, 93, [433, 489, 533, 540, 562, 249, 249]⟩
  | 1 => ⟨.prop 2 549, 163, []⟩
  | 2 => ⟨.prop 3 549, 164, []⟩
  | 3 => ⟨.prop 4 549, 165, []⟩
  | 4 => ⟨.prop 5 549, 166, []⟩
  | 5 => ⟨.prop 6 549, 167, []⟩
  | 6 => ⟨.prop 7 549, 168, []⟩
  | 7 => ⟨.prop 8 549, 169, []⟩
  | _ => defaultEntry
noncomputable def getEntry_8_7 : Nat → NodeEntry
  | 0 => ⟨.e 4 .any, 155, [550]⟩
  | 1 => ⟨.s1 5 .any, 93, [560]⟩
  | 2 => ⟨.prop 1 568, 170, []⟩
  | 3 => ⟨.prop 1 569, 171, []⟩
  | 4 => ⟨.e 5 .any, 170, [570]⟩
  | 5 => ⟨.s1 6 .any, 171, [571]⟩
  | 6 => ⟨.prop 1 572, 172, []⟩
  | 7 => ⟨.prop 1 573, 173, []⟩
  | _ => defaultEntry
noncomputable def getEntry_8 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_8_0 (r % 8)
  | 1 => getEntry_8_1 (r % 8)
  | 2 => getEntry_8_2 (r % 8)
  | 3 => getEntry_8_3 (r % 8)
  | 4 => getEntry_8_4 (r % 8)
  | 5 => getEntry_8_5 (r % 8)
  | 6 => getEntry_8_6 (r % 8)
  | 7 => getEntry_8_7 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry_9_0 : Nat → NodeEntry
  | 0 => ⟨.e 6 .any, 172, [574]⟩
  | 1 => ⟨.s1 7 .any, 173, [575]⟩
  | _ => defaultEntry
noncomputable def getEntry_9 (r : Nat) : NodeEntry :=
  match r / 8 with
  | 0 => getEntry_9_0 (r % 8)
  | _ => defaultEntry
noncomputable def getEntry (i : Nat) : NodeEntry :=
  match i / 64 with
  | 0 => getEntry_0 (i % 64)
  | 1 => getEntry_1 (i % 64)
  | 2 => getEntry_2 (i % 64)
  | 3 => getEntry_3 (i % 64)
  | 4 => getEntry_4 (i % 64)
  | 5 => getEntry_5 (i % 64)
  | 6 => getEntry_6 (i % 64)
  | 7 => getEntry_7 (i % 64)
  | 8 => getEntry_8 (i % 64)
  | 9 => getEntry_9 (i % 64)
  | _ => defaultEntry

noncomputable def getSpec (i : Nat) : NodeSpec := (getEntry i).spec
noncomputable def getNodeBkt (i : Nat) : ExitBuckets := getBkt (getEntry i).bktId

noncomputable def checkDep (exp : NodeSpec) (idx : Nat) (dst : ExitBuckets) : Bool :=
  Nat.blt idx numNodes && eqSpec (getSpec idx) exp && subsetBkt (getNodeBkt idx) dst

noncomputable def checkZDep (u : Nat) (exp : NodeSpec) (idx : Nat) (dst : ExitBuckets) : Bool :=
  Nat.blt idx u && eqSpec (getSpec idx) exp && subsetBkt (getNodeBkt idx) dst

noncomputable def checkZDeps (u : Nat) (dst : ExitBuckets) : List NodeSpec → List Nat → Bool
  | [], [] => true
  | e :: es, i :: is => checkZDep u e i dst && checkZDeps u dst es is
  | _, _ => false

noncomputable def checkFDeps (dst : ExitBuckets) : List NodeSpec → List Nat → Bool
  | [], [] => true
  | e :: es, i :: is => checkDep e i dst && checkFDeps dst es is
  | _, _ => false

def splitRT : RT → Option (List RT)
  | .any => some [.nil, .z, .r1 .c1 .any, .r2 .c1 .any, .h3, .h4, .h5, .h6, .ge7]
  | .pos => some [.r1 .c1 .any, .r2 .c1 .any, .h3, .h4, .h5, .h6, .ge7]
  | .ge2 => some [.r2 .c1 .any, .h3, .h4, .h5, .h6, .ge7]
  | .ge3 => some [.h3, .h4, .h5, .h6, .ge7]
  | .ge5 => some [.h5, .h6, .ge7]
  | _ => none

def push0Tail : TailAtom → List RT
  | .nil => [.nil]
  | .ge5 => [.ge5]
  | .ge3 => [.h4, .ge5]
  | .any => [.nil, .pos]

noncomputable def checkPropBkt (d : Nat) (dst : ExitBuckets) (idx : Nat) (expSub : NodeSpec) :
  Bool :=
  if Nat.blt idx numNodes then
    match getSpec idx with
    | .prop d' s => Nat.beq d' d && Nat.blt s numNodes && eqSpec (getSpec s) expSub && subsetBkt
      (getNodeBkt idx) dst
    | _ => false
  else false

noncomputable def checkMar0 (d1 : Nat) (dst : ExitBuckets) : List RT → List Nat → Option (List Nat)
  | [], hs => some hs
  | t :: ts, idx :: hs =>
    if checkDep (.s d1 t) idx dst then checkMar0 d1 dst ts hs else none
  | _, [] => none

noncomputable def checkBump0 (d1 : Nat) (dst : ExitBuckets) : List RT → List Nat → Option (List Nat)
  | [], hs => some hs
  | t :: ts, idx :: hs =>
    if checkPropBkt d1 dst idx (.e 0 t) then checkBump0 d1 dst ts hs else none
  | _, [] => none

noncomputable def checkBump1 (d2 : Nat) (dst : ExitBuckets) : List RT → List Nat → Option (List Nat)
  | [], hs => some hs
  | t :: ts, hs =>
    match t with
    | .r2 c b =>
      match hs with
      | idx :: hs' =>
        if checkPropBkt d2 dst idx (.e c.toNat (cons1 (tailToRT b))) then checkBump1 d2 dst ts hs'
          else none
      | [] => none
    | .r2p b =>
      match hs with
      | i1 :: i2 :: hs' =>
        if checkPropBkt d2 dst i1 (.e 4 (cons1 (tailToRT b))) &&
           checkPropBkt d2 dst i2 (.e 4 (.r1 .c1 .any)) then checkBump1 d2 dst ts hs' else none
      | _ => none
    | _ =>
      match hs with
      | idx :: hs' =>
        if checkPropBkt d2 dst idx (.e 0 (cons1 t)) then checkBump1 d2 dst ts hs' else none
      | [] => none

def checkDirectList (f : RT → Bool) : List RT → Bool
  | [] => true
  | t :: ts => f t && checkDirectList f ts

noncomputable def checkNodeProp (u d sub : Nat) (dst : ExitBuckets) (hs : List Nat) : Bool :=
  if Nat.blt sub u then
    let sb := getNodeBkt sub
    let d1 := capD (d + 1)
    let d2 := capD (d1 + 1)
    checkDirectList (fun t => memElPop (d + 3) (cons1 t) dst) sb.mar1 &&
    (sb.mar2.isEmpty || memElPop (d + 3) .ge3 dst) &&
    checkDirectList (fun t => memElPop d (cons2 t) dst) sb.mz0 &&
    (sb.mz1.isEmpty || memElPop d .h5 dst) &&
    (sb.mz2.isEmpty || memElPop d .ge7 dst) &&
    (sb.bump2.isEmpty || memElPop (d1 + 4) (.r1 .c2 .any) dst) &&
    match checkMar0 d1 dst sb.mar0 hs with
    | none => false
    | some hs1 =>
      match checkBump0 d1 dst sb.bump0 hs1 with
      | none => false
      | some hs2 =>
        match checkBump1 d2 dst sb.bump1 hs2 with
        | some [] => true
        | _ => false
  else false

noncomputable def checkNodeA (u d : Nat) (rt : RT) (dst : ExitBuckets) (hs : List Nat) : Bool :=
  match splitRT rt with
  | some srs => checkZDeps u dst (srs.map (fun sr => .a d sr)) hs
  | none =>
    match rt with
    | .nil => hs.isEmpty && memElPop (d + 4) (.r1 .c2 .nil) dst
    | .z => hs.isEmpty && memElPop d .nil dst && memElPop d .pos dst
    | .h3 => checkFDeps dst [.a (capD (d + 1)) .nil, .a (capD (d + 1)) .ge3] hs
    | .h4 => match hs with | [i] => checkPropBkt (capD (d + 1)) dst i (.e 0 .z) | _ => false
    | .h5 =>
      match hs with | [i] => checkPropBkt (capD (d + 1)) dst i (.e 0 (.r1 .c1 .any)) | _ => false
    | .h6 =>
      match hs with | [i] => checkPropBkt (capD (d + 1)) dst i (.e 0 (.r2 .c1 .any)) | _ => false
    | .ge7 => hs.isEmpty && memElPop (d + 4) (.r1 .c1 .any) dst
    | .r2 .c1 b => match hs with | [i] => checkPropBkt d dst i (.e 0 (tailToRT b)) | _ => false
    | .r2 .c2 b => match hs with | [i] => checkPropBkt d dst i (.e 0 (.r2 .c1 b)) | _ => false
    | .r2 .c3 b => match hs with | [i] => checkPropBkt d dst i (.e 0 (.r2 .c2 b)) | _ => false
    | .r2 .c4 b => match hs with | [i] => checkPropBkt d dst i (.e 0 (.r2 .c3 b)) | _ => false
    | .r2p b => match hs with
      | [i1, i2] => checkPropBkt d dst i1 (.e 0 (.r2 .c3 b)) && checkPropBkt d dst i2 (.e 0 (.r2p
        b))
      | _ => false
    | .r1 .c1 b => hs.isEmpty &&
      match b with
      | .nil => memElPop d (.r2 .c1 .nil) dst
      | .ge5 => memElPop d (.r2 .c1 .ge3) dst
      | .ge3 => memElPop d (.r2 .c2 .any) dst && memElPop d (.r2 .c1 .ge3) dst
      | .any => memElPop d .nil dst && memElPop d .ge3 dst && memElPop d (.r2 .c1 .any) dst
    | .r1 _ _ | .r1p _ => hs.isEmpty && memElPop d (.r2 .c1 .any) dst
    | _ => false

noncomputable def checkNodeS (u d : Nat) (rt : RT) (dst : ExitBuckets) (hs : List Nat) : Bool :=
  match splitRT rt with
  | some srs => checkZDeps u dst (srs.map (fun sr => .s d sr)) hs
  | none =>
    let d1 := capD (d + 1)
    match rt with
    | .nil => hs.isEmpty && memElPop (d + 3) (.r1 .c1 .nil) dst
    | .z => checkFDeps dst [.a d1 .nil, .a d1 .pos] hs
    | .h3 => hs.isEmpty && memElPop (d + 3) .nil dst && memElPop (d + 3) .ge2 dst
    | .h4 | .h5 | .h6 | .ge7 => hs.isEmpty && memElPop (d + 3) (.r1 .c1 .any) dst
    | .r2 c b => match hs with | [i] => checkPropBkt d dst i (.s1 c.toNat (tailToRT b)) | _ => false
    | .r2p b => match hs with
      | [i1, i2] => checkPropBkt d dst i1 (.s1 4 (tailToRT b)) && checkPropBkt d dst i2 (.s1 4
        (.r2 .c1 .any))
      | _ => false
    | .r1 .c1 b =>
      match b with
      | .nil => hs.isEmpty && memElPop (d + 4) (.r1 .c2 .nil) dst
      | .ge5 => match hs with
        | [i1, i2] => checkPropBkt d1 dst i1 (.e 0 .h4) && checkPropBkt d1 dst i2 (.e 0 .ge5)
        | _ => false
      | .ge3 => match hs with
        | [i1, i2] => checkPropBkt d1 dst i1 (.e 0 (.r2 .c1 .any)) && checkPropBkt d1 dst i2 (.e 0
          .ge3)
        | _ => false
      | .any => memElPop (d + 4) (.r1 .c2 .nil) dst &&
        match hs with
        | [i1, i2, i3] => checkDep (.a d1 .nil) i1 dst && checkDep (.a d1 .ge3) i2 dst &&
          checkPropBkt d1 dst i3 (.e 0 .any)
        | _ => false
    | .r1 .c2 b =>
      match push0Tail b, hs with
      | [p1], [i1] => checkPropBkt d1 dst i1 (.a 1 p1)
      | [p1, p2], [i1, i2] => checkPropBkt d1 dst i1 (.a 1 p1) && checkPropBkt d1 dst i2 (.a 1 p2)
      | _, _ => false
    | .r1 .c3 b => match hs with | [i] => checkPropBkt d1 dst i (.e 1 (tailToRT b)) | _ => false
    | .r1 .c4 b => match hs with | [i] => checkPropBkt d1 dst i (.e 1 (.r1 .c1 b)) | _ => false
    | .r1p _ => match hs with | [i] => checkPropBkt d1 dst i (.e 1 (.r1 .c1 .any)) | _ => false
    | _ => false

noncomputable def checkNodeS1 (u c : Nat) (rt : RT) (dst : ExitBuckets) (hs : List Nat) : Bool :=
  if Nat.beq c 0 then false
  else if Nat.beq c 1 then
    match hs with | [i] => checkZDep u (.s 1 rt) i dst | _ => false
  else
    match rt with
    | .r2 cl b =>
      if Nat.ble (c + cl.toNat) 7 then
        match hs with | [i] => checkDep (.s1 (c + cl.toNat) (tailToRT b)) i dst | _ => false
      else
        match hs with | [i] => Nat.blt i u && checkPropBkt 1 dst i (.s1 (c - 1) rt) | _ => false
    | _ =>
      match hs with | [i] => Nat.blt i u && checkPropBkt 1 dst i (.s1 (c - 1) rt) | _ => false

noncomputable def checkNodeE (u k : Nat) (rt : RT) (dst : ExitBuckets) (hs : List Nat) : Bool :=
  if Nat.beq k 0 then
    match hs with | [i] => checkZDep u (.s 0 rt) i dst | _ => false
  else
    match hs with | [i] => Nat.blt i u && checkPropBkt 1 dst i (.e (k - 1) rt) | _ => false

noncomputable def checkEntry (u : Nat) (sp : NodeSpec) (dst : ExitBuckets) (hs : List Nat) : Bool :=
  match sp with
  | .prop d sub => checkNodeProp u d sub dst hs
  | .a d rt => checkNodeA u d rt dst hs
  | .s d rt => checkNodeS u d rt dst hs
  | .s1 c rt => checkNodeS1 u c rt dst hs
  | .e k rt => checkNodeE u k rt dst hs

noncomputable def checkNode (u : Nat) : Bool :=
  let ent := getEntry u
  checkEntry u ent.spec (getBkt ent.bktId) ent.hints

noncomputable def checkRange : Nat → Nat → Bool
  | _, 0 => true
  | lo, fuel + 1 => checkNode lo && checkRange (lo + 1) fuel

theorem cert_chunk_0 : checkRange 0 32 = true := by decide +kernel
theorem cert_chunk_1 : checkRange 32 32 = true := by decide +kernel
theorem cert_chunk_2 : checkRange 64 32 = true := by decide +kernel
theorem cert_chunk_3 : checkRange 96 32 = true := by decide +kernel
theorem cert_chunk_4 : checkRange 128 32 = true := by decide +kernel
theorem cert_chunk_5 : checkRange 160 32 = true := by decide +kernel
theorem cert_chunk_6 : checkRange 192 32 = true := by decide +kernel
theorem cert_chunk_7 : checkRange 224 32 = true := by decide +kernel
theorem cert_chunk_8 : checkRange 256 32 = true := by decide +kernel
theorem cert_chunk_9 : checkRange 288 32 = true := by decide +kernel
theorem cert_chunk_10 : checkRange 320 32 = true := by decide +kernel
theorem cert_chunk_11 : checkRange 352 32 = true := by decide +kernel
theorem cert_chunk_12 : checkRange 384 32 = true := by decide +kernel
theorem cert_chunk_13 : checkRange 416 32 = true := by decide +kernel
theorem cert_chunk_14 : checkRange 448 32 = true := by decide +kernel
theorem cert_chunk_15 : checkRange 480 32 = true := by decide +kernel
theorem cert_chunk_16 : checkRange 512 32 = true := by decide +kernel
theorem cert_chunk_17 : checkRange 544 32 = true := by decide +kernel
theorem cert_chunk_18 : checkRange 576 2 = true := by decide +kernel

theorem checkRange_mem : ∀ (lo cnt u : Nat),
    checkRange lo cnt = true → lo ≤ u → u < lo + cnt → checkNode u = true
  | _, 0, _, _, hle, hlt => by omega
  | lo, cnt + 1, u, h, hle, hlt => by
    simp only [checkRange, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hle with rfl | hgt
    · exact h.1
    · exact checkRange_mem (lo + 1) cnt u h.2 (by omega) (by omega)

theorem cert_all (u : Nat) (hu : u < numNodes) : checkNode u = true := by
  rcases Nat.lt_or_ge u 32 with h0 | h0
  · exact checkRange_mem 0 32 u cert_chunk_0 (by omega) h0
  rcases Nat.lt_or_ge u 64 with h1 | h1
  · exact checkRange_mem 32 32 u cert_chunk_1 (by omega) h1
  rcases Nat.lt_or_ge u 96 with h2 | h2
  · exact checkRange_mem 64 32 u cert_chunk_2 (by omega) h2
  rcases Nat.lt_or_ge u 128 with h3 | h3
  · exact checkRange_mem 96 32 u cert_chunk_3 (by omega) h3
  rcases Nat.lt_or_ge u 160 with h4 | h4
  · exact checkRange_mem 128 32 u cert_chunk_4 (by omega) h4
  rcases Nat.lt_or_ge u 192 with h5 | h5
  · exact checkRange_mem 160 32 u cert_chunk_5 (by omega) h5
  rcases Nat.lt_or_ge u 224 with h6 | h6
  · exact checkRange_mem 192 32 u cert_chunk_6 (by omega) h6
  rcases Nat.lt_or_ge u 256 with h7 | h7
  · exact checkRange_mem 224 32 u cert_chunk_7 (by omega) h7
  rcases Nat.lt_or_ge u 288 with h8 | h8
  · exact checkRange_mem 256 32 u cert_chunk_8 (by omega) h8
  rcases Nat.lt_or_ge u 320 with h9 | h9
  · exact checkRange_mem 288 32 u cert_chunk_9 (by omega) h9
  rcases Nat.lt_or_ge u 352 with h10 | h10
  · exact checkRange_mem 320 32 u cert_chunk_10 (by omega) h10
  rcases Nat.lt_or_ge u 384 with h11 | h11
  · exact checkRange_mem 352 32 u cert_chunk_11 (by omega) h11
  rcases Nat.lt_or_ge u 416 with h12 | h12
  · exact checkRange_mem 384 32 u cert_chunk_12 (by omega) h12
  rcases Nat.lt_or_ge u 448 with h13 | h13
  · exact checkRange_mem 416 32 u cert_chunk_13 (by omega) h13
  rcases Nat.lt_or_ge u 480 with h14 | h14
  · exact checkRange_mem 448 32 u cert_chunk_14 (by omega) h14
  rcases Nat.lt_or_ge u 512 with h15 | h15
  · exact checkRange_mem 480 32 u cert_chunk_15 (by omega) h15
  rcases Nat.lt_or_ge u 544 with h16 | h16
  · exact checkRange_mem 512 32 u cert_chunk_16 (by omega) h16
  rcases Nat.lt_or_ge u 576 with h17 | h17
  · exact checkRange_mem 544 32 u cert_chunk_17 (by omega) h17
  exact checkRange_mem 576 2 u cert_chunk_18 (by omega) (by unfold numNodes at hu; omega)

/-! ## Section 5: Semantics of `RT`, `ExitBuckets`, `MatchesD`, and Certificate Soundness -/

theorem eqTail_eq : ∀ {a b : TailAtom}, eqTail a b = true → a = b
  | .nil, .nil, _ | .ge5, .ge5, _ | .ge3, .ge3, _ | .any, .any, _ => rfl
  | .nil, .ge5, h | .nil, .ge3, h | .nil, .any, h
  | .ge5, .nil, h | .ge5, .ge3, h | .ge5, .any, h
  | .ge3, .nil, h | .ge3, .ge5, h | .ge3, .any, h
  | .any, .nil, h | .any, .ge5, h | .any, .ge3, h => by simp [eqTail] at h

theorem eqLen_eq : ∀ {a b : RunLen}, eqLen a b = true → a = b
  | .c1, .c1, _ | .c2, .c2, _ | .c3, .c3, _ | .c4, .c4, _ => rfl
  | .c1, .c2, h | .c1, .c3, h | .c1, .c4, h
  | .c2, .c1, h | .c2, .c3, h | .c2, .c4, h
  | .c3, .c1, h | .c3, .c2, h | .c3, .c4, h
  | .c4, .c1, h | .c4, .c2, h | .c4, .c3, h => by simp [eqLen] at h

theorem eqRT_eq {a b : RT} (h : eqRT a b = true) : a = b := by
  cases a <;> cases b <;> simp only [eqRT, Bool.and_eq_true] at h
  all_goals first
    | rfl
    | exact absurd h (by decide)
    | exact congrArg _ (eqTail_eq h)
    | (obtain ⟨h1, h2⟩ := h; rw [eqLen_eq h1, eqTail_eq h2])

theorem eqSpec_eq {a b : NodeSpec} (h : eqSpec a b = true) : a = b := by
  cases a <;> cases b <;> simp only [eqSpec, Bool.and_eq_true] at h
  all_goals first
    | exact absurd h (by decide)
    | (obtain ⟨h1, h2⟩ := h
       first
       | rw [Nat.eq_of_beq_eq_true h1, eqRT_eq h2]
       | rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2])

def InTail : TailAtom → List ℕ → Prop
  | .nil, R => R = []
  | .ge5, R => ∃ h rt, 5 ≤ h ∧ R = h :: rt
  | .ge3, R => ∃ h rt, 3 ≤ h ∧ R = h :: rt
  | .any, _ => True

def InRT : RT → List ℕ → Prop
  | .nil, R => R = []
  | .z, R => ∃ rt, R = 0 :: rt
  | .h3, R => ∃ rt, R = 3 :: rt
  | .h4, R => ∃ rt, R = 4 :: rt
  | .h5, R => ∃ rt, R = 5 :: rt
  | .h6, R => ∃ rt, R = 6 :: rt
  | .ge7, R => ∃ h rt, 7 ≤ h ∧ R = h :: rt
  | .ge5, R => ∃ h rt, 5 ≤ h ∧ R = h :: rt
  | .ge3, R => ∃ h rt, 3 ≤ h ∧ R = h :: rt
  | .ge2, R => ∃ h rt, 2 ≤ h ∧ R = h :: rt
  | .pos, R => ∃ h rt, 1 ≤ h ∧ R = h :: rt
  | .any, _ => True
  | .r1 c b, R => ∃ rt, R = List.replicate c.toNat 1 ++ rt ∧ InTail b rt
  | .r1p b, R => ∃ k rt, 4 ≤ k ∧ R = List.replicate k 1 ++ rt ∧ InTail b rt
  | .r2 c b, R => ∃ rt, R = List.replicate c.toNat 2 ++ rt ∧ InTail b rt
  | .r2p b, R => ∃ k rt, 4 ≤ k ∧ R = List.replicate k 2 ++ rt ∧ InTail b rt

theorem inTail_iff_tailToRT (b : TailAtom) (R : List ℕ) : InTail b R ↔ InRT (tailToRT b) R := by
  cases b <;> rfl

theorem toTail_sound {t : RT} {R : List ℕ} (h : InRT t R) : InTail (toTail t) R := by
  cases t with
  | nil => exact h
  | h5 => obtain ⟨rt, rfl⟩ := h; exact ⟨5, rt, by omega, rfl⟩
  | h6 => obtain ⟨rt, rfl⟩ := h; exact ⟨6, rt, by omega, rfl⟩
  | ge7 => obtain ⟨hd, rt, hh, rfl⟩ := h; exact ⟨hd, rt, by omega, rfl⟩
  | ge5 => exact h
  | h3 => obtain ⟨rt, rfl⟩ := h; exact ⟨3, rt, by omega, rfl⟩
  | h4 => obtain ⟨rt, rfl⟩ := h; exact ⟨4, rt, by omega, rfl⟩
  | ge3 => exact h
  | _ => trivial

theorem cons1_sound {t : RT} {R : List ℕ} (h : InRT t R) : InRT (cons1 t) (1 :: R) := by
  cases t with
  | r1 c b =>
    obtain ⟨rt, rfl, hb⟩ := h
    cases c with
    | c1 => exact ⟨rt, rfl, hb⟩
    | c2 => exact ⟨rt, rfl, hb⟩
    | c3 => exact ⟨rt, rfl, hb⟩
    | c4 => exact ⟨5, rt, by omega, rfl, hb⟩
  | r1p b =>
    obtain ⟨k, rt, hk, rfl, hb⟩ := h
    exact ⟨k + 1, rt, by omega, by rw [List.replicate_succ, List.cons_append], hb⟩
  | _ =>
    exact ⟨R, rfl, toTail_sound h⟩

theorem cons2_sound {t : RT} {R : List ℕ} (h : InRT t R) : InRT (cons2 t) (2 :: R) := by
  cases t with
  | r2 c b =>
    obtain ⟨rt, rfl, hb⟩ := h
    cases c with
    | c1 => exact ⟨rt, rfl, hb⟩
    | c2 => exact ⟨rt, rfl, hb⟩
    | c3 => exact ⟨rt, rfl, hb⟩
    | c4 => exact ⟨5, rt, by omega, rfl, hb⟩
  | r2p b =>
    obtain ⟨k, rt, hk, rfl, hb⟩ := h
    exact ⟨k + 1, rt, by omega, by rw [List.replicate_succ, List.cons_append], hb⟩
  | _ =>
    exact ⟨R, rfl, toTail_sound h⟩

theorem subTail_sound {a b : TailAtom} (h : subTail a b = true) {R : List ℕ} (hR : InTail a R) :
    InTail b R := by
  cases a <;> cases b <;> simp [subTail] at h
  · exact hR
  · trivial
  · exact hR
  · obtain ⟨hd, rt, hh, rfl⟩ := hR; exact ⟨hd, rt, by omega, rfl⟩
  · trivial
  · exact hR
  · trivial
  · trivial

theorem clenGt_lt {a b : RunLen} (h : clenGt a b = true) : b.toNat < a.toNat := by
  cases a <;> cases b <;> simp [clenGt, RunLen.toNat] at h ⊢

theorem runLen_le4 (c : RunLen) : c.toNat ≤ 4 := by
  cases c <;> decide

theorem replicate_split {α : Type*} (a : α) {k m : ℕ} (h : m ≤ k) (rt : List α) :
    List.replicate k a ++ rt = List.replicate m a ++ (List.replicate (k - m) a ++ rt) := by
  rw [← List.append_assoc, ← List.replicate_add]
  exact congrArg (fun n => List.replicate n a ++ rt) (by omega)

theorem subRT_sound {a b : RT} (h : subRT a b = true) {R : List ℕ} (hR : InRT a R) : InRT b R := by
  cases a with
  | nil =>
    cases b <;> simp [subRT] at h
    · exact hR
    · trivial
  | z =>
    cases b <;> simp [subRT] at h
    · exact hR
    · trivial
  | h3 =>
    obtain ⟨rt, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨rt, rfl⟩
    · exact ⟨3, rt, by omega, rfl⟩
    · exact ⟨3, rt, by omega, rfl⟩
    · exact ⟨3, rt, by omega, rfl⟩
    · trivial
  | h4 =>
    obtain ⟨rt, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨rt, rfl⟩
    · exact ⟨4, rt, by omega, rfl⟩
    · exact ⟨4, rt, by omega, rfl⟩
    · exact ⟨4, rt, by omega, rfl⟩
    · trivial
  | h5 =>
    obtain ⟨rt, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨rt, rfl⟩
    · exact ⟨5, rt, by omega, rfl⟩
    · exact ⟨5, rt, by omega, rfl⟩
    · exact ⟨5, rt, by omega, rfl⟩
    · exact ⟨5, rt, by omega, rfl⟩
    · trivial
  | h6 =>
    obtain ⟨rt, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨rt, rfl⟩
    · exact ⟨6, rt, by omega, rfl⟩
    · exact ⟨6, rt, by omega, rfl⟩
    · exact ⟨6, rt, by omega, rfl⟩
    · exact ⟨6, rt, by omega, rfl⟩
    · trivial
  | ge7 =>
    obtain ⟨hd, rt, hh, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · trivial
  | ge5 =>
    obtain ⟨hd, rt, hh, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · trivial
  | ge3 =>
    obtain ⟨hd, rt, hh, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · trivial
  | ge2 =>
    obtain ⟨hd, rt, hh, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨hd, rt, by omega, rfl⟩
    · exact ⟨hd, rt, by omega, rfl⟩
    · trivial
  | pos =>
    obtain ⟨hd, rt, hh, rfl⟩ := hR
    cases b <;> simp [subRT] at h
    · exact ⟨hd, rt, by omega, rfl⟩
    · trivial
  | any =>
    cases b <;> simp [subRT] at h
    trivial
  | r1 ca ba =>
    obtain ⟨rt, rfl, hba⟩ := hR
    cases b with
    | any => trivial
    | pos =>
      cases ca <;> exact ⟨1, _, by omega, rfl⟩
    | r1 cb bb =>
      simp only [subRT, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨heq, hs⟩ | ⟨hgt, hany⟩
      · rw [eqLen_eq heq]; exact ⟨rt, rfl, subTail_sound hs hba⟩
      · rw [eqTail_eq hany]
        exact ⟨List.replicate (ca.toNat - cb.toNat) 1 ++ rt,
          replicate_split 1 (Nat.le_of_lt (clenGt_lt hgt)) rt, trivial⟩
    | r1p bb =>
      simp only [subRT, Bool.and_eq_true] at h
      obtain ⟨heq, hs⟩ := h
      rw [eqLen_eq heq]
      exact ⟨4, rt, by omega, rfl, subTail_sound hs hba⟩
    | _ => simp [subRT] at h
  | r1p ba =>
    obtain ⟨k, rt, hk, rfl, hba⟩ := hR
    cases b with
    | any => trivial
    | pos =>
      have hk1 : 1 ≤ k := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ⟨1, List.replicate k' 1 ++ rt, by omega, rfl⟩
    | r1 cb bb =>
      simp only [subRT] at h
      rw [eqTail_eq h]
      exact ⟨List.replicate (k - cb.toNat) 1 ++ rt,
        replicate_split 1 (by have := runLen_le4 cb; omega) rt, trivial⟩
    | r1p bb =>
      simp only [subRT] at h
      exact ⟨k, rt, hk, rfl, subTail_sound h hba⟩
    | _ => simp [subRT] at h
  | r2 ca ba =>
    obtain ⟨rt, rfl, hba⟩ := hR
    cases b with
    | any => trivial
    | pos => cases ca <;> exact ⟨2, _, by omega, rfl⟩
    | ge2 => cases ca <;> exact ⟨2, _, by omega, rfl⟩
    | r2 cb bb =>
      simp only [subRT, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨heq, hs⟩ | ⟨hgt, hany⟩
      · rw [eqLen_eq heq]; exact ⟨rt, rfl, subTail_sound hs hba⟩
      · rw [eqTail_eq hany]
        exact ⟨List.replicate (ca.toNat - cb.toNat) 2 ++ rt,
          replicate_split 2 (Nat.le_of_lt (clenGt_lt hgt)) rt, trivial⟩
    | r2p bb =>
      simp only [subRT, Bool.and_eq_true] at h
      obtain ⟨heq, hs⟩ := h
      rw [eqLen_eq heq]
      exact ⟨4, rt, by omega, rfl, subTail_sound hs hba⟩
    | _ => simp [subRT] at h
  | r2p ba =>
    obtain ⟨k, rt, hk, rfl, hba⟩ := hR
    cases b with
    | any => trivial
    | pos =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ⟨2, List.replicate k' 2 ++ rt, by omega, rfl⟩
    | ge2 =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ⟨2, List.replicate k' 2 ++ rt, by omega, rfl⟩
    | r2 cb bb =>
      simp only [subRT] at h
      rw [eqTail_eq h]
      exact ⟨List.replicate (k - cb.toNat) 2 ++ rt,
        replicate_split 2 (by have := runLen_le4 cb; omega) rt, trivial⟩
    | r2p bb =>
      simp only [subRT] at h
      exact ⟨k, rt, hk, rfl, subTail_sound h hba⟩
    | _ => simp [subRT] at h

theorem memSub_sound {t : RT} {ys : List RT} (h : memSub t ys = true) {R : List ℕ} (hR : InRT t R) :
    ∃ y ∈ ys, InRT y R := by
  induction ys with
  | nil => simp [memSub] at h
  | cons y ys ih =>
    simp only [memSub, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · exact ⟨y, List.mem_cons_self .., subRT_sound h1 hR⟩
    · obtain ⟨y', hy', hR'⟩ := ih h2
      exact ⟨y', List.mem_cons_of_mem _ hy', hR'⟩

theorem subList_sound {xs ys : List RT} (h : subList xs ys = true) {x : RT} (hx : x ∈ xs)
    {R : List ℕ} (hR : InRT x R) : ∃ y ∈ ys, InRT y R := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    simp only [subList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact memSub_sound h.1 hR
    · exact ih h.2 hmem

def InBkt (bkt : ExitBuckets) (L : List ℕ) (s : SegState) : Prop :=
  (∃ rs t, t ∈ bkt.mar0 ∧ InRT t rs ∧ s = (.mAR, L, 2 :: rs)) ∨
  (∃ rs t, t ∈ bkt.mar1 ∧ InRT t rs ∧ s = (.mAR, L, 5 :: rs)) ∨
  (∃ n rs t, 2 ≤ n ∧ t ∈ bkt.mar2 ∧ InRT t rs ∧ s = (.mAR, L, (3 * n + 2) :: rs)) ∨
  (∃ rs t, t ∈ bkt.mz0 ∧ InRT t rs ∧ s = (.mA0R, L, 0 :: 1 :: rs)) ∨
  (∃ rs t, t ∈ bkt.mz1 ∧ InRT t rs ∧ s = (.mA0R, L, 0 :: 4 :: rs)) ∨
  (∃ n rs t, 2 ≤ n ∧ t ∈ bkt.mz2 ∧ InRT t rs ∧ s = (.mA0R, L, 0 :: (3 * n + 1) :: rs)) ∨
  (∃ rs t, t ∈ bkt.bump0 ∧ InRT t rs ∧ s = (.mA0R, bump1L L, 2 :: rs)) ∨
  (∃ rs t, t ∈ bkt.bump1 ∧ InRT t rs ∧ s = (.mA0R, bump1L L, 5 :: rs)) ∨
  (∃ n rs t, 2 ≤ n ∧ t ∈ bkt.bump2 ∧ InRT t rs ∧ s = (.mA0R, bump1L L, (3 * n + 2) :: rs))

theorem subsetBkt_sound {src dst : ExitBuckets} (h : subsetBkt src dst = true)
    {L : List ℕ} {s : SegState} (hs : InBkt src L s) : InBkt dst L s := by
  unfold subsetBkt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rcases hs with ⟨rs, t, ht, hrt, rfl⟩ | ⟨rs, t, ht, hrt, rfl⟩ | ⟨n, rs, t, hn, ht, hrt, rfl⟩ |
                 ⟨rs, t, ht, hrt, rfl⟩ | ⟨rs, t, ht, hrt, rfl⟩ | ⟨n, rs, t, hn, ht, hrt, rfl⟩ |
                 ⟨rs, t, ht, hrt, rfl⟩ | ⟨rs, t, ht, hrt, rfl⟩ | ⟨n, rs, t, hn, ht, hrt, rfl⟩
  · obtain ⟨y, hy, hry⟩ := subList_sound h1 ht hrt; exact Or.inl ⟨rs, y, hy, hry, rfl⟩
  · obtain ⟨y, hy, hry⟩ := subList_sound h2 ht hrt; exact Or.inr (Or.inl ⟨rs, y, hy, hry, rfl⟩)
  · obtain ⟨y, hy, hry⟩ := subList_sound h3 ht hrt; exact Or.inr (Or.inr (Or.inl ⟨n, rs, y, hn,
      hy, hry, rfl⟩))
  · obtain ⟨y, hy, hry⟩ := subList_sound h4 ht hrt; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rs, y,
      hy, hry, rfl⟩)))
  · obtain ⟨y, hy, hry⟩ := subList_sound h5 ht hrt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rs, y, hy, hry, rfl⟩))))
  · obtain ⟨y, hy, hry⟩ := subList_sound h6 ht hrt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, rs, y, hn, hy, hry, rfl⟩)))))
  · obtain ⟨y, hy, hry⟩ := subList_sound h7 ht hrt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨rs, y, hy, hry, rfl⟩))))))
  · obtain ⟨y, hy, hry⟩ := subList_sound h8 ht hrt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨rs, y, hy, hry, rfl⟩)))))))
  · obtain ⟨y, hy, hry⟩ := subList_sound h9 ht hrt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr ⟨n, rs, y, hn, hy, hry, rfl⟩)))))))

def MatchesD (d d' : ℕ) : Prop :=
  if d < 6 then d' = d else 6 ≤ d' ∧ d' % 3 = d % 3

theorem matchesD_capD {d d' : ℕ} (hd : MatchesD d d') (c : ℕ) :
    MatchesD (capD (d + c)) (d' + c) := by
  unfold MatchesD at *
  unfold capD
  rcases Nat.lt_or_ge d 6 with hlt | hge
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hlt))] at hd; rw [hd]
    rcases Nat.lt_or_ge (d + c) 9 with h9 | h9
    · have hb : Nat.blt (d + c) 9 = true := Nat.blt_eq.mpr h9
      rw [(ite_eq_left_of_eq_true _ _ (eq_true hb))]
      rcases Nat.lt_or_ge (d + c) 6 with h6 | h6
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true h6))]
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false (by omega)))]; exact ⟨h6, rfl⟩
    · have hf : ¬ (Nat.blt (d + c) 9 = true) := fun hb => by
        have := Nat.blt_eq.mp hb; omega
      rw [(ite_eq_right_of_eq_false _ _ (eq_false hf)), (ite_eq_right_of_eq_false _ _ (eq_false
        (by omega)))]
      exact ⟨by omega, by omega⟩
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false (by omega)))] at hd
    obtain ⟨h6, hmod⟩ := hd
    rcases Nat.lt_or_ge (d + c) 9 with h9 | h9
    · have hb : Nat.blt (d + c) 9 = true := Nat.blt_eq.mpr h9
      rw [(ite_eq_left_of_eq_true _ _ (eq_true hb)), (ite_eq_right_of_eq_false _ _ (eq_false (by
        omega)))]
      exact ⟨by omega, by omega⟩
    · have hf : ¬ (Nat.blt (d + c) 9 = true) := fun hb => by
        have := Nat.blt_eq.mp hb; omega
      rw [(ite_eq_right_of_eq_false _ _ (eq_false hf)), (ite_eq_right_of_eq_false _ _ (eq_false
        (by omega)))]
      exact ⟨by omega, by omega⟩

theorem matchesD_one : MatchesD 1 1 := by unfold MatchesD; rw [(ite_eq_left_of_eq_true _ _
  (eq_true (by omega)))]

theorem matchesD_elPop {d d' c : ℕ} (hd : MatchesD d d') :
    (d' + c) % 3 = (d + c) % 3 ∧ qCap ((d' + c) / 3) = qCap ((d + c) / 3) := by
  unfold MatchesD at hd
  rcases Nat.lt_or_ge d 6 with hlt | hge
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hlt))] at hd; subst hd; exact ⟨rfl, rfl⟩
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false (by omega)))] at hd
    obtain ⟨h6, hmod⟩ := hd
    refine ⟨by omega, ?_⟩
    unfold qCap
    have h1 : Nat.ble 2 ((d' + c) / 3) = true := Nat.ble_eq.mpr (by omega)
    have h2 : Nat.ble 2 ((d + c) / 3) = true := Nat.ble_eq.mpr (by omega)
    rw [h1, h2]; rfl

theorem safe_of_mEL {d d' c : ℕ} (hd : MatchesD d d') {t : RT} {dst : ExitBuckets}
    (hm : memElPop (d + c) t dst = true) {L rs : List ℕ} (hrs : InRT t rs) (fuel : ℕ) :
    SafeFrom (InBkt dst L) (evalSegCfg .mEL ((d' + c) :: L) (0 :: rs)) fuel := by
  have ⟨hmod, hq⟩ := matchesD_elPop (c := c) hd
  set k := d' + c
  have hdiv : k = 3 * (k / 3) + k % 3 := by omega
  have hshift : ReachesIn target_tm (3 * (k / 3))
      (evalSegCfg .mEL (k :: L) (0 :: rs))
      (evalSegCfg .mEL ((k % 3) :: L) ((3 * (k / 3)) :: rs)) := by
    have h := mEL_shift_mul (k / 3) (k % 3) 0 L rs
    rw [Nat.add_zero] at h
    rwa [← hdiv] at h
  unfold memElPop at hm
  rw [← hmod, ← hq] at hm
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with hr | hr | hr
  · rw [hr] at hm hshift
    have hfin := ReachesIn.trans hshift (mEL_d0 (3 * (k / 3)) L rs)
    rcases (by omega : k / 3 = 0 ∨ k / 3 = 1 ∨ 2 ≤ k / 3) with hq0 | hq1 | hq2
    · have hqc : qCap (k / 3) = 0 := by rw [hq0]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      rw [hq0] at hfin
      exact SafeFrom.of_done (by omega) hfin (Or.inl ⟨rs, y, hy, hry, rfl⟩)
    · have hqc : qCap (k / 3) = 1 := by rw [hq1]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      rw [hq1] at hfin
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inl ⟨rs, y, hy, hry, rfl⟩))
    · have hqc : qCap (k / 3) = 2 := by unfold qCap; rw [Nat.ble_eq.mpr hq2]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inl ⟨k / 3, rs, y, hq2, hy, hry,
        rfl⟩)))
  · rw [hr] at hm hshift
    have hfin := ReachesIn.trans hshift (mEL_d1 (3 * (k / 3)) L rs)
    rcases (by omega : k / 3 = 0 ∨ k / 3 = 1 ∨ 2 ≤ k / 3) with hq0 | hq1 | hq2
    · have hqc : qCap (k / 3) = 0 := by rw [hq0]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      rw [hq0] at hfin
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inr (Or.inl ⟨rs, y, hy, hry,
        rfl⟩))))
    · have hqc : qCap (k / 3) = 1 := by rw [hq1]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      rw [hq1] at hfin
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rs, y, hy,
        hry, rfl⟩)))))
    · have hqc : qCap (k / 3) = 2 := by unfold qCap; rw [Nat.ble_eq.mpr hq2]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k /
        3, rs, y, hq2, hy, hry, rfl⟩))))))
  · rw [hr] at hm hshift
    have hfin := ReachesIn.trans hshift (mEL_d2 (3 * (k / 3)) L rs)
    rcases (by omega : k / 3 = 0 ∨ k / 3 = 1 ∨ 2 ≤ k / 3) with hq0 | hq1 | hq2
    · have hqc : qCap (k / 3) = 0 := by rw [hq0]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      rw [hq0] at hfin
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨rs, y, hy, hry, rfl⟩)))))))
    · have hqc : qCap (k / 3) = 1 := by rw [hq1]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      rw [hq1] at hfin
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨rs, y, hy, hry, rfl⟩))))))))
    · have hqc : qCap (k / 3) = 2 := by unfold qCap; rw [Nat.ble_eq.mpr hq2]; rfl
      rw [hqc] at hm; dsimp only at hm
      obtain ⟨y, hy, hry⟩ := memSub_sound hm hrs
      exact SafeFrom.of_done (by omega) hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨k / 3, rs, y, hq2, hy, hry, rfl⟩))))))))

theorem safe_of_mEL0 {d d' : ℕ} (hd : MatchesD d d') {t : RT} {dst : ExitBuckets}
    (hm : memElPop d t dst = true) {L rs : List ℕ} (hrs : InRT t rs) (fuel : ℕ) :
    SafeFrom (InBkt dst L) (evalSegCfg .mEL (d' :: L) (0 :: rs)) fuel :=
  safe_of_mEL (d := d) (d' := d') (c := 0) hd hm hrs fuel

theorem checkDirectList_mem {f : RT → Bool} {ts : List RT}
    (h : checkDirectList f ts = true) {t : RT} (ht : t ∈ ts) : f t = true := by
  induction ts with
  | nil => cases ht
  | cons a ts ih =>
    simp only [checkDirectList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ht with rfl | hmem
    · exact h.1
    · exact ih h.2 hmem

theorem checkMar0_mem {d1 : Nat} {dst : ExitBuckets} {ts : List RT} {hs hs' : List Nat}
    (h : checkMar0 d1 dst ts hs = some hs') {t : RT} (ht : t ∈ ts) :
    ∃ idx, checkDep (.s d1 t) idx dst = true := by
  induction ts generalizing hs with
  | nil => cases ht
  | cons a ts ih =>
    cases hs with
    | nil => simp [checkMar0] at h
    | cons idx hs0 =>
      unfold checkMar0 at h
      rcases hc : checkDep (.s d1 a) idx dst with _ | _
      · rw [hc] at h; cases h
      · rw [hc] at h
        rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
        rcases List.mem_cons.mp ht with rfl | hmem
        · exact ⟨idx, hc⟩
        · exact ih h hmem

theorem checkBump0_mem {d1 : Nat} {dst : ExitBuckets} {ts : List RT} {hs hs' : List Nat}
    (h : checkBump0 d1 dst ts hs = some hs') {t : RT} (ht : t ∈ ts) :
    ∃ idx, checkPropBkt d1 dst idx (.e 0 t) = true := by
  induction ts generalizing hs with
  | nil => cases ht
  | cons a ts ih =>
    cases hs with
    | nil => simp [checkBump0] at h
    | cons idx hs0 =>
      unfold checkBump0 at h
      rcases hc : checkPropBkt d1 dst idx (.e 0 a) with _ | _
      · rw [hc] at h; cases h
      · rw [hc] at h
        rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
        rcases List.mem_cons.mp ht with rfl | hmem
        · exact ⟨idx, hc⟩
        · exact ih h hmem

def Bump1Ok (d2 : Nat) (dst : ExitBuckets) : RT → Prop
  | .r2 c b => ∃ idx, checkPropBkt d2 dst idx (.e c.toNat (cons1 (tailToRT b))) = true
  | .r2p b => ∃ i1 i2, checkPropBkt d2 dst i1 (.e 4 (cons1 (tailToRT b))) = true ∧
                       checkPropBkt d2 dst i2 (.e 4 (.r1 .c1 .any)) = true
  | t => ∃ idx, checkPropBkt d2 dst idx (.e 0 (cons1 t)) = true

theorem checkBump1_mem {d2 : Nat} {dst : ExitBuckets} {ts : List RT} {hs hs' : List Nat}
    (h : checkBump1 d2 dst ts hs = some hs') {t : RT} (ht : t ∈ ts) :
    Bump1Ok d2 dst t := by
  induction ts generalizing hs with
  | nil => cases ht
  | cons a ts ih =>
    unfold checkBump1 at h
    cases a with
    | r2 c b =>
      cases hs with
      | nil => cases h
      | cons idx hs0 =>
        dsimp only at h
        rcases hc : checkPropBkt d2 dst idx (.e c.toNat (cons1 (tailToRT b))) with _ | _
        · rw [hc] at h; cases h
        · rw [hc] at h; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
          rcases List.mem_cons.mp ht with rfl | hmem
          · exact ⟨idx, hc⟩
          · exact ih h hmem
    | r2p b =>
      cases hs with
      | nil => cases h
      | cons i1 hs1 =>
        cases hs1 with
        | nil => cases h
        | cons i2 hs0 =>
          dsimp only at h
          rcases hc : (checkPropBkt d2 dst i1 (.e 4 (cons1 (tailToRT b))) &&
                       checkPropBkt d2 dst i2 (.e 4 (.r1 .c1 .any))) with _ | _
          · rw [hc] at h; cases h
          · rw [hc] at h; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
            rcases List.mem_cons.mp ht with rfl | hmem
            · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
              exact ⟨i1, i2, h1, h2⟩
            · exact ih h hmem
    | _ =>
      cases hs with
      | nil => cases h
      | cons idx hs0 =>
        dsimp only at h
        rcases hc : checkPropBkt d2 dst idx (.e 0 (cons1 _)) with _ | _
        · rw [hc] at h; cases h
        · rw [hc] at h; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
          rcases List.mem_cons.mp ht with rfl | hmem
          · exact ⟨idx, hc⟩
          · exact ih h hmem

/-! ### Semantic Interpretation of Node Specs (`ValidSpec`) -/

def EvalSubCfg (sp : NodeSpec) (L R : List ℕ) (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  match sp with
  | .a d rt => ∃ d', MatchesD d d' ∧ InRT rt R ∧ cfg = evalSegCfg .mA0R (d' :: L) R
  | .s d rt => ∃ d', MatchesD d d' ∧ InRT rt R ∧ cfg = evalSegCfg .mAR (0 :: d' :: L) R
  | .s1 c rt => InRT rt R ∧ cfg = evalSegCfg .mAR (0 :: (List.replicate c 1 ++ L)) R
  | .e k rt => InRT rt R ∧ cfg = evalSegCfg .mAR (0 :: 0 :: (List.replicate k 1 ++ L)) R
  | .prop _ _ => False

def ValidNode (fuel u : Nat) : Prop :=
  match getSpec u with
  | .a d rt => ∀ d' L R, MatchesD d d' → InRT rt R →
      SafeFrom (InBkt (getNodeBkt u) L) (evalSegCfg .mA0R (d' :: L) R) fuel
  | .s d rt => ∀ d' L R, MatchesD d d' → InRT rt R →
      SafeFrom (InBkt (getNodeBkt u) L) (evalSegCfg .mAR (0 :: d' :: L) R) fuel
  | .s1 c rt => ∀ L R, InRT rt R →
      SafeFrom (InBkt (getNodeBkt u) L) (evalSegCfg .mAR (0 :: (List.replicate c 1 ++ L)) R) fuel
  | .e k rt => ∀ L R, InRT rt R →
      SafeFrom (InBkt (getNodeBkt u) L) (evalSegCfg .mAR (0 :: 0 :: (List.replicate k 1 ++ L)) R)
        fuel
  | .prop d sub => ∀ d' L R cfg, MatchesD d d' → EvalSubCfg (getSpec sub) (d' :: L) R cfg →
      SafeFrom (InBkt (getNodeBkt u) L) cfg fuel

theorem use_dep {idx : Nat} {exp : NodeSpec} {dst : ExitBuckets}
    (hc : checkDep exp idx dst = true) :
    idx < numNodes ∧ getSpec idx = exp ∧ subsetBkt (getNodeBkt idx) dst = true := by
  unfold checkDep at hc
  simp only [Bool.and_eq_true] at hc
  exact ⟨Nat.blt_eq.mp hc.1.1, eqSpec_eq hc.1.2, hc.2⟩

theorem use_zdep {u idx : Nat} {exp : NodeSpec} {dst : ExitBuckets}
    (hc : checkZDep u exp idx dst = true) :
    idx < u ∧ getSpec idx = exp ∧ subsetBkt (getNodeBkt idx) dst = true := by
  unfold checkZDep at hc
  simp only [Bool.and_eq_true] at hc
  exact ⟨Nat.blt_eq.mp hc.1.1, eqSpec_eq hc.1.2, hc.2⟩

theorem use_propBkt {d idx : Nat} {dst : ExitBuckets} {expSub : NodeSpec}
    (hc : checkPropBkt d dst idx expSub = true) :
    ∃ s, idx < numNodes ∧ getSpec idx = .prop d s ∧ s < numNodes ∧
         getSpec s = expSub ∧ subsetBkt (getNodeBkt idx) dst = true := by
  unfold checkPropBkt at hc
  rcases hlt : Nat.blt idx numNodes with _ | _
  · rw [hlt] at hc; cases hc
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hlt))] at hc
    rcases hsp : getSpec idx with _ | _ | _ | _ | ⟨d', s⟩
    · rw [hsp] at hc; cases hc
    · rw [hsp] at hc; cases hc
    · rw [hsp] at hc; cases hc
    · rw [hsp] at hc; cases hc
    · rw [hsp] at hc; simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hd', hs⟩, heq⟩, hsub⟩ := hc
      exact ⟨s, Nat.blt_eq.mp hlt, by rw [Nat.eq_of_beq_eq_true hd'], Nat.blt_eq.mp hs, eqSpec_eq
        heq, hsub⟩

theorem checkZDeps_lookup {u : Nat} {dst : ExitBuckets} {es : List NodeSpec} {hs : List Nat}
    (h : checkZDeps u dst es hs = true) {e : NodeSpec} (he : e ∈ es) :
    ∃ idx, idx < u ∧ getSpec idx = e ∧ subsetBkt (getNodeBkt idx) dst = true := by
  induction es generalizing hs with
  | nil => cases he
  | cons a es ih =>
    cases hs with
    | nil => simp [checkZDeps] at h
    | cons i hs' =>
      simp only [checkZDeps, Bool.and_eq_true] at h
      rcases List.mem_cons.mp he with rfl | hm
      · exact ⟨i, use_zdep h.1⟩
      · exact ih h.2 hm

theorem splitRT_cover {rt : RT} {srs : List RT} (h : splitRT rt = some srs) {R : List ℕ} (hR :
  InRT rt R) :
    ∃ sr ∈ srs, InRT sr R := by
  cases rt with
  | any =>
    injection h with hs; subst hs
    rcases R with _ | ⟨hd, tl⟩
    · exact ⟨.nil, by simp, rfl⟩
    · rcases hd with _ | _ | _ | _ | _ | _ | _ | h7
      · exact ⟨.z, by simp, tl, rfl⟩
      · exact ⟨.r1 .c1 .any, by simp, tl, rfl, trivial⟩
      · exact ⟨.r2 .c1 .any, by simp, tl, rfl, trivial⟩
      · exact ⟨.h3, by simp, tl, rfl⟩
      · exact ⟨.h4, by simp, tl, rfl⟩
      · exact ⟨.h5, by simp, tl, rfl⟩
      · exact ⟨.h6, by simp, tl, rfl⟩
      · exact ⟨.ge7, by simp, h7 + 7, tl, by omega, rfl⟩
  | pos =>
    injection h with hs; subst hs
    obtain ⟨hd, tl, hh, rfl⟩ := hR
    rcases hd with _ | _ | _ | _ | _ | _ | _ | h7
    · omega
    · exact ⟨.r1 .c1 .any, by simp, tl, rfl, trivial⟩
    · exact ⟨.r2 .c1 .any, by simp, tl, rfl, trivial⟩
    · exact ⟨.h3, by simp, tl, rfl⟩
    · exact ⟨.h4, by simp, tl, rfl⟩
    · exact ⟨.h5, by simp, tl, rfl⟩
    · exact ⟨.h6, by simp, tl, rfl⟩
    · exact ⟨.ge7, by simp, h7 + 7, tl, by omega, rfl⟩
  | ge2 =>
    injection h with hs; subst hs
    obtain ⟨hd, tl, hh, rfl⟩ := hR
    rcases hd with _ | _ | _ | _ | _ | _ | _ | h7
    · omega
    · omega
    · exact ⟨.r2 .c1 .any, by simp, tl, rfl, trivial⟩
    · exact ⟨.h3, by simp, tl, rfl⟩
    · exact ⟨.h4, by simp, tl, rfl⟩
    · exact ⟨.h5, by simp, tl, rfl⟩
    · exact ⟨.h6, by simp, tl, rfl⟩
    · exact ⟨.ge7, by simp, h7 + 7, tl, by omega, rfl⟩
  | ge3 =>
    injection h with hs; subst hs
    obtain ⟨hd, tl, hh, rfl⟩ := hR
    rcases hd with _ | _ | _ | _ | _ | _ | _ | h7
    · omega
    · omega
    · omega
    · exact ⟨.h3, by simp, tl, rfl⟩
    · exact ⟨.h4, by simp, tl, rfl⟩
    · exact ⟨.h5, by simp, tl, rfl⟩
    · exact ⟨.h6, by simp, tl, rfl⟩
    · exact ⟨.ge7, by simp, h7 + 7, tl, by omega, rfl⟩
  | ge5 =>
    injection h with hs; subst hs
    obtain ⟨hd, tl, hh, rfl⟩ := hR
    rcases hd with _ | _ | _ | _ | _ | _ | _ | h7
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact ⟨.h5, by simp, tl, rfl⟩
    · exact ⟨.h6, by simp, tl, rfl⟩
    · exact ⟨.ge7, by simp, h7 + 7, tl, by omega, rfl⟩
  | _ => simp [splitRT] at h

theorem valid_to_sub {fuel sub : Nat} (hv : ValidNode fuel sub) {L R : List ℕ} {cfg : Cfg (Fin 2)
  (Fin 6)}
    (hev : EvalSubCfg (getSpec sub) L R cfg) :
    SafeFrom (InBkt (getNodeBkt sub) L) cfg fuel := by
  unfold ValidNode at hv
  rcases hsp : getSpec sub with ⟨d, rt⟩ | ⟨d, rt⟩ | ⟨c, rt⟩ | ⟨k, rt⟩ | ⟨d, s⟩
  · rw [hsp] at hv hev
    obtain ⟨d', hd', hR, rfl⟩ := hev; exact hv d' L R hd' hR
  · rw [hsp] at hv hev
    obtain ⟨d', hd', hR, rfl⟩ := hev; exact hv d' L R hd' hR
  · rw [hsp] at hv hev
    obtain ⟨hR, rfl⟩ := hev; exact hv L R hR
  · rw [hsp] at hv hev
    obtain ⟨hR, rfl⟩ := hev; exact hv L R hR
  · rw [hsp] at hev; exact False.elim hev

/-! ### Helper: Discharge a `.prop` dependency call at fuel `m < fuel` -/

theorem call_prop_e {f : Nat} {d d' k idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkPropBkt d dst idx (.e k rt) = true)
    (hd : MatchesD d d') (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: 0 :: (List.replicate k 1 ++ (d' :: L))) R) f := by
  obtain ⟨s, hidx, hsp, hs, hsub, hsb⟩ := use_propBkt hc
  have hv := ihf idx hidx
  unfold ValidNode at hv
  rw [hsp] at hv
  have hev : EvalSubCfg (getSpec s) (d' :: L) R
      (evalSegCfg .mAR (0 :: 0 :: (List.replicate k 1 ++ (d' :: L))) R) := by
    rw [hsub]; exact ⟨hR, rfl⟩
  exact (hv d' L R _ hd hev).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem call_prop_e0 {f : Nat} {d d' idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkPropBkt d dst idx (.e 0 rt) = true)
    (hd : MatchesD d d') (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: 0 :: d' :: L) R) f := by
  simpa only [List.replicate_zero, List.nil_append] using call_prop_e ihf hc hd hR

theorem call_prop_e1 {f : Nat} {d d' idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkPropBkt d dst idx (.e 1 rt) = true)
    (hd : MatchesD d d') (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: 0 :: 1 :: d' :: L) R) f := by
  simpa only [List.replicate_one, List.singleton_append] using call_prop_e ihf hc hd hR

theorem call_prop_a {f : Nat} {d d' dsub idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkPropBkt d dst idx (.a dsub rt) = true)
    (hd : MatchesD d d') (hds : MatchesD dsub dsub) (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mA0R (dsub :: d' :: L) R) f := by
  obtain ⟨s, hidx, hsp, hs, hsub, hsb⟩ := use_propBkt hc
  have hv := ihf idx hidx
  unfold ValidNode at hv
  rw [hsp] at hv
  have hev : EvalSubCfg (getSpec s) (d' :: L) R (evalSegCfg .mA0R (dsub :: d' :: L) R) := by
    rw [hsub]; exact ⟨dsub, hds, hR, rfl⟩
  exact (hv d' L R _ hd hev).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem call_prop_s1 {f : Nat} {d d' c idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkPropBkt d dst idx (.s1 c rt) = true)
    (hd : MatchesD d d') (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: (List.replicate c 1 ++ (d' :: L))) R) f := by
  obtain ⟨s, hidx, hsp, hs, hsub, hsb⟩ := use_propBkt hc
  have hv := ihf idx hidx
  unfold ValidNode at hv
  rw [hsp] at hv
  have hev : EvalSubCfg (getSpec s) (d' :: L) R
      (evalSegCfg .mAR (0 :: (List.replicate c 1 ++ (d' :: L))) R) := by
    rw [hsub]; exact ⟨hR, rfl⟩
  exact (hv d' L R _ hd hev).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem call_a {f : Nat} {d d' idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkDep (.a d rt) idx dst = true)
    (hd : MatchesD d d') (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mA0R (d' :: L) R) f := by
  obtain ⟨hidx, hsp, hsb⟩ := use_dep hc
  have hv := ihf idx hidx
  unfold ValidNode at hv; rw [hsp] at hv
  exact (hv d' L R hd hR).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem call_s {f : Nat} {d d' idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkDep (.s d rt) idx dst = true)
    (hd : MatchesD d d') (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: d' :: L) R) f := by
  obtain ⟨hidx, hsp, hsb⟩ := use_dep hc
  have hv := ihf idx hidx
  unfold ValidNode at hv; rw [hsp] at hv
  exact (hv d' L R hd hR).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem call_s1 {f : Nat} {c idx : Nat} {rt : RT} {dst : ExitBuckets} {L R : List ℕ}
    (ihf : ∀ u, u < numNodes → ValidNode f u)
    (hc : checkDep (.s1 c rt) idx dst = true) (hR : InRT rt R) :
    SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: (List.replicate c 1 ++ L)) R) f := by
  obtain ⟨hidx, hsp, hsb⟩ := use_dep hc
  have hv := ihf idx hidx
  unfold ValidNode at hv; rw [hsp] at hv
  exact (hv L R hR).weaken (fun _ hx => subsetBkt_sound hsb hx)

/-! ### Main Certificate Soundness Theorem (`cert_sound`) -/

theorem cert_sound_a {fuel u d : Nat} {rt : RT} {dst : ExitBuckets} {hs : List Nat}
    (hu : u < numNodes)
    (ih_fuel : ∀ m < fuel, ∀ v, v < numNodes → ValidNode m v)
    (ih_u : ∀ v < u, v < numNodes → ValidNode fuel v)
    (hchk : checkNodeA u d rt dst hs = true) :
    ∀ d' L R, MatchesD d d' → InRT rt R →
      SafeFrom (InBkt dst L) (evalSegCfg .mA0R (d' :: L) R) fuel := by
  unfold checkNodeA at hchk
  intro d' L R hd hR
  rcases hspl : splitRT rt with _ | srs
  · rw [hspl] at hchk; dsimp only at hchk
    cases rt with
    | nil =>
      rw [Bool.and_eq_true] at hchk
      subst hR
      exact SafeFrom.step_prefix (by omega) (lem_A_nil d' L) fun _ =>
        safe_of_mEL hd hchk.2 ⟨[], rfl, rfl⟩ _
    | z =>
      simp only [Bool.and_eq_true] at hchk
      obtain ⟨rt', rfl⟩ := hR
      rcases rt' with _ | ⟨x, y⟩
      · exact SafeFrom.step_prefix (by omega) (step_mA0R_0 (d' :: L) []) fun _ =>
          safe_of_mEL0 hd hchk.1.2 rfl _
      · exact SafeFrom.step_prefix (by omega) (step_mA0R_0 (d' :: L) (x :: y)) fun _ =>
          safe_of_mEL0 hd hchk.2 ⟨x + 1, y, by omega, rfl⟩ _
    | h3 =>
      rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [checkFDeps] at hchk
      · simp [checkFDeps] at hchk
      · simp only [checkFDeps, Bool.and_eq_true] at hchk
        obtain ⟨rt', rfl⟩ := hR
        rcases rt' with _ | ⟨x, y⟩
        · exact SafeFrom.step_prefix (by omega) (lem_A_3_nil d' L) fun hge =>
            call_a (ih_fuel _ (by omega)) hchk.1 (matchesD_capD hd 1) rfl
        · exact SafeFrom.step_prefix (by omega) (lem_A_3_pos d' x L y) fun hge =>
            call_a (ih_fuel _ (by omega)) hchk.2.1 (matchesD_capD hd 1) ⟨x + 3, y, by omega, rfl⟩
      · simp [checkFDeps] at hchk
    | h4 =>
      rcases hs with _ | ⟨i, _ | _⟩
      · cases hchk
      · obtain ⟨rt', rfl⟩ := hR
        exact SafeFrom.step_prefix (by omega) (lem_A_ge4 d' 0 L rt') fun hge =>
          call_prop_e0 (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) ⟨rt', rfl⟩
      · cases hchk
    | h5 =>
      rcases hs with _ | ⟨i, _ | _⟩
      · cases hchk
      · obtain ⟨rt', rfl⟩ := hR
        exact SafeFrom.step_prefix (by omega) (lem_A_ge4 d' 1 L rt') fun hge =>
          call_prop_e0 (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) ⟨rt', rfl, trivial⟩
      · cases hchk
    | h6 =>
      rcases hs with _ | ⟨i, _ | _⟩
      · cases hchk
      · obtain ⟨rt', rfl⟩ := hR
        exact SafeFrom.step_prefix (by omega) (lem_A_ge4 d' 2 L rt') fun hge =>
          call_prop_e0 (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) ⟨rt', rfl, trivial⟩
      · cases hchk
    | ge7 =>
      rw [Bool.and_eq_true] at hchk
      obtain ⟨hd7, rt', hh7, rfl⟩ := hR
      rcases Nat.eq_or_lt_of_le hh7 with rfl | hgt7
      · rcases rt' with _ | ⟨x, y⟩
        · exact SafeFrom.step_prefix (by omega) (lem_A_7_nil d' L) fun _ =>
            safe_of_mEL hd hchk.2 ⟨[], rfl, trivial⟩ _
        · exact SafeFrom.step_prefix (by omega) (lem_A_7_pos d' x L y) fun _ =>
            safe_of_mEL hd hchk.2 ⟨(x + 2) :: y, rfl, trivial⟩ _
      · obtain ⟨x, rfl⟩ : ∃ x, hd7 = x + 8 := ⟨hd7 - 8, by omega⟩
        exact SafeFrom.step_prefix (by omega) (lem_A_ge8 d' x L rt') fun _ =>
          safe_of_mEL hd hchk.2 ⟨1 :: x :: rt', rfl, trivial⟩ _
    | r2 cl b =>
      obtain ⟨rt', rfl, hb⟩ := hR
      cases cl with
      | c1 =>
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · exact SafeFrom.step_prefix (by omega) (step_mA0R_2 (d' :: L) rt') fun hge =>
            call_prop_e0 (ih_fuel _ (by omega)) hchk hd ((inTail_iff_tailToRT b rt').mp hb)
        · cases hchk
      | c2 =>
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · exact SafeFrom.step_prefix (by omega) (step_mA0R_2 (d' :: L) (2 :: rt')) fun hge =>
            call_prop_e0 (ih_fuel _ (by omega)) hchk hd ⟨rt', rfl, hb⟩
        · cases hchk
      | c3 =>
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · exact SafeFrom.step_prefix (by omega) (step_mA0R_2 (d' :: L) (2 :: 2 :: rt')) fun hge =>
            call_prop_e0 (ih_fuel _ (by omega)) hchk hd ⟨rt', rfl, hb⟩
        · cases hchk
      | c4 =>
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · exact SafeFrom.step_prefix (by omega) (step_mA0R_2 (d' :: L) (2 :: 2 :: 2 :: rt')) fun
            hge =>
            call_prop_e0 (ih_fuel _ (by omega)) hchk hd ⟨rt', rfl, hb⟩
        · cases hchk
    | r2p b =>
      obtain ⟨m, rt', hm, rfl, hb⟩ := hR
      rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · cases hchk
      · cases hchk
      · rw [Bool.and_eq_true] at hchk
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [List.replicate_succ, List.cons_append]
        exact SafeFrom.step_prefix (by omega) (step_mA0R_2 (d' :: L) (List.replicate m' 2 ++ rt'))
          fun hge => by
          rcases Nat.eq_or_lt_of_le (by omega : 3 ≤ m') with rfl | hgt
          · exact call_prop_e0 (ih_fuel _ (by omega)) hchk.1 hd ⟨rt', rfl, hb⟩
          · exact call_prop_e0 (ih_fuel _ (by omega)) hchk.2 hd ⟨m', rt', by omega, rfl, hb⟩
      · cases hchk
    | r1 cl b =>
      obtain ⟨rt', rfl, hb⟩ := hR
      cases cl with
      | c1 =>
        rw [Bool.and_eq_true] at hchk
        cases b with
        | nil =>
          subst hb
          exact SafeFrom.step_prefix (by omega) (lem_A_1_nil d' L) fun _ =>
            safe_of_mEL0 hd hchk.2 ⟨[], rfl, rfl⟩ _
        | ge5 =>
          obtain ⟨h5, y, hh5, rfl⟩ := hb
          obtain ⟨x, rfl⟩ : ∃ x, h5 = x + 1 := ⟨h5 - 1, by omega⟩
          exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' x L y) fun _ =>
            safe_of_mEL0 hd hchk.2 ⟨x :: y, rfl, ⟨x, y, by omega, rfl⟩⟩ _
        | ge3 =>
          rw [Bool.and_eq_true] at hchk
          obtain ⟨h3, y, hh3, rfl⟩ := hb
          obtain ⟨x, rfl⟩ : ∃ x, h3 = x + 1 := ⟨h3 - 1, by omega⟩
          exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' x L y) fun _ => by
            rcases Nat.eq_or_lt_of_le (by omega : 2 ≤ x) with rfl | hgt
            · exact safe_of_mEL0 hd hchk.2.1 ⟨y, rfl, trivial⟩ _
            · exact safe_of_mEL0 hd hchk.2.2 ⟨x :: y, rfl, ⟨x, y, by omega, rfl⟩⟩ _
        | any =>
          simp only [Bool.and_eq_true] at hchk
          rcases rt' with _ | ⟨hd1, tl1⟩
          · exact SafeFrom.step_prefix (by omega) (lem_A_1_nil d' L) fun _ =>
              safe_of_mEL0 hd hchk.2.2 ⟨[], rfl, trivial⟩ _
          · rcases hd1 with _ | x
            · rcases tl1 with _ | ⟨hd2, tl2⟩
              · exact SafeFrom.step_prefix (by omega) (lem_A_1_0_nil d' L) fun _ =>
                  safe_of_mEL0 hd hchk.2.1.1 rfl _
              · exact SafeFrom.step_prefix (by omega) (lem_A_1_0_pos d' hd2 L tl2) fun _ =>
                  safe_of_mEL0 hd hchk.2.1.2 ⟨hd2 + 3, tl2, by omega, rfl⟩ _
            · exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' x L tl1) fun _ =>
                safe_of_mEL0 hd hchk.2.2 ⟨x :: tl1, rfl, trivial⟩ _
      | c2 =>
        rw [Bool.and_eq_true] at hchk
        exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' 0 L rt') fun _ =>
          safe_of_mEL0 hd hchk.2 ⟨0 :: rt', rfl, trivial⟩ _
      | c3 =>
        rw [Bool.and_eq_true] at hchk
        exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' 0 L (1 :: rt')) fun _ =>
          safe_of_mEL0 hd hchk.2 ⟨0 :: 1 :: rt', rfl, trivial⟩ _
      | c4 =>
        rw [Bool.and_eq_true] at hchk
        exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' 0 L (1 :: 1 :: rt')) fun _ =>
          safe_of_mEL0 hd hchk.2 ⟨0 :: 1 :: 1 :: rt', rfl, trivial⟩ _
    | r1p b =>
      rw [Bool.and_eq_true] at hchk
      obtain ⟨m, rt', hm, rfl, _⟩ := hR
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append]
      exact SafeFrom.step_prefix (by omega) (lem_A_1_pos d' 0 L (List.replicate m' 1 ++ rt')) fun
        _ =>
        safe_of_mEL0 hd hchk.2 ⟨0 :: (List.replicate m' 1 ++ rt'), rfl, trivial⟩ _
    | ge5 | ge3 | ge2 | pos | any => simp [splitRT] at hspl
  · rw [hspl] at hchk; dsimp only at hchk
    obtain ⟨sr, hsr, hRsr⟩ := splitRT_cover hspl hR
    obtain ⟨idx, hlt, hsp, hsb⟩ := checkZDeps_lookup hchk (List.mem_map_of_mem (f := fun sr =>
      NodeSpec.a d sr) hsr)
    have hv := ih_u idx hlt (by omega)
    unfold ValidNode at hv; rw [hsp] at hv
    exact (hv d' L R hd hRsr).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem cert_sound_s {fuel u d : Nat} {rt : RT} {dst : ExitBuckets} {hs : List Nat}
    (hu : u < numNodes)
    (ih_fuel : ∀ m < fuel, ∀ v, v < numNodes → ValidNode m v)
    (ih_u : ∀ v < u, v < numNodes → ValidNode fuel v)
    (hchk : checkNodeS u d rt dst hs = true) :
    ∀ d' L R, MatchesD d d' → InRT rt R →
      SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: d' :: L) R) fuel := by
  unfold checkNodeS at hchk
  intro d' L R hd hR
  rcases hspl : splitRT rt with _ | srs
  · rw [hspl] at hchk; dsimp only at hchk
    cases rt with
    | nil =>
      rw [Bool.and_eq_true] at hchk
      subst hR
      exact SafeFrom.step_prefix (by omega) (lem_S_nil d' L) fun _ =>
        safe_of_mEL hd hchk.2 ⟨[], rfl, rfl⟩ _
    | z =>
      rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [checkFDeps] at hchk
      · simp [checkFDeps] at hchk
      · simp only [checkFDeps, Bool.and_eq_true] at hchk
        obtain ⟨rt', rfl⟩ := hR
        rcases rt' with _ | ⟨x, y⟩
        · exact SafeFrom.step_prefix (by omega) (step_mAR_3 (d' :: L) []) fun hge =>
            call_a (ih_fuel _ (by omega)) hchk.1 (matchesD_capD hd 1) rfl
        · exact SafeFrom.step_prefix (by omega) (step_mAR_3 (d' :: L) (x :: y)) fun hge =>
            call_a (ih_fuel _ (by omega)) hchk.2.1 (matchesD_capD hd 1) ⟨x + 1, y, by omega, rfl⟩
      · simp [checkFDeps] at hchk
    | h3 =>
      simp only [Bool.and_eq_true] at hchk
      obtain ⟨rt', rfl⟩ := hR
      rcases rt' with _ | ⟨x, y⟩
      · exact SafeFrom.step_prefix (by omega) (lem_S_3_nil d' L) fun _ =>
          safe_of_mEL hd hchk.1.2 rfl _
      · exact SafeFrom.step_prefix (by omega) (lem_S_3_pos d' x L y) fun _ =>
          safe_of_mEL hd hchk.2 ⟨x + 2, y, by omega, rfl⟩ _
    | h4 =>
      rw [Bool.and_eq_true] at hchk
      obtain ⟨rt', rfl⟩ := hR
      exact SafeFrom.step_prefix (by omega) (lem_S_ge4 d' 0 L rt') fun _ =>
        safe_of_mEL hd hchk.2 ⟨0 :: rt', rfl, trivial⟩ _
    | h5 =>
      rw [Bool.and_eq_true] at hchk
      obtain ⟨rt', rfl⟩ := hR
      exact SafeFrom.step_prefix (by omega) (lem_S_ge4 d' 1 L rt') fun _ =>
        safe_of_mEL hd hchk.2 ⟨1 :: rt', rfl, trivial⟩ _
    | h6 =>
      rw [Bool.and_eq_true] at hchk
      obtain ⟨rt', rfl⟩ := hR
      exact SafeFrom.step_prefix (by omega) (lem_S_ge4 d' 2 L rt') fun _ =>
        safe_of_mEL hd hchk.2 ⟨2 :: rt', rfl, trivial⟩ _
    | ge7 =>
      rw [Bool.and_eq_true] at hchk
      obtain ⟨hd7, rt', hh7, rfl⟩ := hR
      obtain ⟨x, rfl⟩ : ∃ x, hd7 = x + 4 := ⟨hd7 - 4, by omega⟩
      exact SafeFrom.step_prefix (by omega) (lem_S_ge4 d' x L rt') fun _ =>
        safe_of_mEL hd hchk.2 ⟨x :: rt', rfl, trivial⟩ _
    | r2 cl b =>
      obtain ⟨rt', rfl, hb⟩ := hR
      rcases hs with _ | ⟨i, _ | _⟩
      · cases hchk
      · have hdesc := seg_desc_run (cl.toNat - 1) (0 :: d' :: L) rt'
        have hrep1 : cl.toNat - 1 + 1 = cl.toNat := by cases cl <;> decide
        rw [hrep1] at hdesc
        have hrepL : List.replicate (cl.toNat - 1) 1 ++ bump1L (0 :: d' :: L) =
            List.replicate cl.toNat 1 ++ (d' :: L) := by
          cases cl <;> rfl
        rw [hrepL] at hdesc
        exact SafeFrom.step_prefix (by cases cl <;> decide) hdesc fun hge =>
          call_prop_s1 (ih_fuel _ (by omega)) hchk hd ((inTail_iff_tailToRT b rt').mp hb)
      · cases hchk
    | r2p b =>
      obtain ⟨m, rt', hm, rfl, hb⟩ := hR
      rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · cases hchk
      · cases hchk
      · rw [Bool.and_eq_true] at hchk
        rw [replicate_split 2 hm rt']
        have hdesc := seg_desc_run 3 (0 :: d' :: L) (List.replicate (m - 4) 2 ++ rt')
        have hrepL : List.replicate 3 1 ++ bump1L (0 :: d' :: L) =
            List.replicate 4 1 ++ (d' :: L) := rfl
        rw [hrepL] at hdesc
        exact SafeFrom.step_prefix (by omega) hdesc fun hge => by
          rcases Nat.eq_or_lt_of_le hm with rfl | hgt
          · simp only [Nat.sub_self, List.replicate_zero, List.nil_append]
            exact call_prop_s1 (ih_fuel _ (by omega)) hchk.1 hd ((inTail_iff_tailToRT b rt').mp hb)
          · obtain ⟨m', hm'⟩ : ∃ m', m - 4 = m' + 1 := ⟨m - 5, by omega⟩
            rw [hm', List.replicate_succ, List.cons_append]
            exact call_prop_s1 (ih_fuel _ (by omega)) hchk.2 hd ⟨List.replicate m' 2 ++ rt', rfl,
              trivial⟩
      · cases hchk
    | r1 cl b =>
      obtain ⟨rt', rfl, hb⟩ := hR
      cases cl with
      | c1 =>
        cases b with
        | nil =>
          rw [Bool.and_eq_true] at hchk
          subst hb
          exact SafeFrom.step_prefix (by omega) (lem_S_1_nil d' L) fun _ =>
            safe_of_mEL hd hchk.2 ⟨[], rfl, rfl⟩ _
        | ge5 =>
          rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
          · cases hchk
          · cases hchk
          · rw [Bool.and_eq_true] at hchk
            obtain ⟨h5, y, hh5, rfl⟩ := hb
            obtain ⟨x, rfl⟩ : ∃ x, h5 = x + 1 := ⟨h5 - 1, by omega⟩
            exact SafeFrom.step_prefix (by omega) (lem_S_1_pos d' x L y) fun hge => by
              rcases Nat.eq_or_lt_of_le (by omega : 4 ≤ x) with rfl | hgt
              · exact call_prop_e0 (ih_fuel _ (by omega)) hchk.1 (matchesD_capD hd 1) ⟨y, rfl⟩
              · exact call_prop_e0 (ih_fuel _ (by omega)) hchk.2 (matchesD_capD hd 1) ⟨x, y, by
                  omega, rfl⟩
          · cases hchk
        | ge3 =>
          rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
          · cases hchk
          · cases hchk
          · rw [Bool.and_eq_true] at hchk
            obtain ⟨h3, y, hh3, rfl⟩ := hb
            obtain ⟨x, rfl⟩ : ∃ x, h3 = x + 1 := ⟨h3 - 1, by omega⟩
            exact SafeFrom.step_prefix (by omega) (lem_S_1_pos d' x L y) fun hge => by
              rcases Nat.eq_or_lt_of_le (by omega : 2 ≤ x) with rfl | hgt
              · exact call_prop_e0 (ih_fuel _ (by omega)) hchk.1 (matchesD_capD hd 1) ⟨y, rfl,
                  trivial⟩
              · exact call_prop_e0 (ih_fuel _ (by omega)) hchk.2 (matchesD_capD hd 1) ⟨x, y, by
                  omega, rfl⟩
          · cases hchk
        | any =>
          rw [Bool.and_eq_true] at hchk
          rcases hs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, _ | _⟩⟩⟩
          · cases hchk.2
          · cases hchk.2
          · cases hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases rt' with _ | ⟨hd1, tl1⟩
            · exact SafeFrom.step_prefix (by omega) (lem_S_1_nil d' L) fun _ =>
                safe_of_mEL hd hchk.1 ⟨[], rfl, rfl⟩ _
            · rcases hd1 with _ | x
              · rcases tl1 with _ | ⟨hd2, tl2⟩
                · exact SafeFrom.step_prefix (by omega) (lem_S_1_0_nil d' L) fun hge =>
                    call_a (ih_fuel _ (by omega)) hchk.2.1.1 (matchesD_capD hd 1) rfl
                · exact SafeFrom.step_prefix (by omega) (lem_S_1_0_pos d' hd2 L tl2) fun hge =>
                    call_a (ih_fuel _ (by omega)) hchk.2.1.2 (matchesD_capD hd 1) ⟨hd2 + 3, tl2,
                      by omega, rfl⟩
              · exact SafeFrom.step_prefix (by omega) (lem_S_1_pos d' x L tl1) fun hge =>
                  call_prop_e0 (ih_fuel _ (by omega)) hchk.2.2 (matchesD_capD hd 1) trivial
          · cases hchk.2
      | c2 =>
        cases b with
        | nil =>
          subst hb
          rcases hs with _ | ⟨i1, _ | _⟩
          · cases hchk
          · exact SafeFrom.step_prefix (by omega) (lem_S_1_1 d' L []) fun hge =>
              call_prop_a (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) matchesD_one rfl
          · cases hchk
        | ge5 =>
          obtain ⟨h5, y, hh5, rfl⟩ := hb
          rcases hs with _ | ⟨i1, _ | _⟩
          · cases hchk
          · exact SafeFrom.step_prefix (by omega) (lem_S_1_1 d' L (h5 :: y)) fun hge =>
              call_prop_a (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) matchesD_one ⟨h5 + 1,
                y, by omega, rfl⟩
          · cases hchk
        | ge3 =>
          obtain ⟨h3, y, hh3, rfl⟩ := hb
          rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
          · cases hchk
          · cases hchk
          · dsimp only [push0Tail] at hchk
            rw [Bool.and_eq_true] at hchk
            exact SafeFrom.step_prefix (by omega) (lem_S_1_1 d' L (h3 :: y)) fun hge => by
              rcases Nat.eq_or_lt_of_le hh3 with rfl | hgt
              · exact call_prop_a (ih_fuel _ (by omega)) hchk.1 (matchesD_capD hd 1) matchesD_one
                  ⟨y, rfl⟩
              · exact call_prop_a (ih_fuel _ (by omega)) hchk.2 (matchesD_capD hd 1) matchesD_one
                  ⟨h3 + 1, y, by omega, rfl⟩
          · cases hchk
        | any =>
          rcases hs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
          · cases hchk
          · cases hchk
          · dsimp only [push0Tail] at hchk
            rw [Bool.and_eq_true] at hchk
            rcases rt' with _ | ⟨hd1, tl1⟩
            · exact SafeFrom.step_prefix (by omega) (lem_S_1_1 d' L []) fun hge =>
                call_prop_a (ih_fuel _ (by omega)) hchk.1 (matchesD_capD hd 1) matchesD_one rfl
            · exact SafeFrom.step_prefix (by omega) (lem_S_1_1 d' L (hd1 :: tl1)) fun hge =>
                call_prop_a (ih_fuel _ (by omega)) hchk.2 (matchesD_capD hd 1) matchesD_one ⟨hd1 +
                  1, tl1, by omega, rfl⟩
          · cases hchk
      | c3 =>
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · exact SafeFrom.step_prefix (by omega) (lem_S_1_1_1 d' L rt') fun hge =>
            call_prop_e1 (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) ((inTail_iff_tailToRT b
              rt').mp hb)
        · cases hchk
      | c4 =>
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · exact SafeFrom.step_prefix (by omega) (lem_S_1_1_1 d' L (1 :: rt')) fun hge =>
            call_prop_e1 (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) ⟨rt', rfl, hb⟩
        · cases hchk
    | r1p b =>
      obtain ⟨m, rt', hm, rfl, _⟩ := hR
      rcases hs with _ | ⟨i, _ | _⟩
      · cases hchk
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 4 := ⟨m - 4, by omega⟩
        rw [replicate_split 1 (by omega : 3 ≤ m' + 4) rt']
        have hsub : m' + 4 - 3 = m' + 1 := by omega
        rw [hsub]
        exact SafeFrom.step_prefix (by omega) (lem_S_1_1_1 d' L (List.replicate (m' + 1) 1 ++
          rt')) fun hge =>
          call_prop_e1 (ih_fuel _ (by omega)) hchk (matchesD_capD hd 1) ⟨List.replicate m' 1 ++
            rt', rfl, trivial⟩
      · cases hchk
    | ge5 | ge3 | ge2 | pos | any => simp [splitRT] at hspl
  · rw [hspl] at hchk; dsimp only at hchk
    obtain ⟨sr, hsr, hRsr⟩ := splitRT_cover hspl hR
    obtain ⟨idx, hlt, hsp, hsb⟩ := checkZDeps_lookup hchk (List.mem_map_of_mem (f := fun sr =>
      NodeSpec.s d sr) hsr)
    have hv := ih_u idx hlt (by omega)
    unfold ValidNode at hv; rw [hsp] at hv
    exact (hv d' L R hd hRsr).weaken (fun _ hx => subsetBkt_sound hsb hx)

theorem cert_sound_s1 {fuel u c : Nat} {rt : RT} {dst : ExitBuckets} {hs : List Nat}
    (hu : u < numNodes)
    (ih_fuel : ∀ m < fuel, ∀ v, v < numNodes → ValidNode m v)
    (ih_u : ∀ v < u, v < numNodes → ValidNode fuel v)
    (hchk : checkNodeS1 u c rt dst hs = true) :
    ∀ L R, InRT rt R →
      SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: (List.replicate c 1 ++ L)) R) fuel := by
  unfold checkNodeS1 at hchk
  intro L R hR
  rcases c with _ | _ | c'
  · have h00 : Nat.beq 0 0 = true := by decide
    rw [(ite_eq_left_of_eq_true _ _ (eq_true h00))] at hchk; cases hchk
  · have h10 : ¬ (Nat.beq (0 + 1) 0 = true) := by decide
    have h11 : Nat.beq (0 + 1) 1 = true := by decide
    rw [(ite_eq_right_of_eq_false _ _ (eq_false h10)), (ite_eq_left_of_eq_true _ _ (eq_true h11))]
      at hchk
    rcases hs with _ | ⟨i, _ | _⟩
    · cases hchk
    · obtain ⟨hlt, hsp, hsb⟩ := use_zdep hchk
      have hv := ih_u i hlt (by omega)
      unfold ValidNode at hv; rw [hsp] at hv
      simpa only [Nat.zero_add, List.replicate_one, List.singleton_append] using
        (hv 1 L R matchesD_one hR).weaken (fun _ hx => subsetBkt_sound hsb hx)
    · cases hchk
  · set c := c' + 2
    have hne0 : ¬ (Nat.beq c 0 = true) := fun hb => by have := Nat.eq_of_beq_eq_true hb; omega
    have hne1 : ¬ (Nat.beq c 1 = true) := fun hb => by have := Nat.eq_of_beq_eq_true hb; omega
    rw [(ite_eq_right_of_eq_false _ _ (eq_false hne0)), (ite_eq_right_of_eq_false _ _ (eq_false
      hne1))] at hchk
    cases rt with
    | r2 cl b =>
      dsimp only at hchk
      rcases hle : Nat.ble (c + cl.toNat) 7 with _ | _
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false (by rw [hle]; decide)))] at hchk
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · rw [Bool.and_eq_true] at hchk
          have hlt : i < u := Nat.blt_eq.mp hchk.1
          obtain ⟨s, _, hsp, _, hsub, hsb⟩ := use_propBkt hchk.2
          have hv := ih_u i hlt (by omega)
          unfold ValidNode at hv; rw [hsp] at hv
          have hrep : List.replicate c 1 ++ L = List.replicate (c - 1) 1 ++ (1 :: L) := by
            have hc' : c = (c - 1) + 1 := by omega
            conv_lhs => rw [hc']
            rw [List.replicate_succ', List.append_assoc]; rfl
          rw [hrep]
          have hev : EvalSubCfg (getSpec s) (1 :: L) R
              (evalSegCfg .mAR (0 :: (List.replicate (c - 1) 1 ++ (1 :: L))) R) := by
            rw [hsub]; exact ⟨hR, rfl⟩
          exact (hv 1 L R _ matchesD_one hev).weaken (fun _ hx => subsetBkt_sound hsb hx)
        · cases hchk
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hle))] at hchk
        obtain ⟨rt', rfl, hbt⟩ := hR
        rcases hs with _ | ⟨i, _ | _⟩
        · cases hchk
        · have hdesc := seg_desc_run (cl.toNat - 1) (0 :: (List.replicate c 1 ++ L)) rt'
          have hrep1 : cl.toNat - 1 + 1 = cl.toNat := by cases cl <;> decide
          rw [hrep1] at hdesc
          have hrepL : List.replicate (cl.toNat - 1) 1 ++ bump1L (0 :: (List.replicate c 1 ++ L)) =
              List.replicate (c + cl.toNat) 1 ++ L := by
            simp only [bump1L]
            have h1 : (1 : ℕ) :: (List.replicate c 1 ++ L) = List.replicate (c + 1) 1 ++ L := by
              rw [← List.cons_append, ← List.replicate_succ]
            rw [h1, ← List.append_assoc, ← List.replicate_add]
            exact congrArg (fun n => List.replicate n 1 ++ L) (by cases cl <;> simp [RunLen.toNat]
              <;> omega)
          rw [hrepL] at hdesc
          exact SafeFrom.step_prefix (by cases cl <;> decide) hdesc fun hge =>
            call_s1 (ih_fuel _ (by omega)) hchk ((inTail_iff_tailToRT b rt').mp hbt)
        · cases hchk
    | _ =>
      dsimp only at hchk
      rcases hs with _ | ⟨i, _ | _⟩
      · cases hchk
      · rw [Bool.and_eq_true] at hchk
        have hlt : i < u := Nat.blt_eq.mp hchk.1
        obtain ⟨s, _, hsp, _, hsub, hsb⟩ := use_propBkt hchk.2
        have hv := ih_u i hlt (by omega)
        unfold ValidNode at hv; rw [hsp] at hv
        have hrep : List.replicate c 1 ++ L = List.replicate (c - 1) 1 ++ (1 :: L) := by
          have hc' : c = (c - 1) + 1 := by omega
          conv_lhs => rw [hc']
          rw [List.replicate_succ', List.append_assoc]; rfl
        rw [hrep]
        have hev : EvalSubCfg (getSpec s) (1 :: L) R
            (evalSegCfg .mAR (0 :: (List.replicate (c - 1) 1 ++ (1 :: L))) R) := by
          rw [hsub]; exact ⟨hR, rfl⟩
        exact (hv 1 L R _ matchesD_one hev).weaken (fun _ hx => subsetBkt_sound hsb hx)
      · cases hchk

theorem cert_sound_e {fuel u k : Nat} {rt : RT} {dst : ExitBuckets} {hs : List Nat}
    (hu : u < numNodes)
    (ih_u : ∀ v < u, v < numNodes → ValidNode fuel v)
    (hchk : checkNodeE u k rt dst hs = true) :
    ∀ L R, InRT rt R →
      SafeFrom (InBkt dst L) (evalSegCfg .mAR (0 :: 0 :: (List.replicate k 1 ++ L)) R) fuel := by
  unfold checkNodeE at hchk
  intro L R hR
  rcases k with _ | k'
  · have h00 : Nat.beq 0 0 = true := by decide
    rw [(ite_eq_left_of_eq_true _ _ (eq_true h00))] at hchk
    rcases hs with _ | ⟨i, _ | _⟩
    · cases hchk
    · obtain ⟨hlt, hsp, hsb⟩ := use_zdep hchk
      have hv := ih_u i hlt (by omega)
      unfold ValidNode at hv; rw [hsp] at hv
      have h0 : MatchesD 0 0 := by unfold MatchesD; rw [(ite_eq_left_of_eq_true _ _ (eq_true (by
        omega)))]
      simpa only [List.replicate_zero, List.nil_append] using
        (hv 0 L R h0 hR).weaken (fun _ hx => subsetBkt_sound hsb hx)
    · cases hchk
  · have hne0 : ¬ (Nat.beq (k' + 1) 0 = true) := fun hb => by
      have := Nat.eq_of_beq_eq_true hb; omega
    rw [(ite_eq_right_of_eq_false _ _ (eq_false hne0))] at hchk
    rcases hs with _ | ⟨i, _ | _⟩
    · cases hchk
    · rw [Bool.and_eq_true] at hchk
      have hlt : i < u := Nat.blt_eq.mp hchk.1
      obtain ⟨s, _, hsp, _, hsub, hsb⟩ := use_propBkt hchk.2
      have hv := ih_u i hlt (by omega)
      unfold ValidNode at hv; rw [hsp] at hv
      have hrep : List.replicate (k' + 1) 1 ++ L = List.replicate k' 1 ++ (1 :: L) := by
        rw [List.replicate_succ', List.append_assoc]; rfl
      rw [hrep]
      have hev : EvalSubCfg (getSpec s) (1 :: L) R
          (evalSegCfg .mAR (0 :: 0 :: (List.replicate k' 1 ++ (1 :: L))) R) := by
        rw [hsub]; exact ⟨hR, rfl⟩
      exact (hv 1 L R _ matchesD_one hev).weaken (fun _ hx => subsetBkt_sound hsb hx)
    · cases hchk

theorem cert_sound_prop {fuel u d sub : Nat} {dst : ExitBuckets} {hs : List Nat}
    (hu : u < numNodes)
    (ih_fuel : ∀ m < fuel, ∀ v, v < numNodes → ValidNode m v)
    (ih_u : ∀ v < u, v < numNodes → ValidNode fuel v)
    (hchk : checkNodeProp u d sub dst hs = true) :
    ∀ d' L R cfg, MatchesD d d' → EvalSubCfg (getSpec sub) (d' :: L) R cfg →
      SafeFrom (InBkt dst L) cfg fuel := by
  unfold checkNodeProp at hchk
  dsimp only at hchk
  intro d' L R cfg hd hev
  rcases hlt_sub : Nat.blt sub u with _ | _
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false (by rw [hlt_sub]; decide)))] at hchk; cases hchk
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hlt_sub))] at hchk
    have hsub_lt : sub < u := Nat.blt_eq.mp hlt_sub
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨⟨⟨⟨⟨⟨h_mar1, h_mar2⟩, h_mz0⟩, h_mz1⟩, h_mz2⟩, h_bump2⟩, h_rest⟩ := hchk
    rcases hm0 : checkMar0 (capD (d + 1)) dst (getNodeBkt sub).mar0 hs with _ | hs1
    · rw [hm0] at h_rest; cases h_rest
    · rw [hm0] at h_rest; dsimp only at h_rest
      rcases hb0 : checkBump0 (capD (d + 1)) dst (getNodeBkt sub).bump0 hs1 with _ | hs2
      · rw [hb0] at h_rest; cases h_rest
      · rw [hb0] at h_rest; dsimp only at h_rest
        rcases hb1 : checkBump1 (capD (capD (d + 1) + 1)) dst (getNodeBkt sub).bump1 hs2 with _
          | hs3
        · rw [hb1] at h_rest; cases h_rest
        · rw [hb1] at h_rest
          have hv_sub := ih_u sub hsub_lt (by omega)
          refine (valid_to_sub hv_sub hev).bind fun m s' hm1 hmle hs' => ?_
          rcases hs' with ⟨rs, t, ht, hrt, rfl⟩ | ⟨rs, t, ht, hrt, rfl⟩ | ⟨n, rs, t, hn, ht, hrt,
            rfl⟩ |
                          ⟨rs, t, ht, hrt, rfl⟩ | ⟨rs, t, ht, hrt, rfl⟩ | ⟨n, rs, t, hn, ht, hrt,
                            rfl⟩ |
                          ⟨rs, t, ht, hrt, rfl⟩ | ⟨rs, t, ht, hrt, rfl⟩ | ⟨n, rs, t, hn, ht, hrt,
                            rfl⟩
          · -- mar0: `mAR (d' :: L) (2 :: rs)` -> `mAR (0 :: (d' + 1) :: L) rs`
            obtain ⟨idx, hdep⟩ := checkMar0_mem hm0 ht
            exact SafeFrom.step_prefix (by omega) (step_mAR_2_loop (d' :: L) rs) fun hge =>
              call_s (ih_fuel _ (by omega)) hdep (matchesD_capD hd 1) hrt
          · -- mar1: `mAR (d' :: L) (5 :: rs)` -> `mEL ((d' + 3) :: L) (0 :: 1 :: rs)`
            have hdir := checkDirectList_mem h_mar1 ht
            exact SafeFrom.step_prefix (by omega) (lem_MAR_ge5 d' 0 L rs) fun _ =>
              safe_of_mEL hd hdir (cons1_sound hrt) _
          · -- mar2: `mAR (d' :: L) ((3*n + 2) :: rs)` with `2 ≤ n`
            have hne : (getNodeBkt sub).mar2.isEmpty = false := by
              cases h : (getNodeBkt sub).mar2 <;> [rw [h] at ht; rfl]; cases ht
            simp only [hne, Bool.false_or] at h_mar2
            have hx : 3 * n + 2 = (3 * n - 3) + 5 := by omega
            rw [hx]
            exact SafeFrom.step_prefix (by omega) (lem_MAR_ge5 d' (3 * n - 3) L rs) fun _ =>
              safe_of_mEL hd h_mar2 ⟨3 * n - 3 + 1, rs, by omega, rfl⟩ _
          · -- mz0: `mA0R (d' :: L) (0 :: 1 :: rs)` -> `mEL (d' :: L) (0 :: 2 :: rs)`
            have hdir := checkDirectList_mem h_mz0 ht
            exact SafeFrom.step_prefix (by omega) (step_mA0R_0 (d' :: L) (1 :: rs)) fun _ =>
              safe_of_mEL0 hd hdir (cons2_sound hrt) _
          · -- mz1: `mA0R (d' :: L) (0 :: 4 :: rs)` -> `mEL (d' :: L) (0 :: 5 :: rs)`
            have hne : (getNodeBkt sub).mz1.isEmpty = false := by
              cases h : (getNodeBkt sub).mz1 <;> [rw [h] at ht; rfl]; cases ht
            simp only [hne, Bool.false_or] at h_mz1
            exact SafeFrom.step_prefix (by omega) (step_mA0R_0 (d' :: L) (4 :: rs)) fun _ =>
              safe_of_mEL0 hd h_mz1 ⟨rs, rfl⟩ _
          · -- mz2: `mA0R (d' :: L) (0 :: (3*n + 1) :: rs)` with `2 ≤ n`
            have hne : (getNodeBkt sub).mz2.isEmpty = false := by
              cases h : (getNodeBkt sub).mz2 <;> [rw [h] at ht; rfl]; cases ht
            simp only [hne, Bool.false_or] at h_mz2
            exact SafeFrom.step_prefix (by omega) (step_mA0R_0 (d' :: L) ((3 * n + 1) :: rs)) fun
              _ =>
              safe_of_mEL0 hd h_mz2 ⟨3 * n + 2, rs, by omega, rfl⟩ _
          · -- bump0: `mA0R ((d' + 1) :: L) (2 :: rs)` -> `mAR (0 :: 0 :: (d' + 1) :: L) rs`
            obtain ⟨idx, hdep⟩ := checkBump0_mem hb0 ht
            exact SafeFrom.step_prefix (by omega) (step_mA0R_2 ((d' + 1) :: L) rs) fun hge =>
              call_prop_e0 (ih_fuel _ (by omega)) hdep (matchesD_capD hd 1) hrt
          · -- bump1: `mA0R ((d' + 1) :: L) (5 :: rs)` -> `mAR (0 :: 0 :: (d' + 2) :: L) (1 :: rs)`
            have hbm := checkBump1_mem hb1 ht
            unfold Bump1Ok at hbm
            have hd1 : MatchesD (capD (d + 1)) (d' + 1) := matchesD_capD hd 1
            have hd2 : MatchesD (capD (capD (d + 1) + 1)) (d' + 2) := by
              have h := matchesD_capD hd1 1; simpa only [Nat.add_assoc] using h
            cases t with
            | r2 cl b =>
              obtain ⟨idx, hdep⟩ := hbm
              obtain ⟨rt', rfl, hbt⟩ := hrt
              have hstep := ReachesIn.trans (lem_A_ge4 (d' + 1) 1 L (List.replicate cl.toNat 2 ++
                rt'))
                (lem_BUMP_push2_run cl.toNat ((d' + 2) :: L) rt')
              exact SafeFrom.step_prefix (by omega) hstep fun hge =>
                call_prop_e (ih_fuel _ (by omega)) hdep hd2 (cons1_sound ((inTail_iff_tailToRT b
                  rt').mp hbt))
            | r2p b =>
              obtain ⟨i1, i2, hdep1, hdep2⟩ := hbm
              obtain ⟨k2, rt', hk2, rfl, hbt⟩ := hrt
              rw [replicate_split 2 hk2 rt']
              have hstep := ReachesIn.trans
                (lem_A_ge4 (d' + 1) 1 L (List.replicate 4 2 ++ (List.replicate (k2 - 4) 2 ++ rt')))
                (lem_BUMP_push2_run 4 ((d' + 2) :: L) (List.replicate (k2 - 4) 2 ++ rt'))
              exact SafeFrom.step_prefix (by omega) hstep fun hge => by
                rcases Nat.eq_or_lt_of_le hk2 with rfl | hgt
                · simp only [Nat.sub_self, List.replicate_zero, List.nil_append]
                  exact call_prop_e (ih_fuel _ (by omega)) hdep1 hd2 (cons1_sound
                    ((inTail_iff_tailToRT b rt').mp hbt))
                · exact call_prop_e (ih_fuel _ (by omega)) hdep2 hd2 ⟨List.replicate (k2 - 4) 2 ++
                    rt', rfl, trivial⟩
            | _ =>
              obtain ⟨idx, hdep⟩ := hbm
              exact SafeFrom.step_prefix (by omega) (lem_A_ge4 (d' + 1) 1 L rs) fun hge =>
                call_prop_e0 (ih_fuel _ (by omega)) hdep hd2 (cons1_sound hrt)
          · -- bump2: `mA0R ((d' + 1) :: L) ((3*n + 2) :: rs)` with `2 ≤ n`
            have hne : (getNodeBkt sub).bump2.isEmpty = false := by
              cases h : (getNodeBkt sub).bump2 <;> [rw [h] at ht; rfl]; cases ht
            simp only [hne, Bool.false_or] at h_bump2
            have hx : 3 * n + 2 = (3 * n - 6) + 8 := by omega
            rw [hx]
            have hd1 : MatchesD (capD (d + 1)) (d' + 1) := matchesD_capD hd 1
            exact SafeFrom.step_prefix (by omega) (lem_A_ge8 (d' + 1) (3 * n - 6) L rs) fun _ =>
              safe_of_mEL hd1 h_bump2 ⟨(3 * n - 6) :: rs, rfl, trivial⟩ _

theorem cert_sound (fuel : ℕ) : ∀ u : Nat, u < numNodes → ValidNode fuel u := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih_fuel =>
    intro u hu
    induction u using Nat.strong_induction_on with
    | h u ih_u =>
      have hchk := cert_all u hu
      unfold checkNode at hchk
      dsimp only at hchk
      unfold ValidNode
      have hsp_eq : getSpec u = (getEntry u).spec := rfl
      have hnb : getNodeBkt u = getBkt (getEntry u).bktId := rfl
      rw [hsp_eq, hnb]
      generalize hsp : (getEntry u).spec = sp at hchk ⊢
      cases sp with
      | a d rt => exact cert_sound_a hu ih_fuel ih_u hchk
      | s d rt => exact cert_sound_s hu ih_fuel ih_u hchk
      | s1 c rt => exact cert_sound_s1 hu ih_fuel ih_u hchk
      | e k rt => exact cert_sound_e hu ih_u hchk
      | prop d sub => exact cert_sound_prop hu ih_fuel ih_u hchk

/-! ## Section 6: Closing the Exponential Loop and Main Theorem (`IsNotHalt target_tm`) -/

theorem e6_spec : getSpec 576 = .e 6 .any := rfl
theorem s1_7_spec : getSpec 577 = .s1 7 .any := rfl

theorem e6_bkt_eq : getNodeBkt 576 =
    ⟨[], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .any), .h5], [], [], [],
      [], []⟩ := rfl

theorem s1_7_bkt_eq : getNodeBkt 577 =
    ⟨[], [], [], [(.r2 .c1 .ge5), (.r2 .c2 .ge5), (.r2 .c3 .ge5), (.r2p .ge5), .h5], [], [], [],
      [], []⟩ := rfl

theorem inBkt_e6_mz0 {L : List ℕ} {s : SegState} (h : InBkt (getNodeBkt 576) L s) :
    ∃ rs, s = (.mA0R, L, 0 :: 1 :: rs) := by
  rw [e6_bkt_eq] at h
  rcases h with ⟨_, _, ht, _, _⟩ | ⟨_, _, ht, _, _⟩ | ⟨_, _, _, _, ht, _, _⟩ |
                ⟨rs, _, _, _, hs⟩ | ⟨_, _, ht, _, _⟩ | ⟨_, _, _, _, ht, _, _⟩ |
                ⟨_, _, ht, _, _⟩ | ⟨_, _, ht, _, _⟩ | ⟨_, _, _, _, ht, _, _⟩
  · cases ht
  · cases ht
  · cases ht
  · exact ⟨rs, hs⟩
  · cases ht
  · cases ht
  · cases ht
  · cases ht
  · cases ht

theorem inBkt_s1_7_ge5 {L : List ℕ} {s : SegState} (h : InBkt (getNodeBkt 577) L s) :
    ∃ c h5 rt, 5 ≤ h5 ∧ s = (.mA0R, L, 0 :: 1 :: List.replicate c 2 ++ h5 :: rt) := by
  rw [s1_7_bkt_eq] at h
  rcases h with ⟨_, _, ht, _, _⟩ | ⟨_, _, ht, _, _⟩ | ⟨_, _, _, _, ht, _, _⟩ |
                ⟨rs, t, ht, hrt, hs⟩ | ⟨_, _, ht, _, _⟩ | ⟨_, _, _, _, ht, _, _⟩ |
                ⟨_, _, ht, _, _⟩ | ⟨_, _, ht, _, _⟩ | ⟨_, _, _, _, ht, _, _⟩
  · cases ht
  · cases ht
  · cases ht
  · subst hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨rt, rfl, h5, y, hh5, rfl⟩ := hrt; exact ⟨1, h5, y, hh5, rfl⟩
    · obtain ⟨rt, rfl, h5, y, hh5, rfl⟩ := hrt; exact ⟨2, h5, y, hh5, rfl⟩
    · obtain ⟨rt, rfl, h5, y, hh5, rfl⟩ := hrt; exact ⟨3, h5, y, hh5, rfl⟩
    · obtain ⟨c, rt, hc, rfl, h5, y, hh5, rfl⟩ := hrt; exact ⟨c, h5, y, hh5, rfl⟩
    · obtain ⟨rt, rfl⟩ := hrt; exact ⟨0, 5, rt, by omega, rfl⟩
  · cases ht
  · cases ht
  · cases ht
  · cases ht
  · cases ht

theorem loop_safe (fuel : ℕ) :
    ∀ (k : ℕ) (R : List ℕ), 42 ≤ k → ∃ c', ReachesIn target_tm fuel (evalSegCfg .mAR (E k) R) c'
      := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro k R hk
    -- Step 1: split E k into E(6) above L_bot = 1^(k - 6) ++ [0]
    have hE : E k = 0 :: 0 :: (List.replicate 6 1 ++ (List.replicate (k - 6) 1 ++ [0])) := by
      unfold E
      rw [← List.append_assoc (List.replicate 6 1), ← List.replicate_add]
      exact congrArg (fun m => 0 :: 0 :: (List.replicate m 1 ++ [0])) (by omega)
    have hvE := cert_sound fuel 576 (by unfold numNodes; omega)
    unfold ValidNode at hvE; rw [e6_spec] at hvE
    have hsafe1 : SafeFrom (InBkt (getNodeBkt 576) (List.replicate (k - 6) 1 ++ [0]))
        (evalSegCfg .mAR (E k) R) fuel := by
      rw [hE]; exact hvE (List.replicate (k - 6) 1 ++ [0]) R trivial
    rcases hsafe1 with hc | ⟨m1, s1, hm1, hm1le, hrm1, hs1⟩
    · exact hc
    · obtain ⟨rs1, rfl⟩ := inBkt_e6_mz0 hs1
      -- Step 2: drain 1^(k - 6) ++ [0] to mAR [] (2^(k - 4) ++ rs1)
      have hdr1 : ReachesIn target_tm (3 * (k - 6) + 3)
          (evalSegCfg .mA0R (List.replicate (k - 6) 1 ++ [0]) (0 :: 1 :: rs1))
          (evalSegCfg .mAR [] (List.replicate (k - 4) 2 ++ rs1)) := by
        have h := drain_ones_to_2 (k - 7) rs1
        have he1 : k - 7 + 1 = k - 6 := by omega
        have he2 : k - 7 + 3 = k - 4 := by omega
        rw [he1, he2] at h; exact h
      -- Step 3: seg_desc_run on a = k - 4 gives 0 :: 1^(k - 5) ++ [0]
      have hdesc : ReachesIn target_tm (3 * (k - 4))
          (evalSegCfg .mAR [] (List.replicate (k - 4) 2 ++ rs1))
          (evalSegCfg .mAR (0 :: (List.replicate 7 1 ++ (List.replicate (k - 12) 1 ++ [0]))) rs1)
            := by
        have h := seg_desc_run (k - 5) [] rs1
        have he1 : k - 5 + 1 = k - 4 := by omega
        rw [he1] at h
        have hL : (0 : ℕ) :: (List.replicate (k - 5) 1 ++ bump1L []) =
            0 :: (List.replicate 7 1 ++ (List.replicate (k - 12) 1 ++ [0])) := by
          simp only [bump1L]
          rw [← List.append_assoc (List.replicate 7 1), ← List.replicate_add]
          exact congrArg (fun m => 0 :: (List.replicate m 1 ++ [0])) (by omega)
        rwa [hL] at h
      have hmid := ReachesIn.trans hrm1 (ReachesIn.trans hdr1 hdesc)
      rcases Nat.lt_or_ge fuel (m1 + (3 * (k - 6) + 3 + 3 * (k - 4))) with hlt | hge
      · exact reachesIn_prefix (by omega) hmid
      · -- Step 4: apply S1(7, ANY) at remaining fuel `rem1`
        set rem1 := fuel - (m1 + (3 * (k - 6) + 3 + 3 * (k - 4)))
        have hvS := cert_sound rem1 577 (by unfold numNodes; omega)
        unfold ValidNode at hvS; rw [s1_7_spec] at hvS
        have hsafe2 := hvS (List.replicate (k - 12) 1 ++ [0]) rs1 trivial
        rcases hsafe2 with ⟨c', hc'⟩ | ⟨m2, s2, hm2, hm2le, hrm2, hs2⟩
        · exact ⟨c', reachesIn_cast (ReachesIn.trans hmid hc') (by omega)⟩
        · obtain ⟨c, h5, rt, hh5, rfl⟩ := inBkt_s1_7_ge5 hs2
          -- Step 5: drain 1^(k - 12) ++ [0] to mAR [] (2^(k - 10 + c) ++ h5 :: rt)
          have hdr2 : ReachesIn target_tm (3 * (k - 12) + 3)
              (evalSegCfg .mA0R (List.replicate (k - 12) 1 ++ [0]) (0 :: 1 :: (List.replicate c 2
                ++ h5 :: rt)))
              (evalSegCfg .mAR [] (List.replicate (k - 10 + c) 2 ++ h5 :: rt)) := by
            have h := drain_ones_to_2 (k - 13) (List.replicate c 2 ++ h5 :: rt)
            have he1 : k - 13 + 1 = k - 12 := by omega
            have he2 : k - 13 + 3 = k - 10 := by omega
            rw [he1, he2, ← List.append_assoc, ← List.replicate_add] at h
            exact h
          -- Step 6: universal h >= 4 sweep + seg_drain + seg_sea_enter
          set a' := k - 10 + c
          have ha' : 32 ≤ a' := by omega
          have ht4 : h5 = (h5 - 4) + 4 := by omega
          have hsw : ReachesIn target_tm (6 * (a' - 1) + 23)
              (evalSegCfg .mAR [] (List.replicate a' 2 ++ h5 :: rt))
              (evalSegCfg .mAR [] (List.replicate (a' - 1) 2 ++ 5 :: 1 :: (h5 - 4) :: rt)) := by
            have h := seg_sweep_ge4 (a' - 1) (h5 - 4) rt
            have ha1 : a' - 1 + 1 = a' := by omega
            rw [ha1, ← ht4] at h; exact h
          have hdrain : ReachesIn target_tm (3 * (a' - 1) * (a' - 1) + 20 * (a' - 1))
              (evalSegCfg .mAR [] (List.replicate (a' - 1) 2 ++ 5 :: 1 :: (h5 - 4) :: rt))
              (evalSegCfg .mAR [] (5 :: (List.replicate (2 * a' - 1) 1 ++ (h5 - 4) :: rt))) := by
            have h := seg_drain (a' - 1) (1 :: (h5 - 4) :: rt)
            have hrep : List.replicate (2 * (a' - 1)) 1 ++ 1 :: (h5 - 4) :: rt =
                List.replicate (2 * a' - 1) 1 ++ (h5 - 4) :: rt := by
              have hb : 2 * a' - 1 = 2 * (a' - 1) + 1 := by omega
              rw [hb, List.replicate_succ', List.append_assoc]; rfl
            rwa [hrep] at h
          have hsea : ReachesIn target_tm (14 + 18 * (2 * a' / 3))
              (evalSegCfg .mAR [] (5 :: (List.replicate (2 * a' - 1) 1 ++ (h5 - 4) :: rt)))
              (evalSegCfg .mAR (E (2 * ((2 * a') / 3)))
                (List.replicate ((2 * a') % 3) 1 ++ (h5 - 4) :: rt)) := by
            have h := seg_sea_enter (2 * a' - 2) ((h5 - 4) :: rt)
            have he1 : 2 * a' - 2 + 1 = 2 * a' - 1 := by omega
            have he2 : 2 * a' - 2 + 2 = 2 * a' := by omega
            rw [he1, he2] at h; exact h
          have htot := ReachesIn.trans (ReachesIn.trans hmid hrm2)
            (ReachesIn.trans hdr2 (ReachesIn.trans hsw (ReachesIn.trans hdrain hsea)))
          set used := m1 + (3 * (k - 6) + 3 + 3 * (k - 4)) + m2 +
            ((3 * (k - 12) + 3) + ((6 * (a' - 1) + 23) +
              ((3 * (a' - 1) * (a' - 1) + 20 * (a' - 1)) + (14 + 18 * (2 * a' / 3)))))
          rcases Nat.lt_or_ge fuel used with hlt2 | hge2
          · exact reachesIn_prefix (by omega) htot
          · have hlt_next : fuel - used < fuel := by omega
            have hk_next : 42 ≤ 2 * ((2 * a') / 3) := by omega
            obtain ⟨c', hc'⟩ := ih (fuel - used) hlt_next (2 * ((2 * a') / 3))
              (List.replicate ((2 * a') % 3) 1 ++ (h5 - 4) :: rt) hk_next
            exact ⟨c', reachesIn_cast (ReachesIn.trans htot hc') (by omega)⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  obtain ⟨K, hK⟩ := entry_to_E78
  exact isNotHalt_of_reach_and_safe hK fun n => loop_safe n 78 [1, 1] (by omega)

private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

end NonHaltProof

public section

/-- The machine `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← NonHaltProof.target_tm_eq_target]
  exact NonHaltProof.is_does_not_halt

end

end BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH
