/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RD---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

@[simp] private lemma multiStep_zero_simp (c : Cfg (Fin 2) (Fin 6)) :
    multiStep target_tm c 0 = some c := rfl

@[simp] private lemma multiStep_succ_simp (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep target_tm c (n + 1) = (step target_tm c).bind (fun c' => multiStep target_tm c' n) := by
  rw [multiStep, Function.iterate_succ_apply]
  change ((fun x => Option.bind x (step target_tm))^[n] (step target_tm c)) = _
  cases hs : step target_tm c with
  | none =>
    have hnone : ∀ k, ((fun x => Option.bind x (step target_tm))^[k] none) = none := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply]; exact ih
    simp [hnone]
  | some c' => rfl

@[simp] private lemma lb_head_cons_fin2 (a : Fin 2) (s : ListBlank (Fin 2)) :
    (a >> s).head = a := ListBlank.head_cons a s

@[simp] private lemma lb_tail_cons_fin2 (a : Fin 2) (s : ListBlank (Fin 2)) :
    (a >> s).tail = s := ListBlank.tail_cons a s

@[simp] private lemma pow_succ_zero (k : ℕ) (s : ListBlank (Fin 2)) :
    (([0] : List (Fin 2)) ^ (k + 1)) +> s = (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> s) := rfl

@[simp] private lemma pow_zero_zero (s : ListBlank (Fin 2)) :
    (([0] : List (Fin 2)) ^ 0) +> s = s := rfl

@[simp] private lemma head_default_fin2 :
    ((default : ListBlank (Fin 2)).head) = (0 : Fin 2) := rfl

@[simp] private lemma tail_default_fin2 :
    ((default : ListBlank (Fin 2)).tail) = default := rfl

@[simp] private lemma cons_zero_default_fin2 :
    (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default := by
  apply ListBlank.ext
  intro n
  cases n <;> rfl

private def encL : List ℕ → ListBlank (Fin 2)
  | [] => (1 : Fin 2) >> default
  | 0 :: w => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encL w
  | (n + 1) :: w => (1 : Fin 2) >> ((([0] : List (Fin 2)) ^ (n + 1)) +> encL w)

@[simp] private lemma encL_head (w : List ℕ) : (encL w).head = (1 : Fin 2) := by
  cases w with
  | nil => simp [encL]
  | cons x w' => cases x <;> simp [encL]

private def bumpW : List ℕ → List ℕ
  | [] => []
  | 0 :: w => 1 :: 1 :: w
  | (n + 1) :: w => (n + 2) :: w

@[simp] private lemma encL_bumpW (w : List ℕ) :
    (1 : Fin 2) >> ((0 : Fin 2) >> (encL w).tail) = encL (bumpW w) := by
  cases w with
  | nil => simp [encL, bumpW]
  | cons x w' =>
    cases x with
    | zero => simp [encL, bumpW]
    | succ n => simp [encL, bumpW]

private def encR : List (Fin 3) → ListBlank (Fin 2)
  | [] => default
  | 0 :: v => (0 : Fin 2) >> encR v
  | 1 :: v => (1 : Fin 2) >> (0 : Fin 2) >> encR v
  | 2 :: v => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encR v

private inductive GoodVA : ℕ → List (Fin 3) → Prop
  | zero       : GoodVA 0 [0]
  | z001 {a v} : GoodVA a (0 :: v) → GoodVA 0 (0 :: 0 :: 1 :: v)
  | z01 {a v}  : GoodVA a (0 :: v) → GoodVA (a + 1) (0 :: 1 :: v)
  | z02 {a v}  : GoodVA a (0 :: v) → GoodVA 0 (0 :: 2 :: v)

private inductive GoodCD : ℕ → List (Fin 3) → Prop
  | nil       : GoodCD 0 []
  | z01 {a v} : GoodVA a (0 :: v) → GoodCD 0 (0 :: 1 :: v)
  | z1 {b v}  : GoodCD b v → GoodCD (b + 1) (1 :: v)

private lemma GoodVA_cons0 {b : ℕ} {v : List (Fin 3)} : GoodCD b v → GoodVA b (0 :: v)
  | .nil => .zero
  | .z01 hv => .z001 hv
  | .z1 hv => .z01 (GoodVA_cons0 hv)

private inductive SafeW : ℕ → List ℕ → Prop
  | nil {b}    : SafeW b []
  | z0 {b w}   : SafeW 0 w → SafeW b (0 :: w)
  | z1 {b w}   : SafeW (b + 1) w → SafeW b (1 :: w)
  | z2 {b w}   : SafeW b w → SafeW b (2 :: w)
  | z3 {b k w} : SafeW b ((k + 2) :: w) → SafeW (b + 1) ((k + 3) :: w)

private lemma SafeW_mono_aux {b : ℕ} {w : List ℕ} (hw : SafeW b w) : ∀ d, b ≤ d → SafeW d w := by
  induction hw with
  | nil => intro d _; exact .nil
  | z0 hw0 => intro d _; exact .z0 hw0
  | z1 _ ih => intro d hd; exact .z1 (ih (d + 1) (by omega))
  | z2 _ ih => intro d hd; exact .z2 (ih d hd)
  | z3 _ ih =>
    intro d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    exact .z3 (ih d' (by omega))

private lemma SafeW_mono {b b' : ℕ} (h : b ≤ b') {w : List ℕ} (hw : SafeW b w) : SafeW b' w :=
  SafeW_mono_aux hw b' h

private lemma bumpW_safe {b : ℕ} {w : List ℕ} (hw : SafeW b w) : SafeW (b + 1) (bumpW w) := by
  cases hw with
  | nil => exact .nil
  | z0 hw0 => exact .z1 (.z1 (SafeW_mono (by omega) hw0))
  | z1 hw1 => exact .z2 hw1
  | z2 hw2 => exact .z3 (k := 0) (.z2 hw2)
  | @z3 b₀ k u hw3 => exact .z3 (k := k + 1) (.z3 hw3)

private inductive SafeWA : ℕ → List ℕ → Prop
  | nil {a}  : SafeWA a []
  | z0 {a w} : SafeW 0 w → SafeWA a (0 :: w)
  | z1 {a w} : SafeW a w → SafeWA a (1 :: w)

private lemma SafeWA_succ_to_SafeW {a : ℕ} {w : List ℕ} (hw : SafeWA (a + 1) w) : SafeW a w := by
  cases hw with
  | nil => exact .nil
  | z0 hw0 => exact .z0 hw0
  | z1 hw1 => exact .z1 hw1

private lemma SafeWA_zero_to_SafeW0 {w : List ℕ} (hw : SafeWA 0 w) : SafeW 0 w := by
  cases hw with
  | nil => exact .nil
  | z0 hw0 => exact .z0 hw0
  | z1 hw1 => exact .z1 (SafeW_mono (by omega) hw1)

private inductive SymMode where
  | modeC | modeD | modeA

private def evalSym : SymMode → List ℕ → List (Fin 3) → Cfg (Fin 2) (Fin 6)
  | .modeC, w, v => (encL w) <{{2}} (encR v)
  | .modeD, w, v => ((1 : Fin 2) >> encL w) <{{3}} ((0 : Fin 2) >> encR v)
  | .modeA, w, v => (encL w) {{0}}> (encR v)

private inductive GoodSym : Cfg (Fin 2) (Fin 6) → Prop
  | mkC {b w v} : SafeW b w → GoodCD b v → GoodSym (evalSym .modeC w v)
  | mkD {b w v} : SafeW (b + 1) w → GoodCD b v → GoodSym (evalSym .modeD w v)
  | mkA {a w v} : SafeWA a w → GoodVA a v → GoodSym (evalSym .modeA w v)

private lemma step_sym_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : GoodSym cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧ GoodSym cfg' := by
  cases h with
  | @mkC b w v hw hv =>
    cases hw with
    | nil =>
      refine ⟨evalSym .modeA [] (0 :: v), ⟨8, by omega, ?_⟩, .mkA .nil (GoodVA_cons0 hv)⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z0 _ w' hw' =>
      refine ⟨evalSym .modeC w' (0 :: 1 :: v), ⟨3, by omega, ?_⟩, .mkC hw' (.z01 (GoodVA_cons0 hv))⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z1 _ w' hw' =>
      refine ⟨evalSym .modeC w' (1 :: v), ⟨2, by omega, ?_⟩, .mkC hw' (.z1 hv)⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z2 _ w' hw' =>
      refine ⟨evalSym .modeD (bumpW w') v, ⟨5, by omega, ?_⟩, .mkD (bumpW_safe hw') hv⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z3 b₀ k w' hw' =>
      cases hv with
      | @z1 _ vt hvt =>
        refine ⟨evalSym .modeA (1 :: (k + 2) :: w') (0 :: vt), ⟨12, by omega, ?_⟩,
          .mkA (.z1 hw') (GoodVA_cons0 hvt)⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
  | @mkD b w v hw hv =>
    cases hv with
    | nil =>
      refine ⟨evalSym .modeC (1 :: w) [1, 1], ⟨7, by omega, ?_⟩,
        .mkC (.z1 (SafeW_mono (by omega) hw)) (.z1 (.z1 .nil))⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z01 a vt hvt =>
      refine ⟨evalSym .modeA (1 :: 1 :: w) (0 :: vt), ⟨4, by omega, ?_⟩,
        .mkA (.z1 (SafeW_mono (by omega) (.z1 hw))) hvt⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z1 b' vt hvt =>
      refine ⟨evalSym .modeD (1 :: w) vt, ⟨2, by omega, ?_⟩, .mkD (.z1 hw) hvt⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
  | @mkA a w v hw hv =>
    cases hv with
    | @z01 a₀ vt hvt =>
      refine ⟨evalSym .modeA (1 :: w) (0 :: vt), ⟨4, by omega, ?_⟩,
        .mkA (.z1 (SafeWA_succ_to_SafeW hw)) hvt⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z02 a₀ vt hvt =>
      refine ⟨evalSym .modeA (0 :: w) (0 :: vt), ⟨5, by omega, ?_⟩,
        .mkA (.z0 (SafeWA_zero_to_SafeW0 hw)) hvt⟩
      simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | zero =>
      cases hw with
      | nil =>
        refine ⟨evalSym .modeA [] [0, 2, 1], ⟨17, by omega, ?_⟩,
          .mkA .nil (.z02 (.z01 .zero))⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
      | @z0 w' hw' =>
        refine ⟨evalSym .modeA (1 :: 2 :: w') [0], ⟨10, by omega, ?_⟩,
          .mkA (.z1 (.z2 hw')) .zero⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
      | @z1 w' hw' =>
        refine ⟨evalSym .modeC w' [0, 1, 1], ⟨5, by omega, ?_⟩,
          .mkC hw' (.z01 (.z01 .zero))⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
    | @z001 a₀ vt hvt =>
      cases hw with
      | nil =>
        refine ⟨evalSym .modeA [] (0 :: 2 :: 2 :: vt), ⟨17, by omega, ?_⟩,
          .mkA .nil (.z02 (.z02 hvt))⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
      | @z0 w' hw' =>
        refine ⟨evalSym .modeA (0 :: 2 :: w') (0 :: vt), ⟨11, by omega, ?_⟩,
          .mkA (.z0 (.z2 hw')) hvt⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]
      | @z1 w' hw' =>
        refine ⟨evalSym .modeC w' (0 :: 1 :: 2 :: vt), ⟨5, by omega, ?_⟩,
          .mkC hw' (.z01 (.z02 hvt))⟩
        simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]

private lemma init_reaches_sym :
    multiStep target_tm (init []) 2 = some (evalSym .modeC [] [1]) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = ⟨some 0, ⟨0, default, default⟩⟩ := rfl
  rw [h0]
  simp [step, target_tm, Tape.move, Tape.write, evalSym, encL, encR]

private lemma _ms_succ (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm c (n + 1) = (multiStep target_tm c n).bind (step target_tm) :=
  Function.iterate_succ_apply' _ n (some c)

private lemma _ms_add (c : Cfg (Fin 2) (Fin 6)) (m k : Nat) :
    multiStep target_tm c (m + k) = (multiStep target_tm c m).bind (fun c' => multiStep target_tm c' k) := by
  induction k with
  | zero => rw [Nat.add_zero]; cases multiStep target_tm c m <;> rfl
  | succ k ih =>
    rw [← Nat.add_assoc, _ms_succ, ih]
    cases multiStep target_tm c m with
    | none => rfl
    | some c' => exact (_ms_succ c' k).symm

private lemma _closed_not_halt
    (P : Cfg (Fin 2) (Fin 6) → Prop)
    (h_step : ∀ c, P c → ∃ c', (c [target_tm]⊢⁺ c') ∧ P c')
    (c₀ : Cfg (Fin 2) (Fin 6))
    {N₀ : ℕ} (h_init : multiStep target_tm (init []) N₀ = some c₀)
    (h₀ : P c₀) :
    IsNotHalt target_tm := by
  have h_unb : ∀ K : ℕ, ∃ M ≥ K, ∃ c, multiStep target_tm (init []) M = some c ∧ P c := by
    intro K
    induction K with
    | zero => exact ⟨N₀, Nat.zero_le N₀, c₀, h_init, h₀⟩
    | succ K ih =>
      rcases ih with ⟨M, hMK, c, hMc, hc⟩
      rcases h_step c hc with ⟨c', ⟨k, hk_pos, h_ck⟩, hc'⟩
      refine ⟨M + k, by omega, c', ?_, hc'⟩
      rw [_ms_add (init []) M k, hMc]
      exact h_ck
  intro cfg ⟨N, hN⟩
  rcases h_unb (N + 1) with ⟨M, hMN, c, hMc, _⟩
  obtain ⟨d, rfl⟩ : ∃ d, M = (N + 1) + d := ⟨M - (N + 1), by omega⟩
  rw [_ms_add (init []) (N + 1) d, _ms_succ (init []) N, hN] at hMc
  cases hst : step target_tm cfg with
  | none =>
    change Option.bind (step target_tm cfg) (fun c' => multiStep target_tm c' d) = some c at hMc
    rw [hst] at hMc; cases hMc
  | some _ => rfl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact _closed_not_halt GoodSym step_sym_closed (evalSym .modeC [] [1])
    init_reaches_sym (.mkC .nil (.z1 .nil))

-- END GOAL STATEMENT

end BusyBeaver.M_1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RDHHH
