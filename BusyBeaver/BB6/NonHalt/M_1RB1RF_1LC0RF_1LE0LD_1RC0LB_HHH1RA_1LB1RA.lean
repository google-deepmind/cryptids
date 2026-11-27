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
import BusyBeaver.Calculi.PairStackA

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)


-- Machine `1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`

open BusyBeaver.Calculi.PairStackA

/-- Shared copy of `target_tm`. -/
private def tm_local : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

/-- Prepend `n` copies of `1` onto a `ListBlank (Fin 2)`. -/
private def rep1 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, s => s
  | n + 1, s => (1 : Fin 2) >> rep1 n s

/-- Left half-tape encoding (`a ↦ 1^(a+1) 0`). -/
private def encLeft581 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => (1 : Fin 2) >> rep1 a ((0 : Fin 2) >> encLeft581 L)

/-- Right half-tape encoding (`(d, false) ↦ 1^(d+1) 0`, `(d, true) ↦ 1^(d+1) 00`). -/
private def encRight581 : List Seg → ListBlank (Fin 2)
  | [] => default
  | (d, false) :: R => (1 : Fin 2) >> rep1 d ((0 : Fin 2) >> encRight581 R)
  | (d, true)  :: R => (1 : Fin 2) >> rep1 d ((0 : Fin 2) >> (0 : Fin 2) >> encRight581 R)

/-- Raw TM configuration for `Cfg581`. -/
private def evalCfg581 (c : Cfg581) : Cfg (Fin 2) (Fin 6) :=
  match c.mode with
  | .FR0 => Cfg.headRight 1 (encLeft581 c.L) (encRight581 c.R)
  | .BL0 => Cfg.headLeft  2 (encLeft581 c.L) (encRight581 c.R)
  | .DR0 => Cfg.headRight 0 (encLeft581 c.L) (encRight581 c.R)
  | .DL0 => Cfg.headLeft  0 (encLeft581 c.L) (encRight581 c.R)

private theorem zero_cons_default581 : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default :=
  zero_cons_default

private theorem encLeft581_bumpL (L : List ℕ) :
    encLeft581 (bumpL L) = (1 : Fin 2) >> encLeft581 L := by
  cases L with
  | nil => simp [bumpL, encLeft581, rep1]
  | cons _ _ => rfl

private theorem encRight581_bumpR (R : List Seg) :
    encRight581 (bumpR R) = (1 : Fin 2) >> encRight581 R := by
  cases R with
  | nil => simp [bumpR, encRight581, rep1]
  | cons x xs =>
    rcases x with ⟨d, b⟩
    cases b <;> rfl

local macro "exec_local" : tactic =>
  `(tactic| simp only [ReachesIn, multiStep, Function.iterate_succ_apply',
    Function.iterate_zero_apply, Option.bind, Option.map, Option.bind_some, Option.bind_eq_bind,
    step, tm_local, Tape.write, Tape.move, Turing.Tape.move, Cfg.headLeft, Cfg.headRight,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default581, ListBlank.head_default_fin, ListBlank.tail_default])

/-- Exact positive raw-TM soundness of every `step581` macro transition. -/
private theorem step581_sound (c c' : Cfg581) (h : step581 c = some c') :
    ReachesPlus tm_local (evalCfg581 c) (evalCfg581 c') := by
  rcases c with ⟨mode, L, R⟩
  cases mode with
  | FR0 =>
    cases R with
    | nil =>
      simp only [step581, Option.some.injEq] at h; subst h
      refine ⟨1, by omega, ?_⟩
      simp only [evalCfg581, encRight581, rep1]; exec_local
    | cons seg R2 =>
      rcases seg with ⟨d, b⟩
      cases d with
      | zero =>
        cases b with
        | false =>
          simp only [step581, Option.some.injEq] at h; subst h
          refine ⟨3, by omega, ?_⟩
          simp only [evalCfg581, encRight581, rep1, encRight581_bumpR]; exec_local
        | true =>
          simp only [step581, Option.some.injEq] at h; subst h
          refine ⟨3, by omega, ?_⟩
          simp only [evalCfg581, encRight581, rep1]; exec_local
      | succ d1 =>
        cases d1 with
        | zero =>
          cases b with
          | false =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨3, by omega, ?_⟩
            simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
          | true =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨4, by omega, ?_⟩
            simp only [evalCfg581, encLeft581, encRight581, rep1, encRight581_bumpR]; exec_local
        | succ d2 =>
          cases d2 with
          | zero =>
            simp only [step581, Option.some.injEq] at h; subst h
            cases b <;> (refine ⟨2, by omega, ?_⟩; simp only [evalCfg581, encLeft581, encRight581,
                                     rep1]; exec_local)
          | succ d3 =>
            simp only [step581, Option.some.injEq] at h; subst h
            cases b <;> (refine ⟨2, by omega, ?_⟩; simp only [evalCfg581, encLeft581, encRight581,
                                     rep1]; exec_local)
  | BL0 =>
    cases L with
    | nil => simp [step581] at h
    | cons a L2 =>
      cases a with
      | zero =>
        simp only [step581, Option.some.injEq] at h; subst h
        refine ⟨4, by omega, ?_⟩
        simp only [evalCfg581, encLeft581, rep1, encLeft581_bumpL]; exec_local
      | succ a1 =>
        cases a1 with
        | zero =>
          simp only [step581, Option.some.injEq] at h; subst h
          refine ⟨3, by omega, ?_⟩
          simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
        | succ a2 =>
          cases a2 with
          | zero =>
            cases L2 with
            | nil => simp [step581] at h
            | cons a' L3 =>
              simp only [step581, Option.some.injEq] at h; subst h
              refine ⟨7, by omega, ?_⟩
              simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
          | succ a3 =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨2, by omega, ?_⟩
            simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
  | DR0 =>
    cases R with
    | nil =>
      simp only [step581, Option.some.injEq] at h; subst h
      refine ⟨1, by omega, ?_⟩
      simp only [evalCfg581, encRight581, encLeft581_bumpL]; exec_local
    | cons seg R2 =>
      rcases seg with ⟨d, b⟩
      cases d with
      | zero =>
        cases b with
        | false =>
          simp only [step581, Option.some.injEq] at h; subst h
          refine ⟨2, by omega, ?_⟩
          simp only [evalCfg581, encRight581, rep1, encRight581_bumpR]; exec_local
        | true =>
          simp only [step581, Option.some.injEq] at h; subst h
          refine ⟨2, by omega, ?_⟩
          simp only [evalCfg581, encRight581, rep1]; exec_local
      | succ d1 =>
        cases d1 with
        | zero =>
          cases b with
          | false =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨3, by omega, ?_⟩
            simp only [evalCfg581, encRight581, rep1, encLeft581_bumpL]; exec_local
          | true =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨4, by omega, ?_⟩
            simp only [evalCfg581, encRight581, rep1, encLeft581_bumpL,
                encRight581_bumpR]; exec_local
        | succ d2 =>
          cases d2 with
          | zero =>
            simp only [step581, Option.some.injEq] at h; subst h
            cases b <;> (refine ⟨2, by omega, ?_⟩; simp only [evalCfg581, encRight581, rep1,
                                     encLeft581_bumpL]; exec_local)
          | succ d3 =>
            simp only [step581, Option.some.injEq] at h; subst h
            cases b <;> (refine ⟨2, by omega, ?_⟩; simp only [evalCfg581, encRight581, rep1,
                                     encLeft581_bumpL]; exec_local)
  | DL0 =>
    cases L with
    | nil =>
      simp only [step581, Option.some.injEq] at h; subst h
      refine ⟨1, by omega, ?_⟩
      simp only [evalCfg581, encLeft581, rep1]; exec_local
    | cons a L2 =>
      cases R with
      | nil =>
        cases a with
        | zero =>
          cases L2 with
          | nil => simp [step581] at h
          | cons a' L3 =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨11, by omega, ?_⟩
            simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
        | succ a1 =>
          simp only [step581, Option.some.injEq] at h; subst h
          refine ⟨2, by omega, ?_⟩
          simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
      | cons seg R2 =>
        rcases seg with ⟨d, b⟩
        cases d with
        | zero =>
          cases b with
          | false =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨3, by omega, ?_⟩
            simp only [evalCfg581, encLeft581, encRight581, rep1]; exec_local
          | true =>
            simp only [step581, Option.some.injEq] at h; subst h
            refine ⟨4, by omega, ?_⟩
            simp only [evalCfg581, encLeft581, encRight581, rep1, encRight581_bumpR]; exec_local
        | succ d1 =>
          cases d1 with
          | zero =>
            simp only [step581, Option.some.injEq] at h; subst h
            cases b <;> (refine ⟨2, by omega, ?_⟩; simp only [evalCfg581, encLeft581, encRight581,
                                     rep1]; exec_local)
          | succ d2 =>
            simp only [step581, Option.some.injEq] at h; subst h
            cases b <;> (refine ⟨2, by omega, ?_⟩; simp only [evalCfg581, encLeft581, encRight581,
                                     rep1]; exec_local)

private theorem run581_reachesStar :
    ∀ (k : ℕ) (c c' : Cfg581),
      run581 k c = some c' → ReachesStar tm_local (evalCfg581 c) (evalCfg581 c')
  | 0, c, c', h => by
    simp only [run581, Option.some.injEq] at h
    subst h
    exact ⟨0, ReachesIn.zero tm_local _⟩
  | k + 1, c, c', h => by
    simp only [run581] at h
    cases hs : step581 c with
    | none => rw [hs] at h; contradiction
    | some c1 =>
      rw [hs] at h
      obtain ⟨m1, _, hm1⟩ := step581_sound c c1 hs
      exact ReachesStar.trans ⟨m1, hm1⟩ (run581_reachesStar k c1 c' h)

/-- Blank-tape entry to initial `Cfg581`. -/
private theorem init_reaches_start_local :
    ReachesStar tm_local (init [] : Cfg (Fin 2) (Fin 6)) (evalCfg581 ⟨.BL0, [0], [(1, false), (0,
        false)]⟩) := by
  rw [init_nil]
  refine ⟨15, ?_⟩
  simp only [evalCfg581, encLeft581, encRight581, rep1]
  exec_local

private def wallR0_local : List Seg :=
    [(0, true), (1, false), (1, false), (2, false), (1, false), (2, false), (1, false), (1, false),
    (2, false), (0, true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2,
    false)]

private theorem run_chunk_0 :
    run581 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [1, 0, 1, 3, 2], [(0, false)]⟩ :=
        rfl
private theorem run_chunk_1 :
    run581 50 ⟨.BL0, [1, 0, 1, 3, 2], [(0, false)]⟩ = some ⟨.DL0, [2, 3, 5], [(1, false), (1,
        false), (1, false)]⟩ := rfl
private theorem run_chunk_2 :
    run581 50 ⟨.DL0, [2, 3, 5], [(1, false), (1, false), (1, false)]⟩ = some ⟨.DL0, [1, 3, 1, 1, 0,
        8], [(0, false), (1, false)]⟩ := rfl
private theorem run_chunk_3 :
    run581 50 ⟨.DL0, [1, 3, 1, 1, 0, 8], [(0, false), (1, false)]⟩ = some ⟨.DR0, [5], [(0, false),
        (0, true), (0, true), (0, true), (1, true), (1, false), (1, false), (1, false), (2,
        false)]⟩ := rfl
private theorem run_chunk_4 :
    run581 50 ⟨.DR0, [5], [(0, false), (0, true), (0, true), (0, true), (1, true), (1, false), (1,
        false), (1, false), (2, false)]⟩ = some ⟨.BL0, [3], [(1, false), (1, false), (2, false), (1,
        false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ := rfl
private theorem run_chunk_5 :
    run581 50 ⟨.BL0, [3], [(1, false), (1, false), (2, false), (1, false), (1, true), (2, false),
        (1, false), (1, false), (2, false)]⟩ = some ⟨.FR0, [0, 6, 3, 1, 0, 3, 1, 3, 2], [(1, false),
        (0, false)]⟩ := rfl
private theorem run_chunk_6 :
    run581 50 ⟨.FR0, [0, 6, 3, 1, 0, 3, 1, 3, 2], [(1, false), (0, false)]⟩ = some ⟨.BL0, [0, 6, 1,
        1, 0, 4, 0, 3, 1, 3, 2], [(0, true), (1, false)]⟩ := rfl
private theorem run_chunk_7 :
    run581 50 ⟨.BL0, [0, 6, 1, 1, 0, 4, 0, 3, 1, 3, 2], [(0, true), (1, false)]⟩ = some ⟨.FR0, [1,
        3, 6, 1, 3, 2], [(2, false), (1, true), (1, false), (1, false), (1, false), (2, false)]⟩ :=
        rfl
private theorem run_chunk_8 :
    run581 50 ⟨.FR0, [1, 3, 6, 1, 3, 2], [(2, false), (1, true), (1, false), (1, false), (1, false),
        (2, false)]⟩ = some ⟨.BL0, [3, 2, 3, 1, 3, 6, 1, 3, 2], [(1, false), (1, false), (1, false),
        (2, false)]⟩ := rfl
private theorem run_chunk_9 :
    run581 50 ⟨.BL0, [3, 2, 3, 1, 3, 6, 1, 3, 2], [(1, false), (1, false), (1, false), (2,
        false)]⟩ = some ⟨.FR0, [8, 3, 1, 3, 6, 1, 3, 2], [(2, true), (1, false), (1, false), (1,
        false), (2, false)]⟩ := rfl
private theorem run_chunk_10 :
    run581 50 ⟨.FR0, [8, 3, 1, 3, 6, 1, 3, 2], [(2, true), (1, false), (1, false), (1, false), (2,
        false)]⟩ = some ⟨.BL0, [6, 3, 1, 3, 6, 1, 3, 2], [(1, false), (1, false), (1, true), (0,
        true), (1, false), (1, false), (1, false), (2, false)]⟩ := rfl
private theorem run_chunk_11 :
    run581 50 ⟨.BL0, [6, 3, 1, 3, 6, 1, 3, 2], [(1, false), (1, false), (1, true), (0, true), (1,
        false), (1, false), (1, false), (2, false)]⟩ = some ⟨.FR0, [10, 1, 3, 2], [(0, true), (2,
        false), (1, false), (1, false), (1, false), (1, false), (2, false), (0, true), (1,
        true), (1, false), (1, false), (1, false), (2, false)]⟩ := rfl
private theorem run_chunk_12 :
    run581 50 ⟨.FR0, [10, 1, 3, 2], [(0, true), (2, false), (1, false), (1, false), (1, false), (1,
        false), (2, false), (0, true), (1, true), (1, false), (1, false), (1, false), (2,
        false)]⟩ = some ⟨.DR0, [0, 0, 1, 1, 1, 3, 0, 1, 1, 1, 3, 0, 1, 3, 2], [(0, true), (1, true),
        (1, false), (1, false), (1, false), (2, false)]⟩ := rfl
private theorem run_chunk_13 :
    run581 50 ⟨.DR0, [0, 0, 1, 1, 1, 3, 0, 1, 1, 1, 3, 0, 1, 3, 2], [(0, true), (1, true), (1,
        false), (1, false), (1, false), (2, false)]⟩ = some ⟨.BL0, [1, 3, 2], [(0, true), (1,
        false), (1, false), (2, false), (0, true), (0, true), (1, false), (1, false), (2,
        false), (0, true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2,
        false)]⟩ := rfl
private theorem run_chunk_14 :
    run581 50 ⟨.BL0, [1, 3, 2], [(0, true), (1, false), (1, false), (2, false), (0, true), (0,
        true), (1, false), (1, false), (2, false), (0, true), (0, true), (1, false), (1, true), (2,
        false), (1, false), (1, false), (2, false)]⟩ = some ⟨.FR0, [0, 3, 1, 3, 2], [(1, false), (0,
        true), (1, false), (2, false), (1, false), (1, false), (2, false), (0, true), (0, true), (1,
        false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ := rfl
private theorem run_chunk_15 :
    run581 10 ⟨.FR0, [0, 3, 1, 3, 2], [(1, false), (0, true), (1, false), (2, false), (1, false),
        (1, false), (2, false), (0, true), (0, true), (1, false), (1, true), (2, false), (1,
        false), (1, false), (2, false)]⟩ = some ⟨.BL0, [1, 3, 2], [(0, true), (1, false), (1,
        false), (2, false), (1, false), (2, false), (1, false), (1, false), (2, false), (0,
        true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ :=
        rfl

private theorem start_reaches_wall_local :
    run581 760 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [1, 3, 2], wallR0_local⟩ := by
  have h0 : run581 0 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [0], [(1, false), (0,
      false)]⟩ := rfl
  have h1 : run581 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [1, 0, 1, 3, 2], [(0,
      false)]⟩ := by
    have :=
        run581_add 0 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [0], [(1, false), (0,
        false)]⟩ h0
    rw [this]; exact run_chunk_0
  have h2 : run581 100 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.DL0, [2, 3, 5], [(1, false),
      (1, false), (1, false)]⟩ := by
    have :=
        run581_add 50 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [1, 0, 1, 3, 2], [(0,
        false)]⟩ h1
    rw [this]; exact run_chunk_1
  have h3 : run581 150 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.DL0, [1, 3, 1, 1, 0, 8], [(0,
      false), (1, false)]⟩ := by
    have :=
        run581_add 100 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.DL0, [2, 3, 5], [(1, false), (1,
        false), (1, false)]⟩ h2
    rw [this]; exact run_chunk_2
  have h4 : run581 200 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.DR0, [5], [(0, false), (0,
      true), (0, true), (0, true), (1, true), (1, false), (1, false), (1, false), (2, false)]⟩ := by
    have :=
        run581_add 150 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.DL0, [1, 3, 1, 1, 0, 8], [(0,
        false), (1, false)]⟩ h3
    rw [this]; exact run_chunk_3
  have h5 : run581 250 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [3], [(1, false), (1,
      false), (2, false), (1, false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ :=
      by
    have :=
        run581_add 200 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.DR0, [5], [(0, false), (0, true),
        (0, true), (0, true), (1, true), (1, false), (1, false), (1, false), (2, false)]⟩ h4
    rw [this]; exact run_chunk_4
  have h6 : run581 300 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.FR0, [0, 6, 3, 1, 0, 3, 1, 3,
      2], [(1, false), (0, false)]⟩ := by
    have :=
        run581_add 250 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [3], [(1, false), (1, false),
        (2, false), (1, false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ h5
    rw [this]; exact run_chunk_5
  have h7 : run581 350 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [0, 6, 1, 1, 0, 4, 0, 3,
      1, 3, 2], [(0, true), (1, false)]⟩ := by
    have :=
        run581_add 300 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.FR0, [0, 6, 3, 1, 0, 3, 1, 3, 2],
        [(1, false), (0, false)]⟩ h6
    rw [this]; exact run_chunk_6
  have h8 : run581 400 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.FR0, [1, 3, 6, 1, 3, 2], [(2,
      false), (1, true), (1, false), (1, false), (1, false), (2, false)]⟩ := by
    have :=
        run581_add 350 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [0, 6, 1, 1, 0, 4, 0, 3, 1,
        3, 2], [(0, true), (1, false)]⟩ h7
    rw [this]; exact run_chunk_7
  have h9 : run581 450 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [3, 2, 3, 1, 3, 6, 1, 3,
      2], [(1, false), (1, false), (1, false), (2, false)]⟩ := by
    have :=
        run581_add 400 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.FR0, [1, 3, 6, 1, 3, 2], [(2,
        false), (1, true), (1, false), (1, false), (1, false), (2, false)]⟩ h8
    rw [this]; exact run_chunk_8
  have h10 : run581 500 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.FR0, [8, 3, 1, 3, 6, 1, 3,
      2], [(2, true), (1, false), (1, false), (1, false), (2, false)]⟩ := by
    have :=
        run581_add 450 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [3, 2, 3, 1, 3, 6, 1, 3, 2],
        [(1, false), (1, false), (1, false), (2, false)]⟩ h9
    rw [this]; exact run_chunk_9
  have h11 : run581 550 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [6, 3, 1, 3, 6, 1, 3,
      2], [(1, false), (1, false), (1, true), (0, true), (1, false), (1, false), (1, false), (2,
      false)]⟩ := by
    have :=
        run581_add 500 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.FR0, [8, 3, 1, 3, 6, 1, 3, 2],
        [(2, true), (1, false), (1, false), (1, false), (2, false)]⟩ h10
    rw [this]; exact run_chunk_10
  have h12 : run581 600 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.FR0, [10, 1, 3, 2], [(0,
      true), (2, false), (1, false), (1, false), (1, false), (1, false), (2, false), (0, true), (1,
      true), (1, false), (1, false), (1, false), (2, false)]⟩ := by
    have :=
        run581_add 550 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [6, 3, 1, 3, 6, 1, 3, 2],
        [(1, false), (1, false), (1, true), (0, true), (1, false), (1, false), (1, false), (2,
        false)]⟩ h11
    rw [this]; exact run_chunk_11
  have h13 : run581 650 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.DR0, [0, 0, 1, 1, 1, 3, 0, 1,
      1, 1, 3, 0, 1, 3, 2], [(0, true), (1, true), (1, false), (1, false), (1, false), (2,
      false)]⟩ := by
    have :=
        run581_add 600 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.FR0, [10, 1, 3, 2], [(0, true),
        (2, false), (1, false), (1, false), (1, false), (1, false), (2, false), (0, true), (1,
        true), (1, false), (1, false), (1, false), (2, false)]⟩ h12
    rw [this]; exact run_chunk_12
  have h14 : run581 700 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [1, 3, 2], [(0, true),
      (1, false), (1, false), (2, false), (0, true), (0, true), (1, false), (1, false), (2,
      false), (0, true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2,
      false)]⟩ := by
    have :=
        run581_add 650 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.DR0, [0, 0, 1, 1, 1, 3, 0, 1, 1,
        1, 3, 0, 1, 3, 2], [(0, true), (1, true), (1, false), (1, false), (1, false), (2,
        false)]⟩ h13
    rw [this]; exact run_chunk_13
  have h15 : run581 750 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.FR0, [0, 3, 1, 3, 2], [(1,
      false), (0, true), (1, false), (2, false), (1, false), (1, false), (2, false), (0, true), (0,
      true), (1, false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ := by
    have :=
        run581_add 700 50 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.BL0, [1, 3, 2], [(0, true), (1,
        false), (1, false), (2, false), (0, true), (0, true), (1, false), (1, false), (2,
        false), (0, true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2,
        false)]⟩ h14
    rw [this]; exact run_chunk_14
  have h16 : run581 760 ⟨.BL0, [0], [(1, false), (0, false)]⟩ = some ⟨.BL0, [1, 3, 2], [(0, true),
      (1, false), (1, false), (2, false), (1, false), (2, false), (1, false), (1, false), (2,
      false), (0, true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2,
      false)]⟩ := by
    have :=
        run581_add 750 10 ⟨.BL0, [0], [(1, false), (0, false)]⟩ ⟨.FR0, [0, 3, 1, 3, 2], [(1, false),
        (0, true), (1, false), (2, false), (1, false), (1, false), (2, false), (0, true), (0,
        true), (1, false), (1, true), (2, false), (1, false), (1, false), (2, false)]⟩ h15
    rw [this]; exact run_chunk_15
  exact h16

private theorem init_reaches_wall_local :
    ReachesStar tm_local (init [] : Cfg (Fin 2) (Fin 6))
      (evalCfg581 ⟨.BL0, [1, 3, 2], wallR0_local⟩) :=
  init_reaches_start_local.trans (run581_reachesStar _ _ _ start_reaches_wall_local)

/-- Generic non-halting bridge from `∀ n, run581 n c0 ≠ none` to `IsNotHalt tm_local`. -/
private theorem isNotHalt_of_run581_no_halt (c0 : Cfg581)
    (hreach : ReachesStar tm_local (init [] : Cfg (Fin 2) (Fin 6)) (evalCfg581 c0))
    (hno : ∀ n, run581 n c0 ≠ none) :
    IsNotHalt tm_local := by
  refine IsNotHalt.of_reachesPlus_invariant
    (P := fun cfg => ∃ c, (∀ n, run581 n c ≠ none) ∧ cfg = evalCfg581 c)
    hreach ⟨c0, hno, rfl⟩ ?_
  rintro _ ⟨c, hc, rfl⟩
  cases hs : step581 c with
  | none =>
    have h1 := hc 1
    simp only [run581, hs] at h1
    exact absurd rfl h1
  | some c' =>
    refine ⟨evalCfg581 c', step581_sound c c' hs, c', ?_, rfl⟩
    intro n
    have hn := hc (n + 1)
    simp only [run581, hs] at hn
    exact hn

private theorem target_tm_eq_tm_local : target_tm = tm_local := by
  funext s b
  match s, b with
  | 0, 0 => rfl | 0, 1 => rfl | 1, 0 => rfl | 1, 1 => rfl
  | 2, 0 => rfl | 2, 1 => rfl | 3, 0 => rfl | 3, 1 => rfl
  | 4, 0 => rfl | 4, 1 => rfl | 5, 0 => rfl | 5, 1 => rfl


private theorem is_does_not_halt : IsNotHalt target_tm := by
  rw [target_tm_eq_tm_local]
  refine isNotHalt_of_run581_no_halt ⟨.BL0, [1, 3, 2], wallR0_local⟩ init_reaches_wall_local
    (BusyBeaver.Calculi.PairStackA.strongWall_no_halt wallR0_local ?_)
  exact ⟨[(1, false), (1, false), (2, false), (1, false), (2, false), (1, false), (1, false), (2,
      false), (0, true), (0, true), (1, false), (1, true), (2, false), (1, false), (1, false), (2,
      false)], rfl, trivial, Or.inl ⟨_, rfl,
      BusyBeaver.Calculi.PairStackA.strong2_of_step_21
      (BusyBeaver.Calculi.PairStackA.good2_of_2_1_1 _)⟩⟩


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA
