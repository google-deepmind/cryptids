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
import BusyBeaver.Calculi.Longitudinal


/-!
# Busy Beaver Machine `1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_0RCHHH_1RD0LA_1RE0RA_0LF1LD_1LC1RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LE_0RCHHH_1RD0LA_1RE0RA_0LF1LD_1LC1RF` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RCHHH_1RD0LA_1RE0RA_0LF1LD_1LC1RF"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

private def tm : Machine (Fin 2) (Fin 6) := fun q a =>
  match q.val, a.val with
  | 0, 0 => some (some 1, Stmt.write 1 .right)
  | 0, 1 => some (some 4, Stmt.write 0 .left)
  | 1, 0 => some (some 2, Stmt.write 0 .right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 .right)
  | 2, 1 => some (some 0, Stmt.write 0 .left)
  | 3, 0 => some (some 4, Stmt.write 1 .right)
  | 3, 1 => some (some 0, Stmt.write 0 .right)
  | 4, 0 => some (some 5, Stmt.write 0 .left)
  | 4, 1 => some (some 3, Stmt.write 1 .left)
  | 5, 0 => some (some 2, Stmt.write 1 .left)
  | _, _ => some (some 5, Stmt.write 1 .right)

open BusyBeaver.Longitudinal

private theorem tm_eq_target : tm = target_tm := by
  funext ⟨q, hq⟩ ⟨a, ha⟩
  rcases q with _ | _ | _ | _ | _ | _ | q <;> rcases a with _ | _ | a <;> try rfl
  all_goals omega

/-! ## Pure `Bool`/`Nat` Shadow Bounded Simulator -/

private structure BCfgB where
  l : List Bool
  r : List Bool
  q : ℕ
  isRight : Bool
  deriving DecidableEq

private def bSym (b : Bool) : Fin 2 :=
  if b then 1 else 0

private def bWord (bs : List Bool) : List (Fin 2) :=
  bs.map bSym

private theorem bWord_nil : bWord [] = [] := rfl

private theorem bWord_cons (b : Bool) (bs : List Bool) :
    bWord (b :: bs) = bSym b :: bWord bs := rfl

private theorem bWord_1010 : bWord [true, false, true, false] = [1, 0, 1, 0] := rfl

private theorem bWord_00 : bWord [false, false] = [0, 0] := rfl

private theorem bWord_append (xs ys : List Bool) :
    bWord (xs ++ ys) = bWord xs ++ bWord ys := by
  simp [bWord]

private def bState : ℕ → Fin 6
  | 0 => A
  | 1 => B
  | 2 => C
  | 3 => D
  | 4 => E
  | _ => F

private def BCfgB.toCfg (x : BCfgB) (l₀ r₀ : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  match x.isRight with
  | false => (bWord x.r +> l₀) <{{bState x.q}} (bWord x.l +> r₀)
  | true => (bWord x.l +> l₀) {{bState x.q}}> (bWord x.r +> r₀)

private def tmB (q : ℕ) (m : Bool) : Option (ℕ × Bool × Bool) :=
  match q, m with
  | 0, false => some (1, true, true)
  | 0, true => some (4, false, false)
  | 1, false => some (2, false, true)
  | 1, true => none
  | 2, false => some (3, true, true)
  | 2, true => some (0, false, false)
  | 3, false => some (4, true, true)
  | 3, true => some (0, false, true)
  | 4, false => some (5, false, false)
  | 4, true => some (3, true, false)
  | 5, false => some (2, true, false)
  | 5, true => some (5, true, true)
  | _, _ => none

private def boolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

private def stepB (x : BCfgB) : Option BCfgB :=
  match x.r with
  | [] => none
  | m :: r₀ =>
    match tmB x.q m with
    | none => none
    | some (q', w, d') =>
      if boolBeq x.isRight d' then
        some ⟨w :: x.l, r₀, q', d'⟩
      else
        some ⟨w :: r₀, x.l, q', d'⟩

private theorem stepB_spec (x : BCfgB) {x' : BCfgB} (h : stepB x = some x')
    (l₀ r₀ : ListBlank (Fin 2)) :
    (x.toCfg l₀ r₀) [tm]⊢ (x'.toCfg l₀ r₀) := by
  rcases x with ⟨l, _ | ⟨_ | _, r₀⟩, _ | _ | _ | _ | _ | _ | q, _ | _⟩ <;>
    dsimp [stepB, tmB] at h <;> cases h <;>
    simp [BCfgB.toCfg, bWord, bSym, bState, BusyBeaver.step, tm, Tape.write, Tape.move,
      A, B, C, D, E, F]

private def stepsB : ℕ → BCfgB → Option BCfgB
  | 0, x =>
    match stepB x with
    | none => some x
    | some _ => none
  | n + 1, x =>
    match stepB x with
    | none => some x
    | some x' => stepsB n x'

private theorem stepsB_spec :
    ∀ n (x x' : BCfgB), stepsB n x = some x' →
      ∀ l₀ r₀ : ListBlank (Fin 2), (x.toCfg l₀ r₀) [tm]⊢* (x'.toCfg l₀ r₀)
  | 0, x, x', h, _, _ => by
    dsimp only [stepsB] at h
    rcases h_st : stepB x with _ | _ <;> rw [h_st] at h <;> cases h
    exact stepStar_refl tm _
  | n + 1, x, x', h, l₀, r₀ => by
    dsimp only [stepsB] at h
    rcases h_st : stepB x with _ | y <;> rw [h_st] at h
    · cases h
      exact stepStar_refl tm _
    · exact stepStar_trans ⟨1, stepB_spec x h_st l₀ r₀⟩ (stepsB_spec n y x' h l₀ r₀)

private def steps1B (n : ℕ) (x : BCfgB) : Option BCfgB :=
  match stepB x with
  | none => none
  | some x' => stepsB n x'

private theorem steps1B_spec {n : ℕ} {x x' : BCfgB} (h : steps1B n x = some x')
    (l₀ r₀ : ListBlank (Fin 2)) :
    (x.toCfg l₀ r₀) [tm]⊢⁺ (x'.toCfg l₀ r₀) := by
  dsimp only [steps1B] at h
  rcases h_st : stepB x with _ | y <;> rw [h_st] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, stepB_spec x h_st l₀ r₀⟩
      (stepsB_spec n y x' h l₀ r₀)

private def stepR0infB (x : BCfgB) : Option BCfgB :=
  match x.r with
  | [] =>
    match x.isRight with
    | true =>
      match tmB x.q false with
      | none => none
      | some (q', w, d') =>
        if d' then
          some ⟨w :: x.l, [], q', true⟩
        else
          some ⟨[w], x.l, q', false⟩
    | false => none
  | _ :: _ => stepB x

private theorem stepR0infB_spec (x : BCfgB) {x' : BCfgB} (h : stepR0infB x = some x')
    (l₀ : ListBlank (Fin 2)) :
    (x.toCfg l₀ default) [tm]⊢ (x'.toCfg l₀ default) := by
  rcases x with ⟨l, _ | ⟨m, r₀⟩, q, isR⟩
  · rcases isR with _ | _
    · cases h
    · rcases q with _ | _ | _ | _ | _ | _ | q <;>
        dsimp [stepR0infB, tmB] at h <;> cases h <;>
        simp [BCfgB.toCfg, bWord, bSym, bState, BusyBeaver.step, tm, Tape.write, Tape.move,
          A, B, C, D, E, F]
  · exact stepB_spec ⟨l, m :: r₀, q, isR⟩ h l₀ default

private def stepsR0infB : ℕ → BCfgB → Option BCfgB
  | 0, x =>
    match stepR0infB x with
    | none => some x
    | some _ => none
  | n + 1, x =>
    match stepR0infB x with
    | none => some x
    | some x' => stepsR0infB n x'

private theorem stepsR0infB_spec :
    ∀ n (x x' : BCfgB), stepsR0infB n x = some x' →
      ∀ l₀ : ListBlank (Fin 2), (x.toCfg l₀ default) [tm]⊢* (x'.toCfg l₀ default)
  | 0, x, x', h, _ => by
    dsimp only [stepsR0infB] at h
    rcases h_st : stepR0infB x with _ | _ <;> rw [h_st] at h <;> cases h
    exact stepStar_refl tm _
  | n + 1, x, x', h, l₀ => by
    dsimp only [stepsR0infB] at h
    rcases h_st : stepR0infB x with _ | y <;> rw [h_st] at h
    · cases h
      exact stepStar_refl tm _
    · exact stepStar_trans ⟨1, stepR0infB_spec x h_st l₀⟩ (stepsR0infB_spec n y x' h l₀)

private def steps1R0infB (n : ℕ) (x : BCfgB) : Option BCfgB :=
  match stepR0infB x with
  | none => none
  | some x' => stepsR0infB n x'

private theorem steps1R0infB_spec {n : ℕ} {x x' : BCfgB} (h : steps1R0infB n x = some x')
    (l₀ : ListBlank (Fin 2)) :
    (x.toCfg l₀ default) [tm]⊢⁺ (x'.toCfg l₀ default) := by
  dsimp only [steps1R0infB] at h
  rcases h_st : stepR0infB x with _ | y <;> rw [h_st] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, stepR0infB_spec x h_st l₀⟩
      (stepsR0infB_spec n y x' h l₀)

private def stepBoth0infB (x : BCfgB) : Option BCfgB :=
  match x.r with
  | [] =>
    match tmB x.q false with
    | none => none
    | some (q', w, d') =>
      if boolBeq x.isRight d' then
        some ⟨w :: x.l, [], q', d'⟩
      else
        some ⟨[w], x.l, q', d'⟩
  | _ :: _ => stepB x

private theorem stepBoth0infB_spec (x : BCfgB) {x' : BCfgB} (h : stepBoth0infB x = some x') :
    (x.toCfg default default) [tm]⊢ (x'.toCfg default default) := by
  rcases x with ⟨l, _ | ⟨m, r₀⟩, q, isR⟩
  · rcases q with _ | _ | _ | _ | _ | _ | q <;> rcases isR with _ | _ <;>
      dsimp [stepBoth0infB, tmB] at h <;> cases h <;>
      simp [BCfgB.toCfg, bWord, bSym, bState, BusyBeaver.step, tm, Tape.write, Tape.move,
        A, B, C, D, E, F]
  · exact stepB_spec ⟨l, m :: r₀, q, isR⟩ h default default

private def stepsExactBoth0infB : ℕ → BCfgB → Option BCfgB
  | 0, x => some x
  | n + 1, x =>
    match stepBoth0infB x with
    | none => none
    | some x' => stepsExactBoth0infB n x'

private theorem stepsExactBoth0infB_spec :
    ∀ n (x x' : BCfgB), stepsExactBoth0infB n x = some x' →
      (x.toCfg default default) [tm]⊢* (x'.toCfg default default)
  | 0, _, _, h => by
    cases h
    exact stepStar_refl tm _
  | n + 1, x, x', h => by
    dsimp only [stepsExactBoth0infB] at h
    rcases h_st : stepBoth0infB x with _ | y <;> rw [h_st] at h
    · cases h
    · exact stepStar_trans ⟨1, stepBoth0infB_spec x h_st⟩
        (stepsExactBoth0infB_spec n y x' h)

private def tmFlipB (q : ℕ) (m : Bool) : Option (ℕ × Bool × Bool) :=
  (tmB q m).map fun (q', w, d') => (q', w, !d')

private def stepFlipR0infB (x : BCfgB) : Option BCfgB :=
  match x.r with
  | [] =>
    match x.isRight with
    | true =>
      match tmFlipB x.q false with
      | none => none
      | some (q', w, d') =>
        if d' then
          some ⟨w :: x.l, [], q', true⟩
        else
          some ⟨[w], x.l, q', false⟩
    | false => none
  | m :: r₀ =>
    match tmFlipB x.q m with
    | none => none
    | some (q', w, d') =>
      if boolBeq x.isRight d' then
        some ⟨w :: x.l, r₀, q', d'⟩
      else
        some ⟨w :: r₀, x.l, q', d'⟩

private theorem stepFlipR0infB_spec (x : BCfgB) {x' : BCfgB} (h : stepFlipR0infB x = some x')
    (l₀ : ListBlank (Fin 2)) :
    (x.toCfg l₀ default) [flipTM tm]⊢ (x'.toCfg l₀ default) := by
  rcases x with ⟨l, _ | ⟨_ | _, r₀⟩, _ | _ | _ | _ | _ | _ | q, _ | _⟩ <;>
    dsimp [stepFlipR0infB, tmFlipB, tmB] at h <;> cases h <;>
    simp [BCfgB.toCfg, bWord, bSym, bState, BusyBeaver.step, flipTM, flipStmt, flipDir, tm,
      Tape.write, Tape.move, A, B, C, D, E, F]

private def stepsFlipExactB : ℕ → BCfgB → Option BCfgB
  | 0, x => some x
  | n + 1, x =>
    match stepFlipR0infB x with
    | none => none
    | some x' => stepsFlipExactB n x'

private theorem stepsFlipExactB_spec :
    ∀ n (x x' : BCfgB), stepsFlipExactB n x = some x' →
      ∀ l₀ : ListBlank (Fin 2), (x.toCfg l₀ default) [flipTM tm]⊢* (x'.toCfg l₀ default)
  | 0, _, _, h, _ => by
    cases h
    exact stepStar_refl _ _
  | n + 1, x, x', h, l₀ => by
    dsimp only [stepsFlipExactB] at h
    rcases h_st : stepFlipR0infB x with _ | y <;> rw [h_st] at h
    · cases h
    · exact stepStar_trans ⟨1, stepFlipR0infB_spec x h_st l₀⟩
        (stepsFlipExactB_spec n y x' h l₀)

private theorem bool_beq_iff (a b : Bool) : boolBeq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private def bWordEq : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => boolBeq a b && bWordEq as bs
  | _, _ => false

private theorem bWordEq_iff : ∀ xs ys : List Bool, bWordEq xs ys = true ↔ xs = ys
  | [], [] => by simp [bWordEq]
  | [], _ :: _ => by simp [bWordEq]
  | _ :: _, [] => by simp [bWordEq]
  | a :: as, b :: bs => by
    simp only [bWordEq, Bool.and_eq_true, bool_beq_iff, bWordEq_iff as bs, List.cons.injEq]

private def allFalse : List Bool → Bool
  | [] => true
  | a :: as => (!a) && allFalse as

private theorem allFalse_spec :
    ∀ xs : List Bool, allFalse xs = true → bWord xs +> (default : ListBlank (Fin 2)) = default
  | [], _ => rfl
  | false :: xs, h => by
    dsimp only [allFalse, Bool.not_false, Bool.true_and] at h
    rw [bWord_cons, Longitudinal.append_cons, allFalse_spec xs h]
    change ListBlank.cons (default : ListBlank (Fin 2)).head (default : ListBlank (Fin 2)).tail =
      default
    exact ListBlank.cons_head_tail default
  | true :: _, h => by cases h

private def eqR0infB : List Bool → List Bool → Bool
  | [], ys => allFalse ys
  | x :: xs, [] => allFalse (x :: xs)
  | x :: xs, y :: ys => boolBeq x y && eqR0infB xs ys

private theorem eqR0infB_spec :
    ∀ xs ys : List Bool, eqR0infB xs ys = true →
      bWord xs +> (default : ListBlank (Fin 2)) = bWord ys +> default
  | [], ys, h => (allFalse_spec ys h).symm
  | x :: xs, [], h => allFalse_spec (x :: xs) h
  | x :: xs, y :: ys, h => by
    dsimp only [eqR0infB] at h
    rw [Bool.and_eq_true, bool_beq_iff] at h
    rw [h.1, bWord_cons, bWord_cons, Longitudinal.append_cons, Longitudinal.append_cons,
      eqR0infB_spec xs ys h.2]

private def skipPrefixB (p l : List Bool) : Option (List Bool) :=
  let len := p.length
  if bWordEq p (l.take len) then some (l.drop len) else none

private theorem skipPrefixB_spec {p l rest : List Bool} (h : skipPrefixB p l = some rest) :
    l = p ++ rest := by
  dsimp only [skipPrefixB] at h
  cases h_eq : bWordEq p (l.take p.length) <;> rw [h_eq] at h
  · cases h
  · cases h
    have hp : l.take p.length = p := ((bWordEq_iff _ _).mp h_eq).symm
    have htd := List.take_append_drop p.length l
    rw [hp] at htd
    exact htd.symm

/-! ## Signals, Shift Rules for `W`, and Direct 1/2-Pass Tile Checkers -/

private def WB : List Bool :=
  [false, false, true, false, false, true, true, false, false, true, true, false]

private def W : List (Fin 2) := bWord WB

private def WMidB : List Bool :=
  [true, true, true, true, true, false, true, false, true, false, true, false]

private def WMid : List (Fin 2) := bWord WMidB

private def powWB : ℕ → List Bool
  | 0 => []
  | n + 1 => WB ++ powWB n

private theorem bWord_powWB : ∀ n : ℕ, bWord (powWB n) = W ^ n
  | 0 => rfl
  | n + 1 => by
    rw [powWB, bWord_append, pow_succ_list, bWord_powWB n]
    rfl

private def hR : DH0 (Fin 2) (Fin 6) := (B, [1, 0, 1, 0])

private def hE : DH0 (Fin 2) (Fin 6) := (E, [])

private def hF : DH0 (Fin 2) (Fin 6) := (F, [0, 0])

private def hret : Bool → DH0 (Fin 2) (Fin 6)
  | false => hE
  | true => hF

private def hSig : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) :=
  [(hR, hE)]

private def retQ : Bool → ℕ
  | false => 4
  | true => 5

private def retPreB : Bool → List Bool
  | false => []
  | true => [false, false]

private theorem bState_retQ (f : Bool) : bState (retQ f) = (hret f).1 := by
  cases f <;> rfl

private theorem bWord_retPreB (f : Bool) : bWord (retPreB f) = (hret f).2 := by
  cases f <;> rfl

private def checkSeg1B (f : Bool) (wIn wOut : List Bool) (t1 : ℕ) : Bool :=
  match steps1B t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
  | some ⟨l, [], q, false⟩ =>
    Nat.beq q (retQ f) &&
    match skipPrefixB (retPreB f) l with
    | some rest => bWordEq rest wOut
    | none => false
  | _ => false

private theorem checkSeg1B_spec {f : Bool} {wIn wOut : List Bool} {t1 : ℕ}
    (h : checkSeg1B f wIn wOut t1 = true) :
    SegRLs tm [(hR, hret f)] [] (bWord wIn) (bWord wOut) := by
  dsimp only [checkSeg1B] at h
  rcases h_st : steps1B t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
    _ | ⟨l, _ | _, q, _ | _⟩ <;> rw [h_st] at h
  any_goals cases h
  dsimp only at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  have h₂ := h.2
  rcases h_sp : skipPrefixB (retPreB f) l with _ | rest <;> rw [h_sp] at h₂
  · cases h₂
  · have hl := skipPrefixB_spec h_sp
    have hrest : rest = wOut := (bWordEq_iff _ _).mp h₂
    subst hrest
    refine .cons (fun l₀ r₀ => ?_) (.nil _)
    have h_run := steps1B_spec h_st l₀ r₀
    simp only [BCfgB.toCfg, hl, h.1, bState_retQ, bWord_nil, bWord_1010, bWord_append,
      bWord_retPreB, Longitudinal.append_nil, Longitudinal.append_assoc] at h_run
    cases f <;> exact h_run

private def checkSeg2B (f f' : Bool) (wIn xMid wOut : List Bool) (t1 t2 : ℕ) : Bool :=
  match stepsB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
  | some ⟨l₁, [], 1, true⟩ =>
    bWordEq l₁ ([true, false, true, false] ++ xMid) &&
    match stepsB t2 ⟨retPreB f', xMid, retQ f', false⟩ with
    | some ⟨l₂, [], q, false⟩ =>
      Nat.beq q (retQ f) &&
      match skipPrefixB (retPreB f) l₂ with
      | some rest => bWordEq rest wOut
      | none => false
    | _ => false
  | _ => false

private theorem checkSeg2B_spec {f f' : Bool} {wIn xMid wOut : List Bool} {t1 t2 : ℕ}
    (h : checkSeg2B f f' wIn xMid wOut t1 t2 = true) :
    SegRLs tm [(hR, hret f)] [(hR, hret f')] (bWord wIn) (bWord wOut) := by
  dsimp only [checkSeg2B] at h
  rcases h_s1 : stepsB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
    _ | ⟨l₁, _ | _, _ | ⟨_ | _, _⟩, _ | _⟩ <;> rw [h_s1] at h
  any_goals cases h
  simp only [Nat.zero_add] at h h_s1
  rw [Bool.and_eq_true] at h
  have hl₁ : l₁ = [true, false, true, false] ++ xMid := (bWordEq_iff _ _).mp h.1
  subst hl₁
  have h₂ := h.2
  rcases h_s2 : stepsB t2 ⟨retPreB f', xMid, retQ f', false⟩ with
    _ | ⟨l₂, _ | _, q, _ | _⟩ <;> rw [h_s2] at h₂
  any_goals cases h₂
  dsimp only at h₂
  rw [Bool.and_eq_true, Nat.beq_eq] at h₂
  have h₃ := h₂.2
  rcases h_sp : skipPrefixB (retPreB f) l₂ with _ | rest <;> rw [h_sp] at h₃
  · cases h₃
  · have hl₂ := skipPrefixB_spec h_sp
    have hrest : rest = wOut := (bWordEq_iff _ _).mp h₃
    subst hrest
    refine SegRLs.S' (w₂ := bWord xMid) (fun l₀ r₀ => ?_) (fun l₀ r₀ => ?_) (.nil _)
    · have hr := stepsB_spec t1 _ _ h_s1 l₀ r₀
      simpa only [BCfgB.toCfg, bState, bWord_nil, bWord_1010, bWord_append,
        Longitudinal.append_nil, Longitudinal.append_assoc, toDHCfg, hR] using hr
    · have hl := stepsB_spec t2 _ _ h_s2 l₀ r₀
      simp only [BCfgB.toCfg, hl₂, h₂.1, bState_retQ, bWord_nil, bWord_append, bWord_retPreB,
        Longitudinal.append_nil, Longitudinal.append_assoc] at hl
      cases f <;> cases f' <;> exact hl

private def checkTailB (f : Bool) (wIn wOut : List Bool) (t1 : ℕ) : Bool :=
  match steps1R0infB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
  | some ⟨l, [], q, false⟩ =>
    Nat.beq q (retQ f) &&
    match skipPrefixB (retPreB f) l with
    | some rest => eqR0infB rest wOut
    | none => false
  | _ => false

private theorem checkTailB_spec {f : Bool} {wIn wOut : List Bool} {t1 : ℕ}
    (h : checkTailB f wIn wOut t1 = true) :
    SideRL tm hR (hret f) (bWord wIn +> default) (bWord wOut +> default) := by
  dsimp only [checkTailB] at h
  rcases h_st : steps1R0infB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
    _ | ⟨l, _ | _, q, _ | _⟩ <;> rw [h_st] at h
  any_goals cases h
  dsimp only at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  have h₂ := h.2
  rcases h_sp : skipPrefixB (retPreB f) l with _ | rest <;> rw [h_sp] at h₂
  · cases h₂
  · have hl := skipPrefixB_spec h_sp
    have heq := eqR0infB_spec rest wOut h₂
    intro l₀
    have hr := steps1R0infB_spec h_st l₀
    simp only [BCfgB.toCfg, hl, h.1, bState_retQ, bWord_nil, bWord_1010, bWord_append,
      bWord_retPreB, Longitudinal.append_nil, Longitudinal.append_assoc, heq] at hr
    cases f <;> exact hr

private def checkRightB (wIn xMid : List Bool) (t1 : ℕ) : Bool :=
  match stepsB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
  | some ⟨l₁, [], 1, true⟩ => bWordEq l₁ ([true, false, true, false] ++ xMid)
  | _ => false

private theorem checkRightB_spec {wIn xMid : List Bool} {t1 : ℕ}
    (h : checkRightB wIn xMid t1 = true) (l₀ r₀ : ListBlank (Fin 2)) :
    (([1, 0, 1, 0] +> l₀) {{B}}> (bWord wIn +> r₀)) [tm]⊢*
      (([1, 0, 1, 0] +> (bWord xMid +> l₀)) {{B}}> r₀) := by
  dsimp only [checkRightB] at h
  rcases h_s1 : stepsB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
    _ | ⟨l₁, _ | _, _ | ⟨_ | _, _⟩, _ | _⟩ <;> rw [h_s1] at h
  any_goals cases h
  have hl₁ : l₁ = [true, false, true, false] ++ xMid := (bWordEq_iff _ _).mp h
  subst hl₁
  have hr := stepsB_spec t1 _ _ h_s1 l₀ r₀
  simpa only [BCfgB.toCfg, bState, bWord_nil, bWord_1010, bWord_append,
    Longitudinal.append_nil, Longitudinal.append_assoc] using hr

private def HaltsTm (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg : Cfg (Fin 2) (Fin 6), (c [tm]⊢* cfg) ∧ (step tm cfg).isNone

private theorem haltsFrom_of_halted {c : Cfg (Fin 2) (Fin 6)} (h : (step tm c).isNone) :
    HaltsTm c :=
  ⟨c, stepStar_refl tm c, h⟩

private theorem haltsFrom_of_stepStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h₁₂ : c₁ [tm]⊢* c₂) (h₂ : HaltsTm c₂) : HaltsTm c₁ := by
  rcases h₂ with ⟨cfg, h₂₃, hh⟩
  exact ⟨cfg, stepStar_trans h₁₂ h₂₃, hh⟩

private def checkHaltB (wIn : List Bool) (t1 : ℕ) : Bool :=
  match stepsB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
  | some ⟨_, true :: _, 1, _⟩ => true
  | _ => false

private theorem checkHaltB_spec {wIn : List Bool} {t1 : ℕ}
    (h : checkHaltB wIn t1 = true) (l₀ r₀ : ListBlank (Fin 2)) :
    HaltsTm (([1, 0, 1, 0] +> l₀) {{B}}> (bWord wIn +> r₀)) := by
  dsimp only [checkHaltB] at h
  rcases h_st : stepsB t1 ⟨[true, false, true, false], wIn, 1, true⟩ with
    _ | ⟨l₁, _ | ⟨_ | _, r₁⟩, _ | ⟨_ | _, _⟩, d⟩ <;> rw [h_st] at h
  any_goals cases h
  have hr := stepsB_spec t1 _ _ h_st l₀ r₀
  simp only [BCfgB.toCfg, bState, bWord_1010] at hr
  refine haltsFrom_of_stepStar hr (haltsFrom_of_halted ?_)
  cases d <;> simp [bWord, bSym, BusyBeaver.step, tm, B]

private theorem passW_one : SegRR tm hR hR W WMid := by
  have hc : checkRightB WB WMidB 29 = true := by decide
  intro l r
  exact checkRightB_spec hc l r

private theorem wallLL_E : SegLL tm hE hE WMid W := by
  have hc : stepsB 61 ⟨[], WMidB, 4, false⟩ = some ⟨WB, [], 4, false⟩ := by decide
  intro l r
  have hr := stepsB_spec 61 _ _ hc l r
  simpa only [BCfgB.toCfg, toDHCfg, hE, bState, bWord_nil, WMid, W,
    Longitudinal.append_nil] using hr

private theorem wallLL_F : SegLL tm hF hF WMid W := by
  have hc : stepsB 61 ⟨[false, false], WMidB, 5, false⟩ =
      some ⟨[false, false] ++ WB, [], 5, false⟩ := by decide
  intro l r
  have hr := stepsB_spec 61 _ _ hc l r
  simpa only [BCfgB.toCfg, toDHCfg, hF, bState, bWord_nil, bWord_00, bWord_append, WMid, W,
    Longitudinal.append_nil, Longitudinal.append_assoc] using hr

private theorem wall (n : ℕ) : SegRLs tm hSig hSig (W ^ n) (W ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm hSig
  | succ n ih =>
    rw [pow_succ_list]
    have h1 : SegRLs tm hSig hSig W W := by
      simpa only [hSig, pow_one_list] using SegRLs.wall passW_one wallLL_E 1
    exact h1.concat ih

private theorem wallF (n : ℕ) : SegRLs tm [(hR, hF)] [(hR, hF)] (W ^ n) (W ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm [(hR, hF)]
  | succ n ih =>
    rw [pow_succ_list]
    have h1 : SegRLs tm [(hR, hF)] [(hR, hF)] W W := by
      simpa only [pow_one_list] using SegRLs.wall passW_one wallLL_F 1
    exact h1.concat ih

private theorem walls (f : Bool) (n : ℕ) :
    SegRLs tm [(hR, hret f)] [(hR, hret f)] (W ^ n) (W ^ n) := by
  cases f
  · exact wall n
  · exact wallF n

private theorem passW (n : ℕ) (l r : ListBlank (Fin 2)) :
    (([1, 0, 1, 0] +> l) {{B}}> (W ^ n +> r)) [tm]⊢*
      (([1, 0, 1, 0] +> (WMid ^ n +> l)) {{B}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl tm _
  | succ n ih =>
    rw [pow_succ_list, Longitudinal.append_assoc]
    have h1 := passW_one l (W ^ n +> r)
    simp only [toDHCfg, hR] at h1
    have h2 := ih (WMid +> l)
    have h_eq : WMid ^ n +> (WMid +> l) = WMid ^ (n + 1) +> l := by
      rw [← Longitudinal.append_assoc, ← pow_succ_list']
    rw [h_eq] at h2
    exact stepStar_trans h1 h2

private theorem comp_seg {a b c₁ c₂ u₁ g₁ u₂ g₂ : ℕ} {w w₁ w₂ : List (Fin 2)}
    (h₁ : SegRLs tm (hSig ^ a) (hSig ^ c₁) (w ++ W ^ u₁) (W ^ g₁ ++ w₁))
    (h₂ : SegRLs tm (hSig ^ b) (hSig ^ c₂) (w₁ ++ W ^ u₂) (W ^ g₂ ++ w₂)) :
    SegRLs tm (hSig ^ (a + b)) (hSig ^ (c₁ + c₂)) (w ++ W ^ (u₁ + u₂)) (W ^ (g₁ + g₂) ++ w₂) := by
  rw [pow_add_list hSig a b, pow_add_list hSig c₁ c₂, pow_add_list W u₁ u₂, pow_add_list W g₁ g₂]
  have i₁ :
      SegRLs tm (hSig ^ a) (hSig ^ c₁) (w ++ (W ^ u₁ ++ W ^ u₂)) (W ^ g₁ ++ (w₁ ++ W ^ u₂)) := by
    have hc := h₁.concat (SegRLs.wall_pow (wall u₂) c₁)
    simpa only [List.append_assoc] using hc
  have i₂ :
      SegRLs tm (hSig ^ b) (hSig ^ c₂) (W ^ g₁ ++ (w₁ ++ W ^ u₂)) (W ^ g₁ ++ (W ^ g₂ ++ w₂)) := by
    have hc := (SegRLs.wall_pow (wall g₁) b).concat h₂
    simpa only [List.append_assoc] using hc
  simpa only [List.append_assoc] using i₁.trans i₂

private theorem comp_tail {a b g₁ g₂ : ℕ} {w w₁ w₂ : List (Fin 2)}
    (h₁ : SideRLs tm (hSig ^ a) (w +> default) ((W ^ g₁ ++ w₁) +> default))
    (h₂ : SideRLs tm (hSig ^ b) (w₁ +> default) ((W ^ g₂ ++ w₂) +> default)) :
    SideRLs tm (hSig ^ (a + b)) (w +> default) ((W ^ (g₁ + g₂) ++ w₂) +> default) := by
  rw [pow_add_list hSig a b, pow_add_list W g₁ g₂]
  have i₂ : SideRLs tm (hSig ^ b) ((W ^ g₁ ++ w₁) +> default)
      ((W ^ g₁ ++ (W ^ g₂ ++ w₂)) +> default) := by
    rw [Longitudinal.append_assoc, Longitudinal.append_assoc]
    exact (SegRLs.wall_pow (wall g₁) b).sideRLs_concat h₂
  simpa only [List.append_assoc] using h₁.trans i₂

/-! ## Balanced Binary Search Tree Indexed by `Nat` -/

private inductive Bst (α : Type) where
  | leaf : Bst α
  | node : ℕ → α → Bst α → Bst α → Bst α

private def Bst.get? {α : Type} (t : Bst α) (k : ℕ) : Option α :=
  match t with
  | .leaf => none
  | .node tk v l r =>
    if Nat.blt k tk then l.get? k
    else if Nat.blt tk k then r.get? k
    else some v

private def Bst.allB {α : Type} (p : ℕ → α → Bool) : Bst α → Bool
  | .leaf => true
  | .node k v l r => p k v && Bst.allB p l && Bst.allB p r

private theorem Bst.allB_spec {α : Type} {p : ℕ → α → Bool} :
    ∀ (t : Bst α), Bst.allB p t = true → ∀ k v, t.get? k = some v → p k v = true
  | .leaf, _, _, _, h => by cases h
  | .node tk tv l r, hall, k, v, hget => by
    dsimp only [Bst.allB] at hall
    rw [Bool.and_assoc, Bool.and_eq_true, Bool.and_eq_true] at hall
    dsimp only [Bst.get?] at hget
    cases h₁ : Nat.blt k tk <;> rw [h₁] at hget
    · simp only [Bool.false_eq_true, ↓reduceIte] at hget
      cases h₂ : Nat.blt tk k <;> rw [h₂] at hget
      · simp only [Bool.false_eq_true, ↓reduceIte] at hget
        cases hget
        have hk : k = tk := by
          have hle1 : tk ≤ k := by
            rcases Nat.lt_or_ge k tk with hlt | hge
            · exact absurd (Nat.blt_eq.mpr hlt) (by simp [h₁])
            · exact hge
          have hle2 : k ≤ tk := by
            rcases Nat.lt_or_ge tk k with hlt | hge
            · exact absurd (Nat.blt_eq.mpr hlt) (by simp [h₂])
            · exact hge
          omega
        subst hk
        exact hall.1
      · simp only [↓reduceIte] at hget
        exact Bst.allB_spec r hall.2.2 k v hget
    · simp only [↓reduceIte] at hget
      exact Bst.allB_spec l hall.2.1 k v hget

/-! ## Bit-Packed Word Dictionary and Rule Tables -/

private def decodeBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, b => Nat.beq (b % 2) 1 :: decodeBits n (b / 2)

private def wordTree : Bst (ℕ × ℕ) :=
  .node 207 (48, 112589453812836)
    (.node 103 (16, 25702)
      (.node 51 (36, 27487659108)
        (.node 25 (13, 3300)
          (.node 12 (33, 3435956836)
            (.node 6 (23, 5016164)
              (.node 3 (2, 2)
                (.node 1 (9, 228)
                  (.node 0 (0, 0) .leaf .leaf)
                  (.node 2 (10, 612) .leaf .leaf))
                (.node 5 (19, 314596)
                  (.node 4 (17, 52452) .leaf .leaf)
                  .leaf))
              (.node 9 (28, 160730340)
                (.node 8 (44, 10519663381092)
                  (.node 7 (40, 657478700260) .leaf .leaf)
                  .leaf)
                (.node 11 (20, 641252)
                  (.node 10 (32, 2571930212) .leaf .leaf)
                  .leaf)))
            (.node 19 (17, 52388)
              (.node 16 (41, 1723570358884)
                (.node 14 (25, 13421156)
                  (.node 13 (20, 821860) .leaf .leaf)
                  (.node 15 (37, 107722886372) .leaf .leaf))
                (.node 18 (15, 19044)
                  (.node 17 (11, 1252) .leaf .leaf)
                  .leaf))
              (.node 22 (13, 2660)
                (.node 21 (17, 51812)
                  (.node 20 (7, 100) .leaf .leaf)
                  .leaf)
                (.node 24 (21, 838244)
                  (.node 23 (25, 13421732) .leaf .leaf)
                  .leaf))))
          (.node 38 (8, 102)
            (.node 32 (16, 25700)
              (.node 29 (26, 21547620)
                (.node 27 (34, 6925617764)
                  (.node 26 (30, 432590052) .leaf .leaf)
                  (.node 28 (26, 27053220) .leaf .leaf))
                (.node 31 (16, 26214)
                  (.node 30 (14, 6500) .leaf .leaf)
                  .leaf))
              (.node 35 (26, 26843492)
                (.node 34 (54, 7205723755547236)
                  (.node 33 (50, 450357734460644) .leaf .leaf)
                  .leaf)
                (.node 37 (28, 105276516)
                  (.node 36 (12, 1606) .leaf .leaf)
                  .leaf)))
            (.node 45 (25, 13159588)
              (.node 42 (28, 107373670)
                (.node 40 (12, 1638)
                  (.node 39 (8, 100) .leaf .leaf)
                  (.node 41 (20, 419430) .leaf .leaf))
                (.node 44 (41, 862425238116)
                  (.node 43 (37, 53901576420) .leaf .leaf)
                  .leaf))
              (.node 48 (28, 107373668)
                (.node 47 (17, 51428)
                  (.node 46 (41, 879609039460) .leaf .leaf)
                  .leaf)
                (.node 50 (34, 6866913892)
                  (.node 49 (30, 429181156) .leaf .leaf)
                  .leaf)))))
        (.node 77 (53, 3602862454656228)
          (.node 64 (32, 1684300900)
            (.node 58 (52, 1801431260882020)
              (.node 55 (44, 7036335449702)
                (.node 53 (25, 13159012)
                  (.node 52 (24, 6710372) .leaf .leaf)
                  (.node 54 (20, 411238) .leaf .leaf))
                (.node 57 (48, 112589451716198)
                  (.node 56 (48, 112581400618084) .leaf .leaf)
                  .leaf))
              (.node 61 (36, 27487659622)
                (.node 60 (36, 26948822116)
                  (.node 59 (36, 27487790182) .leaf .leaf)
                  .leaf)
                (.node 63 (32, 1717986918)
                  (.node 62 (36, 27487782502) .leaf .leaf)
                  .leaf)))
            (.node 71 (40, 431214716518)
              (.node 68 (26, 26527972)
                (.node 66 (33, 3435973860)
                  (.node 65 (24, 6579302) .leaf .leaf)
                  (.node 67 (49, 225178903415396) .leaf .leaf))
                (.node 70 (22, 1644900)
                  (.node 69 (30, 424462948) .leaf .leaf)
                  .leaf))
              (.node 74 (48, 112589451708006)
                (.node 73 (48, 112589990552676)
                  (.node 72 (56, 28823028991550564) .leaf .leaf)
                  .leaf)
                (.node 76 (72, 1888937585939979723876)
                  (.node 75 (68, 118058596914174518886) .leaf .leaf)
                  .leaf))))
          (.node 90 (16, 51430)
            (.node 84 (9, 230)
              (.node 81 (17, 52390)
                (.node 79 (41, 878962959974)
                  (.node 78 (57, 57645799278676580) .leaf .leaf)
                  (.node 80 (45, 14063440782436) .leaf .leaf))
                (.node 83 (21, 844900)
                  (.node 82 (17, 58468) .leaf .leaf)
                  .leaf))
              (.node 87 (29, 214754404)
                (.node 86 (25, 13421798)
                  (.node 85 (25, 13411428) .leaf .leaf)
                  .leaf)
                (.node 89 (33, 3435979876)
                  (.node 88 (29, 214748390) .leaf .leaf)
                  .leaf)))
            (.node 97 (60, 461168601303762534)
              (.node 94 (34, 6866914532)
                (.node 92 (6, 38)
                  (.node 91 (20, 828516) .leaf .leaf)
                  (.node 93 (13, 3302) .leaf .leaf))
                (.node 96 (52, 1801431227458660)
                  (.node 95 (34, 6787205732) .leaf .leaf)
                  .leaf))
              (.node 100 (40, 431214584932)
                (.node 99 (36, 26948822630)
                  (.node 98 (64, 7378697620860331108) .leaf .leaf)
                  .leaf)
                (.node 102 (24, 6710886)
                  (.node 101 (24, 6579300) .leaf .leaf)
                  .leaf))))))
      (.node 155 (34, 6740822628)
        (.node 129 (41, 880038667364)
          (.node 116 (45, 14073681463524)
            (.node 110 (34, 6791154916)
              (.node 107 (34, 6740823268)
                (.node 105 (37, 54975581412)
                  (.node 104 (32, 1717986404) .leaf .leaf)
                  (.node 106 (37, 53897628260) .leaf .leaf))
                (.node 109 (10, 356)
                  (.node 108 (38, 107857349220) .leaf .leaf)
                  .leaf))
              (.node 113 (44, 6899401909348)
                (.node 112 (40, 431212611174)
                  (.node 111 (38, 108662655588) .leaf .leaf)
                  .leaf)
                (.node 115 (60, 461166394195862628)
                  (.node 114 (44, 7036874417766) .leaf .leaf)
                  .leaf)))
            (.node 123 (54, 7116901617027684)
              (.node 120 (41, 879605091556)
                (.node 118 (37, 54975581348)
                  (.node 117 (49, 225178903431780) .leaf .leaf)
                  (.node 119 (45, 14073748818532) .leaf .leaf))
                (.node 122 (54, 7200481747979428)
                  (.node 121 (53, 3602862454655588) .leaf .leaf)
                  .leaf))
              (.node 126 (33, 3435710692)
                (.node 125 (32, 1717978726)
                  (.node 124 (42, 1759210183012) .leaf .leaf)
                  .leaf)
                (.node 128 (37, 55000327782)
                  (.node 127 (37, 54971386468) .leaf .leaf)
                  .leaf))))
          (.node 142 (18, 84196)
            (.node 136 (25, 13427812)
              (.node 133 (37, 53926585958)
                (.node 131 (26, 27042916)
                  (.node 130 (22, 1689830) .leaf .leaf)
                  (.node 132 (14, 6630) .leaf .leaf))
                (.node 135 (21, 838886)
                  (.node 134 (41, 862858798180) .leaf .leaf)
                  .leaf))
              (.node 139 (22, 1362150)
                (.node 138 (38, 122621299300)
                  (.node 137 (34, 7663570148) .leaf .leaf)
                  .leaf)
                (.node 141 (10, 358)
                  (.node 140 (26, 21800036) .leaf .leaf)
                  .leaf)))
            (.node 149 (50, 450358606875236)
              (.node 146 (22, 1676452)
                (.node 144 (14, 5348)
                  (.node 143 (22, 1362532) .leaf .leaf)
                  (.node 145 (30, 429165156) .leaf .leaf))
                (.node 148 (46, 28147358420132)
                  (.node 147 (22, 1657444) .leaf .leaf)
                  .leaf))
              (.node 152 (38, 109950831844)
                (.node 151 (46, 28147412945508)
                  (.node 150 (42, 1759213308132) .leaf .leaf)
                  .leaf)
                (.node 154 (30, 421088420)
                  (.node 153 (38, 107798628964) .leaf .leaf)
                  .leaf)))))
        (.node 181 (25, 13158628)
          (.node 168 (53, 3602862454917732)
            (.node 162 (4, 6)
              (.node 159 (26, 26511972)
                (.node 157 (30, 421317220)
                  (.node 156 (26, 26331364) .leaf .leaf)
                  (.node 158 (22, 1645796) .leaf .leaf))
                (.node 161 (34, 6871927396)
                  (.node 160 (18, 103588) .leaf .leaf)
                  .leaf))
              (.node 165 (41, 879609040036)
                (.node 164 (49, 225179914242660)
                  (.node 163 (33, 3368848612) .leaf .leaf)
                  .leaf)
                (.node 167 (49, 225178903431396)
                  (.node 166 (57, 57645799278430820) .leaf .leaf)
                  .leaf)))
            (.node 175 (41, 879605091492)
              (.node 172 (45, 14073748572772)
                (.node 170 (49, 225178907609700)
                  (.node 169 (45, 14073681464548) .leaf .leaf)
                  (.node 171 (41, 879605107876) .leaf .leaf))
                (.node 174 (41, 879609301604)
                  (.node 173 (37, 54975580388) .leaf .leaf)
                  .leaf))
              (.node 178 (41, 879609285220)
                (.node 177 (37, 54975319268)
                  (.node 176 (45, 14073681726052) .leaf .leaf)
                  .leaf)
                (.node 180 (33, 3368602212)
                  (.node 179 (33, 3435973796) .leaf .leaf)
                  .leaf))))
          (.node 194 (29, 210537060)
            (.node 188 (41, 879605107300)
              (.node 185 (29, 214748324)
                (.node 183 (21, 822500)
                  (.node 182 (29, 210553444) .leaf .leaf)
                  (.node 184 (37, 54975564388) .leaf .leaf))
                (.node 187 (37, 54975318244)
                  (.node 186 (45, 14073681463908) .leaf .leaf)
                  .leaf))
              (.node 191 (33, 3435972836)
                (.node 190 (33, 3368847972)
                  (.node 189 (33, 3435957476) .leaf .leaf)
                  .leaf)
                (.node 193 (29, 214748388)
                  (.node 192 (37, 54975580772) .leaf .leaf)
                  .leaf)))
            (.node 201 (48, 112589988586596)
              (.node 198 (44, 7036872320100)
                (.node 196 (26, 26823908)
                  (.node 195 (21, 822436) .leaf .leaf)
                  (.node 197 (40, 439771096166) .leaf .leaf))
                (.node 200 (44, 7036840862822)
                  (.node 199 (40, 439804650596) .leaf .leaf)
                  .leaf))
              (.node 204 (36, 27487790694)
                (.node 203 (44, 7036874417252)
                  (.node 202 (40, 439804642918) .leaf .leaf)
                  .leaf)
                (.node 206 (44, 7036840731750)
                  (.node 205 (52, 1801431227327588) .leaf .leaf)
                  .leaf)))))))
    (.node 311 (33, 3368864356)
      (.node 259 (53, 3602862521764452)
        (.node 233 (64, 7378662445111600228)
          (.node 220 (22, 1658084)
            (.node 214 (32, 1717986406)
              (.node 211 (32, 1684431972)
                (.node 209 (44, 7036874286180)
                  (.node 208 (40, 439802553958) .leaf .leaf)
                  (.node 210 (28, 105268838) .leaf .leaf))
                (.node 213 (40, 439804519524)
                  (.node 212 (24, 6579814) .leaf .leaf)
                  .leaf))
              (.node 217 (44, 7036840862820)
                (.node 216 (40, 439802545766)
                  (.node 215 (48, 112589451715684) .leaf .leaf)
                  .leaf)
                (.node 219 (28, 105276518)
                  (.node 218 (36, 26950788196) .leaf .leaf)
                  .leaf)))
            (.node 227 (40, 439804650598)
              (.node 224 (48, 112589956998246)
                (.node 222 (30, 429495460)
                  (.node 221 (38, 109950831204) .leaf .leaf)
                  (.node 223 (30, 421087844) .leaf .leaf))
                (.node 226 (44, 7036872320614)
                  (.node 225 (52, 1801439314076772) .leaf .leaf)
                  .leaf))
              (.node 230 (64, 7378662445078045798)
                (.node 229 (44, 7036840732262)
                  (.node 228 (56, 28822899637249124) .leaf .leaf)
                  .leaf)
                (.node 232 (60, 461166402817386086)
                  (.node 231 (68, 118058599121250837604) .leaf .leaf)
                  .leaf))))
          (.node 246 (40, 439802553446)
            (.node 240 (40, 431214716006)
              (.node 237 (52, 1766246855369828)
                (.node 235 (56, 28259949683827812)
                  (.node 234 (56, 28822900176217190) .leaf .leaf)
                  (.node 236 (48, 110390428452454) .leaf .leaf))
                (.node 239 (48, 110390967297124)
                  (.node 238 (44, 6899401778790) .leaf .leaf)
                  .leaf))
              (.node 243 (40, 439771096164)
                (.node 242 (36, 27485685350)
                  (.node 241 (44, 7036335449188) .leaf .leaf)
                  .leaf)
                (.node 245 (48, 112589453681764)
                  (.node 244 (32, 1717855846) .leaf .leaf)
                  .leaf)))
            (.node 253 (40, 439802553444)
              (.node 250 (28, 105277030)
                (.node 248 (32, 1684424294)
                  (.node 247 (40, 431212618852) .leaf .leaf)
                  (.node 249 (36, 26950919268) .leaf .leaf))
                (.node 252 (24, 6710374)
                  (.node 251 (32, 1717855332) .leaf .leaf)
                  .leaf))
              (.node 256 (44, 7036840731748)
                (.node 255 (28, 107374182)
                  (.node 254 (36, 27487790180) .leaf .leaf)
                  .leaf)
                (.node 258 (49, 225178903432356)
                  (.node 257 (36, 27487659110) .leaf .leaf)
                  .leaf)))))
        (.node 285 (26, 26512548)
          (.node 272 (37, 55371523172)
            (.node 266 (29, 210554084)
              (.node 263 (41, 862425221732)
                (.node 261 (49, 225178907626084)
                  (.node 260 (45, 14073681725668) .leaf .leaf)
                  (.node 262 (41, 879605107940) .leaf .leaf))
                (.node 265 (37, 53901838948)
                  (.node 264 (33, 3368848548) .leaf .leaf)
                  .leaf))
              (.node 269 (37, 54935315558)
                (.node 268 (37, 54975564964)
                  (.node 267 (45, 14073744624228) .leaf .leaf)
                  .leaf)
                (.node 271 (33, 3460712038)
                  (.node 270 (41, 885942281316) .leaf .leaf)
                  .leaf)))
            (.node 279 (25, 13411942)
              (.node 276 (37, 54933218404)
                (.node 274 (29, 174351460)
                  (.node 273 (29, 216295014) .leaf .leaf)
                  (.node 275 (21, 681062) .leaf .leaf))
                (.node 278 (33, 3433456740)
                  (.node 277 (29, 214582886) .leaf .leaf)
                  .leaf))
              (.node 282 (21, 681060)
                (.node 281 (21, 844902)
                  (.node 280 (29, 216294500) .leaf .leaf)
                  .leaf)
                (.node 284 (17, 52454)
                  (.node 283 (13, 2662) .leaf .leaf)
                  .leaf))))
          (.node 298 (40, 439804520038)
            (.node 292 (40, 431181031014)
              (.node 289 (52, 1766117500937316)
                (.node 287 (60, 461168601842607204)
                  (.node 286 (56, 28823037581485670) .leaf .leaf)
                  (.node 288 (52, 1801439850947686) .leaf .leaf))
                (.node 291 (48, 110382343939172)
                  (.node 290 (44, 6898896488038) .leaf .leaf)
                  .leaf))
              (.node 295 (52, 1801439311979620)
                (.node 294 (36, 26950919270)
                  (.node 293 (44, 6899435332708) .leaf .leaf)
                  .leaf)
                (.node 297 (48, 112589957129316)
                  (.node 296 (44, 7036872312422) .leaf .leaf)
                  .leaf)))
            (.node 305 (40, 431181030500)
              (.node 302 (44, 7036874409574)
                (.node 300 (48, 112589451715686)
                  (.node 299 (56, 28822899639215204) .leaf .leaf)
                  (.node 301 (52, 1801439848850532) .leaf .leaf))
                (.node 304 (40, 439804651110)
                  (.node 303 (48, 112589990683748) .leaf .leaf)
                  .leaf))
              (.node 308 (36, 27485693028)
                (.node 307 (32, 1684431974)
                  (.node 306 (32, 1684300902) .leaf .leaf)
                  .leaf)
                (.node 310 (29, 210537636)
                  (.node 309 (28, 107365990) .leaf .leaf)
                  .leaf))))))
      (.node 363 (34, 6871946404)
        (.node 337 (26, 26855652)
          (.node 324 (30, 429181540)
            (.node 318 (25, 13421796)
              (.node 315 (37, 54975318628)
                (.node 313 (29, 214731364)
                  (.node 312 (25, 13159652) .leaf .leaf)
                  (.node 314 (21, 838820) .leaf .leaf))
                (.node 317 (33, 3435973220)
                  (.node 316 (29, 214747364) .leaf .leaf)
                  .leaf))
              (.node 321 (30, 421317796)
                (.node 320 (33, 3435957412)
                  (.node 319 (41, 879605090916) .leaf .leaf)
                  .leaf)
                (.node 323 (26, 26822884)
                  (.node 322 (34, 6866651748) .leaf .leaf)
                  .leaf)))
            (.node 331 (26, 29935844)
              (.node 328 (18, 84580)
                (.node 326 (26, 27036260)
                  (.node 325 (22, 1676516) .leaf .leaf)
                  (.node 327 (18, 105636) .leaf .leaf))
                (.node 330 (34, 7663569508)
                  (.node 329 (30, 424463524) .leaf .leaf)
                  .leaf))
              (.node 334 (38, 109946112612)
                (.node 333 (22, 1871076)
                  (.node 332 (30, 478988900) .leaf .leaf)
                  .leaf)
                (.node 336 (34, 6875040356)
                  (.node 335 (30, 429477028) .leaf .leaf)
                  .leaf))))
          (.node 350 (46, 27800464296548)
            (.node 344 (52, 1801431227450982)
              (.node 341 (52, 1801439313945700)
                (.node 339 (22, 1678564)
                  (.node 338 (30, 429705828) .leaf .leaf)
                  (.node 340 (36, 26950788710) .leaf .leaf))
                (.node 343 (60, 461166394227450980)
                  (.node 342 (44, 7036872320102) .leaf .leaf)
                  .leaf))
              (.node 347 (46, 27800396941540)
                (.node 346 (52, 1801431227327590)
                  (.node 345 (56, 28822899639346276) .leaf .leaf)
                  .leaf)
                (.node 349 (42, 1737524808932)
                  (.node 348 (50, 444806351080036) .leaf .leaf)
                  .leaf)))
            (.node 357 (38, 109954256036)
              (.node 354 (50, 450358670051940)
                (.node 352 (54, 7205738720578148)
                  (.node 351 (38, 108595563684) .leaf .leaf)
                  (.node 353 (46, 28147416877284) .leaf .leaf))
                (.node 356 (46, 28148289538660)
                  (.node 355 (42, 1759213554916) .leaf .leaf)
                  .leaf))
              (.node 360 (34, 6732696164)
                (.node 359 (30, 420792548)
                  (.node 358 (38, 107722885732) .leaf .leaf)
                  .leaf)
                (.node 362 (42, 1759218272868)
                  (.node 361 (26, 26299620) .leaf .leaf)
                  .leaf)))))
        (.node 389 (38, 109866420836)
          (.node 376 (33, 3435963494)
            (.node 370 (33, 3437651046)
              (.node 367 (37, 54975319204)
                (.node 365 (29, 214732004)
                  (.node 364 (50, 450357806844516) .leaf .leaf)
                  (.node 366 (45, 14073681709668) .leaf .leaf))
                (.node 369 (29, 210553060)
                  (.node 368 (37, 53901576804) .leaf .leaf)
                  .leaf))
              (.node 373 (45, 14073679209572)
                (.node 372 (41, 879604942438)
                  (.node 371 (49, 225178865263716) .leaf .leaf)
                  .leaf)
                (.node 375 (41, 879606654052)
                  (.node 374 (37, 54975309414) .leaf .leaf)
                  .leaf)))
            (.node 383 (33, 3370542182)
              (.node 380 (21, 838822)
                (.node 378 (25, 13159014)
                  (.node 377 (33, 3368707172) .leaf .leaf)
                  (.node 379 (29, 214738020) .leaf .leaf))
                (.node 382 (22, 1696868)
                  (.node 381 (18, 105638) .leaf .leaf)
                  .leaf))
              (.node 386 (26, 30197988)
                (.node 385 (34, 7730678372)
                  (.node 384 (30, 478989476) .leaf .leaf)
                  .leaf)
                (.node 388 (22, 1887460)
                  (.node 387 (30, 483183204) .leaf .leaf)
                  .leaf))))
          (.node 402 (24, 10275428)
            (.node 396 (36, 41092435108)
              (.node 393 (14, 5350)
                (.node 391 (18, 85158)
                  (.node 390 (30, 429165732) .leaf .leaf)
                  (.node 392 (22, 1369188) .leaf .leaf))
                (.node 395 (15, 19620)
                  (.node 394 (18, 91236) .leaf .leaf)
                  .leaf))
              (.node 399 (36, 41146960484)
                (.node 398 (32, 2571684068)
                  (.node 397 (40, 658351114852) .leaf .leaf)
                  .leaf)
                (.node 401 (28, 164153956)
                  (.node 400 (24, 10046628) .leaf .leaf)
                  .leaf)))
            (.node 409 (33, 6787222116)
              (.node 406 (33, 6732696740)
                (.node 404 (12, 3236)
                  (.node 403 (16, 40164) .leaf .leaf)
                  (.node 405 (19, 313956) .leaf .leaf))
                (.node 408 (29, 424200420)
                  (.node 407 (37, 108595300964) .leaf .leaf)
                  .leaf))
              (.node 412 (16, 58468)
                (.node 411 (12, 3238)
                  (.node 410 (25, 26512612) .leaf .leaf)
                  .leaf)
                (.node 414 (14, 9316)
                  (.node 413 (8, 230) .leaf .leaf)
                  .leaf)))))))

private def wordB (i : ℕ) : List Bool :=
  match wordTree.get? i with
  | some (ln, bits) => decodeBits ln bits
  | none => []

private def wordF (i : ℕ) : List (Fin 2) :=
  bWord (wordB i)

private theorem bWord_wordB (i : ℕ) : bWord (wordB i) = wordF i := rfl

private abbrev SegRule := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

private def segTree : Bst SegRule :=
  .node 223 (1, 70, 0, 0, 1, 1, 111, 0, 0, 0)
    (.node 134 (1, 383, 0, 0, 10, 6, 75, 0, 0, 0)
      (.node 65 (0, 48, 0, 0, 1, 12, 133, 0, 0, 0)
        (.node 41 (0, 51, 1, 0, 0, 12, 161, 0, 0, 0)
          (.node 27 (1, 28, 0, 0, 9, 1, 111, 0, 0, 0)
            (.node 21 (1, 1, 0, 0, 0, 12, 111, 0, 0, 0)
              (.node 12 (1, 23, 0, 0, 0, 12, 111, 0, 0, 0)
                (.node 4 (0, 12, 1, 0, 0, 12, 133, 0, 0, 0)
                  (.node 1 (0, 14, 1, 0, 0, 12, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 19 (0, 21, 0, 1, 0, 12, 35, 83, 17, 43871)
                  (.node 14 (1, 4, 0, 0, 0, 12, 111, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 24 (1, 25, 0, 0, 0, 12, 111, 0, 0, 0)
                (.node 23 (0, 53, 0, 1, 0, 12, 59, 117, 25, 11231071)
                  (.node 22 (1, 19, 1, 0, 0, 12, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 25 (0, 22, 0, 1, 0, 12, 31, 57, 13, 2751) .leaf .leaf)))
            (.node 36 (1, 162, 0, 0, 2, 12, 45, 0, 0, 0)
              (.node 31 (0, 32, 0, 1, 0, 12, 48, 68, 16, 24415)
                (.node 29 (1, 142, 0, 0, 7, 1, 111, 0, 0, 0)
                  (.node 28 (0, 29, 0, 1, 1, 1, 62, 114, 26, 22462143) .leaf .leaf)
                  .leaf)
                (.node 34 (1, 148, 0, 0, 15, 1, 111, 0, 0, 0)
                  (.node 32 (1, 38, 0, 0, 0, 12, 75, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 39 (1, 40, 1, 0, 0, 12, 75, 0, 0, 0)
                (.node 38 (0, 39, 0, 1, 0, 12, 24, 34, 8, 95)
                  (.node 37 (1, 54, 0, 0, 0, 12, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 40 (0, 48, 1, 0, 0, 12, 103, 0, 0, 0) .leaf .leaf))))
          (.node 54 (0, 52, 0, 0, 0, 12, 103, 0, 0, 0)
            (.node 48 (1, 41, 0, 0, 0, 12, 75, 0, 0, 0)
              (.node 45 (0, 46, 1, 0, 1, 1, 193, 0, 0, 0)
                (.node 44 (1, 163, 0, 0, 38, 12, 111, 0, 0, 0)
                  (.node 42 (0, 37, 0, 1, 0, 12, 76, 128, 28, 99966815) .leaf .leaf)
                  .leaf)
                (.node 47 (0, 24, 0, 0, 0, 12, 75, 0, 0, 0)
                  (.node 46 (1, 191, 0, 0, 6, 12, 111, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 52 (1, 31, 0, 0, 0, 12, 75, 0, 0, 0)
                (.node 51 (1, 42, 0, 0, 0, 12, 75, 0, 0, 0)
                  (.node 50 (1, 196, 0, 0, 5, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 53 (1, 47, 0, 0, 0, 12, 111, 0, 0, 0) .leaf .leaf)))
            (.node 60 (1, 210, 0, 0, 18, 12, 75, 0, 0, 0)
              (.node 58 (1, 200, 0, 0, 30, 12, 75, 0, 0, 0)
                (.node 57 (0, 58, 0, 0, 1, 1, 161, 0, 0, 0)
                  (.node 56 (1, 197, 0, 0, 8, 12, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 59 (0, 60, 0, 1, 1, 1, 100, 162, 36, 25591504735) .leaf .leaf))
              (.node 63 (0, 64, 0, 1, 3, 12, 96, 136, 32, 1600085855)
                (.node 62 (0, 199, 0, 0, 5, 12, 103, 0, 0, 0)
                  (.node 61 (0, 218, 0, 1, 9, 12, 100, 162, 36, 25601335135) .leaf .leaf)
                  .leaf)
                (.node 64 (1, 65, 0, 0, 2, 12, 75, 0, 0, 0) .leaf .leaf)))))
        (.node 100 (1, 307, 0, 0, 4, 4, 75, 0, 0, 0)
          (.node 82 (1, 84, 0, 0, 0, 6, 75, 0, 0, 0)
            (.node 74 (0, 96, 0, 0, 0, 6, 103, 0, 0, 0)
              (.node 69 (1, 220, 0, 0, 5, 1, 111, 0, 0, 0)
                (.node 67 (1, 175, 0, 0, 24, 12, 111, 0, 0, 0)
                  (.node 66 (0, 67, 1, 0, 1, 1, 249, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 73 (1, 227, 0, 0, 0, 6, 75, 0, 0, 0)
                  (.node 72 (1, 224, 0, 0, 4, 6, 75, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 80 (1, 269, 0, 0, 16, 6, 75, 0, 0, 0)
                (.node 78 (1, 258, 0, 0, 38, 12, 111, 0, 0, 0)
                  (.node 76 (1, 230, 0, 0, 34, 12, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 81 (0, 83, 0, 0, 0, 6, 81, 0, 0, 0) .leaf .leaf)))
            (.node 89 (1, 86, 0, 0, 6, 6, 75, 0, 0, 0)
              (.node 85 (1, 81, 0, 0, 0, 6, 75, 0, 0, 0)
                (.node 84 (0, 85, 1, 0, 0, 6, 79, 0, 0, 0)
                  (.node 83 (1, 93, 0, 0, 0, 6, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 87 (1, 135, 0, 0, 4, 6, 75, 0, 0, 0)
                  (.node 86 (0, 87, 0, 0, 1, 1, 79, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 96 (1, 229, 0, 0, 0, 6, 75, 0, 0, 0)
                (.node 95 (1, 285, 0, 0, 7, 1, 111, 0, 0, 0)
                  (.node 93 (0, 82, 0, 0, 0, 6, 79, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 98 (1, 286, 0, 0, 36, 12, 75, 0, 0, 0) .leaf .leaf))))
          (.node 117 (1, 120, 0, 0, 0, 6, 111, 0, 0, 0)
            (.node 108 (1, 321, 0, 0, 9, 1, 111, 0, 0, 0)
              (.node 103 (0, 104, 1, 0, 0, 4, 133, 0, 0, 0)
                (.node 102 (0, 101, 0, 1, 0, 4, 72, 102, 24, 6250335)
                  (.node 101 (1, 103, 0, 0, 0, 4, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 106 (1, 310, 0, 0, 16, 12, 111, 0, 0, 0)
                  (.node 104 (1, 102, 0, 0, 0, 4, 75, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 115 (1, 346, 0, 0, 34, 12, 75, 0, 0, 0)
                (.node 113 (1, 340, 0, 0, 38, 12, 75, 0, 0, 0)
                  (.node 111 (1, 329, 0, 0, 15, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 116 (0, 117, 0, 0, 0, 6, 75, 0, 0, 0) .leaf .leaf)))
            (.node 123 (1, 347, 0, 0, 19, 1, 111, 0, 0, 0)
              (.node 120 (0, 119, 0, 0, 0, 6, 163, 0, 0, 0)
                (.node 119 (1, 118, 0, 0, 0, 6, 111, 0, 0, 0)
                  (.node 118 (0, 121, 1, 0, 0, 6, 279, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 121 (1, 116, 0, 0, 0, 6, 111, 0, 0, 0) .leaf .leaf))
              (.node 129 (1, 370, 0, 0, 14, 6, 75, 0, 0, 0)
                (.node 127 (1, 365, 0, 0, 20, 12, 111, 0, 0, 0)
                  (.node 125 (0, 254, 0, 0, 9, 12, 103, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 131 (1, 381, 0, 0, 3, 1, 75, 0, 0, 0) .leaf .leaf))))))
      (.node 180 (1, 181, 0, 0, 1, 1, 111, 0, 0, 0)
        (.node 159 (1, 160, 0, 0, 1, 1, 111, 0, 0, 0)
          (.node 148 (0, 149, 0, 0, 1, 1, 199, 0, 0, 0)
            (.node 143 (1, 144, 0, 0, 1, 1, 111, 0, 0, 0)
              (.node 138 (1, 384, 0, 0, 13, 1, 111, 0, 0, 0)
                (.node 136 (1, 284, 0, 0, 2, 6, 75, 0, 0, 0)
                  (.node 135 (0, 136, 0, 0, 1, 1, 79, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 142 (0, 143, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 140 (1, 391, 0, 0, 5, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 146 (0, 147, 0, 1, 1, 1, 42, 106, 22, 1403743)
                (.node 145 (1, 146, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 144 (0, 145, 1, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 147 (1, 30, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)))
            (.node 154 (0, 155, 0, 0, 1, 1, 141, 0, 0, 0)
              (.node 151 (1, 152, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 150 (0, 151, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 149 (1, 150, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 153 (1, 154, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 152 (0, 153, 0, 1, 1, 1, 90, 174, 38, 92319473503) .leaf .leaf)
                  .leaf))
              (.node 157 (1, 158, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 156 (0, 157, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 155 (1, 156, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 158 (0, 159, 0, 0, 1, 1, 109, 0, 0, 0) .leaf .leaf))))
          (.node 170 (1, 171, 0, 0, 1, 1, 111, 0, 0, 0)
            (.node 165 (0, 166, 1, 0, 1, 1, 309, 0, 0, 0)
              (.node 162 (1, 38, 1, 0, 1, 1, 45, 0, 0, 0)
                (.node 161 (1, 35, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 160 (0, 161, 1, 0, 1, 1, 135, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 164 (1, 165, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 163 (0, 164, 1, 0, 1, 1, 251, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 168 (1, 169, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 167 (0, 168, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 166 (1, 167, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 169 (0, 170, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf)))
            (.node 175 (0, 176, 0, 0, 1, 1, 105, 0, 0, 0)
              (.node 173 (0, 174, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 172 (1, 173, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 171 (0, 172, 0, 0, 1, 1, 163, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 174 (1, 66, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf))
              (.node 178 (1, 179, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 177 (0, 178, 0, 0, 1, 1, 133, 0, 0, 0)
                  (.node 176 (1, 177, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 179 (0, 180, 0, 1, 1, 1, 83, 151, 33, 2875154271) .leaf .leaf)))))
        (.node 202 (0, 203, 0, 0, 1, 1, 103, 0, 0, 0)
          (.node 191 (0, 192, 0, 0, 1, 1, 75, 0, 0, 0)
            (.node 186 (1, 187, 0, 0, 1, 1, 111, 0, 0, 0)
              (.node 183 (0, 184, 1, 0, 1, 1, 163, 0, 0, 0)
                (.node 182 (1, 183, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 181 (0, 182, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 185 (0, 186, 1, 0, 1, 1, 221, 0, 0, 0)
                  (.node 184 (1, 185, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 189 (0, 190, 0, 1, 1, 1, 83, 151, 33, 2884984671)
                (.node 188 (1, 189, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 187 (0, 188, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 190 (1, 45, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)))
            (.node 197 (0, 198, 0, 0, 1, 1, 191, 0, 0, 0)
              (.node 194 (1, 195, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 193 (0, 194, 0, 1, 1, 1, 79, 125, 29, 180313951)
                  (.node 192 (1, 193, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 196 (0, 159, 0, 1, 1, 1, 62, 114, 26, 22539103)
                  (.node 195 (0, 14, 0, 0, 1, 1, 105, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 200 (0, 201, 0, 0, 1, 1, 191, 0, 0, 0)
                (.node 199 (1, 63, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 198 (1, 62, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 201 (1, 202, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))))
          (.node 213 (1, 214, 0, 0, 1, 1, 75, 0, 0, 0)
            (.node 208 (0, 209, 0, 0, 1, 1, 161, 0, 0, 0)
              (.node 205 (1, 206, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 204 (0, 205, 1, 0, 1, 1, 277, 0, 0, 0)
                  (.node 203 (1, 204, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 207 (1, 208, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 206 (0, 207, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 211 (1, 212, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 210 (0, 211, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 209 (1, 59, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 212 (0, 213, 1, 0, 1, 1, 191, 0, 0, 0) .leaf .leaf)))
            (.node 218 (1, 219, 0, 0, 1, 1, 75, 0, 0, 0)
              (.node 216 (0, 217, 0, 0, 1, 1, 103, 0, 0, 0)
                (.node 215 (1, 216, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 214 (0, 215, 1, 0, 1, 1, 249, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 217 (1, 61, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))
              (.node 221 (1, 222, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 220 (0, 221, 1, 0, 1, 1, 163, 0, 0, 0)
                  (.node 219 (0, 198, 1, 0, 1, 1, 221, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 222 (0, 223, 0, 1, 1, 1, 66, 140, 30, 359358303) .leaf .leaf)))))))
    (.node 309 (0, 104, 0, 0, 1, 1, 103, 0, 0, 0)
      (.node 266 (0, 267, 1, 0, 1, 1, 221, 0, 0, 0)
        (.node 245 (1, 246, 0, 0, 1, 1, 75, 0, 0, 0)
          (.node 234 (0, 235, 0, 1, 1, 1, 152, 256, 56, 26834637669359455)
            (.node 229 (0, 73, 0, 0, 1, 1, 191, 0, 0, 0)
              (.node 226 (0, 73, 0, 0, 1, 1, 161, 0, 0, 0)
                (.node 225 (1, 226, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 224 (0, 225, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 228 (1, 74, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 227 (0, 228, 1, 0, 1, 1, 307, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 232 (0, 233, 0, 0, 1, 1, 161, 0, 0, 0)
                (.node 231 (1, 232, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 230 (0, 231, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 233 (1, 234, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)))
            (.node 240 (0, 241, 0, 0, 1, 1, 249, 0, 0, 0)
              (.node 237 (1, 238, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 236 (0, 237, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 235 (1, 236, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 239 (1, 240, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 238 (0, 239, 0, 0, 1, 1, 191, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 243 (1, 244, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 242 (0, 243, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 241 (1, 242, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 244 (0, 245, 1, 0, 1, 1, 249, 0, 0, 0) .leaf .leaf))))
          (.node 256 (1, 257, 0, 0, 1, 1, 75, 0, 0, 0)
            (.node 251 (1, 252, 0, 0, 1, 1, 75, 0, 0, 0)
              (.node 248 (0, 249, 0, 0, 1, 1, 103, 0, 0, 0)
                (.node 247 (1, 248, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 246 (0, 247, 0, 1, 1, 1, 104, 188, 40, 409464037215) .leaf .leaf)
                  .leaf)
                (.node 250 (0, 251, 0, 0, 1, 1, 161, 0, 0, 0)
                  (.node 249 (1, 250, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 254 (1, 255, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 253 (1, 125, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 252 (0, 253, 1, 0, 1, 1, 191, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 255 (0, 256, 1, 0, 1, 1, 219, 0, 0, 0) .leaf .leaf)))
            (.node 261 (1, 262, 0, 0, 1, 1, 111, 0, 0, 0)
              (.node 259 (1, 260, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 258 (0, 259, 0, 0, 1, 1, 163, 0, 0, 0)
                  (.node 257 (0, 199, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 260 (0, 261, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))
              (.node 264 (0, 265, 0, 0, 1, 1, 105, 0, 0, 0)
                (.node 263 (1, 264, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 262 (0, 263, 0, 1, 1, 1, 107, 185, 41, 738565906271) .leaf .leaf)
                  .leaf)
                (.node 265 (1, 266, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)))))
        (.node 288 (0, 289, 0, 1, 1, 1, 148, 230, 52, 1677164854337375)
          (.node 277 (0, 278, 0, 0, 1, 1, 103, 0, 0, 0)
            (.node 272 (1, 273, 0, 0, 1, 1, 75, 0, 0, 0)
              (.node 269 (0, 270, 0, 0, 1, 1, 227, 0, 0, 0)
                (.node 268 (0, 174, 0, 0, 1, 1, 105, 0, 0, 0)
                  (.node 267 (1, 268, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 271 (0, 272, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 270 (1, 271, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 275 (0, 276, 1, 0, 1, 1, 169, 0, 0, 0)
                (.node 274 (1, 275, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 273 (0, 274, 0, 1, 1, 1, 79, 125, 29, 200010431) .leaf .leaf)
                  .leaf)
                (.node 276 (1, 277, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)))
            (.node 283 (0, 85, 1, 1, 1, 1, 59, 117, 25, 12498271)
              (.node 280 (1, 281, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 279 (0, 280, 0, 0, 1, 1, 139, 0, 0, 0)
                  (.node 278 (1, 279, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 282 (1, 283, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 281 (0, 282, 0, 1, 1, 1, 55, 91, 21, 780991) .leaf .leaf)
                  .leaf))
              (.node 286 (0, 287, 0, 0, 1, 1, 191, 0, 0, 0)
                (.node 285 (0, 69, 0, 0, 1, 1, 105, 0, 0, 0)
                  (.node 284 (0, 83, 0, 0, 1, 1, 79, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 287 (1, 288, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))))
          (.node 299 (1, 300, 0, 0, 1, 1, 75, 0, 0, 0)
            (.node 294 (0, 295, 1, 0, 1, 1, 279, 0, 0, 0)
              (.node 291 (1, 292, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 290 (0, 291, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 289 (1, 290, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 293 (1, 294, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 292 (0, 293, 0, 0, 1, 1, 191, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 297 (1, 298, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 296 (0, 297, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 295 (1, 296, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 298 (0, 299, 1, 0, 1, 1, 307, 0, 0, 0) .leaf .leaf)))
            (.node 304 (0, 305, 0, 1, 1, 1, 120, 170, 40, 409621978975)
              (.node 302 (0, 303, 0, 0, 1, 1, 103, 0, 0, 0)
                (.node 301 (1, 302, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 300 (0, 301, 0, 0, 1, 1, 221, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 303 (1, 304, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))
              (.node 307 (0, 308, 0, 0, 1, 1, 191, 0, 0, 0)
                (.node 306 (0, 249, 0, 0, 1, 1, 133, 0, 0, 0)
                  (.node 305 (1, 306, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 308 (1, 309, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))))))
      (.node 352 (1, 353, 0, 0, 1, 1, 111, 0, 0, 0)
        (.node 331 (0, 332, 0, 0, 1, 1, 75, 0, 0, 0)
          (.node 320 (0, 192, 0, 0, 1, 1, 105, 0, 0, 0)
            (.node 315 (1, 316, 0, 0, 1, 1, 111, 0, 0, 0)
              (.node 312 (0, 313, 0, 0, 1, 1, 133, 0, 0, 0)
                (.node 311 (1, 312, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 310 (0, 311, 0, 0, 1, 1, 105, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 314 (0, 315, 1, 0, 1, 1, 163, 0, 0, 0)
                  (.node 313 (1, 314, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 318 (0, 319, 1, 0, 1, 1, 191, 0, 0, 0)
                (.node 317 (1, 318, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 316 (0, 317, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 319 (1, 320, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)))
            (.node 326 (1, 327, 0, 0, 1, 1, 111, 0, 0, 0)
              (.node 323 (0, 324, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 322 (1, 323, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 321 (0, 322, 0, 0, 1, 1, 163, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 325 (0, 326, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 324 (1, 325, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 329 (0, 330, 0, 0, 1, 1, 199, 0, 0, 0)
                (.node 328 (1, 109, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 327 (0, 328, 0, 1, 1, 1, 38, 80, 18, 87743) .leaf .leaf)
                  .leaf)
                (.node 330 (1, 331, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf))))
          (.node 342 (0, 343, 1, 0, 1, 1, 337, 0, 0, 0)
            (.node 337 (0, 338, 0, 0, 1, 1, 75, 0, 0, 0)
              (.node 334 (1, 335, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 333 (0, 334, 1, 0, 1, 1, 163, 0, 0, 0)
                  (.node 332 (1, 333, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 336 (1, 337, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 335 (0, 336, 0, 0, 1, 1, 141, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 340 (0, 341, 1, 0, 1, 1, 279, 0, 0, 0)
                (.node 339 (0, 326, 0, 0, 1, 1, 109, 0, 0, 0)
                  (.node 338 (1, 339, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 341 (1, 342, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)))
            (.node 347 (0, 348, 0, 0, 1, 1, 75, 0, 0, 0)
              (.node 345 (1, 57, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 344 (0, 345, 0, 0, 1, 1, 103, 0, 0, 0)
                  (.node 343 (1, 344, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 346 (0, 345, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf))
              (.node 350 (1, 351, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 349 (0, 350, 0, 0, 1, 1, 163, 0, 0, 0)
                  (.node 348 (1, 349, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 351 (0, 352, 1, 0, 1, 1, 281, 0, 0, 0) .leaf .leaf)))))
        (.node 374 (0, 375, 0, 0, 1, 1, 139, 0, 0, 0)
          (.node 363 (0, 364, 1, 0, 1, 1, 251, 0, 0, 0)
            (.node 358 (1, 359, 0, 0, 1, 1, 111, 0, 0, 0)
              (.node 355 (0, 356, 0, 0, 1, 1, 199, 0, 0, 0)
                (.node 354 (1, 355, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 353 (0, 354, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 357 (0, 358, 0, 1, 1, 1, 90, 174, 38, 92004859743)
                  (.node 356 (1, 357, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 361 (0, 362, 1, 0, 1, 1, 193, 0, 0, 0)
                (.node 360 (1, 361, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 359 (0, 360, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 362 (1, 363, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)))
            (.node 369 (0, 311, 0, 0, 1, 1, 75, 0, 0, 0)
              (.node 366 (1, 367, 0, 0, 1, 1, 111, 0, 0, 0)
                (.node 365 (0, 366, 1, 0, 1, 1, 221, 0, 0, 0)
                  (.node 364 (1, 124, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 368 (1, 369, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 367 (0, 368, 0, 1, 1, 1, 87, 177, 37, 46002429791) .leaf .leaf)
                  .leaf))
              (.node 372 (0, 373, 0, 0, 1, 1, 103, 0, 0, 0)
                (.node 371 (1, 372, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 370 (0, 371, 1, 0, 1, 1, 249, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 373 (1, 374, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf))))
          (.node 385 (1, 386, 0, 0, 1, 1, 111, 0, 0, 0)
            (.node 380 (0, 136, 0, 0, 1, 1, 81, 0, 0, 0)
              (.node 377 (1, 378, 0, 0, 1, 1, 75, 0, 0, 0)
                (.node 376 (0, 377, 0, 1, 1, 1, 83, 151, 33, 3198902111)
                  (.node 375 (1, 376, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 379 (1, 380, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 378 (0, 379, 0, 0, 1, 1, 133, 0, 0, 0) .leaf .leaf)
                  .leaf))
              (.node 383 (0, 276, 0, 0, 1, 1, 191, 0, 0, 0)
                (.node 382 (1, 132, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 381 (0, 382, 0, 0, 1, 1, 81, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 384 (0, 385, 0, 0, 1, 1, 163, 0, 0, 0) .leaf .leaf)))
            (.node 390 (0, 50, 0, 0, 1, 1, 105, 0, 0, 0)
              (.node 388 (0, 389, 1, 0, 1, 1, 167, 0, 0, 0)
                (.node 387 (1, 388, 0, 0, 1, 1, 111, 0, 0, 0)
                  (.node 386 (0, 387, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 389 (1, 390, 0, 0, 1, 1, 111, 0, 0, 0) .leaf .leaf))
              (.node 393 (0, 394, 0, 0, 1, 1, 79, 0, 0, 0)
                (.node 392 (1, 393, 0, 0, 1, 1, 75, 0, 0, 0)
                  (.node 391 (0, 392, 0, 0, 1, 1, 81, 0, 0, 0) .leaf .leaf)
                  .leaf)
                (.node 394 (1, 141, 0, 0, 1, 1, 75, 0, 0, 0) .leaf .leaf)))))))

private abbrev TailRule := ℕ × ℕ × ℕ

private def tailTree : Bst TailRule :=
  .node 400 (0, 401, 141)
    (.node 18 (1, 20, 111)
      (.node 10 (1, 400, 111)
        (.node 6 (1, 395, 111)
          (.node 0 (0, 2, 67) .leaf .leaf)
          (.node 8 (1, 396, 111) .leaf .leaf))
        (.node 13 (1, 404, 111)
          (.node 11 (0, 402, 75) .leaf .leaf)
          (.node 16 (1, 406, 111) .leaf .leaf)))
      (.node 397 (1, 398, 111)
        (.node 91 (1, 411, 75)
          (.node 20 (1, 3, 75) .leaf .leaf)
          (.node 396 (0, 397, 199) .leaf .leaf))
        (.node 399 (1, 9, 111)
          (.node 398 (0, 399, 75) .leaf .leaf)
          .leaf)))
    (.node 408 (0, 409, 75)
      (.node 404 (0, 405, 105)
        (.node 402 (1, 403, 111)
          (.node 401 (1, 11, 111) .leaf .leaf)
          (.node 403 (0, 13, 109) .leaf .leaf))
        (.node 406 (0, 407, 199)
          (.node 405 (1, 17, 111) .leaf .leaf)
          (.node 407 (1, 408, 111) .leaf .leaf)))
      (.node 412 (1, 413, 75)
        (.node 410 (0, 10, 193)
          (.node 409 (1, 410, 111) .leaf .leaf)
          (.node 411 (0, 412, 81) .leaf .leaf))
        (.node 414 (1, 92, 75)
          (.node 413 (0, 414, 79) .leaf .leaf)
          .leaf)))

private inductive CAct where
  | back0 : Bool → ℕ → ℕ → ℕ → ℕ → CAct
  | right : ℕ → ℕ → ℕ → Option (Bool × ℕ × ℕ × ℕ × ℕ) →
      Option (Bool × ℕ × ℕ × ℕ × ℕ) → CAct
  | more : CAct
  | halt : ℕ → CAct

private def csegTree : Bst CAct :=
  .node 643 (.back0 false 0 48 2 103)
    (.node 359 (.back0 false 1 19 6 111)
      (.node 68 (.back0 false 0 12 3 133)
        (.node 24 (.back0 false 0 14 7 75)
          (.node 20 (.back0 false 0 14 3 75)
            (.node 18 (.back0 false 0 14 1 75)
              (.node 17 (.back0 false 0 14 0 75)
                (.node 16 (.more) .leaf .leaf)
                .leaf)
              (.node 19 (.back0 false 0 14 2 75) .leaf .leaf))
            (.node 22 (.back0 false 0 14 5 75)
              (.node 21 (.back0 false 0 14 4 75) .leaf .leaf)
              (.node 23 (.back0 false 0 14 6 75) .leaf .leaf)))
          (.node 64 (.more)
            (.node 27 (.back0 false 0 14 10 75)
              (.node 26 (.back0 false 0 14 9 75)
                (.node 25 (.back0 false 0 14 8 75) .leaf .leaf)
                .leaf)
              (.node 28 (.back0 false 0 14 11 75) .leaf .leaf))
            (.node 66 (.back0 false 0 12 1 133)
              (.node 65 (.back0 false 0 12 0 133) .leaf .leaf)
              (.node 67 (.back0 false 0 12 2 133) .leaf .leaf))))
        (.node 236 (.back0 false 1 4 12 111)
          (.node 73 (.back0 false 0 12 8 133)
            (.node 71 (.back0 false 0 12 6 133)
              (.node 70 (.back0 false 0 12 5 133)
                (.node 69 (.back0 false 0 12 4 133) .leaf .leaf)
                .leaf)
              (.node 72 (.back0 false 0 12 7 133) .leaf .leaf))
            (.node 75 (.back0 false 0 12 10 133)
              (.node 74 (.back0 false 0 12 9 133) .leaf .leaf)
              (.node 76 (.back0 false 0 12 11 133) .leaf .leaf)))
          (.node 354 (.back0 false 1 19 1 111)
            (.node 316 (.right 161 978363480644944044669375672557335484111667983711 371
              (some (false, 0, 21, 12, 803)) (some (true, 0, 21, 12, 823)))
              (.node 308 (.right 65 12348683215628006751 147 (none)
                (some (true, 0, 21, 4, 343)))
                .leaf
                .leaf)
              (.node 353 (.back0 false 1 19 0 111) .leaf .leaf))
            (.node 356 (.back0 false 1 19 3 111)
              (.node 355 (.back0 false 1 19 2 111) .leaf .leaf)
              (.node 358 (.back0 false 1 19 5 111) .leaf .leaf)))))
      (.node 572 (.right 170 501839541786562033184691554359529764704636175250783 398
        (some (true, 1, 36, 12, 844)) (none))
        (.node 428 (.back0 false 0 27 12 133)
          (.node 364 (.back0 false 1 19 11 111)
            (.node 362 (.back0 false 1 19 9 111)
              (.node 361 (.back0 false 1 19 8 111)
                (.node 360 (.back0 false 1 19 7 111) .leaf .leaf)
                .leaf)
              (.node 363 (.back0 false 1 19 10 111) .leaf .leaf))
            (.node 396 (.back0 false 1 25 12 111)
              (.node 380 (.right 169 250461260165646731253657763132329085323815777858911
                395 (some (false, 0, 53, 12, 837)) (some (true, 0, 53, 12, 857)))
                .leaf
                .leaf)
              (.node 412 (.right 157 61356838081364821089426937186034858985753277791 367
                (some (false, 0, 22, 12, 777)) (some (true, 0, 22, 12, 797)))
                .leaf
                .leaf)))
          (.node 504 (.right 112 1934382190648634892325420998718815 272 (none)
            (some (true, 0, 32, 8, 548)))
            (.node 499 (.right 52 1677809098814815 132 (none) (some (true, 0, 32, 3, 248)))
              (.node 492 (.back0 true 1 31 11 115)
                (.node 460 (.right 170
                  500922535143998453961111605624158464079510260544863 398 (none)
                    (some (true, 0, 29, 12, 874)))
                  .leaf
                  .leaf)
                .leaf)
              (.node 501 (.right 76 28148965657581500888415 188 (none)
                (some (true, 0, 32, 5, 368)))
                .leaf
                .leaf))
            (.node 508 (.right 160 544480182062332240827656737844688962651313010015 384
              (some (false, 0, 32, 12, 788)) (some (true, 0, 32, 12, 788)))
              (.node 507 (.right 148 132929731948811582233314633262863516272293215 356
                (none) (some (true, 0, 32, 11, 728)))
                .leaf
                .leaf)
              (.node 540 (.back0 false 0 34 12 133) .leaf .leaf))))
        (.node 630 (.back0 false 1 40 5 75)
          (.node 625 (.back0 false 1 40 0 75)
            (.node 618 (.right 128 126722981576173664659742680423308064095 304
              (none) (some (true, 0, 39, 10, 634)))
              (.node 615 (.right 92 1844062085382373547468780895 220 (none)
                (some (true, 0, 39, 7, 454)))
                (.node 612 (.right 56 26834635142329695 136 (none)
                  (some (true, 0, 39, 4, 274)))
                  .leaf
                  .leaf)
                .leaf)
              (.node 620 (.right 152 2126058834067486025508069453880810825869292895 360
                (some (false, 0, 39, 12, 754)) (some (true, 0, 39, 12, 754)))
                .leaf
                .leaf))
            (.node 627 (.back0 false 1 40 2 75)
              (.node 626 (.back0 false 1 40 1 75) .leaf .leaf)
              (.node 629 (.back0 false 1 40 4 75) .leaf .leaf)))
          (.node 636 (.back0 false 1 40 11 75)
            (.node 632 (.back0 false 1 40 7 75)
              (.node 631 (.back0 false 1 40 6 75) .leaf .leaf)
              (.node 635 (.back0 false 1 40 10 75) .leaf .leaf))
            (.node 641 (.back0 false 0 48 0 103)
              (.node 640 (.more) .leaf .leaf)
              (.node 642 (.back0 false 0 48 1 103) .leaf .leaf))))))
    (.node 1132 (.back0 true 1 40 12 115)
      (.node 679 (.right 112 1933639426625063664160481524184415 272 (none)
        (some (true, 0, 37, 7, 548)))
        (.node 660 (.back0 false 0 51 3 161)
          (.node 656 (.more)
            (.node 649 (.back0 false 0 48 8 103)
              (.node 646 (.back0 false 0 48 5 103)
                (.node 644 (.back0 false 0 48 3 103) .leaf .leaf)
                .leaf)
              (.node 652 (.back0 false 0 48 11 103) .leaf .leaf))
            (.node 658 (.back0 false 0 51 1 161)
              (.node 657 (.back0 false 0 51 0 161) .leaf .leaf)
              (.node 659 (.back0 false 0 51 2 161) .leaf .leaf)))
          (.node 665 (.back0 false 0 51 8 161)
            (.node 663 (.back0 false 0 51 6 161)
              (.node 662 (.back0 false 0 51 5 161)
                (.node 661 (.back0 false 0 51 4 161) .leaf .leaf)
                .leaf)
              (.node 664 (.back0 false 0 51 7 161) .leaf .leaf))
            (.node 675 (.right 64 6869667240838821215 160 (none)
              (some (true, 0, 37, 3, 308)))
              (.node 668 (.back0 false 0 51 11 161) .leaf .leaf)
              (.node 678 (.right 100 472079938140884683632930059615 244 (none)
                (some (true, 0, 37, 6, 488)))
                .leaf
                .leaf))))
        (.node 828 (.back0 false 1 42 12 75)
          (.node 700 (.back0 false 0 44 12 75)
            (.node 684 (.right 172 2229334477111689282501447026630176293937948441048415
              412 (some (false, 0, 37, 12, 848)) (some (true, 0, 37, 12, 848)))
              (.node 682 (.right 148 132878689593773441463795127071748751040574815 356
                (none) (some (true, 0, 37, 10, 728)))
                (.node 681 (.right 136 32441086326604844107371857195251159922015 328
                  (none) (some (true, 0, 37, 9, 668)))
                  .leaf
                  .leaf)
                .leaf)
              (.node 693 (.back0 false 0 44 5 75) .leaf .leaf))
            (.node 764 (.back0 false 0 24 12 75)
              (.node 721 (.back0 false 0 46 0 193) .leaf .leaf)
              (.node 796 (.back0 false 0 50 12 75) .leaf .leaf)))
          (.node 956 (.right 180 570709626349712997376188736408282782449506029682423135
            436 (none) (some (true, 0, 60, 12, 882)))
            (.node 892 (.back0 false 0 56 12 161)
              (.node 860 (.back0 false 1 47 12 111) .leaf .leaf)
              (.node 924 (.back0 false 0 58 12 161) .leaf .leaf))
            (.node 1068 (.back0 false 0 67 11 249)
              (.node 1019 (.right 164 8711696034085951435591746300660618802212461999455
                404 (none) (some (true, 0, 64, 11, 796)))
                .leaf
                .leaf)
              (.node 1100 (.back0 false 0 69 12 75) .leaf .leaf)))))
      (.node 1756 (.right 154 7656643643303080564608927585497604479352436063 350
        (some (true, 1, 38, 11, 776)) (none))
        (.node 1345 (.back0 false 0 85 0 79)
          (.node 1276 (.back0 false 0 80 12 161)
            (.node 1212 (.back0 false 0 76 12 307)
              (.node 1196 (.back0 false 0 96 12 103)
                (.node 1148 (.back0 false 0 72 11 307) .leaf .leaf)
                .leaf)
              (.node 1244 (.back0 false 0 78 12 133) .leaf .leaf))
            (.node 1340 (.back0 false 1 93 12 75)
              (.node 1308 (.back0 false 0 83 12 81) .leaf .leaf)
              (.node 1344 (.more) .leaf .leaf)))
          (.node 1596 (.back0 false 0 100 12 161)
            (.node 1516 (.right 178
              128676332394414663297181244023720442305806294532355423 422
                (some (false, 0, 95, 12, 868)) (none))
              (.node 1410 (.back0 false 0 89 2 79)
                (.node 1388 (.back0 false 0 87 12 79) .leaf .leaf)
                .leaf)
              (.node 1564 (.back0 false 0 98 12 103) .leaf .leaf))
            (.node 1692 (.right 181
              1029410684235840863671924443265284505866638393890698591 439
                (some (false, 0, 106, 12, 879)) (none))
              (.node 1644 (.right 168 139387135728498109470177715845891575829964904592735
                408 (none) (some (true, 0, 101, 12, 822)))
                .leaf
                .leaf)
              (.node 1724 (.back0 false 0 108 12 133) .leaf .leaf))))
        (.node 2060 (.back0 false 0 129 12 161)
          (.node 1888 (.more)
            (.node 1836 (.back0 false 0 115 11 335)
              (.node 1804 (.back0 false 0 113 12 103)
                (.node 1772 (.back0 false 0 111 12 133) .leaf .leaf)
                .leaf)
              (.node 1868 (.back0 false 0 117 12 75) .leaf .leaf))
            (.node 1996 (.back0 true 1 125 12 115)
              (.node 1964 (.right 198
                134465365606074290998527620905569363007288524300851707508063 474
                  (some (false, 0, 123, 12, 962)) (none))
                .leaf
                .leaf)
              (.node 2028 (.back0 false 0 127 12 75) .leaf .leaf)))
          (.node 2172 (.back0 false 0 136 12 79)
            (.node 2124 (.back0 true 0 48 11 119)
              (.node 2092 (.back0 false 0 131 12 79) .leaf .leaf)
              (.node 2140 (.back0 false 0 134 12 161) .leaf .leaf))
            (.node 2236 (.back0 false 0 140 12 79)
              (.node 2204 (.back0 false 0 138 12 133) .leaf .leaf)
              (.node 2268 (.halt 24) .leaf .leaf))))))

private abbrev CTailRule := Bool × ℕ × ℕ × ℕ

private def ctailTree : Bst CTailRule :=
  .node 9 (true, 0, 10, 251)
    (.node 5 (true, 0, 6, 171)
      (.node 3 (true, 0, 20, 55)
        (.node 2 (true, 1, 3, 93) .leaf .leaf)
        .leaf)
      (.node 7 (false, 0, 8, 133) .leaf .leaf))
    (.node 90 (false, 0, 91, 79)
      (.node 17 (true, 0, 18, 113)
        (.node 15 (false, 0, 16, 133) .leaf .leaf)
        .leaf)
      (.node 92 (true, 0, 2, 63) .leaf .leaf))

private def mergeTree : Bst ℕ :=
  .node 327731 (74)
    (.node 32789 (110)
      (.node 8244 (126)
        (.node 8229 (43)
          (.node 8216 (49)
            (.node 8213 (68) .leaf .leaf)
            .leaf)
          (.node 8243 (116) .leaf .leaf))
        (.node 32780 (33)
          (.node 32774 (7)
            (.node 32771 (5) .leaf .leaf)
            .leaf)
          (.node 32781 (15) .leaf .leaf)))
      (.node 32819 (77)
        (.node 32809 (105)
          (.node 32799 (66)
            (.node 32793 (26) .leaf .leaf)
            .leaf)
          (.node 32815 (107) .leaf .leaf))
        (.node 32850 (137)
          (.node 32849 (94) .leaf .leaf)
          (.node 327717 (112) .leaf .leaf))))
    (.node 335946 (75)
      (.node 335919 (133)
        (.node 335896 (79)
          (.node 335876 (128)
            (.node 327753 (97) .leaf .leaf)
            .leaf)
          (.node 335904 (99) .leaf .leaf))
        (.node 335924 (55)
          (.node 335920 (57) .leaf .leaf)
          (.node 335926 (71) .leaf .leaf)))
      (.node 688159 (86)
        (.node 688150 (139)
          (.node 688148 (90)
            (.node 335974 (114) .leaf .leaf)
            .leaf)
          (.node 688153 (130) .leaf .leaf))
        (.node 688169 (88)
          (.node 688168 (135) .leaf .leaf)
          (.node 966737 (122) .leaf .leaf))))

private inductive NatTree where
  | empty : NatTree
  | node : ℕ → NatTree → NatTree → NatTree

private def NatTree.toListAux : NatTree → List ℕ → List ℕ
  | .empty, acc => acc
  | .node x l r, acc => l.toListAux (x :: r.toListAux acc)

private def schedPart0 : NatTree :=
  .node 3877
    (.node 113
      (.node 35
        (.node 14
          (.node 10
            (.node 14
              (.node 2
                (.node 2
                  (.node 1 .empty .empty)
                  .empty)
                (.node 5 .empty .empty))
              (.node 1
                (.node 9 .empty .empty)
                (.node 15 .empty .empty)))
            (.node 1
              (.node 11
                (.node 21 .empty .empty)
                (.node 2 .empty .empty))
              (.node 32
                (.node 1 .empty .empty)
                (.node 8 .empty .empty))))
          (.node 2
            (.node 45
              (.node 15
                (.node 1
                  (.node 9 .empty .empty)
                  .empty)
                (.node 86 .empty .empty))
              (.node 11
                (.node 23 .empty .empty)
                (.node 8 .empty .empty)))
            (.node 2
              (.node 7
                (.node 31 .empty .empty)
                (.node 6 .empty .empty))
              (.node 34
                (.node 5 .empty .empty)
                (.node 69 .empty .empty)))))
        (.node 256
          (.node 110
            (.node 9
              (.node 2
                (.node 8
                  (.node 14 .empty .empty)
                  .empty)
                (.node 1 .empty .empty))
              (.node 453
                (.node 226 .empty .empty)
                (.node 227 .empty .empty)))
            (.node 6
              (.node 26
                (.node 56 .empty .empty)
                (.node 13 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty))))
          (.node 767
            (.node 7
              (.node 47
                (.node 107 .empty .empty)
                (.node 39 .empty .empty))
              (.node 958
                (.node 311 .empty .empty)
                (.node 191 .empty .empty)))
            (.node 125
              (.node 1163
                (.node 2348 .empty .empty)
                (.node 583 .empty .empty))
              (.node 431
                (.node 952 .empty .empty)
                (.node 221 .empty .empty))))))
      (.node 4451
        (.node 4
          (.node 121
            (.node 1958
              (.node 161
                (.node 29
                  (.node 47 .empty .empty)
                  .empty)
                (.node 3921 .empty .empty))
              (.node 491
                (.node 980 .empty .empty)
                (.node 242 .empty .empty)))
            (.node 8
              (.node 30
                (.node 59 .empty .empty)
                (.node 14 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty))))
          (.node 6
            (.node 9
              (.node 2
                (.node 9 .empty .empty)
                (.node 1 .empty .empty))
              (.node 23
                (.node 50 .empty .empty)
                (.node 11 .empty .empty)))
            (.node 16728
              (.node 1
                (.node 2 .empty .empty)
                (.node 8265 .empty .empty))
              (.node 17768
                (.node 7845 .empty .empty)
                (.node 8879 .empty .empty)))))
        (.node 7745
          (.node 11
            (.node 135
              (.node 563
                (.node 1103
                  (.node 2219 .empty .empty)
                  .empty)
                (.node 259 .empty .empty))
              (.node 19
                (.node 83 .empty .empty)
                (.node 27 .empty .empty)))
            (.node 17773
              (.node 71102
                (.node 23 .empty .empty)
                (.node 35553 .empty .empty))
              (.node 31012
                (.node 2273 .empty .empty)
                (.node 15503 .empty .empty))))
          (.node 41
            (.node 479
              (.node 1925
                (.node 3881 .empty .empty)
                (.node 959 .empty .empty))
              (.node 137
                (.node 239 .empty .empty)
                (.node 53 .empty .empty)))
            (.node 62054
              (.node 65
                (.node 5 .empty .empty)
                (.node 124113 .empty .empty))
              (.node 15515
                (.node 31028 .empty .empty)
                (.node 7754 .empty .empty)))))))
    (.node 47603
      (.node 53374
        (.node 3839
          (.node 8
            (.node 119
              (.node 482
                (.node 971
                  (.node 1938 .empty .empty)
                  .empty)
                (.node 241 .empty .empty))
              (.node 30
                (.node 59 .empty .empty)
                (.node 14 .empty .empty)))
            (.node 62986
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty))
              (.node 15551
                (.node 31487 .empty .empty)
                (.node 7679 .empty .empty))))
          (.node 3839
            (.node 191
              (.node 959
                (.node 2111 .empty .empty)
                (.node 575 .empty .empty))
              (.node 15335
                (.node 30599 .empty .empty)
                (.node 7679 .empty .empty)))
            (.node 191
              (.node 959
                (.node 1919 .empty .empty)
                (.node 431 .empty .empty))
              (.node 47
                (.node 143 .empty .empty)
                (.node 6281 .empty .empty)))))
        (.node 6335
          (.node 363836
            (.node 10079
              (.node 4991
                (.node 12839
                  (.node 27095 .empty .empty)
                  .empty)
                (.node 16894 .empty .empty))
              (.node 182014
                (.node 2207 .empty .empty)
                (.node 96 .empty .empty)))
            (.node 101375
              (.node 405496
                (.node 161089 .empty .empty)
                (.node 202751 .empty .empty))
              (.node 25343
                (.node 50687 .empty .empty)
                (.node 12671 .empty .empty))))
          (.node 29
            (.node 383
              (.node 1565
                (.node 3119 .empty .empty)
                (.node 767 .empty .empty))
              (.node 113
                (.node 191 .empty .empty)
                (.node 47 .empty .empty)))
            (.node 761663
              (.node 761662
                (.node 161 .empty .empty)
                (.node 1523325 .empty .empty))
              (.node 190415
                (.node 380831 .empty .empty)
                (.node 95207 .empty .empty))))))
      (.node 24575
        (.node 49151
          (.node 92
            (.node 1487
              (.node 5951
                (.node 11900
                  (.node 23798 .empty .empty)
                  .empty)
                (.node 2975 .empty .empty))
              (.node 371
                (.node 743 .empty .empty)
                (.node 182 .empty .empty)))
            (.node 2
              (.node 23
                (.node 47 .empty .empty)
                (.node 11 .empty .empty))
              (.node 9
                (.node 1 .empty .empty)
                (.node 203506 .empty .empty))))
          (.node 4607
            (.node 73277
              (.node 293375
                (.node 586817 .empty .empty)
                (.node 146687 .empty .empty))
              (.node 18431
                (.node 36737 .empty .empty)
                (.node 9215 .empty .empty)))
            (.node 125
              (.node 893
                (.node 2303 .empty .empty)
                (.node 641 .empty .empty))
              (.node 595967
                (.node 2601983 .empty .empty)
                (.node 92159 .empty .empty)))))
        (.node 1
          (.node 767
            (.node 12287
              (.node 49149
                (.node 24574
                  (.node 18430 .empty .empty)
                  .empty)
                (.node 24575 .empty .empty))
              (.node 3071
                (.node 6143 .empty .empty)
                (.node 1535 .empty .empty)))
            (.node 47
              (.node 191
                (.node 383 .empty .empty)
                (.node 95 .empty .empty))
              (.node 11
                (.node 23 .empty .empty)
                (.node 2 .empty .empty))))
          (.node 767
            (.node 12287
              (.node 49124
                (.node 9 .empty .empty)
                (.node 24575 .empty .empty))
              (.node 3071
                (.node 6143 .empty .empty)
                (.node 1535 .empty .empty)))
            (.node 47
              (.node 191
                (.node 383 .empty .empty)
                (.node 95 .empty .empty))
              (.node 147489
                (.node 7 .empty .empty)
                (.node 73746 .empty .empty)))))))

private def schedPart1 : NatTree :=
  .node 48383
    (.node 3092
      (.node 1
        (.node 122828
          (.node 143
            (.node 2303
              (.node 9217
                (.node 18434
                  (.node 36875 .empty .empty)
                  .empty)
                (.node 4607 .empty .empty))
              (.node 575
                (.node 1151 .empty .empty)
                (.node 287 .empty .empty)))
            (.node 11
              (.node 35
                (.node 71 .empty .empty)
                (.node 18 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 7 .empty .empty))))
          (.node 959
            (.node 15349
              (.node 61415
                (.node 122829
                  (.node 245654 .empty .empty)
                  .empty)
                (.node 30707 .empty .empty))
              (.node 3839
                (.node 7677 .empty .empty)
                (.node 1919 .empty .empty)))
            (.node 59
              (.node 239
                (.node 479 .empty .empty)
                (.node 119 .empty .empty))
              (.node 11
                (.node 25 .empty .empty)
                (.node 9 .empty .empty)))))
        (.node 98
          (.node 6
            (.node 97
              (.node 393
                (.node 196
                  (.node 15 .empty .empty)
                  .empty)
                (.node 194 .empty .empty))
              (.node 23
                (.node 47 .empty .empty)
                (.node 11 .empty .empty)))
            (.node 1586
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty))
              (.node 395
                (.node 791 .empty .empty)
                (.node 198 .empty .empty))))
          (.node 790812
            (.node 6
              (.node 23
                (.node 49 .empty .empty)
                (.node 11 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 392235 .empty .empty)))
            (.node 49420
              (.node 197702
                (.node 395408 .empty .empty)
                (.node 98852 .empty .empty))
              (.node 12352
                (.node 24714 .empty .empty)
                (.node 6177 .empty .empty))))))
      (.node 15
        (.node 146353
          (.node 8
            (.node 95
              (.node 386
                (.node 774
                  (.node 1540 .empty .empty)
                  .empty)
                (.node 191 .empty .empty))
              (.node 23
                (.node 47 .empty .empty)
                (.node 11 .empty .empty)))
            (.node 2341718
              (.node 5
                (.node 2 .empty .empty)
                (.node 1170860 .empty .empty))
              (.node 585431
                (.node 1170861 .empty .empty)
                (.node 292715 .empty .empty))))
          (.node 573
            (.node 9145
              (.node 36587
                (.node 73175 .empty .empty)
                (.node 18297 .empty .empty))
              (.node 2289
                (.node 4571 .empty .empty)
                (.node 1141 .empty .empty)))
            (.node 35
              (.node 143
                (.node 287 .empty .empty)
                (.node 71 .empty .empty))
              (.node 9
                (.node 13 .empty .empty)
                (.node 1 .empty .empty)))))
        (.node 193
          (.node 49703
            (.node 795215
              (.node 3180866
                (.node 6361737
                  (.node 3180868 .empty .empty)
                  .empty)
                (.node 1590433 .empty .empty))
              (.node 198803
                (.node 397607 .empty .empty)
                (.node 99402 .empty .empty)))
            (.node 3107
              (.node 12422
                (.node 24851 .empty .empty)
                (.node 6212 .empty .empty))
              (.node 776
                (.node 1550 .empty .empty)
                (.node 386 .empty .empty))))
          (.node 9
            (.node 11
              (.node 47
                (.node 95 .empty .empty)
                (.node 23 .empty .empty))
              (.node 2
                (.node 6 .empty .empty)
                (.node 1 .empty .empty)))
            (.node 773471
              (.node 3095039
                (.node 6190066 .empty .empty)
                (.node 1547519 .empty .empty))
              (.node 193535
                (.node 386975 .empty .empty)
                (.node 96767 .empty .empty)))))))
    (.node 47
      (.node 1974623
        (.node 25343
          (.node 6482501
            (.node 1535
              (.node 6143
                (.node 12191
                  (.node 23903 .empty .empty)
                  .empty)
                (.node 3071 .empty .empty))
              (.node 95
                (.node 767 .empty .empty)
                (.node 12965105 .empty .empty)))
            (.node 405119
              (.node 1620671
                (.node 3241337 .empty .empty)
                (.node 810245 .empty .empty))
              (.node 101369
                (.node 202559 .empty .empty)
                (.node 50687 .empty .empty))))
          (.node 185
            (.node 1535
              (.node 6335
                (.node 12671 .empty .empty)
                (.node 3077 .empty .empty))
              (.node 383
                (.node 767 .empty .empty)
                (.node 191 .empty .empty)))
            (.node 1555775
              (.node 4361
                (.node 5 .empty .empty)
                (.node 9454270 .empty .empty))
              (.node 7898207
                (.node 15796990 .empty .empty)
                (.node 3948191 .empty .empty)))))
        (.node 6190079
          (.node 14975
            (.node 273406
              (.node 246431
                (.node 493919
                  (.node 986783 .empty .empty)
                  .empty)
                (.node 112127 .empty .empty))
              (.node 64127
                (.node 135551 .empty .empty)
                (.node 34175 .empty .empty)))
            (.node 138241
              (.node 2687
                (.node 9599 .empty .empty)
                (.node 24898557 .empty .empty))
              (.node 24760319
                (.node 49520632 .empty .empty)
                (.node 12380159 .empty .empty))))
          (.node 24191
            (.node 386879
              (.node 1547519
                (.node 3095039 .empty .empty)
                (.node 773759 .empty .empty))
              (.node 96719
                (.node 193391 .empty .empty)
                (.node 48383 .empty .empty)))
            (.node 1535
              (.node 5999
                (.node 12095 .empty .empty)
                (.node 3023 .empty .empty))
              (.node 383
                (.node 767 .empty .empty)
                (.node 191 .empty .empty))))))
      (.node 101375
        (.node 391
          (.node 101375
            (.node 1621995
              (.node 6487960
                (.node 161
                  (.node 29 .empty .empty)
                  .empty)
                (.node 3243983 .empty .empty))
              (.node 405503
                (.node 811007 .empty .empty)
                (.node 202751 .empty .empty)))
            (.node 6335
              (.node 25343
                (.node 50687 .empty .empty)
                (.node 12671 .empty .empty))
              (.node 1583
                (.node 3167 .empty .empty)
                (.node 779 .empty .empty))))
          (.node 25951934
            (.node 27
              (.node 95
                (.node 191 .empty .empty)
                (.node 47 .empty .empty))
              (.node 7
                (.node 11 .empty .empty)
                (.node 39 .empty .empty)))
            (.node 1621993
              (.node 6487981
                (.node 12975969 .empty .empty)
                (.node 3243993 .empty .empty))
              (.node 405501
                (.node 810995 .empty .empty)
                (.node 202751 .empty .empty)))))
        (.node 12239332
          (.node 193
            (.node 3167
              (.node 12671
                (.node 25343
                  (.node 50687 .empty .empty)
                  .empty)
                (.node 6335 .empty .empty))
              (.node 791
                (.node 1583 .empty .empty)
                (.node 395 .empty .empty)))
            (.node 11
              (.node 47
                (.node 95 .empty .empty)
                (.node 23 .empty .empty))
              (.node 1
                (.node 9 .empty .empty)
                (.node 15 .empty .empty))))
          (.node 191240
            (.node 3059831
              (.node 12239330
                (.node 24478665 .empty .empty)
                (.node 6119665 .empty .empty))
              (.node 764958
                (.node 1529915 .empty .empty)
                (.node 382478 .empty .empty)))
            (.node 11951
              (.node 47809
                (.node 95618 .empty .empty)
                (.node 23903 .empty .empty))
              (.node 2987
                (.node 5975 .empty .empty)
                (.node 1494 .empty .empty)))))))

private def schedPart2 : NatTree :=
  .node 423558671
    (.node 532575167
      (.node 11
        (.node 1529915
          (.node 1
            (.node 47
              (.node 186
                (.node 373
                  (.node 746 .empty .empty)
                  .empty)
                (.node 95 .empty .empty))
              (.node 11
                (.node 23 .empty .empty)
                (.node 2 .empty .empty)))
            (.node 24478667
              (.node 97914674
                (.node 9 .empty .empty)
                (.node 48957335 .empty .empty))
              (.node 6119666
                (.node 12239334 .empty .empty)
                (.node 3059833 .empty .empty))))
          (.node 2987
            (.node 47809
              (.node 191240
                (.node 382478
                  (.node 764958 .empty .empty)
                  .empty)
                (.node 95618 .empty .empty))
              (.node 11951
                (.node 23903 .empty .empty)
                (.node 5975 .empty .empty)))
            (.node 186
              (.node 746
                (.node 1494 .empty .empty)
                (.node 373 .empty .empty))
              (.node 47
                (.node 95 .empty .empty)
                (.node 23 .empty .empty)))))
        (.node 16979
          (.node 4346687
            (.node 69547083
              (.node 64632459
                (.node 1
                  (.node 2 .empty .empty)
                  .empty)
                (.node 139094152 .empty .empty))
              (.node 17386763
                (.node 34773551 .empty .empty)
                (.node 8693383 .empty .empty)))
            (.node 271679
              (.node 1086671
                (.node 2173343 .empty .empty)
                (.node 543339 .empty .empty))
              (.node 67919
                (.node 135839 .empty .empty)
                (.node 33947 .empty .empty))))
          (.node 59
            (.node 1055
              (.node 4235
                (.node 8495 .empty .empty)
                (.node 2119 .empty .empty))
              (.node 267
                (.node 527 .empty .empty)
                (.node 143 .empty .empty)))
            (.node 31116245
              (.node 11
                (.node 35 .empty .empty)
                (.node 7 .empty .empty))
              (.node 86033952
                (.node 618609117 .empty .empty)
                (.node 1065150332 .empty .empty))))))
      (.node 58517378
        (.node 28607
          (.node 7314653
            (.node 117034751
              (.node 16109041
                (.node 133143791
                  (.node 266287583 .empty .empty)
                  .empty)
                (.node 234069496 .empty .empty))
              (.node 29258687
                (.node 58517375 .empty .empty)
                (.node 14629295 .empty .empty)))
            (.node 457151
              (.node 1828655
                (.node 3657329 .empty .empty)
                (.node 914333 .empty .empty))
              (.node 114287
                (.node 228593 .empty .empty)
                (.node 57167 .empty .empty))))
          (.node 113
            (.node 1775
              (.node 7133
                (.node 14255 .empty .empty)
                (.node 3569 .empty .empty))
              (.node 431
                (.node 911 .empty .empty)
                (.node 221 .empty .empty)))
            (.node 936278097
              (.node 29
                (.node 47 .empty .empty)
                (.node 161 .empty .empty))
              (.node 234069524
                (.node 468139046 .empty .empty)
                (.node 117034763 .empty .empty)))))
        (.node 445
          (.node 114290
            (.node 1828667
              (.node 7314671
                (.node 14629343
                  (.node 29258689 .empty .empty)
                  .empty)
                (.node 3657335 .empty .empty))
              (.node 457166
                (.node 914334 .empty .empty)
                (.node 228584 .empty .empty)))
            (.node 7142
              (.node 28571
                (.node 57145 .empty .empty)
                (.node 14286 .empty .empty))
              (.node 1787
                (.node 3572 .empty .empty)
                (.node 890 .empty .empty))))
          (.node 1
            (.node 26
              (.node 110
                (.node 222 .empty .empty)
                (.node 56 .empty .empty))
              (.node 6
                (.node 13 .empty .empty)
                (.node 2 .empty .empty)))
            (.node 6776938552
              (.node 3745112402
                (.node 9 .empty .empty)
                (.node 356643121 .empty .empty))
              (.node 1694234639
                (.node 3388469279 .empty .empty)
                (.node 847117323 .empty .empty)))))))
    (.node 36731
      (.node 12887231
        (.node 3227
          (.node 827267
            (.node 13236203
              (.node 52944827
                (.node 105889667
                  (.node 211779323 .empty .empty)
                  .empty)
                (.node 26472419 .empty .empty))
              (.node 3309051
                (.node 6618103 .empty .empty)
                (.node 1654523 .empty .empty)))
            (.node 51703
              (.node 206819
                (.node 413627 .empty .empty)
                (.node 103403 .empty .empty))
              (.node 12923
                (.node 25851 .empty .empty)
                (.node 6467 .empty .empty))))
          (.node 11
            (.node 199
              (.node 815
                (.node 1619 .empty .empty)
                (.node 395 .empty .empty))
              (.node 47
                (.node 95 .empty .empty)
                (.node 27 .empty .empty)))
            (.node 206195553
              (.node 824782335
                (.node 7 .empty .empty)
                (.node 412391197 .empty .empty))
              (.node 51548927
                (.node 103097821 .empty .empty)
                (.node 25774463 .empty .empty)))))
        (.node 157
          (.node 25151
            (.node 402781
              (.node 1610879
                (.node 3221759
                  (.node 6443553 .empty .empty)
                  .empty)
                (.node 805439 .empty .empty))
              (.node 100641
                (.node 201407 .empty .empty)
                (.node 50303 .empty .empty)))
            (.node 1535
              (.node 6335
                (.node 12637 .empty .empty)
                (.node 3105 .empty .empty))
              (.node 383
                (.node 767 .empty .empty)
                (.node 191 .empty .empty))))
          (.node 9402971
            (.node 150447546
              (.node 601790187
                (.node 33 .empty .empty)
                (.node 300895093 .empty .empty))
              (.node 37611887
                (.node 75223775 .empty .empty)
                (.node 18805943 .empty .empty)))
            (.node 587687
              (.node 2350741
                (.node 4701482 .empty .empty)
                (.node 1175370 .empty .empty))
              (.node 146918
                (.node 293843 .empty .empty)
                (.node 73460 .empty .empty))))))
      (.node 10847
        (.node 710967561
          (.node 71
            (.node 1148
              (.node 4590
                (.node 9181
                  (.node 18362 .empty .empty)
                  .empty)
                (.node 2294 .empty .empty))
              (.node 287
                (.node 575 .empty .empty)
                (.node 143 .empty .empty)))
            (.node 2
              (.node 14
                (.node 35 .empty .empty)
                (.node 8 .empty .empty))
              (.node 9
                (.node 1 .empty .empty)
                (.node 355483780 .empty .empty))))
          (.node 2777219
            (.node 44435471
              (.node 177741889
                (.node 355483778 .empty .empty)
                (.node 88870943 .empty .empty))
              (.node 11108867
                (.node 22217735 .empty .empty)
                (.node 5554434 .empty .empty)))
            (.node 173576
              (.node 694304
                (.node 1388606 .empty .empty)
                (.node 347150 .empty .empty))
              (.node 43393
                (.node 86786 .empty .empty)
                (.node 21695 .empty .empty)))))
        (.node 355483782
          (.node 23
            (.node 338
              (.node 1355
                (.node 2711
                  (.node 5423 .empty .empty)
                  .empty)
                (.node 678 .empty .empty))
              (.node 83
                (.node 169 .empty .empty)
                (.node 42 .empty .empty)))
            (.node 9
              (.node 2
                (.node 11 .empty .empty)
                (.node 1 .empty .empty))
              (.node 1421935127
                (.node 2843870258 .empty .empty)
                (.node 710967563 .empty .empty))))
          (.node 1388606
            (.node 22217735
              (.node 88870945
                (.node 177741890 .empty .empty)
                (.node 44435471 .empty .empty))
              (.node 5554434
                (.node 11108867 .empty .empty)
                (.node 2777219 .empty .empty)))
            (.node 86786
              (.node 347150
                (.node 694304 .empty .empty)
                (.node 173576 .empty .empty))
              (.node 21695
                (.node 43393 .empty .empty)
                (.node 10847 .empty .empty)))))))

private def schedPart3 : NatTree :=
  .node 5759
    (.node 47
      (.node 767
        (.node 111598205
          (.node 23
            (.node 338
              (.node 1355
                (.node 2711
                  (.node 5423 .empty .empty)
                  .empty)
                (.node 678 .empty .empty))
              (.node 83
                (.node 169 .empty .empty)
                (.node 42 .empty .empty)))
            (.node 235847019
              (.node 2
                (.node 11 .empty .empty)
                (.node 1 .empty .empty))
              (.node 446393087
                (.node 892786462 .empty .empty)
                (.node 223196801 .empty .empty))))
          (.node 218111
            (.node 3487487
              (.node 13949951
                (.node 27899777
                  (.node 55799039 .empty .empty)
                  .empty)
                (.node 6974975 .empty .empty))
              (.node 871679
                (.node 1743485 .empty .empty)
                (.node 436097 .empty .empty)))
            (.node 13697
              (.node 54527
                (.node 109055 .empty .empty)
                (.node 27005 .empty .empty))
              (.node 3197
                (.node 6911 .empty .empty)
                (.node 1535 .empty .empty)))))
        (.node 2427167
          (.node 621354755
            (.node 1085728308
              (.node 1025
                (.node 125
                  (.node 641 .empty .empty)
                  .empty)
                (.node 3571147329 .empty .empty))
              (.node 2485419023
                (.node 4970838044 .empty .empty)
                (.node 1242709499 .empty .empty)))
            (.node 38834675
              (.node 155338691
                (.node 310677371 .empty .empty)
                (.node 77669339 .empty .empty))
              (.node 9708671
                (.node 19417343 .empty .empty)
                (.node 4854335 .empty .empty))))
          (.node 9483
            (.node 151691
              (.node 606779
                (.node 1213583 .empty .empty)
                (.node 303395 .empty .empty))
              (.node 37919
                (.node 75847 .empty .empty)
                (.node 18959 .empty .empty)))
            (.node 587
              (.node 2363
                (.node 4751 .empty .empty)
                (.node 1187 .empty .empty))
              (.node 143
                (.node 295 .empty .empty)
                (.node 75 .empty .empty))))))
      (.node 644874239
        (.node 933887
          (.node 240840191
            (.node 3853221887
              (.node 39
                (.node 7
                  (.node 11 .empty .empty)
                  .empty)
                (.node 7706458510 .empty .empty))
              (.node 963325439
                (.node 1926610943 .empty .empty)
                (.node 481645055 .empty .empty)))
            (.node 15040511
              (.node 60211199
                (.node 120422399 .empty .empty)
                (.node 30085631 .empty .empty))
              (.node 3780095
                (.node 7520255 .empty .empty)
                (.node 1872383 .empty .empty))))
          (.node 21281931262
            (.node 49151
              (.node 245759
                (.node 486911 .empty .empty)
                (.node 102911 .empty .empty))
              (.node 4607
                (.node 44543 .empty .empty)
                (.node 4935745535 .empty .empty)))
            (.node 10354556927
              (.node 288620543
                (.node 10641702911 .empty .empty)
                (.node 20703215614 .empty .empty))
              (.node 2588934143
                (.node 5174722559 .empty .empty)
                (.node 1296039935 .empty .empty)))))
        (.node 348561407
          (.node 89231825278
            (.node 22020095
              (.node 78643199
                (.node 163577855
                  (.node 324009983 .empty .empty)
                  .empty)
                (.node 37748735 .empty .empty))
              (.node 3145727
                (.node 12582911 .empty .empty)
                (.node 15445524479 .empty .empty)))
            (.node 5576988671
              (.node 22307955839
                (.node 44615912447 .empty .empty)
                (.node 11153977343 .empty .empty))
              (.node 1394248319
                (.node 2788494335 .empty .empty)
                (.node 697123199 .empty .empty))))
          (.node 1360895
            (.node 21786239
              (.node 87140351
                (.node 174280703 .empty .empty)
                (.node 43570175 .empty .empty))
              (.node 5446655
                (.node 10893311 .empty .empty)
                (.node 2722175 .empty .empty)))
            (.node 85631
              (.node 340991
                (.node 681599 .empty .empty)
                (.node 169343 .empty .empty))
              (.node 21503
                (.node 43007 .empty .empty)
                (.node 9599 .empty .empty)))))))
    (.node 9086
      (.node 959
        (.node 63442319
          (.node 16241232383
            (.node 31942044673
              (.node 481250303
                (.node 383
                  (.node 3071 .empty .empty)
                  .empty)
                (.node 96906974204 .empty .empty))
              (.node 64964929535
                (.node 129929859064 .empty .empty)
                (.node 32482464767 .empty .empty)))
            (.node 1015076975
              (.node 4060308095
                (.node 8120616191 .empty .empty)
                (.node 2030154047 .empty .empty))
              (.node 253769279
                (.node 507538511 .empty .empty)
                (.node 126884591 .empty .empty))))
          (.node 247823
            (.node 3965183
              (.node 15860573
                (.node 31721135 .empty .empty)
                (.node 7930289 .empty .empty))
              (.node 991295
                (.node 1982591 .empty .empty)
                (.node 495599 .empty .empty)))
            (.node 15503
              (.node 61967
                (.node 123887 .empty .empty)
                (.node 30959 .empty .empty))
              (.node 3869
                (.node 7727 .empty .empty)
                (.node 1919 .empty .empty)))))
        (.node 595535711
          (.node 152457142079
            (.node 29
              (.node 143
                (.node 239
                  (.node 497 .empty .empty)
                  .empty)
                (.node 47 .empty .empty))
              (.node 152457142078
                (.node 161 .empty .empty)
                (.node 304914284157 .empty .empty)))
            (.node 9528571379
              (.node 38114285519
                (.node 76228571039 .empty .empty)
                (.node 19057142759 .empty .empty))
              (.node 2382142844
                (.node 4764285686 .empty .empty)
                (.node 1191071423 .empty .empty))))
          (.node 2326310
            (.node 37220978
              (.node 148883927
                (.node 297767855 .empty .empty)
                (.node 74441963 .empty .empty))
              (.node 9305243
                (.node 18610489 .empty .empty)
                (.node 4652622 .empty .empty)))
            (.node 145393
              (.node 581579
                (.node 1163156 .empty .empty)
                (.node 290786 .empty .empty))
              (.node 36347
                (.node 72695 .empty .empty)
                (.node 18174 .empty .empty))))))
      (.node 9944139
        (.node 141989465455
          (.node 14
            (.node 284
              (.node 1136
                (.node 2270
                  (.node 4544 .empty .empty)
                  .empty)
                (.node 566 .empty .empty))
              (.node 71
                (.node 143 .empty .empty)
                (.node 35 .empty .empty)))
            (.node 9
              (.node 2
                (.node 8 .empty .empty)
                (.node 1 .empty .empty))
              (.node 609828568319
                (.node 1219657136642 .empty .empty)
                (.node 304914284159 .empty .empty))))
          (.node 2545700303
            (.node 40731204671
              (.node 162924818699
                (.node 325849637420 .empty .empty)
                (.node 81462409351 .empty .empty))
              (.node 10182801167
                (.node 20365602335 .empty .empty)
                (.node 5091400587 .empty .empty)))
            (.node 159106271
              (.node 636425075
                (.node 1272850139 .empty .empty)
                (.node 318212543 .empty .empty))
              (.node 39776555
                (.node 79553135 .empty .empty)
                (.node 19888279 .empty .empty)))))
        (.node 75
          (.node 19427
            (.node 310751
              (.node 1243015
                (.node 2486027
                  (.node 4972079 .empty .empty)
                  .empty)
                (.node 621503 .empty .empty))
              (.node 77691
                (.node 155375 .empty .empty)
                (.node 38843 .empty .empty)))
            (.node 1211
              (.node 4855
                (.node 9707 .empty .empty)
                (.node 2427 .empty .empty))
              (.node 299
                (.node 611 .empty .empty)
                (.node 151 .empty .empty))))
          (.node 6855751679
            (.node 109692027015
              (.node 11
                (.node 47 .empty .empty)
                (.node 7 .empty .empty))
              (.node 27423006719
                (.node 54846013439 .empty .empty)
                (.node 13711503359 .empty .empty)))
            (.node 428485247
              (.node 1713939071
                (.node 3427875839 .empty .empty)
                (.node 856968575 .empty .empty))
              (.node 107120639
                (.node 214241663 .empty .empty)
                (.node 53560319 .empty .empty)))))))

private def schedPart4 : NatTree :=
  .node 13119339205
    (.node 2111015
      (.node 801983
        (.node 105113126773
          (.node 104447
            (.node 1674239
              (.node 6694271
                (.node 13390847
                  (.node 26781311 .empty .empty)
                  .empty)
                (.node 3348095 .empty .empty))
              (.node 417791
                (.node 835967 .empty .empty)
                (.node 208895 .empty .empty)))
            (.node 6143
              (.node 27263
                (.node 52223 .empty .empty)
                (.node 12671 .empty .empty))
              (.node 2687
                (.node 3071 .empty .empty)
                (.node 383 .empty .empty))))
          (.node 205299071
            (.node 3284785199
              (.node 13139140833
                (.node 26278281647
                  (.node 52556563391 .empty .empty)
                  .empty)
                (.node 6569570413 .empty .empty))
              (.node 821196287
                (.node 1642392609 .empty .empty)
                (.node 410598143 .empty .empty)))
            (.node 12831201
              (.node 51324781
                (.node 102649535 .empty .empty)
                (.node 25662383 .empty .empty))
              (.node 3207791
                (.node 6415597 .empty .empty)
                (.node 1603919 .empty .empty)))))
        (.node 138347547142
          (.node 1569
            (.node 25069
              (.node 100223
                (.node 200481
                  (.node 400943 .empty .empty)
                  .empty)
                (.node 50111 .empty .empty))
              (.node 6287
                (.node 12527 .empty .empty)
                (.node 3119 .empty .empty)))
            (.node 109
              (.node 383
                (.node 767 .empty .empty)
                (.node 191 .empty .empty))
              (.node 33
                (.node 47 .empty .empty)
                (.node 157 .empty .empty))))
          (.node 540420095
            (.node 8646721607
              (.node 34586886767
                (.node 69173773583 .empty .empty)
                (.node 17293443407 .empty .empty))
              (.node 2161680431
                (.node 4323360887 .empty .empty)
                (.node 1080840191 .empty .empty)))
            (.node 33776255
              (.node 135105023
                (.node 270210047 .empty .empty)
                (.node 67552511 .empty .empty))
              (.node 8444111
                (.node 16888127 .empty .empty)
                (.node 4221959 .empty .empty))))))
      (.node 30887930
        (.node 2024271617530
          (.node 4175
            (.node 65999
              (.node 263927
                (.node 527687
                  (.node 1055567 .empty .empty)
                  .empty)
                (.node 131951 .empty .empty))
              (.node 16487
                (.node 32903 .empty .empty)
                (.node 8255 .empty .empty)))
            (.node 311
              (.node 1079
                (.node 1991 .empty .empty)
                (.node 455 .empty .empty))
              (.node 119
                (.node 71 .empty .empty)
                (.node 47 .empty .empty))))
          (.node 7907311007
            (.node 126516976094
              (.node 506067904381
                (.node 1012135808762 .empty .empty)
                (.node 253033952190 .empty .empty))
              (.node 31629244022
                (.node 63258488048 .empty .empty)
                (.node 15814622012 .empty .empty)))
            (.node 494206934
              (.node 1976827751
                (.node 3953655503 .empty .empty)
                (.node 988413875 .empty .empty))
              (.node 123551735
                (.node 247103468 .empty .empty)
                (.node 61775867 .empty .empty)))))
        (.node 236
          (.node 60326
            (.node 965246
              (.node 3860990
                (.node 7721982
                  (.node 15443965 .empty .empty)
                  .empty)
                (.node 1930496 .empty .empty))
              (.node 241310
                (.node 482624 .empty .empty)
                (.node 120656 .empty .empty)))
            (.node 3769
              (.node 15083
                (.node 30164 .empty .empty)
                (.node 7538 .empty .empty))
              (.node 942
                (.node 1883 .empty .empty)
                (.node 470 .empty .empty))))
          (.node 9
            (.node 13
              (.node 59
                (.node 119 .empty .empty)
                (.node 26 .empty .empty))
              (.node 2
                (.node 6 .empty .empty)
                (.node 1 .empty .empty)))
            (.node 209909427309
              (.node 329
                (.node 1396555112362 .empty .empty)
                (.node 104954713654 .empty .empty))
              (.node 52477356827
                (.node 104954713655 .empty .empty)
                (.node 26238678410 .empty .empty)))))))
    (.node 25
      (.node 7
        (.node 457883
          (.node 117218651
            (.node 1875498539
              (.node 7501994207
                (.node 15003988412
                  (.node 5617345003 .empty .empty)
                  .empty)
                (.node 3750997103 .empty .empty))
              (.node 468874635
                (.node 937749271 .empty .empty)
                (.node 234437327 .empty .empty)))
            (.node 7326155
              (.node 29304671
                (.node 58609331 .empty .empty)
                (.node 14652335 .empty .empty))
              (.node 1831535
                (.node 3663079 .empty .empty)
                (.node 915771 .empty .empty))))
          (.node 1787
            (.node 28615
              (.node 114479
                (.node 228947 .empty .empty)
                (.node 57227 .empty .empty))
              (.node 7151
                (.node 14303 .empty .empty)
                (.node 3579 .empty .empty)))
            (.node 107
              (.node 443
                (.node 899 .empty .empty)
                (.node 227 .empty .empty))
              (.node 27
                (.node 55 .empty .empty)
                (.node 11 .empty .empty)))))
        (.node 1831537
          (.node 468874641
            (.node 7501994207
              (.node 30007976841
                (.node 60015953678
                  (.node 39 .empty .empty)
                  .empty)
                (.node 15003988417 .empty .empty))
              (.node 1875498551
                (.node 3750997103 .empty .empty)
                (.node 937749275 .empty .empty)))
            (.node 29304661
              (.node 117218661
                (.node 234437317 .empty .empty)
                (.node 58609331 .empty .empty))
              (.node 7326167
                (.node 14652333 .empty .empty)
                (.node 3663083 .empty .empty))))
          (.node 7151
            (.node 114469
              (.node 457883
                (.node 915767 .empty .empty)
                (.node 228945 .empty .empty))
              (.node 28619
                (.node 57237 .empty .empty)
                (.node 14305 .empty .empty)))
            (.node 445
              (.node 1787
                (.node 3575 .empty .empty)
                (.node 897 .empty .empty))
              (.node 109
                (.node 225 .empty .empty)
                (.node 57 .empty .empty))))))
      (.node 896
        (.node 58609324
          (.node 15003988424
            (.node 240063814742
              (.node 1
                (.node 9
                  (.node 11 .empty .empty)
                  .empty)
                (.node 15 .empty .empty))
              (.node 60015953687
                (.node 120031907373 .empty .empty)
                (.node 30007976843 .empty .empty)))
            (.node 937749275
              (.node 3750997103
                (.node 7501994210 .empty .empty)
                (.node 1875498551 .empty .empty))
              (.node 234437318
                (.node 468874640 .empty .empty)
                (.node 117218660 .empty .empty))))
          (.node 228944
            (.node 3663083
              (.node 14652328
                (.node 29304666 .empty .empty)
                (.node 7326165 .empty .empty))
              (.node 915770
                (.node 1831544 .empty .empty)
                (.node 457883 .empty .empty)))
            (.node 14310
              (.node 57236
                (.node 114470 .empty .empty)
                (.node 28612 .empty .empty))
              (.node 3575
                (.node 7154 .empty .empty)
                (.node 1787 .empty .empty)))))
        (.node 97452719423
          (.node 564012627317
            (.node 26
              (.node 110
                (.node 224
                  (.node 446 .empty .empty)
                  .empty)
                (.node 56 .empty .empty))
              (.node 8
                (.node 11 .empty .empty)
                (.node 2 .empty .empty)))
            (.node 1559243511023
              (.node 251170395529
                (.node 1810413906548 .empty .empty)
                (.node 3118487022040 .empty .empty))
              (.node 389810877743
                (.node 779621755535 .empty .empty)
                (.node 194905438847 .empty .empty))))
          (.node 380674703
            (.node 6090795023
              (.node 24363179789
                (.node 48726359759 .empty .empty)
                (.node 12181589921 .empty .empty))
              (.node 1522698767
                (.node 3045397487 .empty .empty)
                (.node 761349359 .empty .empty)))
            (.node 23792207
              (.node 95168639
                (.node 190337327 .empty .empty)
                (.node 47584319 .empty .empty))
              (.node 5948081
                (.node 11896013 .empty .empty)
                (.node 2973965 .empty .empty)))))))

private def schedPart5 : NatTree :=
  .node 11
    (.node 1668513215
      (.node 58573583
        (.node 90023930879
          (.node 5807
            (.node 92927
              (.node 371759
                (.node 743567
                  (.node 1487009 .empty .empty)
                  .empty)
                (.node 185855 .empty .empty))
              (.node 23231
                (.node 46463 .empty .empty)
                (.node 11663 .empty .empty)))
            (.node 353
              (.node 1487
                (.node 2879 .empty .empty)
                (.node 653 .empty .empty))
              (.node 143
                (.node 191 .empty .empty)
                (.node 47 .empty .empty))))
          (.node 14994837755
            (.node 239917404179
              (.node 959669616699
                (.node 1919339233391
                  (.node 3838678466776 .empty .empty)
                  .empty)
                (.node 479834808347 .empty .empty))
              (.node 59979351035
                (.node 119958702095 .empty .empty)
                (.node 29989675523 .empty .empty)))
            (.node 937177355
              (.node 3748709435
                (.node 7497418883 .empty .empty)
                (.node 1874354723 .empty .empty))
              (.node 234294335
                (.node 468588679 .empty .empty)
                (.node 117147167 .empty .empty)))))
        (.node 443
          (.node 114395
            (.node 1830431
              (.node 7321691
                (.node 14643407
                  (.node 29286795 .empty .empty)
                  .empty)
                (.node 3660851 .empty .empty))
              (.node 457595
                (.node 915215 .empty .empty)
                (.node 228803 .empty .empty)))
            (.node 7151
              (.node 28607
                (.node 57203 .empty .empty)
                (.node 14303 .empty .empty))
              (.node 1783
                (.node 3563 .empty .empty)
                (.node 891 .empty .empty))))
          (.node 427139384552
            (.node 27
              (.node 107
                (.node 227 .empty .empty)
                (.node 55 .empty .empty))
              (.node 7
                (.node 11 .empty .empty)
                (.node 39 .empty .empty)))
            (.node 26696211503
              (.node 106784846207
                (.node 213569692367 .empty .empty)
                (.node 53392423103 .empty .empty))
              (.node 6674052863
                (.node 13348105727 .empty .empty)
                (.node 3337026431 .empty .empty))))))
      (.node 116621675641
        (.node 12719
          (.node 3258815
            (.node 52141055
              (.node 208564175
                (.node 417128303
                  (.node 834256655 .empty .empty)
                  .empty)
                (.node 104282111 .empty .empty))
              (.node 13035263
                (.node 26070527 .empty .empty)
                (.node 6517631 .empty .empty)))
            (.node 203711
              (.node 814655
                (.node 1629359 .empty .empty)
                (.node 407375 .empty .empty))
              (.node 50879
                (.node 101807 .empty .empty)
                (.node 25487 .empty .empty))))
          (.node 47
            (.node 767
              (.node 3215
                (.node 6335 .empty .empty)
                (.node 1583 .empty .empty))
              (.node 191
                (.node 383 .empty .empty)
                (.node 143 .empty .empty)))
            (.node 1865946810323
              (.node 7463787241300
                (.node 14927574482604 .empty .empty)
                (.node 3731893620647 .empty .empty))
              (.node 466486702583
                (.node 932973405165 .empty .empty)
                (.node 233243351291 .empty .empty)))))
        (.node 889751
          (.node 227776713
            (.node 3644427361
              (.node 14577709453
                (.node 29155418913
                  (.node 58310837819 .empty .empty)
                  .empty)
                (.node 7288854729 .empty .empty))
              (.node 911106839
                (.node 1822213679 .empty .empty)
                (.node 455553419 .empty .empty)))
            (.node 14236043
              (.node 56944175
                (.node 113888353 .empty .empty)
                (.node 28472087 .empty .empty))
              (.node 3559009
                (.node 7118025 .empty .empty)
                (.node 1779503 .empty .empty))))
          (.node 3477
            (.node 55607
              (.node 222441
                (.node 444875 .empty .empty)
                (.node 111217 .empty .empty))
              (.node 13905
                (.node 27803 .empty .empty)
                (.node 6949 .empty .empty)))
            (.node 215
              (.node 865
                (.node 1739 .empty .empty)
                (.node 431 .empty .empty))
              (.node 57
                (.node 107 .empty .empty)
                (.node 25 .empty .empty)))))))
    (.node 124460728319
      (.node 2749121143
        (.node 352321535
          (.node 83802193919
            (.node 8229049214773
              (.node 15
                (.node 1
                  (.node 9 .empty .empty)
                  .empty)
                (.node 19906556064932 .empty .empty))
              (.node 335128600030
                (.node 71 .empty .empty)
                (.node 167618543615 .empty .empty)))
            (.node 5234491391
              (.node 20937965567
                (.node 41912107007 .empty .empty)
                (.node 10468982783 .empty .empty))
              (.node 1322778623
                (.node 2617245695 .empty .empty)
                (.node 654311423 .empty .empty))))
          (.node 703775012735
            (.node 21002452991
              (.node 50331647
                (.node 201326591 .empty .empty)
                (.node 36175871 .empty .empty))
              (.node 678904644672
                (.node 1382679657405 .empty .empty)
                (.node 1407550025468 .empty .empty)))
            (.node 43985938283
              (.node 175943753183
                (.node 351887506367 .empty .empty)
                (.node 87971876591 .empty .empty))
              (.node 10996484571
                (.node 21992969143 .empty .empty)
                (.node 5498242283 .empty .empty)))))
        (.node 20975
          (.node 5369375
            (.node 85910027
              (.node 343640147
                (.node 687280283
                  (.node 1374560571 .empty .empty)
                  .empty)
                (.node 171820079 .empty .empty))
              (.node 21477503
                (.node 42955015 .empty .empty)
                (.node 10738751 .empty .empty)))
            (.node 335579
              (.node 1342347
                (.node 2684687 .empty .empty)
                (.node 671183 .empty .empty))
              (.node 83903
                (.node 167795 .empty .empty)
                (.node 41951 .empty .empty))))
          (.node 83
            (.node 1307
              (.node 5239
                (.node 10475 .empty .empty)
                (.node 2619 .empty .empty))
              (.node 335
                (.node 659 .empty .empty)
                (.node 155 .empty .empty)))
            (.node 39
              (.node 11
                (.node 47 .empty .empty)
                (.node 7 .empty .empty))
              (.node 497843699711
                (.node 995687465422 .empty .empty)
                (.node 248921751551 .empty .empty))))))
      (.node 1748625695
        (.node 786431
          (.node 243007487
            (.node 3889594367
              (.node 15557885951
                (.node 31115182079
                  (.node 62230364159 .empty .empty)
                  .empty)
                (.node 7778697215 .empty .empty))
              (.node 972128255
                (.node 1944846335 .empty .empty)
                (.node 486014975 .empty .empty)))
            (.node 15040511
              (.node 60653567
                (.node 121798655 .empty .empty)
                (.node 30572543 .empty .empty))
              (.node 3932159
                (.node 7766015 .empty .empty)
                (.node 1671167 .empty .empty))))
          (.node 447648178175
            (.node 1790592712702
              (.node 98303
                (.node 688127 .empty .empty)
                (.node 1081343 .empty .empty))
              (.node 1790592712703
                (.node 3581185425405 .empty .empty)
                (.node 895296356351 .empty .empty)))
            (.node 27978011135
              (.node 111912044543
                (.node 223824089087 .empty .empty)
                (.node 55956022271 .empty .empty))
              (.node 6994502783
                (.node 13989005567 .empty .empty)
                (.node 3497251391 .empty .empty)))))
        (.node 13340
          (.node 3415283
            (.node 54644552
              (.node 218578211
                (.node 437156423
                  (.node 874312847 .empty .empty)
                  .empty)
                (.node 109289102 .empty .empty))
              (.node 13661137
                (.node 27322274 .empty .empty)
                (.node 6830567 .empty .empty)))
            (.node 213455
              (.node 853823
                (.node 1707642 .empty .empty)
                (.node 426911 .empty .empty))
              (.node 53363
                (.node 106727 .empty .empty)
                (.node 26678 .empty .empty))))
          (.node 50
            (.node 830
              (.node 3335
                (.node 6671 .empty .empty)
                (.node 1667 .empty .empty))
              (.node 206
                (.node 416 .empty .empty)
                (.node 104 .empty .empty)))
            (.node 2
              (.node 11
                (.node 25 .empty .empty)
                (.node 6 .empty .empty))
              (.node 9
                (.node 1 .empty .empty)
                (.node 8768632786532 .empty .empty)))))))

private def schedPart6 : NatTree :=
  .node 678006543551
    (.node 41396
      (.node 519
        (.node 66899367
          (.node 17126235895
            (.node 274019774583
              (.node 1096079098319
                (.node 2192158196639
                  (.node 4384316393279 .empty .empty)
                  .empty)
                (.node 548039549143 .empty .empty))
              (.node 68504943647
                (.node 137009887295 .empty .empty)
                (.node 34252471823 .empty .empty)))
            (.node 1070389735
              (.node 4281558967
                (.node 8563117959 .empty .empty)
                (.node 2140779495 .empty .empty))
              (.node 267597447
                (.node 535194863 .empty .empty)
                (.node 133798711 .empty .empty))))
          (.node 130655
            (.node 2090599
              (.node 8362415
                (.node 16724831
                  (.node 33449671 .empty .empty)
                  .empty)
                (.node 4181223 .empty .empty))
              (.node 522663
                (.node 1045295 .empty .empty)
                (.node 261319 .empty .empty)))
            (.node 8159
              (.node 32679
                (.node 65327 .empty .empty)
                (.node 16327 .empty .empty))
              (.node 2055
                (.node 4079 .empty .empty)
                (.node 1015 .empty .empty)))))
        (.node 2712943806
          (.node 694513614386
            (.node 7
              (.node 55
                (.node 135
                  (.node 247 .empty .empty)
                  .empty)
                (.node 39 .empty .empty))
              (.node 2778054457554
                (.node 5556108915105 .empty .empty)
                (.node 1389027228779 .empty .empty)))
            (.node 43407100898
              (.node 173628403595
                (.node 347256807193 .empty .empty)
                (.node 86814201798 .empty .empty))
              (.node 10851775223
                (.node 21703550449 .empty .empty)
                (.node 5425887611 .empty .empty))))
          (.node 10597436
            (.node 169558988
              (.node 678235952
                (.node 1356471902 .empty .empty)
                (.node 339117974 .empty .empty))
              (.node 42389747
                (.node 84779495 .empty .empty)
                (.node 21194870 .empty .empty)))
            (.node 662339
              (.node 2649359
                (.node 5298719 .empty .empty)
                (.node 1324679 .empty .empty))
              (.node 165584
                (.node 331166 .empty .empty)
                (.node 82790 .empty .empty))))))
      (.node 163878263
        (.node 10739925971222
          (.node 80
            (.node 1295
              (.node 5173
                (.node 10346
                  (.node 20699 .empty .empty)
                  .empty)
                (.node 2586 .empty .empty))
              (.node 323
                (.node 647 .empty .empty)
                (.node 158 .empty .empty)))
            (.node 2
              (.node 20
                (.node 38 .empty .empty)
                (.node 11 .empty .empty))
              (.node 7
                (.node 1 .empty .empty)
                (.node 5369962985612 .empty .empty))))
          (.node 41952835823
            (.node 671245373197
              (.node 2684981492807
                (.node 5369962985613 .empty .empty)
                (.node 1342490746403 .empty .empty))
              (.node 167811343297
                (.node 335622686601 .empty .empty)
                (.node 83905671647 .empty .empty)))
            (.node 2622052237
              (.node 10488208955
                (.node 20976417911 .empty .empty)
                (.node 5244104481 .empty .empty))
              (.node 655513057
                (.node 1311026121 .empty .empty)
                (.node 327756527 .empty .empty)))))
        (.node 1247
          (.node 320075
            (.node 5121193
              (.node 20484781
                (.node 40969569
                  (.node 81939131 .empty .empty)
                  .empty)
                (.node 10242393 .empty .empty))
              (.node 1280301
                (.node 2560595 .empty .empty)
                (.node 640151 .empty .empty)))
            (.node 20003
              (.node 80015
                (.node 160033 .empty .empty)
                (.node 40007 .empty .empty))
              (.node 5003
                (.node 10005 .empty .empty)
                (.node 2497 .empty .empty))))
          (.node 1
            (.node 81
              (.node 311
                (.node 623 .empty .empty)
                (.node 155 .empty .empty))
              (.node 21
                (.node 37 .empty .empty)
                (.node 11 .empty .empty)))
            (.node 842354591561
              (.node 7108761532858
                (.node 15 .empty .empty)
                (.node 3554380766399 .empty .empty))
              (.node 2712026174975
                (.node 5424052349974 .empty .empty)
                (.node 1356013087487 .empty .empty)))))))
    (.node 1022
      (.node 8793470715983
        (.node 5172671
          (.node 1324231679
            (.node 21187704575
              (.node 84750818111
                (.node 169501635839
                  (.node 339003271679 .empty .empty)
                  .empty)
                (.node 42375409151 .empty .empty))
              (.node 5296925951
                (.node 10593852095 .empty .empty)
                (.node 2648463167 .empty .empty)))
            (.node 82764287
              (.node 331057919
                (.node 662115839 .empty .empty)
                (.node 165528767 .empty .empty))
              (.node 20691263
                (.node 41382143 .empty .empty)
                (.node 10345727 .empty .empty))))
          (.node 20159
            (.node 323327
              (.node 1293311
                (.node 2586431 .empty .empty)
                (.node 646655 .empty .empty))
              (.node 80639
                (.node 161471 .empty .empty)
                (.node 40511 .empty .empty)))
            (.node 1343
              (.node 5183
                (.node 9983 .empty .empty)
                (.node 2495 .empty .empty))
              (.node 191
                (.node 767 .empty .empty)
                (.node 17586941431966 .empty .empty)))))
        (.node 67088855
          (.node 17174747492
            (.node 274795959875
              (.node 1099183839494
                (.node 2198367678995
                  (.node 4396735357991 .empty .empty)
                  .empty)
                (.node 549591919748 .empty .empty))
              (.node 68698989968
                (.node 137397979934 .empty .empty)
                (.node 34349494982 .empty .empty)))
            (.node 1073421719
              (.node 4293686870
                (.node 8587373747 .empty .empty)
                (.node 2146843436 .empty .empty))
              (.node 268355426
                (.node 536710859 .empty .empty)
                (.node 134177713 .empty .empty))))
          (.node 262067
            (.node 4193053
              (.node 16772214
                (.node 33544427 .empty .empty)
                (.node 8386106 .empty .empty))
              (.node 1048262
                (.node 2096526 .empty .empty)
                (.node 524132 .empty .empty)))
            (.node 16379
              (.node 65516
                (.node 131030 .empty .empty)
                (.node 32759 .empty .empty))
              (.node 4093
                (.node 8186 .empty .empty)
                (.node 2046 .empty .empty))))))
      (.node 23478686
        (.node 1538699396495
          (.node 1
            (.node 32
              (.node 128
                (.node 254
                  (.node 512 .empty .empty)
                  .empty)
                (.node 62 .empty .empty))
              (.node 8
                (.node 14 .empty .empty)
                (.node 2 .empty .empty)))
            (.node 24619190343946
              (.node 92043975126578
                (.node 9 .empty .empty)
                (.node 42805594438687 .empty .empty))
              (.node 6154797585985
                (.node 12309595171970 .empty .empty)
                (.node 3077398792991 .empty .empty))))
          (.node 6010544519
            (.node 96168712283
              (.node 384674849123
                (.node 769349698247 .empty .empty)
                (.node 192337424562 .empty .empty))
              (.node 24042178069
                (.node 48084356138 .empty .empty)
                (.node 12021089034 .empty .empty)))
            (.node 375659030
              (.node 1502636126
                (.node 3005272259 .empty .empty)
                (.node 751318064 .empty .empty))
              (.node 93914759
                (.node 187829516 .empty .empty)
                (.node 46957379 .empty .empty)))))
        (.node 179
          (.node 45854
            (.node 733706
              (.node 2934836
                (.node 5869670
                  (.node 11739344 .empty .empty)
                  .empty)
                (.node 1467419 .empty .empty))
              (.node 183426
                (.node 366853 .empty .empty)
                (.node 91715 .empty .empty)))
            (.node 2867
              (.node 11462
                (.node 22928 .empty .empty)
                (.node 5732 .empty .empty))
              (.node 716
                (.node 1430 .empty .empty)
                (.node 359 .empty .empty))))
          (.node 4221606606227
            (.node 11
              (.node 44
                (.node 86 .empty .empty)
                (.node 23 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 8443213212464 .empty .empty)))
            (.node 263850412886
              (.node 1055401651556
                (.node 2110803303110 .empty .empty)
                (.node 527700825779 .empty .empty))
              (.node 65962603223
                (.node 131925206444 .empty .empty)
                (.node 32981301611 .empty .empty)))))))

private def schedPart7 : NatTree :=
  .node 1373488490
    (.node 9587
      (.node 1
        (.node 251627
          (.node 64416602
            (.node 1030665674
              (.node 4122662699
                (.node 8245325401
                  (.node 16490650802 .empty .empty)
                  .empty)
                (.node 2061331350 .empty .empty))
              (.node 257666418
                (.node 515332837 .empty .empty)
                (.node 128833211 .empty .empty)))
            (.node 4026037
              (.node 16104150
                (.node 32208301 .empty .empty)
                (.node 8052074 .empty .empty))
              (.node 1006511
                (.node 2013018 .empty .empty)
                (.node 503255 .empty .empty))))
          (.node 491
            (.node 7862
              (.node 31451
                (.node 62905
                  (.node 125810 .empty .empty)
                  .empty)
                (.node 15726 .empty .empty))
              (.node 1967
                (.node 3932 .empty .empty)
                (.node 983 .empty .empty)))
            (.node 30
              (.node 121
                (.node 242 .empty .empty)
                (.node 59 .empty .empty))
              (.node 8
                (.node 14 .empty .empty)
                (.node 2 .empty .empty)))))
        (.node 628495451
          (.node 160894835351
            (.node 2574317365607
              (.node 10297269462421
                (.node 20594538924849
                  (.node 41189077849709 .empty .empty)
                  .empty)
                (.node 5148634731213 .empty .empty))
              (.node 643579341397
                (.node 1287158682803 .empty .empty)
                (.node 321789670701 .empty .empty)))
            (.node 10055927207
              (.node 40223708833
                (.node 80447417675 .empty .empty)
                (.node 20111854415 .empty .empty))
              (.node 2513981805
                (.node 5027963603 .empty .empty)
                (.node 1256990903 .empty .empty))))
          (.node 2455057
            (.node 39280967
              (.node 157123859
                (.node 314247721 .empty .empty)
                (.node 78561933 .empty .empty))
              (.node 9820237
                (.node 19640483 .empty .empty)
                (.node 4910121 .empty .empty)))
            (.node 153443
              (.node 613763
                (.node 1227527 .empty .empty)
                (.node 306885 .empty .empty))
              (.node 38361
                (.node 76717 .empty .empty)
                (.node 19177 .empty .empty))))))
      (.node 1411213
        (.node 92485362848
          (.node 21
            (.node 299
              (.node 1199
                (.node 2399
                  (.node 4797 .empty .empty)
                  .empty)
                (.node 599 .empty .empty))
              (.node 71
                (.node 145 .empty .empty)
                (.node 35 .empty .empty)))
            (.node 369941451394
              (.node 1
                (.node 11 .empty .empty)
                (.node 13 .empty .empty))
              (.node 369941451395
                (.node 739882902789 .empty .empty)
                (.node 184970725694 .empty .empty))))
          (.node 361270946
            (.node 5780335177
              (.node 23121340712
                (.node 46242681422 .empty .empty)
                (.node 11560670354 .empty .empty))
              (.node 1445083794
                (.node 2890167587 .empty .empty)
                (.node 722541899 .empty .empty)))
            (.node 22579434
              (.node 90317735
                (.node 180635473 .empty .empty)
                (.node 45158867 .empty .empty))
              (.node 5644859
                (.node 11289719 .empty .empty)
                (.node 2822426 .empty .empty)))))
        (.node 11
          (.node 2756
            (.node 44099
              (.node 176401
                (.node 352802
                  (.node 705606 .empty .empty)
                  .empty)
                (.node 88199 .empty .empty))
              (.node 11027
                (.node 22050 .empty .empty)
                (.node 5510 .empty .empty)))
            (.node 170
              (.node 686
                (.node 1379 .empty .empty)
                (.node 344 .empty .empty))
              (.node 42
                (.node 85 .empty .empty)
                (.node 23 .empty .empty))))
          (.node 351613054328
            (.node 1406452217314
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty))
              (.node 1406452217315
                (.node 2812904434629 .empty .empty)
                (.node 703226108654 .empty .empty)))
            (.node 21975815894
              (.node 87903263581
                (.node 175806527162 .empty .empty)
                (.node 43951631790 .empty .empty))
              (.node 5493953975
                (.node 10987907948 .empty .empty)
                (.node 2746976987 .empty .empty)))))))
    (.node 302
      (.node 2620528339043
        (.node 10477
          (.node 2682594
            (.node 42921515
              (.node 171686063
                (.node 343372122
                  (.node 686744245 .empty .empty)
                  .empty)
                (.node 85843031 .empty .empty))
              (.node 10730377
                (.node 21460754 .empty .empty)
                (.node 5365187 .empty .empty)))
            (.node 167663
              (.node 670646
                (.node 1341299 .empty .empty)
                (.node 335324 .empty .empty))
              (.node 41915
                (.node 83831 .empty .empty)
                (.node 20954 .empty .empty))))
          (.node 38
            (.node 654
              (.node 2618
                (.node 5238 .empty .empty)
                (.node 1309 .empty .empty))
              (.node 164
                (.node 326 .empty .empty)
                (.node 83 .empty .empty)))
            (.node 1
              (.node 11
                (.node 20 .empty .empty)
                (.node 2 .empty .empty))
              (.node 2620528339042
                (.node 9 .empty .empty)
                (.node 5241056678085 .empty .empty)))))
        (.node 19993043
          (.node 5118219410
            (.node 81891510594
              (.node 327566042378
                (.node 655132084760
                  (.node 1310264169518 .empty .empty)
                  .empty)
                (.node 163783021189 .empty .empty))
              (.node 20472877646
                (.node 40945755299 .empty .empty)
                (.node 10236438824 .empty .empty)))
            (.node 319888715
              (.node 1279554851
                (.node 2559109705 .empty .empty)
                (.node 639777426 .empty .empty))
              (.node 79972177
                (.node 159944354 .empty .empty)
                (.node 39986087 .empty .empty))))
          (.node 78097
            (.node 1249562
              (.node 4998263
                (.node 9996522 .empty .empty)
                (.node 2499131 .empty .empty))
              (.node 312390
                (.node 624781 .empty .empty)
                (.node 156194 .empty .empty)))
            (.node 4883
              (.node 19523
                (.node 39047 .empty .empty)
                (.node 9762 .empty .empty))
              (.node 1220
                (.node 2438 .empty .empty)
                (.node 611 .empty .empty))))))
      (.node 6117119
        (.node 400879630679
          (.node 14367156945412
            (.node 11
              (.node 37
                (.node 74
                  (.node 152 .empty .empty)
                  .empty)
                (.node 18 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty)))
            (.node 6414074090327
              (.node 25656296360926
                (.node 1539008765021 .empty .empty)
                (.node 12828148180391 .empty .empty))
              (.node 1603518522623
                (.node 3207037045247 .empty .empty)
                (.node 801759261095 .empty .empty))))
          (.node 1565935871
            (.node 25054977023
              (.node 100219907495
                (.node 200439815423 .empty .empty)
                (.node 50109953879 .empty .empty))
              (.node 6263744255
                (.node 12527488511 .empty .empty)
                (.node 3131871911 .empty .empty)))
            (.node 97870847
              (.node 391484159
                (.node 782968151 .empty .empty)
                (.node 195741863 .empty .empty))
              (.node 24467711
                (.node 48935423 .empty .empty)
                (.node 12234071 .empty .empty)))))
        (.node 1539008765024
          (.node 12119
            (.node 191231
              (.node 764759
                (.node 1529087
                  (.node 3058343 .empty .empty)
                  .empty)
                (.node 382463 .empty .empty))
              (.node 47615
                (.node 95399 .empty .empty)
                (.node 23807 .empty .empty)))
            (.node 767
              (.node 3071
                (.node 6143 .empty .empty)
                (.node 1535 .empty .empty))
              (.node 6156035060098
                (.node 167 .empty .empty)
                (.node 3078017530046 .empty .empty))))
          (.node 6011752988
            (.node 96188047813
              (.node 384752191256
                (.node 769504382510 .empty .empty)
                (.node 192376095626 .empty .empty))
              (.node 24047011955
                (.node 48094023906 .empty .empty)
                (.node 12023505974 .empty .empty)))
            (.node 375734558
              (.node 1502938247
                (.node 3005876495 .empty .empty)
                (.node 751469123 .empty .empty))
              (.node 93933638
                (.node 187867280 .empty .empty)
                (.node 46966820 .empty .empty)))))))

private def schedPart8 : NatTree :=
  .node 3387414
    (.node 29
      (.node 607038060863
        (.node 359
          (.node 91730
            (.node 1467710
              (.node 5870852
                (.node 11741702
                  (.node 23483411 .empty .empty)
                  .empty)
                (.node 2935427 .empty .empty))
              (.node 366926
                (.node 733856 .empty .empty)
                (.node 183464 .empty .empty)))
            (.node 5735
              (.node 22931
                (.node 45865 .empty .empty)
                (.node 11466 .empty .empty))
              (.node 1430
                (.node 2867 .empty .empty)
                (.node 716 .empty .empty))))
          (.node 20232244007680
            (.node 11
              (.node 44
                (.node 86
                  (.node 179 .empty .empty)
                  .empty)
                (.node 23 .empty .empty))
              (.node 1
                (.node 2 .empty .empty)
                (.node 9 .empty .empty)))
            (.node 9712608974429
              (.node 38850435897928
                (.node 807026058689 .empty .empty)
                (.node 19425217948991 .empty .empty))
              (.node 2428152243647
                (.node 4856304487265 .empty .empty)
                (.node 1214076121757 .empty .empty)))))
        (.node 4631393
          (.node 1185621149
            (.node 18969939425
              (.node 75879757631
                (.node 151759515263
                  (.node 303519030497 .empty .empty)
                  .empty)
                (.node 37939878749 .empty .empty))
              (.node 4742484863
                (.node 9484969727 .empty .empty)
                (.node 2371242431 .empty .empty)))
            (.node 74101277
              (.node 296405345
                (.node 592810559 .empty .empty)
                (.node 148202687 .empty .empty))
              (.node 18525311
                (.node 37050623 .empty .empty)
                (.node 9262655 .empty .empty))))
          (.node 18047
            (.node 289505
              (.node 1157789
                (.node 2315711 .empty .empty)
                (.node 578879 .empty .empty))
              (.node 72383
                (.node 144767 .empty .empty)
                (.node 36125 .empty .empty)))
            (.node 1151
              (.node 4577
                (.node 9023 .empty .empty)
                (.node 2303 .empty .empty))
              (.node 221
                (.node 575 .empty .empty)
                (.node 161 .empty .empty))))))
      (.node 752
        (.node 49256963
          (.node 12609782166
            (.node 201756514679
              (.node 807026058716
                (.node 1614052117430
                  (.node 3228104234866 .empty .empty)
                  .empty)
                (.node 403513029359 .empty .empty))
              (.node 50439128666
                (.node 100878257339 .empty .empty)
                (.node 25219564333 .empty .empty)))
            (.node 788111387
              (.node 3152445541
                (.node 6304891082 .empty .empty)
                (.node 1576222770 .empty .empty))
              (.node 197027845
                (.node 394055690 .empty .empty)
                (.node 98513922 .empty .empty))))
          (.node 192409
            (.node 3078560
              (.node 12314240
                (.node 24628478 .empty .empty)
                (.node 6157118 .empty .empty))
              (.node 769640
                (.node 1539278 .empty .empty)
                (.node 384818 .empty .empty)))
            (.node 12025
              (.node 48102
                (.node 96203 .empty .empty)
                (.node 24050 .empty .empty))
              (.node 3006
                (.node 6011 .empty .empty)
                (.node 1502 .empty .empty)))))
        (.node 221997575459
          (.node 9
            (.node 23
              (.node 95
                (.node 188
                  (.node 374 .empty .empty)
                  .empty)
                (.node 47 .empty .empty))
              (.node 2
                (.node 11 .empty .empty)
                (.node 1 .empty .empty)))
            (.node 3551961207361
              (.node 14207844829449
                (.node 7103922414724 .empty .empty)
                (.node 7103922414722 .empty .empty))
              (.node 887990301839
                (.node 1775980603679 .empty .empty)
                (.node 443995150919 .empty .empty))))
          (.node 867178031
            (.node 13874848465
              (.node 55499393867
                (.node 110998787730 .empty .empty)
                (.node 27749696930 .empty .empty))
              (.node 3468712115
                (.node 6937424231 .empty .empty)
                (.node 1734356058 .empty .empty)))
            (.node 54198625
              (.node 216794507
                (.node 433589015 .empty .empty)
                (.node 108397250 .empty .empty))
              (.node 13549655
                (.node 27099311 .empty .empty)
                (.node 6774827 .empty .empty)))))))
    (.node 73679543
      (.node 12595494911
        (.node 25
          (.node 6614
            (.node 105854
              (.node 423426
                (.node 846853
                  (.node 1693706 .empty .empty)
                  .empty)
                (.node 211715 .empty .empty))
              (.node 26462
                (.node 52928 .empty .empty)
                (.node 13232 .empty .empty)))
            (.node 410
              (.node 1655
                (.node 3308 .empty .empty)
                (.node 827 .empty .empty))
              (.node 102
                (.node 205 .empty .empty)
                (.node 50 .empty .empty))))
          (.node 3224157290495
            (.node 1
              (.node 6
                (.node 11 .empty .empty)
                (.node 2 .empty .empty))
              (.node 12896630828500
                (.node 9 .empty .empty)
                (.node 6448315539455 .empty .empty)))
            (.node 201513148415
              (.node 806036176895
                (.node 1612074541055 .empty .empty)
                (.node 403018088447 .empty .empty))
              (.node 50379792383
                (.node 100753563647 .empty .empty)
                (.node 25190989823 .empty .empty)))))
        (.node 4828662410682
          (.node 25165823
            (.node 392257535
              (.node 1572863999
                (.node 3145727999
                  (.node 6293643263 .empty .empty)
                  .empty)
                (.node 790536191 .empty .empty))
              (.node 100663295
                (.node 199139327 .empty .empty)
                (.node 50331647 .empty .empty)))
            (.node 77258598570921
              (.node 2187263
                (.node 12582911 .empty .empty)
                (.node 12836048732159 .empty .empty))
              (.node 19314649642729
                (.node 38629299285458 .empty .empty)
                (.node 9657324821363 .empty .empty))))
          (.node 18861962543
            (.node 301791400667
              (.node 1207165602671
                (.node 2414331205343 .empty .empty)
                (.node 603582801335 .empty .empty))
              (.node 75447850165
                (.node 150895700330 .empty .empty)
                (.node 37723925082 .empty .empty)))
            (.node 1178872657
              (.node 4715490635
                (.node 9430981271 .empty .empty)
                (.node 2357745314 .empty .empty))
              (.node 294718163
                (.node 589436327 .empty .empty)
                (.node 147359082 .empty .empty))))))
      (.node 1887547270283
        (.node 563
          (.node 143903
            (.node 2302487
              (.node 9209941
                (.node 18419882
                  (.node 36839771 .empty .empty)
                  .empty)
                (.node 4604970 .empty .empty))
              (.node 575618
                (.node 1151243 .empty .empty)
                (.node 287809 .empty .empty)))
            (.node 8994
              (.node 35975
                (.node 71951 .empty .empty)
                (.node 17987 .empty .empty))
              (.node 2246
                (.node 4499 .empty .empty)
                (.node 1124 .empty .empty))))
          (.node 1
            (.node 35
              (.node 140
                (.node 278 .empty .empty)
                (.node 71 .empty .empty))
              (.node 8
                (.node 14 .empty .empty)
                (.node 2 .empty .empty)))
            (.node 30200756324498
              (.node 30200756324500
                (.node 9 .empty .empty)
                (.node 60401512649001 .empty .empty))
              (.node 7550189081123
                (.node 15100378162249 .empty .empty)
                (.node 3775094540562 .empty .empty)))))
        (.node 14400841
          (.node 3686615761
            (.node 58985852195
              (.node 235943408783
                (.node 471886817569
                  (.node 943773635138 .empty .empty)
                  .empty)
                (.node 117971704391 .empty .empty))
              (.node 14746463051
                (.node 29492926098 .empty .empty)
                (.node 7373231522 .empty .empty)))
            (.node 230413487
              (.node 921653939
                (.node 1843307879 .empty .empty)
                (.node 460826970 .empty .empty))
              (.node 57603371
                (.node 115206743 .empty .empty)
                (.node 28801682 .empty .empty))))
          (.node 56255
            (.node 900050
              (.node 3600210
                (.node 7200419 .empty .empty)
                (.node 1800107 .empty .empty))
              (.node 225011
                (.node 450025 .empty .empty)
                (.node 112506 .empty .empty)))
            (.node 3515
              (.node 14063
                (.node 28127 .empty .empty)
                (.node 7031 .empty .empty))
              (.node 877
                (.node 1754 .empty .empty)
                (.node 438 .empty .empty)))))))

private def schedPart9 : NatTree :=
  .node 10665455
    (.node 316765048241
      (.node 20316863
        (.node 1331486368895
          (.node 9
            (.node 13
              (.node 54
                (.node 109
                  (.node 218 .empty .empty)
                  .empty)
                (.node 26 .empty .empty))
              (.node 2
                (.node 6 .empty .empty)
                (.node 1 .empty .empty)))
            (.node 21303781902485
              (.node 85215127609727
                (.node 170430255219508 .empty .empty)
                (.node 42607563804863 .empty .empty))
              (.node 5325945475583
                (.node 10651890951209 .empty .empty)
                (.node 2662972737791 .empty .empty))))
          (.node 5201118677
            (.node 83217898025
              (.node 332871592277
                (.node 665743184447 .empty .empty)
                (.node 166435796159 .empty .empty))
              (.node 20804474495
                (.node 41608948991 .empty .empty)
                (.node 10402237247 .empty .empty)))
            (.node 325069865
              (.node 1300279679
                (.node 2600559359 .empty .empty)
                (.node 650139839 .empty .empty))
              (.node 81267455
                (.node 162534911 .empty .empty)
                (.node 40633727 .empty .empty)))))
        (.node 341
          (.node 79337
            (.node 1269845
              (.node 5079209
                (.node 10158485 .empty .empty)
                (.node 2539583 .empty .empty))
              (.node 317417
                (.node 634943 .empty .empty)
                (.node 158741 .empty .empty)))
            (.node 4991
              (.node 19817
                (.node 39701 .empty .empty)
                (.node 9941 .empty .empty))
              (.node 1193
                (.node 2495 .empty .empty)
                (.node 575 .empty .empty))))
          (.node 81091852350527
            (.node 251652158708248
              (.node 41
                (.node 191 .empty .empty)
                (.node 16525511398943 .empty .empty))
              (.node 44734227003605
                (.node 125826079354127 .empty .empty)
                (.node 162183704701030 .empty .empty)))
            (.node 5068240771919
              (.node 20272963087679
                (.node 40545926175281 .empty .empty)
                (.node 10136481543791 .empty .empty))
              (.node 1267060192943
                (.node 2534120385983 .empty .empty)
                (.node 633530096477 .empty .empty))))))
      (.node 47
        (.node 4833437
          (.node 1237363439
            (.node 19797815471
              (.node 79191262079
                (.node 158382524159 .empty .empty)
                (.node 39595631039 .empty .empty))
              (.node 4949453873
                (.node 9898907741 .empty .empty)
                (.node 2474726975 .empty .empty)))
            (.node 77335217
              (.node 309340847
                (.node 618681743 .empty .empty)
                (.node 154670429 .empty .empty))
              (.node 19333823
                (.node 38667647 .empty .empty)
                (.node 9666863 .empty .empty))))
          (.node 18863
            (.node 302063
              (.node 1208369
                (.node 2416703 .empty .empty)
                (.node 604223 .empty .empty))
              (.node 75503
                (.node 151055 .empty .empty)
                (.node 37775 .empty .empty)))
            (.node 1181
              (.node 4721
                (.node 9437 .empty .empty)
                (.node 2351 .empty .empty))
              (.node 305
                (.node 575 .empty .empty)
                (.node 191 .empty .empty)))))
        (.node 698972296925
          (.node 178936908014207
            (.node 697657346636645
              (.node 657779961515201
                (.node 29 .empty .empty)
                (.node 1413404978693272 .empty .empty))
              (.node 715747632056639
                (.node 1431495264113254 .empty .empty)
                (.node 357873816028337 .empty .empty)))
            (.node 11183556750911
              (.node 44734227003503
                (.node 89468454007103 .empty .empty)
                (.node 22367113501775 .empty .empty))
              (.node 2795889187727
                (.node 5591778375407 .empty .empty)
                (.node 1397944593839 .empty .empty))))
          (.node 2730360575
            (.node 43685768561
              (.node 174743074223
                (.node 349486148465 .empty .empty)
                (.node 87371537117 .empty .empty))
              (.node 10921442141
                (.node 21842884271 .empty .empty)
                (.node 5460721073 .empty .empty)))
            (.node 170647517
              (.node 682590143
                (.node 1365180287 .empty .empty)
                (.node 341295023 .empty .empty))
              (.node 42661871
                (.node 85323761 .empty .empty)
                (.node 21330959 .empty .empty)))))))
    (.node 887
      (.node 3801180578934
        (.node 191
          (.node 41663
            (.node 666623
              (.node 2666351
                (.node 5332751 .empty .empty)
                (.node 1333199 .empty .empty))
              (.node 166655
                (.node 333311 .empty .empty)
                (.node 83327 .empty .empty)))
            (.node 2609
              (.node 10397
                (.node 20783 .empty .empty)
                (.node 5183 .empty .empty))
              (.node 623
                (.node 1343 .empty .empty)
                (.node 335 .empty .empty))))
          (.node 973102228207151
            (.node 3892408912828606
              (.node 29
                (.node 47 .empty .empty)
                (.node 161 .empty .empty))
              (.node 3892408912828607
                (.node 7784817825657213 .empty .empty)
                (.node 1946204456414303 .empty .empty)))
            (.node 60818889262945
              (.node 243275557051787
                (.node 486551114103575 .empty .empty)
                (.node 121637778525890 .empty .empty))
              (.node 15204722315735
                (.node 30409444631471 .empty .empty)
                (.node 7602361157867 .empty .empty)))))
        (.node 58001411
          (.node 14848361636
            (.node 237573786182
              (.node 950295144733
                (.node 1900590289466 .empty .empty)
                (.node 475147572366 .empty .empty))
              (.node 59393446547
                (.node 118786893092 .empty .empty)
                (.node 29696723270 .empty .empty)))
            (.node 928022603
              (.node 3712090406
                (.node 7424180819 .empty .empty)
                (.node 1856045204 .empty .empty))
              (.node 232005649
                (.node 464011298 .empty .empty)
                (.node 116002823 .empty .empty))))
          (.node 226568
            (.node 3625088
              (.node 14500355
                (.node 29000706 .empty .empty)
                (.node 7250174 .empty .empty))
              (.node 906272
                (.node 1812542 .empty .empty)
                (.node 453134 .empty .empty)))
            (.node 14159
              (.node 56641
                (.node 113282 .empty .empty)
                (.node 28319 .empty .empty))
              (.node 3539
                (.node 7079 .empty .empty)
                (.node 1770 .empty .empty))))))
      (.node 3497261327
        (.node 229196517953087
          (.node 2
            (.node 54
              (.node 218
                (.node 443 .empty .empty)
                (.node 109 .empty .empty))
              (.node 13
                (.node 26 .empty .empty)
                (.node 6 .empty .empty)))
            (.node 3667144287249559
              (.node 9
                (.node 1 .empty .empty)
                (.node 7334288574499124 .empty .empty))
              (.node 916786071812399
                (.node 1833572143624791 .empty .empty)
                (.node 458393035906183 .empty .empty))))
          (.node 895298898247
            (.node 14324782372079
              (.node 57299129488271
                (.node 114598258976543 .empty .empty)
                (.node 28649564744151 .empty .empty))
              (.node 3581195593007
                (.node 7162391186023 .empty .empty)
                (.node 1790597796519 .empty .empty)))
            (.node 55956181151
              (.node 223824724559
                (.node 447649449119 .empty .empty)
                (.node 111912362295 .empty .empty))
              (.node 13989045271
                (.node 27978090575 .empty .empty)
                (.node 6994522647 .empty .empty)))))
        (.node 53367
          (.node 13661183
            (.node 218578839
              (.node 874315335
                (.node 1748630647 .empty .empty)
                (.node 437157655 .empty .empty))
              (.node 54644695
                (.node 109289423 .empty .empty)
                (.node 27322359 .empty .empty)))
            (.node 853823
              (.node 3415295
                (.node 6830591 .empty .empty)
                (.node 1707647 .empty .empty))
              (.node 213455
                (.node 426911 .empty .empty)
                (.node 106711 .empty .empty))))
          (.node 199
            (.node 3319
              (.node 13343
                (.node 26687 .empty .empty)
                (.node 6671 .empty .empty))
              (.node 823
                (.node 1671 .empty .empty)
                (.node 423 .empty .empty)))
            (.node 7
              (.node 47
                (.node 95 .empty .empty)
                (.node 39 .empty .empty))
              (.node 23
                (.node 8154804734598879 .empty .empty)
                (.node 23 .empty .empty)))))))

private def batchSchedule : List ℕ :=
  schedPart0.toListAux (schedPart1.toListAux (schedPart2.toListAux
    (schedPart3.toListAux (schedPart4.toListAux (schedPart5.toListAux
      (schedPart6.toListAux (schedPart7.toListAux
        (schedPart8.toListAux (schedPart9.toListAux [])))))))))

/-! ## Kernel Rule Table Verification -/

private def checkSegRule (wi : ℕ) (r : SegRule) : Bool :=
  let (g, vi, u, c, _, _, t1, t2, xl, xb) := r
  let wIn := wordB wi ++ powWB u
  let wOut := powWB g ++ wordB vi
  if Nat.beq c 0 then
    checkSeg1B false wIn wOut t1
  else if Nat.beq c 1 then
    checkSeg2B false false wIn (decodeBits xl xb) wOut t1 t2
  else
    false

private theorem checkSegRule_spec {wi : ℕ} {r : SegRule} (h : checkSegRule wi r = true) :
    let (g, vi, u, c, _, _, _, _, _, _) := r
    SegRLs tm (hSig ^ (1 : ℕ)) (hSig ^ c) (wordF wi ++ W ^ u) (W ^ g ++ wordF vi) := by
  rcases r with ⟨g, vi, u, c, pre, per, t1, t2, xl, xb⟩
  dsimp only [checkSegRule] at h ⊢
  cases hc0 : Nat.beq c 0 <;> rw [hc0] at h
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hc1 : Nat.beq c 1 <;> rw [hc1] at h
    · cases h
    · simp only [↓reduceIte] at h
      have hc : c = 1 := Nat.beq_eq.mp hc1
      subst hc
      have hs := checkSeg2B_spec h
      simpa only [wordF, bWord_append, bWord_powWB, pow_one_list, hSig, hret] using hs
  · simp only [↓reduceIte] at h
    have hc : c = 0 := Nat.beq_eq.mp hc0
    subst hc
    have hs := checkSeg1B_spec h
    simpa only [wordF, bWord_append, bWord_powWB, pow_one_list, pow_zero_list, hSig, hret] using hs

private def checkTailRule (wi : ℕ) (r : TailRule) : Bool :=
  let (g, vi, t1) := r
  checkTailB false (wordB wi) (powWB g ++ wordB vi) t1

private theorem checkTailRule_spec {wi : ℕ} {r : TailRule} (h : checkTailRule wi r = true) :
    let (g, vi, _) := r
    SideRLs tm (hSig ^ (1 : ℕ)) (wordF wi +> default) ((W ^ g ++ wordF vi) +> default) := by
  rcases r with ⟨g, vi, t1⟩
  have hs := checkTailB_spec h
  rw [pow_one_list, hSig]
  simpa only [wordF, bWord_append, bWord_powWB, hret] using SideRLs.single hs

private def checkLOpt (f' : Bool) (sIn xMid : List Bool) (t1 : ℕ) :
    Option (Bool × ℕ × ℕ × ℕ × ℕ) → Bool
  | none => true
  | some (f, g, ci, b, t2) =>
    checkSeg2B f f' sIn xMid (powWB g ++ wordB ci ++ powWB b) t1 t2

private def checkCAct (k : ℕ) (act : CAct) : Bool :=
  let wi := k / 16
  let j := k % 16
  let sIn := wordB wi ++ powWB j
  match act with
  | .back0 f g ci b t1 =>
    checkSeg1B f sIn (powWB g ++ wordB ci ++ powWB b) t1
  | .right xl xb t1 lf lt =>
    let xMid := decodeBits xl xb
    checkRightB sIn xMid t1 && checkLOpt false sIn xMid t1 lf && checkLOpt true sIn xMid t1 lt
  | .more => true
  | .halt t1 => checkHaltB sIn t1

private def checkCTailRule (ti : ℕ) (r : CTailRule) : Bool :=
  let (f, g, ci, t1) := r
  checkTailB f (wordB ti) (powWB g ++ wordB ci) t1

private def checkMergeRule (k wmi : ℕ) : Bool :=
  let wn := k / 512
  let w2i := k % 512
  let wi := wn / 16
  let n := wn % 16
  bWordEq (wordB wmi) (wordB wi ++ powWB n ++ wordB w2i)

private theorem all_seg_ok : Bst.allB checkSegRule segTree = true := by
  decide +kernel

private theorem all_tail_ok : Bst.allB checkTailRule tailTree = true := by
  decide +kernel

private theorem all_cseg_ok : Bst.allB checkCAct csegTree = true := by
  decide +kernel

private theorem all_ctail_ok : Bst.allB checkCTailRule ctailTree = true := by
  decide +kernel

private theorem all_merge_ok : Bst.allB checkMergeRule mergeTree = true := by
  decide +kernel

/-! ## Integer-ID Batch and Call Evaluators -/

private abbrev IdCells := List (ℕ × ℕ)

private def idSide : IdCells → ℕ → ListBlank (Fin 2)
  | [], ti => wordF ti +> default
  | (wi, n) :: cs, ti => wordF wi +> (W ^ n +> idSide cs ti)

private def walkSegId : ℕ → ℕ → Option (ℕ × ℕ × ℕ × ℕ)
  | wi, 0 => some (wi, 0, 0, 0)
  | wi, n + 1 =>
    match segTree.get? wi with
    | none => none
    | some (g, vi, u, c, _, _, _, _, _, _) =>
      match walkSegId vi n with
      | none => none
      | some (w', g', u', c') =>
        withReducedNat (g + g') fun g'' =>
        withReducedNat (u + u') fun u'' =>
        withReducedNat (c + c') fun c'' =>
        some (w', g'', u'', c'')

private theorem walkSegId_spec :
    ∀ n wi w' g u c, walkSegId wi n = some (w', g, u, c) →
      SegRLs tm (hSig ^ n) (hSig ^ c) (wordF wi ++ W ^ u) (W ^ g ++ wordF w')
  | 0, wi, _, _, _, _, h => by
    cases h
    simp only [pow_zero_list, List.append_nil, List.nil_append]
    exact .nil _
  | n + 1, wi, w', g, u, c, h => by
    dsimp only [walkSegId] at h
    rcases h_lk : segTree.get? wi with _ | ⟨g₁, vi, u₁, c₁, pre, per, t1, t2, xl, xb⟩ <;>
      rw [h_lk] at h
    · cases h
    · dsimp only at h
      rcases h_wk : walkSegId vi n with _ | ⟨w₂, g₂, u₂, c₂⟩ <;> rw [h_wk] at h
      · cases h
      · simp only [withReducedNat_eq] at h
        cases h
        have h₁ := checkSegRule_spec (Bst.allB_spec segTree all_seg_ok wi _ h_lk)
        have h₂ := walkSegId_spec n vi w' g₂ u₂ c₂ h_wk
        have h_add : n + 1 = 1 + n := by omega
        rw [h_add]
        exact comp_seg h₁ h₂

private theorem cycSegId_spec (k p : ℕ) {wi g u c : ℕ}
    (hp : SegRLs tm (hSig ^ p) (hSig ^ c) (wordF wi ++ W ^ u) (W ^ g ++ wordF wi)) :
    SegRLs tm (hSig ^ (k * p)) (hSig ^ (k * c)) (wordF wi ++ W ^ (k * u))
      (W ^ (k * g) ++ wordF wi) := by
  induction k with
  | zero =>
    simp only [Nat.zero_mul, pow_zero_list, List.append_nil, List.nil_append]
    exact .nil _
  | succ k ih =>
    have h₁ : (k + 1) * p = p + k * p := by rw [Nat.succ_mul, Nat.add_comm]
    have h₂ : (k + 1) * c = c + k * c := by rw [Nat.succ_mul, Nat.add_comm]
    have h₃ : (k + 1) * u = u + k * u := by rw [Nat.succ_mul, Nat.add_comm]
    have h₄ : (k + 1) * g = g + k * g := by rw [Nat.succ_mul, Nat.add_comm]
    rw [h₁, h₂, h₃, h₄]
    exact comp_seg hp ih

private def fwalkId (wi t : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match segTree.get? wi with
  | none => none
  | some (_, _, _, _, pre, per, _, _, _, _) =>
    if Nat.ble t (pre + per) then
      walkSegId wi t
    else
      match walkSegId wi pre with
      | none => none
      | some (w₁, g₁, u₁, c₁) =>
        match walkSegId w₁ per with
        | none => none
        | some (w₂, g₂, u₂, c₂) =>
          if Nat.beq w₂ w₁ then
            withReducedNat (t - pre) fun m =>
            withReducedNat (m / per) fun k =>
            withReducedNat (m % per) fun r =>
            match walkSegId w₁ r with
            | none => none
            | some (w₃, g₃, u₃, c₃) =>
              withReducedNat (g₁ + k * g₂ + g₃) fun gTot =>
              withReducedNat (u₁ + k * u₂ + u₃) fun uTot =>
              withReducedNat (c₁ + k * c₂ + c₃) fun cTot =>
              some (w₃, gTot, uTot, cTot)
          else
            none

private theorem fwalkId_spec {wi t w' g u c : ℕ}
    (h : fwalkId wi t = some (w', g, u, c)) :
    SegRLs tm (hSig ^ t) (hSig ^ c) (wordF wi ++ W ^ u) (W ^ g ++ wordF w') := by
  dsimp only [fwalkId] at h
  rcases h_lk : segTree.get? wi with _ | ⟨_, _, _, _, pre, per, _, _, _, _⟩ <;> rw [h_lk] at h
  · cases h
  · dsimp only at h
    cases h_ble : Nat.ble t (pre + per) <;> rw [h_ble] at h
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hgt : pre + per < t := by
        rcases Nat.lt_or_ge (pre + per) t with hlt | hge
        · exact hlt
        · exact absurd (Nat.ble_eq.mpr hge) (by simp [h_ble])
      rcases h₁ : walkSegId wi pre with _ | ⟨w₁, g₁, u₁, c₁⟩ <;> rw [h₁] at h
      · cases h
      · dsimp only at h
        rcases h₂ : walkSegId w₁ per with _ | ⟨w₂, g₂, u₂, c₂⟩ <;> rw [h₂] at h
        · cases h
        · dsimp only at h
          cases h_eq : Nat.beq w₂ w₁ <;> rw [h_eq] at h
          · cases h
          · simp only [↓reduceIte, withReducedNat_eq] at h
            rcases h₃ : walkSegId w₁ ((t - pre) % per) with _ | ⟨w₃, g₃, u₃, c₃⟩ <;>
              rw [h₃] at h
            · cases h
            · cases h
              have hw21 : w₂ = w₁ := Nat.beq_eq.mp h_eq
              subst w₂
              have s₁ := walkSegId_spec pre wi w₁ g₁ u₁ c₁ h₁
              have s₂ := walkSegId_spec per w₁ w₁ g₂ u₂ c₂ h₂
              have s₃ := walkSegId_spec ((t - pre) % per) w₁ w' g₃ u₃ c₃ h₃
              have s_cyc := cycSegId_spec ((t - pre) / per) per s₂
              have s_all := comp_seg (comp_seg s₁ s_cyc) s₃
              have ht_eq : pre + (t - pre) / per * per + (t - pre) % per = t := by
                have hdiv := Nat.div_add_mod (t - pre) per
                rw [Nat.mul_comm] at hdiv
                omega
              rwa [ht_eq] at s_all
    · simp only [↓reduceIte] at h
      exact walkSegId_spec t wi w' g u c h

private def walkTailId : ℕ → ℕ → Option (ℕ × ℕ)
  | ti, 0 => some (ti, 0)
  | ti, n + 1 =>
    match tailTree.get? ti with
    | none => none
    | some (g, vi, _) =>
      match walkTailId vi n with
      | none => none
      | some (t', g') =>
        withReducedNat (g + g') fun g'' =>
        some (t', g'')

private theorem walkTailId_spec :
    ∀ n ti t' g, walkTailId ti n = some (t', g) →
      SideRLs tm (hSig ^ n) (wordF ti +> default) ((W ^ g ++ wordF t') +> default)
  | 0, ti, _, _, h => by
    cases h
    simp only [pow_zero_list, List.nil_append]
    exact .nil _
  | n + 1, ti, t', g, h => by
    dsimp only [walkTailId] at h
    rcases h_lk : tailTree.get? ti with _ | ⟨g₁, vi, t1⟩ <;> rw [h_lk] at h
    · cases h
    · dsimp only at h
      rcases h_wk : walkTailId vi n with _ | ⟨t₂, g₂⟩ <;> rw [h_wk] at h
      · cases h
      · simp only [withReducedNat_eq] at h
        cases h
        have h₁ := checkTailRule_spec (Bst.allB_spec tailTree all_tail_ok ti _ h_lk)
        have h₂ := walkTailId_spec n vi t' g₂ h_wk
        have h_add : n + 1 = 1 + n := by omega
        rw [h_add]
        exact comp_tail h₁ h₂

private def batchId : ℕ → IdCells → ℕ → Option (ℕ × IdCells × ℕ)
  | t, [], ti =>
    if Nat.beq t 0 then
      some (0, [], ti)
    else
      match walkTailId ti t with
      | some (ti', g) => some (g, [], ti')
      | none => none
  | t, (wi, n) :: cs, ti =>
    match fwalkId wi t with
    | none => none
    | some (wi', g, u, c) =>
      if Nat.ble u n then
        match batchId c cs ti with
        | none => none
        | some (e, cs', ti') =>
          withReducedNat (n - u + e) fun n' =>
          some (g, (wi', n') :: cs', ti')
      else
        none

private theorem batchId_spec :
    ∀ t cs ti e cs' ti', batchId t cs ti = some (e, cs', ti') →
      SideRLs tm (hSig ^ t) (idSide cs ti) (W ^ e +> idSide cs' ti')
  | t, [], ti, e, cs', ti', h => by
    dsimp only [batchId] at h
    cases h_t0 : Nat.beq t 0 <;> rw [h_t0] at h
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases h_wk : walkTailId ti t with _ | ⟨ti₁, g⟩ <;> rw [h_wk] at h
      · cases h
      · cases h
        have hw := walkTailId_spec t ti ti' e h_wk
        dsimp only [idSide]
        rwa [← Longitudinal.append_assoc]
    · simp only [↓reduceIte] at h
      cases h
      have ht0 : t = 0 := Nat.beq_eq.mp h_t0
      subst ht0
      simp only [pow_zero_list, Longitudinal.append_nil]
      exact .nil _
  | t, (wi, n) :: cs, ti, e, cs', ti', h => by
    dsimp only [batchId] at h
    rcases h_fw : fwalkId wi t with _ | ⟨wi₁, g, u, c⟩ <;> rw [h_fw] at h
    · cases h
    · dsimp only at h
      cases h_un : Nat.ble u n <;> rw [h_un] at h
      · cases h
      · simp only [↓reduceIte] at h
        have hun : u ≤ n := Nat.ble_eq.mp h_un
        rcases h_rec : batchId c cs ti with _ | ⟨e₁, cs₁, ti₁⟩ <;> rw [h_rec] at h
        · cases h
        · simp only [withReducedNat_eq] at h
          cases h
          have h_seg := fwalkId_spec h_fw
          have h_ih := batchId_spec c cs ti e₁ cs₁ ti' h_rec
          have h_comb :=
            (h_seg.concat (SegRLs.wall_pow (wall (n - u)) c)).sideRLs_concat h_ih
          have hn_eq : n = u + (n - u) := by omega
          dsimp only [idSide]
          conv_lhs =>
            rw [hn_eq, pow_add_list, Longitudinal.append_assoc,
              ← Longitudinal.append_assoc (wordF wi) (W ^ u)]
          rw [pow_add_list W (n - u) e₁]
          simpa only [Longitudinal.append_assoc] using h_comb

private inductive IdOut where
  | stuck : IdOut
  | back : Bool → ℕ → IdCells → ℕ → IdOut
  | halted : IdOut

private def callId : ℕ → IdCells → ℕ → IdOut
  | 0, _, _ => .stuck
  | _ + 1, [], ti =>
    match ctailTree.get? ti with
    | some (f, g, ci, _) => .back f g [] ci
    | none => .stuck
  | fuel + 1, (wi, n) :: rest, ti =>
    withReducedNat (Nat.min n 12) fun j =>
    let k := wi * 16 + j
    match csegTree.get? k with
    | some (.back0 f g ci b _) =>
      withReducedNat (b + (n - j)) fun n' =>
      .back f g ((ci, n') :: rest) ti
    | some (.right _ _ _ lf lt) =>
      match callId fuel rest ti with
      | .back f' a rest' ti' =>
        match if f' then lt else lf with
        | some (f, g, ci, b, _) =>
          withReducedNat (b + (n - j) + a) fun n' =>
          .back f g ((ci, n') :: rest') ti'
        | none => .stuck
      | .halted => .halted
      | .stuck => .stuck
    | some .more =>
      if Nat.ble n 12 then
        match rest with
        | (w2i, n2) :: rest2 =>
          if Nat.blt w2i 512 then
            match mergeTree.get? ((wi * 16 + n) * 512 + w2i) with
            | some wmi => callId fuel ((wmi, n2) :: rest2) ti
            | none => .stuck
          else
            .stuck
        | [] =>
          if Nat.blt ti 512 then
            match mergeTree.get? ((wi * 16 + n) * 512 + ti) with
            | some wmi => callId fuel [] wmi
            | none => .stuck
          else
            .stuck
      else
        .stuck
    | some (.halt _) => .halted
    | none => .stuck

private theorem sideRL_of_sideRLs_one {a b : DH0 (Fin 2) (Fin 6)} {r r' : ListBlank (Fin 2)}
    (h : SideRLs tm [(a, b)] r r') : SideRL tm a b r r' :=
  fun l => h.elim_single l

private theorem div_mod_16 (wi j : ℕ) (hj : j ≤ 12) :
    (wi * 16 + j) / 16 = wi ∧ (wi * 16 + j) % 16 = j := by
  omega

private theorem div_mod_merge (wi n w2i : ℕ) (hn : n ≤ 12) (hw2 : w2i < 512) :
    ((wi * 16 + n) * 512 + w2i) / 512 / 16 = wi ∧
    ((wi * 16 + n) * 512 + w2i) / 512 % 16 = n ∧
    ((wi * 16 + n) * 512 + w2i) % 512 = w2i := by
  omega

private theorem callId_spec :
    ∀ fuel cs ti,
      match callId fuel cs ti with
      | .back f a cs' ti' => SideRL tm hR (hret f) (idSide cs ti) (W ^ a +> idSide cs' ti')
      | .halted => ∀ l, HaltsTm (([1, 0, 1, 0] +> l) {{B}}> idSide cs ti)
      | .stuck => True
  | 0, _, _ => trivial
  | _ + 1, [], ti => by
    dsimp only [callId]
    rcases h_lk : ctailTree.get? ti with _ | ⟨f, g, ci, t1⟩
    · trivial
    · dsimp only
      have h_ok := Bst.allB_spec ctailTree all_ctail_ok ti _ h_lk
      have hs := checkTailB_spec h_ok
      dsimp only [idSide]
      simpa only [wordF, bWord_append, bWord_powWB, Longitudinal.append_assoc] using hs
  | fuel + 1, (wi, n) :: rest, ti => by
    dsimp only [callId, withReducedNat_eq]
    set j := Nat.min n 12
    have hj_le : j ≤ 12 := Nat.min_le_right n 12
    obtain ⟨hd16, hm16⟩ := div_mod_16 wi j hj_le
    have h_split_n : ∀ X : ListBlank (Fin 2),
        (wordF wi ++ W ^ j) +> (W ^ (n - j) +> X) = wordF wi +> (W ^ n +> X) := by
      intro X
      have hjn : j + (n - j) = n := by
        simp only [j, Nat.min_def]
        split_ifs <;> omega
      rw [Longitudinal.append_assoc, ← Longitudinal.append_assoc (W ^ j), ← pow_add_list, hjn]
    rcases h_lk : csegTree.get? (wi * 16 + j) with _ | act
    · trivial
    · have h_act := Bst.allB_spec csegTree all_cseg_ok (wi * 16 + j) act h_lk
      dsimp only [checkCAct] at h_act
      rw [hd16, hm16] at h_act
      rcases act with ⟨f, g, ci, b, t1⟩ | ⟨xl, xb, t1, lf, lt⟩ | _ | ⟨t1⟩
      · dsimp only [withReducedNat_eq] at h_act ⊢
        have hs := checkSeg1B_spec h_act
        simp only [bWord_append, bWord_powWB, bWord_wordB] at hs
        have h_comb :=
          sideRL_of_sideRLs_one (hs.sideRLs_concat (.nil (W ^ (n - j) +> idSide rest ti)))
        dsimp only [idSide]
        rw [← h_split_n, pow_add_list W b (n - j)]
        simpa only [Longitudinal.append_assoc] using h_comb
      · dsimp only [withReducedNat_eq] at h_act ⊢
        rw [Bool.and_assoc, Bool.and_eq_true, Bool.and_eq_true] at h_act
        have h_ih := callId_spec fuel rest ti
        rcases h_c : callId fuel rest ti with _ | ⟨f', a, rest', ti'⟩ | _ <;> rw [h_c] at h_ih
        · trivial
        · cases f'
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rcases h_lf : lf with _ | ⟨f, g, ci, b, t2⟩ <;> rw [h_lf] at h_act
            · trivial
            · dsimp only [checkLOpt, withReducedNat_eq] at h_act ⊢
              have hs := checkSeg2B_spec h_act.2.1
              simp only [bWord_append, bWord_powWB, bWord_wordB] at hs
              have h_j := hs.concat (walls false (n - j))
              have h_k := sideRL_of_sideRLs_one (h_j.sideRLs_concat (SideRLs.single h_ih))
              dsimp only [idSide]
              rw [← h_split_n, pow_add_list W (b + (n - j)) a, pow_add_list W b (n - j)]
              simpa only [Longitudinal.append_assoc] using h_k
          · simp only [↓reduceIte]
            rcases h_lt : lt with _ | ⟨f, g, ci, b, t2⟩ <;> rw [h_lt] at h_act
            · trivial
            · dsimp only [checkLOpt, withReducedNat_eq] at h_act ⊢
              have hs := checkSeg2B_spec h_act.2.2
              simp only [bWord_append, bWord_powWB, bWord_wordB] at hs
              have h_j := hs.concat (walls true (n - j))
              have h_k := sideRL_of_sideRLs_one (h_j.sideRLs_concat (SideRLs.single h_ih))
              dsimp only [idSide]
              rw [← h_split_n, pow_add_list W (b + (n - j)) a, pow_add_list W b (n - j)]
              simpa only [Longitudinal.append_assoc] using h_k
        · dsimp only
          intro l
          have h_pass := checkRightB_spec h_act.1 l (W ^ (n - j) +> idSide rest ti)
          simp only [bWord_append, bWord_powWB, bWord_wordB] at h_pass
          dsimp only [idSide]
          rw [← h_split_n]
          exact haltsFrom_of_stepStar h_pass
            (haltsFrom_of_stepStar
              (passW (n - j) (bWord (decodeBits xl xb) +> l) (idSide rest ti)) (h_ih _))
      · dsimp only
        cases h_ble : Nat.ble n 12
        · trivial
        · have hn12 : n ≤ 12 := Nat.ble_eq.mp h_ble
          rcases rest with _ | ⟨⟨w2i, n2⟩, rest2⟩
          · dsimp only
            cases h_lt : Nat.blt ti 512
            · trivial
            · rcases h_m : mergeTree.get? ((wi * 16 + n) * 512 + ti) with _ | wmi
              · trivial
              · dsimp only
                have hm_ok := Bst.allB_spec mergeTree all_merge_ok _ wmi h_m
                obtain ⟨hm1, hm2, hm3⟩ := div_mod_merge wi n ti hn12 (Nat.blt_eq.mp h_lt)
                dsimp only [checkMergeRule] at hm_ok
                rw [hm1, hm2, hm3] at hm_ok
                have h_weq : wordF wmi = wordF wi ++ W ^ n ++ wordF ti := by
                  have hb := (bWordEq_iff _ _).mp hm_ok
                  simp only [wordF, hb, bWord_append, bWord_powWB]
                have h_ih := callId_spec fuel [] wmi
                rcases h_c : callId fuel [] wmi with _ | _ | _ <;> rw [h_c] at h_ih
                · trivial
                · simpa only [↓reduceIte, idSide, h_weq, Longitudinal.append_assoc] using h_ih
                · simpa only [↓reduceIte, idSide, h_weq, Longitudinal.append_assoc] using h_ih
          · dsimp only
            cases h_lt : Nat.blt w2i 512
            · trivial
            · rcases h_m : mergeTree.get? ((wi * 16 + n) * 512 + w2i) with _ | wmi
              · trivial
              · dsimp only
                have hm_ok := Bst.allB_spec mergeTree all_merge_ok _ wmi h_m
                obtain ⟨hm1, hm2, hm3⟩ := div_mod_merge wi n w2i hn12 (Nat.blt_eq.mp h_lt)
                dsimp only [checkMergeRule] at hm_ok
                rw [hm1, hm2, hm3] at hm_ok
                have h_weq : wordF wmi = wordF wi ++ W ^ n ++ wordF w2i := by
                  have hb := (bWordEq_iff _ _).mp hm_ok
                  simp only [wordF, hb, bWord_append, bWord_powWB]
                have h_ih := callId_spec fuel ((wmi, n2) :: rest2) ti
                rcases h_c : callId fuel ((wmi, n2) :: rest2) ti with _ | _ | _ <;>
                  rw [h_c] at h_ih
                · trivial
                · simpa only [↓reduceIte, idSide, h_weq, Longitudinal.append_assoc] using h_ih
                · simpa only [↓reduceIte, idSide, h_weq, Longitudinal.append_assoc] using h_ih
      · dsimp only
        intro l
        have hh := checkHaltB_spec h_act l (W ^ (n - j) +> idSide rest ti)
        simp only [bWord_append, bWord_powWB, bWord_wordB] at hh
        dsimp only [idSide]
        rwa [h_split_n] at hh

/-! ## Left Wall Transitions and Top-Level Schedule Runner -/

private def wlWordB : List Bool :=
  [true, true, true, true, true, false, true, false, true, false, true]

private def wlWord : List (Fin 2) := bWord wlWordB

private def wl : ListBlank (Fin 2) := wlWord +> default

private def startCfg (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ([1, 0, 1, 0] +> wl) {{B}}> r

private def newcellB : List Bool :=
  [false, false, true, false, false, true, true, true, false]

private def newcell : List (Fin 2) := bWord newcellB

private theorem wordF_zero : wordF 0 = [] := by
  decide

private theorem wordF_one : wordF 1 = newcell := by
  decide

private theorem emitE (r : ListBlank (Fin 2)) : (wl <{{E}} r) [tm]⊢* startCfg r := by
  have hf : stepsFlipExactB 93 ⟨[], wlWordB, 4, true⟩ =
      some ⟨[true, false, true, false] ++ wlWordB, [], 1, false⟩ := by decide
  have h := stepsFlipExactB_spec 93 _ _ hf r
  have h_unflip := stepStar_flipTM h
  rw [flipTM_flipTM] at h_unflip
  simpa only [BCfgB.toCfg, bState, bWord_nil, bWord_1010, bWord_append, flipCfg_headLeft,
    flipCfg_headRight, Longitudinal.append_nil, Longitudinal.append_assoc, wlWord, wl,
    startCfg] using h_unflip

private theorem emitF (r : ListBlank (Fin 2)) :
    (wl <{{F}} ([0, 0] +> r)) [tm]⊢* startCfg (newcell +> r) := by
  have hf : stepsFlipExactB 264 ⟨[false, false], wlWordB, 5, true⟩ =
      some ⟨[true, false, true, false] ++ wlWordB, newcellB, 1, false⟩ := by decide
  have h := stepsFlipExactB_spec 264 _ _ hf r
  have h_unflip := stepStar_flipTM h
  rw [flipTM_flipTM] at h_unflip
  simpa only [BCfgB.toCfg, bState, bWord_00, bWord_1010, bWord_append, flipCfg_headLeft,
    flipCfg_headRight, Longitudinal.append_assoc, wlWord, wl, newcell, startCfg] using h_unflip

private theorem init_reaches_start : (init []) [tm]⊢* startCfg default := by
  have hf : stepsExactBoth0infB 138 ⟨[], [], 0, true⟩ =
      some ⟨[true, false, true, false] ++ wlWordB, [], 1, true⟩ := by decide
  have h := stepsExactBoth0infB_spec 138 _ _ hf
  have h_lhs : (⟨[], [], 0, true⟩ : BCfgB).toCfg default default = init [] := rfl
  rw [h_lhs] at h
  simpa only [BCfgB.toCfg, bState, bWord_nil, bWord_1010, bWord_append,
    Longitudinal.append_nil, Longitudinal.append_assoc, wlWord, wl, startCfg] using h

private theorem calls :
    ∀ (t : ℕ) (r r' : ListBlank (Fin 2)),
      SideRLs tm (hSig ^ t) r r' → (startCfg r) [tm]⊢* startCfg r'
  | 0, _, _, h => by
    cases h
    exact stepStar_refl tm _
  | t + 1, r, r', h => by
    rw [pow_succ_list, hSig] at h
    cases h with
    | cons h₁ h₂ =>
      have h_step : (startCfg r) [tm]⊢* startCfg _ :=
        stepStar_trans (stepPlus_to_stepStar (h₁ wl)) (emitE _)
      exact stepStar_trans h_step (calls t _ r' h₂)

private def idConf (k : ℕ) (cs : IdCells) (ti : ℕ) : Cfg (Fin 2) (Fin 6) :=
  startCfg (W ^ k +> idSide cs ti)

private def runSched : List ℕ → ℕ → IdCells → ℕ → Bool
  | [], _, _, _ => false
  | t :: ts, k, cs, ti =>
    let (k₁, cs₁, ti₁) :=
      if Nat.blt 0 t then
        match batchId t cs ti with
        | some (e, cs', ti') =>
          withReducedNat (k + e) fun k' => (k', cs', ti')
        | none => (k, cs, ti)
      else
        (k, cs, ti)
    match callId 200 cs₁ ti₁ with
    | .back false a cs₂ ti₂ =>
      withReducedNat (k₁ + a) fun k₂ =>
      runSched ts k₂ cs₂ ti₂
    | .back true a cs₂ ti₂ =>
      withReducedNat (k₁ + a) fun k₂ =>
      runSched ts 0 ((1, k₂) :: cs₂) ti₂
    | .halted => true
    | .stuck => false

private theorem runSched_spec :
    ∀ ts k cs ti, runSched ts k cs ti = true → HaltsTm (idConf k cs ti)
  | [], _, _, _, h => by cases h
  | t :: ts, k, cs, ti, h => by
    dsimp only [runSched] at h
    have h_bstep :
        ∃ k₁ cs₁ ti₁,
          (if Nat.blt 0 t then
            match batchId t cs ti with
            | some (e, cs', ti') => withReducedNat (k + e) fun k' => (k', cs', ti')
            | none => (k, cs, ti)
          else (k, cs, ti)) = (k₁, cs₁, ti₁) ∧
          ((idConf k cs ti) [tm]⊢* idConf k₁ cs₁ ti₁) := by
      cases Nat.blt 0 t
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨k, cs, ti, rfl, stepStar_refl tm _⟩
      · simp only [↓reduceIte]
        rcases h_bt : batchId t cs ti with _ | ⟨e, cs', ti'⟩
        · exact ⟨k, cs, ti, rfl, stepStar_refl tm _⟩
        · dsimp only [withReducedNat_eq]
          refine ⟨k + e, cs', ti', rfl, ?_⟩
          have hb := batchId_spec t cs ti e cs' ti' h_bt
          have h_side := (SegRLs.wall_pow (wall k) t).sideRLs_concat hb
          have h_calls := calls t _ _ h_side
          dsimp only [idConf]
          rwa [pow_add_list W k e, Longitudinal.append_assoc]
    rcases h_bstep with ⟨k₁, cs₁, ti₁, h_eq, h_star⟩
    rw [h_eq] at h
    dsimp only at h
    have hc := callId_spec 200 cs₁ ti₁
    rcases h_cl : callId 200 cs₁ ti₁ with _ | ⟨_ | _, a, cs₂, ti₂⟩ | _ <;>
      rw [h_cl] at h hc <;> dsimp only [withReducedNat_eq] at h
    · cases h
    · refine haltsFrom_of_stepStar h_star (haltsFrom_of_stepStar ?_ (runSched_spec ts _ _ _ h))
      have h_side := (wall k₁).sideRLs_concat (SideRLs.single hc)
      have h_calls := calls 1 _ _ (by simpa only [pow_one_list] using h_side)
      dsimp only [idConf]
      rwa [pow_add_list W k₁ a, Longitudinal.append_assoc]
    · refine haltsFrom_of_stepStar h_star (haltsFrom_of_stepStar ?_ (runSched_spec ts _ _ _ h))
      have h_side := sideRL_of_sideRLs_one ((wallF k₁).sideRLs_concat (SideRLs.single hc))
      have h₁ := stepPlus_to_stepStar (h_side wl)
      dsimp only [toDHCfg, hR, hF] at h₁
      have h₂ := emitF (W ^ k₁ +> (W ^ a +> idSide cs₂ ti₂))
      dsimp only [idConf, startCfg, idSide]
      rw [wordF_one, pow_zero_list, Longitudinal.append_nil, pow_add_list W k₁ a,
        Longitudinal.append_assoc]
      exact stepStar_trans h₁ h₂
    · refine haltsFrom_of_stepStar h_star ?_
      dsimp only [idConf, startCfg]
      exact haltsFrom_of_stepStar (passW k₁ wl (idSide cs₁ ti₁)) (hc _)

private theorem sched_halts : runSched batchSchedule 0 [] 0 = true := by
  decide +kernel

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF` halts from the blank tape. -/
theorem is_halt : IsHalt target := by
  rw [← target_tm_eq_target, ← tm_eq_target]
  have h_halts := runSched_spec batchSchedule 0 [] 0 sched_halts
  have h_init_conf : idConf 0 [] 0 = startCfg default := by
    simp [idConf, idSide, wordF_zero]
  rw [h_init_conf] at h_halts
  exact haltsFrom_of_stepStar init_reaches_start h_halts

end

end BusyBeaver.M_1RB0LE_0RCHHH_1RD0LA_1RE0RA_0LF1LD_1LC1RF
