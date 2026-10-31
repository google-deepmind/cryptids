/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_HHH1LA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

@[simp] lemma zMz (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma z00 : Turing.ListBlank.cons (0 : Fin 2) default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = Turing.ListBlank.cons a (l +> s) := rfl
@[simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

lemma zSm (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z01 (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa (tm : Machine (Fin 2) (Fin 6)) (c_1 : Cfg (Fin 2) (Fin 6)) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zPs {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 : Cfg (Fin 2) (Fin 6)} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z02 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSp {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z03 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂

macro "finish" : tactic =>
  `(tactic| (try simp only [z00, zDh, zDt]) <;> exact ⟨0, rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
macro "execute" : tactic =>
  `(tactic| focus (repeat (first | finish | step)))

@[simp] lemma z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] lemma z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

lemma zLp_add {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n :=
  BusyBeaver.Longitudinal.pow_add_list l m n

lemma zLp_shift {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ^ n ++ l := by
  rw [Nat.add_comm 1 n, BusyBeaver.Longitudinal.pow_succ_list']

lemma z07 (l : zF) (n : Nat) (s : zB) : (l ^ (1 + n)) +> s = l +> ((l ^ n) +> s) := by
  rw [zLp', append_assoc]

lemma z09 (l : zF) (n : Nat) (s : zB) : (l ^ n) +> (l +> s) = (l ^ (1 + n)) +> s := by
  rw [zLp_shift, append_assoc]

-- State aliases mapping TM1 (A..F) to #687 (TM2)
abbrev qA : Fin 6 := 4
abbrev qB : Fin 6 := 2
abbrev qC : Fin 6 := 3
abbrev qD : Fin 6 := 5
abbrev qE : Fin 6 := 0
abbrev qF : Fin 6 := 1

abbrev Z : zF := [0, 0]
abbrev U : zF := [0, 1]
abbrev V : zF := [1, 0]
abbrev O : zF := [1, 1]

inductive DState where
  | AL | BR | CR | DL | EL | ER | FL | FR
  deriving DecidableEq, Repr

def dstateToCfg (q : DState) (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  match q with
  | .AL => l <{{qA}} r
  | .BR => l {{qB}}> r
  | .CR => l {{qC}}> r
  | .DL => l <{{qD}} r
  | .EL => l <{{qE}} r
  | .ER => l {{qE}}> r
  | .FL => l <{{qF}} r
  | .FR => l {{qF}}> r

def bitToSym (b : Bool) : Fin 2 := if b then 1 else 0

@[simp] lemma bitToSym_false : bitToSym false = 0 := rfl
@[simp] lemma bitToSym_true : bitToSym true = 1 := rfl

def evalBoolList : List Bool → zB → zB
  | [], tail => tail
  | b :: bs, tail => Turing.ListBlank.cons (bitToSym b) (evalBoolList bs tail)

@[simp] lemma evalBoolList_nil (tail : zB) : evalBoolList [] tail = tail := rfl
@[simp] lemma evalBoolList_cons (b : Bool) (bs : List Bool) (tail : zB) :
    evalBoolList (b :: bs) tail = Turing.ListBlank.cons (bitToSym b) (evalBoolList bs tail) := rfl

def pushBool (w : Bool) (xs : List Bool) : List Bool :=
  match w, xs with
  | false, [] => []
  | _, _ => w :: xs

@[simp] lemma eval_pushBool (w : Bool) (xs : List Bool) :
    evalBoolList (pushBool w xs) default = Turing.ListBlank.cons (bitToSym w) (evalBoolList xs default) := by
  cases w <;> cases xs <;> simp [pushBool]

-- 1. Direct-matching Raw step evaluator on List Bool (no intermediate tuple projections!)
def rawSteps (r_def : Bool) : Nat → DState → List Bool → List Bool → DState × List Bool × List Bool
  | 0, q, l, r => (q, l, r)
  | n + 1, q, l, r =>
    match q with
    | .AL =>
      match l with
      | [] => rawSteps r_def n .BR [true] r
      | false :: l' => rawSteps r_def n .BR (true :: l') r
      | true :: l' => rawSteps r_def n .DL l' (true :: r)
    | .BR =>
      match r with
      | [] => if r_def then rawSteps r_def n .CR (pushBool false l) [] else (q, l, r)
      | false :: r' => rawSteps r_def n .CR (pushBool false l) r'
      | true :: r' => rawSteps r_def n .CR (true :: l) r'
    | .CR =>
      match r with
      | [] => if r_def then rawSteps r_def n .AL l [true] else (q, l, r)
      | false :: r' => rawSteps r_def n .AL l (true :: r')
      | true :: r' => rawSteps r_def n .ER (true :: l) r'
    | .DL =>
      match l with
      | true :: l' => rawSteps r_def n .EL l' (true :: r)
      | _ => (q, l, r)
    | .EL =>
      match l with
      | [] => rawSteps r_def n .FR [true] r
      | false :: l' => rawSteps r_def n .FR (true :: l') r
      | true :: l' => rawSteps r_def n .CR (pushBool false l') r
    | .ER =>
      match r with
      | [] => if r_def then rawSteps r_def n .FR (true :: l) [] else (q, l, r)
      | false :: r' => rawSteps r_def n .FR (true :: l) r'
      | true :: r' => rawSteps r_def n .CR (pushBool false l) r'
    | .FL =>
      match l with
      | [] => rawSteps r_def n .BR [] r
      | false :: l' => rawSteps r_def n .BR (false :: l') r
      | true :: l' => rawSteps r_def n .FL l' (if r_def then pushBool false r else false :: r)
    | .FR =>
      match r with
      | [] => if r_def then rawSteps r_def n .BR (pushBool false l) [] else (q, l, r)
      | false :: r' => rawSteps r_def n .BR (pushBool false l) r'
      | true :: r' => rawSteps r_def n .FL l (if r_def then pushBool false r' else false :: r')

lemma rawSteps_false_sound (n : Nat) (q : DState) (l r : List Bool) (r_tail : zB) :
    (dstateToCfg q (evalBoolList l default) (evalBoolList r r_tail)) [target_tm]⊢*
      (dstateToCfg (rawSteps false n q l r).1 (evalBoolList (rawSteps false n q l r).2.1 default)
        (evalBoolList (rawSteps false n q l r).2.2 r_tail)) := by
  induction n generalizing q l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    cases q with
    | AL =>
      cases l with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR [true] r)
      | cons b l' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR (true :: l') r)
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .DL l' (true :: r))
    | BR =>
      cases r with
      | nil => exact ⟨0, rfl⟩
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l) r')
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .CR (true :: l) r')
    | CR =>
      cases r with
      | nil => exact ⟨0, rfl⟩
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .AL l (true :: r'))
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .ER (true :: l) r')
    | DL =>
      cases l with
      | nil => exact ⟨0, rfl⟩
      | cons b l' =>
        cases b
        · exact ⟨0, rfl⟩
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .EL l' (true :: r))
    | EL =>
      cases l with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR [true] r)
      | cons b l' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR (true :: l') r)
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l') r)
    | ER =>
      cases r with
      | nil => exact ⟨0, rfl⟩
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR (true :: l) r')
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l) r')
    | FL =>
      cases l with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR [] r)
      | cons b l' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR (false :: l') r)
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .FL l' (false :: r))
    | FR =>
      cases r with
      | nil => exact ⟨0, rfl⟩
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .BR (pushBool false l) r')
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .FL l (false :: r'))

lemma rawSteps_true_sound (n : Nat) (q : DState) (l r : List Bool) :
    (dstateToCfg q (evalBoolList l default) (evalBoolList r default)) [target_tm]⊢*
      (dstateToCfg (rawSteps true n q l r).1 (evalBoolList (rawSteps true n q l r).2.1 default)
        (evalBoolList (rawSteps true n q l r).2.2 default)) := by
  induction n generalizing q l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    cases q with
    | AL =>
      cases l with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR [true] r)
      | cons b l' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR (true :: l') r)
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .DL l' (true :: r))
    | BR =>
      cases r with
      | nil => exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l) [])
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l) r')
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .CR (true :: l) r')
    | CR =>
      cases r with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .AL l [true])
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .AL l (true :: r'))
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .ER (true :: l) r')
    | DL =>
      cases l with
      | nil => exact ⟨0, rfl⟩
      | cons b l' =>
        cases b
        · exact ⟨0, rfl⟩
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .EL l' (true :: r))
    | EL =>
      cases l with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR [true] r)
      | cons b l' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR (true :: l') r)
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l') r)
    | ER =>
      cases r with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR (true :: l) [])
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .FR (true :: l) r')
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .CR (pushBool false l) r')
    | FL =>
      cases l with
      | nil => exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR [] r)
      | cons b l' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; execute) (ih .BR (false :: l') r)
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .FL l' (pushBool false r))
    | FR =>
      cases r with
      | nil => exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .BR (pushBool false l) [])
      | cons b r' =>
        cases b
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .BR (pushBool false l) r')
        · exact zSt (by dsimp [dstateToCfg]; rw [eval_pushBool]; execute) (ih .FL l (pushBool false r'))

-- 2. Symbolic & Concrete Macro Evaluator (parameterized over abstract `l_tail : zB`)
inductive SymElem where
  | bit (b : Bool)
  | blk (b1 b2 : Bool) (v : Nat)
  deriving DecidableEq, Repr

def pairWord (b1 b2 : Bool) : zF := [bitToSym b1, bitToSym b2]

def evalSideWith (vars : Nat → Nat) (tail : zB) : List SymElem → zB
  | [] => tail
  | .bit b :: xs => Turing.ListBlank.cons (bitToSym b) (evalSideWith vars tail xs)
  | .blk b1 b2 v :: xs => (pairWord b1 b2 ^ (vars v)) +> evalSideWith vars tail xs

@[simp] lemma evalSideWith_nil (vars : Nat → Nat) (tail : zB) :
    evalSideWith vars tail [] = tail := rfl
@[simp] lemma evalSideWith_bit (vars : Nat → Nat) (tail : zB) (b : Bool) (xs : List SymElem) :
    evalSideWith vars tail (.bit b :: xs) = Turing.ListBlank.cons (bitToSym b) (evalSideWith vars tail xs) := rfl
@[simp] lemma evalSideWith_blk (vars : Nat → Nat) (tail : zB) (b1 b2 : Bool) (v : Nat) (xs : List SymElem) :
    evalSideWith vars tail (.blk b1 b2 v :: xs) = (pairWord b1 b2 ^ (vars v)) +> evalSideWith vars tail xs := rfl

def push (w : Bool) (xs : List SymElem) : List SymElem :=
  match w, xs with
  | false, [] => []
  | _, _ => .bit w :: xs

@[simp] lemma eval_push_false (vars : Nat → Nat) (xs : List SymElem) :
    evalSideWith vars default (push false xs) = Turing.ListBlank.cons 0 (evalSideWith vars default xs) := by
  cases xs <;> simp [push]

def push_sym (b1 b2 : Bool) (v : Nat) : List SymElem → List SymElem
  | .bit b :: xs =>
    if b == b1 then .bit b1 :: push_sym b2 b1 v xs
    else .blk b1 b2 v :: .bit b :: xs
  | xs => .blk b1 b2 v :: xs

lemma rot_pair (b1 b2 : Bool) (k : Nat) (r : zB) :
    ([bitToSym b1] : zF) +> ((pairWord b2 b1 ^ k) +> r) =
      (pairWord b1 b2 ^ k) +> ([bitToSym b1] +> r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 (pairWord b2 b1) k r, z07 (pairWord b1 b2) k ([bitToSym b1] +> r)]
    simp only [pairWord, append_cons, append_nil] at ih ⊢
    rw [ih]

lemma eval_push_sym (vars : Nat → Nat) (tail : zB) (b1 b2 : Bool) (v : Nat) (xs : List SymElem) :
    evalSideWith vars tail (push_sym b1 b2 v xs) =
      (pairWord b1 b2 ^ (vars v)) +> evalSideWith vars tail xs := by
  induction xs generalizing b1 b2 with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | bit b =>
      dsimp [push_sym]
      split_ifs with h
      · have hb : b = b1 := by simpa using h
        subst hb
        simp only [evalSideWith_bit, ih b2 b]
        exact rot_pair b b2 (vars v) (evalSideWith vars tail xs)
      · rfl
    | blk c1 c2 w => rfl

-- Shift rules SR1..SR4
lemma shiftR_E_O_step (l r : zB) :
    (l {{qE}}> (O +> r)) [target_tm]⊢* ((V +> l) {{qE}}> r) := by
  simp only [O, V, append_cons, append_nil]
  execute

lemma shiftR_E_O (k : Nat) (l r : zB) :
    (l {{qE}}> ((O ^ k) +> r)) [target_tm]⊢* (((V ^ k) +> l) {{qE}}> r) := by
  induction k generalizing l with
  | zero => simp only [z05, append_nil]; finish
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 O k r]
    refine zSt (shiftR_E_O_step l ((O ^ k) +> r)) ?_
    simpa only [z09 V k l] using ih (V +> l)

lemma shiftR_C_O_step (l r : zB) :
    (l {{qC}}> (O +> r)) [target_tm]⊢* ((U +> l) {{qC}}> r) := by
  simp only [O, U, append_cons, append_nil]
  execute

lemma shiftR_C_O (k : Nat) (l r : zB) :
    (l {{qC}}> ((O ^ k) +> r)) [target_tm]⊢* (((U ^ k) +> l) {{qC}}> r) := by
  induction k generalizing l with
  | zero => simp only [z05, append_nil]; finish
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 O k r]
    refine zSt (shiftR_C_O_step l ((O ^ k) +> r)) ?_
    simpa only [z09 U k l] using ih (U +> l)

lemma shiftL_F_V_step (l r : zB) :
    ((V +> l) <{{qF}} (Z +> r)) [target_tm]⊢* (l <{{qF}} (Z +> (O +> r))) := by
  simp only [V, Z, O, append_cons, append_nil]
  execute

lemma shiftL_F_V (k : Nat) (l r : zB) :
    (((V ^ k) +> l) <{{qF}} (Z +> r)) [target_tm]⊢* (l <{{qF}} (Z +> ((O ^ k) +> r))) := by
  induction k generalizing r with
  | zero => simp only [z05, append_nil]; finish
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 V k l]
    refine zSt (shiftL_F_V_step ((V ^ k) +> l) r) ?_
    simpa only [z09 O k r] using ih (O +> r)

lemma shiftL_F_U_step (l r : zB) :
    ((U +> l) <{{qF}} ([0, 0, 0] +> r)) [target_tm]⊢* (l <{{qF}} ([0, 0, 0] +> (O +> r))) := by
  simp only [U, O, append_cons, append_nil]
  execute

lemma shiftL_F_U (k : Nat) (l r : zB) :
    (((U ^ k) +> l) <{{qF}} ([0, 0, 0] +> r)) [target_tm]⊢* (l <{{qF}} ([0, 0, 0] +> ((O ^ k) +> r))) := by
  induction k generalizing r with
  | zero => simp only [z05, append_nil]; finish
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 U k l]
    refine zSt (shiftL_F_U_step ((U ^ k) +> l) r) ?_
    simpa only [z09 O k r] using ih (O +> r)

-- Fuel-bounded helper loops (k = 200 exceeds max list length < 150)
def f_shift_loop : Nat → List SymElem → List SymElem → List SymElem × List SymElem
  | k + 1, .bit true :: .bit false :: l, r => f_shift_loop k l (.bit true :: .bit true :: r)
  | _, l, r => (l, r)

lemma f_shift_loop_sound (k : Nat) (vars : Nat → Nat) (l_tail : zB) (l r : List SymElem) :
    ((evalSideWith vars l_tail l) <{{qF}} (Z +> evalSideWith vars default r)) [target_tm]⊢*
      ((evalSideWith vars l_tail (f_shift_loop k l r).1) <{{qF}}
        (Z +> evalSideWith vars default (f_shift_loop k l r).2)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rcases l with _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, l2⟩⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · dsimp [f_shift_loop]
      exact zSt (shiftL_F_V_step (evalSideWith vars l_tail l2) (evalSideWith vars default r))
        (ih l2 (.bit true :: .bit true :: r))
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩

def e_shift_m : Nat → Nat → List SymElem → Nat × List SymElem
  | k + 1, m, .bit true :: .bit true :: r => e_shift_m k (m + 1) r
  | _, m, r => (m, r)

lemma e_shift_m_sound (k : Nat) (l_tail : zB) (vars : Nat → Nat) (n_off m : Nat) (r : List SymElem) :
    (((V ^ (n_off + m)) +> l_tail) {{qE}}> (evalSideWith vars default r)) [target_tm]⊢*
      (((V ^ (n_off + (e_shift_m k m r).1)) +> l_tail) {{qE}}>
        (evalSideWith vars default (e_shift_m k m r).2)) := by
  induction k generalizing m r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rcases r with _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, r2⟩⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · dsimp [e_shift_m]
      have h1 := shiftR_E_O_step ((V ^ (n_off + m)) +> l_tail) (evalSideWith vars default r2)
      have h_eq : V +> ((V ^ (n_off + m)) +> l_tail) = (V ^ (n_off + (m + 1))) +> l_tail := by
        rw [← z07 V (n_off + m) l_tail, show 1 + (n_off + m) = n_off + (m + 1) by omega]
      rw [h_eq] at h1
      exact zSt h1 (ih (m + 1) r2)
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩

def c_ones_loop : Nat → List SymElem → List SymElem → List SymElem × List SymElem
  | k + 1, l, .bit true :: .bit true :: r => c_ones_loop k (.bit false :: .bit true :: l) r
  | _, l, r => (l, r)

lemma c_ones_loop_sound (k : Nat) (vars : Nat → Nat) (l_tail : zB) (l r : List SymElem) :
    ((evalSideWith vars l_tail l) {{qC}}> (evalSideWith vars default r)) [target_tm]⊢*
      ((evalSideWith vars l_tail (c_ones_loop k l r).1) {{qC}}>
        (evalSideWith vars default (c_ones_loop k l r).2)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rcases r with _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, r2⟩⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · dsimp [c_ones_loop]
      exact zSt (shiftR_C_O_step (evalSideWith vars l_tail l) (evalSideWith vars default r2))
        (ih (.bit false :: .bit true :: l) r2)
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩

def c_zeros_loop : Nat → List SymElem → List SymElem → List SymElem × List SymElem
  | k + 1, .bit false :: l, .bit false :: r => c_zeros_loop k (.bit true :: .bit true :: l) r
  | _, l, r => (l, r)

lemma c_zeros_step (l r : zB) :
    ((Turing.ListBlank.cons 0 l) {{qC}}> (Turing.ListBlank.cons 0 r)) [target_tm]⊢*
      ((Turing.ListBlank.cons 1 (Turing.ListBlank.cons 1 l)) {{qC}}> r) := by
  execute

lemma c_zeros_loop_sound (k : Nat) (vars : Nat → Nat) (l_tail : zB) (l r : List SymElem) :
    ((evalSideWith vars l_tail l) {{qC}}> (evalSideWith vars default r)) [target_tm]⊢*
      ((evalSideWith vars l_tail (c_zeros_loop k l r).1) {{qC}}>
        (evalSideWith vars default (c_zeros_loop k l r).2)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rcases l with _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, l2⟩
    · exact ⟨0, rfl⟩
    · rcases r with _ | ⟨⟨_ | _⟩ | ⟨_, _, _⟩, r2⟩
      · exact ⟨0, rfl⟩
      · dsimp [c_zeros_loop]
        exact zSt (c_zeros_step (evalSideWith vars l_tail l2) (evalSideWith vars default r2))
          (ih (.bit true :: .bit true :: l2) r2)
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩

def toSymCfg (l_tail : zB) (vars : Nat → Nat) (n_off : Nat) (q : DState) (m : Nat) (l r : List SymElem) : Cfg (Fin 2) (Fin 6) :=
  dstateToCfg q (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l) (evalSideWith vars default r)

def symMacroSteps : Nat → DState → Nat → List SymElem → List SymElem → DState × Nat × List SymElem × List SymElem
  | 0, q, m, l, r => (q, m, l, r)
  | n + 1, q, m, l, r =>
    match q with
    | .FL =>
      match r with
      | .bit false :: .bit false :: r_tail =>
        match l with
        | [] =>
          let (m', r') := e_shift_m 200 (m + 2) r_tail
          symMacroSteps n .ER m' [] r'
        | .bit true :: .bit false :: l2 =>
          let (l', r') := f_shift_loop 200 l2 (.bit true :: .bit true :: r_tail)
          symMacroSteps n .FL m l' (.bit false :: .bit false :: r')
        | .blk true false v :: l_rest =>
          symMacroSteps n .FL m l_rest (.bit false :: .bit false :: push_sym true true v r_tail)
        | .blk false true v :: l_rest =>
          match r_tail with
          | .bit false :: r_tail2 =>
            symMacroSteps n .FL m l_rest (.bit false :: .bit false :: .bit false :: push_sym true true v r_tail2)
          | _ => (q, m, l, r)
        | .bit false :: l_rest =>
          symMacroSteps n .BR m (.bit false :: l_rest) (.bit false :: .bit false :: r_tail)
        | .bit true :: l_rest =>
          symMacroSteps n .FL m l_rest (.bit false :: .bit false :: .bit false :: r_tail)
        | _ => (q, m, l, r)
      | _ =>
        match l with
        | .bit true :: l_rest => symMacroSteps n .FL m l_rest (push false r)
        | _ => (q, m, l, r)
    | .ER =>
      match r with
      | [] => symMacroSteps n .FR m (.bit true :: l) []
      | .bit false :: r_rest => symMacroSteps n .FR m (.bit true :: l) r_rest
      | .blk true true v :: r_rest =>
        symMacroSteps n .ER m (push_sym true false v l) r_rest
      | .bit true :: r_rest => symMacroSteps n .CR m (.bit false :: l) r_rest
      | _ => (q, m, l, r)
    | .CR =>
      match r with
      | [] => symMacroSteps n .AL m l [.bit true]
      | .bit false :: r_rest =>
        match l with
        | .bit false :: l_rest =>
          let (l', r') := c_zeros_loop 200 (.bit true :: .bit true :: l_rest) r_rest
          symMacroSteps n .CR m l' r'
        | _ => symMacroSteps n .AL m l (.bit true :: r_rest)
      | .bit true :: .bit true :: r_rest =>
        let (l', r') := c_ones_loop 200 (.bit false :: .bit true :: l) r_rest
        symMacroSteps n .CR m l' r'
      | .blk true true v :: r_rest =>
        symMacroSteps n .CR m (push_sym false true v l) r_rest
      | .bit true :: r_rest => symMacroSteps n .ER m (.bit true :: l) r_rest
      | _ => (q, m, l, r)
    | .BR =>
      match r with
      | [] => symMacroSteps n .CR m (.bit false :: l) []
      | .bit false :: r_rest => symMacroSteps n .CR m (.bit false :: l) r_rest
      | .bit true :: r_rest => symMacroSteps n .CR m (.bit true :: l) r_rest
      | _ => (q, m, l, r)
    | .AL =>
      match l with
      | .bit false :: l_rest => symMacroSteps n .BR m (.bit true :: l_rest) r
      | .bit true :: l_rest => symMacroSteps n .DL m l_rest (.bit true :: r)
      | _ => (q, m, l, r)
    | .FR =>
      match r with
      | [] => symMacroSteps n .BR m (.bit false :: l) []
      | .bit false :: r_rest => symMacroSteps n .BR m (.bit false :: l) r_rest
      | .bit true :: r_rest => symMacroSteps n .FL m l (push false r_rest)
      | _ => (q, m, l, r)
    | .EL =>
      match l, m with
      | [], m' + 1 => symMacroSteps n .CR m' [.bit false, .bit false] r
      | .bit false :: l_rest, _ => symMacroSteps n .FR m (.bit true :: l_rest) r
      | .bit true :: l_rest, _ => symMacroSteps n .CR m (.bit false :: l_rest) r
      | _, _ => (q, m, l, r)
    | .DL =>
      match l with
      | .bit true :: l_rest => symMacroSteps n .EL m l_rest (.bit true :: r)
      | _ => (q, m, l, r)

lemma bounce_empty_sound (l_tail : zB)
    (h_bounce : ∀ r_t : zB, (l_tail <{{qF}} (Turing.ListBlank.cons 0 (Turing.ListBlank.cons 0 r_t))) [target_tm]⊢*
      (((V ^ 2) +> l_tail) {{qE}}> r_t))
    (vars : Nat → Nat) (n_off m : Nat) (r_tail : List SymElem) :
    (toSymCfg l_tail vars n_off .FL m [] (.bit false :: .bit false :: r_tail)) [target_tm]⊢*
      (toSymCfg l_tail vars n_off .ER (e_shift_m 200 (m + 2) r_tail).1 [] (e_shift_m 200 (m + 2) r_tail).2) := by
  dsimp [toSymCfg, dstateToCfg]
  have h1 := shiftL_F_V (n_off + m) l_tail (evalSideWith vars default r_tail)
  have h2 := h_bounce ((O ^ (n_off + m)) +> evalSideWith vars default r_tail)
  have h3 := shiftR_E_O (n_off + m) ((V ^ 2) +> l_tail) (evalSideWith vars default r_tail)
  have h_eq : (V ^ (n_off + m)) +> ((V ^ 2) +> l_tail) = (V ^ (n_off + (m + 2))) +> l_tail := by
    rw [← append_assoc, ← zLp_add V (n_off + m) 2, Nat.add_assoc]
  rw [h_eq] at h3
  have h4 := e_shift_m_sound 200 l_tail vars n_off (m + 2) r_tail
  exact zSt h1 (zSt h2 (zSt h3 h4))

lemma fl_push_false_step (l_tail : zB) (vars : Nat → Nat) (n_off m : Nat) (l_rest r : List SymElem) :
    (toSymCfg l_tail vars n_off .FL m (.bit true :: l_rest) r) [target_tm]⊢*
      (toSymCfg l_tail vars n_off .FL m l_rest (push false r)) := by
  dsimp [toSymCfg, dstateToCfg]
  rw [eval_push_false]
  execute

lemma symMacroSteps_sound (l_tail : zB)
    (h_bounce : ∀ r_t : zB, (l_tail <{{qF}} (Turing.ListBlank.cons 0 (Turing.ListBlank.cons 0 r_t))) [target_tm]⊢*
      (((V ^ 2) +> l_tail) {{qE}}> r_t))
    (vars : Nat → Nat) (n_off k : Nat) (q : DState) (m : Nat) (l r : List SymElem) :
    (toSymCfg l_tail vars n_off q m l r) [target_tm]⊢*
      (toSymCfg l_tail vars n_off (symMacroSteps k q m l r).1 (symMacroSteps k q m l r).2.1
        (symMacroSteps k q m l r).2.2.1 (symMacroSteps k q m l r).2.2.2) := by
  induction k generalizing q m l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    cases q with
    | FL =>
      rcases r with _ | ⟨⟨_ | _⟩ | ⟨c1, c2, w⟩, _ | ⟨⟨_ | _⟩ | ⟨c3, c4, w2⟩, r_tail⟩⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest []) (ih .FL m l_rest (push false []))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest [.bit false]) (ih .FL m l_rest (push false [.bit false]))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact zSt (bounce_empty_sound l_tail h_bounce vars n_off m r_tail) (ih .ER (e_shift_m 200 (m + 2) r_tail).1 [] (e_shift_m 200 (m + 2) r_tail).2)
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute)
            (ih .BR m (.bit false :: l_rest) (.bit false :: .bit false :: r_tail))
        · rcases l_rest with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l2⟩
          · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute)
              (ih .FL m [] (.bit false :: .bit false :: .bit false :: r_tail))
          · exact zSt (zSt (shiftL_F_V_step (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l2)
              (evalSideWith vars default r_tail))
              (f_shift_loop_sound 200 vars ((V ^ (n_off + m)) +> l_tail) l2 (.bit true :: .bit true :: r_tail)))
              (ih .FL m (f_shift_loop 200 l2 (.bit true :: .bit true :: r_tail)).1
                (.bit false :: .bit false :: (f_shift_loop 200 l2 (.bit true :: .bit true :: r_tail)).2))
          · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute)
              (ih .FL m (.bit true :: l2) (.bit false :: .bit false :: .bit false :: r_tail))
          · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute)
              (ih .FL m (.blk b1 b2 v :: l2) (.bit false :: .bit false :: .bit false :: r_tail))
        · cases b1 <;> cases b2
          · exact ⟨0, rfl⟩
          · rcases r_tail with _ | ⟨⟨_ | _⟩ | ⟨c5, c6, w3⟩, r_tail2⟩
            · exact ⟨0, rfl⟩
            · refine zSt ?_ (ih .FL m l_rest (.bit false :: .bit false :: .bit false :: push_sym true true v r_tail2))
              dsimp [toSymCfg, dstateToCfg]
              rw [eval_push_sym]
              exact shiftL_F_U (vars v) (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l_rest)
                (evalSideWith vars default r_tail2)
            · exact ⟨0, rfl⟩
            · exact ⟨0, rfl⟩
          · refine zSt ?_ (ih .FL m l_rest (.bit false :: .bit false :: push_sym true true v r_tail))
            dsimp [toSymCfg, dstateToCfg]
            rw [eval_push_sym]
            exact shiftL_F_V (vars v) (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l_rest)
              (evalSideWith vars default r_tail)
          · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.bit false :: .bit true :: r_tail))
            (ih .FL m l_rest (push false (.bit false :: .bit true :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.bit false :: .blk c3 c4 w2 :: r_tail))
            (ih .FL m l_rest (push false (.bit false :: .blk c3 c4 w2 :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest [.bit true])
            (ih .FL m l_rest (push false [.bit true]))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.bit true :: .bit false :: r_tail))
            (ih .FL m l_rest (push false (.bit true :: .bit false :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.bit true :: .bit true :: r_tail))
            (ih .FL m l_rest (push false (.bit true :: .bit true :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.bit true :: .blk c3 c4 w2 :: r_tail))
            (ih .FL m l_rest (push false (.bit true :: .blk c3 c4 w2 :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest [.blk c1 c2 w])
            (ih .FL m l_rest (push false [.blk c1 c2 w]))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.blk c1 c2 w :: .bit false :: r_tail))
            (ih .FL m l_rest (push false (.blk c1 c2 w :: .bit false :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.blk c1 c2 w :: .bit true :: r_tail))
            (ih .FL m l_rest (push false (.blk c1 c2 w :: .bit true :: r_tail)))
        · exact ⟨0, rfl⟩
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact zSt (fl_push_false_step l_tail vars n_off m l_rest (.blk c1 c2 w :: .blk c3 c4 w2 :: r_tail))
            (ih .FL m l_rest (push false (.blk c1 c2 w :: .blk c3 c4 w2 :: r_tail)))
        · exact ⟨0, rfl⟩
    | ER =>
      rcases r with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, r_rest⟩
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .FR m (.bit true :: l) [])
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .FR m (.bit true :: l) r_rest)
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .CR m (.bit false :: l) r_rest)
      · cases b1 <;> cases b2
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · refine zSt ?_ (ih .ER m (push_sym true false v l) r_rest)
          dsimp [toSymCfg, dstateToCfg]
          rw [eval_push_sym]
          exact shiftR_E_O (vars v) (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l)
            (evalSideWith vars default r_rest)
    | CR =>
      rcases r with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, r_rest⟩
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .AL m l [.bit true])
      · rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .AL m [] (.bit true :: r_rest))
        · exact zSt (zSt (c_zeros_step (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l_rest)
            (evalSideWith vars default r_rest))
            (c_zeros_loop_sound 200 vars ((V ^ (n_off + m)) +> l_tail) (.bit true :: .bit true :: l_rest) r_rest))
            (ih .CR m (c_zeros_loop 200 (.bit true :: .bit true :: l_rest) r_rest).1
              (c_zeros_loop 200 (.bit true :: .bit true :: l_rest) r_rest).2)
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .AL m (.bit true :: l_rest) (.bit true :: r_rest))
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .AL m (.blk b1 b2 v :: l_rest) (.bit true :: r_rest))
      · rcases r_rest with _ | ⟨⟨_ | _⟩ | ⟨c1, c2, w⟩, r2⟩
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .ER m (.bit true :: l) [])
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .ER m (.bit true :: l) (.bit false :: r2))
        · exact zSt (zSt (shiftR_C_O_step (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l)
            (evalSideWith vars default r2))
            (c_ones_loop_sound 200 vars ((V ^ (n_off + m)) +> l_tail) (.bit false :: .bit true :: l) r2))
            (ih .CR m (c_ones_loop 200 (.bit false :: .bit true :: l) r2).1
              (c_ones_loop 200 (.bit false :: .bit true :: l) r2).2)
        · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .ER m (.bit true :: l) (.blk c1 c2 w :: r2))
      · cases b1 <;> cases b2
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
        · refine zSt ?_ (ih .CR m (push_sym false true v l) r_rest)
          dsimp [toSymCfg, dstateToCfg]
          rw [eval_push_sym]
          exact shiftR_C_O (vars v) (evalSideWith vars ((V ^ (n_off + m)) +> l_tail) l)
            (evalSideWith vars default r_rest)
    | BR =>
      rcases r with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, r_rest⟩
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .CR m (.bit false :: l) [])
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .CR m (.bit false :: l) r_rest)
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .CR m (.bit true :: l) r_rest)
      · exact ⟨0, rfl⟩
    | AL =>
      rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
      · exact ⟨0, rfl⟩
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .BR m (.bit true :: l_rest) r)
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .DL m l_rest (.bit true :: r))
      · exact ⟨0, rfl⟩
    | FR =>
      rcases r with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, r_rest⟩
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .BR m (.bit false :: l) [])
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .BR m (.bit false :: l) r_rest)
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; rw [eval_push_false]; execute) (ih .FL m l (push false r_rest))
      · exact ⟨0, rfl⟩
    | EL =>
      rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
      · cases m with
        | zero => exact ⟨0, rfl⟩
        | succ m' =>
          refine zSt ?_ (ih .CR m' [.bit false, .bit false] r)
          dsimp [toSymCfg, dstateToCfg]
          have h_eq : n_off + (m' + 1) = 1 + (n_off + m') := by omega
          rw [h_eq, z07 V (n_off + m') l_tail]
          simp only [V, append_cons, append_nil]
          execute
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .FR m (.bit true :: l_rest) r)
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .CR m (.bit false :: l_rest) r)
      · exact ⟨0, rfl⟩
    | DL =>
      rcases l with _ | ⟨⟨_ | _⟩ | ⟨b1, b2, v⟩, l_rest⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact zSt (by dsimp [toSymCfg, dstateToCfg]; execute) (ih .EL m l_rest (.bit true :: r))
      · exact ⟨0, rfl⟩

-- 3. Canonical Configurations `Kr`, `Ev`, and Symbolic Transitions
def l_G_core_bool : List Bool := [true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false, true, true]
def r_init_bool : List Bool := [false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, false, true, true]
def l_G_tail : zB := evalBoolList l_G_core_bool default

theorem raw_G_bounce_eq :
    rawSteps false 765 .FL l_G_core_bool [false, false] =
      (.ER, true :: false :: true :: false :: l_G_core_bool, []) := rfl

lemma G_bounce (r_t : zB) :
    (l_G_tail <{{qF}} (Turing.ListBlank.cons 0 (Turing.ListBlank.cons 0 r_t))) [target_tm]⊢*
      (((V ^ 2) +> l_G_tail) {{qE}}> r_t) := by
  have h := rawSteps_false_sound 765 .FL l_G_core_bool [false, false] r_t
  rw [raw_G_bounce_eq] at h
  exact h

theorem raw_init_eq :
    rawSteps true 6736 .ER [] [] =
      (.ER, true :: false :: true :: false :: l_G_core_bool, r_init_bool) := rfl

lemma symMacroSteps_sound_eq (vars : Nat → Nat) (n_off k : Nat)
    (q : DState) (m : Nat) (l r : List SymElem)
    (q' : DState) (m' : Nat) (l' r' : List SymElem)
    (heq : symMacroSteps k q m l r = (q', m', l', r')) :
    (toSymCfg l_G_tail vars n_off q m l r) [target_tm]⊢*
      (toSymCfg l_G_tail vars n_off q' m' l' r') := by
  have h := symMacroSteps_sound l_G_tail G_bounce vars n_off k q m l r
  rw [heq] at h
  exact h

lemma symMacroSteps_ER_plus (k : Nat) (vars : Nat → Nat) (n_off m : Nat) (r_rest : List SymElem)
    (q' : DState) (m' : Nat) (l' r' : List SymElem)
    (heq : symMacroSteps (k + 1) .ER m [] (.bit true :: .bit false :: r_rest) = (q', m', l', r')) :
    (toSymCfg l_G_tail vars n_off .ER m [] (.bit true :: .bit false :: r_rest)) [target_tm]⊢⁺
      (toSymCfg l_G_tail vars n_off q' m' l' r') := by
  have h : (toSymCfg l_G_tail vars n_off .ER m [] (.bit true :: .bit false :: r_rest)) [target_tm]⊢⁺
      (toSymCfg l_G_tail vars n_off
        (symMacroSteps (k + 1) .ER m [] (.bit true :: .bit false :: r_rest)).1
        (symMacroSteps (k + 1) .ER m [] (.bit true :: .bit false :: r_rest)).2.1
        (symMacroSteps (k + 1) .ER m [] (.bit true :: .bit false :: r_rest)).2.2.1
        (symMacroSteps (k + 1) .ER m [] (.bit true :: .bit false :: r_rest)).2.2.2) := by
    refine z02 ?_ (symMacroSteps_sound l_G_tail G_bounce vars n_off k .CR m [.bit false] (.bit false :: r_rest))
    dsimp [toSymCfg, dstateToCfg, evalSideWith, bitToSym]
    refine z03 (by simp only [Turing.ListBlank.head_cons, zDh]; rfl) ?_
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt]
    exact ⟨0, rfl⟩
  rw [heq] at h
  exact h

def repO : Nat → List SymElem → List SymElem
  | 0, xs => xs
  | k + 1, xs => .bit true :: .bit true :: repO k xs

def addVars : List Nat → List SymElem → List SymElem
  | [], xs => xs
  | v :: vs, xs => .blk true true v :: addVars vs xs

def addBits : List Bool → List SymElem → List SymElem
  | [], xs => xs
  | b :: bs, xs => .bit b :: addBits bs xs

def evalVarSum (vars : Nat → Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => vars v + evalVarSum vars vs

lemma eval_repO (vars : Nat → Nat) (tail : zB) (k : Nat) (xs : List SymElem) :
    evalSideWith vars tail (repO k xs) = (O ^ k) +> evalSideWith vars tail xs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [zLp O k, append_assoc]
    dsimp [repO, evalSideWith, O]
    rw [ih]

lemma eval_addVars (vars : Nat → Nat) (tail : zB) (vs : List Nat) (xs : List SymElem) :
    evalSideWith vars tail (addVars vs xs) =
      (O ^ (evalVarSum vars vs)) +> evalSideWith vars tail xs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change ((O ^ (vars v)) +> evalSideWith vars tail (addVars vs xs)) =
      (O ^ (vars v + evalVarSum vars vs)) +> evalSideWith vars tail xs
    rw [ih, ← append_assoc, ← zLp_add O (vars v) (evalVarSum vars vs)]

lemma eval_repO_addVars (vars : Nat → Nat) (tail : zB) (c : Nat) (vs : List Nat) (xs : List SymElem) :
    evalSideWith vars tail (repO c (addVars vs xs)) =
      (O ^ (c + evalVarSum vars vs)) +> evalSideWith vars tail xs := by
  rw [eval_repO, eval_addVars, ← append_assoc, ← zLp_add O c (evalVarSum vars vs)]

lemma eval_addBits (vars : Nat → Nat) (tail : zB) (bs : List Bool) (xs : List SymElem) :
    evalSideWith vars tail (addBits bs xs) = evalBoolList bs (evalSideWith vars tail xs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => dsimp [addBits, evalSideWith, evalBoolList]; rw [ih]

def seg0 : List Bool := [true, false]
def seg1 : List Bool := [false, true, true, false]
def seg2 : List Bool := [false, false, false, false, false, false, true]
def seg3 : List Bool := [false, true, true, false, true, true, true, true, false, false, false, false, false, false]
def seg4 : List Bool := [false, true, true, false, false, true, true, false, true, true, true]

def mkSymRTail (ca : Nat) (va : List Nat) (cb : Nat) (vb : List Nat)
    (cc : Nat) (vc : List Nat) (cd : Nat) (vd : List Nat) : List SymElem :=
  repO ca (addVars va
    (addBits seg1 (repO cb (addVars vb
      (addBits seg2 (repO cc (addVars vc
        (addBits seg3 (repO cd (addVars vd
          (addBits seg4 [])))))))))))

def mkSymR (ca : Nat) (va : List Nat) (cb : Nat) (vb : List Nat)
    (cc : Nat) (vc : List Nat) (cd : Nat) (vd : List Nat) : List SymElem :=
  .bit true :: .bit false :: mkSymRTail ca va cb vb cc vc cd vd

def r_kr_tail (a b c d : Nat) : zB :=
  evalBoolList seg0 ((O ^ a) +> evalBoolList seg1 ((O ^ b) +> evalBoolList seg2
    ((O ^ c) +> evalBoolList seg3 ((O ^ d) +> evalBoolList seg4 default))))

lemma eval_mkSymR (vars : Nat → Nat) (ca : Nat) (va : List Nat) (cb : Nat) (vb : List Nat)
    (cc : Nat) (vc : List Nat) (cd : Nat) (vd : List Nat) :
    evalSideWith vars default (mkSymR ca va cb vb cc vc cd vd) =
      r_kr_tail (ca + evalVarSum vars va) (cb + evalVarSum vars vb)
        (cc + evalVarSum vars vc) (cd + evalVarSum vars vd) := by
  change evalSideWith vars default (addBits seg0 (mkSymRTail ca va cb vb cc vc cd vd)) = _
  dsimp [mkSymRTail, r_kr_tail]
  simp only [eval_addBits, eval_repO_addVars, evalSideWith_nil]

def Kr (n a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((V ^ (n + 2)) +> l_G_tail) {{qE}}> r_kr_tail a b c d)

def Ev (N X : Nat) : Cfg (Fin 2) (Fin 6) :=
  Kr N (4 * X + 26) (2 * X + 32) 17 9

lemma toSymCfg_mkSymR (vars : Nat → Nat) (n k : Nat)
    (ca : Nat) (va : List Nat) (cb : Nat) (vb : List Nat)
    (cc : Nat) (vc : List Nat) (cd : Nat) (vd : List Nat) :
    toSymCfg l_G_tail vars n .ER (k + 2) [] (mkSymR ca va cb vb cc vc cd vd) =
      Kr (n + k) (ca + evalVarSum vars va) (cb + evalVarSum vars vb)
        (cc + evalVarSum vars vc) (cd + evalVarSum vars vd) := by
  unfold toSymCfg dstateToCfg Kr
  dsimp only [evalSideWith]
  rw [eval_mkSymR, Nat.add_assoc]

lemma symMacroSteps_mkSymR_plus (k : Nat) (vars : Nat → Nat) (n k_m : Nat)
    (ca : Nat) (va : List Nat) (cb : Nat) (vb : List Nat)
    (cc : Nat) (vc : List Nat) (cd : Nat) (vd : List Nat)
    (k_m' : Nat)
    (ca' : Nat) (va' : List Nat) (cb' : Nat) (vb' : List Nat)
    (cc' : Nat) (vc' : List Nat) (cd' : Nat) (vd' : List Nat)
    (n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 : Nat)
    (heq : symMacroSteps (k + 1) .ER (k_m + 2) [] (mkSymR ca va cb vb cc vc cd vd) =
      (.ER, k_m' + 2, [], mkSymR ca' va' cb' vb' cc' vc' cd' vd'))
    (hn1 : n + k_m = n1) (ha1 : ca + evalVarSum vars va = a1)
    (hb1 : cb + evalVarSum vars vb = b1) (hc1 : cc + evalVarSum vars vc = c1)
    (hd1 : cd + evalVarSum vars vd = d1)
    (hn2 : n + k_m' = n2) (ha2 : ca' + evalVarSum vars va' = a2)
    (hb2 : cb' + evalVarSum vars vb' = b2) (hc2 : cc' + evalVarSum vars vc' = c2)
    (hd2 : cd' + evalVarSum vars vd' = d2) :
    (Kr n1 a1 b1 c1 d1) [target_tm]⊢⁺ (Kr n2 a2 b2 c2 d2) := by
  subst hn1 ha1 hb1 hc1 hd1 hn2 ha2 hb2 hc2 hd2
  rw [← toSymCfg_mkSymR vars n k_m ca va cb vb cc vc cd vd]
  rw [← toSymCfg_mkSymR vars n k_m' ca' va' cb' vb' cc' vc' cd' vd']
  exact symMacroSteps_ER_plus k vars n (k_m + 2) (mkSymRTail ca va cb vb cc vc cd vd)
    .ER (k_m' + 2) [] (mkSymR ca' va' cb' vb' cc' vc' cd' vd') heq

def mkVars (a b c d : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

theorem sym_S_step_eq :
    symMacroSteps 1067 .ER 2 [] (mkSymR 5 [0] 3 [1] 3 [2] 1 [3]) =
      (.ER, 26, [], mkSymR 1 [0] 5 [1] 3 [2] 3 [3]) := rfl

lemma S_step (n a b c d : Nat) :
    (Kr n (5 + a) (3 + b) (3 + c) (1 + d)) [target_tm]⊢⁺
      (Kr (24 + n) (1 + a) (5 + b) (3 + c) (3 + d)) :=
  symMacroSteps_mkSymR_plus 1066 (mkVars a b c d) n 0
    5 [0] 3 [1] 3 [2] 1 [3] 24 1 [0] 5 [1] 3 [2] 3 [3]
    _ _ _ _ _ _ _ _ _ _ sym_S_step_eq
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)

theorem sym_TE_eq :
    symMacroSteps 11957 .ER 2 [] (mkSymR 2 [] 44 [1] 17 [] 10 [3]) =
      (.ER, 280, [], mkSymR 1 [1] 41 [] 35 [3] 9 []) := rfl

lemma TE (n b d : Nat) :
    (Kr n 2 (44 + b) 17 (10 + d)) [target_tm]⊢⁺
      (Kr (278 + n) (1 + b) 41 (35 + d) 9) :=
  symMacroSteps_mkSymR_plus 11956 (mkVars 0 b 0 d) n 0
    2 [] 44 [1] 17 [] 10 [3] 278 1 [1] 41 [] 35 [3] 9 []
    _ _ _ _ _ _ _ _ _ _ sym_TE_eq
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)

theorem sym_TO_eq :
    symMacroSteps 11792 .ER 2 [] (mkSymR 1 [] 41 [1] 18 [2] 9 [3]) =
      (.ER, 296, [], mkSymR 14 [1, 2] 40 [3] 17 [] 9 []) := rfl

lemma TO (n b c d : Nat) :
    (Kr n 1 (41 + b) (18 + c) (9 + d)) [target_tm]⊢⁺
      (Kr (294 + n) (14 + b + c) (40 + d) 17 9) :=
  symMacroSteps_mkSymR_plus 11791 (mkVars 0 b c d) n 0
    1 [] 41 [1] 18 [2] 9 [3] 294 14 [1, 2] 40 [3] 17 [] 9 []
    _ _ _ _ _ _ _ _ _ _ sym_TO_eq
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)

theorem sym_T6_eq :
    symMacroSteps 11927 .ER 2 [] (mkSymR 3 [] 41 [1] 17 [2] 9 [3]) =
      (.ER, 298, [], mkSymR 13 [1, 2] 40 [3] 17 [] 9 []) := rfl

lemma T6 (n b c d : Nat) :
    (Kr n 3 (41 + b) (17 + c) (9 + d)) [target_tm]⊢⁺
      (Kr (296 + n) (13 + b + c) (40 + d) 17 9) :=
  symMacroSteps_mkSymR_plus 11926 (mkVars 0 b c d) n 0
    3 [] 41 [1] 17 [2] 9 [3] 296 13 [1, 2] 40 [3] 17 [] 9 []
    _ _ _ _ _ _ _ _ _ _ sym_T6_eq
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)

theorem sym_T8_eq :
    symMacroSteps 11689 .ER 2 [] (mkSymR 4 [] 44 [1] 17 [] 10 [3]) =
      (.ER, 272, [], mkSymR 7 [1] 43 [] 33 [3] 9 []) := rfl

lemma T8 (n b d : Nat) :
    (Kr n 4 (44 + b) 17 (10 + d)) [target_tm]⊢⁺
      (Kr (270 + n) (7 + b) 43 (33 + d) 9) :=
  symMacroSteps_mkSymR_plus 11688 (mkVars 0 b 0 d) n 0
    4 [] 44 [1] 17 [] 10 [3] 270 7 [1] 43 [] 33 [3] 9 []
    _ _ _ _ _ _ _ _ _ _ sym_T8_eq
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)
    (by omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega) (by simp only [evalVarSum, mkVars]; try omega)
    (by simp only [evalVarSum, mkVars]; try omega)

lemma follow_Kr_plus {n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 n1' a1' b1' c1' d1' : Nat} {c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : (Kr n1 a1 b1 c1 d1) [target_tm]⊢⁺ (Kr n2 a2 b2 c2 d2))
    (hn : n1 = n1') (ha : a1 = a1') (hb : b1 = b1') (hc : c1 = c1') (hd : d1 = d1')
    (h2 : (Kr n2 a2 b2 c2 d2) [target_tm]⊢* c3) :
    (Kr n1' a1' b1' c1' d1') [target_tm]⊢* c3 := by
  subst hn ha hb hc hd
  exact zPs (z02 h1 h2)

lemma follow_Kr_star {n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 n1' a1' b1' c1' d1' : Nat} {c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : (Kr n1 a1 b1 c1 d1) [target_tm]⊢* (Kr n2 a2 b2 c2 d2))
    (hn : n1 = n1') (ha : a1 = a1') (hb : b1 = b1') (hc : c1 = c1') (hd : d1 = d1')
    (h2 : (Kr n2 a2 b2 c2 d2) [target_tm]⊢* c3) :
    (Kr n1' a1' b1' c1' d1') [target_tm]⊢* c3 := by
  subst hn ha hb hc hd
  exact zSt h1 h2

lemma finish_Kr {n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 : Nat}
    (hn : n1 = n2) (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
    (Kr n1 a1 b1 c1 d1) [target_tm]⊢* (Kr n2 a2 b2 c2 d2) := by
  subst hn ha hb hc hd
  exact ⟨0, rfl⟩

lemma follow_Kr_star_plus {n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 n1' a1' b1' c1' d1' : Nat} {c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : (Kr n1 a1 b1 c1 d1) [target_tm]⊢* (Kr n2 a2 b2 c2 d2))
    (hn : n1 = n1') (ha : a1 = a1') (hb : b1 = b1') (hc : c1 = c1') (hd : d1 = d1')
    (h2 : (Kr n2 a2 b2 c2 d2) [target_tm]⊢⁺ c3) :
    (Kr n1' a1' b1' c1' d1') [target_tm]⊢⁺ c3 := by
  subst hn ha hb hc hd
  exact zSp h1 h2

lemma follow_Kr_plus_plus {n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 n1' a1' b1' c1' d1' : Nat} {c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : (Kr n1 a1 b1 c1 d1) [target_tm]⊢⁺ (Kr n2 a2 b2 c2 d2))
    (hn : n1 = n1') (ha : a1 = a1') (hb : b1 = b1') (hc : c1 = c1') (hd : d1 = d1')
    (h2 : (Kr n2 a2 b2 c2 d2) [target_tm]⊢⁺ c3) :
    (Kr n1' a1' b1' c1' d1') [target_tm]⊢⁺ c3 := by
  subst hn ha hb hc hd
  exact zPt h1 h2

lemma finish_Kr_plus {n1 a1 b1 c1 d1 n2 a2 b2 c2 d2 n1' a1' b1' c1' d1' n2' a2' b2' c2' d2' : Nat}
    (h1 : (Kr n1 a1 b1 c1 d1) [target_tm]⊢⁺ (Kr n2 a2 b2 c2 d2))
    (hn1 : n1 = n1') (ha1 : a1 = a1') (hb1 : b1 = b1') (hc1 : c1 = c1') (hd1 : d1 = d1')
    (hn2 : n2 = n2') (ha2 : a2 = a2') (hb2 : b2 = b2') (hc2 : c2 = c2') (hd2 : d2 = d2') :
    (Kr n1' a1' b1' c1' d1') [target_tm]⊢⁺ (Kr n2' a2' b2' c2' d2') := by
  subst hn1 ha1 hb1 hc1 hd1 hn2 ha2 hb2 hc2 hd2
  exact h1

lemma S_iter (k : Nat) : ∀ n a b c d : Nat,
    (Kr n (4 * k + 1 + a) (3 + b) (3 + c) (1 + d)) [target_tm]⊢*
      (Kr (24 * k + n) (1 + a) (2 * k + 3 + b) (3 + c) (2 * k + 1 + d)) := by
  induction k with
  | zero =>
    intro n a b c d
    exact finish_Kr (by omega) (by omega) (by omega) (by omega) (by omega)
  | succ k ih =>
    intro n a b c d
    refine follow_Kr_plus (S_step n (4 * k + a) b c d) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    refine follow_Kr_star (ih (24 + n) a (2 + b) c (2 + d)) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    exact finish_Kr (by omega) (by omega) (by omega) (by omega) (by omega)

lemma DC (N X : Nat) :
    (Ev N X) [target_tm]⊢⁺ (Ev (48 * X + 716 + N) (4 + X)) := by
  unfold Ev
  refine follow_Kr_star_plus (S_iter (X + 6) N 1 (2 * X + 29) 14 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus_plus (TE (24 * (X + 6) + N) (4 * X) (2 * X + 11)) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star_plus (S_iter X (278 + (24 * (X + 6) + N)) 0 38 (2 * X + 43) 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  exact finish_Kr_plus (TO (24 * X + (278 + (24 * (X + 6) + N))) (2 * X) (2 * X + 28) (2 * X))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)

lemma rawSteps_true_sound_eq (n : Nat) (q : DState) (l r : List Bool)
    (q' : DState) (l' r' : List Bool)
    (heq : rawSteps true n q l r = (q', l', r')) :
    (dstateToCfg q (evalBoolList l default) (evalBoolList r default)) [target_tm]⊢*
      (dstateToCfg q' (evalBoolList l' default) (evalBoolList r' default)) := by
  have h := rawSteps_true_sound n q l r
  rw [heq] at h
  exact h

theorem sym_init_eq :
    symMacroSteps 42693 .ER 2 [] (addBits r_init_bool []) =
      (.ER, 1293, [], mkSymR 35 [] 38 [] 21 [] 9 []) := rfl

lemma init_to_Kr : (init []) [target_tm]⊢* (Kr 1291 35 38 21 9) := by
  have h1 := rawSteps_true_sound_eq 6736 .ER [] []
    .ER (true :: false :: true :: false :: l_G_core_bool) r_init_bool raw_init_eq
  have h2 := symMacroSteps_sound_eq (mkVars 0 0 0 0) 0 42693
    .ER 2 [] (addBits r_init_bool [])
    .ER 1293 [] (mkSymR 35 [] 38 [] 21 [] 9 []) sym_init_eq
  have h12 : (dstateToCfg .ER (evalBoolList [] default) (evalBoolList [] default)) [target_tm]⊢*
      (toSymCfg l_G_tail (mkVars 0 0 0 0) 0 .ER 1293 [] (mkSymR 35 [] 38 [] 21 [] 9 [])) := by
    refine zSt h1 ?_
    have heq : dstateToCfg .ER (evalBoolList (true :: false :: true :: false :: l_G_core_bool) default) (evalBoolList r_init_bool default) =
        toSymCfg l_G_tail (mkVars 0 0 0 0) 0 .ER 2 [] (addBits r_init_bool []) := by
      unfold toSymCfg dstateToCfg
      rw [eval_addBits]
      rfl
    rw [heq]
    exact h2
  have h3 := toSymCfg_mkSymR (mkVars 0 0 0 0) 0 1291 35 [] 38 [] 21 [] 9 []
  dsimp [evalVarSum] at h3
  rw [h3] at h12
  exact h12

lemma opening : (Kr 1291 35 38 21 9) [target_tm]⊢* (Ev 6649 21) := by
  unfold Ev
  refine follow_Kr_star (S_iter 8 1291 2 35 18 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (T6 1483 13 4 16) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 7 1779 1 53 14 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (TE 1947 26 13) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 6 2225 2 38 45 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (T6 2369 12 31 12) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 13 2665 3 49 14 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (T8 2977 34 25) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 10 3247 0 40 55 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (TO 3487 22 40 20) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 18 3781 3 57 14 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (T8 4213 52 35) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 14 4483 2 40 65 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (T6 4819 30 51 28) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 23 5115 1 65 14 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (TE 5667 70 45) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_star (S_iter 17 5945 2 38 77 8) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  refine follow_Kr_plus (T6 6353 34 63 34) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  exact finish_Kr (by omega) (by omega) (by omega) (by omega) (by omega)

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ N X, c = Ev N X)
    ⟨Ev 6649 21, zSt init_to_Kr opening, 6649, 21, rfl⟩ ?_
  rintro _ ⟨N, X, rfl⟩
  exact ⟨Ev (48 * X + 716 + N) (4 + X), DC N X, 48 * X + 716 + N, 4 + X, rfl⟩

end BusyBeaver.M_1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_HHH1LA
