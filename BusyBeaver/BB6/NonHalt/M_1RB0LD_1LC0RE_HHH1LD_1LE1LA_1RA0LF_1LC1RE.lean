/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import BusyBeaver.Stack
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.Excursion

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 1 Dir.right)


namespace PriorReduction
/-- Transition function for `1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 1 Dir.right)


local notation "zB" => ListBlank (Fin 2)

open Counter
open scoped BusyBeaver.PairStack

local macro "finish" : tactic => `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus
      (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
      zero_cons_default, default_head, default_tail])
local macro "execute" : tactic => `(tactic| repeat (any_goals (first | finish | gstep)))

/-- Four directed boundary modes of `1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE`. -/
private inductive SegMode where
  | mRA
  | mRAE
  | mLD1
  | mLD0
deriving DecidableEq, Repr

/-- Four right-tape zero-run tokens: `r0 = [1]`, `r1 = [0, 1]`, `r2 = [0, 0, 1]`, `r3 = [0, 0, 0,
    1]`. -/
private inductive RTok where
  | r0
  | r1
  | r2
  | r3
deriving DecidableEq, Repr

/-- Seven-state right-to-left parity DFA (+ rejecting `sBad`) certifying `NoFactor [0, 0, 0, 0, 1]`
    on `R`. -/
private inductive RState where
  | sG
  | sS3
  | sA
  | sE
  | sA0
  | sA00
  | sA000
  | sBad
deriving DecidableEq, Repr

/-- Prepends `k` leading `1` bits (`false` tokens) onto a left token stack. -/
private def oneRuns : ℕ → List Bool → List Bool
  | 0, Ls => Ls
  | k + 1, Ls => false :: oneRuns k Ls

/-- Encodes a left token list onto `ListBlank (Fin 2)`. -/
private def encL : List Bool → zB
  | [] => default
  | false :: rest => (1 : Fin 2) >> encL rest
  | true :: rest => (0 : Fin 2) >> (1 : Fin 2) >> encL rest

/-- Encodes a right token list onto `ListBlank (Fin 2)`. -/
private def encR : List RTok → zB
  | [] => default
  | .r0 :: rest => (1 : Fin 2) >> encR rest
  | .r1 :: rest => (0 : Fin 2) >> (1 : Fin 2) >> encR rest
  | .r2 :: rest => (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encR rest
  | .r3 :: rest => (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encR rest

/-- Right-to-left DFA transition on a single right token. -/
private def dfaStep : RTok → RState → RState
  | .r0, .sG => .sG
  | .r1, .sG => .sG
  | .r2, .sG => .sG
  | .r3, .sG => .sS3
  | .r1, .sS3 => .sA
  | .r0, .sA => .sA0
  | .r1, .sA => .sE
  | .r1, .sE => .sA
  | .r0, .sA0 => .sA00
  | .r1, .sA0 => .sE
  | .r0, .sA00 => .sA000
  | .r1, .sA00 => .sG
  | .r2, .sA00 => .sG
  | .r3, .sA00 => .sS3
  | .r1, .sA000 => .sA
  | _, _ => .sBad

/-- Evaluates the right-to-left parity DFA over `Rs : List RTok`. -/
private def evalR : List RTok → RState
  | [] => .sG
  | r :: rest => dfaStep r (evalR rest)

/-- Structural left-stack invariant forbidding adjacent `true :: true` (no interior `010`). -/
private def validL : List Bool → Bool
  | [] => true
  | [true] => true
  | true :: false :: rest => validL rest
  | true :: true :: _ => false
  | false :: rest => validL rest

/-- Boundary invariant for `L` in `.mRA` and `.mLD1`: empty, `[1]`, or starting with `1, 1`. -/
private def isRAL : List Bool → Bool
  | [] => true
  | [false] => true
  | false :: false :: _ => true
  | _ => false

/-- Boundary invariant for `Ls` in `.mRAE` (with `k = 3`): either `[]` (`^111`) or `true :: _` (`L''
    10111`). -/
private def isRAELS : List Bool → Bool
  | [] => true
  | true :: _ => true
  | false :: _ => false

/-- Checks whether `Rs` begins with `[r0, r0]` (`11`). -/
private def startsWith00 : List RTok → Bool
  | .r0 :: .r0 :: _ => true
  | _ => false

/-- Checks whether `Rs` begins with `r1` (`01`). -/
private def startsWith1 : List RTok → Bool
  | .r1 :: _ => true
  | _ => false

/-- Allowed right DFA states in `.mRA`: every accepting state except `.sE`. -/
private def isRARState : RState → Bool
  | .sBad => false
  | .sE => false
  | _ => true

/-- Allowed right DFA states in `.mLD1`: `.sG` or `.sA00`. -/
private def isLD1RState : RState → Bool
  | .sG => true
  | .sA00 => true
  | _ => false

private abbrev SegState := SegMode × ℕ × List Bool × List RTok

/-- Mode-specific validity invariant over `(m, k, Ls, Rs)`. -/
private def validMode (m : SegMode) (k : ℕ) (Ls : List Bool) (Rs : List RTok) : Bool :=
  match m with
  | .mRA => isRAL (oneRuns k Ls) && isRARState (evalR Rs)
  | .mRAE => (k == 3) && isRAELS Ls && (evalR Rs == .sE)
  | .mLD1 => (k == 0) && isRAL Ls && startsWith00 Rs && isLD1RState (evalR Rs)
  | .mLD0 => (k == 0) && startsWith1 Rs && (evalR Rs == .sG)

/-- Closed structural validity invariant on `SegState`. -/
private def ValidSeg (s : SegState) : Prop :=
  validL s.2.2.1 = true ∧ validMode s.1 s.2.1 s.2.2.1 s.2.2.2 = true

/-- Evaluates a segmented state into a concrete machine configuration. -/
private def evalCfg (s : SegState) : Cfg (Fin 2) (Fin 6) :=
  let Lb := encL (oneRuns s.2.1 s.2.2.1)
  let Rb := encR s.2.2.2
  match s.1 with
  | .mRA => ((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}> Rb
  | .mRAE => ((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}> Rb
  | .mLD1 => Lb <{{(3 : Fin 6)}} Rb
  | .mLD0 => Lb <{{(3 : Fin 6)}} Rb

/-- Initial segmented state reached at step `10` from the blank tape. -/
private def s₀ : SegState := (.mRA, 1, [], [.r0, .r0])

private theorem valid_s₀ : ValidSeg s₀ :=
  ⟨rfl, rfl⟩

private theorem init_reaches_segmented_system :
    (init []) [target_tm]⊢⁺ evalCfg s₀ := by
  have h_init :
      (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{(0 : Fin 6)}}> (default : zB)) := rfl
  rw [h_init]
  dsimp only [evalCfg, s₀, oneRuns, encL, encR]
  execute

/-- Prepends a `0` bit onto a left token list starting with `[]` or `false :: _`. -/
private def pushZeroL : List Bool → List Bool
  | [] => []
  | false :: rest => true :: rest
  | true :: rest => true :: rest

private theorem validL_oneRuns (k : ℕ) (Ls : List Bool) (hL : validL Ls = true) :
    validL (oneRuns k Ls) = true := by
  induction k with
  | zero => exact hL
  | succ _ ih => exact ih

private theorem isRAL_oneRuns_succ (k : ℕ) (Ls : List Bool) (h : isRAL (oneRuns k Ls) = true) :
    isRAL (oneRuns (k + 1) Ls) = true := by
  rcases k with _ | k
  · rcases Ls with _ | ⟨_ | _, _⟩ <;> simp_all [oneRuns, isRAL]
  · simp [oneRuns, isRAL]

private theorem isRAL_oneRuns_add2 (k : ℕ) (Ls : List Bool) :
    isRAL (oneRuns (k + 2) Ls) = true := by
  simp [oneRuns, isRAL]

private theorem zero_cons_encL (Ls : List Bool) (h : isRAL Ls = true) :
    (0 : Fin 2) >> encL Ls = encL (pushZeroL Ls) := by
  rcases Ls with _ | ⟨_ | _, rest⟩
  · simp [encL, pushZeroL]
  · rfl
  · simp [isRAL] at h

private theorem validL_pushZeroL (Ls : List Bool) (hL : validL Ls = true) (hRAL : isRAL Ls = true) :
    validL (pushZeroL Ls) = true := by
  rcases Ls with _ | ⟨_ | _, _ | ⟨_ | _, rest⟩⟩
  · rfl
  · rfl
  · exact hL
  · simp [isRAL] at hRAL
  · simp [isRAL] at hRAL
  · simp [isRAL] at hRAL
  · simp [isRAL] at hRAL

-- Atomic multi-step machine rules (independent of `Lb` / `Rb`!)

private theorem raw_RA_1 (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}> ((1 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Lb) {{(0 : Fin 6)}}> Rb) := by
  execute

private theorem raw_RA_010 (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}> ((0 : Fin 2) >> (1 : Fin 2) >>
        (0 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          Lb) {{(0 : Fin 6)}}> Rb) := by
  execute

private theorem raw_RA_0101 (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}>
      ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          Lb) {{(0 : Fin 6)}}> Rb) := by
  exact stepPlus_trans (raw_RA_010 Lb ((1 : Fin 2) >> Rb))
    (raw_RA_1 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> Lb) Rb)

private theorem raw_RA_00 (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}> ((0 : Fin 2) >> (0 : Fin 2) >>
        Rb)) [target_tm]⊢⁺
      (Lb <{{(3 : Fin 6)}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Rb)) := by
  execute

private theorem raw_RA_011 (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> Lb) {{(0 : Fin 6)}}> ((0 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (Lb <{{(3 : Fin 6)}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> Rb)) := by
  execute

private theorem raw_D1_combined (Rb : zB) :
    (((1 : Fin 2) >> default) <{{(3 : Fin 6)}} ((1 : Fin 2) >> (1 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          default) {{(0 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> Rb)) := by
  execute

private theorem raw_RAE_35_base (Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        default) {{(0 : Fin 6)}}>
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> default) {{(0 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> Rb)) := by
  execute

private theorem raw_RAE_35_ext (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (1 : Fin 2) >> Lb) {{(0 : Fin 6)}}>
      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin
            2) >> Lb) {{(0 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> Rb)) := by
  execute

private theorem raw_LD_empty (Rb : zB) :
    ((default : zB) <{{(3 : Fin 6)}} Rb) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) {{(0 : Fin 6)}}> Rb) := by
  execute

private theorem raw_LD_1_R0 (Rb : zB) :
    (((1 : Fin 2) >> default) <{{(3 : Fin 6)}} ((0 : Fin 2) >> Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) {{(0 : Fin 6)}}> Rb) := by
  execute

private theorem raw_LD_11 (Lb Rb : zB) :
    (((1 : Fin 2) >> (1 : Fin 2) >> Lb) <{{(3 : Fin 6)}} Rb) [target_tm]⊢⁺
      (Lb <{{(3 : Fin 6)}} ((0 : Fin 2) >> (1 : Fin 2) >> Rb)) := by
  execute

private theorem raw_LD_110 (Lb Rb : zB) :
    (((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lb) <{{(3 : Fin 6)}} Rb) [target_tm]⊢⁺
      (Lb <{{(3 : Fin 6)}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> Rb)) := by
  execute

private theorem raw_LD_101_R0 (Lb Rb : zB) :
    (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Lb) <{{(3 : Fin 6)}} ((0 : Fin 2) >>
        Rb)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lb) {{(0 : Fin 6)}}> Rb) := by
  execute

/-- Inductive rightward `RA`-sweep over `Rs : List RTok` (consuming leading `r0 = [1]` tokens into
    `k`). -/
private def stepRALoop (k : ℕ) (Ls : List Bool) : List RTok → SegState
  | [] => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1])
  | .r0 :: Rs' => stepRALoop (k + 1) Ls Rs'
  | .r1 :: [] => (.mRA, 2, pushZeroL (oneRuns k Ls), [])
  | .r1 :: .r0 :: [] => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1])
  | .r1 :: .r0 :: .r0 :: Rs' => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1, .r1] ++ Rs')
  | .r1 :: .r0 :: .r1 :: Rs' => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1, .r2] ++ Rs')
  | .r1 :: .r0 :: .r2 :: Rs' => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1, .r3] ++ Rs')
  | .r1 :: .r0 :: .r3 :: Rs' => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1, .r3] ++ Rs')
  | .r1 :: .r1 :: Rs' => (.mRA, 3, pushZeroL (oneRuns k Ls), Rs')
  | .r1 :: .r2 :: Rs' => (.mRA, 2, pushZeroL (oneRuns k Ls), .r1 :: Rs')
  | .r1 :: .r3 :: Rs' => (.mRA, 2, pushZeroL (oneRuns k Ls), .r2 :: Rs')
  | .r2 :: Rs' => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1, .r0] ++ Rs')
  | .r3 :: Rs' => (.mLD1, 0, oneRuns k Ls, [.r0, .r0, .r1, .r1] ++ Rs')

private theorem reach_RA_sweep (Rs : List RTok) (k : ℕ) (Ls : List Bool)
    (hL : validL Ls = true)
    (hRAL : isRAL (oneRuns k Ls) = true)
    (hR : isRARState (evalR Rs) = true) :
    ValidSeg (stepRALoop k Ls Rs) ∧
      ((evalCfg (.mRA, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepRALoop k Ls Rs)) := by
  induction Rs generalizing k with
  | nil =>
    refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
    · simp [stepRALoop, validMode, hRAL, startsWith00, isLD1RState, evalR, dfaStep]
    · dsimp only [stepRALoop, evalCfg, oneRuns, encR]
      have h0 := raw_RA_00 (encL (oneRuns k Ls)) default
      simpa only [zero_cons_default] using h0
  | cons r Rs' ih =>
    cases r with
    | r0 =>
      have hR' : isRARState (evalR Rs') = true := by
        simp only [evalR] at hR
        revert hR
        generalize evalR Rs' = st
        cases st <;> decide
      have hRAL' := isRAL_oneRuns_succ k Ls hRAL
      rcases ih (k + 1) hRAL' hR' with ⟨hv', hstep'⟩
      refine ⟨hv', stepPlus_trans ?_ hstep'⟩
      dsimp only [evalCfg, oneRuns, encL, encR]
      exact raw_RA_1 (encL (oneRuns k Ls)) (encR Rs')
    | r1 =>
      rcases Rs' with _ | ⟨t2, Rs2⟩
      · refine ⟨⟨validL_pushZeroL (oneRuns k Ls) (validL_oneRuns k Ls hL) hRAL, ?_⟩, ?_⟩
        · simp [stepRALoop, validMode, isRAL_oneRuns_add2 0, isRARState, evalR]
        · dsimp only [stepRALoop, evalCfg, oneRuns, encL, encR]
          rw [← zero_cons_encL (oneRuns k Ls) hRAL]
          have h0 := raw_RA_010 (encL (oneRuns k Ls)) default
          simpa only [zero_cons_default] using h0
      · cases t2 with
        | r0 =>
          rcases Rs2 with _ | ⟨t3, Rs3⟩
          · refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
            · simp [stepRALoop, validMode, hRAL, startsWith00, isLD1RState, evalR, dfaStep]
            · dsimp only [stepRALoop, evalCfg, oneRuns, encR]
              have h0 := raw_RA_011 (encL (oneRuns k Ls)) default
              simpa only [zero_cons_default] using h0
          · cases t3 with
            | r0 =>
              refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
              · simp only [stepRALoop, validMode, beq_self_eq_true, Bool.true_and, hRAL,
                  startsWith00, List.cons_append, List.nil_append, evalR]
                simp only [evalR] at hR
                revert hR
                generalize evalR Rs3 = st
                cases st <;> decide
              · dsimp only [stepRALoop, evalCfg, oneRuns, List.cons_append, List.nil_append, encR]
                exact raw_RA_011 (encL (oneRuns k Ls)) ((1 : Fin 2) >> encR Rs3)
            | r1 =>
              refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
              · simp only [stepRALoop, validMode, beq_self_eq_true, Bool.true_and, hRAL,
                  startsWith00, List.cons_append, List.nil_append, evalR]
                simp only [evalR] at hR
                revert hR
                generalize evalR Rs3 = st
                cases st <;> decide
              · dsimp only [stepRALoop, evalCfg, oneRuns, List.cons_append, List.nil_append, encR]
                exact raw_RA_011 (encL (oneRuns k Ls)) ((0 : Fin 2) >> (1 : Fin 2) >> encR Rs3)
            | r2 =>
              refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
              · simp only [stepRALoop, validMode, beq_self_eq_true, Bool.true_and, hRAL,
                  startsWith00, List.cons_append, List.nil_append, evalR]
                simp only [evalR] at hR
                revert hR
                generalize evalR Rs3 = st
                cases st <;> decide
              · dsimp only [stepRALoop, evalCfg, oneRuns, List.cons_append, List.nil_append, encR]
                exact raw_RA_011 (encL (oneRuns k Ls))
                    ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encR Rs3)
            | r3 =>
              exfalso
              simp only [evalR] at hR
              revert hR
              generalize evalR Rs3 = st
              cases st <;> decide
        | r1 =>
          refine ⟨⟨validL_pushZeroL (oneRuns k Ls) (validL_oneRuns k Ls hL) hRAL, ?_⟩, ?_⟩
          · simp only [stepRALoop, validMode, isRAL_oneRuns_add2 1, Bool.true_and]
            simp only [evalR] at hR
            revert hR
            generalize evalR Rs2 = st
            cases st <;> decide
          · dsimp only [stepRALoop, evalCfg, oneRuns, encL, encR]
            rw [← zero_cons_encL (oneRuns k Ls) hRAL]
            exact raw_RA_0101 (encL (oneRuns k Ls)) (encR Rs2)
        | r2 =>
          refine ⟨⟨validL_pushZeroL (oneRuns k Ls) (validL_oneRuns k Ls hL) hRAL, ?_⟩, ?_⟩
          · simp only [stepRALoop, validMode, isRAL_oneRuns_add2 0, Bool.true_and, evalR]
            simp only [evalR] at hR
            revert hR
            generalize evalR Rs2 = st
            cases st <;> decide
          · dsimp only [stepRALoop, evalCfg, oneRuns, encL, encR]
            rw [← zero_cons_encL (oneRuns k Ls) hRAL]
            exact raw_RA_010 (encL (oneRuns k Ls)) ((0 : Fin 2) >> (1 : Fin 2) >> encR Rs2)
        | r3 =>
          refine ⟨⟨validL_pushZeroL (oneRuns k Ls) (validL_oneRuns k Ls hL) hRAL, ?_⟩, ?_⟩
          · simp only [stepRALoop, validMode, isRAL_oneRuns_add2 0, Bool.true_and, evalR]
            simp only [evalR] at hR
            revert hR
            generalize evalR Rs2 = st
            cases st <;> decide
          · dsimp only [stepRALoop, evalCfg, oneRuns, encL, encR]
            rw [← zero_cons_encL (oneRuns k Ls) hRAL]
            exact raw_RA_010 (encL (oneRuns k Ls))
                ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encR Rs2)
    | r2 =>
      refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
      · simp only [stepRALoop, validMode, beq_self_eq_true, Bool.true_and, hRAL,
          startsWith00, List.cons_append, List.nil_append, evalR]
        simp only [evalR] at hR
        revert hR
        generalize evalR Rs' = st
        cases st <;> decide
      · dsimp only [stepRALoop, evalCfg, oneRuns, List.cons_append, List.nil_append, encR]
        exact raw_RA_00 (encL (oneRuns k Ls)) ((1 : Fin 2) >> encR Rs')
    | r3 =>
      refine ⟨⟨validL_oneRuns k Ls hL, ?_⟩, ?_⟩
      · simp only [stepRALoop, validMode, beq_self_eq_true, Bool.true_and, hRAL,
          startsWith00, List.cons_append, List.nil_append, evalR]
        simp only [evalR] at hR
        revert hR
        generalize evalR Rs' = st
        cases st <;> decide
      · dsimp only [stepRALoop, evalCfg, oneRuns, List.cons_append, List.nil_append, encR]
        exact raw_RA_00 (encL (oneRuns k Ls)) ((0 : Fin 2) >> (1 : Fin 2) >> encR Rs')

private theorem step_RA_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok)
    (hv : ValidSeg (.mRA, k, Ls, Rs)) :
    ValidSeg (stepRALoop k Ls Rs) ∧
      ((evalCfg (.mRA, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepRALoop k Ls Rs)) := by
  rcases hv with ⟨hL, hM⟩
  simp only [validMode, Bool.and_eq_true] at hM
  exact reach_RA_sweep Rs k Ls hL hM.1 hM.2

/-- Macro-step from `.mRAE`. -/
private def stepRAE (Ls : List Bool) (Rs : List RTok) : SegState :=
  match Rs with
  | .r1 :: .r1 :: Rs2 =>
    let dst := if evalR Rs2 == .sE then SegMode.mRAE else SegMode.mRA
    (dst, 3, true :: false :: false :: Ls, Rs2)
  | .r1 :: .r0 :: .r1 :: Rs3 =>
    match Ls with
    | [] => (.mRA, 2, [true, false, false, false], .r1 :: Rs3)
    | _ :: Ls'' => (.mRA, 2, true :: false :: false :: false :: false :: Ls'', .r1 :: Rs3)
  | _ => (.mRA, 2, [], [])

private theorem step_RAE_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok)
    (hv : ValidSeg (.mRAE, k, Ls, Rs)) :
    ValidSeg (stepRAE Ls Rs) ∧
      ((evalCfg (.mRAE, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepRAE Ls Rs)) := by
  rcases hv with ⟨hL, hM⟩
  simp only [validMode, Bool.and_eq_true, beq_iff_eq] at hM
  rcases hM with ⟨⟨rfl, hELS⟩, hRE⟩
  rcases Rs with _ | ⟨t0, Rs1⟩
  · simp [evalR] at hRE
  · cases t0 with
    | r0 =>
      exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs1 = st; cases st <;> decide
    | r2 =>
      exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs1 = st; cases st <;> decide
    | r3 =>
      exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs1 = st; cases st <;> decide
    | r1 =>
      rcases Rs1 with _ | ⟨t1, Rs2⟩
      · simp [evalR, dfaStep] at hRE
      · cases t1 with
        | r2 =>
          exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs2 = st; cases st <;>
              decide
        | r3 =>
          exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs2 = st; cases st <;>
              decide
        | r1 =>
          have hLnew : validL (true :: false :: false :: Ls) = true := hL
          have hstep :
              ((evalCfg (.mRAE, 3, Ls, .r1 :: .r1 :: Rs2)) [target_tm]⊢⁺
                evalCfg (if evalR Rs2 == .sE then SegMode.mRAE else SegMode.mRA,
                  3, true :: false :: false :: Ls, Rs2)) := by
            have h0 := raw_RA_0101 (encL (oneRuns 3 Ls)) (encR Rs2)
            split <;> exact h0
          refine ⟨⟨hLnew, ?_⟩, hstep⟩
          dsimp only [stepRAE]
          split
          · rename_i heq
            simp only [beq_iff_eq] at heq
            simp [validMode, isRAELS, heq]
          · rename_i hne
            simp only [beq_iff_eq] at hne
            simp only [validMode, isRAL_oneRuns_add2 1, Bool.true_and]
            simp only [evalR] at hRE
            revert hRE hne
            generalize evalR Rs2 = st
            cases st <;> decide
        | r0 =>
          rcases Rs2 with _ | ⟨t2, Rs3⟩
          · simp [evalR, dfaStep] at hRE
          · cases t2 with
            | r0 =>
              exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs3 = st; cases st <;>
                  decide
            | r2 =>
              exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs3 = st; cases st <;>
                  decide
            | r3 =>
              exfalso; simp only [evalR] at hRE; revert hRE; generalize evalR Rs3 = st; cases st <;>
                  decide
            | r1 =>
              have hRnew : isRARState (evalR (.r1 :: Rs3)) = true := by
                simp only [evalR] at hRE ⊢
                revert hRE
                generalize evalR Rs3 = st
                cases st <;> decide
              rcases Ls with _ | ⟨b, Ls''⟩
              · refine ⟨⟨rfl, by simp [stepRAE, validMode, isRAL_oneRuns_add2 0, hRnew]⟩, ?_⟩
                dsimp only [stepRAE, evalCfg, oneRuns, encL, encR]
                exact raw_RAE_35_base (encR Rs3)
              · cases b with
                | false => simp [isRAELS] at hELS
                | true =>
                  have hL'' : validL Ls'' = true := by
                    rcases Ls'' with _ | ⟨_ | _, _⟩ <;> simp_all [validL]
                  refine ⟨⟨hL'', by simp [stepRAE, validMode, isRAL_oneRuns_add2 0, hRnew]⟩, ?_⟩
                  dsimp only [stepRAE, evalCfg, oneRuns, encL, encR]
                  exact raw_RAE_35_ext (encL Ls'') (encR Rs3)

/-- Macro-step from `.mLD1`. -/
private def stepLD1 (Ls : List Bool) (Rs : List RTok) : SegState :=
  match Ls with
  | [] => (.mRA, 1, [], Rs)
  | [false] =>
    match Rs with
    | .r0 :: .r0 :: Rs' =>
      let dst := if evalR (.r1 :: Rs') == .sE then SegMode.mRAE else SegMode.mRA
      (dst, 3, [], .r1 :: Rs')
    | _ => (.mRA, 1, [], Rs)
  | false :: false :: Ls' => (.mLD0, 0, Ls', .r1 :: Rs)
  | _ => (.mRA, 1, [], Rs)

private theorem step_LD1_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok)
    (hv : ValidSeg (.mLD1, k, Ls, Rs)) :
    ValidSeg (stepLD1 Ls Rs) ∧
      ((evalCfg (.mLD1, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepLD1 Ls Rs)) := by
  rcases hv with ⟨hL, hM⟩
  simp only [validMode, Bool.and_eq_true, beq_iff_eq] at hM
  rcases hM with ⟨⟨⟨rfl, hRAL⟩, h00⟩, hR⟩
  rcases Ls with _ | ⟨b0, Ls1⟩
  · refine ⟨⟨rfl, ?_⟩, ?_⟩
    · simp only [stepLD1, validMode, oneRuns, isRAL, Bool.true_and]
      revert hR; generalize evalR Rs = st; cases st <;> decide
    · dsimp only [stepLD1, evalCfg, oneRuns, encL]
      exact raw_LD_empty (encR Rs)
  · cases b0 with
    | true => simp [isRAL] at hRAL
    | false =>
      rcases Ls1 with _ | ⟨b1, Ls2⟩
      · rcases Rs with _ | ⟨t0, _ | ⟨t1, Rs'⟩⟩
        · simp [startsWith00] at h00
        · simp [startsWith00] at h00
        · cases t0 with
          | r1 | r2 | r3 => simp [startsWith00] at h00
          | r0 =>
            cases t1 with
            | r1 | r2 | r3 => simp [startsWith00] at h00
            | r0 =>
              have hstep :
                  ((evalCfg (.mLD1, 0, [false], .r0 :: .r0 :: Rs')) [target_tm]⊢⁺
                    evalCfg (if evalR (.r1 :: Rs') == .sE then SegMode.mRAE else SegMode.mRA,
                      3, [], .r1 :: Rs')) := by
                have h0 := raw_D1_combined (encR Rs')
                split <;> exact h0
              refine ⟨⟨rfl, ?_⟩, hstep⟩
              dsimp only [stepLD1]
              split
              · rename_i heq
                simp only [beq_iff_eq] at heq
                simp [validMode, isRAELS, heq]
              · rename_i hne
                simp only [beq_iff_eq] at hne
                simp only [validMode, isRAL_oneRuns_add2 1, Bool.true_and]
                simp only [evalR] at hR hne ⊢
                revert hR hne
                generalize evalR Rs' = st
                cases st <;> decide
      · cases b1 with
        | true => simp [isRAL] at hRAL
        | false =>
          refine ⟨⟨hL, ?_⟩, ?_⟩
          · simp only [stepLD1, validMode, beq_self_eq_true, Bool.true_and, startsWith1, evalR]
            revert hR; generalize evalR Rs = st; cases st <;> decide
          · dsimp only [stepLD1, evalCfg, oneRuns, encL, encR]
            exact raw_LD_11 (encL Ls2) (encR Rs)

/-- Macro-step from `.mLD0` (`none` iff `Ls = [true]`, reaching the halt at `C0`). -/
private def stepLD0 (Ls : List Bool) (Rs : List RTok) : Option SegState :=
  match Ls, Rs with
  | [], _ => some (.mRA, 1, [], Rs)
  | [false], .r1 :: Rs' => some (.mRA, 1, [], .r0 :: Rs')
  | [true], _ => none
  | false :: false :: Ls', _ => some (.mLD0, 0, Ls', .r1 :: Rs)
  | true :: false :: Ls', .r1 :: Rs' => some (.mLD0, 0, Ls', .r1 :: .r2 :: Rs')
  | false :: true :: Ls', .r1 :: Rs' => some (.mRA, 2, Ls', .r0 :: Rs')
  | _, _ => none

private theorem step_LD0_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok) (s' : SegState)
    (hv : ValidSeg (.mLD0, k, Ls, Rs)) (h : stepLD0 Ls Rs = some s') :
    ValidSeg s' ∧ ((evalCfg (.mLD0, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg s') := by
  rcases hv with ⟨hL, hM⟩
  simp only [validMode, Bool.and_eq_true, beq_iff_eq] at hM
  rcases hM with ⟨⟨rfl, h1⟩, hRG⟩
  rcases Rs with _ | ⟨t0, Rs'⟩
  · simp [startsWith1] at h1
  · cases t0 with
    | r0 | r2 | r3 => simp [startsWith1] at h1
    | r1 =>
      rcases Ls with _ | ⟨b0, Ls1⟩
      · simp only [stepLD0, Option.some.injEq] at h; subst h
        refine ⟨⟨rfl, by simp [validMode, oneRuns, isRAL, isRARState, hRG]⟩, ?_⟩
        dsimp only [evalCfg, oneRuns, encL]
        exact raw_LD_empty (encR (.r1 :: Rs'))
      · cases b0 with
        | false =>
          rcases Ls1 with _ | ⟨b1, Ls2⟩
          · simp only [stepLD0, Option.some.injEq] at h; subst h
            refine ⟨⟨rfl, ?_⟩, ?_⟩
            · simp only [validMode, oneRuns, isRAL, Bool.true_and, evalR]
              simp only [evalR] at hRG
              revert hRG; generalize evalR Rs' = st; cases st <;> decide
            · dsimp only [evalCfg, oneRuns, encL, encR]
              exact raw_LD_1_R0 ((1 : Fin 2) >> encR Rs')
          · cases b1 with
            | false =>
              simp only [stepLD0, Option.some.injEq] at h; subst h
              refine ⟨⟨hL, ?_⟩, ?_⟩
              · dsimp only [validMode, startsWith1]
                rw [evalR, hRG]
                rfl
              · dsimp only [evalCfg, oneRuns, encL, encR]
                exact raw_LD_11 (encL Ls2) (encR (.r1 :: Rs'))
            | true =>
              simp only [stepLD0, Option.some.injEq] at h; subst h
              have hL2 : validL Ls2 = true := by
                rcases Ls2 with _ | ⟨_ | _, _⟩ <;> simp_all [validL]
              refine ⟨⟨hL2, ?_⟩, ?_⟩
              · simp only [validMode, isRAL_oneRuns_add2 0, Bool.true_and, evalR]
                simp only [evalR] at hRG
                revert hRG; generalize evalR Rs' = st; cases st <;> decide
              · dsimp only [evalCfg, oneRuns, encL, encR]
                exact raw_LD_101_R0 (encL Ls2) ((1 : Fin 2) >> encR Rs')
        | true =>
          rcases Ls1 with _ | ⟨b1, Ls2⟩
          · simp [stepLD0] at h
          · cases b1 with
            | true => simp [validL] at hL
            | false =>
              simp only [stepLD0, Option.some.injEq] at h; subst h
              refine ⟨⟨hL, ?_⟩, ?_⟩
              · simp only [validMode, beq_self_eq_true, Bool.true_and, startsWith1, evalR]
                simp only [evalR] at hRG
                revert hRG; generalize evalR Rs' = st; cases st <;> decide
              · dsimp only [evalCfg, oneRuns, encL, encR]
                exact raw_LD_110 (encL Ls2) ((0 : Fin 2) >> (1 : Fin 2) >> encR Rs')

/-- Macro-transition function on `SegState`. -/
private def stepMacro (s : SegState) : Option SegState :=
  match s.1 with
  | .mRA => some (stepRALoop s.2.1 s.2.2.1 s.2.2.2)
  | .mRAE => some (stepRAE s.2.2.1 s.2.2.2)
  | .mLD1 => some (stepLD1 s.2.2.1 s.2.2.2)
  | .mLD0 => stepLD0 s.2.2.1 s.2.2.2

private theorem segmented_step_sound (s s' : SegState) (hv : ValidSeg s)
    (h : stepMacro s = some s') :
    ValidSeg s' ∧ ((evalCfg s) [target_tm]⊢⁺ evalCfg s') := by
  rcases s with ⟨m, k, Ls, Rs⟩
  cases m with
  | mRA =>
    simp only [stepMacro, Option.some.injEq] at h
    subst h
    exact step_RA_sound k Ls Rs hv
  | mRAE =>
    simp only [stepMacro, Option.some.injEq] at h
    subst h
    exact step_RAE_sound k Ls Rs hv
  | mLD1 =>
    simp only [stepMacro, Option.some.injEq] at h
    subst h
    exact step_LD1_sound k Ls Rs hv
  | mLD0 => exact step_LD0_sound k Ls Rs s' hv h

private theorem target_tm_eq (other : Machine (Fin 2) (Fin 6))
    (h : ∀ q s, other q s = target_tm q s) : other = target_tm :=
  funext fun q => funext fun s => h q s

end PriorReduction


open Counter BusyBeaver.Excursion

/-! ### Re-export Segmented Macro-Transition System from `PriorReduction` -/

open PriorReduction (SegMode RTok RState oneRuns dfaStep evalR validL startsWith00
  startsWith1 isRARState isLD1RState SegState validMode ValidSeg evalCfg s₀ valid_s₀
  pushZeroL validL_oneRuns isRAL_oneRuns_add2 stepRALoop stepRAE stepLD1 stepMacro)

private theorem target_tm_eq_prior : target_tm = PriorReduction.target_tm :=
  PriorReduction.target_tm_eq target_tm fun
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
    | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

private theorem init_reaches_s₀ :
    (init []) [target_tm]⊢⁺ evalCfg s₀ :=
  target_tm_eq_prior.symm ▸ PriorReduction.init_reaches_segmented_system

private theorem step_RA_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok)
    (hv : ValidSeg (.mRA, k, Ls, Rs)) :
    ValidSeg (stepRALoop k Ls Rs) ∧
      ((evalCfg (.mRA, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepRALoop k Ls Rs)) :=
  target_tm_eq_prior.symm ▸ PriorReduction.step_RA_sound k Ls Rs hv

private theorem step_RAE_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok)
    (hv : ValidSeg (.mRAE, k, Ls, Rs)) :
    ValidSeg (stepRAE Ls Rs) ∧
      ((evalCfg (.mRAE, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepRAE Ls Rs)) :=
  target_tm_eq_prior.symm ▸ PriorReduction.step_RAE_sound k Ls Rs hv

private theorem step_LD1_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok)
    (hv : ValidSeg (.mLD1, k, Ls, Rs)) :
    ValidSeg (stepLD1 Ls Rs) ∧
      ((evalCfg (.mLD1, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg (stepLD1 Ls Rs)) :=
  target_tm_eq_prior.symm ▸ PriorReduction.step_LD1_sound k Ls Rs hv

private theorem step_LD0_sound (k : ℕ) (Ls : List Bool) (Rs : List RTok) (s' : SegState)
    (hv : ValidSeg (.mLD0, k, Ls, Rs))
    (h : PriorReduction.stepLD0 Ls Rs = some s') :
    ValidSeg s' ∧ ((evalCfg (.mLD0, k, Ls, Rs)) [target_tm]⊢⁺ evalCfg s') :=
  target_tm_eq_prior.symm ▸ PriorReduction.step_LD0_sound k Ls Rs s' hv h

private theorem segmented_step_sound (s s' : SegState) (hv : ValidSeg s)
    (h : stepMacro s = some s') :
    ValidSeg s' ∧ ((evalCfg s) [target_tm]⊢⁺ evalCfg s') :=
  target_tm_eq_prior.symm ▸ PriorReduction.segmented_step_sound s s' hv h

/-! ### Universal Call-Return Parity Conservation Theorem -/

/-- Number of leading `r0` tokens in `Rs`. -/
private def lead0 : List RTok → ℕ
  | .r0 :: rest => lead0 rest + 1
  | _ => 0

/-- Drops all leading `r0` tokens from `Rs`. -/
private def drop0 : List RTok → List RTok
  | .r0 :: rest => drop0 rest
  | Rs => Rs

private theorem stepRALoop_drop0 (Rs : List RTok) (k : ℕ) (Ls : List Bool) :
    stepRALoop k Ls Rs = stepRALoop (k + lead0 Rs) Ls (drop0 Rs) := by
  induction Rs generalizing k with
  | nil => simp [lead0, drop0]
  | cons r rest ih =>
    cases r with
    | r0 =>
      simp only [stepRALoop, lead0, drop0]
      rw [ih (k + 1)]
      congr 1
      omega
    | r1 | r2 | r3 => simp [lead0, drop0]

private theorem isRARState_drop0 (Rs : List RTok) (hR : isRARState (evalR Rs) = true) :
    isRARState (evalR (drop0 Rs)) = true := by
  induction Rs with
  | nil => exact hR
  | cons r rest ih =>
    cases r with
    | r0 =>
      apply ih
      simp only [evalR] at hR
      revert hR
      generalize evalR rest = st
      cases st <;> decide
    | r1 | r2 | r3 => exact hR

private theorem drop0_head_ne_r0 (Rs : List RTok) :
    match drop0 Rs with
    | .r0 :: _ => False
    | _ => True := by
  induction Rs with
  | nil => trivial
  | cons r rest ih =>
    cases r with
    | r0 => exact ih
    | r1 | r2 | r3 => trivial

/-- Return-shape invariant on `R` in `.mLD0`: `evalR Rs = .sG` and `Rs` starts with `r1`
    followed by `0` or `2` `r0` tokens before a non-`r0` token. -/
private def GoodRetR (Rs : List RTok) : Prop :=
  evalR Rs = .sG ∧
  ((∃ U, Rs = .r1 :: .r0 :: .r0 :: .r1 :: U) ∨
   (∃ U, Rs = .r1 :: .r1 :: U) ∨
   (∃ U, Rs = .r1 :: .r2 :: U))

private theorem goodRetR_startsWith1 {Rs : List RTok} (h : GoodRetR Rs) :
    startsWith1 Rs = true := by
  rcases h with ⟨_, ⟨U, rfl⟩ | ⟨U, rfl⟩ | ⟨U, rfl⟩⟩ <;> rfl

private theorem goodRetR_push_r1 {Rs : List RTok} (h : GoodRetR Rs) :
    GoodRetR (.r1 :: Rs) := by
  rcases h with ⟨hG, hShape⟩
  refine ⟨by simp [evalR, hG, dfaStep], Or.inr (Or.inl ?_)⟩
  rcases hShape with ⟨U, rfl⟩ | ⟨U, rfl⟩ | ⟨U, rfl⟩
  · exact ⟨.r0 :: .r0 :: .r1 :: U, rfl⟩
  · exact ⟨.r1 :: U, rfl⟩
  · exact ⟨.r2 :: U, rfl⟩

private theorem goodRetR_push_r1_r2 {Rs' : List RTok} (h : GoodRetR (.r1 :: Rs')) :
    GoodRetR (.r1 :: .r2 :: Rs') := by
  rcases h with ⟨hG, _⟩
  refine ⟨?_, Or.inr (Or.inr ⟨Rs', rfl⟩)⟩
  simp only [evalR] at hG ⊢
  revert hG
  generalize evalR Rs' = st
  cases st <;> decide

private theorem goodRetR_lead0_replace_r0 {Rs' : List RTok} (h : GoodRetR (.r1 :: Rs')) :
    lead0 (.r0 :: Rs') % 2 = 1 := by
  rcases h with ⟨_, ⟨U, hEq⟩ | ⟨U, hEq⟩ | ⟨U, hEq⟩⟩ <;>
    injection hEq with _ hTail <;> subst hTail <;> simp [lead0]

private theorem validL_oneRuns_tail (k : ℕ) (L : List Bool) (hL : validL L = true) :
    validL (true :: oneRuns (k + 1) L) = true := by
  simp only [oneRuns, validL]
  exact validL_oneRuns k L hL

/-- Draining `oneRuns m L_bot` two `false` tokens at a time in `.mLD0` preserves `GoodRetR`
    and leaves `m % 2` zeros above `L_bot`. -/
private theorem mLD0_drain_zeros (m : ℕ) (L_bot : List Bool) (hL : validL L_bot = true) :
    ∀ Rs, GoodRetR Rs →
      Leads target_tm (evalCfg (.mLD0, 0, oneRuns m L_bot, Rs))
        (fun cfg => ∃ R', GoodRetR R' ∧
          cfg = evalCfg (.mLD0, 0, if m % 2 = 0 then L_bot else false :: L_bot, R')) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro Rs hGood
    match m with
    | 0 =>
      exact fun n hn => ⟨n, _, Nat.le_refl n, ⟨Rs, hGood, by simp [oneRuns]⟩, hn⟩
    | 1 =>
      exact fun n hn => ⟨n, _, Nat.le_refl n, ⟨Rs, hGood, by simp [oneRuns]⟩, hn⟩
    | m' + 2 =>
      have hv : ValidSeg (.mLD0, 0, false :: false :: oneRuns m' L_bot, Rs) := by
        refine ⟨validL_oneRuns (m' + 2) L_bot hL, ?_⟩
        simp [validMode, goodRetR_startsWith1 hGood, hGood.1]
      have hstep : (evalCfg (.mLD0, 0, false :: false :: oneRuns m' L_bot, Rs)) [target_tm]⊢⁺
          evalCfg (.mLD0, 0, oneRuns m' L_bot, .r1 :: Rs) :=
        (step_LD0_sound 0 (false :: false :: oneRuns m' L_bot) Rs
          (.mLD0, 0, oneRuns m' L_bot, .r1 :: Rs) hv rfl).2
      have hMod : (m' + 2) % 2 = m' % 2 := by omega
      rw [hMod]
      exact Leads.of_stepPlus_leads hstep (ih m' (by omega) (.r1 :: Rs) (goodRetR_push_r1 hGood))

/-- Helper: executing `mLD1` when `L = oneRuns (k' + 2) L_bot` and `Rs = r0 :: r0 :: r1 :: U`
    leads to the parity-matched `.mLD0` return with `GoodRetR`. -/
private theorem mLD1_return_leads (k' : ℕ) (L_bot : List Bool) (hL : validL L_bot = true)
    (U : List RTok) (hR : isLD1RState (evalR (.r0 :: .r0 :: .r1 :: U)) = true) :
    Leads target_tm (evalCfg (.mLD1, 0, oneRuns (k' + 2) L_bot, .r0 :: .r0 :: .r1 :: U))
      (fun cfg => ∃ R', GoodRetR R' ∧
        cfg = evalCfg (.mLD0, 0, if (k' + 2) % 2 = 0 then L_bot else false :: L_bot, R')) := by
  have hv1 : ValidSeg (.mLD1, 0, oneRuns (k' + 2) L_bot, .r0 :: .r0 :: .r1 :: U) := by
    refine ⟨validL_oneRuns (k' + 2) L_bot hL, ?_⟩
    simp [validMode, isRAL_oneRuns_add2, startsWith00, hR]
  have h1 := step_LD1_sound 0 (oneRuns (k' + 2) L_bot) (.r0 :: .r0 :: .r1 :: U) hv1
  simp only [oneRuns, stepLD1] at h1
  have hGood : GoodRetR (.r1 :: .r0 :: .r0 :: .r1 :: U) := by
    refine ⟨?_, Or.inl ⟨U, rfl⟩⟩
    have hv1' := h1.1.2
    simp only [validMode, Bool.and_eq_true, beq_iff_eq] at hv1'
    exact hv1'.2
  have hMod : (k' + 2) % 2 = k' % 2 := by omega
  rw [hMod]
  exact Leads.of_stepPlus_leads h1.2 (mLD0_drain_zeros k' L_bot hL _ hGood)

/-- Universal Call-Return Parity Conservation Theorem:
    From any valid `.mRA` state with `k + lead0 Rs ≥ 2`, either the computation never halts inside
    the call or it strictly advances (`Advances`) to `.mLD0` with `L_bot` plus `(k + lead0 Rs) % 2`
    zeros and a right tape satisfying `GoodRetR`. -/
private theorem callRA_advances_budget :
    ∀ (n : ℕ) (k : ℕ) (L_bot : List Bool) (Rs : List RTok),
      2 ≤ k + lead0 Rs →
      ValidSeg (.mRA, k, L_bot, Rs) →
      HaltsIn target_tm (evalCfg (.mRA, k, L_bot, Rs)) n →
      ∃ m d, m < n ∧
        (∃ R', GoodRetR R' ∧
          d = evalCfg (.mLD0, 0, if (k + lead0 Rs) % 2 = 0 then L_bot else false :: L_bot, R')) ∧
        HaltsIn target_tm d m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k L_bot Rs hk hv hHalt
    have hL : validL L_bot = true := hv.1
    have hRA := step_RA_sound k L_bot Rs hv
    have hRA_adv : Advances target_tm (evalCfg (.mRA, k, L_bot, Rs))
        (fun c => c = evalCfg (stepRALoop k L_bot Rs)) :=
      Advances.of_stepPlus hRA.2 rfl
    rcases hRA_adv n hHalt with ⟨n₁, _, hn₁lt, rfl, hHalt₁⟩
    rw [stepRALoop_drop0] at hRA hHalt₁
    have hR0 : isRARState (evalR Rs) = true := by
      have hm := hv.2
      simp only [validMode, Bool.and_eq_true] at hm
      exact hm.2
    have hRdrop := isRARState_drop0 Rs hR0
    have hNoR0 := drop0_head_ne_r0 Rs
    obtain ⟨kp, hkp⟩ : ∃ kp, k + lead0 Rs = kp + 2 := ⟨k + lead0 Rs - 2, by omega⟩
    rw [hkp] at hRA hHalt₁ ⊢
    -- Helper for recursive subcall when stepRALoop returns (.mRA, k_next, pushZeroL (oneRuns (kp +
    -- 2) L_bot), R_next)
    have hRecCase : ∀ (k_next : ℕ) (R_next : List RTok),
        2 ≤ k_next →
        ValidSeg (.mRA, k_next, true :: oneRuns (kp + 1) L_bot, R_next) →
        HaltsIn target_tm (evalCfg (.mRA, k_next, true :: oneRuns (kp + 1) L_bot, R_next)) n₁ →
        ∃ m d, m < n ∧
          (∃ R', GoodRetR R' ∧
            d = evalCfg (.mLD0, 0, if (kp + 2) % 2 = 0 then L_bot else false :: L_bot, R')) ∧
          HaltsIn target_tm d m := by
      intro k_next R_next hk_next hv_sub hHalt_sub
      rcases ih n₁ hn₁lt k_next (true :: oneRuns (kp + 1) L_bot) R_next
          (by omega) hv_sub hHalt_sub with
        ⟨n₂, _, hn₂lt, ⟨R₁, hGood₁, rfl⟩, hHalt₂⟩
      rcases hGood₁ with ⟨hG₁, hSh₁⟩
      obtain ⟨R₁', rfl⟩ : ∃ R₁', R₁ = .r1 :: R₁' := by
        rcases hSh₁ with ⟨U, rfl⟩ | ⟨U, rfl⟩ | ⟨U, rfl⟩
        · exact ⟨.r0 :: .r0 :: .r1 :: U, rfl⟩
        · exact ⟨.r1 :: U, rfl⟩
        · exact ⟨.r2 :: U, rfl⟩
      have hGood₁' : GoodRetR (.r1 :: R₁') := ⟨hG₁, hSh₁⟩
      split_ifs at hHalt₂ with hPar
      · -- Even sub-return: L = true :: false :: oneRuns kp L_bot -> mLD0 pops (true, false), pushes
        -- (r1, r2)
        have hv_ld0 : ValidSeg (.mLD0, 0, true :: false :: oneRuns kp L_bot, .r1 :: R₁') := by
          refine ⟨validL_oneRuns_tail kp L_bot hL, ?_⟩
          simp [validMode, startsWith1, hG₁]
        have hstep_10 := (step_LD0_sound 0 (true :: false :: oneRuns kp L_bot) (.r1 :: R₁')
          (.mLD0, 0, oneRuns kp L_bot, .r1 :: .r2 :: R₁') hv_ld0 rfl).2
        have hGood₂ := goodRetR_push_r1_r2 hGood₁'
        have hLeads := Leads.of_stepPlus_leads hstep_10 (mLD0_drain_zeros kp L_bot hL _ hGood₂)
        rcases hLeads n₂ hHalt₂ with ⟨m, d, hmn₂, hd, hHm⟩
        have hMod : (kp + 2) % 2 = kp % 2 := by omega
        rw [hMod]
        exact ⟨m, d, by omega, hd, hHm⟩
      · -- Odd sub-return: L = false :: true :: oneRuns (kp + 1) L_bot -> mLD0 pops (false, true),
        -- bounces to mRA k=2!
        have hv_ld0 : ValidSeg (.mLD0, 0, false :: true :: oneRuns (kp + 1) L_bot, .r1 :: R₁') := by
          refine ⟨validL_oneRuns_tail kp L_bot hL, ?_⟩
          simp [validMode, startsWith1, hG₁]
        have hstep_01 := step_LD0_sound 0 (false :: true :: oneRuns (kp + 1) L_bot) (.r1 :: R₁')
          (.mRA, 2, oneRuns (kp + 1) L_bot, .r0 :: R₁') hv_ld0 rfl
        have hAdv01 := Advances.of_stepPlus hstep_01.2 rfl
        rcases hAdv01 n₂ hHalt₂ with ⟨n₃, _, hn₃lt, rfl, hHalt₃⟩
        -- Second IH call on (.mRA, 2, oneRuns (kp + 1) L_bot, .r0 :: R₁')!
        have hOddLead : lead0 (.r0 :: R₁') % 2 = 1 := goodRetR_lead0_replace_r0 hGood₁'
        have hPar2 : (2 + lead0 (.r0 :: R₁')) % 2 ≠ 0 := by omega
        rcases ih n₃ (by omega) 2 (oneRuns (kp + 1) L_bot) (.r0 :: R₁')
            (by omega) hstep_01.1 hHalt₃ with
          ⟨n₄, _, hn₄lt, ⟨R₂, hGood₂, rfl⟩, hHalt₄⟩
        simp only [hPar2, ↓reduceIte] at hHalt₄
        -- Now L = false :: oneRuns (kp + 1) L_bot = oneRuns (kp + 2) L_bot!
        have hLeads := mLD0_drain_zeros (kp + 2) L_bot hL R₂ hGood₂
        rcases hLeads n₄ hHalt₄ with ⟨m, d, hmn₄, hd, hHm⟩
        exact ⟨m, d, by omega, hd, hHm⟩
    -- Now case split on `drop0 Rs`!
    cases hD : drop0 Rs with
    | nil =>
      rw [hD] at hRA hHalt₁
      simp only [stepRALoop] at hRA hHalt₁
      have hL1 := mLD1_return_leads kp L_bot hL [] (by rfl)
      rcases hL1 n₁ hHalt₁ with ⟨m, d, hmn₁, hd, hHm⟩
      exact ⟨m, d, by omega, hd, hHm⟩
    | cons t0 rest0 =>
      rw [hD] at hNoR0 hRA hHalt₁ hRdrop
      cases t0 with
      | r0 => exact False.elim hNoR0
      | r2 =>
        simp only [stepRALoop, List.cons_append, List.nil_append] at hRA hHalt₁
        have hLD1R : isLD1RState (evalR (.r0 :: .r0 :: .r1 :: .r0 :: rest0)) = true := by
          have hm := hRA.1.2; simp only [validMode, Bool.and_eq_true] at hm; exact hm.2
        rcases mLD1_return_leads kp L_bot hL (.r0 :: rest0) hLD1R n₁ hHalt₁ with ⟨m, d, hmn₁, hd,
            hHm⟩
        exact ⟨m, d, by omega, hd, hHm⟩
      | r3 =>
        simp only [stepRALoop, List.cons_append, List.nil_append] at hRA hHalt₁
        have hLD1R : isLD1RState (evalR (.r0 :: .r0 :: .r1 :: .r1 :: rest0)) = true := by
          have hm := hRA.1.2; simp only [validMode, Bool.and_eq_true] at hm; exact hm.2
        rcases mLD1_return_leads kp L_bot hL (.r1 :: rest0) hLD1R n₁ hHalt₁ with ⟨m, d, hmn₁, hd,
            hHm⟩
        exact ⟨m, d, by omega, hd, hHm⟩
      | r1 =>
        cases rest0 with
        | nil =>
          simp only [stepRALoop, oneRuns, pushZeroL] at hRA hHalt₁
          exact hRecCase 2 [] (by omega) hRA.1 hHalt₁
        | cons t1 rest1 =>
          cases t1 with
          | r1 =>
            simp only [stepRALoop, oneRuns, pushZeroL] at hRA hHalt₁
            exact hRecCase 3 rest1 (by omega) hRA.1 hHalt₁
          | r2 =>
            simp only [stepRALoop, oneRuns, pushZeroL] at hRA hHalt₁
            exact hRecCase 2 (.r1 :: rest1) (by omega) hRA.1 hHalt₁
          | r3 =>
            simp only [stepRALoop, oneRuns, pushZeroL] at hRA hHalt₁
            exact hRecCase 2 (.r2 :: rest1) (by omega) hRA.1 hHalt₁
          | r0 =>
            cases rest1 with
            | nil =>
              simp only [stepRALoop] at hRA hHalt₁
              rcases mLD1_return_leads kp L_bot hL [] (by rfl) n₁ hHalt₁ with ⟨m, d, hmn₁, hd, hHm⟩
              exact ⟨m, d, by omega, hd, hHm⟩
            | cons t2 rest2 =>
              cases t2 with
              | r0 =>
                simp only [stepRALoop, List.cons_append, List.nil_append] at hRA hHalt₁
                have hLD1R : isLD1RState (evalR (.r0 :: .r0 :: .r1 :: .r1 :: rest2)) = true := by
                  have hm := hRA.1.2; simp only [validMode, Bool.and_eq_true] at hm; exact hm.2
                rcases mLD1_return_leads kp L_bot hL (.r1 :: rest2) hLD1R n₁ hHalt₁ with ⟨m, d,
                    hmn₁, hd, hHm⟩
                exact ⟨m, d, by omega, hd, hHm⟩
              | r1 =>
                simp only [stepRALoop, List.cons_append, List.nil_append] at hRA hHalt₁
                have hLD1R : isLD1RState (evalR (.r0 :: .r0 :: .r1 :: .r2 :: rest2)) = true := by
                  have hm := hRA.1.2; simp only [validMode, Bool.and_eq_true] at hm; exact hm.2
                rcases mLD1_return_leads kp L_bot hL (.r2 :: rest2) hLD1R n₁ hHalt₁ with ⟨m, d,
                    hmn₁, hd, hHm⟩
                exact ⟨m, d, by omega, hd, hHm⟩
              | r2 =>
                simp only [stepRALoop, List.cons_append, List.nil_append] at hRA hHalt₁
                have hLD1R : isLD1RState (evalR (.r0 :: .r0 :: .r1 :: .r3 :: rest2)) = true := by
                  have hm := hRA.1.2; simp only [validMode, Bool.and_eq_true] at hm; exact hm.2
                rcases mLD1_return_leads kp L_bot hL (.r3 :: rest2) hLD1R n₁ hHalt₁ with ⟨m, d,
                    hmn₁, hd, hHm⟩
                exact ⟨m, d, by omega, hd, hHm⟩
              | r3 =>
                exfalso
                simp only [evalR] at hRdrop
                revert hRdrop
                generalize evalR rest2 = st
                cases st <;> decide

private theorem callRA_advances (k : ℕ) (L_bot : List Bool) (Rs : List RTok)
    (hk : 2 ≤ k + lead0 Rs) (hv : ValidSeg (.mRA, k, L_bot, Rs)) :
    Advances target_tm (evalCfg (.mRA, k, L_bot, Rs))
      (fun cfg => ∃ R', GoodRetR R' ∧
        cfg = evalCfg (.mLD0, 0, if (k + lead0 Rs) % 2 = 0 then L_bot else false :: L_bot, R')) :=
  fun n hHalt => callRA_advances_budget n k L_bot Rs hk hv hHalt

/-! ### Reflected Symbolic Verifier over the 132-Checkpoint Period-87 CPS Graph -/

/-- Compact 7-bit subset of non-`sBad` `RState` values for exact `evalR` tracking. -/
private structure RMask where
  g : Bool
  s3 : Bool
  a : Bool
  e : Bool
  a0 : Bool
  a00 : Bool
  a000 : Bool
deriving DecidableEq

private def RMask.contains (m : RMask) : RState → Bool
  | .sG => m.g
  | .sS3 => m.s3
  | .sA => m.a
  | .sE => m.e
  | .sA0 => m.a0
  | .sA00 => m.a00
  | .sA000 => m.a000
  | .sBad => false

private def RMask.anyNonE (m : RMask) : Bool :=
  m.g || m.s3 || m.a || m.a0 || m.a00 || m.a000

private def RMask.advance (r : RTok) (m : RMask) : RMask :=
  match r with
  | .r0 => ⟨m.g, false, false, false, m.a, m.a0, m.a00⟩
  | .r1 => ⟨m.g || m.a00, false, m.s3 || m.e || m.a000, m.a || m.a0, false, false, false⟩
  | .r2 => ⟨m.g || m.a00, false, false, false, false, false, false⟩
  | .r3 => ⟨false, m.g || m.a00, false, false, false, false, false⟩

private def RMask.evalPrefix (Rs : List RTok) (m : RMask) : RMask :=
  Rs.foldr RMask.advance m

private theorem RMask.advance_sound (r : RTok) (m : RMask) (st : RState)
    (hm : m.contains st = true) (hnb : dfaStep r st ≠ .sBad) :
    (m.advance r).contains (dfaStep r st) = true := by
  cases r <;> cases st <;> simp_all [RMask.contains, RMask.advance, dfaStep]

private theorem RMask.evalPrefix_sound (Rs W : List RTok) (m : RMask)
    (hm : m.contains (evalR W) = true) (hnb : evalR (Rs ++ W) ≠ .sBad) :
    (RMask.evalPrefix Rs m).contains (evalR (Rs ++ W)) = true := by
  induction Rs with
  | nil => exact hm
  | cons r rest ih =>
    have hnb_rest : evalR (rest ++ W) ≠ .sBad := by
      intro hbad
      apply hnb
      simp [evalR, hbad, dfaStep]
    have h1 := ih hnb_rest
    exact RMask.advance_sound r (RMask.evalPrefix rest m) (evalR (rest ++ W)) h1 hnb

private theorem RMask.not_e_of_false (m : RMask) (st : RState)
    (hm : m.contains st = true) (he : m.e = false) : st ≠ .sE := by
  intro h; subst h; simp [RMask.contains, he] at hm

private theorem RMask.eq_e_of_anyNonE_false (m : RMask) (st : RState)
    (hm : m.contains st = true) (hn : m.anyNonE = false) : st = .sE := by
  cases st <;> simp_all [RMask.contains, RMask.anyNonE]

private def maskSGSA00 : RMask := ⟨true, false, false, false, false, true, false⟩
private def maskUA : RMask := ⟨true, true, false, true, false, true, true⟩

/-- Symbolic right-tail abstraction. -/
private inductive SymTail where
  | even0
  | any (m : RMask)
deriving DecidableEq

private def SymTail.mask : SymTail → RMask
  | .even0 => maskSGSA00
  | .any m => m

private def TailSat : SymTail → List RTok → Prop
  | .even0, W => GoodRetR (.r1 :: W)
  | .any m, W => m.contains (evalR W) = true

private theorem tailSat_mask (t : SymTail) (W : List RTok) (ht : TailSat t W) :
    t.mask.contains (evalR W) = true := by
  cases t with
  | any m => exact ht
  | even0 =>
    have hG := ht.1
    simp only [evalR] at hG
    simp only [SymTail.mask, maskSGSA00, RMask.contains]
    revert hG
    generalize evalR W = st
    cases st <;> decide

/-- Balanced binary tree storing the 132 concrete checkpoint left stacks. -/
private inductive LTree where
  | empty
  | leaf (L : List Bool)
  | node (l r : LTree)
deriving DecidableEq

private def LTree.In (L : List Bool) : LTree → Prop
  | .empty => False
  | .leaf L' => L = L'
  | .node l r => LTree.In L l ∨ LTree.In L r

private def LTree.checkAll (f : List Bool → Bool) : LTree → Bool
  | .empty => true
  | .leaf L => f L
  | .node l r => LTree.checkAll f l && LTree.checkAll f r

private theorem LTree.checkAll_sound (f : List Bool → Bool) (T : LTree)
    (h : LTree.checkAll f T = true) :
    ∀ L, LTree.In L T → f L = true := by
  induction T with
  | empty => intro _ hIn; exact False.elim hIn
  | leaf L' => intro L hIn; subst hIn; exact h
  | node l r ihl ihr =>
    simp only [LTree.checkAll, Bool.and_eq_true] at h
    intro L hIn
    rcases hIn with hl | hr
    · exact ihl h.1 L hl
    · exact ihr h.2 L hr

private def LTree.memByPath : List Bool → List Bool → LTree → Bool
  | [], L, .leaf L' => L == L'
  | false :: p, L, .node l _ => LTree.memByPath p L l
  | true :: p, L, .node _ r => LTree.memByPath p L r
  | _, _, _ => false

private theorem LTree.memByPath_sound (p : List Bool) (L : List Bool) (T : LTree)
    (h : LTree.memByPath p L T = true) : LTree.In L T := by
  induction p generalizing T with
  | nil =>
    cases T with
    | leaf L' => simp only [LTree.memByPath, beq_iff_eq] at h; exact h
    | empty | node _ _ => simp [LTree.memByPath] at h
  | cons b rest ih =>
    cases T with
    | node l r =>
      cases b with
      | false => exact Or.inl (ih l h)
      | true => exact Or.inr (ih r h)
    | empty | leaf _ => cases b <;> simp [LTree.memByPath] at h

/-- Compact prefix trie oracle mapping a checkpoint `L` to its 7-bit path in `cpTree`. -/
private inductive CPTrie where
  | tip (p : List Bool)
  | branch (e : List Bool) (l r : CPTrie)
deriving DecidableEq

private def CPTrie.lookup : CPTrie → List Bool → List Bool
  | .tip p, _ => p
  | .branch e _ _, [] => e
  | .branch _ l _, false :: rest => CPTrie.lookup l rest
  | .branch _ _ r, true :: rest => CPTrie.lookup r rest

private def cpTree : LTree :=
  (.node
  (.node
  (.node
  (.node
  (.node
  (.node
  (.node
  (.leaf [true, false, false, true, false, false, true, false, false, true, false, true, false,
      false, false, false, false, false, true, false, false, true, false, false])
  (.leaf [true, false, false, false, false, false, false, true, false, false, true, false, false,
      false, true, false, false, true, false, false, true, false, false, false, false, true]))
  (.node
  (.leaf [true, false, false, true, false, false, false, false, false, false, false, false, false,
      true, false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [true, false, false, false, false, false, false, false, false, false, false, true, false,
      true, false, false, false, false, false, false, false, false, true, false, false])))
  (.node
  (.node
  (.leaf [true, false, false, false, false, true, false, false, false, false, false, true, false,
      false, false, false, false, false, false, false, true, false, false])
  (.leaf [false, true, false, false, false, true, false, false, false, false, true, false, false,
      false, true, false, false, true, false, false, false, false]))
  (.node
  (.leaf [true, false, false, false, false, false, false, false, true, false, false, false, false,
      false, false, false, false, true, false, false])
  (.leaf [false, false, false, false, true, false, false, false, false, true, false, false, false,
      true, false, false, true, false, false, false, false]))))
  (.node
  (.node
  (.node
  (.leaf [false, true, false, false, false, true, false, false, true, false, false, true, false,
      false, false, true, false, false, true, false, false, false, false, false, false, false,
          false])
  (.leaf [true, false, false, false, false, true, false, false, false, true, false, false, true,
      false, false, false, false]))
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, true, false, false, true,
      false, false, false, false])
  (.leaf [false, false, false, false, true, false, false, true, false, false, true, false, false,
      false, true, false, false, true, false, false, false, false, false, false, false, false])))
  (.node
  (.node
  (.leaf [true, false, false, false, false, false, true, false, false, true, false, false, false,
      false])
  (.leaf [false, false, true, false, false, false, false, false, true, false, false, true, false,
      false, false, false]))
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, false, false, false, true,
      false, true, false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [true, false, false, false, false, false, false, false, false, true, false, true, false,
      false, true, false, false, true, false, false, false, false, true])))))
  (.node
  (.node
  (.node
  (.node
  (.leaf [true, false, false, true, false, false, true, false, false, false, true, false, false,
      true, false, false, false, false, false, false, false, false])
  (.leaf [false, false, true, false, false, false, false, false, false, false, false, true, false,
      true, false, false, true, false, false, true, false, false, false, false, true]))
  (.node
  (.leaf [true, false, false, true, false, false, false, true, false, false, true, false, false,
      true, false, false, false, false, true])
  (.leaf [false, true, false, false, false, true, false, false, true, false, false, false, false,
      true, false, true, false, false, true, false, false, false, false])))
  (.node
  (.node
  (.leaf [false, true, false, true, false, false, true, false, false, false, true, false, false,
      true, false, false, true, false, false, false, false, true])
  (.leaf [true, false, false, true, false, false, false, false, true, false, true, false, false,
      true, false, false, false, false]))
  (.node
  (.leaf [true, false, false, true, false, false, false, false, true, false, true, false, false,
      true, false, false, false, false, true])
  (.leaf [false, false, false, false, true, false, false, true, false, false, false, false, true,
      false, true, false, false, true, false, false, false, false]))))
  (.node
  (.node
  (.node
  (.leaf [false, false, true, false, false, true, false, false, false, true, false, false, true,
      false, false, true, false, false, false, false, true])
  (.leaf [true, false, false, true, false, false, true, false, false, true, false, false, false,
      true, false, false, true, false, false, false, false, false, false, false, false]))
  (.node
  (.leaf [true, false, false, false, false, false, false, true, false, false, false, false, true,
      false, true, false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [false, true, false, true, false, false, true, false, false, false, false, true, false,
      true, false, false, true, false, false, false, false, true])))
  (.node
  (.node
  (.leaf [true, false, false, false, false, true, false, false, true, false, false, false, true,
      false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [false, true, false, false, true, false, false, false, true, false, false, true, false,
      false, false, false, false, true, false, false, true, false, false, false, false]))
  (.node
  (.leaf [false, false, true, false, false, true, false, false, false, false, true, false, true,
      false, false, true, false, false, false, false, true])
  (.node
  (.leaf [true, false, false, false, false, true, false, false, false, true, false, false, true,
      false, false, true, false, false, false, false, true])
  (.leaf [false, false, false, true, false, false, false, true, false, false, true, false, false,
      false, false, false, true, false, false, true, false, false, false, false])))))))
  (.node
  (.node
  (.node
  (.node
  (.node
  (.leaf [true, false, false, false, false, false, true, false, false, true, false, false, true,
      false, false, false, false, true])
  (.leaf [false, false, false, false, true, false, false, true, false, false, false, false, false,
      true, false, false, true, false, false, false, false]))
  (.node
  (.leaf [true, false, false, false, false, false, false, false, false, false, true, false, false,
      true, false, false, false, false, true])
  (.leaf [true, false, false, true, false, false, false, false, false, true, false, false, true,
      false, false, false, false])))
  (.node
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, false, false, false, false,
      true, false, false, true, false, false, false, false, true])
  (.leaf [true, false, false, true, false, true, false, false, false, false, true, false, false,
      false, false, true, false, false, true, false, false]))
  (.node
  (.leaf [false, true, false, false, false, true, false, false, true, false, false, true, false,
      false, false, true, false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [false, false, true, false, false, false, false, false, false, false, false, false, true,
      false, false, true, false, false, false, false, true]))))
  (.node
  (.node
  (.node
  (.leaf [true, false, false, false, false, false, false, false, false, true, false, true, false,
      false, false, false, false, false, false, false, true, false, false])
  (.leaf [true, false, false, true, false, false, true, false, false, false, true, false, false,
      true, false, false, true, false, false, false, false, true]))
  (.node
  (.leaf [false, false, false, false, true, false, false, true, false, false, true, false, false,
      false, true, false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [false, true, false, true, false, false, true, false, true, false, false, false, false,
      true, false, false, false, false, true, false, false, true, false, false])))
  (.node
  (.node
  (.leaf [true, false, false, true, false, false, false, true, false, false, false, false, false,
      false, false, false, true, false, false])
  (.leaf [false, true, false, false, false, true, false, false, false, false, false, false, false,
      false, false, true, false, false, true, false, false, false, false]))
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, false, false, false, true,
      false, true, false, false, false, false, false, false, false, false, true, false, false])
  (.leaf [false, false, true, false, false, true, false, true, false, false, false, false, true,
      false, false, false, false, true, false, false, true, false, false])))))
  (.node
  (.node
  (.node
  (.node
  (.leaf [true, false, false, false, false, false, false, false, false, false, true, false, false,
      true, false, false, false, false])
  (.leaf [true, false, false, false, false, true, false, false, false, true, false, false, true,
      false, false, false, false, true]))
  (.node
  (.leaf [false, false, false, false, true, false, false, false, false, false, false, false, false,
      false, true, false, false, true, false, false, false, false])
  (.leaf [false, false, true, false, false, false, false, false, false, false, false, true, false,
      true, false, false, false, false, false, false, false, false, true, false, false])))
  (.node
  (.node
  (.leaf [false, true, false, false, true, false, false, true, false, false, false, true, false,
      false, true, false, false, true, false, false, false, true, false, false, true, false, false,
          false, false, true])
  (.leaf [true, false, false, false, false, false, true, false, false, true, false, false, false,
      false, true]))
  (.node
  (.leaf [false, true, false, true, false, false, false, false, true, false, false, false, true,
      false, false, true, false, false, false, false, true])
  (.leaf [false, true, false, true, false, false, true, false, false, false, true, false, false,
      false, false, false, false, false, false, true, false, false]))))
  (.node
  (.node
  (.node
  (.leaf [false, false, false, true, false, false, true, false, false, false, true, false, false,
      true, false, false, true, false, false, false, true, false, false, true, false, false, false,
          false, true])
  (.leaf [true, false, true, false, false, false, false, true, false, false, false, false, true,
      false, false, true, false, false]))
  (.node
  (.leaf [false, false, true, false, false, false, false, true, false, false, false, true, false,
      false, true, false, false, false, false, true])
  (.leaf [false, false, true, false, false, true, false, false, false, true, false, false, false,
      false, false, false, false, false, true, false, false])))
  (.node
  (.node
  (.leaf [false, false, false, true, false, false, false, true, false, false, true, false, false,
      true, false, false, false, true, false, false, true, false, false, false, false, true])
  (.leaf [true, false, true, false, false, false, false, false, false, true, false, false, true,
      false, false]))
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, true, false, false, true,
      false, false, false, false, true])
  (.node
  (.leaf [false, false, false, false, true, false, false, true, false, false, true, false, false,
      false, true, false, false, true, false, false, false, false, true])
  (.leaf [true, false, false, false, false, false, false, true, false, false, true, false, false,
      false, true, false, false, true, false, false, false, false, false, false, false,
          false]))))))))
  (.node
  (.node
  (.node
  (.node
  (.node
  (.node
  (.leaf [true, false, false, true, false, false, true, false, false, false, true, false, false,
      true, false, false, false, false, true])
  (.leaf [false, false, true, false, false, false, false, false, true, false, false, true, false,
      false, false, false, true]))
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, false, true, false, false,
      true, false, false, false, true, false, false, true, false, false, false, false, false, false,
          false, false])
  (.leaf [true, false, false, false, false, false, false, false, false, false, false, true, false,
      true, false, false, true, false, false, true, false, false, false, false, true])))
  (.node
  (.node
  (.leaf [true, false, false, true, false, false, false, false, false, false, false, false, false,
      true, false, false, true, false, false, false, false, false, false, false, false])
  (.leaf [false, true, false, true, false, true, false, false, false, false, true, false, false,
      false, false, true, false, false, true, false, false]))
  (.node
  (.leaf [false, false, true, false, false, false, false, false, false, true, false, false, true,
      false, false, false, true, false, false, true, false, false, false, false, false, false,
          false, false])
  (.leaf [false, true, false, false, true, false, false, false, true, false, false, true, false,
      false, true, false, true, false, false, false, false, false, false, true, false, false, true,
          false, false, true, false, false]))))
  (.node
  (.node
  (.node
  (.leaf [true, false, false, false, false, true, false, false, false, false, false, true, false,
      false, true, false, false, true, false, false, false, false, true])
  (.leaf [false, false, true, false, true, false, false, false, false, true, false, false, false,
      false, true, false, false, true, false, false]))
  (.node
  (.leaf [false, false, false, true, false, false, false, true, false, false, true, false, false,
      true, false, true, false, false, false, false, false, false, true, false, false, true, false,
          false, true, false, false])
  (.leaf [true, false, false, false, false, false, false, false, true, false, false, true, false,
      false, true, false, false, false, false, true])))
  (.node
  (.node
  (.leaf [false, true, false, true, false, true, false, false, false, false, false, false, true,
      false, false, true, false, false])
  (.leaf [false, false, false, false, true, false, false, true, false, false, true, false, true,
      false, false, false, false, false, false, true, false, false, true, false, false, true, false,
          false]))
  (.node
  (.leaf [true, false, false, true, false, true, false, false, false, false, false, false, false,
      false, true, false, false])
  (.leaf [false, false, true, false, true, false, false, false, false, false, false, true, false,
      false, true, false, false])))))
  (.node
  (.node
  (.node
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, false, true, false, false,
      false, true, false, false, true, false, false, true, false, false, false, false, true, false])
  (.leaf [true, false, false, false, false, false, false, true, false, false, false, true, false,
      false, true, false, false, true, false, false, false, false, true, false]))
  (.node
  (.leaf [true, false, false, true, false, false, true, false, true, false, false, false, false,
      false, false, true, false, false, true, false, false, true, false, false])
  (.leaf [false, false, true, false, false, false, false, false, false, true, false, false, false,
      true, false, false, true, false, false, true, false, false, false, false, true, false])))
  (.node
  (.node
  (.leaf [false, true, false, false, true, false, false, false, true, false, false, false, false,
      true, false, true, false, false, true, false, false, true, false, false, false])
  (.leaf [true, false, false, false, false, true, false, false, true, false, true, false, false,
      false, false, false, false, false, false, true, false, false, false]))
  (.node
  (.leaf [false, false, false, true, false, false, false, true, false, false, false, false, true,
      false, true, false, false, true, false, false, true, false, false, false])
  (.leaf [true, false, false, false, false, true, false, true, false, false, false, false, false,
      false, false, false, true, false, false, false]))))
  (.node
  (.node
  (.node
  (.leaf [false, false, false, false, true, false, false, false, false, true, false, true, false,
      false, true, false, false, true, false, false, false])
  (.leaf [true, false, false, false, true, false, false, false, false, false, false, false, false,
      true, false, false, false]))
  (.node
  (.leaf [false, true, false, true, false, false, false, true, false, false, true, false, false,
      true, false, false, false])
  (.leaf [false, true, false, false, true, false, false, false, true, false, false, false, false,
      false, false, true, false, true, false, false, false, false, false, false, true, false, false,
          true, false, false])))
  (.node
  (.node
  (.leaf [true, false, false, false, false, true, false, true, false, false, true, false, false,
      true, false, false, false])
  (.leaf [false, false, true, false, false, false, true, false, false, true, false, false, true,
      false, false, false]))
  (.node
  (.leaf [false, false, false, true, false, false, false, true, false, false, false, false, false,
      false, true, false, true, false, false, false, false, false, false, true, false, false, true,
          false, false])
  (.node
  (.leaf [true, false, false, false, true, false, false, true, false, false, true, false, false,
      false])
  (.leaf [false, true, false, true, false, true, false, false, false, false, false, false, true,
      false, false, false, false])))))))
  (.node
  (.node
  (.node
  (.node
  (.node
  (.leaf [false, false, false, false, true, false, false, false, false, false, false, true, false,
      true, false, false, false, false, false, false, true, false, false, true, false, false])
  (.leaf [true, false, true, false, false, false, false, false, false, true, false, false, false,
      false]))
  (.node
  (.leaf [false, false, true, false, true, false, false, false, false, false, false, true, false,
      false, false, false])
  (.leaf [false, true, false, true, false, false, true, false, false, false, false, false, true,
      false, false, true, false, false, false, false, false, false, false, false])))
  (.node
  (.node
  (.leaf [true, false, false, false, false, false, false, true, false, true, false, false, false,
      false, false, false, true, false, false, true, false, false])
  (.leaf [true, false, false, true, false, false, false, false, false, true, false, false, true,
      false, false, false, false, false, false, false, false]))
  (.node
  (.leaf [false, false, true, false, false, true, false, false, false, false, false, true, false,
      false, true, false, false, false, false, false, false, false, false])
  (.leaf [true, false, false, false, false, false, false, false, false, false, true, false, false,
      true, false, false, true, false, false, false, false, true]))))
  (.node
  (.node
  (.node
  (.leaf [true, false, false, false, false, true, false, false, false, true, false, false, false,
      false, false, false, false, false, true, false, false])
  (.leaf [false, true, false, false, true, false, false, false, true, false, false, false, false,
      false, true, false, false, false, false, false, false, true, false, false, true, false, false,
          true, false, false]))
  (.node
  (.leaf [true, false, false, false, false, false, true, false, false, false, false, false, false,
      false, false, true, false, false])
  (.leaf [false, false, false, true, false, false, false, true, false, false, false, false, false,
      true, false, false, false, false, false, false, true, false, false, true, false, false, true,
          false, false])))
  (.node
  (.node
  (.leaf [true, false, false, true, false, true, false, false, true, false, false, false, false])
  (.leaf [false, false, false, false, true, false, false, false, false, false, true, false, false,
      false, false, false, false, true, false, false, true, false, false, true, false, false]))
  (.node
  (.leaf [true, false, false, false, false, false, true, false, false, false, false, false, false,
      true, false, false, true, false, false, true, false, false])
  (.leaf [true, false, false, false, false, true, false, true, false, false, true, false, false,
      true, false, false, false, false, true, false])))))
  (.node
  (.node
  (.node
  (.node
  (.leaf [false, true, false, true, false, false, false, false, true, false, true, false, false,
      true, false, false, true, false, false, false, false, true, false])
  (.leaf [false, true, false, false, true, false, false, true, false, false, false, true, false,
      false, true, false, false, true, false, false, true, false, true, false, false, false, false,
          false, false, true, false, false, true, false, false]))
  (.node
  (.leaf [true, false, false, false, true, false, false, true, false, false, true, false, false,
      false, false, true, false])
  (.leaf [false, false, true, false, false, false, false, true, false, true, false, false, true,
      false, false, true, false, false, false, false, true, false])))
  (.node
  (.node
  (.leaf [false, false, false, true, false, false, true, false, false, false, true, false, false,
      true, false, false, true, false, false, true, false, true, false, false, false, false, false,
          false, true, false, false, true, false, false])
  (.leaf [true, false, true, false, false, false, false, false, false, false, false, true, false,
      false, false]))
  (.node
  (.leaf [false, true, false, true, false, false, false, true, false, false, true, false, false,
      true, false, false, false, false, true, false])
  (.leaf [false, false, false, true, false, false, false, true, false, false, true, false, false,
      true, false, false, true, false, true, false, false, false, false, false, false, true, false,
          false, true, false, false]))))
  (.node
  (.node
  (.node
  (.leaf [true, false, true, false, false, true, false, false, false, false, false])
  (.leaf [false, false, true, false, false, false, true, false, false, true, false, false, true,
      false, false, false, false, true, false]))
  (.node
  (.leaf [false, false, false, false, true, false, false, true, false, false, true, false, false,
      true, false, true, false, false, false, false, false, false, true, false, false, true, false,
          false])
  (.leaf [false, true, false, true, false, true, false, false, false, false, false, false, false,
      false, true, false, false, false])))
  (.node
  (.node
  (.leaf [false, true, false, true, false, false, false, false, false, false, true, false, false,
      true, false, false, false, true, false, false, true, false, false, true, false, false, false,
          false, true])
  (.leaf [false, false, true, false, true, false, false, false, false, false, false, false, false,
      true, false, false, false]))
  (.node
  (.leaf [false, false, true, false, false, false, false, false, false, true, false, false, true,
      false, false, false, true, false, false, true, false, false, true, false, false, false, false,
          true])
  (.node
  (.leaf [false, true, false, true, false, true, false, false, true, false, false, false, false,
      false])
  (.leaf [false, false, true, false, true, false, false, true, false, false, false, false,
      false])))))))))

private def cpTrie : CPTrie :=
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, false, false, true, false])
  (.tip [true, true, false, false, false, false, false]))
  (.tip [true, true, false, true, true, false, true]))
  (.branch []
  (.branch []
  (.tip [false, false, false, false, true, true, true])
  (.tip [true, false, true, true, false, false, false]))
  (.tip [])))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, false, false, false, true])
  (.tip [false, false, true, false, true, true, true]))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, false, true, false, true, true])
  (.tip [false, true, true, true, true, true, true, false]))
  (.tip []))
  (.tip [false, true, false, true, false, true, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip [true, true, true, true, false, true, false]))
  (.tip [true, false, false, true, true, false, true]))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, true, true, true, false])
  (.tip [true, true, false, true, false, true, true]))
  (.tip [true, false, true, false, true, true, false]))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, true, true, true, true, true, true])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, true, true, false, false])
  (.tip [true, true, true, false, true, true, true]))
  (.tip [true, false, false, true, false, true, false]))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, true, false, false, false])
  (.tip [true, true, true, false, true, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, false, true, true, true])
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, false, false, true, true])
  (.tip [false, false, true, false, false, false, true]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, false, false, true, true])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, false, false, true, true, false])
  (.tip [true, true, true, true, true, true, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, false, false, true, true, false, true]
  (.tip [])
  (.tip [true, false, false, false, false, false, true]))
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.tip [false, true, true, true, false, true, false])
  (.tip [true, true, true, false, false, true, true]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch [true, false, true, true, true, false, true]
  (.tip [true, true, true, true, false, false, true])
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, false, false, true, true, false])
  (.tip [false, false, true, true, true, true, false]))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, true, false, true, true])
  (.tip [false, false, true, true, false, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [false, true, false, true, true, true, true]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, true, true, true, false, true])
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, false, false, false, true, false])
  (.tip [true, false, false, true, true, true, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [true, false, false, true, false, false, true]))
  (.tip []))
  (.tip [true, true, true, true, true, true, true, true]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, true, true, false, true])
  (.tip [false, false, false, false, true, false, true]))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, true, false, false, true, true])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, false, true, false, false, false])
  (.tip [false, true, false, false, true, true, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, true, false, true, true])
  (.tip [true, true, false, true, false, false, true]))
  (.tip [true, false, true, false, true, false, false]))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, true, true, true, false, true])
  (.tip [true, false, false, false, true, true, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, false, true, false, false])
  (.tip [true, true, true, false, false, false, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, false, true, false, false])
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, true, true, true, false])
  (.tip [false, false, false, true, true, true, false]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, false, false, false, false])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, false, false, false, true, false])
  (.tip [true, true, true, true, true, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, false, false, true, false, true, false]
  (.tip [])
  (.tip [false, true, true, true, true, true, false]))
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.tip [false, true, true, false, true, true, false])
  (.tip [true, true, true, false, false, false, false]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch [true, false, true, true, false, true, false]
  (.tip [true, true, true, false, true, true, false])
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, false, false, false, true, true])
  (.tip [false, false, true, true, false, true, true]))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, false, true, true, true])
  (.tip [false, false, true, false, true, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [false, true, false, true, false, true, true]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, true, true, false, true, true])
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, true, true, true, true, true])
  (.tip [true, false, false, true, true, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [true, false, false, false, true, false, true]))
  (.tip []))
  (.tip [true, true, true, true, true, true, true, false]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, false, false, false, true, true])
  (.tip [true, false, false, false, false, true, true]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, true, true, false, false, false, false]
  (.tip [])
  (.tip [false, true, false, false, false, true, false]))
  (.tip []))
  (.tip [true, true, false, false, true, true, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, true, false, false, false])
  (.tip [false, false, false, true, true, true, true]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, false, false, true, true, false])
  (.tip [true, false, false, true, false, true, true]))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, true, true, false, true, false])
  (.tip [true, false, true, false, false, false, true]))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, true, true, true, true, true, true])
  (.tip [false, false, false, false, false, false, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip [true, true, false, false, true, false, false]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, false, true, false, true, false])
  (.tip [true, true, false, true, true, true, false]))
  (.tip []))
  (.tip []))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, false, false, true, true, false, false]
  (.tip [])
  (.tip [false, true, true, false, true, false, true]))
  (.tip []))
  (.tip [false, true, false, false, false, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, false, false, true, false, false])
  (.tip [true, false, false, true, false, false, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, false, true, false, false, false])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, false, false, true, false, false, true]
  (.tip [])
  (.tip [false, true, true, false, false, false, true]))
  (.tip []))
  (.tip [false, false, true, true, true, true, true, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.tip [false, false, true, true, true, false, false])
  (.tip [true, false, true, false, true, false, true]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, false, true, true, true])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch [true, false, true, true, true, false, false]
  (.tip [true, true, false, true, true, true, true])
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, true, true, false, false, true])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch [true, false, true, true, true, true, true, false]
  (.tip [true, true, true, false, false, true, false])
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, false, false, true, false, false])
  (.tip [false, false, false, false, false, true, false]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip []))
  (.tip []))
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, true, false, false, false, true, true]
  (.tip [true, true, false, false, true, false, true])
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch [false, false, true, false, true, false, true]
  (.tip [])
  (.tip [false, false, true, false, true, true, false]))
  (.tip []))
  (.tip []))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, true, false, true, true, false, false])
  (.tip [false, false, true, false, false, true, false]))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.tip [])
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [false, false, true, false, false, false, false])
  (.tip [true, false, false, false, false, false, false]))
  (.tip []))
  (.tip [false, true, false, true, false, false, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [])))
  (.branch []
  (.branch []
  (.tip [false, false, true, true, false, false, true])
  (.tip [false, false, false, false, false, false, false]))
  (.tip [])))
  (.tip [true, false, true, false, false, true, false]))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, false, false, true, true, true, false])
  (.tip [false, true, false, false, true, false, true]))
  (.tip []))
  (.tip [true, true, false, true, true, false, false]))
  (.tip []))
  (.tip [])))
  (.tip [])))
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, true, false, true, false, true])
  (.branch []
  (.branch []
  (.branch []
  (.tip [true, true, false, false, false, false, true])
  (.tip [false, true, true, true, true, false, true]))
  (.tip []))
  (.tip [])))
  (.tip []))
  (.tip [false, true, true, true, false, false, true]))
  (.tip []))
  (.tip [true, true, true, true, false, false, false]))
  (.tip []))
  (.tip [])))
  (.tip [])))

private def isCP (L : List Bool) : Bool :=
  LTree.memByPath (CPTrie.lookup cpTrie L) L cpTree

private theorem isCP_sound (L : List Bool) (h : isCP L = true) : LTree.In L cpTree :=
  LTree.memByPath_sound (CPTrie.lookup cpTrie L) L cpTree h

/-- Target invariant predicate `CPInv` on concrete machine configurations. -/
private def CPInv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ L R, LTree.In L cpTree ∧ GoodRetR R ∧ cfg = evalCfg (.mLD0, 0, L, R)

private theorem lead0_append_of_drop0_ne_nil (R W : List RTok) (h : (drop0 R).isEmpty = false) :
    lead0 (R ++ W) = lead0 R := by
  induction R with
  | nil => simp [drop0] at h
  | cons r rest ih =>
    cases r with
    | r0 => simp only [List.cons_append, lead0]; rw [ih h]
    | r1 | r2 | r3 => simp [lead0]

private theorem lead0_append_even0 (R W : List RTok) (hW : GoodRetR (.r1 :: W)) :
    lead0 (R ++ W) % 2 = lead0 R % 2 := by
  induction R with
  | nil =>
    rcases hW with ⟨_, ⟨U, hEq⟩ | ⟨U, hEq⟩ | ⟨U, hEq⟩⟩ <;>
      injection hEq with _ hTail <;> subst hTail <;> simp [lead0]
  | cons r rest ih =>
    cases r with
    | r0 => simp only [List.cons_append, lead0]; omega
    | r1 | r2 | r3 => simp [lead0]

private theorem lead0_append_ge (R W : List RTok) : lead0 R ≤ lead0 (R ++ W) := by
  induction R with
  | nil => simp [lead0]
  | cons r rest ih =>
    cases r with
    | r0 => simp only [List.cons_append, lead0]; omega
    | r1 | r2 | r3 => simp [lead0]

/-- Reflected bounded-fuel symbolic verifier proving `Advances target_tm (evalCfg s) CPInv`. -/
private def checkSym : ℕ → SegMode → ℕ → List Bool → List RTok → SymTail → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, .mRA, k, L, R, t =>
    let k2 := k + lead0 R
    let R2 := drop0 R
    match R2 with
    | .r2 :: rest =>
      checkSym fuel .mLD1 0 (oneRuns k2 L) (.r0 :: .r0 :: .r1 :: .r0 :: rest) t
    | .r3 :: rest =>
      checkSym fuel .mLD1 0 (oneRuns k2 L) (.r0 :: .r0 :: .r1 :: .r1 :: rest) t
    | .r1 :: .r1 :: rest =>
      checkSym fuel .mRA 3 (pushZeroL (oneRuns k2 L)) rest t
    | .r1 :: .r2 :: rest =>
      checkSym fuel .mRA 2 (pushZeroL (oneRuns k2 L)) (.r1 :: rest) t
    | .r1 :: .r3 :: rest =>
      checkSym fuel .mRA 2 (pushZeroL (oneRuns k2 L)) (.r2 :: rest) t
    | .r1 :: .r0 :: .r0 :: rest =>
      checkSym fuel .mLD1 0 (oneRuns k2 L) (.r0 :: .r0 :: .r1 :: .r1 :: rest) t
    | .r1 :: .r0 :: .r1 :: rest =>
      checkSym fuel .mLD1 0 (oneRuns k2 L) (.r0 :: .r0 :: .r1 :: .r2 :: rest) t
    | .r1 :: .r0 :: .r2 :: rest =>
      checkSym fuel .mLD1 0 (oneRuns k2 L) (.r0 :: .r0 :: .r1 :: .r3 :: rest) t
    | .r1 :: .r0 :: [] =>
      match t with
      | .even0 =>
        checkSym fuel .mLD1 0 (oneRuns k2 L) [.r0, .r0, .r1, .r1, .r0, .r1] (.any maskUA) &&
        checkSym fuel .mLD1 0 (oneRuns k2 L) [.r0, .r0, .r1, .r2] (.any maskSGSA00) &&
        checkSym fuel .mLD1 0 (oneRuns k2 L) [.r0, .r0, .r1, .r3] (.any maskSGSA00)
      | .any _ =>
        if decide (2 ≤ k2) then
          isCP (if k2 % 2 == 0 then L else false :: L)
        else false
    | _ =>
      -- Try Call-Return closure if `k2 ≥ 2` and `lead0 (R ++ W) % 2` is determined!
      let parKnown := !R2.isEmpty || (t == .even0)
      if decide (2 ≤ k2) && parKnown then
        isCP (if k2 % 2 == 0 then L else false :: L)
      else false
  | fuel + 1, .mRAE, _, L, R, t =>
    match R with
    | .r1 :: .r1 :: rest =>
      let mNext := RMask.evalPrefix rest t.mask
      let L' := true :: false :: false :: L
      let okE := !mNext.e || checkSym fuel .mRAE 3 L' rest t
      let okA := !mNext.anyNonE || checkSym fuel .mRA 3 L' rest t
      okE && okA
    | .r1 :: .r0 :: .r1 :: rest =>
      let L' := match L with
        | [] => [true, false, false, false]
        | _ :: L'' => true :: false :: false :: false :: false :: L''
      checkSym fuel .mRA 2 L' (.r1 :: rest) t
    | _ => false
  | fuel + 1, .mLD1, _, L, R, t =>
    match L with
    | [] => checkSym fuel .mRA 1 [] R t
    | [false] =>
      match R with
      | .r0 :: .r0 :: rest =>
        let R' := .r1 :: rest
        let mNext := RMask.evalPrefix R' t.mask
        let okE := !mNext.e || checkSym fuel .mRAE 3 [] R' t
        let okA := !mNext.anyNonE || checkSym fuel .mRA 3 [] R' t
        okE && okA
      | _ => false
    | false :: false :: L' =>
      checkSym fuel .mLD0 0 L' (.r1 :: R) t
    | _ => false
  | fuel + 1, .mLD0, _, L, R, t =>
    match L, R with
    | [], _ => checkSym fuel .mRA 1 [] R t
    | [false], .r1 :: rest => checkSym fuel .mRA 1 [] (.r0 :: rest) t
    | false :: false :: L', _ => checkSym fuel .mLD0 0 L' (.r1 :: R) t
    | true :: false :: L', .r1 :: rest => checkSym fuel .mLD0 0 L' (.r1 :: .r2 :: rest) t
    | false :: true :: L', .r1 :: rest => checkSym fuel .mRA 2 L' (.r0 :: rest) t
    | _, _ => false

private theorem stepRALoop_append_drop0 (k : ℕ) (L : List Bool) (R W : List RTok)
    (h : (drop0 R).isEmpty = false) :
    stepRALoop k L (R ++ W) = stepRALoop (k + lead0 R) L (drop0 R ++ W) := by
  induction R generalizing k with
  | nil => simp [drop0] at h
  | cons r rest ih =>
    cases r with
    | r0 =>
      simp only [List.cons_append, stepRALoop, lead0, drop0]
      rw [ih (k + 1) h]
      congr 1; omega
    | r1 | r2 | r3 => simp [lead0, drop0]

private theorem evalR_ne_sBad_of_valid {m : SegMode} {k : ℕ} {L : List Bool} {Rs : List RTok}
    (hv : ValidSeg (m, k, L, Rs)) : evalR Rs ≠ .sBad := by
  have hm := hv.2
  cases m <;> simp only [validMode, Bool.and_eq_true, beq_iff_eq] at hm
  · intro h; rw [h] at hm; simp [isRARState] at hm
  · rw [hm.2]; decide
  · intro h; rw [h] at hm; simp [isLD1RState] at hm
  · rw [hm.2]; decide

/-- Soundness of the reflected symbolic verifier `checkSym`:
    if `checkSym fuel m k L R t = true`, then for every tail `W` satisfying `TailSat t W`
    such that `ValidSeg (m, k, L, R ++ W)`, the concrete state strictly `Advances` to `CPInv`. -/
private theorem checkSym_sound (fuel : ℕ) :
    ∀ (m : SegMode) (k : ℕ) (L : List Bool) (R : List RTok) (t : SymTail),
      checkSym fuel m k L R t = true →
      ∀ (W : List RTok), TailSat t W → ValidSeg (m, k, L, R ++ W) →
        Advances target_tm (evalCfg (m, k, L, R ++ W)) CPInv := by
  induction fuel with
  | zero => intro _ _ _ _ _ hc; simp [checkSym] at hc
  | succ fuel ih =>
    intro m k L R t hc W hW hv
    cases m with
    | mRA =>
      -- Re-prove hCallLeaf directly with `hv : ValidSeg (.mRA, k, L, R ++ W)` (clean, complete)
      have hCallRA :
          2 ≤ k + lead0 R →
          ((drop0 R).isEmpty = false ∨ t = .even0) →
          isCP (if (k + lead0 R) % 2 == 0 then L else false :: L) = true →
          Advances target_tm (evalCfg (.mRA, k, L, R ++ W)) CPInv := by
        intro hkR hParKind hcp
        have hk2 : 2 ≤ k + lead0 (R ++ W) :=
            le_trans hkR (Nat.add_le_add_left (lead0_append_ge R W) k)
        have hParEq : (k + lead0 (R ++ W)) % 2 = (k + lead0 R) % 2 := by
          rcases hParKind with hne | rfl
          · rw [lead0_append_of_drop0_ne_nil R W hne]
          · have := lead0_append_even0 R W hW; omega
        have hCP := isCP_sound _ hcp
        exact (callRA_advances k L (R ++ W) hk2 hv).mono (fun d hd => by
          rcases hd with ⟨R', hGood', rfl⟩
          refine ⟨if (k + lead0 (R ++ W)) % 2 = 0 then L else false :: L, R', ?_, hGood', rfl⟩
          rw [hParEq]
          by_cases h0 : (k + lead0 R) % 2 = 0
          · simp only [h0, beq_iff_eq, ↓reduceIte] at hCP ⊢; exact hCP
          · simp only [h0, beq_iff_eq, ↓reduceIte] at hCP ⊢; exact hCP)
      dsimp only [checkSym] at hc
      generalize hD : drop0 R = R2 at hc
      have hStepRA := step_RA_sound k L (R ++ W) hv
      cases R2 with
      | nil =>
        simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or] at hc
        by_cases hg : (decide (2 ≤ k + lead0 R) && (t == .even0)) = true
        · simp only [hg, ↓reduceIte] at hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
          exact hCallRA hg.1 (Or.inr hg.2) hc
        · simp only [hg] at hc; simp at hc
      | cons t0 rest0 =>
        have hne : (drop0 R).isEmpty = false := by rw [hD]; rfl
        have hLoop := stepRALoop_append_drop0 k L R W hne
        rw [hD] at hLoop
        cases t0 with
        | r0 =>
          exfalso
          have hNo := drop0_head_ne_r0 R
          rw [hD] at hNo
          exact hNo
        | r2 =>
          rw [hLoop] at hStepRA
          simp only [List.cons_append, stepRALoop] at hStepRA
          exact Advances.of_stepPlus_leads hStepRA.2
            (ih .mLD1 0 (oneRuns (k + lead0 R) L) (.r0 :: .r0 :: .r1 :: .r0 ::
                rest0) t hc W hW hStepRA.1).to_leads
        | r3 =>
          rw [hLoop] at hStepRA
          simp only [List.cons_append, stepRALoop] at hStepRA
          exact Advances.of_stepPlus_leads hStepRA.2
            (ih .mLD1 0 (oneRuns (k + lead0 R) L) (.r0 :: .r0 :: .r1 :: .r1 ::
                rest0) t hc W hW hStepRA.1).to_leads
        | r1 =>
          cases rest0 with
          | nil =>
            simp only [List.isEmpty_cons, Bool.not_false, Bool.true_or, Bool.and_true] at hc
            by_cases hg : decide (2 ≤ k + lead0 R) = true
            · simp only [hg, ↓reduceIte] at hc
              simp only [decide_eq_true_eq] at hg
              exact hCallRA hg (Or.inl hne) hc
            · simp only [hg] at hc; simp at hc
          | cons t1 rest1 =>
            cases t1 with
            | r1 =>
              rw [hLoop] at hStepRA
              simp only [List.cons_append, stepRALoop] at hStepRA
              exact Advances.of_stepPlus_leads hStepRA.2
                (ih .mRA 3 (pushZeroL (oneRuns (k + lead0 R) L)) rest1 t hc W hW hStepRA.1).to_leads
            | r2 =>
              rw [hLoop] at hStepRA
              simp only [List.cons_append, stepRALoop] at hStepRA
              exact Advances.of_stepPlus_leads hStepRA.2
                (ih .mRA 2 (pushZeroL (oneRuns (k + lead0 R) L)) (.r1 ::
                    rest1) t hc W hW hStepRA.1).to_leads
            | r3 =>
              rw [hLoop] at hStepRA
              simp only [List.cons_append, stepRALoop] at hStepRA
              exact Advances.of_stepPlus_leads hStepRA.2
                (ih .mRA 2 (pushZeroL (oneRuns (k + lead0 R) L)) (.r2 ::
                    rest1) t hc W hW hStepRA.1).to_leads
            | r0 =>
              cases rest1 with
              | nil =>
                cases t with
                | any _ =>
                  by_cases hg : decide (2 ≤ k + lead0 R) = true
                  · simp only [hg, ↓reduceIte] at hc
                    simp only [decide_eq_true_eq] at hg
                    exact hCallRA hg (Or.inl hne) hc
                  · simp only [hg] at hc; simp at hc
                | even0 =>
                  simp only [Bool.and_eq_true] at hc
                  rcases hc with ⟨⟨hc1, hc2⟩, hc3⟩
                  rw [hLoop] at hStepRA
                  dsimp only [TailSat, GoodRetR] at hW
                  rcases hW with ⟨hGW, ⟨U, hEq⟩ | ⟨U, hEq⟩ | ⟨U, hEq⟩⟩
                  · injection hEq with _ hW'
                    subst hW'
                    simp only [List.cons_append, List.nil_append, stepRALoop] at hStepRA
                    have hU : maskUA.contains (evalR U) = true := by
                      simp only [evalR] at hGW
                      simp only [maskUA, RMask.contains]
                      revert hGW
                      generalize evalR U = st
                      cases st <;> decide
                    exact Advances.of_stepPlus_leads hStepRA.2
                      (ih .mLD1 0 (oneRuns (k + lead0 R) L) [.r0, .r0, .r1, .r1, .r0,
                          .r1] (.any maskUA) hc1 U hU hStepRA.1).to_leads
                  · injection hEq with _ hW'
                    subst hW'
                    simp only [List.cons_append, List.nil_append, stepRALoop] at hStepRA
                    have hU : maskSGSA00.contains (evalR U) = true := by
                      simp only [evalR] at hGW
                      simp only [maskSGSA00, RMask.contains]
                      revert hGW
                      generalize evalR U = st
                      cases st <;> decide
                    exact Advances.of_stepPlus_leads hStepRA.2
                      (ih .mLD1 0 (oneRuns (k + lead0 R) L) [.r0, .r0, .r1,
                          .r2] (.any maskSGSA00) hc2 U hU hStepRA.1).to_leads
                  · injection hEq with _ hW'
                    subst hW'
                    simp only [List.cons_append, List.nil_append, stepRALoop] at hStepRA
                    have hU : maskSGSA00.contains (evalR U) = true := by
                      simp only [evalR] at hGW
                      simp only [maskSGSA00, RMask.contains]
                      revert hGW
                      generalize evalR U = st
                      cases st <;> decide
                    exact Advances.of_stepPlus_leads hStepRA.2
                      (ih .mLD1 0 (oneRuns (k + lead0 R) L) [.r0, .r0, .r1,
                          .r3] (.any maskSGSA00) hc3 U hU hStepRA.1).to_leads
              | cons t2 rest2 =>
                cases t2 with
                | r0 =>
                  rw [hLoop] at hStepRA
                  simp only [List.cons_append, stepRALoop] at hStepRA
                  exact Advances.of_stepPlus_leads hStepRA.2
                    (ih .mLD1 0 (oneRuns (k + lead0 R) L) (.r0 :: .r0 :: .r1 :: .r1 ::
                        rest2) t hc W hW hStepRA.1).to_leads
                | r1 =>
                  rw [hLoop] at hStepRA
                  simp only [List.cons_append, stepRALoop] at hStepRA
                  exact Advances.of_stepPlus_leads hStepRA.2
                    (ih .mLD1 0 (oneRuns (k + lead0 R) L) (.r0 :: .r0 :: .r1 :: .r2 ::
                        rest2) t hc W hW hStepRA.1).to_leads
                | r2 =>
                  rw [hLoop] at hStepRA
                  simp only [List.cons_append, stepRALoop] at hStepRA
                  exact Advances.of_stepPlus_leads hStepRA.2
                    (ih .mLD1 0 (oneRuns (k + lead0 R) L) (.r0 :: .r0 :: .r1 :: .r3 ::
                        rest2) t hc W hW hStepRA.1).to_leads
                | r3 =>
                  simp only [List.isEmpty_cons, Bool.not_false, Bool.true_or, Bool.and_true] at hc
                  by_cases hg : decide (2 ≤ k + lead0 R) = true
                  · simp only [hg, ↓reduceIte] at hc
                    simp only [decide_eq_true_eq] at hg
                    exact hCallRA hg (Or.inl hne) hc
                  · simp only [hg] at hc; simp at hc
    | mRAE =>
      dsimp only [checkSym] at hc
      have hStep := step_RAE_sound k L (R ++ W) hv
      rcases R with _ | ⟨t0, _ | ⟨t1, rest1⟩⟩
      · simp at hc
      · simp at hc
      · cases t0 with
        | r0 | r2 | r3 => simp at hc
        | r1 =>
          cases t1 with
          | r2 | r3 => simp at hc
          | r1 =>
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
            simp only [List.cons_append, stepRAE] at hStep
            have hmW := tailSat_mask t W hW
            by_cases hE : evalR (rest1 ++ W) = .sE
            · simp only [hE, beq_self_eq_true, ↓reduceIte] at hStep
              have hnb : evalR (rest1 ++ W) ≠ .sBad := by rw [hE]; decide
              have hIn := RMask.evalPrefix_sound rest1 W t.mask hmW hnb
              have hcE : checkSym fuel .mRAE 3 (true :: false :: false :: L) rest1 t = true := by
                rcases hc.1 with hfe | hok
                · exact False.elim (RMask.not_e_of_false _ _ hIn hfe hE)
                · exact hok
              exact Advances.of_stepPlus_leads hStep.2
                (ih .mRAE 3 (true :: false :: false :: L) rest1 t hcE W hW hStep.1).to_leads
            · have hbeq : (evalR (rest1 ++ W) == .sE) = false := beq_false_of_ne hE
              simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hStep
              have hnb := evalR_ne_sBad_of_valid hStep.1
              have hIn := RMask.evalPrefix_sound rest1 W t.mask hmW hnb
              have hcA : checkSym fuel .mRA 3 (true :: false :: false :: L) rest1 t = true := by
                rcases hc.2 with hfn | hok
                · exact False.elim (hE (RMask.eq_e_of_anyNonE_false _ _ hIn hfn))
                · exact hok
              exact Advances.of_stepPlus_leads hStep.2
                (ih .mRA 3 (true :: false :: false :: L) rest1 t hcA W hW hStep.1).to_leads
          | r0 =>
            rcases rest1 with _ | ⟨t2, rest2⟩
            · simp at hc
            · cases t2 with
              | r0 | r2 | r3 => simp at hc
              | r1 =>
                simp only [List.cons_append, stepRAE] at hStep
                cases L with
                | nil =>
                  exact Advances.of_stepPlus_leads hStep.2
                    (ih .mRA 2 [true, false, false,
                        false] (.r1 :: rest2) t hc W hW hStep.1).to_leads
                | cons _ L'' =>
                  exact Advances.of_stepPlus_leads hStep.2
                    (ih .mRA 2 (true :: false :: false :: false :: false :: L'') (.r1 ::
                        rest2) t hc W hW hStep.1).to_leads
    | mLD1 =>
      dsimp only [checkSym] at hc
      have hStep := step_LD1_sound k L (R ++ W) hv
      rcases L with _ | ⟨b0, _ | ⟨b1, L'⟩⟩
      · simp only [stepLD1] at hStep
        exact Advances.of_stepPlus_leads hStep.2
          (ih .mRA 1 [] R t hc W hW hStep.1).to_leads
      · cases b0 with
        | true => simp at hc
        | false =>
          rcases R with _ | ⟨t0, _ | ⟨t1, rest⟩⟩
          · simp at hc
          · simp at hc
          · cases t0 with
            | r1 | r2 | r3 => simp at hc
            | r0 =>
              cases t1 with
              | r1 | r2 | r3 => simp at hc
              | r0 =>
                simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
                simp only [List.cons_append, stepLD1] at hStep
                have hmW := tailSat_mask t W hW
                by_cases hE : evalR (.r1 :: (rest ++ W)) = .sE
                · simp only [hE, beq_self_eq_true, ↓reduceIte] at hStep
                  have hnb : evalR ((.r1 :: rest) ++ W) ≠ .sBad := by simp [hE]
                  have hIn := RMask.evalPrefix_sound (.r1 :: rest) W t.mask hmW hnb
                  have hcE : checkSym fuel .mRAE 3 [] (.r1 :: rest) t = true := by
                    rcases hc.1 with hfe | hok
                    · exact False.elim (RMask.not_e_of_false _ _ hIn hfe (by simpa using hE))
                    · exact hok
                  exact Advances.of_stepPlus_leads hStep.2
                    (ih .mRAE 3 [] (.r1 :: rest) t hcE W hW hStep.1).to_leads
                · have hbeq : (evalR (.r1 :: (rest ++ W)) == .sE) = false := beq_false_of_ne hE
                  simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hStep
                  have hnb := evalR_ne_sBad_of_valid hStep.1
                  have hIn := RMask.evalPrefix_sound (.r1 :: rest) W t.mask hmW hnb
                  have hcA : checkSym fuel .mRA 3 [] (.r1 :: rest) t = true := by
                    rcases hc.2 with hfn | hok
                    · exact False.elim (hE (RMask.eq_e_of_anyNonE_false _ _ hIn hfn))
                    · exact hok
                  exact Advances.of_stepPlus_leads hStep.2
                    (ih .mRA 3 [] (.r1 :: rest) t hcA W hW hStep.1).to_leads
      · cases b0 with
        | true => simp at hc
        | false =>
          cases b1 with
          | true => simp at hc
          | false =>
            simp only [stepLD1] at hStep
            exact Advances.of_stepPlus_leads hStep.2
              (ih .mLD0 0 L' (.r1 :: R) t hc W hW hStep.1).to_leads
    | mLD0 =>
      dsimp only [checkSym] at hc
      rcases L with _ | ⟨b0, _ | ⟨b1, L'⟩⟩
      · have hStep := step_LD0_sound k [] (R ++ W) (.mRA, 1, [], R ++ W) hv rfl
        exact Advances.of_stepPlus_leads hStep.2
          (ih .mRA 1 [] R t hc W hW hStep.1).to_leads
      · cases b0 with
        | true => simp at hc
        | false =>
          rcases R with _ | ⟨t0, rest⟩
          · simp at hc
          · cases t0 with
            | r0 | r2 | r3 => simp at hc
            | r1 =>
              have hStep :=
                  step_LD0_sound k [false] (.r1 :: (rest ++ W)) (.mRA, 1, [],
                  .r0 :: (rest ++ W)) hv rfl
              exact Advances.of_stepPlus_leads hStep.2
                (ih .mRA 1 [] (.r0 :: rest) t hc W hW hStep.1).to_leads
      · cases b0 with
        | false =>
          cases b1 with
          | false =>
            have hStep :=
                step_LD0_sound k (false :: false :: L') (R ++ W) (.mLD0, 0, L',
                .r1 :: (R ++ W)) hv rfl
            exact Advances.of_stepPlus_leads hStep.2
              (ih .mLD0 0 L' (.r1 :: R) t hc W hW hStep.1).to_leads
          | true =>
            rcases R with _ | ⟨t0, rest⟩
            · simp at hc
            · cases t0 with
              | r0 | r2 | r3 => simp at hc
              | r1 =>
                have hStep := step_LD0_sound k (false :: true :: L') (.r1 :: (rest ++ W))
                  (.mRA, 2, L', .r0 :: (rest ++ W)) hv rfl
                exact Advances.of_stepPlus_leads hStep.2
                  (ih .mRA 2 L' (.r0 :: rest) t hc W hW hStep.1).to_leads
        | true =>
          cases b1 with
          | true => simp at hc
          | false =>
            rcases R with _ | ⟨t0, rest⟩
            · simp at hc
            · cases t0 with
              | r0 | r2 | r3 => simp at hc
              | r1 =>
                have hStep := step_LD0_sound k (true :: false :: L') (.r1 :: (rest ++ W))
                  (.mLD0, 0, L', .r1 :: .r2 :: (rest ++ W)) hv rfl
                exact Advances.of_stepPlus_leads hStep.2
                  (ih .mLD0 0 L' (.r1 :: .r2 :: rest) t hc W hW hStep.1).to_leads

/-- Kernel-decided check that every one of the 132 checkpoints satisfies `validL` and closes in ≤
    250 steps. -/
private def checkAllCPs : Bool :=
  LTree.checkAll (fun L => validL L && checkSym 250 .mLD0 0 L [.r1] .even0) cpTree

private theorem checkAllCPs_true : checkAllCPs = true := by
  decide +kernel

private theorem cpInv_advances : ∀ cfg, CPInv cfg → Advances target_tm cfg CPInv := by
  rintro cfg ⟨L, R, hIn, hGood, rfl⟩
  have hCheck := LTree.checkAll_sound _ cpTree checkAllCPs_true L hIn
  simp only [Bool.and_eq_true] at hCheck
  obtain ⟨W, rfl⟩ : ∃ W, R = .r1 :: W := by
    rcases hGood with ⟨_, ⟨U, rfl⟩ | ⟨U, rfl⟩ | ⟨U, rfl⟩⟩
    · exact ⟨.r0 :: .r0 :: .r1 :: U, rfl⟩
    · exact ⟨.r1 :: U, rfl⟩
    · exact ⟨.r2 :: U, rfl⟩
  have hv : ValidSeg (.mLD0, 0, L, [.r1] ++ W) :=
    ⟨hCheck.1, by simp [validMode, startsWith1, hGood.1]⟩
  exact checkSym_sound 250 .mLD0 0 L [.r1] .even0 hCheck.2 W hGood hv

/-! ### 32-Macro-Step Initial Orbit Bridge `init [] ⊢* cp62` -/

/-- Iterates `stepMacro` for `n` macro steps. -/
private def runMacro : ℕ → SegState → Option SegState
  | 0, s => some s
  | n + 1, s =>
    match stepMacro s with
    | some s' => runMacro n s'
    | none => none

private theorem runMacro_sound (n : ℕ) :
    ∀ s s', ValidSeg s → runMacro n s = some s' →
      ValidSeg s' ∧ ((evalCfg s) [target_tm]⊢* evalCfg s') := by
  induction n with
  | zero =>
    intro s s' hv h
    simp only [runMacro, Option.some.injEq] at h
    subst h
    exact ⟨hv, stepStar_refl target_tm (evalCfg s)⟩
  | succ n ih =>
    intro s s' hv h
    simp only [runMacro] at h
    cases h1 : stepMacro s with
    | none => simp [h1] at h
    | some s1 =>
      rw [h1] at h
      rcases segmented_step_sound s s1 hv h1 with ⟨hv1, hp1⟩
      rcases ih s1 s' hv1 h with ⟨hv', hs'⟩
      exact ⟨hv', stepPlus_stepStar (stepPlus_stepStar_trans hp1 hs')⟩

private def cpInitL : List Bool :=
    [true, false, true, false, false, false, false, false, false, true, false, false, true, false,
    false]
private def cpInitR : List RTok := [.r1, .r0, .r0, .r1]

private theorem runMacro_32 : runMacro 32 s₀ = some (.mLD0, 0, cpInitL, cpInitR) := by
  decide +kernel

private theorem cpInitL_in : LTree.In cpInitL cpTree :=
  isCP_sound cpInitL (by decide +kernel)

private theorem cpInitR_good : GoodRetR cpInitR :=
  ⟨rfl, Or.inl ⟨[], rfl⟩⟩


private theorem is_does_not_halt : IsNotHalt target_tm := by
  have h32 := (runMacro_sound 32 s₀ (.mLD0, 0, cpInitL, cpInitR) valid_s₀ runMacro_32).2
  have hInit : (init []) [target_tm]⊢* evalCfg (.mLD0, 0, cpInitL, cpInitR) :=
    stepPlus_stepStar (stepPlus_stepStar_trans init_reaches_s₀ h32)
  exact does_not_halt_of_advances hInit ⟨cpInitL, cpInitR, cpInitL_in, cpInitR_good,
      rfl⟩ cpInv_advances


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE
