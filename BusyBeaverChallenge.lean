/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
meta import Lean.Elab.Term

/-! # Busy Beaver Challenge Specification (`BusyBeaverChallenge`) -/

@[expose] public section

namespace ConjectureMachines
open Turing

/-- A Turing machine transition table over `states` states and `symbols` symbols. -/
structure Machine (states symbols : ℕ) where
  transition : Fin states → Fin symbols → Option (Fin symbols × Dir × Fin states)

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- Build a `Machine states symbols` from a list of per-state transition rows. -/
def Machine.ofRows (rows : List (List (Option (Fin symbols × Dir × Fin states)))) :
    Machine states symbols := ⟨fun q a => (rows.getD q.val []).getD a.val none⟩

end ConjectureMachines
end

meta section
namespace BusyBeaver
open Lean Elab Term

private def parseRleBlock (block : String) : TermElabM (TSyntax `term) := do
  let chars := block.toList
  if chars.length == 0 || chars.length % 3 != 0 then
    throwError "Invalid RLE state block length: {block}"
  let numSymbols := chars.length / 3
  let mut cellStxs : Array (TSyntax `term) := #[]
  for i in [:numSymbols] do
    let wChar := chars[3 * i]!
    let dChar := chars[3 * i + 1]!
    let sChar := chars[3 * i + 2]!
    if wChar == '-' && dChar == '-' && sChar == '-' then
      cellStxs := cellStxs.push (← `(none))
    else
      if !wChar.isDigit then
        throwError "Invalid symbol character '{wChar}' in RLE block: {block}"
      let wLit := Syntax.mkNumLit (String.singleton wChar)
      let dirStx ← match dChar with
        | 'L' => `(Turing.Dir.left)
        | 'R' => `(Turing.Dir.right)
        | _ => throwError "Invalid direction '{dChar}' in RLE block: {block}"
      if sChar < 'A' || sChar > 'Z' then
        throwError "Invalid state letter '{sChar}' in RLE block: {block}"
      let stateIdx := sChar.toNat - 'A'.toNat
      let sLit := Syntax.mkNumLit (toString stateIdx)
      cellStxs := cellStxs.push (← `(some ($wLit, $dirStx, $sLit)))
  `([$cellStxs,*])

elab "load_rle_rows% " rle:str : term <= expectedType? => do
  let blocks := rle.getString.trimAscii.toString.splitOn "_"
  if blocks.isEmpty then
    throwError "Empty RLE string"
  let mut rowStxs : Array (TSyntax `term) := #[]
  for b in blocks do
    rowStxs := rowStxs.push (← parseRleBlock b)
  elabTerm (← `([$rowStxs,*])) expectedType?

elab "load_rle_machine% " rle:str : term <= expectedType? => do
  let blocks := rle.getString.trimAscii.toString.splitOn "_"
  if blocks.isEmpty then
    throwError "Empty RLE string"
  let mut rowStxs : Array (TSyntax `term) := #[]
  for b in blocks do
    rowStxs := rowStxs.push (← parseRleBlock b)
  elabTerm (← `(ConjectureMachines.Machine.ofRows [$rowStxs,*])) expectedType?

end BusyBeaver
end

@[expose] public section

namespace BusyBeaver
open Relation Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- A Turing machine statement writing `symbol` and moving the tape head in direction `dir`. -/
structure Stmt (Γ : Type*) where
  /-- Construct a write-and-move statement. -/
  write ::
  /-- Symbol written to the tape cell under the head. -/
  symbol : Γ
  /-- Direction in which the tape head moves after writing. -/
  dir : Dir
  deriving Inhabited

/-- A Post-Turing machine with symbol type `Γ` and state label type `Λ`. -/
@[nolint unusedArguments]
def Machine (Γ Λ : Type*) [Inhabited Λ] :=
  Λ → Γ → Option (Option Λ × Stmt Γ)

omit [Inhabited Γ] in
instance Machine.inhabited : Inhabited (Machine Γ Λ) := by
  unfold Machine; infer_instance

/-- Instantaneous configuration of a Turing machine: optional control state `q` and `tape`. -/
@[ext]
structure Cfg (Γ Λ : Type*) [Inhabited Γ] where
  /-- Current control state (`none` represents an explicit terminal state). -/
  q : Option Λ
  /-- Current doubly-infinite tape centered at the head. -/
  tape : Tape Γ

instance Cfg.inhabited : Inhabited (Cfg Γ Λ) := ⟨⟨default, default⟩⟩

/-- Configuration in state `q` with the tape head reading the first symbol of `r`. -/
def Cfg.headRight {Γ Λ : Type*} [Inhabited Γ] (q : Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  ⟨some q, ⟨r.head, l, r.tail⟩⟩

/-- Configuration in state `q` with the tape head reading the first symbol of `l`. -/
def Cfg.headLeft {Γ Λ : Type*} [Inhabited Γ] (q : Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  ⟨some q, ⟨l.head, l.tail, r⟩⟩

/-- Single-step execution semantics of a `BusyBeaver.Machine`. -/
def step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ)
  | ⟨none, _⟩ => none
  | ⟨some q, T⟩ =>
    (M q T.1).map fun ⟨q', a⟩ ↦
      ⟨q', match a with | Stmt.write a d => (T.write a).move d⟩

/-- Initial configuration on tape prefix `l` (all-blank tape when `l = []`). -/
def init (l : List Γ) : Cfg Γ Λ := ⟨some default, Tape.mk₁ l⟩

/-- Multi-step execution semantics (`n` steps). -/
def multiStep (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) : Option (Cfg Γ Λ) :=
  (Option.bind · (step M))^[n] config

/-- Exact `n`-step reachability (`multiStep M c₁ n = some c₂`). -/
def ReachesIn (M : Machine Γ Λ) (n : ℕ) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  multiStep M c₁ n = some c₂

/-- Reflexive-transitive multi-step reachability (`∃ n, multiStep M c₁ n = some c₂`). -/
def ReachesStar (M : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  ∃ n, multiStep M c₁ n = some c₂

/-- Non-empty transitive multi-step reachability (`∃ n > 0, multiStep M c₁ n = some c₂`). -/
def ReachesPlus (M : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  ∃ n > 0, multiStep M c₁ n = some c₂

/-- Repeat finite list `l` `n` times (`l ^ n`). -/
instance instHPowListNat : HPow (List Γ) ℕ (List Γ) :=
  ⟨fun l n => (List.replicate n l).flatten⟩

/-- A configuration is halting for `M` if no next transition is defined. -/
def IsHaltingConfiguration (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  (step M cfg).isNone

/-- `M` eventually reaches a halting configuration when started on the blank tape (`init []`). -/
def IsHalt (M : Machine Γ Λ) : Prop :=
  ∃ cfg : Cfg Γ Λ, ReachesStar M (init []) cfg ∧ (step M cfg).isNone

/-- `M` never halts when started on the blank tape (`init []`). -/
def IsNotHalt (M : Machine Γ Λ) : Prop :=
  ∀ cfg : Cfg Γ Λ, ReachesStar M (init []) cfg → (step M cfg).isSome

/-- Alias for `IsNotHalt`. -/
abbrev IsDoesNotHalt (M : Machine Γ Λ) : Prop := IsNotHalt M

/-- Parametric regular-expression half-tape expressions for `HasCollatzReduction`. -/
inductive TapeExpr (Γ : Type*) where
  | default : TapeExpr Γ
  | sym (a : Γ) (rest : TapeExpr Γ)
  | rep (blk : List Γ) (var_idx : ℕ) (rest : TapeExpr Γ)

/-- Evaluate a `TapeExpr Γ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapeExpr {Γ : Type*} [Inhabited Γ] : TapeExpr Γ → (ℕ → ℕ) → ListBlank Γ
  | .default, _ => default
  | .sym a rest, vars => ListBlank.cons a (evalTapeExpr rest vars)
  | .rep blk v rest, vars => ListBlank.append (blk ^ vars v) (evalTapeExpr rest vars)

/-- Parametric full-tape configuration pattern. -/
structure TapePattern (Γ Λ : Type*) where
  left : TapeExpr Γ
  head : Option Λ
  right : TapeExpr Γ

/-- Evaluate a `TapePattern Γ Λ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapePattern {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (p : TapePattern Γ Λ) (vars : ℕ → ℕ) : Cfg Γ Λ :=
  let r := evalTapeExpr p.right vars
  ⟨p.head, ⟨r.head, evalTapeExpr p.left vars, r.tail⟩⟩

/-- Guard condition over `ℕ`-valued pattern variables. -/
inductive VarCond where
  | ge_const (idx : ℕ) (val : ℕ)
  | ge_var (idx1 idx2 : ℕ)
  | and (c1 c2 : VarCond)
  | or (c1 c2 : VarCond)
  | not (c : VarCond)
  | true

/-- Evaluate a `VarCond` under variable assignment `vars : ℕ → ℕ`. -/
def evalVarCond : VarCond → (ℕ → ℕ) → Prop
  | .ge_const idx val, vars => vars idx ≥ val
  | .ge_var idx1 idx2, vars => vars idx1 ≥ vars idx2
  | .and c1 c2, vars => evalVarCond c1 vars ∧ evalVarCond c2 vars
  | .or c1 c2, vars => evalVarCond c1 vars ∨ evalVarCond c2 vars
  | .not c, vars => ¬ evalVarCond c vars
  | .true, _ => True

/-- Finite list of guarded tape patterns. -/
abbrev TapePatternSet (Γ Λ : Type*) := List (TapePattern Γ Λ × VarCond)

/-- Membership of configuration `cfg` in a `TapePatternSet`. -/
def IsInPatternSet {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (ps : TapePatternSet Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  ∃ entry : TapePattern Γ Λ × VarCond, entry ∈ ps ∧
    ∃ vars : ℕ → ℕ, cfg = evalTapePattern entry.1 vars ∧ evalVarCond entry.2 vars

/-- `ps` is a closed accelerated `TapePatternSet` for `M` if `M`'s blank-tape trajectory enters
`ps` and every member configuration of `ps` steps in `ReachesPlus` (`n > 0` steps) either to
another member of `ps` or to a halting configuration. -/
def IsClosedPatternSet (M : Machine Γ Λ) (ps : TapePatternSet Γ Λ) : Prop :=
  (∃ cfg₀, ReachesStar M (init []) cfg₀ ∧ IsInPatternSet ps cfg₀) ∧
  (∀ cfg, IsInPatternSet ps cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step M cfg').isNone))

/-- `M`'s blank-tape trajectory enters a closed accelerated `TapePatternSet` in which every
member configuration steps in `ReachesPlus` either to another member or to a halting state. -/
def HasCollatzReduction (M : Machine Γ Λ) : Prop :=
  ∃ ps : TapePatternSet Γ Λ, IsClosedPatternSet M ps

/-- An abstract partial transition system `next : S → Option S` halts from `s₀ : S` if iterating
`next` from `some s₀` eventually produces `none`. -/
def CollatzHalts {S : Type*} (next : S → Option S) (s₀ : S) : Prop :=
  ∃ n : ℕ, ((Option.bind · next)^[n] (some s₀)).isNone

/-- `encode`, `next`, and `start` form a valid Collatz-like acceleration of `M` when:
1. `M` reaches `encode start` from the blank tape (`init []`),
2. Every defined step `next s = some s'` takes `M` from `encode s` to `encode s'` in `ReachesPlus`
   (at least one raw Turing machine step), and
3. Every undefined step `next s = none` means `M` reaches a halting configuration from
   `encode s`. -/
structure IsValidAcceleration (M : Machine Γ Λ) {S : Type*}
    (start : S) (encode : S → Cfg Γ Λ) (next : S → Option S) : Prop where
  /-- `M` reaches `encode start` from the blank tape (`init []`). -/
  init_reaches : ReachesStar M (init []) (encode start)
  /-- Every non-halting accelerated step takes at least one Turing machine step. -/
  step_some : ∀ s s', next s = some s' → ReachesPlus M (encode s) (encode s')
  /-- Every halting accelerated state reaches a halting Turing machine configuration. -/
  step_none : ∀ s, next s = none →
    ∃ cfg', ReachesStar M (encode s) cfg' ∧ (step M cfg').isNone

namespace SixState

/-- State `A` (`0 : Fin 6`), the initial state. -/
abbrev A : Fin 6 := 0
/-- State `B` (`1 : Fin 6`). -/
abbrev B : Fin 6 := 1
/-- State `C` (`2 : Fin 6`). -/
abbrev C : Fin 6 := 2
/-- State `D` (`3 : Fin 6`). -/
abbrev D : Fin 6 := 3
/-- State `E` (`4 : Fin 6`). -/
abbrev E : Fin 6 := 4
/-- State `F` (`5 : Fin 6`). -/
abbrev F : Fin 6 := 5

end SixState

/-- Canonical `NeZero 2` instance for `(states, 2)` Turing machines. -/
instance (priority := high) instNeZeroTwo : @NeZero ℕ Zero.ofOfNat0 2 := Nat.instNeZeroSucc

/-- Canonical `NeZero 6` instance for `(6, symbols)` Turing machines. -/
instance (priority := high) instNeZeroSix : @NeZero ℕ Zero.ofOfNat0 6 := Nat.instNeZeroSucc

end BusyBeaver

namespace ConjectureMachines
variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- Convert a `ConjectureMachines.Machine states symbols` into a
`BusyBeaver.Machine (Fin symbols) (Fin states)`. -/
def Machine.toBB (M : Machine states symbols) :
    BusyBeaver.Machine (Fin symbols) (Fin states) :=
  fun q s => (M.transition q s).map fun (a, d, q') => (some q', BusyBeaver.Stmt.write a d)

end ConjectureMachines

namespace BusyBeaver
open Turing SixState

namespace M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def cfg_S0z (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))) (ListBlank.append [1, 0, 1] ((ListBlank.append
      (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))))))

def cfg_S0p (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append [1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))))
      (ListBlank.append [0, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [1] default)))))))

def cfg_T1 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1] default))))))))) (ListBlank.append [1] default)))

def cfg_T0 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 1] default))))))))) (ListBlank.append [1] default)))

def cfg_T11 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1] default))))))))) (ListBlank.append [1] default)))

def cfg_T3 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 0, 0, 1] default))))))))) (ListBlank.append [1] default)))

def cfg_T10 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1, 1] default))))))))) (ListBlank.append [1] default)))

def cfg_Tn (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] default))))) (ListBlank.append [1] default)))

def cfg_Ea (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(n)) ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [1]
      default)))

def cfg_Eb (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1, 1, 0, 1] default))))))) (ListBlank.append [1] default)))

def cfg_Ec (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(n)) ((ListBlank.append [1] default))))) (ListBlank.append [1] default)))

def cfg_Ed (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1] default))))))) (ListBlank.append [1] default)))

def pat_B : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0] 2 (.rep [1, 0] 0 (.rep [1, 0] 3 (.rep [0, 1] 0
      (.rep [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
          1
        (.rep [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] 4
          (.rep [0] 5 (.rep [1, 1, 0] 6 (.rep [1] 1 .default))))))))
    head := some B
    right := .rep [0, 0, 1] 0 (.sym 1 .default) }

def cond_B : VarCond :=
  .or (.and (.ge_const 0 1) (.and (.not (.ge_const 0 2)) (.and (.not (.ge_const 1 1))
        (.and (.not (.ge_const 4 1)) (.and (.not (.ge_const 5 1)) (.not (.ge_const 6 1)))))))
      (.and (.not (.ge_const 0 1)) (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2))
        (.and (.not (.ge_const 2 1)) (.and (.not (.ge_const 3 1)) (.not (.ge_const 6 2)))))))

def pat_F : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1
      (.rep [0] 2 (.rep [1] 0 .default)))))))
    head := some F
    right := .sym 1 .default }

def cond_F : VarCond :=
  .or (.and (.ge_const 0 1) (.and (.not (.ge_const 0 2)) (.not (.ge_const 1 1))))
      (.and (.not (.ge_const 0 1)) (.not (.ge_const 2 1)))

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_B, cond_B), (pat_F, cond_F)]

inductive State where
  | S0z (a c : ℕ)
  | S0p (a b c : ℕ)
  | T1 (j m : ℕ)
  | T0 (j m : ℕ)
  | T11 (j m : ℕ)
  | T3 (j m : ℕ)
  | T10 (j m : ℕ)
  | Tn (j : ℕ)
  | Ea (n : ℕ)
  | Eb (k t : ℕ)
  | Ec (n : ℕ)
  | Ed (k t : ℕ)
  deriving DecidableEq, Repr

def start : State := .T1 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .S0z a c => cfg_S0z a c
  | .S0p a b c => cfg_S0p a b c
  | .T1 j m => cfg_T1 j m
  | .T0 j m => cfg_T0 j m
  | .T11 j m => cfg_T11 j m
  | .T3 j m => cfg_T3 j m
  | .T10 j m => cfg_T10 j m
  | .Tn j => cfg_Tn j
  | .Ea n => cfg_Ea n
  | .Eb k t => cfg_Eb k t
  | .Ec n => cfg_Ec n
  | .Ed k t => cfg_Ed k t

def next : State → Option State
  | .S0z a 0 => some (.T1 0 (2 * a + 3))
  | .S0z a (c + 1) => some (.S0p 0 (2 * a + 4) c)
  | .S0p a 0 c => some (.S0p 0 (2 * a + 1) (c + 4))
  | .S0p a 1 c => some (.S0p (a + 2) 0 (c + 2))
  | .S0p a 2 c => some (.S0z (a + 2) c)
  | .S0p a (b + 3) c => some (.S0p (a + 2) b c)
  | .T1 _ 0 => some (.Tn 0)
  | .T1 j 1 => some (.T11 0 (2 * j + 7))
  | .T1 j 2 => some (.S0p 0 (2 * j + 5) 3)
  | .T1 j (m + 3) => some (.T1 (j + 2) m)
  | .T0 j 0 => some (.S0z (j + 1) 0)
  | .T0 _ 1 => none
  | .T0 j 2 => some (.S0z (j + 2) 0)
  | .T0 j (m + 3) => some (.T0 (j + 2) m)
  | .T11 j 0 => some (.T1 0 (2 * j + 6))
  | .T11 j 1 => some (.T3 0 (2 * j + 7))
  | .T11 j 2 => some (.Ea j)
  | .T11 j (m + 3) => some (.T11 (j + 2) m)
  | .T3 j 0 => some (.T1 0 (2 * j + 8))
  | .T3 j 1 => some (.T10 0 (2 * j + 7))
  | .T3 j 2 => some (.Ec j)
  | .T3 j (m + 3) => some (.T3 (j + 2) m)
  | .T10 j 0 => some (.T0 0 (2 * j + 6))
  | .T10 _ 1 => none
  | .T10 _ 2 => none
  | .T10 j (m + 3) => some (.T10 (j + 2) m)
  | .Tn j => some (.Tn (j + 2))
  | .Ea n => some (.Eb 0 (2 * n + 1))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ec n => some (.Ed 0 (2 * n + 1))
  | .Ed k t => some (.Ed (k + 1) t)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB

namespace M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_H : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some A
    right := .rep [1] 1 (.rep [0, 1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_H, .true)]

inductive State where
  /-- $H(a, b, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^b\,(01)^c\,0^\infty$. -/
  | H (a b c : ℕ)

def start : State := .H 0 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .H a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))

def next : State → Option State
  | .H 0 b 0 => if b % 2 = 0 then some (.H 0 0 (b / 2 + 1)) else none
  | .H 0 b 1 => some (.H (b + 2) 0 1)
  | .H 0 b (d + 2) => some (.H (b + 3) 0 (d + 1))
  | .H (a + 1) 0 0 => some (.H (a + 1) 0 1)
  | .H (a + 1) 0 1 => some (.H a 4 0)
  | .H (a + 1) 0 (d + 2) => some (.H a 5 d)
  | .H (a + 1) 1 0 => some (.H a 0 1)
  | .H 1 1 (d + 1) => some (.H 2 0 (d + 2))
  | .H (a + 2) 1 (d + 1) => some (.H a 4 (d + 1))
  | .H (a + 1) 2 c => some (.H a 0 (c + 2))
  | .H 1 (m + 3) c => some (.H (m + 4) 0 (c + 1))
  | .H (a + 2) (m + 3) c => some (.H a (m + 6) c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA

namespace M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .rep [1] 0 .default
      head := some SixState.A
      right := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1] 2 .default))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | E (a k c : ℕ)
  | M_1 (a k d : ℕ)
  | M_0 (n z : ℕ)

def start : State := .E 3 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a k c =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))
  | .M_1 a k d =>
    Cfg.headRight SixState.C
      (ListBlank.append [0] (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
      (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
  | .M_0 n z =>
    Cfg.headRight SixState.C
      (ListBlank.append [0] (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ n) default)))
      (ListBlank.append (([1] : List (Fin 2)) ^ z) default)

def next : State → Option State
  | .E a 0 c => some (.M_0 a c)
  | .E a 1 c =>
    if c % 2 = 0 then some (.E (a + 3) (c / 2) 0)
    else if c = 1 then none
    else some (.M_0 (a + 5) (c - 3))
  | .E a (k + 2) 0 => some (.M_0 (a + 2) (2 * k + 1))
  | .E a (k + 2) (d + 1) => some (.M_1 (a + 3) k d)
  | .M_1 a k d =>
    if d % 2 = 0 then some (.E (a + 3) k (d + 1))
    else if d = 1 then some (.E a 1 (2 * k + 2))
    else some (.E (a + 3) (k + 1) (d - 1))
  | .M_0 n 0 => some (.E 3 0 (n + 2))
  | .M_0 n (d + 1) =>
    if d % 2 = 0 then
      if n % 2 = 0 then some (.E 3 (n / 2) (d + 1))
      else some (.E 4 (n / 2 + 1) (d + 1))
    else if d = 1 then
      if n % 2 = 0 then some (.E 0 1 (n + 2))
      else some (.E 1 1 (n + 3))
    else
      if n % 2 = 0 then some (.E 3 (n / 2 + 1) (d - 1))
      else some (.E 4 (n / 2 + 2) (d - 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

namespace M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
              (.rep [1] 1 (.rep [0, 1] 2
                (.sym 1 (.sym 1 (.sym 1
                  (.rep [0, 1, 1, 1, 1] 3
                    (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

inductive State where
  /-- $C(a, f, g, d) :=
    0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^3\,(01111)^d\,011\,0^\infty$. -/
  | C (a f g d : ℕ)

def start : State := .C 2 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a f g d =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([0, 1, 1, 1, 1] : List (Fin 2)) ^ d)
                (ListBlank.append [0, 1, 1] default))))))

def next : State → Option State
  | .C 0 f 0 d =>
    if f % 2 = 0 then some (.C 2 0 (f / 2 + 2) d)
    else some (.C 5 0 (f / 2 + 1) d)
  | .C 0 f 1 d =>
    if f = 0 then some (.C 2 0 0 (d + 2))
    else if f % 2 = 0 then some (.C 5 0 (f / 2 - 1) (d + 1))
    else some (.C 2 0 (f / 2 + 1) (d + 1))
  | .C 0 f (g + 2) d => some (.C (f + 3) 3 g d)
  | .C 1 f 0 d =>
    if f % 2 = 0 then some (.C 0 0 (f / 2 + 3) d)
    else none
  | .C 1 f 1 d =>
    if f % 2 = 0 then none
    else some (.C 0 0 (f / 2 + 2) (d + 1))
  | .C 1 f (g + 2) d => some (.C (f + 4) 3 g d)
  | .C (a + 2) f g d => some (.C a (f + 3) g d)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE

namespace M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))
    head := some F
    right := .rep [1, 1, 1] 1 (.sym 0 (.rep [1] 2 (.sym 0 (.sym 1 (.sym 1 .default))))) }

def pat_Q : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some F
    right := .rep [1, 1, 1] 0
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default)))))))))))) }

def pat_R : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some F
    right := .rep [1, 1, 1] 0
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))))))))) }

def pat_U : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))
    head := some F
    right := .rep [1, 1, 1] 0
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default)))))))))))) }

def pat_T : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 0, 0] 0
      (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0
        (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0
          (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))))))))))))))
    head := some F
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true), (pat_Q, .true), (pat_R, .true), (pat_U, .true), (pat_T, .true)]

inductive State where
  /-- $P(b, k, c) := 0^\infty\,1111\,0^b\,\mathrm{F}{>}\,(111)^k\,0\,1^c\,011\,0^\infty$. -/
  | P (b k c : ℕ)

def start : State := .P 4 0 11

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P b k c =>
    Cfg.headRight SixState.F
      (ListBlank.append (([0] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1] default))
      (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ c)
            (ListBlank.append [0, 1, 1] default))))

def next : State → Option State
  | .P 0 k c => some (.P (3 * k + 3) 0 (c + 2))
  | .P 1 k 0 => if k = 2 then some (.P 7 2 18) else none
  | .P 1 k 1 => if k = 1 then some (.P 7 2 18) else none
  | .P 1 k (c + 2) => some (.P 0 (k + 1) c)
  | .P (b + 2) k 0 => some (.P b 0 (3 * k + 5))
  | .P (b + 2) k 1 => some (.P b 0 (3 * k + 8))
  | .P (b + 2) k (c + 2) => some (.P (b + 1) (k + 1) c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA

namespace M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some A
    right := .sym 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A2, .true)]

inductive State where
  /-- $A_2(a, b, c) := 0^\infty\,(10)^b\,11\,(10)^{a+1}\,\mathrm{A}{>}\,1^{c+1}\,0^\infty$. -/
  | A2 (a b c : ℕ)

def start : State := .A2 0 1 6

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A2 a b c =>
    Cfg.headRight A
      (ListBlank.cons 0 (ListBlank.cons 1
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.cons 1 (ListBlank.cons 1
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))))))
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def next : State → Option State
  | .A2 0 b 0 => some (.A2 0 1 (2 * b + 10))
  | .A2 (a + 1) b 0 => some (.A2 a b 1)
  | .A2 a b 1 => some (.A2 0 1 (4 * a + 2 * b + 14))
  | .A2 _ 0 2 => none
  | .A2 _ 0 3 => none
  | .A2 a 0 4 => some (.A2 0 1 (2 * a + 12))
  | .A2 a 0 5 => some (.A2 0 1 (2 * a + 16))
  | .A2 a 0 (c + 6) => some (.A2 0 (a + 4) c)
  | .A2 a (b + 1) (c + 2) => some (.A2 (a + 2) b c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE

namespace M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) := [
  -- 1. h = 0
  (⟨.rep [1] 1 (.rep [1, 0] 0 .default), some SixState.A, .rep [1] 2 .default⟩,
   .and (.ge_const 1 1) (.not (.ge_const 2 1))),
  -- 2. h >= 3
  (⟨.rep [1] 1 (.rep [1, 0] 0 .default), some SixState.A, .rep [1] 2 .default⟩,
   .and (.ge_const 1 1) (.ge_const 2 3)),
  -- 3. h = 2, g even
  (⟨.rep [1, 1] 1 (.rep [1, 0] 0 .default), some SixState.A, .rep [1] 2 .default⟩,
   .and (.ge_const 1 1) (.and (.ge_const 2 2) (.not (.ge_const 2 3)))),
  -- 4. h = 2, g odd, a = 0
  (⟨.rep [1] 1 .default, some SixState.A, .rep [1] 2 .default⟩,
   .and (.ge_const 1 1) (.and (.ge_const 2 2) (.not (.ge_const 2 3)))),
  -- 5. h = 1, g even
  (⟨.rep [1, 1] 1 (.rep [1, 0] 0 .default), some SixState.A, .rep [1] 2 .default⟩,
   .and (.ge_const 1 1) (.and (.ge_const 2 1) (.not (.ge_const 2 2))))
]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE

namespace M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left :=
      .sym 1 (.sym 1 (.rep [1, 1] 2 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.rep [1] 0 .default))))))
    head := some B
    right := .default }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

inductive State where
  /-- $A(a, b, c) := 0^\infty\,1^a\,0\,(10)^b\,0\,(11)^{c+1}\,\mathrm{B}{>}\,0^\infty$. -/
  | A (a b c : ℕ)

def start : State := .A 3 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c =>
    Cfg.headRight SixState.B
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
        (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
            (ListBlank.cons 0
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
      default

def next : State → Option State
  | .A 0 0 _ => none
  | .A (a + 1) 0 c => some (.A a c 2)
  | .A 0 1 c => some (.A (2 * c + 9) 0 0)
  | .A (a + 1) 1 c => some (.A a c 6)
  | .A a (b + 2) c => some (.A a b (c + 3))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE

namespace M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def cfg_S0z (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append ([1] : List (Fin 2)) default)))
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ c)
        (ListBlank.append ([0, 1] : List (Fin 2)) default)))

def cfg_S0p (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append ([1] : List (Fin 2)) default)))
    (ListBlank.append
      ([0] : List (Fin 2))
      (ListBlank.append
        (([0] : List (Fin 2)) ^ b)
        (ListBlank.append
          ([1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1] : List (Fin 2)) default)))))

def cfg_T1 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1] : List (Fin 2)) default)))))

def cfg_T0 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 1] : List (Fin 2)) default)))))

def cfg_T11 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))))

def cfg_T3 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))))

def cfg_T10 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))))

def cfg_Tn (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)))

def cfg_Ea (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))

def cfg_Eb (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
        1] : List (Fin 2))
      (ListBlank.append
        (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append
          (([0] : List (Fin 2)) ^ t)
          (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))

def cfg_Ec (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append ([1] : List (Fin 2)) default)))

def cfg_Ed (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
        1] : List (Fin 2))
      (ListBlank.append
        (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append
          (([0] : List (Fin 2)) ^ t)
          (ListBlank.append ([1] : List (Fin 2)) default))))

def cfg_T1s (b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ 2)
        (ListBlank.append ([1] : List (Fin 2)) default)))
    (ListBlank.append
      ([0] : List (Fin 2))
      (ListBlank.append
        (([0] : List (Fin 2)) ^ b)
        (ListBlank.append ([1, 0] : List (Fin 2)) default)))

def cfg_Tns (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ (j + 2))
        (ListBlank.append ([1] : List (Fin 2)) default)))
    default

def pat_S0p_T1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some SixState.A
    right := .sym 0 (.rep [0] 1 (.rep [1, 0] 2 (.rep [0, 1] 3 .default))) }

def cond_S0p_T1 : VarCond :=
  .or (.and (.ge_const 3 1) (.and (.not (.ge_const 3 2)) (.ge_const 2 1)))
    (.or
      (.and (.not (.ge_const 3 1))
        (.and (.ge_const 2 1)
          (.and (.not (.ge_const 2 2))
            (.and (.ge_const 0 2) (.not (.ge_const 0 3))))))
      (.and (.not (.ge_const 3 1))
        (.and (.not (.ge_const 2 1))
          (.and (.not (.ge_const 1 1)) (.ge_const 0 2)))))

def pat_Ebd : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some SixState.A
    right :=
      .sym 1
        (.rep
          [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
          3
          (.rep [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] 0
            (.rep [0] 1 (.sym 1 (.rep [1, 0, 1] 2 .default))))) }

def cond_Ebd : VarCond :=
  .and (.not (.ge_const 2 2)) (.and (.ge_const 3 1) (.not (.ge_const 3 2)))

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_S0p_T1, cond_S0p_T1), (pat_Ebd, cond_Ebd)]

inductive State where
  | S0p (a b c : ℕ)
  | S0z (a c : ℕ)
  | T1 (j m : ℕ)
  | T0 (j m : ℕ)
  | T11 (j m : ℕ)
  | T3 (j m : ℕ)
  | T10 (j m : ℕ)
  | Tn (j : ℕ)
  | Ea (n : ℕ)
  | Eb (k t : ℕ)
  | Ec (n : ℕ)
  | Ed (k t : ℕ)

def start : State := .S0p 0 1 3

def encode : State → Cfg (Fin 2) (Fin 6)
  | .S0p a b c => cfg_S0p a b c
  | .S0z a c => cfg_S0z a c
  | .T1 j m => cfg_T1 j m
  | .T0 j m => cfg_T0 j m
  | .T11 j m => cfg_T11 j m
  | .T3 j m => cfg_T3 j m
  | .T10 j m => cfg_T10 j m
  | .Tn j => cfg_Tn j
  | .Ea n => cfg_Ea n
  | .Eb k t => cfg_Eb k t
  | .Ec n => cfg_Ec n
  | .Ed k t => cfg_Ed k t

def next : State → Option State
  | .S0p a 0 c => some (.S0p 0 (2 * a + 1) (c + 4))
  | .S0p a 1 c => some (.S0p (a + 2) 0 (c + 2))
  | .S0p a 2 c => some (.S0z (a + 2) c)
  | .S0p a (b + 3) c => some (.S0p (a + 2) b c)
  | .S0z a 0 => some (.T1 0 (2 * a + 3))
  | .S0z a (c + 1) => some (.S0p 0 (2 * a + 4) c)
  | .T1 _ 0 => some (.Tn 0)
  | .T1 j 1 => some (.T11 0 (2 * j + 7))
  | .T1 j 2 => some (.S0p 0 (2 * j + 5) 3)
  | .T1 j (m + 3) => some (.T1 (j + 2) m)
  | .T0 j 0 => some (.S0z (j + 1) 0)
  | .T0 _ 1 => none
  | .T0 j 2 => some (.S0z (j + 2) 0)
  | .T0 j (m + 3) => some (.T0 (j + 2) m)
  | .T11 j 0 => some (.T1 0 (2 * j + 6))
  | .T11 j 1 => some (.T3 0 (2 * j + 7))
  | .T11 j 2 => some (.Ea j)
  | .T11 j (m + 3) => some (.T11 (j + 2) m)
  | .T3 j 0 => some (.T1 0 (2 * j + 8))
  | .T3 j 1 => some (.T10 0 (2 * j + 7))
  | .T3 j 2 => some (.Ec j)
  | .T3 j (m + 3) => some (.T3 (j + 2) m)
  | .T10 j 0 => some (.T0 0 (2 * j + 6))
  | .T10 _ 1 => none
  | .T10 _ 2 => none
  | .T10 j (m + 3) => some (.T10 (j + 2) m)
  | .Tn j => some (.Tn (j + 2))
  | .Ea n => some (.Eb 0 (2 * n + 1))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ec n => some (.Ed 0 (2 * n + 1))
  | .Ed k t => some (.Ed (k + 1) t)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH

namespace M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left  := .default
    head  := some D
    right := .rep [1, 0] 0 (.rep [1, 1, 0] 1 (.rep [0] 2 (.rep [1] 3 .default))) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .not (.ge_const 2 2))]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

namespace M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left  := .default
    head  := some D
    right := .rep [1, 0] 0 (.rep [1, 1, 0] 1 (.rep [0] 2 (.rep [1] 3 .default))) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .not (.ge_const 2 2))]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

namespace M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.rep [1] 0 .default)
    head := some C
    right := .rep [1] 2 .default }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

inductive State where
  /-- $C(m, k, b) := 0^\infty\,1^m\,(10)^k\,\mathrm{C}{>}\,1^b\,0^\infty$. -/
  | C (m k b : ℕ)

def start : State := .C 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C m k b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ m) default))
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default)

def next : State → Option State
  | .C m k 0 => some (.C (m + 1) 0 (2 * k + 2))
  | .C 0 k 1 => some (.C (2 * k + 3) 0 2)
  | .C 0 k (b + 2) => some (.C (2 * k + 2) 1 b)
  | .C 1 0 (b + 1) => some (.C 0 0 (b + 3))
  | .C 1 (k + 1) 1 => some (.C (2 * k + 7) 0 2)
  | .C 1 (k + 1) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C 2 0 1 => some (.C 0 1 0)
  | .C 2 0 (_ + 2) => none
  | .C 2 1 (b + 1) => some (.C 0 1 (b + 1))
  | .C 2 (k + 2) 1 => some (.C (2 * k + 7) 0 2)
  | .C 2 (k + 2) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C (m + 3) k (b + 1) => some (.C m (k + 2) b)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH

namespace M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 0] 1 (.rep [1] 0 .default)
    head  := some F
    right := .sym 0 (.sym 0 (.rep [1] 2 .default)) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

namespace M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .rep [1, 0] 0 (.rep [1] 1 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .ge_const 1 1)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C (a b : ℕ)
  | P (k n p : ℕ)

def start : State := .C 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b =>
    Cfg.headRight SixState.E default
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))
  | .P k n p =>
    Cfg.headLeft SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append (([1] : List (Fin 2)) ^ (p + 1)) default))

def next : State → Option State
  | .C a 0 => some (.C 2 (2 * a + 1))
  | .C _ 1 => none
  | .C a (d + 2) => some (.P a 0 (d + 2))
  | .P 0 n 0 => some (.C (n + 1) 2)
  | .P 0 n 1 => some (.C (n + 1) 0)
  | .P 0 n (p + 2) => some (.C (n + 2) p)
  | .P (k + 1) n 0 => some (.P k (n + 1) 2)
  | .P (k + 1) n 1 => some (.P k (n + 1) 0)
  | .P (k + 1) n (p + 2) => some (.P k (n + 2) p)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

namespace M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))))
      head := some SixState.A
      right := .sym 1 (.sym 1 (.rep [0, 1] 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }, .true),
   ({ left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
      head := some SixState.E
      right := .sym 1 (.rep [1, 1, 0, 1] 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
          (.rep [1, 1] 2 (.sym 0 (.sym 1 .default)))))))))) }, .true),
   ({ left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
      head := some SixState.E
      right := .sym 1 (.rep [1, 1, 0, 1] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }, .true),
   ({ left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
      head := some SixState.E
      right := .sym 1 (.rep [1, 1, 0, 1] 1
        (.sym 1 (.sym 1 (.sym 1 (.rep [0, 1] 2
          (.sym 0 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))))))))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | J (u v w : ℕ)
  | S_E (b m k : ℕ)
  | S_E0 (b m : ℕ)
  | S_E1 (b m n : ℕ)

def start : State := .J 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .J u v w =>
    Cfg.headRight SixState.A
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
          (ListBlank.append [1, 1, 1, 1, 1] default)))
      (ListBlank.append [1, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ v)
          (ListBlank.append (([1] : List (Fin 2)) ^ w)
            (ListBlank.append [0, 1] default))))
  | .S_E b m k =>
    Cfg.headRight SixState.E
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append [1]
        (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] default)))))
  | .S_E0 b m =>
    Cfg.headRight SixState.E
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append [1]
        (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 0, 1] default)))
  | .S_E1 b m n =>
    Cfg.headRight SixState.E
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append [1]
        (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
              (ListBlank.append [0, 1, 0, 0, 1] default)))))

def next : State → Option State
  | .J 0 v 0 => some (.S_E0 (v + 3) 0)
  | .J 0 v 1 => some (.S_E1 (v + 2) 0 0)
  | .J 0 v 2 => some (.S_E (v + 2) 0 0)
  | .J 0 v (w + 3) => some (.J (v + 3) 0 w)
  | .J 1 v 0 => some (.S_E 0 0 (v + 3))
  | .J (u + 2) v 0 => some (.S_E1 u 0 (v + 2))
  | .J 1 _ 1 => none
  | .J (u + 2) v 1 => some (.S_E u 0 (v + 2))
  | .J (u + 1) v (w + 2) => some (.J u (v + 2) w)
  | .S_E 0 0 k => some (.J 0 0 (2 * k + 6))
  | .S_E 0 (m + 1) k => some (.J 2 (2 * m + 4) (2 * k + 1))
  | .S_E 1 m k => some (.J 0 (2 * m + 3) (2 * k + 1))
  | .S_E (b + 2) m k => some (.S_E b (m + 1) k)
  | .S_E0 0 m => some (.S_E 2 0 (2 * m))
  | .S_E0 1 m => some (.S_E 0 0 (2 * m + 1))
  | .S_E0 (b + 2) m => some (.S_E0 b (m + 1))
  | .S_E1 0 m n => some (.S_E 2 0 (2 * m + n + 2))
  | .S_E1 1 m n => some (.S_E 0 0 (2 * m + n + 3))
  | .S_E1 (b + 2) m n => some (.S_E1 b (m + 1) n)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

namespace M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .rep [1] 1 (.sym 0 (.rep [1] 2 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .true)]

inductive State where
  /-- $D(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,1^b\,0\,1^c\,0^\infty$. -/
  | D (a b c : ℕ)

def start : State := .D 0 3 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b c =>
    Cfg.headRight SixState.D
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

def next : State → Option State
  | .D _ 0 0 => none
  | .D a 0 1 => some (.D 0 (a + 3) 1)
  | .D a 0 2 => some (.D 0 (a + 2) 2)
  | .D a 0 (c + 3) => some (.D (a + 3) 0 c)
  | .D a 1 0 => some (.D (a + 1) 0 1)
  | .D a 1 (c + 1) => some (.D (a + 1) 1 c)
  | .D a 2 c => some (.D 0 a (c + 3))
  | .D a (b + 3) 0 =>
    if b % 3 = 0 then none
    else if b % 3 = 1 then some (.D (a + 1) (b + 2) 1)
    else some (.D (a + 1) b 2)
  | .D a (b + 3) (c + 1) =>
    if b % 3 = 0 then some (.D (a + 1) (b + 1) (c + 2))
    else if b % 3 = 1 then some (.D (a + 1) (b + 3) c)
    else some (.D (a + 1) b (c + 3))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB

namespace M_1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_HHH1LC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some D
    right := .sym 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 .default))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

inductive State where
  /-- $P(a, b, c) := 0^\infty\,1^a\,\mathrm{D}{>}\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | P (a b c : ℕ)

def start : State := .P 0 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P a b c =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ b)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))

def next : State → Option State
  | .P a 0 c =>
    if c % 2 = 0 then some (.P 0 (a + c + 1) 1)
    else some (.P 0 (a + c + 1) 2)
  | .P 0 1 _ => none
  | .P (a + 1) 1 c => some (.P 0 a (c + 3))
  | .P a (b + 2) 0 =>
    if b % 2 = 0 then some (.P (a + 1) b 2)
    else some (.P (a + 1) b 1)
  | .P a (b + 2) (c + 1) =>
    if b % 2 = 0 then some (.P (a + 1) (b + 2) c)
    else some (.P (a + 1) b (c + 2))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_HHH1LC

namespace M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 (.rep [0, 1, 1, 1] 1 .default)
    head  := some D
    right := .sym 1 (.sym 1 (.rep [0, 1] 2 (.rep [1] 3 .default))) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .not (.ge_const 1 2))]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

namespace M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left :=
      .rep [0, 1] 0
        (.sym 0 (.sym 1 (.rep [1] 1 (.rep [0, 1, 1, 1] 2 (.rep [0, 1] 3 .default)))))
    head := some C
    right := .default }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

inductive State where
  /-- $C(c, b, a, d) := 0^\infty\,(10)^d\,(1110)^a\,1^b\,10\,(10)^c\,\mathrm{C}{>}\,0^\infty$. -/
  | C (c b a d : ℕ)

def start : State := .C 0 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C c b a d =>
    Cfg.headRight SixState.C
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)))))
      default

def next : State → Option State
  | .C c 0 0 d =>
    if (c + d) % 2 = 0 then
      some (.C 0 0 ((c + d) / 2 + 1) 1)
    else
      none
  | .C c 0 1 0 => some (.C 0 (2 * (c + 1) + 5) 0 0)
  | .C c 0 1 (d + 1) => some (.C 0 (2 * (c + 1) + 6) 0 d)
  | .C c 0 (a + 2) d => some (.C 0 (2 * (c + 1) + 8) a d)
  | .C c 1 0 0 => some (.C 0 (2 * c + 5) 0 0)
  | .C c 1 0 (d + 1) => some (.C (c + 3) 0 0 (d + 1))
  | .C c 1 (a + 1) d => some (.C (c + 3) 0 (a + 1) d)
  | .C c 2 0 0 => some (.C 0 (2 * c + 5) 0 0)
  | .C c 2 0 (d + 1) => some (.C 0 (2 * c + 6) 0 d)
  | .C c 2 (a + 1) d => some (.C 0 (2 * c + 8) a d)
  | .C c (b + 3) a d => some (.C (c + 4) b a d)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA

namespace M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 0 (.rep [1] 2 .default)
    head  := some A
    right := .sym 0 (.rep [1, 0] 1 (.rep [1] 0 .default)) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

namespace M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0, 1, 0, 1, 0] 0 .default))))
    head := some A
    right := .rep [0, 1] 1 .default }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

inductive State where
  /-- $A(n, m) := 0^\infty\,(01)^{3n+2}\,\mathrm{A}{>}\,(01)^m\,0^\infty$. -/
  | A (n m : ℕ)

def start : State := .A 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A n m =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * n + 2)) default)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default)

def next : State → Option State
  | .A n 0 => some (.A 0 (3 * n + 2))
  | .A n 1 =>
    if n % 2 = 0 then none
    else some (.A (3 * (n / 2) + 2) 0)
  | .A n (m + 2) =>
    if n % 2 = 0 then some (.A (3 * (n / 2) + 1) m)
    else some (.A (3 * (n / 2) + 2) (m + 1))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB

namespace M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some E
    right := .sym 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 .default))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

inductive State where
  /-- $P(a, b, c) := 0^\infty\,1^a\,\mathrm{E}{>}\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | P (a b c : ℕ)

def start : State := .P 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ b)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))

def next : State → Option State
  | .P a 0 c =>
    if c % 2 = 0 then some (.P 0 (a + c + 1) 2)
    else some (.P 0 (a + c + 1) 1)
  | .P 0 1 _ => none
  | .P (a + 1) 1 c => some (.P 0 a (c + 3))
  | .P a (b + 2) c =>
    if b % 2 = 0 then some (.P 0 (a + c + 3 * (b / 2) + 4) 2)
    else some (.P (a + 1) b (c + 1))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB

namespace M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

inductive State where
  /-- $P(m, k) := 0^\infty\,1^m\,\mathrm{E}{>}\,1\,1^k\,0^\infty$. -/
  | P (m k : ℕ)

def start : State := .P 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P m k =>
    Cfg.headRight SixState.E
      (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))

def next : State → Option State
  | .P 0 0 => some (.P 0 2)
  | .P 0 (k + 1) => some (.P 2 k)
  | .P 1 _ => none
  | .P (m + 2) k =>
    if m % 2 = 0 then
      some (.P (3 * (m / 2) + k + 3) 1)
    else
      some (.P (m / 2) (m / 2 + k + 4))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE

namespace M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 (.sym 0 (.rep [1] 1 .default)))
    head := some C
    right := .rep [1] 2 (.sym 0 (.rep [1] 3 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

inductive State where
  /-- $C(d, k, a, b) := 0^\infty\,1^k\,0\,1^{d+1}\,\mathrm{C}{>}\,1^a\,0\,1^b\,0^\infty$. -/
  | C (d k a b : ℕ)

def start : State := .C 1 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C d k a b =>
    Cfg.headRight SixState.C
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ d)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ k) default))))
      (ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))

def next : State → Option State
  | .C 0 0 0 _ => none
  | .C 0 (k + 1) 0 b => some (.C k 0 0 (b + 2))
  | .C 1 0 0 b => some (.C 1 0 (b + 1) 0)
  | .C 1 (k + 1) 0 b => some (.C k 0 2 (b + 1))
  | .C (d + 2) k 0 b => some (.C d (k + 1) 0 (b + 1))
  | .C 0 0 (a + 1) b => some (.C (a + 2) 0 b 0)
  | .C 0 (k + 1) (a + 1) b => some (.C k 0 (a + 3) b)
  | .C (d + 1) k (a + 1) b => some (.C d (k + 1) (a + 1) b)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

namespace M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left  := .sym 1 (.rep [1] 0 .default)
      head  := some SixState.C
      right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                (.rep [1] 1 (.rep [0, 1] 2
                  (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default))))))))))))) }, .true),
   ({ left  := .sym 1 (.rep [1] 0 .default)
      head  := some SixState.C
      right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                (.rep [1] 1 (.rep [0, 1] 2
                  (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                    (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C_3 (a b c : ℕ)
  | C_6 (a b c : ℕ)
  | M_3 (a : Bool) (b c : ℕ)
  | M_6_pos (a : Bool) (b c : ℕ)
  | L_3 (a : Bool) (b : ℕ)
  | L_6 (a : Bool) (b : ℕ)

def start : State := .C_3 4 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C_3 a b c =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))))
  | .C_6 a b c =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default)))))
  | .M_3 a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [1] (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))))
  | .M_6_pos a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [1] (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default)))))
  | .L_3 a b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ ((b + 1) + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append [0, 1, 1] default)))
  | .L_6 a b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (b + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ 6)
          (ListBlank.append [0, 1, 1] default)))

def next : State → Option State
  | .C_3 0 b c => some (.M_3 false b c)
  | .C_3 1 b c => some (.M_3 true b c)
  | .C_3 (a + 2) b c => some (.C_3 a (b + 3) c)
  | .C_6 0 b 0 => some (.M_3 false (b + 3) 0)
  | .C_6 1 b 0 => some (.M_3 true (b + 3) 0)
  | .C_6 0 b (c + 1) => some (.M_6_pos false b c)
  | .C_6 1 b (c + 1) => some (.M_6_pos true b c)
  | .C_6 (a + 2) b c => some (.C_6 a (b + 3) c)
  | .M_3 a b 0 => some (.L_3 a b)
  | .M_3 a b 1 => some (.L_6 a b)
  | .M_3 a b (c + 2) => some (.C_3 (b + 4 + if a then 1 else 0) 3 c)
  | .M_6_pos a b 0 => some (.C_3 (b + 4 + if a then 1 else 0) 0 3)
  | .M_6_pos a b (c + 1) => some (.C_6 (b + 4 + if a then 1 else 0) 3 c)
  | .L_3 a b =>
    if b % 2 = 0 then some (.C_3 (if a then 1 else 0) 0 (b / 2 + 3))
    else if a then some (.C_3 6 3 (b / 2))
    else none
  | .L_6 a b =>
    if b % 2 = 1 then some (.C_6 (if a then 1 else 0) 0 (b / 2 + 3))
    else if !a then none
    else if b = 0 then some (.C_3 6 0 3)
    else some (.C_6 6 3 (b / 2 - 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA

namespace M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_61 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

def pat_270 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_61, .true), (pat_270, .true)]

inductive State where
  /-- $P_{61}(a, c) := 0^\infty\,1^{a+1}\,\mathrm{B}{>}\,1^{c+3}\,01\,0^\infty$. -/
  | P61 (a c : ℕ)
  /-- $P_{270}(a, b,
    c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,110\,(10)^b\,1^{c+3}\,01\,0^\infty$. -/
  | P270 (a b c : ℕ)

def start : State := .P61 0 7

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P61 a c =>
    Cfg.headRight B
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
        (ListBlank.append (([1] : List (Fin 2)) ^ c)
          (ListBlank.cons 0 (ListBlank.cons 1 default))))))
  | .P270 a b c =>
    Cfg.headRight D
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
            (ListBlank.append (([1] : List (Fin 2)) ^ c)
              (ListBlank.cons 0 (ListBlank.cons 1 default))))))))))

def next : State → Option State
  | .P61 a 0 => some (.P61 0 (4 * a + 4 * (a / 2) + 15))
  | .P61 a 1 => some (.P61 0 (2 * a + 11))
  | .P61 _ 2 => none
  | .P61 a (c + 3) => some (.P270 a 0 c)
  | .P270 0 _ 0 => none
  | .P270 1 _ 0 => none
  | .P270 (a + 2) b 0 => some (.P61 0 (4 * a + 4 * (a / 2) + 4 * b + 35))
  | .P270 0 _ 1 => none
  | .P270 1 _ 1 => none
  | .P270 (a + 2) b 1 => some (.P61 0 (4 * a + 4 * (a / 2) + 4 * b + 27))
  | .P270 a b 2 => some (.P61 0 (2 * a + 2 * b + 13))
  | .P270 0 b (c + 3) => some (.P61 (2 * b + 8) c)
  | .P270 1 b (c + 3) => some (.P61 (2 * b + 10) c)
  | .P270 (_ + 2) _ 3 => none
  | .P270 (a + 2) b (c + 4) => some (.P270 a (b + 3) c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH

namespace M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_B : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.rep [1] 0 .default)
    head := some B
    right := .rep [1] 2 .default }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_B, .true)]

inductive State where
  /-- $B(a, k, c) := 0^\infty\,1^a\,(10)^k\,\mathrm{B}{>}\,1^c\,0^\infty$. -/
  | B (a k c : ℕ)

def start : State := .B 5 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .B a k c =>
    Cfg.headRight SixState.B
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([1] : List (Fin 2)) ^ c) default)

def next : State → Option State
  | .B a k 1 => some (.B a (k + 1) 0)
  | .B _ _ 2 => none
  | .B a k 3 => some (.B a (k + 2) 1)
  | .B 0 k 0 => some (.B 1 0 (2 * k + 2))
  | .B 1 0 0 => some (.B 5 0 1)
  | .B 1 (k + 1) 0 => some (.B 2 2 (2 * k + 1))
  | .B (a + 2) k 0 => some (.B a 1 (2 * k + 1))
  | .B 0 k (d + 4) =>
    if k % 2 = 0 then some (.B (4 * (k / 2) + 2) 2 (d + 1))
    else some (.B (4 * (k / 2) + 5) 0 (d + 4))
  | .B (a + 1) k (d + 4) => some (.B a (k + 1) (d + 3))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC

namespace M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_B2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some B
    right := .sym 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_B2, .true)]

inductive State where
  /-- $B_2(a, b, c) := 0^\infty\,(10)^b\,11\,(10)^{a+1}\,\mathrm{B}{>}\,1^{c+1}\,0^\infty$. -/
  | B2 (a b c : ℕ)

def start : State := .B2 0 1 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .B2 a b c =>
    Cfg.headRight B
      (ListBlank.cons 0 (ListBlank.cons 1
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.cons 1 (ListBlank.cons 1
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))))))
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def next : State → Option State
  | .B2 0 b 0 => some (.B2 0 1 (2 * b + 10))
  | .B2 (a + 1) b 0 => some (.B2 a b 1)
  | .B2 a b 1 => some (.B2 0 1 (4 * a + 2 * b + 14))
  | .B2 _ 0 2 => none
  | .B2 _ 0 3 => none
  | .B2 a 0 4 => some (.B2 0 1 (2 * a + 12))
  | .B2 a 0 5 => some (.B2 0 1 (2 * a + 16))
  | .B2 a 0 (c + 6) => some (.B2 0 (a + 4) c)
  | .B2 a (b + 1) (c + 2) => some (.B2 (a + 2) b c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE

namespace M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_Master : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [0, 0, 1] 1 (.rep [1] 2 (.rep [0, 0, 1, 1] 0 .default))
    head  := some A
    right := .default }

def cond_Master : VarCond :=
  .or (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2)) (.not (.ge_const 2 1))))
    (.or (.and (.ge_const 1 2) (.and (.not (.ge_const 1 3)) (.not (.ge_const 2 1))))
      (.or (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2)) (.and (.ge_const 2 3) (.not
        (.ge_const 2 4)))))
        (.or (.and (.ge_const 1 3) (.and (.not (.ge_const 1 4)) (.and (.ge_const 2 3) (.not
          (.ge_const 2 4)))))
             (.and (.ge_const 1 3) (.and (.not (.ge_const 1 4)) (.and (.ge_const 2 5) (.not
               (.ge_const 2 6))))))))

def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_Master, cond_Master)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA

namespace M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .rep [0, 1] 1 (.rep [1] 0 .default)
      head := some SixState.A
      right := .rep [0, 1] 2 (.rep [1] 3 .default) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | A (a b c d : ℕ)

def start : State := .A 0 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c d =>
    Cfg.headRight SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default))

def next : State → Option State
  | .A a b (c + 1) d => some (.A a (b + 1) c d)
  | .A a b 0 0 => some (.A (a + 1) 0 0 (2 * b + 2))
  | .A (a + 3) b 0 (d + 1) => some (.A a (b + 2) 0 d)
  | .A 2 b 0 (d + 1) => some (.A 0 0 (b + 1) d)
  | .A 1 (b + 1) 0 (d + 1) => some (.A 1 1 (b + 2) d)
  | .A 1 0 0 (d + 1) => some (.A 0 0 0 (d + 3))
  | .A 0 0 0 1 => some (.A 0 0 2 5)
  | .A 0 (b + 1) 0 1 => some (.A 0 0 2 (2 * b + 3))
  | .A 0 b 0 (d + 2) =>
    if b ≥ d + 1 then some (.A (3 * d + 2) 1 2 (2 * b - 2 * d - 1))
    else if d = b then none
    else if d = b + 1 then some (.A (3 * b + 2) 0 0 6)
    else if d = b + 2 then some (.A (3 * b + 4) 0 0 4)
    else some (.A (3 * b + 3) 2 0 (d - b - 3))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

namespace M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_Q : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .rep [1, 0] 0 (.rep [1, 1, 0] 1 (.sym 1 (.sym 1 .default))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_Q, .true)]

inductive State where
  /-- $Q(a, c) := 0^\infty\,\mathrm{D}{>}\,(10)^a\,(110)^c\,11\,0^\infty$. -/
  | Q (a c : ℕ)

def start : State := .Q 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .Q a c =>
    Cfg.headRight SixState.D default
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append [1, 1] default)))

def next : State → Option State
  | .Q a c =>
    if a % 3 = 1 then
      some (.Q (3 * (a / 3)) (c + 2))
    else if a % 3 = 2 then
      some (.Q (4 * (a / 3) + 4) (c + 1))
    else
      match c with
      | c' + 1 => some (.Q (4 * (a / 3) + 3) c')
      | 0 =>
        if a % 9 = 0 then
          some (.Q (12 * (a / 9) + 3) 0)
        else if a % 9 = 3 then
          some (.Q (12 * (a / 9) + 6) 1)
        else
          none

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC

namespace M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_E : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 0 (.rep [0] 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 (.sym 0 (.rep [1] 3 .default)))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_E, .not (.ge_const 0 2))]

inductive State where
  /-- Canonical hub configuration
  $E(q, a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^q\,1^a\,0\,1^b\,0\,1^c\,0^\infty$
  with $q \in \{0, 1\}$. -/
  | E (q : Bool) (a b c : ℕ)
  /-- Even-block right-sweep configuration
  $F(d, 2k, b, c) := 0^\infty\,1^{d+1}\,\mathrm{F}{>}\,1^{2k}\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | F_even (d k b c : ℕ)

def start : State := .E true 3 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E q a b c =>
    Cfg.headRight SixState.E default
      (ListBlank.append [0]
        (ListBlank.append (([0] : List (Fin 2)) ^ (if q then 1 else 0))
          (ListBlank.append (([1] : List (Fin 2)) ^ a)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ b)
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))))
  | .F_even d k b c =>
    Cfg.headRight SixState.F
      (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))

def mkE (m b c : ℕ) : State :=
  .E (decide (m % 2 = 1)) m b c

def enterF_d0 (a b c : ℕ) : Option State :=
  if a % 2 = 0 then
    some (.F_even 0 (a / 2) b c)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (b + 2) (c + 3) 0)
  else
    none

def enterF_d1 (a b c : ℕ) : Option State :=
  if a % 2 = 0 then
    some (.F_even 1 (a / 2) b c)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (b + 3) (c + 3) 0)
  else
    some (.E true (a - 2) (b + 6) c)

def enterF_c0 (d a b : ℕ) : Option State :=
  if a % 2 = 0 then
    some (.F_even d (a / 2) b 0)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (d + b + 2) 3 0)
  else
    some (mkE (d + 1) (a - 4) (b + 3))

def next : State → Option State
  | .E false a b c => enterF_d0 a b c
  | .E true 0 0 0 => none
  | .E true 0 0 (c + 1) => some (mkE (c + 2) 3 0)
  | .E true 0 (b + 1) c => enterF_c0 2 (b + 1) c
  | .E true (a + 1) b c => enterF_d1 (a + 1) b c
  | .F_even d 0 0 0 => some (mkE (d + 1) 3 0)
  | .F_even d 0 0 (c + 1) => some (.F_even (d + 1) 0 (c + 1) 0)
  | .F_even d 0 (b + 1) c => enterF_c0 (d + 1) (b + 1) c
  | .F_even 0 1 b c => some (mkE (b + 2) (c + 3) 0)
  | .F_even 1 1 b c => some (.E true (b + 4) c 0)
  | .F_even (d + 2) 1 b c => some (mkE (d + 1) (b + 4) c)
  | .F_even d (k + 2) b c => some (.F_even (d + 1) k (b + 3) c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD

namespace M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 .default))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

inductive State where
  /-- $A(a, b) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,0^\infty$. -/
  | A (a b : ℕ)
  /-- $B(a, b, c) := 0^\infty\,{<}\mathrm{C}\,(10)^a\,110\,(10)^b\,110\,(1010)^c\,0^\infty$. -/
  | B (a b c : ℕ)

def start : State := .A 2 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b =>
    Cfg.headRight SixState.C default
      (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
          (ListBlank.cons 1
            (ListBlank.cons 1
              (ListBlank.cons 0
                (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default))))))
  | .B a b c =>
    Cfg.headRight SixState.C default
      (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
          (ListBlank.cons 1
            (ListBlank.cons 1
              (ListBlank.cons 0
                (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
                  (ListBlank.cons 1
                    (ListBlank.cons 1
                      (ListBlank.cons 0
                        (ListBlank.append (([1, 0, 1, 0] : List (Fin 2)) ^ c)
                          default))))))))))

def next : State → Option State
  | .A a b =>
    if a < b then
      some (.A (2 * a + 2) (b - a - 1))
    else if a = b then
      none
    else if (a - b - 1) % 2 = 0 then
      some (.A (2 * ((a - b - 1) / 2) + 2) (2 * b + 2))
    else
      some (.B 2 (2 * ((a - b - 1) / 2) + 1) (b + 1))
  | .B a b c =>
    if a < b then
      some (.B (2 * a + 2) (b - a - 1) c)
    else if a = b then
      some (.A 2 (4 * a + 2 * c + 6))
    else
      some (.A 2 (2 * a + 2 * c + 2))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC

namespace M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.rep [0, 1] 1 .default)))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

def pat_E : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.rep [0, 1] 1 .default)))
    head := some E
    right := .sym 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .true), (pat_E, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | D (a b c : ℕ)
  | E (a b c : ℕ)

def start : State := .D 1 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b c =>
    evalTapePattern pat_D fun k => match k with | 0 => a | 1 => b | 2 => c | _ => 0
  | .E a b c =>
    evalTapePattern pat_E fun k => match k with | 0 => a | 1 => b | 2 => c | _ => 0

def next : State → Option State
  | .D (a + 1) b c => some (.D a b (c + 2))
  | .D 0 0 0 => some (.D 2 0 0)
  | .D 0 0 (c + 1) => some (.E 1 0 (c + 1))
  | .D 0 1 0 => some (.D 0 2 0)
  | .D 0 1 1 => some (.D 1 2 0)
  | .D 0 1 2 => some (.D 2 2 0)
  | .D 0 1 (c + 3) => some (.E 1 2 (c + 1))
  | .D 0 (b + 2) c => some (.E 1 b (c + 2))
  | .E (a + 1) b 0 => some (.E a b 1)
  | .E 0 0 0 => some (.D 0 0 1)
  | .E 0 (b + 1) 0 => some (.D 1 b 0)
  | .E a 0 1 => some (.D (a + 1) 0 1)
  | .E a 0 2 => some (.D (a + 2) 0 1)
  | .E _ 0 3 => none
  | .E a 0 4 => some (.D 0 (a + 3) 0)
  | .E a 0 5 => some (.D 1 (a + 3) 0)
  | .E a 0 6 => some (.D 2 (a + 3) 0)
  | .E a 0 (c + 7) => some (.E 1 (a + 3) (c + 1))
  | .E a (b + 1) 1 => some (.D (a + 2) b 0)
  | .E a (b + 1) 2 => some (.D (a + 3) b 0)
  | .E a (b + 1) (c + 3) => some (.E (a + 2) b (c + 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

namespace M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 .default))
    head := some A
    right := .rep [1, 1] 0 (.sym 0 (.rep [1] 1 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_C, .ge_const 1 6)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C (a b : ℕ)
  | M_3 (a c d : ℕ)
  | M_4 (a b c d : ℕ)

def start : State := .C 0 3

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (b + 6)) default)))
  | .M_3 a c d =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))
  | .M_4 a b c d =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))

def next : State → Option State
  | .C 0 b =>
    if b % 2 = 0 then some (.C (b / 2 + 1) 3)
    else some (.C (b / 2 + 3) 0)
  | .C (a + 1) b =>
    if b % 2 = 0 then some (.M_4 a (b / 2 + 1) 4 0)
    else some (.M_3 a (b / 2 + 2) 6)
  | .M_3 0 0 _ => none
  | .M_3 1 0 _ => none
  | .M_3 (a + 2) 0 d => some (.C (a + 1) (d + 3))
  | .M_3 0 (c + 1) d => some (.C (c + 1) d)
  | .M_3 (a + 1) (c + 1) d => some (.M_3 a c (d + 6))
  | .M_4 a 0 c d => some (.C (a + c + 1) d)
  | .M_4 0 1 0 _ => none
  | .M_4 (a + 1) 1 0 d => some (.C (a + 1) (d + 6))
  | .M_4 a (b + 2) 0 d => some (.M_3 a b (d + 9))
  | .M_4 a (b + 1) (c + 1) d => some (.M_4 a b c (d + 6))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

namespace M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

abbrev left_bcd (b c d : ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ b)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) default))

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 1 (.rep [0, 1] 2 (.rep [1] 3 .default))
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

def cfg_C (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (left_bcd b c d)
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 default)))))

def cfg_8 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
      (ListBlank.cons 1 (left_bcd b c d))))
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)))))

def cfg_57 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
      (ListBlank.cons 1 (left_bcd b c d))))
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))))

def cfg_89 (a k b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (left_bcd b c d)
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
            (ListBlank.cons 1 default))))))))

def cfg_101 (a k u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
        (ListBlank.cons 1 (left_bcd b c d)))))
    (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
            (ListBlank.cons 1 default))))))))

inductive State where
  /-- $C(a, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^b\,\mathrm{C}{>}\,110\,(10)^a\,1\,0^\infty$. -/
  | C (a b c d : ℕ)
  /-- $W(k, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^b\,\mathrm{E}{>}\,11110\,(10)^k\,1\,0^\infty$. -/
  | W (k b c d : ℕ)
  /-- $M(k, u, b, c, d) :=
    0^\infty\,1^d\,(10)^c\,1^{b+1}\,(01)^u\,10\,\mathrm{E}{>}\,01110\,(10)^k\,1\,0^\infty$. -/
  | M (k u b c d : ℕ)
  /-- $S(a, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^{b+1}\,0\,\mathrm{A}{>}\,111\,(11)^a\,0^\infty$. -/
  | S (a b c d : ℕ)
  /-- $R(a, b, c, d) :=
    0^\infty\,1^d\,(10)^c\,1^{b+1}\,0\,\mathrm{A}{>}\,1111\,(11)^a\,0^\infty$. -/
  | R (a b c d : ℕ)

def start : State := .C 0 3 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b c d => cfg_C a b c d
  | .W k b c d => cfg_89 0 k b c d
  | .M k u b c d => cfg_101 0 k u b c d
  | .S a b c d => cfg_57 a 0 b c d
  | .R a b c d => cfg_8 a 0 b c d

def next : State → Option State
  | .C 0 0 0 0 => some (.C 0 3 0 0)
  | .C 1 0 0 0 => some (.S 0 1 0 0)
  | .C (k + 2) 0 0 0 => some (.W k 2 0 0)
  | .C 0 0 0 1 => none
  | .C 0 0 0 (d + 2) => some (.C 2 d 0 0)
  | .C 1 0 0 (d + 1) => some (.S 0 (d + 2) 0 0)
  | .C (k + 2) 0 0 (d + 1) => some (.M k 0 d 0 0)
  | .C 0 0 (c + 1) d => some (.C 0 3 (c + 1) d)
  | .C 1 0 (c + 1) d => some (.S 0 1 (c + 1) d)
  | .C (k + 2) 0 (c + 1) d => some (.W k 2 (c + 1) d)
  | .C 0 1 _ 0 => none
  | .C 0 1 c (d + 1) => some (.C (c + 2) d 0 0)
  | .C 0 (b + 2) c d => some (.C 2 b c d)
  | .C 1 (b + 1) c d => some (.S 0 (b + 2) c d)
  | .C (k + 2) (b + 1) c d => some (.M k 0 b c d)
  | .W 0 b c d => some (.C 2 b c d)
  | .W 1 b c d => some (.S 0 (b + 3) c d)
  | .W (k + 2) b c d => some (.M k 0 (b + 1) c d)
  | .M 0 u b c d => some (.S (u + 2) b c d)
  | .M 1 u 0 c 0 => some (.C 0 0 (u + c + 5) 1)
  | .M 2 u 0 c 0 => some (.C 0 3 (u + c + 5) 1)
  | .M 3 u 0 c 0 => some (.C 0 4 (u + c + 5) 1)
  | .M (k + 4) u 0 c 0 => some (.W k 2 (u + c + 5) 1)
  | .M (k + 1) u 0 c 1 => some (.W k (2 * (u + c) + 6) 0 0)
  | .M (k + 1) u 0 c (d + 2) => some (.M k (u + c + 2) d 0 0)
  | .M (k + 1) u 1 0 0 => some (.W k (2 * u + 6) 0 0)
  | .M (k + 1) u 1 0 (d + 1) => some (.M k (u + 2) d 0 0)
  | .M (k + 1) u 1 (c + 1) d => some (.W k (2 * u + 6) (c + 1) d)
  | .M (k + 1) u (b + 2) c d => some (.M k (u + 2) b c d)
  | .S a 0 c 0 => some (.C (a + c + 2) 0 0 0)
  | .S a 0 c 1 => some (.C 0 (2 * (a + c) + 4) 0 0)
  | .S a 0 c (d + 2) => some (.R (a + c + 1) d 0 0)
  | .S a 1 0 0 => some (.C 0 (2 * a + 4) 0 0)
  | .S a 1 0 (d + 1) => some (.R (a + 1) d 0 0)
  | .S a 1 (c + 1) d => some (.C 0 (2 * a + 4) (c + 1) d)
  | .S a (b + 2) c d => some (.R (a + 1) b c d)
  | .R a 0 c 0 => some (.C 0 (2 * (a + c) + 7) 0 0)
  | .R a 0 c 1 => some (.C 0 (2 * (a + c) + 5) 0 0)
  | .R _ 0 _ 2 => none
  | .R a 0 c (d + 3) => some (.C (a + c + 3) d 0 0)
  | .R a 1 0 0 => some (.C 0 (2 * a + 5) 0 0)
  | .R _ 1 0 1 => none
  | .R a 1 0 (d + 2) => some (.C (a + 3) d 0 0)
  | .R a 1 (c + 1) d => some (.C 0 (2 * a + 5) (c + 1) d)
  | .R _ 2 _ 0 => none
  | .R a 2 c (d + 1) => some (.C (a + c + 3) d 0 0)
  | .R a (b + 3) c d => some (.C (a + 3) b c d)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE

namespace M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 1] 1 (.rep [0, 1] 0 .default)
    head  := some C
    right := .rep [1, 1] 2 (.rep [1, 0] 3 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))) }
def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_A, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State
  | mk (a k d c : ℕ)

def start : State := .mk 0 0 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .mk a k d c => evalTapePattern pat_A (fun | 0 => a | 1 => k | 2 => d | 3 => c | _ => 0)

def next : State → Option State
  | .mk a (k + 1) d (c + 1) => some (.mk a k (d + 2) c)
  | .mk a (k + 1) d 0       => some (.mk a (k + 1) 0 (d + 1))
  | .mk (a + 1) 0 d (c + 2) => some (.mk a (d + 1) 2 c)
  | .mk (a + 1) 0 d 1       => some (.mk a (d + 2) 0 1)
  | .mk (a + 1) 0 d 0       => some (.mk a (d + 2) 0 0)
  | .mk 0 0 d (c + 1)       => some (.mk (d + 1) 0 0 (c + 1))
  | .mk 0 0 _ 0             => none

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC

namespace M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 1 (.sym 0 (.rep [1] 0 .default))
    head := some F
    right := .sym 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

inductive State where
  /-- $P(a, b, c) := 0^\infty\,1^a\,0\,1^b\,\mathrm{F}{>}\,1\,1^c\,0^\infty$. -/
  | P (a b c : ℕ)

def start : State := .P 0 3 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P a b c =>
    Cfg.headRight SixState.F
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def next : State → Option State
  | .P 0 0 c => some (.P 0 (c + 3) 1)
  | .P (a + 1) 0 c => some (.P 0 (a + c + 7) 1)
  | .P a 1 c => some (.P (a + 2) (c + 3) 1)
  | .P 0 2 _ => none
  | .P (a + 1) 2 c => some (.P a (c + 4) 1)
  | .P a (b + 3) c => some (.P a (b + 1) (c + 3))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA

namespace M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def cfg_D_base (a b : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b) r))

def cfg_D7 (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b (ListBlank.append [1] default)

def cfg_D74 (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b (ListBlank.append [0, 1, 0, 1] default)

def cfg_D75 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 0, 1] default)))

def cfg_D76 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1] default)))

def cfg_D77 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def cfg_D158 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1] default)))

def cfg_D160 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 0, 1] default)))

def cfg_D162 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def cfg_D230 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1] default)))

def cfg_D231 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def cfg_D294 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1] default)))

def cfg_D296 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def pat_A_right : TapeExpr (Fin 2) :=
  .sym 1 (.sym 1
    (.rep [1, 1] 1
      (.rep [1] 2
        (.rep [0, 1] 3
          (.rep [0] 4
            (.rep [0, 0] 5
              (.rep [1] 6
                (.rep [1, 1] 7
                  (.rep [0, 1] 8 .default)))))))))

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some D
    right := pat_A_right }

def eq_const (idx val : ℕ) : VarCond :=
  .and (.ge_const idx val) (.not (.ge_const idx (val + 1)))

def cond_case_7 : VarCond :=
  .and (eq_const 2 1) (.and (eq_const 3 0) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 0) (.and (eq_const 7 0) (eq_const 8 0))))))

def cond_case_74 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 0) (.and (eq_const 7 0) (eq_const 8 1))))))

def cond_case_75 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 3)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 1)))))

def cond_case_76 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 2) (eq_const 8 1)))))

def cond_case_77 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 3)
    (.and (eq_const 6 3) (eq_const 8 1))))

def cond_case_158 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 1) (eq_const 8 1)))))

def cond_case_160 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 2)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 1)))))

def cond_case_162 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 2)
    (.and (eq_const 6 3) (eq_const 8 1))))

def cond_case_230 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 2)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 0)))))

def cond_case_231 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 3)
    (.and (eq_const 6 2) (eq_const 8 1))))

def cond_case_294 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 3)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 0)))))

def cond_case_296 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 2)
    (.and (eq_const 6 2) (eq_const 8 1))))

def cond_A : VarCond :=
  .or cond_case_7 (.or cond_case_74 (.or cond_case_75 (.or cond_case_76
    (.or cond_case_77 (.or cond_case_158 (.or cond_case_160 (.or cond_case_162
      (.or cond_case_230 (.or cond_case_231 (.or cond_case_294 cond_case_296))))))))))

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, cond_A)]

inductive State where
  | D7 (a b : ℕ)
  | D74 (a b : ℕ)
  | D75 (a b c : ℕ)
  | D76 (a b c : ℕ)
  | D77 (a b c d : ℕ)
  | D158 (a b c : ℕ)
  | D160 (a b c : ℕ)
  | D162 (a b c d : ℕ)
  | D230 (a b c : ℕ)
  | D231 (a b c d : ℕ)
  | D294 (a b c : ℕ)
  | D296 (a b c d : ℕ)

def start : State := .D7 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D7 a b => cfg_D7 a b
  | .D74 a b => cfg_D74 a b
  | .D75 a b c => cfg_D75 a b c
  | .D76 a b c => cfg_D76 a b c
  | .D77 a b c d => cfg_D77 a b c d
  | .D158 a b c => cfg_D158 a b c
  | .D160 a b c => cfg_D160 a b c
  | .D162 a b c d => cfg_D162 a b c d
  | .D230 a b c => cfg_D230 a b c
  | .D231 a b c d => cfg_D231 a b c d
  | .D294 a b c => cfg_D294 a b c
  | .D296 a b c d => cfg_D296 a b c d

def next : State → Option State
  | .D7 0 b => some (.D77 0 0 0 (b + 1))
  | .D7 (a + 1) b => some (.D7 a (b + 1))
  | .D74 0 b => some (.D7 (b + 2) 0)
  | .D74 (a + 1) b => some (.D74 a (b + 1))
  | .D75 0 b 0 => some (.D158 (b + 1) 0 0)
  | .D75 0 b (c + 1) => some (.D160 (b + 1) 0 c)
  | .D75 (a + 1) b c => some (.D75 a (b + 1) c)
  | .D76 0 b 0 => some (.D75 0 0 (b + 2))
  | .D76 0 b (c + 1) => some (.D77 0 0 (b + 2) c)
  | .D76 (a + 1) b c => some (.D76 a (b + 1) c)
  | .D77 0 b 0 d => some (.D158 (b + 1) 0 (d + 1))
  | .D77 0 b (c + 1) d => some (.D162 (b + 1) 0 c d)
  | .D77 (a + 1) b c d => some (.D77 a (b + 1) c d)
  | .D158 0 b 0 => some (.D230 0 0 (b + 3))
  | .D158 0 b (c + 1) => some (.D231 0 0 (b + 2) c)
  | .D158 (a + 1) b c => some (.D158 a (b + 1) c)
  | .D160 0 b 0 => some (.D74 (b + 2) 0)
  | .D160 0 b (c + 1) => some (.D75 (b + 2) 0 c)
  | .D160 (a + 1) b c => some (.D160 a (b + 1) c)
  | .D162 0 b 0 d => some (.D76 (b + 2) 0 d)
  | .D162 0 b (c + 1) d => some (.D77 (b + 2) 0 c d)
  | .D162 (a + 1) b c d => some (.D162 a (b + 1) c d)
  | .D230 0 _ 0 => none
  | .D230 0 b 1 => some (.D74 (b + 1) 0)
  | .D230 0 b (c + 2) => some (.D294 (b + 1) 0 c)
  | .D230 (a + 1) b c => some (.D230 a (b + 1) c)
  | .D231 0 b 0 d => some (.D76 (b + 1) 0 d)
  | .D231 0 b (c + 1) d => some (.D296 (b + 1) 0 c d)
  | .D231 (a + 1) b c d => some (.D231 a (b + 1) c d)
  | .D294 0 b c => some (.D230 (b + 2) 0 c)
  | .D294 (a + 1) b c => some (.D294 a (b + 1) c)
  | .D296 0 b 0 d => some (.D158 (b + 2) 0 d)
  | .D296 0 b (c + 1) d => some (.D231 (b + 2) 0 c d)
  | .D296 (a + 1) b c d => some (.D296 a (b + 1) c d)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC

namespace M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1, 1] 0 .default)))
      head := some SixState.D
      right := .sym 1 (.rep [1] 2 .default) },
    .and (.ge_const 0 1) (.and (.ge_const 1 1) (.ge_const 2 1)))]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C (k m f : ℕ)

def start : State := .C 2 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C k m f =>
    Cfg.headRight SixState.D
      (ListBlank.append [0]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default))))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1)) default))

def next : State → Option State
  | .C 0 0 _ => none
  | .C 0 1 _ => none
  | .C 0 2 f =>
    if f % 2 = 0 then some (.C (f / 2 + 3) 2 4)
    else some (.C (f / 2 + 5) 0 1)
  | .C 0 (m + 3) f =>
    if f % 2 = 0 then some (.C m (f / 2 + 5) 1)
    else some (.C m (f / 2 + 5) 4)
  | .C 1 0 f =>
    if f % 2 = 0 then some (.C (f / 2 + 3) 0 1)
    else some (.C (f / 2 + 2) 2 4)
  | .C (k + 2) 0 f =>
    if f % 2 = 0 then some (.C k (f / 2 + 3) 4)
    else some (.C k (f / 2 + 4) 1)
  | .C (k + 1) (m + 1) f =>
    if k < m then some (.C 0 (m - k) (f + 6 * (k + 1)))
    else if m < k then some (.C (k - m) 0 (f + 6 * (m + 1)))
    else some (.C 0 0 (f + 6 * (k + 1)))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

namespace M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
      head := some SixState.E
      right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1
        (.rep [1, 1] 2 .default)))))) }, .true),
   ({ left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
      head := some SixState.E
      right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1
        (.rep [1, 1] 2 .default)))))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C_0 (a b c : ℕ)
  | C_1 (a b c : ℕ)

def start : State := .C_1 2 2 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C_0 a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))
  | .C_1 a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))

def next : State → Option State
  | .C_0 _ 0 0 => none
  | .C_0 a 0 1 => some (.C_1 2 2 (a + 1))
  | .C_0 a 0 (d + 2) => some (.C_0 1 (a + 3) d)
  | .C_0 a (b + 1) 0 => some (.C_1 (a + 1) 0 b)
  | .C_0 a (b + 1) (c + 1) => some (.C_0 (a + 3) b c)
  | .C_1 _ 0 0 => none
  | .C_1 a 0 1 => some (.C_0 1 0 (a + 3))
  | .C_1 a 0 (d + 2) => some (.C_1 2 (a + 3) d)
  | .C_1 a (b + 1) 0 => some (.C_0 (a + 2) 0 b)
  | .C_1 a (b + 1) (c + 1) => some (.C_1 (a + 3) b c)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

namespace M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 1 (.rep [0, 1] 0
      (.sym 1 (.rep [0, 1] 1 (.sym 1 (.rep [0, 1] 2 .default)))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

inductive State where
  /-- $C(a, b, c) := 0^\infty\,{<}\mathrm{C}\,1\,(01)^a\,1\,(01)^b\,1\,(01)^c\,0^\infty$. -/
  | C (a b c : ℕ)

def start : State := .C 1 3 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b c =>
    Cfg.headLeft SixState.C default
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append [1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))))

def next : State → Option State
  | .C a 0 0 => if a % 2 = 1 then some (.C 1 (3 * (a / 2) + 6) 1) else none
  | .C a 0 (c + 1) => some (.C 1 (a + 2) c)
  | .C a 1 c => some (.C 1 (a + 2) (c + 2))
  | .C a (b + 2) c => some (.C (a + 3) b c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA

namespace M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .default
      head := some SixState.C
      right := .sym 0 (.rep [1] 0 .default) }, .ge_const 0 1),
   ({ left := .sym 1 (.rep [0, 1] 0 .default)
      head := some SixState.C
      right := .sym 0 (.rep [1] 1 .default) }, .ge_const 1 1)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | P_1 (c : ℕ)
  | P_2 (a c : ℕ)
  | D_0_odd (k w : ℕ)
  | D_0_even (k w : ℕ)
  | D_succ_odd (a k w : ℕ)

def start : State := .P_1 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 c =>
    Cfg.headRight SixState.C default
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .P_2 a c =>
    Cfg.headRight SixState.C
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .D_0_odd k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_0_even k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_succ_odd a k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

def next : State → Option State
  | .P_1 0 => some (.P_1 2)
  | .P_1 (w + 1) => some (.D_0_odd 0 w)
  | .P_2 a 0 => some (.P_2 a 2)
  | .P_2 a (w + 1) => some (.D_succ_odd a 0 w)
  | .D_0_odd k 0 => some (.P_1 (2 * k + 3))
  | .D_0_odd k 1 => some (.P_1 (2 * k + 5))
  | .D_0_odd k (w + 2) => some (.D_0_even (k + 1) w)
  | .D_0_even _ 0 => none
  | .D_0_even k 1 => some (.P_2 k 2)
  | .D_0_even k 2 => some (.P_2 k 4)
  | .D_0_even k 3 => some (.P_2 k 6)
  | .D_0_even k (w + 4) => some (.D_succ_odd k 2 w)
  | .D_succ_odd 0 k 0 => some (.P_1 (2 * k + 4))
  | .D_succ_odd 0 k 1 => some (.P_1 (2 * k + 6))
  | .D_succ_odd (a + 1) k 0 => some (.P_2 a (2 * k + 4))
  | .D_succ_odd (a + 1) k 1 => some (.P_2 a (2 * k + 6))
  | .D_succ_odd 0 k (w + 2) => some (.D_0_odd (k + 2) w)
  | .D_succ_odd (a + 1) k (w + 2) => some (.D_succ_odd a (k + 2) w)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 .default
    head  := some A
    right := .rep [1] 1 .default }

/-- Hub Pattern 2: `P2(k, m, c) := 0^∞ (10)^(k+1) (11)^m A> 1^c 0^∞` (`k, m, c ∈ ℕ`). -/
def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 1] 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head  := some A
    right := .rep [1] 2 .default }

/-- The closed 2-hub pattern set `ps`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State
  | P_1 (a c : Nat)
  | P_2 (k m c : Nat)

def start : State := .P_1 2 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a c => evalTapePattern pat_P1 (fun | 0 => a | 1 => c | _ => 0)
  | .P_2 k m c => evalTapePattern pat_P2 (fun | 0 => k | 1 => m | 2 => c | _ => 0)

def next : State → Option State
  | .P_1 a 0 => some (.P_1 2 (a + 1))
  | .P_1 a 1 => some (.P_1 (a + 2) 0)
  | .P_1 a (c + 2) =>
    match a % 2 with
    | 0 => some (.P_1 (a + 3) c)
    | _ => match c with
      | 0 => none
      | 1 => some (.P_2 (a / 2) 1 0)
      | d + 2 => some (.P_2 (a / 2) 2 d)
  | .P_2 k m 1 => some (.P_2 k (m + 1) 0)
  | .P_2 0 m 0 => some (.P_1 0 (2 * m + 3))
  | .P_2 (k + 1) m 0 => some (.P_2 k 0 (2 * m + 3))
  | .P_2 0 m (d + 2) => some (.P_1 (2 * m + 4) d)
  | .P_2 (k + 1) m (d + 2) => some (.P_2 k (m + 2) d)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .default
      head := some SixState.C
      right := .sym 0 (.rep [1] 0 .default) }, .ge_const 0 1),
   ({ left := .sym 1 (.rep [0, 1] 0 .default)
      head := some SixState.C
      right := .sym 0 (.rep [1] 1 .default) }, .ge_const 1 1)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | P_1 (c : ℕ)
  | P_2 (a c : ℕ)
  | D_1_0_odd (k w : ℕ)
  | D_1_0_even (k w : ℕ)
  | D_1_succ_odd (a k w : ℕ)

def start : State := .P_1 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 c =>
    Cfg.headRight SixState.C default
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .P_2 a c =>
    Cfg.headRight SixState.C
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .D_1_0_odd k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_1_0_even k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_1_succ_odd a k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

def next : State → Option State
  | .P_1 0 => some (.P_1 3)
  | .P_1 (w + 1) => some (.D_1_0_even 0 w)
  | .P_2 0 0 => some (.P_1 4)
  | .P_2 (a + 1) 0 => some (.P_2 a 4)
  | .P_2 0 (w + 1) => some (.D_1_0_odd 1 w)
  | .P_2 (a + 1) (w + 1) => some (.D_1_succ_odd a 1 w)
  | .D_1_0_odd k 0 => some (.P_1 (2 * k + 3))
  | .D_1_0_odd k 1 => some (.P_1 (2 * k + 5))
  | .D_1_0_odd k (w + 2) => some (.D_1_0_even (k + 1) w)
  | .D_1_0_even _ 0 => none
  | .D_1_0_even k 1 => some (.P_2 k 2)
  | .D_1_0_even k 2 => some (.P_2 k 4)
  | .D_1_0_even k 3 => some (.P_2 k 6)
  | .D_1_0_even k (w + 4) => some (.D_1_succ_odd k 2 w)
  | .D_1_succ_odd 0 k 0 => some (.P_1 (2 * k + 4))
  | .D_1_succ_odd 0 k 1 => some (.P_1 (2 * k + 6))
  | .D_1_succ_odd (a + 1) k 0 => some (.P_2 a (2 * k + 4))
  | .D_1_succ_odd (a + 1) k 1 => some (.P_2 a (2 * k + 6))
  | .D_1_succ_odd 0 k (w + 2) => some (.D_1_0_odd (k + 2) w)
  | .D_1_succ_odd (a + 1) k (w + 2) => some (.D_1_succ_odd a (k + 2) w)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def drainB (b w : ℕ) : Option (ℕ × ℕ) :=
  if b % 2 = 0 then
    if b = 0 then some (w + 1, 0)
    else some (5 * (b / 2 - 1) + w + 6, 0)
  else if b = 1 then some (w + 1, 0)
  else if b = 3 then some (w + 1, 1)
  else if b = 5 then none
  else
    let m := b / 2 - 3
    let q := m / 3
    if m % 3 = 0 then some (6 * q + w + 7, 0)
    else if m % 3 = 1 then some (5 * q + w + 6, q + 2)
    else drainB q (5 * q + w + 12)
termination_by b

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1, 0, 1, 0, 1] 0 .default
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 .default))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

def cfg_C (k a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1, 0, 1, 0, 1] : List (Fin 2)) ^ k) default)
    (ListBlank.append [0, 1, 0]
      (ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))

inductive State where
  /-- $C(k, a, b) := 0^\infty\,(10101)^k\,\mathrm{C}{>}\,0\,1\,0\,1^a\,0\,1^b\,0^\infty$. -/
  | C (k a b : ℕ)

def start : State := .C 0 2 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C k a b => cfg_C k a b

def next : State → Option State
  | .C k a b =>
    if a % 2 = 0 then
      if a = 0 then none
      else if a = 2 then
        if b % 2 = 0 then
          if b = 0 then some (.C 0 (5 * k + 6) 0)
          else if b = 2 then some (.C 0 (5 * k + 6) 1)
          else some (.C (k + 1) (b - 3) 1)
        else some (.C (k + 1) (b + 1) 0)
      else
        match drainB b (a - 3) with
        | some (a', b') => some (.C (k + 1) a' b')
        | none => none
    else if a = 1 then
      if b = 0 then none
      else if b = 1 then none
      else
        match drainB (b - 2) (5 * k + 7) with
        | some (a', b') => some (.C 0 a' b')
        | none => none
    else if a = 3 then some (.C 0 (5 * k + b + 6) 0)
    else if a = 5 then some (.C 0 (5 * k + 6) (b + 1))
    else some (.C (k + 1) (a - 6) (b + 1))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC

namespace M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.rep [0, 1] 0 .default)
    head := some A
    right := .rep [0, 1] 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

inductive State where
  /-- $A(a, b, c) := 0^\infty\,(10)^a\,0\,\mathrm{A}{>}\,(01)^b\,1^c\,0^\infty$. -/
  | A (a b c : ℕ)

def start : State := .A 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def next : State → Option State
  | .A a b 0 => some (.A a 0 (2 * b + 2))
  | .A 0 _ 1 => none
  | .A 0 b (d + 2) => some (.A (b + 2) 0 (d + 1))
  | .A (a + 1) b (d + 1) => some (.A a (b + 2) d)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE

namespace M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_C1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .default }

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.rep [1] 1 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.rep [0, 1] 2 .default)) }

def pat_C2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C1, .true), (pat_D, .true), (pat_C2, .true)]

def cfg_C1 (a : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    default

def cfg_D (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))

def cfg_C2 (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))

inductive State where
  /-- $C_1(a) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,0^\infty$. -/
  | C1 (a : ℕ)
  /-- $D(a, b, c) := 0^\infty\,1^b\,(10)^{a+1}\,\mathrm{D}{>}\,(01)^{c+1}\,0^\infty$. -/
  | D (a b c : ℕ)
  /-- $C_2(a, b) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,1101\,(01)^b\,0^\infty$. -/
  | C2 (a b : ℕ)

def start : State := .C1 3

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C1 a => cfg_C1 a
  | .D a b c => cfg_D a b c
  | .C2 a b => cfg_C2 a b

def next : State → Option State
  | .C1 0 => none
  | .C1 1 => some (.C2 1 0)
  | .C1 (a + 2) => some (.D 0 a 1)
  | .C2 0 b => some (.C1 (2 * b + 7))
  | .C2 1 b => some (.C1 (2 * b + 9))
  | .C2 (a + 2) b => some (.C2 a (b + 2))
  | .D a 0 0 => some (.C2 (2 * a + 1) 1)
  | .D a 1 0 => some (.C2 (2 * a + 3) 0)
  | .D a 2 0 => some (.C2 (2 * a + 5) 0)
  | .D _ 3 0 => none
  | .D _ 4 0 => none
  | .D a 5 0 => some (.C2 1 (a + 3))
  | .D a (b + 6) 0 => some (.D 0 b (a + 4))
  | .D a 0 (c + 1) => some (.C2 (2 * a + 3) c)
  | .D a 1 (c + 1) => some (.D (a + 1) 0 c)
  | .D a (b + 2) (c + 1) => some (.D (a + 2) b c)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE

namespace M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some A
    right := .default }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

inductive State where
  /-- $A(m, n) := 0^\infty\,1^{m+1}\,(01)^n\,0\,\mathrm{A}{>}\,0^\infty$. -/
  | A (m n : ℕ)

def start : State := .A 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A m n =>
    Cfg.headRight SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default)))
      default

def next : State → Option State
  | .A 0 n =>
    if n % 2 = 0 then none
    else some (.A (6 * (n / 2) + 6) 1)
  | .A 1 _ => none
  | .A 2 n =>
    if n % 2 = 0 then some (.A (6 * (n / 2) + 5) 1)
    else some (.A (6 * (n / 2) + 9) 1)
  | .A 3 n =>
    if n % 2 = 0 then some (.A 0 (3 * (n / 2) + 3))
    else some (.A 0 (3 * (n / 2) + 5))
  | .A (m + 4) n =>
    if n % 2 = 0 then some (.A m (3 * (n / 2) + 4))
    else some (.A m (3 * (n / 2) + 6))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF

namespace M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

inductive State where
  /-- $A(a, b) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^{b+1}\,0^\infty$. -/
  | A (a b : ℕ)

def start : State := .A 1 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))

def next : State → Option State
  | .A a b =>
    let k := a / 2
    if a % 2 = 0 then
      match b with
      | 0 => some (.A 3 (2 * k + 1))
      | 1 => some (.A (2 * k + 1) 0)
      | c + 2 => some (.A (2 * k + 3) c)
    else if b ≤ 2 * k then
      if b % 2 = 0 then
        some (.A (4 * (b / 2) + 3) (2 * (k - b / 2) + 2))
      else
        some (.A (4 * (b / 2) + 7) (2 * (k - b / 2 - 1)))
    else if b = 2 * k + 1 then
      some (.A (4 * k + 1) 0)
    else if b = 2 * k + 2 then
      some (.A (4 * k + 7) 0)
    else if b = 2 * k + 3 then
      none
    else if b = 2 * k + 4 then
      some (.A (4 * k + 5) 0)
    else
      some (.A (4 * k + 7) (b - 2 * k - 5))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE

namespace M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_64 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some A
    right := .sym 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_64, VarCond.true)]

inductive State where
  /-- $E(a, b, c) := 0^\infty\,1\,(01)^{b+1}\,(11)^a\,111\,\mathrm{A}{>}\,1^{c+1}\,0^\infty$. -/
  | E (a b c : ℕ)

def start : State := .E 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a b c =>
    Cfg.headRight A
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
          (ListBlank.cons 1 (ListBlank.cons 0
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
              (ListBlank.cons 1 default))))))))
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def next : State → Option State
  | .E a 0 0 => some (.E 0 0 (2 * a + 5))
  | .E a 0 1 => some (.E 0 0 (2 * a + 3))
  | .E a 0 2 => some (.E 0 0 (2 * a + 9))
  | .E a 0 3 => some (.E 0 0 (2 * a + 7))
  | .E a 0 4 => some (.E 0 0 (2 * a + 12))
  | .E a 0 5 => some (.E 0 0 (2 * a + 10))
  | .E _ 0 6 => none
  | .E a 0 (c + 7) => some (.E 0 (a + 4) (c + 1))
  | .E a 1 0 => some (.E 0 2 (2 * a + 3))
  | .E a 1 1 => some (.E 0 2 (2 * a + 1))
  | .E a (b + 1) (c + 2) => some (.E (a + 2) b c)
  | .E a (b + 2) 0 => some (.E 0 b (2 * a + 7))
  | .E a (b + 2) 1 => some (.E 0 b (2 * a + 5))

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD

namespace M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 0 (.rep [1, 0] 1 (.sym 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.sym 1 (.sym 1 .default))) }

def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [0, 1] 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 .default))))
    head := some D
    right := .rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | P_1 (a b c : ℕ)
  | P_2 (a b c : ℕ)
  deriving DecidableEq, Repr

def start : State := .P_1 1 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a b c => evalTapePattern pat_P1 (fun | 0 => a | 1 => b | 2 => c | _ => 0)
  | .P_2 a b c => evalTapePattern pat_P2 (fun | 0 => a | 1 => b | 2 => c | _ => 0)

def next : State → Option State
  | .P_1 0 _ 0 => none
  | .P_1 (a + 1) b 0 => some (.P_2 2 (b + 1) a)
  | .P_1 a 0 1 => some (.P_2 2 0 (a + 1))
  | .P_1 a 0 (c + 2) => some (.P_1 (a + 4) 0 c)
  | .P_1 a (b + 1) (c + 1) => some (.P_1 (a + 2) b c)
  | .P_2 a b 0 => some (.P_1 1 (b + 2) (a + 1))
  | .P_2 a 0 1 => some (.P_2 2 0 (a + 4))
  | .P_2 _ 0 2 => none
  | .P_2 a 0 (c + 3) => some (.P_2 2 (a + 2) c)
  | .P_2 a (b + 1) (c + 1) => some (.P_2 (a + 2) b c)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB

namespace M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.rep [0, 1] 3 (.sym 1 .default))) }

def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 .default) }

def pat_P3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 .default }

def pat_P4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.rep [0, 1] 3 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true), (pat_P3, .true), (pat_P4, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | P_1 (a b c d : ℕ)
  | P_2 (a b c : ℕ)
  | P_3 (a b c : ℕ)
  | P_4 (a b c d : ℕ)
  deriving DecidableEq, Repr

def start : State := .P_2 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a b c d => evalTapePattern pat_P1 (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)
  | .P_2 a b c => evalTapePattern pat_P2 (fun | 0 => a | 1 => b | 2 => c | _ => 0)
  | .P_3 a b c => evalTapePattern pat_P3 (fun | 0 => a | 1 => b | 2 => c | _ => 0)
  | .P_4 a b c d => evalTapePattern pat_P4 (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)

def next : State → Option State
  | .P_1 0 b c 0 =>
    if b % 2 = 0 then some (.P_2 0 0 (b / 2 + c + 2))
    else some (.P_1 (b / 2 + c) 4 1 2)
  | .P_1 1 0 c 0 => some (.P_1 c 4 1 2)
  | .P_1 1 1 c 0 => some (.P_1 0 0 1 (c + 2))
  | .P_1 1 2 c 0 => some (.P_2 0 2 (c + 3))
  | .P_1 1 (_ + 3) _ 0 => none
  | .P_1 (a + 2) b c 0 => some (.P_1 a b 1 (c + 2))
  | .P_1 0 0 0 (_ + 1) => none
  | .P_1 0 0 (c + 1) (d + 1) => some (.P_4 c 4 1 (d + 2))
  | .P_1 0 (b' + 1) c (d + 1) =>
    if (b' + 1) % 2 = 0 then some (.P_4 (b' / 2 + c) 4 1 (d + 2))
    else some (.P_1 0 0 (b' / 2 + c + 2) d)
  | .P_1 (a + 1) b c (d + 1) => some (.P_1 a b (c + 2) d)
  | .P_2 0 0 0 => none
  | .P_2 0 0 (c + 1) => some (.P_1 c 4 1 1)
  | .P_2 0 (b' + 1) c =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 1)
    else some (.P_3 0 0 (b' / 2 + c + 2))
  | .P_2 (a + 1) b c => some (.P_3 a b (c + 2))
  | .P_3 0 0 0 => none
  | .P_3 0 0 (c + 1) => some (.P_1 c 4 1 2)
  | .P_3 0 (b' + 1) c =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 2)
    else some (.P_2 0 0 (b' / 2 + c + 2))
  | .P_3 (a + 1) b c => some (.P_2 a b (c + 2))
  | .P_4 0 0 0 0 => none
  | .P_4 0 0 (c + 1) 0 => some (.P_1 c 4 1 1)
  | .P_4 0 (b' + 1) c 0 =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 1)
    else some (.P_3 0 0 (b' / 2 + c + 2))
  | .P_4 (a + 1) b c 0 => some (.P_3 a b (c + 2))
  | .P_4 0 0 0 (_ + 1) => none
  | .P_4 0 0 (c + 1) (d + 1) => some (.P_1 c 4 1 (d + 2))
  | .P_4 0 (b' + 1) c (d + 1) =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 (d + 2))
    else some (.P_4 0 0 (b' / 2 + c + 2) d)
  | .P_4 (a + 1) b c (d + 1) => some (.P_4 a b (c + 2) d)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD

end BusyBeaver
