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

/-- Parametric half-tape segment for `HasStackedCollatzReduction`: in addition to single symbols
and repeated blocks, a `.word words stack_idx` segment expands a variable-length stack word
`stacks stack_idx : List ℕ` over a finite block vocabulary `words : List (List Γ)`. -/
inductive StackSeg (Γ : Type*) where
  /-- Single symbol `a`. -/
  | sym (a : Γ)
  /-- Finite block `blk` repeated `vars var_idx` times. -/
  | rep (blk : List Γ) (var_idx : ℕ)
  /-- Stack word `stacks stack_idx` expanded over block vocabulary `words`. -/
  | word (words : List (List Γ)) (stack_idx : ℕ)

/-- Whether a `StackSeg Γ` is a `.word` stack segment. -/
def StackSeg.isWord {Γ : Type*} : StackSeg Γ → Bool
  | .word _ _ => true
  | _ => false

/-- A `StackSeg Γ` is well-formed when every repeated block or stack-vocabulary block is non-empty
and contains no blank (`default`) symbols, and every `.word` vocabulary is non-empty. -/
def StackSeg.WellFormed {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] : StackSeg Γ → Bool
  | .sym _ => true
  | .rep blk _ => !blk.isEmpty && blk.all (· != default)
  | .word words _ => !words.isEmpty && words.all (fun w => !w.isEmpty && w.all (· != default))

/-- Parametric stack-word half-tape expression (evaluated from head to blank tail). -/
abbrev StackExpr (Γ : Type*) := List (StackSeg Γ)

/-- Evaluate a single `StackSeg Γ` under counter assignment `vars : ℕ → ℕ` and stack assignment
`stks : ℕ → List ℕ`. -/
def evalStackSeg {Γ : Type*} : StackSeg Γ → (ℕ → ℕ) → (ℕ → List ℕ) → List Γ
  | .sym a, _, _ => [a]
  | .rep blk v, vars, _ => blk ^ vars v
  | .word words s, _, stks => ((stks s).map (fun d => words.getD d [])).flatten

/-- Evaluate a `StackExpr Γ` under counter assignment `vars : ℕ → ℕ` and stack assignment
`stks : ℕ → List ℕ`. -/
def evalStackExpr {Γ : Type*} [Inhabited Γ] :
    StackExpr Γ → (ℕ → ℕ) → (ℕ → List ℕ) → ListBlank Γ
  | [], _, _ => default
  | seg :: rest, vars, stks =>
      ListBlank.append (evalStackSeg seg vars stks) (evalStackExpr rest vars stks)

/-- Parametric stack-word full-tape configuration pattern. -/
structure StackPattern (Γ Λ : Type*) where
  /-- Left half-tape expression. -/
  left : StackExpr Γ
  /-- Control state (`some q` or `none`). -/
  head : Option Λ
  /-- Right half-tape expression (whose head is under the tape head). -/
  right : StackExpr Γ

/-- A `StackPattern Γ Λ` is well-formed when all segments on both half-tapes are well-formed
(non-empty and blank-free blocks), at least one half-tape is empty (single-sided tape boundary),
and at most one `.word` stack segment appears across the pattern. -/
def StackPattern.WellFormed {Γ Λ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (p : StackPattern Γ Λ) : Bool :=
  p.left.all StackSeg.WellFormed &&
  p.right.all StackSeg.WellFormed &&
  (p.left.isEmpty || p.right.isEmpty) &&
  (decide (p.left.countP StackSeg.isWord + p.right.countP StackSeg.isWord ≤ 1))

/-- Evaluate a `StackPattern Γ Λ` under counter assignment `vars : ℕ → ℕ` and stack assignment
`stks : ℕ → List ℕ`. -/
def evalStackPattern {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (p : StackPattern Γ Λ) (vars : ℕ → ℕ) (stks : ℕ → List ℕ) : Cfg Γ Λ :=
  let r := evalStackExpr p.right vars stks
  ⟨p.head, ⟨r.head, evalStackExpr p.left vars stks, r.tail⟩⟩

/-- Finite list of guarded stack-word tape patterns. -/
abbrev StackPatternSet (Γ Λ : Type*) := List (StackPattern Γ Λ × VarCond)

/-- A `StackPatternSet Γ Λ` is well-formed when it is non-empty and every pattern in it is
well-formed (`StackPattern.WellFormed`). -/
def IsWellFormedStackPatternSet {Γ Λ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (ps : StackPatternSet Γ Λ) : Prop :=
  (!ps.isEmpty && ps.all (fun entry => entry.1.WellFormed)) = true

/-- Membership of configuration `cfg` in a `StackPatternSet`. -/
def IsInStackPatternSet {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (ps : StackPatternSet Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  ∃ entry : StackPattern Γ Λ × VarCond, entry ∈ ps ∧
    ∃ (vars : ℕ → ℕ) (stks : ℕ → List ℕ),
      cfg = evalStackPattern entry.1 vars stks ∧ evalVarCond entry.2 vars

/-- `ps` is a closed accelerated `StackPatternSet` for `M` if `ps` is well-formed
(`IsWellFormedStackPatternSet`), `M`'s blank-tape trajectory enters `ps`, and every member
configuration of `ps` steps in `ReachesPlus` (`n > 0` steps) either to another member of `ps` or
to a halting configuration.

In `BusyBeaverChallenge.lean`, `IsClosedStackPatternSet` pins an explicit `ps` and is always paired
with a concrete Level B finite-state transducer acceleration (`IsValidAcceleration`). -/
def IsClosedStackPatternSet [DecidableEq Γ] (M : Machine Γ Λ) (ps : StackPatternSet Γ Λ) : Prop :=
  IsWellFormedStackPatternSet ps ∧
  (∃ cfg₀, ReachesStar M (init []) cfg₀ ∧ IsInStackPatternSet ps cfg₀) ∧
  (∀ cfg, IsInStackPatternSet ps cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧
      (IsInStackPatternSet ps cfg' ∨ (step M cfg').isNone))

/-- `M`'s blank-tape trajectory enters a well-formed closed accelerated `StackPatternSet` in which
every member configuration steps in `ReachesPlus` either to another member or to a halting state.
This existential summary is always paired in `BusyBeaverChallenge.lean` with a concrete `ps`
(`IsClosedStackPatternSet M ps`) and an explicit Level B finite-state transducer acceleration
(`IsValidAcceleration M start encode next`). -/
def HasStackedCollatzReduction [DecidableEq Γ] (M : Machine Γ Λ) : Prop :=
  ∃ ps : StackPatternSet Γ Λ, IsClosedStackPatternSet M ps

/-- Allowed half-tape views in a separator mode: either a fixed prefix in front of the encoded
stack, or a fixed prefix in front of its `.tail`. -/
inductive HalfTapeView (Γ : Type*) where
  /-- Fixed prefix `pfx` directly in front of the encoded stack. -/
  | id (pfx : List Γ)
  /-- Fixed prefix `pfx` in front of the `.tail` of the encoded stack. -/
  | tail (pfx : List Γ)

/-- Apply a `HalfTapeView Γ` to an encoded half-tape `ListBlank Γ`. -/
def applyView {Γ : Type*} [Inhabited Γ] : HalfTapeView Γ → ListBlank Γ → ListBlank Γ
  | .id pfx, s => ListBlank.append pfx s
  | .tail pfx, s => ListBlank.append pfx s.tail

/-- Right-nested `n`-tuple of natural numbers indexed by the machine's symbol count `n`
(`ℕ × ℕ` for 2-symbol machines, `ℕ × ℕ × ℕ` for 3-symbol machines, etc.). -/
@[reducible] def StackTuple (n : ℕ) : Type :=
  Nat.casesOn n Unit (fun m => Nat.rec ℕ (fun _ ih => ℕ × ih) m)

/-- Primary coordinate of a `StackTuple n`. -/
@[reducible, simp] def stackDigit {n : ℕ} : StackTuple n → ℕ :=
  Nat.casesOn (motive := fun n => StackTuple n → ℕ) n
    (fun _ => 0)
    (fun m => Nat.casesOn (motive := fun m => StackTuple (m + 1) → ℕ) m
      (fun a => a)
      (fun _ p => p.1))

/-- Separator run length for the `(n + 1)`-symbol tail of a `StackTuple (n + 2)`. -/
@[reducible, simp] def stackSepLen {n : ℕ} (sep maxSep : ℕ) : StackTuple n → ℕ :=
  Nat.casesOn (motive := fun n => StackTuple n → ℕ) n
    (fun _ => 0)
    (fun m => Nat.casesOn (motive := fun m => StackTuple (m + 1) → ℕ) m
      (fun b => sep + b % maxSep)
      (fun k p => (sep + p.1 % maxSep) * stackDigit (n := k + 1) p.2))

/-- Valid `(dSym, sSym)` symbol polarity for a `(k + 2)`-symbol machine: for 2-symbol machines
(`k = 0`), `(dSym, sSym) ∈ {(1, 0), (0, 1)}`; for `(k + 3)`-symbol machines (`k ≥ 1`), any
distinct `dSym ≠ sSym`. -/
@[reducible] def IsValidStackPolarity : {k : ℕ} → Fin (k + 2) → Fin (k + 2) → Prop
  | 0, dSym, sSym =>
    (dSym = (1 : Fin 2) ∧ sSym = (0 : Fin 2)) ∨ (dSym = (0 : Fin 2) ∧ sSym = (1 : Fin 2))
  | _ + 1, dSym, sSym => dSym ≠ sSym

/-- Every `StackMode` evaluates `(L, R)` as a fixed control state `q` and fixed bounded
`HalfTapeView`s `vL, vR` (`≤ 8`-symbol prefixes) of `encLeft L` and `encRight R` (either scanning
`0` between them or stepping onto the left or right view). -/
def IsValidStackModes {Γ Λ StackMode α : Type*} [Inhabited Γ] [OfNat Γ 0]
    (encLeft encRight : List α → ListBlank Γ)
    (eval : StackMode → List α → List α → Cfg Γ Λ) : Prop :=
  ∀ m : StackMode, ∃ (q : Λ) (vL vR : HalfTapeView Γ),
    (HalfTapeView.casesOn vL List.length List.length) ≤ 8 ∧
    (HalfTapeView.casesOn vR List.length List.length) ≤ 8 ∧
    ((∀ L R, eval m L R =
      ⟨some q, ⟨(0 : Γ), applyView vL (encLeft L), applyView vR (encRight R)⟩⟩) ∨
    (∀ L R, eval m L R = Cfg.headLeft q (applyView vL (encLeft L)) (applyView vR (encRight R))) ∨
    (∀ L R, eval m L R = Cfg.headRight q (applyView vL (encLeft L)) (applyView vR (encRight R))))

/-- The blank-tape trajectory of `M` enters a closed 2nd-order digit-stack configuration family
over `(k + 2)`-symbol tuple stacks `List (StackTuple (k + 2))` with valid symbol polarity,
parametric unary-block stack recurrences (`strideL, offsetL, sepL, strideR, offsetR, sepR > 0`,
`1 ≤ maxSepL, maxSepR ≤ 4`), head-`dSym` non-surjectivity, at most 6 bounded-prefix modes
(`IsValidStackModes`), blank-tape multi-digit stack reachability (`3 ≤ L_g.length + R_g.length`
with a positive digit), an arbitrary-depth stack-frame transfer transition, and closure under
`ReachesPlus` up to halting. -/
def HasStackReduction {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (StackMode : Type)
    (dSym sSym : Fin (k + 2))
    (encLeft encRight : List (StackTuple (k + 2)) → ListBlank (Fin (k + 2)))
    (evalStackCfg :
      StackMode → List (StackTuple (k + 2)) → List (StackTuple (k + 2)) → Cfg (Fin (k + 2)) Λ)
    (IsInStackSystem : Cfg (Fin (k + 2)) Λ → Prop),
    IsValidStackPolarity dSym sSym ∧
    encLeft [] = default ∧
    encRight [] = default ∧
    (∀ a b L, (encLeft ((a, b) :: L)).head = dSym) ∧
    (∀ d b R, (encRight ((d, b) :: R)).head = dSym) ∧
    (∃ t : ListBlank (Fin (k + 2)),
      t.head = dSym ∧ ∀ L : List (StackTuple (k + 2)), encLeft L ≠ t) ∧
    (∃ t : ListBlank (Fin (k + 2)),
      t.head = dSym ∧ ∀ R : List (StackTuple (k + 2)), encRight R ≠ t) ∧
    (∃ strideL offsetL sepL maxSepL strideR offsetR sepR maxSepR : ℕ,
      strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧ 1 ≤ maxSepL ∧ maxSepL ≤ 4 ∧
      strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧ 1 ≤ maxSepR ∧ maxSepR ≤ 4 ∧
      (∀ a b L, encLeft ((a, b) :: L) =
        ListBlank.append (([dSym] : List (Fin (k + 2))) ^ (strideL * a + offsetL))
          (ListBlank.append
            (([sSym] : List (Fin (k + 2))) ^ (stackSepLen (n := k + 1) sepL maxSepL b))
            (encLeft L))) ∧
      (∀ d b R, encRight ((d, b) :: R) =
        ListBlank.append (([dSym] : List (Fin (k + 2))) ^ (strideR * d + offsetR))
          (ListBlank.append
            (([sSym] : List (Fin (k + 2))) ^ (stackSepLen (n := k + 1) sepR maxSepR b))
            (encRight R)))) ∧
    (∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes) ∧
    IsValidStackModes encLeft encRight evalStackCfg ∧
    (∀ cfg, IsInStackSystem cfg ↔ ∃ m L R, cfg = evalStackCfg m L R) ∧
    (∀ m L R, IsInStackSystem (evalStackCfg m L R)) ∧
    (∃ (m_g : StackMode) (L_g R_g : List (StackTuple (k + 2))),
      ReachesPlus M (init []) (evalStackCfg m_g L_g R_g) ∧
      3 ≤ L_g.length + R_g.length ∧
      (∃ x ∈ L_g ++ R_g, 1 ≤ x.1)) ∧
    ((∃ (m m' : StackMode) (x : StackTuple (k + 2))
        (g : StackTuple (k + 2) → StackTuple (k + 2))
        (f : List (StackTuple (k + 2)) → List (StackTuple (k + 2))),
        (∀ s, s.length ≤ (f s).length) ∧
        ∀ z L R,
          ReachesPlus M (evalStackCfg m (x :: z :: L) R) (evalStackCfg m' (g z :: L) (f R))) ∨
      (∃ (m m' : StackMode) (x : StackTuple (k + 2))
        (g : StackTuple (k + 2) → StackTuple (k + 2))
        (f : List (StackTuple (k + 2)) → List (StackTuple (k + 2))),
        (∀ s, s.length ≤ (f s).length) ∧
        ∀ z L R,
          ReachesPlus M (evalStackCfg m L (x :: z :: R)) (evalStackCfg m' (f L) (g z :: R)))) ∧
    (∀ cfg, IsInStackSystem cfg →
      ∃ cfg', ReachesPlus M cfg cfg' ∧ (IsInStackSystem cfg' ∨ (step M cfg').isNone))

/-- Tape orientation for a mixed-radix odometer-word system (`HasOdometerReduction`). -/
inductive OdomSide where
  /-- Odometer stack on the left half-tape and active word on the right half-tape. -/
  | leftOdom
  /-- Odometer stack on the right half-tape and active word on the left half-tape. -/
  | rightOdom

/-- Evaluate the outward-facing hub configuration (head at `q_R` facing the active word `w` across
fixed boundary prefix `pfx_R`). -/
@[reducible, simp]
def evalOdomR {Γ Λ : Type*} [Inhabited Γ]
    (side : OdomSide) (q_R : Λ) (pfx_R : List Γ)
    (encOdom : ListBlank Γ) (w : ListBlank Γ) : Cfg Γ Λ :=
  match side with
  | .leftOdom => Cfg.headRight q_R (ListBlank.append pfx_R encOdom) w
  | .rightOdom => Cfg.headLeft q_R w (ListBlank.append pfx_R encOdom)

/-- Evaluate the inward-facing odometer entry configuration (head at `q_L` facing the odometer
stack `encOdom` across fixed boundary prefix `pfx_L`). -/
@[reducible, simp]
def evalOdomL {Γ Λ : Type*} [Inhabited Γ]
    (side : OdomSide) (q_L : Λ) (pfx_L : List Γ)
    (encOdom : ListBlank Γ) (w : ListBlank Γ) : Cfg Γ Λ :=
  match side with
  | .leftOdom => Cfg.headLeft q_L encOdom (ListBlank.append pfx_L w)
  | .rightOdom => Cfg.headRight q_L (ListBlank.append pfx_L w) encOdom

/-- The blank-tape trajectory of `M` enters a closed outward-facing odometer-word hub coupled with
a non-surjective multi-bit mixed-radix odometer stack (`OdomTok`, `cap`, `dec`, `drain`) supporting
odd-doubling (`2c + 1`), even-doubling (`2c`), and base-`b` division (`c / b`, `b ≥ 2`) frames,
universal capacity decrement (`cap stk ≥ 1`) and full-stack drain (`cap stk = 0`), active `0`-bit
reflection, and push/reflect/halt closure under `ReachesPlus`. -/
def HasOdometerReduction {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (OdomTok : Type)
    (side : OdomSide)
    (q_R : List OdomTok → Λ)
    (q_L : Λ)
    (pfx_R pfx_L odomBase : List (Fin (k + 2)))
    (odomWord : OdomTok → List (Fin (k + 2)))
    (encOdom : List OdomTok → ListBlank (Fin (k + 2)))
    (cap : List OdomTok → ℕ)
    (dec : List OdomTok → List OdomTok)
    (decPfx : List OdomTok → List (Fin (k + 2)))
    (drain : List OdomTok → List (Fin (k + 2)))
    (IsInOdomSystem : Cfg (Fin (k + 2)) Λ → Prop),
    (∃ toks : List OdomTok, 2 ≤ toks.length ∧ toks.length ≤ 6 ∧ ∀ t : OdomTok, t ∈ toks) ∧
    odomBase ≠ [] ∧
    (∀ t : OdomTok, 2 ≤ (odomWord t).length) ∧
    encOdom [] = ListBlank.append odomBase default ∧
    (∀ t stk, encOdom (t :: stk) = ListBlank.append (odomWord t) (encOdom stk)) ∧
    (∃ t : ListBlank (Fin (k + 2)), ∀ stk : List OdomTok, encOdom stk ≠ t) ∧
    cap [] = 0 ∧
    (∃ (t_inc t_even t_div : OdomTok) (b : ℕ) (blk_inc blk_div : List (Fin (k + 2))),
      2 ≤ b ∧ 2 ≤ blk_inc.length ∧ 2 ≤ blk_div.length ∧
      (∀ stk, cap (t_inc :: stk) = 2 * cap stk + 1) ∧
      (∀ stk, cap (t_even :: stk) = 2 * cap stk) ∧
      (∀ stk, cap (t_div :: stk) = cap stk / b) ∧
      (∀ stk w,
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) (ListBlank.append blk_inc w))
          (evalOdomR side (q_R (t_inc :: stk)) pfx_R (encOdom (t_inc :: stk)) w)) ∧
      (∀ stk w,
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) (ListBlank.append blk_div w))
          (evalOdomR side (q_R (t_div :: stk)) pfx_R (encOdom (t_div :: stk)) w))) ∧
    (∀ stk, (dec stk).length = stk.length) ∧
    (∀ stk, cap stk ≥ 1 → cap (dec stk) = cap stk - 1) ∧
    (∀ stk w, cap stk ≥ 1 →
      ReachesPlus M
        (evalOdomL side q_L pfx_L (encOdom stk) w)
        (evalOdomR side (q_R (dec stk)) pfx_R (encOdom (dec stk))
          (ListBlank.append (decPfx stk) w))) ∧
    (∀ stk, cap stk = 0 → drain stk ≠ []) ∧
    (∀ stk w, cap stk = 0 →
      ReachesPlus M
        (evalOdomL side q_L pfx_L (encOdom stk) w)
        (evalOdomR side (q_R []) pfx_R (encOdom []) (ListBlank.append (drain stk) w))) ∧
    (∀ stk w,
      ReachesPlus M
        (evalOdomR side (q_R stk) pfx_R (encOdom stk) (ListBlank.cons (0 : Fin (k + 2)) w))
        (evalOdomL side q_L pfx_L (encOdom stk) (ListBlank.cons (1 : Fin (k + 2)) w))) ∧
    (∀ stk w,
      (∃ t w',
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) w)
          (evalOdomR side (q_R (t :: stk)) pfx_R (encOdom (t :: stk)) w')) ∨
      (∃ w',
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) w)
          (evalOdomL side q_L pfx_L (encOdom stk) w')) ∨
      (∃ cfg',
        ReachesPlus M (evalOdomR side (q_R stk) pfx_R (encOdom stk) w) cfg' ∧
          (step M cfg').isNone)) ∧
    (∀ cfg, IsInOdomSystem cfg ↔
      ∃ stk w, cfg = evalOdomR side (q_R stk) pfx_R (encOdom stk) w) ∧
    (∃ (stk₀ : List OdomTok) (w₀ : ListBlank (Fin (k + 2))),
      ReachesPlus M (init []) (evalOdomR side (q_R stk₀) pfx_R (encOdom stk₀) w₀) ∧
      2 ≤ stk₀.length ∧ 1 ≤ cap stk₀) ∧
    (∀ stk w,
      ∃ cfg', ReachesPlus M (evalOdomR side (q_R stk) pfx_R (encOdom stk) w) cfg' ∧
        (IsInOdomSystem cfg' ∨ (step M cfg').isNone))

/-- Every `TransducerMode` evaluates `(L, R)` as a fixed control state `q` and fixed bounded
`HalfTapeView`s `vL, vR` (`≤ 8`-symbol prefixes) of `encLeft L` and `encRight R` (either scanning
`0` between them or stepping onto the left or right view). -/
def IsValidTransducerModes {Γ Λ TransducerMode TokL TokR : Type*} [Inhabited Γ] [OfNat Γ 0]
    (encLeft : List TokL → ListBlank Γ)
    (encRight : List TokR → ListBlank Γ)
    (eval : TransducerMode → List TokL → List TokR → Cfg Γ Λ) : Prop :=
  ∀ m : TransducerMode, ∃ (q : Λ) (vL vR : HalfTapeView Γ),
    (match vL with | .id p => p.length ≤ 8 | .tail p => p.length ≤ 8) ∧
    (match vR with | .id p => p.length ≤ 8 | .tail p => p.length ≤ 8) ∧
    ((∀ L R, eval m L R =
      ⟨some q, ⟨(0 : Γ), applyView vL (encLeft L), applyView vR (encRight R)⟩⟩) ∨
    (∀ L R, eval m L R = Cfg.headLeft q (applyView vL (encLeft L)) (applyView vR (encRight R))) ∨
    (∀ L R, eval m L R = Cfg.headRight q (applyView vL (encLeft L)) (applyView vR (encRight R))))

/-- Scaled integer Kraft-McMillan weight `∑_{t ∈ toks} base ^ (maxLen - (word t).length)`. -/
@[reducible, simp]
def kraftSum {Tok Γ : Type*} (base maxLen : ℕ) (word : Tok → List Γ) : List Tok → ℕ
  | [] => 0
  | t :: ts => base ^ (maxLen - (word t).length) + kraftSum base maxLen word ts

/-- Iterate a partial macro-transducer step `stepMacro` for `n` macro-steps. -/
@[reducible, simp]
def iterTransducerMacro {Mode TokL TokR : Type*}
    (stepMacro : Mode → List TokL → List TokR → Option (Mode × List TokL × List TokR)) :
    ℕ → (Mode × List TokL × List TokR) → Option (Mode × List TokL × List TokR)
  | 0, s => some s
  | n + 1, (m, L, R) =>
      match stepMacro m L R with
      | none => none
      | some s' => iterTransducerMacro stepMacro n s'

/-- The blank-tape trajectory of `M` is governed by a closed, full-tape, strict-sub-Kraft
finite-alphabet word-stack transducer (`TransducerMode`, `TokL`, `TokR`, `stepMacro`) with bounded
blank-tape entry, `512..2048`-step stack expansion, full constructor orbit reachability, a single
boundary-closed halting exit gate, and orbit-exercised bidirectional multi-bit block-transduction
sweeps. -/
def HasTransducerReduction {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (TransducerMode TokL TokR : Type)
    (baseL baseR : List (Fin (k + 2)))
    (wordL : TokL → List (Fin (k + 2)))
    (wordR : TokR → List (Fin (k + 2)))
    (encLeft : List TokL → ListBlank (Fin (k + 2)))
    (encRight : List TokR → ListBlank (Fin (k + 2)))
    (evalTransducerCfg : TransducerMode → List TokL → List TokR → Cfg (Fin (k + 2)) Λ)
    (stepMacro : TransducerMode → List TokL → List TokR →
      Option (TransducerMode × List TokL × List TokR))
    (IsInTransducerSystem : Cfg (Fin (k + 2)) Λ → Prop),
    (∃ modes : List TransducerMode,
      2 ≤ modes.length ∧ modes.length ≤ 8 ∧ ∀ m : TransducerMode, m ∈ modes) ∧
    (∃ (toksL : List TokL) (maxLenL : ℕ),
      toksL.Nodup ∧ (toksL.map wordL).Nodup ∧ maxLenL ≤ 8 ∧
      2 ≤ toksL.length ∧ toksL.length ≤ 8 ∧ (∀ t : TokL, t ∈ toksL) ∧
      (∀ t : TokL, 1 ≤ (wordL t).length ∧ (wordL t).length ≤ maxLenL) ∧
      kraftSum (k + 2) maxLenL wordL toksL < (k + 2) ^ maxLenL) ∧
    (∃ (toksR : List TokR) (maxLenR : ℕ),
      toksR.Nodup ∧ (toksR.map wordR).Nodup ∧ maxLenR ≤ 8 ∧
      2 ≤ toksR.length ∧ toksR.length ≤ 8 ∧ (∀ t : TokR, t ∈ toksR) ∧
      (∀ t : TokR, 1 ≤ (wordR t).length ∧ (wordR t).length ≤ maxLenR) ∧
      kraftSum (k + 2) maxLenR wordR toksR < (k + 2) ^ maxLenR) ∧
    baseL.length ≤ 8 ∧ baseR.length ≤ 8 ∧
    ((∀ t : TokL, 2 ≤ (wordL t).length) ∨ (∀ t : TokR, 2 ≤ (wordR t).length)) ∧
    (∃ t : TokL, (0 : Fin (k + 2)) ∈ wordL t ∧ ∃ a, a ∈ wordL t ∧ a ≠ 0) ∧
    (∃ t : TokR, (0 : Fin (k + 2)) ∈ wordR t ∧ ∃ a, a ∈ wordR t ∧ a ≠ 0) ∧
    encLeft [] = ListBlank.append baseL default ∧
    (∀ t L, encLeft (t :: L) = ListBlank.append (wordL t) (encLeft L)) ∧
    encRight [] = ListBlank.append baseR default ∧
    (∀ t R, encRight (t :: R) = ListBlank.append (wordR t) (encRight R)) ∧
    (∃ t : ListBlank (Fin (k + 2)), ∀ L : List TokL, encLeft L ≠ t) ∧
    (∃ t : ListBlank (Fin (k + 2)), ∀ R : List TokR, encRight R ≠ t) ∧
    IsValidTransducerModes encLeft encRight evalTransducerCfg ∧
    (∀ cfg, IsInTransducerSystem cfg ↔ ∃ m L R, cfg = evalTransducerCfg m L R) ∧
    (∀ m L R m' L' R',
      stepMacro m L R = some (m', L', R') →
        ReachesPlus M (evalTransducerCfg m L R) (evalTransducerCfg m' L' R')) ∧
    ∃ (m₀ : TransducerMode) (L₀ : List TokL) (R₀ : List TokR),
      L₀.length + R₀.length ≤ 4 ∧
      ReachesPlus M (init []) (evalTransducerCfg m₀ L₀ R₀) ∧
      (∃ (n_grow : ℕ) (m_g : TransducerMode) (L_g : List TokL) (R_g : List TokR),
        512 ≤ n_grow ∧ n_grow ≤ 2048 ∧
        iterTransducerMacro stepMacro n_grow (m₀, L₀, R₀) = some (m_g, L_g, R_g) ∧
        20 ≤ L_g.length + R_g.length) ∧
      (∀ m : TransducerMode, ∃ (n_m : ℕ) (L_m : List TokL) (R_m : List TokR),
        n_m ≤ 256 ∧
        iterTransducerMacro stepMacro n_m (m₀, L₀, R₀) = some (m, L_m, R_m)) ∧
      (∀ t : TokL, ∃ (n_t : ℕ) (m_t : TransducerMode) (L_t : List TokL) (R_t : List TokR),
        n_t ≤ 256 ∧
        iterTransducerMacro stepMacro n_t (m₀, L₀, R₀) = some (m_t, L_t, R_t) ∧
        t ∈ L_t) ∧
      (∀ t : TokR, ∃ (n_t : ℕ) (m_t : TransducerMode) (L_t : List TokL) (R_t : List TokR),
        n_t ≤ 256 ∧
        iterTransducerMacro stepMacro n_t (m₀, L₀, R₀) = some (m_t, L_t, R_t) ∧
        t ∈ R_t) ∧
      ((∃ (m_exit : TransducerMode) (tL_exit : TokL) (exitNext : List TokL),
          exitNext.Nodup ∧ exitNext ≠ [] ∧
          (∀ R : List TokR, (stepMacro m_exit [tL_exit] R).isSome) ∧
          (∀ m L R,
            stepMacro m L R = none ↔
              (m = m_exit ∧ ∃ t₂ L'', t₂ ∈ exitNext ∧ L = tL_exit :: t₂ :: L'')) ∧
          (∀ t₂ ∈ exitNext, ∀ R : List TokR, ∃ cfg_h,
            ReachesPlus M (evalTransducerCfg m_exit [tL_exit, t₂] R) cfg_h ∧
              (step M cfg_h).isNone) ∧
          (∀ t₂ ∈ exitNext, ∃ sfx : List TokL, sfx.length ≤ 2 ∧
            ∀ (L'' : List TokL) (R : List TokR), ∃ cfg_h,
              ReachesPlus M (evalTransducerCfg m_exit (tL_exit :: t₂ :: (sfx ++ L'')) R) cfg_h ∧
                (step M cfg_h).isNone)) ∨
        (∃ (m_exit : TransducerMode) (tR_exit : TokR) (exitNext : List TokR),
          exitNext.Nodup ∧ exitNext ≠ [] ∧
          (∀ L : List TokL, (stepMacro m_exit L [tR_exit]).isSome) ∧
          (∀ m L R,
            stepMacro m L R = none ↔
              (m = m_exit ∧ ∃ t₂ R'', t₂ ∈ exitNext ∧ R = tR_exit :: t₂ :: R'')) ∧
          (∀ t₂ ∈ exitNext, ∀ L : List TokL, ∃ cfg_h,
            ReachesPlus M (evalTransducerCfg m_exit L [tR_exit, t₂]) cfg_h ∧
              (step M cfg_h).isNone) ∧
          (∀ t₂ ∈ exitNext, ∃ sfx : List TokR, sfx.length ≤ 2 ∧
            ∀ (L : List TokL) (R'' : List TokR), ∃ cfg_h,
              ReachesPlus M (evalTransducerCfg m_exit L (tR_exit :: t₂ :: (sfx ++ R''))) cfg_h ∧
                (step M cfg_h).isNone))) ∧
      (∃ (m_lr m_rl : TransducerMode) (tL tL' : TokL) (tR tR' : TokR) (s₁ s₂ s₃ s₄ : ℕ),
        1 ≤ s₁ ∧ s₁ ≤ 4 ∧ 1 ≤ s₂ ∧ s₂ ≤ 4 ∧
        1 ≤ s₃ ∧ s₃ ≤ 4 ∧ 1 ≤ s₄ ∧ s₄ ≤ 4 ∧
        2 ≤ (wordL tL).length ∧ 2 ≤ (wordR tR).length ∧
        2 ≤ (wordL tL').length ∧ 2 ≤ (wordR tR').length ∧
        (((wordL tL) ^ s₁).reverse ≠ (wordR tR) ^ s₂ ∨
          ((wordR tR') ^ s₃).reverse ≠ (wordL tL') ^ s₄) ∧
        (wordL tL ≠ wordL tL' ∨ wordR tR ≠ wordR tR' ∨ s₁ ≠ s₂ ∨ s₃ ≠ s₄) ∧
        (∃ (n_lr : ℕ) (L_lr : List TokL) (R_lr : List TokR),
          n_lr ≤ 256 ∧
          iterTransducerMacro stepMacro n_lr (m₀, L₀, R₀) = some (m_lr, L_lr, R_lr) ∧
          L_lr.take (2 * s₁) = List.replicate (2 * s₁) tL) ∧
        (∃ (n_rl : ℕ) (L_rl : List TokL) (R_rl : List TokR),
          n_rl ≤ 256 ∧
          iterTransducerMacro stepMacro n_rl (m₀, L₀, R₀) = some (m_rl, L_rl, R_rl) ∧
          R_rl.take (2 * s₃) = List.replicate (2 * s₃) tR') ∧
        (∀ (n : ℕ) (L : List TokL) (R : List TokR),
          ReachesPlus M
            (evalTransducerCfg m_lr (List.replicate (s₁ * (n + 1)) tL ++ L) R)
            (evalTransducerCfg m_lr L (List.replicate (s₂ * (n + 1)) tR ++ R))) ∧
        (∀ (n : ℕ) (L : List TokL) (R : List TokR),
          ReachesPlus M
            (evalTransducerCfg m_rl L (List.replicate (s₃ * (n + 1)) tR' ++ R))
            (evalTransducerCfg m_rl (List.replicate (s₄ * (n + 1)) tL' ++ L) R)))

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

namespace ThreeState

/-- State `A` (`0 : Fin 3`), the initial state. -/
abbrev A : Fin 3 := 0
/-- State `B` (`1 : Fin 3`). -/
abbrev B : Fin 3 := 1
/-- State `C` (`2 : Fin 3`). -/
abbrev C : Fin 3 := 2

end ThreeState

/-- Canonical `NeZero 2` instance for `(states, 2)` Turing machines. -/
instance (priority := high) instNeZeroTwo : @NeZero ℕ Zero.ofOfNat0 2 := Nat.instNeZeroSucc

/-- Canonical `NeZero 3` instance for `(3, 3)` Turing machines. -/
instance (priority := high) instNeZeroThree : @NeZero ℕ Zero.ofOfNat0 3 := Nat.instNeZeroSucc

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

inductive HighLevelState where
  | S (b c : ℕ)
  | T (m : ℕ)
  | Tn (j : ℕ)
  | Eb (k t : ℕ)
  | Ed (k t : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .T 1

def toState : HighLevelState → State
  | .S b c => .S0p 0 b c
  | .T m => .T1 0 m
  | .Tn j => .Tn j
  | .Eb k t => .Eb k t
  | .Ed k t => .Ed k t

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .S b c =>
    let a := 2 * (b / 3)
    if b % 3 = 0 then some (.S (2 * a + 1) (c + 4))
    else if b % 3 = 1 then some (.S (2 * a + 5) (c + 6))
    else if c = 0 then some (.T (2 * a + 7))
    else some (.S (2 * a + 8) (c - 1))
  | .T m =>
    let j0 := 2 * (m / 3)
    if m % 3 = 0 then some (.Tn 0)
    else if m % 3 = 2 then some (.S (2 * j0 + 5) 3)
    else
      let m1 := 2 * j0 + 7
      let j1 := 2 * (m1 / 3)
      if m1 % 3 = 0 then some (.T (2 * j1 + 6))
      else if m1 % 3 = 2 then some (.Eb 0 (2 * j1 + 1))
      else
        let m2 := 2 * j1 + 7
        let j2 := 2 * (m2 / 3)
        if m2 % 3 = 0 then some (.T (2 * j2 + 8))
        else if m2 % 3 = 2 then some (.Ed 0 (2 * j2 + 1))
        else
          let m3 := 2 * j2 + 7
          let j3 := 2 * (m3 / 3)
          if m3 % 3 ≠ 0 then none
          else
            let m4 := 2 * j3 + 6
            let j4 := 2 * (m4 / 3)
            if m4 % 3 = 1 then none
            else if m4 % 3 = 0 then some (.T (2 * j4 + 5))
            else some (.T (2 * j4 + 7))
  | .Tn j => some (.Tn (j + 2))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ed k t => some (.Ed (k + 1) t)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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
inductive HighLevelState where
  | E (p : Bool) (k c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .E false 0 2

def toState : HighLevelState → State
  | .E p k c => .E (if p then 4 else 3) k c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .E p k c =>
    if c % 2 = 1 then
      if k % 2 = 0 then some (.E (!p) (3 * (k / 2) + 2) c)
      else if c = 1 then none
      else if c = 3 then some (.E false 0 (6 * (k / 2) + (if p then 11 else 10)))
      else some (.E p (3 * (k / 2) + (if p then 6 else 5)) (c - 5))
    else if c = 2 * k then
      some (.E false 0 (6 * k + (if p then 6 else 5)))
    else if 2 * k = c + 2 then
      some (.E false 0 (6 * k + (if p then 3 else 2)))
    else if 2 * k ≥ c + 4 then
      some (.E (!p) (3 * (c / 2) + 3) (2 * k - c - 3))
    else if k = 0 then
      some (.E (!p) 3 (c - 2))
    else
      some (.E p (3 * k + (if p then 2 else 1)) (c - 2 * k - 1))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | C0 (g d : ℕ)
  | C2 (g d : ℕ)
  | C5 (g d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C2 0 0

def toState : HighLevelState → State
  | .C0 g d => .C 0 0 g d
  | .C2 g d => .C 2 0 g d
  | .C5 g d => .C 5 0 g d

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def scanG (r : Bool) (f g d : ℕ) : Option HighLevelState :=
  if g = 0 then
    if !r then
      if f % 2 = 0 then some (.C2 (f / 2 + 2) d)
      else some (.C5 (f / 2 + 1) d)
    else
      if f % 2 = 0 then some (.C0 (f / 2 + 3) d)
      else none
  else if g = 1 then
    if !r then
      if f = 0 then some (.C2 0 (d + 2))
      else if f % 2 = 0 then some (.C5 (f / 2 - 1) (d + 1))
      else some (.C2 (f / 2 + 1) (d + 1))
    else
      if f % 2 = 0 then none
      else some (.C0 (f / 2 + 2) (d + 1))
  else
    let s := f + 3 + if r then 1 else 0
    scanG (decide (s % 2 = 1)) (3 * (s / 2) + 3) (g - 2) d
termination_by g
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .C0 g d => scanG false 0 g d
  | .C2 g d => scanG false 3 g d
  | .C5 g d => scanG true 6 g d

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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

/-! ### Level B: accelerated state machine -/

def Config_gen (a g h : Nat) : Cfg (Fin 2) (Fin 6) :=
  let left := ListBlank.append (([1] : List (Fin 2)) ^ g)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ a) default)
  let right := ListBlank.append (([1] : List (Fin 2)) ^ h) default
  ⟨some A, ⟨right.head, left, right.tail⟩⟩

def S (k : Nat) : Nat :=
  2^(k+1) - k - 1

def find_k_fuel (a : Nat) (fuel : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun k => k)
    (fun _ ih k => if a < S (k+1) then k else ih (k+1))
    fuel k

def find_k (a : Nat) : Nat :=
  find_k_fuel a a 0

def a_new (a g : Nat) : Nat :=
  let j := find_k a
  let k_g := (g - 1) / 2
  if a = S j then
    2^(j+1) + k_g
  else
    S (j+1) - 1 - a

inductive State where
  | H0 (a g : ℕ)
  | H3 (a g h : ℕ)
  | H2_even (a k : ℕ)
  | H2_odd0 (k : ℕ)
  | H1_even (a k : ℕ)

def start : State := .H2_odd0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .H0 a g => Config_gen a (g + 1) 0
  | .H3 a g h => Config_gen a (g + 1) (h + 3)
  | .H2_even a k => Config_gen a (2 * (k + 1)) 2
  | .H2_odd0 k => Config_gen 0 (2 * k + 1) 2
  | .H1_even a k => Config_gen a (2 * (k + 1)) 1

def classifyEven (a k h : ℕ) : State :=
  Nat.casesOn h (.H1_even a k) fun h =>
  Nat.casesOn h (.H2_even a k) fun h' =>
  .H3 a (2 * k + 1) h'

def next : State → Option State
  | .H0 0 g => some (.H3 0 0 g)
  | .H0 (a + 1) g => some (.H3 a 0 (g + 1))
  | .H3 a g h =>
    if (g + 1) % 2 = 0 then
      let k := (g + 1) / 2
      Nat.casesOn a (some (classifyEven (k + 1) 0 h)) fun a' =>
      some (classifyEven a' (k + 1) h)
    else
      let k := (g + 1) / 2
      Nat.casesOn a (some (classifyEven 0 (k + 1) h)) fun a =>
      Nat.casesOn a (some (classifyEven (k + 2) 0 h)) fun a'' =>
        let a_org := a'' + 2
        let a_n := a_new a_org (2 * k + 1)
        let k_n := if a_org = S (find_k a_org) then 1
                   else (a_org + find_k a_org + 2 - a_n) + k
        some (classifyEven a_n (k_n - 1) h)
  | .H2_even 0 _ => none
  | .H2_even (a + 1) k => some (.H0 a (2 * k + 5))
  | .H2_odd0 k => some (.H0 0 (2 * k + 3))
  | .H1_even 0 0 => none
  | .H1_even (a + 1) 0 => some (.H0 a 3)
  | .H1_even a (k + 1) => some (.H2_even a k)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | H (a g : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .H 0 3

def toState : HighLevelState → State
  | .H a g => .H0 a g

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def drainEven (a k h : ℕ) : Option HighLevelState :=
  if h = 0 then
    if a = 0 then none else some (.H (a - 1) (2 * k + 3))
  else if h = 1 then
    if a = 0 then none else some (.H (a - 1) (2 * k + 5))
  else if a = 0 then
    drainEven (k + 2) 0 (h - 2)
  else
    drainEven (a - 1) (k + 2) (h - 2)
termination_by h
decreasing_by all_goals omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .H a g =>
    if a = 0 then
      drainEven 0 1 g
    else if a = 1 then
      drainEven 0 1 (g + 1)
    else if a = 2 then
      drainEven 2 0 (g + 1)
    else
      let a0 := a - 1
      let a_n := a_new a0 1
      let k_n := if a0 = S (find_k a0) then 1 else a0 + find_k a0 + 2 - a_n
      drainEven a_n (k_n - 1) (g + 1)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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

inductive HighLevelState where
  | S (b c : ℕ)
  | T (m : ℕ)
  | Tn (j : ℕ)
  | Eb (k t : ℕ)
  | Ed (k t : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .S 1 3

def toState : HighLevelState → State
  | .S b c => .S0p 0 b c
  | .T m => .T1 0 m
  | .Tn j => .Tn j
  | .Eb k t => .Eb k t
  | .Ed k t => .Ed k t

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .S b c =>
    let a := 2 * (b / 3)
    if b % 3 = 0 then some (.S (2 * a + 1) (c + 4))
    else if b % 3 = 1 then some (.S (2 * a + 5) (c + 6))
    else if c = 0 then some (.T (2 * a + 7))
    else some (.S (2 * a + 8) (c - 1))
  | .T m =>
    let j0 := 2 * (m / 3)
    if m % 3 = 0 then some (.Tn 0)
    else if m % 3 = 2 then some (.S (2 * j0 + 5) 3)
    else
      let m1 := 2 * j0 + 7
      let j1 := 2 * (m1 / 3)
      if m1 % 3 = 0 then some (.T (2 * j1 + 6))
      else if m1 % 3 = 2 then some (.Eb 0 (2 * j1 + 1))
      else
        let m2 := 2 * j1 + 7
        let j2 := 2 * (m2 / 3)
        if m2 % 3 = 0 then some (.T (2 * j2 + 8))
        else if m2 % 3 = 2 then some (.Ed 0 (2 * j2 + 1))
        else
          let m3 := 2 * j2 + 7
          let j3 := 2 * (m3 / 3)
          if m3 % 3 ≠ 0 then none
          else
            let m4 := 2 * j3 + 6
            let j4 := 2 * (m4 / 3)
            if m4 % 3 = 1 then none
            else if m4 % 3 = 0 then some (.T (2 * j4 + 5))
            else some (.T (2 * j4 + 7))
  | .Tn j => some (.Tn (j + 2))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ed k t => some (.Ed (k + 1) t)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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

/-! ### Level B: accelerated state machine -/

def D_cfg (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ b)
        (ListBlank.append (([0] : List (Fin 2)) ^ c)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))

def H_mid (a b m : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [0] (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))))
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)

def B_mid (a k b d : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B
    (ListBlank.append (([1] : List (Fin 2)) ^ k)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [0, 0] (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ b)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))

def A_rem (a k q m : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft A
    (ListBlank.append (([1] : List (Fin 2)) ^ k)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ q)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))

inductive State
  | D0 (a b d : ℕ)
  | D1 (a b d : ℕ)
  | H (a b m : ℕ)
  | B (a k b d : ℕ)
  | A_pos (a k q m : ℕ)
  | A_zero (a q m : ℕ)

def start : State := .D0 0 0 4

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D0 a b d => D_cfg a b 0 d
  | .D1 a b d => D_cfg a b 1 d
  | .H a b m => H_mid a (b + 1) (m + 1)
  | .B a k b d => B_mid a (k + 1) b d
  | .A_pos a k q m => A_rem a (k + 1) q m
  | .A_zero a q m => A_rem a 0 (q + 1) m

def next : State → Option State
  | .D1 0 0 d => some (.D1 0 0 (d + 1))
  | .D1 0 (b + 1) d => some (.D1 1 b (d + 2))
  | .D1 (a + 1) b d => some (.B a 0 b d)
  | .D0 a b 0 =>
    Nat.casesOn a
      (Nat.casesOn b (some (.D1 0 0 1)) fun b => some (.D1 1 b 2))
      fun a => some (.B a 0 b 0)
  | .D0 a b 1 =>
    Nat.casesOn b
      (Nat.casesOn a (some (.D0 0 0 4)) fun a => some (.B (a + 1) 0 0 0))
      fun b => some (.D1 (a + 2) b 3)
  | .D0 a b 2 =>
    Nat.casesOn a (some (.D1 1 b 2)) fun a => some (.B a 0 (b + 1) 0)
  | .D0 a b (d + 3) => some (.D0 (a + 2) b (d + 1))
  | .H a b 0 =>
    Nat.casesOn a none fun a =>
    some (.D1 (if a = 0 then 1 else a + 1) (b + 1) 5)
  | .H a b 1 => some (.D1 (a + 2) (b + 1) 2)
  | .H a b (m + 2) =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn m (some (.D1 2 (b + 2) 3)) fun m =>
       Nat.casesOn m (some (.D1 1 (b + 3) 2)) fun m =>
       some (.D0 2 (b + 3) (m + 1)))
      fun a => some (.H a (b + 2) m)
  | .B a k (b + 1) d => some (.B a (k + 1) b (d + 2))
  | .B a 0 0 d =>
    Nat.casesOn a (some (.D0 0 0 (d + 4))) fun a =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn d (some (.D1 1 2 2)) fun d => some (.D0 2 2 (d + 1)))
      fun a => some (.H a 1 (d + 1))
  | .B a (k + 1) 0 d => some (.A_pos a k 0 (d + 3))
  | .A_zero a q m => some (.D1 (a + 2) q m)
  | .A_pos a 0 q m =>
    Nat.casesOn a none fun a =>
    Nat.casesOn q
      (some (.D1 (if a = 0 then 1 else a + 1) 0 (m + 2)))
      fun q => some (.D1 (if a = 0 then 1 else a + 1) (q + 1) (m + 2))
  | .A_pos a 1 q m =>
    Nat.casesOn a (some (.D1 1 q m)) fun a =>
    some (.A_pos a q 0 (m + 2 * q + 3))
  | .A_pos a 2 q m => some (.A_zero a q m)
  | .A_pos a (k + 3) q m => some (.A_pos a k (q + 1) m)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
inductive HighLevelState where
  | D (a d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D 0 7

def toState : HighLevelState → State
  | .D a d => .D1 (a + 1) 0 d

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalA (a k m : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if k % 3 = 2 then some (a + 1, k / 3, m)
  else if a = 0 then (if k % 3 = 0 then none else some (0, k / 3, m))
  else if k % 3 = 0 then some (a - 1, k / 3, m + 2)
  else evalA (a - 1) (k / 3) (m + 2 * (k / 3) + 3)
termination_by a
decreasing_by omega

def drainB (a b d : ℕ) : Option HighLevelState :=
  if b = 0 then some (.D a d)
  else
    (evalA a (b - 1) (d + 2 * b + 3)).bind fun p =>
      if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none
termination_by b
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .D a d =>
    if a = 0 then
      if d % 2 = 1 then drainB (d + 1) 2 2 else some (.D d 7)
    else if d % 2 = 1 ∧ a ≥ d + 5 then drainB (a - d - 5) (d + 3) 5
    else if d % 2 = 0 ∧ a ≥ d + 3 then drainB (a - d - 2) (d + 2) 2
    else if a % 2 = 1 then none
    else if a = d + 2 then drainB 0 a 2
    else if d % 2 = 1 then drainB (d + 4 - a) (a - 1) 3
    else (evalA (d + 1 - a) a (2 * a + 5)).bind fun p => drainB p.1 p.2.1 p.2.2

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

/-! ### Level B: accelerated state machine -/

def D_cfg (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ b)
        (ListBlank.append (([0] : List (Fin 2)) ^ c)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))

def A_ones (a k b d : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft A
    (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ b)
      (ListBlank.append ([0] : List (Fin 2))
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))

def H_mid (a b m : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [0] (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))))
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)

def B_mid (a k b d : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B
    (ListBlank.append (([1] : List (Fin 2)) ^ k)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [0, 0] (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ b)
      (ListBlank.append ([0] : List (Fin 2))
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))

inductive State
  | D0 (a b d : ℕ)
  | D1 (a b d : ℕ)
  | H (a b m : ℕ)
  | B (a k b d : ℕ)
  | A (a k b d : ℕ)

def start : State := .D0 0 0 4

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D0 a b d => D_cfg a b 0 d
  | .D1 a b d => D_cfg a b 1 d
  | .H a b m => H_mid a (b + 1) (m + 1)
  | .B a k b d => B_mid a (k + 1) b d
  | .A a k b d => A_ones a k b d

def next : State → Option State
  | .D1 0 0 d => some (.D1 0 0 (d + 1))
  | .D1 0 (b + 1) d => some (.D1 1 b (d + 2))
  | .D1 (a + 1) b d => some (.B a 0 b d)
  | .D0 a b 0 =>
    Nat.casesOn a
      (Nat.casesOn b (some (.D1 0 0 1)) fun b => some (.D1 1 b 2))
      fun a => some (.B a 0 b 0)
  | .D0 a b 1 =>
    Nat.casesOn b
      (Nat.casesOn a (some (.D0 0 0 4)) fun a => some (.B (a + 1) 0 0 0))
      fun b => some (.D1 (a + 2) b 3)
  | .D0 a b 2 =>
    Nat.casesOn a (some (.D1 1 b 2)) fun a => some (.B a 0 (b + 1) 0)
  | .D0 a b (d + 3) => some (.D0 (a + 2) b (d + 1))
  | .H a b 0 =>
    Nat.casesOn a (some (.A 0 0 (b + 1) 3)) fun a =>
    some (.A (a + 1) 0 (b + 1) 3)
  | .H a b 1 => some (.D1 (a + 2) (b + 1) 2)
  | .H a b (m + 2) =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a
      (Nat.casesOn m (some (.D1 2 (b + 2) 3)) fun m =>
       Nat.casesOn m (some (.D1 1 (b + 3) 2)) fun m =>
       some (.D0 2 (b + 3) (m + 1)))
      fun a => some (.H a (b + 2) m)
  | .B a k (b + 1) d => some (.B a (k + 1) b (d + 2))
  | .B a 0 0 d =>
    Nat.casesOn a (some (.D0 0 0 (d + 4))) fun a =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a (some (.D0 0 2 (d + 2))) fun a =>
    some (.H a 1 (d + 1))
  | .B a (k + 1) 0 d => some (.A a k 0 (d + 3))
  | .A a 0 b d =>
    Nat.casesOn a none fun a =>
    Nat.casesOn a (some (.D1 0 (b + 1) d)) fun a =>
    some (.A a 2 b (d + 2))
  | .A a 1 b d =>
    Nat.casesOn a (some (.D1 1 b d)) fun a =>
    some (.B a 1 b d)
  | .A a 2 b d => some (.D1 (a + 2) b d)
  | .A a (k + 3) b d => some (.A a k (b + 1) d)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
inductive HighLevelState where
  | D (a d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D 0 7

def toState : HighLevelState → State
  | .D a d => .D1 (a + 1) 0 d

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalA (a k m : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if k % 3 = 2 then some (a + 1, k / 3, m)
  else if a = 0 then (if k % 3 = 0 then none else some (0, k / 3, m))
  else if k % 3 = 0 then some (a - 1, k / 3, m + 2)
  else evalA (a - 1) (k / 3) (m + 2 * (k / 3) + 3)
termination_by a
decreasing_by omega

def drainB (a b d : ℕ) : Option HighLevelState :=
  if b = 0 then some (.D a d)
  else
    (evalA a (b - 1) (d + 2 * b + 3)).bind fun p =>
      if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none
termination_by b
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .D a d =>
    if a = 0 then
      if d % 2 = 1 then drainB (d + 1) 2 2 else some (.D d 7)
    else if d % 2 = 1 ∧ a ≥ d + 5 then drainB (a - d - 5) (d + 3) 5
    else if d % 2 = 0 ∧ a ≥ d + 3 then drainB (a - d - 2) (d + 2) 2
    else if a % 2 = 1 then none
    else if a = d + 2 then drainB 0 a 2
    else if d % 2 = 1 then drainB (d + 4 - a) (a - 1) 3
    else (evalA (d + 1 - a) a (2 * a + 5)).bind fun p => drainB p.1 p.2.1 p.2.2

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

namespace BB6
theorem isHalt_HHH1LC_iff_HHH0LA :
    IsHalt M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.target ↔
      IsHalt M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.target := by sorry
end BB6

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

/-! ### Level B: accelerated state machine -/

def F_R (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
    (ListBlank.append [0, 0] r)

def cfg_A (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
    (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def Odd_cfg (p k n m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  F_R (2 * p + 1) k
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

def ETail_cfg (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
      (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Symbolic configuration state space for `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`. -/
inductive State
  /-- $A(b, k, c) := 0^\infty\,1^b\,(01)^k\,\mathrm{F}{>}\,0\,0\,1^c\,0^\infty$. -/
  | A (b k c : ℕ)
  /-- $Odd(p, k, n, m, c) :=
  0^\infty\,1^{2p+1}\,(01)^k\,\mathrm{F}{>}\,0\,0\,1^{2n}\,(01)^{m+1}\,1^c\,0^\infty$. -/
  | Odd (p k n m c : ℕ)
  /-- $ETail(k, m, c) := 0^\infty\,1^{2k+9}\,\mathrm{E}{>}\,(01)^m\,1^c\,0^\infty$. -/
  | ETail (k m c : ℕ)

/-- Initial symbolic state $A(5, 0, 2)$, reached from the blank tape. -/
def start : State := .A 5 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A b k c => cfg_A b k c
  | .Odd p k n m c => Odd_cfg p k n m c
  | .ETail k m c => ETail_cfg k m c

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.A 4 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b (some (.A 3 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.A (b + 1) 0 5))
      fun k => some (.A b k 1)
  | .A b k 1 =>
    Nat.casesOn b (some (.A (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 0)) fun k => some (.Odd 2 0 0 k 0)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.A (b + 1) 0 (2 * k + 7))
  | .A b k (c + 2) =>
    Nat.casesOn b (some (.A 1 (k + 1) c)) fun b =>
    Nat.casesOn b (some (.A 1 (k + 2) c)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 (c + 1))) fun k => some (.Odd 2 0 0 k (c + 1))) fun b =>
    some (.A (b + 1) (k + 2) c)
  | .Odd p k (n + 1) m c =>
    Nat.casesOn p (some (.Odd 0 (k + 2) n m c)) fun p =>
    some (.Odd p (k + 2) n m c)
  | .Odd p k 0 m c =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn m (some (.A (2 * p + 1) 0 (2 * (k + 3) + c))) fun m =>
    some (.Odd p 0 (k + 3) m c)
  | .ETail k 0 c => some (.A (2 * k + c + 7) 0 3)
  | .ETail k 1 c => some (.A (2 * (k + 4) + 1) 0 c)
  | .ETail k (m + 2) c => some (.Odd (k + 4) 0 0 m c)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
inductive HighLevelState where
  /-- $A(b, c) := 0^\infty\,1^b\,\mathrm{F}{>}\,00\,1^c\,0^\infty$. -/
  | A (b c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .A 5 2

def toState : HighLevelState → State
  | .A b c => .A b 0 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalOdd (m p n c : ℕ) : HighLevelState :=
  if m = 0 then
    if p ≤ n + 1 then .A (4 * n + c + 7) 3 else .A (2 * (p - n - 2) + 1) (4 * n + c + 6)
  else if m = 1 then
    if p ≤ n + 1 then .A (4 * n + 9) c else evalOdd 0 (p - n - 2) (2 * n + 3) c
  else
    if p ≤ n + 1 then evalOdd (m - 2) (2 * n + 4) 0 c
    else evalOdd (m - 1) (p - n - 2) (2 * n + 3) c
termination_by m
decreasing_by all_goals omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .A b c =>
    if b = 0 then some (.A (2 * c + 4) 3)
    else if b = 2 then (if c = 0 then some (.A 3 3) else some (.A 5 (c - 1)))
    else if 2 * (c / 2) + 5 ≤ b then some (.A (b - 2 * (c / 2) - 4) (2 * c + 5))
    else if b % 2 = 1 then some (.A (2 * c + 6) 3)
    else if b ≤ 2 * (c / 2) then some (evalOdd (b - 3) 2 0 (c - b + 1))
    else if b = 2 * (c / 2) + 2 then some (evalOdd (b - 4 + c % 2) 2 0 0)
    else none

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  /-- `.C a b` encodes $C(a, b + 1) := 0^\infty\,\mathrm{E}{>}\,(10)^a\,1^{b+1}\,0^\infty$. -/
  | C (a b : ℕ)

/-- Initial state `.C 0 2`, encoding $C(0, 3) = 0^\infty\,\mathrm{E}{>}\,1^3\,0^\infty$. -/
def highLevelStart : HighLevelState := .C 0 2

def toState : HighLevelState → State
  | .C a b => .C a b

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .C a 0 => some (.C 2 (2 * a + 1))
  | .C _ 1 => none
  | .C a (d + 2) =>
    if d ≥ 2 * a then some (.C (2 * a + 2) (d - 2 * a))
    else if d % 2 = 1 then
      some (.C ((6 * a + d + 5) / 4) ((6 * a + d + 5) % 4))
    else
      some (.C ((6 * a + d + 8) / 4) ((6 * a + d + 8) % 4))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  /-- $J(u, w) := 0^\infty\,1^5\,(10)^u\,1\,\mathrm{A}{>}\,1^{w+2}\,01\,0^\infty$. -/
  | J (u w : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .J 0 0

def toState : HighLevelState → State
  | .J u w => .J u 0 w

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .J u w =>
    let m := w / 2
    if w ≥ 2 * u + 3 then some (.J (2 * u + 3) (w - 2 * u - 3))
    else if w = 2 * u + 2 then some (.J 0 (4 * u + 18))
    else if w = 2 * u + 1 then some (.J 11 (4 * u + 2))
    else if w = 2 * u then some (.J 0 (4 * u + 12))
    else
      let d := u - m
      if w % 2 = 0 then
        if d = 1 then some (.J 0 (2 * w + 12))
        else if d % 2 = 0 then some (.J 11 (2 * u + w - 2))
        else some (.J 0 (2 * u + w + 10))
      else
        if d = 1 then none
        else if d = 2 then some (.J 0 (2 * w + 8))
        else if d % 2 = 0 then
          if w = 1 then some (.J 11 (2 * u + 10))
          else some (.J (d + 7) (2 * w - 4))
        else some (.J (d + 3) (2 * w))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

/-! ### Level B: accelerated state machine -/

abbrev cfg_A (l : ListBlank (Fin 2)) (k j c : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
    (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
      (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

abbrev l_hat : ListBlank (Fin 2) :=
  ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)

abbrev l_ones3 : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ 3) default

abbrev cfg_C001 (l : ListBlank (Fin 2)) (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C l
    (ListBlank.append [0, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))

inductive State where
  | S_def (k j c : ℕ)
  | S_hat (k j c : ℕ)
  | C_def (a b : ℕ)
  | C_hat (a b : ℕ)
  | C_ones3 (a b : ℕ)

def start : State := .S_def 2 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .S_def k j c => cfg_A default k j c
  | .S_hat k j c => cfg_A l_hat k j c
  | .C_def a b => cfg_C001 default a b
  | .C_hat a b => cfg_C001 l_hat a b
  | .C_ones3 a b => cfg_C001 l_ones3 a b

def next : State → Option State
  | .S_def 0 0 c => some (.C_def 0 (c + 2))
  | .S_def 0 (j + 1) c => some (.C_hat j c)
  | .S_def 1 j 0 => some (.S_def 0 0 (2 * j + 3))
  | .S_def 1 j (c + 1) => some (.C_def (j + 1) c)
  | .S_def 2 j 0 => some (.S_def 0 0 (2 * j + 5))
  | .S_def 2 j (c + 1) => some (.C_def (j + 2) c)
  | .S_def (k + 3) j 0 => some (.S_def (k + 1) 0 (2 * j + 5))
  | .S_def (k + 3) j (c + 1) => some (.S_def k (j + 2) c)
  | .S_hat 0 0 c => some (.S_def 2 0 (c + 2))
  | .S_hat 0 (j + 1) c => some (.S_def 6 (j + 1) c)
  | .S_hat 1 j 0 => some (.S_def 1 1 (2 * j + 5))
  | .S_hat 1 j (c + 1) => some (.C_ones3 (j + 1) c)
  | .S_hat 2 j 0 => some (.S_hat 0 0 (2 * j + 5))
  | .S_hat 2 j (c + 1) => some (.S_def 1 (j + 3) c)
  | .S_hat (k + 3) j 0 => some (.S_hat (k + 1) 0 (2 * j + 5))
  | .S_hat (k + 3) j (c + 1) => some (.S_hat k (j + 2) c)
  | .C_def a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 2) 0 0)) fun b =>
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 2) 0 3)) fun c =>
      some (.S_def (4 * (a / 2) + 4) 0 c)
    else
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 4) 0 1)) fun c =>
      some (.S_def (4 * (a / 2) + 3) 0 (c + 1))
  | .C_hat a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 2) 0 0)) fun b =>
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 2) 0 3)) fun c =>
      some (.S_hat (4 * (a / 2) + 4) 0 c)
    else
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 4) 0 1)) fun c =>
      some (.S_hat (4 * (a / 2) + 3) 0 (c + 1))
  | .C_ones3 a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 2)) 0 0)) fun b =>
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 2)) 0 3)) fun c =>
      some (.S_def (3 + (4 * (a / 2) + 4)) 0 c)
    else
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 4)) 0 1)) fun c =>
      some (.S_def (3 + (4 * (a / 2) + 3)) 0 (c + 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
inductive HighLevelState where
  /-- $S(p, k, c) := 0^\infty\,(1110)^p\,1^k\,\mathrm{D}{>}\,11\,1^c\,0^\infty$. -/
  | S (p : Bool) (k c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .S false 2 0

def toState : HighLevelState → State
  | .S false k c => .S_def k 0 c
  | .S true k c => .S_hat k 0 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .S p k c =>
    let q := k / 3
    let r := k % 3
    if c < q then some (.S p (k - 3 * c - 2) (4 * c + 5))
    else
      let d := c - q
      if p then
        if r = 0 then
          if q = 0 then some (.S false 2 (c + 2))
          else if d = 0 then some (.S false 4 (4 * q + 5))
          else if d = 1 then some (.S false 1 (4 * q + 9))
          else if d = 2 then some (.S true (4 * q + 8) 1)
          else some (.S true (4 * q + 7) (d - 2))
        else if r = 1 then
          if d = 0 then some (.S false 8 (4 * q + 1))
          else if d = 1 then some (.S false (4 * q + 7) 1)
          else some (.S false (4 * q + 6) (d - 1))
        else
          if d = 0 then some (.S true 0 (4 * q + 5))
          else if d = 1 then some (.S false 0 (4 * q + 9))
          else if d = 2 then none
          else if d = 3 then some (.S false (4 * q + 10) 0)
          else if d = 4 then some (.S false (4 * q + 10) 3)
          else some (.S false (4 * q + 12) (d - 5))
      else
        if r = 0 then
          if q = 0 then
            if c = 0 then some (.S false 2 3) else some (.S false 4 (c - 1))
          else if d = 0 then some (.S true (4 * q) 1)
          else some (.S true (4 * q - 1) d)
        else if r = 1 then
          if d = 0 then some (.S false 0 (4 * q + 3))
          else if d = 1 then some (.S false (4 * q + 4) 1)
          else some (.S false (4 * q + 3) (d - 1))
        else
          if d = 0 then some (.S false 0 (4 * q + 5))
          else if d = 1 then none
          else if d = 2 then some (.S false (4 * q + 6) 0)
          else if d = 3 then some (.S false (4 * q + 6) 3)
          else some (.S false (4 * q + 8) (d - 4))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | L (p : Bool) (b : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .L false 0

def toState : HighLevelState → State
  | .L p b => .C 0 b 0 (if p then 1 else 0)

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def drainA (b a : ℕ) (p : Bool) : HighLevelState :=
  if a = 0 then
    .L p b
  else if a = 1 then
    let q := b / 3
    if b % 3 = 0 then .L false (8 * q + if p then 8 else 7)
    else if b % 3 = 1 then .L false (8 * q + if p then 14 else 13)
    else .L p (8 * q + 8)
  else
    let q := b / 3
    let b' := if b % 3 = 0 then 8 * q + 10 else if b % 3 = 1 then 8 * q + 16 else 8 * q + 8
    drainA b' (a - (2 - b % 3 / 2)) p
termination_by a
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .L false b =>
    let q := b / 3
    if b % 3 = 0 then some (drainA 0 (2 * q + 1) true)
    else some (.L false (8 * q + 5))
  | .L true b =>
    let q := b / 3
    if b % 3 = 0 then none
    else if b % 3 = 1 then some (drainA 0 (2 * q + 3) true)
    else some (.L false (8 * q + 6))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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

/-! ### Level B: accelerated state machine -/

def F_R (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
    (ListBlank.append [0, 0] r)

def cfg_F (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
    (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def Odd_cfg (p k n m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  F_R (2 * p + 1) k
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

def ETail_cfg (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
      (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

def π : Fin 6 -> Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 4
  | 5 => 0

def mirrorTape : Tape (Fin 2) -> Tape (Fin 2)
  | ⟨head, l, r⟩ => ⟨head, r, l⟩

def mirrorCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map π, mirrorTape c.tape⟩

inductive State
  | A (b k c : ℕ)
  | Odd (p k n m c : ℕ)
  | ETail (k m c : ℕ)

def start : State := .A 4 0 3

def encode_F : State → Cfg (Fin 2) (Fin 6)
  | .A b k c => cfg_F b k c
  | .Odd p k n m c => Odd_cfg p k n m c
  | .ETail k m c => ETail_cfg k m c

def encode (s : State) : Cfg (Fin 2) (Fin 6) :=
  mirrorCfg (encode_F s)

def next : State → Option State
  | .A b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.A 4 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b (some (.A 3 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.A (b + 1) 0 5))
      fun k => some (.A b k 1)
  | .A b k 1 =>
    Nat.casesOn b (some (.A (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 0)) fun k => some (.Odd 2 0 0 k 0)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.A (b + 1) 0 (2 * k + 7))
  | .A b k (c + 2) =>
    Nat.casesOn b (some (.A 1 (k + 1) c)) fun b =>
    Nat.casesOn b (some (.A 1 (k + 2) c)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 (c + 1))) fun k => some (.Odd 2 0 0 k (c + 1))) fun b =>
    some (.A (b + 1) (k + 2) c)
  | .Odd p k (n + 1) m c =>
    Nat.casesOn p (some (.Odd 0 (k + 2) n m c)) fun p =>
    some (.Odd p (k + 2) n m c)
  | .Odd p k 0 m c =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn m (some (.A (2 * p + 1) 0 (2 * (k + 3) + c))) fun m =>
    some (.Odd p 0 (k + 3) m c)
  | .ETail k 0 c => some (.A (2 * k + c + 7) 0 3)
  | .ETail k 1 c => some (.A (2 * (k + 4) + 1) 0 c)
  | .ETail k (m + 2) c => some (.Odd (k + 4) 0 0 m c)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
inductive HighLevelState where
  /-- $A(b, c) := 0^\infty\,1^c\,0\,\mathrm{A}{>}\,0\,1^b\,0^\infty$. -/
  | A (b c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .A 4 3

def toState : HighLevelState → State
  | .A b c => .A b 0 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalOdd (m p n c : ℕ) : HighLevelState :=
  if m = 0 then
    if p ≤ n + 1 then .A (4 * n + c + 7) 3 else .A (2 * (p - n - 2) + 1) (4 * n + c + 6)
  else if m = 1 then
    if p ≤ n + 1 then .A (4 * n + 9) c else evalOdd 0 (p - n - 2) (2 * n + 3) c
  else
    if p ≤ n + 1 then evalOdd (m - 2) (2 * n + 4) 0 c
    else evalOdd (m - 1) (p - n - 2) (2 * n + 3) c
termination_by m
decreasing_by all_goals omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .A b c =>
    if b = 0 then some (.A (2 * c + 4) 3)
    else if b = 2 then (if c = 0 then some (.A 3 3) else some (.A 5 (c - 1)))
    else if 2 * (c / 2) + 5 ≤ b then some (.A (b - 2 * (c / 2) - 4) (2 * c + 5))
    else if b % 2 = 1 then some (.A (2 * c + 6) 3)
    else if b ≤ 2 * (c / 2) then some (evalOdd (b - 3) 2 0 (c - b + 1))
    else if b = 2 * (c / 2) + 2 then some (evalOdd (b - 4 + c % 2) 2 0 0)
    else none

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | N (d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .N 1

def toState : HighLevelState → State
  | .N d => .C d 0 0 0

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def scanEven (d b : ℕ) : Option HighLevelState :=
  if d % 2 = 0 then
    if d = 0 then none
    else scanEven (d / 2 - 1) (b + d / 2 + 2)
  else if d = 1 then
    some (.N (b + 4))
  else
    some (.N (b + 5 * (d / 2 - 1) + 9))
termination_by d
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .N d => scanEven d 0

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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
inductive HighLevelState where
  | C3_0 (r : Bool) (c : ℕ)
  | C3_12 (c : ℕ)
  | C6_0 (r : Bool) (c : ℕ)
  | C6_12 (c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C3_0 false 6

def toState : HighLevelState → State
  | .C3_0 r c => .C_3 (if r then 1 else 0) 0 c
  | .C3_12 c => .C_3 0 12 c
  | .C6_0 r c => .C_6 (if r then 1 else 0) 0 c
  | .C6_12 c => .C_6 0 12 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def syracuseScan (r : Bool) (b k : ℕ) : Bool × ℕ :=
  if k = 0 then (r, b)
  else
    let s := b + if r then 1 else 0
    syracuseScan (decide (s % 2 = 1)) (3 * (s / 2) + 9) (k - 1)
termination_by k
decreasing_by omega

def finishC3 (r : Bool) (b rem : ℕ) : Option HighLevelState :=
  if rem = 0 then
    if b % 2 = 0 then some (.C3_0 r (b / 2 + 3))
    else if r then some (.C3_12 (b / 2))
    else none
  else
    if b % 2 = 1 then some (.C6_0 r (b / 2 + 3))
    else if !r then none
    else if b = 0 then some (.C6_0 true 13)
    else some (.C6_12 (b / 2 - 1))

def finishC6 (r : Bool) (b rem : ℕ) : Option HighLevelState :=
  if rem = 0 then
    if b % 2 = 1 then some (.C3_0 r (b / 2 + 5))
    else if r then some (.C3_12 (b / 2 + 1))
    else none
  else
    let s := b + if r then 1 else 0
    let s1 := (3 * (s / 2) + 6) + if s % 2 = 1 then 1 else 0
    finishC3 (decide (s1 % 2 = 1)) (3 * (s1 / 2) + 9) 1

def highLevelNext : HighLevelState → Option HighLevelState
  | .C3_0 r c => let p := syracuseScan r 0 (c / 2); finishC3 p.1 p.2 (c % 2)
  | .C3_12 c => let p := syracuseScan false 12 (c / 2); finishC3 p.1 p.2 (c % 2)
  | .C6_0 r c => let p := syracuseScan r 0 (c / 2); finishC6 p.1 p.2 (c % 2)
  | .C6_12 c => let p := syracuseScan false 12 (c / 2); finishC6 p.1 p.2 (c % 2)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | P (c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .P 7

def toState : HighLevelState → State
  | .P c => .P61 0 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def drainP (a c : ℕ) : Option HighLevelState :=
  if c = 0 then some (.P (4 * a + 4 * (a / 2) + 15))
  else if c = 1 then some (.P (2 * a + 11))
  else if c = 2 then none
  else
    let c0 := c - 3
    let k := min (a / 2) (c0 / 4)
    let a1 := a - 2 * k
    let b1 := 3 * k
    let c1 := c0 - 4 * k
    if c1 = 0 then
      if a1 < 2 then none
      else some (.P (4 * (a1 - 2) + 4 * ((a1 - 2) / 2) + 4 * b1 + 35))
    else if c1 = 1 then
      if a1 < 2 then none
      else some (.P (4 * (a1 - 2) + 4 * ((a1 - 2) / 2) + 4 * b1 + 27))
    else if c1 = 2 then
      some (.P (2 * a1 + 2 * b1 + 13))
    else if c1 = 3 then
      if a1 = 0 then some (.P (12 * b1 + 63))
      else if a1 = 1 then some (.P (12 * b1 + 75))
      else none
    else if a1 = 0 then drainP (2 * b1 + 8) (c1 - 3)
    else drainP (2 * b1 + 10) (c1 - 3)
termination_by c
decreasing_by
  all_goals exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) (by omega)

def highLevelNext : HighLevelState → Option HighLevelState
  | .P c => drainP 0 c

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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

/-! ### Level B: accelerated state machine -/

/-- Left stack block `[0, 0, 1, 1]` (representing `1100` from left to right on the tape). -/
abbrev U4 : List (Fin 2) := [0, 0, 1, 1]

/-- Canonical left tape `LA a := [0, 0, 1, 1] ^ a` (blank beyond). -/
def LA (a : Nat) : ListBlank (Fin 2) := ListBlank.append (U4 ^ a) default

def R1_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (ListBlank.append [0, 0, 1] (LA n)) default

def R2_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (ListBlank.append [0, 0, 1, 0, 0, 1] (LA n)) default

def Q_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (ListBlank.append [0, 0, 1, 1, 1, 1] (LA n)) default

def S4_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (ListBlank.append [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1] (LA n)) default

def S6_cfg (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (ListBlank.append [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1] (LA n)) default

inductive State where
  /-- $R_1(n) := 0^\infty\,(1100)^n\,100\,\mathrm{A}{>}\,0^\infty$. -/
  | R1 (n : ℕ)
  /-- $R_2(n) := 0^\infty\,(1100)^n\,100100\,\mathrm{A}{>}\,0^\infty$. -/
  | R2 (n : ℕ)
  /-- $Q(n) := 0^\infty\,(1100)^n\,111100\,\mathrm{A}{>}\,0^\infty$. -/
  | Q (n : ℕ)
  /-- $S_4(n) := 0^\infty\,(1100)^n\,111100100100\,\mathrm{A}{>}\,0^\infty$. -/
  | S4 (n : ℕ)
  /-- $S_6(n) := 0^\infty\,(1100)^n\,11111100100100\,\mathrm{A}{>}\,0^\infty$. -/
  | S6 (n : ℕ)

def start : State := .S6 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .R1 n => R1_cfg n
  | .R2 n => R2_cfg n
  | .Q n => Q_cfg n
  | .S4 n => S4_cfg n
  | .S6 n => S6_cfg n

/-- `P_cfg n` (`LA n {{A}}> default`): `P 0 ↦ S6 1`, `P 1 ↦ S4 0`, `P (n + 2) ↦ S6 n`. -/
def next_P (n : ℕ) : Option State :=
  Nat.casesOn n (some (.S6 1)) fun n =>
  Nat.casesOn n (some (.S4 0)) fun n' =>
  some (.S6 n')

/-- `R1 0 ↦ R1 4`, `R1 1 ↦ R1 6`, `R1 (n + 2) ↦ R1 (n + 7)`. -/
def next_R1 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 4)) fun n =>
  Nat.casesOn n (some (.R1 6)) fun n' =>
  some (.R1 (n' + 7))

/-- `T1_cfg n`: `T1 0 ↦ R1 7`, `T1 (n + 1) ↦ R1 (n + 8)`. -/
def next_T1 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 7)) fun n' =>
  some (.R1 (n' + 8))

/-- `R3_cfg n`: `R3 0 ↦ T1 4`, `R3 1 ↦ T1 6`, `R3 (n + 2) ↦ T1 (n + 7)`. -/
def next_R3 (n : ℕ) : Option State :=
  Nat.casesOn n (next_T1 4) fun n =>
  Nat.casesOn n (next_T1 6) fun n' =>
  next_T1 (n' + 7)

/-- `HubTail (a + 7) w r_R2`: consume `W8` blocks five at a time (`a ↦ a + 31`), branching on the
remainder `w mod 5`. -/
def next_HubTail_r_R2 : ℕ → ℕ → Option State
  | a, 0 => some (.R1 (a + 8))
  | a, 1 => some (.R2 (a + 11))
  | a, 2 => some (.Q (a + 19))
  | a, 3 => some (.R2 (a + 26))
  | a, 4 => next_R3 (a + 32)
  | a, w' + 5 => next_HubTail_r_R2 (a + 31) w'

/-- `HubTail (a + 7) w r_3`; the remainder `w = 3` halts. -/
def next_HubTail_r_3 : ℕ → ℕ → Option State
  | a, 0 => some (.R1 (a + 10))
  | a, 1 => some (.Q (a + 16))
  | a, 2 => some (.R2 (a + 23))
  | _, 3 => none
  | a, 4 => some (.R2 (a + 37))
  | a, w' + 5 => next_HubTail_r_3 (a + 31) w'

/-- `HubTail (a + 7) w r_4`. -/
def next_HubTail_r_4 : ℕ → ℕ → Option State
  | a, 0 => next_T1 (a + 9)
  | a, 1 => some (.R2 (a + 15))
  | a, 2 => some (.R1 (a + 25))
  | a, 3 => some (.S6 (a + 28))
  | a, 4 => some (.R2 (a + 41))
  | a, w' + 5 => next_HubTail_r_4 (a + 31) w'

/-- `HubTail (a + 7) w r_5`. -/
def next_HubTail_r_5 : ℕ → ℕ → Option State
  | a, 0 => some (.R1 (a + 12))
  | a, 1 => some (.R1 (a + 15))
  | a, 2 => some (.R2 (a + 26))
  | a, 3 => some (.Q (a + 34))
  | a, 4 => next_T1 (a + 38)
  | a, w' + 5 => next_HubTail_r_5 (a + 31) w'

/-- Successor maps of the seven `Scan` prefixes `p0`, `p001010`, `p0010`, `p0010110`, `p00`,
`p010`, `pnil`, each as a function of the offset `a` of `LA (a + 4)`, together with the two carry
components `p0_next`/`p0010_next` giving the `p0`/`p0010` successor maps one `B4` block further
(these let the bundles be defined by plain structural recursion on the block count). -/
structure NextScanBundle where
  p0 : ℕ → Option State
  p001010 : ℕ → Option State
  p0010 : ℕ → Option State
  p0010110 : ℕ → Option State
  p00 : ℕ → Option State
  p010 : ℕ → Option State
  pnil : ℕ → Option State
  p0_next : ℕ → Option State
  p0010_next : ℕ → Option State

/-- `HubW8 (a + 7) w b rend`: consume `W8` blocks five at a time, then hand over to the `Scan`
prefix selected by the remainder `w mod 5`. -/
def next_HubW8 (nb : NextScanBundle) : ℕ → ℕ → Option State
  | a, 0 => nb.p0 (a + 4)
  | a, 1 => nb.p010 (a + 7)
  | a, 2 => nb.p00 (a + 16)
  | a, 3 => nb.p0010 (a + 22)
  | a, 4 => nb.p001010 (a + 28)
  | a, w' + 5 => next_HubW8 nb (a + 31) w'

/-- `Scan (a + 4) b pfx r_Q` successor maps, by recursion on the number `b` of `B4` blocks. -/
def next_ScanBundle_r_Q (b : ℕ) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.R1 (a + 4))
      p001010 := fun a => next_P (a + 8)
      p0010 := fun a => some (.R2 (a + 4))
      p0010110 := fun a => next_P (a + 10)
      p00 := fun a => some (.R1 (a + 4))
      p010 := fun a => next_P (a + 7)
      pnil := fun a => next_P (a + 5)
      p0_next := fun a => some (.S6 (a + 2))
      p0010_next := fun a => some (.R1 (a + 9)) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

/-- `Scan (a + 4) b pfx r_S6` successor maps; the prefix `p0010110` with `b = 0` halts. -/
def next_ScanBundle_r_S6 (b : ℕ) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.S4 (a + 9))
      p001010 := fun a => next_T1 (a + 11)
      p0010 := fun a => some (.R1 (a + 10))
      p0010110 := fun _ => none
      p00 := fun a => some (.R2 (a + 11))
      p010 := fun a => some (.R1 (a + 14))
      pnil := fun a => next_T1 (a + 8)
      p0_next := fun a => next_HubTail_r_4 0 ((a + 1) / 2 + 1)
      p0010_next := fun a => next_HubTail_r_3 0 ((a + 8) / 2) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

/-- `Scan (a + 4) b pfx r_S4` successor maps. -/
def next_ScanBundle_r_S4 (b : ℕ) : NextScanBundle :=
  Nat.rec
    { p0 := fun a => some (.R2 (a + 7))
      p001010 := fun a => some (.R1 (a + 9))
      p0010 := fun a => some (.R1 (a + 9))
      p0010110 := fun a => some (.S4 (a + 9))
      p00 := fun a => next_T1 (a + 4)
      p010 := fun a => some (.Q (a + 9))
      pnil := fun a => some (.R1 (a + 6))
      p0_next := fun a => next_HubTail_r_5 0 ((a + 1) / 2 + 1)
      p0010_next := fun a => some (.R1 (a + 13)) }
    (fun _ nb =>
      { p0 := nb.p0_next
        p001010 := fun a => nb.p0 (a + 6)
        p0010 := nb.p0010_next
        p0010110 := fun a => nb.p00 (a + 9)
        p00 := fun a => nb.p010 (a + 3)
        p010 := fun a => nb.pnil (a + 4)
        pnil := fun a => nb.p0 (a + 3)
        p0_next := fun a => next_HubW8 nb 0 ((a + 3) / 2)
        p0010_next := fun a => nb.p0010110 (a + 5) })
    b

/-- `R2 0 ↦ R1 4`; `R2 (n + 1)` drains `n` stack blocks in pairs into `HubTail 7 (n / 2) r_R2`. -/
def next_R2 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 4)) fun n' =>
  next_HubTail_r_R2 0 (n' / 2)

/-- `Q 0 ↦ R1 6`; `Q (n + 1)` sweeps into `Scan 6 n p0010110 r_Q`. -/
def next_Q (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 6)) fun n' =>
  (next_ScanBundle_r_Q n').p0010110 2

/-- `S4 0 ↦ R1 10`; `S4 (n + 1)` sweeps into `Scan 6 n p0010110 r_S4`. -/
def next_S4 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 10)) fun n' =>
  (next_ScanBundle_r_S4 n').p0010110 2

/-- `S6 0 ↦ R1 9`; `S6 1` drains into `HubTail 7 2 r_3`; `S6 (n + 2)` sweeps into
`Scan 6 n p0010110 r_S6`. -/
def next_S6 (n : ℕ) : Option State :=
  Nat.casesOn n (some (.R1 9)) fun n =>
  Nat.casesOn n (next_HubTail_r_3 0 2) fun n' =>
  (next_ScanBundle_r_S6 n').p0010110 2

/-- The accelerated Collatz-like transition function on the five core families. -/
def next : State → Option State
  | .R1 n => next_R1 n
  | .R2 n => next_R2 n
  | .Q n => next_Q n
  | .S4 n => next_S4 n
  | .S6 n => next_S6 n

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
abbrev HighLevelState := State

def highLevelStart : HighLevelState := start

def highLevelEncode : HighLevelState → Cfg (Fin 2) (Fin 6) := encode

def highLevelNext : HighLevelState → Option HighLevelState := next

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  | C (b d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 0 0

def toState : HighLevelState → State
  | .C b d => .A 0 b 0 d

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def drainA (a b d : ℕ) : HighLevelState :=
  if a = 0 then .C b d
  else if a = 1 then
    if d = 0 then .C 1 (2 * b + 1)
    else if b = 0 then .C 0 (d + 2)
    else .C 1 (2 * b + 4 * d + 1)
  else if a = 2 ∧ d ≠ 0 then .C (b + 1) (d - 1)
  else
    let a1 := a + (1 - d)
    let b1 := if d = 0 then 0 else b
    let d1 := (if d = 0 then 2 * b + 1 else d - 1) + 1
    let k := min (a1 / 3) d1
    drainA (a1 - 3 * k) (b1 + 2 * k) (d1 - k)
termination_by a
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .C b 0 => some (.C 0 (2 * b + 4))
  | .C 0 1 => some (.C 2 5)
  | .C (b + 1) 1 => some (.C 2 (2 * b + 3))
  | .C b (d + 2) =>
    if b ≥ d + 1 then some (drainA (3 * d + 2) 3 (2 * b - 2 * d - 1))
    else if d = b then none
    else if d = b + 1 then some (drainA (3 * b + 2) 0 6)
    else if d = b + 2 then some (drainA (3 * b + 4) 0 4)
    else some (drainA (3 * b + 3) 2 (d - b - 3))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | E (a b c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .E 3 0 0

def toState : HighLevelState → State
  | .E a b c => mkE a b c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalFGe2 (d k b c : ℕ) : Option HighLevelState :=
  if k = 0 then
    if b = 0 then
      if c = 0 then some (.E (d + 3) 3 0)
      else evalFGe2 (d + 1) 0 c 0
    else if b % 2 = 0 then evalFGe2 (d + 1) (b / 2) c 0
    else if b = 1 then none
    else if b = 3 then some (.E (d + c + 5) 3 0)
    else some (.E (d + 4) (b - 4) (c + 3))
  else if k = 1 then
    some (.E (d + 1) (b + 4) c)
  else
    evalFGe2 (d + 1) (k - 2) (b + 3) c
termination_by 5 * k + 3 * b + 4 * c
decreasing_by all_goals omega

def evalF1 (k b c : ℕ) : Option HighLevelState :=
  if k = 0 then
    if b = 0 then
      if c = 0 then some (.E 2 3 0)
      else evalFGe2 0 0 c 0
    else if b % 2 = 0 then evalFGe2 0 (b / 2) c 0
    else if b = 1 then none
    else if b = 3 then some (.E (c + 4) 3 0)
    else some (.E 3 (b - 4) (c + 3))
  else if k = 1 then
    if b % 2 = 1 then some (.E (b + 4) c 0)
    else evalFGe2 0 (b / 2) (c + 3) 0
  else
    evalFGe2 0 (k - 2) (b + 3) c

def evalF0 (k b c : ℕ) : Option HighLevelState :=
  if k = 0 then
    if b = 0 then
      if c = 0 then some (.E 1 3 0)
      else evalF1 0 c 0
    else if b % 2 = 0 then evalF1 (b / 2) c 0
    else if b = 1 then none
    else if b = 3 then some (.E (c + 3) 3 0)
    else some (.E 2 (b - 4) (c + 3))
  else if k = 1 then
    some (.E (b + 2) (c + 3) 0)
  else
    evalF1 (k - 2) (b + 3) c

def highLevelNext : HighLevelState → Option HighLevelState
  | .E a b c =>
    if a % 2 = 0 then evalF0 (a / 2) b c
    else if a = 1 then none
    else some (.E (b + 3 * a - 6) (c + 3) 0)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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

inductive HighLevelState where
  | A (k b : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .A 0 0

def toState : HighLevelState → State
  | .A k b => .A (2 * k + 2) b

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalB (a b c : ℕ) : HighLevelState :=
  if a < b then evalB (2 * a + 2) (b - a - 1) c
  else if a = b then .A 0 (4 * a + 2 * c + 6)
  else .A 0 (2 * a + 2 * c + 2)
termination_by b
decreasing_by omega

def drainA (k b : ℕ) : Option HighLevelState :=
  let a := 2 * k + 2
  if a < b then drainA (2 * k + 2) (b - a - 1)
  else if a = b then none
  else if (a - b - 1) % 2 = 0 then
    some (.A ((a - b - 1) / 2) (2 * b + 2))
  else
    some (evalB 2 (2 * ((a - b - 1) / 2) + 1) (b + 1))
termination_by b
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .A k b => drainA k b

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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
inductive HighLevelState where
  /-- $E(b, d) := 0^\infty\,(10)^b\,1111\,\mathrm{E}{>}\,1^{d+2}\,0^\infty$. -/
  | E (b d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .E 0 1

def toState : HighLevelState → State
  | .E b d => .E 1 b (d + 1)

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .E b d =>
    let c := d + 1
    let m := d / 2
    if b > m then
      if b = m + 1 then some (.E 0 (2 * c + 3))
      else if b = m + 2 then some (.E 2 (2 * c + 1))
      else some (.E (b - m - 3) (2 * c + 5))
    else
      let rem := c - 2 * b
      if rem ≤ 2 then some (.E 0 (2 * c + 2))
      else if rem = 3 then none
      else if rem ≤ 6 then some (.E (2 * b + 2) (2 * rem - 7))
      else some (.E (2 * b + 4) (rem - 7))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  /-- `.C a b` encodes
    $C(a, b + 6) := 0^\infty\,110\,\mathrm{A}{>}\,(11)^a\,0\,1^{b+6}\,0^\infty$. -/
  | C (a b : ℕ)

/-- Initial state `.C 0 3`, encoding $C(0, 9) = 0^\infty\,110\,\mathrm{A}{>}\,0\,1^9\,0^\infty$. -/
def highLevelStart : HighLevelState := .C 0 3

def toState : HighLevelState → State
  | .C a b => .C a b

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .C 0 b =>
    if b % 2 = 0 then some (.C (b / 2 + 1) 3)
    else some (.C (b / 2 + 3) 0)
  | .C (a + 1) b =>
    if b % 2 = 0 then
      let k := b / 2
      if k ≤ a + 3 then some (.C (a + 4 - k) (6 * k + 6))
      else if k ≤ a + 5 then none
      else some (.C (k - a - 5) (6 * a + 33))
    else
      let k := b / 2 + 2
      if k > a then some (.C (k - a) (6 * a + 6))
      else if a ≤ k + 1 then none
      else some (.C (a - k - 1) (6 * k + 9))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | C0 (a b : ℕ)
  | C1 (a b c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C0 0 3

def toState : HighLevelState → State
  | .C0 a b => .C a b 0 0
  | .C1 a b c => .C a b c 1

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalR (a b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if b = 0 then
    if !d1 then some (.C0 0 (2 * a + 7))
    else some (.C0 0 (2 * (a + c) + 5))
  else if b = 1 then
    if !d1 then some (.C0 0 (2 * a + 5))
    else if c = 0 then none
    else some (.C1 0 (2 * a + 5) c)
  else if b = 2 then
    if !d1 then none
    else some (.C0 (a + c + 3) 0)
  else
    if !d1 then some (.C0 (a + 3) (b - 3))
    else some (.C1 (a + 3) (b - 3) c)

def evalS (a b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if b = 0 then
    if !d1 then some (.C0 (a + 2) 0)
    else some (.C0 0 (2 * (a + c) + 4))
  else if b = 1 then
    if !d1 then some (.C0 0 (2 * a + 4))
    else if c = 0 then evalR (a + 1) 0 0 false
    else some (.C1 0 (2 * a + 4) c)
  else
    evalR (a + 1) (b - 2) c d1

def evalM (k u b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if k = 0 then
    evalS (u + 2) b c d1
  else
    let k' := k - 1
    if b = 0 then
      if !d1 then
        if k = 1 then some (.C1 0 0 (u + 5))
        else if k = 2 then some (.C1 0 3 (u + 5))
        else if k = 3 then some (.C1 0 4 (u + 5))
        else if k = 4 then some (.C1 2 2 (u + 5))
        else if k = 5 then evalS 0 5 (u + 5) true
        else evalM (k - 6) 0 3 (u + 5) true
      else
        if k' = 0 then some (.C0 2 (2 * (u + c) + 6))
        else if k' = 1 then evalS 0 (2 * (u + c) + 9) 0 false
        else evalM (k' - 2) 0 (2 * (u + c) + 7) 0 false
    else if b = 1 then
      if !d1 then
        if k' = 0 then some (.C0 2 (2 * u + 6))
        else if k' = 1 then evalS 0 (2 * u + 9) 0 false
        else evalM (k' - 2) 0 (2 * u + 7) 0 false
      else if c = 0 then
        evalM k' (u + 2) 0 0 false
      else
        if k' = 0 then some (.C1 2 (2 * u + 6) c)
        else if k' = 1 then evalS 0 (2 * u + 9) c true
        else evalM (k' - 2) 0 (2 * u + 7) c true
    else
      evalM k' (u + 2) (b - 2) c d1
termination_by k
decreasing_by all_goals omega

def evalW (k b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if k = 0 then
    if d1 then some (.C1 2 b c) else some (.C0 2 b)
  else if k = 1 then
    evalS 0 (b + 3) c d1
  else
    evalM (k - 2) 0 (b + 1) c d1

def evalCPos (a b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if b = 0 then
    if d1 && c == 0 then
      if a = 1 then evalS 0 2 0 false
      else evalM (a - 2) 0 0 0 false
    else
      if a = 1 then evalS 0 1 c d1
      else evalW (a - 2) 2 c d1
  else
    if a = 1 then evalS 0 (b + 1) c d1
    else evalM (a - 2) 0 (b - 1) c d1

def highLevelNext : HighLevelState → Option HighLevelState
  | .C0 a b =>
    if a = 0 then
      if b = 0 then evalCPos 2 1 0 false
      else if b = 1 then none
      else evalCPos 2 (b - 2) 0 false
    else
      evalCPos a b 0 false
  | .C1 a b c =>
    if a = 0 then
      if b = 0 then
        if c = 0 then none
        else evalCPos 2 1 c true
      else if b = 1 then
        some (.C0 (c + 2) 0)
      else
        evalCPos 2 (b - 2) c true
    else
      evalCPos a b c true

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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
  /-- $C(a, k, d, c) :=
  0^\infty\,(10)^a\,(11)^k\,\mathrm{C}{>}\,(11)^d\,(10)^c\,1111\,0^\infty$. -/
  | mk (a k d c : ℕ)

def start : State := .mk 0 0 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .mk a k d c => evalTapePattern pat_A fun i =>
      if i = 0 then a else if i = 1 then k else if i = 2 then d else if i = 3 then c else 0

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
inductive HighLevelState where
  | D (a c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D 0 1

def toState : HighLevelState → State
  | .D a c => .mk a 0 0 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalK (k c : ℕ) : ℕ × ℕ :=
  let c1 := max c 1
  if c1 ≤ k then evalK (k - c1) (2 * c1 + 1)
  else (2 * k + 2, c1 - k - 1)
termination_by k
decreasing_by omega

def drainD (a d c : ℕ) : Option HighLevelState :=
  if a = 0 then
    if c = 0 then none else some (.D (d + 1) c)
  else
    let nextDC :=
      if c = 0 then evalK (d + 1) 0
      else if c - 1 ≤ d + 1 then evalK (d + 1 - (c - 1)) (2 * (c - 1) + 1)
      else (2 * d + 4, c - 1 - d - 2)
    drainD (a - 1) nextDC.1 nextDC.2
termination_by a
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .D a c => drainD a 0 c

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | D (p : Bool) (x d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D true 3 1

def toState : HighLevelState → State
  | .D false x d => .D76 0 x d
  | .D true x d => .D231 0 0 x d

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .D false x 0 =>
    let k := (x + 2) / 2
    if x % 2 = 0 then
      if (3 * k + 4) % 2 = 0 then none
      else some (.D true 3 (3 * ((3 * k + 4) / 2) + 4))
    else
      some (.D true 3 (3 * k + 6))
  | .D false x (d + 1) =>
    let k := (x + 2) / 2
    if x % 2 = 0 then some (.D true (3 * k + 3) d)
    else some (.D false (3 * k + 3) d)
  | .D true x d =>
    let k := x / 2
    if x % 2 = 0 then some (.D false (3 * k + 1) d)
    else if d = 0 then
      if (3 * k + 6) % 2 = 0 then none
      else some (.D true 3 (3 * ((3 * k + 6) / 2) + 4))
    else some (.D true (3 * k + 5) (d - 1))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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
  /-- $C(k, m, f) :=
  0^\infty\,(11)^{k+1}\,0\,(11)^{m+1}\,0\,\mathrm{D}{>}\,1^{f+2}\,0^\infty$. -/
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
inductive HighLevelState where
  /-- $D_p(a, b) := C(2(a+1), 2(b+1), 2 + 3p)$, i.e. `.C a b (if p then 4 else 1)`. -/
  | C (a b : ℕ) (p : Bool)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 2 0 false

def toState : HighLevelState → State
  | .C a b p => .C a b (if p then 4 else 1)

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .C a b p =>
    let r := if p then 1 else 0
    if a ≥ b + 2 then some (.C (a - b - 2) (3 * b + r + 4) p)
    else if a = b + 1 then
      if p then some (.C (3 * b + 5) 0 false) else some (.C (3 * b + 2) 2 true)
    else if b ≤ a + 1 then none
    else if b = a + 2 then
      if p then some (.C (3 * a + 5) 2 true) else some (.C (3 * a + 5) 0 false)
    else some (.C (b - a - 3) (3 * a + 2 * r + 5) (!p))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  /-- $C(a, c) := 0^\infty\,1^{a+2}\,\mathrm{E}{>}\,110\,1^{2c+2}\,0^\infty$. -/
  | C (a c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 8 1

def toState : HighLevelState → State
  | .C a c => if a % 2 = 0 then .C_0 (a / 2) 0 c else .C_1 (a / 2) 0 c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .C _ 0 => none
  | .C a 1 =>
    if a % 2 = 1 then some (.C 2 (a / 2 + 3))
    else if a = 0 then some (.C 14 0)
    else some (.C 17 (a / 2 - 1))
  | .C a (d + 2) =>
    let k := a / 2
    if k + 3 ≤ d then some (.C (3 * a + 20) (d - k - 3))
    else some (.C (6 * d + 3 * (a % 2) + 5) (k + 2 - d))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  | D (a w : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D 0 1

def toState : HighLevelState → State
  | .D 0 w => .D_0_odd 0 w
  | .D (a + 1) w => .D_succ_odd a 0 w

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalK2 (a w : ℕ) : Option HighLevelState :=
  let m := w / 2
  if a > m then some (.D (a - m - 1) (2 * w + 7))
  else if a = m then some (.D 0 (2 * w + 6))
  else if w = 2 * a + 2 then none
  else if w ≤ 2 * a + 5 then some (.D (2 * a + 4) (2 * w - 4 * a - 5))
  else evalK2 (2 * a + 4) (w - 2 * a - 6)
termination_by w
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .D a w =>
    let m := w / 2
    if a > m then some (.D (a - m - 1) (2 * w + 3))
    else if a = m then some (.D 0 (2 * w + 2))
    else if w = 2 * a + 2 then none
    else if w ≤ 2 * a + 5 then some (.D (2 * a + 2) (2 * w - 4 * a - 5))
    else evalK2 (2 * a + 2) (w - 2 * a - 6)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
  | .P_1 a c => evalTapePattern pat_P1 (fun i => if i = 0 then a else if i = 1 then c else 0)
  | .P_2 k m c => evalTapePattern pat_P2
      (fun i => if i = 0 then k else if i = 1 then m else if i = 2 then c else 0)

def next : State → Option State
  | .P_1 a 0 => some (.P_1 2 (a + 1))
  | .P_1 a 1 => some (.P_1 (a + 2) 0)
  | .P_1 a (c + 2) =>
    if a % 2 = 0 then some (.P_1 (a + 3) c)
    else
      Nat.casesOn c none fun c =>
      Nat.casesOn c (some (.P_2 (a / 2) 1 0)) fun d =>
      some (.P_2 (a / 2) 2 d)
  | .P_2 k m 1 => some (.P_2 k (m + 1) 0)
  | .P_2 0 m 0 => some (.P_1 0 (2 * m + 3))
  | .P_2 (k + 1) m 0 => some (.P_2 k 0 (2 * m + 3))
  | .P_2 0 m (d + 2) => some (.P_1 (2 * m + 4) d)
  | .P_2 (k + 1) m (d + 2) => some (.P_2 k (m + 2) d)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
inductive HighLevelState where
  /-- $P_1(a, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^c\,0^\infty$. -/
  | P_1 (a c : ℕ)

def highLevelStart : HighLevelState := .P_1 2 1

def toState : HighLevelState → State
  | .P_1 a c => .P_1 a c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalP2 (k c : ℕ) : HighLevelState :=
  if 2 * k ≤ c then
    if c ≤ 2 * k + 1 then .P_1 0 (2 * c + 3) else .P_1 (4 * k + 4) (c - 2 * k - 2)
  else evalP2 (k - c / 2 - 1) (2 * c + 3)
termination_by k
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .P_1 a 0 => some (.P_1 2 (a + 1))
  | .P_1 a 1 => some (.P_1 (a + 2) 0)
  | .P_1 a (c + 2) =>
    if a % 2 = 0 then some (.P_1 (a + 3) c)
    else if c = 0 then none
    else if c = 1 then some (evalP2 (a / 2) 1)
    else some (evalP2 (a / 2 + 1) c)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
inductive HighLevelState where
  | D (p : Bool) (a w : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D false 0 3

def toState : HighLevelState → State
  | .D p 0 w => .D_1_0_odd (if p then 2 else 1) w
  | .D p (a + 1) w => .D_1_succ_odd a (if p then 2 else 1) w

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def drainJ1 (a w : ℕ) : Option HighLevelState :=
  let m := w / 2
  if a ≥ m + 2 then some (.D false (a - m - 2) (2 * w + 7))
  else if a = m + 1 then some (.D true 1 (2 * w + 3))
  else if a = m then some (.D true 1 (2 * w + 2))
  else if w = 2 * a + 2 then none
  else if w ≤ 2 * a + 5 then some (.D false (2 * a + 3) (2 * w - 4 * a - 5))
  else drainJ1 (2 * a + 4) (w - 2 * a - 6)
termination_by w
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .D false a w =>
    let m := w / 2
    if a ≥ m + 2 then some (.D false (a - m - 2) (2 * w + 5))
    else if a = m + 1 then some (.D true 1 (2 * w + 1))
    else if a = m then some (.D true 1 (2 * w))
    else if w = 2 * a + 2 then none
    else if w ≤ 2 * a + 5 then some (.D false (2 * a + 2) (2 * w - 4 * a - 5))
    else drainJ1 (2 * a + 3) (w - 2 * a - 6)
  | .D true a w => drainJ1 a w

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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

inductive HighLevelState where
  | C (a : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 3

def toState : HighLevelState → State
  | .C a => .C1 a

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def evalD0 (b c : ℕ) : Option HighLevelState :=
  let k := min (b / 2) c
  let a1 := 2 * k
  let b1 := b - 2 * k
  let c1 := c - k
  if c1 > 0 then
    if b1 = 0 then some (.C (4 * a1 + 2 * c1 + 11))
    else if c1 = 1 then some (.C (4 * a1 + 15))
    else some (.C (4 * a1 + 2 * c1 + 13))
  else if b1 = 0 then some (.C (4 * a1 + 11))
  else if b1 = 1 then some (.C (4 * a1 + 13))
  else if b1 = 2 then some (.C (4 * a1 + 17))
  else if b1 = 3 ∨ b1 = 4 then none
  else if b1 = 5 then some (.C (2 * a1 + 15))
  else evalD0 (b1 - 6) (a1 + 4)
termination_by b
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .C 0 => none
  | .C 1 => some (.C 9)
  | .C (a + 2) => evalD0 a 1

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry

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
  | .P_1 a b c => evalTapePattern pat_P1
      (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0)
  | .P_2 a b c => evalTapePattern pat_P2
      (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0)

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
inductive HighLevelState where
  /-- $P(b, c) := 0^\infty\,11\,(01)^b\,10101\,\mathrm{D}{>}\,(10)^c\,1111\,0^\infty$. -/
  | P (b c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .P 1 0

def toState : HighLevelState → State
  | .P b c => .P_2 2 b c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .P b c =>
    if c ≥ b + 3 then some (.P (2 * b + 4) (c - b - 3))
    else if c = b + 2 then none
    else if c = b + 1 then some (.P 0 (2 * b + 6))
    else if 3 * c + 1 ≤ b then some (.P (b - 3 * c) (4 * c + 6))
    else if (b - c) % 2 = 1 then some (.P 1 (4 * c + 6))
    else some (.P 0 (4 * c + 6))

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
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
  | .P_1 a b c d => evalTapePattern pat_P1 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else 0
  | .P_2 a b c => evalTapePattern pat_P2 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else 0
  | .P_3 a b c => evalTapePattern pat_P3 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else 0
  | .P_4 a b c d => evalTapePattern pat_P4 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else 0

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
inductive HighLevelState where
  /-- $P(a, d) := 0^\infty\,1111\,(01)^a\,1\,\mathrm{C}{>}\,011\,(01)^d\,1\,0^\infty$. -/
  | P (a d : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .P 1 1

def toState : HighLevelState → State
  | .P a d => .P_1 a 4 1 d

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def highLevelNext : HighLevelState → Option HighLevelState
  | .P a d =>
    if a ≥ d + 2 then some (.P (a - d - 2) (2 * d + 3))
    else if a = d + 1 then none
    else if a = d then some (.P (2 * a + 4) 1)
    else if 3 * a + 1 ≤ d then some (.P (4 * a + 6) (d - 3 * a))
    else if (d - a) % 2 = 0 then some (.P (4 * a + 6) 2)
    else some (.P (4 * a + 6) 1)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD

namespace M_1RB0LB0RC_2LC2LA1RA_1RA1LCHHH
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB0LB0RC_2LC2LA1RA_1RA1LC---"

abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

inductive State where
  | A (a c : ℕ)
  deriving DecidableEq, Repr

def start : State := .A 1 1

def encode : State → Cfg (Fin 3) (Fin 3)
  | .A a c =>
    Cfg.headRight ThreeState.A
      (ListBlank.append (([1, 0] : List (Fin 3)) ^ c) default)
      (ListBlank.append (([1] : List (Fin 3)) ^ a) (ListBlank.cons 2 default))

def next : State → Option State
  | .A a c =>
    if a ≤ c then
      if a % 2 = 0 then
        if c % 2 = 0 then none
        else some (.A 1 (a / 2 + c + 2))
      else if c % 2 = 0 then
        some (.A (3 * a) (c - a + 4))
      else
        some (.A (3 * a + 2) (c - a + 1))
    else if c % 4 = 0 ∨ c % 4 = 2 then
      some (.A (a - c - 1) (3 * (c / 2) + 2))
    else if c % 4 = 1 then
      if a = c + 1 then none
      else some (.A (a - c - 2) (3 * (c / 2) + 5))
    else if a = c + 1 then
      none
    else if a = c + 2 then
      some (.A (3 * c + 8) 1)
    else if a = c + 3 then
      none
    else
      some (.A (a - c - 4) (3 * (c / 2) + 8))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

def pat_A : TapePattern (Fin 3) (Fin 3) :=
  { left := .rep [1, 0] 1 .default
    head := some ThreeState.A
    right := .rep [1] 0 (.sym 2 .default) }

def ps : TapePatternSet (Fin 3) (Fin 3) :=
  [(pat_A, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB0LB0RC_2LC2LA1RA_1RA1LCHHH

namespace M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB1LB2LC_1LA2RB1RB_---0LA2LA"

abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

inductive State where
  | W (w : List Bool)
  deriving DecidableEq, Repr

inductive Carry where
  | ca
  | cb
  | cc
  | cd
  | ce
  | cf
  deriving DecidableEq, Repr

def pass : Carry → List Bool → Option (List Bool)
  | .ca, [] => some [true]
  | .ca, false :: zs => List.cons true <$> pass .cc zs
  | .ca, true :: zs => List.cons false <$> pass .cb zs
  | .cb, [] => some [false, true]
  | .cb, false :: zs => some (true :: zs)
  | .cb, true :: zs => some (false :: zs)
  | .cc, [] => none
  | .cc, false :: zs => List.cons true <$> pass .ca zs
  | .cc, true :: zs => List.cons false <$> pass .cd zs
  | .cd, [] => some [false, false, true]
  | .cd, false :: zs => List.cons false <$> pass .ce zs
  | .cd, true :: zs => List.cons true <$> pass .cf zs
  | .ce, [] => none
  | .ce, false :: zs => List.cons false <$> pass .ca zs
  | .ce, true :: zs => List.cons true <$> pass .cd zs
  | .cf, [] => some [true, false, false, true]
  | .cf, false :: zs => List.cons false <$> pass .cd zs
  | .cf, true :: zs => List.cons true <$> pass .ca zs

def start : State := .W [true]

def encode : State → Cfg (Fin 3) (Fin 3)
  | .W w =>
      Cfg.headRight ThreeState.B
        (ListBlank.append (w.map fun b => if b then 1 else 2) default) default

def next : State → Option State
  | .W w => (fun w' => .W (false :: w')) <$> pass .ca w

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

def pat_W : StackPattern (Fin 3) (Fin 3) :=
  { left := [.word [[2], [1]] 0]
    head := some ThreeState.B
    right := [] }

def ps : StackPatternSet (Fin 3) (Fin 3) :=
  [(pat_W, .true)]

theorem is_closed_stack_pattern_set : IsClosedStackPatternSet target ps := by sorry

theorem has_stacked_collatz_reduction : HasStackedCollatzReduction target := by sorry
end M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA

namespace WilyCoyote

inductive State where
  | W (w : List Bool)
  deriving DecidableEq, Repr

inductive WilyMode where
  | s0
  | s1
  | s2
  | s3
  deriving DecidableEq, Repr

def wilyPass : WilyMode → List Bool → Option (List Bool)
  | .s0, [] => some [false]
  | .s0, false :: xs => List.cons true <$> wilyPass .s1 xs
  | .s0, true :: xs => List.cons false <$> wilyPass .s2 xs
  | .s1, [] => none
  | .s1, false :: xs => List.cons true <$> wilyPass .s3 xs
  | .s1, true :: xs => List.cons false <$> wilyPass .s0 xs
  | .s2, [] => some [true, true, false, false]
  | .s2, false :: xs => List.cons false <$> wilyPass .s2 xs
  | .s2, true :: xs => List.cons true <$> wilyPass .s1 xs
  | .s3, [] => some [false, false]
  | .s3, b :: xs => some ((!b) :: xs)

def start : State := .W [false, false]

def encode : State → Cfg (Fin 3) (Fin 3)
  | .W w =>
      Cfg.headRight ThreeState.A default
        (ListBlank.cons 0 (ListBlank.append (w.map fun b => if b then 1 else 2) default))

def next : State → Option State
  | .W w => (fun w' => .W (false :: w')) <$> wilyPass .s0 w

def pat_W : StackPattern (Fin 3) (Fin 3) :=
  { left := []
    head := some ThreeState.A
    right := [.sym 0, .word [[2], [1]] 0] }

def ps : StackPatternSet (Fin 3) (Fin 3) :=
  [(pat_W, .true)]

end WilyCoyote

namespace M_1RB2LA1LA_2LA0RA2RC_HHH0LC2RA
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2LA1LA_2LA0RA2RC_---0LC2RA"

abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

abbrev State := WilyCoyote.State
abbrev WilyMode := WilyCoyote.WilyMode
abbrev wilyPass := WilyCoyote.wilyPass
abbrev start : State := WilyCoyote.start
abbrev encode : State → Cfg (Fin 3) (Fin 3) := WilyCoyote.encode
abbrev next : State → Option State := WilyCoyote.next
abbrev pat_W : StackPattern (Fin 3) (Fin 3) := WilyCoyote.pat_W
abbrev ps : StackPatternSet (Fin 3) (Fin 3) := WilyCoyote.ps

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

theorem is_closed_stack_pattern_set : IsClosedStackPatternSet target ps := by sorry

theorem has_stacked_collatz_reduction : HasStackedCollatzReduction target := by sorry
end M_1RB2LA1LA_2LA0RA2RC_HHH0LC2RA

namespace M_1RB2LA1LA_2LA0RA2RC_HHH1RB2RA
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2LA1LA_2LA0RA2RC_---1RB2RA"

abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

abbrev State := WilyCoyote.State
abbrev WilyMode := WilyCoyote.WilyMode
abbrev wilyPass := WilyCoyote.wilyPass
abbrev start : State := WilyCoyote.start
abbrev encode : State → Cfg (Fin 3) (Fin 3) := WilyCoyote.encode
abbrev next : State → Option State := WilyCoyote.next
abbrev pat_W : StackPattern (Fin 3) (Fin 3) := WilyCoyote.pat_W
abbrev ps : StackPatternSet (Fin 3) (Fin 3) := WilyCoyote.ps

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

theorem is_closed_stack_pattern_set : IsClosedStackPatternSet target ps := by sorry

theorem has_stacked_collatz_reduction : HasStackedCollatzReduction target := by sorry
end M_1RB2LA1LA_2LA0RA2RC_HHH1RB2RA

namespace M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2LC1RC_2LC---2RB_2LA0LB0RA"

abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

inductive State where
  | A (a c : ℕ)
  deriving DecidableEq, Repr

def start : State := .A 0 1

def encode : State → Cfg (Fin 3) (Fin 3)
  | .A a c =>
    Cfg.headLeft ThreeState.C
      (ListBlank.append (([2] : List (Fin 3)) ^ a) (ListBlank.append [1] default))
      (ListBlank.append (([2, 0] : List (Fin 3)) ^ c) default)

def next : State → Option State
  | .A a c =>
    if a ≤ c then
      if a % 2 = 0 then
        if c % 2 = 0 then none
        else some (.A 1 (a / 2 + c + 2))
      else if c % 2 = 0 then
        some (.A (3 * a) (c - a + 4))
      else
        some (.A (3 * a + 2) (c - a + 1))
    else if c % 4 = 0 ∨ c % 4 = 2 then
      some (.A (a - c - 1) (3 * (c / 2) + 2))
    else if c % 4 = 1 then
      if a = c + 1 then none
      else some (.A (a - c - 2) (3 * (c / 2) + 5))
    else if a = c + 1 then
      none
    else if a = c + 2 then
      some (.A (3 * c + 8) 1)
    else if a = c + 3 then
      none
    else
      some (.A (a - c - 4) (3 * (c / 2) + 8))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

def pat_A0 : TapePattern (Fin 3) (Fin 3) :=
  { left := .default
    head := some ThreeState.C
    right := .sym 1 (.rep [2, 0] 1 .default) }

def pat_AS : TapePattern (Fin 3) (Fin 3) :=
  { left := .rep [2] 0 (.sym 1 .default)
    head := some ThreeState.C
    right := .sym 2 (.rep [2, 0] 1 .default) }

def ps : TapePatternSet (Fin 3) (Fin 3) :=
  [(pat_A0, .true), (pat_AS, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA

namespace M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2RA1LC_2LC1RB2RB_---2LA1LA"

abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

inductive State where
  | A (a b c : ℕ)
  deriving DecidableEq, Repr

def start : State := .A 2 0 0

def encode : State → Cfg (Fin 3) (Fin 3)
  | .A a b c =>
      Cfg.headLeft ThreeState.A
        (ListBlank.append (([1] : List (Fin 3)) ^ (2 * b + 2))
          (ListBlank.append (([2, 1] : List (Fin 3)) ^ a) default))
        (ListBlank.append (([1] : List (Fin 3)) ^ (2 * (c + 2))) default)

def next : State → Option State
  | .A a b c =>
      let q := b / 6
      let r := b % 6
      if r = 0 then
        some (.A (a + 1) (8 * q + c) 1)
      else if r = 1 then
        match a with
        | 0 => none
        | a' + 1 => some (.A a' (8 * q + c + 4) 0)
      else if r = 2 then
        some (.A a (8 * q + c + 2) 3)
      else if r = 3 then
        some (.A (a + 1) (8 * q + c + 4) 0)
      else if r = 4 then
        some (.A a (8 * q + c + 6) 1)
      else
        some (.A a (8 * q + c + 8) 0)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

def pat_A : TapePattern (Fin 3) (Fin 3) :=
  { left := .sym 1 (.rep [1, 1] 1 (.rep [2, 1] 0 .default))
    head := some ThreeState.A
    right := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 2 .default))))) }

def ps : TapePatternSet (Fin 3) (Fin 3) :=
  [(pat_A, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry

theorem has_collatz_reduction : HasCollatzReduction target := by sorry
end M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA

namespace Stack
def encStack : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s => ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.cons 0 (encStack s))

def encStack2 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.cons 0 (ListBlank.cons 0 (encStack2 s)))

def encRun : List ℕ → ListBlank (Fin 2)
  | [] => default
  | k :: xs => ListBlank.append (([0] : List (Fin 2)) ^ k) (ListBlank.cons 1 (encRun xs))

def incRun : List ℕ → List ℕ
  | [] => []
  | k :: xs => (k + 1) :: xs

def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | a :: s => (a + 1) :: s

def bumpHeadBy : ℕ → List ℕ → List ℕ
  | 0, s => s
  | k + 1, s => bumpHeadBy k (bumpHead s)
end Stack

open Stack

namespace M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_odometer_reduction : HasOdometerReduction target := by sorry
end M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH

namespace M_1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RDHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RDHHH

namespace M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_transducer_reduction : HasTransducerReduction target := by sorry
end M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA

namespace M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_odometer_reduction : HasOdometerReduction target := by sorry
end M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB

namespace M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive State where
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

def transferD (a : ℕ) (L R : List ℕ) : State :=
  let p := R.foldl (fun p d => (d, p.1 :: p.2)) (a, L)
  .C p.1 p.2 [0]

def start : State := .C 0 [0] [1]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a L R => Cfg.headRight C (encStack (a :: L)) (ListBlank.cons 0 (encStack R))

def next : State → Option State
  | .C 0 [] _ => none
  | .C 0 (b :: L) R => some (transferD b L (bumpHead (bumpHead R)))
  | .C 1 [] R => some (.C 0 [] (0 :: R))
  | .C 1 (b :: L) R => some (.C (b + 1) L (0 :: R))
  | .C (a + 2) L R => some (.C a (bumpHead L) (bumpHead R))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | C (a : ℕ) (L : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 3 [0]

def toState : HighLevelState → State
  | .C a L => .C a L [0]

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def transferHL (a : ℕ) (L R : List ℕ) : HighLevelState :=
  let p := R.foldl (fun p d => (d, p.1 :: p.2)) (a, L)
  .C p.1 p.2

def stepEpoch (a : ℕ) (L R : List ℕ) : Option HighLevelState :=
  let k := a / 2
  let R₁ := bumpHeadBy k R
  if L = [] then
    if a ≤ 1 then none
    else if a % 2 = 0 then some (transferHL (k - 1) [] (bumpHead (bumpHead R₁)))
    else stepEpoch k [] (0 :: R₁)
  else
    let b := L.headD 0
    let L' := L.tail
    if a % 2 = 0 then some (transferHL (b + k) L' (bumpHead (bumpHead R₁)))
    else stepEpoch (b + k + 1) L' (0 :: R₁)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  · omega
  · cases L with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp +zetaDelta only [List.length_cons]
      omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .C a L => stepEpoch a L [0]

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

namespace M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive RightMode where
  | ar
  | br
  | cr
  deriving DecidableEq, Repr

inductive State where
  | E (L R : List ℕ)
  deriving DecidableEq, Repr

def sweepElem (stepRt : RightMode → List ℕ → State) :
    ℕ → RightMode → List ℕ → List ℕ → State
  | 0, .ar, L, Rt => .E L (incRun Rt)
  | 0, .br, L, _ => stepRt .ar (incRun L)
  | 0, .cr, L, _ => stepRt .br (0 :: L)
  | d + 1, .ar, L, Rt => sweepElem stepRt d .br (0 :: L) Rt
  | d + 1, .br, L, Rt => sweepElem stepRt d .cr (incRun L) Rt
  | 1, .cr, L, _ => stepRt .br (1 :: L)
  | d + 2, .cr, L, Rt => .E L ((d + 2) :: Rt)

def sweepRight : RightMode → List ℕ → List ℕ → State
  | .ar, L, [] => .E (1 :: L) []
  | .br, L, [] => .E (incRun L) []
  | .cr, L, [] => .E L []
  | m, L, d :: Rt => sweepElem (fun m' L' => sweepRight m' L' Rt) d m L Rt

def sweepFL : List ℕ → List ℕ → State
  | [], R => sweepRight .ar [] (2 :: R)
  | 0 :: Lt, R => sweepFL Lt (0 :: R)
  | 1 :: Lt, R => sweepRight .br (incRun Lt) (0 :: R)
  | 2 :: Lt, R => .E Lt (2 :: R)
  | (a + 3) :: Lt, R => sweepRight .ar (a :: Lt) (2 :: R)

def start : State := .E [1] []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E L R => Cfg.headLeft SixState.E (encRun L) (encRun R)

def next : State → Option State
  | .E [] R => some (sweepFL [] (0 :: R))
  | .E (0 :: _) _ => none
  | .E ((a + 1) :: Lt) R => some (sweepFL (a :: Lt) (0 :: R))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

namespace M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def bump2 (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (1, []) fun b xs => (b + 2, xs)

def d0Out : List ℕ → List ℕ
  | [] => [0]
  | [d] => [d + 1]
  | d :: r :: s => (r + d + 2) :: s

inductive State where
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

def scanOnes (a : ℕ) (L : List ℕ) : List ℕ → Option State
  | [] => none
  | [0] =>
    let (b, L') := bump2 L
    some (.C b L' [a + 2, 0])
  | 0 :: r :: R =>
    let (b, L') := bump2 L
    some (.C b L' ((a + r + 3) :: d0Out R))
  | 1 :: R => scanOnes 0 (a :: L) R
  | (r + 2) :: R => some (.C (a + 2) L (r :: d0Out R))

def start : State := .C 1 [] [0, 0]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a L R => Cfg.headRight C (encStack2 (a :: L)) (ListBlank.cons 0 (encStack R))

def next : State → Option State
  | .C a L R => scanOnes a L R

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 1 [] [0, 0]

def toState : HighLevelState → State
  | .C a L R => .C a L R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def d0Iter (k : ℕ) (R : List ℕ) : List ℕ :=
  if k = 0 then R else d0Iter (k - 1) (d0Out R)
termination_by k
decreasing_by omega

def scanEpoch (a : ℕ) (L R : List ℕ) : Option HighLevelState :=
  if R = [] then
    none
  else
    let r₀ := R.headD 0
    let R' := R.tail
    let k := r₀ / 2
    let Rk := d0Iter k R'
    let a₁ := a + 2 * k
    if r₀ % 2 = 0 then
      let p := bump2 L
      List.casesOn Rk (some (.C p.1 p.2 [a₁ + 2, 0])) fun r R'' =>
        some (.C p.1 p.2 ((a₁ + r + 3) :: d0Out R''))
    else if Rk.length - 1 < R'.length ∨
        (R'.length = 0 ∧ Rk.length ≤ 1 ∧ Rk.headD 0 < r₀) then
      scanEpoch 0 (a₁ :: L) Rk
    else
      none
termination_by (R.length - 1, R.headD 0)
decreasing_by
  simp_wf
  cases R with
  | nil => contradiction
  | cons head tail =>
    simp +zetaDelta only [Prod.lex_def, List.headD_eq_head?, List.head?_cons, Option.getD_some,
      List.tail_cons, List.length_cons] at *
    omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .C a L R => scanEpoch a L R

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB

namespace M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive State where
  | C (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ)
  | F (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def start : State := .F 1 0 [] 0 []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b L r R =>
      Cfg.headRight C (encStack ((a + 1) :: b :: L))
        (ListBlank.cons 0
          (ListBlank.append (([1] : List (Fin 2)) ^ r) (ListBlank.cons 0 (encStack R))))
  | .F a b L r R =>
      Cfg.headRight F (encStack (a :: b :: L))
        (ListBlank.cons 0
          (ListBlank.append (([1] : List (Fin 2)) ^ r) (ListBlank.cons 0 (encStack R))))

def next : State → Option State
  | .C 0 0 _ _ _ => none
  | .C 0 (b + 1) L r R =>
      if b % 2 = 0 then
        List.casesOn L (some (.F (b + 3) 0 [] r R))
          fun c L' => some (.F (b + 3) (c + 1) L' r R)
      else
        List.casesOn L (some (.C (2 * (b / 2)) 0 [] 0 ((r + 1) :: R)))
          fun c L' => some (.C (2 * (b / 2)) (c + 1) L' 0 ((r + 1) :: R))
  | .C (a + 1) b L r R => some (.F a b L 0 (r :: R))
  | .F a b L r R =>
      let a' := a + 2 * (r / 2)
      if r % 2 = 0 then
        match R with
        | [] => some (.C (a' + 2) b L 0 [])
        | 0 :: [] => some (.F 0 (b + 1) L a' [])
        | 0 :: e :: R' =>
            if a' % 2 = 0 then
              some (.F (a' + 3) (b + 1) L e R')
            else
              some (.C (2 * (a' / 2)) (b + 1) L 0 ((e + 1) :: R'))
        | (d + 1) :: R' => some (.F 0 (b + 1) L a' (d :: R'))
      else
        List.casesOn R (some (.C a' b L 0 [0]))
          fun e R' => some (.F 0 (a' + 1) (b :: L) e R')

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | F (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .F 1 0 [] 0 []

def toState : HighLevelState → State
  | .F a b L r R => .F a b L r R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def exitC (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) : Option HighLevelState :=
  List.rec
    (fun a b r R =>
      if a ≥ 1 then some (.F (a - 1) b [] 0 (r :: R))
      else if b = 0 then none
      else
        let b' := b - 1
        if b' % 2 = 0 then some (.F (b' + 3) 0 [] r R)
        else if b' = 1 then none
        else some (.F (2 * (b' / 2) - 1) 0 [] 0 (0 :: (r + 1) :: R)))
    (fun c L' ih a b r R =>
      if a ≥ 1 then some (.F (a - 1) b (c :: L') 0 (r :: R))
      else if b = 0 then none
      else
        let b' := b - 1
        if b' % 2 = 0 then some (.F (b' + 3) (c + 1) L' r R)
        else if b' = 1 then ih 0 (c + 1) 0 ((r + 1) :: R)
        else some (.F (2 * (b' / 2) - 1) (c + 1) L' 0 (0 :: (r + 1) :: R)))
    L a b r R

def highLevelNext : HighLevelState → Option HighLevelState
  | .F a b L r R =>
    let a' := a + 2 * (r / 2)
    if r % 2 = 0 then
      List.casesOn R (exitC (a' + 2) b L 0 []) fun d R' =>
        if d = 0 then
          List.casesOn R' (some (.F 0 (b + 1) L a' [])) fun e R'' =>
            if a' % 2 = 0 then
              some (.F (a' + 3) (b + 1) L e R'')
            else
              exitC (2 * (a' / 2)) (b + 1) L 0 ((e + 1) :: R'')
        else
          some (.F 0 (b + 1) L a' ((d - 1) :: R'))
    else
      List.casesOn R (exitC a' b L 0 [0]) fun e R' =>
        some (.F 0 (a' + 1) (b :: L) e R')

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA

namespace M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def encStack : List (ℕ × Bool) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: xs =>
    ListBlank.append (([0] : List (Fin 2)) ^ (a + 1))
      (ListBlank.append (if b then [1, 1] else [1]) (encStack xs))

def incHead : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => []
  | (a, b) :: xs => (a + 1, b) :: xs

inductive RetMode where
  | r01
  | r10
  | r11
  | r21
  deriving DecidableEq, Repr

def unwind01 : RetMode × List (ℕ × Bool) → RetMode × List (ℕ × Bool)
  | (.r01, R') => (.r01, (0, false) :: R')
  | (.r10, R') => (.r10, (0, false) :: R')
  | (.r11, R') => (.r10, (0, true) :: R')
  | (.r21, R') => (.r11, (0, false) :: incHead R')

def unwind111 : RetMode × List (ℕ × Bool) → RetMode × List (ℕ × Bool)
  | (.r01, R') => (.r01, (0, true) :: R')
  | (.r10, R') => (.r11, (0, false) :: R')
  | (.r11, R') => (.r11, (0, true) :: R')
  | (.r21, R') => (.r21, (0, true) :: R')

def unwind11 : RetMode × List (ℕ × Bool) → RetMode × List (ℕ × Bool)
  | (.r01, R') => (.r21, R')
  | (.r10, R') => (.r01, (0, false) :: R')
  | (.r11, R') => (.r01, (0, true) :: R')
  | (.r21, R') => (.r11, (0, true) :: R')

def bounceR : List (ℕ × Bool) → Option (RetMode × List (ℕ × Bool))
  | [] => some (.r11, [])
  | (0, false) :: R₁ => unwind01 <$> bounceR R₁
  | (0, true) :: R₁ => some (.r01, incHead R₁)
  | (1, false) :: R₁ => unwind111 <$> bounceR R₁
  | (1, true) :: R₁ => some (.r01, (0, false) :: R₁)
  | (2, false) :: R₁ => (fun p => unwind11 (unwind01 p)) <$> bounceR R₁
  | (2, true) :: R₁ => some (.r21, incHead R₁)
  | (3, _) :: _ => none
  | (d + 4, b) :: R₁ => some (.r11, (d + 1, b) :: R₁)

inductive State where
  | E (L R : List (ℕ × Bool))
  deriving DecidableEq, Repr

def closeRet : List (ℕ × Bool) → RetMode × List (ℕ × Bool) → State
  | L, (.r01, R') => .E L ((0, true) :: R')
  | [], (.r10, R') => .E [(0, false)] ((0, false) :: R')
  | (0, false) :: L₁, (.r10, R') => .E ((0, true) :: L₁) ((0, false) :: R')
  | (0, true) :: L₁, (.r10, R') => .E (incHead L₁) ((0, true) :: (0, false) :: R')
  | (a + 1, bL) :: L₁, (.r10, R') => .E ((0, false) :: (a, bL) :: L₁) ((0, false) :: R')
  | [], (.r11, R') => .E [(0, false)] ((0, true) :: R')
  | (0, false) :: L₁, (.r11, R') => .E ((0, true) :: L₁) ((0, true) :: R')
  | (0, true) :: L₁, (.r11, R') => .E (incHead L₁) ((0, true) :: (0, true) :: R')
  | (a + 1, bL) :: L₁, (.r11, R') => .E ((0, false) :: (a, bL) :: L₁) ((0, true) :: R')
  | [], (.r21, R') => .E [(0, true)] ((0, true) :: R')
  | (0, false) :: L₁, (.r21, R') => .E (incHead L₁) ((0, true) :: (0, true) :: R')
  | (0, true) :: L₁, (.r21, R') => .E ((0, false) :: L₁) ((0, true) :: (0, true) :: R')
  | (a + 1, bL) :: L₁, (.r21, R') => .E ((0, true) :: (a, bL) :: L₁) ((0, true) :: R')

def stepZero : List (ℕ × Bool) → Bool → List (ℕ × Bool) → State
  | [], false, R₁ => .E [] ((1, false) :: incHead R₁)
  | [], true, R₁ => .E [] ((1, false) :: (0, false) :: R₁)
  | (0, false) :: L₁, b, R₁ => .E L₁ ((0, false) :: (0, b) :: R₁)
  | (0, true) :: L₁, b, R₁ => .E L₁ ((1, false) :: (0, b) :: R₁)
  | (1, false) :: L₁, false, R₁ => .E (incHead L₁) ((0, true) :: incHead R₁)
  | (1, false) :: L₁, true, R₁ => .E (incHead L₁) ((0, true) :: (0, false) :: R₁)
  | (1, true) :: L₁, false, R₁ => .E ((0, false) :: L₁) ((0, true) :: incHead R₁)
  | (1, true) :: L₁, true, R₁ => .E ((0, false) :: L₁) ((0, true) :: (0, false) :: R₁)
  | (a + 2, bL) :: L₁, false, R₁ => .E ((a, bL) :: L₁) ((1, false) :: incHead R₁)
  | (a + 2, bL) :: L₁, true, R₁ => .E ((a, bL) :: L₁) ((1, false) :: (0, false) :: R₁)

def start : State := .E [(1, false)] [(0, false)]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E L R => Cfg.headRight SixState.E (encStack L).tail (encStack R).tail

def next : State → Option State
  | .E L [] => some (closeRet L (.r11, []))
  | .E L ((0, b) :: R₁) => some (stepZero L b R₁)
  | .E L ((d + 1, b) :: R₁) => closeRet L <$> bounceR ((d, b) :: R₁)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | E (R : List (ℕ × Bool))
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .E [(0, true)]

def toState : HighLevelState → State
  | .E R => .E [] R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def exitRet : RetMode × List (ℕ × Bool) → HighLevelState
  | (.r01, R') => .E ((0, true) :: R')
  | (.r10, R') => .E ((0, false) :: (0, false) :: R')
  | (.r11, R') => .E ((0, false) :: (0, true) :: R')
  | (.r21, R') => .E ((1, false) :: (0, true) :: R')

def highLevelNext : HighLevelState → Option HighLevelState
  | .E [] => some (.E [(0, false), (0, true)])
  | .E ((d, b) :: R₁) =>
    Nat.casesOn d
      (some (.E ((1, false) :: (if b then (0, false) :: R₁ else incHead R₁))))
      fun d' => exitRet <$> bounceR ((d', b) :: R₁)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC

namespace M_1RB0RE_0RCHHH_1LD1LE_1LE1LD_1RF0LC_1RA1RF
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB0RE_0RCHHH_1LD1LE_1LE1LD_1RF0LC_1RA1RF

namespace M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH

namespace M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def encStack (s : List ℕ) : ListBlank (Fin 2) :=
  List.rec default
    (fun a _ ih =>
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 1)) (ListBlank.cons 0 ih))
    s

def bounceRight : ℕ → List ℕ → List ℕ
  | 0, [] => [0, 0]
  | 0, d :: R => (d + 1) :: R
  | b + 1, R => 0 :: bounceRight b R

inductive State where
  | B (L R : List ℕ)
  deriving DecidableEq, Repr

def scanZeros (a : ℕ) (L : List ℕ) : List ℕ → Option State
  | [] => none
  | [0] => some (.B [] (L.reverse ++ [a + 2, 0]))
  | 0 :: 0 :: R => scanZeros (a + 2) L R
  | 0 :: (b + 1) :: R => some (.B ((a + 2) :: L) (b :: R))
  | (b + 1) :: R => some (.B ((a + 1) :: L) (bounceRight b R))

def start : State := .B [] [0, 1]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .B L R => Cfg.headRight B (ListBlank.cons 0 (encStack L)) (encStack R)

def next : State → Option State
  | .B L [] => some (.B [] (L.reverse ++ [0, 0]))
  | .B L (d :: R) => scanZeros 0 (List.replicate d 0 ++ L) R

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | B (R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .B [0, 1]

def toState : HighLevelState → State
  | .B R => .B [] R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def peelZeroPairs (a : ℕ) : List ℕ → ℕ × List ℕ
  | d₁ :: d₂ :: R => if d₁ = 0 ∧ d₂ = 0 then peelZeroPairs (a + 2) R else (a, d₁ :: d₂ :: R)
  | R => (a, R)

def scanEpoch (L R : List ℕ) : Option HighLevelState :=
  if R = [] then
    some (.B (L.reverse ++ [0, 0]))
  else
    let d := R.headD 0
    let R₁ := R.tail
    let L₁ := List.replicate d 0 ++ L
    let p := peelZeroPairs 0 R₁
    List.casesOn (motive := fun _ => Option HighLevelState) p.2 none fun c R₃ =>
      if c = 0 then
        List.casesOn (motive := fun _ => Option HighLevelState) R₃
          (some (.B (L₁.reverse ++ [p.1 + 2, 0]))) fun e R₄ =>
            if ((e - 1) :: R₄).sum + ((e - 1) :: R₄).length <
                (d :: R₁).sum + (d :: R₁).length then
              scanEpoch ((p.1 + 2) :: L₁) ((e - 1) :: R₄)
            else none
      else
        if (bounceRight (c - 1) R₃).sum + (bounceRight (c - 1) R₃).length <
            (d :: R₁).sum + (d :: R₁).length then
          scanEpoch ((p.1 + 1) :: L₁) (bounceRight (c - 1) R₃)
        else none
termination_by R.sum + R.length
decreasing_by
  all_goals simp_wf
  all_goals
    cases R with
    | nil => contradiction
    | cons _ _ =>
      simp +zetaDelta only [List.headD_cons, List.tail_cons, List.sum_cons, List.length_cons] at *
      omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .B R => scanEpoch [] R

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA

namespace M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive State where
  | D (a b : ℕ) (L R : List ℕ)
  | E (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

def sweepD (a b : ℕ) (L R : List ℕ) : State :=
  let t := R.foldl (fun t d => (d, t.1, t.2.1 :: t.2.2)) (a, b, L)
  .D t.1 t.2.1 t.2.2 []

def start : State := .D 1 0 [] []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b L R =>
    Cfg.headRight D (encStack (a :: b :: L)) (ListBlank.cons 0 (encStack R))
  | .E a L R =>
    Cfg.headLeft E (ListBlank.append [1, 0] (encStack (a :: L))) (encStack R)

def next : State → Option State
  | .D a b L R =>
    let k := a / 2
    if a % 2 = 0 then
      List.casesOn R (some (.E (b + k) L [k]))
        fun d R' => some (.E (b + k) L ((d + k + 1) :: R'))
    else
      List.casesOn R (some (.D k (b + k + 2) (bumpHead L) []))
        fun d R' => some (sweepD (d + k + 1) (b + k + 2) (bumpHead L) R')
  | .E 0 [] _ => none
  | .E 0 (b :: L) R => some (.E b L (0 :: R))
  | .E 1 [] R => some (sweepD 0 1 [0] R)
  | .E 1 (b :: L) R => some (sweepD 0 (b + 2) (bumpHead L) R)
  | .E (a + 2) [] R => some (.D a 0 [] (0 :: R))
  | .E (a + 2) (b :: L) R => some (.D a (b + 1) L (0 :: R))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | D (a b : ℕ) (L : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .D 1 0 []

def toState : HighLevelState → State
  | .D a b L => .D a b L []

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def sweepDHL (a b : ℕ) (L R : List ℕ) : HighLevelState :=
  let t := R.foldl (fun t d => (d, t.1, t.2.1 :: t.2.2)) (a, b, L)
  .D t.1 t.2.1 t.2.2

def runE (a : ℕ) (L : List ℕ) (r₀ : ℕ) (R' : List ℕ) : Option HighLevelState :=
  if L = [] then
    if a = 0 then none
    else if a = 1 then some (sweepDHL 0 1 [0] (r₀ :: R'))
    else
      let a₂ := a - 2
      let k₂ := a₂ / 2
      if a₂ % 2 = 1 then some (sweepDHL (k₂ + 1) (k₂ + 2) [0] (r₀ :: R'))
      else runE k₂ [] (k₂ + 1) (r₀ :: R')
  else
    let b := L.headD 0
    let L' := L.tail
    if a = 0 then runE b L' 0 (r₀ :: R')
    else if a = 1 then some (sweepDHL 0 (b + 2) (bumpHead L') (r₀ :: R'))
    else
      let a₂ := a - 2
      let k₂ := a₂ / 2
      if a₂ % 2 = 1 then some (sweepDHL (k₂ + 1) (b + 1 + k₂ + 2) (bumpHead L') (r₀ :: R'))
      else runE (b + 1 + k₂) L' (k₂ + 1) (r₀ :: R')
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  · omega
  · cases L with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp +zetaDelta only [List.length_cons]
      omega
  · cases L with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp +zetaDelta only [List.length_cons]
      omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .D a b L =>
    let k := a / 2
    if a % 2 = 1 then some (.D k (b + k + 2) (bumpHead L))
    else runE (b + k) L k []

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA

namespace M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def encRight (s : List ℕ) : ListBlank (Fin 2) :=
  List.rec default
    (fun d _ ih =>
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [0, 0, 0] ih))
    s

def toLeft : List ℕ → ℕ → List ℕ
  | [], bot => [bot]
  | p :: pre, bot => (p + 1) :: toLeft pre bot

def bumpPosBy (k : ℕ) : List ℕ → ℕ → List ℕ × ℕ
  | [], bot => ([], bot + k)
  | p :: pre, bot => ((p + k) :: pre, bot)

def cOneTail : List ℕ → ℕ → List ℕ × ℕ
  | [], bot => ([bot + 1], 0)
  | p :: pre, bot =>
    let (pre', bot') := bumpPosBy 1 pre bot
    ((p + 2) :: pre', bot')

inductive State where
  | B (pre : List ℕ) (bot : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def drainPos (a : ℕ) (pre : List ℕ) (bot : ℕ) (R : List ℕ) : State :=
  let t := R.foldl
    (fun t r => let p := bumpPosBy 1 t.2.1 t.2.2; (r, t.1 :: p.1, p.2))
    (a, pre, bot)
  .B ((t.1 + 2) :: t.2.1) t.2.2 []

def peelOnes : List ℕ → ℕ → ℕ → List ℕ → Option State
  | [], 2, _, _ => none
  | [], 0, d, R => some (drainPos d [] 0 R)
  | [], 1, 0, R => some (.B [0, 0] 0 R)
  | [], 1, 1, R => some (.B [1, 0] 0 R)
  | [], 1, d + 2, R => some (drainPos d [0] 0 R)
  | [], b + 3, d + 1, R => some (drainPos d [b] 0 R)
  | [], b + 3, 0, R =>
    let m := b / 2
    let R₂ := bumpHeadBy m R
    if b % 2 = 1 then
      some (.B [1, 1] m R₂)
    else
      List.casesOn R₂ (some (.B [1, 0] m [])) fun r₂ R₂' => some (drainPos r₂ [m + 3] 1 R₂')
  | 0 :: pre, bot, 0, R =>
    let (pre₁, bot₁) := cOneTail pre bot
    some (.B (0 :: pre₁) bot₁ R)
  | 0 :: pre, bot, 1, R =>
    let (pre₁, bot₁) := cOneTail pre bot
    some (.B (1 :: pre₁) bot₁ R)
  | 0 :: pre, bot, d + 2, R =>
    let (pre₁, bot₁) := cOneTail pre bot
    some (drainPos d pre₁ bot₁ R)
  | 1 :: pre, bot, d, R => peelOnes pre bot 0 (d :: R)
  | (b + 2) :: pre, bot, d + 1, R =>
    let (pre₁, bot₁) := bumpPosBy 1 pre bot
    some (drainPos d (b :: pre₁) bot₁ R)
  | (b + 2) :: pre, bot, 0, R =>
    let m := b / 2
    let (pre₂, bot₂) := bumpPosBy m pre bot
    let R₂ := bumpHeadBy m R
    if b % 2 = 1 then
      let (pre₃, bot₃) := bumpPosBy 1 pre₂ bot₂
      some (.B (1 :: 1 :: pre₃) bot₃ R₂)
    else
      List.casesOn R₂
        (let (pre₃, bot₃) := bumpPosBy 1 pre₂ bot₂; some (.B (1 :: 0 :: pre₃) bot₃ []))
        fun r₂ R₂' =>
          some (List.casesOn pre₂ (drainPos r₂ [bot₂ + 4] 1 R₂') fun q qs =>
            let (pre₃, bot₃) := bumpPosBy 2 qs bot₂
            drainPos r₂ ((q + 5) :: pre₃) bot₃ R₂')

def start : State := .B [] 0 []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .B pre bot R => Cfg.headRight B (encStack (toLeft pre bot)) (ListBlank.cons 0 (encRight R))

def next : State → Option State
  | .B pre bot [] => peelOnes pre bot 0 []
  | .B pre bot (r :: R) => peelOnes pre bot (r + 1) R

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB

namespace M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF

namespace M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive DrainMode where
  | A
  | B
  | BR
  deriving DecidableEq, Repr

inductive State where
  | E (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def bounceBEmpty : ℕ → List ℕ → Option State
  | d, [] =>
    if d % 2 = 1 then none
    else some (.E 0 (List.replicate (d / 2 + 1) 0 ++ [1]) 0 [])
  | d, e :: R =>
    if d % 2 = 1 then some (.E 0 (List.replicate (d / 2) 0 ++ [1]) e R)
    else bounceBEmpty (e + d + 4) R

def drainLeft : DrainMode → List ℕ → ℕ → List ℕ → Option State
  | .A, [], d, R => bounceBEmpty (d + 1) R
  | .B, [], d, R => bounceBEmpty d R
  | .BR, [], d, R => some (.E 1 [] d R)
  | .A, a :: L, d, R =>
    drainLeft (if a % 2 = 0 then .A else .B) L (a + d + 2) R
  | .B, 0 :: L, d, R => drainLeft .BR L (d + 1) R
  | .B, (a + 1) :: L, d, R =>
    drainLeft (if a % 2 = 0 then .A else .B) L a ((d + 1) :: R)
  | .BR, 0 :: L, d, R => drainLeft .BR L 0 (d :: R)
  | .BR, (a + 1) :: L, d, R =>
    drainLeft (if a % 2 = 0 then .A else .B) L a (0 :: d :: R)

def start : State := .E 1 [] 0 []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a L d R => Cfg.headRight E (encStack (a :: L)) (ListBlank.cons 0 (encStack (d :: R)))

def next : State → Option State
  | .E a L 0 [] =>
    drainLeft (if (a + 3) % 2 = 0 then .A else .B) L (a + 3) [0]
  | .E a L 0 (e :: R) =>
    drainLeft (if a % 2 = 0 then .B else .A) L (a + e + 4) R
  | .E a L (d + 1) R =>
    if d % 2 = 0 then
      List.casesOn R none fun e R' =>
        if d / 2 = 0 then some (.E (a + 3) L e R')
        else some (.E 0 (List.replicate (d / 2 - 1) 0 ++ (a + 3) :: L) e R')
    else
      List.casesOn R
        (drainLeft .A (List.replicate (d / 2) 0 ++ (a + 3) :: L) 0 [0])
        fun e R' => drainLeft .A (List.replicate (d / 2) 0 ++ (a + 3) :: L) (e + 1) R'

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | E (k d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .E 2 0 []

def toState : HighLevelState → State
  | .E k d R => .E 0 (List.replicate k 0 ++ [1]) d R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def bounceBHL : ℕ → List ℕ → Option HighLevelState
  | d, [] =>
    if d % 2 = 1 then none
    else some (.E (d / 2 + 1) 0 [])
  | d, e :: R =>
    if d % 2 = 1 then some (.E (d / 2) e R)
    else bounceBHL (e + d + 4) R

def drainPre : DrainMode → List ℕ → ℕ → List ℕ → Option HighLevelState
  | .A, [], d, R => bounceBHL (d + 3) R
  | .B, [], d, R => some (.E 0 (d + 1) R)
  | .BR, [], d, R => some (.E 0 0 (d :: R))
  | .A, x :: Lpre, d, R =>
    drainPre (if x % 2 = 0 then .A else .B) Lpre (x + d + 2) R
  | .B, x :: Lpre, d, R =>
    if x = 0 then drainPre .BR Lpre (d + 1) R
    else drainPre (if (x - 1) % 2 = 0 then .A else .B) Lpre (x - 1) ((d + 1) :: R)
  | .BR, x :: Lpre, d, R =>
    if x = 0 then drainPre .BR Lpre 0 (d :: R)
    else drainPre (if (x - 1) % 2 = 0 then .A else .B) Lpre (x - 1) (0 :: d :: R)

def scanR (a : ℕ) (Lpre : List ℕ) (d : ℕ) (R : List ℕ) : Option HighLevelState :=
  List.rec (motive := fun _ => ℕ → List ℕ → ℕ → Option HighLevelState)
    (fun a Lpre d =>
      if d = 0 then
        drainPre (if (a + 3) % 2 = 0 then .A else .B) Lpre (a + 3) [0]
      else if (d - 1) % 2 = 0 then
        none
      else
        drainPre .A (List.replicate ((d - 1) / 2) 0 ++ (a + 3) :: Lpre) 0 [0])
    (fun e R' ih a Lpre d =>
      if d = 0 then
        drainPre (if a % 2 = 0 then .B else .A) Lpre (a + e + 4) R'
      else if (d - 1) % 2 = 0 then
        if (d - 1) / 2 = 0 then
          ih (a + 3) Lpre e
        else
          ih 0 (List.replicate ((d - 1) / 2 - 1) 0 ++ (a + 3) :: Lpre) e
      else
        drainPre .A (List.replicate ((d - 1) / 2) 0 ++ (a + 3) :: Lpre) (e + 1) R')
    R a Lpre d

def highLevelNext : HighLevelState → Option HighLevelState
  | .E k d R => scanR 0 (List.replicate k 0) d R

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD

namespace M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def bump2 (s : List ℕ) : List ℕ :=
  List.casesOn s [1] fun a xs => (a + 2) :: xs

def bump2NE (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (1, []) fun a xs => (a + 2, xs)

def add3 (k : ℕ) (L : List ℕ) : List ℕ :=
  ((fun s => bumpHead (bumpHead (bumpHead s)))^[k]) L

def cSweepTail : List ℕ → ℕ → List ℕ → List ℕ
  | [], a₀, R =>
    let R₁ := List.replicate (a₀ / 2) 0 ++ R
    if a₀ % 2 = 0 then R₁ else bump2 R₁
  | a₁ :: Lp, a₀, R =>
    let R₂ := bump2 (List.replicate (a₀ / 2) 0 ++ R)
    cSweepTail Lp (if a₀ % 2 = 0 then a₁ else a₁ + 1) R₂

inductive State where
  | B (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def runCR1 (b : ℕ) (L : List ℕ) : List ℕ → Option State
  | [] => some (.B [] 0 (cSweepTail L b [1]))
  | 0 :: R =>
    let p := bump2NE R
    some (.B ((b + 1) :: L) p.1 p.2)
  | 1 :: R => runCR1 1 (b :: L) R
  | [2] => none
  | 2 :: e :: R => some (.B (0 :: 1 :: b :: L) e R)
  | (d + 3) :: R => some (.B (2 :: b :: L) d R)

def start : State := .B [0] 0 []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .B L d R => Cfg.headRight B (encStack L) (ListBlank.cons 0 (encStack (d :: R)))

def next : State → Option State
  | .B L d R =>
    let L₁ := add3 (d / 3) L
    if d % 3 = 0 then
      List.casesOn L₁
        (let p := bump2NE R; some (.B [0] p.1 p.2))
        fun a₀ Lp => some (.B [] 0 (cSweepTail Lp a₀ (bump2 R)))
    else if d % 3 = 1 then
      let p := bump2NE L₁
      runCR1 p.1 p.2 R
    else
      List.casesOn R none fun e R' => some (.B (0 :: bump2 L₁) e R')

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | B (R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .B [1]

def toState : HighLevelState → State
  | .B R => .B [] 0 R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def scanHL : Bool → ℕ → List ℕ → ℕ → List ℕ → Option HighLevelState
  | true, a, Lp, _, [] => some (.B (cSweepTail Lp a [1]))
  | true, a, Lp, _, r :: R' =>
    if r = 0 then
      if R' = [] then scanHL false (a + 1) Lp 1 []
      else scanHL false (a + 1) Lp (R'.headD 0 + 2) R'.tail
    else if r = 1 then
      scanHL true 1 (a :: Lp) 0 R'
    else if r = 2 then
      if R' = [] then none
      else scanHL false 0 (1 :: a :: Lp) (R'.headD 0) R'.tail
    else
      scanHL false 2 (a :: Lp) (r - 3) R'
  | false, a, Lp, d, R =>
    let a₁ := a + 3 * (d / 3)
    if d % 3 = 0 then
      some (.B (cSweepTail Lp a₁ (bump2 R)))
    else if d % 3 = 1 then
      scanHL true (a₁ + 2) Lp 0 R
    else if R = [] then
      none
    else
      scanHL false 0 ((a₁ + 2) :: Lp) (R.headD 0) R.tail
termination_by inCR1 _ _ _ R => (R.length, if inCR1 then 0 else 1)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.left
    omega
  · cases R' with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp only [List.length_cons]
      omega
  · apply Prod.Lex.left
    omega
  · cases R' with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp only [List.length_cons]
      omega
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · cases R with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp only [List.length_cons]
      omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .B R =>
    let p := bump2NE R
    scanHL false 0 [] p.1 p.2

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC

namespace M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive OdomTok where
  | L0
  | L1
  | L2
  deriving DecidableEq, Repr

@[simp]
def odomWord : OdomTok → List (Fin 2)
  | .L0 => [0, 0, 1, 0]
  | .L1 => [1, 0, 1, 0]
  | .L2 => [1, 1, 0]

@[simp]
def encOdom : List OdomTok → ListBlank (Fin 2)
  | [] => ListBlank.append [1] default
  | t :: l => ListBlank.append (odomWord t) (encOdom l)

@[simp]
def cap : List OdomTok → ℕ
  | [] => 0
  | .L0 :: l => 2 * cap l + 1
  | .L1 :: l => 2 * cap l
  | .L2 :: l => cap l / 2

@[simp]
def decFuel : ℕ → List OdomTok → List OdomTok
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, .L0 :: l => .L1 :: l
  | n + 1, .L1 :: l => .L0 :: decFuel n l
  | n + 1, .L2 :: l => .L2 :: decFuel n (decFuel n l)

def dec (l : List OdomTok) : List OdomTok :=
  decFuel l.length l

@[simp]
def drain : List OdomTok → List (Fin 2)
  | [] => [1, 0]
  | .L0 :: tl => drain tl ++ [1, 0, 1, 0]
  | .L1 :: tl => drain tl ++ [1, 0, 1, 0]
  | .L2 :: tl => drain tl ++ (if cap tl % 2 = 0 then [0, 0, 0] else [1, 0, 0])

abbrev State : Type := List OdomTok × List (Fin 2)

def start : State := ([], [])

def encode (s : State) : Cfg (Fin 2) (Fin 6) :=
  evalOdomR .leftOdom 2 [0] (encOdom s.1) (ListBlank.append s.2 default)

def stepLWord (l : List OdomTok) (w : List (Fin 2)) : State :=
  if cap l ≥ 1 then (dec l, w) else ([], drain l ++ w)

def popBit : List (Fin 2) → Fin 2 × List (Fin 2)
  | [] => (0, [])
  | b :: w => (b, w)

def next (s : State) : Option State :=
  let (l, w) := s
  let (b₀, w₁) := popBit w
  if b₀ = 0 then
    some (stepLWord l (1 :: w₁))
  else
    let (b₁, w₂) := popBit w₁
    if b₁ = 0 then
      let (b₂, w₃) := popBit w₂
      if b₂ = 0 then
        some (.L2 :: l, w₃)
      else
        let (b₃, w₄) := popBit w₃
        if b₃ = 0 then
          some (.L0 :: l, w₄)
        else
          some (stepLWord l (1 :: 0 :: 0 :: 0 :: w₄))
    else
      let (b₂, w₃) := popBit w₂
      if b₂ = 0 then
        some (.L2 :: l, w₃)
      else
        none

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

theorem has_odometer_reduction : HasOdometerReduction target := by sorry

inductive HighLevelState where
  | W (w : List (Fin 2))
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .W []

def toState : HighLevelState → State
  | .W w => ([], w)

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def runOdom : List OdomTok → List (Fin 2) → Option HighLevelState
  | l, [] =>
    if cap l = 0 then some (.W (drain l ++ [1]))
    else if cap (dec l) < cap l then runOdom (.L2 :: dec l) []
    else none
  | l, b₀ :: w₁ =>
    if b₀ = 0 then
      if cap l = 0 then some (.W (drain l ++ 1 :: w₁))
      else if cap (dec l) < cap l then runOdom (dec l) (1 :: w₁)
      else none
    else
      match w₁ with
      | [] => runOdom (.L2 :: l) []
      | b₁ :: w₂ =>
        if b₁ = 0 then
          match w₂ with
          | [] => runOdom (.L2 :: l) []
          | b₂ :: w₃ =>
            if b₂ = 0 then runOdom (.L2 :: l) w₃
            else
              match w₃ with
              | [] => runOdom (.L0 :: l) []
              | b₃ :: w₄ =>
                if b₃ = 0 then runOdom (.L0 :: l) w₄
                else if cap l = 0 then some (.W (drain l ++ 1 :: 0 :: 0 :: 0 :: w₄))
                else if cap (dec l) < cap l then runOdom (dec l) (1 :: 0 :: 0 :: 0 :: w₄)
                else none
        else
          match w₂ with
          | [] => runOdom (.L2 :: l) []
          | b₂ :: w₃ =>
            if b₂ = 0 then runOdom (.L2 :: l) w₃
            else none
termination_by l w => (w.length, cap l)
decreasing_by
  all_goals simp_wf
  all_goals omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .W w => runOdom [] w

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH

namespace M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB

namespace M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive State where
  | D (L R : List ℕ)
  deriving DecidableEq, Repr

def sweepB : List ℕ → List ℕ → State
  | L, [] => .D (incRun L) []
  | L, 0 :: Rt => sweepB (incRun L) Rt
  | L, 1 :: Rt => sweepB (0 :: incRun L) Rt
  | L, (d + 2) :: Rt => .D (incRun L) ((d + 1) :: Rt)

def start : State := .D [1] []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D L R => Cfg.headLeft SixState.D (encRun L) (encRun R)

def next : State → Option State
  | .D [] R => some (sweepB [0] (1 :: R))
  | .D [0] R => some (sweepB [] (incRun (incRun R)))
  | .D (0 :: 0 :: L'') R => some (sweepB L'' (0 :: incRun R))
  | .D (0 :: (k + 1) :: L'') R => some (sweepB (k :: L'') (incRun (incRun R)))
  | .D [1] R => some (.D [] (1 :: 0 :: R))
  | .D (1 :: 0 :: L'') R => some (sweepB (0 :: L'') (0 :: 0 :: R))
  | .D (1 :: (k + 1) :: L'') R => some (.D (k :: L'') (1 :: 0 :: R))
  | .D [2] R => some (sweepB [] (2 :: 1 :: R))
  | .D (2 :: 0 :: _) _ => none
  | .D (2 :: 1 :: L'') R => some (sweepB L'' (0 :: 1 :: 1 :: R))
  | .D (2 :: (k + 2) :: L'') R => some (sweepB (k :: L'') (2 :: 1 :: R))
  | .D ((k + 3) :: L') R => some (sweepB (0 :: k :: L') (1 :: R))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH

namespace M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB

namespace M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive State where
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

def transferB : List ℕ → List ℕ → State
  | [], [] => .C 0 [] []
  | a :: L, [] => .C (a + 1) L []
  | L, d :: R => transferB (d :: bumpHead L) R

def start : State := .C 3 [0] []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a L R => Cfg.headRight C (encStack (a :: L)) (ListBlank.cons 0 (encStack2 R).tail)

def next : State → Option State
  | .C 0 [] _ => none
  | .C 0 (0 :: L) R => some (transferB ((R.headD 0 + 2) :: 0 :: L) R.tail)
  | .C 0 ((b + 1) :: L) R => some (transferB (b :: L) ((R.headD 0 + 2) :: R.tail))
  | .C (a + 1) L R =>
    let k := a / 2
    let r := R.headD 0
    if a % 2 = 0 then
      some (transferB (bumpHead^[k] L) ((r + k + 2) :: R.tail))
    else
      List.casesOn L (some (.C k [] (0 :: (r + k) :: R.tail)))
        fun b L' => some (.C (b + k + 1) L' (0 :: (r + k) :: R.tail))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | C (a : ℕ) (L : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .C 3 [0]

def toState : HighLevelState → State
  | .C a L => .C a L []

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def transferBHL : List ℕ → List ℕ → HighLevelState
  | [], [] => .C 0 []
  | a :: L, [] => .C (a + 1) L
  | L, d :: R => transferBHL (d :: bumpHead L) R

def runEpoch (a : ℕ) (L R : List ℕ) : Option HighLevelState :=
  let r := R.headD 0
  if a = 0 then
    List.casesOn L none fun b L' =>
      if b = 0 then some (transferBHL ((r + 2) :: 0 :: L') R.tail)
      else some (transferBHL ((b - 1) :: L') ((r + 2) :: R.tail))
  else
    let k := (a - 1) / 2
    if (a - 1) % 2 = 0 then
      some (transferBHL (bumpHead^[k] L) ((r + k + 2) :: R.tail))
    else if L = [] then
      runEpoch k [] (0 :: (r + k) :: R.tail)
    else
      runEpoch (L.headD 0 + k + 1) L.tail (0 :: (r + k) :: R.tail)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  · omega
  · cases L with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp +zetaDelta only [List.length_cons]
      omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .C a L => runEpoch a L []

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB

namespace M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH

namespace M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def sepRight : Fin 3 → List (Fin 2)
  | 0 => [0]
  | 1 => [0, 0]
  | 2 => [0, 0, 0]

def encLeft : List (ℕ × Bool) → ListBlank (Fin 2)
  | [] => default
  | (a, false) :: L =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.cons 0 (encLeft L))
  | (a, true) :: L =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0, 0] (encLeft L))

def encRight : List (ℕ × Fin 3) → ListBlank (Fin 2)
  | [] => default
  | (d, c) :: R =>
    ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append (sepRight c) (encRight R))

def bumpHeadL (s : List (ℕ × Bool)) : List (ℕ × Bool) :=
  List.casesOn s [(0, false)] fun p L => (p.1 + 1, p.2) :: L

def bump2R : List (ℕ × Fin 3) → List (ℕ × Fin 3)
  | [] => [(1, 0)]
  | (d, c) :: R => (d + 2, c) :: R

def push01 (s : List (ℕ × Bool)) : List (ℕ × Bool) :=
  List.casesOn s [(0, false)] fun p L => (0, true) :: (p.1, p.2) :: L

def prepend00 : ℕ → List (ℕ × Bool) → List (ℕ × Bool)
  | 0, L => L
  | k + 1, L => (0, false) :: prepend00 k L

inductive State where
  | D (L : List (ℕ × Bool)) (R : List (ℕ × Fin 3))
  deriving DecidableEq, Repr

def runB (twoZeros : Bool) :
    ℕ → Bool → List (ℕ × Bool) → List (ℕ × Fin 3) → Option State
  | 0, _, [], R =>
    some (.D [] (if twoZeros then (1, 1) :: R else bump2R R))
  | 0, false, p :: L', R =>
    some (.D (p :: L') (if twoZeros then (1, 1) :: R else bump2R R))
  | 0, true, (a₂, b₂) :: L', R =>
    some (.D ((a₂ + 1, b₂) :: L') ((0, if twoZeros then 2 else 0) :: R))
  | 1, _, [], R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D [] (bump2R R₁))
  | 1, false, (a₂, b₂) :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    runB false (a₂ + 1) b₂ L' R₁
  | 1, true, p :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D (p :: L') (bump2R R₁))
  | 2, _, [], _ => none
  | 2, false, (a₂, b₂) :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    runB true a₂ b₂ L' R₁
  | 2, true, _ :: _, _ => none
  | 3, _, [], R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D [] (bump2R R₁))
  | 3, false, (a₂, b₂) :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D ((a₂ + 1, b₂) :: L') ((0, 0) :: R₁))
  | 3, true, p :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D ((0, false) :: p :: L') ((0, 0) :: R₁))
  | a + 4, b, L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D ((a, b) :: L') (bump2R R₁))

def runBR (k : ℕ) (Lrest : List (ℕ × Bool)) :
    ℕ → Fin 3 → List (ℕ × Fin 3) → Option State
  | 0, _, [] => runB false 0 false (prepend00 k (push01 Lrest)) []
  | 0, c₁, (d₂, c₂) :: R' =>
    if c₁ = 0 then
      runBR (k + 1) Lrest d₂ c₂ R'
    else if c₁ = 1 then
      runB false 0 false (prepend00 k (push01 Lrest)) ((d₂, c₂) :: R')
    else
      some (.D (prepend00 k (push01 Lrest)) ((1, 0) :: (d₂, c₂) :: R'))
  | 1, _, [] => runB false 0 true (prepend00 k (push01 Lrest)) []
  | 1, c₁, (d₂, c₂) :: R' =>
    let L := prepend00 k (push01 Lrest)
    if c₁ = 0 then
      runBR 0 L d₂ c₂ R'
    else if c₁ = 1 then
      runB false 0 true L ((d₂, c₂) :: R')
    else
      some (.D (bumpHeadL L) ((0, 1) :: (d₂, c₂) :: R'))
  | 2, _, [] => some (.D (prepend00 k (push01 Lrest)) [(0, 0)])
  | 2, c₁, (d₂, c₂) :: R' =>
    let L := prepend00 k (push01 Lrest)
    if c₁ = 0 then
      some (.D L ((0, 1) :: (d₂, c₂) :: R'))
    else if c₁ = 1 then
      some (.D L ((0, 2) :: (d₂, c₂) :: R'))
    else
      some (.D (prepend00 k (push01 (bumpHeadL Lrest))) ((1, 1) :: (d₂, c₂) :: R'))
  | d₁ + 3, c₁, R' =>
    some (.D (prepend00 k (push01 Lrest)) ((0, 0) :: (d₁, c₁) :: R'))

def start : State := .D [] [(1, 0)]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D L R => Cfg.headRight D (encLeft L) (ListBlank.cons 0 (encRight R))

def next : State → Option State
  | .D [] [] => some (.D [(0, false)] [(1, 0)])
  | .D [] ((d₁, c₁) :: R') => runBR 0 [] (d₁ + 1) c₁ R'
  | .D ((a, b) :: L') R =>
    let R₁ := List.replicate (a / 4) (2, (0 : Fin 3)) ++ R
    if a % 4 = 0 then
      match L', b with
      | [], _ => some (.D [] ((0, 0) :: R₁))
      | p :: L'', false => some (.D (p :: L'') ((0, 0) :: R₁))
      | (a₂, b₂) :: L'', true =>
        let Lnext := (a₂ + 1, b₂) :: L''
        match R₁ with
        | [] => runB false 0 true Lnext []
        | (d₁, c₁) :: R₁' => runBR 0 Lnext d₁ c₁ R₁'
    else if a % 4 = 1 then
      match L', b with
      | [], _ => some (.D [] ((2, 0) :: R₁))
      | (a₂, b₂) :: L'', false => runB false (a₂ + 1) b₂ L'' ((0, 0) :: R₁)
      | p :: L'', true => some (.D (p :: L'') ((2, 0) :: R₁))
    else if a % 4 = 2 then
      match L', b with
      | [], _ => none
      | (a₂, b₂) :: L'', false => runB true a₂ b₂ L'' ((0, 0) :: R₁)
      | _ :: _, true => none
    else
      match L', b with
      | [], _ => some (.D [] ((2, 0) :: R₁))
      | (a₂, b₂) :: L'', false => some (.D ((a₂ + 1, b₂) :: L'') ((0, 0) :: (0, 0) :: R₁))
      | p :: L'', true => some (.D ((0, false) :: p :: L'') ((0, 0) :: (0, 0) :: R₁))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB

namespace M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def encRight (E : List ℕ) (c : ℕ) : ListBlank (Fin 2) :=
  List.rec (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)
    (fun e _ ih =>
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * e + 1)) (ListBlank.cons 0 ih))
    E

inductive State where
  | B (L E : List ℕ) (c : ℕ)
  deriving DecidableEq, Repr

def drainD : List ℕ → List ℕ → ℕ → State
  | [], E, c => .B [0] E c
  | a :: Lt, E, c =>
    if a % 2 = 1 then
      .B (bumpHead Lt) (List.replicate (a / 2 + 1) 0 ++ E) c
    else
      List.casesOn (List.replicate (a / 2) 0 ++ E) (drainD Lt [] (c + 2))
        fun e Et => drainD Lt ((e + 1) :: Et) c

def start : State := .B [0] [] 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .B L E c => Cfg.headRight B (encStack L) (encRight E c)

def next : State → Option State
  | .B L [] c => some (drainD (bumpHeadBy c L) [] 3)
  | .B L [e₀] 0 => some (drainD (bumpHeadBy (2 * e₀) L) [] 2)
  | .B _ [_] 1 => none
  | .B L [e₀] 2 => some (.B (bumpHead (bumpHeadBy (2 * e₀) L)) [0, 0] 1)
  | .B L [e₀] 3 => some (drainD (bumpHeadBy (2 * e₀) L) [1] 0)
  | .B L [e₀] (c + 4) => some (drainD (bumpHeadBy (2 * e₀) L) [1, 0] c)
  | .B L (e₀ :: 0 :: E₂) c => some (drainD (bumpHeadBy (2 * e₀) L) (1 :: E₂) c)
  | .B L (e₀ :: 1 :: E₂) c => some (.B (4 :: bumpHeadBy (2 * e₀) L) E₂ c)
  | .B L (e₀ :: (e₁ + 2) :: E₂) c => some (drainD (4 :: bumpHeadBy (2 * e₀) L) (e₁ :: E₂) c)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | B (E : List ℕ) (c : ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .B [] 1

def toState : HighLevelState → State
  | .B E c => .B [0] E c

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def drainEven : List ℕ → List ℕ → ℕ → HighLevelState
  | [], E, c => .B E c
  | h :: hs, E, c =>
    List.casesOn (motive := fun _ => HighLevelState) (List.replicate h 0 ++ E)
      (drainEven hs [] (c + 2)) fun e Et => drainEven hs ((e + 1) :: Et) c

def drainOdd : ℕ → List ℕ → List ℕ → ℕ → HighLevelState
  | h₀, [], E, c => .B (List.replicate (h₀ + 1) 0 ++ E) c
  | h₀, h₁ :: hs, E, c => drainOdd h₁ hs (1 :: (List.replicate (h₀ - 1) 0 ++ E)) c

def peelPairs : ℕ → List ℕ → List ℕ → ℕ → Option HighLevelState
  | h₀, hs, [], c =>
    if c % 2 = 0 then some (drainEven ((h₀ + c / 2) :: hs) [] 3)
    else some (drainOdd (h₀ + c / 2) hs [] 3)
  | h₀, hs, [e₀], c =>
    if c = 0 then some (drainEven ((h₀ + e₀) :: hs) [] 2)
    else if c = 1 then none
    else if c = 2 then some (drainOdd (h₀ + e₀) hs [1] 1)
    else if c = 3 then some (drainEven ((h₀ + e₀) :: hs) [1] 0)
    else some (drainEven ((h₀ + e₀) :: hs) [1, 0] (c - 4))
  | h₀, hs, e₀ :: e₁ :: E₂, c =>
    if e₁ = 0 then some (drainEven ((h₀ + e₀) :: hs) (1 :: E₂) c)
    else if e₁ = 1 then peelPairs 2 ((h₀ + e₀) :: hs) E₂ c
    else some (drainEven (2 :: (h₀ + e₀) :: hs) ((e₁ - 2) :: E₂) c)

def highLevelNext : HighLevelState → Option HighLevelState
  | .B E c => peelPairs 0 [] E c

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD

namespace M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive State where
  | E (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def drainOddB : List ℕ → ℕ → List ℕ → State
  | [], d, R => .E (d + 2) R
  | [j], d, R => .E 1 (List.replicate j 0 ++ (d + 1) :: R)
  | 0 :: j2 :: ks, d, R => drainOddB ks (2 * j2 + d + 6) R
  | (j1 + 1) :: j2 :: ks, d, R =>
    drainOddB ks (2 * j2 + 5) (List.replicate j1 0 ++ (d + 1) :: R)

def scanE : List ℕ → ℕ → List ℕ → Option State
  | ks, d, [] =>
    if d % 2 = 1 then none
    else
      List.casesOn ks (some (.E 1 (List.replicate (d / 2 + 1) 0)))
        fun j2 ks' => some (drainOddB ks' (2 * j2 + 5) (List.replicate (d / 2) 0))
  | ks, d, e :: R =>
    if d % 2 = 1 then scanE ((d / 2) :: ks) e R
    else some (drainOddB ks (d + e + 2) R)

def start : State := .E 0 [0]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E d R => Cfg.headRight E default (ListBlank.cons 0 (encStack (d :: R)))

def next : State → Option State
  | .E d R => scanE [] d R

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA

namespace M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def finishRet (s : List ℕ) : List ℕ :=
  List.casesOn s [] fun r₀ R =>
    Nat.casesOn r₀ (List.casesOn R [] fun r2 R' => 0 :: (r2 + 1) :: R') fun r => r :: R

def retPass : Bool → List Bool → List ℕ → List ℕ
  | false, [], R => finishRet (bumpHead R)
  | true, [], R => finishRet (0 :: bumpHead R)
  | false, false :: bs, R => retPass true bs (bumpHead R)
  | false, true :: bs, R => retPass true bs (bumpHead (bumpHead R))
  | true, false :: bs, R => retPass false bs (0 :: bumpHead R)
  | true, [true], R => finishRet (0 :: 0 :: bumpHead R)
  | true, true :: false :: bs, R => retPass true bs (0 :: 0 :: bumpHead R)
  | true, true :: true :: bs, R => retPass true bs (1 :: 0 :: bumpHead R)

def scanPass : Bool → List Bool → List ℕ → Option (List ℕ)
  | false, bs, [] => some (retPass false bs [0])
  | true, bs, [] => some (retPass true bs [0, 0])
  | false, bs, 0 :: R => some (retPass false (false :: bs) R)
  | false, bs, 1 :: R => some (retPass true (false :: bs) R)
  | false, bs, 2 :: R => scanPass false (false :: false :: bs) R
  | false, bs, 3 :: R => scanPass true (false :: bs) R
  | false, _, (_ + 4) :: _ => none
  | true, bs, 0 :: R => some (retPass false (true :: false :: bs) R)
  | true, bs, 1 :: R => some (retPass true (true :: false :: bs) R)
  | true, bs, 2 :: R => scanPass false (false :: true :: false :: bs) R
  | true, bs, 3 :: R => scanPass true (true :: false :: bs) R
  | true, _, (_ + 4) :: _ => none

inductive State where
  | E (R : List ℕ)
  deriving DecidableEq, Repr

def start : State := .E []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E R => Cfg.headRight E default (ListBlank.cons 0 (ListBlank.cons 1 (encStack R)))

def next : State → Option State
  | .E [] => some (.E [0, 0])
  | .E (0 :: R) => (scanPass false [false, false] R).map .E
  | .E (1 :: R) => (scanPass true [false] R).map .E
  | .E ((_ + 2) :: _) => none

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | E (R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .E [0]

def toState : HighLevelState → State
  | .E R => .E (0 :: R)

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def retHL : Bool → List Bool → List ℕ → List ℕ
  | false, [], R => bumpHead (bumpHead R)
  | true, [], R => 3 :: bumpHead R
  | false, false :: bs, R => retHL true bs (bumpHead R)
  | false, true :: bs, R => retHL true bs (bumpHead (bumpHead R))
  | true, false :: bs, R => retHL false bs (0 :: bumpHead R)
  | true, [true], R => 1 :: 0 :: bumpHead R
  | true, true :: false :: bs, R => retHL true bs (0 :: 0 :: bumpHead R)
  | true, true :: true :: bs, R => retHL true bs (1 :: 0 :: bumpHead R)

def scanHL : Bool → List Bool → List ℕ → Option HighLevelState
  | false, bs, [] => some (.E (retHL false bs [0]))
  | true, bs, [] => some (.E (retHL true bs [0, 0]))
  | m, bs, r :: R =>
    let bm := if m then true :: false :: bs else false :: bs
    if r = 0 then some (.E (retHL false bm R))
    else if r = 1 then some (.E (retHL true bm R))
    else if r = 2 then scanHL false (false :: bm) R
    else if r = 3 then scanHL true bm R
    else none

def highLevelNext : HighLevelState → Option HighLevelState
  | .E R => scanHL false [] R

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH

namespace M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def bumpNE (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (0, []) fun a xs => (a + 1, xs)

def peelEL (k : ℕ) (R : List ℕ) : List ℕ :=
  ((fun s => 0 :: bumpHead (bumpHead s))^[k]) R

inductive State where
  | EL (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  | E0 (L R : List ℕ)
  deriving DecidableEq, Repr

def runF : List ℕ → List ℕ → State
  | L, [] =>
    let p := bumpNE L
    .EL p.1 p.2 0 []
  | L, [0] =>
    let p := bumpNE L
    .EL p.1 p.2 2 []
  | L, 0 :: e :: R =>
    let p := bumpNE L
    .EL p.1 p.2 0 (e :: R)
  | L, 1 :: R => runF (0 :: bumpHead L) R
  | L, 2 :: R =>
    let pL := bumpNE (bumpHead (bumpHead L))
    let pR := bumpNE (bumpHead R)
    .EL pL.1 pL.2 pR.1 pR.2
  | L, (d + 3) :: R => .E0 (bumpHead L) (d :: R)

def runE0 : List ℕ → List ℕ → State
  | [], R => runF [0, 0] R
  | [0], R => runF [0, 1, 0] R
  | 0 :: a :: L, R => .EL a L 0 (1 :: R)
  | 1 :: L, R => runE0 L (1 :: R)
  | (a + 2) :: L, R => .EL a L 0 (1 :: R)

def start : State := .EL 1 [] 1 []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .EL a L d R => Cfg.headLeft E (encStack (a :: L)) (encStack (d :: R))
  | .E0 L R => Cfg.headRight E (encStack L) (ListBlank.cons 0 (encStack (0 :: R)))

def next : State → Option State
  | .E0 L R => some (runE0 L R)
  | .EL a L d R =>
    let R₁ := peelEL (a / 4) (d :: R)
    if a % 4 = 0 then
      match L with
      | [] => none
      | [0] =>
        let p := bumpNE R₁
        some (.EL 1 [] (p.1 + 2) p.2)
      | 0 :: b :: L' =>
        let p := bumpNE R₁
        some (.EL b L' (p.1 + 3) p.2)
      | [1] =>
        let p := bumpNE R₁
        some (.E0 [] (p.1 :: p.2))
      | 1 :: c :: L' =>
        let p := bumpNE R₁
        some (runF (0 :: (c + 1) :: L') (p.1 :: p.2))
      | (b + 2) :: L' =>
        let p := bumpNE R₁
        some (.E0 (b :: L') (p.1 :: p.2))
    else if a % 4 = 1 then
      some (runF L (bumpHead (bumpHead R₁)))
    else if a % 4 = 2 then
      let R₂ := bumpHead (bumpHead R₁)
      List.casesOn L (some (.E0 [] R₂)) fun b L' => some (.EL b L' 0 R₂)
    else
      some (.E0 L (bumpHead (bumpHead R₁)))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry

inductive HighLevelState where
  | EL (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .EL 1 [] 1 []

def toState : HighLevelState → State
  | .EL a L d R => .EL a L d R

def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

def countOnes (L : List ℕ) : ℕ × List ℕ :=
  List.rec (motive := fun _ => ℕ × List ℕ) (0, [])
    (fun x xs p => if x = 1 then (p.1 + 1, p.2) else (0, x :: xs)) L

def pushZeroBump (k : ℕ) (L : List ℕ) : List ℕ :=
  ((fun s => 0 :: bumpHead s)^[k]) L

def stepFHead (R' : List ℕ) (ih : List ℕ → HighLevelState) : ℕ → List ℕ → HighLevelState
  | 0, L =>
    let p := bumpNE L
    List.casesOn (motive := fun _ => HighLevelState) R' (.EL p.1 p.2 2 []) fun e R'' =>
      .EL p.1 p.2 0 (e :: R'')
  | 1, L => ih (0 :: bumpHead L)
  | 2, L =>
    let pL := bumpNE (bumpHead (bumpHead L))
    let pR := bumpNE (bumpHead R')
    .EL pL.1 pL.2 pR.1 pR.2
  | d + 3, L =>
    let c := countOnes (bumpHead L)
    List.casesOn (motive := fun _ => HighLevelState) c.2
      (stepFHead R' ih d (pushZeroBump c.1 [0, 0])) fun x Lt =>
        if x = 0 then
          List.casesOn (motive := fun _ => HighLevelState) Lt
            (stepFHead R' ih d (pushZeroBump c.1 [0, 1, 0])) fun a Lt' =>
              .EL a Lt' 0 (1 :: (List.replicate c.1 1 ++ (d :: R')))
        else
          .EL (x - 2) Lt 0 (1 :: (List.replicate c.1 1 ++ (d :: R')))

def runFHL (L R : List ℕ) : HighLevelState :=
  List.rec (motive := fun _ => List ℕ → HighLevelState)
    (fun L =>
      let p := bumpNE L
      .EL p.1 p.2 0 [])
    (fun r R' ih L => stepFHead R' ih r L)
    R L

def runE0HL (L R : List ℕ) : HighLevelState :=
  let c := countOnes L
  List.casesOn (motive := fun _ => HighLevelState) c.2
    (runFHL (pushZeroBump c.1 [0, 0]) R) fun x Lt =>
      if x = 0 then
        List.casesOn (motive := fun _ => HighLevelState) Lt
          (runFHL (pushZeroBump c.1 [0, 1, 0]) R) fun a Lt' =>
            .EL a Lt' 0 (1 :: (List.replicate c.1 1 ++ R))
      else
        .EL (x - 2) Lt 0 (1 :: (List.replicate c.1 1 ++ R))

def highLevelNext : HighLevelState → Option HighLevelState
  | .EL a L d R =>
    let R₁ := peelEL (a / 4) (d :: R)
    if a % 4 = 0 then
      List.casesOn (motive := fun _ => Option HighLevelState) L none fun b Lp =>
        let p := bumpNE R₁
        if b = 0 then
          List.casesOn (motive := fun _ => Option HighLevelState) Lp
            (some (.EL 1 [] (p.1 + 2) p.2)) fun b' L'' =>
              some (.EL b' L'' (p.1 + 3) p.2)
        else if b = 1 then
          List.casesOn (motive := fun _ => Option HighLevelState) Lp
            (some (runE0HL [] (p.1 :: p.2))) fun c L'' =>
              some (runFHL (0 :: (c + 1) :: L'') (p.1 :: p.2))
        else
          some (runE0HL ((b - 2) :: Lp) (p.1 :: p.2))
    else
      let R₂ := bumpHead (bumpHead R₁)
      if a % 4 = 1 then
        some (runFHL L R₂)
      else if a % 4 = 2 then
        List.casesOn (motive := fun _ => Option HighLevelState) L
          (some (runE0HL [] R₂)) fun b L' =>
            some (.EL b L' 0 R₂)
      else
        some (runE0HL L R₂)

theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by sorry

theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart := by sorry

theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart := by sorry
end M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD

namespace M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

def bump1 (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (0, []) fun r xs => (r + 1, xs)

def bump2 (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (1, []) fun c xs => (c + 2, xs)

inductive State where
  | CR (a b : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

def stepZero (b d : ℕ) (L R : List ℕ) : State :=
  let pL := bump2 L
  if b = 0 then
    let pR := bump1 R
    .CR (d + 1) pL.1 pL.2 pR.1 pR.2
  else if b = 1 then
    .CR 0 pL.1 pL.2 (d + 1) R
  else
    .CR (b - 2) pL.1 pL.2 0 (d :: R)

def stepOne (b : ℕ) (L R : List ℕ) : State :=
  List.casesOn R (.CR 0 (b + 5) L 0 []) fun r₀ R₂ =>
    Nat.casesOn r₀
      (List.casesOn R₂ (.CR 0 (b + 5) L 0 []) fun r₂ R₃ =>
        let pR := bump1 R₃
        .CR (r₂ + 1) (b + 5) L pR.1 pR.2)
      fun e =>
        let pR := bump1 R₂
        .CR e (b + 5) L pR.1 pR.2

def start : State := .CR 0 0 [] 0 []

def encode : State → Cfg (Fin 2) (Fin 6)
  | .CR a b L d R =>
    Cfg.headRight C (encStack (a :: b :: L))
      (ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ d)
        (ListBlank.cons 0 (encStack R))))

def next : State → Option State
  | .CR a b L 0 R =>
    let q := a / 3
    let b₁ := b + 2 * q
    let R₁ := bumpHeadBy q R
    if a % 3 = 0 then
      some (stepZero b₁ 0 L R₁)
    else if a % 3 = 1 then
      some (stepOne b₁ L R₁)
    else
      let pR := bump1 R₁
      some (.CR 0 (b₁ + 2) L (pR.1 + 1) pR.2)
  | .CR 0 b L (d + 1) R => some (stepZero b (d + 1) L R)
  | .CR 1 _ _ (_ + 1) _ => none
  | .CR (a + 2) b L (d + 1) R =>
    let pR := bump1 R
    some (.CR (d + 1) (a + 1) (b :: L) pR.1 pR.2)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA

namespace M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA

namespace M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

theorem has_stack_reduction : HasStackReduction target := by sorry
end M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD

namespace M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

inductive Sep where
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr

def encSep : Sep → List (Fin 2)
  | .s1 => [0]
  | .s2 => [0, 0]
  | .s3 => [0, 0, 0]
  | .s4 => [0, 0, 0, 0]

def encStack : List (ℕ × Sep) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: xs =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.append (encSep b) (encStack xs))

inductive State where
  | M0 (L R : List (ℕ × Sep))
  deriving DecidableEq, Repr

def bumpHead : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => [(0, .s1)]
  | (a, b) :: xs => (a + 1, b) :: xs

def tailAsRight : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => [(0, .s1)]
  | (a, b) :: xs => (a, b) :: xs

def rightAsTail : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => []
  | (a, b) :: xs => (a + 1, b) :: xs

def pushZeroSep (b : Sep) : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => []
  | (a, b') :: xs => (0, b) :: (a, b') :: xs

def peelSep : Sep → List (ℕ × Sep) → List (ℕ × Sep)
  | _, [] => []
  | .s1, (a, b') :: xs => (a + 1, b') :: xs
  | .s2, (a, b') :: xs => (0, .s1) :: (a, b') :: xs
  | .s3, (a, b') :: xs => (0, .s2) :: (a, b') :: xs
  | .s4, (a, b') :: xs => (0, .s3) :: (a, b') :: xs

def peelInner : Sep → List (ℕ × Sep) → List (ℕ × Sep)
  | _, [] => [(0, .s1)]
  | .s2, (a₂, b₂) :: rs => (a₂ + 1, b₂) :: rs
  | .s3, (a₂, b₂) :: rs => (0, .s1) :: (a₂, b₂) :: rs
  | _, (a₂, b₂) :: rs => (0, .s2) :: (a₂, b₂) :: rs

def popRD : Sep → List (ℕ × Sep) → List (ℕ × Sep)
  | .s1, R => rightAsTail (tailAsRight R)
  | .s2, R => (0, .s1) :: tailAsRight R
  | .s3, R => (0, .s2) :: tailAsRight R
  | .s4, R => (0, .s3) :: tailAsRight R

def sepParity : Sep → ℕ
  | .s1 => 0
  | .s2 => 1
  | .s3 => 0
  | .s4 => 1

def weightR : List (ℕ × Sep) → ℕ
  | [] => 0
  | (a, b) :: rs => if rs.isEmpty then a else a + sepParity b + weightR rs

inductive FState where
  | f00
  | f01
  | f02
  | f03
  | f04
  | f05
  deriving DecidableEq, Repr

inductive Stage3Mode where
  | q0
  | qz
  | qz1
  deriving DecidableEq, Repr

def stepBit0 (runZ1 : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) :
    FState × List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | (.f00, R₁) => some (.f01, R₁)
  | (.f01, R₁) => some (.f02, bumpHead R₁)
  | (.f02, R₁) => runZ1 R₁
  | (.f03, R₁) => some (.f04, R₁)
  | (.f04, R₁) => some (.f00, (0, .s1) :: (0, .s1) :: R₁)
  | (.f05, R₁) => some (.f00, (0, .s1) :: (0, .s1) :: R₁)

def stepBit1 (runZ : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) :
    FState × List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | (.f00, R₁) => runZ R₁
  | (.f01, R₁) => some (.f03, R₁)
  | (.f02, R₁) => some (.f00, (0, .s1) :: R₁)
  | (.f03, R₁) => some (.f05, R₁)
  | (.f04, R₁) => some (.f00, (0, .s3) :: R₁)
  | (.f05, _) => none

def evalQ0Aux
    (runZ runZ1 : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) :
    List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | [] => some (.f00, [(0, .s1)])
  | (0, .s1) :: Rt =>
    if Rt.isEmpty then
      some (.f00, (0, .s1) :: peelInner .s1 [])
    else
      ((evalQ0Aux runZ runZ1 Rt).bind (stepBit0 runZ1)).bind (stepBit1 runZ)
  | (0, .s2) :: Rt => some (.f00, (0, .s1) :: peelInner .s2 Rt)
  | (0, .s3) :: Rt => some (.f00, (0, .s1) :: peelInner .s3 Rt)
  | (0, .s4) :: Rt => some (.f00, (0, .s1) :: peelInner .s4 Rt)
  | (1, .s1) :: Rt =>
    if Rt.isEmpty then
      (runZ1 (peelInner .s1 [])).bind (stepBit1 runZ)
    else
      ((runZ Rt).bind (stepBit0 runZ1)).bind (stepBit1 runZ)
  | (1, .s2) :: Rt => (runZ1 (peelInner .s2 Rt)).bind (stepBit1 runZ)
  | (1, .s3) :: Rt => (runZ1 (peelInner .s3 Rt)).bind (stepBit1 runZ)
  | (1, .s4) :: Rt => (runZ1 (peelInner .s4 Rt)).bind (stepBit1 runZ)
  | (_ + 2, _) :: _ => none

def evalStage3 : ℕ → Stage3Mode → List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | 0, _, _ => some (.f00, [(0, .s1)])
  | fuel + 1, m, R =>
    let runZ := evalStage3 fuel .qz
    let runZ1 := evalStage3 fuel .qz1
    let res0 := evalQ0Aux runZ runZ1 R
    match m with
    | .q0 => res0
    | .qz => res0.bind (stepBit0 runZ1)
    | .qz1 => (res0.bind (stepBit0 runZ1)).bind (stepBit1 runZ)

def exitF (L₂ : List (ℕ × Sep)) : FState × List (ℕ × Sep) → State
  | (.f00, R) => .M0 ((0, .s4) :: tailAsRight L₂) ((0, .s1) :: R)
  | (.f01, R) => .M0 ((0, .s1) :: (0, .s3) :: tailAsRight L₂) (rightAsTail (bumpHead R))
  | (.f02, R) => .M0 ((0, .s1) :: (0, .s4) :: tailAsRight L₂) (rightAsTail R)
  | (.f03, R) => .M0 ((0, .s1) :: (0, .s3) :: tailAsRight L₂) ((0, .s2) :: R)
  | (.f04, R) => .M0 ((0, .s1) :: (0, .s4) :: tailAsRight L₂) ((0, .s2) :: R)
  | (.f05, R) => .M0 ((0, .s1) :: (0, .s4) :: tailAsRight L₂) ((0, .s2) :: R)

def stepD : Sep → List (ℕ × Sep) → List (ℕ × Sep) → Option State
  | c, [], R => some (.M0 [(0, .s1), (0, .s1)] (popRD c R))
  | c, (0, .s1) :: [], R => some (.M0 [(0, .s1), (0, .s1)] (popRD c R))
  | c, (0, .s1) :: (0, .s1) :: L₂, R =>
    if L₂.isEmpty then
      some (.M0 [] ((0, .s1) :: (0, c) :: tailAsRight R))
    else
      stepD .s3 L₂ ((0, c) :: tailAsRight R)
  | c, (0, .s1) :: (0, .s2) :: L₂, R =>
    some (.M0 (pushZeroSep .s1 L₂) ((0, .s1) :: (0, c) :: tailAsRight R))
  | c, (0, .s1) :: (0, .s3) :: L₂, R =>
    some (.M0 (pushZeroSep .s2 L₂) ((0, .s1) :: (0, c) :: tailAsRight R))
  | c, (0, .s1) :: (0, .s4) :: L₂, R =>
    some (.M0 (pushZeroSep .s3 L₂) ((0, .s1) :: (0, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s1) :: L₂, R =>
    some (.M0 (pushZeroSep .s2 L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s2) :: L₂, R =>
    some (.M0 (pushZeroSep .s3 L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s3) :: L₂, R =>
    some (.M0 (pushZeroSep .s4 L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s4) :: L₂, R =>
    if L₂.isEmpty then
      some (.M0 [] ((1, c) :: tailAsRight R))
    else
      let rP := (0, c) :: tailAsRight R
      exitF L₂ <$> evalStage3 (weightR rP + 1) .q0 rP
  | c, (0, .s1) :: (a₂ + 2, b₂) :: L₂, R =>
    some (.M0 ((0, .s1) :: (a₂, b₂) :: L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s2) :: L₁, R =>
    some (.M0 ((0, .s1) :: peelInner .s2 L₁) (popRD c R))
  | c, (0, .s3) :: L₁, R =>
    some (.M0 ((0, .s1) :: peelInner .s3 L₁) (popRD c R))
  | c, (0, .s4) :: L₁, R =>
    some (.M0 ((0, .s1) :: peelInner .s4 L₁) (popRD c R))
  | c, (1, b₁) :: L₁, R =>
    some (.M0 (peelSep b₁ L₁) ((1, c) :: tailAsRight R))
  | _, (_ + 2, _) :: _, _ => none

def start : State := .M0 [(0, .s1), (0, .s1)] [(1, .s1)]

def encode : State → Cfg (Fin 2) (Fin 6)
  | .M0 L R =>
    Cfg.headRight SixState.A (encStack L).tail (ListBlank.cons 0 (encStack R).tail)

def next : State → Option State
  | .M0 L [] => stepD .s1 L []
  | .M0 L ((0, bR) :: Rt) => stepD .s1 L (peelSep bR Rt)
  | .M0 L ((1, bR) :: Rt) => some (.M0 ((0, .s1) :: tailAsRight L) (peelSep bR Rt))
  | .M0 L ((2, bR) :: Rt) => some (.M0 ((0, .s2) :: tailAsRight L) (peelSep bR Rt))
  | .M0 _ ((_ + 3, _) :: _) => none

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA

end BusyBeaver
