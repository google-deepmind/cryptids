/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Busy Beaver Holdout Definitions (`BusyBeaver.Defs`)

Canonical Post-Turing machine execution model and behavioral goal predicates for Busy Beaver
holdouts:

- `IsHalt` — `M` eventually reaches a halting configuration from the blank tape (`init []`).
- `IsNotHalt` (`IsDoesNotHalt`) — `M` never halts from the blank tape.
- `HasCollatzReduction` — `M` is governed by a closed accelerated regular-expression tape pattern
  set.
- `HasStackedCollatzReduction` — `M` is governed by a closed accelerated stack-word tape pattern
  set.
- `HasStackReduction` — `M` is governed by a closed 2nd-order digit-stack system.
- `HasOdometerReduction` — `M` is governed by a closed mixed-radix odometer-word hub.
- `HasTransducerReduction` — `M` is governed by a closed bidirectional word-stack transducer.
-/

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
@[reducible] def Cfg.headRight {Γ Λ : Type*} [Inhabited Γ] (q : Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  ⟨some q, ⟨r.head, l, r.tail⟩⟩

/-- Configuration in state `q` with the tape head reading the first symbol of `l`. -/
@[reducible] def Cfg.headLeft {Γ Λ : Type*} [Inhabited Γ] (q : Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
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

scoped notation3 c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
scoped notation3 c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
scoped notation3 c₁ " [" M "]⊢* " c₂ => ReachesStar M c₁ c₂
scoped notation3 c₁ " [" M "]⊢⁺ " c₂ => ReachesPlus M c₁ c₂

scoped notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
scoped notation:67 s:67 " << " a:68 => ListBlank.cons a s
scoped infixr:67 " >> " => ListBlank.cons
scoped notation:67 s:67 " <+ " l:68 => ListBlank.append l s
scoped infixr:67 " +> " => ListBlank.append
@[inherit_doc Cfg.headRight]
scoped notation3 l " {{" q "}}> " r => Cfg.headRight q l r
@[inherit_doc Cfg.headLeft]
scoped notation3 l " <{{" q "}} " r => Cfg.headLeft q l r

def list_nat_repeat {Γ : Type*} : List Γ → Nat → List Γ
  | _, 0 => []
  | l, n + 1 => l ++ list_nat_repeat l n


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
  /-- All-blank tail (`default : ListBlank Γ`). -/
  | default : TapeExpr Γ
  /-- Single symbol `a` followed by `rest`. -/
  | sym (a : Γ) (rest : TapeExpr Γ)
  /-- Finite block `blk` repeated `vars var_idx` times followed by `rest`. -/
  | rep (blk : List Γ) (var_idx : ℕ) (rest : TapeExpr Γ)

/-- Evaluate a `TapeExpr Γ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapeExpr {Γ : Type*} [Inhabited Γ] : TapeExpr Γ → (ℕ → ℕ) → ListBlank Γ
  | .default, _ => default
  | .sym a rest, vars => ListBlank.cons a (evalTapeExpr rest vars)
  | .rep blk v rest, vars => ListBlank.append (blk ^ vars v) (evalTapeExpr rest vars)

/-- Parametric full-tape configuration pattern. -/
structure TapePattern (Γ Λ : Type*) where
  /-- Left half-tape expression. -/
  left : TapeExpr Γ
  /-- Control state (`some q` or `none`). -/
  head : Option Λ
  /-- Right half-tape expression (whose head is under the tape head). -/
  right : TapeExpr Γ

/-- Evaluate a `TapePattern Γ Λ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapePattern {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (p : TapePattern Γ Λ) (vars : ℕ → ℕ) : Cfg Γ Λ :=
  let r := evalTapeExpr p.right vars
  ⟨p.head, ⟨r.head, evalTapeExpr p.left vars, r.tail⟩⟩

/-- Guard condition over `ℕ`-valued pattern variables. -/
inductive VarCond where
  /-- `vars idx ≥ val`. -/
  | ge_const (idx : ℕ) (val : ℕ)
  /-- `vars idx1 ≥ vars idx2`. -/
  | ge_var (idx1 idx2 : ℕ)
  /-- Conjunction of conditions. -/
  | and (c1 c2 : VarCond)
  /-- Disjunction of conditions. -/
  | or (c1 c2 : VarCond)
  /-- Negation of a condition. -/
  | not (c : VarCond)
  /-- Trivially satisfied condition. -/
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


/-- Legacy alias `IsCryptid` for `HasCollatzReduction`. -/
abbrev IsCryptid (M : Machine Γ Λ) : Prop := HasCollatzReduction M

/-- Alias `IsStackCryptid` for `HasStackReduction`. -/
abbrev IsStackCryptid {k : ℕ} {Λ : Type*} [Inhabited Λ] (M : Machine (Fin (k + 2)) Λ) : Prop :=
  HasStackReduction M

/-- Alias `IsOdometerCryptid` for `HasOdometerReduction`. -/
abbrev IsOdometerCryptid {k : ℕ} {Λ : Type*} [Inhabited Λ] (M : Machine (Fin (k + 2)) Λ) : Prop :=
  HasOdometerReduction M

/-- Alias `IsTransducerCryptid` for `HasTransducerReduction`. -/
abbrev IsTransducerCryptid {k : ℕ} {Λ : Type*} [Inhabited Λ] (M : Machine (Fin (k + 2)) Λ) : Prop :=
  HasTransducerReduction M

end BusyBeaver
