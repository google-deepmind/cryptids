/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs.Core

/-!
# Accelerated Pattern Set Reductions (`BusyBeaver.Defs.Patterns`)

Parametric regular-expression tape patterns and Collatz-like acceleration semantics:

- `TapeExpr` — parametric regular-expression half-tape expressions.
- `evalTapeExpr` — evaluation of a tape expression under a variable valuation.
- `TapePattern` — parametric full-tape configuration pattern.
- `evalTapePattern` — evaluation of a tape pattern under a variable valuation.
- `VarCond` — guard conditions over pattern variables.
- `evalVarCond` — satisfaction of guard conditions.
- `TapePatternSet` — finite list of guarded tape patterns.
- `IsInPatternSet` — configuration membership in a pattern set.
- `IsClosedPatternSet` — inductive closure of a pattern set under accelerated execution.
- `HasCollatzReduction` — existence of a closed pattern set.
- `CollatzHalts` — halting predicate for abstract transition systems.
- `IsValidAcceleration` — sound simulation by a Collatz-like acceleration system.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

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

end BusyBeaver
