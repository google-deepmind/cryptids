/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Core Turing Machine Semantics (`BusyBeaver.Defs.Core`)

Canonical Post-Turing machine execution model, configuration reachability, and halting
predicates for Busy Beaver holdouts:

- `Stmt` — atomic tape write-and-move action.
- `Machine` — Post-Turing transition function.
- `Cfg` — machine configuration (optional state + doubly-infinite tape).
- `Cfg.headRight`, `Cfg.headLeft` — directed-head configuration constructors.
- `step` — single-step execution semantics.
- `init` — initial configuration on a given tape prefix.
- `multiStep` — `n`-step execution semantics.
- `ReachesIn` — exact `n`-step reachability.
- `ReachesStar` — reflexive-transitive multi-step reachability.
- `ReachesPlus` — positive-step multi-step reachability.
- `instHPowListNat` — finite list repetition `l ^ n`.
- `IsHaltingConfiguration` — configuration with no valid next step.
- `IsHalt` — blank-tape halting predicate.
- `IsNotHalt` (`IsDoesNotHalt`) — blank-tape non-halting predicate.
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
scoped notation3 l " {{" q "}}> " r => (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg _ _)
scoped notation3 l " <{{" q "}} " r => (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg _ _)

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



/-- Atomic `NeZero (k + 2)` instance for alphabet size `Fin (k + 2)`.
Ensures `HasStackReduction` and `HasOdometerReduction` synthesize an atomic constant
rather than composite proof `instNeZeroNatHAdd_1 k 2`, avoiding per-module `_proof_1`
auxiliary definitions that break cross-module AST equality in the comparator.
Priority `default + 1` is required because at default priority Lean prioritizes
Mathlib's composite `instNeZeroNatHAdd_1`. -/
instance (priority := default + 1) instNeZeroK2 (k : ℕ) : @NeZero ℕ Zero.ofOfNat0 (k + 2) :=
  ⟨Nat.succ_ne_zero (k + 1)⟩

/-- Atomic `NeZero 2` instance with higher priority than `instNeZeroK2`.
Ensures literal `Fin 2` does not match `instNeZeroK2 0`, which would embed a dependency
on `0` into the typeclass instance and break `generalize 0 = n` in downstream proofs. -/
instance (priority := default + 2) instNeZeroTwoLit : @NeZero ℕ Zero.ofOfNat0 2 :=
  ⟨Nat.succ_ne_zero 1⟩

end BusyBeaver
