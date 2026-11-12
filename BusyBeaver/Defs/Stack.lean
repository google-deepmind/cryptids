/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs.Core
public import BusyBeaver.Defs.Patterns

/-!
# Stack-Word Tape Patterns and Stack Reductions (`BusyBeaver.Defs.Stack`)

Stack-word tape pattern expressions, stacked Collatz reductions, and 2nd-order digit-stack systems:

- `StackSeg` — parametric half-tape segment with variable-length stack words.
- `StackSeg.isWord`, `StackSeg.WellFormed` — stack segment predicates.
- `StackExpr`, `evalStackExpr` — parametric stack-word half-tape expressions.
- `StackPattern`, `StackPattern.WellFormed`, `evalStackPattern` — stack configuration patterns.
- `StackPatternSet`, `IsWellFormedStackPatternSet`, `IsInStackPatternSet` — stack pattern sets.
- `IsClosedStackPatternSet`, `HasStackedCollatzReduction` — stacked Collatz reductions.
- `HalfTapeView`, `applyView` — bounded half-tape view selectors.
- `StackTuple`, `stackDigit`, `stackSepLen` — tuple stacks and separator lengths.
- `IsValidStackPolarity` — digit/separator symbol polarity.
- `IsValidStackModes` — bounded-prefix stack mode views.
- `HasStackReduction` — 2nd-order digit-stack reduction.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

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

/-- Unifying 2nd-Order Digit-Stack Schema (`IsStackCryptid`). -/
def IsStackCryptid {k : ℕ} {Λ : Type*} [Inhabited Λ]
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
    (∃ cfg₀, ReachesPlus M (init []) cfg₀ ∧ IsInStackSystem cfg₀) ∧
    (∀ cfg, IsInStackSystem cfg →
      ∃ cfg', ReachesPlus M cfg cfg' ∧ (IsInStackSystem cfg' ∨ (step M cfg').isNone))

end BusyBeaver
