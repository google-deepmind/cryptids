/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.SetTheory.ZFC.Basic
public import Mathlib.Data.Nat.Digits.Defs
meta import Lean.Elab.Term

/-!
# Cryptids Challenge Specification (`Challenge`)

Self-contained specification module audited against `Cryptids` by `leanprover/comparator`:

- **Constructive gate (`comparator/constructive.json`, `goldbach_21.json`, `zf_380.json`,
  `riemann_104.json`; `permitted_axioms = ["propext", "Quot.sound"]`):**
  The direct simulation state reductions (`Goldbach21`, `Zf380`, `Riemann104`), the `Erdos14`
  reduction, all five `candidate_fewer_states` theorems (including
  `Riemann95.candidate_fewer_states`), and all ZF
  machine-to-proof-search equivalences (`Zf393.halts_zf393_iff_zfInconsistent`,
  `Zf380.Semantics.halts_candidate_iff_zfInconsistent`,
  `Semantics.Zf.halts_zf432_iff_wadeZFInconsistent`) are verified **without `Classical.choice`**
  (`ListBlank` uses primitive `Quot` rather than `Quotient` so `Halts` is choice-free). Because
  `Zf/Soundness.lean` proves `not_zfInconsistent` via `ZFSet.{0}` (`Classical.choice`)—and
  `CIC + EM` proves `Con(ZF)` without choice (`digama0/ConZF`)—disallowing `Classical.choice`
  blocks classical `Con(ZF)` shortcuts for `Halts M ↔ ZFInconsistent` (though Lean's type theory
  remains stronger than `PA`/`ZF`; see `Cryptids/Semantics/README.md`).
- **Full gate (`comparator/all.json`; `permitted_axioms = ["propext", "Quot.sound",
  "Classical.choice"]`):**
  Audits all 27 theorems, including `Riemann95.candidate_equivalent` (which uses
  `Classical.choice` via `Nat.Prime`), classical `ZFSet.{0}` soundness/non-halting, negated-`Π₁⁰`
  Goldbach (`¬ GoldbachConjecture`, which uses Markov's Principle), analytic
  `RiemannHypothesis` equivalences, and the `erdos_15` and `erdos_14` equivalences with
  `ErdosPowersOfTwoConjecture` (`Nat.digits` uses `Classical.choice`;
  `¬ ErdosPowersOfTwoConjecture` also uses Markov's Principle).
-/

meta section
namespace ConjectureMachines.Machines
open Lean Elab Term

private def parseCellStx (cell : String) : TermElabM (TSyntax `term) := do
  if cell == "---" then `(none)
  else match cell.toList with
    | wChar :: dChar :: rest =>
      if rest.isEmpty then throwError "Malformed transition cell: {cell}"
      let wLit := Syntax.mkNumLit (String.singleton wChar)
      let dirStx ← match dChar with
        | 'L' => `(Turing.Dir.left) | 'R' => `(Turing.Dir.right)
        | _ => throwError "Invalid direction in transition cell: {cell}"
      `(some ($wLit, $dirStx, $(Syntax.mkNumLit (String.ofList rest))))
    | _ => throwError "Malformed transition cell: {cell}"

elab "load_machine_rows% " path:str : term <= expectedType? => do
  let contents ← liftM (m := IO) (IO.FS.readFile path.getString)
  let mut rowStxs : Array (TSyntax `term) := #[]
  for rawLine in contents.splitOn "\n" do
    let line := ((rawLine.splitOn "#").headD "").trimAscii.toString
    if !line.isEmpty then
      match (line.splitOn " ").filter (fun s => !s.isEmpty) with
      | [c0, c1] => rowStxs := rowStxs.push (← `([$(← parseCellStx c0), $(← parseCellStx c1)]))
      | _ => throwError "Expected 2 columns in transition table line: {rawLine}"
  elabTerm (← `([$rowStxs,*])) expectedType?
end ConjectureMachines.Machines
end

@[expose] public section
namespace ConjectureMachines
open Turing (Dir)
open StateTransition
export Turing (Dir)

scoped instance (priority := 10000) instLTFinConstructive (n : ℕ) : LT (Fin n) := instLTFin
scoped instance (priority := 10000) instLEFinConstructive (n : ℕ) : LE (Fin n) := instLEFin
scoped instance (priority := 10000) instDecidableEqFinConstructive (n : ℕ) : DecidableEq (Fin n) :=
  instDecidableEqFin n
scoped instance (priority := 10000) instDecidableLTFinConstructive (n : ℕ) : DecidableLT (Fin n) :=
  fun a b => Fin.decLt a b
scoped instance (priority := 10000) instDecidableLEFinConstructive (n : ℕ) : DecidableLE (Fin n) :=
  fun a b => Fin.decLe a b
scoped instance (priority := 10000) instLinearOrderFinConstructive (n : ℕ) :
    LinearOrder (Fin n) where
  le := instLEFin.le
  lt := instLTFin.lt
  le_refl := Fin.le_refl
  le_trans := @Fin.le_trans n
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm := @Fin.le_antisymm n
  le_total := @Fin.le_total n
  toDecidableLE := fun a b => Fin.decLe a b
  toDecidableEq := instDecidableEqFin n
  toDecidableLT := fun a b => Fin.decLt a b
  min a b := if a ≤ b then a else b
  max a b := if a ≤ b then b else a
  min_def _ _ := rfl
  max_def _ _ := rfl
  compare a b := compareOfLessAndEq a b
  compare_eq_compareOfLessAndEq _ _ := rfl

/-- Half-tape of a Turing machine, quotienting `List Γ` by trailing blank symbols
(`Turing.BlankRel`) via Lean's primitive `Quot` rather than `Quotient (BlankRel.setoid Γ)` so that
`ListBlank`, `Tape`, and `Halts` carry zero `Classical.choice` dependency. -/
def ListBlank (Γ : Type*) [Inhabited Γ] :=
  Quot (@Turing.BlankRel Γ _)

instance ListBlank.inhabited {Γ : Type*} [Inhabited Γ] : Inhabited (ListBlank Γ) :=
  ⟨Quot.mk _ []⟩

/-- Quotient map turning a `List Γ` into a `ListBlank Γ`. -/
def ListBlank.mk {Γ : Type*} [Inhabited Γ] : List Γ → ListBlank Γ :=
  Quot.mk _

/-- Lift a blank-extension-invariant function from `List Γ` to `ListBlank Γ`. -/
protected abbrev ListBlank.liftOn {Γ : Type*} [Inhabited Γ] {α : Sort*} (l : ListBlank Γ)
    (f : List Γ → α) (H : ∀ a b, Turing.BlankExtends a b → f a = f b) : α :=
  Quot.liftOn l f fun a b h => h.elim (H a b) fun h' => (H b a h').symm

/-- Head symbol of a `ListBlank`. -/
def ListBlank.head {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) : Γ :=
  l.liftOn List.headI <| by
    rintro (_ | _) _ ⟨_ | _, rfl⟩ <;> rfl

/-- Tail of a `ListBlank`. -/
def ListBlank.tail {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ :=
  l.liftOn (fun l => ListBlank.mk l.tail) <| by
    rintro (_ | _) _ ⟨i, rfl⟩
    · rcases i with - | i <;>
        [exact Quot.sound (Or.inl ⟨0, rfl⟩); exact Quot.sound (Or.inl ⟨i, rfl⟩)]
    · exact Quot.sound (Or.inl ⟨i, rfl⟩)

/-- Prepend a symbol onto a `ListBlank`. -/
def ListBlank.cons {Γ : Type*} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ :=
  l.liftOn (fun l => ListBlank.mk (a :: l)) <| by
    rintro _ _ ⟨i, rfl⟩
    exact Quot.sound (Or.inl ⟨i, rfl⟩)

/-- Bidirectional Turing machine tape over alphabet `Γ`. -/
structure Tape (Γ : Type*) [Inhabited Γ] where
  head : Γ
  left : ListBlank Γ
  right : ListBlank Γ

instance Tape.inhabited {Γ : Type*} [Inhabited Γ] : Inhabited (Tape Γ) :=
  ⟨⟨default, default, default⟩⟩

/-- Shift the tape in response to a head movement `Dir.left` or `Dir.right`. -/
def Tape.move {Γ : Type*} [Inhabited Γ] : Dir → Tape Γ → Tape Γ
  | Dir.left, ⟨a, L, R⟩ => ⟨L.head, L.tail, R.cons a⟩
  | Dir.right, ⟨a, L, R⟩ => ⟨R.head, L.cons a, R.tail⟩

/-- Replace the symbol under the head. -/
def Tape.write {Γ : Type*} [Inhabited Γ] (b : Γ) (T : Tape Γ) : Tape Γ :=
  { T with head := b }

/-- Construct a tape from a left half-tape and an inclusive right half-tape. -/
def Tape.mk' {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) : Tape Γ :=
  ⟨R.head, L, R.tail⟩

/-- Construct a tape from left and inclusive-right `List`s. -/
def Tape.mk₂ {Γ : Type*} [Inhabited Γ] (L R : List Γ) : Tape Γ :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk R)

/-- Construct a tape with `l` starting at the head and blanks to the left. -/
def Tape.mk₁ {Γ : Type*} [Inhabited Γ] (l : List Γ) : Tape Γ :=
  Tape.mk₂ [] l

/-- A Turing machine transition table over `states` states and `symbols` symbols. -/
structure Machine (states symbols : ℕ) where
  transition : Fin states → Fin symbols → Option (Fin symbols × Dir × Fin states)

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- A Turing machine configuration: current state and tape. -/
structure Cfg (states symbols : ℕ) [NeZero symbols] where
  state : Fin states
  tape : Tape (Fin symbols)

/-- Single execution step, returning `none` when no transition is defined. -/
def step (M : Machine states symbols) : Cfg states symbols → Option (Cfg states symbols)
  | ⟨q, T⟩ => (M.transition q T.head).map fun ⟨a, d, q'⟩ => ⟨q', (T.write a).move d⟩

/-- Initial configuration in state `0` on the all-blank tape. -/
def init : Cfg states symbols := ⟨0, Tape.mk₁ []⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
def Halts (M : Machine states symbols) : Prop := (StateTransition.eval (step M) init).Dom

/-- Build a `Machine states symbols` from a list of per-state transition rows. -/
def Machine.ofRows (rows : List (List (Option (Fin symbols × Dir × Fin states)))) :
    Machine states symbols := ⟨fun q a => (rows.getD q.val []).getD a.val none⟩

/-- A Turing machine over `symbols` tape symbols bundled with its non-zero state count. -/
structure BundledMachine (symbols : ℕ) where
  states : ℕ
  [neZeroStates : NeZero states]
  toMachine : Machine states symbols

attribute [instance] BundledMachine.neZeroStates

/-- Bundle a `Machine (states + 1) symbols` into a `BundledMachine symbols`. -/
abbrev Machine.bundle {states symbols : ℕ} (M : Machine (states + 1) symbols) :
    BundledMachine symbols := ⟨states + 1, M⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
abbrev BundledMachine.Halts {symbols : ℕ} [NeZero symbols] (M : BundledMachine symbols) : Prop :=
  ConjectureMachines.Halts M.toMachine

export BundledMachine (Halts)

namespace Machines
/-- Rows of `goldbach25`. -/ def goldbach25Rows : List (List (Option (Fin 2 × Dir × Fin 25))) :=
  load_machine_rows% "baselines/tables/goldbach_25.txt"
/-- 25-state Goldbach baseline. -/ def goldbach25 : Machine 25 2 := Machine.ofRows goldbach25Rows
/-- Rows of `goldbach21`. -/ def goldbach21Rows : List (List (Option (Fin 2 × Dir × Fin 21))) :=
  load_machine_rows% "artifacts/goldbach_21/machine.txt"
/-- 21-state Goldbach candidate. -/ def goldbach21 : Machine 21 2 := Machine.ofRows goldbach21Rows
/-- Rows of `zf432`. -/ def zf432Rows : List (List (Option (Fin 2 × Dir × Fin 432))) :=
  load_machine_rows% "baselines/tables/zf_432.txt"
/-- 432-state ZF baseline. -/ def zf432 : Machine 432 2 := Machine.ofRows zf432Rows
/-- Rows of `zf393`. -/ def zf393Rows : List (List (Option (Fin 2 × Dir × Fin 393))) :=
  load_machine_rows% "baselines/tables/zf_393.txt"
/-- 393-state ZF machine. -/ def zf393 : Machine 393 2 := Machine.ofRows zf393Rows
/-- Rows of `zf380`. -/ def zf380Rows : List (List (Option (Fin 2 × Dir × Fin 380))) :=
  load_machine_rows% "artifacts/zf_380/machine.txt"
/-- 380-state ZF candidate. -/ def zf380 : Machine 380 2 := Machine.ofRows zf380Rows
/-- Rows of `riemann744`. -/ def riemann744Rows : List (List (Option (Fin 2 × Dir × Fin 744))) :=
  load_machine_rows% "baselines/tables/riemann_744.txt"
/-- 744-state RH baseline. -/ def riemann744 : Machine 744 2 := Machine.ofRows riemann744Rows
/-- Rows of `riemann120`. -/ def riemann120Rows : List (List (Option (Fin 2 × Dir × Fin 120))) :=
  load_machine_rows% "baselines/tables/riemann_120.txt"
/-- 120-state RH machine. -/ def riemann120 : Machine 120 2 := Machine.ofRows riemann120Rows
/-- Rows of `riemann104`. -/ def riemann104Rows : List (List (Option (Fin 2 × Dir × Fin 104))) :=
  load_machine_rows% "artifacts/riemann_104/machine.txt"
/-- 104-state RH candidate. -/ def riemann104 : Machine 104 2 := Machine.ofRows riemann104Rows
/-- Rows of `riemann95`. -/ def riemann95Rows : List (List (Option (Fin 2 × Dir × Fin 95))) :=
  load_machine_rows% "artifacts/riemann_95/machine.txt"
/-- 95-state RH candidate. -/ def riemann95 : Machine 95 2 := Machine.ofRows riemann95Rows
/-- Rows of `erdos15`. -/ def erdos15Rows : List (List (Option (Fin 2 × Dir × Fin 15))) :=
  load_machine_rows% "baselines/tables/erdos_15.txt"
/-- 15-state Erdős machine. -/ def erdos15 : Machine 15 2 := Machine.ofRows erdos15Rows
/-- Rows of `erdos14`. -/ def erdos14Rows : List (List (Option (Fin 2 × Dir × Fin 14))) :=
  load_machine_rows% "artifacts/erdos_14/machine.txt"
/-- 14-state Erdős candidate. -/ def erdos14 : Machine 14 2 := Machine.ofRows erdos14Rows
end Machines

/-- **Goldbach's Conjecture**: every even integer greater than 2 is the sum of two primes. -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- Unreduced harmonic numerator `harmNum n = n! * H_n` computed by `riemann.nql`. -/
def harmNum : ℕ → ℕ | 0 => 0 | n + 1 => harmNum n * (n + 1) + n.factorial

/-- Elementary harmonic/LCM counterexample inequality tested at stage `x` by `riemann.nql`. -/
def MatiyasevichRiemannCounterexample (x : ℕ) : Prop :=
  253 < x ∧
  let lcm := (Finset.Icc 1 x).lcm id
  let a := (harmNum lcm - lcm.factorial * x) ^ 2
  let b := lcm.factorial ^ 2
  let c := harmNum x ^ 4 * x
  let d := x.factorial ^ 4
  b * c < a * d

/-- Cantor pairing function `x + (x + y) * (x + y + 1) / 2`. -/
def cantorPair (x y : ℕ) : ℕ := x + (x + y) * (x + y + 1) / 2
/-- Gödel number of $v_x = v_y$. -/ def zfEq (x y : ℕ) : ℕ := cantorPair (cantorPair x y) 0
/-- Gödel number of $v_x \in v_y$. -/ def zfMem (x y : ℕ) : ℕ := cantorPair (cantorPair x y) 1
/-- Gödel number of $\varphi \to \psi$. -/ def zfImp (φ ψ : ℕ) : ℕ := cantorPair (cantorPair φ ψ) 2
/-- Gödel number of $\neg \varphi$. -/ def zfNot (φ : ℕ) : ℕ := cantorPair φ 3
/-- Gödel number of $\forall v_x\, \varphi$. -/ def zfAll (x φ : ℕ) : ℕ :=
  cantorPair (cantorPair x φ) 4
/-- Gödel number of $\exists v_x\, \varphi$. -/ def zfEx (x φ : ℕ) : ℕ := zfNot (zfAll x (zfNot φ))
/-- Gödel number of $\varphi \land \psi$. -/ def zfAnd (φ ψ : ℕ) : ℕ := zfNot (zfImp φ (zfNot ψ))

/-- Well-formed formulas of first-order set theory with variables indexed by `ℕ`. -/
inductive ZFFormula : Type where
  | eq (x y : ℕ) : ZFFormula | mem (x y : ℕ) : ZFFormula | imp (φ ψ : ZFFormula) : ZFFormula
  | not (φ : ZFFormula) : ZFFormula | all (x : ℕ) (φ : ZFFormula) : ZFFormula
  deriving DecidableEq, Repr

/-- Gödel number of a `ZFFormula`. -/
def ZFFormula.code : ZFFormula → ℕ
  | .eq x y => zfEq x y | .mem x y => zfMem x y | .imp φ ψ => zfImp φ.code ψ.code
  | .not φ => zfNot φ.code | .all x φ => zfAll x φ.code

/-- Tarski satisfaction of a `ZFFormula` in `ZFSet.{u}` under assignment `v`. -/
def ZFFormula.Holds (v : ℕ → ZFSet.{u}) : ZFFormula → Prop
  | .eq x y => v x = v y | .mem x y => v x ∈ v y | .imp φ ψ => φ.Holds v → ψ.Holds v
  | .not φ => ¬ φ.Holds v | .all x φ => ∀ s : ZFSet.{u}, φ.Holds (Function.update v x s)

/-- Axiom `B1`. -/ def axB1 (φ ψ χ : ℕ) : ℕ := zfImp (zfImp φ ψ) (zfImp (zfImp ψ χ) (zfImp φ χ))
/-- Axiom `B2`. -/ def axB2 (φ : ℕ) : ℕ := zfImp (zfImp (zfNot φ) φ) φ
/-- Axiom `B3`. -/ def axB3 (φ ψ : ℕ) : ℕ := zfImp φ (zfImp (zfNot φ) ψ)
/-- Axiom `B4`. -/ def axB4 (x φ ψ : ℕ) : ℕ :=
  zfImp (zfAll x (zfImp φ ψ)) (zfImp (zfAll x φ) (zfAll x ψ))
/-- Axiom `B6a`. -/ def axB6a (x y z : ℕ) : ℕ :=
  zfAnd (zfImp (zfEq x y) (zfAll z (zfEq x y))) (zfImp (zfMem x y) (zfAll z (zfMem x y)))
/-- Axiom `B6b`. -/ def axB6b (x y φ : ℕ) : ℕ := zfImp (zfAll x (zfAll y φ)) (zfAll y (zfAll x φ))
/-- Axiom `B6c`. -/ def axB6c (x φ : ℕ) : ℕ := zfImp (zfEx x (zfAll x φ)) φ
/-- Axiom `B7`. -/ def axB7 (x y : ℕ) : ℕ := zfEx x (zfEq x y)
/-- Axiom `B8a`. -/ def axB8a (x y z : ℕ) : ℕ := zfImp (zfEq x y) (zfImp (zfEq x z) (zfEq y z))
/-- Axiom `B8b`. -/ def axB8b (x y z : ℕ) : ℕ := zfImp (zfEq x y) (zfImp (zfMem x z) (zfMem y z))
/-- Axiom `B8c`. -/ def axB8c (x y z : ℕ) : ℕ := zfImp (zfEq x y) (zfImp (zfMem z x) (zfMem z y))
/-- Axiom `EXT`. -/ def axExt : ℕ :=
  zfImp (zfAll 2 (zfAnd (zfImp (zfMem 2 0) (zfMem 2 1)) (zfImp (zfMem 2 1) (zfMem 2 0)))) (zfEq 0 1)
/-- Helper for `axRep`. -/ def axRepRhs (φ : ℕ) : ℕ := zfEx 3 (zfAnd (zfMem 3 0) (zfAll 1 φ))
/-- Axiom scheme `REP`. -/ def axRep (φ : ℕ) : ℕ :=
  zfImp (zfAll 3 (zfEx 1 (zfAll 2 (zfImp (zfAll 1 φ) (zfEq 2 1)))))
    (zfEx 1 (zfAll 2 (zfAnd (zfImp (zfMem 2 1) (axRepRhs φ)) (zfImp (axRepRhs φ) (zfMem 2 1)))))
/-- Axiom `POW`. -/ def axPow : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfAll 3 (zfImp (zfMem 3 2) (zfMem 3 0))) (zfMem 2 1)))
/-- Axiom `UNI`. -/ def axUni : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfEx 3 (zfAnd (zfMem 2 3) (zfMem 3 0))) (zfMem 2 1)))
/-- Helper formula used in `axInf`. -/ def axInfSingleton : ℕ :=
  zfAll 1 (zfAnd (zfImp (zfMem 1 2) (zfEq 1 0)) (zfImp (zfEq 1 0) (zfMem 1 2)))
/-- Axiom `INF`. -/ def axInf : ℕ :=
  zfEx 1
    (zfAnd (zfMem 0 1) (zfAll 0 (zfImp (zfMem 0 1) (zfEx 2 (zfAnd (zfMem 2 1) axInfSingleton)))))

/-- O'Rear's `zf2.nql` Hilbert system for Zermelo–Fraenkel set theory. -/
inductive ZFProvable : ℕ → Prop where
  | moot : ZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : ZFProvable φ → ZFProvable (zfImp φ ψ) → ZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : ZFProvable φ → ZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : ZFProvable (axB1 φ ψ χ) | b2 (φ : ℕ) : ZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : ZFProvable (axB3 φ ψ) | b4 (x φ ψ : ℕ) : ZFProvable (axB4 x φ ψ)
  | b6a (x y z : ℕ) (hxz : x ≠ z) (hzy : z ≠ y) : ZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : ZFProvable (axB6b x y φ) | b6c (x φ : ℕ) : ZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : ZFProvable (axB7 x y) | b8a (x y z : ℕ) : ZFProvable (axB8a x y z)
  | b8b (x y z : ℕ) : ZFProvable (axB8b x y z) | b8c (x y z : ℕ) : ZFProvable (axB8c x y z)
  | ext : ZFProvable axExt | rep (φ : ℕ) : ZFProvable (axRep φ) | pow : ZFProvable axPow
  | uni : ZFProvable axUni | inf : ZFProvable axInf

/-- Inconsistency of `ZFProvable` ($v_0 \in v_0$). -/
def ZFInconsistent : Prop := ZFProvable (zfMem 0 0)

/-- Wade's `zf_432_wade.tm` Hilbert system for Zermelo–Fraenkel set theory. -/
inductive WadeZFProvable : ℕ → Prop where
  | moot : WadeZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : WadeZFProvable φ → WadeZFProvable (zfImp φ ψ) → WadeZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : WadeZFProvable φ → WadeZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : WadeZFProvable (axB1 φ ψ χ) | b2 (φ : ℕ) : WadeZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : WadeZFProvable (axB3 φ ψ) | b4 (x φ ψ : ℕ) : WadeZFProvable (axB4 x φ ψ)
  | b6a_wade (x y z : ℕ) (hxz : x ≠ z) (hy : y ≠ 0) : WadeZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : WadeZFProvable (axB6b x y φ) | b6c (x φ : ℕ) : WadeZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : WadeZFProvable (axB7 x y) | b8a_zero (x y : ℕ) : WadeZFProvable (axB8a x y 0)
  | b8b (x y z : ℕ) : WadeZFProvable (axB8b x y z)
  | b8c_zero (x y : ℕ) : WadeZFProvable (axB8c x y 0)
  | ext : WadeZFProvable axExt | rep (φ : ℕ) : WadeZFProvable (axRep φ) | pow : WadeZFProvable axPow
  | uni : WadeZFProvable axUni | inf : WadeZFProvable axInf

/-- Inconsistency of `WadeZFProvable` ($v_0 \in v_0$). -/
def WadeZFInconsistent : Prop := WadeZFProvable (zfMem 0 0)

/-- **Erdős's conjecture on powers of two** (Erdős 1979): for every `n > 8`, the base-3
expansion of `2 ^ n` contains the digit `2`. -/
def ErdosPowersOfTwoConjecture : Prop :=
  ∀ n : ℕ, 8 < n → 2 ∈ Nat.digits 3 (2 ^ n)

namespace Goldbach21
/-- 25-state Goldbach reference machine (`goldbach_25`, Yao & Leng 2024). -/
abbrev reference : BundledMachine 2 := Machines.goldbach25.bundle
/-- 21-state Goldbach candidate machine (`goldbach_21`). -/
abbrev candidate : BundledMachine 2 := Machines.goldbach21.bundle
theorem candidate_fewer_states : candidate.states < reference.states := by sorry
theorem candidate_equivalent : Halts candidate ↔ Halts reference := by sorry
namespace Semantics
theorem halts_reference_iff_not_goldbach : Halts reference ↔ ¬ GoldbachConjecture := by sorry
theorem halts_candidate_iff_not_goldbach : Halts candidate ↔ ¬ GoldbachConjecture := by sorry
end Semantics
end Goldbach21

namespace Zf393
/-- 393-state ZF consistency machine (`zf_393`, Wade 2026). -/
abbrev zf393 : Machine 393 2 := Machines.zf393
theorem halts_zf393_iff_zfInconsistent : ConjectureMachines.Halts zf393 ↔ ZFInconsistent := by
  sorry
theorem not_halts_zf393 : ¬ ConjectureMachines.Halts zf393 := by sorry
end Zf393

namespace Zf380
/-- 393-state ZF consistency reference machine (`zf_393`, Wade 2026). -/
abbrev reference : BundledMachine 2 := Machines.zf393.bundle
/-- 380-state ZF consistency candidate machine (`zf_380`). -/
abbrev candidate : BundledMachine 2 := Machines.zf380.bundle
theorem candidate_fewer_states : candidate.states < reference.states := by sorry
theorem candidate_equivalent : Halts candidate ↔ Halts reference := by sorry
namespace Semantics
theorem halts_candidate_iff_zfInconsistent : Halts candidate ↔ ZFInconsistent := by sorry
theorem not_halts_candidate : ¬ Halts candidate := by sorry
end Semantics
end Zf380

namespace Semantics.Zf
theorem zfProvable_sound_zfSet (φ : ZFFormula) (h : ZFProvable φ.code)
    (v : ℕ → ZFSet.{0}) : φ.Holds v := by sorry
theorem not_zfInconsistent : ¬ ZFInconsistent := by sorry
theorem halts_zf432_iff_wadeZFInconsistent :
    ConjectureMachines.Halts Machines.zf432 ↔ WadeZFInconsistent := by sorry
end Semantics.Zf

namespace Semantics.Riemann
theorem halts_riemann744_iff_exists_counterexample :
    ConjectureMachines.Halts Machines.riemann744 ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x :=
  by sorry
theorem halts_riemann744_iff_not_riemannHypothesis :
    ConjectureMachines.Halts Machines.riemann744 ↔ ¬ RiemannHypothesis := by sorry
end Semantics.Riemann

namespace Riemann120
/-- 120-state Riemann Hypothesis machine (`riemann_120`, Shunia 2026). -/
abbrev riemann120 : Machine 120 2 := Machines.riemann120
theorem halts_riemann120_iff_not_riemannHypothesis :
    ConjectureMachines.Halts riemann120 ↔ ¬ RiemannHypothesis := by sorry
end Riemann120

namespace Riemann104
/-- 120-state Riemann Hypothesis reference machine (`riemann_120`, Shunia 2026). -/
abbrev reference : BundledMachine 2 := Machines.riemann120.bundle
/-- 104-state Riemann Hypothesis candidate machine (`riemann_104`). -/
abbrev candidate : BundledMachine 2 := Machines.riemann104.bundle
theorem candidate_fewer_states : candidate.states < reference.states := by sorry
theorem candidate_equivalent : Halts candidate ↔ Halts reference := by sorry
namespace Semantics
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts candidate ↔ ¬ RiemannHypothesis := by sorry
end Semantics
end Riemann104

namespace Riemann95
/-- 104-state Riemann Hypothesis reference machine. -/
abbrev reference : BundledMachine 2 := Machines.riemann104.bundle
/-- 95-state Riemann Hypothesis candidate machine. -/
abbrev candidate : BundledMachine 2 := Machines.riemann95.bundle
theorem candidate_fewer_states : candidate.states < reference.states := by sorry
theorem candidate_equivalent : Halts candidate ↔ Halts reference := by sorry
namespace Semantics
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts candidate ↔ ¬ RiemannHypothesis := by sorry
end Semantics
end Riemann95

namespace Erdos15
/-- 15-state Erdős powers-of-two machine (`erdos_15`, Stérin & Woods 2021). -/
abbrev erdos15 : Machine 15 2 := Machines.erdos15
theorem halts_erdos15_iff_exists_counterexample :
    ConjectureMachines.Halts erdos15 ↔ ∃ n : ℕ, 8 < n ∧ 2 ∉ Nat.digits 3 (2 ^ n) := by sorry
theorem halts_erdos15_iff_not_erdosPowersOfTwo :
    ConjectureMachines.Halts erdos15 ↔ ¬ ErdosPowersOfTwoConjecture := by sorry
end Erdos15

namespace Erdos14
/-- 15-state Erdős powers-of-two reference machine (`erdos_15`, Stérin & Woods 2021). -/
abbrev reference : BundledMachine 2 := Machines.erdos15.bundle
/-- 14-state Erdős powers-of-two candidate machine (`erdos_14`, Stérin 2026). -/
abbrev candidate : BundledMachine 2 := Machines.erdos14.bundle
theorem candidate_fewer_states : candidate.states < reference.states := by sorry
theorem candidate_equivalent : Halts candidate ↔ Halts reference := by sorry
namespace Semantics
theorem halts_candidate_iff_not_erdosPowersOfTwo :
    Halts candidate ↔ ¬ ErdosPowersOfTwoConjecture := by sorry
end Semantics
end Erdos14

end ConjectureMachines
