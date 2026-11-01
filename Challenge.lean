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
  `Riemann95.candidate_fewer_states`), all ZF
  machine-to-proof-search equivalences (`Zf393.halts_zf393_iff_zfInconsistent`,
  `Zf380.Semantics.halts_candidate_iff_zfInconsistent`,
  `Semantics.Zf.halts_zf432_iff_wadeZFInconsistent`), and first-order Peano Arithmetic (`PA`)
  consistency and $\Sigma_1^0$ standard-model adequacy (`Semantics.PA.not_paProvable_false`,
  `Semantics.PA.paHalts_holds_iff_halts`, `Semantics.PA.paZFInconsistent_holds_iff_zfInconsistent`)
  are verified **without `Classical.choice`** (`ListBlank` uses primitive `Quot` rather than
  `Quotient` so `Halts` is choice-free). Because `Zf/Soundness.lean` proves `not_zfInconsistent`
  via `ZFSet.{0}` (`Classical.choice`)—and `CIC + EM` proves `Con(ZF)` without choice
  (`digama0/ConZF`)—disallowing `Classical.choice` blocks classical `Con(ZF)` shortcuts for
  `Halts M ↔ ZFInconsistent`, while deeply embedded `PAProvable` provides a weak first-order
  metatheory that cannot prove `Con(PA)` or `Con(ZF)` (see `Cryptids/Semantics/README.md`).
- **Full gate (`comparator/all.json`; `permitted_axioms = ["propext", "Quot.sound",
  "Classical.choice"]`):**
  Audits all 34 theorems, including `Riemann95.candidate_equivalent` (which uses
  `Classical.choice` via `Nat.Prime`), classical `PA` and `ZFSet.{0}` soundness/non-halting,
  negated-`Π₁⁰` Goldbach (`¬ GoldbachConjecture`, which uses Markov's Principle), analytic
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

section
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
end

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

/-- First-order terms in the language of Peano Arithmetic
$\mathcal{L}_{\mathrm{PA}} = \{0, S, +, \times\}$. -/
inductive PATerm : Type where
  | var (x : ℕ) : PATerm
  | zero : PATerm
  | succ (t : PATerm) : PATerm
  | add (t₁ t₂ : PATerm) : PATerm
  | mul (t₁ t₂ : PATerm) : PATerm
  deriving DecidableEq, Repr

/-- Standard numeral $\overline{n}$ in $\mathcal{L}_{\mathrm{PA}}$. -/
def PATerm.ofNat : ℕ → PATerm
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

/-- Whether variable `x` occurs in a `PATerm`. -/
def PATerm.hasVar (x : ℕ) : PATerm → Bool
  | .var y => y == x
  | .zero => false
  | .succ t => t.hasVar x
  | .add t₁ t₂ | .mul t₁ t₂ => t₁.hasVar x || t₂.hasVar x

/-- Smallest variable index strictly greater than every variable occurring in a `PATerm`. -/
def PATerm.freshVar : PATerm → ℕ
  | .var x => x + 1
  | .zero => 0
  | .succ t => t.freshVar
  | .add t₁ t₂ | .mul t₁ t₂ => max t₁.freshVar t₂.freshVar

/-- Substitute term `s` for variable `x` in a `PATerm`. -/
def PATerm.subst : PATerm → ℕ → PATerm → PATerm
  | .var y, x, s => if y == x then s else .var y
  | .zero, _, _ => .zero
  | .succ t, x, s => .succ (t.subst x s)
  | .add t₁ t₂, x, s => .add (t₁.subst x s) (t₂.subst x s)
  | .mul t₁ t₂, x, s => .mul (t₁.subst x s) (t₂.subst x s)

/-- Evaluate a `PATerm` in the standard model `ℕ` under assignment `v`. -/
def PATerm.eval (v : ℕ → ℕ) : PATerm → ℕ
  | .var x => v x
  | .zero => 0
  | .succ t => t.eval v + 1
  | .add t₁ t₂ => t₁.eval v + t₂.eval v
  | .mul t₁ t₂ => t₁.eval v * t₂.eval v

/-- First-order formulas of Peano Arithmetic with variables indexed by `ℕ`. -/
inductive PAFormula : Type where
  | bot : PAFormula
  | eq (t₁ t₂ : PATerm) : PAFormula
  | and (φ ψ : PAFormula) : PAFormula
  | or (φ ψ : PAFormula) : PAFormula
  | imp (φ ψ : PAFormula) : PAFormula
  | all (x : ℕ) (φ : PAFormula) : PAFormula
  | ex (x : ℕ) (φ : PAFormula) : PAFormula
  deriving DecidableEq, Repr

/-- Negation $\neg \varphi := \varphi \to \bot$. -/
abbrev PAFormula.not (φ : PAFormula) : PAFormula := .imp φ .bot

/-- Bi-implication $\varphi \leftrightarrow \psi := (\varphi \to \psi) \land (\psi \to \varphi)$. -/
abbrev PAFormula.iff (φ ψ : PAFormula) : PAFormula := .and (.imp φ ψ) (.imp ψ φ)

/-- Inequality $s \neq t := \neg (s = t)$. -/
abbrev paNe (s t : PATerm) : PAFormula := .not (.eq s t)

/-- Non-strict inequality $a \le b := \exists k,\, a + k = b$ with a fresh witness variable `k`. -/
def paLe (a b : PATerm) : PAFormula :=
  let k := max a.freshVar b.freshVar
  .ex k (.eq (.add a (.var k)) b)

/-- Strict inequality $a < b := S(a) \le b$. -/
def paLt (a b : PATerm) : PAFormula :=
  paLe (.succ a) b

/-- Finite disjunction of a list of `PAFormula`s. -/
def paDisjList : List PAFormula → PAFormula
  | [] => .bot
  | [φ] => φ
  | φ :: rest => .or φ (paDisjList rest)

/-- Whether variable `x` occurs free in a `PAFormula`. -/
def PAFormula.hasFree (x : ℕ) : PAFormula → Bool
  | .bot => false
  | .eq t₁ t₂ => t₁.hasVar x || t₂.hasVar x
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.hasFree x || ψ.hasFree x
  | .all y φ | .ex y φ => !(y == x) && φ.hasFree x

/-- Whether term `s` is free for `x` in `φ` (no free occurrence of `x` lies under a binder
for any variable occurring in `s`). -/
def PAFormula.freeFor (x : ℕ) (s : PATerm) : PAFormula → Bool
  | .bot | .eq _ _ => true
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.freeFor x s && ψ.freeFor x s
  | .all y φ | .ex y φ => (y == x) || ((!φ.hasFree x || !s.hasVar y) && φ.freeFor x s)

/-- Substitute term `s` for free occurrences of variable `x` in `φ`. -/
def PAFormula.subst (x : ℕ) (s : PATerm) : PAFormula → PAFormula
  | .bot => .bot
  | .eq t₁ t₂ => .eq (t₁.subst x s) (t₂.subst x s)
  | .and φ ψ => .and (φ.subst x s) (ψ.subst x s)
  | .or φ ψ => .or (φ.subst x s) (ψ.subst x s)
  | .imp φ ψ => .imp (φ.subst x s) (ψ.subst x s)
  | .all y φ => if y == x then .all y φ else .all y (φ.subst x s)
  | .ex y φ => if y == x then .ex y φ else .ex y (φ.subst x s)

/-- Standard Tarski satisfaction of a `PAFormula` in `ℕ` under variable assignment `v`. -/
def PAFormula.Holds (v : ℕ → ℕ) : PAFormula → Prop
  | .bot => False
  | .eq t₁ t₂ => t₁.eval v = t₂.eval v
  | .and φ ψ => φ.Holds v ∧ ψ.Holds v
  | .or φ ψ => φ.Holds v ∨ ψ.Holds v
  | .imp φ ψ => φ.Holds v → ψ.Holds v
  | .all x φ => ∀ a : ℕ, φ.Holds (Function.update v x a)
  | .ex x φ => ∃ a : ℕ, φ.Holds (Function.update v x a)

/-- Standard Hilbert proof system for first-order Peano Arithmetic ($\mathrm{PA}$), combining
classical first-order logic with equality, the six defining equations of $0, S, +, \times$, and the
full first-order induction schema. -/
inductive PAProvable : PAFormula → Prop where
  | mp {φ ψ : PAFormula} : PAProvable φ → PAProvable (.imp φ ψ) → PAProvable ψ
  | gen (x : ℕ) {φ : PAFormula} : PAProvable φ → PAProvable (.all x φ)
  | imp_k (φ ψ : PAFormula) : PAProvable (.imp φ (.imp ψ φ))
  | imp_s (φ ψ χ : PAFormula) :
      PAProvable (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | dne (φ : PAFormula) : PAProvable (.imp (.not (.not φ)) φ)
  | and_intro (φ ψ : PAFormula) : PAProvable (.imp φ (.imp ψ (.and φ ψ)))
  | and_left (φ ψ : PAFormula) : PAProvable (.imp (.and φ ψ) φ)
  | and_right (φ ψ : PAFormula) : PAProvable (.imp (.and φ ψ) ψ)
  | or_left (φ ψ : PAFormula) : PAProvable (.imp φ (.or φ ψ))
  | or_right (φ ψ : PAFormula) : PAProvable (.imp ψ (.or φ ψ))
  | or_elim (φ ψ χ : PAFormula) :
      PAProvable (.imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (.or φ ψ) χ)))
  | all_imp (x : ℕ) (φ ψ : PAFormula) :
      PAProvable (.imp (.all x (.imp φ ψ)) (.imp (.all x φ) (.all x ψ)))
  | all_vacuous (x : ℕ) (φ : PAFormula) (h : φ.hasFree x = false) :
      PAProvable (.imp φ (.all x φ))
  | all_elim (x : ℕ) (t : PATerm) (φ : PAFormula) (h : φ.freeFor x t = true) :
      PAProvable (.imp (.all x φ) (φ.subst x t))
  | ex_intro (x : ℕ) (t : PATerm) (φ : PAFormula) (h : φ.freeFor x t = true) :
      PAProvable (.imp (φ.subst x t) (.ex x φ))
  | ex_elim (x : ℕ) (φ ψ : PAFormula) (h : ψ.hasFree x = false) :
      PAProvable (.imp (.all x (.imp φ ψ)) (.imp (.ex x φ) ψ))
  | eq_refl (t : PATerm) : PAProvable (.eq t t)
  | eq_subst (x : ℕ) (s t : PATerm) (φ : PAFormula)
      (hs : φ.freeFor x s = true) (ht : φ.freeFor x t = true) :
      PAProvable (.imp (.eq s t) (.imp (φ.subst x s) (φ.subst x t)))
  | pa_zero_ne_succ : PAProvable (.not (.eq (.succ (.var 0)) .zero))
  | pa_succ_inj :
      PAProvable (.imp (.eq (.succ (.var 0)) (.succ (.var 1))) (.eq (.var 0) (.var 1)))
  | pa_add_zero : PAProvable (.eq (.add (.var 0) .zero) (.var 0))
  | pa_add_succ :
      PAProvable (.eq (.add (.var 0) (.succ (.var 1))) (.succ (.add (.var 0) (.var 1))))
  | pa_mul_zero : PAProvable (.eq (.mul (.var 0) .zero) .zero)
  | pa_mul_succ :
      PAProvable (.eq (.mul (.var 0) (.succ (.var 1))) (.add (.mul (.var 0) (.var 1)) (.var 0)))
  | pa_ind (x : ℕ) (φ : PAFormula) :
      PAProvable (.imp (φ.subst x .zero)
        (.imp (.all x (.imp φ (φ.subst x (.succ (.var x))))) (.all x φ)))

/-- Polynomial characterization $2 z = 2 x + (x + y)(x + y + 1)$ of `z = cantorPair x y`. -/
def paCantorPairEq (x y z : PATerm) : PAFormula :=
  let s := PATerm.add x y
  .eq (.mul (.ofNat 2) z) (.add (.mul (.ofNat 2) x) (.mul s (.succ s)))

/-- Gödel's $\beta$-function graph $\beta(c, d, i) = r$, defined by
$\exists q,\; c = q \cdot (1 + (i + 1) d) + r \land r < 1 + (i + 1) d$. -/
def paBetaEq (c d i r : PATerm) : PAFormula :=
  let m := PATerm.succ (.mul (.succ i) d)
  let q := max (max c.freshVar m.freshVar) r.freshVar
  .ex q (.and (.eq c (.add (.mul (.var q) m) r)) (paLt r m))

/-- Symbolic Cantor-pairing expression over variable indices and small natural constants,
used to arithmetize nested Cantor codes without expanding large numerals. -/
inductive PAZFTerm : Type where
  | var (x : ℕ) : PAZFTerm
  | const (n : ℕ) : PAZFTerm
  | pair (a b : PAZFTerm) : PAZFTerm
  deriving DecidableEq, Repr

/-- Number of fresh existential variables allocated when translating a `PAZFTerm`. -/
def PAZFTerm.numVars : PAZFTerm → ℕ
  | .var _ | .const _ => 0
  | .pair a b => 2 + a.numVars + b.numVars

/-- Translate `out = e` into a `PAFormula`, allocating fresh intermediate variables starting at
`base`. -/
def PAZFTerm.eqFormula : PAZFTerm → PATerm → ℕ → PAFormula
  | .var x, out, _ => .eq out (.var x)
  | .const n, out, _ => .eq out (.ofNat n)
  | .pair a b, out, base =>
    .ex base (.ex (base + 1)
      (.and (paCantorPairEq (.var base) (.var (base + 1)) out)
        (.and (a.eqFormula (.var base) (base + 2))
          (b.eqFormula (.var (base + 1)) (base + 2 + a.numVars)))))

/-- Symbolic Cantor code `(q, (h, (L, R)))` of a binary Turing machine configuration. -/
def pzPackCfg (q h : ℕ) (L R : PAZFTerm) : PAZFTerm :=
  .pair (.const q) (.pair (.const h) (.pair L R))

/-- Single-step relation of a 2-symbol Turing machine `M` between configuration codes `.var 4`
and `.var 5`. -/
def paStep {states : ℕ} (M : Machine states 2) : PAFormula :=
  paDisjList <| (List.finRange states).flatMap fun q =>
    (List.finRange 2).flatMap fun h =>
      match M.transition q h with
      | none => []
      | some (w, .right, q') =>
        [0, 1].map fun h' =>
          .ex 6 (.ex 7 (.ex 8 (.ex 9
            (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
              (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
                (.and (.eq (.var 8) (.add (.mul (.ofNat 2) (.var 6)) (.ofNat w.val)))
                  (.eq (.var 7) (.add (.mul (.ofNat 2) (.var 9)) (.ofNat h')))))))))
      | some (w, .left, q') =>
        [0, 1].map fun h' =>
          .ex 6 (.ex 7 (.ex 8 (.ex 9
            (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
              (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
                (.and (.eq (.var 6) (.add (.mul (.ofNat 2) (.var 8)) (.ofNat h')))
                  (.eq (.var 9) (.add (.mul (.ofNat 2) (.var 7)) (.ofNat w.val)))))))))

/-- Undefined-transition (halted) predicate for a 2-symbol Turing machine `M` at configuration
code `.var 4`. -/
def paHalted {states : ℕ} (M : Machine states 2) : PAFormula :=
  paDisjList <| (List.finRange states).flatMap fun q =>
    (List.finRange 2).flatMap fun h =>
      match M.transition q h with
      | some _ => []
      | none => [.ex 6 (.ex 7 ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10))]

/-- Closed $\Sigma_1^0$ $\mathcal{L}_{\mathrm{PA}}$-sentence asserting that the 2-symbol Turing
machine `M` halts when started in state `0` on the all-blank tape (encoded by `0`). -/
def paHalts {states : ℕ} (M : Machine states 2) : PAFormula :=
  .ex 0 (.ex 1 (.ex 2
    (.and (paBetaEq (.var 1) (.var 2) .zero .zero)
      (.and
        (.all 3 (.imp (paLt (.var 3) (.var 0))
          (.ex 4 (.ex 5
            (.and (paBetaEq (.var 1) (.var 2) (.var 3) (.var 4))
              (.and (paBetaEq (.var 1) (.var 2) (.succ (.var 3)) (.var 5))
                (paStep M)))))))
        (.ex 4
          (.and (paBetaEq (.var 1) (.var 2) (.var 0) (.var 4))
            (paHalted M)))))))

/-- Symbolic `PAZFTerm` constructors mirroring `zfEq..axInf`. -/
def pzEq (x y : PAZFTerm) : PAZFTerm := .pair (.pair x y) (.const 0)
/-- Symbolic `PAZFTerm` for `zfMem`. -/
def pzMem (x y : PAZFTerm) : PAZFTerm := .pair (.pair x y) (.const 1)
/-- Symbolic `PAZFTerm` for `zfImp`. -/
def pzImp (φ ψ : PAZFTerm) : PAZFTerm := .pair (.pair φ ψ) (.const 2)
/-- Symbolic `PAZFTerm` for `zfNot`. -/
def pzNot (φ : PAZFTerm) : PAZFTerm := .pair φ (.const 3)
/-- Symbolic `PAZFTerm` for `zfAll`. -/
def pzAll (x φ : PAZFTerm) : PAZFTerm := .pair (.pair x φ) (.const 4)
/-- Symbolic `PAZFTerm` for `zfEx`. -/
def pzEx (x φ : PAZFTerm) : PAZFTerm := pzNot (pzAll x (pzNot φ))
/-- Symbolic `PAZFTerm` for `zfAnd`. -/
def pzAnd (φ ψ : PAZFTerm) : PAZFTerm := pzNot (pzImp φ (pzNot ψ))
/-- Symbolic `PAZFTerm` for `axB1`. -/
def pzB1 (φ ψ χ : PAZFTerm) : PAZFTerm := pzImp (pzImp φ ψ) (pzImp (pzImp ψ χ) (pzImp φ χ))
/-- Symbolic `PAZFTerm` for `axB2`. -/
def pzB2 (φ : PAZFTerm) : PAZFTerm := pzImp (pzImp (pzNot φ) φ) φ
/-- Symbolic `PAZFTerm` for `axB3`. -/
def pzB3 (φ ψ : PAZFTerm) : PAZFTerm := pzImp φ (pzImp (pzNot φ) ψ)
/-- Symbolic `PAZFTerm` for `axB4`. -/
def pzB4 (x φ ψ : PAZFTerm) : PAZFTerm :=
  pzImp (pzAll x (pzImp φ ψ)) (pzImp (pzAll x φ) (pzAll x ψ))
/-- Symbolic `PAZFTerm` for `axB6a`. -/
def pzB6a (x y z : PAZFTerm) : PAZFTerm :=
  pzAnd (pzImp (pzEq x y) (pzAll z (pzEq x y))) (pzImp (pzMem x y) (pzAll z (pzMem x y)))
/-- Symbolic `PAZFTerm` for `axB6b`. -/
def pzB6b (x y φ : PAZFTerm) : PAZFTerm := pzImp (pzAll x (pzAll y φ)) (pzAll y (pzAll x φ))
/-- Symbolic `PAZFTerm` for `axB6c`. -/
def pzB6c (x φ : PAZFTerm) : PAZFTerm := pzImp (pzEx x (pzAll x φ)) φ
/-- Symbolic `PAZFTerm` for `axB7`. -/
def pzB7 (x y : PAZFTerm) : PAZFTerm := pzEx x (pzEq x y)
/-- Symbolic `PAZFTerm` for `axB8a`. -/
def pzB8a (x y z : PAZFTerm) : PAZFTerm := pzImp (pzEq x y) (pzImp (pzEq x z) (pzEq y z))
/-- Symbolic `PAZFTerm` for `axB8b`. -/
def pzB8b (x y z : PAZFTerm) : PAZFTerm := pzImp (pzEq x y) (pzImp (pzMem x z) (pzMem y z))
/-- Symbolic `PAZFTerm` for `axB8c`. -/
def pzB8c (x y z : PAZFTerm) : PAZFTerm := pzImp (pzEq x y) (pzImp (pzMem z x) (pzMem z y))
/-- Symbolic `PAZFTerm` for `axExt`. -/
def pzExt : PAZFTerm :=
  pzImp
    (pzAll (.const 2)
      (pzAnd (pzImp (pzMem (.const 2) (.const 0)) (pzMem (.const 2) (.const 1)))
        (pzImp (pzMem (.const 2) (.const 1)) (pzMem (.const 2) (.const 0)))))
    (pzEq (.const 0) (.const 1))
/-- Symbolic `PAZFTerm` for `axRepRhs`. -/
def pzRepRhs (φ : PAZFTerm) : PAZFTerm :=
  pzEx (.const 3) (pzAnd (pzMem (.const 3) (.const 0)) (pzAll (.const 1) φ))
/-- Symbolic `PAZFTerm` for `axRep`. -/
def pzRep (φ : PAZFTerm) : PAZFTerm :=
  pzImp
    (pzAll (.const 3)
      (pzEx (.const 1)
        (pzAll (.const 2) (pzImp (pzAll (.const 1) φ) (pzEq (.const 2) (.const 1))))))
    (pzEx (.const 1)
      (pzAll (.const 2)
        (pzAnd (pzImp (pzMem (.const 2) (.const 1)) (pzRepRhs φ))
          (pzImp (pzRepRhs φ) (pzMem (.const 2) (.const 1))))))
/-- Symbolic `PAZFTerm` for `axPow`. -/
def pzPow : PAZFTerm :=
  pzEx (.const 1)
    (pzAll (.const 2)
      (pzImp (pzAll (.const 3) (pzImp (pzMem (.const 3) (.const 2)) (pzMem (.const 3) (.const 0))))
        (pzMem (.const 2) (.const 1))))
/-- Symbolic `PAZFTerm` for `axUni`. -/
def pzUni : PAZFTerm :=
  pzEx (.const 1)
    (pzAll (.const 2)
      (pzImp (pzEx (.const 3) (pzAnd (pzMem (.const 2) (.const 3)) (pzMem (.const 3) (.const 0))))
        (pzMem (.const 2) (.const 1))))
/-- Symbolic `PAZFTerm` for `axInfSingleton`. -/
def pzInfSingleton : PAZFTerm :=
  pzAll (.const 1)
    (pzAnd (pzImp (pzMem (.const 1) (.const 2)) (pzEq (.const 1) (.const 0)))
      (pzImp (pzEq (.const 1) (.const 0)) (pzMem (.const 1) (.const 2))))
/-- Symbolic `PAZFTerm` for `axInf`. -/
def pzInf : PAZFTerm :=
  pzEx (.const 1)
    (pzAnd (pzMem (.const 0) (.const 1))
      (pzAll (.const 0)
        (pzImp (pzMem (.const 0) (.const 1))
          (pzEx (.const 2) (pzAnd (pzMem (.const 2) (.const 1)) pzInfSingleton)))))

/-- Validity of step `i = .var 3` (with formula code `w = .var 4`) in a $\beta$-coded `ZFProvable`
derivation `(c = .var 1, d = .var 2)`. -/
def paIsZFStep : PAFormula :=
  paDisjList
    [ (pzEq (.const 0) (.const 0)).eqFormula (.var 4) 10
    , .ex 5 (.ex 6 (.ex 8 (.ex 9
        (.and (paLt (.var 8) (.var 3))
          (.and (paLt (.var 9) (.var 3))
            (.and (paBetaEq (.var 1) (.var 2) (.var 8) (.var 5))
              (.and (paBetaEq (.var 1) (.var 2) (.var 9) (.var 6))
                ((pzImp (.var 5) (.var 4)).eqFormula (.var 6) 10))))))))
    , .ex 5 (.ex 6 (.ex 8
        (.and (paLt (.var 8) (.var 3))
          (.and (paBetaEq (.var 1) (.var 2) (.var 8) (.var 6))
            ((pzAll (.var 5) (.var 6)).eqFormula (.var 4) 10)))))
    , .ex 5 (.ex 6 (.ex 7 ((pzB1 (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 ((pzB2 (.var 5)).eqFormula (.var 4) 10)
    , .ex 5 (.ex 6 ((pzB3 (.var 5) (.var 6)).eqFormula (.var 4) 10))
    , .ex 5 (.ex 6 (.ex 7 ((pzB4 (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 (.ex 7
        (.and (paNe (.var 5) (.var 7))
          (.and (paNe (.var 7) (.var 6))
            ((pzB6a (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))))
    , .ex 5 (.ex 6 (.ex 7 ((pzB6b (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 ((pzB6c (.var 5) (.var 6)).eqFormula (.var 4) 10))
    , .ex 5 (.ex 6 ((pzB7 (.var 5) (.var 6)).eqFormula (.var 4) 10))
    , .ex 5 (.ex 6 (.ex 7 ((pzB8a (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 (.ex 7 ((pzB8b (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , .ex 5 (.ex 6 (.ex 7 ((pzB8c (.var 5) (.var 6) (.var 7)).eqFormula (.var 4) 10)))
    , pzExt.eqFormula (.var 4) 10
    , .ex 5 ((pzRep (.var 5)).eqFormula (.var 4) 10)
    , pzPow.eqFormula (.var 4) 10
    , pzUni.eqFormula (.var 4) 10
    , pzInf.eqFormula (.var 4) 10 ]

/-- Closed $\Sigma_1^0$ $\mathcal{L}_{\mathrm{PA}}$-sentence asserting `ZFInconsistent`
($\mathrm{ZF} \vdash v_0 \in v_0$). -/
def paZFInconsistent : PAFormula :=
  .ex 0 (.ex 1 (.ex 2
    (.and
      (.all 3 (.imp (paLe (.var 3) (.var 0))
        (.ex 4 (.and (paBetaEq (.var 1) (.var 2) (.var 3) (.var 4)) paIsZFStep))))
      (.ex 4
        (.and (paBetaEq (.var 1) (.var 2) (.var 0) (.var 4))
          ((pzMem (.const 0) (.const 0)).eqFormula (.var 4) 10))))))

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

namespace Semantics.PA
theorem not_paProvable_false : ¬ PAProvable .bot := by sorry
theorem paHalts_holds_iff_halts {states : ℕ} [NeZero states] (M : Machine states 2)
    (v : ℕ → ℕ) : (paHalts M).Holds v ↔ ConjectureMachines.Halts M := by sorry
theorem paZFInconsistent_holds_iff_zfInconsistent (v : ℕ → ℕ) :
    paZFInconsistent.Holds v ↔ ZFInconsistent := by sorry
theorem paProvable_sound_nat (φ : PAFormula) (h : PAProvable φ) (v : ℕ → ℕ) :
    φ.Holds v := by sorry
theorem paProvable_halts_zf380_iff_zf393 :
    PAProvable ((paHalts Machines.zf380).iff (paHalts Machines.zf393)) := by sorry
theorem paProvable_halts_zf393_iff_zfInconsistent :
    PAProvable ((paHalts Machines.zf393).iff paZFInconsistent) := by sorry
theorem paProvable_halts_zf380_iff_zfInconsistent :
    PAProvable ((paHalts Machines.zf380).iff paZFInconsistent) := by sorry
end Semantics.PA

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
