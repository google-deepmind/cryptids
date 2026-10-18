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
meta import Lean.Elab.Term

/-!
# Turing Machine Definitions (`Cryptids.Machines`)

Machines with `states` states and `symbols` symbols, over Mathlib's tape, together with the
elaboration-time table loader `load_machine_rows%` and all baseline and candidate machines in
`ConjectureMachines.Machines`.
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
open Turing StateTransition

/-- A transition table: for a state and the symbol under the head, either the
symbol to write, the direction to move and the state to enter, or `none` to
halt. -/
structure Machine (states symbols : ℕ) where
  transition : Fin states → Fin symbols → Option (Fin symbols × Dir × Fin states)

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- A configuration: the current state and the tape, whose `head` is the
symbol under the head. -/
structure Cfg (states symbols : ℕ) [NeZero symbols] where
  state : Fin states
  tape : Tape (Fin symbols)

/-- One step, or `none` when the transition is missing. -/
def step (M : Machine states symbols) : Cfg states symbols → Option (Cfg states symbols)
  | ⟨q, T⟩ => (M.transition q T.head).map fun ⟨a, d, q'⟩ => ⟨q', (T.write a).move d⟩

/-- The start state on the all-blank tape. -/
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
end Machines

/-- The configuration `n` steps in from `init`, or `none` once `M` has halted. -/
def run (M : Machine states symbols) (n : ℕ) : Option (Cfg states symbols) :=
  (fun c => c.bind (step M))^[n] (some init)

/-- `M`, started in state `0` on the all-blank tape, has not halted within `n` steps. -/
def Runs (M : Machine states symbols) (n : ℕ) : Prop := (run M n).isSome

instance (M : Machine states symbols) (n : ℕ) : Decidable (Runs M n) :=
  inferInstanceAs (Decidable ((run M n).isSome = true))

end ConjectureMachines
