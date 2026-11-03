/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import BusyBeaver.Defs
meta import Lean.Elab.Term

/-!
# Bridge Between `ConjectureMachines` and `BusyBeaver` (`BusyBeaver.Bridge`)

Connects `ConjectureMachines.Machine states symbols` to `BusyBeaver.Machine (Fin symbols)
(Fin states)`:

- `load_rle_rows%` / `load_rle_machine%` — Elaboration-time parsers for standard
  `bbchallenge.org` RLE transition strings (such as
  `"1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"`), complementing `load_machine_rows%` for `.txt`
  tables.
- `ConjectureMachines.Machine.toBB` / `ConjectureMachines.Cfg.toBB` — Canonical embedding of finite
  Turing machines and configurations into `BusyBeaver`.
- `isHalt_toBB_iff_halts` & `isNotHalt_toBB_iff_not_halts` — Halting equivalence between
  `BusyBeaver.IsHalt` / `BusyBeaver.IsNotHalt` on `M.toBB` and `ConjectureMachines.Halts M`.
-/

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
    if (wChar == '-' && dChar == '-' && sChar == '-') ||
        (wChar == 'H' && dChar == 'H' && sChar == 'H') then
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

/-- Elaboration-time parser turning a standard `bbchallenge.org` RLE string (e.g.
`"1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"`) into transition rows for
`ConjectureMachines.Machine.ofRows`. -/
elab "load_rle_rows% " rle:str : term <= expectedType? => do
  let blocks := rle.getString.trimAscii.toString.splitOn "_"
  if blocks.isEmpty then
    throwError "Empty RLE string"
  let mut rowStxs : Array (TSyntax `term) := #[]
  for b in blocks do
    rowStxs := rowStxs.push (← parseRleBlock b)
  elabTerm (← `([$rowStxs,*])) expectedType?

/-- Elaboration-time parser turning a standard `bbchallenge.org` RLE string directly into a
`ConjectureMachines.Machine`. -/
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

/-- Canonical `NeZero 2` instance for `(states, 2)` Turing machines. -/
instance (priority := high) instNeZeroTwo : @NeZero ℕ Zero.ofOfNat0 2 := Nat.instNeZeroSucc

/-- Canonical `NeZero 3` instance for `(3, 3)` Turing machines. -/
instance (priority := high) instNeZeroThree : @NeZero ℕ Zero.ofOfNat0 3 := Nat.instNeZeroSucc

/-- Canonical `NeZero 6` instance for `(6, symbols)` Turing machines. -/
instance (priority := high) instNeZeroSix : @NeZero ℕ Zero.ofOfNat0 6 := Nat.instNeZeroSucc

end BusyBeaver

namespace ConjectureMachines

open Relation StateTransition

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- Embed `ConjectureMachines.ListBlank Γ` into Mathlib's `Turing.ListBlank Γ`. -/
def ListBlank.toTuring {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) : Turing.ListBlank Γ :=
  l.liftOn Turing.ListBlank.mk fun _ _ h => Quotient.sound' (Or.inl h)

@[simp]
theorem ListBlank.toTuring_inj {Γ : Type*} [Inhabited Γ] {l₁ l₂ : ListBlank Γ} :
    l₁.toTuring = l₂.toTuring ↔ l₁ = l₂ :=
  ⟨l₁.induction_on fun _ => l₂.induction_on fun _ h => Quot.sound (Quotient.exact' h),
   congrArg _⟩

@[simp]
theorem ListBlank.toTuring_head {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) :
    l.toTuring.head = l.head :=
  l.induction_on fun _ => rfl

@[simp]
theorem ListBlank.toTuring_tail {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) :
    l.toTuring.tail = l.tail.toTuring :=
  l.induction_on fun _ => rfl

@[simp]
theorem ListBlank.toTuring_cons {Γ : Type*} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) :
    l.toTuring.cons a = (l.cons a).toTuring :=
  l.induction_on fun _ => rfl

/-- Embed `ConjectureMachines.Tape Γ` into Mathlib's `Turing.Tape Γ`. -/
def Tape.toTuring {Γ : Type*} [Inhabited Γ] (T : Tape Γ) : Turing.Tape Γ :=
  ⟨T.head, T.left.toTuring, T.right.toTuring⟩

@[simp]
theorem Tape.toTuring_inj {Γ : Type*} [Inhabited Γ] {T₁ T₂ : Tape Γ} :
    T₁.toTuring = T₂.toTuring ↔ T₁ = T₂ := by
  cases T₁; cases T₂; simp [Tape.toTuring]

/-- Convert a `ConjectureMachines.Machine states symbols` into a
`BusyBeaver.Machine (Fin symbols) (Fin states)`. -/
def Machine.toBB (M : Machine states symbols) :
    BusyBeaver.Machine (Fin symbols) (Fin states) :=
  fun q s => (M.transition q s).map fun (a, d, q') => (some q', BusyBeaver.Stmt.write a d)

/-- Convert a `ConjectureMachines.Cfg states symbols` into a
`BusyBeaver.Cfg (Fin symbols) (Fin states)`. -/
def Cfg.toBB (c : Cfg states symbols) :
    BusyBeaver.Cfg (Fin symbols) (Fin states) :=
  ⟨some c.state, c.tape.toTuring⟩

omit [NeZero states] in
@[simp]
theorem Cfg.toBB_inj {c₁ c₂ : Cfg states symbols} :
    c₁.toBB = c₂.toBB ↔ c₁ = c₂ := by
  cases c₁; cases c₂; simp [Cfg.toBB]

@[simp]
theorem init_toBB :
    (BusyBeaver.init ([] : List (Fin symbols)) : BusyBeaver.Cfg (Fin symbols) (Fin states)) =
      (ConjectureMachines.init : Cfg states symbols).toBB :=
  rfl

@[simp]
theorem step_toBB (M : Machine states symbols) (c : Cfg states symbols) :
    BusyBeaver.step M.toBB c.toBB = (ConjectureMachines.step M c).map Cfg.toBB := by
  obtain ⟨q, T⟩ := c
  simp only [Cfg.toBB, BusyBeaver.step, Machine.toBB, ConjectureMachines.step, Option.map_map,
    Tape.toTuring]
  rcases M.transition q T.head with _ | ⟨a, d, q'⟩
  · rfl
  · cases d <;>
      simp [Cfg.toBB, Tape.move, Tape.write, Turing.Tape.move, Turing.Tape.write, Tape.toTuring]

theorem step_toBB_isNone_iff (M : Machine states symbols) (c : Cfg states symbols) :
    (BusyBeaver.step M.toBB c.toBB).isNone ↔ ConjectureMachines.step M c = none := by
  rw [step_toBB, Option.isNone_iff_eq_none, Option.map_eq_none_iff]

theorem step_toBB_isSome_iff (M : Machine states symbols) (c : Cfg states symbols) :
    (BusyBeaver.step M.toBB c.toBB).isSome ↔ (ConjectureMachines.step M c).isSome := by
  rw [step_toBB, Option.isSome_map]

private theorem iterate_bind_none {α : Type*} (f : α → Option α) (n : ℕ) :
    (fun x : Option α => x.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Option.bind_none, ih]

private theorem iterate_bind_toBB (M : Machine states symbols) (n : ℕ)
    (x : Option (Cfg states symbols)) :
    (fun y : Option (BusyBeaver.Cfg (Fin symbols) (Fin states)) =>
        y.bind (BusyBeaver.step M.toBB))^[n] (x.map Cfg.toBB) =
      ((fun y : Option (Cfg states symbols) =>
          y.bind (ConjectureMachines.step M))^[n] x).map Cfg.toBB := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hbind :
        (x.map Cfg.toBB).bind (BusyBeaver.step M.toBB) =
          (x.bind (ConjectureMachines.step M)).map Cfg.toBB := by
      cases x <;> simp [step_toBB]
    rw [hbind, ih]

theorem multiStep_toBB (M : Machine states symbols) (c : Cfg states symbols) (n : ℕ) :
    BusyBeaver.multiStep M.toBB c.toBB n =
      ((fun y : Option (Cfg states symbols) =>
          y.bind (ConjectureMachines.step M))^[n] (some c)).map Cfg.toBB :=
  iterate_bind_toBB M n (some c)

omit [NeZero states] in
private theorem reaches_iff_exists_iterate (M : Machine states symbols)
    (c c' : Cfg states symbols) :
    StateTransition.Reaches (ConjectureMachines.step M) c c' ↔
      ∃ n : ℕ, (fun y : Option (Cfg states symbols) =>
        y.bind (ConjectureMachines.step M))^[n] (some c) = some c' := by
  constructor
  · intro h
    refine Relation.ReflTransGen.head_induction_on h ?_ ?_
    · exact ⟨0, rfl⟩
    · intro a b hab _ ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      simp only [Option.mem_def] at hab
      simpa [Option.bind, hab] using hn
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero =>
      injection hn with h
      subst h
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      change (fun y : Option (Cfg states symbols) =>
        y.bind (ConjectureMachines.step M))^[n] (ConjectureMachines.step M c) = some c' at hn
      rcases hstep : ConjectureMachines.step M c with _ | c₁
      · rw [hstep, iterate_bind_none] at hn
        cases hn
      · rw [hstep] at hn
        exact Relation.ReflTransGen.head hstep (ih c₁ hn)

/-- A `ConjectureMachines.Machine` halts from `init` if and only if its `BusyBeaver` image
satisfies `BusyBeaver.IsHalt`. -/
theorem isHalt_toBB_iff_halts (M : Machine states symbols) :
    BusyBeaver.IsHalt M.toBB ↔ ConjectureMachines.Halts M := by
  unfold BusyBeaver.IsHalt ConjectureMachines.Halts
  rw [Part.dom_iff_mem]
  simp only [StateTransition.mem_eval, init_toBB]
  constructor
  · rintro ⟨cfg, ⟨n, hms⟩, hnone⟩
    rw [multiStep_toBB, Option.map_eq_some_iff] at hms
    obtain ⟨c', hc', rfl⟩ := hms
    refine ⟨c', (reaches_iff_exists_iterate M init c').mpr ⟨n, hc'⟩, ?_⟩
    exact (step_toBB_isNone_iff M c').mp hnone
  · rintro ⟨c', hreach, hnone⟩
    obtain ⟨n, hn⟩ := (reaches_iff_exists_iterate M init c').mp hreach
    refine ⟨c'.toBB, ⟨n, ?_⟩, (step_toBB_isNone_iff M c').mpr hnone⟩
    rw [multiStep_toBB, hn, Option.map_some]

/-- A `ConjectureMachines.Machine` does not halt from `init` if and only if its `BusyBeaver` image
satisfies `BusyBeaver.IsNotHalt`. -/
theorem isNotHalt_toBB_iff_not_halts (M : Machine states symbols) :
    BusyBeaver.IsNotHalt M.toBB ↔ ¬ ConjectureMachines.Halts M := by
  rw [← isHalt_toBB_iff_halts]
  unfold BusyBeaver.IsNotHalt BusyBeaver.IsHalt
  constructor
  · intro h ⟨cfg, hreach, hnone⟩
    have hsome := h cfg hreach
    rw [Option.isNone_iff_eq_none] at hnone
    simp [hnone] at hsome
  · intro h cfg hreach
    by_contra hnsome
    apply h
    refine ⟨cfg, hreach, ?_⟩
    simpa using hnsome

end ConjectureMachines
