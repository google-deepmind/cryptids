/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Algebra.Order.SuccPred
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
/-- Rows of `erdos15`. -/ def erdos15Rows : List (List (Option (Fin 2 × Dir × Fin 15))) :=
  load_machine_rows% "baselines/tables/erdos_15.txt"
/-- 15-state Erdős machine. -/ def erdos15 : Machine 15 2 := Machine.ofRows erdos15Rows
/-- Rows of `erdos14`. -/ def erdos14Rows : List (List (Option (Fin 2 × Dir × Fin 14))) :=
  load_machine_rows% "artifacts/erdos_14/machine.txt"
/-- 14-state Erdős candidate. -/ def erdos14 : Machine 14 2 := Machine.ofRows erdos14Rows
end Machines

attribute [-simp] Nat.add_eq_right Order.add_one_le_iff Order.lt_add_one_iff

@[simp high] theorem nat_add_one_le_iff {x y : ℕ} : x + no_index 1 ≤ y ↔ x < y := by
  constructor <;> intro h <;> omega

@[simp high] theorem nat_lt_add_one_iff {x y : ℕ} : x < y + no_index 1 ↔ x ≤ y := by
  constructor <;> intro h <;> omega

@[simp high] theorem nat_add_eq_left {n m : ℕ} : n + m = m ↔ n = 0 := by
  constructor <;> intro h <;> omega

instance (priority := 10000) instBEqFinConstructive (n : ℕ) : BEq (Fin n) := instBEqOfDecidableEq
instance (priority := 10000) instLawfulBEqFinConstructive (n : ℕ) : LawfulBEq (Fin n) where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
instance (priority := 10000) instReflBEqFinConstructive (n : ℕ) : ReflBEq (Fin n) :=
  (instLawfulBEqFinConstructive n).toReflBEq
instance (priority := 10000) instEquivBEqFinConstructive (n : ℕ) : EquivBEq (Fin n) where
  symm h := decide_eq_true (of_decide_eq_true h).symm
  trans h1 h2 := decide_eq_true ((of_decide_eq_true h1).trans (of_decide_eq_true h2))
instance (priority := 10000) instPreorderFinConstructive (n : ℕ) : Preorder (Fin n) :=
  (instLinearOrderFinConstructive n).toPreorder
instance (priority := 10000) instPartialOrderFinConstructive (n : ℕ) : PartialOrder (Fin n) :=
  (instLinearOrderFinConstructive n).toPartialOrder

instance (priority := 10000) instLinearOrderNatConstructive : LinearOrder ℕ where
  le := Nat.le
  lt := Nat.lt
  le_refl := Nat.le_refl
  le_trans := @Nat.le_trans
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  toDecidableLE := Nat.decLe
  toDecidableEq := instDecidableEqNat
  toDecidableLT := Nat.decLt
  min a b := if a ≤ b then a else b
  max a b := if a ≤ b then b else a
  min_def _ _ := rfl
  max_def _ _ := rfl
  compare a b := compareOfLessAndEq a b
  compare_eq_compareOfLessAndEq _ _ := rfl

instance (priority := 10000) instPreorderNatConstructive : Preorder ℕ :=
  instLinearOrderNatConstructive.toPreorder
instance (priority := 10000) instPartialOrderNatConstructive : PartialOrder ℕ :=
  instLinearOrderNatConstructive.toPartialOrder

instance (priority := 10000) instAddLeftReflectLENatConstructive : AddLeftReflectLE ℕ :=
  ⟨@Nat.le_of_add_le_add_left⟩

instance (priority := 10000) instAddRightReflectLENatConstructive : AddRightReflectLE ℕ :=
  ⟨fun {_ _ _} h => Nat.le_of_add_le_add_right h⟩

instance (priority := 10000) instSuccOrderNatConstructive : SuccOrder ℕ where
  succ n := n + 1
  le_succ := Nat.le_succ
  max_of_succ_le {a} h := absurd h (Nat.not_succ_le_self a)
  succ_le_of_lt := id

instance (priority := 10000) instSuccAddOrderNatConstructive : SuccAddOrder ℕ :=
  ⟨fun _ => rfl⟩

@[simp high] theorem nat_lt_one_iff (n : ℕ) : n < 1 ↔ n = 0 := by constructor <;> intro h <;> omega
@[simp high] theorem nat_lt_two_iff (n : ℕ) : n < 2 ↔ n = 0 ∨ n = 1 :=
  ⟨fun h => match n with | 0 => Or.inl rfl | 1 => Or.inr rfl | _ + 2 => by omega,
   fun h => h.elim (fun _ => by omega) (fun _ => by omega)⟩
@[simp high] theorem nat_lt_succ_self (n : ℕ) : n < n + 1 := Nat.lt_succ_self n
@[simp high] theorem nat_add_lt_add_left (a b c : ℕ) : a + b < a + c ↔ b < c := by
  constructor <;> intro h <;> omega
@[simp high] theorem nat_add_lt_add_right (a b c : ℕ) : a + c < b + c ↔ a < b := by
  constructor <;> intro h <;> omega
@[simp high] theorem nat_add_le_add_left (a b c : ℕ) : a + b ≤ a + c ↔ b ≤ c := by
  constructor <;> intro h <;> omega
@[simp high] theorem nat_add_le_add_right (a b c : ℕ) : a + c ≤ b + c ↔ a ≤ b := by
  constructor <;> intro h <;> omega
@[simp high] theorem nat_add_pos_iff (a b : ℕ) : 0 < a + b ↔ 0 < a ∨ 0 < b :=
  ⟨fun h => match a with | 0 => Or.inr (by omega) | _ + 1 => Or.inl (by omega),
   fun h => h.elim (fun _ => by omega) (fun _ => by omega)⟩
@[simp high] theorem nat_add_eq_right {n m : ℕ} : n + m = n ↔ m = 0 := by
  constructor <;> intro h <;> omega
@[simp high] theorem nat_zero_le (n : ℕ) : 0 ≤ n := Nat.zero_le n
@[simp high] theorem nat_ofNat_pos {n : ℕ} [h : n.AtLeastTwo] :
    0 < (no_index (OfNat.ofNat n : ℕ)) := Nat.zero_lt_of_lt h.1
@[simp high] theorem nat_one_lt_ofNat {n : ℕ} [h : n.AtLeastTwo] :
    1 < (no_index (OfNat.ofNat n : ℕ)) := h.1
@[simp high] theorem list_take_eq_self_iff {α : Type*} (x : List α) {n : ℕ} :
    x.take n = x ↔ x.length ≤ n := by
  induction x generalizing n with
  | nil => simp
  | cons _ _ ih => cases n <;> simp [ih]

/-- The configuration `n` steps in from `init`, or `none` once `M` has halted. -/
def run (M : Machine states symbols) (n : ℕ) : Option (Cfg states symbols) :=
  (fun c => c.bind (step M))^[n] (some init)

/-- `M`, started in state `0` on the all-blank tape, has not halted within `n` steps. -/
def Runs (M : Machine states symbols) (n : ℕ) : Prop := (run M n).isSome

instance (M : Machine states symbols) (n : ℕ) : Decidable (Runs M n) :=
  inferInstanceAs (Decidable ((run M n).isSome = true))

@[elab_as_elim]
protected theorem ListBlank.induction_on {Γ : Type*} [Inhabited Γ] {p : ListBlank Γ → Prop}
    (q : ListBlank Γ) (h : ∀ a, p (ListBlank.mk a)) : p q :=
  Quot.ind h q

@[simp]
theorem ListBlank.head_mk {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI :=
  rfl

@[simp]
theorem ListBlank.tail_mk {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail :=
  rfl

@[simp]
theorem ListBlank.cons_mk {Γ : Type*} [Inhabited Γ] (a : Γ) (l : List Γ) :
    ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) :=
  rfl

@[simp]
theorem ListBlank.head_cons {Γ : Type*} [Inhabited Γ] (a : Γ) :
    ∀ l : ListBlank Γ, (l.cons a).head = a :=
  Quot.ind fun _ => rfl

@[simp]
theorem ListBlank.tail_cons {Γ : Type*} [Inhabited Γ] (a : Γ) :
    ∀ l : ListBlank Γ, (l.cons a).tail = l :=
  Quot.ind fun _ => rfl

@[simp]
theorem ListBlank.cons_head_tail {Γ : Type*} [Inhabited Γ] :
    ∀ l : ListBlank Γ, l.tail.cons l.head = l :=
  Quot.ind fun l => by
    change ListBlank.cons (ListBlank.mk l).head (ListBlank.mk l).tail = ListBlank.mk l
    rw [ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
    refine Quot.sound (Or.inr ?_)
    cases l
    · exact ⟨1, rfl⟩
    · exact ⟨0, by simp⟩

/-- The `n`-th symbol of a `ListBlank`. -/
def ListBlank.nth {Γ : Type*} [Inhabited Γ] : ListBlank Γ → ℕ → Γ
  | l, 0 => l.head
  | l, n + 1 => l.tail.nth n

@[simp]
theorem ListBlank.nth_zero {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head :=
  rfl

@[simp]
theorem ListBlank.nth_succ {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) :
    l.nth (n + 1) = l.tail.nth n :=
  rfl

/-- Prepend a finite `List` of symbols onto a `ListBlank`. -/
@[simp]
def ListBlank.append {Γ : Type*} [Inhabited Γ] : List Γ → ListBlank Γ → ListBlank Γ
  | [], L => L
  | a :: l, L => ListBlank.cons a (ListBlank.append l L)

@[simp]
theorem ListBlank.append_mk {Γ : Type*} [Inhabited Γ] (l₁ l₂ : List Γ) :
    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) := by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]

theorem ListBlank.append_assoc {Γ : Type*} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
    ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) := by
  refine l₃.induction_on fun l => ?_
  simp only [ListBlank.append_mk, List.append_assoc]

@[simp]
theorem Tape.write_self {Γ : Type*} [Inhabited Γ] : ∀ T : Tape Γ, T.write T.1 = T
  | ⟨_, _, _⟩ => rfl

@[simp]
theorem Tape.write_mk {Γ : Type*} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ) :
    (Tape.mk a L R).write b = Tape.mk b L R :=
  rfl

@[simp]
theorem Tape.mk'_left {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).left = L :=
  rfl

@[simp]
theorem Tape.mk'_head {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).head = R.head :=
  rfl

@[simp]
theorem Tape.mk'_right {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).right = R.tail :=
  rfl

@[simp]
theorem Tape.move_left_mk' {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.left = Tape.mk' L.tail (R.cons L.head) := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, ListBlank.cons_head_tail,
    ListBlank.tail_cons]

@[simp]
theorem Tape.move_right_mk' {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.right = Tape.mk' (L.cons R.head) R.tail :=
  rfl

@[simp]
theorem Tape.write_mk' {Γ : Type*} [Inhabited Γ] (b : Γ) (L R : ListBlank Γ) :
    (Tape.mk' L R).write b = Tape.mk' L (R.tail.cons b) := by
  simp only [Tape.write, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]

/-! ### Constructive (`Classical.choice`-free) `StateTransition` Lemmas -/

private theorem pfun_mem_fix_iff {α β : Type*} {f : α →. β ⊕ α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixF_eq] at h₂
    obtain ⟨h₂, h₃⟩ := Part.mem_assert_iff.1 h₂
    split at h₃
    next e => cases Part.mem_some_iff.1 h₃; exact Or.inl ⟨h₂, e⟩
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
   fun h => by
    rcases h with (⟨h₁, h₂⟩ | ⟨a', ⟨h₁, h₂⟩, h₃⟩)
    · refine Part.mem_assert ⟨a, fun y hy => ?_⟩ ?_
      · cases (Part.mem_unique ⟨h₁, h₂⟩ hy)
      · rw [WellFounded.fixF_eq]
        refine Part.mem_assert h₁ ?_
        split
        next e => injection h₂.symm.trans e with h'; exact Part.mem_some_iff.2 h'
        next e => cases h₂.symm.trans e
    · obtain ⟨hacc, h₄⟩ := Part.mem_assert_iff.1 h₃
      refine Part.mem_assert ⟨a, fun y hy => ?_⟩ ?_
      · injection Part.mem_unique ⟨h₁, h₂⟩ hy with e
        exact e ▸ hacc
      · rw [WellFounded.fixF_eq]
        refine Part.mem_assert h₁ ?_
        split
        next e => cases h₂.symm.trans e
        next e => injection h₂.symm.trans e with h'; subst h'; exact h₄⟩

private theorem pfun_fix_fwd {α β : Type*} {f : α →. β ⊕ α} {b : β} {a a' : α}
    (hb : b ∈ f.fix a) (ha' : Sum.inr a' ∈ f a) : b ∈ f.fix a' := by
  rcases pfun_mem_fix_iff.1 hb with h' | ⟨_, h', e'⟩ <;> cases Part.mem_unique ha' h'
  exact e'

@[elab_as_elim]
theorem evalInduction' {σ : Type*} {f : σ → Option σ} {b : σ} {C : σ → Prop} {a : σ}
    (h : b ∈ eval f a) (H : ∀ a, b ∈ eval f a → (∀ a', f a = some a' → C a') → C a) : C a := by
  let g : σ →. σ ⊕ σ := fun s => Part.some ((f s).elim (Sum.inl s) Sum.inr)
  have hmem : b ∈ g.fix a := h
  obtain ⟨hacc, h₂⟩ := Part.mem_assert_iff.1 hmem
  clear h hmem
  induction hacc with
  | intro x hx IH =>
    have hxmem : b ∈ g.fix x := Part.mem_assert ⟨x, hx⟩ h₂
    refine H x hxmem fun x' ex' => ?_
    have hinr : Sum.inr x' ∈ g x := Part.mem_some_iff.2 (by rw [ex']; rfl)
    exact IH x' hinr (Part.mem_assert_iff.1 (pfun_fix_fwd hxmem hinr)).snd

theorem mem_eval' {σ : Type*} {f : σ → Option σ} {a b : σ} :
    b ∈ eval f a ↔ Reaches f a b ∧ f b = none := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · refine evalInduction' h fun a h IH => ?_
    rcases e : f a with _ | a'
    · rw [Part.mem_unique h
          (pfun_mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e]; rfl)]
      exact ⟨Relation.ReflTransGen.refl, e⟩
    · rcases pfun_mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
        cases Part.mem_some_iff.1 h
      obtain ⟨h₁, h₂⟩ := IH a' e
      exact ⟨Relation.ReflTransGen.head e h₁, h₂⟩
  · refine Relation.ReflTransGen.head_induction_on h₁ ?_ fun h _ IH => ?_
    · exact pfun_mem_fix_iff.2 (Or.inl (Part.mem_some_iff.2 (by rw [h₂]; rfl)))
    · exact pfun_mem_fix_iff.2 (Or.inr ⟨_, Part.mem_some_iff.2 (by rw [h]; rfl), IH⟩)

private theorem rtg_cases_head {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ Relation.ReflTransGen r c b := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail x y _ hxy ih =>
    rcases ih with rfl | ⟨c, hac, hcx⟩
    · exact Or.inr ⟨y, hxy, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨c, hac, Relation.ReflTransGen.tail hcx hxy⟩

private theorem reaches_total_det {σ : Type*} {f : σ → Option σ} {a b c : σ}
    (hab : Reaches f a b) (hac : Reaches f a c) : Reaches f b c ∨ Reaches f c b := by
  induction hab using Relation.ReflTransGen.head_induction_on generalizing c with
  | refl => exact Or.inl hac
  | @head x x₁ hx₁ hxb ih =>
    rcases rtg_cases_head hac with rfl | ⟨c₁, hc₁, hc₁c⟩
    · exact Or.inr (Relation.ReflTransGen.head hx₁ hxb)
    · cases Option.mem_unique hx₁ hc₁
      exact ih hc₁c

private theorem reaches_of_none {σ : Type*} {f : σ → Option σ} {b c : σ}
    (hb : f b = none) (hbc : Reaches f b c) : b = c := by
  rcases rtg_cases_head hbc with rfl | ⟨d, hbd, _⟩
  · rfl
  · cases hb.symm.trans hbd

theorem reaches_eval' {σ : Type*} {f : σ → Option σ} {a b : σ} (ab : Reaches f a b) :
    eval f a = eval f b := by
  refine Part.ext fun c => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨ac, c0⟩ := mem_eval'.1 h
    refine mem_eval'.2 ⟨?_, c0⟩
    rcases reaches_total_det ab ac with bc | cb
    · exact bc
    · exact reaches_of_none c0 cb ▸ Relation.ReflTransGen.refl
  · obtain ⟨bc, c0⟩ := mem_eval'.1 h
    exact mem_eval'.2 ⟨ab.trans bc, c0⟩

private theorem tr_reaches' {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ : σ₁} {a₂ : σ₂}
    (aa : tr a₁ a₂) {b₁ : σ₁} (ab : Reaches f₁ a₁ b₁) :
    ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂ := by
  induction ab with
  | refl => exact ⟨a₂, aa, Relation.ReflTransGen.refl⟩
  | @tail c₁ d₁ _ cd IH =>
    obtain ⟨c₂, cc, ac₂⟩ := IH
    have := H cc
    rw [show f₁ c₁ = _ from cd] at this
    obtain ⟨d₂, dd, cd₂⟩ := this
    exact ⟨d₂, dd, ac₂.trans cd₂.to_reflTransGen⟩

private theorem tr_reaches_rev' {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ : σ₁} {a₂ b₂ : σ₂}
    (aa : tr a₁ a₂) (ab : Reaches f₂ a₂ b₂) :
    ∃ c₁ c₂, Reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁ := by
  induction ab with
  | refl => exact ⟨a₁, a₂, Relation.ReflTransGen.refl, aa, Relation.ReflTransGen.refl⟩
  | @tail c₂ d₂ _ cd IH =>
    obtain ⟨e₁, e₂, ce, ee, ae⟩ := IH
    rcases rtg_cases_head ce with rfl | ⟨d', cd', de⟩
    · have := H ee
      rcases eg : f₁ e₁ with _ | g₁
      · rw [eg] at this
        cases cd.symm.trans this
      · rw [eg] at this
        obtain ⟨g₂, gg, cg⟩ := this
        obtain ⟨d', cd', dg⟩ := Relation.TransGen.head'_iff.1 cg
        cases Option.mem_unique cd cd'
        exact ⟨g₁, g₂, dg, gg, ae.tail eg⟩
    · cases Option.mem_unique cd cd'
      exact ⟨e₁, e₂, de, ee, ae⟩

theorem tr_eval' {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ : σ₁} {a₂ : σ₂}
    (aa : tr a₁ a₂) (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ := by
  obtain ⟨ab, b0⟩ := mem_eval'.1 ab
  obtain ⟨b₂, bb, ab⟩ := tr_reaches' H aa ab
  refine ⟨b₂, bb, mem_eval'.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this

theorem tr_eval_rev' {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ : σ₁} {b₂ a₂ : σ₂}
    (aa : tr a₁ a₂) (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ := by
  obtain ⟨ab, b0⟩ := mem_eval'.1 ab
  obtain ⟨c₁, c₂, bc, cc, ac⟩ := tr_reaches_rev' H aa ab
  cases reaches_of_none b0 bc
  refine ⟨c₁, cc, mem_eval'.2 ⟨ac, ?_⟩⟩
  have := H cc
  rcases hfc : f₁ c₁ with _ | d₁
  · rfl
  rw [hfc] at this
  obtain ⟨_, _, bd⟩ := this
  obtain ⟨_, h, _⟩ := Relation.TransGen.head'_iff.1 bd
  cases b0.symm.trans h

theorem tr_eval_dom' {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ : σ₁} {a₂ : σ₂}
    (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom :=
  ⟨fun h => let ⟨_, _, h, _⟩ := tr_eval_rev' H aa ⟨h, rfl⟩; h,
   fun h => let ⟨_, _, h, _⟩ := tr_eval' H aa ⟨h, rfl⟩; h⟩

end ConjectureMachines
