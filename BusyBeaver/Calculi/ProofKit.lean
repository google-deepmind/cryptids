/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs
public import BusyBeaver.Basic
public import BusyBeaver.Calculi.Compat

/-!
# Shared Proof Prelude & Tactic Kit (`BusyBeaver.ProofKit`)

Untrusted direct-import-only module (NOT re-exported by `BusyBeaver.Import`) consolidating the
per-file proof prelude copied across `suspects/official/` proofs:

1. **Step / `multiStep` / Default-Tape `@[simp]` Lemmas**:
   - `zMz`, `zMo`, `zMs`, `z00`, `zZcd`, `zDh`, `zDt`, `zPpp` (complementing `Compat.z01..z06`,
     `Compat.zMa`, `Compat.zMt`, `Compat.zPs`, `Compat.zPt`, `Compat.zSt`).
2. **List-Power & `ListBlank` Algebra Aliases**:
   - `zPz`, `zPsl`, `zCal`, `zAnl`, `zLan`, `zLac`, `zLpa`, `zLpc`, `zLaa`, `zLp1`, `zPar`,
     `zPsr`, `zPl`, `zPa1`, `zPal`, `zSp2`, `zPsp`, `zSpp`, `zSsp`.
   - `listblank_append_pow_add`, `listblank_right_pow_add` (and generic `_gen` forms).
3. **Canonical Deterministic Step Tactics (`finish`, `gstep`, `execute5`, `execute`, `execute n`)**:
   - `finish` closes reflexive `⊢*` goals (`exists 0 <;> fail`).
   - `gstep` advances a single deterministic concrete step (`⊢⁺` / `⊢*`) by simplifying tape heads,
     `Tape.move`, `Tape.write`, and blank tails.
   - `execute` repeats `(any_goals (first | finish | gstep))`; `execute n` runs `n` `gstep`s then
     `finish`; `execute5` runs 5 rounds.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-! ## Step & Default-Tape Lemmas (`z*` Shorthands) -/

theorem zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 0 = some config := rfl

theorem zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 1 = step M config := rfl

theorem zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) :=
  multiStep_add M config n 1

theorem z00 {n : ℕ} [NeZero n] : (0 : Fin n) >> (default : ListBlank (Fin n)) = default :=
  ListBlank.cons_zero_default

theorem zZcd {n : ℕ} [NeZero n] : (0 : Fin n) >> (default : ListBlank (Fin n)) = default :=
  ListBlank.cons_zero_default

theorem zDh {n : ℕ} [NeZero n] : (default : ListBlank (Fin n)).head = 0 :=
  ListBlank.head_default_fin

theorem zDt {n : ℕ} [NeZero n] : (default : ListBlank (Fin n)).tail = default :=
  ListBlank.tail_default

theorem zPpp {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_trans h₁ h₂

/-! ## Extended `z*` List-Power, `ListBlank`, and Reachability Aliases -/

theorem zPz {α : Type*} (l : List α) : l ^ (0 : ℕ) = [] := rfl

theorem zPsl {α : Type*} (l : List α) (n : ℕ) : l ^ (n + 1) = l ++ (l ^ n) := rfl

theorem zCal {α : Type*} (x : α) (xs ys : List α) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

theorem zAnl {α : Type*} (l : List α) : l ++ [] = l := List.append_nil l

theorem zLan {α : Type*} [Inhabited α] (b : ListBlank α) : ([] : List α) +> b = b := rfl

theorem zLac {α : Type*} [Inhabited α] (x : α) (xs : List α) (b : ListBlank α) :
    (x :: xs) +> b = x >> (xs +> b) := rfl

theorem zLpa {α : Type*} (l : List α) (n m : ℕ) :
    l ^ (n + m) = l ^ n ++ l ^ m :=
  list_pow_add l n m

theorem zLpc {α : Type*} (l : List α) (n m : ℕ) :
    l ^ n ++ l ^ m = l ^ m ++ l ^ n :=
  list_pow_add_comm l n m

theorem zLaa {α : Type*} [Inhabited α] (s : ListBlank α) (l₁ l₂ : List α) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) :=
  listblank_append_append s l₁ l₂

theorem zLp1 {α : Type*} (u : List α) (k : ℕ) : u ^ k ++ u = u ^ (k + 1) :=
  list_pow_append_one u k

theorem zPar {α : Type*} [Inhabited α] (u : List α) (m n : ℕ) (r : ListBlank α) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_right_assoc]

theorem zPsr {α : Type*} [Inhabited α] (u : List α) (n : ℕ) (r : ListBlank α) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_right_assoc]

theorem zPl {α : Type*} [Inhabited α] (s : ListBlank α) (u : List α) (m n : ℕ) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, list_pow_add_comm, ← list_pow_add]

theorem zPa1 {α : Type*} [Inhabited α] (u : List α) (k : ℕ) (r : ListBlank α) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [← listblank_append_right_assoc, list_pow_append_one]

theorem zPal {α : Type*} [Inhabited α] (l : ListBlank α) (u : List α) (k : ℕ) :
    (l <+ u) <+ (u ^ k) = l <+ (u ^ (k + 1)) := by
  rw [listblank_append_append, list_pow_append_one]

theorem zSp2 (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ :=
  z01 tm c₁ c₂ h

theorem zPsp {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  z02 h₁ h₂

theorem zSpp {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus h₁ h₂

theorem zSsp {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  z03 h₁ h₂

/-! ## `ListBlank` Power Concatenation Helpers -/

theorem listblank_append_pow_add_gen {α : Type*} [Inhabited α]
    (s : ListBlank α) (u : List α) (n m : ℕ) :
    (s <+ (u ^ n)) <+ (u ^ m) = s <+ (u ^ (n + m)) :=
  (zPl s u n m).symm

theorem listblank_right_pow_add_gen {α : Type*} [Inhabited α]
    (s : ListBlank α) (u : List α) (n m : ℕ) :
    (u ^ n) +> ((u ^ m) +> s) = (u ^ (n + m)) +> s :=
  (zPar u n m s).symm

theorem listblank_append_word_pow_add {α : Type*} [Inhabited α]
    (s : ListBlank α) (u : List α) (n m : ℕ) :
    (s <+ (u ^ n)) <+ (u ^ m) = s <+ (u ^ (n + m)) :=
  (zPl s u n m).symm

theorem listblank_right_word_pow_add {α : Type*} [Inhabited α]
    (s : ListBlank α) (u : List α) (n m : ℕ) :
    (u ^ n) +> ((u ^ m) +> s) = (u ^ (n + m)) +> s :=
  (zPar u n m s).symm

theorem listblank_append_pow_add {nSym : ℕ} [NeZero nSym]
    (s : ListBlank (Fin nSym)) (n m : ℕ) :
    (s <+ (([1] : List (Fin nSym)) ^ n)) <+ (([1] : List (Fin nSym)) ^ m) =
    s <+ (([1] : List (Fin nSym)) ^ (n + m)) :=
  (zPl s [1] n m).symm

theorem listblank_right_pow_add {nSym : ℕ} [NeZero nSym]
    (s : ListBlank (Fin nSym)) (n m : ℕ) :
    (([1] : List (Fin nSym)) ^ n) +> ((([1] : List (Fin nSym)) ^ m) +> s) =
    (([1] : List (Fin nSym)) ^ (n + m)) +> s :=
  (zPar [1] n m s).symm

/-! ## Canonical Deterministic Step Macros -/

/-- Closes reflexive `⊢*` goals (`0` steps). -/
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)

/-- Advances a single deterministic TM transition on `⊢*` or `⊢⁺` goals. -/
macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [listblank_append_cons, listblank_append_nil,
      Turing.ListBlank.head_cons, zDh, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      Tape.write, listblank_append_cons, listblank_append_nil,
      z00, zDh, zDt, zero_cons_default, default_head, default_tail])

/-- Executes up to 5 deterministic TM steps. -/
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | gstep)) <;>
    (any_goals (first | finish | gstep)) <;>
    (any_goals (first | finish | gstep)) <;>
    (any_goals (first | finish | gstep)) <;>
    (any_goals (first | finish | gstep)))

/-- Repeatedly applies `finish | gstep` until no deterministic steps remain. -/
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | gstep)))

/-- Applies `n` deterministic `gstep`s followed by `finish`. -/
macro "execute " n:num : tactic =>
  `(tactic| (iterate $n gstep
             finish))

/-- Alias for `execute`: repeatedly applies `finish | gstep` until no deterministic steps remain. -/
macro "gsteps" : tactic =>
  `(tactic| execute)

/-- Alias for `execute n`: applies `n` deterministic `gstep`s followed by `finish`. -/
macro "gsteps " n:num : tactic =>
  `(tactic| execute $n)

/-! ## Scoped Simplification Lemmas (`BusyBeaver.ProofKit`) -/

/-! Scoped `simp` registration for the `z*` step, tape, and list-power shorthands.
Activate in proof files with `open scoped BusyBeaver.ProofKit` (or `open ProofKit`). -/
namespace ProofKit

attribute [scoped simp]
  zMz zMo zMs z00 zZcd zDh zDt
  zPz zPsl zCal zAnl zLan zLac zLpa

end ProofKit

end BusyBeaver
