/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Machine `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE` — `is_cryptid` (`IsCryptid target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 4, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000
namespace Solution
@[simp] lemma zPz (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zPsl (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma zCal (x : α) (l₁ l₂ : List α) : (x :: l₁) ++ l₂ = x :: (l₁ ++ l₂) := rfl
@[simp] lemma zLan (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma zLac (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma zDt : (default : ListBlank (Fin 2)).tail = default := rfl
lemma zStp {c_1 c_2 : Cfg (Fin 2) (Fin 6)} (h : step target_tm c_1 = some c_2) : c_1 [target_tm]⊢⁺ c_2 := ⟨1, by decide, h⟩
local notation "zzTP" => TapePattern (Fin 2) (Fin 6)
local notation "zzTE" => TapeExpr (Fin 2)
local notation "zzG" => Cfg (Fin 2) (Fin 6)
local notation "zzV" => Nat -> Nat
local notation "zzE" => evalTapePattern
local notation "zzD" => TapeExpr.default
local notation "zz0" x:arg => TapeExpr.sym 0 x
local notation "zz1" x:arg => TapeExpr.sym 1 x
local notation "zzR" l:arg v:arg x:arg => TapeExpr.rep l v x
local notation "zzM" l:arg q:arg r:arg => ({ left := l, head := some q, right := r } : TapePattern (Fin 2) (Fin 6))
local notation "zzF1" a:arg => (fun k : Nat => match k with | 0 => a | _ => 0)
local notation "zzF2" a:arg b:arg => (fun k : Nat => match k with | 0 => a | 1 => b | _ => 0)
local notation "zzF3" a:arg b:arg c:arg => (fun k : Nat => match k with | 0 => a | 1 => b | 2 => c | _ => 0)
local notation "zzF4" a:arg b:arg c:arg d:arg => (fun k : Nat => match k with | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)
local macro "zzS1" : tactic => `(tactic| simp only [step, target_tm, evalTapePattern, evalTapeExpr, zPz, zPsl, zCal, List.singleton_append, List.nil_append, Turing.Tape.write, Turing.Tape.move, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt, Option.map])
local macro "zzS2" : tactic => `(tactic| simp only [zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt])
local macro "zzD1" a:ident b:ident : tactic => `(tactic| (simp -failIfUnchanged only [evalTapePattern, $a:ident, $b:ident, evalTapeExpr]; zzS1))
local macro "zzD2" a:ident b:ident c:ident : tactic => `(tactic| (simp -failIfUnchanged only [evalTapePattern, $a:ident, $b:ident, evalTapeExpr]; rw [$c:ident]; zzS1))
local macro "zzD3" a:ident b:ident c:ident : tactic => `(tactic| (rw [$c:ident]; simp -failIfUnchanged only [evalTapePattern, $a:ident, $b:ident, evalTapeExpr]; zzS1))
local macro "zzD4" a:ident b:ident c:ident d:ident : tactic => `(tactic| (rw [$c:ident]; simp -failIfUnchanged only [evalTapePattern, $a:ident, $b:ident, evalTapeExpr]; rw [$d:ident]; zzS1))
local macro "zzD5" a:ident : tactic => `(tactic| (simp -failIfUnchanged only [evalTapePattern, $a:ident, evalTapeExpr]; zzS1))
local macro "zzH" v:ident h:ident e:term : tactic => `(tactic| obtain ⟨$v:ident, $h:ident⟩ : ∃ $v:ident : zzV, $v:ident = $e := ⟨_, rfl⟩)
@[simp] abbrev zP0 := (zzM (zz1 (zz1 zzD)) 0 zzD)
@[simp] def zK1 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 zzD) zv
@[simp] def zK2 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 2 (zz1 zzD)) zv
@[simp] def zK3 (zv : zzV) := zzE (zzM (zz1 zzD) 2 (zz1 (zz1 zzD))) zv
@[simp] def zK4 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz1 (zz1 zzD)))) zv
@[simp] def zK5 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz1 (zz1 (zz1 zzD))))) zv
@[simp] def zK6 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz1 (zz1 zzD)))) zv
@[simp] def zK7 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz1 (zz1 zzD))) zv
@[simp] def zK8 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz1 zzD)))) zv
@[simp] def zK9 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zz1 (zz1 zzD))))) zv
@[simp] def zK10 (zv : zzV) := zzE (zzM zzD 4 (zz0 (zz1 (zzR [0,1] 0 (zz1 zzD))))) zv
@[simp] def zK11 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz1 zzD))) zv
@[simp] def zK12 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 zzD)))))) zv
@[simp] def zK13 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz1 zzD)) zv
@[simp] def zK14 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz0 (zz1 (zzR [0,1] 0 (zz1 zzD))))) zv
@[simp] def zK15 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 zzD)) zv
@[simp] def zK16 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz1 zzD))) zv
@[simp] def zK17 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 zzD)))))) zv
@[simp] def zK18 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 zzD))) zv
@[simp] def zK19 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 zzD)) zv
@[simp] def zK20 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz0 (zz1 (zzR [0,1] 1 (zz1 zzD))))) zv
@[simp] def zK21 (zv : zzV) := zzE (zzM zzD 0 (zz0 (zz0 (zz1 zzD)))) zv
@[simp] def zK22 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 zzD)) zv
@[simp] def zK23 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz1 zzD))) zv
@[simp] def zK24 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 zzD)))))) zv
@[simp] def zK25 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz0 (zz1 zzD))) zv
@[simp] def zK26 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 zzD))) zv
@[simp] def zK27 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] def zK28 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] def zK29 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] abbrev zP30 := (zzM zzD 2 (zz0 (zz1 (zzR [0,1] 0 zzD))))
@[simp] def zK31 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 (zz0 (zz1 zzD))))) zv
@[simp] def zK32 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz0 (zz1 zzD))))) zv
@[simp] def zK33 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 zzD)) zv
@[simp] def zK34 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK35 (zv : zzV) := zzE (zzM zzD 0 (zz0 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK36 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK37 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD))))) zv
@[simp] def zK38 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz0 (zz1 (zzR [0,1] 0 zzD)))) zv
@[simp] def zK39 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz0 (zz1 (zzR [0,1] 0 zzD)))) zv
@[simp] def zK40 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD)))))) zv
@[simp] def zK41 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD)))))) zv
@[simp] def zK42 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 (zz1 zzD)) zv
@[simp] def zK43 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK44 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK45 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 zzD)) zv
@[simp] def zK46 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz0 (zz1 (zzR [0,1] 0 zzD)))))) zv
@[simp] def zK47 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 zzD)) zv
@[simp] def zK48 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 0 zzD))))))) zv
@[simp] def zK49 (zv : zzV) := zzE (zzM zzD 1 (zz1 zzD)) zv
@[simp] def zK50 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 0 zzD)))))))) zv
@[simp] def zK51 (zv : zzV) := zzE (zzM zzD 1 zzD) zv
@[simp] def zK52 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD)))))))) zv
@[simp] def zK53 (zv : zzV) := zzE (zzM zzD 2 zzD) zv
@[simp] def zK54 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD))))))) zv
@[simp] def zK55 (zv : zzV) := zzE (zzM (zz1 zzD) 3 zzD) zv
@[simp] def zK56 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK57 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD)))))))) zv
@[simp] def zK58 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 zzD) zv
@[simp] def zK59 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz1 (zzR [0,1] 0 zzD)))) zv
@[simp] def zK60 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD))))))) zv
@[simp] def zK61 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 zzD) zv
@[simp] def zK62 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz1 zzD)) zv
@[simp] def zK63 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK64 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK65 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD)))))))) zv
@[simp] abbrev zP66 := (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 zzD)
@[simp] def zK67 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 zzD) zv
@[simp] abbrev zP68 := (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz0 (zz1 (zzR [0,1] 1 zzD))))
@[simp] def zK69 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz1 (zzR [0,1] 1 zzD)))) zv
@[simp] def zK70 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 zzD))))))) zv
@[simp] def zK71 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 zzD) zv
@[simp] def zK72 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 zzD) zv
@[simp] def zK73 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 zzD)) zv
@[simp] def zK74 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD))))) zv
@[simp] def zK75 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz1 zzD)) zv
@[simp] def zK76 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD))))) zv
@[simp] def zK77 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz1 (zzR [0,1] 1 zzD))))) zv
@[simp] def zK78 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 zzD)))))))) zv
@[simp] def zK79 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 2 (zz1 zzD)) zv
@[simp] def zK80 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 zzD)) zv
@[simp] def zK81 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz1 (zzR [0,1] 1 zzD)))))) zv
@[simp] def zK82 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 2 (zz1 (zz1 zzD))) zv
@[simp] def zK83 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 1 zzD))))))) zv
@[simp] def zK84 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 2 (zz1 (zz1 (zz1 zzD)))) zv
@[simp] def zK85 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 1 zzD)))))))) zv
@[simp] def zK86 (zv : zzV) := zzE (zzM (zz1 zzD) 2 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK87 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 2 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK88 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD)))))))) zv
@[simp] def zK89 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 zzD)))))))) zv
@[simp] def zK90 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK91 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 2 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK92 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 zzD))))))))) zv
@[simp] def zK93 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 zzD))))))))) zv
@[simp] def zK94 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK95 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK96 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK97 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK98 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK99 (zv : zzV) := zzE (zzM zzD 4 (zz0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK100 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK101 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK102 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK103 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK104 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK105 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))) zv
@[simp] def zK106 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK107 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK108 (zv : zzV) := zzE (zzM zzD 0 (zz0 (zz0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))))) zv
@[simp] def zK109 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK110 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK111 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK112 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK113 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK114 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK115 (zv : zzV) := zzE (zzM zzD 0 (zz0 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK116 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK117 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK118 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK119 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK120 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK121 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK122 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK123 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] def zK124 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK125 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK126 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))))) zv
@[simp] def zK127 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz1 zzD))))) zv
@[simp] def zK128 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))))))) zv
@[simp] def zK129 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))))) zv
@[simp] def zK130 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))))) zv
@[simp] def zK131 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zz1 zzD)))))) zv
@[simp] def zK132 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))))))) zv
@[simp] def zK133 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK134 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK135 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD)))))) zv
@[simp] def zK136 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK137 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK138 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK139 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD))))) zv
@[simp] abbrev zP140 := (zzM zzD 2 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))
@[simp] def zK141 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK142 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK143 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz1 zzD))) zv
@[simp] def zK144 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD)))))) zv
@[simp] def zK145 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK146 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK147 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK148 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK149 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz1 zzD)) zv
@[simp] def zK150 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD))))) zv
@[simp] def zK151 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK152 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK153 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK154 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK155 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK156 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK157 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 0 zzD) zv
@[simp] def zK158 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz1 zzD))) zv
@[simp] def zK159 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD)))))) zv
@[simp] def zK160 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 0 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK161 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK162 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK163 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK164 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK165 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK166 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK167 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 zzD) zv
@[simp] def zK168 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz1 zzD)) zv
@[simp] def zK169 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz1 zzD))))) zv
@[simp] def zK170 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK171 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK172 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK173 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 zzD)) zv
@[simp] def zK174 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK175 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK176 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK177 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK178 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK179 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK180 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz0 (zzR [1,0] 2 (zz1 (zz1 (zzR [1,1] 3 zzD))))))))))) zv
@[simp] def zK181 (zv : zzV) := zzE (zzM (zz1 zzD) 2 (zz1 zzD)) zv
@[simp] def zK182 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 2 (zz1 zzD)) zv
@[simp] def zK183 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 zzD) zv
@[simp] def zK184 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz1 zzD))) zv
@[simp] def zK185 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 zzD)))))) zv
@[simp] def zK186 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK187 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))) zv
@[simp] def zK188 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK189 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 zzD))) zv
@[simp] def zK190 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 zzD))) zv
@[simp] def zK191 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK192 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK193 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK194 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK195 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK196 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK197 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK198 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz0 (zzR [1,0] 2 (zz1 (zz1 (zzR [1,1] 3 zzD)))))))))) zv
@[simp] def zK199 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz1 zzD))) zv
@[simp] def zK200 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 2 (zz1 (zz1 zzD))) zv
@[simp] def zK201 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] def zK202 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] def zK203 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK204 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK205 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz1 zzD)))) zv
@[simp] def zK206 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK207 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] abbrev zP208 := (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))
@[simp] def zK209 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz1 (zz1 zzD)))) zv
@[simp] def zK210 (zv : zzV) := zzE (zzM (zz1 zzD) 2 (zz1 (zz1 (zz1 zzD)))) zv
@[simp] def zK211 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 2 (zz1 (zz1 (zz1 zzD)))) zv
@[simp] def zK212 (zv : zzV) := zzE (zzM zzD 4 (zz0 (zz1 (zzR [0,1] 0 zzD)))) zv
@[simp] def zK213 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz0 (zz1 zzD))))) zv
@[simp] def zK214 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz0 (zz1 zzD))))) zv
@[simp] def zK215 (zv : zzV) := zzE (zzM zzD 4 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK216 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))))))) zv
@[simp] def zK217 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK218 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz1 zzD))))) zv
@[simp] def zK219 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK220 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK221 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK222 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz1 zzD))) zv
@[simp] def zK223 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK224 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 2 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK225 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 zzD)) zv
@[simp] def zK226 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK227 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK228 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD))))) zv
@[simp] def zK229 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK230 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK231 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK232 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK233 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 zzD)))))) zv
@[simp] def zK234 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK235 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK236 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz0 (zzR [1,0] 2 (zz1 (zz1 (zzR [1,1] 3 zzD))))))))))) zv
@[simp] def zK237 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz1 zzD)) zv
@[simp] def zK238 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK239 (zv : zzV) := zzE (zzM (zz1 zzD) 2 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK240 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 2 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK241 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 zzD) zv
@[simp] def zK242 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz0 (zz1 (zzR [0,1] 0 zzD)))) zv
@[simp] def zK243 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD)))))) zv
@[simp] def zK244 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD)))))) zv
@[simp] abbrev zP245 := (zzM (zz1 (zz1 zzD)) 4 (zz1 (zz1 (zzR [1,1] 0 zzD))))
@[simp] def zK246 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK247 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK248 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK249 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD)))))) zv
@[simp] def zK250 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz1 zzD)))))) zv
@[simp] def zK251 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK252 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK253 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK254 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK255 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))))) zv
@[simp] def zK256 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz0 (zzR [1,0] 2 (zz1 (zz1 (zzR [1,1] 3 zzD)))))))))))) zv
@[simp] def zK257 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK258 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 zzD)) zv
@[simp] def zK259 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz0 (zz1 (zzR [0,1] 0 zzD))))) zv
@[simp] def zK260 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK261 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK262 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK263 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 zzD))))))) zv
@[simp] def zK264 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 zzD))))))) zv
@[simp] def zK265 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))))) zv
@[simp] def zK266 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK267 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK268 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 zzD) zv
@[simp] def zK269 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz0 (zz1 (zzR [0,1] 1 zzD)))) zv
@[simp] def zK270 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))))))) zv
@[simp] abbrev zP271 := (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zzR [1,1] 1 zzD))))
@[simp] def zK272 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK273 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 zzD)) zv
@[simp] def zK274 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz0 (zz1 (zzR [0,1] 1 zzD))))) zv
@[simp] def zK275 (zv : zzV) := zzE (zzM zzD 0 (zz0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK276 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK277 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK278 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK279 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK280 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK281 (zv : zzV) := zzE (zzM zzD 2 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK282 (zv : zzV) := zzE (zzM (zz1 zzD) 0 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK283 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK284 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK285 (zv : zzV) := zzE (zzM zzD 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK286 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz1 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK287 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK288 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK289 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK290 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 1 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK291 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))) zv
@[simp] def zK292 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 1 (zz1 (zz0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK293 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK294 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))))) zv
@[simp] def zK295 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD)))))))) zv
@[simp] def zK296 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))))) zv
@[simp] def zK297 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK298 (zv : zzV) := zzE (zzM zzD 1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK299 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK300 (zv : zzV) := zzE (zzM zzD 2 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK301 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK302 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK303 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK304 (zv : zzV) := zzE (zzM (zz1 zzD) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK305 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz1 (zz1 (zzR [1,1] 0 zzD)))) zv
@[simp] def zK306 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK307 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK308 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 3 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK309 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 0 (zz1 zzD)) zv
@[simp] def zK310 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 0 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK311 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK312 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK313 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD))))) zv
@[simp] def zK314 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz1 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK315 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz1 (zzR [0,1] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK316 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK317 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz1 (zz1 zzD))) zv
@[simp] def zK318 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK319 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK320 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] abbrev zP321 := (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))
@[simp] def zK322 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK323 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 3 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 (zz1 (zz1 (zzR [1,1] 3 zzD)))))))))) zv
@[simp] def zK324 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK325 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK326 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK327 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK328 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK329 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK330 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK331 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz1 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK332 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK333 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 3 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 (zz1 (zz1 (zzR [1,1] 3 zzD))))))))))) zv
@[simp] def zK334 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))) zv
@[simp] def zK335 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))) zv
@[simp] def zK336 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK337 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 0 zzD))))))) zv
@[simp] def zK338 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK339 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK340 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))) zv
@[simp] def zK341 (zv : zzV) := zzE (zzM zzD 0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK342 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] def zK343 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK344 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK345 (zv : zzV) := zzE (zzM zzD 4 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK346 (zv : zzV) := zzE (zzM (zz1 zzD) 4 (zz1 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK347 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 4 (zz1 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK348 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK349 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK350 (zv : zzV) := zzE (zzM (zz1 zzD) 1 (zz1 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))))) zv
@[simp] def zK351 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 1 (zz1 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 (zz1 (zz1 (zzR [1,1] 3 zzD))))))))))) zv
@[simp] def zK352 (zv : zzV) := zzE (zzM (zz1 zzD) 5 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK353 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))))) zv
@[simp] def zK354 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))))) zv
@[simp] def zK355 (zv : zzV) := zzE (zzM zzD 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 0 (zz0 (zz1 (zzR [0,1] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))))))) zv
@[simp] def zK356 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 1 (zz1 (zz0 (zz0 (zz0 (zzR [0,0] 1 (zz0 (zz1 (zzR [0,1] 2 (zz1 (zz1 (zzR [1,1] 3 zzD)))))))))))) zv
@[simp] def zK357 (zv : zzV) := zzE (zzM (zz1 (zz1 zzD)) 4 (zz0 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))) zv
@[simp] def zK358 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 zzD))) 5 (zz1 (zz0 (zzR [1,0] 0 (zz1 (zz1 (zzR [1,1] 1 zzD))))))) zv
@[simp] def zK359 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz0 (zz1 (zz1 (zzR [1,1] 1 zzD))))) zv
@[simp] def zK360 (zv : zzV) := zzE (zzM (zz1 (zz1 (zzR [1,1] 0 zzD))) 4 (zz0 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD)))))))) zv
@[simp] def zK361 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz1 (zzR [1,1] 1 zzD)))) zv
@[simp] def zK362 (zv : zzV) := zzE (zzM (zz1 (zz1 (zz1 (zzR [1,1] 0 zzD)))) 5 (zz1 (zz0 (zzR [1,0] 1 (zz1 (zz1 (zzR [1,1] 2 zzD))))))) zv
@[simp] abbrev p_271_step1 := (zzM (zz1 (zzR [1,1] 0 zzD)) 0 (zz1 (zz0 (zz1 (zzR [1,1] 1 zzD)))))
@[simp] abbrev pat_30_step1 := (zzM (zz1 zzD) 3 (zz1 (zzR [0,1] 0 zzD)))
@[simp] abbrev pat_140_step1 := (zzM (zz1 zzD) 3 (zz0 (zzR [0,0] 0 (zz1 (zz1 (zz1 (zzR [1,1] 1 zzD)))))))
@[simp] abbrev pat_A3 := (zzM (zz1 (zzR [1] 0 (zzR [1,1] 1 zzD))) 3 (zzR [0] 2 (zzR [0,0] 3 (zzR [1] 4 (zzR [0,1] 5 (zzR [1,1] 6 zzD))))))
def zC30 : VarCond := (.and (.not (.ge_const 0 1)) (.and (.not (.ge_const 1 1)) (.and (.not (.ge_const 2 1)) (.and (.not (.ge_const 3 1)) (.and (.and (.ge_const 4 1) (.not (.ge_const 4 2))) (.not (.ge_const 6 1)))))))
def zC140 : VarCond := (.and (.not (.ge_const 0 1)) (.and (.not (.ge_const 1 1)) (.and (.and (.ge_const 2 1) (.not (.ge_const 2 2))) (.and (.and (.ge_const 4 3) (.not (.ge_const 4 4))) (.not (.ge_const 5 1))))))
def zC66 : VarCond := (.and (.and (.ge_const 0 1) (.not (.ge_const 0 2))) (.and (.not (.ge_const 2 1)) (.and (.not (.ge_const 3 1)) (.and (.not (.ge_const 4 1)) (.and (.not (.ge_const 5 1)) (.not (.ge_const 6 1)))))))
def zC76 : VarCond := (.and (.not (.ge_const 0 1)) (.and (.ge_const 1 1) (.and (.not (.ge_const 2 1)) (.and (.not (.ge_const 3 1)) (.and (.and (.ge_const 4 1) (.not (.ge_const 4 2))) (.and (.ge_const 5 1) (.not (.ge_const 6 1))))))))
def zC331 : VarCond := (.and (.not (.ge_const 0 1)) (.and (.not (.ge_const 2 1)) (.and (.not (.ge_const 3 1)) (.and (.and (.ge_const 4 1) (.not (.ge_const 4 2))) (.and (.ge_const 5 1) (.ge_const 6 1))))))
def cond_A3 : VarCond := (.or zC30 (.or zC140 (.or zC66 (.or zC76 zC331))))
def ps : TapePatternSet (Fin 2) (Fin 6) := (pat_A3, cond_A3) :: []
lemma mem_ps_A3 : (pat_A3, cond_A3) ∈ ps := .head _
lemma in_ps_30_step1 (zv : zzV) : IsInPatternSet ps (zzE pat_30_step1 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 | 6 => 0 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [pat_30_step1, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC30 (fun k => match k with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 | 6 => 0 | _ => 0) := by simp -failIfUnchanged [zC30, evalVarCond]; try omega
    exact Or.inl h_c
lemma in_ps_140_step1 (zv : zzV) : IsInPatternSet ps (zzE pat_140_step1 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => 0 | 2 => 1 | 3 => zv 0 | 4 => 3 | 5 => 0 | 6 => zv 1 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [pat_140_step1, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC140 (fun k => match k with | 0 => 0 | 1 => 0 | 2 => 1 | 3 => zv 0 | 4 => 3 | 5 => 0 | 6 => zv 1 | _ => 0) := by simp -failIfUnchanged [zC140, evalVarCond]; try omega
    exact Or.inr (Or.inl h_c)
lemma zI66 (zv : zzV) : IsInPatternSet ps (zzE zP66 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 1 | 1 => zv 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [zP66, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC66 (fun k => match k with | 0 => 1 | 1 => zv 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | _ => 0) := by simp -failIfUnchanged [zC66, evalVarCond]; try omega
    exact Or.inr (Or.inr (Or.inl h_c))
lemma zI63 (zv : zzV) : IsInPatternSet ps (zK63 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 + 1 | 6 => 0 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [zK63, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC76 (fun k => match k with | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 + 1 | 6 => 0 | _ => 0) := by simp -failIfUnchanged [zC76, evalVarCond]; try omega
    exact Or.inr (Or.inr (Or.inr (Or.inl h_c)))
lemma zI76 (zv : zzV) : IsInPatternSet ps (zK76 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => zv 0 + 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 1 + 1 | 6 => 0 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [zK76, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC76 (fun k => match k with | 0 => 0 | 1 => zv 0 + 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 1 + 1 | 6 => 0 | _ => 0) := by simp -failIfUnchanged [zC76, evalVarCond]; try omega
    exact Or.inr (Or.inr (Or.inr (Or.inl h_c)))
lemma zI287 (zv : zzV) : IsInPatternSet ps (zK287 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 + 1 | 6 => zv 1 + 1 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [zK287, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC331 (fun k => match k with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 + 1 | 6 => zv 1 + 1 | _ => 0) := by simp -failIfUnchanged [zC331, evalVarCond]; try omega
    exact Or.inr (Or.inr (Or.inr (Or.inr h_c)))
lemma zI314 (zv : zzV) : IsInPatternSet ps (zK314 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 + 1 | 6 => zv 1 + 1 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [zK314, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC331 (fun k => match k with | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 0 + 1 | 6 => zv 1 + 1 | _ => 0) := by simp -failIfUnchanged [zC331, evalVarCond]; try omega
    exact Or.inr (Or.inr (Or.inr (Or.inr h_c)))
lemma zI331 (zv : zzV) : IsInPatternSet ps (zK331 zv) := by
  refine ⟨(pat_A3, cond_A3), mem_ps_A3, fun k => match k with | 0 => 0 | 1 => zv 0 + 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 1 + 1 | 6 => zv 2 + 1 | _ => 0, ?_, ?_⟩
  · simp -failIfUnchanged only [zK331, pat_A3, evalTapePattern, evalTapeExpr]
    zzS2
  · have h_c : evalVarCond zC331 (fun k => match k with | 0 => 0 | 1 => zv 0 + 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => zv 1 + 1 | 6 => zv 2 + 1 | _ => 0) := by simp -failIfUnchanged [zC331, evalVarCond]; try omega
    exact Or.inr (Or.inr (Or.inr (Or.inr h_c)))
lemma init_reaches_pat_30_step1 : (init []) [target_tm]⊢* (zzE pat_30_step1 (fun _ => 0)) := by
  use 4
  have h_raw : multiStep target_tm (init []) 4 = some (⟨some 3, ⟨1, (1 : Fin 2) >> default, (0 : Fin 2) >> default⟩⟩ : Cfg (Fin 2) (Fin 6)) := rfl
  rw [h_raw]
  simp only [pat_30_step1, evalTapePattern, evalTapeExpr, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁
  obtain ⟨m, _, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
local notation "zzQ" c:arg => ∃ cfg', (c [target_tm]⊢⁺ cfg') /\ (IsInPatternSet ps cfg' \/ (step target_tm cfg').isNone)
lemma zzB {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h_step : step target_tm c_1 = some c_2)
    (h_in : IsInPatternSet ps c_2) :
    zzQ (c_1) :=
  ⟨c_2, zStp h_step, Or.inl h_in⟩
lemma zzC {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h_step : step target_tm c_1 = some c_2)
    (h_next : zzQ (c_2)) :
    zzQ (c_1) := by
  rcases h_next with ⟨cfg', h₂, h_in⟩
  exact ⟨cfg', zPt (zStp h_step) h₂, h_in⟩
local macro "zzR1" p1:ident p2:ident v:ident h:ident : tactic => `(tactic| refine @zzC _ (zzE $p2:ident $v:ident) (by zzD3 $p1:ident $p2:ident $h:ident) ?_)
local macro "zzR2" p1:ident p2:ident v:ident h:ident hr:ident : tactic => `(tactic| refine @zzC _ (zzE $p2:ident $v:ident) (by zzD4 $p1:ident $p2:ident $h:ident $hr:ident) ?_)
local macro "zzO" v:ident h:ident e:term p1:ident p2:ident : tactic => `(tactic| (zzH $v:ident $h:ident $e; zzR1 $p1:ident $p2:ident $v:ident $h:ident))
local macro "zzO2" v:ident h:ident e:term p1:ident p2:ident hr:ident : tactic => `(tactic| (zzH $v:ident $h:ident $e; zzR2 $p1:ident $p2:ident $v:ident $h:ident $hr:ident))
local macro "zzK1" c1:ident c2:ident e:term : tactic => `(tactic| (refine zzC ?_ $e; zzD1 $c1:ident $c2:ident))
local macro "zzK2" c1:ident c2:ident h:ident e:term : tactic => `(tactic| (refine zzC ?_ $e; zzD2 $c1:ident $c2:ident $h:ident))
local macro "zzKB1" c1:ident c2:ident e:term : tactic => `(tactic| (refine zzB ?_ $e; zzD1 $c1:ident $c2:ident))
local macro "zzKB2" c1:ident c2:ident h:ident e:term : tactic => `(tactic| (refine zzB ?_ $e; zzD2 $c1:ident $c2:ident $h:ident))
lemma step_to_ps_30 (zv : zzV) : zzQ ((zzE zP30 zv)) := by zzKB1 zP30 pat_30_step1 (in_ps_30_step1 zv)
lemma step_to_ps_140 (zv : zzV) : zzQ ((zzE zP140 zv)) := by zzKB1 zP140 pat_140_step1 (in_ps_140_step1 zv)
lemma zS27 (zv : zzV) : zzQ ((zK27 zv)) := by zzK1 zK27 zP30 (step_to_ps_30 (zzF1 (1)))
lemma zS25 (zv : zzV) : zzQ ((zK25 zv)) := by zzK1 zK25 zK27 (zS27 (fun _ => 0))
lemma zS21 (zv : zzV) : zzQ ((zK21 zv)) := by zzK1 zK21 zK25 (zS25 (fun _ => 0))
lemma zS18 (zv : zzV) : zzQ ((zK18 zv)) := by zzK1 zK18 zK21 (zS21 (fun _ => 0))
lemma zS15 (zv : zzV) : zzQ ((zK15 zv)) := by zzK1 zK15 zK18 (zS18 (fun _ => 0))
lemma zS13 (zv : zzV) : zzQ ((zK13 zv)) := by zzK1 zK13 zK15 (zS15 (fun _ => 0))
lemma zS11 (zv : zzV) : zzQ ((zK11 zv)) := by zzK1 zK11 zK13 (zS13 (fun _ => 0))
lemma zS44 (zv : zzV) : zzQ ((zK44 zv)) := by zzK1 zK44 zP30 (step_to_ps_30 (zzF1 ((zv 0 + 1))))
lemma zS39 (zv : zzV) : zzQ ((zK39 zv)) := by zzK1 zK39 zK44 (zS44 (zzF1 (zv 0)))
lemma zS35 (zv : zzV) : zzQ ((zK35 zv)) := by zzK1 zK35 zK39 (zS39 (zzF1 (zv 0)))
lemma zS31 (zv : zzV) : zzQ ((zK31 zv)) := by zzK1 zK31 zK35 (zS35 (zzF1 (1)))
lemma zS28 (zv : zzV) : zzQ ((zK28 zv)) := by zzK1 zK28 zK31 (zS31 (fun _ => 0))
lemma zS40 (zv : zzV) : zzQ ((zK40 zv)) := by zzK1 zK40 zK35 (zS35 (zzF1 ((zv 0 + 1))))
lemma zS36 (zv : zzV) : zzQ ((zK36 zv)) := by zzK1 zK36 zK40 (zS40 (zzF1 (zv 0)))
lemma zA41 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK37 zv'))) :
  zzQ ((zK41 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK41 zK36 h_vl (zS36 (zzF1 ((zv 1 + 1))))
  · zzK2 zK41 zK37 h_vl (h_u (zzF2 (l) ((zv 1 + 1))) (by (try simp only []); omega))
lemma zS37 (zv : zzV) : zzQ ((zK37 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK37 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK37 zK41 (zA41 (zzF2 (zv 0) (zv 1)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS32 (zv : zzV) : zzQ ((zK32 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK32 zK36 h_vl (zS36 (zzF1 (1)))
  · zzK2 zK32 zK37 h_vl (zS37 (zzF2 (l) (1)))
lemma zS29 (zv : zzV) : zzQ ((zK29 zv)) := by zzK1 zK29 zK32 (zS32 (zzF1 (zv 0)))
lemma step_cfg_284_succ (zv : zzV) : zzQ ((zK284 (zzF2 ((zv 0 + 1)) (zv 1)))) := by zzKB1 zK284 zK287 (zI287 (zzF2 (zv 0) (zv 1)))
lemma zS281 (zv : zzV) : zzQ ((zK281 zv)) := by zzK1 zK281 zK284 (step_cfg_284_succ zv)
lemma zS279 (zv : zzV) : zzQ ((zK279 zv)) := by zzK1 zK279 zK281 (zS281 (zzF2 (zv 0) (zv 1)))
lemma zS275 (zv : zzV) : zzQ ((zK275 zv)) := by zzK1 zK275 zK279 (zS279 (zzF2 (zv 0) (zv 1)))
lemma zS270 (zv : zzV) : zzQ ((zK270 zv)) := by zzK1 zK270 zK275 (zS275 (zzF2 (1) (zv 0)))
lemma zS260 (zv : zzV) : zzQ ((zK260 zv)) := by zzK1 zK260 zK270 (zS270 (zzF1 (zv 0)))
lemma zS285 (zv : zzV) : zzQ ((zK285 zv)) := by zzK1 zK285 zK275 (zS275 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS282 (zv : zzV) : zzQ ((zK282 zv)) := by zzK1 zK282 zK285 (zS285 (zzF2 (zv 0) (zv 1)))
lemma zA286 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK283 zv'))) :
  zzQ ((zK286 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK286 zK282 h_vl (zS282 (zzF2 ((zv 1 + 1)) (zv 2)))
  · zzK2 zK286 zK283 h_vl (h_u (zzF3 (l) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS283 (zv : zzV) : zzQ ((zK283 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK283 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK283 zK286 (zA286 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS280 (zv : zzV) : zzQ ((zK280 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK280 zK282 h_vl (zS282 (zzF2 (1) (zv 1)))
  · zzK2 zK280 zK283 h_vl (zS283 (zzF3 (l) (1) (zv 1)))
lemma zS276 (zv : zzV) : zzQ ((zK276 zv)) := by zzK1 zK276 zK280 (zS280 (zzF2 (zv 0) (zv 1)))
lemma step_hub_271_step1 (zv : zzV) : zzQ ((zzE p_271_step1 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · rcases h_vl : zv 0 with _ | l
    · have h_eq : zzE p_271_step1 zv = zK28 (fun _ => 0) := by
        simp -failIfUnchanged only [evalTapePattern, p_271_step1, zK28, evalTapeExpr]; rw [h_vr, h_vl]
        zzS2
      rw [h_eq]; exact zS28 (fun _ => 0)
    · have h_eq : zzE p_271_step1 zv = zK29 (zzF1 (l)) := by
        simp -failIfUnchanged only [evalTapePattern, p_271_step1, zK29, evalTapeExpr]; rw [h_vr, h_vl]
        zzS2
      rw [h_eq]; exact zS29 (zzF1 (l))
  · rcases h_vl : zv 0 with _ | l
    · have h_eq : zzE p_271_step1 zv = zK260 (zzF1 (r)) := by
        simp -failIfUnchanged only [evalTapePattern, p_271_step1, zK260, evalTapeExpr]; rw [h_vr, h_vl]
        zzS2
      rw [h_eq]; exact zS260 (zzF1 (r))
    · have h_eq : zzE p_271_step1 zv = zK276 (zzF2 (l) (r)) := by
        simp -failIfUnchanged only [evalTapePattern, p_271_step1, zK276, evalTapeExpr]; rw [h_vr, h_vl]
        zzS2
      rw [h_eq]; exact zS276 (zzF2 (l) (r))
lemma step_to_ps_271 (zv : zzV) : zzQ ((zzE zP271 zv)) := by zzK1 zP271 p_271_step1 (step_hub_271_step1 zv)
lemma step_to_ps_245 (zv : zzV) : zzQ ((zzE zP245 zv)) := by zzK1 zP245 p_271_step1 (step_hub_271_step1 (zzF2 (0) (zv 0)))
lemma zS26 (zv : zzV) : zzQ ((zK26 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK26 zK28 h_vl (zS28 (fun _ => 0))
  · zzK2 zK26 zK29 h_vl (zS29 (zzF1 (l)))
lemma zS22 (zv : zzV) : zzQ ((zK22 zv)) := by zzK1 zK22 zK26 (zS26 (zzF1 (zv 0)))
lemma zS19 (zv : zzV) : zzQ ((zK19 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK19 zK15 h_vl (zS15 (fun _ => 0))
  · zzK2 zK19 zK22 h_vl (zS22 (zzF1 (l)))
lemma zS16 (zv : zzV) : zzQ ((zK16 zv)) := by zzK1 zK16 zK19 (zS19 (zzF1 (1)))
lemma zS23 (zv : zzV) : zzQ ((zK23 zv)) := by zzK1 zK23 zK19 (zS19 (zzF1 ((zv 0 + 1))))
lemma zA24 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK20 zv'))) :
  zzQ ((zK24 zv)) := by
  zzK1 zK24 zK20 (h_u (zzF2 ((zv 0 + 1)) (zv 1)) (by (try simp only []); omega))
lemma zS20 (zv : zzV) : zzQ ((zK20 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK20 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK20 zK23 h_vr (zS23 (zzF1 (zv 0)))
  · zzK2 zK20 zK24 h_vr (zA24 (zzF2 (zv 0) (r)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS17 (zv : zzV) : zzQ ((zK17 zv)) := by zzK1 zK17 zK20 (zS20 (zzF2 (1) (zv 0)))
lemma zS14 (zv : zzV) : zzQ ((zK14 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK14 zK16 h_vr (zS16 (fun _ => 0))
  · zzK2 zK14 zK17 h_vr (zS17 (zzF1 (r)))
lemma zS12 (zv : zzV) : zzQ ((zK12 zv)) := by zzK1 zK12 zK14 (zS14 (zzF1 (zv 0)))
lemma zS10 (zv : zzV) : zzQ ((zK10 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK10 zK11 h_vr (zS11 (fun _ => 0))
  · zzK2 zK10 zK12 h_vr (zS12 (zzF1 (r)))
lemma zS9 (zv : zzV) : zzQ ((zK9 zv)) := by zzK1 zK9 zK10 (zS10 (zzF1 (1)))
lemma zS8 (zv : zzV) : zzQ ((zK8 zv)) := by zzK1 zK8 zK9 (zS9 (fun _ => 0))
lemma zS7 (zv : zzV) : zzQ ((zK7 zv)) := by zzK1 zK7 zK8 (zS8 (fun _ => 0))
lemma zS6 (zv : zzV) : zzQ ((zK6 zv)) := by zzK1 zK6 zK7 (zS7 (fun _ => 0))
lemma zS5 (zv : zzV) : zzQ ((zK5 zv)) := by zzK1 zK5 zK6 (zS6 (fun _ => 0))
lemma zS4 (zv : zzV) : zzQ ((zK4 zv)) := by zzK1 zK4 zK5 (zS5 (fun _ => 0))
lemma zS3 (zv : zzV) : zzQ ((zK3 zv)) := by zzK1 zK3 zK4 (zS4 (fun _ => 0))
lemma zS2 (zv : zzV) : zzQ ((zK2 zv)) := by zzK1 zK2 zK3 (zS3 (fun _ => 0))
lemma zS1 (zv : zzV) : zzQ ((zK1 zv)) := by zzK1 zK1 zK2 (zS2 (fun _ => 0))
lemma step_hub_0 (zv : zzV) : zzQ ((zzE zP0 zv)) := by zzK1 zP0 zK1 (zS1 (fun _ => 0))
lemma zS33 (zv : zzV) : zzQ ((zK33 zv)) := by zzK1 zK33 zP0 (step_hub_0 (fun _ => 0))
lemma zS61 (zv : zzV) : zzQ ((zK61 zv)) := by zzKB1 zK61 zP66 (zI66 (zzF1 (1)))
lemma zS58 (zv : zzV) : zzQ ((zK58 zv)) := by zzK1 zK58 zK61 (zS61 (fun _ => 0))
lemma zS55 (zv : zzV) : zzQ ((zK55 zv)) := by zzK1 zK55 zK58 (zS58 (fun _ => 0))
lemma zS53 (zv : zzV) : zzQ ((zK53 zv)) := by zzK1 zK53 zK55 (zS55 (fun _ => 0))
lemma zS51 (zv : zzV) : zzQ ((zK51 zv)) := by zzK1 zK51 zK53 (zS53 (fun _ => 0))
lemma zS49 (zv : zzV) : zzQ ((zK49 zv)) := by zzK1 zK49 zK51 (zS51 (fun _ => 0))
lemma zS47 (zv : zzV) : zzQ ((zK47 zv)) := by zzK1 zK47 zK49 (zS49 (fun _ => 0))
lemma zS45 (zv : zzV) : zzQ ((zK45 zv)) := by zzK1 zK45 zK47 (zS47 (fun _ => 0))
lemma zS42 (zv : zzV) : zzQ ((zK42 zv)) := by zzK1 zK42 zK45 (zS45 (fun _ => 0))
lemma zS241 (zv : zzV) : zzQ ((zK241 zv)) := by
  refine ⟨zzE { left := (.sym 1 (.sym 1 (.sym 1 .default))), head := some 5, right := .default } (fun _ => 0), zStp ?_, Or.inr (by simp [step, target_tm, evalTapePattern, evalTapeExpr])⟩
  zzD5 zK241
lemma zS225 (zv : zzV) : zzQ ((zK225 zv)) := by zzK1 zK225 zK241 (zS241 (fun _ => 0))
lemma zS268 (zv : zzV) : zzQ ((zK268 zv)) := by
  refine ⟨zzE { left := (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))), head := some 5, right := .default } (zzF1 (zv 0)), zStp ?_, Or.inr (by simp [step, target_tm, evalTapePattern, evalTapeExpr])⟩
  zzD5 zK268
lemma zS258 (zv : zzV) : zzQ ((zK258 zv)) := by zzK1 zK258 zK268 (zS268 (zzF1 (1)))
lemma zS273 (zv : zzV) : zzQ ((zK273 zv)) := by zzK1 zK273 zK268 (zS268 (zzF1 ((zv 0 + 1))))
lemma zA274 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK269 zv'))) :
  zzQ ((zK274 zv)) := by
  zzK1 zK274 zK269 (h_u (zzF2 ((zv 0 + 1)) (zv 1)) (by (try simp only []); omega))
lemma zS269 (zv : zzV) : zzQ ((zK269 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK269 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK269 zK273 h_vr (zS273 (zzF1 (zv 0)))
  · zzK2 zK269 zK274 h_vr (zA274 (zzF2 (zv 0) (r)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS259 (zv : zzV) : zzQ ((zK259 zv)) := by zzK1 zK259 zK269 (zS269 (zzF2 (1) (zv 0)))
lemma zS242 (zv : zzV) : zzQ ((zK242 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK242 zK258 h_vr (zS258 (fun _ => 0))
  · zzK2 zK242 zK259 h_vr (zS259 (zzF1 (r)))
lemma zS226 (zv : zzV) : zzQ ((zK226 zv)) := by zzK1 zK226 zK242 (zS242 (zzF1 (zv 0)))
lemma zS212 (zv : zzV) : zzQ ((zK212 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK212 zK225 h_vr (zS225 (fun _ => 0))
  · zzK2 zK212 zK226 h_vr (zS226 (zzF1 (r)))
lemma zS201 (zv : zzV) : zzQ ((zK201 zv)) := by zzK1 zK201 zK212 (zS212 (zzF1 (1)))
lemma zS189 (zv : zzV) : zzQ ((zK189 zv)) := by zzK1 zK189 zK201 (zS201 (fun _ => 0))
lemma zS237 (zv : zzV) : zzQ ((zK237 zv)) := by zzK1 zK237 zK189 (zS189 (fun _ => 0))
lemma zS222 (zv : zzV) : zzQ ((zK222 zv)) := by zzK1 zK222 zK237 (zS237 (fun _ => 0))
lemma zS209 (zv : zzV) : zzQ ((zK209 zv)) := by zzK1 zK209 zK222 (zS222 (fun _ => 0))
lemma zS199 (zv : zzV) : zzQ ((zK199 zv)) := by zzK1 zK199 zK209 (zS209 (fun _ => 0))
lemma zS181 (zv : zzV) : zzQ ((zK181 zv)) := by zzK1 zK181 zK199 (zS199 (fun _ => 0))
lemma zS229 (zv : zzV) : zzQ ((zK229 zv)) := by zzK1 zK229 zP245 (step_to_ps_245 (zzF1 (zv 0)))
lemma zS261 (zv : zzV) : zzQ ((zK261 zv)) := by zzK1 zK261 zP271 (step_to_ps_271 (zzF2 (1) (zv 0)))
lemma zS277 (zv : zzV) : zzQ ((zK277 zv)) := by zzK1 zK277 zP271 (step_to_ps_271 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA278 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK272 zv'))) :
  zzQ ((zK278 zv)) := by
  zzK1 zK278 zK272 (h_u (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS272 (zv : zzV) : zzQ ((zK272 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK272 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK272 zK277 h_vr (zS277 (zzF2 (zv 0) (zv 2)))
  · zzK2 zK272 zK278 h_vr (zA278 (zzF3 (zv 0) (r) (zv 2)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS262 (zv : zzV) : zzQ ((zK262 zv)) := by zzK1 zK262 zK272 (zS272 (zzF3 (1) (zv 0) (zv 1)))
lemma zS246 (zv : zzV) : zzQ ((zK246 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK246 zK261 h_vr (zS261 (zzF1 (zv 1)))
  · zzK2 zK246 zK262 h_vr (zS262 (zzF2 (r) (zv 1)))
lemma zS230 (zv : zzV) : zzQ ((zK230 zv)) := by zzK1 zK230 zK246 (zS246 (zzF2 (zv 0) (zv 1)))
lemma zS215 (zv : zzV) : zzQ ((zK215 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK215 zK229 h_vr (zS229 (zzF1 (zv 1)))
  · zzK2 zK215 zK230 h_vr (zS230 (zzF2 (r) (zv 1)))
lemma zS203 (zv : zzV) : zzQ ((zK203 zv)) := by zzK1 zK203 zK215 (zS215 (zzF2 (1) (zv 0)))
lemma zS191 (zv : zzV) : zzQ ((zK191 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK191 zK201 h_vr (zS201 (fun _ => 0))
  · zzK2 zK191 zK203 h_vr (zS203 (zzF1 (r)))
lemma zS267 (zv : zzV) : zzQ ((zK267 zv)) := by zzK1 zK267 zK191 (zS191 (zzF1 ((zv 0 + 1))))
lemma zS257 (zv : zzV) : zzQ ((zK257 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK257 zK237 h_vr (zS237 (fun _ => 0))
  · zzK2 zK257 zK267 h_vr (zS267 (zzF1 (r)))
lemma zS238 (zv : zzV) : zzQ ((zK238 zv)) := by zzK1 zK238 zK257 (zS257 (zzF1 (zv 0)))
lemma zS223 (zv : zzV) : zzQ ((zK223 zv)) := by zzK1 zK223 zK238 (zS238 (zzF1 (zv 0)))
lemma zS210 (zv : zzV) : zzQ ((zK210 zv)) := by zzK1 zK210 zK223 (zS223 (zzF1 (1)))
lemma zS239 (zv : zzV) : zzQ ((zK239 zv)) := by zzK1 zK239 zK223 (zS223 (zzF1 ((zv 0 + 1))))
lemma zA240 (zv : zzV)
  (h_u : ∀ zv', zv' 0 <= zv 0 -> zzQ ((zK224 zv'))) :
  zzQ ((zK240 zv)) := by
  zzK1 zK240 zK224 (h_u (zzF2 (zv 0) ((zv 1 + 1))) (by (try simp only []); omega))
lemma zS224 (zv : zzV) : zzQ ((zK224 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK224 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK224 zK239 h_vl (zS239 (zzF1 (zv 1)))
  · zzK2 zK224 zK240 h_vl (zA240 (zzF2 (l) (zv 1)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS211 (zv : zzV) : zzQ ((zK211 zv)) := by zzK1 zK211 zK224 (zS224 (zzF2 (zv 0) (1)))
lemma zS200 (zv : zzV) : zzQ ((zK200 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK200 zK210 h_vl (zS210 (fun _ => 0))
  · zzK2 zK200 zK211 h_vl (zS211 (zzF1 (l)))
lemma zS182 (zv : zzV) : zzQ ((zK182 zv)) := by zzK1 zK182 zK200 (zS200 (zzF1 (zv 0)))
lemma zS167 (zv : zzV) : zzQ ((zK167 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK167 zK181 h_vl (zS181 (fun _ => 0))
  · zzK2 zK167 zK182 h_vl (zS182 (zzF1 (l)))
lemma zS157 (zv : zzV) : zzQ ((zK157 zv)) := by zzK1 zK157 zK167 (zS167 (zzF1 (1)))
lemma zS149 (zv : zzV) : zzQ ((zK149 zv)) := by zzK1 zK149 zK157 (zS157 (fun _ => 0))
lemma zS143 (zv : zzV) : zzQ ((zK143 zv)) := by zzK1 zK143 zK149 (zS149 (fun _ => 0))
lemma zS183 (zv : zzV) : zzQ ((zK183 zv)) := by zzK1 zK183 zK167 (zS167 (zzF1 ((zv 0 + 1))))
lemma zS168 (zv : zzV) : zzQ ((zK168 zv)) := by zzK1 zK168 zK183 (zS183 (zzF1 (zv 0)))
lemma zS158 (zv : zzV) : zzQ ((zK158 zv)) := by zzK1 zK158 zK168 (zS168 (zzF1 (1)))
lemma zS184 (zv : zzV) : zzQ ((zK184 zv)) := by zzK1 zK184 zK168 (zS168 (zzF1 ((zv 0 + 1))))
lemma zA185 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK169 zv'))) :
  zzQ ((zK185 zv)) := by
  zzK1 zK185 zK169 (h_u (zzF2 ((zv 0 + 1)) (zv 1)) (by (try simp only []); omega))
lemma zS169 (zv : zzV) : zzQ ((zK169 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK169 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK169 zK184 h_vr (zS184 (zzF1 (zv 0)))
  · zzK2 zK169 zK185 h_vr (zA185 (zzF2 (zv 0) (r)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS159 (zv : zzV) : zzQ ((zK159 zv)) := by zzK1 zK159 zK169 (zS169 (zzF2 (1) (zv 0)))
lemma zS150 (zv : zzV) : zzQ ((zK150 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK150 zK158 h_vr (zS158 (fun _ => 0))
  · zzK2 zK150 zK159 h_vr (zS159 (zzF1 (r)))
lemma zS144 (zv : zzV) : zzQ ((zK144 zv)) := by zzK1 zK144 zK150 (zS150 (zzF1 (zv 0)))
lemma zS139 (zv : zzV) : zzQ ((zK139 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK139 zK143 h_vr (zS143 (fun _ => 0))
  · zzK2 zK139 zK144 h_vr (zS144 (zzF1 (r)))
lemma zS135 (zv : zzV) : zzQ ((zK135 zv)) := by zzK1 zK135 zK139 (zS139 (zzF1 ((zv 0 + 1))))
lemma zS131 (zv : zzV) : zzQ ((zK131 zv)) := by zzK1 zK131 zK135 (zS135 (zzF1 (1)))
lemma zS127 (zv : zzV) : zzQ ((zK127 zv)) := by zzK1 zK127 zK131 (zS131 (fun _ => 0))
lemma zS123 (zv : zzV) : zzQ ((zK123 zv)) := by zzK1 zK123 zK127 (zS127 (fun _ => 0))
lemma zS136 (zv : zzV) : zzQ ((zK136 zv)) := by zzK1 zK136 zP140 (step_to_ps_140 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS132 (zv : zzV) : zzQ ((zK132 zv)) := by zzK1 zK132 zK136 (zS136 (zzF2 (1) (zv 0)))
lemma zS128 (zv : zzV) : zzQ ((zK128 zv)) := by zzK1 zK128 zK132 (zS132 (zzF1 (zv 0)))
lemma zS124 (zv : zzV) : zzQ ((zK124 zv)) := by zzK1 zK124 zK128 (zS128 (zzF1 (zv 0)))
lemma zS121 (zv : zzV) : zzQ ((zK121 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK121 zK123 h_vr (zS123 (fun _ => 0))
  · zzK2 zK121 zK124 h_vr (zS124 (zzF1 (r)))
lemma zS119 (zv : zzV) : zzQ ((zK119 zv)) := by zzK1 zK119 zK121 (zS121 (zzF1 (zv 0)))
lemma zS227 (zv : zzV) : zzQ ((zK227 zv)) := by zzK1 zK227 zK212 (zS212 (zzF1 ((zv 0 + 1))))
lemma zS213 (zv : zzV) : zzQ ((zK213 zv)) := by zzK1 zK213 zK227 (zS227 (zzF1 (1)))
lemma zS243 (zv : zzV) : zzQ ((zK243 zv)) := by zzK1 zK243 zK227 (zS227 (zzF1 ((zv 0 + 1))))
lemma zA244 (zv : zzV)
  (h_u : ∀ zv', zv' 0 <= zv 0 -> zzQ ((zK228 zv'))) :
  zzQ ((zK244 zv)) := by
  zzK1 zK244 zK228 (h_u (zzF2 (zv 0) ((zv 1 + 1))) (by (try simp only []); omega))
lemma zS228 (zv : zzV) : zzQ ((zK228 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK228 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK228 zK243 h_vl (zS243 (zzF1 (zv 1)))
  · zzK2 zK228 zK244 h_vl (zA244 (zzF2 (l) (zv 1)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS214 (zv : zzV) : zzQ ((zK214 zv)) := by zzK1 zK214 zK228 (zS228 (zzF2 (zv 0) (1)))
lemma zS202 (zv : zzV) : zzQ ((zK202 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK202 zK213 h_vl (zS213 (fun _ => 0))
  · zzK2 zK202 zK214 h_vl (zS214 (zzF1 (l)))
lemma zS190 (zv : zzV) : zzQ ((zK190 zv)) := by zzK1 zK190 zK202 (zS202 (zzF1 (zv 0)))
lemma zS173 (zv : zzV) : zzQ ((zK173 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK173 zK189 h_vl (zS189 (fun _ => 0))
  · zzK2 zK173 zK190 h_vl (zS190 (zzF1 (l)))
lemma zS231 (zv : zzV) : zzQ ((zK231 zv)) := by zzK1 zK231 zK215 (zS215 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS216 (zv : zzV) : zzQ ((zK216 zv)) := by zzK1 zK216 zK231 (zS231 (zzF2 (1) (zv 0)))
lemma zS247 (zv : zzV) : zzQ ((zK247 zv)) := by zzK1 zK247 zK231 (zS231 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA248 (zv : zzV)
  (h_u : ∀ zv', zv' 0 <= zv 0 -> zzQ ((zK232 zv'))) :
  zzQ ((zK248 zv)) := by
  zzK1 zK248 zK232 (h_u (zzF3 (zv 0) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS232 (zv : zzV) : zzQ ((zK232 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK232 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK232 zK247 h_vl (zS247 (zzF2 (zv 1) (zv 2)))
  · zzK2 zK232 zK248 h_vl (zA248 (zzF3 (l) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS217 (zv : zzV) : zzQ ((zK217 zv)) := by zzK1 zK217 zK232 (zS232 (zzF3 (zv 0) (1) (zv 1)))
lemma zS204 (zv : zzV) : zzQ ((zK204 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK204 zK216 h_vl (zS216 (zzF1 (zv 1)))
  · zzK2 zK204 zK217 h_vl (zS217 (zzF2 (l) (zv 1)))
lemma zS192 (zv : zzV) : zzQ ((zK192 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK192 zK202 h_vr (zS202 (zzF1 (zv 0)))
  · zzK2 zK192 zK204 h_vr (zS204 (zzF2 (zv 0) (r)))
lemma zS174 (zv : zzV) : zzQ ((zK174 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK174 zK191 h_vl (zS191 (zzF1 ((zv 1 + 1))))
  · zzK2 zK174 zK192 h_vl (zS192 (zzF2 (l) ((zv 1 + 1))))
lemma zS163 (zv : zzV) : zzQ ((zK163 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK163 zK173 h_vr (zS173 (zzF1 (1)))
  · zzK2 zK163 zK174 h_vr (zS174 (zzF2 (1) (r)))
lemma zS153 (zv : zzV) : zzQ ((zK153 zv)) := by zzK1 zK153 zK163 (zS163 (zzF1 (zv 0)))
lemma zS193 (zv : zzV) : zzQ ((zK193 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK193 zK173 h_vr (zS173 (zzF1 ((zv 0 + 1))))
  · zzK2 zK193 zK174 h_vr (zS174 (zzF2 ((zv 0 + 1)) (r)))
lemma zS175 (zv : zzV) : zzQ ((zK175 zv)) := by zzK1 zK175 zK193 (zS193 (zzF2 (zv 0) (zv 1)))
lemma zA194 (zv : zzV)
  (h_u : ∀ zv', zv' 1 < zv 1 -> zzQ ((zK176 zv'))) :
  zzQ ((zK194 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK194 zK175 h_vr (zS175 (zzF2 ((zv 0 + 1)) (zv 2)))
  · zzK2 zK194 zK176 h_vr (h_u (zzF3 ((zv 0 + 1)) (r) (zv 2)) (by (try simp only []); omega))
lemma zS176 (zv : zzV) : zzQ ((zK176 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK176 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK176 zK194 (zA194 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS164 (zv : zzV) : zzQ ((zK164 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK164 zK175 h_vr (zS175 (zzF2 (1) (zv 1)))
  · zzK2 zK164 zK176 h_vr (zS176 (zzF3 (1) (r) (zv 1)))
lemma zS154 (zv : zzV) : zzQ ((zK154 zv)) := by zzK1 zK154 zK164 (zS164 (zzF2 (zv 0) (zv 1)))
lemma zS147 (zv : zzV) : zzQ ((zK147 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK147 zK153 h_vr (zS153 (zzF1 (zv 1)))
  · zzK2 zK147 zK154 h_vr (zS154 (zzF2 (r) (zv 1)))
lemma zS141 (zv : zzV) : zzQ ((zK141 zv)) := by zzK1 zK141 zK147 (zS147 (zzF2 (zv 0) (zv 1)))
lemma zS137 (zv : zzV) : zzQ ((zK137 zv)) := by zzK1 zK137 zK141 (zS141 (zzF2 (zv 0) (zv 1)))
lemma zS133 (zv : zzV) : zzQ ((zK133 zv)) := by zzK1 zK133 zK137 (zS137 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS129 (zv : zzV) : zzQ ((zK129 zv)) := by zzK1 zK129 zK133 (zS133 (zzF2 (1) (zv 0)))
lemma zS125 (zv : zzV) : zzQ ((zK125 zv)) := by zzK1 zK125 zK129 (zS129 (zzF1 (zv 0)))
lemma zS263 (zv : zzV) : zzQ ((zK263 zv)) := by zzK1 zK263 zK135 (zS135 (zzF1 ((zv 0 + 1))))
lemma zS249 (zv : zzV) : zzQ ((zK249 zv)) := by zzK1 zK249 zK263 (zS263 (zzF1 (zv 0)))
lemma zA264 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK250 zv'))) :
  zzQ ((zK264 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK264 zK249 h_vl (zS249 (zzF1 ((zv 1 + 1))))
  · zzK2 zK264 zK250 h_vl (h_u (zzF2 (l) ((zv 1 + 1))) (by (try simp only []); omega))
lemma zS250 (zv : zzV) : zzQ ((zK250 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK250 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK250 zK264 (zA264 (zzF2 (zv 0) (zv 1)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS233 (zv : zzV) : zzQ ((zK233 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK233 zK249 h_vl (zS249 (zzF1 (1)))
  · zzK2 zK233 zK250 h_vl (zS250 (zzF2 (l) (1)))
lemma zS218 (zv : zzV) : zzQ ((zK218 zv)) := by zzK1 zK218 zK233 (zS233 (zzF1 (zv 0)))
lemma zS205 (zv : zzV) : zzQ ((zK205 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK205 zK127 h_vl (zS127 (fun _ => 0))
  · zzK2 zK205 zK218 h_vl (zS218 (zzF1 (l)))
lemma zS265 (zv : zzV) : zzQ ((zK265 zv)) := by zzK1 zK265 zK136 (zS136 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS251 (zv : zzV) : zzQ ((zK251 zv)) := by zzK1 zK251 zK265 (zS265 (zzF2 (zv 0) (zv 1)))
lemma zA266 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK252 zv'))) :
  zzQ ((zK266 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK266 zK251 h_vl (zS251 (zzF2 ((zv 1 + 1)) (zv 2)))
  · zzK2 zK266 zK252 h_vl (h_u (zzF3 (l) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS252 (zv : zzV) : zzQ ((zK252 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK252 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK252 zK266 (zA266 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS234 (zv : zzV) : zzQ ((zK234 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK234 zK251 h_vl (zS251 (zzF2 (1) (zv 1)))
  · zzK2 zK234 zK252 h_vl (zS252 (zzF3 (l) (1) (zv 1)))
lemma zS219 (zv : zzV) : zzQ ((zK219 zv)) := by zzK1 zK219 zK234 (zS234 (zzF2 (zv 0) (zv 1)))
lemma zS206 (zv : zzV) : zzQ ((zK206 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK206 zK128 h_vl (zS128 (zzF1 (zv 1)))
  · zzK2 zK206 zK219 h_vl (zS219 (zzF2 (l) (zv 1)))
lemma zS195 (zv : zzV) : zzQ ((zK195 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK195 zK205 h_vr (zS205 (zzF1 (zv 0)))
  · zzK2 zK195 zK206 h_vr (zS206 (zzF2 (zv 0) (r)))
lemma zS177 (zv : zzV) : zzQ ((zK177 zv)) := by zzK1 zK177 zK195 (zS195 (zzF2 (zv 0) (zv 1)))
lemma zS253 (zv : zzV) : zzQ ((zK253 zv)) := by zzK1 zK253 zK133 (zS133 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA254 (zv : zzV)
  (h_u : ∀ zv', zv' 0 <= zv 0 -> zzQ ((zK235 zv'))) :
  zzQ ((zK254 zv)) := by
  zzK1 zK254 zK235 (h_u (zzF3 (zv 0) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS235 (zv : zzV) : zzQ ((zK235 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK235 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK235 zK253 h_vl (zS253 (zzF2 (zv 1) (zv 2)))
  · zzK2 zK235 zK254 h_vl (zA254 (zzF3 (l) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS220 (zv : zzV) : zzQ ((zK220 zv)) := by zzK1 zK220 zK235 (zS235 (zzF3 (zv 0) (1) (zv 1)))
lemma zS207 (zv : zzV) : zzQ ((zK207 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK207 zK129 h_vl (zS129 (zzF1 (zv 1)))
  · zzK2 zK207 zK220 h_vl (zS220 (zzF2 (l) (zv 1)))
lemma zS196 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK196 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK196 zK207 h_vr (zS207 (zzF2 (zv 0) (zv 2)))
  · zzK2 zK196 zP208 h_vr (h_208 (zzF3 (zv 0) (r) (zv 2)) (by (try simp only []); omega))
lemma zS178 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK178 zv)) := by zzK1 zK178 zK196 (zS196 B h_208 (zzF3 (zv 0) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS165 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 0 <= B) : zzQ ((zK165 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK165 zK177 h_vr (zS177 (zzF2 (1) (zv 1)))
  · zzK2 zK165 zK178 h_vr (zS178 B h_208 (zzF3 (1) (r) (zv 1)) (by (try simp only []); omega))
lemma zS155 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 0 <= B) : zzQ ((zK155 zv)) := by zzK1 zK155 zK165 (zS165 B h_208 (zzF2 (zv 0) (zv 1)) (by (try simp only []); omega))
lemma zS197 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK197 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK197 zK177 h_vr (zS177 (zzF2 ((zv 0 + 1)) (zv 2)))
  · zzK2 zK197 zK178 h_vr (zS178 B h_208 (zzF3 ((zv 0 + 1)) (r) (zv 2)) (by (try simp only []); omega))
lemma zS179 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK179 zv)) := by zzK1 zK179 zK197 (zS197 B h_208 (zzF3 (zv 0) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zA198 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 2 <= B)
  (h_u : ∀ zv', zv' 1 < zv 1 -> zv' 2 <= B -> zzQ ((zK180 zv'))) :
  zzQ ((zK198 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK198 zK179 h_vr (zS179 B h_208 (zzF3 ((zv 0 + 1)) (zv 2) (zv 3)) (by (try simp only []); omega))
  · zzK2 zK198 zK180 h_vr (h_u (zzF4 ((zv 0 + 1)) (r) (zv 2) (zv 3)) (by (try simp only []); omega) (by (try simp only []); omega))
lemma zS180 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 2 <= B) : zzQ ((zK180 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zv 2 <= B -> zzQ ((zK180 zv)) from h_ind (zv 1) zv rfl h_B
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n h_B => ?_)
  zzK1 zK180 zK198 (zA198 B h_208 (zzF4 (zv 0) (zv 1) (zv 2) (zv 3)) (by (try simp only []); omega) (fun zv' h_le h_B' => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl h_B'))
lemma zS166 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK166 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK166 zK179 h_vr (zS179 B h_208 (zzF3 (1) (zv 1) (zv 2)) (by (try simp only []); omega))
  · zzK2 zK166 zK180 h_vr (zS180 B h_208 (zzF4 (1) (r) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS156 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK156 zv)) := by zzK1 zK156 zK166 (zS166 B h_208 (zzF3 (zv 0) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS148 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK148 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK148 zK155 h_vr (zS155 B h_208 (zzF2 (zv 1) (zv 2)) (by (try simp only []); omega))
  · zzK2 zK148 zK156 h_vr (zS156 B h_208 (zzF3 (r) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS142 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK142 zv)) := by zzK1 zK142 zK148 (zS148 B h_208 (zzF3 (zv 0) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS138 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK138 zv)) := by zzK1 zK138 zK142 (zS142 B h_208 (zzF3 (zv 0) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS134 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK134 zv)) := by zzK1 zK134 zK138 (zS138 B h_208 (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zA130 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 0 <= B) : zzQ ((zK130 zv)) := by zzK1 zK130 zK134 (zS134 B h_208 (zzF3 (1) (zv 0) (zv 1)) (by (try simp only []); omega))
lemma zS255 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK255 zv)) := by zzK1 zK255 zK134 (zS134 B h_208 (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zA256 (zv : zzV) (B : Nat) (h_B : zv 2 <= B)
  (h_u : ∀ zv', zv' 0 <= zv 0 -> zv' 2 <= B -> zzQ ((zK236 zv'))) :
  zzQ ((zK256 zv)) := by
  zzK1 zK256 zK236 (h_u (zzF4 (zv 0) ((zv 1 + 1)) (zv 2) (zv 3)) (by (try simp only []); omega) (by (try simp only []); omega))
lemma zS236 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 2 <= B) : zzQ ((zK236 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zv 2 <= B -> zzQ ((zK236 zv)) from h_ind (zv 0) zv rfl h_B
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n h_B => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK236 zK255 h_vl (zS255 B h_208 (zzF3 (zv 1) (zv 2) (zv 3)) (by (try simp only []); omega))
  · zzK2 zK236 zK256 h_vl (zA256 (zzF4 (l) (zv 1) (zv 2) (zv 3)) B (by (try simp only []); omega) (fun zv' h_le h_B' => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl h_B'))
lemma zS221 (B : Nat) (h_208 : ∀ zv', zv' 1 < B -> zzQ ((zzE zP208 zv'))) (zv : zzV) (h_B : zv 1 <= B) : zzQ ((zK221 zv)) := by zzK1 zK221 zK236 (zS236 B h_208 (zzF4 (zv 0) (1) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma step_hub_208 (zv : zzV) : zzQ ((zzE zP208 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zzE zP208 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zP208 zK130 h_vl (zA130 n (fun zv' h_lt => ih (zv' 1) h_lt zv' rfl) (zzF2 (zv 1) (zv 2)) (by (try simp only []); omega))
  · zzK2 zP208 zK221 h_vl (zS221 n (fun zv' h_lt => ih (zv' 1) h_lt zv' rfl) (zzF3 (l) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS130 (zv : zzV) :
  zzQ ((zK130 zv)) :=
  zA130 (zv 0) (fun zv' _ => step_hub_208 zv') zv (Nat.le_refl _)
lemma zS126 (zv : zzV) : zzQ ((zK126 zv)) := by zzK1 zK126 zK130 (zS130 (zzF2 (zv 0) (zv 1)))
lemma zS122 (zv : zzV) : zzQ ((zK122 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK122 zK125 h_vr (zS125 (zzF1 (zv 1)))
  · zzK2 zK122 zK126 h_vr (zS126 (zzF2 (r) (zv 1)))
lemma zS120 (zv : zzV) : zzQ ((zK120 zv)) := by zzK1 zK120 zK122 (zS122 (zzF2 (zv 0) (zv 1)))
lemma zS118 (zv : zzV) : zzQ ((zK118 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK118 zK119 h_vr (zS119 (zzF1 (zv 1)))
  · zzK2 zK118 zK120 h_vr (zS120 (zzF2 (r) (zv 1)))
lemma zS116 (zv : zzV) : zzQ ((zK116 zv)) := by zzK1 zK116 zK118 (zS118 (zzF2 (zv 0) (zv 1)))
lemma zS114 (zv : zzV) : zzQ ((zK114 zv)) := by zzK1 zK114 zK116 (zS116 (zzF2 (zv 0) (zv 1)))
lemma zS111 (zv : zzV) : zzQ ((zK111 zv)) := by zzK1 zK111 zK114 (zS114 (zzF2 (1) (zv 0)))
lemma zS108 (zv : zzV) : zzQ ((zK108 zv)) := by zzK1 zK108 zK111 (zS111 (zzF1 (zv 0)))
lemma zS106 (zv : zzV) : zzQ ((zK106 zv)) := by zzK1 zK106 zK108 (zS108 (zzF1 (zv 0)))
lemma zS104 (zv : zzV) : zzQ ((zK104 zv)) := by zzK1 zK104 zK106 (zS106 (zzF1 (zv 0)))
lemma zS117 (zv : zzV) : zzQ ((zK117 zv)) := by zzK1 zK117 zK114 (zS114 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS115 (zv : zzV) : zzQ ((zK115 zv)) := by zzK1 zK115 zK117 (zS117 (zzF2 (zv 0) (zv 1)))
lemma zS112 (zv : zzV) : zzQ ((zK112 zv)) := by zzK1 zK112 zK115 (zS115 (zzF2 (zv 0) (zv 1)))
lemma zS109 (zv : zzV) : zzQ ((zK109 zv)) := by zzK1 zK109 zK112 (zS112 (zzF2 (zv 0) (zv 1)))
lemma zA113 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK110 zv'))) :
  zzQ ((zK113 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK113 zK109 h_vl (zS109 (zzF2 ((zv 1 + 1)) (zv 2)))
  · zzK2 zK113 zK110 h_vl (h_u (zzF3 (l) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS110 (zv : zzV) : zzQ ((zK110 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK110 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK110 zK113 (zA113 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS107 (zv : zzV) : zzQ ((zK107 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK107 zK109 h_vl (zS109 (zzF2 (1) (zv 1)))
  · zzK2 zK107 zK110 h_vl (zS110 (zzF3 (l) (1) (zv 1)))
lemma zS105 (zv : zzV) : zzQ ((zK105 zv)) := by zzK1 zK105 zK107 (zS107 (zzF2 (zv 0) (zv 1)))
lemma zS103 (zv : zzV) : zzQ ((zK103 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK103 zK104 h_vl (zS104 (zzF1 (zv 1)))
  · zzK2 zK103 zK105 h_vl (zS105 (zzF2 (l) (zv 1)))
lemma zS102 (zv : zzV) : zzQ ((zK102 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK102 zK19 h_vr (zS19 (zzF1 (1)))
  · zzK2 zK102 zK103 h_vr (zS103 (zzF2 (1) (r)))
lemma zS101 (zv : zzV) : zzQ ((zK101 zv)) := by zzK1 zK101 zK102 (zS102 (zzF1 (zv 0)))
lemma zS100 (zv : zzV) : zzQ ((zK100 zv)) := by zzK1 zK100 zK101 (zS101 (zzF1 (zv 0)))
lemma zS99 (zv : zzV) : zzQ ((zK99 zv)) := by zzK1 zK99 zK100 (zS100 (zzF1 (zv 0)))
lemma zS98 (zv : zzV) : zzQ ((zK98 zv)) := by zzK1 zK98 zK99 (zS99 (zzF1 (zv 0)))
lemma zS97 (zv : zzV) : zzQ ((zK97 zv)) := by zzK1 zK97 zK98 (zS98 (zzF1 (zv 0)))
lemma zS96 (zv : zzV) : zzQ ((zK96 zv)) := by zzK1 zK96 zK97 (zS97 (zzF1 (zv 0)))
lemma zS95 (zv : zzV) : zzQ ((zK95 zv)) := by zzK1 zK95 zK96 (zS96 (zzF1 (zv 0)))
lemma zS94 (zv : zzV) : zzQ ((zK94 zv)) := by zzK1 zK94 zK95 (zS95 (zzF1 (zv 0)))
lemma zS90 (zv : zzV) : zzQ ((zK90 zv)) := by zzK1 zK90 zK94 (zS94 (zzF1 (zv 0)))
lemma zS86 (zv : zzV) : zzQ ((zK86 zv)) := by zzK1 zK86 zK90 (zS90 (zzF1 (zv 0)))
lemma zA91 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK87 zv'))) :
  zzQ ((zK91 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK91 zK86 h_vl (zS86 (zzF1 ((zv 1 + 1))))
  · zzK2 zK91 zK87 h_vl (h_u (zzF2 (l) ((zv 1 + 1))) (by (try simp only []); omega))
lemma zS87 (zv : zzV) : zzQ ((zK87 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK87 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK87 zK91 (zA91 (zzF2 (zv 0) (zv 1)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS84 (zv : zzV) : zzQ ((zK84 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK84 zK86 h_vl (zS86 (zzF1 (1)))
  · zzK2 zK84 zK87 h_vl (zS87 (zzF2 (l) (1)))
lemma zS82 (zv : zzV) : zzQ ((zK82 zv)) := by zzK1 zK82 zK84 (zS84 (zzF1 (zv 0)))
lemma zS79 (zv : zzV) : zzQ ((zK79 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK79 zK3 h_vl (zS3 (fun _ => 0))
  · zzK2 zK79 zK82 h_vl (zS82 (zzF1 (l)))
lemma zS72 (zv : zzV) : zzQ ((zK72 zv)) := by zzK1 zK72 zK79 (zS79 (zzF1 (zv 0)))
lemma zS67 (zv : zzV) : zzQ ((zK67 zv)) := by zzK1 zK67 zK72 (zS72 (zzF1 (zv 0)))
lemma zS62 (zv : zzV) : zzQ ((zK62 zv)) := by zzK1 zK62 zK67 (zS67 (zzF1 (1)))
lemma zS59 (zv : zzV) : zzQ ((zK59 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK59 zK62 h_vr (zS62 (fun _ => 0))
  · zzKB2 zK59 zK63 h_vr (zI63 (zzF1 (r)))
lemma zS56 (zv : zzV) : zzQ ((zK56 zv)) := by zzK1 zK56 zK59 (zS59 (zzF1 (zv 0)))
lemma zS75 (zv : zzV) : zzQ ((zK75 zv)) := by zzK1 zK75 zK67 (zS67 (zzF1 ((zv 0 + 1))))
lemma zS69 (zv : zzV) : zzQ ((zK69 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK69 zK75 h_vr (zS75 (zzF1 (zv 0)))
  · zzKB2 zK69 zK76 h_vr (zI76 (zzF2 (zv 0) (r)))
lemma zS64 (zv : zzV) : zzQ ((zK64 zv)) := by zzK1 zK64 zK69 (zS69 (zzF2 (1) (zv 0)))
lemma zS77 (zv : zzV) : zzQ ((zK77 zv)) := by zzK1 zK77 zK69 (zS69 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA78 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK70 zv'))) :
  zzQ ((zK78 zv)) := by
  zzK1 zK78 zK70 (h_u (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS70 (zv : zzV) : zzQ ((zK70 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK70 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK70 zK77 h_vr (zS77 (zzF2 (zv 0) (zv 2)))
  · zzK2 zK70 zK78 h_vr (zA78 (zzF3 (zv 0) (r) (zv 2)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS65 (zv : zzV) : zzQ ((zK65 zv)) := by zzK1 zK65 zK70 (zS70 (zzF3 (1) (zv 0) (zv 1)))
lemma zS60 (zv : zzV) : zzQ ((zK60 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK60 zK64 h_vr (zS64 (zzF1 (zv 1)))
  · zzK2 zK60 zK65 h_vr (zS65 (zzF2 (r) (zv 1)))
lemma zS57 (zv : zzV) : zzQ ((zK57 zv)) := by zzK1 zK57 zK60 (zS60 (zzF2 (zv 0) (zv 1)))
lemma zS54 (zv : zzV) : zzQ ((zK54 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK54 zK56 h_vr (zS56 (zzF1 (zv 1)))
  · zzK2 zK54 zK57 h_vr (zS57 (zzF2 (r) (zv 1)))
lemma zS52 (zv : zzV) : zzQ ((zK52 zv)) := by zzK1 zK52 zK54 (zS54 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS50 (zv : zzV) : zzQ ((zK50 zv)) := by zzK1 zK50 zK52 (zS52 (zzF2 (1) (zv 0)))
lemma zS48 (zv : zzV) : zzQ ((zK48 zv)) := by zzK1 zK48 zK50 (zS50 (zzF1 (zv 0)))
lemma zS46 (zv : zzV) : zzQ ((zK46 zv)) := by zzK1 zK46 zK48 (zS48 (zzF1 (zv 0)))
lemma zS43 (zv : zzV) : zzQ ((zK43 zv)) := by zzK1 zK43 zK46 (zS46 (zzF1 (zv 0)))
lemma zS38 (zv : zzV) : zzQ ((zK38 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK38 zK42 h_vr (zS42 (fun _ => 0))
  · zzK2 zK38 zK43 h_vr (zS43 (zzF1 (r)))
lemma zS34 (zv : zzV) : zzQ ((zK34 zv)) := by zzK1 zK34 zK38 (zS38 (zzF1 (zv 0)))
lemma zS71 (zv : zzV) : zzQ ((zK71 zv)) := by zzKB1 zK71 zP66 (zI66 (zzF1 ((zv 0 + 1))))
lemma zA80 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK73 zv'))) :
  zzQ ((zK80 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK80 zK47 h_vl (zS47 (fun _ => 0))
  · zzK2 zK80 zK73 h_vl (h_u (zzF1 (l)) (by (try simp only []); omega))
lemma zS73 (zv : zzV) : zzQ ((zK73 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK73 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK73 zK80 (zA80 (zzF1 (zv 0)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS92 (zv : zzV) : zzQ ((zK92 zv)) := by zzK1 zK92 zK52 (zS52 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS88 (zv : zzV) : zzQ ((zK88 zv)) := by zzK1 zK88 zK92 (zS92 (zzF2 (zv 0) (zv 1)))
lemma zA93 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK89 zv'))) :
  zzQ ((zK93 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK93 zK88 h_vl (zS88 (zzF2 ((zv 1 + 1)) (zv 2)))
  · zzK2 zK93 zK89 h_vl (h_u (zzF3 (l) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS89 (zv : zzV) : zzQ ((zK89 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK89 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK89 zK93 (zA93 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS85 (zv : zzV) : zzQ ((zK85 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK85 zK88 h_vl (zS88 (zzF2 (1) (zv 1)))
  · zzK2 zK85 zK89 h_vl (zS89 (zzF3 (l) (1) (zv 1)))
lemma zS83 (zv : zzV) : zzQ ((zK83 zv)) := by zzK1 zK83 zK85 (zS85 (zzF2 (zv 0) (zv 1)))
lemma zS81 (zv : zzV) : zzQ ((zK81 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK81 zK48 h_vl (zS48 (zzF1 (zv 1)))
  · zzK2 zK81 zK83 h_vl (zS83 (zzF2 (l) (zv 1)))
lemma zS74 (zv : zzV) : zzQ ((zK74 zv)) := by zzK1 zK74 zK81 (zS81 (zzF2 (zv 0) (zv 1)))
lemma zS170 (zv : zzV) : zzQ ((zK170 zv)) := by zzK1 zK170 zK104 (zS104 (zzF1 (zv 0)))
lemma zS160 (zv : zzV) : zzQ ((zK160 zv)) := by zzK1 zK160 zK170 (zS170 (zzF1 (zv 0)))
lemma zS151 (zv : zzV) : zzQ ((zK151 zv)) := by zzK1 zK151 zK160 (zS160 (zzF1 (zv 0)))
lemma zS145 (zv : zzV) : zzQ ((zK145 zv)) := by zzK1 zK145 zK151 (zS151 (zzF1 (zv 0)))
lemma zS186 (zv : zzV) : zzQ ((zK186 zv)) := by zzK1 zK186 zK103 (zS103 (zzF2 (zv 0) (zv 1)))
lemma zS171 (zv : zzV) : zzQ ((zK171 zv)) := by zzK1 zK171 zK186 (zS186 (zzF2 (zv 0) (zv 1)))
lemma zS161 (zv : zzV) : zzQ ((zK161 zv)) := by zzK1 zK161 zK171 (zS171 (zzF2 (1) (zv 0)))
lemma zS187 (zv : zzV) : zzQ ((zK187 zv)) := by zzK1 zK187 zK171 (zS171 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA188 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK172 zv'))) :
  zzQ ((zK188 zv)) := by
  zzK1 zK188 zK172 (h_u (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS172 (zv : zzV) : zzQ ((zK172 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK172 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK172 zK187 h_vr (zS187 (zzF2 (zv 0) (zv 2)))
  · zzK2 zK172 zK188 h_vr (zA188 (zzF3 (zv 0) (r) (zv 2)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS162 (zv : zzV) : zzQ ((zK162 zv)) := by zzK1 zK162 zK172 (zS172 (zzF3 (1) (zv 0) (zv 1)))
lemma zS152 (zv : zzV) : zzQ ((zK152 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK152 zK161 h_vr (zS161 (zzF1 (zv 1)))
  · zzK2 zK152 zK162 h_vr (zS162 (zzF2 (r) (zv 1)))
lemma zS146 (zv : zzV) : zzQ ((zK146 zv)) := by zzK1 zK146 zK152 (zS152 (zzF2 (zv 0) (zv 1)))
lemma zS317 (zv : zzV) : zzQ ((zK317 zv)) := by zzK1 zK317 zK28 (zS28 (fun _ => 0))
lemma zS309 (zv : zzV) : zzQ ((zK309 zv)) := by zzK1 zK309 zK317 (zS317 (fun _ => 0))
lemma zS310 (zv : zzV) : zzQ ((zK310 zv)) := by zzK1 zK310 zP245 (step_to_ps_245 (zzF1 ((zv 0 + 1))))
lemma zS305 (zv : zzV) : zzQ ((zK305 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK305 zK309 h_vr (zS309 (fun _ => 0))
  · zzK2 zK305 zK310 h_vr (zS310 (zzF1 (r)))
lemma zS301 (zv : zzV) : zzQ ((zK301 zv)) := by zzK1 zK301 zK305 (zS305 (zzF1 (zv 0)))
lemma zS324 (zv : zzV) : zzQ ((zK324 zv)) := by zzK1 zK324 zP271 (step_to_ps_271 (zzF2 (zv 0) ((zv 1 + 1))))
lemma zS318 (zv : zzV) : zzQ ((zK318 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK318 zK22 h_vr (zS22 (zzF1 (zv 0)))
  · zzK2 zK318 zK324 h_vr (zS324 (zzF2 (zv 0) (r)))
lemma zS311 (zv : zzV) : zzQ ((zK311 zv)) := by zzK1 zK311 zK318 (zS318 (zzF2 (1) (zv 0)))
lemma zS325 (zv : zzV) : zzQ ((zK325 zv)) := by zzK1 zK325 zK318 (zS318 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA326 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK319 zv'))) :
  zzQ ((zK326 zv)) := by
  zzK1 zK326 zK319 (h_u (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)) (by (try simp only []); omega))
lemma zS319 (zv : zzV) : zzQ ((zK319 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK319 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK319 zK325 h_vr (zS325 (zzF2 (zv 0) (zv 2)))
  · zzK2 zK319 zK326 h_vr (zA326 (zzF3 (zv 0) (r) (zv 2)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS312 (zv : zzV) : zzQ ((zK312 zv)) := by zzK1 zK312 zK319 (zS319 (zzF3 (1) (zv 0) (zv 1)))
lemma zS306 (zv : zzV) : zzQ ((zK306 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK306 zK311 h_vr (zS311 (zzF1 (zv 1)))
  · zzK2 zK306 zK312 h_vr (zS312 (zzF2 (r) (zv 1)))
lemma zS302 (zv : zzV) : zzQ ((zK302 zv)) := by zzK1 zK302 zK306 (zS306 (zzF2 (zv 0) (zv 1)))
lemma zS299 (zv : zzV) : zzQ ((zK299 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK299 zK301 h_vr (zS301 (zzF1 (zv 1)))
  · zzK2 zK299 zK302 h_vr (zS302 (zzF2 (r) (zv 1)))
lemma zS297 (zv : zzV) : zzQ ((zK297 zv)) := by zzK1 zK297 zK299 (zS299 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS295 (zv : zzV) : zzQ ((zK295 zv)) := by zzK1 zK295 zK297 (zS297 (zzF2 (1) (zv 0)))
lemma zS293 (zv : zzV) : zzQ ((zK293 zv)) := by zzK1 zK293 zK295 (zS295 (zzF1 (zv 0)))
lemma zS291 (zv : zzV) : zzQ ((zK291 zv)) := by zzK1 zK291 zK293 (zS293 (zzF1 (zv 0)))
lemma zS289 (zv : zzV) : zzQ ((zK289 zv)) := by zzK1 zK289 zK291 (zS291 (zzF1 (zv 0)))
lemma zS361 (zv : zzV) : zzQ ((zK361 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK361 zK19 h_vr (zS19 (zzF1 ((zv 0 + 1))))
  · zzK2 zK361 zK103 h_vr (zS103 (zzF2 ((zv 0 + 1)) (r)))
lemma zS359 (zv : zzV) : zzQ ((zK359 zv)) := by zzK1 zK359 zK361 (zS361 (zzF2 (zv 0) (zv 1)))
lemma zA362 (zv : zzV)
  (h_u : ∀ zv', zv' 1 < zv 1 -> zzQ ((zK360 zv'))) :
  zzQ ((zK362 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK362 zK359 h_vr (zS359 (zzF2 ((zv 0 + 1)) (zv 2)))
  · zzK2 zK362 zK360 h_vr (h_u (zzF3 ((zv 0 + 1)) (r) (zv 2)) (by (try simp only []); omega))
lemma zS360 (zv : zzV) : zzQ ((zK360 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK360 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK360 zK362 (zA362 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS358 (zv : zzV) : zzQ ((zK358 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK358 zK359 h_vr (zS359 (zzF2 (1) (zv 1)))
  · zzK2 zK358 zK360 h_vr (zS360 (zzF3 (1) (r) (zv 1)))
lemma zS357 (zv : zzV) : zzQ ((zK357 zv)) := by zzK1 zK357 zK358 (zS358 (zzF2 (zv 0) (zv 1)))
lemma zS352 (zv : zzV) : zzQ ((zK352 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK352 zK101 h_vr (zS101 (zzF1 (zv 1)))
  · zzK2 zK352 zK357 h_vr (zS357 (zzF2 (r) (zv 1)))
lemma zS345 (zv : zzV) : zzQ ((zK345 zv)) := by zzK1 zK345 zK352 (zS352 (zzF2 (zv 0) (zv 1)))
lemma zS341 (zv : zzV) : zzQ ((zK341 zv)) := by zzK1 zK341 zK345 (zS345 (zzF2 (zv 0) (zv 1)))
lemma zS337 (zv : zzV) : zzQ ((zK337 zv)) := by zzK1 zK337 zK341 (zS341 (zzF2 (1) (zv 0)))
lemma zS346 (zv : zzV) : zzQ ((zK346 zv)) := by zzK1 zK346 zK341 (zS341 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zA347 (zv : zzV)
  (h_u : ∀ zv', zv' 0 <= zv 0 -> zzQ ((zK342 zv'))) :
  zzQ ((zK347 zv)) := by
  zzK1 zK347 zK342 (h_u (zzF3 (zv 0) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS342 (zv : zzV) : zzQ ((zK342 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK342 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK342 zK346 h_vl (zS346 (zzF2 (zv 1) (zv 2)))
  · zzK2 zK342 zK347 h_vl (zA347 (zzF3 (l) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS338 (zv : zzV) : zzQ ((zK338 zv)) := by zzK1 zK338 zK342 (zS342 (zzF3 (zv 0) (1) (zv 1)))
lemma zS334 (zv : zzV) : zzQ ((zK334 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK334 zK337 h_vl (zS337 (zzF1 (zv 1)))
  · zzK2 zK334 zK338 h_vl (zS338 (zzF2 (l) (zv 1)))
lemma zS327 (zv : zzV) : zzQ ((zK327 zv)) := by zzK1 zK327 zK334 (zS334 (zzF2 (zv 0) (zv 1)))
lemma zS320 (zv : zzV) : zzQ ((zK320 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK320 zK97 h_vl (zS97 (zzF1 (zv 1)))
  · zzK2 zK320 zK327 h_vl (zS327 (zzF2 (l) (zv 1)))
lemma zS313 (zv : zzV) : zzQ ((zK313 zv)) := by zzK1 zK313 zK320 (zS320 (zzF2 (1) (zv 0)))
lemma zS307 (zv : zzV) : zzQ ((zK307 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK307 zK313 h_vr (zS313 (zzF1 (zv 1)))
  · zzKB2 zK307 zK314 h_vr (zI314 (zzF2 (r) (zv 1)))
lemma zS303 (zv : zzV) : zzQ ((zK303 zv)) := by zzK1 zK303 zK307 (zS307 (zzF2 (zv 0) (zv 1)))
lemma zS330 (zv : zzV) : zzQ ((zK330 zv)) := by zzK1 zK330 zK320 (zS320 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS322 (zv : zzV) : zzQ ((zK322 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK322 zK330 h_vr (zS330 (zzF2 (zv 0) (zv 2)))
  · zzKB2 zK322 zK331 h_vr (zI331 (zzF3 (zv 0) (r) (zv 2)))
lemma zS315 (zv : zzV) : zzQ ((zK315 zv)) := by zzK1 zK315 zK322 (zS322 (zzF3 (1) (zv 0) (zv 1)))
lemma zS332 (zv : zzV) : zzQ ((zK332 zv)) := by zzK1 zK332 zK322 (zS322 (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)))
lemma zA333 (zv : zzV)
  (h_u : ∀ zv', zv' 1 <= zv 1 -> zzQ ((zK323 zv'))) :
  zzQ ((zK333 zv)) := by
  zzK1 zK333 zK323 (h_u (zzF4 ((zv 0 + 1)) (zv 1) (zv 2) (zv 3)) (by (try simp only []); omega))
lemma zS323 (zv : zzV) : zzQ ((zK323 zv)) := by
  suffices h_ind : ∀ n zv, zv 1 = n -> zzQ ((zK323 zv)) from h_ind (zv 1) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  rcases h_vr : zv 1 with _ | r
  · zzK2 zK323 zK332 h_vr (zS332 (zzF3 (zv 0) (zv 2) (zv 3)))
  · zzK2 zK323 zK333 h_vr (zA333 (zzF4 (zv 0) (r) (zv 2) (zv 3)) (fun zv' h_le => ih (zv' 1) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS316 (zv : zzV) : zzQ ((zK316 zv)) := by zzK1 zK316 zK323 (zS323 (zzF4 (1) (zv 0) (zv 1) (zv 2)))
lemma zS308 (zv : zzV) : zzQ ((zK308 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK308 zK315 h_vr (zS315 (zzF2 (zv 1) (zv 2)))
  · zzK2 zK308 zK316 h_vr (zS316 (zzF3 (r) (zv 1) (zv 2)))
lemma zS304 (zv : zzV) : zzQ ((zK304 zv)) := by zzK1 zK304 zK308 (zS308 (zzF3 (zv 0) (zv 1) (zv 2)))
lemma zS300 (zv : zzV) : zzQ ((zK300 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK300 zK303 h_vr (zS303 (zzF2 (zv 1) (zv 2)))
  · zzK2 zK300 zK304 h_vr (zS304 (zzF3 (r) (zv 1) (zv 2)))
lemma zS298 (zv : zzV) : zzQ ((zK298 zv)) := by zzK1 zK298 zK300 (zS300 (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)))
lemma zS296 (zv : zzV) : zzQ ((zK296 zv)) := by zzK1 zK296 zK298 (zS298 (zzF3 (1) (zv 0) (zv 1)))
lemma zS294 (zv : zzV) : zzQ ((zK294 zv)) := by zzK1 zK294 zK296 (zS296 (zzF2 (zv 0) (zv 1)))
lemma zS292 (zv : zzV) : zzQ ((zK292 zv)) := by zzK1 zK292 zK294 (zS294 (zzF2 (zv 0) (zv 1)))
lemma zS290 (zv : zzV) : zzQ ((zK290 zv)) := by zzK1 zK290 zK292 (zS292 (zzF2 (zv 0) (zv 1)))
lemma zS288 (zv : zzV) : zzQ ((zK288 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · zzK2 zK288 zK289 h_vr (zS289 (zzF1 (zv 1)))
  · zzK2 zK288 zK290 h_vr (zS290 (zzF2 (r) (zv 1)))
lemma zS287 (zv : zzV) : zzQ ((zK287 zv)) := by zzK1 zK287 zK288 (zS288 (zzF2 (zv 0) (zv 1)))
lemma zS353 (zv : zzV) : zzQ ((zK353 zv)) := by zzK1 zK353 zK297 (zS297 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma zS348 (zv : zzV) : zzQ ((zK348 zv)) := by zzK1 zK348 zK353 (zS353 (zzF2 (zv 0) (zv 1)))
lemma zA354 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK349 zv'))) :
  zzQ ((zK354 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK354 zK348 h_vl (zS348 (zzF2 ((zv 1 + 1)) (zv 2)))
  · zzK2 zK354 zK349 h_vl (h_u (zzF3 (l) ((zv 1 + 1)) (zv 2)) (by (try simp only []); omega))
lemma zS349 (zv : zzV) : zzQ ((zK349 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK349 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK349 zK354 (zA354 (zzF3 (zv 0) (zv 1) (zv 2)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS343 (zv : zzV) : zzQ ((zK343 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK343 zK348 h_vl (zS348 (zzF2 (1) (zv 1)))
  · zzK2 zK343 zK349 h_vl (zS349 (zzF3 (l) (1) (zv 1)))
lemma zS339 (zv : zzV) : zzQ ((zK339 zv)) := by zzK1 zK339 zK343 (zS343 (zzF2 (zv 0) (zv 1)))
lemma zS335 (zv : zzV) : zzQ ((zK335 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK335 zK293 h_vl (zS293 (zzF1 (zv 1)))
  · zzK2 zK335 zK339 h_vl (zS339 (zzF2 (l) (zv 1)))
lemma zS328 (zv : zzV) : zzQ ((zK328 zv)) := by zzK1 zK328 zK335 (zS335 (zzF2 (zv 0) (zv 1)))
lemma zS355 (zv : zzV) : zzQ ((zK355 zv)) := by zzK1 zK355 zK298 (zS298 (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)))
lemma zS350 (zv : zzV) : zzQ ((zK350 zv)) := by zzK1 zK350 zK355 (zS355 (zzF3 (zv 0) (zv 1) (zv 2)))
lemma zA356 (zv : zzV)
  (h_u : ∀ zv', zv' 0 < zv 0 -> zzQ ((zK351 zv'))) :
  zzQ ((zK356 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK356 zK350 h_vl (zS350 (zzF3 ((zv 1 + 1)) (zv 2) (zv 3)))
  · zzK2 zK356 zK351 h_vl (h_u (zzF4 (l) ((zv 1 + 1)) (zv 2) (zv 3)) (by (try simp only []); omega))
lemma zS351 (zv : zzV) : zzQ ((zK351 zv)) := by
  suffices h_ind : ∀ n zv, zv 0 = n -> zzQ ((zK351 zv)) from h_ind (zv 0) zv rfl
  intro n
  refine Nat.strongRecOn n (fun n ih zv h_n => ?_)
  zzK1 zK351 zK356 (zA356 (zzF4 (zv 0) (zv 1) (zv 2) (zv 3)) (fun zv' h_le => ih (zv' 0) (by simp -failIfUnchanged only [] at h_le; omega) zv' rfl))
lemma zS344 (zv : zzV) : zzQ ((zK344 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK344 zK350 h_vl (zS350 (zzF3 (1) (zv 1) (zv 2)))
  · zzK2 zK344 zK351 h_vl (zS351 (zzF4 (l) (1) (zv 1) (zv 2)))
lemma zS340 (zv : zzV) : zzQ ((zK340 zv)) := by zzK1 zK340 zK344 (zS344 (zzF3 (zv 0) (zv 1) (zv 2)))
lemma zS336 (zv : zzV) : zzQ ((zK336 zv)) := by
  rcases h_vl : zv 0 with _ | l
  · zzK2 zK336 zK294 h_vl (zS294 (zzF2 (zv 1) (zv 2)))
  · zzK2 zK336 zK340 h_vl (zS340 (zzF3 (l) (zv 1) (zv 2)))
lemma zS329 (zv : zzV) : zzQ ((zK329 zv)) := by zzK1 zK329 zK336 (zS336 (zzF3 (zv 0) (zv 1) (zv 2)))
lemma step_hub_30_step1 (zv : zzV) : zzQ ((zzE pat_30_step1 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · have h_eq : zzE pat_30_step1 zv = zK33 (fun _ => 0) := by
      simp -failIfUnchanged only [evalTapePattern, pat_30_step1, zK33, evalTapeExpr]; rw [h_vr]
      zzS2
    rw [h_eq]; exact zS33 (fun _ => 0)
  · have h_eq : zzE pat_30_step1 zv = zK34 (zzF1 (r)) := by
      simp -failIfUnchanged only [evalTapePattern, pat_30_step1, zK34, evalTapeExpr]; rw [h_vr]
      zzS2
    rw [h_eq]; exact zS34 (zzF1 (r))
lemma step_hub_66 (zv : zzV) : zzQ ((zzE zP66 zv)) := by zzK1 zP66 zK71 (zS71 (zzF1 (zv 0)))
lemma step_hub_68 (zv : zzV) : zzQ ((zzE zP68 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zP68 zK73 h_vr (zS73 (zzF1 (zv 0)))
  · zzK2 zP68 zK74 h_vr (zS74 (zzF2 (zv 0) (r)))
lemma zS76 (zv : zzV) : zzQ ((zK76 zv)) := by zzK1 zK76 zP68 (step_hub_68 (zzF2 ((zv 0 + 1)) (zv 1)))
lemma step_hub_140_step1 (zv : zzV) : zzQ ((zzE pat_140_step1 zv)) := by
  rcases h_vr : zv 0 with _ | r
  · have h_eq : zzE pat_140_step1 zv = zK145 (zzF1 (zv 1)) := by
      simp -failIfUnchanged only [evalTapePattern, pat_140_step1, zK145, evalTapeExpr]; rw [h_vr]
      zzS2
    rw [h_eq]; exact zS145 (zzF1 (zv 1))
  · have h_eq : zzE pat_140_step1 zv = zK146 (zzF2 (r) (zv 1)) := by
      simp -failIfUnchanged only [evalTapePattern, pat_140_step1, zK146, evalTapeExpr]; rw [h_vr]
      zzS2
    rw [h_eq]; exact zS146 (zzF2 (r) (zv 1))
lemma step_hub_321 (zv : zzV) : zzQ ((zzE zP321 zv)) := by
  rcases h_vr : zv 1 with _ | r
  · zzK2 zP321 zK328 h_vr (zS328 (zzF2 (zv 0) (zv 2)))
  · zzK2 zP321 zK329 h_vr (zS329 (zzF3 (zv 0) (r) (zv 2)))
lemma zS331 (zv : zzV) : zzQ ((zK331 zv)) := by zzK1 zK331 zP321 (step_hub_321 (zzF3 ((zv 0 + 1)) (zv 1) (zv 2)))
lemma step_hub_A3_30 (zv : zzV) (h_cond : evalVarCond zC30 zv) : zzQ ((zzE pat_A3 zv)) := by
  simp -failIfUnchanged [zC30, evalVarCond] at h_cond
  have h_0 : zv 0 = 0 := by omega
  have h_1 : zv 1 = 0 := by omega
  have h_2 : zv 2 = 0 := by omega
  have h_3 : zv 3 = 0 := by omega
  have h_4 : zv 4 = 1 := by omega
  have h_6 : zv 6 = 0 := by omega
  have h_eq : zzE pat_A3 zv = zzE pat_30_step1 (zzF1 (zv 5)) := by
    simp -failIfUnchanged only [pat_A3, pat_30_step1, evalTapePattern, evalTapeExpr]
    rw [h_0]; rw [h_1]; rw [h_2]; rw [h_3]; rw [h_4]; rw [h_6]
    simp only [Nat.add_sub_cancel, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
  rw [h_eq]
  exact step_hub_30_step1 (zzF1 (zv 5))
lemma step_hub_A3_140 (zv : zzV) (h_cond : evalVarCond zC140 zv) : zzQ ((zzE pat_A3 zv)) := by
  simp -failIfUnchanged [zC140, evalVarCond] at h_cond
  have h_0 : zv 0 = 0 := by omega
  have h_1 : zv 1 = 0 := by omega
  have h_2 : zv 2 = 1 := by omega
  have h_4 : zv 4 = 3 := by omega
  have h_5 : zv 5 = 0 := by omega
  have h_eq : zzE pat_A3 zv = zzE pat_140_step1 (zzF2 (zv 3) (zv 6)) := by
    simp -failIfUnchanged only [pat_A3, pat_140_step1, evalTapePattern, evalTapeExpr]
    rw [h_0]; rw [h_1]; rw [h_2]; rw [h_4]; rw [h_5]
    simp only [Nat.add_sub_cancel, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
  rw [h_eq]
  exact step_hub_140_step1 (zzF2 (zv 3) (zv 6))
lemma step_hub_A3_66 (zv : zzV) (h_cond : evalVarCond zC66 zv) : zzQ ((zzE pat_A3 zv)) := by
  simp -failIfUnchanged [zC66, evalVarCond] at h_cond
  have h_0 : zv 0 = 1 := by omega
  have h_2 : zv 2 = 0 := by omega
  have h_3 : zv 3 = 0 := by omega
  have h_4 : zv 4 = 0 := by omega
  have h_5 : zv 5 = 0 := by omega
  have h_6 : zv 6 = 0 := by omega
  have h_eq : zzE pat_A3 zv = zzE zP66 (zzF1 (zv 1)) := by
    simp -failIfUnchanged only [pat_A3, zP66, evalTapePattern, evalTapeExpr]
    rw [h_0]; rw [h_2]; rw [h_3]; rw [h_4]; rw [h_5]; rw [h_6]
    simp only [Nat.add_sub_cancel, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
  rw [h_eq]
  exact step_hub_66 (zzF1 (zv 1))
lemma step_hub_A3_76 (zv : zzV) (h_cond : evalVarCond zC76 zv) : zzQ ((zzE pat_A3 zv)) := by
  simp -failIfUnchanged [zC76, evalVarCond] at h_cond
  have h_0 : zv 0 = 0 := by omega
  have h_1 : zv 1 = (zv 1 - 1) + 1 := by omega
  have h_2 : zv 2 = 0 := by omega
  have h_3 : zv 3 = 0 := by omega
  have h_4 : zv 4 = 1 := by omega
  have h_5 : zv 5 = (zv 5 - 1) + 1 := by omega
  have h_6 : zv 6 = 0 := by omega
  have h_eq : zzE pat_A3 zv = zK76 (zzF2 ((zv 1 - 1)) ((zv 5 - 1))) := by
    simp -failIfUnchanged only [pat_A3, zK76, evalTapePattern, evalTapeExpr]
    rw [h_0]; rw [h_1]; rw [h_2]; rw [h_3]; rw [h_4]; rw [h_5]; rw [h_6]
    simp only [Nat.add_sub_cancel, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
  rw [h_eq]
  exact zS76 (zzF2 ((zv 1 - 1)) ((zv 5 - 1)))
lemma step_hub_A3_331 (zv : zzV) (h_cond : evalVarCond zC331 zv) : zzQ ((zzE pat_A3 zv)) := by
  simp -failIfUnchanged [zC331, evalVarCond] at h_cond
  have h_0 : zv 0 = 0 := by omega
  have h_2 : zv 2 = 0 := by omega
  have h_3 : zv 3 = 0 := by omega
  have h_4 : zv 4 = 1 := by omega
  have h_5 : zv 5 = (zv 5 - 1) + 1 := by omega
  have h_6 : zv 6 = (zv 6 - 1) + 1 := by omega
  rcases h_1 : zv 1 with _ | v1
  · have h_eq : zzE pat_A3 zv = zK287 (zzF2 ((zv 5 - 1)) ((zv 6 - 1))) := by
      simp -failIfUnchanged only [pat_A3, zK287, evalTapePattern, evalTapeExpr]
      rw [h_0]; rw [h_1]; rw [h_2]; rw [h_3]; rw [h_4]; rw [h_5]; rw [h_6]
      simp only [Nat.add_sub_cancel, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
    rw [h_eq]
    exact zS287 (zzF2 ((zv 5 - 1)) ((zv 6 - 1)))
  · have h_eq : zzE pat_A3 zv = zK331 (zzF3 (v1) ((zv 5 - 1)) ((zv 6 - 1))) := by
      simp -failIfUnchanged only [pat_A3, zK331, evalTapePattern, evalTapeExpr]
      rw [h_0]; rw [h_1]; rw [h_2]; rw [h_3]; rw [h_4]; rw [h_5]; rw [h_6]
      simp only [Nat.add_sub_cancel, zPz, zPsl, zCal, List.singleton_append, List.nil_append, zLan, zLac, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zZcd, zDh, zDt]
    rw [h_eq]
    exact zS331 (zzF3 (v1) ((zv 5 - 1)) ((zv 6 - 1)))
lemma step_hub_A3 (zv : zzV) (h_cond : evalVarCond cond_A3 zv) : zzQ ((zzE pat_A3 zv)) := by
  simp -failIfUnchanged [cond_A3, evalVarCond] at h_cond
  rcases h_cond with h_cond | h_cond
  · exact step_hub_A3_30 zv h_cond
  rcases h_cond with h_cond | h_cond
  · exact step_hub_A3_140 zv h_cond
  rcases h_cond with h_cond | h_cond
  · exact step_hub_A3_66 zv h_cond
  rcases h_cond with h_cond | h_cond
  · exact step_hub_A3_76 zv h_cond
  exact step_hub_A3_331 zv h_cond
lemma init_reaches_ps : ∃ cfg_0, ((init []) [target_tm]⊢* cfg_0) /\ IsInPatternSet ps cfg_0 := by
  exact ⟨zzE pat_30_step1 (fun _ => 0), init_reaches_pat_30_step1, in_ps_30_step1 (fun _ => 0)⟩
theorem is_cryptid_proof (_ : True := trivial) : IsCryptid target_tm := by
  refine ⟨ps, by decide, init_reaches_ps, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, zv, rfl, h_cond⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact step_hub_A3 zv h_cond
  · nomatch h_mem
end Solution

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_cryptid : IsCryptid target_tm := Solution.is_cryptid_proof

end BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE
