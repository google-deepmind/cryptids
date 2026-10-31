/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.ElabRLE

/-!
# Machine Specification, Verified Transfers, and Family Definitions for BB6 `A6`

Core definitions and local soundness theorems for the 6-state, 2-symbol Turing machine
`1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---` (`A6`):

- `a6Target` & `a6StepCode_agrees` — Lightweight `BusyBeaver.Machine` specification (free of heavy
  `Cryptids.Machines` imports) and agreement with `a6StepCode`.
- `fastExit2` & `fastExit2_sound` — Verified 2-bit base-word (`Z, Y, X, W`) exit table.
- `transferB_batch` & `transferD_batch` — Certified quadratic-step (`4*k*b + 6*k^2 + 12*k`)
  counter transfers directly over `ListBlank (Fin 2)`.
- `stepEntry` & `stepEntry_sound` — Soundness of the accelerated Entry RLE simulator.
- `entryMilestone`, `initReturnCfg`, & `returnTarget` — Closed-form milestone and symbolic family
  specifications.
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open Turing
open BusyBeaver.WordRLE BusyBeaver.AffRLE

/-! ## Transition Table and 2-Bit Base Vocabulary -/

/-- Map `ℕ` state indices `0..5` into `Fin 6`. -/
def qOf (n : ℕ) : Fin 6 :=
  ⟨n % 6, Nat.mod_lt _ (by decide)⟩

/-- Pure `ℕ`-indexed symbol transition function for `A6`. -/
def a6StepCode (q : ℕ) (a : Fin 2) : Option (Fin 2 × Bool × ℕ) :=
  match q, a.val with
  | 0, 0 => some (1, true, 1)  | 0, 1 => some (0, false, 5)
  | 1, 0 => some (1, true, 2)  | 1, 1 => some (0, true, 0)
  | 2, 0 => some (1, false, 3) | 2, 1 => some (0, true, 1)
  | 3, 0 => some (0, false, 4) | 3, 1 => some (0, false, 2)
  | 4, 0 => some (0, false, 0) | 4, 1 => some (0, false, 2)
  | 5, 0 => some (0, false, 1) | _, _ => none

/-- Lightweight `BusyBeaver.Machine` representation of `A6`
(`1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`). -/
def a6Target : Machine (Fin 2) (Fin 6) := fun q a ↦
  match a6StepCode q.val a with
  | some (b, dir', q') =>
    some (some (qOf q'), Stmt.write b (if dir' then Dir.right else Dir.left))
  | none => none

/-- `a6StepCode` agrees everywhere with `a6Target`. -/
theorem a6StepCode_agrees : StepCodeAgrees a6Target qOf a6StepCode := by
  intro q a b dir' q' h
  match q with
  | 0 => simp [a6Target, qOf, h]
  | 1 => simp [a6Target, qOf, h]
  | 2 => simp [a6Target, qOf, h]
  | 3 => simp [a6Target, qOf, h]
  | 4 => simp [a6Target, qOf, h]
  | 5 => simp [a6Target, qOf, h]
  | q + 6 => simp [a6StepCode] at h

/-- Two-bit spatial base words: `0 ↦ [0, 0]` (`Z`), `1 ↦ [0, 1]` (`Y`), `2 ↦ [1, 0]` (`X`),
`3 ↦ [1, 1]` (`W`). -/
def baseWord : ℕ → List (Fin 2)
  | 0 => [0, 0]
  | 1 => [0, 1]
  | 2 => [1, 0]
  | 3 => [1, 1]
  | _ => []

/-- Base word `0` (`[0, 0]`) consists solely of blank symbols. -/
theorem baseWord_zero_blank : ∀ x ∈ baseWord 0, x = default := by
  decide

/-- Fast 2-bit base-word exit table `(q, dir, sym) ↦ (sym', q', dir', dt)`. -/
@[inline]
def fastExit2 (q : ℕ) (dir : Bool) (sym : ℕ) : Option (ℕ × ℕ × Bool × ℕ) :=
  if dir then
    match q, sym with
    | 0, 0 => some (3, 2, true, 2)  | 0, 1 => some (2, 0, true, 2)
    | 0, 2 => some (0, 5, false, 1) | 0, 3 => some (1, 5, false, 1)
    | 1, 0 => some (1, 2, false, 3) | 1, 1 => some (2, 1, true, 2)
    | 1, 2 => some (1, 1, true, 2)  | 1, 3 => some (0, 1, false, 3)
    | 2, 0 => some (2, 3, false, 1) | 2, 1 => some (3, 3, false, 1)
    | 2, 2 => some (1, 2, true, 2)  | 2, 3 => some (0, 0, true, 2)
    | 3, 0 => some (0, 4, false, 1) | 3, 1 => some (1, 4, false, 1)
    | 3, 2 => some (0, 2, false, 1) | 3, 3 => some (1, 2, false, 1)
    | 4, 0 => some (0, 0, false, 1) | 4, 1 => some (1, 0, false, 1)
    | 4, 2 => some (0, 2, false, 1) | 4, 3 => some (1, 2, false, 1)
    | 5, 0 => some (0, 1, false, 1) | 5, 1 => some (1, 1, false, 1)
    | _, _ => none
  else
    match q, sym with
    | 0, 0 => some (1, 1, true, 1)  | 0, 1 => some (0, 1, false, 2)
    | 0, 2 => some (3, 1, true, 1)  | 0, 3 => none
    | 1, 0 => some (1, 2, true, 1)  | 1, 1 => some (0, 0, true, 1)
    | 1, 2 => some (3, 2, true, 1)  | 1, 3 => some (2, 0, true, 1)
    | 2, 0 => some (1, 4, false, 2) | 2, 1 => some (0, 1, true, 1)
    | 2, 2 => some (1, 2, false, 2) | 2, 3 => some (2, 1, true, 1)
    | 3, 0 => some (0, 0, false, 2) | 3, 1 => some (2, 3, false, 2)
    | 3, 2 => some (0, 2, false, 2) | 3, 3 => some (1, 2, true, 3)
    | 4, 0 => some (3, 2, true, 3)  | 4, 1 => some (2, 3, false, 2)
    | 4, 2 => some (0, 5, false, 2) | 4, 3 => some (1, 2, true, 3)
    | 5, 0 => some (1, 2, false, 4) | 5, 1 => none
    | 5, 2 => some (1, 1, true, 3)  | _, _ => none

private def checkFastExit2One (q : ℕ) (dir : Bool) (s : ℕ) : Bool :=
  match fastExit2 q dir s with
  | none => true
  | some (s', q', dir', dt) =>
    runWordExit a6StepCode 10 (baseWord s) q dir == some (baseWord s', q', dir', dt)

private theorem checkFastExit2_all :
    ((List.range 6).all fun q ↦
      [false, true].all fun dir ↦
        (List.range 4).all fun s ↦ checkFastExit2One q dir s) = true := by
  decide

/-- Soundness of `fastExit2` for every `(q, dir, s)` entry. -/
theorem fastExit2_sound : BaseExitSound a6Target qOf baseWord fastExit2 := by
  intro q dir s s' q' dir' dt hfe
  have hq : q < 6 := by
    match q with
    | 0 | 1 | 2 | 3 | 4 | 5 => omega
    | d + 6 =>
      unfold fastExit2 at hfe
      cases dir <;> contradiction
  have hs : s < 4 := by
    match s with
    | 0 | 1 | 2 | 3 => omega
    | d + 4 =>
      unfold fastExit2 at hfe
      match q with
      | 0 | 1 | 2 | 3 | 4 | 5 => cases dir <;> contradiction
      | q' + 6 => cases dir <;> contradiction
  have h1 := (List.all_eq_true.mp checkFastExit2_all) q (List.mem_range.mpr hq)
  have h2 := (List.all_eq_true.mp h1) dir (by cases dir <;> simp)
  have h3 := (List.all_eq_true.mp h2) s (List.mem_range.mpr hs)
  simp only [checkFastExit2One, hfe] at h3
  exact runWordExit_sound a6StepCode_agrees (eq_of_beq h3)

/-! ## Quadratic Counter Transfers (`transferD_batch` and `transferB_batch`) -/

private theorem batch_cost_succ (k b : ℕ) :
    (4 * b + 18) + (4 * k * (b + 3) + 6 * k * k + 12 * k) =
      4 * (k + 1) * b + 6 * (k + 1) * (k + 1) + 12 * (k + 1) := by
  have h1 : 4 * k * (b + 3) = 4 * k * b + 12 * k := by
    rw [Nat.mul_add]
    omega
  have h2 : 4 * (k + 1) * b = 4 * k * b + 4 * b := by
    rw [Nat.mul_add 4 k 1, Nat.mul_one, Nat.add_mul]
  have h3 : 6 * (k + 1) * (k + 1) = 6 * k * k + 12 * k + 6 := by
    rw [Nat.mul_add 6 k 1, Nat.mul_one, Nat.mul_add, Nat.mul_one, Nat.add_mul]
    omega
  omega

private theorem transferD_one (b : ℕ) (lTail : ListBlank (Fin 2)) :
    ReachesIn a6Target (4 * b + 18)
      (Cfg.headLeft 3
        (ListBlank.append [0, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2) lTail))
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default))
      (Cfg.headLeft 3
        (ListBlank.append [0, 0] lTail)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 3)) default)) := by
  have hOpen : WordExit a6Target qOf [0, 1, 0, 1, 0, 0] 3 false [0, 0, 0, 1, 0, 1] 2 true 13 :=
    runWordExit_sound a6StepCode_agrees (fuel := 20) (by decide)
  have h1 := hOpen lTail (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default)
  simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true, dirCfg, qOf] at h1
  have h1' : ReachesIn a6Target 13
      (Cfg.headLeft 3
        (ListBlank.append [0, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2) lTail))
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default))
      (Cfg.headRight 2
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2) (ListBlank.append [0, 0] lTail))
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default)) := by
    simpa [list_pow_succ, list_pow_zero, ListBlank.append_assoc] using h1
  have hexC : WordExit a6Target qOf [1, 0] 2 true [0, 1] 2 true 2 :=
    runWordExit_sound a6StepCode_agrees (fuel := 10) (by decide)
  have h2 := sweepWord_sound hexC b
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2) (ListBlank.append [0, 0] lTail)) default
  simp only [placeSide, ↓reduceIte, Bool.not_true, Bool.false_eq_true, reverse_pow,
    dirCfg, qOf] at h2
  have h2' : ReachesIn a6Target (2 * b)
      (Cfg.headRight 2
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2) (ListBlank.append [0, 0] lTail))
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default))
      (Cfg.headRight 2
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0, 0] lTail))
        default) := by
    simpa [list_pow_add, ListBlank.append_assoc] using h2
  have h3 : ReachesIn a6Target 1
      (Cfg.headRight 2
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0, 0] lTail))
        default)
      (Cfg.headLeft 3
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0, 0] lTail))
        (ListBlank.append [1, 0] default)) := by
    have hs := step_headRight_default_left (M := a6Target) (q := (2 : Fin 6)) (q' := 3) (b := 1)
      rfl (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0, 0] lTail))
    have hr10 : ListBlank.cons (1 : Fin 2) default = ListBlank.append [1, 0] default := by
      simp
    rw [hr10] at hs
    exact ReachesIn.single hs
  have hexD : WordExit a6Target qOf [0, 1] 3 false [1, 0] 3 false 2 :=
    runWordExit_sound a6StepCode_agrees (fuel := 10) (by decide)
  have h4 := sweepWord_sound hexD (b + 2)
    (ListBlank.append [0, 0] lTail) (ListBlank.append [1, 0] default)
  simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false, reverse_pow,
    dirCfg, qOf] at h4
  have h4' : ReachesIn a6Target (2 * (b + 2))
      (Cfg.headLeft 3
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0, 0] lTail))
        (ListBlank.append [1, 0] default))
      (Cfg.headLeft 3
        (ListBlank.append [0, 0] lTail)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 3)) default)) := by
    simpa [list_pow_succ', ListBlank.append_assoc] using h4
  have htot := ((h1'.trans h2').trans h3).trans h4'
  have hdt : 13 + 2 * b + 1 + 2 * (b + 2) = 4 * b + 18 := by omega
  rwa [hdt] at htot

/-- `k`-batch state-`D` quadratic transfer over arbitrary left tail `lTail`. -/
theorem transferD_batch (k b : ℕ) (lTail : ListBlank (Fin 2)) :
    ReachesIn a6Target (4 * k * b + 6 * k * k + 12 * k)
      (Cfg.headLeft 3
        (ListBlank.append [0, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * k)) lTail))
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) default))
      (Cfg.headLeft 3
        (ListBlank.append [0, 0] lTail)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 3 * k)) default)) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have hpow : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [hpow, list_pow_add, ListBlank.append_assoc]
    have h1 := transferD_one b (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * k)) lTail)
    have h2 := ih (b + 3)
    have htr := h1.trans h2
    have hcnt : b + 3 + 3 * k = b + 3 * (k + 1) := by omega
    rw [batch_cost_succ, hcnt] at htr
    exact htr

private theorem transferB_one (b : ℕ) (lTail : ListBlank (Fin 2)) :
    ReachesIn a6Target (4 * b + 18)
      (Cfg.headRight 1
        (ListBlank.append [0, 1, 0, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2) lTail))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))
      (Cfg.headRight 1
        (ListBlank.append [0, 1, 0, 0] lTail)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 3)) default)) := by
  set midL := ListBlank.append [0, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2) lTail)
  have hexB : WordExit a6Target qOf [0, 1] 1 true [1, 0] 1 true 2 :=
    runWordExit_sound a6StepCode_agrees (fuel := 10) (by decide)
  have h1 := sweepWord_sound hexB b (ListBlank.append [0, 1] midL) default
  simp only [placeSide, ↓reduceIte, Bool.not_true, Bool.false_eq_true, reverse_pow,
    dirCfg, qOf] at h1
  have h1' : ReachesIn a6Target (2 * b)
      (Cfg.headRight 1
        (ListBlank.append [0, 1, 0, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2) lTail))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))
      (Cfg.headRight 1
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) midL)
        default) := by
    simpa [midL, list_pow_succ', ListBlank.append_assoc] using h1
  have hexTurn : WordExit a6Target qOf [0, 0] 1 true [0, 1] 2 false 3 :=
    runWordExit_sound a6StepCode_agrees (fuel := 10) (by decide)
  have h2 := hexTurn (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) midL) default
  simp only [placeSide, ↓reduceIte, Bool.not_false, dirCfg, qOf] at h2
  have hdef00 : ListBlank.append ([0, 0] : List (Fin 2)) default = default :=
    lb_blank_word [0, 0] baseWord_zero_blank
  rw [hdef00] at h2
  have hexCL : WordExit a6Target qOf [1, 0] 2 false [0, 1] 2 false 2 :=
    runWordExit_sound a6StepCode_agrees (fuel := 10) (by decide)
  have h3 := sweepWord_sound hexCL (b + 1) midL (ListBlank.append [0, 1] default)
  simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false, reverse_pow,
    dirCfg, qOf] at h3
  have h3' : ReachesIn a6Target (2 * (b + 1))
      (Cfg.headLeft 2
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) midL)
        (ListBlank.append [0, 1] default))
      (Cfg.headLeft 2 midL
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default)) := by
    simpa [list_pow_succ', ListBlank.append_assoc] using h3
  set r₂ := ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default
  have hexL5 : WordExit a6Target qOf [0, 1, 0, 0, 0] 2 false [0, 0, 0, 0, 1] 1 false 5 :=
    runWordExit_sound a6StepCode_agrees (fuel := 15) (by decide)
  have h4 := hexL5 (ListBlank.cons 1 lTail) r₂
  simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false, dirCfg, qOf] at h4
  have h4' : ReachesIn a6Target 5
      (Cfg.headLeft 2 midL r₂)
      (Cfg.headLeft 1 (ListBlank.cons 1 lTail) (ListBlank.append [0, 0, 0, 0, 1] r₂)) := by
    simpa [midL, list_pow_succ, list_pow_zero, ListBlank.append_assoc] using h4
  have h5 : ReachesIn a6Target 1
      (Cfg.headLeft 1 (ListBlank.cons 1 lTail) (ListBlank.append [0, 0, 0, 0, 1] r₂))
      (Cfg.headRight 0 (ListBlank.cons 0 lTail)
        (ListBlank.append [0, 0, 0] (ListBlank.append [0, 1] r₂))) := by
    have hs := step_headLeft_right (M := a6Target) (q := (1 : Fin 6)) (q' := 0) (a := 1) (b := 0)
      rfl lTail (ListBlank.append [0, 0, 0, 0, 1] r₂)
    simpa [ListBlank.append_assoc] using ReachesIn.single hs
  have hexR7 : WordExit a6Target qOf [0, 0, 0] 0 true [0, 1, 0] 1 true 7 :=
    runWordExit_sound a6StepCode_agrees (fuel := 15) (by decide)
  have h6 := hexR7 (ListBlank.cons 0 lTail) (ListBlank.append [0, 1] r₂)
  simp only [placeSide, ↓reduceIte, Bool.not_true, Bool.false_eq_true, dirCfg, qOf] at h6
  have h6' : ReachesIn a6Target 7
      (Cfg.headRight 0 (ListBlank.cons 0 lTail)
        (ListBlank.append [0, 0, 0] (ListBlank.append [0, 1] r₂)))
      (Cfg.headRight 1 (ListBlank.append [0, 1, 0, 0] lTail)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 3)) default)) := by
    simpa [r₂, list_pow_succ, ListBlank.append_assoc] using h6
  have htot := ((((h1'.trans h2).trans h3').trans h4').trans h5).trans h6'
  have hdt : 2 * b + 3 + 2 * (b + 1) + 5 + 1 + 7 = 4 * b + 18 := by omega
  rwa [hdt] at htot

/-- `k`-batch state-`B` quadratic transfer over arbitrary left tail `lTail`. -/
theorem transferB_batch (k b : ℕ) (lTail : ListBlank (Fin 2)) :
    ReachesIn a6Target (4 * k * b + 6 * k * k + 12 * k)
      (Cfg.headRight 1
        (ListBlank.append [0, 1, 0, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * k)) lTail))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))
      (Cfg.headRight 1
        (ListBlank.append [0, 1, 0, 0] lTail)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 3 * k)) default)) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have hpow : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [hpow, list_pow_add, ListBlank.append_assoc]
    have h1 := transferB_one b (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * k)) lTail)
    have h2 := ih (b + 3)
    have htr := h1.trans h2
    have hcnt : b + 3 + 3 * k = b + 3 * (k + 1) := by omega
    rw [batch_cost_succ, hcnt] at htr
    exact htr

/-! ## Accelerated Entry RLE Simulator (`stepNormal`, `stepEntry`) and Soundness -/

/-- Pop a single word copy from `stk`, popping `(0, [])` from `[]` and failing if `tc = 0`. -/
@[inline]
def popOne : List Run → Option (ℕ × List Run)
  | [] => some (0, [])
  | ⟨ts, tc⟩ :: rest =>
    if Nat.beq tc 0 then none
    else if Nat.beq tc 1 then some (ts, rest)
    else withNat (tc - 1) fun rem ↦ some (ts, Run.mk ts rem :: rest)

/-- Return the top symbol index of `stk` (`0` for an empty stack). -/
@[inline]
def topRunSym : List Run → ℕ
  | [] => 0
  | top :: _ => top.sym

private theorem popOne_sound {stk stk' : List Run} {s : ℕ}
    (hp : popOne stk = some (s, stk')) (side : Bool) :
    s = topRunSym stk ∧
      evalSide side baseWord stk =
        if side then ListBlank.append (baseWord s) (evalSide true baseWord stk')
        else ListBlank.append (baseWord s).reverse (evalSide false baseWord stk') := by
  have hzRev : ∀ x ∈ (baseWord 0).reverse, x = default :=
    fun x hx ↦ baseWord_zero_blank x (List.mem_reverse.mp hx)
  rcases stk with _ | ⟨⟨ts, tc⟩, rest⟩
  · simp only [popOne, Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    cases side <;>
      simp [evalSide, lb_blank_word _ baseWord_zero_blank, lb_blank_word _ hzRev]
  · simp only [popOne] at hp
    by_cases h0 : Nat.beq tc 0 = true
    · simp [h0] at hp
    · have hn0 := Bool.eq_false_iff.mpr h0
      rw [hn0] at hp
      have hpos : 1 ≤ tc := by
        have hne : tc ≠ 0 := fun h ↦ h0 (by rw [h]; rfl)
        omega
      by_cases h1 : Nat.beq tc 1 = true
      · simp only [Bool.false_eq_true, ↓reduceIte, h1, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        have htc1 : tc = 1 := Nat.eq_of_beq_eq_true h1
        subst htc1
        refine ⟨rfl, ?_⟩
        cases side <;> simp [evalSide]
      · have hn1 := Bool.eq_false_iff.mpr h1
        simp only [Bool.false_eq_true, ↓reduceIte, hn1, withNat_eq, Option.some.injEq,
          Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        have htc : tc = 1 + (tc - 1) := by omega
        refine ⟨rfl, ?_⟩
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, evalSide]
          conv_lhs => rw [htc, list_pow_add, list_pow_one, ListBlank.append_assoc]
        · simp only [↓reduceIte, evalSide]
          conv_lhs => rw [htc, list_pow_add, list_pow_one, ListBlank.append_assoc]

/-- Early-stop guard when sweeping `Y^b` rightwards in state `B` at a transfer boundary. -/
@[inline]
def isStopEarly (q q' : ℕ) (dir' : Bool) (l r : List Run) : Bool :=
  if Nat.beq q' q && dir' && Nat.beq q 1 && Nat.beq (topRunSym r) 1 then
    match r, l with
    | [_], ⟨0, 1⟩ :: ⟨2, aCnt⟩ :: _ => Nat.ble 2 aCnt
    | _, _ => false
  else false

/-- Non-transfer RLE step (homogeneous sweep or single-word exit). -/
def stepNormal (q : ℕ) (dir : Bool) (l r : List Run) : Option (ℕ × EntryCfg) :=
  if dir then
    let sym := topRunSym r
    match fastExit2 q true sym with
    | none => none
    | some (sym', q', dir', exDt) =>
      if Nat.beq q' q && dir' && !isStopEarly q q' dir' l r then
        match r with
        | [] => none
        | ⟨_, tc⟩ :: rest =>
          withNat (exDt * tc) fun dt ↦ some (dt, EntryCfg.mk q' true (pushLit sym' tc l) rest)
      else
        match popOne r with
        | none => none
        | some (_, r') =>
          if dir' then some (exDt, EntryCfg.mk q' true (pushLit sym' 1 l) r')
          else some (exDt, EntryCfg.mk q' false l (pushLit sym' 1 r'))
  else
    let sym := topRunSym l
    match fastExit2 q false sym with
    | none => none
    | some (sym', q', dir', exDt) =>
      if Nat.beq q' q && !dir' then
        match l with
        | [] => none
        | ⟨_, tc⟩ :: rest =>
          withNat (exDt * tc) fun dt ↦ some (dt, EntryCfg.mk q' false rest (pushLit sym' tc r))
      else
        match popOne l with
        | none => none
        | some (_, l') =>
          if dir' then some (exDt, EntryCfg.mk q' true (pushLit sym' 1 l') r)
          else some (exDt, EntryCfg.mk q' false l' (pushLit sym' 1 r))

/-- Soundness of `stepNormal`. -/
theorem stepNormal_sound : StepFnSound a6Target qOf baseWord stepNormal := by
  intro q dir l r dt c' hst
  unfold stepNormal at hst
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst
    rcases hfe : fastExit2 q false (topRunSym l) with _ | ⟨sym', q', dir', exDt⟩
    · rw [hfe] at hst
      simp at hst
    · rw [hfe] at hst
      have hex := fastExit2_sound q false (topRunSym l) sym' q' dir' exDt hfe
      by_cases hsw : (Nat.beq q' q && !dir') = true
      · simp only [hsw, ↓reduceIte] at hst
        rcases l with _ | ⟨⟨ts, tc⟩, rest⟩
        · simp at hst
        · simp only [withNat_eq, Option.some.injEq, Prod.mk.injEq] at hst
          rcases hst with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsw
          have hqq : q' = q := Nat.eq_of_beq_eq_true hsw.1
          have hdd : dir' = false := hsw.2
          subst hqq; subst hdd
          have hrun := sweepWord_sound hex tc (evalSide false baseWord rest)
            (evalSide true baseWord r)
          simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false, reverse_pow] at hrun
          simpa [evalEntryCfg, evalSide, topRunSym,
            evalSide_pushLit baseWord_zero_blank] using hrun
      · have hnsw := Bool.eq_false_iff.mpr hsw
        simp only [hnsw, Bool.false_eq_true, ↓reduceIte] at hst
        rcases hpop : popOne l with _ | ⟨ps, l'⟩
        · simp [hpop] at hst
        · rw [hpop] at hst
          have ⟨hps, hlEq⟩ := popOne_sound hpop false
          simp only [Bool.false_eq_true, ↓reduceIte] at hlEq
          have hrun := hex (evalSide false baseWord l') (evalSide true baseWord r)
          cases dir'
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
            rcases hst with ⟨rfl, rfl⟩
            simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hrun
            simpa [evalEntryCfg, hlEq, hps,
              evalSide_pushLit baseWord_zero_blank] using hrun
          · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
            rcases hst with ⟨rfl, rfl⟩
            simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hrun
            simpa [evalEntryCfg, hlEq, hps,
              evalSide_pushLit baseWord_zero_blank] using hrun
  · simp only [↓reduceIte] at hst
    rcases hfe : fastExit2 q true (topRunSym r) with _ | ⟨sym', q', dir', exDt⟩
    · rw [hfe] at hst
      simp at hst
    · rw [hfe] at hst
      have hex := fastExit2_sound q true (topRunSym r) sym' q' dir' exDt hfe
      by_cases hsw : (Nat.beq q' q && dir' && !isStopEarly q q' dir' l r) = true
      · simp only [hsw, ↓reduceIte] at hst
        rcases r with _ | ⟨⟨ts, tc⟩, rest⟩
        · simp at hst
        · simp only [withNat_eq, Option.some.injEq, Prod.mk.injEq] at hst
          rcases hst with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true] at hsw
          have hqq : q' = q := Nat.eq_of_beq_eq_true hsw.1.1
          have hdd : dir' = true := hsw.1.2
          subst hqq; subst hdd
          have hrun := sweepWord_sound hex tc (evalSide false baseWord l)
            (evalSide true baseWord rest)
          simp only [placeSide, ↓reduceIte, Bool.not_true, Bool.false_eq_true, reverse_pow] at hrun
          simpa [evalEntryCfg, evalSide, topRunSym,
            evalSide_pushLit baseWord_zero_blank] using hrun
      · have hnsw := Bool.eq_false_iff.mpr hsw
        simp only [hnsw, Bool.false_eq_true, ↓reduceIte] at hst
        rcases hpop : popOne r with _ | ⟨ps, r'⟩
        · simp [hpop] at hst
        · rw [hpop] at hst
          have ⟨hps, hrEq⟩ := popOne_sound hpop true
          simp only [↓reduceIte] at hrEq
          have hrun := hex (evalSide false baseWord l) (evalSide true baseWord r')
          cases dir'
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
            rcases hst with ⟨rfl, rfl⟩
            simp only [placeSide, ↓reduceIte, Bool.not_false] at hrun
            simpa [evalEntryCfg, hrEq, hps,
              evalSide_pushLit baseWord_zero_blank] using hrun
          · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
            rcases hst with ⟨rfl, rfl⟩
            simp only [placeSide, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hrun
            simpa [evalEntryCfg, hrEq, hps,
              evalSide_pushLit baseWord_zero_blank] using hrun

/-- Extract optional right-side count `b` for a transfer (`[] ↦ 0`, `[⟨w, b⟩] ↦ b`). -/
@[inline]
def transferRightCount (expSym : ℕ) : List Run → Option ℕ
  | [] => some 0
  | [⟨s, b⟩] => if Nat.beq s expSym then some b else none
  | _ => none

private theorem transferRightCount_eval {expSym : ℕ} {r : List Run} {b : ℕ}
    (h : transferRightCount expSym r = some b) :
    evalSide true baseWord r = ListBlank.append (baseWord expSym ^ b) default := by
  rcases r with _ | ⟨⟨s, c⟩, _ | _⟩
  · simp only [transferRightCount, Option.some.injEq] at h
    subst h
    rfl
  · simp only [transferRightCount] at h
    by_cases hs : Nat.beq s expSym = true
    · simp only [hs, ↓reduceIte, Option.some.injEq] at h
      have heq := Nat.eq_of_beq_eq_true hs
      subst heq; subst h
      rfl
    · have hns := Bool.eq_false_iff.mpr hs
      simp [hns] at h
  · simp [transferRightCount] at h

/-- Full accelerated Entry transition function combining `transferD`, `transferB`, and
`stepNormal`. -/
def stepEntry (q : ℕ) (dir : Bool) (l r : List Run) : Option (ℕ × EntryCfg) :=
  if !dir && Nat.beq q 3 then
    match l with
    | ⟨s0, c0⟩ :: ⟨s1, a⟩ :: tail =>
      let zOk := match tail with | [] => true | ⟨zSym, _⟩ :: _ => Nat.beq zSym 0 || Nat.beq zSym 2
      if Nat.beq s0 0 && Nat.beq c0 1 && Nat.beq s1 1 && Nat.ble 2 a && zOk then
        match transferRightCount 2 r with
        | some b =>
          let k := a / 2
          let rem := a - 2 * k
          let lBase := if Nat.beq rem 0 then tail else withNat rem fun rm ↦ Run.mk 1 rm :: tail
          withNat (b + 3 * k) fun rb ↦
          withNat (4 * k * b + 6 * k * k + 12 * k) fun dt ↦
            some (dt, EntryCfg.mk 3 false (pushLit 0 1 lBase) [Run.mk 2 rb])
        | none => stepNormal 3 false (Run.mk s0 c0 :: Run.mk s1 a :: tail) r
      else stepNormal 3 false (Run.mk s0 c0 :: Run.mk s1 a :: tail) r
    | l' => stepNormal 3 false l' r
  else if dir && Nat.beq q 1 then
    match l with
    | ⟨s0, c0⟩ :: ⟨s1, c1⟩ :: ⟨s2, a⟩ :: tail =>
      let zOk := match tail with | [] => true | ⟨zSym, _⟩ :: _ => Nat.beq zSym 0
      if Nat.beq s0 2 && Nat.beq c0 1 && Nat.beq s1 0 && Nat.beq c1 1 && Nat.beq s2 2 &&
          Nat.ble 2 a && zOk then
        match transferRightCount 1 r with
        | some b =>
          let k := a / 2
          let rem := a - 2 * k
          let lBase := if Nat.beq rem 0 then tail else withNat rem fun rm ↦ Run.mk 2 rm :: tail
          withNat (b + 3 * k) fun rb ↦
          withNat (4 * k * b + 6 * k * k + 12 * k) fun dt ↦
            some (dt, EntryCfg.mk 1 true (pushLit 2 1 (pushLit 0 1 lBase)) [Run.mk 1 rb])
        | none => stepNormal 1 true (Run.mk s0 c0 :: Run.mk s1 c1 :: Run.mk s2 a :: tail) r
      else stepNormal 1 true (Run.mk s0 c0 :: Run.mk s1 c1 :: Run.mk s2 a :: tail) r
    | l' => stepNormal 1 true l' r
  else stepNormal q dir l r

/-- Soundness of `stepEntry`. -/
theorem stepEntry_sound : StepFnSound a6Target qOf baseWord stepEntry := by
  intro q dir l r dt c' hst
  unfold stepEntry at hst
  by_cases hcD : (!dir && Nat.beq q 3) = true
  · simp only [hcD, ↓reduceIte] at hst
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcD
    have hd0 : dir = false := hcD.1
    have hq3 : q = 3 := Nat.eq_of_beq_eq_true hcD.2
    subst hd0; subst hq3
    rcases l with _ | ⟨⟨s0, c0⟩, _ | ⟨⟨s1, a⟩, tail⟩⟩
    · exact stepNormal_sound 3 false [] r dt c' hst
    · exact stepNormal_sound 3 false [⟨s0, c0⟩] r dt c' hst
    · simp only at hst
      set zOk := match tail with | [] => true | ⟨zSym, _⟩ :: _ => Nat.beq zSym 0 || Nat.beq zSym 2
      by_cases hcond : (Nat.beq s0 0 && Nat.beq c0 1 && Nat.beq s1 1 && Nat.ble 2 a && zOk) = true
      · simp only [hcond, ↓reduceIte] at hst
        simp only [Bool.and_eq_true] at hcond
        have hs0 : s0 = 0 := Nat.eq_of_beq_eq_true hcond.1.1.1.1
        have hc0 : c0 = 1 := Nat.eq_of_beq_eq_true hcond.1.1.1.2
        have hs1 : s1 = 1 := Nat.eq_of_beq_eq_true hcond.1.1.2
        have ha2 : 2 ≤ a := Nat.le_of_ble_eq_true hcond.1.2
        subst hs0; subst hc0; subst hs1
        rcases htr : transferRightCount 2 r with _ | b
        · rw [htr] at hst
          exact stepNormal_sound 3 false _ r dt c' hst
        · rw [htr] at hst
          simp only [withNat_eq, Option.some.injEq, Prod.mk.injEq] at hst
          rcases hst with ⟨rfl, rfl⟩
          set k := a / 2
          set rem := a - 2 * k
          set lBase := if Nat.beq rem 0 then tail else Run.mk 1 rem :: tail
          have hlBase : evalSide false baseWord lBase =
              ListBlank.append (([1, 0] : List (Fin 2)) ^ rem)
                (evalSide false baseWord tail) := by
            dsimp only [lBase]
            by_cases hr0 : Nat.beq rem 0 = true
            · have h0 := Nat.eq_of_beq_eq_true hr0
              simp [h0]
            · have hnr0 := Bool.eq_false_iff.mpr hr0
              simp [hnr0, evalSide, baseWord]
          have haSplit : a = 2 * k + rem := by omega
          have hrun := transferD_batch k b (evalSide false baseWord lBase)
          have hrEq := transferRightCount_eval htr
          simpa [evalEntryCfg, dirCfg, qOf, evalSide, baseWord, hrEq,
            evalSide_pushLit baseWord_zero_blank, hlBase, haSplit, list_pow_add,
            ListBlank.append_assoc] using hrun
      · have hncond := Bool.eq_false_iff.mpr hcond
        rw [hncond] at hst
        exact stepNormal_sound 3 false _ r dt c' hst
  · have hncD := Bool.eq_false_iff.mpr hcD
    simp only [hncD, Bool.false_eq_true, ↓reduceIte] at hst
    by_cases hcB : (dir && Nat.beq q 1) = true
    · simp only [hcB, ↓reduceIte] at hst
      simp only [Bool.and_eq_true] at hcB
      have hd1 : dir = true := hcB.1
      have hq1 : q = 1 := Nat.eq_of_beq_eq_true hcB.2
      subst hd1; subst hq1
      rcases l with _ | ⟨⟨s0, c0⟩, _ | ⟨⟨s1, c1⟩, _ | ⟨⟨s2, a⟩, tail⟩⟩⟩
      · exact stepNormal_sound 1 true [] r dt c' hst
      · exact stepNormal_sound 1 true [⟨s0, c0⟩] r dt c' hst
      · exact stepNormal_sound 1 true [⟨s0, c0⟩, ⟨s1, c1⟩] r dt c' hst
      · simp only at hst
        set zOk := match tail with | [] => true | ⟨zSym, _⟩ :: _ => Nat.beq zSym 0
        by_cases hcond : (Nat.beq s0 2 && Nat.beq c0 1 && Nat.beq s1 0 && Nat.beq c1 1 &&
            Nat.beq s2 2 && Nat.ble 2 a && zOk) = true
        · simp only [hcond, ↓reduceIte] at hst
          simp only [Bool.and_eq_true] at hcond
          have hs0 : s0 = 2 := Nat.eq_of_beq_eq_true hcond.1.1.1.1.1.1
          have hc0 : c0 = 1 := Nat.eq_of_beq_eq_true hcond.1.1.1.1.1.2
          have hs1 : s1 = 0 := Nat.eq_of_beq_eq_true hcond.1.1.1.1.2
          have hc1 : c1 = 1 := Nat.eq_of_beq_eq_true hcond.1.1.1.2
          have hs2 : s2 = 2 := Nat.eq_of_beq_eq_true hcond.1.1.2
          have ha2 : 2 ≤ a := Nat.le_of_ble_eq_true hcond.1.2
          subst hs0; subst hc0; subst hs1; subst hc1; subst hs2
          rcases htr : transferRightCount 1 r with _ | b
          · rw [htr] at hst
            exact stepNormal_sound 1 true _ r dt c' hst
          · rw [htr] at hst
            simp only [withNat_eq, Option.some.injEq, Prod.mk.injEq] at hst
            rcases hst with ⟨rfl, rfl⟩
            set k := a / 2
            set rem := a - 2 * k
            set lBase := if Nat.beq rem 0 then tail else Run.mk 2 rem :: tail
            have hlBase : evalSide false baseWord lBase =
                ListBlank.append (([0, 1] : List (Fin 2)) ^ rem)
                  (evalSide false baseWord tail) := by
              dsimp only [lBase]
              by_cases hr0 : Nat.beq rem 0 = true
              · have h0 := Nat.eq_of_beq_eq_true hr0
                simp [h0]
              · have hnr0 := Bool.eq_false_iff.mpr hr0
                simp [hnr0, evalSide, baseWord]
            have haSplit : a = 2 * k + rem := by omega
            have hrun := transferB_batch k b (evalSide false baseWord lBase)
            have hrEq := transferRightCount_eval htr
            simpa [evalEntryCfg, dirCfg, qOf, evalSide, baseWord, hrEq,
              evalSide_pushLit baseWord_zero_blank, hlBase, haSplit, list_pow_add,
              ListBlank.append_assoc] using hrun
        · have hncond := Bool.eq_false_iff.mpr hcond
          rw [hncond] at hst
          exact stepNormal_sound 1 true _ r dt c' hst
    · have hncB := Bool.eq_false_iff.mpr hcB
      simp only [hncB, Bool.false_eq_true, ↓reduceIte] at hst
      exact stepNormal_sound q dir l r dt c' hst

/-! ## Closed-Form Milestone Configurations `C(m)` and Symbolic Family Specification -/

/-- Fixed outer prefix `U` of the `C(m)` family. -/
def uRuns : List (ℕ × ℕ) :=
  [(2, 1), (1, 1), (0, 1), (2, 8), (0, 1), (2, 5), (1, 11), (0, 1)]

/-- Growing outer block `P = X^8 Y^10 Z`. -/
def pRuns : List (ℕ × ℕ) :=
  [(2, 8), (1, 10), (0, 1)]

/-- Fixed middle separator `V(N)` with `N = 791761176`. -/
def vRuns : List (ℕ × ℕ) :=
  [(2, 791761176), (1, 9), (0, 1), (2, 21), (1, 41), (0, 1), (2, 15), (1, 93), (0, 1)]

/-- Growing inner block `Q = X^36 Y^17 Z X^91 Y^38 Z X^15 Y^93 Z`. -/
def qRuns : List (ℕ × ℕ) :=
  [(2, 36), (1, 17), (0, 1), (2, 91), (1, 38), (0, 1), (2, 15), (1, 93), (0, 1)]

/-- Fixed head-adjacent suffix `W = X^14 Z X^5 Z X`. -/
def wRuns : List (ℕ × ℕ) :=
  [(2, 14), (0, 1), (2, 5), (0, 1), (2, 1)]

/-- Repeat a run list `n` times. -/
def repRuns : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, _ => []
  | n + 1, xs => xs ++ repRuns n xs

/-- Expand a `(sym, count)` run list into a flat list of 2-bit base-word indices. -/
def expandRunWords : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (s, n) :: rest => List.replicate n s ++ expandRunWords rest

/-- Base-word sequence of block `P` (`19` two-bit words). -/
def pWord : List ℕ := expandRunWords pRuns

/-- Base-word sequence of block `Q` (`293` two-bit words). -/
def qWord : List ℕ := expandRunWords qRuns

/-- Closed-form Entry milestone configuration `C(m)` for concrete `m : ℕ`. -/
def entryMilestone (m : ℕ) : EntryCfg :=
  ⟨1, true,
    pushRunsLeft (uRuns ++ repRuns m pRuns ++ vRuns ++ repRuns m qRuns ++ wRuns) [],
    [⟨1, 6⟩]⟩

/-- Symbolic initial configuration `C(k + 8)` (`wid = 4` is `P`, `wid = 5` is `Q`). -/
def initReturnCfg : AffCfg :=
  let s₀ : List AffRun := []
  let s₁ := pushAffConstRuns uRuns s₀
  let s₂ := match pushAff 4 ⟨1, 8⟩ s₁ with | some s => s | none => s₁
  let s₃ := pushAffConstRuns vRuns s₂
  let s₄ := match pushAff 5 ⟨1, 8⟩ s₃ with | some s => s | none => s₃
  let s₅ := pushAffConstRuns wRuns s₄
  ⟨1, true, s₅, [⟨1, ⟨0, 6⟩⟩]⟩

/-- Exact affine return step count `119808 * k + 304037417082`
(`= 304036458618 + 119808 * (k + 8)`). -/
def returnTarget : AffNat :=
  ⟨119808, 304037417082⟩

end BusyBeaver.BB6.A6

end
