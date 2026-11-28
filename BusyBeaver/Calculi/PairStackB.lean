/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Calculi.PairStackA
import Mathlib.Tactic.Linarith

/-!
# Shared 6-Mode Pair-Stack Transducer, `EvalF` Bisimulation & `W_closed` Bridge

Shared non-halting infrastructure for the 6-mode pair-stack equivalence class
(`1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`, `1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB`, and
`1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA`):
1. Base machine `tm484`, 6-mode pair-stack transducer (`Mode484`, `State484`, `stepAtomic`,
   `isDoor`, `stepTot`, `runTot`), tape encoding `evalAtomic`, and 24-branch `stepAtomic_sound`.
2. Machine-independent `(EvalF, EvalDL, Disp)` big-step relation and constructive bounded-horizon
   `tm484 <-> EvalF` bisimulation (`orbit_safe_of_evalF_W_closed`).
3. Simulation `(EvalF, EvalDL) -> (BigF, BigD1)` into `BusyBeaver.Calculi.PairStackA` and
   `W_closed` / `W_closed_step` closing the singleton wall invariant across the 3-machine family.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.Calculi.PairStackB

/-- Base machine `tm484` (`1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`). -/
def tm484 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

/-! ## 6-Mode Pair-Stack Transducer (`stepAtomic`, `isDoor`, `stepTot`) -/

/-- Nullary control modes of the 6-mode pair-stack transducer. -/
inductive Mode484 : Type
  | mC0
  | mAL
  | mE1
  | mBR
  | mDR
  | mD0

/-- Pair-stack configuration `(mode, L, R)`: `(a, false)` encodes `1^(a+1) 0` and `(a, true)`
encodes `1^(a+1) 00` outwards from the head. -/
structure State484 : Type where
  mode : Mode484
  L : List (ℕ × Bool)
  R : List (ℕ × Bool)

/-- Increment the top `1^(a+1)` block of a stack (creating `[(0, false)]` on an empty stack). -/
def bump : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => [(0, false)]
  | (a, sep) :: rest => (a + 1, sep) :: rest

/-- Exact 26-branch atomic step of the 6-mode stack transducer (`some (s', dt)` on the `24`
non-halting branches and `none` on the `2` halting doorways). -/
def stepAtomic (s : State484) : Option (State484 × ℕ) :=
  match s.mode with
  | .mC0 => some (⟨.mAL, s.L, bump s.R⟩, 1)
  | .mAL =>
    match s.L with
    | [] => some (⟨.mBR, [(0, false)], s.R⟩, 1)
    | (0, false) :: Ls => some (⟨.mE1, Ls, s.R⟩, 1)
    | (0, true) :: _ => none
    | (1, false) :: Ls =>
      match s.R with
      | [] => some (⟨.mC0, Ls, []⟩, 2)
      | r0 :: Rs => some (⟨.mAL, Ls, (0, true) :: r0 :: Rs⟩, 3)
    | (1, true) :: Ls => some (⟨.mBR, bump Ls, (0, true) :: s.R⟩, 4)
    | (2, false) :: Ls => some (⟨.mBR, bump Ls, (1, false) :: s.R⟩, 6)
    | (2, true) :: Ls => some (⟨.mBR, (0, false) :: Ls, (1, false) :: s.R⟩, 6)
    | (a + 3, sep) :: Ls => some (⟨.mC0, (a, sep) :: Ls, (0, false) :: s.R⟩, 4)
  | .mE1 =>
    match s.L with
    | [] => none
    | l0 :: Ls => some (⟨.mBR, l0 :: Ls, bump (bump s.R)⟩, 6)
  | .mBR =>
    match s.R with
    | [] =>
      match s.L with
      | [] => some (⟨.mC0, [], [(0, false)]⟩, 1)
      | (0, false) :: Ls => some (⟨.mD0, (0, true) :: Ls, []⟩, 3)
      | (0, true) :: Ls => some (⟨.mBR, (0, false) :: Ls, [(0, true), (0, false)]⟩, 9)
      | (a + 1, sep) :: Ls => some (⟨.mD0, (0, false) :: (a, sep) :: Ls, []⟩, 3)
    | (0, false) :: Rs => some (⟨.mD0, bump s.L, Rs⟩, 1)
    | (0, true) :: Rs => some (⟨.mC0, bump (bump s.L), Rs⟩, 2)
    | (d + 1, c) :: Rs => some (⟨.mDR, bump s.L, (d, c) :: Rs⟩, 1)
  | .mDR =>
    match s.R with
    | [] => some (⟨.mC0, bump s.L, []⟩, 1)
    | (0, false) :: Rs =>
      match s.L with
      | [] => some (⟨.mBR, [], bump Rs⟩, 3)
      | l0 :: Ls => some (⟨.mDR, (0, false) :: l0 :: Ls, Rs⟩, 4)
    | (0, true) :: Rs =>
      match s.L with
      | [] => some (⟨.mBR, [], (0, false) :: Rs⟩, 3)
      | l0 :: Ls => some (⟨.mD0, (0, false) :: l0 :: Ls, Rs⟩, 4)
    | (d + 1, c) :: Rs => some (⟨.mBR, bump s.L, (d, c) :: Rs⟩, 1)
  | .mD0 =>
    match s.R with
    | [] => some (⟨.mC0, bump s.L, []⟩, 1)
    | (0, false) :: Rs => some (⟨.mC0, bump s.L, bump Rs⟩, 3)
    | (0, true) :: Rs => some (⟨.mC0, bump s.L, (0, false) :: Rs⟩, 3)
    | (1, false) :: Rs => some (⟨.mD0, (0, false) :: bump s.L, Rs⟩, 3)
    | (1, true) :: Rs => some (⟨.mC0, (1, false) :: bump s.L, Rs⟩, 4)
    | (d + 2, c) :: Rs => some (⟨.mDR, (0, false) :: bump s.L, (d, c) :: Rs⟩, 3)

/-- Boolean doorway predicate (`stepAtomic s = none ↔ isDoor s = true`). -/
def isDoor (s : State484) : Bool :=
  match s.mode, s.L with
  | .mAL, (0, true) :: _ => true
  | .mE1, [] => true
  | _, _ => false

/-- Totalized step function (`Option`-free; doorways stutter in place). -/
def stepTot (s : State484) : State484 :=
  match stepAtomic s with
  | none => s
  | some (s', _) => s'

/-- Exact `n`-step iteration of `stepTot`. -/
def runTot : ℕ → State484 → State484
  | 0, s => s
  | n + 1, s => runTot n (stepTot s)

theorem stepAtomic_cost_pos {s s' : State484} {dt : ℕ}
    (h : stepAtomic s = some (s', dt)) : 0 < dt := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | mC0 =>
    simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩; decide
  | mAL =>
    rcases L with _ | ⟨⟨_ | _ | _ | a, _ | _⟩, Ls⟩
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp [stepAtomic] at h
    · cases R with
      | nil =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      | cons _ _ =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
  | mE1 =>
    cases L with
    | nil => simp [stepAtomic] at h
    | cons _ _ =>
      simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩; decide
  | mBR =>
    rcases R with _ | ⟨⟨_ | d, _ | _⟩, Rs⟩
    · rcases L with _ | ⟨⟨_ | a, _ | _⟩, Ls⟩
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
  | mDR =>
    rcases R with _ | ⟨⟨_ | d, _ | _⟩, Rs⟩
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · cases L with
      | nil =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      | cons _ _ =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
    · cases L with
      | nil =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
      | cons _ _ =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
  | mD0 =>
    rcases R with _ | ⟨⟨_ | _ | d, _ | _⟩, Rs⟩
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide

theorem stepAtomic_eq_none_iff (s : State484) :
    stepAtomic s = none ↔ isDoor s = true := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | mC0 => simp [stepAtomic, isDoor]
  | mAL =>
    rcases L with _ | ⟨⟨_ | _ | _ | a, _ | _⟩, Ls⟩
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · cases R <;> simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
  | mE1 =>
    cases L <;> simp [stepAtomic, isDoor]
  | mBR =>
    rcases R with _ | ⟨⟨_ | d, _ | _⟩, Rs⟩
    · rcases L with _ | ⟨⟨_ | a, _ | _⟩, Ls⟩ <;> simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
  | mDR =>
    rcases R with _ | ⟨⟨_ | d, _ | _⟩, Rs⟩
    · simp [stepAtomic, isDoor]
    · cases L <;> simp [stepAtomic, isDoor]
    · cases L <;> simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
    · simp [stepAtomic, isDoor]
  | mD0 =>
    rcases R with _ | ⟨⟨_ | _ | d, _ | _⟩, Rs⟩ <;> simp [stepAtomic, isDoor]

theorem stepAtomic_some_of_not_door {s : State484} (h : isDoor s = false) :
    ∃ dt, 0 < dt ∧ stepAtomic s = some (stepTot s, dt) := by
  cases hs : stepAtomic s with
  | none =>
    have hd := (stepAtomic_eq_none_iff s).mp hs
    rw [hd] at h; cases h
  | some p =>
    rcases p with ⟨s', dt⟩
    refine ⟨dt, stepAtomic_cost_pos hs, ?_⟩
    simp [stepTot, hs]

/-! ## Tape Encoding & 24-Branch Raw-TM Soundness (`stepAtomic_sound`) -/

/-- Prepend `n` ones (`1 : Fin 2`) onto a `ListBlank (Fin 2)` half-tape. -/
def pushOnes : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, t => t
  | n + 1, t => ListBlank.cons 1 (pushOnes n t)

/-- Prepend `1` zero (`sep = false`) or `2` zeros (`sep = true`) onto a half-tape. -/
def pushSep (sep : Bool) (t : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  if sep then ListBlank.cons 0 (ListBlank.cons 0 t) else ListBlank.cons 0 t

/-- Encode a pair-stack `List (ℕ × Bool)` outwards from the head. -/
def encStack : List (ℕ × Bool) → ListBlank (Fin 2)
  | [] => default
  | (a, sep) :: rest => pushOnes (a + 1) (pushSep sep (encStack rest))

private theorem encStack_bump (S : List (ℕ × Bool)) :
    encStack (bump S) = ListBlank.cons 1 (encStack S) := by
  cases S with
  | nil => simp [bump, encStack, pushOnes, pushSep, BusyBeaver.ListBlank.cons_zero_default]
  | cons p rest =>
    rcases p with ⟨a, sep⟩
    rfl

/-- Direct tape embedding of `State484` into base machine `tm484`. -/
def enc484 (s : State484) : Cfg (Fin 2) (Fin 6) :=
  match s.mode with
  | .mC0 => ⟨some 2, ⟨0, encStack s.L, encStack s.R⟩⟩
  | .mAL => Cfg.headLeft 0 (encStack s.L) (encStack s.R)
  | .mE1 => ⟨some 4, ⟨0, encStack s.L, ListBlank.cons 0 (encStack s.R)⟩⟩
  | .mBR => Cfg.headRight 1 (encStack s.L) (encStack s.R)
  | .mDR => Cfg.headRight 3 (encStack s.L) (encStack s.R)
  | .mD0 => ⟨some 3, ⟨0, encStack s.L, encStack s.R⟩⟩

private def stepWin (bL bR : Bool) : Fin 6 × Fin 2 × List (Fin 2) × List (Fin 2) →
    Option (Fin 6 × Fin 2 × List (Fin 2) × List (Fin 2))
  | (q, hd, ls, rs) =>
    match tm484 q hd with
    | some (some q', Stmt.write w Dir.right) =>
      match rs with
      | a :: rs' => some (q', a, w :: ls, rs')
      | [] => if bR then some (q', 0, w :: ls, []) else none
    | some (some q', Stmt.write w Dir.left) =>
      match ls with
      | a :: ls' => some (q', a, ls', w :: rs)
      | [] => if bL then some (q', 0, [], w :: rs) else none
    | _ => none

private def multiStepWin (bL bR : Bool) : ℕ → Fin 6 × Fin 2 × List (Fin 2) × List (Fin 2) →
    Option (Fin 6 × Fin 2 × List (Fin 2) × List (Fin 2))
  | 0, st => some st
  | n + 1, st => (stepWin bL bR st).bind (multiStepWin bL bR n)

private def evalCell (l r : ListBlank (Fin 2)) (q : Fin 6) (hd : Fin 2)
    (ls rs : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some q, ⟨hd, ls +> l, rs +> r⟩⟩

private theorem stepWin_sound {bL bR : Bool} {l r : ListBlank (Fin 2)}
    (hL : bL = true → l = default) (hR : bR = true → r = default)
    {q q' : Fin 6} {hd hd' : Fin 2} {ls rs ls' rs' : List (Fin 2)}
    (hs : stepWin bL bR (q, hd, ls, rs) = some (q', hd', ls', rs')) :
    step tm484 (evalCell l r q hd ls rs) = some (evalCell l r q' hd' ls' rs') := by
  rcases htm : tm484 q hd with _ | ⟨_ | q₁, ⟨w, dir⟩⟩
  · simp [stepWin, htm] at hs
  · simp [stepWin, htm] at hs
  · simp only [stepWin, htm] at hs
    cases dir with
    | right =>
      cases rs with
      | cons a rs₀ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl, rfl, rfl⟩
        simp [evalCell, step, htm, Tape.write, Tape.move, ListBlank.append]
      | nil =>
        cases hbR : bR with
        | false => simp [hbR] at hs
        | true =>
          simp only [hbR, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl, rfl, rfl⟩
          have hr0 := hR hbR; subst hr0
          simp [evalCell, step, htm, Tape.write, Tape.move, ListBlank.append]
    | left =>
      cases ls with
      | cons a ls₀ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl, rfl, rfl⟩
        simp [evalCell, step, htm, Tape.write, Tape.move, ListBlank.append]
      | nil =>
        cases hbL : bL with
        | false => simp [hbL] at hs
        | true =>
          simp only [hbL, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl, rfl, rfl⟩
          have hl0 := hL hbL; subst hl0
          simp [evalCell, step, htm, Tape.write, Tape.move, ListBlank.append]

private theorem multiStepWin_sound {bL bR : Bool} {l r : ListBlank (Fin 2)}
    (hL : bL = true → l = default) (hR : bR = true → r = default) :
    ∀ (n : ℕ) (q : Fin 6) (hd : Fin 2) (ls rs : List (Fin 2))
      (q' : Fin 6) (hd' : Fin 2) (ls' rs' : List (Fin 2)),
      multiStepWin bL bR n (q, hd, ls, rs) = some (q', hd', ls', rs') →
      multiStep tm484 (evalCell l r q hd ls rs) n = some (evalCell l r q' hd' ls' rs')
  | 0, _, _, _, _, _, _, _, _, h => by
    simp only [multiStepWin, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl
  | n + 1, q, hd, ls, rs, q', hd', ls', rs', h => by
    simp only [multiStepWin] at h
    rcases hsw : stepWin bL bR (q, hd, ls, rs) with _ | ⟨q₁, hd₁, ls₁, rs₁⟩
    · simp [hsw] at h
    · simp only [hsw, Option.bind_some] at h
      have h1 : multiStep tm484 (evalCell l r q hd ls rs) 1 =
          some (evalCell l r q₁ hd₁ ls₁ rs₁) :=
        stepWin_sound hL hR hsw
      have h2 := multiStepWin_sound hL hR n q₁ hd₁ ls₁ rs₁ q' hd' ls' rs' h
      rw [Nat.add_comm n 1]
      exact multiStep_trans h1 h2

private theorem runWin_eq {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (bL bR : Bool) (n : ℕ) (l r : ListBlank (Fin 2))
    (q : Fin 6) (hd : Fin 2) (ls rs : List (Fin 2))
    (q' : Fin 6) (hd' : Fin 2) (ls' rs' : List (Fin 2))
    (hL : bL = true → l = default) (hR : bR = true → r = default)
    (hc₁ : c₁ = evalCell l r q hd ls rs)
    (hc₂ : c₂ = evalCell l r q' hd' ls' rs')
    (hw : multiStepWin bL bR n (q, hd, ls, rs) = some (q', hd', ls', rs')) :
    multiStep tm484 c₁ n = some c₂ := by
  rw [hc₁, hc₂]
  exact multiStepWin_sound hL hR n q hd ls rs q' hd' ls' rs' hw

private theorem no_false (h : false = true) : False := by cases h

private theorem headLeft_nil (q : Fin 6) (r : ListBlank (Fin 2)) :
    Cfg.headLeft q (default : ListBlank (Fin 2)) r = ⟨some q, ⟨0, default, r⟩⟩ := by
  simp [Cfg.headLeft]

private theorem headRight_nil (q : Fin 6) (l : ListBlank (Fin 2)) :
    Cfg.headRight q l (default : ListBlank (Fin 2)) = ⟨some q, ⟨0, l, default⟩⟩ := by
  simp [Cfg.headRight]

private theorem headLeft_cons (q : Fin 6) (x : Fin 2) (l r : ListBlank (Fin 2)) :
    Cfg.headLeft q (ListBlank.cons x l) r = ⟨some q, ⟨x, l, r⟩⟩ := by
  simp [Cfg.headLeft, ListBlank.head_cons, ListBlank.tail_cons]

private theorem headRight_cons (q : Fin 6) (x : Fin 2) (l r : ListBlank (Fin 2)) :
    Cfg.headRight q l (ListBlank.cons x r) = ⟨some q, ⟨x, l, r⟩⟩ := by
  simp [Cfg.headRight, ListBlank.head_cons, ListBlank.tail_cons]

/-- Exact raw-TM soundness of all `24` defined `stepAtomic` branches on `tm484`. -/
theorem stepAtomic_sound (s s' : State484) (dt : ℕ)
    (h : stepAtomic s = some (s', dt)) :
    0 < dt ∧ multiStep tm484 (enc484 s) dt = some (enc484 s') := by
  have hpos := stepAtomic_cost_pos h
  refine ⟨hpos, ?_⟩
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | mC0 =>
    simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    cases L with
    | nil =>
      refine runWin_eq true false 1 default (encStack R) 2 0 [] [] 0 0 [] [1]
        (fun _ => rfl) (fun h => (no_false h).elim) rfl ?_ rfl
      simp [enc484, encStack, encStack_bump, headLeft_nil, evalCell, ListBlank.append]
    | cons p Ls =>
      rcases p with ⟨a, sep⟩
      refine runWin_eq false false 1 (pushOnes a (pushSep sep (encStack Ls))) (encStack R)
        2 0 [1] [] 0 1 [] [1] (fun h => (no_false h).elim) (fun h => (no_false h).elim) rfl ?_ rfl
      simp [enc484, encStack, encStack_bump, pushOnes, headLeft_cons, evalCell, ListBlank.append]
  | mAL =>
    rcases L with _ | ⟨⟨_ | _ | _ | a, _ | _⟩, Ls⟩
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases R with
      | nil =>
        refine runWin_eq true true 1 default default 0 0 [] [] 1 0 [1] []
          (fun _ => rfl) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, headLeft_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, headRight_nil, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
      | cons r0 Rs =>
        rcases r0 with ⟨d, c⟩
        refine runWin_eq true false 1 default (pushOnes d (pushSep c (encStack Rs)))
          0 0 [] [1] 1 1 [1] [] (fun _ => rfl) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, headLeft_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 1 (encStack Ls) (encStack R) 0 1 [0] [] 4 0 [] [0]
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ rfl rfl
      simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
    · simp [stepAtomic] at h
    · cases R with
      | nil =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq false false 2 (encStack Ls) default 0 1 [1, 0] [] 2 0 [] [0, 0]
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
      | cons r0 Rs =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        cases Ls with
        | nil =>
          refine runWin_eq true false 3 default (encStack (r0 :: Rs))
            0 1 [1, 0] [] 0 0 [] [1, 0, 0]
            (fun _ => rfl) (fun h => (no_false h).elim) ?_ ?_ rfl
          · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
          · simp [enc484, encStack, pushOnes, pushSep, headLeft_nil, evalCell, ListBlank.append]
        | cons l1 Lss =>
          rcases l1 with ⟨a1, s1⟩
          refine runWin_eq false false 3 (pushOnes a1 (pushSep s1 (encStack Lss)))
            (encStack (r0 :: Rs)) 0 1 [1, 0, 1] [] 0 1 [] [1, 0, 0]
            (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
          · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
          · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases R with
      | nil =>
        refine runWin_eq false true 4 (encStack Ls) default 0 1 [1, 0, 0] [] 1 1 [1] [0, 0]
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
      | cons r0 Rs =>
        rcases r0 with ⟨d, c⟩
        refine runWin_eq false false 4 (encStack Ls) (pushOnes d (pushSep c (encStack Rs)))
          0 1 [1, 0, 0] [1] 1 1 [1] [0, 0, 1]
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases R with
      | nil =>
        refine runWin_eq false true 6 (encStack Ls) default 0 1 [1, 1, 0] [] 1 1 [1] [1, 0]
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
      | cons r0 Rs =>
        rcases r0 with ⟨d, c⟩
        refine runWin_eq false false 6 (encStack Ls) (pushOnes d (pushSep c (encStack Rs)))
          0 1 [1, 1, 0] [1] 1 1 [1] [1, 0, 1]
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases R with
      | nil =>
        refine runWin_eq false true 6 (encStack Ls) default 0 1 [1, 1, 0, 0] [] 1 1 [1, 0] [1, 0]
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      | cons r0 Rs =>
        rcases r0 with ⟨d, c⟩
        refine runWin_eq false false 6 (encStack Ls) (pushOnes d (pushSep c (encStack Rs)))
          0 1 [1, 1, 0, 0] [1] 1 1 [1, 0] [1, 0, 1]
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 4 (pushOnes a (pushSep false (encStack Ls))) (encStack R)
        0 1 [1, 1, 1] [] 2 0 [1] [1, 0]
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 4 (pushOnes a (pushSep true (encStack Ls))) (encStack R)
        0 1 [1, 1, 1] [] 2 0 [1] [1, 0]
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headLeft_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
  | mE1 =>
    cases L with
    | nil => simp [stepAtomic] at h
    | cons l0 Ls =>
      rcases l0 with ⟨a, sep⟩
      simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 6 (pushOnes a (pushSep sep (encStack Ls))) (encStack R)
        4 0 [1] [0] 1 1 [1] [1]
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, encStack_bump, headRight_cons, evalCell,
          ListBlank.append]
  | mBR =>
    rcases R with _ | ⟨⟨_ | d, _ | _⟩, Rs⟩
    · rcases L with _ | ⟨⟨_ | a, _ | _⟩, Ls⟩
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq true true 1 default default 1 0 [] [] 2 0 [] [1]
          (fun _ => rfl) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, headRight_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq false true 3 (encStack Ls) default 1 0 [1, 0] [] 3 0 [1, 0, 0] []
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq false true 9 (encStack Ls) default 1 0 [1, 0, 0] [] 1 1 [1, 0] [0, 0, 1]
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq false true 3 (pushOnes a (pushSep false (encStack Ls))) default
          1 0 [1, 1] [] 3 0 [1, 0, 1] []
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
      · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq false true 3 (pushOnes a (pushSep true (encStack Ls))) default
          1 0 [1, 1] [] 3 0 [1, 0, 1] []
          (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_nil, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 1 (encStack L) (encStack Rs) 1 1 [] [0] 3 0 [1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 2 (encStack L) (encStack Rs) 1 1 [] [0, 0] 2 0 [1, 1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 1 (encStack L) (pushOnes d (pushSep false (encStack Rs)))
        1 1 [] [1] 3 1 [1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
          ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 1 (encStack L) (pushOnes d (pushSep true (encStack Rs)))
        1 1 [] [1] 3 1 [1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
          ListBlank.append]
  | mDR =>
    rcases R with _ | ⟨⟨_ | d, _ | _⟩, Rs⟩
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false true 1 (encStack L) default 3 0 [] [] 2 0 [1] []
        (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
      · simp [enc484, encStack, headRight_nil, evalCell, ListBlank.append]
      · simp [enc484, encStack, encStack_bump, evalCell, ListBlank.append]
    · cases L with
      | nil =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq true false 3 default (encStack Rs) 3 1 [] [0] 1 1 [0] []
          (fun _ => rfl) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, encStack_bump, headRight_cons, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
      | cons l0 Ls =>
        rcases l0 with ⟨a, sep⟩
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        cases Rs with
        | nil =>
          refine runWin_eq false true 4 (pushOnes a (pushSep sep (encStack Ls))) default
            3 1 [1] [0] 3 0 [1, 0, 1] []
            (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
          · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
          · simp [enc484, encStack, pushOnes, pushSep, headRight_nil, evalCell, ListBlank.append]
        | cons r1 Rss =>
          rcases r1 with ⟨d1, c1⟩
          refine runWin_eq false false 4 (pushOnes a (pushSep sep (encStack Ls)))
            (pushOnes d1 (pushSep c1 (encStack Rss))) 3 1 [1] [0, 1] 3 1 [1, 0, 1] []
            (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
          · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
          · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
    · cases L with
      | nil =>
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq true false 3 default (encStack Rs) 3 1 [] [0, 0] 1 1 [0] [0]
          (fun _ => rfl) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append,
            BusyBeaver.ListBlank.cons_zero_default]
      | cons l0 Ls =>
        rcases l0 with ⟨a, sep⟩
        simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine runWin_eq false false 4 (pushOnes a (pushSep sep (encStack Ls))) (encStack Rs)
          3 1 [1] [0, 0] 3 0 [1, 0, 1] []
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 1 (encStack L) (pushOnes d (pushSep false (encStack Rs)))
        3 1 [] [1] 1 1 [1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
          ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 1 (encStack L) (pushOnes d (pushSep true (encStack Rs)))
        3 1 [] [1] 1 1 [1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, headRight_cons, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
          ListBlank.append]
  | mD0 =>
    rcases R with _ | ⟨⟨_ | _ | d, _ | _⟩, Rs⟩
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false true 1 (encStack L) default 3 0 [] [] 2 0 [1] []
        (fun h => (no_false h).elim) (fun _ => rfl) ?_ ?_ rfl
      · simp [enc484, encStack, evalCell, ListBlank.append]
      · simp [enc484, encStack, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 3 (encStack L) (encStack Rs) 3 0 [] [1, 0] 2 0 [1] [1]
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
      · simp [enc484, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 3 (encStack L) (encStack Rs) 3 0 [] [1, 0, 0] 2 0 [1] [1, 0]
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 3 (encStack L) (encStack Rs) 3 0 [] [1, 1, 0] 3 0 [1, 0, 1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine runWin_eq false false 4 (encStack L) (encStack Rs)
        3 0 [] [1, 1, 0, 0] 2 0 [1, 1, 0, 1] []
        (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
      · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
      · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, evalCell, ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases d with
      | zero =>
        refine runWin_eq false false 3 (encStack L) (encStack Rs)
          3 0 [] [1, 1, 1, 0] 3 1 [1, 0, 1] [0]
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
      | succ d' =>
        refine runWin_eq false false 3 (encStack L)
          (pushOnes (d' + 1) (pushSep false (encStack Rs)))
          3 0 [] [1, 1, 1] 3 1 [1, 0, 1] []
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
    · simp only [stepAtomic, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases d with
      | zero =>
        refine runWin_eq false false 3 (encStack L) (encStack Rs)
          3 0 [] [1, 1, 1, 0, 0] 3 1 [1, 0, 1] [0, 0]
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]
      | succ d' =>
        refine runWin_eq false false 3 (encStack L)
          (pushOnes (d' + 1) (pushSep true (encStack Rs)))
          3 0 [] [1, 1, 1] 3 1 [1, 0, 1] []
          (fun h => (no_false h).elim) (fun h => (no_false h).elim) ?_ ?_ rfl
        · simp [enc484, encStack, pushOnes, pushSep, evalCell, ListBlank.append]
        · simp [enc484, encStack, pushOnes, pushSep, encStack_bump, headRight_cons, evalCell,
            ListBlank.append]

/-! ## Turnkey `IsNotHalt` & Step-Indexed Safety Bridges -/

theorem multiStep_add_eq {M : Machine (Fin 2) (Fin 6)} {c₁ : Cfg (Fin 2) (Fin 6)} :
    ∀ a b : ℕ, multiStep M c₁ (a + b) = (multiStep M c₁ a).bind (fun c₂ => multiStep M c₂ b) :=
  multiStep_add M c₁

theorem isSome_step_of_multiStep_succ {M : Machine (Fin 2) (Fin 6)}
    {c c' : Cfg (Fin 2) (Fin 6)} {k : ℕ}
    (h : multiStep M c (k + 1) = some c') : (step M c).isSome = true := by
  have h1 : multiStep M c (1 + k) = some c' := by rwa [Nat.add_comm] at h
  rw [multiStep_add_eq 1 k] at h1
  cases hs : step M c with
  | none =>
    have hms1 : multiStep M c 1 = none := hs
    rw [hms1] at h1
    cases h1
  | some _ => rfl

/-- Exact `runTot` vs `stepTot^[n]` agreement. -/
theorem runTot_eq_iterate (n : ℕ) (s : State484) : runTot n s = stepTot^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [runTot, Function.iterate_succ_apply]
    exact ih (stepTot s)

/-- If every `stepTot`-iterate from `s₀` avoids doorways, then `enc484 s₀` reaches arbitrarily
large raw-TM step counts `t ≥ n`. -/
theorem multiStep_ge_of_orbit_safe (s₀ : State484)
    (hsafe : ∀ n : ℕ, isDoor (stepTot^[n] s₀) = false) :
    ∀ n : ℕ, ∃ t ≥ n, multiStep tm484 (enc484 s₀) t = some (enc484 (stepTot^[n] s₀)) := by
  intro n
  induction n with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨t, ht, hmt⟩
    obtain ⟨dt, hdt_pos, hst⟩ := stepAtomic_some_of_not_door (hsafe n)
    have hsound := (stepAtomic_sound _ _ _ hst).2
    refine ⟨t + dt, Nat.add_le_add ht hdt_pos, ?_⟩
    rw [Function.iterate_succ_apply']
    exact multiStep_trans hmt hsound

/-- Universal `stepTot`-based survival helper: checking `n` concrete steps via `runTot`. -/
theorem stepTot_iter_add (a b : ℕ) (s : State484) :
    stepTot^[a + b] s = stepTot^[b] (stepTot^[a] s) := by
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- Additive composition for `runTot`. -/
theorem runTot_add (a b : ℕ) (s : State484) :
    runTot (a + b) s = runTot b (runTot a s) := by
  rw [runTot_eq_iterate, runTot_eq_iterate, runTot_eq_iterate, stepTot_iter_add]

/-- Boolean prefix-safety checker: `safePrefix k s` holds iff `isDoor (stepTot^[j] s) = false`
for all `j < k`. -/
def safePrefix : ℕ → State484 → Bool
  | 0, _ => true
  | k + 1, s => !(isDoor s) && safePrefix k (stepTot s)

theorem safePrefix_sound : ∀ (k : ℕ) (s : State484),
    safePrefix k s = true → ∀ j < k, isDoor (stepTot^[j] s) = false
  | 0, _, _, _, hj => (Nat.not_lt_zero _ hj).elim
  | k + 1, s, hs, 0, _ => by
    simp only [safePrefix, Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.1
  | k + 1, s, hs, j + 1, hj => by
    simp only [safePrefix, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rw [Function.iterate_succ_apply]
    exact safePrefix_sound k (stepTot s) hs.2 j (Nat.lt_of_succ_lt_succ hj)

theorem safePrefix_chunks (s₁ s₂ : State484) (a b : ℕ)
    (hrun : runTot a s₁ = s₂)
    (ha : ∀ j < a, isDoor (stepTot^[j] s₁) = false)
    (hb : ∀ j < b, isDoor (stepTot^[j] s₂) = false) :
    ∀ j < a + b, isDoor (stepTot^[j] s₁) = false := by
  intro j hj
  by_cases hja : j < a
  · exact ha j hja
  · have hjb : j - a < b := by omega
    have hsplit : j = a + (j - a) := by omega
    rw [hsplit, stepTot_iter_add, ← runTot_eq_iterate a, hrun]
    exact hb (j - a) hjb


/-! ## Pure Stack Helpers & `StrictNo0F` / `DLNo0F` -/

/-- Prepend `n` copies of `(1, false)` to a right-tape stack. -/
def rep1 : ℕ → List (ℕ × Bool) → List (ℕ × Bool)
  | 0, R => R
  | n + 1, R => (1, false) :: rep1 n R

/-- Double-bump helper `bump (bump R)`. -/
def bump2 (R : List (ℕ × Bool)) : List (ℕ × Bool) := bump (bump R)

/-- Strict `NoNonlast0F`: `(0, false)` never appears before the last element of `R`. -/
def StrictNo0F : List (ℕ × Bool) → Prop
  | [] => True
  | [_] => True
  | (0, false) :: _ :: _ => False
  | _ :: rest => StrictNo0F rest

/-- Relaxed `NoNonlast0F` for `mBR`/`EvalDL`: `(0, false)` may appear at head or last, never
strictly inside. -/
def DLNo0F : List (ℕ × Bool) → Prop
  | [] => True
  | _ :: rest => StrictNo0F rest

theorem rep1_cons_one (q : ℕ) (R : List (ℕ × Bool)) :
    rep1 q ((1, false) :: R) = (1, false) :: rep1 q R := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [rep1, ih]

theorem rep1_nonempty (q : ℕ) {R : List (ℕ × Bool)} (hR : R ≠ []) :
    rep1 q R ≠ [] := by
  cases q with
  | zero => exact hR
  | succ q => simp only [rep1, ne_eq, reduceCtorEq, not_false_eq_true]

theorem bump_nonempty (R : List (ℕ × Bool)) : bump R ≠ [] := by
  cases R with
  | nil => simp only [bump, ne_eq, reduceCtorEq, not_false_eq_true]
  | cons p rest =>
    rcases p with ⟨d, c⟩
    simp only [bump, ne_eq, reduceCtorEq, not_false_eq_true]

theorem bump2_nonempty (R : List (ℕ × Bool)) : bump2 R ≠ [] :=
  bump_nonempty (bump R)

theorem strictNo0F_tail {p : ℕ × Bool} {rest : List (ℕ × Bool)}
    (h : StrictNo0F (p :: rest)) : StrictNo0F rest := by
  cases rest with
  | nil => trivial
  | cons r1 rs =>
    rcases p with ⟨d, c⟩
    cases d with
    | zero =>
      cases c with
      | false => exact False.elim h
      | true => exact h
    | succ d => exact h

theorem strictNo0F_imp_dlNo0F {R : List (ℕ × Bool)} (h : StrictNo0F R) : DLNo0F R := by
  cases R with
  | nil => trivial
  | cons p rest => exact strictNo0F_tail h

theorem strictNo0F_cons_pos (d : ℕ) (c : Bool) {R : List (ℕ × Bool)}
    (h : StrictNo0F R) : StrictNo0F ((d + 1, c) :: R) := by
  cases R with
  | nil => trivial
  | cons r1 rs => exact h

theorem strictNo0F_cons_zero_true {R : List (ℕ × Bool)}
    (h : StrictNo0F R) : StrictNo0F ((0, true) :: R) := by
  cases R with
  | nil => trivial
  | cons r1 rs => exact h

theorem strictNo0F_rep1 (q : ℕ) {R : List (ℕ × Bool)}
    (h : StrictNo0F R) : StrictNo0F (rep1 q R) := by
  induction q with
  | zero => exact h
  | succ q ih => exact strictNo0F_cons_pos 0 false ih

theorem strictNo0F_bump {R : List (ℕ × Bool)} (h : StrictNo0F R) :
    StrictNo0F (bump R) := by
  cases R with
  | nil => trivial
  | cons p rest =>
    rcases p with ⟨d, c⟩
    exact strictNo0F_cons_pos d c (strictNo0F_tail h)

theorem strictNo0F_bump2 {R : List (ℕ × Bool)} (h : StrictNo0F R) :
    StrictNo0F (bump2 R) :=
  strictNo0F_bump (strictNo0F_bump h)

/-! ## Machine-Independent Big-Step Relation (`EvalF`, `EvalDL`, `Disp`) -/

mutual
  /-- Big-step evaluation of `mD0 ((a, false) :: Ls) R ⊢⁺ mAL ((a + 1 + Δ, false) :: Ls) Z`
  (equivalently `FR0 ((a + 1) :: Ls) R ⊢⁺ BL0 ((a + 1 + Δ) :: Ls) Z` in `PairStackA`). -/
  inductive EvalF : ℕ → List (ℕ × Bool) → ℕ → List (ℕ × Bool) → Prop
    | nil :
        EvalF 1 [] 0 [(0, false)]
    | zero_false (R : List (ℕ × Bool)) :
        EvalF 1 ((0, false) :: R) 0 (bump2 R)
    | zero_true (R : List (ℕ × Bool)) :
        EvalF 1 ((0, true) :: R) 0 ((1, false) :: R)
    | one_false {n1 n2 Δ1 Δ : ℕ} {R Z1 Z : List (ℕ × Bool)} :
        EvalF n1 R Δ1 Z1 → Disp n2 (1 + Δ1) Z1 Δ Z →
        EvalF (n1 + n2 + 1) ((1, false) :: R) Δ Z
    | one_true (R : List (ℕ × Bool)) :
        EvalF 1 ((1, true) :: R) 0 ((0, true) :: bump R)
    | two_false {n1 n2 Δ1 Δ : ℕ} {R Z1 Z : List (ℕ × Bool)} :
        EvalF n1 (bump2 R) Δ1 Z1 → Disp n2 Δ1 Z1 Δ Z →
        EvalF (n1 + n2 + 1) ((2, false) :: R) Δ Z
    | two_true {n1 n2 Δ1 Δ : ℕ} {R Z1 Z : List (ℕ × Bool)} :
        EvalF n1 ((1, false) :: R) Δ1 Z1 → Disp n2 Δ1 Z1 Δ Z →
        EvalF (n1 + n2 + 1) ((2, true) :: R) Δ Z
    | ge3 {d n1 n2 Δ1 Δ : ℕ} {c : Bool} {R Z1 Z : List (ℕ × Bool)} :
        EvalDL n1 ((d, c) :: R) Δ1 Z1 → Disp n2 (1 + Δ1) Z1 Δ Z →
        EvalF (n1 + n2 + 1) ((d + 3, c) :: R) Δ Z

  /-- Big-step evaluation of `mBR ((a, false) :: Ls) ((d, c) :: R) ⊢⁺ mAL ((a + Δ, false) :: Ls) Z`
  (equivalently `DL0 (a :: Ls) ((d, c) :: R) ⊢⁺ BL0 ((a + Δ) :: Ls) Z` in `PairStackA`). -/
  inductive EvalDL : ℕ → List (ℕ × Bool) → ℕ → List (ℕ × Bool) → Prop
    | even_false {q n Δ : ℕ} {R Z : List (ℕ × Bool)} :
        EvalF n R Δ Z →
        EvalDL (n + 1) ((2 * q, false) :: R) (2 * q + 2 + Δ) Z
    | even_true (q : ℕ) (R : List (ℕ × Bool)) :
        EvalDL 1 ((2 * q, true) :: R) (2 * q + 2) (bump R)
    | odd_false {q n Δ : ℕ} {R Z : List (ℕ × Bool)} :
        EvalF n (bump2 R) Δ Z →
        EvalDL (n + 1) ((2 * q + 1, false) :: R) (2 * q + 1 + Δ) Z
    | odd_true {q n Δ : ℕ} {R Z : List (ℕ × Bool)} :
        EvalF n ((1, false) :: R) Δ Z →
        EvalDL (n + 1) ((2 * q + 1, true) :: R) (2 * q + 1 + Δ) Z

  /-- Big-step dispatch of `mAL ((v, false) :: (b, false) :: Ls) Z ⊢⁺ mAL ((b + Δ, false) :: Ls) Z'`
  for nonempty `Z`. -/
  inductive Disp : ℕ → ℕ → List (ℕ × Bool) → ℕ → List (ℕ × Bool) → Prop
    | rem0 {q n Δ : ℕ} {Z Z' : List (ℕ × Bool)} :
        EvalDL n (rep1 q Z) Δ Z' →
        Disp (n + 1) (3 * q) Z (2 + Δ) Z'
    | rem1 (q : ℕ) (Z : List (ℕ × Bool)) :
        Disp 1 (3 * q + 1) Z 0 ((0, true) :: rep1 q Z)
    | rem2 {q n Δ : ℕ} {Z Z' : List (ℕ × Bool)} :
        EvalF n (bump2 (rep1 q Z)) Δ Z' →
        Disp (n + 1) (3 * q + 2) Z (2 + Δ) Z'
end

/-! ## Non-Emptiness & `StrictNo0F` Preservation for `EvalF` / `EvalDL` / `Disp` -/

theorem evalF_out_props {n : ℕ} {R : List (ℕ × Bool)} {Δ : ℕ} {Z : List (ℕ × Bool)}
    (h : EvalF n R Δ Z) : Z ≠ [] ∧ (StrictNo0F R → StrictNo0F Z) := by
  exact
    @EvalF.rec
      (motive_1 := fun _ R _ Z _ => Z ≠ [] ∧ (StrictNo0F R → StrictNo0F Z))
      (motive_2 := fun _ R _ Z _ => Z ≠ [] ∧ (DLNo0F R → StrictNo0F Z))
      (motive_3 := fun _ _ Z _ Z' _ => Z' ≠ [] ∧ (StrictNo0F Z → StrictNo0F Z'))
      ⟨by simp only [ne_eq, reduceCtorEq, not_false_eq_true], fun _ => trivial⟩
      (fun R => ⟨bump2_nonempty R, fun hR => strictNo0F_bump2 (strictNo0F_tail hR)⟩)
      (fun R => ⟨by simp only [ne_eq, reduceCtorEq, not_false_eq_true],
        fun hR => strictNo0F_cons_pos 0 false (strictNo0F_tail hR)⟩)
      (fun _ _ ih1 ih2 => ⟨ih2.1, fun hR => ih2.2 (ih1.2 (strictNo0F_tail hR))⟩)
      (fun R => ⟨by simp only [ne_eq, reduceCtorEq, not_false_eq_true],
        fun hR => strictNo0F_cons_zero_true (strictNo0F_bump (strictNo0F_tail hR))⟩)
      (fun _ _ ih1 ih2 =>
        ⟨ih2.1, fun hR => ih2.2 (ih1.2 (strictNo0F_bump2 (strictNo0F_tail hR)))⟩)
      (fun _ _ ih1 ih2 =>
        ⟨ih2.1, fun hR => ih2.2 (ih1.2 (strictNo0F_cons_pos 0 false (strictNo0F_tail hR)))⟩)
      (fun _ _ ih1 ih2 => ⟨ih2.1, fun hR => ih2.2 (ih1.2 (strictNo0F_tail hR))⟩)
      (fun _ ih => ⟨ih.1, fun hR => ih.2 hR⟩)
      (fun _ R => ⟨bump_nonempty R, fun hR => strictNo0F_bump hR⟩)
      (fun _ ih => ⟨ih.1, fun hR => ih.2 (strictNo0F_bump2 hR)⟩)
      (fun _ ih => ⟨ih.1, fun hR => ih.2 (strictNo0F_cons_pos 0 false hR)⟩)
      (fun _ ih => ⟨ih.1, fun hZ => ih.2 (strictNo0F_imp_dlNo0F (strictNo0F_rep1 _ hZ))⟩)
      (fun q _ => ⟨by simp only [ne_eq, reduceCtorEq, not_false_eq_true],
        fun hZ => strictNo0F_cons_zero_true (strictNo0F_rep1 q hZ)⟩)
      (fun _ ih => ⟨ih.1, fun hZ => ih.2 (strictNo0F_bump2 (strictNo0F_rep1 _ hZ))⟩)
      n R Δ Z h

theorem evalF_out_nonempty {n : ℕ} {R : List (ℕ × Bool)} {Δ : ℕ} {Z : List (ℕ × Bool)}
    (h : EvalF n R Δ Z) : Z ≠ [] :=
  (evalF_out_props h).1

theorem evalF_preserves_no0f {n : ℕ} {R : List (ℕ × Bool)} {Δ : ℕ} {Z : List (ℕ × Bool)}
    (h : EvalF n R Δ Z) (hR : StrictNo0F R) : StrictNo0F Z :=
  (evalF_out_props h).2 hR

/-! ## Bounded-Horizon Safety Helpers & Deterministic Stride Loops -/

/-- `SafeSteps k s` means `isDoor (runTot j s) = false` for all `j < k`. -/
def SafeSteps (k : ℕ) (s : State484) : Prop :=
  ∀ j : ℕ, j < k → isDoor (runTot j s) = false

theorem safeSteps_zero (s : State484) : SafeSteps 0 s :=
  fun _ hj => False.elim (Nat.not_lt_zero _ hj)

theorem safeSteps_mono {k1 k2 : ℕ} {s : State484} (hle : k1 ≤ k2) (h : SafeSteps k2 s) :
    SafeSteps k1 s :=
  fun j hj => h j (Nat.lt_of_lt_of_le hj hle)

theorem safeSteps_step {k : ℕ} {s : State484}
    (hd : isDoor s = false) (hnext : SafeSteps k (stepTot s)) :
    SafeSteps (k + 1) s := by
  intro j hj
  cases j with
  | zero => exact hd
  | succ j' => exact hnext j' (Nat.lt_of_succ_lt_succ hj)

theorem safeSteps_trans {a b : ℕ} {s : State484}
    (ha : SafeSteps a s) (hb : SafeSteps b (runTot a s)) :
    SafeSteps (a + b) s := by
  intro j hj
  rcases Nat.lt_or_ge j a with hlt | hge
  · exact ha j hlt
  · have hsub : j - a < b := by omega
    have hsplit : j = a + (j - a) := by omega
    rw [hsplit, runTot_add]
    exact hb (j - a) hsub

/-- General horizon-composition lemma: if `s` steps safely for `c` steps to `s1` (`c > 0`),
and `s1` is safe for remaining budget `k - c`, then `s` is safe for `k`. -/
theorem safeSteps_of_prefix {k c : ℕ} {s s1 : State484}
    (hpre : SafeSteps c s) (hrun : runTot c s = s1) (hrem : SafeSteps (k - c) s1) :
    SafeSteps k s := by
  rcases Nat.lt_or_ge c k with hlt | hge
  · have hsum : c + (k - c) = k := by omega
    rw [← hsum]
    refine safeSteps_trans hpre ?_
    rw [hrun]
    exact hrem
  · exact safeSteps_mono hge hpre

/-- Helper to combine a safe prefix `c` with a remaining-horizon outcome (either safe for `k - c`
or an exit within `k - c`). -/
theorem mAL_drain_3q (q r : ℕ) (Ls R : List (ℕ × Bool)) :
    SafeSteps (2 * q) ⟨.mAL, (3 * q + r, false) :: Ls, R⟩ ∧
    runTot (2 * q) ⟨.mAL, (3 * q + r, false) :: Ls, R⟩ =
      ⟨.mAL, (r, false) :: Ls, rep1 q R⟩ := by
  induction q generalizing R with
  | zero =>
    exact ⟨safeSteps_zero _, by simp only [Nat.mul_zero, Nat.zero_add]; rfl⟩
  | succ q ih =>
    have hstep1 : stepTot ⟨.mAL, (3 * (q + 1) + r, false) :: Ls, R⟩ =
        ⟨.mC0, (3 * q + r, false) :: Ls, (0, false) :: R⟩ := by
      have heq : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
      rw [heq]; rfl
    have hstep2 : stepTot ⟨.mC0, (3 * q + r, false) :: Ls, (0, false) :: R⟩ =
        ⟨.mAL, (3 * q + r, false) :: Ls, (1, false) :: R⟩ := rfl
    have hd1 : isDoor ⟨.mAL, (3 * (q + 1) + r, false) :: Ls, R⟩ = false := by
      have heq : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
      rw [heq]; rfl
    have hd2 : isDoor ⟨.mC0, (3 * q + r, false) :: Ls, (0, false) :: R⟩ = false := rfl
    rcases ih ((1, false) :: R) with ⟨hs, hr⟩
    have h2 : 2 * (q + 1) = 2 + 2 * q := by omega
    have hpre2 : SafeSteps 2 ⟨.mAL, (3 * (q + 1) + r, false) :: Ls, R⟩ := by
      refine safeSteps_step hd1 ?_
      rw [hstep1]
      exact safeSteps_step hd2 (safeSteps_zero _)
    have hrun2 : runTot 2 ⟨.mAL, (3 * (q + 1) + r, false) :: Ls, R⟩ =
        ⟨.mAL, (3 * q + r, false) :: Ls, (1, false) :: R⟩ := by
      change stepTot (stepTot ⟨.mAL, (3 * (q + 1) + r, false) :: Ls, R⟩) = _
      rw [hstep1, hstep2]
    constructor
    · rw [h2]
      refine safeSteps_trans hpre2 ?_
      rw [hrun2]
      exact hs
    · rw [h2, runTot_add, hrun2, hr, rep1_cons_one]
      rfl

theorem mBR_drain_2q (q r a : ℕ) (c : Bool) (Ls R : List (ℕ × Bool)) :
    SafeSteps (2 * q) ⟨.mBR, (a, false) :: Ls, (2 * q + r, c) :: R⟩ ∧
    runTot (2 * q) ⟨.mBR, (a, false) :: Ls, (2 * q + r, c) :: R⟩ =
      ⟨.mBR, (a + 2 * q, false) :: Ls, (r, c) :: R⟩ := by
  induction q generalizing a with
  | zero =>
    exact ⟨safeSteps_zero _, by simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; rfl⟩
  | succ q ih =>
    have hstep1 : stepTot ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ =
        ⟨.mDR, (a + 1, false) :: Ls, (2 * q + r + 1, c) :: R⟩ := by
      have heq : 2 * (q + 1) + r = (2 * q + r + 1) + 1 := by omega
      rw [heq]; rfl
    have hstep2 : stepTot ⟨.mDR, (a + 1, false) :: Ls, (2 * q + r + 1, c) :: R⟩ =
        ⟨.mBR, (a + 2, false) :: Ls, (2 * q + r, c) :: R⟩ := rfl
    have hd1 : isDoor ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ = false := rfl
    have hd2 : isDoor ⟨.mDR, (a + 1, false) :: Ls, (2 * q + r + 1, c) :: R⟩ = false := rfl
    rcases ih (a + 2) with ⟨hs, hr⟩
    have h2 : 2 * (q + 1) = 2 + 2 * q := by omega
    have ha : a + 2 + 2 * q = a + 2 * (q + 1) := by omega
    have hpre2 : SafeSteps 2 ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ := by
      refine safeSteps_step hd1 ?_
      rw [hstep1]
      exact safeSteps_step hd2 (safeSteps_zero _)
    have hrun2 : runTot 2 ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ =
        ⟨.mBR, (a + 2, false) :: Ls, (2 * q + r, c) :: R⟩ := by
      change stepTot (stepTot ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩) = _
      rw [hstep1, hstep2]
    constructor
    · have hgoal : SafeSteps (2 + 2 * q) ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ := by
        refine safeSteps_trans hpre2 ?_
        rw [hrun2]
        exact hs
      exact fun j hj => hgoal j (by omega)
    · rw [show runTot (2 * (q + 1)) ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ =
          runTot (2 + 2 * q) ⟨.mBR, (a, false) :: Ls, (2 * (q + 1) + r, c) :: R⟩ from
          congrArg (fun n => runTot n _) h2, runTot_add, hrun2, hr, ha]

theorem mBR_bump2_nonempty (a : ℕ) (Ls R : List (ℕ × Bool)) (hR : R ≠ []) :
    SafeSteps 2 ⟨.mBR, (a, false) :: Ls, bump2 R⟩ ∧
    runTot 2 ⟨.mBR, (a, false) :: Ls, bump2 R⟩ = ⟨.mBR, (a + 2, false) :: Ls, R⟩ := by
  cases R with
  | nil => exact False.elim (hR rfl)
  | cons p rest =>
    rcases p with ⟨d, c⟩
    constructor
    · exact safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
    · rfl

/-! ## Constructive Bounded-Horizon `tm484 ↔ EvalF` Bisimulation -/

/-- Horizon outcome for `mD0 ((a, false) :: Ls) R`: either safe for `k` steps, or reaches
`mAL ((a + 1 + Δ, false) :: Ls) Z` in `0 < m ≤ k` safe steps with `EvalF n R Δ Z`. -/
def D0Outcome (k a : ℕ) (Ls R : List (ℕ × Bool)) : Prop :=
  SafeSteps k ⟨.mD0, (a, false) :: Ls, R⟩ ∨
  ∃ m n Δ Z, m ≤ k ∧ 0 < m ∧ EvalF n R Δ Z ∧
    SafeSteps m ⟨.mD0, (a, false) :: Ls, R⟩ ∧
    runTot m ⟨.mD0, (a, false) :: Ls, R⟩ = ⟨.mAL, (a + 1 + Δ, false) :: Ls, Z⟩

/-- Horizon outcome for `mBR ((a, false) :: Ls) ((d, c) :: R)`. -/
def BROutcome (k a d : ℕ) (c : Bool) (Ls R : List (ℕ × Bool)) : Prop :=
  SafeSteps k ⟨.mBR, (a, false) :: Ls, (d, c) :: R⟩ ∨
  ∃ m n Δ Z, m ≤ k ∧ 0 < m ∧ EvalDL n ((d, c) :: R) Δ Z ∧
    SafeSteps m ⟨.mBR, (a, false) :: Ls, (d, c) :: R⟩ ∧
    runTot m ⟨.mBR, (a, false) :: Ls, (d, c) :: R⟩ = ⟨.mAL, (a + Δ, false) :: Ls, Z⟩

/-- Horizon outcome for `mDR ((0, false) :: (b, false) :: Ls) R` (exact `bump2 R` bisimulation!). -/
def DR0Outcome (k b : ℕ) (Ls R : List (ℕ × Bool)) : Prop :=
  SafeSteps k ⟨.mDR, (0, false) :: (b, false) :: Ls, R⟩ ∨
  ∃ m n Δ Z, m ≤ k ∧ 0 < m ∧ EvalF n (bump2 R) Δ Z ∧
    SafeSteps m ⟨.mDR, (0, false) :: (b, false) :: Ls, R⟩ ∧
    runTot m ⟨.mDR, (0, false) :: (b, false) :: Ls, R⟩ = ⟨.mAL, (b + Δ, false) :: Ls, Z⟩

/-- Horizon outcome for `mAL ((v, false) :: (b, false) :: Ls) Z` (`Z ≠ []`). -/
def DispOutcome (k v b : ℕ) (Ls Z : List (ℕ × Bool)) : Prop :=
  SafeSteps k ⟨.mAL, (v, false) :: (b, false) :: Ls, Z⟩ ∨
  ∃ m n Δ Z', m ≤ k ∧ 0 < m ∧ Disp n v Z Δ Z' ∧
    SafeSteps m ⟨.mAL, (v, false) :: (b, false) :: Ls, Z⟩ ∧
    runTot m ⟨.mAL, (v, false) :: (b, false) :: Ls, Z⟩ = ⟨.mAL, (b + Δ, false) :: Ls, Z'⟩

def HorizonProp (k : ℕ) : Prop :=
  (∀ a Ls R, D0Outcome k a Ls R) ∧
  (∀ a Ls d c R, BROutcome k a d c Ls R) ∧
  (∀ b Ls R, DR0Outcome k b Ls R) ∧
  (∀ v b Ls Z, Z ≠ [] → DispOutcome k v b Ls Z)

/-- Main constructive bounded-horizon `tm484 ↔ EvalF` bisimulation theorem. -/
theorem horizon_bisim : ∀ k : ℕ, HorizonProp k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    -- Break out the 4 components cleanly.
    have hD0 : ∀ a Ls R, D0Outcome k a Ls R := by
      intro a Ls R
      cases R with
      | nil =>
        -- mD0 (a::Ls) [] ⊢² mAL ((a+1)::Ls) [(0, false)]
        have hs : SafeSteps 2 ⟨.mD0, (a, false) :: Ls, []⟩ :=
          safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hs)
        · exact Or.inr ⟨2, 1, 0, [(0, false)], hge, by omega, EvalF.nil, hs, rfl⟩
      | cons r0 R' =>
        rcases r0 with ⟨d, c⟩
        cases d with
        | zero =>
          cases c with
          | false =>
            have hs : SafeSteps 2 ⟨.mD0, (a, false) :: Ls, (0, false) :: R'⟩ :=
              safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
            rcases Nat.lt_or_ge k 2 with hlt | hge
            · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hs)
            · exact Or.inr ⟨2, 1, 0, bump2 R', hge, by omega, EvalF.zero_false R', hs, rfl⟩
          | true =>
            have hs : SafeSteps 2 ⟨.mD0, (a, false) :: Ls, (0, true) :: R'⟩ :=
              safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
            rcases Nat.lt_or_ge k 2 with hlt | hge
            · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hs)
            · exact Or.inr ⟨2, 1, 0, (1, false) :: R', hge, by omega, EvalF.zero_true R', hs, rfl⟩
        | succ d1 =>
          cases d1 with
          | zero =>
            cases c with
            | false =>
              -- mD0 (a::Ls) ((1,F)::R') ⊢¹ mD0 (0::(a+1)::Ls) R'
              have hpre : SafeSteps 1 ⟨.mD0, (a, false) :: Ls, (1, false) :: R'⟩ :=
                safeSteps_step rfl (safeSteps_zero _)
              rcases Nat.lt_or_ge k 1 with hlt | hge
              · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
              · rcases (ih (k - 1) (by omega)).1 0 ((a + 1, false) :: Ls) R' with hs1 | ⟨m1, n1, Δ1,
                    Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
                · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
                · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
                  have hlt2 : k - 1 - m1 < k := by omega
                  rcases (ih (k - 1 - m1) hlt2).2.2.2 (1 + Δ1) (a + 1) Ls Z1 hne1 with hs2 | ⟨m2,
                      n2, Δ2, Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
                  · refine Or.inl ?_
                    have h12 : SafeSteps (1 + m1) ⟨.mD0, (a, false) :: Ls, (1, false) :: R'⟩ :=
                      safeSteps_trans hpre hs1
                    have hr12 : runTot (1 + m1) ⟨.mD0, (a, false) :: Ls, (1, false) :: R'⟩ =
                        ⟨.mAL, (1 + Δ1, false) :: (a + 1, false) :: Ls, Z1⟩ := by
                      rw [runTot_add]; exact hr1
                    have hsub : k - (1 + m1) = k - 1 - m1 := by omega
                    rw [← hsub] at hs2
                    exact safeSteps_of_prefix h12 hr12 hs2
                  · refine Or.inr ⟨1 + m1 + m2, n1 + n2 + 1, Δ2, Z2, by omega, by omega,
                      EvalF.one_false hev1 hdp2, ?_, ?_⟩
                    · refine safeSteps_trans (safeSteps_trans hpre hs1) ?_
                      rw [runTot_add]
                      change SafeSteps m2 (runTot m1 ⟨.mD0, (0, false) :: (a + 1, false) :: Ls, R'⟩)
                      rw [hr1]
                      exact hs2
                    · rw [runTot_add, runTot_add]
                      change runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (a + 1, false) :: Ls,
                          R'⟩) = _
                      rw [hr1]
                      exact hr2
            | true =>
              -- mD0 (a::Ls) ((1,T)::R') ⊢³ mAL ((a+1)::Ls) ((0,T) :: bump R')
              have hs : SafeSteps 3 ⟨.mD0, (a, false) :: Ls, (1, true) :: R'⟩ :=
                safeSteps_step rfl (safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _)))
              have hr : runTot 3 ⟨.mD0, (a, false) :: Ls, (1, true) :: R'⟩ =
                  ⟨.mAL, (a + 1, false) :: Ls, (0, true) :: bump R'⟩ := by
                cases R' with
                | nil => rfl
                | cons p rs => rcases p with ⟨dd, cc⟩; rfl
              rcases Nat.lt_or_ge k 3 with hlt | hge
              · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hs)
              · exact Or.inr ⟨3, 1, 0, (0, true) :: bump R', hge, by omega, EvalF.one_true R', hs,
                                                                   hr⟩
          | succ d2 =>
            cases d2 with
            | zero =>
              cases c with
              | false =>
                -- mD0 (a::Ls) ((2,F)::R') ⊢² mDR (0::0::(a+1)::Ls) R'
                have hpre : SafeSteps 2 ⟨.mD0, (a, false) :: Ls, (2, false) :: R'⟩ :=
                  safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
                rcases Nat.lt_or_ge k 2 with hlt | hge
                · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
                · rcases (ih (k - 2) (by omega)).2.2.1 0 ((a + 1, false) :: Ls) R' with hs1 | ⟨m1,
                      n1, Δ1, Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
                  · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
                  · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
                    have hr1' : runTot m1 ⟨.mDR, (0, false) :: (0, false) :: (a + 1, false) :: Ls,
                        R'⟩ =
                        ⟨.mAL, (Δ1, false) :: (a + 1, false) :: Ls, Z1⟩ := by
                      simpa only [Nat.zero_add] using hr1
                    rcases (ih (k - 2 - m1) (by omega)).2.2.2 Δ1 (a + 1) Ls Z1 hne1 with hs2 | ⟨m2,
                        n2, Δ2, Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
                    · refine Or.inl ?_
                      have h12 : SafeSteps (2 + m1) ⟨.mD0, (a, false) :: Ls, (2, false) :: R'⟩ :=
                        safeSteps_trans hpre hs1
                      have hr12 : runTot (2 + m1) ⟨.mD0, (a, false) :: Ls, (2, false) :: R'⟩ =
                          ⟨.mAL, (Δ1, false) :: (a + 1, false) :: Ls, Z1⟩ := by
                        rw [runTot_add]; exact hr1'
                      have hsub : k - (2 + m1) = k - 2 - m1 := by omega
                      rw [← hsub] at hs2
                      exact safeSteps_of_prefix h12 hr12 hs2
                    · refine Or.inr ⟨2 + m1 + m2, n1 + n2 + 1, Δ2, Z2, by omega, by omega,
                        EvalF.two_false hev1 hdp2, ?_, ?_⟩
                      · refine safeSteps_trans (safeSteps_trans hpre hs1) ?_
                        rw [runTot_add]
                        change SafeSteps m2 (runTot m1 ⟨.mDR, (0, false) :: (0, false) :: (a + 1,
                            false) :: Ls, R'⟩)
                        rw [hr1']; exact hs2
                      · rw [runTot_add, runTot_add]
                        change runTot m2 (runTot m1 ⟨.mDR, (0, false) :: (0, false) :: (a + 1,
                            false) :: Ls, R'⟩) = _
                        rw [hr1']; exact hr2
              | true =>
                -- mD0 (a::Ls) ((2,T)::R') ⊢² mD0 (0::0::(a+1)::Ls) R'
                -- which steps via EvalF R' -> Disp (1+Δ1) -> Disp Δ2!
                have hpre : SafeSteps 2 ⟨.mD0, (a, false) :: Ls, (2, true) :: R'⟩ :=
                  safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
                rcases Nat.lt_or_ge k 2 with hlt | hge
                · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
                · rcases (ih (k - 2) (by omega)).1 0 ((0, false) :: (a + 1,
                      false) :: Ls) R' with hs1 | ⟨m1, n1, Δ1, Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
                  · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
                  · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
                    rcases (ih (k - 2 - m1) (by omega)).2.2.2 (1 + Δ1) 0 ((a + 1,
                        false) :: Ls) Z1 hne1 with hs2 | ⟨m2, n2, Δ2, Z2, hm2le, hm2pos, hdp2, hs2,
                        hr2⟩
                    · refine Or.inl ?_
                      have h12 : SafeSteps (2 + m1) ⟨.mD0, (a, false) :: Ls, (2, true) :: R'⟩ :=
                        safeSteps_trans hpre hs1
                      have hr12 : runTot (2 + m1) ⟨.mD0, (a, false) :: Ls, (2, true) :: R'⟩ =
                          ⟨.mAL, (1 + Δ1, false) :: (0, false) :: (a + 1, false) :: Ls, Z1⟩ := by
                        rw [runTot_add]; exact hr1
                      have hsub : k - (2 + m1) = k - 2 - m1 := by omega
                      rw [← hsub] at hs2
                      exact safeSteps_of_prefix h12 hr12 hs2
                    · have hev12 : EvalF (n1 + n2 + 1) ((1, false) :: R') Δ2 Z2 :=
                        EvalF.one_false hev1 hdp2
                      have hne2 : Z2 ≠ [] := evalF_out_nonempty hev12
                      have hr2' : runTot m2 ⟨.mAL, (1 + Δ1, false) :: (0, false) :: (a + 1,
                          false) :: Ls, Z1⟩ =
                          ⟨.mAL, (Δ2, false) :: (a + 1, false) :: Ls, Z2⟩ := by
                        simpa only [Nat.zero_add] using hr2
                      rcases (ih (k - 2 - m1 - m2) (by omega)).2.2.2 Δ2
                          (a + 1) Ls Z2 hne2 with hs3 | ⟨m3, n3, Δ3, Z3, hm3le, hm3pos, hdp3, hs3,
                          hr3⟩
                      · refine Or.inl ?_
                        have h12 : SafeSteps (2 + m1) ⟨.mD0, (a, false) :: Ls, (2, true) :: R'⟩ :=
                          safeSteps_trans hpre hs1
                        have h123 : SafeSteps (2 + m1 + m2) ⟨.mD0, (a, false) :: Ls, (2,
                            true) :: R'⟩ := by
                          refine safeSteps_trans h12 ?_
                          rw [runTot_add]
                          change SafeSteps m2 (runTot m1 ⟨.mD0, (0, false) :: (0, false) :: (a + 1,
                              false) :: Ls, R'⟩)
                          rw [hr1]; exact hs2
                        have hr123 : runTot (2 + m1 + m2) ⟨.mD0, (a, false) :: Ls, (2,
                            true) :: R'⟩ =
                            ⟨.mAL, (Δ2, false) :: (a + 1, false) :: Ls, Z2⟩ := by
                          rw [runTot_add, runTot_add]
                          change runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (0, false) :: (a + 1,
                              false) :: Ls, R'⟩) = _
                          rw [hr1]; exact hr2'
                        have hsub : k - (2 + m1 + m2) = k - 2 - m1 - m2 := by omega
                        rw [← hsub] at hs3
                        exact safeSteps_of_prefix h123 hr123 hs3
                      · refine Or.inr ⟨2 + m1 + m2 + m3, (n1 + n2 + 1) + n3 + 1, Δ3, Z3, by omega,
                            by omega,
                          EvalF.two_true hev12 hdp3, ?_, ?_⟩
                        · have h12 : SafeSteps (2 + m1) ⟨.mD0, (a, false) :: Ls, (2, true) :: R'⟩ :=
                            safeSteps_trans hpre hs1
                          have h123 : SafeSteps (2 + m1 + m2) ⟨.mD0, (a, false) :: Ls, (2,
                              true) :: R'⟩ := by
                            refine safeSteps_trans h12 ?_
                            rw [runTot_add]
                            change SafeSteps m2 (runTot m1 ⟨.mD0, (0, false) :: (0,
                                false) :: (a + 1, false) :: Ls, R'⟩)
                            rw [hr1]; exact hs2
                          refine safeSteps_trans h123 ?_
                          rw [runTot_add, runTot_add]
                          change SafeSteps m3 (runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (0,
                              false) :: (a + 1, false) :: Ls, R'⟩))
                          rw [hr1, hr2']; exact hs3
                        · rw [runTot_add, runTot_add, runTot_add]
                          change runTot m3 (runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (0,
                              false) :: (a + 1, false) :: Ls, R'⟩)) = _
                          rw [hr1, hr2']; exact hr3
            | succ d3 =>
              -- mD0 (a::Ls) ((d3+3, c)::R') ⊢² mBR (1::(a+1)::Ls) ((d3, c)::R')
              have hpre : SafeSteps 2 ⟨.mD0, (a, false) :: Ls, (d3 + 3, c) :: R'⟩ :=
                safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
              rcases Nat.lt_or_ge k 2 with hlt | hge
              · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
              · rcases (ih (k - 2) (by omega)).2.1 1 ((a + 1, false) :: Ls) d3 c R' with hs1 | ⟨m1,
                    n1, Δ1, Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
                · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
                · have hne1 : Z1 ≠ [] := by
                    -- EvalDL always produces nonempty Z1
                    cases hev1 with
                    | even_false hf => exact evalF_out_nonempty hf
                    | even_true _ => exact bump_nonempty _
                    | odd_false hf => exact evalF_out_nonempty hf
                    | odd_true hf => exact evalF_out_nonempty hf
                  rcases (ih (k - 2 - m1) (by omega)).2.2.2 (1 + Δ1)
                      (a + 1) Ls Z1 hne1 with hs2 | ⟨m2, n2, Δ2, Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
                  · refine Or.inl ?_
                    have h12 : SafeSteps (2 + m1) ⟨.mD0, (a, false) :: Ls, (d3 + 3, c) :: R'⟩ :=
                      safeSteps_trans hpre hs1
                    have hr12 : runTot (2 + m1) ⟨.mD0, (a, false) :: Ls, (d3 + 3, c) :: R'⟩ =
                        ⟨.mAL, (1 + Δ1, false) :: (a + 1, false) :: Ls, Z1⟩ := by
                      rw [runTot_add]; exact hr1
                    have hsub : k - (2 + m1) = k - 2 - m1 := by omega
                    rw [← hsub] at hs2
                    exact safeSteps_of_prefix h12 hr12 hs2
                  · refine Or.inr ⟨2 + m1 + m2, n1 + n2 + 1, Δ2, Z2, by omega, by omega,
                      EvalF.ge3 hev1 hdp2, ?_, ?_⟩
                    · refine safeSteps_trans (safeSteps_trans hpre hs1) ?_
                      rw [runTot_add]
                      change SafeSteps m2 (runTot m1 ⟨.mBR, (1, false) :: (a + 1, false) :: Ls, (d3,
                          c) :: R'⟩)
                      rw [hr1]; exact hs2
                    · rw [runTot_add, runTot_add]
                      change runTot m2 (runTot m1 ⟨.mBR, (1, false) :: (a + 1, false) :: Ls, (d3,
                          c) :: R'⟩) = _
                      rw [hr1]; exact hr2
    have hBR : ∀ a Ls d c R, BROutcome k a d c Ls R := by
      intro a Ls d c R
      set q := d / 2
      set r := d % 2
      have hdiv : d = 2 * q + r := by omega
      have hr_lt : r = 0 ∨ r = 1 := by omega
      rcases hr_lt with hr0 | hr1
      · have hdq : d = 2 * q := by omega
        rw [hdq]
        rcases mBR_drain_2q q 0 a c Ls R with ⟨hdr_s, hdr_r⟩
        have hdr_s' : SafeSteps (2 * q) ⟨.mBR, (a, false) :: Ls, (2 * q, c) :: R⟩ := by
          simpa only [Nat.add_zero] using hdr_s
        have hdr_r' : runTot (2 * q) ⟨.mBR, (a, false) :: Ls, (2 * q, c) :: R⟩ =
            ⟨.mBR, (a + 2 * q, false) :: Ls, (0, c) :: R⟩ := by
          simpa only [Nat.add_zero] using hdr_r
        cases c with
        | false =>
          -- +1 step to mD0 ((a+2q+1)::Ls) R
          have hpre : SafeSteps (2 * q + 1) ⟨.mBR, (a, false) :: Ls, (2 * q, false) :: R⟩ := by
            refine safeSteps_trans hdr_s' ?_
            rw [hdr_r']
            exact safeSteps_step rfl (safeSteps_zero _)
          have hrun : runTot (2 * q + 1) ⟨.mBR, (a, false) :: Ls, (2 * q, false) :: R⟩ =
              ⟨.mD0, (a + 2 * q + 1, false) :: Ls, R⟩ := by
            rw [runTot_add, hdr_r']; rfl
          rcases Nat.lt_or_ge k (2 * q + 1) with hlt | hge
          · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
          · rcases (ih (k - (2 * q + 1)) (by omega)).1 (a + 2 * q + 1) Ls R with hs1 | ⟨m1, n1, Δ1,
                Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
            · exact Or.inl (safeSteps_of_prefix hpre hrun hs1)
            · refine Or.inr ⟨2 * q + 1 + m1, n1 + 1, 2 * q + 2 + Δ1, Z1, by omega, by omega,
                EvalDL.even_false hev1, ?_, ?_⟩
              · refine safeSteps_trans hpre ?_
                rw [hrun]; exact hs1
              · rw [runTot_add, hrun, hr1]
                have ha : a + 2 * q + 1 + 1 + Δ1 = a + (2 * q + 2 + Δ1) := by omega
                rw [ha]
        | true =>
          -- +2 steps to mAL ((a+2q+2)::Ls) (bump R)
          have hpre : SafeSteps (2 * q + 2) ⟨.mBR, (a, false) :: Ls, (2 * q, true) :: R⟩ := by
            refine safeSteps_trans hdr_s' ?_
            rw [hdr_r']
            exact safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
          have hrun : runTot (2 * q + 2) ⟨.mBR, (a, false) :: Ls, (2 * q, true) :: R⟩ =
              ⟨.mAL, (a + (2 * q + 2), false) :: Ls, bump R⟩ := by
            rw [runTot_add, hdr_r']
            have ha : a + 2 * q + 1 + 1 = a + (2 * q + 2) := by omega
            change ({
                mode := .mAL
                L := (a + 2 * q + 1 + 1, false) :: Ls
                R := bump R } : State484) = _
            rw [ha]
          rcases Nat.lt_or_ge k (2 * q + 2) with hlt | hge
          · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
          · exact Or.inr ⟨2 * q + 2, 1, 2 * q + 2, bump R, hge, by omega,
              EvalDL.even_true q R, hpre, hrun⟩
      · have hdq : d = 2 * q + 1 := by omega
        rw [hdq]
        rcases mBR_drain_2q q 1 a c Ls R with ⟨hdr_s, hdr_r⟩
        cases c with
        | false =>
          -- +2 steps to mDR (0::(a+2q+1)::Ls) R
          have hpre : SafeSteps (2 * q + 2) ⟨.mBR, (a, false) :: Ls, (2 * q + 1, false) :: R⟩ := by
            refine safeSteps_trans hdr_s ?_
            rw [hdr_r]
            exact safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
          have hrun : runTot (2 * q + 2) ⟨.mBR, (a, false) :: Ls, (2 * q + 1, false) :: R⟩ =
              ⟨.mDR, (0, false) :: (a + 2 * q + 1, false) :: Ls, R⟩ := by
            rw [runTot_add, hdr_r]; rfl
          rcases Nat.lt_or_ge k (2 * q + 2) with hlt | hge
          · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
          · rcases (ih (k - (2 * q + 2)) (by omega)).2.2.1 (a + 2 * q + 1) Ls R with hs1 | ⟨m1, n1,
                Δ1, Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
            · exact Or.inl (safeSteps_of_prefix hpre hrun hs1)
            · refine Or.inr ⟨2 * q + 2 + m1, n1 + 1, 2 * q + 1 + Δ1, Z1, by omega, by omega,
                EvalDL.odd_false hev1, ?_, ?_⟩
              · refine safeSteps_trans hpre ?_
                rw [hrun]; exact hs1
              · rw [runTot_add, hrun, hr1]
                have ha : a + 2 * q + 1 + Δ1 = a + (2 * q + 1 + Δ1) := by omega
                rw [ha]
        | true =>
          -- +2 steps to mD0 (0::(a+2q+1)::Ls) R -> EvalF R -> Disp (1+Δ1)
          have hpre : SafeSteps (2 * q + 2) ⟨.mBR, (a, false) :: Ls, (2 * q + 1, true) :: R⟩ := by
            refine safeSteps_trans hdr_s ?_
            rw [hdr_r]
            exact safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _))
          have hrun : runTot (2 * q + 2) ⟨.mBR, (a, false) :: Ls, (2 * q + 1, true) :: R⟩ =
              ⟨.mD0, (0, false) :: (a + 2 * q + 1, false) :: Ls, R⟩ := by
            rw [runTot_add, hdr_r]; rfl
          rcases Nat.lt_or_ge k (2 * q + 2) with hlt | hge
          · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
          · rcases (ih (k - (2 * q + 2)) (by omega)).1 0 ((a + 2 * q + 1,
                false) :: Ls) R with hs1 | ⟨m1, n1, Δ1, Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
            · exact Or.inl (safeSteps_of_prefix hpre hrun hs1)
            · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
              rcases (ih (k - (2 * q + 2) - m1) (by omega)).2.2.2 (1 + Δ1)
                  (a + 2 * q + 1) Ls Z1 hne1 with hs2 | ⟨m2, n2, Δ2, Z2, hm2le, hm2pos, hdp2, hs2,
                  hr2⟩
              · refine Or.inl ?_
                have h12 : SafeSteps (2 * q + 2 + m1) ⟨.mBR, (a, false) :: Ls, (2 * q + 1,
                    true) :: R⟩ := by
                  refine safeSteps_trans hpre ?_
                  rw [hrun]; exact hs1
                have hr12 : runTot (2 * q + 2 + m1) ⟨.mBR, (a, false) :: Ls, (2 * q + 1,
                    true) :: R⟩ =
                    ⟨.mAL, (1 + Δ1, false) :: (a + 2 * q + 1, false) :: Ls, Z1⟩ := by
                  rw [runTot_add, hrun]; exact hr1
                have hsub : k - (2 * q + 2 + m1) = k - (2 * q + 2) - m1 := by omega
                rw [← hsub] at hs2
                exact safeSteps_of_prefix h12 hr12 hs2
              · refine Or.inr ⟨2 * q + 2 + m1 + m2, (n1 + n2 + 1) + 1, 2 * q + 1 + Δ2, Z2, by omega,
                    by omega,
                  EvalDL.odd_true (EvalF.one_false hev1 hdp2), ?_, ?_⟩
                · have h12 : SafeSteps (2 * q + 2 + m1) ⟨.mBR, (a, false) :: Ls, (2 * q + 1,
                      true) :: R⟩ := by
                    refine safeSteps_trans hpre ?_
                    rw [hrun]; exact hs1
                  refine safeSteps_trans h12 ?_
                  rw [runTot_add, hrun, hr1]; exact hs2
                · rw [runTot_add, runTot_add, hrun, hr1, hr2]
                  have ha : a + 2 * q + 1 + Δ2 = a + (2 * q + 1 + Δ2) := by omega
                  rw [ha]
    have hDR0 : ∀ b Ls R, DR0Outcome k b Ls R := by
      intro b Ls R
      cases R with
      | nil =>
        -- mDR (0::b::Ls) [] ⊢³ mAL (b::Ls) [(0,T), (0,F)], matching EvalF (bump2 []) = EvalF
        -- [(1,F)]!
        have hs : SafeSteps 3 ⟨.mDR, (0, false) :: (b, false) :: Ls, []⟩ :=
          safeSteps_step rfl (safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _)))
        have hev : EvalF 3 (bump2 []) 0 [(0, true), (0, false)] := by
          change EvalF (1 + 1 + 1) [(1, false)] 0 [(0, true), (0, false)]
          exact EvalF.one_false EvalF.nil (Disp.rem1 0 [(0, false)])
        rcases Nat.lt_or_ge k 3 with hlt | hge
        · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hs)
        · exact Or.inr ⟨3, 3, 0, [(0, true), (0, false)], hge, by omega, hev, hs, rfl⟩
      | cons r0 R' =>
        rcases r0 with ⟨d, c⟩
        cases d with
        | zero =>
          cases c with
          | false =>
            -- mDR (0::b::Ls) ((0,F)::R') ⊢¹ mDR (0::0::b::Ls) R', matching EvalF ((2,F)::R')!
            have hpre : SafeSteps 1 ⟨.mDR, (0, false) :: (b, false) :: Ls, (0, false) :: R'⟩ :=
              safeSteps_step rfl (safeSteps_zero _)
            rcases Nat.lt_or_ge k 1 with hlt | hge
            · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
            · rcases (ih (k - 1) (by omega)).2.2.1 0 ((b, false) :: Ls) R' with hs1 | ⟨m1, n1, Δ1,
                  Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
              · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
              · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
                have hr1' : runTot m1 ⟨.mDR, (0, false) :: (0, false) :: (b, false) :: Ls, R'⟩ =
                    ⟨.mAL, (Δ1, false) :: (b, false) :: Ls, Z1⟩ := by
                  simpa only [Nat.zero_add] using hr1
                rcases (ih (k - 1 - m1) (by omega)).2.2.2 Δ1 b Ls Z1 hne1 with hs2 | ⟨m2, n2, Δ2,
                    Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
                · refine Or.inl ?_
                  have h12 : SafeSteps (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                      false) :: R'⟩ :=
                    safeSteps_trans hpre hs1
                  have hr12 : runTot (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                      false) :: R'⟩ =
                      ⟨.mAL, (Δ1, false) :: (b, false) :: Ls, Z1⟩ := by
                    rw [runTot_add]; exact hr1'
                  have hsub : k - (1 + m1) = k - 1 - m1 := by omega
                  rw [← hsub] at hs2
                  exact safeSteps_of_prefix h12 hr12 hs2
                · refine Or.inr ⟨1 + m1 + m2, n1 + n2 + 1, Δ2, Z2, by omega, by omega,
                    EvalF.two_false hev1 hdp2, ?_, ?_⟩
                  · refine safeSteps_trans (safeSteps_trans hpre hs1) ?_
                    rw [runTot_add]
                    change SafeSteps m2 (runTot m1 ⟨.mDR, (0, false) :: (0, false) :: (b,
                        false) :: Ls, R'⟩)
                    rw [hr1']; exact hs2
                  · rw [runTot_add, runTot_add]
                    change runTot m2 (runTot m1 ⟨.mDR, (0, false) :: (0, false) :: (b, false) :: Ls,
                        R'⟩) = _
                    rw [hr1']; exact hr2
          | true =>
            -- mDR (0::b::Ls) ((0,T)::R') ⊢¹ mD0 (0::0::b::Ls) R', matching EvalF ((2,T)::R')!
            have hpre : SafeSteps 1 ⟨.mDR, (0, false) :: (b, false) :: Ls, (0, true) :: R'⟩ :=
              safeSteps_step rfl (safeSteps_zero _)
            rcases Nat.lt_or_ge k 1 with hlt | hge
            · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
            · rcases (ih (k - 1) (by omega)).1 0 ((0, false) :: (b, false) :: Ls) R' with hs1 | ⟨m1,
                  n1, Δ1, Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
              · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
              · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
                rcases (ih (k - 1 - m1) (by omega)).2.2.2 (1 + Δ1) 0 ((b,
                    false) :: Ls) Z1 hne1 with hs2 | ⟨m2, n2, Δ2, Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
                · refine Or.inl ?_
                  have h12 : SafeSteps (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                      true) :: R'⟩ :=
                    safeSteps_trans hpre hs1
                  have hr12 : runTot (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                      true) :: R'⟩ =
                      ⟨.mAL, (1 + Δ1, false) :: (0, false) :: (b, false) :: Ls, Z1⟩ := by
                    rw [runTot_add]; exact hr1
                  have hsub : k - (1 + m1) = k - 1 - m1 := by omega
                  rw [← hsub] at hs2
                  exact safeSteps_of_prefix h12 hr12 hs2
                · have hev12 : EvalF (n1 + n2 + 1) ((1, false) :: R') Δ2 Z2 :=
                    EvalF.one_false hev1 hdp2
                  have hne2 : Z2 ≠ [] := evalF_out_nonempty hev12
                  have hr2' : runTot m2 ⟨.mAL, (1 + Δ1, false) :: (0, false) :: (b, false) :: Ls,
                      Z1⟩ =
                      ⟨.mAL, (Δ2, false) :: (b, false) :: Ls, Z2⟩ := by
                    simpa only [Nat.zero_add] using hr2
                  rcases (ih (k - 1 - m1 - m2) (by omega)).2.2.2 Δ2 b Ls Z2 hne2 with hs3 | ⟨m3, n3,
                      Δ3, Z3, hm3le, hm3pos, hdp3, hs3, hr3⟩
                  · refine Or.inl ?_
                    have h12 : SafeSteps (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                        true) :: R'⟩ :=
                      safeSteps_trans hpre hs1
                    have h123 : SafeSteps (1 + m1 + m2) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                        true) :: R'⟩ := by
                      refine safeSteps_trans h12 ?_
                      rw [runTot_add]
                      change SafeSteps m2 (runTot m1 ⟨.mD0, (0, false) :: (0, false) :: (b,
                          false) :: Ls, R'⟩)
                      rw [hr1]; exact hs2
                    have hr123 : runTot (1 + m1 + m2) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                        true) :: R'⟩ =
                        ⟨.mAL, (Δ2, false) :: (b, false) :: Ls, Z2⟩ := by
                      rw [runTot_add, runTot_add]
                      change runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (0, false) :: (b,
                          false) :: Ls, R'⟩) = _
                      rw [hr1]; exact hr2'
                    have hsub : k - (1 + m1 + m2) = k - 1 - m1 - m2 := by omega
                    rw [← hsub] at hs3
                    exact safeSteps_of_prefix h123 hr123 hs3
                  · refine Or.inr ⟨1 + m1 + m2 + m3, (n1 + n2 + 1) + n3 + 1, Δ3, Z3, by omega,
                        by omega,
                      EvalF.two_true hev12 hdp3, ?_, ?_⟩
                    · have h12 : SafeSteps (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                          true) :: R'⟩ :=
                        safeSteps_trans hpre hs1
                      have h123 : SafeSteps (1 + m1 + m2) ⟨.mDR, (0, false) :: (b, false) :: Ls, (0,
                          true) :: R'⟩ := by
                        refine safeSteps_trans h12 ?_
                        rw [runTot_add]
                        change SafeSteps m2 (runTot m1 ⟨.mD0, (0, false) :: (0, false) :: (b,
                            false) :: Ls, R'⟩)
                        rw [hr1]; exact hs2
                      refine safeSteps_trans h123 ?_
                      rw [runTot_add, runTot_add]
                      change SafeSteps m3 (runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (0,
                          false) :: (b, false) :: Ls, R'⟩))
                      rw [hr1, hr2']; exact hs3
                    · rw [runTot_add, runTot_add, runTot_add]
                      change runTot m3 (runTot m2 (runTot m1 ⟨.mD0, (0, false) :: (0, false) :: (b,
                          false) :: Ls, R'⟩)) = _
                      rw [hr1, hr2']; exact hr3
        | succ d1 =>
          -- mDR (0::b::Ls) ((d1+1, c)::R') ⊢¹ mBR (1::b::Ls) ((d1, c)::R'), matching EvalF ((d1+3,
          -- c)::R')!
          have hpre : SafeSteps 1 ⟨.mDR, (0, false) :: (b, false) :: Ls, (d1 + 1, c) :: R'⟩ :=
            safeSteps_step rfl (safeSteps_zero _)
          rcases Nat.lt_or_ge k 1 with hlt | hge
          · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
          · rcases (ih (k - 1) (by omega)).2.1 1 ((b, false) :: Ls) d1 c R' with hs1 | ⟨m1, n1, Δ1,
                Z1, hm1le, hm1pos, hev1, hs1, hr1⟩
            · exact Or.inl (safeSteps_of_prefix hpre rfl hs1)
            · have hne1 : Z1 ≠ [] := by
                cases hev1 with
                | even_false hf => exact evalF_out_nonempty hf
                | even_true _ => exact bump_nonempty _
                | odd_false hf => exact evalF_out_nonempty hf
                | odd_true hf => exact evalF_out_nonempty hf
              rcases (ih (k - 1 - m1) (by omega)).2.2.2 (1 + Δ1) b Ls Z1 hne1 with hs2 | ⟨m2, n2,
                  Δ2, Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
              · refine Or.inl ?_
                have h12 : SafeSteps (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (d1 + 1,
                    c) :: R'⟩ :=
                  safeSteps_trans hpre hs1
                have hr12 : runTot (1 + m1) ⟨.mDR, (0, false) :: (b, false) :: Ls, (d1 + 1,
                    c) :: R'⟩ =
                    ⟨.mAL, (1 + Δ1, false) :: (b, false) :: Ls, Z1⟩ := by
                  rw [runTot_add]; exact hr1
                have hsub : k - (1 + m1) = k - 1 - m1 := by omega
                rw [← hsub] at hs2
                exact safeSteps_of_prefix h12 hr12 hs2
              · refine Or.inr ⟨1 + m1 + m2, n1 + n2 + 1, Δ2, Z2, by omega, by omega,
                  EvalF.ge3 hev1 hdp2, ?_, ?_⟩
                · refine safeSteps_trans (safeSteps_trans hpre hs1) ?_
                  rw [runTot_add]
                  change SafeSteps m2 (runTot m1 ⟨.mBR, (1, false) :: (b, false) :: Ls, (d1,
                      c) :: R'⟩)
                  rw [hr1]; exact hs2
                · rw [runTot_add, runTot_add]
                  change runTot m2 (runTot m1 ⟨.mBR, (1, false) :: (b, false) :: Ls, (d1,
                      c) :: R'⟩) = _
                  rw [hr1]; exact hr2
    have hDisp : ∀ v b Ls Z, Z ≠ [] → DispOutcome k v b Ls Z := by
      intro v b Ls Z hZne
      set q := v / 3
      set r := v % 3
      have hdiv : v = 3 * q + r := by omega
      have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr_cases with hr0 | hr1 | hr2
      · have hvq : v = 3 * q := by omega
        rw [hvq]
        rcases mAL_drain_3q q 0 ((b, false) :: Ls) Z with ⟨hdr_s, hdr_r⟩
        have hdr_s' : SafeSteps (2 * q) ⟨.mAL, (3 * q, false) :: (b, false) :: Ls, Z⟩ := by
          simpa only [Nat.add_zero] using hdr_s
        have hdr_r' : runTot (2 * q) ⟨.mAL, (3 * q, false) :: (b, false) :: Ls, Z⟩ =
            ⟨.mAL, (0, false) :: (b, false) :: Ls, rep1 q Z⟩ := by
          simpa only [Nat.add_zero] using hdr_r
        have hrep_ne : rep1 q Z ≠ [] := rep1_nonempty q hZne
        rcases mBR_bump2_nonempty b Ls (rep1 q Z) hrep_ne with ⟨hb_s, hb_r⟩
        -- mAL (0::b::Ls) (rep1 q Z) ⊢¹ mE1 (b::Ls) (rep1 q Z) ⊢¹ mBR (b::Ls) (bump2 (rep1 q Z)) ⊢²
        -- mBR ((b+2)::Ls) (rep1 q Z)
        have hpre : SafeSteps (2 * q + 4) ⟨.mAL, (3 * q, false) :: (b, false) :: Ls, Z⟩ := by
          refine safeSteps_trans hdr_s' ?_
          rw [hdr_r']
          exact safeSteps_step rfl (safeSteps_step rfl hb_s)
        have hrun : runTot (2 * q + 4) ⟨.mAL, (3 * q, false) :: (b, false) :: Ls, Z⟩ =
            ⟨.mBR, (b + 2, false) :: Ls, rep1 q Z⟩ := by
          rw [runTot_add, hdr_r']
          change runTot 2 ⟨.mBR, (b, false) :: Ls, bump2 (rep1 q Z)⟩ = _
          exact hb_r
        rcases Nat.lt_or_ge k (2 * q + 4) with hlt | hge
        · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
        · cases hrep : rep1 q Z with
          | nil => exact False.elim (hrep_ne hrep)
          | cons p0 Zrest =>
            rcases p0 with ⟨d0, c0⟩
            rw [hrep] at hrun
            rcases (ih (k - (2 * q + 4)) (by omega)).2.1 (b + 2) Ls d0 c0 Zrest with hs1 | ⟨m1, n1,
                Δ1, Z', hm1le, hm1pos, hev1, hs1, hr1⟩
            · exact Or.inl (safeSteps_of_prefix hpre hrun hs1)
            · have hev1' : EvalDL n1 (rep1 q Z) Δ1 Z' := by rw [hrep]; exact hev1
              refine Or.inr ⟨2 * q + 4 + m1, n1 + 1, 2 + Δ1, Z', by omega, by omega,
                Disp.rem0 hev1', ?_, ?_⟩
              · refine safeSteps_trans hpre ?_
                rw [hrun]; exact hs1
              · rw [runTot_add, hrun, hr1]
                have hb : b + 2 + Δ1 = b + (2 + Δ1) := by omega
                rw [hb]
      · have hvq : v = 3 * q + 1 := by omega
        rw [hvq]
        rcases mAL_drain_3q q 1 ((b, false) :: Ls) Z with ⟨hdr_s, hdr_r⟩
        have hrep_ne : rep1 q Z ≠ [] := rep1_nonempty q hZne
        have hpre : SafeSteps (2 * q + 1) ⟨.mAL, (3 * q + 1, false) :: (b, false) :: Ls, Z⟩ := by
          refine safeSteps_trans hdr_s ?_
          rw [hdr_r]
          exact safeSteps_step rfl (safeSteps_zero _)
        have hrun : runTot (2 * q + 1) ⟨.mAL, (3 * q + 1, false) :: (b, false) :: Ls, Z⟩ =
            ⟨.mAL, (b + 0, false) :: Ls, (0, true) :: rep1 q Z⟩ := by
          rw [runTot_add, hdr_r]
          cases hrep : rep1 q Z with
          | nil => exact False.elim (hrep_ne hrep)
          | cons p0 Zrest => rfl
        rcases Nat.lt_or_ge k (2 * q + 1) with hlt | hge
        · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
        · exact Or.inr ⟨2 * q + 1, 1, 0, (0, true) :: rep1 q Z, hge, by omega,
            Disp.rem1 q Z, hpre, hrun⟩
      · have hvq : v = 3 * q + 2 := by omega
        rw [hvq]
        rcases mAL_drain_3q q 2 ((b, false) :: Ls) Z with ⟨hdr_s, hdr_r⟩
        -- mAL (2::b::Ls) (rep1 q Z) ⊢¹ mBR ((b+1)::Ls) ((1,F)::rep1 q Z) ⊢¹ mDR ((b+2)::Ls)
        -- ((0,F)::rep1 q Z) ⊢¹ mDR (0::(b+2)::Ls) (rep1 q Z)
        have hpre : SafeSteps (2 * q + 3) ⟨.mAL, (3 * q + 2, false) :: (b, false) :: Ls, Z⟩ := by
          refine safeSteps_trans hdr_s ?_
          rw [hdr_r]
          exact safeSteps_step rfl (safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _)))
        have hrun : runTot (2 * q + 3) ⟨.mAL, (3 * q + 2, false) :: (b, false) :: Ls, Z⟩ =
            ⟨.mDR, (0, false) :: (b + 2, false) :: Ls, rep1 q Z⟩ := by
          rw [runTot_add, hdr_r]; rfl
        rcases Nat.lt_or_ge k (2 * q + 3) with hlt | hge
        · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
        · rcases (ih (k - (2 * q + 3)) (by omega)).2.2.1 (b + 2) Ls (rep1 q Z) with hs1 | ⟨m1, n1,
              Δ1, Z', hm1le, hm1pos, hev1, hs1, hr1⟩
          · exact Or.inl (safeSteps_of_prefix hpre hrun hs1)
          · refine Or.inr ⟨2 * q + 3 + m1, n1 + 1, 2 + Δ1, Z', by omega, by omega,
              Disp.rem2 hev1, ?_, ?_⟩
            · refine safeSteps_trans hpre ?_
              rw [hrun]; exact hs1
            · rw [runTot_add, hrun, hr1]
              have hb : b + 2 + Δ1 = b + (2 + Δ1) := by omega
              rw [hb]
    exact ⟨hD0, hBR, hDR0, hDisp⟩

theorem mD0_horizon_safe_or_evalF (k a : ℕ) (Ls R : List (ℕ × Bool)) :
    D0Outcome k a Ls R :=
  (horizon_bisim k).1 a Ls R

theorem mAL_disp_horizon_safe_or_disp (k v b : ℕ) (Ls Z : List (ℕ × Bool)) (hZ : Z ≠ []) :
    DispOutcome k v b Ls Z :=
  (horizon_bisim k).2.2.2 v b Ls Z hZ

/-! ## Turnkey Singleton-Wall Non-Halting Lift for `tm484` -/

/-- One full singleton-wall cycle from `mAL [(2, false)] ((1, false) :: S)` either stays safe
for `k` steps or evaluates `EvalF ((3, false) :: S) = (Δ, Z)` landing at `mAL [(1 + Δ, false)] Z`
in `0 < m ≤ k` safe steps. -/
theorem wall_bounce_horizon (k : ℕ) (S : List (ℕ × Bool)) :
    SafeSteps k ⟨.mAL, [(2, false)], (1, false) :: S⟩ ∨
    ∃ m n Δ Z, m ≤ k ∧ 0 < m ∧ EvalF n ((3, false) :: S) Δ Z ∧
      SafeSteps m ⟨.mAL, [(2, false)], (1, false) :: S⟩ ∧
      runTot m ⟨.mAL, [(2, false)], (1, false) :: S⟩ = ⟨.mAL, [(1 + Δ, false)], Z⟩ := by
  -- 5 deterministic safe steps:
  -- mAL [2] (1::S) -> mBR [0] (1::1::S) -> mDR [1] (0::1::S) -> mDR [0,1] (1::S) -> mBR [1,1]
  -- (0::S) -> mD0 [2,1] S
  have hpre : SafeSteps 5 ⟨.mAL, [(2, false)], (1, false) :: S⟩ :=
    safeSteps_step rfl
        (safeSteps_step rfl
        (safeSteps_step rfl (safeSteps_step rfl (safeSteps_step rfl (safeSteps_zero _)))))
  have hrun : runTot 5 ⟨.mAL, [(2, false)], (1, false) :: S⟩ =
      ⟨.mD0, [(2, false), (1, false)], S⟩ := rfl
  rcases Nat.lt_or_ge k 5 with hlt | hge
  · exact Or.inl (safeSteps_mono (Nat.le_of_lt hlt) hpre)
  · rcases mD0_horizon_safe_or_evalF (k - 5) 2 [(1, false)] S with hs1 | ⟨m1, n1, Δ1, Z1, hm1le,
        hm1pos, hev1, hs1, hr1⟩
    · exact Or.inl (safeSteps_of_prefix hpre hrun hs1)
    · have hne1 : Z1 ≠ [] := evalF_out_nonempty hev1
      rcases mAL_disp_horizon_safe_or_disp (k - 5 - m1) (3 + Δ1) 1 [] Z1 hne1 with hs2 | ⟨m2, n2,
          Δ2, Z2, hm2le, hm2pos, hdp2, hs2, hr2⟩
      · refine Or.inl ?_
        have h12 : SafeSteps (5 + m1) ⟨.mAL, [(2, false)], (1, false) :: S⟩ := by
          refine safeSteps_trans hpre ?_
          rw [hrun]; exact hs1
        have hr12 : runTot (5 + m1) ⟨.mAL, [(2, false)], (1, false) :: S⟩ =
            ⟨.mAL, [(3 + Δ1, false), (1, false)], Z1⟩ := by
          rw [runTot_add, hrun]; exact hr1
        have hsub : k - (5 + m1) = k - 5 - m1 := by omega
        rw [← hsub] at hs2
        exact safeSteps_of_prefix h12 hr12 hs2
      · have hevDL : EvalDL (n1 + 1) ((0, false) :: S) (2 + Δ1) Z1 := by
          simpa only [Nat.mul_zero, Nat.zero_add] using (EvalDL.even_false (q := 0) hev1)
        have hdp2' : Disp n2 (1 + (2 + Δ1)) Z1 Δ2 Z2 := by
          have heq : 1 + (2 + Δ1) = 3 + Δ1 := by omega
          rw [heq]; exact hdp2
        have hevF : EvalF ((n1 + 1) + n2 + 1) ((3, false) :: S) Δ2 Z2 :=
          EvalF.ge3 hevDL hdp2'
        refine Or.inr ⟨5 + m1 + m2, (n1 + 1) + n2 + 1, Δ2, Z2, by omega, by omega, hevF, ?_, ?_⟩
        · have h12 : SafeSteps (5 + m1) ⟨.mAL, [(2, false)], (1, false) :: S⟩ := by
            refine safeSteps_trans hpre ?_
            rw [hrun]; exact hs1
          refine safeSteps_trans h12 ?_
          rw [runTot_add, hrun, hr1]; exact hs2
        · rw [runTot_add, runTot_add, hrun, hr1, hr2]

/-- **Turnkey Singleton-Wall Non-Halting Lift**:
Any predicate `W : List (ℕ × Bool) → Prop` closed under `EvalF ((3, false) :: S) ∈ {7, 10}`
immediately implies `SafeSteps k ⟨.mAL, [(2, false)], (1, false) :: S⟩` for all `k : ℕ`,
completely constructively (zero `excluded middle`). -/
theorem safeSteps_wall_of_evalF_W_closed
    (W : List (ℕ × Bool) → Prop)
    (hW : ∀ n S Δ Z, EvalF n ((3, false) :: S) Δ Z →
      StrictNo0F ((3, false) :: S) → W ((3, false) :: S) →
      (Δ = 7 ∧ W ((3, false) :: (1, false) :: Z)) ∨
      (Δ = 10 ∧ W ((3, false) :: (1, false) :: (1, false) :: Z))) :
    ∀ k S, StrictNo0F S → W ((3, false) :: S) →
      SafeSteps k ⟨.mAL, [(2, false)], (1, false) :: S⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hNo0F hWS
    rcases wall_bounce_horizon k S with hsafe | ⟨m, n, Δ, Z, hmle, hmpos, hev, hsm, hrm⟩
    · exact hsafe
    · have hNo3S : StrictNo0F ((3, false) :: S) := strictNo0F_cons_pos 2 false hNo0F
      have hNoZ : StrictNo0F Z := evalF_preserves_no0f hev hNo3S
      rcases hW n S Δ Z hev hNo3S hWS with ⟨rfl, hW7⟩ | ⟨rfl, hW10⟩
      · -- Δ = 7: mAL [8] Z ⊢⁴ mAL [2] (1 :: 1 :: Z)
        rcases mAL_drain_3q 2 2 [] Z with ⟨hd4, hr4⟩
        have hstep : SafeSteps (m + 4) ⟨.mAL, [(2, false)], (1, false) :: S⟩ := by
          refine safeSteps_trans hsm ?_
          rw [hrm]; exact hd4
        have hrun : runTot (m + 4) ⟨.mAL, [(2, false)], (1, false) :: S⟩ =
            ⟨.mAL, [(2, false)], (1, false) :: (1, false) :: Z⟩ := by
          rw [runTot_add, hrm]; exact hr4
        have hrem : SafeSteps (k - (m + 4)) ⟨.mAL, [(2, false)], (1, false) :: (1, false) :: Z⟩ :=
          ih (k - (m + 4)) (by omega) ((1, false) :: Z) (strictNo0F_cons_pos 0 false hNoZ) hW7
        exact safeSteps_of_prefix hstep hrun hrem
      · -- Δ = 10: mAL [11] Z ⊢⁶ mAL [2] (1 :: 1 :: 1 :: Z)
        rcases mAL_drain_3q 3 2 [] Z with ⟨hd6, hr6⟩
        have hstep : SafeSteps (m + 6) ⟨.mAL, [(2, false)], (1, false) :: S⟩ := by
          refine safeSteps_trans hsm ?_
          rw [hrm]; exact hd6
        have hrun : runTot (m + 6) ⟨.mAL, [(2, false)], (1, false) :: S⟩ =
            ⟨.mAL, [(2, false)], (1, false) :: (1, false) :: (1, false) :: Z⟩ := by
          rw [runTot_add, hrm]; exact hr6
        have hrem : SafeSteps (k - (m + 6)) ⟨.mAL, [(2, false)], (1, false) :: (1, false) :: (1,
            false) :: Z⟩ :=
          ih (k - (m + 6)) (by omega) ((1, false) :: (1, false) :: Z)
            (strictNo0F_cons_pos 0 false (strictNo0F_cons_pos 0 false hNoZ)) hW10
        exact safeSteps_of_prefix hstep hrun hrem

/-- Eternal doorway avoidance from `mAL [(2, false)] ((1, false) :: S)` given any `EvalF`-closed
wall predicate `W`. -/
theorem orbit_safe_of_evalF_W_closed
    (W : List (ℕ × Bool) → Prop)
    (hW : ∀ n S Δ Z, EvalF n ((3, false) :: S) Δ Z →
      StrictNo0F ((3, false) :: S) → W ((3, false) :: S) →
      (Δ = 7 ∧ W ((3, false) :: (1, false) :: Z)) ∨
      (Δ = 10 ∧ W ((3, false) :: (1, false) :: (1, false) :: Z)))
    (S : List (ℕ × Bool)) (hNo0F : StrictNo0F S) (hWS : W ((3, false) :: S)) :
    ∀ k : ℕ, isDoor (stepTot^[k] ⟨.mAL, [(2, false)], (1, false) :: S⟩) = false := by
  intro k
  rw [← runTot_eq_iterate]
  exact safeSteps_wall_of_evalF_W_closed W hW (k + 1) S hNo0F hWS k (Nat.lt_succ_self k)


private theorem bump_eq_bumpR (R : List (ℕ × Bool)) :
    bump R = BusyBeaver.Calculi.PairStackA.bumpR R := by
  cases R with
  | nil => rfl
  | cons x xs => cases x; rfl

private theorem bump2_eq_bumpR2 (R : List (ℕ × Bool)) :
    bump2 R = BusyBeaver.Calculi.PairStackA.bumpR (BusyBeaver.Calculi.PairStackA.bumpR R) := by
  simp only [bump2, bump_eq_bumpR]

private theorem rep1_eq_ones_append (q : ℕ) (R : List (ℕ × Bool)) :
    rep1 q R = BusyBeaver.Calculi.PairStackA.ones q ++ R := by
  induction q with
  | zero => rfl
  | succ k ih => simp [rep1, BusyBeaver.Calculi.PairStackA.ones, ih]

private theorem strictNo0F_to_noNonlast0F :
    ∀ R, StrictNo0F R → BusyBeaver.Calculi.PairStackA.NoNonlast0F R
  | [] => fun _ => trivial
  | [_] => fun _ => trivial
  | (0, false) :: _ :: _ => fun h => h
  | (0, true) :: y :: ys => fun h => strictNo0F_to_noNonlast0F (y :: ys) h
  | (_ + 1, _) :: y :: ys => fun h => strictNo0F_to_noNonlast0F (y :: ys) h

private theorem bigD1_add_2q (q : ℕ) {s d Δ' : ℕ} {b : Bool} {R Z : List (ℕ × Bool)}
    (h : BusyBeaver.Calculi.PairStackA.BigD1 s ((d, b) :: R) Δ' Z) :
    ∃ s', BusyBeaver.Calculi.PairStackA.BigD1 s' ((d + 2 * q, b) :: R) (Δ' + 2 * q) Z := by
  induction q with
  | zero => exact ⟨s, h⟩
  | succ k ih =>
    obtain ⟨sk, hk⟩ := ih
    refine ⟨sk + 1, ?_⟩
    have h1 := BusyBeaver.Calculi.PairStackA.BigD1.ge2 hk
    simpa [Nat.mul_succ, Nat.add_assoc] using h1

private theorem evalF_evalDL_to_bigFD (n : ℕ) :
    (∀ R Δ Z, EvalF n R Δ Z → ∃ s, BusyBeaver.Calculi.PairStackA.BigF s R Δ Z) ∧
    (∀ R Δ Z, EvalDL n R Δ Z → ∃ s, BusyBeaver.Calculi.PairStackA.BigD1 s R (Δ + 1) Z) := by
  refine Nat.strongRecOn n fun m ih => ?_
  constructor
  · intro R Δ Z hF
    cases hF with
    | nil => exact ⟨0, BusyBeaver.Calculi.PairStackA.BigF.nil⟩
    | zero_false R0 =>
      exact ⟨0, by rw [bump2_eq_bumpR2]; exact BusyBeaver.Calculi.PairStackA.BigF.zeroF R0⟩
    | zero_true R0 => exact ⟨0, BusyBeaver.Calculi.PairStackA.BigF.zeroT R0⟩
    | one_true R0 =>
      exact ⟨0, by rw [bump_eq_bumpR]; exact BusyBeaver.Calculi.PairStackA.BigF.oneT R0⟩
    | one_false h1 hdisp =>
      rename_i n1 n2 Δ1 R0 Z1
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).1 R0 Δ1 Z1 h1
      generalize hv : 1 + Δ1 = v at hdisp
      cases hdisp with
      | rem1 q _ =>
        have hrem : (1 + Δ1) % 3 = 1 := by omega
        have hq : (1 + Δ1) / 3 = q := by omega
        refine ⟨s1 + 1, ?_⟩
        rw [rep1_eq_ones_append, ← hq]
        exact BusyBeaver.Calculi.PairStackA.BigF.oneF_rem1 hB1 hrem
      | rem2 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).1 _ Δ2 Z h2
        rw [bump2_eq_bumpR2, rep1_eq_ones_append] at hB2
        have hD2 :
            BusyBeaver.Calculi.PairStackA.BigD1 (s2 + 1)
            (BusyBeaver.Calculi.PairStackA.ones ((1 + Δ1) / 3 + 1) ++ Z1) (Δ2 + 2) Z := by
          have hq : (1 + Δ1) / 3 = q := by omega
          rw [hq]
          exact BusyBeaver.Calculi.PairStackA.BigD1.oneF hB2
        have hrem : (1 + Δ1) % 3 = 2 := by omega
        refine ⟨s1 + (s2 + 1) + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.oneF_rem2 hB1 hrem hD2
        simpa [Nat.add_comm] using hres
      | rem0 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).2 _ Δ2 Z h2
        rw [rep1_eq_ones_append] at hB2
        have hq : (1 + Δ1) / 3 = q := by omega
        rw [← hq] at hB2
        have hrem : (1 + Δ1) % 3 = 0 := by omega
        refine ⟨s1 + s2 + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.oneF_rem0 hB1 hrem hB2
        have hadd : Δ2 + 1 + 1 = 2 + Δ2 := by omega
        rwa [hadd] at hres
    | two_false h1 hdisp =>
      rename_i n1 n2 Δ1 R0 Z1
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).1 _ Δ1 Z1 h1
      rw [bump2_eq_bumpR2] at hB1
      generalize hv : Δ1 = v at hdisp
      cases hdisp with
      | rem1 q _ =>
        have hrem : Δ1 % 3 = 1 := by omega
        have hq : Δ1 / 3 = q := by omega
        refine ⟨s1 + 1, ?_⟩
        rw [rep1_eq_ones_append, ← hq]
        exact BusyBeaver.Calculi.PairStackA.BigF.twoF_rem1 hB1 hrem
      | rem2 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).1 _ Δ2 Z h2
        rw [bump2_eq_bumpR2, rep1_eq_ones_append] at hB2
        have hD2 :
            BusyBeaver.Calculi.PairStackA.BigD1 (s2 + 1)
            (BusyBeaver.Calculi.PairStackA.ones (Δ1 / 3 + 1) ++ Z1) (Δ2 + 2) Z := by
          have hq : Δ1 / 3 = q := by omega
          rw [hq]
          exact BusyBeaver.Calculi.PairStackA.BigD1.oneF hB2
        have hrem : Δ1 % 3 = 2 := by omega
        refine ⟨s1 + (s2 + 1) + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.twoF_rem2 hB1 hrem hD2
        simpa [Nat.add_comm] using hres
      | rem0 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).2 _ Δ2 Z h2
        rw [rep1_eq_ones_append] at hB2
        have hq : Δ1 / 3 = q := by omega
        rw [← hq] at hB2
        have hrem : Δ1 % 3 = 0 := by omega
        refine ⟨s1 + s2 + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.twoF_rem0 hB1 hrem hB2
        have hadd : Δ2 + 1 + 1 = 2 + Δ2 := by omega
        rwa [hadd] at hres
    | two_true h1 hdisp =>
      rename_i n1 n2 Δ1 R0 Z1
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).1 _ Δ1 Z1 h1
      generalize hv : Δ1 = v at hdisp
      cases hdisp with
      | rem1 q _ =>
        have hrem : Δ1 % 3 = 1 := by omega
        have hq : Δ1 / 3 = q := by omega
        refine ⟨s1 + 1, ?_⟩
        rw [rep1_eq_ones_append, ← hq]
        exact BusyBeaver.Calculi.PairStackA.BigF.twoT_rem1 hB1 hrem
      | rem2 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).1 _ Δ2 Z h2
        rw [bump2_eq_bumpR2, rep1_eq_ones_append] at hB2
        have hD2 :
            BusyBeaver.Calculi.PairStackA.BigD1 (s2 + 1)
            (BusyBeaver.Calculi.PairStackA.ones (Δ1 / 3 + 1) ++ Z1) (Δ2 + 2) Z := by
          have hq : Δ1 / 3 = q := by omega
          rw [hq]
          exact BusyBeaver.Calculi.PairStackA.BigD1.oneF hB2
        have hrem : Δ1 % 3 = 2 := by omega
        refine ⟨s1 + (s2 + 1) + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.twoT_rem2 hB1 hrem hD2
        simpa [Nat.add_comm] using hres
      | rem0 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).2 _ Δ2 Z h2
        rw [rep1_eq_ones_append] at hB2
        have hq : Δ1 / 3 = q := by omega
        rw [← hq] at hB2
        have hrem : Δ1 % 3 = 0 := by omega
        refine ⟨s1 + s2 + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.twoT_rem0 hB1 hrem hB2
        have hadd : Δ2 + 1 + 1 = 2 + Δ2 := by omega
        rwa [hadd] at hres
    | ge3 h1 hdisp =>
      rename_i d n1 n2 Δ1 c R0 Z1
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).2 _ Δ1 Z1 h1
      generalize hv : 1 + Δ1 = v at hdisp
      cases hdisp with
      | rem1 q _ =>
        have hrem : (Δ1 + 1) % 3 = 1 := by omega
        have hq : (Δ1 + 1) / 3 = q := by omega
        refine ⟨s1 + 1, ?_⟩
        rw [rep1_eq_ones_append, ← hq]
        exact BusyBeaver.Calculi.PairStackA.BigF.ge3_rem1 hB1 hrem
      | rem2 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).1 _ Δ2 Z h2
        rw [bump2_eq_bumpR2, rep1_eq_ones_append] at hB2
        have hD2 :
            BusyBeaver.Calculi.PairStackA.BigD1 (s2 + 1)
            (BusyBeaver.Calculi.PairStackA.ones ((Δ1 + 1) / 3 + 1) ++ Z1) (Δ2 + 2) Z := by
          have hq : (Δ1 + 1) / 3 = q := by omega
          rw [hq]
          exact BusyBeaver.Calculi.PairStackA.BigD1.oneF hB2
        have hrem : (Δ1 + 1) % 3 = 2 := by omega
        refine ⟨s1 + (s2 + 1) + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.ge3_rem2 hB1 hrem hD2
        simpa [Nat.add_comm] using hres
      | rem0 h2 =>
        rename_i q n2' Δ2
        obtain ⟨s2, hB2⟩ := (ih n2' (by omega)).2 _ Δ2 Z h2
        rw [rep1_eq_ones_append] at hB2
        have hq : (Δ1 + 1) / 3 = q := by omega
        rw [← hq] at hB2
        have hrem : (Δ1 + 1) % 3 = 0 := by omega
        refine ⟨s1 + s2 + 1, ?_⟩
        have hres := BusyBeaver.Calculi.PairStackA.BigF.ge3_rem0 hB1 hrem hB2
        have hadd : Δ2 + 1 + 1 = 2 + Δ2 := by omega
        rwa [hadd] at hres
  · intro R Δ Z hDL
    cases hDL with
    | even_false hF =>
      rename_i q n1 Δ1 R0
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).1 R0 Δ1 Z hF
      obtain ⟨s2, hB2⟩ := bigD1_add_2q q (BusyBeaver.Calculi.PairStackA.BigD1.zeroF hB1)
      refine ⟨s2, ?_⟩
      have h1 : 0 + 2 * q = 2 * q := by omega
      have h2 : Δ1 + 3 + 2 * q = 2 * q + 2 + Δ1 + 1 := by omega
      rw [h1, h2] at hB2
      exact hB2
    | even_true q R0 =>
      obtain ⟨s2, hB2⟩ := bigD1_add_2q q (BusyBeaver.Calculi.PairStackA.BigD1.zeroT R0)
      refine ⟨s2, ?_⟩
      rw [bump_eq_bumpR]
      have h1 : 0 + 2 * q = 2 * q := by omega
      have h2 : 3 + 2 * q = 2 * q + 2 + 1 := by omega
      rw [h1, h2] at hB2
      exact hB2
    | odd_false hF =>
      rename_i q n1 Δ1 R0
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).1 _ Δ1 Z hF
      rw [bump2_eq_bumpR2] at hB1
      obtain ⟨s2, hB2⟩ := bigD1_add_2q q (BusyBeaver.Calculi.PairStackA.BigD1.oneF hB1)
      refine ⟨s2, ?_⟩
      have h1 : 1 + 2 * q = 2 * q + 1 := by omega
      have h2 : Δ1 + 2 + 2 * q = 2 * q + 1 + Δ1 + 1 := by omega
      rw [h1, h2] at hB2
      exact hB2
    | odd_true hF =>
      rename_i q n1 Δ1 R0
      obtain ⟨s1, hB1⟩ := (ih n1 (by omega)).1 _ Δ1 Z hF
      obtain ⟨s2, hB2⟩ := bigD1_add_2q q (BusyBeaver.Calculi.PairStackA.BigD1.oneT hB1)
      refine ⟨s2, ?_⟩
      have h1 : 1 + 2 * q = 2 * q + 1 := by omega
      have h2 : Δ1 + 2 + 2 * q = 2 * q + 1 + Δ1 + 1 := by omega
      rw [h1, h2] at hB2
      exact hB2

def W_closed (R : List (ℕ × Bool)) : Prop :=
  (∃ G, R = (3, false) :: (1, false) :: G ∧ BusyBeaver.Calculi.PairStackA.Strong2 G) ∨
  (∃ G, R = (3, false) :: (1, false) :: (1, false) :: G ∧ BusyBeaver.Calculi.PairStackA.Good2 G)

theorem W_closed_step (n : ℕ) (S : List (ℕ × Bool)) (Δ : ℕ) (Z : List (ℕ × Bool))
    (hev : EvalF n ((3, false) :: S) Δ Z) (hNo : StrictNo0F ((3, false) :: S))
    (hW : W_closed ((3, false) :: S)) :
    (Δ = 7 ∧ W_closed ((3, false) :: (1, false) :: Z)) ∨
    (Δ = 10 ∧ W_closed ((3, false) :: (1, false) :: (1, false) :: Z)) := by
  obtain ⟨s, hB⟩ := (evalF_evalDL_to_bigFD n).1 _ _ _ hev
  have hN := strictNo0F_to_noNonlast0F _ hNo
  rcases hW with ⟨G, hEq, hS⟩ | ⟨G, hEq, hG⟩
  · cases hEq
    have hNG :=
        BusyBeaver.Calculi.PairStackA.noNonlast0F_tail
        (BusyBeaver.Calculi.PairStackA.noNonlast0F_tail hN)
    have ⟨h710, hSf⟩ := (BusyBeaver.Calculi.PairStackA.invAt_all s).good2_f31 hS.1 hB hNG
    have hS' := hSf hS
    rcases h710 with rfl | ⟨rfl, _⟩
    · exact Or.inl ⟨rfl, Or.inl ⟨Z, rfl, hS'⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨Z, rfl, hS'.1⟩⟩
  · cases hEq
    have hNG :=
        BusyBeaver.Calculi.PairStackA.noNonlast0F_tail
        (BusyBeaver.Calculi.PairStackA.noNonlast0F_tail
        (BusyBeaver.Calculi.PairStackA.noNonlast0F_tail hN))
    obtain ⟨rfl, hS'⟩ := (BusyBeaver.Calculi.PairStackA.invAt_all s).good2_f311 hG hB hNG
    exact Or.inl ⟨rfl, Or.inl ⟨Z, rfl, hS'⟩⟩


end BusyBeaver.Calculi.PairStackB
